use anyhow::{anyhow, bail, Context, Result};
use clap::{Parser, ValueEnum};
use indicatif::{MultiProgress, ProgressBar, ProgressStyle};
use md5::Context as Md5Context;
use serde::{Deserialize, Serialize};
use sha2::{Digest as ShaDigestTrait, Sha256};
use std::collections::BTreeMap;
use std::fs::{self, File};
use std::io::{BufReader, BufWriter, Read, Write};
use std::path::{Component, Path, PathBuf};
use std::thread;
use std::time::{Instant, SystemTime, UNIX_EPOCH};
use sysinfo::System;
use time::{format_description::well_known::Rfc3339, OffsetDateTime};
use walkdir::WalkDir;
use xxhash_rust::xxh3::Xxh3;

const IO_BUFFER_SIZE: usize = 8 * 1024 * 1024;

#[derive(Parser, Debug)]
#[command(author, version, about = "Robotface Offloader")]
struct Args {
    #[arg(long)]
    source: PathBuf,

    #[arg(long)]
    dest1: PathBuf,

    #[arg(long)]
    dest2: Option<PathBuf>,

    #[arg(long)]
    dest3: Option<PathBuf>,

    #[arg(long, default_value = "offload_report.json")]
    report: PathBuf,

    #[arg(long, default_value_t = 2)]
    retries: u8,

    #[arg(long, default_value = "copy-then-verify")]
    mode: RunMode,

    #[arg(long, default_value = "xxh3")]
    checksum: ChecksumType,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize, Deserialize, ValueEnum)]
enum RunMode {
    #[value(name = "copy-then-verify")]
    CopyThenVerify,
    #[value(name = "copy-only")]
    CopyOnly,
}

#[derive(Copy, Clone, Debug, Eq, PartialEq, Serialize, Deserialize, ValueEnum)]
enum ChecksumType {
    #[value(name = "xxh3")]
    Xxh3,
    #[value(name = "md5")]
    Md5,
    #[value(name = "sha256")]
    Sha256,
}

#[derive(Debug, Clone)]
struct SourceFile {
    source_path: PathBuf,
    relative_path: PathBuf,
    size_bytes: u64,
    modified_unix_ms: u128,
}

#[derive(Debug, Clone)]
struct DestinationPlan {
    label: &'static str,
    root: PathBuf,
}

#[derive(Debug)]
struct ProcessResult {
    source_checksum: Option<String>,
    destination_1: DestinationStatus,
    destination_2: Option<DestinationStatus>,
    destination_3: Option<DestinationStatus>,
    error: Option<String>,
    bytes_copied_this_run: u64,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct DestinationStatus {
    path: String,
    copied: bool,
    verified: bool,
    checksum: Option<String>,
    size_bytes: Option<u64>,
    status: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct FileReport {
    relative_path: String,
    source_path: String,
    file_size_bytes: u64,
    source_modified_unix_ms: u128,
    checksum_type: String,
    source_checksum: Option<String>,
    destination_1: DestinationStatus,
    destination_2: Option<DestinationStatus>,
    destination_3: Option<DestinationStatus>,
    error: Option<String>,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SummaryReport {
    final_status: String,
    final_progress: String,
    size_of_offload_bytes: u64,
    size_of_offload_human_readable: String,
    bytes_copied_this_run: u64,
    bytes_copied_this_run_human_readable: String,
    checksum_type: String,
    mode: String,
    offload_start_timestamp: String,
    offload_finish_timestamp: String,
    total_time_seconds: f64,
    average_throughput_mb_per_sec: f64,
    total_files: usize,
    completed_files: usize,
    skipped_files: usize,
    failed_files: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct SystemInfoReport {
    operating_system: String,
    logical_processors: usize,
    total_ram_gb: f64,
    app_version: String,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct DestinationRootStatus {
    path: Option<String>,
    provided: bool,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct DestinationRootsReport {
    dest1: DestinationRootStatus,
    dest2: DestinationRootStatus,
    dest3: DestinationRootStatus,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct ResumeReport {
    previous_report_loaded: bool,
    compatible_previous_report_found: bool,
    skipped_previously_completed_files: usize,
    retried_incomplete_or_failed_files: usize,
}

#[derive(Debug, Clone, Serialize, Deserialize)]
struct JobReport {
    summary: SummaryReport,
    system_details: SystemInfoReport,
    source_root_name: String,
    source_root_path: String,
    destination_roots: DestinationRootsReport,
    resume: ResumeReport,
    total_directories: usize,
    files: Vec<FileReport>,
}

enum HasherKind {
    Xxh3(Xxh3),
    Md5(Md5Context),
    Sha256(Sha256),
}

impl HasherKind {
    fn new(checksum_type: ChecksumType) -> Self {
        match checksum_type {
            ChecksumType::Xxh3 => Self::Xxh3(Xxh3::new()),
            ChecksumType::Md5 => Self::Md5(Md5Context::new()),
            ChecksumType::Sha256 => Self::Sha256(Sha256::new()),
        }
    }

    fn update(&mut self, data: &[u8]) {
        match self {
            HasherKind::Xxh3(hasher) => hasher.update(data),
            HasherKind::Md5(hasher) => hasher.consume(data),
            HasherKind::Sha256(hasher) => hasher.update(data),
        }
    }

    fn finalize_hex(self) -> String {
        match self {
            HasherKind::Xxh3(hasher) => format!("{:016x}", hasher.digest()),
            HasherKind::Md5(hasher) => format!("{:x}", hasher.compute()),
            HasherKind::Sha256(hasher) => format!("{:x}", hasher.finalize()),
        }
    }
}

fn main() -> Result<()> {
    let args = Args::parse();
    let job_start_utc = OffsetDateTime::now_utc();
    let job_start_instant = Instant::now();

    validate_paths(&args)?;
    ensure_destination_roots(&args)?;

    let source_root_path = absolute_normalized(&args.source)?;
    let destination_roots = build_destination_roots_report(&args)?;
    let destinations = build_destinations(&args)?;
    let directories = collect_directories(&source_root_path)?;
    create_destination_directories(&directories, &destinations)?;
    let files = collect_files(&source_root_path)?;
    let total_bytes: u64 = files.iter().map(|file| file.size_bytes).sum();

    let previous_report_raw = load_previous_report(&args.report);
    let previous_report_loaded = previous_report_raw.is_some();
    let previous_report = previous_report_raw
        .as_ref()
        .filter(|report| previous_report_is_compatible(report, &source_root_path, &args, &destination_roots));
    let compatible_previous_report_found = previous_report.is_some();
    let previous_file_lookup = previous_report
        .map(build_previous_file_lookup)
        .unwrap_or_default();

    println!("Robotface Offloader");
    println!("Source: {}", source_root_path.display());
    println!("Destination 1: {}", args.dest1.display());
    if let Some(dest2) = &args.dest2 {
        println!("Destination 2: {}", dest2.display());
    }
    if let Some(dest3) = &args.dest3 {
        println!("Destination 3: {}", dest3.display());
    }
    println!("Mode: {}", mode_name(args.mode));
    println!("Checksum: {}", checksum_name(args.checksum));
    println!("Retries: {}", args.retries);
    println!("Files found: {}", files.len());
    println!("Directories found: {}", directories.len());
    println!("Total bytes: {}", total_bytes);
    if compatible_previous_report_found {
        println!("Resume: existing compatible report found, previously verified files will be skipped");
    } else if previous_report_loaded {
        println!("Resume: previous report found but not compatible, full scan will run");
    } else {
        println!("Resume: no previous report found, full scan will run");
    }
    println!();

    let job_pb = ProgressBar::new(files.len() as u64);
    job_pb.set_style(
        ProgressStyle::with_template(
            "[{elapsed_precise}] [{bar:40.cyan/blue}] {pos}/{len} files {msg}",
        )?
        .progress_chars("=>-"),
    );

    let mut file_reports = Vec::with_capacity(files.len());
    let mut skipped_files = 0usize;
    let mut failed_files = 0usize;
    let mut bytes_copied_this_run = 0u64;

    for file in &files {
        job_pb.set_message(file.relative_path.display().to_string());

        if let Some(previous) = previous_file_lookup.get(&file.relative_path) {
            if file_can_be_skipped(file, previous, &args, &destinations) {
                println!(
                    "SKIP: {} (already completed and verified in previous report)",
                    file.relative_path.display()
                );
                skipped_files += 1;
                file_reports.push(build_skipped_file_report(previous, file, &args, &destinations));
                job_pb.inc(1);
                continue;
            }
        }

        let report_template = build_empty_file_report(file, &args, &destinations);

        match process_file_with_retries(&args, file, &destinations) {
            Ok(result) => {
                bytes_copied_this_run += result.bytes_copied_this_run;
                file_reports.push(merge_file_report(report_template, result));
            }
            Err(error) => {
                failed_files += 1;
                file_reports.push(mark_failed_report(report_template, error.to_string()));
            }
        }

        job_pb.inc(1);
    }

    job_pb.finish_with_message("done");

    let completed_files = files.len().saturating_sub(failed_files);
    let retried_incomplete_or_failed_files = files.len().saturating_sub(skipped_files);
    let total_time_seconds = job_start_instant.elapsed().as_secs_f64();
    let job_finish_utc = OffsetDateTime::now_utc();
    let average_throughput_mb_per_sec = if total_time_seconds > 0.0 {
        bytes_copied_this_run as f64 / 1024.0 / 1024.0 / total_time_seconds
    } else {
        0.0
    };

    let report = JobReport {
        summary: SummaryReport {
            final_status: final_status(failed_files == 0, args.mode).to_string(),
            final_progress: "Completed".to_string(),
            size_of_offload_bytes: total_bytes,
            size_of_offload_human_readable: human_size(total_bytes),
            bytes_copied_this_run,
            bytes_copied_this_run_human_readable: human_size(bytes_copied_this_run),
            checksum_type: checksum_name(args.checksum).to_string(),
            mode: mode_name(args.mode).to_string(),
            offload_start_timestamp: format_timestamp(job_start_utc),
            offload_finish_timestamp: format_timestamp(job_finish_utc),
            total_time_seconds,
            average_throughput_mb_per_sec,
            total_files: files.len(),
            completed_files,
            skipped_files,
            failed_files,
        },
        system_details: gather_system_info(),
        source_root_name: source_root_name(&source_root_path),
        source_root_path: source_root_path.display().to_string(),
        destination_roots,
        resume: ResumeReport {
            previous_report_loaded,
            compatible_previous_report_found,
            skipped_previously_completed_files: skipped_files,
            retried_incomplete_or_failed_files,
        },
        total_directories: directories.len(),
        files: file_reports,
    };

    write_report(&args.report, &report)?;

    println!();
    println!(
        "OFFLOAD COMPLETE: {}",
        if failed_files == 0 { "PASS" } else { "FAIL" }
    );
    println!("Report written to {}", args.report.display());

    Ok(())
}

fn process_file_with_retries(
    args: &Args,
    file: &SourceFile,
    destinations: &[DestinationPlan],
) -> Result<ProcessResult> {
    let mut last_error: Option<anyhow::Error> = None;

    for attempt in 0..=args.retries {
        match process_one_file(args, file, destinations) {
            Ok(result) => return Ok(result),
            Err(error) => {
                cleanup_partial_outputs(file, destinations);
                last_error = Some(error);

                if attempt < args.retries {
                    println!(
                        "Retrying {} ({}/{})",
                        file.relative_path.display(),
                        attempt + 1,
                        args.retries
                    );
                }
            }
        }
    }

    Err(last_error.unwrap_or_else(|| anyhow!("unknown processing failure")))
}

fn process_one_file(
    args: &Args,
    file: &SourceFile,
    destinations: &[DestinationPlan],
) -> Result<ProcessResult> {
    let destination_paths: Vec<PathBuf> = destinations
        .iter()
        .map(|destination| destination.root.join(&file.relative_path))
        .collect();

    for path in &destination_paths {
        ensure_parent_directory(path)?;
    }

    println!("COPY: {}", file.relative_path.display());
    copy_to_destinations(&file.source_path, &destination_paths, file.size_bytes)?;

    let mut destination_statuses: Vec<DestinationStatus> = destination_paths
        .iter()
        .map(|path| {
            let size_bytes = fs::metadata(path).ok().map(|metadata| metadata.len());
            DestinationStatus {
                path: path.display().to_string(),
                copied: true,
                verified: false,
                checksum: None,
                size_bytes,
                status: status_after_copy(args.mode).to_string(),
            }
        })
        .collect();

    let mut source_checksum = None;

    if matches!(args.mode, RunMode::CopyThenVerify) {
        println!("VERIFY: {}", file.relative_path.display());

        let progress = MultiProgress::new();
        let src_bar = make_hash_bar(&progress, file.size_bytes, "SRC")?;
        let d1_bar = make_hash_bar(&progress, file.size_bytes, "D1 ")?;
        let d2_bar = if destination_paths.len() >= 2 {
            Some(make_hash_bar(&progress, file.size_bytes, "D2 ")?)
        } else {
            None
        };
        let d3_bar = if destination_paths.len() >= 3 {
            Some(make_hash_bar(&progress, file.size_bytes, "D3 ")?)
        } else {
            None
        };

        let checksum_type = args.checksum;
        let source_path = file.source_path.clone();
        let dest1_path = destination_paths[0].clone();
        let dest2_path = destination_paths.get(1).cloned();
        let dest3_path = destination_paths.get(2).cloned();

        let source_handle =
            thread::spawn(move || hash_file_with_progress_bar(source_path, src_bar, checksum_type));
        let dest1_handle =
            thread::spawn(move || hash_file_with_progress_bar(dest1_path, d1_bar, checksum_type));
        let dest2_handle = if let (Some(path), Some(bar)) = (dest2_path, d2_bar) {
            Some(thread::spawn(move || {
                hash_file_with_progress_bar(path, bar, checksum_type)
            }))
        } else {
            None
        };
        let dest3_handle = if let (Some(path), Some(bar)) = (dest3_path, d3_bar) {
            Some(thread::spawn(move || {
                hash_file_with_progress_bar(path, bar, checksum_type)
            }))
        } else {
            None
        };

        let source_hash = source_handle
            .join()
            .map_err(|_| anyhow!("source hash thread panicked"))??;
        let dest1_hash = dest1_handle
            .join()
            .map_err(|_| anyhow!("dest1 hash thread panicked"))??;
        let dest2_hash = if let Some(handle) = dest2_handle {
            Some(handle.join().map_err(|_| anyhow!("dest2 hash thread panicked"))??)
        } else {
            None
        };
        let dest3_hash = if let Some(handle) = dest3_handle {
            Some(handle.join().map_err(|_| anyhow!("dest3 hash thread panicked"))??)
        } else {
            None
        };

        source_checksum = Some(source_hash.clone());

        destination_statuses[0].checksum = Some(dest1_hash.clone());
        destination_statuses[0].verified = dest1_hash == source_hash;
        destination_statuses[0].status = if destination_statuses[0].verified {
            "Verified".to_string()
        } else {
            "Verification Failed".to_string()
        };

        if let Some(hash) = dest2_hash {
            destination_statuses[1].checksum = Some(hash.clone());
            destination_statuses[1].verified = hash == source_hash;
            destination_statuses[1].status = if destination_statuses[1].verified {
                "Verified".to_string()
            } else {
                "Verification Failed".to_string()
            };
        }

        if let Some(hash) = dest3_hash {
            destination_statuses[2].checksum = Some(hash.clone());
            destination_statuses[2].verified = hash == source_hash;
            destination_statuses[2].status = if destination_statuses[2].verified {
                "Verified".to_string()
            } else {
                "Verification Failed".to_string()
            };
        }
    }

    Ok(ProcessResult {
        source_checksum,
        destination_1: destination_statuses[0].clone(),
        destination_2: destination_statuses.get(1).cloned(),
        destination_3: destination_statuses.get(2).cloned(),
        error: None,
        bytes_copied_this_run: file.size_bytes,
    })
}

fn copy_to_destinations(source_path: &Path, destination_paths: &[PathBuf], size_bytes: u64) -> Result<()> {
    let file_pb = ProgressBar::new(size_bytes);
    file_pb.set_style(
        ProgressStyle::with_template(
            "  COPY [{bar:30.green/white}] {bytes}/{total_bytes} {bytes_per_sec} {eta}",
        )?
        .progress_chars("=>-"),
    );

    let source_file = File::open(source_path)
        .with_context(|| format!("failed to open source file {}", source_path.display()))?;
    let mut reader = BufReader::with_capacity(IO_BUFFER_SIZE, source_file);

    let mut writers: Vec<BufWriter<File>> = destination_paths
        .iter()
        .map(|path| {
            File::create(path)
                .map(|file| BufWriter::with_capacity(IO_BUFFER_SIZE, file))
                .with_context(|| format!("failed to create destination file {}", path.display()))
        })
        .collect::<Result<Vec<_>>>()?;

    let mut buffer = vec![0u8; IO_BUFFER_SIZE];

    loop {
        let bytes_read = reader
            .read(&mut buffer)
            .with_context(|| format!("failed reading source file {}", source_path.display()))?;

        if bytes_read == 0 {
            break;
        }

        let chunk = &buffer[..bytes_read];
        for writer in &mut writers {
            writer.write_all(chunk)?;
        }

        file_pb.inc(bytes_read as u64);
    }

    for writer in &mut writers {
        writer.flush()?;
    }

    file_pb.finish_with_message("done");
    Ok(())
}

fn hash_file_with_progress_bar(
    path: PathBuf,
    pb: ProgressBar,
    checksum_type: ChecksumType,
) -> Result<String> {
    let file = File::open(&path).with_context(|| format!("failed to open {}", path.display()))?;
    let mut reader = BufReader::with_capacity(IO_BUFFER_SIZE, file);
    let mut hasher = HasherKind::new(checksum_type);
    let mut buffer = vec![0u8; IO_BUFFER_SIZE];

    loop {
        let bytes_read = reader.read(&mut buffer)?;
        if bytes_read == 0 {
            break;
        }

        hasher.update(&buffer[..bytes_read]);
        pb.inc(bytes_read as u64);
    }

    pb.finish_with_message("done");
    Ok(hasher.finalize_hex())
}

fn make_hash_bar(progress: &MultiProgress, size_bytes: u64, label: &str) -> Result<ProgressBar> {
    let pb = progress.add(ProgressBar::new(size_bytes));
    pb.set_style(
        ProgressStyle::with_template(
            &format!(
                "  {} HASH [{{bar:30.yellow/white}}] {{bytes}}/{{total_bytes}} {{bytes_per_sec}} {{eta}}",
                label
            ),
        )?
        .progress_chars("=>-"),
    );
    Ok(pb)
}

fn validate_paths(args: &Args) -> Result<()> {
    if !args.source.exists() {
        bail!("source path does not exist: {}", args.source.display());
    }

    if !args.source.is_dir() {
        bail!("source path is not a directory: {}", args.source.display());
    }

    let source = absolute_normalized(&args.source)?;
    let mut all_paths: Vec<(&str, PathBuf)> = vec![("source", source)];
    all_paths.push(("dest1", absolute_normalized(&args.dest1)?));

    if let Some(dest2) = &args.dest2 {
        all_paths.push(("dest2", absolute_normalized(dest2)?));
    }

    if let Some(dest3) = &args.dest3 {
        all_paths.push(("dest3", absolute_normalized(dest3)?));
    }

    for i in 0..all_paths.len() {
        for j in (i + 1)..all_paths.len() {
            let (left_name, left_path) = &all_paths[i];
            let (right_name, right_path) = &all_paths[j];

            if left_path == right_path {
                bail!("{left_name} and {right_name} are the same path");
            }

            if left_path.starts_with(right_path) || right_path.starts_with(left_path) {
                bail!(
                    "{left_name} and {right_name} overlap, which is not allowed: {} <> {}",
                    left_path.display(),
                    right_path.display()
                );
            }
        }
    }

    Ok(())
}

fn ensure_destination_roots(args: &Args) -> Result<()> {
    fs::create_dir_all(&args.dest1)
        .with_context(|| format!("failed to create {}", args.dest1.display()))?;
    if !args.dest1.is_dir() {
        bail!("dest1 is not a directory: {}", args.dest1.display());
    }

    if let Some(dest2) = &args.dest2 {
        fs::create_dir_all(dest2).with_context(|| format!("failed to create {}", dest2.display()))?;
        if !dest2.is_dir() {
            bail!("dest2 is not a directory: {}", dest2.display());
        }
    }

    if let Some(dest3) = &args.dest3 {
        fs::create_dir_all(dest3).with_context(|| format!("failed to create {}", dest3.display()))?;
        if !dest3.is_dir() {
            bail!("dest3 is not a directory: {}", dest3.display());
        }
    }

    Ok(())
}

fn build_destinations(args: &Args) -> Result<Vec<DestinationPlan>> {
    let mut destinations = Vec::with_capacity(3);
    destinations.push(DestinationPlan {
        label: "dest1",
        root: absolute_normalized(&args.dest1)?,
    });

    if let Some(dest2) = &args.dest2 {
        destinations.push(DestinationPlan {
            label: "dest2",
            root: absolute_normalized(dest2)?,
        });
    }

    if let Some(dest3) = &args.dest3 {
        destinations.push(DestinationPlan {
            label: "dest3",
            root: absolute_normalized(dest3)?,
        });
    }

    Ok(destinations)
}

fn build_destination_roots_report(args: &Args) -> Result<DestinationRootsReport> {
    Ok(DestinationRootsReport {
        dest1: DestinationRootStatus {
            path: Some(absolute_normalized(&args.dest1)?.display().to_string()),
            provided: true,
        },
        dest2: DestinationRootStatus {
            path: args
                .dest2
                .as_ref()
                .map(|path| absolute_normalized(path))
                .transpose()?
                .map(|path| path.display().to_string()),
            provided: args.dest2.is_some(),
        },
        dest3: DestinationRootStatus {
            path: args
                .dest3
                .as_ref()
                .map(|path| absolute_normalized(path))
                .transpose()?
                .map(|path| path.display().to_string()),
            provided: args.dest3.is_some(),
        },
    })
}

fn collect_directories(source: &Path) -> Result<Vec<PathBuf>> {
    let mut directories = Vec::new();

    for entry in WalkDir::new(source).min_depth(1) {
        let entry = entry?;
        if entry.file_type().is_dir() {
            directories.push(entry.path().strip_prefix(source)?.to_path_buf());
        }
    }

    directories.sort();
    Ok(directories)
}

fn create_destination_directories(
    relative_directories: &[PathBuf],
    destinations: &[DestinationPlan],
) -> Result<()> {
    for destination in destinations {
        for relative in relative_directories {
            let full_path = destination.root.join(relative);
            fs::create_dir_all(&full_path)
                .with_context(|| format!("failed to create directory {}", full_path.display()))?;
        }
    }

    Ok(())
}

fn collect_files(source: &Path) -> Result<Vec<SourceFile>> {
    let mut files = Vec::new();

    for entry in WalkDir::new(source).min_depth(1) {
        let entry = entry?;
        if entry.file_type().is_file() {
            let path = entry.path().to_path_buf();
            let metadata = entry.metadata()?;
            files.push(SourceFile {
                source_path: path.clone(),
                relative_path: path.strip_prefix(source)?.to_path_buf(),
                size_bytes: metadata.len(),
                modified_unix_ms: metadata_modified_unix_ms(&metadata)?,
            });
        }
    }

    files.sort_by(|left, right| left.relative_path.cmp(&right.relative_path));
    Ok(files)
}

fn build_empty_file_report(
    file: &SourceFile,
    args: &Args,
    destinations: &[DestinationPlan],
) -> FileReport {
    let mut destination_map: BTreeMap<&str, DestinationStatus> = BTreeMap::new();

    for destination in destinations {
        let path = destination.root.join(&file.relative_path);
        destination_map.insert(
            destination.label,
            DestinationStatus {
                path: path.display().to_string(),
                copied: false,
                verified: false,
                checksum: None,
                size_bytes: None,
                status: "Pending".to_string(),
            },
        );
    }

    FileReport {
        relative_path: file.relative_path.display().to_string(),
        source_path: file.source_path.display().to_string(),
        file_size_bytes: file.size_bytes,
        source_modified_unix_ms: file.modified_unix_ms,
        checksum_type: checksum_name(args.checksum).to_string(),
        source_checksum: None,
        destination_1: destination_map
            .remove("dest1")
            .expect("dest1 should always be present"),
        destination_2: destination_map.remove("dest2"),
        destination_3: destination_map.remove("dest3"),
        error: None,
    }
}

fn merge_file_report(mut report: FileReport, result: ProcessResult) -> FileReport {
    report.source_checksum = result.source_checksum;
    report.destination_1 = result.destination_1;
    report.destination_2 = result.destination_2;
    report.destination_3 = result.destination_3;
    report.error = result.error;
    report
}

fn mark_failed_report(mut report: FileReport, error: String) -> FileReport {
    report.error = Some(error);
    report.destination_1.status = "Error".to_string();
    if let Some(dest2) = report.destination_2.as_mut() {
        dest2.status = "Error".to_string();
    }
    if let Some(dest3) = report.destination_3.as_mut() {
        dest3.status = "Error".to_string();
    }
    report
}

fn cleanup_partial_outputs(file: &SourceFile, destinations: &[DestinationPlan]) {
    for destination in destinations {
        let path = destination.root.join(&file.relative_path);
        let _ = fs::remove_file(path);
    }
}

fn ensure_parent_directory(path: &Path) -> Result<()> {
    if let Some(parent) = path.parent() {
        fs::create_dir_all(parent)
            .with_context(|| format!("failed to create directory {}", parent.display()))?;
    }
    Ok(())
}

fn load_previous_report(path: &Path) -> Option<JobReport> {
    if !path.exists() {
        return None;
    }

    let bytes = fs::read(path).ok()?;
    serde_json::from_slice(&bytes).ok()
}

fn previous_report_is_compatible(
    report: &JobReport,
    source_root_path: &Path,
    args: &Args,
    destination_roots: &DestinationRootsReport,
) -> bool {
    if normalize_path_string(&report.source_root_path).as_deref()
        != Some(source_root_path.to_string_lossy().as_ref())
    {
        return false;
    }

    if report.summary.checksum_type != checksum_name(args.checksum) {
        return false;
    }

    if report.summary.mode != mode_name(args.mode) {
        return false;
    }

    destination_root_matches(&report.destination_roots.dest1, &destination_roots.dest1)
        && destination_root_matches(&report.destination_roots.dest2, &destination_roots.dest2)
        && destination_root_matches(&report.destination_roots.dest3, &destination_roots.dest3)
}

fn destination_root_matches(previous: &DestinationRootStatus, current: &DestinationRootStatus) -> bool {
    if previous.provided != current.provided {
        return false;
    }

    match (&previous.path, &current.path) {
        (Some(previous_path), Some(current_path)) => {
            normalize_path_string(previous_path).as_deref() == Some(current_path.as_str())
        }
        (None, None) => true,
        _ => false,
    }
}

fn build_previous_file_lookup(report: &JobReport) -> BTreeMap<PathBuf, FileReport> {
    report
        .files
        .iter()
        .cloned()
        .map(|file| (PathBuf::from(&file.relative_path), file))
        .collect()
}

fn file_can_be_skipped(
    file: &SourceFile,
    previous: &FileReport,
    args: &Args,
    destinations: &[DestinationPlan],
) -> bool {
    if previous.error.is_some() {
        return false;
    }

    if previous.file_size_bytes != file.size_bytes {
        return false;
    }

    if previous.source_modified_unix_ms != file.modified_unix_ms {
        return false;
    }

    if previous.checksum_type != checksum_name(args.checksum) {
        return false;
    }

    if normalize_path_string(&previous.source_path).as_deref()
        != Some(file.source_path.to_string_lossy().as_ref())
    {
        return false;
    }

    if matches!(args.mode, RunMode::CopyThenVerify) && previous.source_checksum.is_none() {
        return false;
    }

    for destination in destinations {
        let expected_path = destination.root.join(&file.relative_path);
        let previous_status = match destination.label {
            "dest1" => Some(&previous.destination_1),
            "dest2" => previous.destination_2.as_ref(),
            "dest3" => previous.destination_3.as_ref(),
            _ => None,
        };

        let Some(status) = previous_status else {
            return false;
        };

        if normalize_path_string(&status.path).as_deref()
            != Some(expected_path.to_string_lossy().as_ref())
        {
            return false;
        }

        if !status.copied {
            return false;
        }

        if matches!(args.mode, RunMode::CopyThenVerify) && !status.verified {
            return false;
        }

        if matches!(args.mode, RunMode::CopyThenVerify) && status.checksum.is_none() {
            return false;
        }

        if !expected_path.exists() {
            return false;
        }

        let Ok(metadata) = fs::metadata(&expected_path) else {
            return false;
        };

        if metadata.len() != file.size_bytes {
            return false;
        }
    }

    true
}

fn build_skipped_file_report(
    previous: &FileReport,
    file: &SourceFile,
    args: &Args,
    destinations: &[DestinationPlan],
) -> FileReport {
    let mut report = previous.clone();
    report.relative_path = file.relative_path.display().to_string();
    report.source_path = file.source_path.display().to_string();
    report.file_size_bytes = file.size_bytes;
    report.source_modified_unix_ms = file.modified_unix_ms;
    report.checksum_type = checksum_name(args.checksum).to_string();
    report.error = None;

    for destination in destinations {
        let expected_path = destination.root.join(&file.relative_path);
        let status = match destination.label {
            "dest1" => &mut report.destination_1,
            "dest2" => report
                .destination_2
                .as_mut()
                .expect("dest2 report should exist when skipping"),
            "dest3" => report
                .destination_3
                .as_mut()
                .expect("dest3 report should exist when skipping"),
            _ => continue,
        };

        status.path = expected_path.display().to_string();
        status.size_bytes = fs::metadata(&expected_path).ok().map(|metadata| metadata.len());
        status.status = if matches!(args.mode, RunMode::CopyThenVerify) {
            "Skipped (already verified)".to_string()
        } else {
            "Skipped (already copied)".to_string()
        };
    }

    report
}

fn gather_system_info() -> SystemInfoReport {
    let mut system = System::new_all();
    system.refresh_all();

    let os_name = System::name().unwrap_or_else(|| "Unknown".to_string());
    let os_version = System::os_version().unwrap_or_default();
    let operating_system = if os_version.is_empty() {
        os_name
    } else {
        format!("{os_name} {os_version}")
    };

    let total_ram_gb = round_two(system.total_memory() as f64 / 1024.0 / 1024.0 / 1024.0);

    SystemInfoReport {
        operating_system,
        logical_processors: num_cpus::get(),
        total_ram_gb,
        app_version: env!("CARGO_PKG_VERSION").to_string(),
    }
}

fn write_report(path: &Path, report: &JobReport) -> Result<()> {
    if let Some(parent) = path.parent() {
        if !parent.as_os_str().is_empty() {
            fs::create_dir_all(parent)
                .with_context(|| format!("failed to create report directory {}", parent.display()))?;
        }
    }

    let bytes = serde_json::to_vec_pretty(report)?;
    fs::write(path, bytes).with_context(|| format!("failed to write report {}", path.display()))?;
    Ok(())
}

fn absolute_normalized(path: &Path) -> Result<PathBuf> {
    let absolute = if path.is_absolute() {
        path.to_path_buf()
    } else {
        std::env::current_dir()?.join(path)
    };

    normalize_components(&absolute)
}

fn normalize_components(path: &Path) -> Result<PathBuf> {
    let mut normalized = PathBuf::new();

    for component in path.components() {
        match component {
            Component::Prefix(prefix) => normalized.push(prefix.as_os_str()),
            Component::RootDir => normalized.push(Path::new(std::path::MAIN_SEPARATOR_STR)),
            Component::CurDir => {}
            Component::ParentDir => {
                if !normalized.pop() {
                    bail!("could not normalize path {}", path.display());
                }
            }
            Component::Normal(part) => normalized.push(part),
        }
    }

    Ok(normalized)
}

fn normalize_path_string(path: &str) -> Option<String> {
    absolute_normalized(Path::new(path))
        .ok()
        .map(|path| path.display().to_string())
}

fn metadata_modified_unix_ms(metadata: &fs::Metadata) -> Result<u128> {
    let modified = metadata.modified()?;
    Ok(system_time_to_unix_ms(modified))
}

fn system_time_to_unix_ms(time: SystemTime) -> u128 {
    time.duration_since(UNIX_EPOCH)
        .unwrap_or_default()
        .as_millis()
}

fn source_root_name(source: &Path) -> String {
    source
        .file_name()
        .map(|part| part.to_string_lossy().to_string())
        .filter(|name| !name.is_empty())
        .unwrap_or_else(|| source.display().to_string())
}

fn checksum_name(checksum: ChecksumType) -> &'static str {
    match checksum {
        ChecksumType::Xxh3 => "xxh3",
        ChecksumType::Md5 => "md5",
        ChecksumType::Sha256 => "sha256",
    }
}

fn mode_name(mode: RunMode) -> &'static str {
    match mode {
        RunMode::CopyThenVerify => "copy-then-verify",
        RunMode::CopyOnly => "copy-only",
    }
}

fn final_status(success: bool, mode: RunMode) -> &'static str {
    if !success {
        "Failed"
    } else {
        match mode {
            RunMode::CopyThenVerify => "Verified",
            RunMode::CopyOnly => "Copied",
        }
    }
}

fn status_after_copy(mode: RunMode) -> &'static str {
    match mode {
        RunMode::CopyThenVerify => "Copied Waiting For Verification",
        RunMode::CopyOnly => "Copied",
    }
}

fn human_size(bytes: u64) -> String {
    let value = bytes as f64;
    let kb = 1024.0;
    let mb = kb * 1024.0;
    let gb = mb * 1024.0;
    let tb = gb * 1024.0;

    if value >= tb {
        format!("{:.2} TB", value / tb)
    } else if value >= gb {
        format!("{:.2} GB", value / gb)
    } else if value >= mb {
        format!("{:.2} MB", value / mb)
    } else if value >= kb {
        format!("{:.2} KB", value / kb)
    } else {
        format!("{bytes} bytes")
    }
}

fn format_timestamp(timestamp: OffsetDateTime) -> String {
    timestamp
        .format(&Rfc3339)
        .unwrap_or_else(|_| "1970-01-01T00:00:00Z".to_string())
}

fn round_two(value: f64) -> f64 {
    (value * 100.0).round() / 100.0
}
