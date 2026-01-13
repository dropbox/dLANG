// Level 3 Test: File I/O
// Tests: reading, writing, paths, temp files

use std::fs::{self, File};
use std::io::{self, BufRead, BufReader, BufWriter, Read, Write};
use std::path::Path;

fn main() -> io::Result<()> {
    // Create a temp directory for our tests
    let test_dir = std::env::temp_dir().join("trust_level3_file_io_test");
    let _ = fs::remove_dir_all(&test_dir);
    fs::create_dir_all(&test_dir)?;

    println!("=== Write and Read ===");
    let test_file = test_dir.join("test.txt");

    // Write to file
    {
        let mut file = File::create(&test_file)?;
        file.write_all(b"Hello, World!\nLine 2\nLine 3\n")?;
    }
    println!("Created: {}", test_file.display());

    // Read entire file to string
    let contents = fs::read_to_string(&test_file)?;
    println!("Read {} bytes", contents.len());
    print!("Contents:\n{}", contents);

    // Read line by line
    println!("=== Read Line by Line ===");
    {
        let file = File::open(&test_file)?;
        let reader = BufReader::new(file);
        for (i, line) in reader.lines().enumerate() {
            let line = line?;
            println!("Line {}: {}", i + 1, line);
        }
    }

    // Append to file
    println!("\n=== Append ===");
    {
        let mut file = fs::OpenOptions::new()
            .append(true)
            .open(&test_file)?;
        writeln!(file, "Appended line")?;
    }
    let new_contents = fs::read_to_string(&test_file)?;
    println!("After append ({} bytes):\n{}", new_contents.len(), new_contents);

    // Binary file I/O
    println!("=== Binary I/O ===");
    let bin_file = test_dir.join("binary.bin");
    {
        let mut file = File::create(&bin_file)?;
        let data: Vec<u8> = (0..=255u8).collect();
        file.write_all(&data)?;
    }
    let bin_data = fs::read(&bin_file)?;
    println!("Binary file size: {} bytes", bin_data.len());
    println!("First 10 bytes: {:?}", &bin_data[..10]);
    println!("Last 10 bytes: {:?}", &bin_data[246..]);

    // Buffered writing
    println!("\n=== Buffered I/O ===");
    let buffered_file = test_dir.join("buffered.txt");
    {
        let file = File::create(&buffered_file)?;
        let mut writer = BufWriter::new(file);
        for i in 0..100 {
            writeln!(writer, "Line {}", i)?;
        }
        writer.flush()?;
    }
    let metadata = fs::metadata(&buffered_file)?;
    println!("Buffered file size: {} bytes", metadata.len());

    // Directory operations
    println!("\n=== Directory Operations ===");
    let sub_dir = test_dir.join("subdir");
    fs::create_dir(&sub_dir)?;
    println!("Created directory: {}", sub_dir.display());

    // Create files in subdir
    fs::write(sub_dir.join("a.txt"), "File A")?;
    fs::write(sub_dir.join("b.txt"), "File B")?;
    fs::write(sub_dir.join("c.txt"), "File C")?;

    // Read directory
    print!("Directory contents: ");
    let mut entries: Vec<_> = fs::read_dir(&sub_dir)?
        .filter_map(|e| e.ok())
        .map(|e| e.file_name().to_string_lossy().to_string())
        .collect();
    entries.sort();
    for entry in entries {
        print!("{} ", entry);
    }
    println!();

    // Path operations
    println!("\n=== Path Operations ===");
    let path = Path::new("/usr/local/bin/program.txt");
    println!("Path: {}", path.display());
    println!("file_name: {:?}", path.file_name());
    println!("file_stem: {:?}", path.file_stem());
    println!("extension: {:?}", path.extension());
    println!("parent: {:?}", path.parent().map(|p| p.display().to_string()));
    println!("is_absolute: {}", path.is_absolute());

    // File metadata
    println!("\n=== File Metadata ===");
    let meta = fs::metadata(&test_file)?;
    println!("is_file: {}", meta.is_file());
    println!("is_dir: {}", meta.is_dir());
    println!("len: {}", meta.len());
    println!("readonly: {}", meta.permissions().readonly());

    // Copy and rename
    println!("\n=== Copy and Rename ===");
    let copy_dest = test_dir.join("copy.txt");
    fs::copy(&test_file, &copy_dest)?;
    println!("Copied {} -> {}", test_file.display(), copy_dest.display());

    let rename_dest = test_dir.join("renamed.txt");
    fs::rename(&copy_dest, &rename_dest)?;
    println!("Renamed {} -> {}", copy_dest.display(), rename_dest.display());

    // Check file existence
    println!("\n=== Existence Checks ===");
    println!("test.txt exists: {}", test_file.exists());
    println!("copy.txt exists: {}", copy_dest.exists());
    println!("renamed.txt exists: {}", rename_dest.exists());

    // Cleanup
    println!("\n=== Cleanup ===");
    fs::remove_dir_all(&test_dir)?;
    println!("Removed test directory: {}", test_dir.display());

    Ok(())
}
