# Fish completion for trustc
# Install: cp trustc.fish ~/.config/fish/completions/

# trustc-specific options
complete -c trustc -l no-verify -d 'Compile without running verification'
complete -c trustc -l verify-verbose -d 'Enable verbose verification output'
complete -c trustc -l profile -d 'Show verification timing breakdown'
complete -c trustc -l output-format -xa 'human json' -d 'Output format'
complete -c trustc -l no-cache -d 'Disable all verification caching'
complete -c trustc -l no-function-cache -d 'Disable function-level caching only'
complete -c trustc -l cache-clear -d 'Clear project verification cache and exit'
complete -c trustc -l use-global-cache -d 'Enable global cache shared across projects'
complete -c trustc -l global-cache-clear -d 'Clear both project and global caches and exit'
complete -c trustc -l cache-stats -d 'Show verification cache statistics'
complete -c trustc -l explain -xa 'E0900 E0901 E0902 E0903 E0904 E0905 E0906 E0907 E0908 E0909' -d 'Explain verification error code'
complete -c trustc -s h -l help -d 'Show help message'

# Common rustc options
complete -c trustc -s o -r -d 'Write output to FILENAME'
complete -c trustc -l out-dir -ra '(__fish_complete_directories)' -d 'Write output to DIR'
complete -c trustc -l edition -xa '2015 2018 2021 2024' -d 'Set Rust edition'
complete -c trustc -l crate-type -xa 'bin lib rlib dylib cdylib staticlib proc-macro' -d 'Type of crate to build'
complete -c trustc -l crate-name -x -d 'Specify the name of the crate'
complete -c trustc -l emit -xa 'asm llvm-bc llvm-ir obj link metadata mir dep-info' -d 'Types of output to emit'
complete -c trustc -l target -x -d 'Target triple'
complete -c trustc -l sysroot -ra '(__fish_complete_directories)' -d 'Override the system root'

# Complete .rs files by default
complete -c trustc -xa '(__fish_complete_suffix .rs)'
