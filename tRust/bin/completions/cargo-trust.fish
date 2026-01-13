# Fish completion for cargo-trust
# Install: cp cargo-trust.fish ~/.config/fish/completions/

# Subcommands
complete -c cargo-trust -n '__fish_use_subcommand' -xa build -d 'Build project with verification'
complete -c cargo-trust -n '__fish_use_subcommand' -xa run -d 'Build and run project with verification'
complete -c cargo-trust -n '__fish_use_subcommand' -xa check -d 'Check project with verification (no codegen)'
complete -c cargo-trust -n '__fish_use_subcommand' -xa test -d 'Run tests with verification'
complete -c cargo-trust -n '__fish_use_subcommand' -xa bench -d 'Run benchmarks with verification'
complete -c cargo-trust -n '__fish_use_subcommand' -xa doc -d 'Build documentation'

# cargo-trust specific options (work for all subcommands)
complete -c cargo-trust -l no-verify -d 'Disable verification (use standard rustc)'
complete -c cargo-trust -l verbose -d 'Enable verbose verification output'
complete -c cargo-trust -l profile -d 'Show verification timing breakdown'
complete -c cargo-trust -l output-format -xa 'human json' -d 'Output format'
complete -c cargo-trust -s h -l help -d 'Show help message'

# Common cargo options
complete -c cargo-trust -l release -d 'Build in release mode'
complete -c cargo-trust -l features -x -d 'Enable features'
complete -c cargo-trust -l all-features -d 'Enable all features'
complete -c cargo-trust -l no-default-features -d 'Disable default features'
complete -c cargo-trust -s p -l package -x -d 'Package to build'
complete -c cargo-trust -l target -x -d 'Target triple'
complete -c cargo-trust -l target-dir -ra '(__fish_complete_directories)' -d 'Target directory'
complete -c cargo-trust -s j -l jobs -x -d 'Number of parallel jobs'

# cargo subcommand for 'cargo trust'
complete -c cargo -n '__fish_seen_subcommand_from trust' -xa build -d 'Build with verification'
complete -c cargo -n '__fish_seen_subcommand_from trust' -xa run -d 'Run with verification'
complete -c cargo -n '__fish_seen_subcommand_from trust' -xa check -d 'Check with verification'
complete -c cargo -n '__fish_seen_subcommand_from trust' -xa test -d 'Test with verification'
