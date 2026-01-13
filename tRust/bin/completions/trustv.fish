# Fish completion for trustv
# Install: cp trustv.fish ~/.config/fish/completions/

# trustv-specific options
complete -c trustv -s v -l verbose -d 'Enable verbose verification output'
complete -c trustv -l profile -d 'Show verification timing breakdown'
complete -c trustv -l output-format -xa 'human json' -d 'Output format'
complete -c trustv -l no-cache -d 'Disable verification caching'
complete -c trustv -l use-global-cache -d 'Enable global cache shared across projects'
complete -c trustv -l explain -xa 'E0900 E0901 E0902 E0903 E0904 E0905 E0906 E0907 E0908 E0909' -d 'Explain verification error code'
complete -c trustv -s h -l help -d 'Show help message'

# Complete .rs files by default
complete -c trustv -xa '(__fish_complete_suffix .rs)'
