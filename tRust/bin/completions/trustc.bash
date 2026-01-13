# Bash completion for trustc
# Source this file or add to /etc/bash_completion.d/

_trustc() {
    local cur prev opts
    COMPREPLY=()
    cur="${COMP_WORDS[COMP_CWORD]}"
    prev="${COMP_WORDS[COMP_CWORD-1]}"

    # trustc-specific options
    local trustc_opts="--no-verify --verify-verbose --profile --output-format --explain --no-cache --no-function-cache --cache-clear --use-global-cache --global-cache-clear --cache-stats --help"

    # Common rustc options
    local rustc_opts="-o --out-dir --edition --crate-type --crate-name --emit --target --sysroot"

    # Error codes for --explain
    local error_codes="E0900 E0901 E0902 E0903 E0904 E0905 E0906 E0907 E0908 E0909"

    case "${prev}" in
        --explain)
            COMPREPLY=( $(compgen -W "${error_codes}" -- ${cur}) )
            return 0
            ;;
        --output-format)
            COMPREPLY=( $(compgen -W "human json" -- ${cur}) )
            return 0
            ;;
        --crate-type)
            COMPREPLY=( $(compgen -W "bin lib rlib dylib cdylib staticlib proc-macro" -- ${cur}) )
            return 0
            ;;
        --edition)
            COMPREPLY=( $(compgen -W "2015 2018 2021 2024" -- ${cur}) )
            return 0
            ;;
        --emit)
            COMPREPLY=( $(compgen -W "asm llvm-bc llvm-ir obj link metadata mir dep-info" -- ${cur}) )
            return 0
            ;;
        -o|--out-dir|--sysroot)
            # File/directory completion
            COMPREPLY=( $(compgen -f -- ${cur}) )
            return 0
            ;;
    esac

    # Complete options or files
    if [[ ${cur} == -* ]]; then
        COMPREPLY=( $(compgen -W "${trustc_opts} ${rustc_opts}" -- ${cur}) )
    else
        # Complete .rs files
        COMPREPLY=( $(compgen -f -X '!*.rs' -- ${cur}) $(compgen -d -- ${cur}) )
    fi
}

complete -F _trustc trustc
