# Bash completion for trustv
# Source this file or add to /etc/bash_completion.d/

_trustv() {
    local cur prev opts
    COMPREPLY=()
    cur="${COMP_WORDS[COMP_CWORD]}"
    prev="${COMP_WORDS[COMP_CWORD-1]}"

    # trustv-specific options
    local trustv_opts="--verbose -v --profile --output-format --explain --no-cache --use-global-cache --help -h"

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
    esac

    # Complete options or files
    if [[ ${cur} == -* ]]; then
        COMPREPLY=( $(compgen -W "${trustv_opts}" -- ${cur}) )
    else
        # Complete .rs files
        COMPREPLY=( $(compgen -f -X '!*.rs' -- ${cur}) $(compgen -d -- ${cur}) )
    fi
}

complete -F _trustv trustv
