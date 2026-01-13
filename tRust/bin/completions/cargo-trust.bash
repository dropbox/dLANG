# Bash completion for cargo-trust
# Source this file or add to /etc/bash_completion.d/

_cargo_trust() {
    local cur prev opts
    COMPREPLY=()
    cur="${COMP_WORDS[COMP_CWORD]}"
    prev="${COMP_WORDS[COMP_CWORD-1]}"

    # cargo-trust specific options
    local trust_opts="--no-verify --verbose --profile --output-format --help"

    # cargo subcommands that work with cargo trust
    local cargo_cmds="build run check test bench doc"

    case "${prev}" in
        --output-format)
            COMPREPLY=( $(compgen -W "human json" -- ${cur}) )
            return 0
            ;;
        trust)
            COMPREPLY=( $(compgen -W "${cargo_cmds} ${trust_opts}" -- ${cur}) )
            return 0
            ;;
    esac

    # After a cargo command, suggest trust opts and cargo opts
    if [[ ${cur} == -* ]]; then
        COMPREPLY=( $(compgen -W "${trust_opts} --release --features --all-features" -- ${cur}) )
    else
        COMPREPLY=( $(compgen -W "${cargo_cmds}" -- ${cur}) )
    fi
}

complete -F _cargo_trust cargo-trust
# Also register for "cargo trust" subcommand if possible
