#!/usr/bin/env python3

import os
import sys


def main() -> None:
    repo_root = os.path.dirname(os.path.abspath(__file__))
    rustc_dir = os.path.join(repo_root, "upstream", "rustc")
    upstream_x = os.path.join(rustc_dir, "x.py")

    if not os.path.exists(upstream_x):
        sys.stderr.write(
            "error: upstream rustc not found at 'upstream/rustc'.\n"
            "hint: run 'git submodule update --init --recursive'\n"
        )
        raise SystemExit(1)

    os.chdir(rustc_dir)
    os.execv(sys.executable, [sys.executable, upstream_x, *sys.argv[1:]])


if __name__ == "__main__":
    main()

