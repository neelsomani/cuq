#!/usr/bin/env python3
"""Minimal MIR to Coq translator stub.

This placeholder sets up argument parsing and basic file scanning so that we can
start wiring real pattern recognisers for the MIR snippets used in the examples.
"""

from __future__ import annotations

import argparse
import sys
from pathlib import Path


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description="Translate a MIR dump into Coq")
    parser.add_argument("input", type=Path, help="Path to the .mir dump produced by rustc")
    parser.add_argument(
        "--module-name",
        default="MirProgram",
        help="Name of the generated Coq module (default: %(default)s)",
    )
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    if not args.input.exists():
        print(f"error: {args.input} does not exist", file=sys.stderr)
        return 1

    source = args.input.read_text()

    print(f"(* Generated from {args.input.name} *)")
    print(f"Module {args.module_name}.\n")
    print("(* TODO: implement translation of MIR statements to MIRSyntax terms. *)")
    print("Definition placeholder : bool := true.")
    print("\nEnd " + args.module_name + ".")
    return 0


if __name__ == "__main__":
    sys.exit(main())
