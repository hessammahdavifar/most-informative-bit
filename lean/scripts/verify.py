#!/usr/bin/env python3
"""Build the Lean project and reject unexpected axioms in Check.lean's audit."""
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
REQUIRED_THEOREMS = {
    "MostInformativeBit.general_courtade_kumar",
    "MostInformativeBit.courtade_kumar_bits",
    "MostInformativeBit.courtade_kumar",
    "MostInformativeBit.source_theorem",
}


def check_audit(output, expected):
    reports = re.findall(r"'([^']+)' depends on axioms: \[([^]]*)\]", output, re.S)
    names = [name for name, _ in reports]
    if len(names) != len(set(names)) or set(names) != expected:
        raise ValueError("Axiom audit is incomplete or contains unexpected declarations.")
    if not REQUIRED_THEOREMS <= expected:
        raise ValueError("Check.lean must audit all final theorems.")
    for name, raw in reports:
        axioms = {a for a in re.split(r"[,\s]+", raw.strip()) if a}
        unexpected = axioms - ALLOWED_AXIOMS
        if unexpected:
            raise ValueError(f"{name}: unexpected axioms {sorted(unexpected)}")
    return len(reports)


def main():
    if shutil.which("lake") is None:
        raise RuntimeError("lake is not on PATH. Install Lean through elan; see README.md.")
    expected = set(re.findall(r"^#print axioms (\S+)",
                             (ROOT / "Check.lean").read_text(), re.M))
    subprocess.run(["lake", "build"], cwd=ROOT, check=True)
    result = subprocess.run(["lake", "env", "lean", "Check.lean"], cwd=ROOT,
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    count = check_audit(result.stdout, expected)
    print(f"PASS: build and {count} axiom audits; only propext, Classical.choice, Quot.sound.")


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, ValueError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        sys.exit(1)
