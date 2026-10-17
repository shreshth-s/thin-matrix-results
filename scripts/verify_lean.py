#!/usr/bin/env python3
"""Check the scoped Lean proofs and report their kernel axiom dependencies.

This is separate from the standard-library numerical/finite Python suite.
See lean/README.md for the statements covered and the remaining proof gaps.
"""
from pathlib import Path
import re
import shutil
import subprocess
import sys


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    subprocess.run(
        [sys.executable, "-E", str(root / "lean" / "generate_aligned_intervals.py")],
        cwd=root, check=True,
    )
    lake = shutil.which("lake")
    if lake is None:
        candidate = Path.home() / ".elan" / "bin" / "lake"
        if candidate.is_file():
            lake = str(candidate)
    if lake is None:
        raise SystemExit("Lean/Lake is required; see lean/README.md.")
    version = subprocess.check_output(
        [lake, "env", "lean", "--short-version"], cwd=root, text=True
    ).strip()
    if version != "4.31.0":
        raise SystemExit(f"Expected pinned Lean 4.31.0; found {version}.")
    print(f"Lean {version}; pinned mathlib from lake-manifest.json", flush=True)
    # Emit only our local imports. A broad `lake build` can trigger unrelated
    # dependency build tasks; the pinned mathlib cache supplies its imports.
    build = root / ".lake" / "build" / "lib" / "lean"
    build.mkdir(parents=True, exist_ok=True)
    allowed_axioms = {"propext", "Classical.choice", "Quot.sound"}
    checked = 0
    for filename in ("LocalIdentities.lean", "AlignedCertificate.lean", "RealCertificate.lean"):
        path = root / "lean" / filename
        print(f"\n{path.relative_to(root)}", flush=True)
        result = subprocess.run(
            [lake, "env", "lean", "-DwarningAsError=true",
             "-o", str(build / (path.stem + ".olean")), str(path)],
            cwd=root, capture_output=True, text=True,
        )
        print(result.stdout, end="", flush=True)
        if result.stderr:
            print(result.stderr, end="", flush=True)
        result.check_returncode()
        reports = re.findall(r"depends on axioms: \[([^\]]*)\]", result.stdout)
        reports += [""] * result.stdout.count("does not depend on any axioms")
        declarations = len(re.findall(r"^#print axioms ", path.read_text(), re.MULTILINE))
        if not declarations or len(reports) != declarations:
            raise SystemExit(f"Missing axiom reports in {filename}.")
        for report in reports:
            axioms = {name.strip() for name in report.split(",") if name.strip()}
            if not axioms <= allowed_axioms:
                raise SystemExit(f"Unapproved axiom dependency: {sorted(axioms - allowed_axioms)}")
        checked += declarations
    print(f"\nPASS: {checked} scoped declarations checked; only standard Lean axioms.")
    print("The complete embeddings, cache costs, reductions and APSP theorem are not formalized.")


if __name__ == "__main__":
    main()
