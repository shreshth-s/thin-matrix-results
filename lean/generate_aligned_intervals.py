#!/usr/bin/env python3
"""Check compact Lean boxes against the Python rational interval computation.

This is a reproducibility aid, not a proof that the intervals enclose real logs.
The real-log/entropy interpretation is not supplied by this Python script.
It prints boxes and checks exact rational containment; it writes no files.
"""
from fractions import Fraction as F
from contextlib import redirect_stdout
import io
from pathlib import Path
import re
import runpy
import sys

if not __debug__:
    raise SystemExit("Run interval generation with Python assertions enabled.")

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE.parent / "outputs"))


def main():
    # Execute the actual canonical numerical verifier with its bundled interval
    # helper. Its 47 comparisons run normally; only the verbose stdout is hidden.
    canonical = HERE.parent / "outputs" / "verify_five_term_aligned_apsp.py"
    with redirect_stdout(io.StringIO()):
        actual = runpy.run_path(str(canonical))
    source = (HERE / "AlignedCertificate.lean").read_text()
    for name in ("c", "theta", "b", "delta", "R", "S"):
        if name in ("R", "S"):
            pattern = rf"def {name} : Nat := ([\d_]+)"
            match = re.search(pattern, source)
            lean_value = int(match[1].replace("_", "")) if match else None
        else:
            pattern = rf"def {name} : Rat := ([\d_]+) / ([\d_]+)"
            match = re.search(pattern, source)
            lean_value = (F(int(match[1].replace("_", "")),
                            int(match[2].replace("_", ""))) if match else None)
        if lean_value is None or lean_value != actual[name]:
            raise AssertionError(f"Lean witness constant differs from canonical verifier: {name}")
        print(f"PASS canonical witness {name} = {lean_value}")
    scale = 10**15
    for name, interval in (("t", actual["T"]), ("g", actual["G"]), ("q", actual["q1"])):
        lo = (interval.lo*scale).__floor__()
        hi = (interval.hi*scale).__ceil__()
        rounded_lo, rounded_hi = F(lo, scale), F(hi, scale)
        if not rounded_lo <= interval.lo <= interval.hi <= rounded_hi:
            raise AssertionError(f"Outward containment failed for {name}")
        for suffix, numerator in (("Lo", lo), ("Hi", hi)):
            pattern = rf"def {name}{suffix} : Rat := (\d+) / (\d+)"
            match = re.search(pattern, source)
            if match is None or F(int(match[1]), int(match[2])) != F(numerator, scale):
                raise AssertionError(f"Lean box differs for {name}{suffix}")
        print(f"PASS {name}: [{lo}/{scale}, {hi}/{scale}] contains Python rational interval")
    print("PASS compact boxes agree with Lean declarations; no real-log theorem is asserted here.")


if __name__ == "__main__":
    main()
