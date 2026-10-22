#!/usr/bin/env python3
"""Replay the published structured-source finite checks and saved outputs."""
from pathlib import Path
import subprocess
import sys


def main():
    if not __debug__:
        raise SystemExit("Verification requires assertions; do not use optimized Python.")
    root = Path(__file__).resolve().parents[1]
    entries = (
        ('light-source-improvement/check_exact_small_bias.py', 'exact-small-bias-results.txt'),
        ('light-source-improvement/check_small_bias_potential.py', 'small-bias-potential-results.txt'),
        ('light-source-improvement/check_light_gauge_embedding.py', 'light-gauge-embedding-results.txt'),
        ('light-source-improvement/check_light_source_gauges.py', 'light-source-gauges-results.txt'),
        ('light-source-improvement/check_strict_light_gauge_backend.py', 'strict-light-gauge-backend-results.txt'),
        ('cropped-source-improvement/check_rectangular_chunks.py', 'rectangular-chunks-results.txt'),
        ('half-source-improvement/check_half_bias.py', 'half-bias-results.txt'),
        ('half-source-improvement/check_half_embedding.py', 'half-embedding-results.txt'),
    )
    for script, saved in entries:
        path = root / "work" / script
        result = subprocess.run([sys.executable, "-E", str(path)], cwd=root,
                                check=True, capture_output=True, text=True)
        if result.stdout != path.with_name(saved).read_text():
            raise SystemExit(f"Saved output mismatch: {script}")
        print(f"PASS {script}: saved output reproduced", flush=True)
    print("PASS: structured-source finite checks; asymptotic proofs remain separate.")


if __name__ == "__main__":
    main()
