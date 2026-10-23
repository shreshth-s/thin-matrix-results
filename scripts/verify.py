#!/usr/bin/env python3
"""Run the repository's standard-library verification suite from any directory."""
from pathlib import Path
import subprocess
import sys


def main() -> None:
    if not __debug__:
        raise SystemExit("Verification requires assertions; run Python without -O/-OO or PYTHONOPTIMIZE.")
    root = Path(__file__).resolve().parents[1]
    for script, recorded in (
        ("verify_exponents.py", "certificate-results.txt"),
        ("verify_subset_convolution.py", "subset-certificate-results.txt"),
        ("verify_deterministic_apsp.py", "deterministic-apsp-certificate-results.txt"),
        ("verify_five_term_apsp.py", "five-term-apsp-certificate-results.txt"),
        ("verify_five_term_ring_apsp.py", "five-term-ring-apsp-certificate-results.txt"),
        ("verify_five_term_cache_apsp.py", "five-term-cache-apsp-certificate-results.txt"),
        ("verify_five_term_aligned_apsp.py", "five-term-aligned-apsp-certificate-results.txt"),
        ("verify_light_source_apsp.py", "light-source-apsp-certificate-results.txt"),
        ("verify_half_source_apsp.py", "half-source-apsp-certificate-results.txt"),
        ("verify_cyclic_3sum.py", "cyclic-3sum-certificate-results.txt"),
        ("verify_five_term_realinput.py", "five-term-realinput-certificate-results.txt"),
        ("verify_five_term_convolution.py", "five-term-convolution-certificate-results.txt"),
        ("verify_five_term_subset.py", "five-term-subset-certificate-results.txt"),
        ("verify_directed_apsp.py", "directed-apsp-certificate-results.txt"),
        ("verify_cyclic_3xor.py", "cyclic-3xor-certificate-results.txt"),
    ):
        certificate = subprocess.run(
            [sys.executable, "-E", str(root / "outputs" / script)], cwd=root, check=True,
            capture_output=True, text=True,
        )
        print(certificate.stdout, end="", flush=True)
        expected = (root / "outputs" / recorded).read_text()
        if certificate.stdout != expected:
            raise SystemExit(f"Certificate output differs from outputs/{recorded}")
    for script in (
        "check_half_source_integer.py", "check_grouped_completion.py", "check_cw_polynomial.py", "check_cw_interpolation.py", "check_cw_block_extraction.py", "check_cw_hash_counting.py", "check_cw_type_regularity.py", "check_modular_behrend.py", "check_cw_entropy_rate.py", "check_equal_copy_recursion.py", "check_retained_recursion.py",
        "check_pruned_encoding.py", "check_reductions.py",
        "check_modular_moments.py", "check_prefix_counts.py",
        "check_rectangular_reductions.py", "check_3sum_counts.py",
        "check_subset_convolution.py", "check_direct_sum_tiling.py",
        "check_aggregated_queries.py", "check_lazy_encoding.py",
        "check_five_term.py", "check_five_term_oracle.py",
        "check_five_term_profile.py", "check_five_term_profile_maps.py",
        "check_five_term_ring.py",
        "check_five_term_cache.py",
        "check_five_term_aligned_embedding.py", "check_five_term_aligned_cache.py",
        "check_five_term_aligned_integration.py",
        "check_composite_fold.py", "check_composite_halving.py",
        "check_exact_counting.py", "check_signed_window_counts.py",
        "check_fixed_bucket_counting.py",
        "check_fixed_linear_bucket_counting.py",
    ):
        subprocess.run([sys.executable, "-E", str(root / "outputs" / script)], cwd=root, check=True)
    subprocess.run([sys.executable, "-E", str(root / "scripts/verify_structured_sources.py")],
                   cwd=root, check=True)
    print("PASS: all checks passed; stored certificate output reproduced.", flush=True)


if __name__ == "__main__":
    main()
