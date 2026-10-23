#!/usr/bin/env python3
"""Check the scoped Lean proofs and report their kernel axiom dependencies.

This is separate from the standard-library numerical/finite Python suite.
See lean/README.md for the statements covered and the remaining proof gaps.
"""
from pathlib import Path
import hashlib
import json
import re
import shutil
import subprocess
import sys


def module_order(directory: Path) -> list[Path]:
    """Compile every local module, with its local imports first."""
    modules = {path.stem: path for path in directory.glob("*.lean")}
    imports = {}
    for name, path in modules.items():
        imports[name] = set()
        for line in path.read_text().splitlines():
            match = re.match(r"^(?:public\s+)?import\s+([^\n]+)", line)
            if match:
                imports[name].update(
                    token for token in match[1].split() if token in modules
                )
    order, visited, pending = [], set(), set()

    def visit(name: str) -> None:
        if name in visited:
            return
        if name in pending:
            raise SystemExit(f"Local Lean import cycle involving {name}.")
        pending.add(name)
        for dependency in sorted(imports[name]):
            visit(dependency)
        pending.remove(name)
        visited.add(name)
        order.append(modules[name])

    for name in sorted(modules):
        visit(name)
    return order


def source_snapshot(root: Path) -> dict[str, str]:
    """Identify the exact checked source/configuration, excluding build output."""
    paths = list((root / "lean").glob("*.lean"))
    paths += [root / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json",
        "scripts/verify_lean.py", "lean/generate_aligned_intervals.py",
        "outputs/verify_five_term_aligned_apsp.py", "outputs/verify_exponents.py",
        "outputs/verify_half_source_apsp.py", "outputs/check_half_source_integer.py", "scripts/verify.py",
        "scripts/check_half_source_binary.lean",
        "outputs/check_grouped_completion.py", "scripts/check_grouped_completion.lean",
        "scripts/check_grouped_preparation.lean", "scripts/check_binary_grouped.lean",
        "scripts/check_cropped_high.lean", "scripts/check_cyclic_window.lean",
        "scripts/check_distinguished_root.lean", "scripts/check_binary_residual.lean",
        "scripts/check_complete_residual.lean", "scripts/check_exact_half_sources.lean",
        "scripts/check_residual_families.lean", "scripts/check_root_windows.lean",
        "scripts/check_window_transforms.lean", "scripts/check_prefix_encoding.lean",
        "scripts/check_prefix_completion.lean", "scripts/check_root_completion.lean", "scripts/check_root_products.lean", "scripts/check_shifted_low.lean", "scripts/check_low_recombination.lean", "scripts/check_physical_low_high.lean", "scripts/check_low_high_join.lean", "scripts/check_folded_band_schedule.lean", "scripts/check_shared_selector_costs.lean",
        "scripts/check_cw_polynomial.lean", "outputs/check_cw_polynomial.py",
        "scripts/check_cw_interpolation.lean", "outputs/check_cw_interpolation.py",
        "scripts/check_cw_block_extraction.lean", "outputs/check_cw_block_extraction.py",
        "scripts/check_cw_hash_counting.lean", "outputs/check_cw_hash_counting.py",
        "scripts/check_cw_type_regularity.lean", "outputs/check_cw_type_regularity.py",
        "scripts/check_modular_behrend.lean", "outputs/check_modular_behrend.py",
        "scripts/check_cw_entropy_rate.lean", "outputs/check_cw_entropy_rate.py",
        "scripts/check_equal_copy_recursion.lean", "outputs/check_equal_copy_recursion.py",
        "scripts/check_retained_recursion.lean", "outputs/check_retained_recursion.py",
        "scripts/check_padded_recursion.lean",
    )]
    return {
        str(path.relative_to(root)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(paths)
    }


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    manifest = json.loads((root / "lake-manifest.json").read_text())
    packages = {package["name"]: package for package in manifest["packages"]}
    if packages["mathlib"]["rev"] != "9a9483a92959bc92bd6a60176dd1fe597298c1f8":
        raise SystemExit("Unexpected mathlib revision in lake-manifest.json.")
    for name, package in packages.items():
        checkout = root / manifest["packagesDir"] / name
        actual = subprocess.check_output(
            ["git", "-C", str(checkout), "rev-parse", "HEAD"], text=True
        ).strip()
        if actual != package["rev"]:
            raise SystemExit(f"Dependency {name} does not match its manifest revision.")
        dirty = subprocess.check_output(
            ["git", "-C", str(checkout), "status", "--porcelain", "--untracked-files=normal"],
            text=True,
        )
        if dirty:
            raise SystemExit(f"Dependency {name} has modified or untracked source files.")
    paths = module_order(root / "lean")
    roots_match = re.search(r"^roots\s*=\s*(\[[^\n]+\])", (root / "lakefile.toml").read_text(), re.MULTILINE)
    declared_roots = [] if roots_match is None else json.loads(roots_match[1])
    if len(declared_roots) != len(paths) or set(declared_roots) != {path.stem for path in paths}:
        raise SystemExit("Lake roots must list every top-level Lean module exactly once.")
    snapshot = source_snapshot(root)
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
    for path in paths:
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
        declarations = len(re.findall(r"^[ \t]*#print axioms ", path.read_text(), re.MULTILINE))
        if not declarations or len(reports) != declarations:
            raise SystemExit(f"Missing axiom reports in {path.name}.")
        for report in reports:
            axioms = {name.strip() for name in report.split(",") if name.strip()}
            if not axioms <= allowed_axioms:
                raise SystemExit(f"Unapproved axiom dependency: {sorted(axioms - allowed_axioms)}")
        checked += declarations
    if source_snapshot(root) != snapshot:
        raise SystemExit("Sources changed during verification; rerun on a frozen snapshot.")
    digest = hashlib.sha256(json.dumps(snapshot, sort_keys=True).encode()).hexdigest()
    print(f"\nPASS: {len(paths)} modules; {checked} scoped declarations checked; only standard Lean axioms.")
    print(f"Source/configuration SHA-256: {digest}")
    print("See lean/README.md for the exact formalization scope and remaining obligations.")


if __name__ == "__main__":
    main()
