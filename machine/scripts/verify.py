#!/usr/bin/env python3
"""Check the isolated Lean 4.33.1 machine backend and its scoped proof axioms.

This verifies concrete initial Light routines and conditional composition
adapters. It does not assert that an improved min-plus solver has been supplied.
Use --core to also recompile the canonical mathematical sources under 4.33.1.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
RUN_ENV = os.environ.copy()
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
PINS = {
    "ThreeSumApsp": "e1a4e6508154ea59f030480661590a9fe3018011",
    "mathlib": "0df444a360eaa60ab8c11dca51a86af692955474",
}
BASE = {
    "MachineBackend.lean": {
        "Light.ThinMatrixBackend.indexedRead_meets",
        "Light.ThinMatrixBackend.pointwise_meets",
        "Light.ThinMatrixBackend.readTask_solved",
        "Light.ThinMatrixBackend.storedCoefficientRead_solvedIn",
    },
    "DenseMarkPass.lean": {
        "Light.DenseMarkPass.ends",
        "Light.DenseMarkPass.meets",
        "Light.DenseMarkPass.meets_of_pos",
        "Light.DenseMarkPass.meets_boolean",
    },
    "DenseScorePass.lean": {
        "Light.DenseScorePass.score_eq_sum",
        "Light.DenseScorePass.ends",
        "Light.DenseScorePass.meets",
        "Light.DenseScorePass.meets_of_pos",
    },
    "DenseSurvivorPass.lean": {
        "Light.DenseSurvivorPass.ends",
        "Light.DenseSurvivorPass.meets",
        "Light.DenseSurvivorPass.meets_of_pos",
    },
    "DenseArgminPass.lean": {
        "Light.DenseArgminPass.scan_isArgmin",
        "Light.DenseArgminPass.ends",
        "Light.DenseArgminPass.meets",
        "Light.DenseArgminPass.meets_linear",
    },
    "DenseAffirmativePass.lean": {
        "Light.DenseAffirmativePass.ends",
        "Light.DenseAffirmativePass.meets",
        "Light.DenseAffirmativePass.meets_of_pos",
    },
    "DenseMinimumUpdatePass.lean": {
        "Light.DenseMinimumUpdatePass.ends",
        "Light.DenseMinimumUpdatePass.meets",
        "Light.DenseMinimumUpdatePass.meets_of_pos",
    },
    "MachineAdapter.lean": {
        "ThinMatrix.MachineAdapter.appendAPSP",
        "ThinMatrix.MachineAdapter.realizedFromMinPlus",
        "ThinMatrix.MachineAdapter.rationalStatementOfMinPlusExecution",
    },
}
CORE = {
    "../lean/APSPReduction.lean": {
        "ThinMatrix.APSPReduction.exists_simple_le",
        "ThinMatrix.APSPReduction.exists_short_le",
        "ThinMatrix.APSPReduction.minPlus_spec",
        "ThinMatrix.APSPReduction.squared_spec",
        "ThinMatrix.APSPReduction.apsp_correct",
        "ThinMatrix.APSPReduction.apsp_polynomial_magnitude",
        "ThinMatrix.APSPReduction.apsp_product_count",
        "ThinMatrix.APSPReduction.apsp_execution",
    },
    "../lean/APSPAlgorithm.lean": {
        "ThinMatrix.APSPAlgorithm.optional_eq_minPlus",
        "ThinMatrix.APSPAlgorithm.fastSquared_eq",
        "ThinMatrix.APSPAlgorithm.fastAPSP_correct",
        "ThinMatrix.APSPAlgorithm.fastTrace_bounded",
        "ThinMatrix.APSPAlgorithm.execution_calls",
        "ThinMatrix.APSPAlgorithm.execution_writes",
        "ThinMatrix.APSPAlgorithm.polylog_oracle_calls",
        "ThinMatrix.APSPAlgorithm.polylog_formation_writes",
        "ThinMatrix.APSPAlgorithm.fastTrace_weight_bound",
        "ThinMatrix.APSPAlgorithm.fastAPSP_entry_bound",
        "ThinMatrix.APSPAlgorithm.execution_correct",
    },
    "../lean/AsymptoticCosts.lean": {
        "ThinMatrix.AsymptoticCosts.existsUniformSlack",
        "ThinMatrix.AsymptoticCosts.stageUniformSlack",
        "ThinMatrix.AsymptoticCosts.scalarGeometryAllStages",
        "ThinMatrix.AsymptoticCosts.cyclicGeometrySlack",
        "ThinMatrix.AsymptoticCosts.scalarTileFitsEventually",
        "ThinMatrix.AsymptoticCosts.cyclicTileFitsEventually",
        "ThinMatrix.AsymptoticCosts.roundedLogPowBigO",
        "ThinMatrix.AsymptoticCosts.completeCostBigO",
        "ThinMatrix.AsymptoticCosts.costBoundOfDomination",
        "ThinMatrix.AsymptoticCosts.costBoundOfEventualDomination",
    },
    "CoreCompatibility.lean": {
        "ThinMatrix.APSPAlgorithm.fastAPSP_correct",
        "ThinMatrix.AsymptoticCosts.completeCostBigO",
    },
    "CanonicalMachineAdapter.lean": {
        "ThinMatrix.CanonicalMachineAdapter.rationalStatementOfLedger",
    },
}
AXIOM_REPORT = re.compile(
    r"'([^']+)'\s+(?:depends on axioms:\s*\[([^\]]*)\]"
    r"|does not depend on any axioms)",
    re.MULTILINE,
)
CORE_LIBRARY_SOURCES = (
    "APSPAlgorithm.lean", "APSPReduction.lean", "AlignedCertificate.lean",
    "AsymptoticCosts.lean", "MinPlusReduction.lean", "RealCertificate.lean",
)


def captured(command: list[str]) -> str:
    result = subprocess.run(
        command, cwd=ROOT, env=RUN_ENV, text=True,
        stdout=subprocess.PIPE, stderr=subprocess.STDOUT
    )
    if result.returncode:
        print(result.stdout, end="")
        raise RuntimeError(f"Command failed with status {result.returncode}: {command!r}")
    return result.stdout


def source_snapshot() -> dict[str, str]:
    """Hash local sources/configuration, excluding dependencies and build output."""
    paths = list(ROOT.glob("*.lean"))
    paths.extend(ROOT.parent / "lean" / name for name in CORE_LIBRARY_SOURCES)
    paths.extend(ROOT / name for name in (
        "lean-toolchain", "lakefile.toml", "lake-manifest.json", "scripts/verify.py",
    ))
    return {
        str(path.relative_to(ROOT.parent)): hashlib.sha256(path.read_bytes()).hexdigest()
        for path in sorted(paths)
    }


def check_dependencies(manifest: dict) -> None:
    """Require every pinned dependency's source checkout to be unchanged."""
    packages = {package["name"]: package for package in manifest["packages"]}
    if len(packages) != len(manifest["packages"]):
        raise RuntimeError("Duplicate dependency names in manifest.")
    for name, rev in PINS.items():
        package = packages.get(name)
        if package is None or package.get("rev") != rev:
            raise RuntimeError(f"Manifest does not pin {name} to {rev}")
    if packages["ThreeSumApsp"].get("subDir") != "3sum-apsp":
        raise RuntimeError("formal-math dependency has the wrong package subdirectory.")
    for name, package in sorted(packages.items()):
        if package.get("type") != "git" or not re.fullmatch(r"[0-9a-f]{40}", package.get("rev", "")):
            raise RuntimeError(f"Dependency {name} lacks an exact Git revision.")
        checkout = ROOT / manifest["packagesDir"] / name
        actual = captured(["git", "-C", str(checkout), "rev-parse", "HEAD"]).strip()
        if actual != package["rev"]:
            raise RuntimeError(f"Dependency checkout mismatch for {name}: {actual}")
        status = captured([
            "git", "-C", str(checkout), "status", "--porcelain=v1", "--untracked-files=all",
        ])
        if status:
            raise RuntimeError(f"Dependency {name} has modified or nonignored untracked files.")


def verify(lake: str, include_core: bool) -> None:
    executable = shutil.which(lake, path=RUN_ENV.get("PATH"))
    if executable is None:
        raise RuntimeError(f"Lake executable not found: {lake}")
    # Preserve an elan shim's argv[0]; resolving its symlink would invoke elan.
    lake = str(Path(executable).absolute())
    RUN_ENV["PATH"] = str(Path(lake).parent) + os.pathsep + RUN_ENV.get("PATH", "")
    RUN_ENV.setdefault("npm_config_cache", str(ROOT / ".lake" / "npm-cache"))
    version = captured([lake, "env", "lean", "--version"])
    if not re.search(r"version 4\.33\.1(?:,|\))", version):
        raise RuntimeError(f"Wrong Lean runtime: {version.strip()}")
    print(version.strip(), flush=True)

    manifest_path = ROOT / "lake-manifest.json"
    if not manifest_path.is_file():
        raise RuntimeError("Missing manifest. Run lake update with the pinned toolchain first.")
    manifest = json.loads(manifest_path.read_text())
    check_dependencies(manifest)
    snapshot = source_snapshot()
    print(f"Pinned dependency source checkouts: {len(manifest['packages'])}; all clean.", flush=True)

    declarations = dict(BASE)
    if include_core:
        declarations.update(CORE)
    targets = [Path(source).stem for source in declarations]
    print("Building imported dependencies and selected source modules...", flush=True)
    subprocess.run([lake, "build", *targets], cwd=ROOT, env=RUN_ENV, check=True)

    reports: dict[str, set[str]] = {}
    transcript: list[str] = [version.strip(), f"Core compatibility checks: {include_core}"]
    for source, expected in declarations.items():
        text = (ROOT / source).read_text()
        if re.search(r"(?m)^\s*(?:unsafe\s+)?axiom\s", text):
            raise RuntimeError(f"Custom axiom declaration in {source}")
        if re.search(r"\bnative_decide\b", text):
            raise RuntimeError(f"native_decide is disallowed in {source}")
        command = [lake, "env", "lean", "-DwarningAsError=true"]
        if source.startswith("../lean/"):
            command.extend(["-R", "../lean"])
        command.append(source)
        output = captured(command)
        transcript.append("$ lake " + " ".join(command[1:]) + "\n" + output)
        found: set[str] = set()
        for match in AXIOM_REPORT.finditer(output):
            name, body = match.groups()
            axioms = set() if body is None else {
                item.strip() for item in body.split(",") if item.strip()
            }
            unexpected = axioms - ALLOWED_AXIOMS
            if unexpected:
                raise RuntimeError(f"{name}: forbidden axioms {sorted(unexpected)}")
            reports[name] = axioms
            found.add(name)
        missing = expected - found
        if missing:
            raise RuntimeError(f"Missing axiom reports in {source}: {sorted(missing)}")
        print(f"PASS {source}: {len(expected)} scoped declarations", flush=True)

    if source_snapshot() != snapshot:
        raise RuntimeError("Sources/configuration changed during verification; rerun on a frozen snapshot.")
    check_dependencies(manifest)
    digest = hashlib.sha256(json.dumps(snapshot, sort_keys=True).encode()).hexdigest()
    total = sum(len(expected) for expected in declarations.values())
    summary = (
        f"PASS: {total} scoped declaration checks ({len(reports)} unique); "
        f"only standard axioms {sorted(ALLOWED_AXIOMS)}.\n"
        f"Source/configuration SHA-256: {digest}\n"
        f"Pinned dependency source checkouts: {len(manifest['packages'])}; all clean before and after.\n"
        "Scope: actual Light primitives and conditional adapters; the improved Light solver remains a premise."
    )
    transcript.append(summary)
    log = ROOT / ".lake" / "verification-output.txt"
    log.parent.mkdir(exist_ok=True)
    log.write_text("\n".join(transcript) + "\n")
    print(summary)
    print(f"Compiler transcript: {log}")


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--lake-bin", default="lake", help="Lake executable from the exact 4.33.1 runtime")
    parser.add_argument("--core", action="store_true", help="also check canonical proof-source compatibility")
    args = parser.parse_args()
    try:
        verify(args.lake_bin, args.core)
    except (OSError, RuntimeError, subprocess.CalledProcessError) as error:
        print(f"FAIL: {error}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())

