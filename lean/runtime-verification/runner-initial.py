#!/usr/bin/env python3
"""Run frozen Lean finite fixtures only after a matching successful kernel audit.

Default: inventory only, no Lean process. Execution requires --run and
--verified-log. Every child starts with inherited LEAN_PATH removed; Lake
provides only the repository's pinned import paths. No repository writes.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
from concurrent.futures import ThreadPoolExecutor
import hashlib
import importlib.util
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import sys
import threading
import time

sys.dont_write_bytecode = True

DEFAULT_ROOT = Path('/tmp/thin-matrix-results-sync-20261021')
DEFAULT_TOOLCHAIN = Path('/tmp/thin-matrix-lean-toolchain/lean-4.31.0-darwin_aarch64/bin')
ACTIVE: dict[int, subprocess.Popen] = {}
ACTIVE_LOCK = threading.Lock()
STOP = threading.Event()


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def inventory(root: Path) -> list[dict]:
    rows = []
    for path in sorted((root / 'scripts').glob('check_*.lean')):
        source = path.read_text()
        is_main = bool(re.search(r'^def main\b', source, re.MULTILINE))
        has_eval = bool(re.search(r'^#eval\b', source, re.MULTILINE))
        if not is_main and not has_eval:
            raise RuntimeError(f'Fixture has neither main nor #eval: {path}')
        rows.append({
            'path': str(path.relative_to(root)),
            'sha256': sha(path),
            'mode': 'main' if is_main else 'eval',
            'lean_arguments': ['--run', str(path.relative_to(root))] if is_main else [str(path.relative_to(root))],
            'source_options': re.findall(r'^set_option\s+(.+)$', source, re.MULTILINE),
            'assertion': 'printed_tuple_true_and_zero_dimension_length_one' if path.name == 'check_half_source_binary.lean' else 'exit_zero_and_anchored_PASS_without_failure_diagnostics',
        })
    return rows


def snapshot_digest(root: Path) -> tuple[str, dict]:
    spec = importlib.util.spec_from_file_location('frozen_lean_verifier', root / 'scripts/verify_lean.py')
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    snapshot = module.source_snapshot(root)
    digest = hashlib.sha256(json.dumps(snapshot, sort_keys=True).encode()).hexdigest()
    return digest, snapshot


def stop_process(proc: subprocess.Popen) -> None:
    if proc.poll() is not None:
        return
    try:
        os.killpg(proc.pid, signal.SIGTERM)
        proc.wait(timeout=5)
    except ProcessLookupError:
        pass
    except subprocess.TimeoutExpired:
        try:
            os.killpg(proc.pid, signal.SIGKILL)
        except ProcessLookupError:
            pass
        proc.wait()


def stop_all() -> None:
    with ACTIVE_LOCK:
        processes = list(ACTIVE.values())
    for proc in processes:
        stop_process(proc)


def output_assertions(row: dict, stdout: str, stderr: str) -> dict:
    """Validate observable outcomes, not arbitrary semantics of fixture source.

    The frozen source audit found uncaught failure exceptions in 70 fixtures.
    One legacy #eval fixture only prints a Bool, so it needs a value check.
    Reject diagnostics even if a process erroneously exits zero after PASS.
    """
    pass_lines = re.findall(r'^PASS(?:\s|:|$).*$', stdout, re.MULTILINE)
    diagnostic = re.compile(
        r'(?im)^\s*(?:FAIL(?:ED|URE)?\b|uncaught exception\b|PANIC\b|panic\b)'
        r'|^.*:\d+:\d+:\s*error:'
        r'|^\s*error:')
    failures = [line for line in (stdout + '\n' + stderr).splitlines()
                if diagnostic.search(line)]
    expected = bool(pass_lines)
    if row['assertion'] == 'printed_tuple_true_and_zero_dimension_length_one':
        tuples = re.findall(r'^\s*\((true|false),\s*(\d+),\s*(\d+)\)\s*$',
                            stdout, re.MULTILINE)
        numbers = re.findall(r'^\s*(\d+)\s*$', stdout, re.MULTILINE)
        expected = len(tuples) == 1 and tuples[0][0] == 'true' and numbers == ['1']
    return {'expected_output_seen': expected, 'failure_diagnostics': failures,
            'pass_lines': pass_lines, 'assertion_passed': expected and not failures}


def run_fixture(row: dict, root: Path, logs: Path, env: dict, lake: str,
                timeout: float, warnings_as_errors: bool) -> dict:
    if STOP.is_set():
        raise RuntimeError('Fixture suite cancelled')
    filename = Path(row['path']).stem
    command = [lake, 'env', 'lean']
    if warnings_as_errors:
        command.append('-DwarningAsError=true')
    command.extend(row['lean_arguments'])
    started = time.monotonic()
    timed_out = False
    stdout_path, stderr_path = logs / f'{filename}.stdout.log', logs / f'{filename}.stderr.log'
    with stdout_path.open('wb') as out, stderr_path.open('wb') as err:
        proc = subprocess.Popen(command, cwd=root, env=env, stdout=out, stderr=err,
                                stdin=subprocess.DEVNULL, start_new_session=True)
        with ACTIVE_LOCK:
            ACTIVE[proc.pid] = proc
            stopping = STOP.is_set()
        if stopping:
            stop_process(proc)
        try:
            proc.wait(timeout=timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            stop_process(proc)
        finally:
            with ACTIVE_LOCK:
                ACTIVE.pop(proc.pid, None)
    stdout = stdout_path.read_text(errors='replace')
    stderr = stderr_path.read_text(errors='replace')
    assertions = output_assertions(row, stdout, stderr)
    passed = proc.returncode == 0 and not timed_out and assertions['assertion_passed']
    result = {
        **row, 'command': command, 'returncode': proc.returncode,
        'timeout': timed_out, **assertions, 'passed': passed,
        'seconds': round(time.monotonic() - started, 3),
        'stdout': str(stdout_path), 'stderr': str(stderr_path),
        'warning_lines': sum('warning:' in line for line in (stdout + stderr).splitlines()),
    }
    (logs / f'{filename}.json').write_text(json.dumps(result, indent=2, sort_keys=True) + '\n')
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--root', type=Path, default=DEFAULT_ROOT)
    parser.add_argument('--logs', type=Path, default=Path('/tmp/runtime-audit-612/results'))
    parser.add_argument('--toolchain-bin', type=Path, default=DEFAULT_TOOLCHAIN)
    parser.add_argument('--jobs', type=int, default=4, choices=range(1, 5))
    parser.add_argument('--timeout', type=float, default=7200, help='seconds per fixture')
    parser.add_argument('--only-main', action='store_true')
    parser.add_argument('--fixture', action='append', default=[], help='exact basename, repeat to select fixtures')
    parser.add_argument('--warnings-as-errors', action='store_true')
    parser.add_argument('--run', action='store_true', help='execute after the matching successful verifier gate')
    parser.add_argument('--verified-log', type=Path)
    args = parser.parse_args()
    root = args.root.resolve()
    rows = inventory(root)
    if args.only_main:
        rows = [row for row in rows if row['mode'] == 'main']
    if args.fixture:
        available = {Path(row['path']).name for row in rows}
        missing = set(args.fixture) - available
        if missing:
            parser.error(f'Unknown or excluded fixtures: {sorted(missing)}')
        rows = [row for row in rows if Path(row['path']).name in args.fixture]
    if not args.run:
        print(json.dumps({'root': str(root), 'fixtures': rows, 'count': len(rows),
                          'executed': False}, indent=2, sort_keys=True))
        return 0
    if args.verified_log is None:
        parser.error('--run requires --verified-log from the completed frozen Lean verifier')
    if args.timeout <= 0:
        parser.error('--timeout must be positive')
    log = args.verified_log.read_text()
    passes = re.findall(r'^PASS: (\d+) modules; (\d+) scoped declarations checked; only standard Lean axioms\.$', log, re.MULTILINE)
    digests = re.findall(r'^Source/configuration SHA-256: ([0-9a-f]{64})$', log, re.MULTILINE)
    if not passes or not digests:
        raise RuntimeError('Verifier log lacks a completed successful audit and source digest')
    before, snapshot = snapshot_digest(root)
    if before != digests[-1]:
        raise RuntimeError('Current source/configuration differs from the successfully verified snapshot')
    if int(passes[-1][0]) != len(list((root / 'lean').glob('*.lean'))):
        raise RuntimeError('Verified module count differs from current repository')
    env = os.environ.copy()
    env.pop('LEAN_PATH', None)
    env['PATH'] = str(args.toolchain_bin.resolve()) + os.pathsep + env.get('PATH', '')
    env['LC_ALL'] = 'C'
    lake = shutil.which('lake', path=env['PATH'])
    if not lake:
        raise RuntimeError('Pinned Lake executable not found')
    version = subprocess.check_output([lake, 'env', 'lean', '--short-version'], cwd=root, env=env, text=True).strip()
    if version != '4.31.0':
        raise RuntimeError(f'Expected Lean 4.31.0, found {version}')
    for row in rows:
        if snapshot.get(row['path']) != row['sha256']:
            raise RuntimeError(f'Fixture absent from verified snapshot or changed: {row["path"]}')
    args.logs = args.logs.resolve()
    if args.logs == root or root in args.logs.parents:
        raise RuntimeError('Runtime logs must be outside the frozen repository')
    if args.logs.exists() and any(args.logs.iterdir()):
        raise RuntimeError('Log directory is not empty; use a fresh directory to preserve earlier evidence')
    args.logs.mkdir(parents=True, exist_ok=True)
    (args.logs / 'inventory.json').write_text(json.dumps(rows, indent=2, sort_keys=True) + '\n')
    (args.logs / 'source-digest.txt').write_text(before + '\n')
    (args.logs / 'source-snapshot.json').write_text(json.dumps(snapshot, indent=2, sort_keys=True) + '\n')
    metadata = {
        'started_utc': datetime.now(timezone.utc).isoformat(),
        'root': str(root), 'argv': [sys.executable, *sys.argv],
        'python_version': sys.version, 'lean_version': version,
        'lake': lake, 'toolchain_bin': str(args.toolchain_bin.resolve()),
        'jobs': args.jobs, 'timeout_seconds': args.timeout,
        'warnings_as_errors': args.warnings_as_errors,
        'lean_path_inherited': False, 'locale': 'C',
        'runner_sha256': sha(Path(__file__)),
        'verification_log': str(args.verified_log.resolve()),
        'verification_log_sha256': sha(args.verified_log),
        'verification_pass': passes[-1], 'source_sha256': before,
    }
    (args.logs / 'run-metadata.json').write_text(json.dumps(metadata, indent=2, sort_keys=True) + '\n')
    (args.logs / 'runner-used.py').write_bytes(Path(__file__).read_bytes())
    results = []
    executor = ThreadPoolExecutor(max_workers=args.jobs)
    try:
        # executor.map runs concurrently but emits status in sorted fixture order.
        for index, result in enumerate(executor.map(
            lambda row: run_fixture(row, root, args.logs, env, lake, args.timeout, args.warnings_as_errors), rows), 1):
            results.append(result)
            print(f'{index:02d}/{len(rows)} {"PASS" if result["passed"] else "FAIL"} {result["path"]} ({result["seconds"]:.3f}s)', flush=True)
    except BaseException:
        STOP.set()
        stop_all()
        executor.shutdown(wait=True, cancel_futures=True)
        raise
    else:
        executor.shutdown(wait=True)
    after, _ = snapshot_digest(root)
    unchanged = before == after and all(sha(root / row['path']) == row['sha256'] for row in rows)
    summary = {'source_sha256': before, 'source_unchanged': unchanged, 'jobs': args.jobs,
               'lean_path_inherited': False, 'count': len(results),
               'passed': sum(r['passed'] for r in results), 'results': results,
               'finished_utc': datetime.now(timezone.utc).isoformat()}
    (args.logs / 'summary.json').write_text(json.dumps(summary, indent=2, sort_keys=True) + '\n')
    ok = unchanged and all(r['passed'] for r in results)
    print(f'{"PASS" if ok else "FAIL"}: {summary["passed"]}/{len(results)} finite Lean fixtures; frozen sources {"unchanged" if unchanged else "CHANGED"}.', flush=True)
    return 0 if ok else 1


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except KeyboardInterrupt:
        stop_all()
        raise SystemExit(130)
