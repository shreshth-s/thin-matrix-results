#!/usr/bin/env python3
"""Merge the frozen 68 unchanged fixture passes with three audited rechecks.

Read-only with respect to source repositories and existing evidence. Does not
run Lean or edit old results. Writes one compact evidence directory outside
the repository, only after every provenance and coverage check succeeds.
"""
from __future__ import annotations
import argparse
from datetime import datetime, timezone
import difflib
import hashlib
import importlib.util
import json
from pathlib import Path
import re
import shutil
import sys
import tempfile

sys.dont_write_bytecode = True
FIXED = frozenset({'scripts/check_exact_half_sources.lean', 'scripts/check_low_recombination.lean'})
BINARY = 'scripts/check_half_source_binary.lean'
RECHECKED = FIXED | {BINARY}
GENERIC = 'exit_zero_and_anchored_PASS_without_failure_diagnostics'
OLD_BINARY = 'printed_tuple_true_and_zero_dimension_length_one'
NEW_BINARY = 'printed_tuple_true_and_zero_dimension_length_zero'


def require(test: bool, message: str) -> None:
    if not test:
        raise ValueError(message)


def sha_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def sha(path: Path) -> str:
    return sha_bytes(path.read_bytes())


def digest(snapshot: dict) -> str:
    return sha_bytes(json.dumps(snapshot, sort_keys=True).encode())


def read_json(path: Path):
    return json.loads(path.read_text())


def indexed(rows: list[dict], label: str) -> dict[str, dict]:
    result = {row['path']: row for row in rows}
    require(len(result) == len(rows), f'{label}: duplicate fixture paths')
    return result


def output_assertion(rule: str, stdout: str, stderr: str) -> bool:
    failure = re.compile(r'(?im)^\s*(?:FAIL(?:ED|URE)?\b|uncaught exception\b|PANIC\b|panic\b)'
                         r'|^.*:\d+:\d+:\s*error:|^\s*error:')
    if failure.search(stdout + '\n' + stderr):
        return False
    if rule in (OLD_BINARY, NEW_BINARY):
        tuples = re.findall(r'^\s*\((true|false),\s*(\d+),\s*(\d+)\)\s*$', stdout, re.M)
        numbers = re.findall(r'^\s*(\d+)\s*$', stdout, re.M)
        return (len(tuples) == 1 and tuples[0][0] == 'true'
                and numbers == ['1' if rule == OLD_BINARY else '0'])
    require(rule == GENERIC, f'Unsupported assertion contract: {rule}')
    return bool(re.search(r'^PASS(?:\s|:|$).*$', stdout, re.M))


def kernel_audit(path: Path, snapshot: dict) -> dict:
    data = path.read_bytes()
    log = data.decode()
    passes = re.findall(r'^PASS: (\d+) modules; (\d+) scoped declarations checked; only standard Lean axioms\.$', log, re.M)
    digests = re.findall(r'^Source/configuration SHA-256: ([0-9a-f]{64})$', log, re.M)
    require(len(passes) == 1 and len(digests) == 1, f'{path}: expected one complete kernel PASS and digest')
    require(digests[0] == digest(snapshot), f'{path}: kernel digest differs from source snapshot')
    modules = [p for p in snapshot if p.startswith('lean/') and p.endswith('.lean') and p.count('/') == 1]
    require(int(passes[0][0]) == len(modules) == 612, f'{path}: expected 612 checked modules')
    return {'path': str(path.resolve()), 'sha256': sha_bytes(data), 'modules': 612,
            'scoped_declarations': int(passes[0][1]), 'source_sha256': digests[0]}


def load_run(directory: Path, name: str) -> dict:
    directory = directory.resolve()
    summary = read_json(directory / 'summary.json')
    metadata = read_json(directory / 'run-metadata.json')
    snapshot = read_json(directory / 'source-snapshot.json')
    inventory = indexed(read_json(directory / 'inventory.json'), f'{name} inventory')
    results = indexed(summary['results'], f'{name} results')
    require(summary['source_unchanged'] is True, f'{name}: sources changed during execution')
    require(summary['count'] == len(results) == len(inventory), f'{name}: inconsistent result counts')
    require(set(results) == set(inventory), f'{name}: result/inventory mismatch')
    require(summary['passed'] == sum(row['passed'] is True for row in results.values()), f'{name}: inconsistent PASS count')
    require(summary['source_sha256'] == metadata['source_sha256'] == digest(snapshot), f'{name}: snapshot digest mismatch')
    require((directory / 'source-digest.txt').read_text().strip() == digest(snapshot), f'{name}: digest file mismatch')
    require(metadata['lean_version'] == '4.31.0', f'{name}: wrong Lean version')
    require(metadata['lean_path_inherited'] is False and summary['lean_path_inherited'] is False, f'{name}: inherited LEAN_PATH')
    require(metadata['jobs'] == summary['jobs'] == 4, f'{name}: expected four-worker run')
    require(sha(directory / 'runner-used.py') == metadata['runner_sha256'], f'{name}: runner hash mismatch')
    gate = metadata.get('verification_gate')
    kernel_snapshot = snapshot
    if gate is not None:
        kernel_snapshot = read_json(directory / 'gate-source-snapshot.json')
        require(gate['mode'] == 'verified_production_with_exact_fixture_only_corrections', f'{name}: unsupported runtime gate')
        require(gate['initial_source_sha256'] == digest(kernel_snapshot), f'{name}: initial gate digest mismatch')
        require(gate['runtime_source_sha256'] == digest(snapshot), f'{name}: runtime gate digest mismatch')
        require(gate['proof_and_configuration_sources_identical'] is True, f'{name}: proof/config identity absent')
        require(gate['final_fresh_kernel_still_required_for_publication'] is True, f'{name}: final audit requirement absent')
        changed = {p for p in set(snapshot) | set(kernel_snapshot) if snapshot.get(p) != kernel_snapshot.get(p)}
        require(changed == FIXED and set(gate['changed_paths']) == FIXED, f'{name}: runtime gate has unrelated source changes')
        require(set(results) == RECHECKED, f'{name}: fixture-only gate used for unexpected targets')
        require(summary['dependency_sources_unchanged'] is True and summary['local_proof_artifacts_unchanged'] is True,
                f'{name}: dependency sources or reused proof artifacts changed during runtime')
        require(len(gate['previously_verified_local_artifacts']) == 612, f'{name}: incomplete reused artifact record')
        require(gate['dependency_sources'] and all(x['revision_matches_pinned_manifest'] is True
                and x['working_tree_clean'] is True for x in gate['dependency_sources'].values()),
                f'{name}: pinned dependency source identity absent')
        require(set(gate['precise_fixture_edits']) == FIXED, f'{name}: missing exact gate patch evidence')
        previous = 'decide (plan.bitSteps≤2^L*ExactHalfWeightTable.candidateBitBudget L)'
        replacement = ('decide (plan.bitSteps≤HalfSourceRetainedTranslations.arithmeticBudget m+\n'
                       '    2^L*ExactHalfWeightTable.candidateBitBudget L)')
        for path, edit in gate['precise_fixture_edits'].items():
            require(sha_bytes(edit['initial_source'].encode()) == edit['initial_sha256'] == kernel_snapshot[path],
                    f'{name}/{path}: original gate fixture source differs')
            require(sha_bytes(edit['runtime_source'].encode()) == edit['runtime_sha256'] == snapshot[path],
                    f'{name}/{path}: current gate fixture source differs')
            require(edit['initial_source'].count(previous) == 1
                    and edit['initial_source'].replace(previous, replacement) == edit['runtime_source'],
                    f'{name}/{path}: gate permits an unaudited fixture edit')
    kernel = kernel_audit(Path(metadata['verification_log']), kernel_snapshot)
    require(kernel['sha256'] == metadata['verification_log_sha256'], f'{name}: verifier log changed')
    if gate is not None:
        require(gate['original_kernel_log_sha256'] == kernel['sha256'], f'{name}: gate kernel log hash mismatch')
        require(kernel['scoped_declarations'] == 5290, f'{name}: fixture-only gate requires original 5290 declarations')
    require(metadata['verification_pass'] == [str(kernel['modules']), str(kernel['scoped_declarations'])], f'{name}: verifier summary mismatch')
    streams = {}
    for path, row in results.items():
        stem = Path(path).stem
        require(row == read_json(directory / f'{stem}.json'), f'{name}/{path}: per-fixture result changed')
        require(row['sha256'] == inventory[path]['sha256'] == snapshot.get(path), f'{name}/{path}: source hash mismatch')
        require(row['mode'] == inventory[path]['mode'] and row['assertion'] == inventory[path]['assertion'], f'{name}/{path}: fixture contract mismatch')
        arguments = ['--run', path] if row['mode'] == 'main' else [path]
        command = [metadata['lake'], 'env', 'lean']
        if metadata['warnings_as_errors']:
            command.append('-DwarningAsError=true')
        command += arguments
        require(row['lean_arguments'] == arguments and row['command'] == command, f'{name}/{path}: unexpected command')
        chunks = {}
        for stream in ('stdout', 'stderr'):
            file = directory / f'{stem}.{stream}.log'
            require(Path(row[stream]).resolve() == file.resolve(), f'{name}/{path}: redirected evidence path')
            chunks[stream] = file.read_bytes()
        out, err = (chunks[s].decode(errors='replace') for s in ('stdout', 'stderr'))
        assertion = output_assertion(row['assertion'], out, err)
        require(row['assertion_passed'] is assertion, f'{name}/{path}: recorded assertion differs from captured output')
        observed = row['returncode'] == 0 and row['timeout'] is False and assertion
        require(row['passed'] is observed, f'{name}/{path}: recorded result differs from captured output')
        streams[path] = chunks
    return {'directory': str(directory), 'summary': summary, 'metadata': metadata,
            'snapshot': snapshot, 'inventory': inventory, 'results': results,
            'streams': streams, 'kernel': kernel}


def current_snapshot(root: Path) -> dict:
    spec = importlib.util.spec_from_file_location('merge_frozen_verifier', root / 'scripts/verify_lean.py')
    require(spec is not None and spec.loader is not None, 'Cannot load source snapshot definition')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module.source_snapshot(root)


def validate_coverage(initial: dict, latest: dict, current: dict, fixtures: set[str]) -> list[tuple[str, dict]]:
    require(len(fixtures) == 71, 'Expected exactly 71 current fixture sources')
    require(set(initial['results']) == fixtures, 'Initial run does not cover exactly the 71 current fixtures')
    require(set(latest['results']) == RECHECKED, 'Recheck must contain exactly the two corrected fixtures and binary fixture')
    require(initial['summary']['passed'] == 68 and latest['summary']['passed'] == 3, 'Expected initial 68 passes and latest three passes')
    failed = {p for p, row in initial['results'].items() if not row['passed']}
    require(failed == RECHECKED, f'Initial failures are not precisely the audited three: {sorted(failed)}')
    changed = {p for p in set(current) | set(initial['snapshot']) if current.get(p) != initial['snapshot'].get(p)}
    require(changed == FIXED, f'Snapshot changes exceed or omit the two audited fixture changes: {sorted(changed)}')
    require(latest['snapshot'] == current, 'Final recheck snapshot is not the current source/config snapshot')
    require(initial['inventory'][BINARY]['assertion'] == OLD_BINARY, 'Initial binary contract is not the documented incorrect rule')
    require(latest['inventory'][BINARY]['assertion'] == NEW_BINARY, 'Final binary contract is not the corrected rule')
    selected = []
    for path in sorted(fixtures):
        run = latest if path in RECHECKED else initial
        row = run['results'][path]
        require(row['passed'] is True, f'{path}: selected result failed')
        require(row['sha256'] == current.get(path), f'{path}: selected result does not match current source')
        selected.append(('rechecked' if path in RECHECKED else 'reused unchanged', row))
    require(len(selected) == 71, 'Incomplete merged fixture coverage')
    return selected


def validate_fixture_corrections(initial_sources: Path, root: Path,
                                 initial_snapshot: dict, current: dict) -> tuple[dict, str]:
    old = 'decide (plan.bitSteps≤2^L*ExactHalfWeightTable.candidateBitBudget L)'
    new = ('decide (plan.bitSteps≤HalfSourceRetainedTranslations.arithmeticBudget m+\n'
           '    2^L*ExactHalfWeightTable.candidateBitBudget L)')
    sources, changes = {}, []
    for path in sorted(FIXED):
        previous = (initial_sources / Path(path).name).read_bytes()
        present = (root / path).read_bytes()
        require(sha_bytes(previous) == initial_snapshot[path], f'{path}: preserved initial source hash mismatch')
        require(sha_bytes(present) == current[path], f'{path}: current source hash mismatch')
        a, b = previous.decode(), present.decode()
        require(a.count(old) == 1, f'{path}: expected one stale budget expression')
        require(a.replace(old, new) == b, f'{path}: changes are not exactly the audited arithmeticBudget addition')
        sources[path] = {'initial': a, 'current': b}
        changes.extend(difflib.unified_diff(a.splitlines(keepends=True), b.splitlines(keepends=True),
                                            fromfile='initial/' + path, tofile='current/' + path))
    return sources, ''.join(changes)


def dump_json(path: Path, obj) -> None:
    path.write_text(json.dumps(obj, indent=2, sort_keys=True) + '\n')


def combined_stream(selected: list[tuple[str, dict]], initial: dict, latest: dict, stream: str) -> bytes:
    pieces = []
    for origin, row in selected:
        run = latest if origin == 'rechecked' else initial
        body = run['streams'][row['path']][stream]
        heading = (f'\n===== {row["path"]} | {origin} | PASS | {stream} =====\n'
                   f'Source SHA-256: {row["sha256"]}\n'
                   f'Command: {json.dumps(row["command"])}\n'
                   f'Exit: {row["returncode"]}; seconds: {row["seconds"]}; output SHA-256: {sha_bytes(body)}\n'
                   '----- captured output begins -----\n').encode()
        pieces += [heading, body, b'\n----- captured output ends -----\n']
    return b''.join(pieces)


def main() -> int:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('--root', type=Path, default=Path('/tmp/thin-matrix-results-sync-20261021'))
    p.add_argument('--initial', type=Path, required=True)
    p.add_argument('--recheck', type=Path, required=True)
    p.add_argument('--verified-log', type=Path, required=True)
    p.add_argument('--output', type=Path, required=True)
    p.add_argument('--initial-fixture-sources', type=Path,
                   default=Path(__file__).resolve().parent / 'initial-fixture-sources')
    args = p.parse_args()
    root, output = args.root.resolve(), args.output.resolve()
    require(output != root and root not in output.parents, 'Evidence output must be outside the frozen source repository')
    require(not output.exists(), 'Output path already exists; preserve earlier evidence')
    require(output.parent.is_dir(), 'Output parent directory must already exist')
    initial, latest = load_run(args.initial, 'initial'), load_run(args.recheck, 'recheck')
    current = current_snapshot(root)
    fixtures = {str(path.relative_to(root)) for path in (root / 'scripts').glob('check_*.lean')}
    selected = validate_coverage(initial, latest, current, fixtures)
    fixture_sources, fixture_diff = validate_fixture_corrections(
        args.initial_fixture_sources, root, initial['snapshot'], current)
    final_kernel = kernel_audit(args.verified_log, current)
    if latest['metadata'].get('verification_gate') is None:
        require(final_kernel['sha256'] == latest['kernel']['sha256'], 'Final kernel log differs from the recheck gate')
    else:
        require(latest['kernel']['sha256'] == initial['kernel']['sha256'],
                'Fixture-only recheck did not use the original complete production proof audit')
        require(read_json(Path(latest['directory']) / 'gate-source-snapshot.json') == initial['snapshot'],
                'Fixture-only recheck gate does not match the initial frozen snapshot')
        require(final_kernel['sha256'] != initial['kernel']['sha256'],
                'Publication still requires the distinct final complete kernel audit')
    initial_root = Path(initial['metadata']['root']).resolve()
    latest_root = Path(latest['metadata']['root']).resolve()
    require(current_snapshot(latest_root) == current,
            'Final recheck working copy does not match the current verified source snapshot')
    initial_live = current_snapshot(initial_root)
    require(initial_live == initial['snapshot'] or initial_live == current,
            'Initial working copy differs from both the permitted initial and current snapshots')
    require(initial['metadata']['warnings_as_errors'] == latest['metadata']['warnings_as_errors'], 'Runtime warning policy differs between runs')
    modes = {'main': 0, 'eval': 0}
    compact = []
    for origin, row in selected:
        source = (root / row['path']).read_text()
        mode = 'main' if re.search(r'^def main\b', source, re.M) else 'eval'
        require(mode == row['mode'], f'{row["path"]}: current execution mode differs')
        require(mode == 'main' or re.search(r'^#eval\b', source, re.M), f'{row["path"]}: no executable fixture')
        modes[mode] += 1
        run = latest if origin == 'rechecked' else initial
        compact.append({key: row[key] for key in ('path', 'sha256', 'mode', 'command', 'seconds', 'returncode', 'warning_lines')} |
                       {'origin': origin, 'passed': True, 'stdout_sha256': sha_bytes(run['streams'][row['path']]['stdout']),
                        'stderr_sha256': sha_bytes(run['streams'][row['path']]['stderr'])})
    require(modes == {'main': 61, 'eval': 10}, f'Unexpected execution modes: {modes}')
    require(current_snapshot(root) == current, 'Source/config changed during merge validation')
    now = datetime.now(timezone.utc).isoformat()
    merged = {'status': 'PASS', 'merged_utc': now, 'source_sha256': digest(current),
              'kernel': final_kernel, 'fixtures': 71, 'passed': 71, 'reused_unchanged': 68,
              'rechecked': 3, 'execution_modes': modes, 'jobs_per_run': 4,
              'fixture_budget_corrections': sorted(FIXED), 'harness_correction': BINARY,
              'initial_status_preserved': {'passed': 68, 'failed': 3},
              'runtime_warnings_as_errors': latest['metadata']['warnings_as_errors'],
              'scope': 'Finite executable fixtures supplement the separately checked Lean theorem; no practical APSP timing claim.',
              'results': compact}
    staging = Path(tempfile.mkdtemp(prefix=f'.{output.name}-', dir=output.parent))
    try:
        dump_json(staging / 'summary.json', merged)
        (staging / 'fixture-corrections.patch').write_text(fixture_diff)
        lines = ['PASS: 71/71 current finite Lean fixtures accounted for.',
                 '68 unchanged passing fixtures reused; 3 targeted rechecks passed.',
                 'This is a provenance-checked merge, not a new simultaneous 71-fixture run.',
                 f'Final kernel audit: {final_kernel["modules"]} modules; {final_kernel["scoped_declarations"]} scoped declarations; standard Lean axioms only.',
                 f'Source/configuration SHA-256: {digest(current)}',
                 'Lean 4.31.0; 61 main fixtures + 10 #eval fixtures; four workers per run; inherited LEAN_PATH removed.',
                 f'Initial working copy: {initial_root}', f'Final recheck working copy: {latest_root}',
                 f'Runtime warnings-as-errors: {latest["metadata"]["warnings_as_errors"]}.', '',
                 'The initial run remains 68 PASS / 3 FAIL. Its failed records were not relabeled.',
                 'Two fixture-only budget expectations were corrected to include translation arithmeticBudget:',
                 *[f'  {path}' for path in sorted(FIXED)],
                 'The binary fixture output was correct in the initial run; the runner incorrectly expected',
                 'raw translations(0).length=1. The correct raw length is 0; the later shifts wrapper has length 1.',
                 ('Targeted rechecks used the initial complete proof audit plus a strict exact-fixture-only gate;'
                  if latest['metadata'].get('verification_gate') else
                  'Targeted rechecks used the complete final kernel audit;'),
                 'the distinct fresh final kernel audit is complete and verified before this merge.',
                 'No Lean proof or configuration source changed between snapshots.', '',
                 'Reproduction: runner-initial.py and runner-corrected.py preserve the exact harnesses.',
                 'provenance.json retains both exact invocations, inventories, snapshots, kernel hashes and original summaries.',
                 'Use the published repository revision matching the source digest above, pinned dependencies,',
                 'and the recorded commands. A full current run may use runner-corrected.py with a fresh matching kernel log.',
                 'Original logs remain untouched. runtime-stdout.log/runtime-stderr.log contain every selected result.',
                 'initial-failures.log retains all three original failed outputs and recorded rejection reasons.',
                 'The initial failure snapshots and final corrected snapshot are distinguished explicitly.', '',
                 merged['scope'], '', 'Selected fixture results (elapsed seconds belong to individual runs):']
        lines += [f'PASS {row["seconds"]:10.3f}s  {row["origin"]:16s}  {row["path"]}' for row in compact]
        (staging / 'summary.txt').write_text('\n'.join(lines) + '\n')
        for stream in ('stdout', 'stderr'):
            (staging / f'runtime-{stream}.log').write_bytes(combined_stream(selected, initial, latest, stream))
        failed_parts = []
        for path in sorted(RECHECKED):
            row = initial['results'][path]
            failed_parts.append((f'\n===== ORIGINAL FAILED RECORD: {path} =====\n' + json.dumps(row, indent=2, sort_keys=True) + '\n').encode())
            for stream in ('stdout', 'stderr'):
                failed_parts += [f'----- original {stream} -----\n'.encode(), initial['streams'][path][stream], b'\n']
        (staging / 'initial-failures.log').write_bytes(b''.join(failed_parts))
        provenance = {'initial': {k: initial[k] for k in ('directory', 'summary', 'metadata', 'snapshot', 'inventory', 'kernel')},
                      'recheck': {k: latest[k] for k in ('directory', 'summary', 'metadata', 'snapshot', 'inventory', 'kernel')},
                      'current_snapshot': current, 'final_complete_kernel_audit': final_kernel,
                      'merger_command': [sys.executable, *sys.argv], 'merger_sha256': sha(Path(__file__)),
                      'snapshot_changed_paths': sorted(FIXED), 'corrected_fixture_sources': fixture_sources}
        dump_json(staging / 'provenance.json', provenance)
        for name, run in (('initial', initial), ('corrected', latest)):
            shutil.copyfile(Path(run['directory']) / 'runner-used.py', staging / f'runner-{name}.py')
        shutil.copyfile(Path(initial['kernel']['path']), staging / 'kernel-initial.log')
        shutil.copyfile(args.verified_log, staging / 'kernel-final.log')
        shutil.copyfile(Path(__file__), staging / 'merge-verified-runs.py')
        manifest = '\n'.join(f'{sha(path)}  {path.name}' for path in sorted(staging.iterdir()) if path.is_file()) + '\n'
        (staging / 'MANIFEST.sha256').write_text(manifest)
        require(current_snapshot(root) == current, 'Source/config changed while writing evidence')
        staging.rename(output)
    except BaseException:
        shutil.rmtree(staging)
        raise
    print(f'PASS: merged 68 unchanged fixture passes with 3 successful rechecks; 71/71 current fixtures.')
    print(f'Evidence: {output}')
    print(f'Source/configuration SHA-256: {digest(current)}')
    return 0


if __name__ == '__main__':
    try:
        raise SystemExit(main())
    except (ValueError, KeyError, FileNotFoundError, json.JSONDecodeError) as exc:
        print(f'REJECTED: {exc}', file=sys.stderr)
        raise SystemExit(1)
