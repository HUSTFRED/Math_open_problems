#!/usr/bin/env python3
"""Portable serial source build. Copy this file to the delivered package as build.py.

Only standard locked dependency caches are reused. Each invocation creates a
fresh output directory and recompiles every local transitive import.
"""
import datetime
import fcntl
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import resource
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent
ENTRY = 'FormalProof'
TIMEOUT = 600
RSS_KIB = 3 * 1024**2
AVAILABLE_KIB = 768 * 1024


def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def main():
    assert (ROOT / 'FormalProof.lean').is_file(), 'Run the script in the delivered source package'
    started = datetime.datetime.now(datetime.timezone.utc)
    run = ROOT / 'builds' / started.strftime('%Y%m%dT%H%M%S_%fZ')
    run.mkdir(parents=True, exist_ok=False)
    output = run / 'lib/lean'
    output.mkdir(parents=True)
    manifest = json.loads((ROOT / 'lake-manifest.json').read_text())
    dependency_paths = []
    dependency_records = []
    for p in manifest['packages']:
        d = ROOT / '.lake/packages' / p['name']
        cache = d / '.lake/build/lib/lean'
        if cache.is_dir():
            dependency_paths.append(cache.resolve())
        git_rev = subprocess.run(['git', '-C', str(d), 'rev-parse', 'HEAD'],
                                 text=True, capture_output=True, check=True).stdout.strip()
        if git_rev != p['rev']:
            raise RuntimeError('Dependency revision differs from lock: ' + p['name'])
        dependency_records.append({'name': p['name'], 'revision': git_rev,
                                   'cache': str(cache.resolve()),
                                   'cache_present': cache.is_dir()})
    lean = shutil.which('lean')
    if lean is None:
        candidate = Path.home() / '.elan/bin/lean'
        if candidate.is_file():
            lean = str(candidate)
    if lean is None:
        raise RuntimeError('Lean/elan not found; see README')
    env = dict(os.environ)
    env.pop('LEAN_PATH', None)
    env.pop('LEAN_SRC_PATH', None)
    env['LEAN_PATH'] = ':'.join(map(str, [output.resolve(), *dependency_paths]))
    env['LEAN_NUM_THREADS'] = env['LEANTHREADS'] = '1'
    version = subprocess.run([lean, '--version'], cwd=ROOT, env=env,
                             text=True, capture_output=True, check=True).stdout.strip()
    required = (ROOT / 'lean-toolchain').read_text().strip().split(':v')[-1]
    if 'version ' + required + ',' not in version:
        raise RuntimeError('Lean version mismatch: ' + version)

    order = []
    visiting = set()
    seen = set()
    def visit(module):
        if module in seen:
            return
        if module in visiting:
            raise RuntimeError('Cyclic local imports: ' + module)
        visiting.add(module)
        source = ROOT / (module.replace('.', '/') + '.lean')
        if not source.is_file():
            raise RuntimeError('Missing delivered source: ' + str(source))
        for line in source.read_text().splitlines():
            m = re.match(r'^\s*(?:public\s+)?(?:meta\s+)?import\s+(.+?)\s*$', line)
            if m:
                for dep in m.group(1).split():
                    if dep == 'FormalProof' or dep.startswith('FormalProof.'):
                        visit(dep)
        visiting.remove(module)
        seen.add(module)
        order.append((module, source))
    visit(ENTRY)

    records = []
    for index, (module, source) in enumerate(order):
        print('Building ' + module, flush=True)
        target = output / (module.replace('.', '/') + '.olean')
        target.parent.mkdir(parents=True, exist_ok=True)
        source_hash = digest(source)
        log = run / (f'{index:02d}_' + module + '.log')
        command = [lean, '-j1', '-s8192', '-M2304', '-DwarningAsError=true',
                   '-Dweak.linter.mathlibStandardSet=true', '-o', str(target),
                   str(source.relative_to(ROOT))]
        t0 = time.monotonic()
        peak = virtual = 0
        low_available = None
        reason = None
        with log.open('x') as stream:
            p = subprocess.Popen(command, cwd=ROOT, env=env, stdout=stream,
                                 stderr=subprocess.STDOUT, start_new_session=True)
            cpu = min(os.sched_getaffinity(0))
            os.sched_setaffinity(p.pid, {cpu})
            while p.poll() is None:
                try:
                    fields = dict(l.split(':', 1) for l in
                                  Path(f'/proc/{p.pid}/status').read_text().splitlines() if ':' in l)
                    rss = int(fields.get('VmRSS', '0').split()[0])
                    vas = int(fields.get('VmSize', '0').split()[0])
                    peak, virtual = max(peak, rss), max(virtual, vas)
                    if rss > RSS_KIB:
                        reason = 'sampled process RSS guard'
                except (FileNotFoundError, ProcessLookupError):
                    pass
                memory = dict(l.split(':', 1) for l in Path('/proc/meminfo').read_text().splitlines())
                available = int(memory['MemAvailable'].split()[0])
                low_available = available if low_available is None else min(low_available, available)
                if available < AVAILABLE_KIB:
                    reason = 'system available memory floor'
                if time.monotonic() - t0 > TIMEOUT:
                    reason = 'wall time guard'
                if reason:
                    try:
                        os.killpg(p.pid, signal.SIGKILL)
                    except ProcessLookupError:
                        pass
                    break
                time.sleep(0.1)
            code = p.wait()
        row = {'module': module, 'source': str(source.relative_to(ROOT)),
               'source_sha256': source_hash, 'source_unchanged': digest(source) == source_hash,
               'command': command, 'exit_code': code, 'termination_reason': reason,
               'seconds': time.monotonic() - t0, 'peak_rss_kib_sampled': peak,
               'peak_virtual_kib_sampled': virtual,
               'minimum_available_kib_sampled': low_available, 'cpu': cpu,
               'log': str(log.relative_to(ROOT)),
               'output': str(target.relative_to(ROOT))}
        records.append(row)
        (run / 'MODULE_RESULTS.json').write_text(json.dumps(records, indent=2) + '\n')
        if code or not row['source_unchanged']:
            print(log.read_text(), file=sys.stderr)
            raise RuntimeError('Source build failed: ' + module)
    success = {'started_utc': started.isoformat(),
               'finished_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
               'platform': platform.platform(), 'python': sys.version, 'lean': version,
               'entry': ENTRY, 'all_local_sources_recompiled': True,
               'local_import_order': [m for m, _ in order],
               'dependency_revisions': dependency_records, 'lean_path': env['LEAN_PATH'],
               'lock_sha256': digest(ROOT / 'lake-manifest.json'),
               'toolchain_sha256': digest(ROOT / 'lean-toolchain'),
               'build_script_sha256': digest(Path(__file__)),
               'module_results': records, 'wall_limit_per_module_seconds': TIMEOUT,
               'rss_guard_kib': RSS_KIB, 'available_floor_kib': AVAILABLE_KIB,
               'as_hard_limit': None, 'controller_maxrss_kib':
               resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
               'note': 'Only current run local .olean directory and standard dependency caches used'}
    (run / 'BUILD_SUCCESS.json').write_text(json.dumps(success, indent=2) + '\n')
    print('SUCCESS: ' + str(run.relative_to(ROOT) / 'BUILD_SUCCESS.json'), flush=True)


if __name__ == '__main__':
    with (ROOT / '.build.lock').open('a') as build_lock:
        fcntl.flock(build_lock.fileno(), fcntl.LOCK_EX)
        main()
