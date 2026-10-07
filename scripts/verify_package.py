from pathlib import Path
import hashlib
import sys

root = Path(__file__).resolve().parents[1]
checked = 0
failures = []
for line in (root / 'SHA256SUMS').read_text(encoding='utf-8').splitlines():
    if not line: continue
    expected, relative = line.split('  ', 1)
    path = (root / relative).resolve()
    if not path.is_relative_to(root):
        failures.append(relative + ': unsafe path')
        continue
    if not path.is_file():
        failures.append(relative + ': missing')
        continue
    actual = hashlib.sha256(path.read_bytes()).hexdigest()
    if actual != expected: failures.append(relative + ': hash differs')
    checked += 1
if failures:
    print('\n'.join(failures))
    sys.exit(1)
print(f'PASS: {checked} files match SHA256SUMS. This is an integrity check, not proof verification.')
