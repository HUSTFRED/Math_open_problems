#!/usr/bin/env python3
"""Record one resource-bounded run; does not inspect historical numbers."""
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import resource
import subprocess
import sys
import time


root = Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_AS, (512 * 1024 * 1024,) * 2)
os.sched_setaffinity(0, {min(os.sched_getaffinity(0))})
command = ["/usr/bin/time", "-v", "-o", "run.time.txt",
           "/usr/bin/timeout", "--signal=KILL", "120s",
           sys.executable, "check_tree90.py"]
started = datetime.now(timezone.utc).isoformat()
start = time.perf_counter()
record = {
    "started_utc": started,
    "command": command,
    "working_directory": str(root),
    "scope": "one fixed graph; no historical numerical input",
    "source_sha256_before": hashlib.sha256((root / "check_tree90.py").read_bytes()).hexdigest(),
    "graph_sha256_before": hashlib.sha256((root / "tree90_edges.json").read_bytes()).hexdigest(),
    "run_plan_sha256": hashlib.sha256((root / "RUN_PLAN.md").read_bytes()).hexdigest(),
    "python_version": sys.version,
    "status": "STARTED",
}
(root / "RUN_STARTED.json").write_text(json.dumps(record, indent=2) + "\n")
with (root / "run.stdout.json").open("wb") as stdout, (root / "run.stderr").open("wb") as stderr:
    completed = subprocess.run(command, cwd=root, stdout=stdout, stderr=stderr,
                               check=False)
record.update({
    "finished_utc": datetime.now(timezone.utc).isoformat(),
    "elapsed_wall_seconds": time.perf_counter() - start,
    "exit_code": completed.returncode,
    "status": "PROCESS_COMPLETED" if completed.returncode == 0 else "FAILED_STOPPED",
    "controller_max_rss_KiB": resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,
    "controller_AS_limit_bytes": list(resource.getrlimit(resource.RLIMIT_AS)),
    "controller_cpu_affinity": sorted(os.sched_getaffinity(0)),
    "stdout_sha256": hashlib.sha256((root / "run.stdout.json").read_bytes()).hexdigest(),
    "stderr_sha256": hashlib.sha256((root / "run.stderr").read_bytes()).hexdigest(),
})
(root / "RUN_RECORD.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
sys.exit(completed.returncode)
