#!/usr/bin/env python3
"""Post-run comparison only; never imported by check_tree90.py."""
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import sys


root = Path(__file__).resolve().parent
run_record = json.loads((root / "RUN_RECORD.json").read_text())
if run_record["exit_code"] != 0:
    raise RuntimeError("no successful new run to compare")
for line in (root / "NEW_RESULT_FROZEN_SHA256SUMS").read_text().splitlines():
    expected, name = line.split("  ", 1)
    actual = hashlib.sha256((root / name).read_bytes()).hexdigest()
    if actual != expected:
        raise RuntimeError("new-run freeze changed before comparison: " + name)

new = json.loads((root / "run.stdout.json").read_text())
graph = json.loads((root / "tree90_edges.json").read_text())
historical_path = (root.parents[1] / "general_rs42_20261004" /
                   "RS42_CANDIDATE_p6.json")
historical_raw = historical_path.read_bytes()
historical = json.loads(historical_raw)
j = new["j"]
comparisons = []
for k in (j - 1, j, j + 1):
    new_value = new["full_coefficients"][k]
    old_value = historical["coefficients_root_DP"][k]
    comparisons.append({"index": k, "independent_graph_deletion": new_value,
                        "historical_root_DP": old_value,
                        "equal": new_value == old_value})
graph_equal = (graph == {"N": historical["N"], "edges": historical["edges"]})
same_difference = new["log_concavity_difference"] == historical["L"]
passed = graph_equal and same_difference and all(item["equal"] for item in comparisons)
record = {
    "compared_utc": datetime.now(timezone.utc).isoformat(),
    "new_run_finished_utc": run_record["finished_utc"],
    "independent_result_was_frozen_before_historical_comparison": True,
    "historical_path": str(historical_path),
    "historical_sha256": hashlib.sha256(historical_raw).hexdigest(),
    "historical_coefficient_field": "coefficients_root_DP",
    "historical_coefficients_used_only_after_new_run": True,
    "graph_only_projection_matches": graph_equal,
    "coefficient_comparisons": comparisons,
    "signed_difference_equal": same_difference,
    "status": "PASS" if passed else "FAIL_STOPPED",
    "limit": "Equality is a post-run cross-check, not an input to the new counting algorithm.",
}
(root / "HISTORICAL_COMPARISON.json").write_text(json.dumps(record, indent=2) + "\n")
print(json.dumps(record, indent=2))
sys.exit(0 if passed else 2)
