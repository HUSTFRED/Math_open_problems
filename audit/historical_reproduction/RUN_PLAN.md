# Fixed 90-vertex independent reproduction plan

Created 2026-10-04, before mathematical execution.

Exact proposition: the supplied fixed edge list defines a finite simple
90-vertex tree with a perfect matching, independence number 45, and a
strict independence-coefficient log-concavity break at j=nu-1. The
checker must reconstruct every coefficient from the graph. No claimed
coefficient or claimed matching is supplied as an input.

Input preparation selects only `N` and `edges` from the existing
`checks/general_rs42_20261004/RS42_CANDIDATE_p6.json`. An independent
JSON file and complete plain-text edge list preserve these graph data.
Old numerical outputs and programs are not imported. The historical
three neighboring coefficients will be opened for comparison only
after the new computation has finished and its result has been saved.

Algorithm: independently validate simplicity, connectedness and
acyclicity; obtain a matching and vertex cover by leaf elimination;
verify all witness edges and the complementary independent set;
compute the full independence polynomial by memoized vertex deletion
`I(G)=I(G-v)+x I(G-N[v])`, factoring disconnected induced subgraphs.
This is a general graph-deletion implementation. It does not use the
old rooted two-state DP, the 64-core-state expansion, the oriented
matching-block model, or the parameter-p formulas.

Scope and resource limits: exactly this one N=90 graph, no graph
generation, parameter sweep, random search or smallest-example search;
one CPU affinity; address-space hard limit 512 MiB; CPU hard limit
120 seconds; external wall-clock kill at 120 seconds. No automatic
retry after a mathematical or resource failure. No legacy certificate
is changed or deleted.

Positive outcome establishes an independently reconstructed finite
counterexample and checks the saved graph against its historical
three-number record. It does not by itself prove the infinite family
or constitute Lean/Danus verifier acceptance. A mismatch, failed graph
check, failed witness, nonnegative difference or exceeded resource limit
stops this run and is preserved as a failure.

Record source, input, interpreter/version, exact command, timestamps,
exit code, stdout, stderr, wall/CPU time, RSS, AS limits and CPU affinity.
Freeze SHA-256 values of the source, input and resulting artifacts.
