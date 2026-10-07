# Independent fixed-graph reproduction result

Run: 2026-10-04 08:33:18.895750 to 08:33:19.862784 UTC. Exit code 0;
standard error empty. One mathematical run was performed; no retry,
parameter expansion, or search was performed.

The input has 90 vertices and 89 edges. Direct checks confirm a finite
simple connected acyclic bipartite graph. A newly constructed perfect
matching has 45 edges; a newly constructed 45-vertex cover and its
45-vertex independent complement certify nu=alpha=45. The complete
independence polynomial was rebuilt from the edge list by induced
graph deletion and component multiplication.

The reconstructed neighboring coefficients are:

| Index | Independent graph-deletion coefficient |
|---|---:|
| 43 | 4761097500672 |
| 44 | 5965496320 |
| 45 | 17567744 |

The exact difference is

    a_44^2-a_43*a_45 = -48054595706911981568 < 0.

Here h=45, beta=1, j=44, while alpha=45<47=h+beta+1. Thus the fixed
graph directly violates the project's explicit RS4.2 implication.
The degree, all coefficients, witnesses and original graph checks are
saved in `run.stdout.json`.

The result and source were frozen in `NEW_RESULT_FROZEN_SHA256SUMS`
before historical numerical fields were read. The post-run comparison
at 08:34:57.506742 UTC found equality of the three coefficients and
the signed difference, with the same N/edge projection. See
`HISTORICAL_COMPARISON.json`. Historical numbers were not inputs to
the new mathematical program.

The new code uses ordinary induced-subgraph bit masks, maximum-degree
vertex deletion, closed-neighborhood deletion and connected-component
factorization. It does not import old code, use rooted P/Q states,
enumerate the symbolic core states, or assume the matching-block
coefficient formulas. The run used 130 memoized induced subgraphs,
51 vertex-deletion splits and 17 component factorizations.

Resource measurements remain distinct:

| Measurement | Observed or enforced value |
|---|---:|
| Interpreter | CPython 3.12.3 |
| Recorded whole run, wall | 0.967015640984755 s |
| GNU time wall | 0.94 s |
| Checker core wall, after startup | 0.05740266598877497 s |
| GNU time maximum RSS | 17888 KiB |
| Checker self maximum RSS | 17760 KiB |
| Recording controller self maximum RSS | 240748 KiB |
| Checker and controller AS hard limits | 536870912 bytes each |
| Mathematical CPU affinity | CPU 0 only |
| CPU hard limit | 120 s |
| External wall kill | 120 s |

RSS is a resident-memory high-water measurement; AS is a distinct
address-space limit. The larger controller high-water value is retained
as reported instead of being substituted for the mathematical child
measurement. All were within the frozen limits. Exact command,
interpreter build, timestamps and source/input hashes appear in
`RUN_RECORD.json` and `run.time.txt`.

This establishes fresh finite executable verification of the supplied
graph. It is separate from the infinite-family written proof, Danus
verifier review, and Lean kernel verification. SHA-256 checks establish
integrity of these artifacts, not correctness of their mathematics.
