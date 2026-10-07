# Independent reproduction of the fixed 90-vertex counterexample

On Ubuntu with Python 3, run:

```bash
python3 check_tree90.py
```

The command writes a complete JSON result to standard output. It uses
only the Python standard library and the neighboring `tree90_edges.json`.
No old result or executable is needed. The checker enforces one CPU,
512 MiB address space, and 120-second CPU and wall limits. For a saved
output, append `> my_result.json`.

`tree90_edges.json` has only N and the complete undirected edge list.
`tree90_edges.txt` presents the same data: first line N, then one pair
of zero-based vertex labels per line. This is one fixed graph; the
program is not a tree search or parameterized family generator.

## Why the counting algorithm is correct

For every induced subgraph G and chosen vertex v, independent sets
partition into those excluding v and those including v. The first
class is counted by I(G-v); the second is in bijection with independent
sets of G-N[v], with v adding one element. Therefore

    I(G)=I(G-v)+x I(G-N[v]).

Independent sets in separate connected components can be chosen
independently, so their polynomials multiply. The empty graph has
polynomial 1; a singleton has 1+x. These identities prove the recursive
implementation by induction on the number of vertices. Choosing a
maximum-degree vertex changes only efficiency. Memoization stores the
same induced graph polynomial and changes no arithmetic. All polynomial
operations use Python arbitrary-precision integers.

This recurrence operates on ordinary graph subsets. It does not use
the old root-in/root-out dynamic program, the explicit six-vertex
core expansion, the oriented matching-block graph, or a symbolic formula
in p. Independence here means a fresh source and different decomposition,
not a claim of independence from Python, hardware, or elementary common
counting identities.

## Why the graph witnesses are conclusive

The checker validates edge endpoints, duplicate edges, connectedness,
acyclicity and bipartition directly. At a leaf l with neighbor v, some
maximum matching contains lv: if l is unmatched, either add lv when
v is unmatched or replace v's matching edge by lv. Removing the matched
pair reduces the maximum matching number by one. Repeating yields the
saved matching. Choosing each matched neighbor v also produces a vertex
cover: every edge removed at that step touches v, except lv which also
touches v. Both witness conditions are explicitly checked against the
original edges.

A matching and equal-size vertex cover certify their optimality. The
complement of the cover is an independently checked independent set.
On this fixed graph the matching is perfect and the complementary
independent set has one vertex per matched edge, proving alpha=nu=N/2.
The separately reconstructed polynomial must have exactly that degree.

The result records all coefficients and all witnesses, the relevant
three coefficients, their exact signed difference, and the original
even-order RS4.2 indices. It checks the graph-specific strict failure.
This executable verification is distinct from the written infinite-family
proof, a Danus verifier acceptance, and Lean kernel acceptance.

## Recorded run

See `RUN_PLAN.md` for the scope frozen before execution, `run.stdout.json`
for the independently computed result, `run.stderr`, `run.time.txt`, and
`RUN_RECORD.json` for the process evidence. `HISTORICAL_COMPARISON.json`
is created only after that result has been saved. `SHA256SUMS` protects
artifact integrity; a matching hash is not mathematical verification.
