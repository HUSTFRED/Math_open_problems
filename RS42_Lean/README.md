# Trees with perfect matchings: Lean formalization

Lean sources accompanying **Prescribed and simultaneous failures of log-concavity in trees with perfect matchings**, by **Heshun Fan**.

The formalization studies failures of log-concavity in independence sequences of trees with perfect matchings. It includes the explicit 90-vertex counterexample to Conjecture 4.2 of Ramos and Sun, counterexamples at any prescribed distance from the independence number, a criterion for weighted core constructions, and simultaneous failures in a single tree.

## Start here

- [Proof map](PROOF_MAP.md): the main results and their Lean entry points.
- [Module guide](docs/MODULE_GUIDE.md): the role of each of the 48 proof modules.
- [Library entry point](lean/FormalProof.lean): imports all the result families.
- [90-vertex graph](graph/tree90_edges.json): the explicit graph on vertices `0` through `89`.

## Main result families

| Result | Entry file |
|---|---|
| Exact 90-vertex counterexample and independent-set counts | [RS42Counterexample90Final.lean](lean/FormalProof/Research003/RS42Counterexample90Final.lean) |
| Failures at a prescribed distance, ratio bounds, and size estimates | [RS42FixedKFinal.lean](lean/FormalProof/Research003/RS42FixedKFinal.lean), [RS42FixedKSizeChain.lean](lean/FormalProof/Research003/RS42FixedKSizeChain.lean) |
| Structural criterion for weighted core constructions | [RS42StructuralFinal.lean](lean/FormalProof/Research003/RS42StructuralFinal.lean) |
| Unequal incoming attachment multiplicities | [RS42StructuralAsymmetricFinal.lean](lean/FormalProof/Research003/RS42StructuralAsymmetricFinal.lean) |
| Simultaneous failures, quantitative bounds, and the two-failure specialization | [RS42SimultaneousFinal.lean](lean/FormalProof/Research003/RS42SimultaneousFinal.lean), [RS42SimultaneousQuantitative.lean](lean/FormalProof/Research003/RS42SimultaneousQuantitative.lean) |

## Build

Install [elan](https://github.com/leanprover/elan) and Git, then run:

```sh
git clone https://github.com/HUSTFRED/Math_open_problems.git
cd Math_open_problems/lean
lake exe cache get
lake build FormalProof
```

The project uses **Lean 4.34.0**, as specified in [lean-toolchain](lean/lean-toolchain). [lake-manifest.json](lean/lake-manifest.json) pins mathlib to `56a9a88447f391672d7aeea117da03b6f7016b0d` and records the exact revisions of its transitive dependencies. Keep this manifest when reproducing the results; `lake update` changes the dependency resolution.

The first setup retrieves the pinned dependencies. `lake exe cache get` downloads compiled mathlib dependencies and can reduce build time. `lake build FormalProof` compiles the local library and all its imported proof modules.

## Repository contents

| Path | Purpose |
|---|---|
| `lean/FormalProof/Research003/` | 48 proof modules |
| `lean/FormalProof.lean` | Library entry point |
| `lean/lakefile.toml` | Lake project settings and library target |
| `lean/lake-manifest.json` | Dependency revision lock |
| `lean/lean-toolchain` | Lean compiler version |
| `graph/tree90_edges.json` | Edge list of the explicit 90-vertex graph |
| `PROOF_MAP.md` | Main theorem names, namespaces, and scope |
| `docs/MODULE_GUIDE.md` | File-by-file source guide |
| `SHA256SUMS` | File integrity manifest |
| `scripts/verify_package.py` | Cross-platform integrity check using Python 3.10 or later |

From the repository root, file integrity can be checked with:

```sh
python scripts/verify_package.py
```

This checks the files against `SHA256SUMS`. Use the Lean build command above to check the formal proofs.
