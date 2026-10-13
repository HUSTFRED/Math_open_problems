# Proof map

This guide follows the formalization described in Section 8 of *Prescribed and simultaneous failures of log-concavity in trees with perfect matchings* by Heshun Fan.

All namespaces below have the prefix `FormalProof.Research003`. The [library entry point](lean/FormalProof.lean) imports the complete collection. The [module guide](docs/MODULE_GUIDE.md) describes the supporting files.

## Prescribed-distance family: Section 8.1

Namespace: `FormalProof.Research003.RS42FixedK`.

In [RS42FixedKFinal.lean](lean/FormalProof/Research003/RS42FixedKFinal.lean):

- `fixed_k_counterexample`: the graph properties and strict failure at the prescribed distance, under the stated positive-distance and scale hypotheses.
- `fixed_k_strict_failure`: the strict comparison of independent-set counts.
- `actualRatio_eq_indepCount`: identifies the formal ratio with actual independent-set counts.
- `actualRatio_le_envelope`, `actualRatio_geometric`, and `actualRatio_tendsto_zero`: the envelope, geometric bound, and limiting ratio.
- `fixed_k_initial_size`: bounds the initial construction size.
- `fixed_k_rs42_alignment`: aligns the construction with the parameters of the conjecture.

[RS42FixedKSizeChain.lean](lean/FormalProof/Research003/RS42FixedKSizeChain.lean) proves `integer_size_bound_le_log_bound`, the explicit comparison between the integer and logarithmic size bounds.

## Structural and asymmetric results: Section 8.2

Namespace: `FormalProof.Research003.RS42Structural`.

[RS42StructuralFinal.lean](lean/FormalProof/Research003/RS42StructuralFinal.lean) provides `structural_counterexample` and `structural_quantitative_conclusion`, under the core-tree, orientation, weight, exponent-gap, and scale hypotheses stated in the source.

In the subnamespace `FormalProof.Research003.RS42Structural.Asymmetric`:

- [RS42StructuralAsymmetric.lean](lean/FormalProof/Research003/RS42StructuralAsymmetric.lean) proves `three_maxima` for the unequal incoming attachment construction.
- [RS42StructuralAsymmetricFinal.lean](lean/FormalProof/Research003/RS42StructuralAsymmetricFinal.lean) supplies `asymmetric_counterexample`, `ratio_geometric`, and `ratio_tendsto_zero`, along with the graph properties.

## Simultaneous failures: Section 8.2

Namespace: `FormalProof.Research003.RS42Simultaneous`.

- [RS42SimultaneousExponent.lean](lean/FormalProof/Research003/RS42SimultaneousExponent.lean): `maximum_formula`, the exact core-maximum formula.
- [RS42SimultaneousFinal.lean](lean/FormalProof/Research003/RS42SimultaneousFinal.lean): `simultaneous_counterexample`, which binds a single graph and proves the distinct failure indices; `real_count_definition` identifies the counts with independent vertex sets.
- [RS42SimultaneousQuantitative.lean](lean/FormalProof/Research003/RS42SimultaneousQuantitative.lean): `ratio_geometric`, `maxRatio_tendsto_zero`, `threshold_bound`, `initial_size_bound`, and `two_place_counterexample`.

The finite 180-vertex example in the paper is supported by its separate integer coefficient calculation. The Lean theorem `two_place_counterexample` concerns the family at scales at least `14400`.

## Exact 90-vertex example: Section 8.3

Namespace: `FormalProof.Research003.RS42Counterexample90`.

- [RS42Counterexample90CountFailure.lean](lean/FormalProof/Research003/RS42Counterexample90CountFailure.lean): `graph90_coefficient_eq_polynomial`, connecting the independence polynomial to actual independent-set counts.
- [RS42Counterexample90Tree.lean](lean/FormalProof/Research003/RS42Counterexample90Tree.lean): treehood and the connection to the explicit edge list.
- [RS42Counterexample90Final.lean](lean/FormalProof/Research003/RS42Counterexample90Final.lean): `graph90_actual_coefficients`, `graph90_counterexample`, `exists_counterexample90`, `not_RamosSun42EvenBetaOne90`, and `not_RamosSun42Explicit`.

The explicit graph has 90 vertices, a perfect matching, and independence number 45. Its coefficients satisfy:

```text
a_43 = 4761097500672
a_44 = 5965496320
a_45 = 17567744
a_44^2 - a_43*a_45 = -48054595706911981568
```

[tree90_edges.json](graph/tree90_edges.json) contains the graph's 89 edges. The `EvenBetaOne90` statement isolates the even-order, `beta = 1` instance; `RamosSun42Explicit` is the separately named explicit natural-number formulation in the source.

## Definitions used by the formalization

The coefficient counts are cardinalities of collections of independent vertex sets. The project matching number is defined using genuine matching subgraphs. Intermediate estimates retain their hypotheses in their Lean statements; the final construction theorems supply the required graph and counting properties.
