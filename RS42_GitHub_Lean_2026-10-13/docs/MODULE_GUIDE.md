# Module guide

All proof files below are in [`lean/FormalProof/Research003/`](../lean/FormalProof/Research003/).
The library contains 48 proof modules, imported through [`FormalProof.lean`](../lean/FormalProof.lean).

## 90-vertex construction

| File | Role |
|---|---|
| [RS42Counterexample90.lean](../lean/FormalProof/Research003/RS42Counterexample90.lean) | Matching-pair graphs, independent-set/state equivalences, and the explicit graph on 90 vertices. |
| [RS42Counterexample90Library.lean](../lean/FormalProof/Research003/RS42Counterexample90Library.lean) | Interfaces to mathlib's independence number, perfect matchings, and independent-set counts. |
| [RS42Counterexample90Counts.lean](../lean/FormalProof/Research003/RS42Counterexample90Counts.lean) | Decomposes the independent sets into three core states and conditional leaf choices. |
| [RS42Counterexample90CountingTools.lean](../lean/FormalProof/Research003/RS42Counterexample90CountingTools.lean) | Relates finite weighted choices to generating-function coefficients. |
| [RS42Counterexample90Factors.lean](../lean/FormalProof/Research003/RS42Counterexample90Factors.lean) | Computes the five leaf-group factors and the graph's closed independence polynomial. |
| [RS42Counterexample90Polynomial.lean](../lean/FormalProof/Research003/RS42Counterexample90Polynomial.lean) | Proves the polynomial expansion, exact coefficients, and strict arithmetic inequality. |
| [RS42Counterexample90CountFailure.lean](../lean/FormalProof/Research003/RS42Counterexample90CountFailure.lean) | Transfers polynomial coefficients and the strict inequality to actual graph counts. |
| [RS42Counterexample90Target.lean](../lean/FormalProof/Research003/RS42Counterexample90Target.lean) | Defines the conjecture statements and identifies the counterexample's indices. |
| [RS42Counterexample90Tree.lean](../lean/FormalProof/Research003/RS42Counterexample90Tree.lean) | Proves treehood and agreement with the explicit edge table. |
| [RS42Counterexample90Final.lean](../lean/FormalProof/Research003/RS42Counterexample90Final.lean) | Assembles the exact counts and the unconditional 90-vertex counterexample. |

## Prescribed-distance family

| File | Role |
|---|---|
| [RS42FixedKBridge.lean](../lean/FormalProof/Research003/RS42FixedKBridge.lean) | Defines the parameterized graph and connects independent sets to matching-pair states. |
| [RS42FixedKDeletion.lean](../lean/FormalProof/Research003/RS42FixedKDeletion.lean) | Proves the counting identity indexed by deleted matching pairs. |
| [RS42FixedKLeaf.lean](../lean/FormalProof/Research003/RS42FixedKLeaf.lean) | Proves safe extension and count comparisons for deleting original leaves. |
| [RS42FixedKBounds.lean](../lean/FormalProof/Research003/RS42FixedKBounds.lean) | Derives coefficient bounds from core-deletion estimates. |
| [RS42FixedKCore.lean](../lean/FormalProof/Research003/RS42FixedKCore.lean) | Expresses core-deletion counts through core states and conditional leaf choices. |
| [RS42FixedKCoreEvaluate.lean](../lean/FormalProof/Research003/RS42FixedKCoreEvaluate.lean) | Evaluates the leaf factors in the core-deletion count. |
| [RS42FixedKCoreFormula.lean](../lean/FormalProof/Research003/RS42FixedKCoreFormula.lean) | Proves exact formulas for the two types of core deletion. |
| [RS42FixedKCoreAlgebra.lean](../lean/FormalProof/Research003/RS42FixedKCoreAlgebra.lean) | Establishes arithmetic bounds for the two core-count formulas. |
| [RS42FixedKCoreClose.lean](../lean/FormalProof/Research003/RS42FixedKCoreClose.lean) | Proves the three coefficient bounds from the exact core counts. |
| [RS42FixedKParameters.lean](../lean/FormalProof/Research003/RS42FixedKParameters.lean) | Defines and bounds the integer threshold and construction size. |
| [RS42FixedKDecay.lean](../lean/FormalProof/Research003/RS42FixedKDecay.lean) | Proves division-free geometric decay estimates for the envelope numerator. |
| [RS42FixedKQuantitative.lean](../lean/FormalProof/Research003/RS42FixedKQuantitative.lean) | Proves the real envelope's geometric bound and convergence to zero. |
| [RS42FixedKRatio.lean](../lean/FormalProof/Research003/RS42FixedKRatio.lean) | Relates the actual coefficient ratio to the envelope under the coefficient bounds. |
| [RS42FixedKSize.lean](../lean/FormalProof/Research003/RS42FixedKSize.lean) | Proves the logarithmic bound on the initial construction size. |
| [RS42FixedKSizeChain.lean](../lean/FormalProof/Research003/RS42FixedKSizeChain.lean) | Compares the integer and logarithmic size bounds explicitly. |
| [RS42FixedKTree.lean](../lean/FormalProof/Research003/RS42FixedKTree.lean) | Proves treehood, the perfect matching, order, and independence number. |
| [RS42FixedKMatchingNumber.lean](../lean/FormalProof/Research003/RS42FixedKMatchingNumber.lean) | Defines matching number using matching subgraphs and proves its value. |
| [RS42FixedKFinal.lean](../lean/FormalProof/Research003/RS42FixedKFinal.lean) | Assembles fixed-distance counterexamples, actual ratios, size bounds, and conjecture alignment. |

## Structural and asymmetric results

| File | Role |
|---|---|
| [RS42StructuralCore.lean](../lean/FormalProof/Research003/RS42StructuralCore.lean) | Defines weighted core attachments and derives their exact exponent count. |
| [RS42StructuralExponent.lean](../lean/FormalProof/Research003/RS42StructuralExponent.lean) | Defines the admissible core maximum and proves attainment and monotonicity. |
| [RS42StructuralDeletion.lean](../lean/FormalProof/Research003/RS42StructuralDeletion.lean) | Bounds assignment losses under deletion in arbitrary directed relations. |
| [RS42StructuralPadding.lean](../lean/FormalProof/Research003/RS42StructuralPadding.lean) | Extends deletion sets to prescribed cardinality and compares their counts to coefficients. |
| [RS42StructuralBounds.lean](../lean/FormalProof/Research003/RS42StructuralBounds.lean) | Proves core-deletion upper bounds and an attained-exponent lower witness. |
| [RS42StructuralCounts.lean](../lean/FormalProof/Research003/RS42StructuralCounts.lean) | Defines actual graph counts and proves coefficient upper and lower bounds. |
| [RS42StructuralParameters.lean](../lean/FormalProof/Research003/RS42StructuralParameters.lean) | Defines the structural threshold and proves its integer estimates. |
| [RS42StructuralQuantitative.lean](../lean/FormalProof/Research003/RS42StructuralQuantitative.lean) | Proves geometric decay and convergence of the structural envelope. |
| [RS42StructuralRatio.lean](../lean/FormalProof/Research003/RS42StructuralRatio.lean) | Relates the actual ratio to the core exponent gap and binomial envelope. |
| [RS42StructuralConclusion.lean](../lean/FormalProof/Research003/RS42StructuralConclusion.lean) | Proves strict failure, geometric bounds, and convergence from the structural hypotheses. |
| [RS42StructuralTree.lean](../lean/FormalProof/Research003/RS42StructuralTree.lean) | Proves realization, treehood, perfect matching, order, and independence and matching numbers. |
| [RS42StructuralFinal.lean](../lean/FormalProof/Research003/RS42StructuralFinal.lean) | Assembles the structural counterexample and quantitative conclusions. |
| [RS42StructuralAsymmetric.lean](../lean/FormalProof/Research003/RS42StructuralAsymmetric.lean) | Computes the three core maxima for unequal incoming attachment multiplicities. |
| [RS42StructuralAsymmetricFinal.lean](../lean/FormalProof/Research003/RS42StructuralAsymmetricFinal.lean) | Proves the asymmetric graph properties, strict failure, and ratio bounds. |

## Simultaneous failures

| File | Role |
|---|---|
| [RS42SimultaneousCore.lean](../lean/FormalProof/Research003/RS42SimultaneousCore.lean) | Defines the chain of three-vertex blocks and constructs legal maximizing states. |
| [RS42SimultaneousExponent.lean](../lean/FormalProof/Research003/RS42SimultaneousExponent.lean) | Proves the exact core-maximum formula and positive gaps at the target indices. |
| [RS42SimultaneousTree.lean](../lean/FormalProof/Research003/RS42SimultaneousTree.lean) | Proves that the oriented chain core is a tree. |
| [RS42SimultaneousJoint.lean](../lean/FormalProof/Research003/RS42SimultaneousJoint.lean) | Establishes a common threshold and distinct simultaneous failure indices. |
| [RS42SimultaneousFinal.lean](../lean/FormalProof/Research003/RS42SimultaneousFinal.lean) | Constructs one graph with all prescribed failures and identifies its actual counts. |
| [RS42SimultaneousQuantitative.lean](../lean/FormalProof/Research003/RS42SimultaneousQuantitative.lean) | Proves geometric bounds, maximum-ratio convergence, size bounds, and the two-failure specialization. |
