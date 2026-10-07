module

public import FormalProof.Research003.RS42Counterexample90Target
public import FormalProof.Research003.RS42Counterexample90Tree
public import FormalProof.Research003.RS42Counterexample90CountFailure

set_option linter.style.header false
set_option linter.hashCommand false

/-!
The unconditional, actual-graph counterexample to Ramos--Sun Conjecture 4.2.
The witness is the fixed graph on Fin 90, linked to the literal edge table.
Every coefficient counts genuine independent vertex subsets. The theorem
has no treehood, counting, arithmetic-failure or conjecture-negation premise.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

/-- Exact coefficients of the actual graph, not a supplied numeric sequence. -/
theorem graph90_actual_coefficients :
    independenceCount graph90 43 = 4761097500672 ∧
    independenceCount graph90 44 = 5965496320 ∧
    independenceCount graph90 45 = 17567744 := by
  simp only [independenceCount_eq_coefficient]
  exact ⟨graph90_coefficient43, graph90_coefficient44, graph90_coefficient45⟩

/-- The complete 90-vertex witness, with no unproved parameter hypotheses. -/
theorem graph90_counterexample :
    graph90.IsTree ∧ graph90.indepNum = 45 ∧
      independenceCount graph90 44 ^ 2 <
        independenceCount graph90 43 * independenceCount graph90 45 ∧
      ¬ (47 ≤ graph90.indepNum) := by
  refine ⟨graph90_isTree, graph90_indepNum, ?_, ?_⟩
  · simpa only [independenceCount_eq_coefficient] using graph90_count_failure
  · rw [graph90_indepNum]
    decide

/-- A standalone graph-theoretic existence statement with true set cardinalities. -/
theorem exists_counterexample90 :
    ∃ T : SimpleGraph (Fin 90), T.IsTree ∧ T.indepNum = 45 ∧
      (Nat.card {s : Finset (Fin 90) // T.IsNIndepSet 44 s}) ^ 2 <
        Nat.card {s : Finset (Fin 90) // T.IsNIndepSet 43 s} *
        Nat.card {s : Finset (Fin 90) // T.IsNIndepSet 45 s} ∧
      ¬ (47 ≤ T.indepNum) :=
  ⟨graph90, graph90_counterexample⟩

/-- The original even-order, beta=1 universal instance is false. -/
theorem not_RamosSun42EvenBetaOne90 : ¬ RamosSun42EvenBetaOne90 :=
  not_evenBetaOne90_of_tree_and_failure graph90_isTree graph90_count_failure

/-- Consequently the project-explicit all-tree conjecture is false as well. -/
theorem not_RamosSun42Explicit : ¬ RamosSun42Explicit :=
  fun h => not_RamosSun42EvenBetaOne90 (explicit_implies_evenBetaOne90 h)

#check graph90
#check graph90_adj_iff_fixedEdges
#check fixed_indices
#check graph90_counterexample
#check exists_counterexample90
#check not_RamosSun42EvenBetaOne90
#check not_RamosSun42Explicit

#print axioms graph90_adj_iff_fixedEdges
#print axioms graph90_isTree
#print axioms graph90_indepNum
#print axioms matching90_isPerfectMatching
#print axioms graph90_actual_coefficients
#print axioms graph90_counterexample
#print axioms exists_counterexample90
#print axioms not_RamosSun42EvenBetaOne90
#print axioms not_RamosSun42Explicit

end FormalProof.Research003.RS42Counterexample90
