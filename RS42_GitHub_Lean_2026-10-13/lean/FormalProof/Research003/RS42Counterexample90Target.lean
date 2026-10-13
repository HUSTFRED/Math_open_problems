module

public import FormalProof.Research003.RS42Counterexample90Library
public import Mathlib.Combinatorics.SimpleGraph.Acyclic

set_option linter.style.header false

/-!
The exact conjecture statements used by the fixed counterexample. All counts
are cardinalities of actual graph-independent finite vertex sets. The final
unconditional witness will be assembled in RS42Counterexample90Final.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

/-- The cardinality of the genuine `k`-element independent vertex sets. -/
noncomputable def independenceCount {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) : ℕ :=
  Nat.card {s : Finset (Fin n) // G.IsNIndepSet k s}

theorem independenceCount_eq_coefficient {n : ℕ} (G : SimpleGraph (Fin n)) (k : ℕ) :
    independenceCount G k = coefficient G k := by
  apply Nat.card_congr
  exact {
    toFun := fun s => ⟨s.1, s.2.isIndepSet, s.2.card_eq⟩
    invFun := fun s => ⟨s.1, ⟨s.2.1, s.2.2⟩⟩
    left_inv := fun _ => Subtype.ext rfl
    right_inv := fun _ => Subtype.ext rfl }

/-- The unambiguous even-order, beta=1 instance asserted for all 90-vertex trees. -/
def RamosSun42EvenBetaOne90 : Prop :=
  ∀ T : SimpleGraph (Fin 90), T.IsTree →
    independenceCount T 44 ^ 2 < independenceCount T 43 * independenceCount T 45 →
    47 ≤ T.indepNum

/-- Project-explicit quantifiers: beta and j are natural numbers and j+beta=floor(N/2).
The witness uses even N and beta=1, so no unspecified beta boundary is needed. -/
def RamosSun42Explicit : Prop :=
  ∀ (N : ℕ), 1 ≤ N → ∀ T : SimpleGraph (Fin N), T.IsTree →
    ∀ j beta : ℕ, 1 ≤ j → j + beta = N / 2 →
      independenceCount T j ^ 2 <
        independenceCount T (j - 1) * independenceCount T (j + 1) →
      N / 2 + beta + 1 ≤ T.indepNum

theorem explicit_implies_evenBetaOne90 :
    RamosSun42Explicit → RamosSun42EvenBetaOne90 := by
  intro h T hT hgap
  exact h 90 (by decide) T hT 44 1 (by decide) (by decide) hgap

theorem fixed_indices :
    Fintype.card (Fin 90) = 90 ∧ 90 / 2 = 45 ∧
      1 ≤ (44 : ℕ) ∧ 44 + 1 = (90 : ℕ) / 2 ∧
      (44 : ℕ) - 1 = 43 ∧ (44 : ℕ) + 1 = 45 ∧
      (90 : ℕ) / 2 + 1 + 1 = 47 := by
  simp

/-- A semantic conclusion lemma, not the final unconditional counterexample. -/
theorem not_evenBetaOne90_of_tree_and_failure
    (hTree : graph90.IsTree)
    (hFailure : coefficient graph90 44 ^ 2 <
      coefficient graph90 43 * coefficient graph90 45) :
    ¬ RamosSun42EvenBetaOne90 := by
  intro h
  have hgap : independenceCount graph90 44 ^ 2 <
      independenceCount graph90 43 * independenceCount graph90 45 := by
    simpa only [independenceCount_eq_coefficient] using hFailure
  have hfalse := h graph90 hTree hgap
  rw [graph90_indepNum] at hfalse
  exact (by decide : ¬ (47 : ℕ) ≤ 45) hfalse


end FormalProof.Research003.RS42Counterexample90
