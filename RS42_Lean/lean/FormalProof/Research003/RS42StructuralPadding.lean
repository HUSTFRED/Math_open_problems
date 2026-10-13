module

public import FormalProof.Research003.RS42StructuralDeletion
public import FormalProof.Research003.RS42FixedKBounds

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
Complete any deletion set to the prescribed cardinality, then compare its
induced-deletion count with the genuine independent-set coefficient. No
assumption about leaves or about coefficient bounds is used.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural

open RS42FixedKDeletion RS42Counterexample90

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The loss depends only on the number of labels needed to complete C. -/
theorem omegaCount_le_pow_sub_card_mul_coefficient (arrow : ι → ι → Prop)
    (C : Finset ι) (r : ℕ) (hCr : C.card ≤ r) (hr : r ≤ Fintype.card ι) :
    omegaCount arrow C ≤ 2 ^ (r - C.card) *
      coefficient (splitGraph arrow) (Fintype.card ι - r) := by
  classical
  obtain ⟨Z, hCZ, _, hZ⟩ := Finset.exists_subsuperset_card_eq
    (s := C) (t := (Finset.univ : Finset ι)) (n := r)
    (by simp) hCr (by simpa only [Finset.card_univ] using hr)
  have hu : C ∪ Z = Z := Finset.union_eq_right.mpr hCZ
  have hloss := omegaCount_le_pow_sdiff_mul arrow C Z
  rw [hu, Finset.card_sdiff_of_subset hCZ, hZ] at hloss
  have hterm : omegaCount arrow Z ≤
      coefficient (splitGraph arrow) (Fintype.card ι - r) := by
    rw [coefficient_splitGraph_deletion_sum arrow r hr]
    exact omegaCount_le_deletion_sum arrow r Z hZ
  exact hloss.trans (Nat.mul_le_mul_left _ hterm)

/-- A uniform factor 2^r is sufficient for every core deletion of size ≤ r. -/
theorem omegaCount_le_pow_mul_coefficient (arrow : ι → ι → Prop)
    (C : Finset ι) (r : ℕ) (hCr : C.card ≤ r) (hr : r ≤ Fintype.card ι) :
    omegaCount arrow C ≤ 2 ^ r *
      coefficient (splitGraph arrow) (Fintype.card ι - r) := by
  calc
    omegaCount arrow C ≤ 2 ^ (r - C.card) *
        coefficient (splitGraph arrow) (Fintype.card ι - r) :=
      omegaCount_le_pow_sub_card_mul_coefficient arrow C r hCr hr
    _ ≤ 2 ^ r * coefficient (splitGraph arrow) (Fintype.card ι - r) :=
      Nat.mul_le_mul_right _
        (Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) (Nat.sub_le r C.card))


end FormalProof.Research003.RS42Structural
