module
public import FormalProof.Research003.RS42StructuralBounds
public import FormalProof.Research003.RS42StructuralPadding
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Structural
open RS42Counterexample90 RS42FixedKDeletion
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def structuralGraph (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) := splitGraph (structuralArrow coreArrow a b p)

noncomputable def structuralIndepCount (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p j : ℕ) : ℕ :=
  Nat.card {s : Finset (Vertex (StructuralLabel a b p)) //
    (structuralGraph coreArrow a b p).IsNIndepSet j s}

noncomputable def structuralCountEquiv (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p j : ℕ) :
    {s : Finset (Vertex (StructuralLabel a b p)) //
      (structuralGraph coreArrow a b p).IsNIndepSet j s} ≃
    {s : Finset (Vertex (StructuralLabel a b p)) //
      Independent (structuralGraph coreArrow a b p) (s : Set _) ∧ s.card = j} where
  toFun s := ⟨s.1, s.2.isIndepSet, s.2.card_eq⟩
  invFun s := ⟨s.1, ⟨s.2.1, s.2.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem structuralIndepCount_eq (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p j : ℕ) :
    structuralIndepCount coreArrow a b p j =
      coefficient (splitGraph (structuralArrow coreArrow a b p)) j :=
  Nat.card_congr (structuralCountEquiv coreArrow a b p j)

theorem structural_label_card (a b : V → ℕ) (p : ℕ) :
    Fintype.card (StructuralLabel a b p) = Fintype.card V + p * ∑ v, (a v + b v) := by
  simp only [StructuralLabel, StructuralLeaf, Fintype.card_sum, Fintype.card_sigma,
    Fintype.card_fin]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro v _
  ring

/-- Lower sandwich on actual independent vertex subsets, with no assumed
coefficient estimate. Cardinality padding works even without enough leaves. -/
theorem structural_count_lower (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p r : ℕ) (hr : r ≤ Fintype.card (StructuralLabel a b p)) :
    2 ^ (p * maxCoreExponent coreArrow a b r) ≤
      2 ^ r * structuralIndepCount coreArrow a b p
        (Fintype.card (StructuralLabel a b p) - r) := by
  rw [structuralIndepCount_eq]
  obtain ⟨C, hC, hlarge⟩ := exists_coreDelete_large coreArrow a b p r
  exact hlarge.trans (omegaCount_le_pow_mul_coefficient
    (structuralArrow coreArrow a b p) (coreDelete a b p C) r
    (by simpa only [coreDelete_card] using hC) hr)

/-- Upper sandwich for actual independent vertex subsets. -/
theorem structural_count_upper (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p r : ℕ) (hr : r ≤ Fintype.card (StructuralLabel a b p)) :
    structuralIndepCount coreArrow a b p (Fintype.card (StructuralLabel a b p) - r) ≤
      (Fintype.card (StructuralLabel a b p)).choose r *
        (2 ^ Fintype.card V * 2 ^ (p * maxCoreExponent coreArrow a b r)) := by
  rw [structuralIndepCount_eq, coefficient_splitGraph_deletion_sum _ r hr]
  apply deletion_sum_le
  intro Z hZ
  exact omega_mixed_le_max coreArrow a b p r Z (by omega)

end FormalProof.Research003.RS42Structural
