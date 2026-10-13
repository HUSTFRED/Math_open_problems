module

public import FormalProof.Research003.RS42StructuralCore
public import FormalProof.Research003.RS42StructuralExponent
public import FormalProof.Research003.RS42FixedKBounds

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
Actual core-deletion upper bounds and an attained-exponent
lower witness. Neither graph count inequality is assumed as a hypothesis.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural

open RS42Counterexample90 RS42FixedKDeletion
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

theorem coreExponent_eq_structuralExponent (a b : V → ℕ) (f : State V) :
    coreExponent a b f = structuralExponent a b f := by
  unfold coreExponent structuralExponent
  apply Finset.sum_congr rfl
  intro v _
  cases h : f v with
  | none => simp [localExponent]
  | some s => simp [localExponent]

open Classical in
theorem zeroFiber_card_le_two_pow (coreArrow : V → V → Prop) (C : Finset V) :
    Fintype.card (ZeroFiber coreArrow C) ≤ 2 ^ Fintype.card V := by
  classical
  let e := zeroFiberEquiv coreArrow C
  have hi : Function.Injective
      (fun c : ZeroFiber coreArrow C => (e c).1) :=
    Subtype.val_injective.comp e.injective
  have hc := Fintype.card_le_of_injective _ hi
  have hr : Fintype.card (Remaining C) ≤ Fintype.card V :=
    Fintype.card_subtype_le (fun v : V => v ∉ C)
  calc
    Fintype.card (ZeroFiber coreArrow C) ≤
        Fintype.card (Remaining C → Fin 2) := hc
    _ = 2 ^ Fintype.card (Remaining C) := by simp
    _ ≤ 2 ^ Fintype.card V := Nat.pow_le_pow_right (by decide) hr

theorem zeroFiber_exponent_le_max (coreArrow : V → V → Prop)
    (a b : V → ℕ) (r : ℕ) (C : Finset V) (hC : C.card ≤ r)
    (c : ZeroFiber coreArrow C) :
    structuralExponent a b c.1.1 ≤ maxCoreExponent coreArrow a b r := by
  classical
  rw [← coreExponent_eq_structuralExponent]
  apply coreExponent_le_max
  simp only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨c.1.2, ?_⟩
  rw [c.2]
  exact hC

/-- Uniform bound on actual induced-deletion assignment counts when the
deleted set contains only core labels. -/
theorem omega_coreDelete_le_max (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p r : ℕ) (C : Finset V) (hC : C.card ≤ r) :
    omegaCount (structuralArrow coreArrow a b p) (coreDelete a b p C) ≤
      2 ^ Fintype.card V * 2 ^ (p * maxCoreExponent coreArrow a b r) := by
  classical
  rw [omega_coreDelete_eq_zeroFiber_exponent_sum]
  calc
    _ ≤ ∑ _c : ZeroFiber coreArrow C, 2 ^ (p * maxCoreExponent coreArrow a b r) := by
      apply Finset.sum_le_sum
      intro c _
      exact Nat.pow_le_pow_right (by decide)
        (Nat.mul_le_mul_left p (zeroFiber_exponent_le_max coreArrow a b r C hC c))
    _ = Fintype.card (ZeroFiber coreArrow C) *
        2 ^ (p * maxCoreExponent coreArrow a b r) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (zeroFiber_card_le_two_pow coreArrow C)

/-- A core deletion attaining the finite exponent maximum supplies a genuine
large count. Its size is at most r; padding to exactly r is a separate step. -/
theorem exists_coreDelete_large (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p r : ℕ) :
    ∃ C : Finset V, C.card ≤ r ∧
      2 ^ (p * maxCoreExponent coreArrow a b r) ≤
        omegaCount (structuralArrow coreArrow a b p) (coreDelete a b p C) := by
  classical
  obtain ⟨f, hf, hmax⟩ := maxCoreExponent_attained coreArrow a b r
  have hf' : legal coreArrow f ∧ (zeroSet f).card ≤ r := by
    simpa only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and]
      using hf
  refine ⟨zeroSet f, hf'.2, ?_⟩
  rw [omega_coreDelete_eq_zeroFiber_exponent_sum]
  let c : ZeroFiber coreArrow (zeroSet f) := ⟨⟨f, hf'.1⟩, rfl⟩
  calc
    _ = 2 ^ (p * structuralExponent a b f) := by
      rw [hmax, coreExponent_eq_structuralExponent]
    _ ≤ ∑ c : ZeroFiber coreArrow (zeroSet f),
        2 ^ (p * structuralExponent a b c.1.1) := by
      exact Finset.single_le_sum
        (f := fun c : ZeroFiber coreArrow (zeroSet f) =>
          2 ^ (p * structuralExponent a b c.1.1))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ c)

def IsStructuralLeaf (a b : V → ℕ) (p : ℕ) : StructuralLabel a b p → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

def safeOriginalSign (a b : V → ℕ) (p : ℕ) : StructuralLabel a b p → Fin 2
  | Sum.inr ⟨_, Sum.inr _⟩ => 1
  | _ => 0

theorem safeOriginalSign_source (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (v w : StructuralLabel a b p)
    (hv : IsStructuralLeaf a b p v) (h : structuralArrow coreArrow a b p v w) :
    safeOriginalSign a b p v ≠ 0 := by
  rcases v with v | ⟨v, j | j⟩
  · exact False.elim hv
  · rcases w with w | ⟨w, k | k⟩ <;> exact False.elim h
  · simp [safeOriginalSign]

theorem safeOriginalSign_target (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (v w : StructuralLabel a b p)
    (hw : IsStructuralLeaf a b p w) (h : structuralArrow coreArrow a b p v w) :
    safeOriginalSign a b p w ≠ 1 := by
  rcases w with w | ⟨w, k | k⟩
  · exact False.elim hw
  · simp [safeOriginalSign]
  · rcases v with v | ⟨v, j | j⟩ <;> exact False.elim h

theorem omega_delete_original_leaves (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (C D : Finset (StructuralLabel a b p))
    (hD : ∀ v, v ∈ D → IsStructuralLeaf a b p v) :
    omegaCount (structuralArrow coreArrow a b p) (C ∪ D) ≤
      omegaCount (structuralArrow coreArrow a b p) C := by
  classical
  apply omegaCount_union_le_of_safe (structuralArrow coreArrow a b p) C D
    (safeOriginalSign a b p)
  · intro v hv w h
    exact safeOriginalSign_source coreArrow a b p v w (hD v hv) h
  · intro w hw v h
    exact safeOriginalSign_target coreArrow a b p v w (hD w hw) h

noncomputable def structuralCorePart (a b : V → ℕ) (p : ℕ)
    (Z : Finset (StructuralLabel a b p)) : Finset V := by
  classical
  exact Finset.univ.filter fun v => Sum.inl v ∈ Z

noncomputable def structuralLeafPart (a b : V → ℕ) (p : ℕ)
    (Z : Finset (StructuralLabel a b p)) : Finset (StructuralLabel a b p) := by
  classical
  exact Z.filter (IsStructuralLeaf a b p)

theorem corePart_leafPart_union (a b : V → ℕ) (p : ℕ)
    (Z : Finset (StructuralLabel a b p)) :
    coreDelete a b p (structuralCorePart a b p Z) ∪ structuralLeafPart a b p Z = Z := by
  classical
  ext v
  cases v with
  | inl v => simp [structuralCorePart, structuralLeafPart, IsStructuralLeaf]
  | inr l => simp [structuralLeafPart, IsStructuralLeaf]

theorem structuralCorePart_card_le (a b : V → ℕ) (p : ℕ)
    (Z : Finset (StructuralLabel a b p)) :
    (structuralCorePart a b p Z).card ≤ Z.card := by
  classical
  rw [← coreDelete_card a b p]
  apply Finset.card_le_card
  intro v hv
  cases v with
  | inl v =>
    have h := (mem_coreDelete_core a b p (structuralCorePart a b p Z) v).mp hv
    exact (Finset.mem_filter.mp h).2
  | inr l => exact False.elim (not_mem_coreDelete_leaf a b p _ l hv)

/-- Every mixed deletion is bounded by the deletion of exactly its core part. -/
theorem omega_mixed_le_corePart (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (Z : Finset (StructuralLabel a b p)) :
    omegaCount (structuralArrow coreArrow a b p) Z ≤
      omegaCount (structuralArrow coreArrow a b p)
        (coreDelete a b p (structuralCorePart a b p Z)) := by
  classical
  have h := omega_delete_original_leaves coreArrow a b p
    (coreDelete a b p (structuralCorePart a b p Z)) (structuralLeafPart a b p Z)
    (by intro v hv; exact (Finset.mem_filter.mp hv).2)
  simpa only [corePart_leafPart_union] using h

/-- Uniform actual Omega bound for every mixed deletion of at most r labels. -/
theorem omega_mixed_le_max (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p r : ℕ) (Z : Finset (StructuralLabel a b p))
    (hZ : Z.card ≤ r) :
    omegaCount (structuralArrow coreArrow a b p) Z ≤
      2 ^ Fintype.card V * 2 ^ (p * maxCoreExponent coreArrow a b r) := by
  exact (omega_mixed_le_corePart coreArrow a b p Z).trans
    (omega_coreDelete_le_max coreArrow a b p r (structuralCorePart a b p Z)
      ((structuralCorePart_card_le a b p Z).trans hZ))


end FormalProof.Research003.RS42Structural
