module
public import FormalProof.Research003.RS42FixedKDeletion
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

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

/-- Core exponent, with `none` encoding a deleted core vertex. -/
def coreExponent (a b : V → ℕ) (f : State V) : ℕ :=
  ∑ v, match f v with
    | none => a v + b v
    | some s => if s = 0 then b v else a v

noncomputable def admissibleCoreStates (arrow : V → V → Prop) (r : ℕ) :
    Finset (State V) := by
  classical
  exact Finset.univ.filter fun f => legal arrow f ∧ (zeroSet f).card ≤ r

noncomputable def maxCoreExponent (arrow : V → V → Prop) (a b : V → ℕ)
    (r : ℕ) : ℕ :=
  (admissibleCoreStates arrow r).sup (coreExponent a b)

theorem coreExponent_le_total (a b : V → ℕ) (f : State V) :
    coreExponent a b f ≤ ∑ v, (a v + b v) := by
  apply Finset.sum_le_sum
  intro v _
  cases h : f v with
  | none => exact le_rfl
  | some s =>
    by_cases hs : s = 0 <;> simp [hs]

theorem admissibleCoreStates_nonempty (arrow : V → V → Prop) (r : ℕ) :
    (admissibleCoreStates arrow r).Nonempty := by
  classical
  refine ⟨fun _ => some 0, ?_⟩
  simp only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro i j hij hbad
    simpa using hbad.2
  · simp [zeroSet]

theorem coreExponent_le_max (arrow : V → V → Prop) (a b : V → ℕ)
    (r : ℕ) (f : State V) (hf : f ∈ admissibleCoreStates arrow r) :
    coreExponent a b f ≤ maxCoreExponent arrow a b r :=
  Finset.le_sup hf

theorem maxCoreExponent_attained (arrow : V → V → Prop) (a b : V → ℕ)
    (r : ℕ) : ∃ f ∈ admissibleCoreStates arrow r,
      maxCoreExponent arrow a b r = coreExponent a b f := by
  exact Finset.exists_mem_eq_sup _ (admissibleCoreStates_nonempty arrow r) _

theorem maxCoreExponent_le_total (arrow : V → V → Prop) (a b : V → ℕ)
    (r : ℕ) : maxCoreExponent arrow a b r ≤ ∑ v, (a v + b v) := by
  apply Finset.sup_le
  intro f _
  exact coreExponent_le_total a b f

theorem maxCoreExponent_mono (arrow : V → V → Prop) (a b : V → ℕ) :
    Monotone (maxCoreExponent arrow a b) := by
  classical
  intro r s hrs
  apply Finset.sup_mono
  intro f hf
  simp only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
  exact ⟨hf.1, hf.2.trans hrs⟩

theorem maxCoreExponent_of_card_le (arrow : V → V → Prop) (a b : V → ℕ)
    (r : ℕ) (hr : Fintype.card V ≤ r) :
    maxCoreExponent arrow a b r = ∑ v, (a v + b v) := by
  classical
  apply le_antisymm (maxCoreExponent_le_total arrow a b r)
  have hf : (fun _ : V => (none : Option (Fin 2))) ∈ admissibleCoreStates arrow r := by
    simp only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro i j hij hbad
      simp at hbad
    · simpa [zeroSet] using hr
  have h := coreExponent_le_max arrow a b r _ hf
  simpa [coreExponent] using h

end FormalProof.Research003.RS42Structural
