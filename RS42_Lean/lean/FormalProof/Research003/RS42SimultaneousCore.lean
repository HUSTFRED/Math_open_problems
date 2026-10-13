module
public import FormalProof.Research003.RS42StructuralExponent
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.BigOperators.Fin
public meta import Mathlib.Tactic.FinCases
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Simultaneous
open RS42Structural RS42Counterexample90 RS42FixedKDeletion
open scoped BigOperators

abbrev Core (t : ℕ) := Fin t × Fin 3
def arrow (t : ℕ) (v w : Core t) : Prop :=
  (v.1 = w.1 ∧ v.2 ≠ 0 ∧ w.2 = 0) ∨
    (v.2 = 0 ∧ w.2 = 0 ∧ v.1.val + 1 = w.1.val)
def outWeight (t : ℕ) : Core t → ℕ := fun _ => 1
def inWeight (t : ℕ) : Core t → ℕ := fun v => if v.2 = 0 then 0 else 2
def zval (s : Option (Fin 2)) : ℕ := if s = none then 1 else 0
def rval : Option (Fin 2) → ℕ
  | none => 1
  | some s => if s = 0 then 0 else 1
def bval : Option (Fin 2) → ℕ
  | none => 3
  | some s => if s = 0 then 2 else 1
def blockExponent {t : ℕ} (f : State (Core t)) (i : Fin t) : ℕ :=
  rval (f (i,0)) + bval (f (i,1)) + bval (f (i,2))
def blockZeros {t : ℕ} (f : State (Core t)) (i : Fin t) : ℕ :=
  zval (f (i,0)) + zval (f (i,1)) + zval (f (i,2))

theorem exponent_split {t : ℕ} (f : State (Core t)) :
    coreExponent (outWeight t) (inWeight t) f = ∑ i, blockExponent f i := by
  unfold coreExponent
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_succ, outWeight, inWeight, blockExponent, rval, bval, Nat.add_assoc]
  rfl

theorem zeros_split {t : ℕ} (f : State (Core t)) :
    (zeroSet f).card = ∑ i, blockZeros f i := by
  have h : (zeroSet f).card = ∑ v, zval (f v) := by
    classical
    simp [zeroSet, zval]
  rw [h, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  simp [Fin.sum_univ_succ, blockZeros, Nat.add_assoc]

theorem local_bound : ∀ c u v : Option (Fin 2),
    ¬ (u = some 0 ∧ c = some 1) → ¬ (v = some 0 ∧ c = some 1) →
    2*(rval c+bval u+bval v) ≤ 8+3*(zval c+zval u+zval v) := by decide

theorem exponent_upper {t : ℕ} (f : State (Core t)) (hf : legal (arrow t) f) :
    2 * coreExponent (outWeight t) (inWeight t) f ≤ 8*t+3*(zeroSet f).card := by
  have h (i : Fin t) : 2*blockExponent f i ≤ 8+3*blockZeros f i := by
    exact local_bound _ _ _
      (hf (i,1) (i,0) (Or.inl ⟨rfl, by simp, rfl⟩))
      (hf (i,2) (i,0) (Or.inl ⟨rfl, by simp, rfl⟩))
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin t))) => h i)
  simpa only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_comm t 8,
    ← exponent_split, ← zeros_split] using hs

def witness (t s : ℕ) (odd : Bool) : State (Core t) := fun v =>
  if v.1.val < s then (if v.2 = 0 then some 1 else none)
  else if v.1.val = s ∧ odd = true ∧ v.2 = 1 then none else some 0

theorem witness_legal (t s : ℕ) (odd : Bool) : legal (arrow t) (witness t s odd) := by
  intro v w h hbad
  rcases h with ⟨heq,hv,hw⟩ | ⟨hv,hw,hn⟩
  · by_cases hs : w.1.val < s
    · have hvs : v.1.val < s := by simpa [heq] using hs
      simp [witness, hvs, hv] at hbad
    · simp [witness, hs, hw] at hbad
  · by_cases hs : w.1.val < s
    · have hvs : v.1.val < s := by omega
      simp [witness, hvs, hv] at hbad
    · simp [witness, hs, hw] at hbad

theorem witness_block {t : ℕ} (s : ℕ) (odd : Bool) (i : Fin t) :
    blockExponent (witness t s odd) i =
      (if i.val < s then 7 else if i.val = s ∧ odd = true then 5 else 4) ∧
    blockZeros (witness t s odd) i =
      (if i.val < s then 2 else if i.val = s ∧ odd = true then 1 else 0) := by
  by_cases hlt : i.val < s
  · simp [blockExponent, blockZeros, witness, hlt, rval, bval, zval]
  · by_cases heq : i.val = s <;> cases odd <;>
      simp [blockExponent, blockZeros, witness, hlt, heq, rval, bval, zval]

end FormalProof.Research003.RS42Simultaneous
