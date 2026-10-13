module

public import FormalProof.Research003.RS42FixedKCoreEvaluate
public import FormalProof.Research003.RS42FixedKCoreAlgebra
public import Mathlib.Algebra.BigOperators.Ring.Finset

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Exact formulas for deleting arbitrary subsets of the u cores, either retaining
or deleting z. The starting finite weighted sum is the cardinality of actual
legal assignments, as proved by the core/leaf equivalence.
-/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace FormalProof.Research003.RS42FixedK

open RS42FixedKDeletion

def coreBranchAllowed {q : ℕ} (C : Finset (Fin q)) (b : Option (Fin 2))
    (i : Fin q) (a : Option (Fin 2)) : Prop :=
  (a = none ↔ i ∈ C) ∧ ¬ (a = some 0 ∧ b = some 1)

noncomputable def coreBranchSum {q : ℕ} (p : ℕ) (C : Finset (Fin q))
    (b : Option (Fin 2)) (i : Fin q) : ℕ := by
  classical
  exact ∑ a : Option (Fin 2), if coreBranchAllowed C b i a then branchWeight p a else 0

theorem coreBranchSum_none {q : ℕ} (p : ℕ) (C : Finset (Fin q)) (i : Fin q) :
    coreBranchSum p C none i =
      if i ∈ C then (2 ^ p) ^ 3 else (2 ^ p) ^ 2 + 2 ^ p := by
  classical
  unfold coreBranchSum
  rw [Fintype.sum_option, Fin.sum_univ_two]
  by_cases hi : i ∈ C <;> simp [coreBranchAllowed, branchWeight, hi]

theorem coreBranchSum_zero {q : ℕ} (p : ℕ) (C : Finset (Fin q)) (i : Fin q) :
    coreBranchSum p C (some 0) i =
      if i ∈ C then (2 ^ p) ^ 3 else (2 ^ p) ^ 2 + 2 ^ p := by
  classical
  unfold coreBranchSum
  rw [Fintype.sum_option, Fin.sum_univ_two]
  by_cases hi : i ∈ C <;> simp [coreBranchAllowed, branchWeight, hi]

theorem coreBranchSum_one {q : ℕ} (p : ℕ) (C : Finset (Fin q)) (i : Fin q) :
    coreBranchSum p C (some 1) i =
      if i ∈ C then (2 ^ p) ^ 3 else 2 ^ p := by
  classical
  unfold coreBranchSum
  rw [Fintype.sum_option, Fin.sum_univ_two]
  by_cases hi : i ∈ C <;> simp [coreBranchAllowed, branchWeight, hi]

/-- Sum first over the root state; each remaining u branch is independent. -/
theorem omega_coreDelete_eq_root_sum (q p : ℕ) (C : Finset (Fin q)) (dz : Bool) :
    omegaCount (arrow q p) (coreDelete C dz) =
      ∑ b : Option (Fin 2), if (b = none ↔ dz = true) then
        (∏ i : Fin q, coreBranchSum p C b i) * rootWeight p b else 0 := by
  classical
  rw [omega_coreDelete_eq_weight_sum, Fintype.sum_prod_type_right]
  apply Finset.sum_congr rfl
  intro b _
  simp only [coreAllowed]
  by_cases hb : b = none ↔ dz = true
  · simp only [hb, true_and, ite_true]
    have hterm (f : Fin q → Option (Fin 2)) :
        (if ∀ i, (f i = none ↔ i ∈ C) ∧ ¬ (f i = some 0 ∧ b = some 1) then
          (∏ i : Fin q, branchWeight p (f i)) * rootWeight p b else 0) =
        (if ∀ i, (f i = none ↔ i ∈ C) ∧ ¬ (f i = some 0 ∧ b = some 1) then
          ∏ i : Fin q, branchWeight p (f i) else 0) * rootWeight p b := by
      by_cases hf : ∀ i, (f i = none ↔ i ∈ C) ∧
        ¬ (f i = some 0 ∧ b = some 1) <;> simp [hf]
    simp_rw [hterm]
    rw [← Finset.sum_mul]
    congr 1
    unfold coreBranchSum coreBranchAllowed
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : ∀ i, (f i = none ↔ i ∈ C) ∧ ¬ (f i = some 0 ∧ b = some 1)
    · rw [ite_eq_left hf]
      apply Finset.prod_congr rfl
      intro i _
      rw [ite_eq_left (hf i)]
    · rw [ite_eq_right hf]
      obtain ⟨i, hi⟩ := not_forall.mp hf
      symm
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      rw [ite_eq_right hi]
  · simp [hb]

private theorem prod_if_mem {q : ℕ} (C : Finset (Fin q)) (a b : ℕ) :
    (∏ i : Fin q, if i ∈ C then a else b) = a ^ C.card * b ^ (q - C.card) := by
  classical
  have hf : (Finset.univ.filter fun i : Fin q => i ∈ C) = C := by
    ext i
    simp
  have hn : (Finset.univ.filter fun i : Fin q => i ∉ C) = Cᶜ := by
    ext i
    simp
  rw [Finset.prod_ite, hf, hn]
  simp only [Finset.prod_const, Finset.card_compl, Fintype.card_fin]

/-- Formula A, valid also at t = 0 and t = q, for every natural q and p. -/
theorem omega_deletedUs (q p : ℕ) (C : Finset (Fin q)) :
    omegaCount (arrow q p) (deletedUs C) = coreA q (2 ^ p) C.card := by
  classical
  have h := omega_coreDelete_eq_root_sum q p C false
  simp only [coreDelete, Bool.false_eq_true, ↓reduceIte] at h
  rw [h, Fintype.sum_option, Fin.sum_univ_two]
  have hfinal :
      (2 ^ p) ^ (3 * C.card) * ((2 ^ p) ^ 2 + 2 ^ p) ^ (q - C.card) +
        (2 ^ p) ^ (3 * C.card) * (2 ^ p) ^ (q - C.card) * 2 ^ p =
      coreA q (2 ^ p) C.card := by
    unfold coreA
    rw [pow_succ]
    ring
  simpa [coreBranchSum_zero, coreBranchSum_one, prod_if_mem,
    rootWeight, ← pow_mul, Nat.mul_assoc] using hfinal

/-- Formula B, valid through deletion of all q + 1 core labels. -/
theorem omega_deletedUsAndZ (q p : ℕ) (C : Finset (Fin q)) :
    omegaCount (arrow q p) (deletedUsAndZ C) = coreB q (2 ^ p) C.card := by
  classical
  have h := omega_coreDelete_eq_root_sum q p C true
  simp only [coreDelete, ↓reduceIte] at h
  rw [h, Fintype.sum_option, Fin.sum_univ_two]
  have hfinal :
      (2 ^ p) ^ (3 * C.card) * ((2 ^ p) ^ 2 + 2 ^ p) ^ (q - C.card) * 2 ^ p =
      coreB q (2 ^ p) C.card := by
    unfold coreB
    rw [pow_succ]
    ring
  simpa [coreBranchSum_none, prod_if_mem,
    rootWeight, ← pow_mul, Nat.mul_assoc] using hfinal

theorem omega_deletedUs_explicit (q p : ℕ) (C : Finset (Fin q)) :
    omegaCount (arrow q p) (deletedUs C) =
      (2 ^ p) ^ (3 * C.card) *
        (((2 ^ p) ^ 2 + 2 ^ p) ^ (q - C.card) +
          (2 ^ p) ^ (q - C.card + 1)) := omega_deletedUs q p C

theorem omega_deletedUsAndZ_explicit (q p : ℕ) (C : Finset (Fin q)) :
    omegaCount (arrow q p) (deletedUsAndZ C) =
      (2 ^ p) ^ (3 * C.card + 1) *
        ((2 ^ p) ^ 2 + 2 ^ p) ^ (q - C.card) := omega_deletedUsAndZ q p C


end FormalProof.Research003.RS42FixedK
