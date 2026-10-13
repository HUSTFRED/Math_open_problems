module

public import FormalProof.Research003.RS42FixedKCore
public import FormalProof.Research003.RS42FixedKCoreAlgebra
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Algebra.BigOperators.Fin

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Evaluate the original-leaf factors in the genuine core-deletion count.
Only one three-state core variable is split at a time; the arbitrarily many
leaves and core branches are handled by finite-product identities.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open RS42FixedKDeletion
open scoped BigOperators

def outWeight (s : Option (Fin 2)) : ℕ := if s = some 0 then 1 else 2

def inWeight (s : Option (Fin 2)) : ℕ := if s = some 1 then 1 else 2

def branchWeight (p : ℕ) (s : Option (Fin 2)) : ℕ :=
  if s = none then (2 ^ p) ^ 3 else if s = some 0 then (2 ^ p) ^ 2 else 2 ^ p

def rootWeight (p : ℕ) (s : Option (Fin 2)) : ℕ :=
  if s = some 0 then 1 else 2 ^ p

@[simp] theorem branchWeight_none (p : ℕ) : branchWeight p none = (2 ^ p) ^ 3 := by
  simp [branchWeight]

@[simp] theorem branchWeight_some_zero (p : ℕ) :
    branchWeight p (some 0) = (2 ^ p) ^ 2 := by simp [branchWeight]

@[simp] theorem branchWeight_some_one (p : ℕ) :
    branchWeight p (some 1) = 2 ^ p := by simp [branchWeight]

@[simp] theorem rootWeight_none (p : ℕ) : rootWeight p none = 2 ^ p := by
  simp [rootWeight]

@[simp] theorem rootWeight_some_zero (p : ℕ) : rootWeight p (some 0) = 1 := by
  simp [rootWeight]

@[simp] theorem rootWeight_some_one (p : ℕ) : rootWeight p (some 1) = 2 ^ p := by
  simp [rootWeight]

theorem outgoing_leaf_card (s : Option (Fin 2)) :
    Nat.card {b : Option (Fin 2) // b ≠ none ∧ ¬ (s = some 0 ∧ b = some 1)} =
      outWeight s := by
  rw [Nat.card_eq_fintype_card]
  cases s with
  | none => decide
  | some b => fin_cases b <;> decide

theorem incoming_leaf_card (s : Option (Fin 2)) :
    Nat.card {b : Option (Fin 2) // b ≠ none ∧ ¬ (b = some 0 ∧ s = some 1)} =
      inWeight s := by
  rw [Nat.card_eq_fintype_card]
  cases s with
  | none => decide
  | some b => fin_cases b <;> decide

theorem leaf_card_out {q p : ℕ} (c : CoreState q) (i : Fin q) (j : Fin p) :
    Nat.card {b : Option (Fin 2) // leafAllowed c (Sum.inl (i, j) : LeafLabel q p) b} =
      outWeight (c.1 i) := outgoing_leaf_card (c.1 i)

theorem leaf_card_in {q p : ℕ} (c : CoreState q) (i : Fin q) (j : Fin (2 * p)) :
    Nat.card {b : Option (Fin 2) //
      leafAllowed c (Sum.inr (Sum.inl (i, j)) : LeafLabel q p) b} =
      inWeight (c.1 i) := incoming_leaf_card (c.1 i)

theorem leaf_card_z {q p : ℕ} (c : CoreState q) (j : Fin p) :
    Nat.card {b : Option (Fin 2) //
      leafAllowed c (Sum.inr (Sum.inr j) : LeafLabel q p) b} =
      outWeight c.2 := outgoing_leaf_card c.2

theorem branchWeight_eq_leaf_weights (p : ℕ) (s : Option (Fin 2)) :
    outWeight s ^ p * inWeight s ^ (2 * p) = branchWeight p s := by
  cases s with
  | none =>
    simp only [outWeight, inWeight, branchWeight, reduceCtorEq, ite_false, ite_true]
    rw [Nat.mul_comm 2 p, pow_mul]
    ring
  | some s =>
    fin_cases s <;> simp [outWeight, inWeight, branchWeight, Nat.mul_comm 2 p, pow_mul]

theorem rootWeight_eq_leaf_weight (p : ℕ) (s : Option (Fin 2)) :
    outWeight s ^ p = rootWeight p s := by
  by_cases hs : s = some 0 <;> simp [outWeight, rootWeight, hs]

theorem leaf_product_eq_local {q p : ℕ} (c : CoreState q) :
    (∏ l : LeafLabel q p, Nat.card {b : Option (Fin 2) // leafAllowed c l b}) =
      (∏ i : Fin q, outWeight (c.1 i) ^ p * inWeight (c.1 i) ^ (2 * p)) *
        outWeight c.2 ^ p := by
  classical
  simp only [Fintype.prod_sum_type, Fintype.prod_prod_type,
    leaf_card_out, leaf_card_in, leaf_card_z, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  ring

theorem leaf_product_eq_weights {q p : ℕ} (c : CoreState q) :
    (∏ l : LeafLabel q p, Nat.card {b : Option (Fin 2) // leafAllowed c l b}) =
      (∏ i : Fin q, branchWeight p (c.1 i)) * rootWeight p c.2 := by
  rw [leaf_product_eq_local]
  simp_rw [branchWeight_eq_leaf_weights, rootWeight_eq_leaf_weight]

open Classical in
theorem omega_coreDelete_eq_weight_sum (q p : ℕ) (C : Finset (Fin q)) (dz : Bool) :
    omegaCount (arrow q p) (coreDelete C dz) =
      ∑ c : CoreState q, if coreAllowed C dz c then
        (∏ i : Fin q, branchWeight p (c.1 i)) * rootWeight p c.2
      else 0 := by
  classical
  rw [omega_coreDelete_eq_core_sum]
  simp only [leaf_product_eq_weights]


end FormalProof.Research003.RS42FixedK
