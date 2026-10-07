module

public import FormalProof.Research003.RS42Counterexample90
public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Finite weighted-choice generating functions for the actual 90-vertex count.
These general identities never enumerate a large function space. They expand
products symbolically, then identify a coefficient with the cardinality of a
specified subtype. No numeric counting premise or extra axiom is introduced.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

open scoped BigOperators
open Polynomial

variable {α ι β κ : Type*}

open Classical in
/-- A weighted sum records exactly the objects satisfying the predicate. -/
theorem card_weighted_sum_eq_coeff [Fintype α]
    (allowed : α → Prop) (weight : α → ℕ) (k : ℕ) :
    Nat.card {a : α // allowed a ∧ weight a = k} =
      (∑ a : α, if allowed a then (X : ℕ[X]) ^ weight a else 0).coeff k := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  symm
  calc
    _ = ∑ a : α, if allowed a ∧ weight a = k then (1 : ℕ) else 0 := by
      rw [Polynomial.finsetSum_coeff]
      apply Finset.sum_congr rfl
      intro a _
      by_cases h : allowed a
      · simp [h, Polynomial.coeff_X_pow, eq_comm]
      · simp [h]
    _ = _ := by simp

/-- Local independent choices, with nonnegative integer weights. -/
noncomputable def weightedChoicePolynomial [Fintype ι] [Fintype β]
    (allowed : ι → β → Prop) (weight : ι → β → ℕ) : ℕ[X] := by
  classical
  exact ∏ i : ι, ∑ b : β, if allowed i b then X ^ weight i b else 0

open Classical in
/-- Symbolic distributivity, including arbitrary index-dependent restrictions. -/
theorem weightedChoicePolynomial_eq_sum [Fintype ι] [Fintype β]
    (allowed : ι → β → Prop) (weight : ι → β → ℕ) :
    weightedChoicePolynomial allowed weight =
      ∑ f : ι → β, if (∀ i, allowed i (f i)) then
        (X : ℕ[X]) ^ (∑ i, weight i (f i)) else 0 := by
  classical
  unfold weightedChoicePolynomial
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro f _
  rw [Fintype.prod_ite_zero]
  rw [Finset.prod_pow_eq_pow_sum]

/-- Fixed total weight is the corresponding product coefficient. -/
theorem card_weighted_choices_eq_coeff [Fintype ι] [Fintype β]
    (allowed : ι → β → Prop) (weight : ι → β → ℕ) (k : ℕ) :
    Nat.card {f : ι → β // (∀ i, allowed i (f i)) ∧
      (∑ i, weight i (f i)) = k} =
      (weightedChoicePolynomial allowed weight).coeff k := by
  classical
  rw [weightedChoicePolynomial_eq_sum]
  convert card_weighted_sum_eq_coeff (fun f : ι → β => ∀ i, allowed i (f i))
    (fun f : ι → β => ∑ i, weight i (f i)) k using 1
  apply congrArg (fun p : ℕ[X] => p.coeff k)
  apply Finset.sum_congr rfl
  intro f _
  by_cases h : ∀ i, allowed i (f i) <;> simp [h]

open Classical in
/-- An additional finite core is summed, while its independent leaf choices
remain a product. This statement uses the exact product-subtype association
needed by the graph90 decomposition. -/
theorem core_leaf_count_eq_coeff [Fintype κ] [Fintype ι] [Fintype β]
    (coreAllowed : κ → Prop) (leafAllowed : κ → ι → β → Prop)
    (coreWeight : κ → ℕ) (leafWeight : κ → ι → β → ℕ) (k : ℕ) :
    Nat.card {cf : κ × (ι → β) // coreAllowed cf.1 ∧
      (∀ i, leafAllowed cf.1 i (cf.2 i)) ∧
      coreWeight cf.1 + (∑ i, leafWeight cf.1 i (cf.2 i)) = k} =
      (∑ c : κ, if coreAllowed c then
        (X : ℕ[X]) ^ coreWeight c *
          weightedChoicePolynomial (leafAllowed c) (leafWeight c) else 0).coeff k := by
  classical
  have hcount := card_weighted_sum_eq_coeff
    (fun cf : κ × (ι → β) => coreAllowed cf.1 ∧
      (∀ i, leafAllowed cf.1 i (cf.2 i)))
    (fun cf : κ × (ι → β) => coreWeight cf.1 +
      ∑ i, leafWeight cf.1 i (cf.2 i)) k
  simp only [and_assoc] at hcount
  rw [hcount]
  apply congrArg (fun p : ℕ[X] => p.coeff k)
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro c _
  rw [weightedChoicePolynomial_eq_sum]
  by_cases hc : coreAllowed c
  · simp only [hc, true_and, ite_true, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro f _
    by_cases hf : ∀ i, leafAllowed c i (f i)
    · simp [hf, pow_add]
    · simp [hf]
  · simp [hc]

#print axioms card_weighted_sum_eq_coeff
#print axioms weightedChoicePolynomial_eq_sum
#print axioms card_weighted_choices_eq_coeff
#print axioms core_leaf_count_eq_coeff

end FormalProof.Research003.RS42Counterexample90
