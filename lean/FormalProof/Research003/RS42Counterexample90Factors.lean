module

public import FormalProof.Research003.RS42Counterexample90Counts
public import FormalProof.Research003.RS42Counterexample90CountingTools
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.hashCommand false

/-!
The five leaf groups of the fixed graph. Only the three core blocks will
be enumerated; the leaf choices remain symbolic powers of linear factors.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

open scoped BigOperators
open Polynomial

def outgoingAllowed (s b : Option (Fin 2)) : Prop := ¬ (s = some 0 ∧ b = some 1)
def incomingAllowed (s b : Option (Fin 2)) : Prop := ¬ (b = some 0 ∧ s = some 1)

theorem coreLegal90_iff (c : State (Fin 3)) :
    coreLegal90 c ↔ outgoingAllowed (c 0) (c 2) ∧
      outgoingAllowed (c 1) (c 2) := by
  simp [coreLegal90, legal, arrow45, Fin.forall_fin_succ, outgoingAllowed]

theorem leafAllowed90_iff (c : State (Fin 3)) (i : Fin 42) (b : Option (Fin 2)) :
    leafAllowed90 c i b ↔
      if i.val < 6 then outgoingAllowed (c 0) b else
      if i.val < 18 then incomingAllowed (c 0) b else
      if i.val < 24 then outgoingAllowed (c 1) b else
      if i.val < 36 then incomingAllowed (c 1) b else outgoingAllowed (c 2) b := by
  fin_cases i <;>
    simp [leafAllowed90, arrow45, Fin.forall_fin_succ,
      outgoingAllowed, incomingAllowed]

noncomputable def outgoingPolynomial (s : Option (Fin 2)) : ℕ[X] :=
  if s = some 0 then 1 + X else 1 + 2 * X

noncomputable def incomingPolynomial (s : Option (Fin 2)) : ℕ[X] :=
  if s = some 1 then 1 + X else 1 + 2 * X

open Classical in
theorem outgoing_sum (s : Option (Fin 2)) :
    (∑ b : Option (Fin 2),
      if outgoingAllowed s b then (X : ℕ[X]) ^ occupied b else 0) =
      outgoingPolynomial s := by
  classical
  by_cases h : s = some 0 <;>
    simp [Fintype.sum_option, Fin.sum_univ_two, outgoingAllowed,
      occupied, outgoingPolynomial, h, two_mul]

open Classical in
theorem incoming_sum (s : Option (Fin 2)) :
    (∑ b : Option (Fin 2),
      if incomingAllowed s b then (X : ℕ[X]) ^ occupied b else 0) =
      incomingPolynomial s := by
  classical
  by_cases h : s = some 1 <;>
    simp [Fintype.sum_option, Fin.sum_univ_two, incomingAllowed,
      occupied, incomingPolynomial, h, two_mul]

theorem five_group_product (a b c d e : ℕ[X]) :
    (∏ i : Fin 42, if i.val < 6 then a else if i.val < 18 then b else
      if i.val < 24 then c else if i.val < 36 then d else e) =
      a ^ 6 * b ^ 12 * c ^ 6 * d ^ 12 * e ^ 6 := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero]
  norm_num
  ring

theorem leafPolynomial90 (c : State (Fin 3)) :
    weightedChoicePolynomial (leafAllowed90 c) (fun _ b => occupied b) =
      outgoingPolynomial (c 0) ^ 6 * incomingPolynomial (c 0) ^ 12 *
      outgoingPolynomial (c 1) ^ 6 * incomingPolynomial (c 1) ^ 12 *
      outgoingPolynomial (c 2) ^ 6 := by
  classical
  unfold weightedChoicePolynomial
  have hfactor (i : Fin 42) :
      (∑ b : Option (Fin 2),
        if leafAllowed90 c i b then (X : ℕ[X]) ^ occupied b else 0) =
        if i.val < 6 then outgoingPolynomial (c 0) else
        if i.val < 18 then incomingPolynomial (c 0) else
        if i.val < 24 then outgoingPolynomial (c 1) else
        if i.val < 36 then incomingPolynomial (c 1) else outgoingPolynomial (c 2) := by
    simp only [leafAllowed90_iff]
    split_ifs <;> first | exact outgoing_sum _ | exact incoming_sum _
  simp_rw [hfactor]
  exact five_group_product _ _ _ _ _

noncomputable def corePolynomial90 : ℕ[X] := by
  classical
  exact ∑ c : State (Fin 3), if coreLegal90 c then
    X ^ (∑ i, occupied (c i)) *
      (outgoingPolynomial (c 0) ^ 6 * incomingPolynomial (c 0) ^ 12 *
       outgoingPolynomial (c 1) ^ 6 * incomingPolynomial (c 1) ^ 12 *
       outgoingPolynomial (c 2) ^ 6) else 0

theorem coefficient_graph90_eq_corePolynomial (k : ℕ) :
    coefficient graph90 k = corePolynomial90.coeff k := by
  classical
  rw [coefficient_graph90_eq_coreLeaf_count]
  rw [core_leaf_count_eq_coeff coreLegal90 leafAllowed90
    (fun c => ∑ i, occupied (c i)) (fun _ _ b => occupied b)]
  simp only [corePolynomial90, leafPolynomial90]

/-- This equivalence has only 27 possible core values. -/
def coreTripleEquiv90 : State (Fin 3) ≃
    Option (Fin 2) × Option (Fin 2) × Option (Fin 2) where
  toFun c := (c 0, c 1, c 2)
  invFun z := ![z.1, z.2.1, z.2.2]
  left_inv c := by
    funext i
    fin_cases i <;> rfl
  right_inv _ := rfl

@[simp] theorem coreTripleEquiv90_symm_apply
    (z : Option (Fin 2) × Option (Fin 2) × Option (Fin 2)) :
    coreTripleEquiv90.symm z = ![z.1, z.2.1, z.2.2] := rfl

theorem corePolynomial90_closed :
    corePolynomial90 =
      ((1 + 2 * X) ^ 6 + X * (1 + X) ^ 6) *
        ((1 + 2 * X) ^ 18 + X * (1 + 2 * X) ^ 12 * (1 + X) ^ 6 +
          X * (1 + 2 * X) ^ 6 * (1 + X) ^ 12) ^ 2 +
      X * (1 + 2 * X) ^ 6 *
        ((1 + 2 * X) ^ 18 + X * (1 + 2 * X) ^ 6 * (1 + X) ^ 12) ^ 2 := by
  classical
  unfold corePolynomial90
  simp only [outgoingPolynomial, incomingPolynomial]
  generalize hA : (1 + 2 * (X : ℕ[X])) = A
  generalize hC : (1 + (X : ℕ[X])) = C
  rw [← coreTripleEquiv90.symm.sum_comp]
  simp [Fintype.sum_prod_type, Fintype.sum_option, Fin.sum_univ_two,
    coreTripleEquiv90_symm_apply, coreLegal90_iff, Fin.sum_univ_three, occupied,
    outgoingAllowed]
  ring

#print axioms coefficient_graph90_eq_corePolynomial
#print axioms corePolynomial90_closed

end FormalProof.Research003.RS42Counterexample90
