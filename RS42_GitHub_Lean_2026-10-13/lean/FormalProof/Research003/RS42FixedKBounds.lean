module

public import FormalProof.Research003.RS42FixedKBridge
public import FormalProof.Research003.RS42FixedKDeletion
public import FormalProof.Research003.RS42FixedKLeaf
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false

/-!
Genuine independent-set coefficients and deletion
counting bounds. The final theorem is explicitly conditional on core estimates
and on two witness deletion estimates. Those assumptions are not asserted here
as established formulas, and this file does not prove the fixed-k conclusion.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedKDeletion

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem deletion_sum_le (arrow : ι → ι → Prop) (r U : ℕ)
    (hU : ∀ Z : Finset ι, Z.card = r → omegaCount arrow Z ≤ U) :
    (∑ Z : {Z : Finset ι // Z.card = r}, omegaCount arrow Z.1) ≤
      (Fintype.card ι).choose r * U := by
  classical
  calc
    _ ≤ ∑ _Z : {Z : Finset ι // Z.card = r}, U := by
      apply Finset.sum_le_sum
      intro Z _
      exact hU Z.1 Z.2
    _ = _ := by simp [Fintype.card_finset_len]

theorem omegaCount_le_deletion_sum (arrow : ι → ι → Prop)
    (r : ℕ) (Z : Finset ι) (hZ : Z.card = r) :
    omegaCount arrow Z ≤
      ∑ W : {W : Finset ι // W.card = r}, omegaCount arrow W.1 := by
  classical
  exact Finset.single_le_sum (f := fun W : {W : Finset ι // W.card = r} =>
    omegaCount arrow W.1) (fun _ _ => Nat.zero_le _)
    (Finset.mem_univ (⟨Z, hZ⟩ : {W : Finset ι // W.card = r}))

end FormalProof.Research003.RS42FixedKDeletion

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90 RS42FixedKDeletion
open scoped BigOperators

theorem coefficient_eq_deletion_sum (q p r : ℕ) (hr : r ≤ m q p) :
    coefficient (graph q p) (m q p - r) =
      ∑ Z : {Z : Finset (Label q p) // Z.card = r}, omegaCount (arrow q p) Z.1 := by
  have hr' : r ≤ Fintype.card (Label q p) := by simpa only [label_card] using hr
  simpa only [label_card, graph] using
    coefficient_splitGraph_deletion_sum (arrow q p) r hr'

/-- Mathlib's actual independent-set count has the same deletion sum. -/
theorem mathlib_count_eq_deletion_sum (q p r : ℕ) (hr : r ≤ m q p) :
    Nat.card {s : Finset (Vertex (Label q p)) //
      (graph q p).IsNIndepSet (m q p - r) s} =
      ∑ Z : {Z : Finset (Label q p) // Z.card = r}, omegaCount (arrow q p) Z.1 := by
  calc
    _ = coefficient (graph q p) (m q p - r) :=
      Nat.card_congr (mathlibCoefficientEquiv q p (m q p - r))
    _ = _ := coefficient_eq_deletion_sum q p r hr

theorem coefficient_le_of_deletion_bound (q p r U : ℕ) (hr : r ≤ m q p)
    (hU : ∀ Z : Finset (Label q p), Z.card = r → omegaCount (arrow q p) Z ≤ U) :
    coefficient (graph q p) (m q p - r) ≤ (m q p).choose r * U := by
  rw [coefficient_eq_deletion_sum q p r hr]
  simpa only [label_card] using deletion_sum_le (arrow q p) r U hU

theorem omegaCount_le_coefficient (q p r : ℕ) (hr : r ≤ m q p)
    (Z : Finset (Label q p)) (hZ : Z.card = r) :
    omegaCount (arrow q p) Z ≤ coefficient (graph q p) (m q p - r) := by
  rw [coefficient_eq_deletion_sum q p r hr]
  exact omegaCount_le_deletion_sum (arrow q p) r Z hZ

/-- Explicit hypothesis for the core bound still to be established from the
core-deletion formulas. This definition is a proposition, not a new axiom. -/
def CoreUpperEstimate (q p : ℕ) : Prop :=
  ∀ C : Finset (Label q p),
    (∀ v, v ∈ C → ¬ IsOriginalLeaf v) → C.card ≤ q - 1 →
      omegaCount (arrow q p) C ≤ (2 ^ q + 1) * (2 ^ p) ^ (2 * q + C.card)

/-- The proved leaf extension comparison converts the conditional core bound
to a bound for every mixed deletion of the same size. -/
theorem deletion_bound_of_core_estimate (q p r : ℕ)
    (hcore : CoreUpperEstimate q p) (hr : r ≤ q - 1)
    (Z : Finset (Label q p)) (hZ : Z.card = r) :
    omegaCount (arrow q p) Z ≤ (2 ^ q + 1) * (2 ^ p) ^ (2 * q + r) := by
  classical
  have hC : (coreDeletion Z).card ≤ r := by
    simpa only [hZ] using coreDeletion_card_le Z
  have hc : omegaCount (arrow q p) (coreDeletion Z) ≤
      (2 ^ q + 1) * (2 ^ p) ^ (2 * q + (coreDeletion Z).card) := by
    apply hcore (coreDeletion Z)
    · intro v hv
      exact (Finset.mem_filter.mp hv).2
    · exact hC.trans hr
  calc
    _ ≤ omegaCount (arrow q p) (coreDeletion Z) := omegaCount_le_coreDeletion Z
    _ ≤ (2 ^ q + 1) * (2 ^ p) ^ (2 * q + (coreDeletion Z).card) := hc
    _ ≤ _ := Nat.mul_le_mul_left _
      (Nat.pow_le_pow_right (pow_pos (by decide : 0 < (2 : ℕ)) _)
        (Nat.add_le_add_left hC _))

theorem coefficient_bound_of_core_estimate (q p r : ℕ)
    (hcore : CoreUpperEstimate q p) (hr : r ≤ q - 1) :
    coefficient (graph q p) (m q p - r) ≤
      (m q p).choose r * (2 ^ q + 1) * (2 ^ p) ^ (2 * q + r) := by
  have hrm : r ≤ m q p := by
    unfold m
    omega
  simpa only [Nat.mul_assoc] using
    coefficient_le_of_deletion_bound q p r ((2 ^ q + 1) * (2 ^ p) ^ (2 * q + r))
      hrm (deletion_bound_of_core_estimate q p r hcore hr)

/-- Conditional assembly only: the core upper estimate and the two witness
estimates must be supplied by separately proved core-counting theorems. -/
theorem three_coefficient_bounds_of_core_estimates (q p : ℕ) (hq : 2 ≤ q)
    (hcore : CoreUpperEstimate q p)
    (Zlo Zhi : Finset (Label q p))
    (hlo_card : Zlo.card = q - 2) (hhi_card : Zhi.card = q)
    (hlo : (2 ^ p) ^ (3 * q - 2) ≤ omegaCount (arrow q p) Zlo)
    (hhi : (2 ^ p) ^ (3 * q + 1) ≤ omegaCount (arrow q p) Zhi) :
    coefficient (graph q p) (m q p - (q - 1)) ≤
        (m q p).choose (q - 1) * (2 ^ q + 1) * (2 ^ p) ^ (3 * q - 1) ∧
      (2 ^ p) ^ (3 * q - 2) ≤ coefficient (graph q p) (m q p - (q - 2)) ∧
      (2 ^ p) ^ (3 * q + 1) ≤ coefficient (graph q p) (m q p - q) := by
  have hqm : q ≤ m q p := by unfold m; omega
  have he : 2 * q + (q - 1) = 3 * q - 1 := by omega
  refine ⟨?_, ?_, ?_⟩
  · simpa only [he] using coefficient_bound_of_core_estimate q p (q - 1) hcore le_rfl
  · exact hlo.trans (omegaCount_le_coefficient q p (q - 2)
      ((Nat.sub_le _ _).trans hqm) Zlo hlo_card)
  · exact hhi.trans (omegaCount_le_coefficient q p q hqm Zhi hhi_card)


end FormalProof.Research003.RS42FixedK
