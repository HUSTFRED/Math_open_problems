module

public import FormalProof.Research003.RS42FixedKCoreFormula
public import FormalProof.Research003.RS42FixedKCoreAlgebra
public import FormalProof.Research003.RS42FixedKBounds

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Closing the core-count hypotheses using actual
induced-deletion counts. The estimates proved here have no assumed core formula
or assumed coefficient bound; they use the two proved core counting formulas.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90 RS42FixedKDeletion

noncomputable def coreIndices {q p : ℕ} (Z : Finset (Label q p)) : Finset (Fin q) := by
  classical
  exact Finset.univ.filter fun i => u i ∈ Z

@[simp] theorem mem_coreIndices {q p : ℕ} (Z : Finset (Label q p)) (i : Fin q) :
    i ∈ coreIndices Z ↔ u i ∈ Z := by
  classical
  simp [coreIndices]

theorem pureCore_eq_deletedUs {q p : ℕ} (Z : Finset (Label q p))
    (hZ : ∀ v, v ∈ Z → ¬ IsOriginalLeaf v) (hz : z q p ∉ Z) :
    Z = deletedUs (coreIndices Z) := by
  ext v
  rcases v with ((i | ⟨⟩) | l)
  · change u i ∈ Z ↔ u i ∈ deletedUs (coreIndices Z)
    change u i ∈ Z ↔ u i ∈ coreDelete (coreIndices Z) false
    rw [mem_coreDelete_u, mem_coreIndices]
  · change z q p ∈ Z ↔ z q p ∈ deletedUs (coreIndices Z)
    exact iff_of_false hz (by simp [deletedUs, u, z])
  · have hl : Sum.inr l ∉ Z := by
      intro h
      exact hZ (Sum.inr l) h (by trivial)
    simp [hl, deletedUs, u]

theorem pureCore_eq_deletedUsAndZ {q p : ℕ} (Z : Finset (Label q p))
    (hZ : ∀ v, v ∈ Z → ¬ IsOriginalLeaf v) (hz : z q p ∈ Z) :
    Z = deletedUsAndZ (coreIndices Z) := by
  ext v
  rcases v with ((i | ⟨⟩) | l)
  · change u i ∈ Z ↔ u i ∈ deletedUsAndZ (coreIndices Z)
    change u i ∈ Z ↔ u i ∈ coreDelete (coreIndices Z) true
    rw [mem_coreDelete_u, mem_coreIndices]
  · change z q p ∈ Z ↔ z q p ∈ deletedUsAndZ (coreIndices Z)
    simp [hz, deletedUsAndZ]
  · have hl : Sum.inr l ∉ Z := by
      intro h
      exact hZ (Sum.inr l) h (by trivial)
    simp [hl, deletedUsAndZ, deletedUs, u, z]

/-- The core upper estimate is now a theorem for every q ≥ 2 and every p. -/
theorem coreUpperEstimate (q p : ℕ) (hq : 2 ≤ q) : CoreUpperEstimate q p := by
  intro Z hZ hcard
  have hB : 1 ≤ (2 : ℕ) ^ p := pow_pos (by decide : 0 < (2 : ℕ)) _
  by_cases hz : z q p ∈ Z
  · have he := pureCore_eq_deletedUsAndZ Z hZ hz
    have hc : (coreIndices Z).card + 1 ≤ q - 1 := by
      have hc' := hcard
      rw [he, deletedUsAndZ_card] at hc'
      exact hc'
    rw [he, omega_deletedUsAndZ, deletedUsAndZ_card]
    exact coreB_le q (2 ^ p) (coreIndices Z).card hq hB hc
  · have he := pureCore_eq_deletedUs Z hZ hz
    have hc : (coreIndices Z).card ≤ q - 1 := by
      have hc' := hcard
      rw [he, deletedUs_card] at hc'
      exact hc'
    rw [he, omega_deletedUs, deletedUs_card]
    exact coreA_le q (2 ^ p) (coreIndices Z).card hq hB hc

/-- Unconditional coefficient upper bound throughout the required deletion
range, with the core bound discharged by exact formula A or B. -/
theorem coefficient_upper_bound (q p r : ℕ) (hq : 2 ≤ q) (hr : r ≤ q - 1) :
    coefficient (graph q p) (m q p - r) ≤
      (m q p).choose r * (2 ^ q + 1) * (2 ^ p) ^ (2 * q + r) :=
  coefficient_bound_of_core_estimate q p r (coreUpperEstimate q p hq) hr

/-- Deleting q - 2 of the u-labels gives the first true coefficient lower
bound. The existence of that subset is finite-set cardinality, not enumeration. -/
theorem coefficient_lower_q_sub_two (q p : ℕ) (hq : 2 ≤ q) :
    (2 ^ p) ^ (3 * q - 2) ≤ coefficient (graph q p) (m q p - (q - 2)) := by
  obtain ⟨C, _, hC⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset (Fin q))) (n := q - 2)
    (by simpa only [Finset.card_univ, Fintype.card_fin] using Nat.sub_le q 2)
  have hqm : q ≤ m q p := by unfold m; omega
  calc
    _ ≤ coreA q (2 ^ p) (q - 2) := coreA_delete_q_sub_two_lower q (2 ^ p) hq
    _ = omegaCount (arrow q p) (deletedUs C) := by
      rw [omega_deletedUs, hC]
    _ ≤ _ := omegaCount_le_coefficient q p (q - 2)
      ((Nat.sub_le q 2).trans hqm) (deletedUs C)
      (by simpa only [deletedUs_card] using hC)

/-- Deleting all u-labels gives the second true coefficient lower bound. -/
theorem coefficient_lower_q (q p : ℕ) :
    (2 ^ p) ^ (3 * q + 1) ≤ coefficient (graph q p) (m q p - q) := by
  have hqm : q ≤ m q p := by unfold m; omega
  calc
    _ ≤ coreA q (2 ^ p) q := coreA_delete_all_lower q (2 ^ p)
    _ = omegaCount (arrow q p) (deletedUs (Finset.univ : Finset (Fin q))) := by
      rw [omega_deletedUs]
      simp
    _ ≤ _ := omegaCount_le_coefficient q p q hqm
      (deletedUs (Finset.univ : Finset (Fin q)))
      (by simp [deletedUs_card])

/-- The three actual graph coefficient estimates with all core assumptions
discharged. This holds for every q ≥ 2 and every p, including p = 0. -/
theorem three_coefficient_bounds (q p : ℕ) (hq : 2 ≤ q) :
    coefficient (graph q p) (m q p - (q - 1)) ≤
        (m q p).choose (q - 1) * (2 ^ q + 1) * (2 ^ p) ^ (3 * q - 1) ∧
      (2 ^ p) ^ (3 * q - 2) ≤ coefficient (graph q p) (m q p - (q - 2)) ∧
      (2 ^ p) ^ (3 * q + 1) ≤ coefficient (graph q p) (m q p - q) := by
  have he : 2 * q + (q - 1) = 3 * q - 1 := by omega
  refine ⟨?_, coefficient_lower_q_sub_two q p hq, coefficient_lower_q q p⟩
  simpa only [he] using coefficient_upper_bound q p (q - 1) hq le_rfl


end FormalProof.Research003.RS42FixedK
