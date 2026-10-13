module

public import FormalProof.Research003.RS42FixedKBounds
public import FormalProof.Research003.RS42FixedKQuantitative

set_option linter.style.header false
set_option linter.hashCommand false

/-!
The real ratio of genuine independent-set coefficients. Its comparison to
the explicit envelope is conditional on the three stated counting bounds;
this module does not claim those bounds without their core-counting proof.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90
open Filter
open scoped Topology

theorem coefficient_pos_of_le (q p j : ℕ) (hj : j ≤ m q p) :
    0 < coefficient (graph q p) j := by
  classical
  have hj' : j ≤ (allPlus q p).card := by simpa only [allPlus_card] using hj
  obtain ⟨s, hs, hcard⟩ := Finset.exists_subset_card_eq hj'
  have hind : Independent (graph q p) (s : Set (Vertex (Label q p))) := by
    intro v hv w hw hne
    exact allPlus_independent q p (hs hv) (hs hw) hne
  unfold coefficient
  exact Nat.card_pos_iff.mpr ⟨⟨⟨s, hind, hcard⟩⟩, inferInstance⟩

noncomputable def actualRatio (q p : ℕ) : ℝ :=
  (coefficient (graph q p) (m q p - (q - 1)) : ℝ) ^ 2 /
    ((coefficient (graph q p) (m q p - (q - 2)) : ℝ) *
      coefficient (graph q p) (m q p - q))

theorem actualRatio_pos (q p : ℕ) : 0 < actualRatio q p := by
  have hc (r : ℕ) : (0 : ℝ) < coefficient (graph q p) (m q p - r) := by
    exact_mod_cast coefficient_pos_of_le q p (m q p - r) (Nat.sub_le _ _)
  exact div_pos (pow_pos (hc (q - 1)) 2) (mul_pos (hc (q - 2)) (hc q))

theorem three_bounds_cross (q B A M P C : ℕ) (hq : 2 ≤ q)
    (hmid : M ≤ C * B ^ (3 * q - 1))
    (hlo : B ^ (3 * q - 2) ≤ A) (hhi : B ^ (3 * q + 1) ≤ P) :
    M ^ 2 * B ≤ C ^ 2 * (A * P) := by
  have he : (B ^ (3 * q - 1)) ^ 2 * B =
      B ^ (3 * q - 2) * B ^ (3 * q + 1) := by
    rw [← pow_mul, ← pow_succ, ← pow_add]
    congr 1
    omega
  calc
    M ^ 2 * B ≤ (C * B ^ (3 * q - 1)) ^ 2 * B :=
      Nat.mul_le_mul_right B (Nat.pow_le_pow_left hmid 2)
    _ = C ^ 2 * ((B ^ (3 * q - 1)) ^ 2 * B) := by ring
    _ = C ^ 2 * (B ^ (3 * q - 2) * B ^ (3 * q + 1)) := by rw [he]
    _ ≤ C ^ 2 * (A * P) := Nat.mul_le_mul_left _ (Nat.mul_le_mul hlo hhi)

theorem actualRatio_le_envelope_of_bounds (q p : ℕ) (hq : 2 ≤ q)
    (hmid : coefficient (graph q p) (m q p - (q - 1)) ≤
      (m q p).choose (q - 1) * (2 ^ q + 1) * (2 ^ p) ^ (3 * q - 1))
    (hlo : (2 ^ p) ^ (3 * q - 2) ≤ coefficient (graph q p) (m q p - (q - 2)))
    (hhi : (2 ^ p) ^ (3 * q + 1) ≤ coefficient (graph q p) (m q p - q)) :
    actualRatio q p ≤ envelope q p := by
  have hcross := three_bounds_cross q (2 ^ p)
    (coefficient (graph q p) (m q p - (q - 2)))
    (coefficient (graph q p) (m q p - (q - 1)))
    (coefficient (graph q p) (m q p - q))
    ((m q p).choose (q - 1) * (2 ^ q + 1)) hq hmid hlo hhi
  have hC : ((m q p).choose (q - 1) * (2 ^ q + 1)) ^ 2 = envelopeNumerator q p := by
    unfold envelopeNumerator m labelCount
    congr 1
    exact Nat.mul_comm _ _
  rw [hC] at hcross
  have hc (r : ℕ) : (0 : ℝ) < coefficient (graph q p) (m q p - r) := by
    exact_mod_cast coefficient_pos_of_le q p (m q p - r) (Nat.sub_le _ _)
  unfold actualRatio envelope
  apply (div_le_div_iff₀ (mul_pos (hc (q - 2)) (hc q))
    (pow_pos (by norm_num : (0 : ℝ) < 2) p)).2
  exact_mod_cast hcross

/-- A reusable squeeze statement. Its domination hypothesis remains explicit. -/
theorem actualRatio_tendsto_zero_of_eventual_bound (q : ℕ) (hq : 2 ≤ q)
    (hbound : ∀ p : ℕ, threshold q ≤ p → actualRatio q p ≤ envelope q p) :
    Tendsto (actualRatio q) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun p => (actualRatio_pos q p).le))
    _ (envelope_tendsto_zero q hq)
  exact Filter.eventually_atTop.2 ⟨threshold q, fun p hp => hbound p hp⟩


end FormalProof.Research003.RS42FixedK
