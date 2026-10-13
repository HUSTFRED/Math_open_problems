module

public import FormalProof.Research003.RS42StructuralParameters
public import FormalProof.Research003.RS42FixedKQuantitative

set_option linter.style.header false
set_option linter.hashCommand false

/-! Quantitative estimates for the explicit structural envelope. These estimates
do not assume the desired envelope inequality for any graph coefficient. -/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural

open Filter
open scoped Topology

noncomputable def structuralEnvelope (d W k Delta p : ℕ) : ℝ :=
  (structuralNumerator d W k p : ℝ) / 2 ^ (p * Delta)

theorem structuralEnvelope_nonneg (d W k Delta p : ℕ) :
    0 ≤ structuralEnvelope d W k Delta p := by
  unfold structuralEnvelope
  exact div_nonneg (Nat.cast_nonneg _) (pow_nonneg (by norm_num) _)

theorem structuralEnvelope_initial (d W k Delta : ℕ) (hDelta : 1 ≤ Delta) :
    structuralEnvelope d W k Delta (structuralThreshold d W k) ≤
      1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2) := by
  apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  simpa only [one_mul] using
    (show (structuralNumerator d W k (structuralThreshold d W k) : ℝ) *
        2 ^ (44 * structuralN d W k ^ 2) ≤
        2 ^ (structuralThreshold d W k * Delta) by
      exact_mod_cast structuralNumerator_initial_scaled d W k Delta hDelta)

/-- Every step after the explicit threshold contracts by at least `2/3`. -/
theorem structuralEnvelope_step (d W k Delta p : ℕ) (hk : 1 ≤ k)
    (hDelta : 1 ≤ Delta) (hp : structuralThreshold d W k ≤ p) :
    structuralEnvelope d W k Delta (p + 1) ≤
      (2 / 3 : ℝ) * structuralEnvelope d W k Delta p := by
  have hc : (3 : ℝ) * structuralNumerator d W k (p + 1) ≤
      4 * structuralNumerator d W k p := by
    exact_mod_cast structuralNumerator_step d W k p hk
      ((structuralThreshold_ge_eight_mul d W k).trans hp)
  have hpow : (2 : ℝ) ≤ 2 ^ Delta := by
    exact_mod_cast (Nat.pow_le_pow_right (by omega : 0 < 2) hDelta :
      (2 : ℕ) ^ 1 ≤ 2 ^ Delta)
  have hm := mul_le_mul_of_nonneg_left hpow
    (Nat.cast_nonneg (structuralNumerator d W k p) :
      (0 : ℝ) ≤ structuralNumerator d W k p)
  unfold structuralEnvelope
  apply (div_le_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) ((p + 1) * Delta))).2
  have hcancel : (2 / 3 : ℝ) *
      ((structuralNumerator d W k p : ℝ) / 2 ^ (p * Delta)) *
        2 ^ ((p + 1) * Delta) =
      (2 / 3 : ℝ) * structuralNumerator d W k p * 2 ^ Delta := by
    rw [Nat.add_mul, Nat.one_mul, pow_add]
    field_simp
  rw [hcancel]
  nlinarith

theorem structuralEnvelope_geometric_add (d W k Delta t : ℕ) (hk : 1 ≤ k)
    (hDelta : 1 ≤ Delta) :
    structuralEnvelope d W k Delta (structuralThreshold d W k + t) ≤
      (1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2)) * (2 / 3 : ℝ) ^ t := by
  induction t with
  | zero => simpa using structuralEnvelope_initial d W k Delta hDelta
  | succ t ih =>
    calc
      structuralEnvelope d W k Delta (structuralThreshold d W k + (t + 1)) ≤
          (2 / 3 : ℝ) *
            structuralEnvelope d W k Delta (structuralThreshold d W k + t) := by
        simpa only [Nat.add_assoc] using
          structuralEnvelope_step d W k Delta (structuralThreshold d W k + t)
            hk hDelta (by omega)
      _ ≤ (2 / 3 : ℝ) *
          ((1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2)) * (2 / 3 : ℝ) ^ t) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2)) *
          (2 / 3 : ℝ) ^ (t + 1) := by rw [pow_succ]; ring

theorem structuralEnvelope_geometric (d W k Delta p : ℕ) (hk : 1 ≤ k)
    (hDelta : 1 ≤ Delta) (hp : structuralThreshold d W k ≤ p) :
    structuralEnvelope d W k Delta p ≤
      (1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2)) *
        (2 / 3 : ℝ) ^ (p - structuralThreshold d W k) := by
  simpa only [Nat.add_sub_of_le hp] using
    structuralEnvelope_geometric_add d W k Delta (p - structuralThreshold d W k)
      hk hDelta

theorem structuralEnvelope_lt_one (d W k Delta p : ℕ) (hk : 1 ≤ k)
    (hDelta : 1 ≤ Delta) (hp : structuralThreshold d W k ≤ p) :
    structuralEnvelope d W k Delta p < 1 := by
  have hC : 0 ≤ 1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2) := by
    exact div_nonneg (by norm_num) (pow_nonneg (by norm_num) _)
  have ht : ∀ t : ℕ, (2 / 3 : ℝ) ^ t ≤ 1 := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [pow_succ]
      calc
        (2 / 3 : ℝ) ^ t * (2 / 3 : ℝ) ≤ 1 * (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 := by norm_num
  have hn : 0 < structuralN d W k := by unfold structuralN; omega
  have hn2 : 0 < structuralN d W k ^ 2 := pow_pos hn _
  have hnat : (2 : ℕ) ^ 0 < 2 ^ (44 * structuralN d W k ^ 2) :=
    Nat.pow_lt_pow_right (by omega) (by omega)
  have hden : (1 : ℝ) < 2 ^ (44 * structuralN d W k ^ 2) := by exact_mod_cast hnat
  calc
    structuralEnvelope d W k Delta p ≤
        (1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2)) *
          (2 / 3 : ℝ) ^ (p - structuralThreshold d W k) :=
      structuralEnvelope_geometric d W k Delta p hk hDelta hp
    _ ≤ 1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2) := by
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left (ht (p - structuralThreshold d W k)) hC
    _ < 1 := (div_lt_one (by linarith)).2 hden

theorem structuralEnvelope_tendsto_zero (d W k Delta : ℕ) (hk : 1 ≤ k)
    (hDelta : 1 ≤ Delta) :
    Tendsto (structuralEnvelope d W k Delta) atTop (𝓝 (0 : ℝ)) := by
  apply (tendsto_add_atTop_iff_nat (structuralThreshold d W k)).1
  have hg : Tendsto (fun t : ℕ =>
      (1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2)) * (2 / 3 : ℝ) ^ t)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)).const_mul
          (1 / (2 : ℝ) ^ (44 * structuralN d W k ^ 2))
  apply squeeze_zero
    (fun t => structuralEnvelope_nonneg d W k Delta (t + structuralThreshold d W k)) _ hg
  intro t
  simpa only [Nat.add_comm t (structuralThreshold d W k)] using
    structuralEnvelope_geometric_add d W k Delta t hk hDelta


end FormalProof.Research003.RS42Structural
