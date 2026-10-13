module

public import FormalProof.Research003.RS42FixedKDecay
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
public import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Real-valued envelope, geometric bound, and limit.  These are estimates for
the numerical envelope only; graph coefficients are not substituted here.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open Filter
open scoped Topology

noncomputable def envelope (q p : ℕ) : ℝ := (envelopeNumerator q p : ℝ) / 2 ^ p

theorem envelope_pos (q p : ℕ) : 0 < envelope q p := by
  apply div_pos
  · exact_mod_cast envelopeNumerator_pos q p
  · exact pow_pos (by norm_num) p

theorem envelope_lt_one (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    envelope q p < 1 := by
  apply (div_lt_one (pow_pos (by norm_num : (0 : ℝ) < 2) p)).2
  exact_mod_cast envelopeNumerator_lt_pow q p hq hp

theorem envelope_initial (q : ℕ) (hq : 2 ≤ q) :
    envelope q (threshold q) ≤ 1 / (2 : ℝ) ^ (16 * q * logThreshold q) := by
  apply (div_le_div_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) _)
    (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  simpa only [one_mul] using
    (show (envelopeNumerator q (threshold q) : ℝ) * 2 ^ (16 * q * logThreshold q) ≤
      2 ^ threshold q by exact_mod_cast envelopeNumerator_initial_scaled q hq)

theorem envelope_step (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    envelope q (p + 1) < (2 / 3 : ℝ) * envelope q p := by
  have hc : (3 : ℝ) * envelopeNumerator q (p + 1) <
      4 * envelopeNumerator q p := by
    exact_mod_cast envelopeNumerator_step q p hq hp
  unfold envelope
  apply (div_lt_iff₀ (pow_pos (by norm_num : (0 : ℝ) < 2) (p + 1))).2
  have hcancel : (2 / 3 : ℝ) * ((envelopeNumerator q p : ℝ) / 2 ^ p) *
      2 ^ (p + 1) = (4 / 3 : ℝ) * envelopeNumerator q p := by
    rw [pow_succ]
    field_simp
    ring
  rw [hcancel]
  nlinarith

theorem envelope_geometric_add (q t : ℕ) (hq : 2 ≤ q) :
    envelope q (threshold q + t) ≤
      (1 / (2 : ℝ) ^ (16 * q * logThreshold q)) * (2 / 3 : ℝ) ^ t := by
  induction t with
  | zero => simpa using envelope_initial q hq
  | succ t ih =>
    calc
      envelope q (threshold q + (t + 1)) ≤
          (2 / 3 : ℝ) * envelope q (threshold q + t) := by
        simpa only [Nat.add_assoc] using
          (envelope_step q (threshold q + t) hq (by omega)).le
      _ ≤ (2 / 3 : ℝ) *
          ((1 / (2 : ℝ) ^ (16 * q * logThreshold q)) * (2 / 3 : ℝ) ^ t) :=
        mul_le_mul_of_nonneg_left ih (by norm_num)
      _ = (1 / (2 : ℝ) ^ (16 * q * logThreshold q)) * (2 / 3 : ℝ) ^ (t + 1) := by
        rw [pow_succ]
        ring

theorem envelope_geometric (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    envelope q p ≤
      (1 / (2 : ℝ) ^ (16 * q * logThreshold q)) * (2 / 3 : ℝ) ^ (p - threshold q) := by
  simpa only [Nat.add_sub_of_le hp] using envelope_geometric_add q (p - threshold q) hq

theorem envelope_tendsto_zero (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (envelope q) atTop (𝓝 (0 : ℝ)) := by
  apply (tendsto_add_atTop_iff_nat (threshold q)).1
  have hg : Tendsto (fun t : ℕ =>
      (1 / (2 : ℝ) ^ (16 * q * logThreshold q)) * (2 / 3 : ℝ) ^ t)
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one
        (by norm_num : (0 : ℝ) ≤ 2 / 3) (by norm_num : (2 / 3 : ℝ) < 1)).const_mul
          (1 / (2 : ℝ) ^ (16 * q * logThreshold q))
  apply squeeze_zero (fun t => (envelope_pos q (t + threshold q)).le) _ hg
  intro t
  simpa only [Nat.add_comm t (threshold q)] using envelope_geometric_add q t hq


end FormalProof.Research003.RS42FixedK
