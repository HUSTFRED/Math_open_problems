module

public import FormalProof.Research003.RS42FixedKParameters
public import Mathlib.Analysis.SpecialFunctions.Log.Base

set_option linter.style.header false
set_option linter.hashCommand false

/-! The explicit real-logarithmic size estimate for the initial parameter. -/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

theorem one_le_parameter_log (q : ℕ) (hq : 2 ≤ q) :
    1 ≤ Real.logb 2 ((q : ℝ) + 1) := by
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have h := Real.logb_le_logb_of_le (b := (2 : ℝ)) (x := (2 : ℝ))
    (y := (q : ℝ) + 1) (by norm_num) (by norm_num) (by linarith)
  simpa only [Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)] using h

theorem logThreshold_le_twice_log (q : ℕ) (hq : 2 ≤ q) :
    (logThreshold q : ℝ) ≤ 2 * Real.logb 2 ((q : ℝ) + 1) := by
  have hL := two_le_logThreshold q hq
  have hprev : 2 ^ (logThreshold q - 1) < q + 1 := by
    apply Nat.lt_of_not_ge
    intro h
    have hmin := logThreshold_min q (logThreshold q - 1) h
    omega
  have hprevR : (2 : ℝ) ^ (logThreshold q - 1) < (q : ℝ) + 1 := by
    exact_mod_cast hprev
  have hlog := Real.logb_lt_logb (b := (2 : ℝ)) (by norm_num)
    (pow_pos (by norm_num) (logThreshold q - 1)) hprevR
  rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2),
    mul_one, Nat.cast_sub (by omega : 1 ≤ logThreshold q), Nat.cast_one] at hlog
  have hone := one_le_parameter_log q hq
  linarith

theorem vertexCount_threshold_log_bound (k : ℕ) (hk : 1 ≤ k) :
    (2 * labelCount (k + 1) (threshold (k + 1)) : ℕ) ≤
      (2064 : ℝ) * (k : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) + 2) := by
  have hq : 2 ≤ k + 1 := by omega
  have hsize : (2 * labelCount (k + 1) (threshold (k + 1)) : ℕ) ≤
      (258 : ℝ) * ((k + 1 : ℕ) : ℝ) ^ 2 * logThreshold (k + 1) := by
    exact_mod_cast vertexCount_threshold_le (k + 1) hq
  have hlog := logThreshold_le_twice_log (k + 1) hq
  have hone := one_le_parameter_log (k + 1) hq
  norm_num only [Nat.cast_add, Nat.cast_one] at hsize hlog hone ⊢
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.logb 2 ((k : ℝ) + 2) := by
    convert le_trans (by norm_num : (0 : ℝ) ≤ 1) hone using 1; congr 1; ring
  have hL : (logThreshold (k + 1) : ℝ) ≤ 2 * Real.logb 2 ((k : ℝ) + 2) := by
    convert hlog using 1; congr 2; ring
  calc
    (2 * labelCount (k + 1) (threshold (k + 1)) : ℕ) ≤
        (258 : ℝ) * ((k : ℝ) + 1) ^ 2 * logThreshold (k + 1) := hsize
    _ ≤ (258 : ℝ) * ((k : ℝ) + 1) ^ 2 *
        (2 * Real.logb 2 ((k : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) (sq_nonneg _))
    _ ≤ (258 : ℝ) * (4 * (k : ℝ) ^ 2) *
        (2 * Real.logb 2 ((k : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (mul_nonneg (by norm_num) hlog0)
    _ = (2064 : ℝ) * (k : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) + 2) := by ring


end FormalProof.Research003.RS42FixedK
