module

public import FormalProof.Research003.RS42FixedKSize

set_option linter.style.header false
set_option linter.hashCommand false

/-! Comparison of the two explicit size bounds, including the intermediate
integer bound itself rather than only their common lower bound N. -/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

theorem integer_size_bound_le_log_bound (k : ℕ) (hk : 1 ≤ k) :
    ((258 * (k + 1) ^ 2 * logThreshold (k + 1) : ℕ) : ℝ) ≤
      2064 * (k : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) + 2) := by
  have hq : 2 ≤ k + 1 := by omega
  have hlog := logThreshold_le_twice_log (k + 1) hq
  have hone := one_le_parameter_log (k + 1) hq
  norm_num only [Nat.cast_add, Nat.cast_one] at hlog hone
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hsq : ((k : ℝ) + 1) ^ 2 ≤ 4 * (k : ℝ) ^ 2 := by nlinarith
  have hlog0 : 0 ≤ Real.logb 2 ((k : ℝ) + 2) := by
    convert le_trans (by norm_num : (0 : ℝ) ≤ 1) hone using 1; congr 1; ring
  have hL : (logThreshold (k + 1) : ℝ) ≤ 2 * Real.logb 2 ((k : ℝ) + 2) := by
    convert hlog using 1; congr 2; ring
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  calc
    (258 : ℝ) * ((k : ℝ) + 1) ^ 2 * logThreshold (k + 1) ≤
        (258 : ℝ) * ((k : ℝ) + 1) ^ 2 *
          (2 * Real.logb 2 ((k : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_left hL (mul_nonneg (by norm_num) (sq_nonneg _))
    _ ≤ (258 : ℝ) * (4 * (k : ℝ) ^ 2) *
        (2 * Real.logb 2 ((k : ℝ) + 2)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq (by norm_num))
        (mul_nonneg (by norm_num) hlog0)
    _ = (2064 : ℝ) * (k : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) + 2) := by ring


end FormalProof.Research003.RS42FixedK
