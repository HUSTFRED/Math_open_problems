module

public import Mathlib.Data.Nat.Find
public import Mathlib.Data.Nat.Choose.Bounds
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Integer parameter estimates for the fixed-distance construction.  These
estimates are independent of its graph and do not assert any graph-counting
or log-concavity theorem.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

theorem succ_le_two_pow (q : ℕ) : q + 1 ≤ 2 ^ q := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [pow_succ]
    omega

theorem logThreshold_exists (q : ℕ) : ∃ L : ℕ, q + 1 ≤ 2 ^ L :=
  ⟨q, succ_le_two_pow q⟩

/-- The least natural exponent bounding `q + 1`. -/
def logThreshold (q : ℕ) : ℕ := Nat.find (logThreshold_exists q)

def threshold (q : ℕ) : ℕ := 32 * q * logThreshold q

def labelCount (q p : ℕ) : ℕ := (3 * q + 1) * p + q + 1

theorem logThreshold_spec (q : ℕ) : q + 1 ≤ 2 ^ logThreshold q :=
  Nat.find_spec (logThreshold_exists q)

theorem logThreshold_min (q L : ℕ) (h : q + 1 ≤ 2 ^ L) :
    logThreshold q ≤ L :=
  Nat.find_min' (logThreshold_exists q) h

theorem logThreshold_le (q : ℕ) : logThreshold q ≤ q :=
  logThreshold_min q q (succ_le_two_pow q)

theorem two_le_logThreshold (q : ℕ) (hq : 2 ≤ q) : 2 ≤ logThreshold q := by
  have hs := logThreshold_spec q
  by_contra hn
  have hl : logThreshold q = 0 ∨ logThreshold q = 1 := by omega
  rcases hl with hl | hl <;> rw [hl] at hs <;> norm_num at hs <;> omega

theorem threshold_pos (q : ℕ) (hq : 2 ≤ q) : 0 < threshold q := by
  have hl := two_le_logThreshold q hq
  unfold threshold
  exact Nat.mul_pos (Nat.mul_pos (by omega) (by omega)) (by omega)

theorem labelCount_threshold_le (q : ℕ) (hq : 2 ≤ q) :
    labelCount q (threshold q) ≤ 129 * q ^ 2 * logThreshold q := by
  have hl := two_le_logThreshold q hq
  have hq1 : 1 ≤ q := by omega
  have hqL : q ≤ q * logThreshold q := by nlinarith
  have hq2 : q * logThreshold q ≤ q ^ 2 * logThreshold q := by
    nlinarith [Nat.mul_le_mul_right (q * logThreshold q) hq1]
  have hsmall : q + 1 ≤ q ^ 2 * logThreshold q := by
    nlinarith
  have ha : 3 * q + 1 ≤ 4 * q := by omega
  have hb := Nat.mul_le_mul_right (32 * q * logThreshold q) ha
  unfold labelCount threshold
  nlinarith

theorem vertexCount_threshold_le (q : ℕ) (hq : 2 ≤ q) :
    2 * labelCount q (threshold q) ≤ 258 * q ^ 2 * logThreshold q := by
  have h := labelCount_threshold_le q hq
  nlinarith

theorem labelCount_threshold_le_pow (q : ℕ) (hq : 2 ≤ q) :
    labelCount q (threshold q) ≤ 2 ^ (7 * logThreshold q) := by
  have hl := two_le_logThreshold q hq
  have hqpow : q ≤ 2 ^ logThreshold q := by
    have := logThreshold_spec q
    omega
  have hlpow : logThreshold q ≤ 2 ^ logThreshold q :=
    (logThreshold_le q).trans hqpow
  calc
    labelCount q (threshold q) ≤ 129 * q ^ 2 * logThreshold q :=
      labelCount_threshold_le q hq
    _ ≤ 256 * (2 ^ logThreshold q) ^ 2 * 2 ^ logThreshold q :=
      Nat.mul_le_mul (Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left hqpow 2)) hlpow
    _ = 2 ^ (8 + 3 * logThreshold q) := by
      rw [show 8 + 3 * logThreshold q = 8 + logThreshold q * 3 by omega,
        pow_add, pow_mul]
      norm_num
      ring
    _ ≤ 2 ^ (7 * logThreshold q) :=
      Nat.pow_le_pow_right (by omega) (by omega)

theorem coreFactor_le_pow (q : ℕ) (hq : 2 ≤ q) :
    2 ^ q + 1 ≤ 2 ^ (q * logThreshold q) := by
  have hl := two_le_logThreshold q hq
  have hp : 1 ≤ 2 ^ q := Nat.one_le_two_pow
  calc
    2 ^ q + 1 ≤ 2 ^ (q + 1) := by rw [pow_succ]; omega
    _ ≤ 2 ^ (q * logThreshold q) :=
      Nat.pow_le_pow_right (by omega) (by nlinarith)

theorem initial_factor_le_pow (q : ℕ) (hq : 2 ≤ q) :
    (2 ^ q + 1) * (labelCount q (threshold q)).choose (q - 1) ≤
      2 ^ (8 * q * logThreshold q) := by
  have hb := labelCount_threshold_le_pow q hq
  calc
    (2 ^ q + 1) * (labelCount q (threshold q)).choose (q - 1) ≤
        2 ^ (q * logThreshold q) * (2 ^ (7 * logThreshold q)) ^ (q - 1) :=
      Nat.mul_le_mul (coreFactor_le_pow q hq)
        ((Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hb _))
    _ = 2 ^ (q * logThreshold q + 7 * logThreshold q * (q - 1)) := by
      rw [← pow_mul, ← pow_add]
    _ ≤ 2 ^ (8 * q * logThreshold q) := by
      apply Nat.pow_le_pow_right (by omega)
      have h := Nat.mul_le_mul_left (7 * logThreshold q) (Nat.sub_le q 1)
      nlinarith

/-- A division-free version of the initial envelope estimate. -/
theorem initial_factor_square_scaled (q : ℕ) (hq : 2 ≤ q) :
    ((2 ^ q + 1) * (labelCount q (threshold q)).choose (q - 1)) ^ 2 *
      2 ^ (16 * q * logThreshold q) ≤ 2 ^ threshold q := by
  have h := Nat.pow_le_pow_left (initial_factor_le_pow q hq) 2
  calc
    ((2 ^ q + 1) * (labelCount q (threshold q)).choose (q - 1)) ^ 2 *
        2 ^ (16 * q * logThreshold q) ≤
        (2 ^ (8 * q * logThreshold q)) ^ 2 * 2 ^ (16 * q * logThreshold q) :=
      Nat.mul_le_mul_right _ h
    _ = 2 ^ threshold q := by
      rw [← pow_mul, ← pow_add]
      congr 1
      unfold threshold
      ring

theorem initial_factor_square_lt (q : ℕ) (hq : 2 ≤ q) :
    ((2 ^ q + 1) * (labelCount q (threshold q)).choose (q - 1)) ^ 2 <
      2 ^ threshold q := by
  have hl := two_le_logThreshold q hq
  calc
    ((2 ^ q + 1) * (labelCount q (threshold q)).choose (q - 1)) ^ 2 ≤
        (2 ^ (8 * q * logThreshold q)) ^ 2 :=
      Nat.pow_le_pow_left (initial_factor_le_pow q hq) 2
    _ < 2 ^ threshold q := by
      rw [← pow_mul]
      apply Nat.pow_lt_pow_right (by omega)
      unfold threshold
      nlinarith

theorem threshold_four_times_degree (q : ℕ) (hq : 2 ≤ q) :
    4 * (2 * (q - 1)) ≤ threshold q := by
  have hl := two_le_logThreshold q hq
  have hs : q - 1 ≤ q := Nat.sub_le _ _
  unfold threshold
  nlinarith

theorem interior_index (q p : ℕ) (hq : 2 ≤ q) :
    1 ≤ labelCount q p - (q - 1) ∧
      labelCount q p - (q - 1) < labelCount q p := by
  unfold labelCount
  omega

/-- A finite, division-free replacement for the geometric-series estimate. -/
theorem power_budget (n p : ℕ) (hn : n ≤ p) :
    (p + 1) ^ n * (p - n) ≤ p ^ (n + 1) := by
  induction n generalizing p with
  | zero => simp
  | succ n ih =>
    have hn0 : n ≤ p := by omega
    have hs : (p + 1) * (p - (n + 1)) ≤ p * (p - n) := by
      have h0 := Nat.sub_add_cancel hn0
      have h1 := Nat.sub_add_cancel hn
      nlinarith
    calc
      (p + 1) ^ (n + 1) * (p - (n + 1)) =
          (p + 1) ^ n * ((p + 1) * (p - (n + 1))) := by
        rw [pow_succ]
        ring
      _ ≤ (p + 1) ^ n * (p * (p - n)) := Nat.mul_le_mul_left _ hs
      _ = ((p + 1) ^ n * (p - n)) * p := by ring
      _ ≤ p ^ (n + 1) * p := Nat.mul_le_mul_right p (ih p hn0)
      _ = p ^ (n + 1 + 1) := (pow_succ _ _).symm

theorem power_budget_strict (n p : ℕ) (hn : 0 < n) (hnp : n ≤ p) :
    (p + 1) ^ n * (p - n) < p ^ (n + 1) := by
  cases n with
  | zero => omega
  | succ n =>
    have hn0 : n ≤ p := by omega
    have hs : (p + 1) * (p - (n + 1)) < p * (p - n) := by
      have h0 := Nat.sub_add_cancel hn0
      have h1 := Nat.sub_add_cancel hnp
      nlinarith
    calc
      (p + 1) ^ (n + 1) * (p - (n + 1)) =
          (p + 1) ^ n * ((p + 1) * (p - (n + 1))) := by
        rw [pow_succ]
        ring
      _ < (p + 1) ^ n * (p * (p - n)) :=
        Nat.mul_lt_mul_of_pos_left hs (Nat.pow_pos (by omega))
      _ = ((p + 1) ^ n * (p - n)) * p := by ring
      _ ≤ p ^ (n + 1) * p := Nat.mul_le_mul_right p (power_budget n p hn0)
      _ = p ^ (n + 1 + 1) := (pow_succ _ _).symm

/-- Thus `(1 + 1/p)^n < 4/3` when `p ≥ 4n`, with no real logarithms. -/
theorem power_ratio_lt_four_thirds (n p : ℕ) (hn : 0 < n) (hnp : 4 * n ≤ p) :
    3 * (p + 1) ^ n < 4 * p ^ n := by
  have hp : 0 < p := by omega
  have hn0 : n ≤ p := by omega
  have hbudget := power_budget_strict n p hn hn0
  rw [pow_succ] at hbudget
  have hcoeff : 3 * p ≤ 4 * (p - n) := by omega
  have hmul := Nat.mul_le_mul_left ((p + 1) ^ n) hcoeff
  apply (Nat.mul_lt_mul_right hp).mp
  nlinarith

theorem threshold_power_ratio (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    3 * (p + 1) ^ (2 * (q - 1)) < 4 * p ^ (2 * (q - 1)) := by
  apply power_ratio_lt_four_thirds
  · omega
  · exact (threshold_four_times_degree q hq).trans hp

/-- Compare the falling factorials one factor at a time. -/
theorem descFactorial_step (a b p r : ℕ) (hr : r ≤ b) :
    (a * (p + 1) + b).descFactorial r * p ^ r ≤
      (a * p + b).descFactorial r * (p + 1) ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hr0 : r ≤ b := by omega
    have hrM : r ≤ a * p + b := by omega
    have hrN : r ≤ a * (p + 1) + b := by omega
    have hs : (a * (p + 1) + b - r) * p ≤ (a * p + b - r) * (p + 1) := by
      have h0 := Nat.sub_add_cancel hrM
      have h1 := Nat.sub_add_cancel hrN
      nlinarith
    calc
      (a * (p + 1) + b).descFactorial (r + 1) * p ^ (r + 1) =
          ((a * (p + 1) + b).descFactorial r * p ^ r) *
            ((a * (p + 1) + b - r) * p) := by
        rw [Nat.descFactorial_succ, pow_succ]
        ring
      _ ≤ ((a * p + b).descFactorial r * (p + 1) ^ r) *
            ((a * p + b - r) * (p + 1)) := Nat.mul_le_mul (ih hr0) hs
      _ = (a * p + b).descFactorial (r + 1) * (p + 1) ^ (r + 1) := by
        rw [Nat.descFactorial_succ, pow_succ]
        ring

theorem choose_step (a b p r : ℕ) (hr : r ≤ b) :
    (a * (p + 1) + b).choose r * p ^ r ≤
      (a * p + b).choose r * (p + 1) ^ r := by
  have h := descFactorial_step a b p r hr
  simp only [Nat.descFactorial_eq_factorial_mul_choose, Nat.mul_assoc] at h
  exact Nat.le_of_mul_le_mul_left h (Nat.factorial_pos r)

theorem labelCount_choose_step (q p : ℕ) :
    (labelCount q (p + 1)).choose (q - 1) * p ^ (q - 1) ≤
      (labelCount q p).choose (q - 1) * (p + 1) ^ (q - 1) := by
  simpa only [labelCount, Nat.add_assoc] using
    choose_step (3 * q + 1) (q + 1) p (q - 1) (by omega)


end FormalProof.Research003.RS42FixedK
