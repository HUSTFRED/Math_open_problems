module

public import FormalProof.Research003.RS42FixedKParameters

set_option linter.style.header false
set_option linter.hashCommand false

/-! Integer estimates for the structural envelope. No graph coefficient bound
is assumed here. The logarithmic parameter is the least natural exponent. -/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural

theorem structuralLog_exists (d W : ℕ) : ∃ ell : ℕ, d + W ≤ 2 ^ ell := by
  refine ⟨d + W, ?_⟩
  have h := RS42FixedK.succ_le_two_pow (d + W)
  omega

def structuralLog (d W : ℕ) : ℕ := Nat.find (structuralLog_exists d W)

theorem structuralLog_spec (d W : ℕ) : d + W ≤ 2 ^ structuralLog d W :=
  Nat.find_spec (structuralLog_exists d W)

theorem structuralLog_min (d W ell : ℕ) (h : d + W ≤ 2 ^ ell) :
    structuralLog d W ≤ ell := Nat.find_min' (structuralLog_exists d W) h

def structuralN (d W k : ℕ) : ℕ := d + k + structuralLog d W + 1

def structuralThreshold (d W k : ℕ) : ℕ := 64 * structuralN d W k ^ 2

def structuralNumerator (d W k p : ℕ) : ℕ :=
  2 ^ (2 * d + 2 * k) * (d + W) ^ (2 * k) * p ^ (2 * k)

theorem structuralThreshold_pos (d W k : ℕ) : 0 < structuralThreshold d W k := by
  unfold structuralThreshold structuralN
  exact Nat.mul_pos (by omega) (pow_pos (by omega) 2)

theorem structuralThreshold_ge_eight_mul (d W k : ℕ) :
    8 * k ≤ structuralThreshold d W k := by
  have hn : 1 ≤ structuralN d W k := by unfold structuralN; omega
  have hk : k ≤ structuralN d W k := by unfold structuralN; omega
  have hs : structuralN d W k ≤ structuralN d W k ^ 2 := by nlinarith
  unfold structuralThreshold
  omega

/-- The polynomial numerator estimate, with a transparent logarithmic input. -/
theorem structuralNumerator_initial_of_log (d W k ell : ℕ)
    (hell : d + W ≤ 2 ^ ell) :
    structuralNumerator d W k (64 * (d + k + ell + 1) ^ 2) ≤
      2 ^ (20 * (d + k + ell + 1) ^ 2) := by
  let n := d + k + ell + 1
  have hn : 1 ≤ n := by dsimp [n]; omega
  have hdk : d + k ≤ n := by dsimp [n]; omega
  have hk : k ≤ n := by omega
  have hl : ell ≤ n := by dsimp [n]; omega
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hnPow : n ≤ 2 ^ n := by
    have h := RS42FixedK.succ_le_two_pow n
    omega
  have hp : 64 * n ^ 2 ≤ 2 ^ (8 * n) := by
    calc
      64 * n ^ 2 ≤ 64 * (2 ^ n) ^ 2 :=
        Nat.mul_le_mul_left 64 (Nat.pow_le_pow_left hnPow 2)
      _ = 2 ^ (6 + 2 * n) := by
        calc
          64 * (2 ^ n) ^ 2 = 2 ^ 6 * (2 ^ n) ^ 2 := by norm_num
          _ = 2 ^ 6 * 2 ^ (n * 2) :=
            congrArg (fun x : ℕ => 2 ^ 6 * x) (pow_mul (2 : ℕ) n 2).symm
          _ = 2 ^ (6 + n * 2) := (pow_add (2 : ℕ) 6 (n * 2)).symm
          _ = 2 ^ (6 + 2 * n) := by congr 1; omega
      _ ≤ 2 ^ (8 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  have hfirst : 2 ^ (2 * d + 2 * k) ≤ 2 ^ (2 * n ^ 2) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hsecond : (d + W) ^ (2 * k) ≤ 2 ^ (2 * n ^ 2) := by
    calc
      (d + W) ^ (2 * k) ≤ (2 ^ ell) ^ (2 * k) :=
        Nat.pow_le_pow_left hell _
      _ = 2 ^ (ell * (2 * k)) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ (2 * n ^ 2) := by
        apply Nat.pow_le_pow_right (by omega)
        have h := Nat.mul_le_mul hl hk
        nlinarith
  have hthird : (64 * n ^ 2) ^ (2 * k) ≤ 2 ^ (16 * n ^ 2) := by
    calc
      (64 * n ^ 2) ^ (2 * k) ≤ (2 ^ (8 * n)) ^ (2 * k) :=
        Nat.pow_le_pow_left hp _
      _ = 2 ^ (8 * n * (2 * k)) := (pow_mul _ _ _).symm
      _ ≤ 2 ^ (16 * n ^ 2) := by
        apply Nat.pow_le_pow_right (by omega)
        have h := Nat.mul_le_mul_left n hk
        nlinarith
  change structuralNumerator d W k (64 * n ^ 2) ≤ 2 ^ (20 * n ^ 2)
  unfold structuralNumerator
  calc
    2 ^ (2 * d + 2 * k) * (d + W) ^ (2 * k) * (64 * n ^ 2) ^ (2 * k) ≤
        2 ^ (2 * n ^ 2) * 2 ^ (2 * n ^ 2) * 2 ^ (16 * n ^ 2) :=
      Nat.mul_le_mul (Nat.mul_le_mul hfirst hsecond) hthird
    _ = 2 ^ (20 * n ^ 2) := by
      rw [← pow_add, ← pow_add]
      congr 1
      ring

theorem structuralNumerator_initial (d W k : ℕ) :
    structuralNumerator d W k (structuralThreshold d W k) ≤
      2 ^ (20 * structuralN d W k ^ 2) :=
  structuralNumerator_initial_of_log d W k (structuralLog d W)
    (structuralLog_spec d W)

theorem structuralNumerator_initial_scaled (d W k Delta : ℕ) (hDelta : 1 ≤ Delta) :
    structuralNumerator d W k (structuralThreshold d W k) *
        2 ^ (44 * structuralN d W k ^ 2) ≤
      2 ^ (structuralThreshold d W k * Delta) := by
  calc
    structuralNumerator d W k (structuralThreshold d W k) *
        2 ^ (44 * structuralN d W k ^ 2) ≤
        2 ^ (20 * structuralN d W k ^ 2) * 2 ^ (44 * structuralN d W k ^ 2) :=
      Nat.mul_le_mul_right _ (structuralNumerator_initial d W k)
    _ = 2 ^ structuralThreshold d W k := by
      rw [← pow_add]
      congr 1
      unfold structuralThreshold
      ring
    _ ≤ 2 ^ (structuralThreshold d W k * Delta) := by
      apply Nat.pow_le_pow_right (by omega)
      nlinarith

theorem structuralNumerator_step (d W k p : ℕ) (hk : 1 ≤ k) (hp : 8 * k ≤ p) :
    3 * structuralNumerator d W k (p + 1) ≤ 4 * structuralNumerator d W k p := by
  have h := (RS42FixedK.power_ratio_lt_four_thirds (2 * k) p
    (by omega) (by omega)).le
  have hm := Nat.mul_le_mul_left (2 ^ (2 * d + 2 * k) * (d + W) ^ (2 * k)) h
  unfold structuralNumerator
  nlinarith


end FormalProof.Research003.RS42Structural
