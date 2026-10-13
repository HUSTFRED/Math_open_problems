module

public import FormalProof.Research003.RS42FixedKParameters

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Division-free decay estimates for the numerical envelope. This module does
not assume or assert the missing graph-counting inequalities.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

def envelopeNumerator (q p : ℕ) : ℕ :=
  ((2 ^ q + 1) * (labelCount q p).choose (q - 1)) ^ 2

theorem labelCount_choose_pos (q p : ℕ) :
    0 < (labelCount q p).choose (q - 1) := by
  apply Nat.choose_pos
  unfold labelCount
  omega

theorem envelopeNumerator_pos (q p : ℕ) : 0 < envelopeNumerator q p := by
  unfold envelopeNumerator
  exact Nat.pow_pos (Nat.mul_pos (Nat.succ_pos (2 ^ q)) (labelCount_choose_pos q p))

theorem choose_square_step (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    3 * ((labelCount q (p + 1)).choose (q - 1)) ^ 2 <
      4 * ((labelCount q p).choose (q - 1)) ^ 2 := by
  have hchoose := Nat.pow_le_pow_left (labelCount_choose_step q p) 2
  have hpower := threshold_power_ratio q p hq hp
  have hpos : 0 < ((labelCount q p).choose (q - 1)) ^ 2 :=
    Nat.pow_pos (labelCount_choose_pos q p)
  have hscaled := Nat.mul_lt_mul_of_pos_left hpower hpos
  have hsquare :
      ((labelCount q (p + 1)).choose (q - 1)) ^ 2 * p ^ (2 * (q - 1)) ≤
        ((labelCount q p).choose (q - 1)) ^ 2 * (p + 1) ^ (2 * (q - 1)) := by
    simpa only [mul_pow, ← pow_mul, Nat.mul_comm (q - 1) 2] using hchoose
  apply Nat.lt_of_mul_lt_mul_right (a := p ^ (2 * (q - 1)))
  nlinarith

/-- After dividing by the doubled denominator, this is the `2/3` step ratio. -/
theorem envelopeNumerator_step (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    3 * envelopeNumerator q (p + 1) < 4 * envelopeNumerator q p := by
  have h := Nat.mul_lt_mul_of_pos_left (choose_square_step q p hq hp)
    (Nat.pow_pos (Nat.succ_pos (2 ^ q)) : 0 < (2 ^ q + 1) ^ 2)
  unfold envelopeNumerator
  nlinarith

theorem envelopeNumerator_initial_scaled (q : ℕ) (hq : 2 ≤ q) :
    envelopeNumerator q (threshold q) * 2 ^ (16 * q * logThreshold q) ≤
      2 ^ threshold q :=
  initial_factor_square_scaled q hq

theorem envelopeNumerator_initial_lt (q : ℕ) (hq : 2 ≤ q) :
    envelopeNumerator q (threshold q) < 2 ^ threshold q :=
  initial_factor_square_lt q hq

theorem envelopeNumerator_lt_pow_add (q t : ℕ) (hq : 2 ≤ q) :
    envelopeNumerator q (threshold q + t) < 2 ^ (threshold q + t) := by
  induction t with
  | zero => simpa using envelopeNumerator_initial_lt q hq
  | succ t ih =>
    have hs := envelopeNumerator_step q (threshold q + t) hq (by omega)
    have hnext : envelopeNumerator q (threshold q + t + 1) <
        2 * envelopeNumerator q (threshold q + t) := by omega
    calc
      envelopeNumerator q (threshold q + (t + 1)) <
          2 * envelopeNumerator q (threshold q + t) := by simpa [Nat.add_assoc] using hnext
      _ < 2 * 2 ^ (threshold q + t) := Nat.mul_lt_mul_of_pos_left ih (by omega)
      _ = 2 ^ (threshold q + (t + 1)) := by
        rw [← Nat.add_assoc, pow_succ]
        ring

theorem envelopeNumerator_lt_pow (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    envelopeNumerator q p < 2 ^ p := by
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le hp
  exact envelopeNumerator_lt_pow_add q t hq

/-- An integer statement of the geometric envelope bound before division. -/
theorem envelopeNumerator_geometric (q t : ℕ) (hq : 2 ≤ q) :
    envelopeNumerator q (threshold q + t) * 3 ^ t ≤
      envelopeNumerator q (threshold q) * 4 ^ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    have hs := (envelopeNumerator_step q (threshold q + t) hq (by omega)).le
    have hm := Nat.mul_le_mul_right (3 ^ t) hs
    calc
      envelopeNumerator q (threshold q + (t + 1)) * 3 ^ (t + 1) =
          (3 * envelopeNumerator q (threshold q + t + 1)) * 3 ^ t := by
        rw [pow_succ]
        simp only [Nat.add_assoc]
        ring
      _ ≤ (4 * envelopeNumerator q (threshold q + t)) * 3 ^ t := hm
      _ = 4 * (envelopeNumerator q (threshold q + t) * 3 ^ t) := by ring
      _ ≤ 4 * (envelopeNumerator q (threshold q) * 4 ^ t) := Nat.mul_le_mul_left 4 ih
      _ = envelopeNumerator q (threshold q) * 4 ^ (t + 1) := by
        rw [pow_succ]
        ring

theorem envelopeNumerator_geometric_scaled (q t : ℕ) (hq : 2 ≤ q) :
    envelopeNumerator q (threshold q + t) * 3 ^ t *
        2 ^ (16 * q * logThreshold q) ≤ 2 ^ threshold q * 4 ^ t := by
  have hg := Nat.mul_le_mul_right (2 ^ (16 * q * logThreshold q))
    (envelopeNumerator_geometric q t hq)
  have hi := Nat.mul_le_mul_right (4 ^ t) (envelopeNumerator_initial_scaled q hq)
  calc
    envelopeNumerator q (threshold q + t) * 3 ^ t *
        2 ^ (16 * q * logThreshold q) ≤
        (envelopeNumerator q (threshold q) * 4 ^ t) *
          2 ^ (16 * q * logThreshold q) := hg
    _ = (envelopeNumerator q (threshold q) * 2 ^ (16 * q * logThreshold q)) *
          4 ^ t := by ring
    _ ≤ 2 ^ threshold q * 4 ^ t := hi


end FormalProof.Research003.RS42FixedK
