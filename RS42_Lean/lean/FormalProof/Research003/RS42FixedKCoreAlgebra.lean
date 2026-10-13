module

public import FormalProof.Research003.RS42FixedKParameters

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Pure natural-number estimates on the two proposed core-deletion formulas.
This file does not identify these expressions with any graph count.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

def coreA (q B t : ℕ) : ℕ :=
  B ^ (3 * t) * ((B ^ 2 + B) ^ (q - t) + B ^ (q - t + 1))

def coreB (q B t : ℕ) : ℕ :=
  B ^ (3 * t + 1) * (B ^ 2 + B) ^ (q - t)

theorem branch_pow_le (B s : ℕ) (hB : 1 ≤ B) :
    (B ^ 2 + B) ^ s ≤ 2 ^ s * B ^ (2 * s) := by
  have h : B ^ 2 + B ≤ 2 * B ^ 2 := by nlinarith
  have hp := Nat.pow_le_pow_left h s
  simpa only [mul_pow, ← pow_mul] using hp

theorem coreA_first_le (q B t : ℕ) (hB : 1 ≤ B) (ht : t ≤ q) :
    B ^ (3 * t) * (B ^ 2 + B) ^ (q - t) ≤ 2 ^ q * B ^ (2 * q + t) := by
  calc
    B ^ (3 * t) * (B ^ 2 + B) ^ (q - t) ≤
        B ^ (3 * t) * (2 ^ (q - t) * B ^ (2 * (q - t))) :=
      Nat.mul_le_mul_left _ (branch_pow_le B (q - t) hB)
    _ = 2 ^ (q - t) * B ^ (2 * q + t) := by
      rw [← mul_assoc, mul_comm (B ^ (3 * t)), mul_assoc, ← pow_add]
      congr 2
      omega
    _ ≤ 2 ^ q * B ^ (2 * q + t) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.sub_le q t))

theorem coreA_second_eq (q B t : ℕ) (ht : t ≤ q) :
    B ^ (3 * t) * B ^ (q - t + 1) = B ^ (q + 2 * t + 1) := by
  rw [← pow_add]
  congr 1
  omega

theorem coreA_le (q B t : ℕ) (hq : 2 ≤ q) (hB : 1 ≤ B) (ht : t ≤ q - 1) :
    coreA q B t ≤ (2 ^ q + 1) * B ^ (2 * q + t) := by
  have htq : t ≤ q := by omega
  have hfirst := coreA_first_le q B t hB htq
  have hsecond : B ^ (3 * t) * B ^ (q - t + 1) ≤ B ^ (2 * q + t) := by
    rw [coreA_second_eq q B t htq]
    exact Nat.pow_le_pow_right (by omega) (by omega)
  unfold coreA
  rw [mul_add]
  nlinarith

theorem coreB_le (q B t : ℕ) (hq : 2 ≤ q) (hB : 1 ≤ B)
    (ht : t + 1 ≤ q - 1) :
    coreB q B t ≤ (2 ^ q + 1) * B ^ (2 * q + (t + 1)) := by
  have htq : t ≤ q := by omega
  unfold coreB
  calc
    B ^ (3 * t + 1) * (B ^ 2 + B) ^ (q - t) ≤
        B ^ (3 * t + 1) * (2 ^ (q - t) * B ^ (2 * (q - t))) :=
      Nat.mul_le_mul_left _ (branch_pow_le B (q - t) hB)
    _ = 2 ^ (q - t) * B ^ (2 * q + (t + 1)) := by
      rw [← mul_assoc, mul_comm (B ^ (3 * t + 1)), mul_assoc, ← pow_add]
      congr 2
      omega
    _ ≤ 2 ^ q * B ^ (2 * q + (t + 1)) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (Nat.sub_le q t))
    _ ≤ (2 ^ q + 1) * B ^ (2 * q + (t + 1)) :=
      Nat.mul_le_mul_right _ (by omega)

theorem coreA_delete_q_sub_two_lower (q B : ℕ) (hq : 2 ≤ q) :
    B ^ (3 * q - 2) ≤ coreA q B (q - 2) := by
  have hsub : q - (q - 2) = 2 := by omega
  have hexp : 3 * (q - 2) + 4 = 3 * q - 2 := by omega
  have hbase : B ^ 2 ≤ B ^ 2 + B := by omega
  have hpow : B ^ 4 ≤ (B ^ 2 + B) ^ 2 := by
    simpa only [← pow_mul] using Nat.pow_le_pow_left hbase 2
  unfold coreA
  rw [hsub]
  calc
    B ^ (3 * q - 2) = B ^ (3 * (q - 2)) * B ^ 4 := by
      rw [← pow_add, hexp]
    _ ≤ B ^ (3 * (q - 2)) * (B ^ 2 + B) ^ 2 := Nat.mul_le_mul_left _ hpow
    _ ≤ B ^ (3 * (q - 2)) * ((B ^ 2 + B) ^ 2 + B ^ (2 + 1)) :=
      Nat.mul_le_mul_left _ (by omega)

theorem coreA_delete_all_lower (q B : ℕ) :
    B ^ (3 * q + 1) ≤ coreA q B q := by
  unfold coreA
  simp only [Nat.sub_self, pow_zero, Nat.zero_add, pow_one]
  rw [pow_succ]
  exact Nat.mul_le_mul_left _ (by omega)


end FormalProof.Research003.RS42FixedK
