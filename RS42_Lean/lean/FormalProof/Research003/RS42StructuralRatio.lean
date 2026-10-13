module
public import FormalProof.Research003.RS42StructuralCounts
public import FormalProof.Research003.RS42FixedKQuantitative
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Structural
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def structuralS (R : V → V → Prop) (a b : V → ℕ) (p r : ℕ) : ℕ :=
  structuralIndepCount R a b p (Fintype.card (StructuralLabel a b p) - r)

/-- Natural gap, used only under the explicit positive-second-difference condition. -/
noncomputable def structuralGap (R : V → V → Prop) (a b : V → ℕ) (k : ℕ) : ℕ :=
  maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1) -
    2 * maxCoreExponent R a b k

noncomputable def structuralRatio (R : V → V → Prop) (a b : V → ℕ) (p k : ℕ) : ℝ :=
  (structuralS R a b p k : ℝ) ^ 2 /
    ((structuralS R a b p (k - 1) : ℝ) * structuralS R a b p (k + 1))

theorem structuralS_pos (R : V → V → Prop) (a b : V → ℕ) (p r : ℕ)
    (hr : r ≤ Fintype.card (StructuralLabel a b p)) : 0 < structuralS R a b p r := by
  have h := structural_count_lower R a b p r hr
  have hp : 0 < 2 ^ (p * maxCoreExponent R a b r) := Nat.two_pow_pos _
  by_contra hn
  have hz : structuralS R a b p r = 0 := by omega
  change 2 ^ (p * maxCoreExponent R a b r) ≤ 2 ^ r * structuralS R a b p r at h
  rw [hz, mul_zero] at h
  omega

theorem structuralGap_pos (R : V → V → Prop) (a b : V → ℕ) (k : ℕ)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    0 < structuralGap R a b k := Nat.sub_pos_of_lt hgap

theorem structuralGap_add (R : V → V → Prop) (a b : V → ℕ) (k : ℕ)
    (hgap : 2 * maxCoreExponent R a b k ≤
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    2 * maxCoreExponent R a b k + structuralGap R a b k =
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1) := by
  unfold structuralGap
  omega

/-- Pure arithmetic combination. Its hypotheses will be discharged below by
actual graph counting theorems, not supplied as unproved final inputs. -/
theorem structural_three_bounds_cross (d k p C L M U eL eM eU δ : ℕ)
    (hk : 1 ≤ k) (he : 2 * eM + δ = eL + eU)
    (hM : M ≤ C * (2 ^ d * 2 ^ (p * eM)))
    (hL : 2 ^ (p * eL) ≤ 2 ^ (k - 1) * L)
    (hU : 2 ^ (p * eU) ≤ 2 ^ (k + 1) * U) :
    M ^ 2 * 2 ^ (p * δ) ≤ 2 ^ (2 * d + 2 * k) * C ^ 2 * (L * U) := by
  have hexp : (2 ^ (p * eM)) ^ 2 * 2 ^ (p * δ) =
      (2 : ℕ) ^ (p * eL) * 2 ^ (p * eU) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    nlinarith
  have hkexp : (2 : ℕ) ^ (k - 1) * 2 ^ (k + 1) = 2 ^ (2 * k) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    M ^ 2 * 2 ^ (p * δ) ≤ (C * (2 ^ d * 2 ^ (p * eM))) ^ 2 * 2 ^ (p * δ) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hM 2)
    _ = (2 ^ (2 * d) * C ^ 2) * ((2 ^ (p * eM)) ^ 2 * 2 ^ (p * δ)) := by
      rw [show 2 * d = d * 2 by omega, pow_mul]
      ring
    _ = (2 ^ (2 * d) * C ^ 2) * (2 ^ (p * eL) * 2 ^ (p * eU)) := by rw [hexp]
    _ ≤ (2 ^ (2 * d) * C ^ 2) * ((2 ^ (k - 1) * L) * (2 ^ (k + 1) * U)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul hL hU)
    _ = (2 ^ (2 * d) * C ^ 2) * ((2 ^ (k - 1) * 2 ^ (k + 1)) * (L * U)) := by ring
    _ = 2 ^ (2 * d + 2 * k) * C ^ 2 * (L * U) := by
      rw [hkexp, pow_add]
      ring

theorem structural_count_cross (R : V → V → Prop) (a b : V → ℕ) (p k : ℕ)
    (hk : 1 ≤ k) (hkm : k + 1 ≤ Fintype.card (StructuralLabel a b p))
    (hgap : 2 * maxCoreExponent R a b k ≤
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    structuralS R a b p k ^ 2 * 2 ^ (p * structuralGap R a b k) ≤
      2 ^ (2 * Fintype.card V + 2 * k) *
        (Fintype.card (StructuralLabel a b p)).choose k ^ 2 *
          (structuralS R a b p (k - 1) * structuralS R a b p (k + 1)) := by
  apply structural_three_bounds_cross _ _ _ _ _ _ _ _ _ _ _ hk
    (structuralGap_add R a b k hgap)
  · exact structural_count_upper R a b p k (by omega)
  · exact structural_count_lower R a b p (k - 1) (by omega)
  · exact structural_count_lower R a b p (k + 1) hkm

theorem structuralRatio_pos (R : V → V → Prop) (a b : V → ℕ) (p k : ℕ)
    (hkm : k + 1 ≤ Fintype.card (StructuralLabel a b p)) :
    0 < structuralRatio R a b p k := by
  have hc (r : ℕ) (hr : r ≤ k + 1) : (0 : ℝ) < structuralS R a b p r := by
    exact_mod_cast structuralS_pos R a b p r (hr.trans hkm)
  exact div_pos (pow_pos (hc k (by omega)) 2)
    (mul_pos (hc (k - 1) (by omega)) (hc (k + 1) le_rfl))

/-- The quantitative actual-ratio bound, derived without assumed coefficient
bounds. The condition is a finite-core second difference, not the target ratio. -/
theorem structuralRatio_le_binomial_envelope (R : V → V → Prop)
    (a b : V → ℕ) (p k : ℕ) (hk : 1 ≤ k)
    (hkm : k + 1 ≤ Fintype.card (StructuralLabel a b p))
    (hgap : 2 * maxCoreExponent R a b k ≤
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    structuralRatio R a b p k ≤
      (2 : ℝ) ^ (2 * Fintype.card V + 2 * k) *
        ((Fintype.card (StructuralLabel a b p)).choose k : ℝ) ^ 2 /
          2 ^ (p * structuralGap R a b k) := by
  have hc (r : ℕ) (hr : r ≤ k + 1) : (0 : ℝ) < structuralS R a b p r := by
    exact_mod_cast structuralS_pos R a b p r (hr.trans hkm)
  unfold structuralRatio
  apply (div_le_div_iff₀ (mul_pos (hc (k - 1) (by omega)) (hc (k + 1) le_rfl))
    (pow_pos (by norm_num : (0 : ℝ) < 2) _)).2
  exact_mod_cast structural_count_cross R a b p k hk hkm hgap

end FormalProof.Research003.RS42Structural
