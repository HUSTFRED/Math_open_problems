module
public import FormalProof.Research003.RS42StructuralRatio
public import FormalProof.Research003.RS42StructuralQuantitative
public import Mathlib.Data.Nat.Choose.Bounds
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Structural
open scoped BigOperators Topology
open Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

noncomputable def totalMultiplicity (a b : V → ℕ) : ℕ := ∑ v, (a v + b v)

/-- The threshold guarantees all three actual coefficient indices exist. -/
theorem structural_indices_valid (a b : V → ℕ) (k p : ℕ) (hk : 1 ≤ k)
    (hW : 1 ≤ totalMultiplicity a b)
    (hp : structuralThreshold (Fintype.card V) (totalMultiplicity a b) k ≤ p) :
    k + 1 ≤ Fintype.card (StructuralLabel a b p) := by
  have he := structuralThreshold_ge_eight_mul (Fintype.card V) (totalMultiplicity a b) k
  have hw := Nat.mul_le_mul_left p hW
  rw [structural_label_card]
  change k + 1 ≤ Fintype.card V + p * totalMultiplicity a b
  omega

theorem structural_binomial_numerator (a b : V → ℕ) (k p : ℕ) (hp : 1 ≤ p) :
    2 ^ (2 * Fintype.card V + 2 * k) *
      (Fintype.card (StructuralLabel a b p)).choose k ^ 2 ≤
        structuralNumerator (Fintype.card V) (totalMultiplicity a b) k p := by
  have hm : Fintype.card (StructuralLabel a b p) ≤
      (Fintype.card V + totalMultiplicity a b) * p := by
    rw [structural_label_card]
    have h := Nat.mul_le_mul_left (Fintype.card V) hp
    change Fintype.card V + p * totalMultiplicity a b ≤ _
    nlinarith
  have hc : (Fintype.card (StructuralLabel a b p)).choose k ≤
      ((Fintype.card V + totalMultiplicity a b) * p) ^ k :=
    (Nat.choose_le_pow _ _).trans (Nat.pow_le_pow_left hm k)
  calc
    _ ≤ 2 ^ (2 * Fintype.card V + 2 * k) *
        (((Fintype.card V + totalMultiplicity a b) * p) ^ k) ^ 2 :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hc 2)
    _ = structuralNumerator (Fintype.card V) (totalMultiplicity a b) k p := by
      unfold structuralNumerator
      rw [← pow_mul, show k * 2 = 2 * k by omega, mul_pow]
      ring

theorem structuralRatio_le_envelope (R : V → V → Prop) (a b : V → ℕ)
    (p k : ℕ) (hk : 1 ≤ k) (hp : 1 ≤ p)
    (hkm : k + 1 ≤ Fintype.card (StructuralLabel a b p))
    (hgap : 2 * maxCoreExponent R a b k ≤
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    structuralRatio R a b p k ≤ structuralEnvelope (Fintype.card V)
      (totalMultiplicity a b) k (structuralGap R a b k) p := by
  refine (structuralRatio_le_binomial_envelope R a b p k hk hkm hgap).trans ?_
  apply div_le_div_of_nonneg_right _ (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _)
  exact_mod_cast structural_binomial_numerator a b k p hp

theorem structuralRatio_geometric (R : V → V → Prop) (a b : V → ℕ)
    (p k : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ totalMultiplicity a b)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1))
    (hp : structuralThreshold (Fintype.card V) (totalMultiplicity a b) k ≤ p) :
    structuralRatio R a b p k ≤
      (1 / (2 : ℝ) ^ (44 * structuralN (Fintype.card V) (totalMultiplicity a b) k ^ 2)) *
        (2 / 3 : ℝ) ^ (p - structuralThreshold (Fintype.card V) (totalMultiplicity a b) k) := by
  have hp1 : 1 ≤ p := (structuralThreshold_pos _ _ _).trans_le hp
  exact (structuralRatio_le_envelope R a b p k hk hp1
    (structural_indices_valid a b k p hk hW hp) hgap.le).trans
      (structuralEnvelope_geometric _ _ _ _ _ hk (structuralGap_pos R a b k hgap) hp)

theorem structuralRatio_lt_one (R : V → V → Prop) (a b : V → ℕ)
    (p k : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ totalMultiplicity a b)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1))
    (hp : structuralThreshold (Fintype.card V) (totalMultiplicity a b) k ≤ p) :
    structuralRatio R a b p k < 1 := by
  have hp1 : 1 ≤ p := (structuralThreshold_pos _ _ _).trans_le hp
  exact (structuralRatio_le_envelope R a b p k hk hp1
    (structural_indices_valid a b k p hk hW hp) hgap.le).trans_lt
      (structuralEnvelope_lt_one _ _ _ _ _ hk (structuralGap_pos R a b k hgap) hp)

/-- Strict failure at the interior index m-k, using actual graph coefficients. -/
theorem structural_strict_failure (R : V → V → Prop) (a b : V → ℕ)
    (p k : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ totalMultiplicity a b)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1))
    (hp : structuralThreshold (Fintype.card V) (totalMultiplicity a b) k ≤ p) :
    let j := Fintype.card (StructuralLabel a b p) - k
    1 ≤ j ∧ j < Fintype.card (StructuralLabel a b p) ∧
      structuralIndepCount R a b p j ^ 2 <
        structuralIndepCount R a b p (j - 1) * structuralIndepCount R a b p (j + 1) := by
  have hkm := structural_indices_valid a b k p hk hW hp
  have hc (r : ℕ) (hr : r ≤ k + 1) : (0 : ℝ) < structuralS R a b p r := by
    exact_mod_cast structuralS_pos R a b p r (hr.trans hkm)
  have hratio := structuralRatio_lt_one R a b p k hk hW hgap hp
  have hstrict : structuralS R a b p k ^ 2 <
      structuralS R a b p (k - 1) * structuralS R a b p (k + 1) := by
    unfold structuralRatio at hratio
    have h := (div_lt_one (mul_pos (hc (k - 1) (by omega)) (hc (k + 1) le_rfl))).mp hratio
    exact_mod_cast h
  refine ⟨by omega, by omega, ?_⟩
  unfold structuralS at hstrict
  have hlo : Fintype.card (StructuralLabel a b p) - (k - 1) =
      Fintype.card (StructuralLabel a b p) - k + 1 := by omega
  have hhi : Fintype.card (StructuralLabel a b p) - (k + 1) =
      Fintype.card (StructuralLabel a b p) - k - 1 := by omega
  simpa only [hlo, hhi, Nat.mul_comm] using hstrict

theorem structuralRatio_tendsto_zero (R : V → V → Prop) (a b : V → ℕ)
    (k : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ totalMultiplicity a b)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    Tendsto (fun p : ℕ => structuralRatio R a b p k) atTop (𝓝 (0 : ℝ)) := by
  apply squeeze_zero' (Filter.Eventually.of_forall (fun p => by
    unfold structuralRatio
    positivity)) _ (structuralEnvelope_tendsto_zero (Fintype.card V)
      (totalMultiplicity a b) k (structuralGap R a b k) hk (structuralGap_pos R a b k hgap))
  filter_upwards [eventually_ge_atTop (structuralThreshold (Fintype.card V)
    (totalMultiplicity a b) k)] with p hp
  exact structuralRatio_le_envelope R a b p k hk
    ((structuralThreshold_pos _ _ _).trans_le hp)
    (structural_indices_valid a b k p hk hW hp) hgap.le

end FormalProof.Research003.RS42Structural
