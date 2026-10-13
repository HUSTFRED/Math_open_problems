module
public import FormalProof.Research003.RS42SimultaneousCore
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Simultaneous
open RS42Structural RS42Counterexample90 RS42FixedKDeletion
open scoped BigOperators

theorem prefix_sum (t s : ℕ) (hs : s ≤ t) :
    (∑ i : Fin t, if i.val < s then 1 else 0) = s := by
  simp [Fin.card_filter_val_lt, Nat.min_eq_right hs]

theorem single_sum (t s : ℕ) (hs : s < t) :
    (∑ i : Fin t, if i.val = s then 1 else 0) = 1 := by
  have h (i : Fin t) : i.val = s ↔ i = ⟨s,hs⟩ := by
    exact ⟨fun hh => Fin.ext hh, fun hh => congrArg Fin.val hh⟩
  simp_rw [h]
  simp

theorem witness_counts (t s : ℕ) (odd : Bool) (hs : s ≤ t)
    (ho : odd = true → s < t) :
    coreExponent (outWeight t) (inWeight t) (witness t s odd) =
      4*t+3*s+(if odd then 1 else 0) ∧
    (zeroSet (witness t s odd)).card = 2*s+(if odd then 1 else 0) := by
  have hsingle : (∑ i : Fin t, if i.val = s ∧ odd = true then 1 else 0) =
      (if odd then 1 else 0) := by
    cases odd
    · simp
    · simpa using single_sum t s (ho rfl)
  have he (i : Fin t) : blockExponent (witness t s odd) i =
      4+3*(if i.val < s then 1 else 0)+(if i.val = s ∧ odd = true then 1 else 0) := by
    rw [(witness_block s odd i).1]
    by_cases hl : i.val < s
    · have hn : i.val ≠ s := by omega
      simp [hl,hn]
    · by_cases hh : i.val = s ∧ odd = true <;> simp [hl,hh]
  have hz (i : Fin t) : blockZeros (witness t s odd) i =
      2*(if i.val < s then 1 else 0)+(if i.val = s ∧ odd = true then 1 else 0) := by
    rw [(witness_block s odd i).2]
    by_cases hl : i.val < s
    · have hn : i.val ≠ s := by omega
      simp [hl,hn]
    · by_cases hh : i.val = s ∧ odd = true <;> simp [hl,hh]
  rw [exponent_split, zeros_split]
  simp_rw [he,hz]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, prefix_sum t s hs, hsingle]
  simp [Nat.mul_comm]

theorem maximum_doubled_upper (t r : ℕ) :
    2*maxCoreExponent (arrow t) (outWeight t) (inWeight t) r ≤ 8*t+3*r := by
  obtain ⟨f,hf,he⟩ := maxCoreExponent_attained (arrow t) (outWeight t) (inWeight t) r
  have hf' : legal (arrow t) f ∧ (zeroSet f).card ≤ r := by
    classical
    simpa only [admissibleCoreStates,Finset.mem_filter,Finset.mem_univ,true_and] using hf
  rw [he]
  have h := exponent_upper f hf'.1
  omega

theorem even_maximum (t s : ℕ) (hs : s ≤ t) :
    maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s) = 4*t+3*s := by
  apply le_antisymm
  · have h := maximum_doubled_upper t (2*s)
    omega
  · obtain ⟨he,hz⟩ := witness_counts t s false hs (by simp)
    have hw : witness t s false ∈ admissibleCoreStates (arrow t) (2*s) := by
      classical
      simp only [admissibleCoreStates,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨witness_legal t s false, by simpa using hz.le⟩
    have h := coreExponent_le_max (arrow t) (outWeight t) (inWeight t) (2*s) _ hw
    simpa [he] using h

theorem odd_maximum (t s : ℕ) (hs : s < t) :
    maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1) = 4*t+3*s+1 := by
  apply le_antisymm
  · have h := maximum_doubled_upper t (2*s+1)
    omega
  · obtain ⟨he,hz⟩ := witness_counts t s true hs.le (by intro _; exact hs)
    have hw : witness t s true ∈ admissibleCoreStates (arrow t) (2*s+1) := by
      classical
      simp only [admissibleCoreStates,Finset.mem_filter,Finset.mem_univ,true_and]
      exact ⟨witness_legal t s true, by simpa using hz.le⟩
    have h := coreExponent_le_max (arrow t) (outWeight t) (inWeight t) (2*s+1) _ hw
    simpa [he] using h

theorem weight_sum (t : ℕ) : (∑ v : Core t, (outWeight t v+inWeight t v)) = 7*t := by
  simp [Fintype.sum_prod_type, Fin.sum_univ_succ, outWeight, inWeight, Nat.mul_comm]

theorem saturated_maximum (t r : ℕ) (hr : 2 * t ≤ r) :
    maxCoreExponent (arrow t) (outWeight t) (inWeight t) r = 7*t := by
  have hu := maxCoreExponent_le_total (arrow t) (outWeight t) (inWeight t) r
  rw [weight_sum] at hu
  have hl := maxCoreExponent_mono (arrow t) (outWeight t) (inWeight t) hr
  rw [even_maximum t t le_rfl] at hl
  omega

theorem gap_one (t s : ℕ) (hs : s < t) :
    maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1-1) +
      maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1+1) =
      2*maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1)+1 := by
  have hlo : 2*s+1-1 = 2*s := by omega
  have hhi : 2*s+1+1 = 2*(s+1) := by omega
  rw [hlo,hhi,even_maximum t s hs.le,even_maximum t (s+1) (by omega),odd_maximum t s hs]
  omega


theorem maximum_formula (t r : ℕ) :
    maxCoreExponent (arrow t) (outWeight t) (inWeight t) r =
      min (7*t) (4*t+3*r/2) := by
  by_cases hr : r ≤ 2*t
  · have hs : r/2 ≤ t := by omega
    by_cases he : r%2 = 0
    · have heq : r = 2*(r/2) := by omega
      rw [heq,even_maximum t (r/2) hs]
      omega
    · have heq : r = 2*(r/2)+1 := by omega
      have hs' : r/2 < t := by omega
      rw [heq,odd_maximum t (r/2) hs']
      omega
  · rw [saturated_maximum t r (by omega)]
    symm
    apply Nat.min_eq_left
    omega

end FormalProof.Research003.RS42Simultaneous
