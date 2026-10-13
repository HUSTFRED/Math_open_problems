module

public import FormalProof.Research003.RS42FixedKTree
public import FormalProof.Research003.RS42FixedKRatio
public import FormalProof.Research003.RS42FixedKSize
public import FormalProof.Research003.RS42FixedKCoreClose
public import FormalProof.Research003.RS42FixedKMatchingNumber

set_option linter.style.header false
set_option linter.hashCommand false

/-! Full fixed-k statements for the actual parameterized tree and its independent sets. -/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90
open Filter
open scoped Topology

noncomputable def indepCount (q p j : ℕ) : ℕ :=
  Nat.card {s : Finset (Vertex (Label q p)) // (graph q p).IsNIndepSet j s}

theorem indepCount_eq_coefficient (q p j : ℕ) :
    indepCount q p j = coefficient (graph q p) j :=
  Nat.card_congr (mathlibCoefficientEquiv q p j)

theorem strict_failure_of_three_bounds (q p : ℕ) (hq : 2 ≤ q)
    (hp : threshold q ≤ p)
    (hmid : coefficient (graph q p) (m q p - (q - 1)) ≤
      (m q p).choose (q - 1) * (2 ^ q + 1) * (2 ^ p) ^ (3 * q - 1))
    (hlo : (2 ^ p) ^ (3 * q - 2) ≤ coefficient (graph q p) (m q p - (q - 2)))
    (hhi : (2 ^ p) ^ (3 * q + 1) ≤ coefficient (graph q p) (m q p - q)) :
    coefficient (graph q p) (m q p - (q - 1)) ^ 2 <
      coefficient (graph q p) (m q p - q) *
        coefficient (graph q p) (m q p - (q - 2)) := by
  have hratio := (actualRatio_le_envelope_of_bounds q p hq hmid hlo hhi).trans_lt
    (envelope_lt_one q p hq hp)
  have hc (r : ℕ) : (0 : ℝ) < coefficient (graph q p) (m q p - r) := by
    exact_mod_cast coefficient_pos_of_le q p (m q p - r) (Nat.sub_le _ _)
  unfold actualRatio at hratio
  have hreal := (div_lt_one (mul_pos (hc (q - 2)) (hc q))).mp hratio
  rw [mul_comm] at hreal
  exact_mod_cast hreal

theorem actualRatio_le_envelope (q p : ℕ) (hq : 2 ≤ q) :
    actualRatio q p ≤ envelope q p := by
  obtain ⟨hm, hl, hh⟩ := three_coefficient_bounds q p hq
  exact actualRatio_le_envelope_of_bounds q p hq hm hl hh

theorem actualRatio_geometric (q p : ℕ) (hq : 2 ≤ q) (hp : threshold q ≤ p) :
    0 < actualRatio q p ∧ actualRatio q p ≤
      (1 / (2 : ℝ) ^ (16 * q * logThreshold q)) * (2 / 3 : ℝ) ^ (p - threshold q) :=
  ⟨actualRatio_pos q p, (actualRatio_le_envelope q p hq).trans
    (envelope_geometric q p hq hp)⟩

theorem actualRatio_tendsto_zero (q : ℕ) (hq : 2 ≤ q) :
    Tendsto (actualRatio q) atTop (𝓝 (0 : ℝ)) :=
  actualRatio_tendsto_zero_of_eventual_bound q hq
    (fun p _ => actualRatio_le_envelope q p hq)

theorem fixed_k_strict_failure (k p : ℕ) (hk : 1 ≤ k)
    (hp : threshold (k + 1) ≤ p) :
    indepCount (k + 1) p (m (k + 1) p - k) ^ 2 <
      indepCount (k + 1) p (m (k + 1) p - k - 1) *
        indepCount (k + 1) p (m (k + 1) p - k + 1) := by
  have hq : 2 ≤ k + 1 := by omega
  have hkm : k + 1 ≤ m (k + 1) p := by unfold m; omega
  obtain ⟨hm, hl, hh⟩ := three_coefficient_bounds (k + 1) p hq
  have h := strict_failure_of_three_bounds (k + 1) p hq hp hm hl hh
  have hi : m (k + 1) p - (k + 1 - 2) = m (k + 1) p - k + 1 := by omega
  have hj : m (k + 1) p - (k + 1) = m (k + 1) p - k - 1 := by omega
  simpa only [indepCount_eq_coefficient, Nat.add_sub_cancel, hi, hj] using h

/-- Every fixed positive k, and every p at or beyond the explicit threshold,
gives an actual finite tree with matching and independence number m and a
strict failure at the internal index m-k. No counting estimate is a premise. -/
theorem fixed_k_counterexample (k p : ℕ) (hk : 1 ≤ k)
    (hp : threshold (k + 1) ≤ p) :
    (graph (k + 1) p).IsTree ∧
    (matching (k + 1) p).IsPerfectMatching ∧
    Fintype.card (Vertex (Label (k + 1) p)) = 2 * m (k + 1) p ∧
    (graph (k + 1) p).indepNum = m (k + 1) p ∧
    matchingNumber (k + 1) p = m (k + 1) p ∧
    (1 ≤ m (k + 1) p - k ∧ m (k + 1) p - k < m (k + 1) p) ∧
    indepCount (k + 1) p (m (k + 1) p - k) ^ 2 <
      indepCount (k + 1) p (m (k + 1) p - k - 1) *
        indepCount (k + 1) p (m (k + 1) p - k + 1) := by
  have hi := interior_index (k + 1) p (by omega : 2 ≤ k + 1)
  refine ⟨graph_isTree _ _, matching_isPerfectMatching _ _, vertex_card _ _,
    graph_indepNum _ _, graph_matchingNumber _ _, ?_, fixed_k_strict_failure k p hk hp⟩
  simpa only [Nat.add_sub_cancel, labelCount, m] using hi

theorem fixed_k_initial_size (k : ℕ) (hk : 1 ≤ k) :
    Fintype.card (Vertex (Label (k + 1) (threshold (k + 1)))) ≤
      258 * (k + 1) ^ 2 * logThreshold (k + 1) ∧
    (Fintype.card (Vertex (Label (k + 1) (threshold (k + 1)))) : ℝ) ≤
      2064 * (k : ℝ) ^ 2 * Real.logb 2 ((k : ℝ) + 2) := by
  rw [vertex_card]
  exact ⟨vertexCount_threshold_le (k + 1) (by omega),
    vertexCount_threshold_log_bound k hk⟩

theorem actualRatio_eq_indepCount (k p : ℕ) (hk : 1 ≤ k) :
    actualRatio (k + 1) p =
      (indepCount (k + 1) p (m (k + 1) p - k) : ℝ) ^ 2 /
        ((indepCount (k + 1) p (m (k + 1) p - k - 1) : ℝ) *
          indepCount (k + 1) p (m (k + 1) p - k + 1)) := by
  have hkm : k + 1 ≤ m (k + 1) p := by unfold m; omega
  have hi : m (k + 1) p - (k + 1 - 2) = m (k + 1) p - k + 1 := by omega
  have hj : m (k + 1) p - (k + 1) = m (k + 1) p - k - 1 := by omega
  simp only [actualRatio, indepCount_eq_coefficient, Nat.add_sub_cancel, hi, hj,
    mul_comm]

/-- Alignment with the original RS42 index and independence-number bound. -/
theorem fixed_k_rs42_alignment (k p : ℕ) (hk : 1 ≤ k) :
    (Fintype.card (Vertex (Label (k + 1) p))) / 2 = m (k + 1) p ∧
    (m (k + 1) p - k) + k = m (k + 1) p ∧
    ¬ (m (k + 1) p + k + 1 ≤ (graph (k + 1) p).indepNum) := by
  have hm : k ≤ m (k + 1) p := by unfold m; omega
  rw [vertex_card, graph_indepNum]
  omega


end FormalProof.Research003.RS42FixedK
