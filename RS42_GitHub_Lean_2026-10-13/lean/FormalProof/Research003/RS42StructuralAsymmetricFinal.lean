module

public import FormalProof.Research003.RS42StructuralAsymmetric
public import FormalProof.Research003.RS42StructuralConclusion
public import FormalProof.Research003.RS42StructuralTree
public import Mathlib.Combinatorics.SimpleGraph.Star

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

/-!
The complete asymmetric inward-star application, connected
to the actual general Structural graph and mathlib independent-set counts.
Only q ≥ 2, incoming weights ≥ 2, and the explicit scale threshold are inputs.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural.Asymmetric

open RS42Counterexample90 (Vertex)
open Filter
open scoped BigOperators Topology

def coreGraph (q : ℕ) : SimpleGraph (Core q) :=
  SimpleGraph.starGraph (Sum.inr ())

theorem coreGraph_isTree (q : ℕ) : (coreGraph q).IsTree :=
  SimpleGraph.isTree_starGraph (Sum.inr ())

theorem coreGraph_cover (q : ℕ) (v w : Core q) :
    (coreGraph q).Adj v w ↔ starArrow q v w ∨ starArrow q w v := by
  rcases v with i | ⟨⟩ <;> rcases w with j | ⟨⟩ <;>
    simp [coreGraph, starArrow]

theorem starArrow_asymm (q : ℕ) (v w : Core q) :
    starArrow q v w → ¬ starArrow q w v := by
  rcases v with i | ⟨⟩ <;> rcases w with j | ⟨⟩ <;> simp [starArrow]

@[simp] theorem core_card (q : ℕ) : Fintype.card (Core q) = q + 1 := by
  simp [Core]

theorem totalMultiplicity_eq {q : ℕ} (weights : Fin q → ℕ) :
    totalMultiplicity (outMultiplicity q) (inMultiplicity weights) =
      totalIncoming weights + q + 1 := total_mass weights

theorem totalMultiplicity_pos {q : ℕ} (weights : Fin q → ℕ) :
    1 ≤ totalMultiplicity (outMultiplicity q) (inMultiplicity weights) := by
  rw [totalMultiplicity_eq]
  omega

def labelCount (q p : ℕ) (weights : Fin q → ℕ) : ℕ :=
  q + 1 + p * (totalIncoming weights + q + 1)

theorem label_card (q p : ℕ) (weights : Fin q → ℕ) :
    Fintype.card (StructuralLabel (outMultiplicity q) (inMultiplicity weights) p) =
      labelCount q p weights := by
  rw [structural_label_card, core_card, total_mass]
  rfl

def threshold (q : ℕ) (weights : Fin q → ℕ) : ℕ :=
  structuralThreshold (q + 1) (totalIncoming weights + q + 1) (q - 1)

/-- This is the same explicit integer threshold as in the general theorem. -/
theorem threshold_explicit (q : ℕ) (weights : Fin q → ℕ) :
    threshold q weights = 64 *
      (q + 1 + (q - 1) + structuralLog (q + 1) (totalIncoming weights + q + 1) + 1) ^ 2 :=
  rfl

theorem computed_gap_one (q : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) :
    structuralGap (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 1) = 1 := by
  have hlo : q - 1 - 1 = q - 2 := by omega
  have hhi : q - 1 + 1 = q := by omega
  unfold structuralGap
  rw [hlo, hhi, exponent_gap_one q hq weights hw]
  omega

theorem second_difference_pos (q : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) :
    2 * maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 1) <
      maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 1 - 1) +
        maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 1 + 1) := by
  have h := computed_gap_one q hq weights hw
  unfold structuralGap at h
  omega

theorem graph_isTree (q p : ℕ) (weights : Fin q → ℕ) :
    (graph q p weights).IsTree :=
  structuralGraph_isTree (coreGraph q) (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) p (coreGraph_isTree q) (coreGraph_cover q) (starArrow_asymm q)

noncomputable def displayedMatching (q p : ℕ) (weights : Fin q → ℕ) :
    (graph q p weights).Subgraph :=
  splitMatching (structuralArrow (starArrow q) (outMultiplicity q) (inMultiplicity weights) p)

theorem displayedMatching_isPerfect (q p : ℕ) (weights : Fin q → ℕ) :
    (displayedMatching q p weights).IsPerfectMatching :=
  structural_matching_isPerfectMatching (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) p

theorem graph_indepNum (q p : ℕ) (weights : Fin q → ℕ) :
    (graph q p weights).indepNum = labelCount q p weights := by
  exact (structural_indepNum (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) p).trans (label_card q p weights)

theorem graph_matchingNumber (q p : ℕ) (weights : Fin q → ℕ) :
    splitMatchingNumber
      (structuralArrow (starArrow q) (outMultiplicity q) (inMultiplicity weights) p) =
        labelCount q p weights := by
  exact (structural_matchingNumber (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) p).trans (label_card q p weights)

theorem graph_vertex_card (q p : ℕ) (weights : Fin q → ℕ) :
    Fintype.card (Vertex (StructuralLabel (outMultiplicity q) (inMultiplicity weights) p)) =
      2 * labelCount q p weights := by
  rw [split_vertex_card
    (structuralArrow (starArrow q) (outMultiplicity q) (inMultiplicity weights) p), label_card]

private theorem threshold_transfer (q p : ℕ) (weights : Fin q → ℕ)
    (hp : threshold q weights ≤ p) :
    structuralThreshold (Fintype.card (Core q))
      (totalMultiplicity (outMultiplicity q) (inMultiplicity weights)) (q - 1) ≤ p := by
  simpa only [core_card, totalMultiplicity_eq, threshold] using hp

/-- Actual coefficient failure at alpha-(q-1), for every integer scale at or
above the explicitly computed threshold, with all core estimates discharged. -/
theorem strict_failure (q p : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) (hp : threshold q weights ≤ p) :
    let j := labelCount q p weights - (q - 1)
    1 ≤ j ∧ j < labelCount q p weights ∧
      count q p weights j ^ 2 < count q p weights (j - 1) * count q p weights (j + 1) := by
  have h := structural_strict_failure (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) p (q - 1) (by omega) (totalMultiplicity_pos weights)
    (second_difference_pos q hq weights hw) (threshold_transfer q p weights hp)
  simpa only [label_card, count] using h

noncomputable def ratio (q p : ℕ) (weights : Fin q → ℕ) : ℝ :=
  structuralRatio (starArrow q) (outMultiplicity q) (inMultiplicity weights) p (q - 1)

theorem ratio_geometric (q p : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) (hp : threshold q weights ≤ p) :
    ratio q p weights ≤
      (1 / (2 : ℝ) ^ (44 * structuralN (q + 1) (totalIncoming weights + q + 1) (q - 1) ^ 2)) *
        (2 / 3 : ℝ) ^ (p - threshold q weights) := by
  have h := structuralRatio_geometric (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) p (q - 1) (by omega) (totalMultiplicity_pos weights)
    (second_difference_pos q hq weights hw) (threshold_transfer q p weights hp)
  simpa only [core_card, totalMultiplicity_eq, threshold, ratio] using h

theorem ratio_tendsto_zero (q : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) :
    Tendsto (fun p : ℕ => ratio q p weights) atTop (𝓝 (0 : ℝ)) :=
  structuralRatio_tendsto_zero (starArrow q) (outMultiplicity q)
    (inMultiplicity weights) (q - 1) (by omega) (totalMultiplicity_pos weights)
    (second_difference_pos q hq weights hw)

/-- The asymmetric application in a single statement. All graph properties
and coefficient bounds are proved for the explicitly constructed true graph. -/
theorem asymmetric_counterexample (q p : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) (hp : threshold q weights ≤ p) :
    (graph q p weights).IsTree ∧
      (displayedMatching q p weights).IsPerfectMatching ∧
      (graph q p weights).indepNum = labelCount q p weights ∧
      splitMatchingNumber
        (structuralArrow (starArrow q) (outMultiplicity q) (inMultiplicity weights) p) =
          labelCount q p weights ∧
      Fintype.card (Vertex (StructuralLabel (outMultiplicity q) (inMultiplicity weights) p)) =
        2 * labelCount q p weights ∧
      (let j := labelCount q p weights - (q - 1)
       1 ≤ j ∧ j < labelCount q p weights ∧
        count q p weights j ^ 2 < count q p weights (j - 1) * count q p weights (j + 1)) :=
  ⟨graph_isTree q p weights, displayedMatching_isPerfect q p weights,
    graph_indepNum q p weights, graph_matchingNumber q p weights,
    graph_vertex_card q p weights, strict_failure q p hq weights hw hp⟩


end FormalProof.Research003.RS42Structural.Asymmetric
