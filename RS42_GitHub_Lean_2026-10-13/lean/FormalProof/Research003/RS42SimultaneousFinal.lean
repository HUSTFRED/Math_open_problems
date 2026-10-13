module
public import FormalProof.Research003.RS42SimultaneousJoint
public import FormalProof.Research003.RS42SimultaneousExponent
public import FormalProof.Research003.RS42SimultaneousTree
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.style.whitespace false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Simultaneous
open RS42Structural RS42Counterexample90
open scoped BigOperators Topology
open Filter

noncomputable def graph (t p : ℕ) := structuralGraph (arrow t) (outWeight t) (inWeight t) p
noncomputable def count (t p j : ℕ) := structuralIndepCount (arrow t) (outWeight t) (inWeight t) p j
def labelCount (t p : ℕ) := t*(3+7*p)
def threshold (t : ℕ) := 64*(5*t+structuralLog (3*t) (7*t))^2

theorem core_card (t : ℕ) : Fintype.card (Core t) = 3*t := by simp [Core, Nat.mul_comm]
theorem mass_eq (t : ℕ) : totalMultiplicity (outWeight t) (inWeight t) = 7*t := weight_sum t
theorem mass_pos (t : ℕ) (ht : 0 < t) : 1 ≤ totalMultiplicity (outWeight t) (inWeight t) := by
  rw [mass_eq]; omega
theorem label_card (t p : ℕ) :
    Fintype.card (StructuralLabel (outWeight t) (inWeight t) p) = labelCount t p := by
  rw [structural_label_card,core_card,weight_sum]
  unfold labelCount
  ring
theorem graph_indepNum (t p : ℕ) : (graph t p).indepNum = labelCount t p :=
  (structural_indepNum (arrow t) (outWeight t) (inWeight t) p).trans (label_card t p)

theorem threshold_at_last (t : ℕ) (ht : 0 < t) :
    structuralThreshold (3*t) (7*t) (2*t-1) = threshold t := by
  unfold structuralThreshold structuralN threshold
  have h : 3*t+(2*t-1)+structuralLog (3*t) (7*t)+1 =
      5*t+structuralLog (3*t) (7*t) := by omega
  rw [h]

theorem threshold_transfer (t p s : ℕ) (hs : s < t) (hp : threshold t ≤ p) :
    structuralThreshold (Fintype.card (Core t))
      (totalMultiplicity (outWeight t) (inWeight t)) (2*s+1) ≤ p := by
  rw [core_card,mass_eq]
  have h := threshold_mono (3*t) (7*t) (show 2*s+1 ≤ 2*t-1 by omega)
  rw [threshold_at_last t (by omega)] at h
  exact h.trans hp

theorem positive_gap (t s : ℕ) (hs : s < t) :
    2*maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1) <
      maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1-1) +
        maxCoreExponent (arrow t) (outWeight t) (inWeight t) (2*s+1+1) := by
  rw [gap_one t s hs]
  omega

theorem strict_failure (t p s : ℕ) (hs : s < t) (hp : threshold t ≤ p) :
    1 ≤ labelCount t p-(2*s+1) ∧ labelCount t p-(2*s+1) < labelCount t p ∧
      count t p (labelCount t p-(2*s+1))^2 <
        count t p (labelCount t p-(2*s+1)-1)*count t p (labelCount t p-(2*s+1)+1) := by
  have h := structural_strict_failure (arrow t) (outWeight t) (inWeight t) p
    (2*s+1) (by omega) (mass_pos t (by omega)) (positive_gap t s hs)
    (threshold_transfer t p s hs hp)
  simpa only [label_card,count] using h

/-- The graph is bound ONCE before quantifying the t failure positions.
All positive gaps are proved internally; only t and the scale threshold are premises. -/
theorem simultaneous_counterexample (t p : ℕ) (ht : 2 ≤ t) (hp : threshold t ≤ p) :
    let G := graph t p
    G.IsTree ∧
    (splitMatching (structuralArrow (arrow t) (outWeight t) (inWeight t) p)).IsPerfectMatching ∧
    Fintype.card (Vertex (StructuralLabel (outWeight t) (inWeight t) p)) = 2*labelCount t p ∧
    G.indepNum = labelCount t p ∧
    splitMatchingNumber (structuralArrow (arrow t) (outWeight t) (inWeight t) p) = labelCount t p ∧
    Function.Injective (fun s : Fin t => G.indepNum-(2*s.val+1)) ∧
    (∀ s : Fin t, let j := G.indepNum-(2*s.val+1)
      1 ≤ j ∧ j < G.indepNum ∧ count t p j^2 < count t p (j-1)*count t p (j+1)) := by
  dsimp only
  have tree := structuralGraph_isTree (coreGraph t) (arrow t) (outWeight t) (inWeight t)
    p (core_isTree t (by omega)) (fun _ _ => Iff.rfl) (arrow_asymm t)
  refine ⟨tree,structural_matching_isPerfectMatching _ _ _ _,?_,graph_indepNum t p,?_,?_,?_⟩
  · rw [split_vertex_card (structuralArrow (arrow t) (outWeight t) (inWeight t) p),label_card]
  · exact (structural_matchingNumber (arrow t) (outWeight t) (inWeight t) p).trans (label_card t p)
  · intro s u heq
    rw [graph_indepNum] at heq
    dsimp only at heq
    have hs := (strict_failure t p s.val s.isLt hp).1
    have hu := (strict_failure t p u.val u.isLt hp).1
    apply Fin.ext
    omega
  · intro s
    simpa only [graph_indepNum] using strict_failure t p s.val s.isLt hp

theorem real_count_definition (t p j : ℕ) : count t p j =
    Nat.card {s : Finset (Vertex (StructuralLabel (outWeight t) (inWeight t) p)) //
      (graph t p).IsNIndepSet j s} := rfl

theorem ratio_tendsto_zero (t s : ℕ) (hs : s < t) :
    Tendsto (fun p : ℕ => structuralRatio (arrow t) (outWeight t) (inWeight t) p (2*s+1))
      atTop (𝓝 (0 : ℝ)) :=
  structuralRatio_tendsto_zero (arrow t) (outWeight t) (inWeight t) (2*s+1)
    (by omega) (mass_pos t (by omega)) (positive_gap t s hs)

end FormalProof.Research003.RS42Simultaneous
