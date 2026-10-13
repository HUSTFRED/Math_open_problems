module
public import FormalProof.Research003.RS42StructuralConclusion
public import FormalProof.Research003.RS42StructuralTree
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Structural
open RS42Counterexample90 (Vertex)
open scoped BigOperators Topology
open Filter
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Complete structural sufficient condition. All premises concern only the
finite oriented core, its nonnegative integer attachment data, and the explicit
scale threshold. No graph coefficient estimate is an input. -/
theorem structural_counterexample (G : SimpleGraph V) (R : V → V → Prop)
    (a b : V → ℕ) (k p : ℕ) (hG : G.IsTree)
    (hcover : ∀ v w, G.Adj v w ↔ R v w ∨ R w v)
    (hasymm : ∀ v w, R v w → ¬ R w v)
    (hk : 1 ≤ k) (hW : 1 ≤ totalMultiplicity a b)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1))
    (hp : structuralThreshold (Fintype.card V) (totalMultiplicity a b) k ≤ p) :
    let m := Fintype.card V + p * totalMultiplicity a b
    (structuralGraph R a b p).IsTree ∧
    (splitMatching (structuralArrow R a b p)).IsPerfectMatching ∧
    Fintype.card (Vertex (StructuralLabel a b p)) = 2 * m ∧
    (structuralGraph R a b p).indepNum = m ∧
    splitMatchingNumber (structuralArrow R a b p) = m ∧
    (∀ j ≤ m, 0 < structuralIndepCount R a b p j) ∧
    (1 ≤ m - k ∧ m - k < m) ∧
    structuralIndepCount R a b p (m - k) ^ 2 <
      structuralIndepCount R a b p (m - k - 1) *
        structuralIndepCount R a b p (m - k + 1) := by
  have hm : Fintype.card (StructuralLabel a b p) =
      Fintype.card V + p * totalMultiplicity a b := structural_label_card a b p
  have hi := structural_strict_failure R a b p k hk hW hgap hp
  dsimp only at hi ⊢
  rw [hm] at hi
  refine ⟨structuralGraph_isTree G R a b p hG hcover hasymm,
    structural_matching_isPerfectMatching R a b p,
    structural_vertex_card R a b p, ?_, ?_, ?_, ⟨hi.1, hi.2.1⟩, hi.2.2⟩
  · exact (structural_indepNum R a b p).trans hm
  · exact (structural_matchingNumber R a b p).trans hm
  · intro j hj
    have hjm : j ≤ Fintype.card (StructuralLabel a b p) := by omega
    have hpos := structuralS_pos R a b p (Fintype.card (StructuralLabel a b p) - j)
      (Nat.sub_le _ _)
    simpa only [structuralS, Nat.sub_sub_self hjm] using hpos

/-- A positive core gap gives both the explicit geometric envelope and convergence
of the actual three-term ratio along all natural scales. -/
theorem structural_quantitative_conclusion (R : V → V → Prop) (a b : V → ℕ)
    (k : ℕ) (hk : 1 ≤ k) (hW : 1 ≤ totalMultiplicity a b)
    (hgap : 2 * maxCoreExponent R a b k <
      maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1)) :
    (∀ p, structuralThreshold (Fintype.card V) (totalMultiplicity a b) k ≤ p →
      0 < structuralRatio R a b p k ∧
      structuralRatio R a b p k ≤
        (1 / (2 : ℝ) ^ (44 * structuralN (Fintype.card V) (totalMultiplicity a b) k ^ 2)) *
          (2 / 3 : ℝ) ^ (p - structuralThreshold (Fintype.card V) (totalMultiplicity a b) k) ∧
      structuralRatio R a b p k < 1) ∧
    Tendsto (fun p : ℕ => structuralRatio R a b p k) atTop (𝓝 (0 : ℝ)) := by
  refine ⟨?_, structuralRatio_tendsto_zero R a b k hk hW hgap⟩
  intro p hp
  exact ⟨structuralRatio_pos R a b p k (structural_indices_valid a b k p hk hW hp),
    structuralRatio_geometric R a b p k hk hW hgap hp,
    structuralRatio_lt_one R a b p k hk hW hgap hp⟩

end FormalProof.Research003.RS42Structural
