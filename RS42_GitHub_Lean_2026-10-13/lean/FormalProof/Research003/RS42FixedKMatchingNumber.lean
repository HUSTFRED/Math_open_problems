module

public import FormalProof.Research003.RS42FixedKTree
public import Mathlib.Order.Lattice.Nat

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Matching number via actual mathlib subgraphs. Mathlib's matching predicates
are reused; the numerical supremum below is a project-local definition.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90 (Vertex)
open scoped BigOperators

/-- Number of actual edges in the simple graph carried by a subgraph. -/
noncomputable def matchingSize {V : Type*} {G : SimpleGraph V} (M : G.Subgraph) : ℕ :=
  Nat.card M.coe.edgeSet

theorem matching_twice_edges_card {V : Type*} [Finite V] {G : SimpleGraph V}
    (M : G.Subgraph) (hM : M.IsMatching) :
    2 * matchingSize M = Nat.card M.verts := by
  classical
  let : Fintype M.verts := Fintype.ofFinite _
  let : Fintype M.coe.edgeSet := Fintype.ofFinite _
  have hdeg := SimpleGraph.Subgraph.isMatching_iff_forall_degree.mp hM
  have hs := M.coe.sum_degrees_eq_twice_card_edges
  have hs' : Fintype.card M.verts = 2 * Fintype.card M.coe.edgeSet := by
    simpa [hdeg, SimpleGraph.edgeFinset_card] using hs
  simpa only [matchingSize, Nat.card_eq_fintype_card] using hs'.symm

theorem matchingSize_le (q p : ℕ) (M : (graph q p).Subgraph) (hM : M.IsMatching) :
    matchingSize M ≤ m q p := by
  have he := matching_twice_edges_card M hM
  have hv : Nat.card M.verts ≤ 2 * m q p := by
    have h := Nat.card_le_card_of_injective (Subtype.val : M.verts → Vertex (Label q p))
      Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, vertex_card] using h
  omega

theorem matchingSize_displayed (q p : ℕ) : matchingSize (matching q p) = m q p := by
  classical
  have he := matching_twice_edges_card (matching q p) (matching_isPerfectMatching q p).1
  have hv : Nat.card (matching q p).verts = 2 * m q p := by
    have h := (matching_isPerfectMatching q p).2.card_verts
    simpa only [Set.toFinset_card, Nat.card_eq_fintype_card, vertex_card] using h
  omega

/-- The set of sizes of genuine matching subgraphs of the parameterized graph. -/
def matchingSizes (q p : ℕ) : Set ℕ :=
  {n | ∃ M : (graph q p).Subgraph, M.IsMatching ∧ matchingSize M = n}

theorem m_mem_matchingSizes (q p : ℕ) : m q p ∈ matchingSizes q p :=
  ⟨matching q p, (matching_isPerfectMatching q p).1, matchingSize_displayed q p⟩

theorem matchingSizes_isGreatest (q p : ℕ) : IsGreatest (matchingSizes q p) (m q p) := by
  refine ⟨m_mem_matchingSizes q p, ?_⟩
  rintro n ⟨M, hM, rfl⟩
  exact matchingSize_le q p M hM

/-- Project-local numerical matching number: supremum of sizes of actual
mathlib matching subgraphs. The next theorem proves this maximum is attained. -/
noncomputable def matchingNumber (q p : ℕ) : ℕ := sSup (matchingSizes q p)

theorem graph_matchingNumber (q p : ℕ) : matchingNumber q p = m q p := by
  have hgreatest := matchingSizes_isGreatest q p
  have hb : BddAbove (matchingSizes q p) := ⟨m q p, hgreatest.2⟩
  apply le_antisymm
  · exact csSup_le ⟨m q p, hgreatest.1⟩ hgreatest.2
  · exact le_csSup hb hgreatest.1


end FormalProof.Research003.RS42FixedK
