module

public import FormalProof.Research003.RS42StructuralCounts
public import FormalProof.Research003.RS42FixedKMatchingNumber

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-!
Graph-theoretic realization of the finite oriented-core construction.  The
tree argument counts genuine edges and lifts genuine walks.  Matching and
independence assertions concern the actual matching-split graph.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural

open RS42Counterexample90
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev ArrowSet (R : V → V → Prop) := {e : V × V // R e.1 e.2}

theorem split_vertex_card (_R : V → V → Prop) :
    Fintype.card (Vertex V) = 2 * Fintype.card V := by
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin, Nat.mul_comm]

theorem split_pair_reachable (R : V → V → Prop) (v : V) (b c : Fin 2) :
    (splitGraph R).Reachable (v, b) (v, c) := by
  by_cases h : b = c
  · subst c
    exact SimpleGraph.Reachable.refl _
  · exact (show (splitGraph R).Adj (v, b) (v, c) from Or.inl ⟨rfl, h⟩).reachable

theorem split_arrow_reachable (R : V → V → Prop) {v w : V} (h : R v w) :
    (splitGraph R).Reachable (v, 0) (w, 0) := by
  have he : (splitGraph R).Adj (v, 0) (w, 1) := Or.inr (Or.inl ⟨rfl, rfl, h⟩)
  exact he.reachable.trans (split_pair_reachable R w 1 0)

private theorem reachable_of_lift {A B : Type*} (G : SimpleGraph A)
    (H : SimpleGraph B) (f : A → B)
    (hlift : ∀ {v w}, G.Adj v w → H.Reachable (f v) (f w))
    {v w : A} (h : G.Reachable v w) : H.Reachable (f v) (f w) := by
  rcases h with ⟨walk⟩
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hadj walk ih => exact (hlift hadj).trans ih

theorem split_connected (G : SimpleGraph V) (R : V → V → Prop)
    (hc : G.Connected) (hcover : ∀ v w, G.Adj v w ↔ R v w ∨ R w v) :
    (splitGraph R).Connected := by
  obtain ⟨r, hr⟩ := (SimpleGraph.connected_iff_exists_forall_reachable G).mp hc
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(r, 0), ?_⟩
  rintro ⟨v, b⟩
  have hreach : (splitGraph R).Reachable (r, 0) (v, 0) := by
    apply reachable_of_lift G (splitGraph R) (fun u => (u, 0)) _ (hr v)
    intro u w h
    rcases (hcover u w).mp h with h | h
    · exact split_arrow_reachable R h
    · exact (split_arrow_reachable R h).symm
  exact hreach.trans (split_pair_reachable R v 0 b)

theorem arrow_card_le_edges (G : SimpleGraph V) (R : V → V → Prop)
    (hcover : ∀ v w, G.Adj v w ↔ R v w ∨ R w v)
    (hasymm : ∀ v w, R v w → ¬ R w v) :
    Nat.card (ArrowSet R) ≤ Nat.card G.edgeSet := by
  let f : ArrowSet R → G.edgeSet := fun e =>
    ⟨s(e.1.1, e.1.2), (SimpleGraph.mem_edgeSet G).mpr
      ((hcover _ _).mpr (Or.inl e.2))⟩
  apply Nat.card_le_card_of_injective f
  intro e f' h
  have he : s(e.1.1, e.1.2) = s(f'.1.1, f'.1.2) := congrArg Subtype.val h
  rcases Sym2.eq_iff.mp he with he | he
  · exact Subtype.ext (Prod.ext he.1 he.2)
  · have hr : R e.1.2 e.1.1 := by
      rw [he.2, he.1]
      exact f'.2
    exact (hasymm _ _ e.2 hr).elim

theorem split_edges_card_le (R : V → V → Prop) :
    Nat.card (splitGraph R).edgeSet ≤ Nat.card V + Nat.card (ArrowSet R) := by
  classical
  let edgeOf : V ⊕ ArrowSet R → (splitGraph R).edgeSet
    | Sum.inl v => ⟨s((v, 0), (v, 1)), (SimpleGraph.mem_edgeSet _).mpr
        (Or.inl ⟨rfl, show (0 : Fin 2) ≠ 1 by decide⟩)⟩
    | Sum.inr e => ⟨s((e.1.1, 0), (e.1.2, 1)), (SimpleGraph.mem_edgeSet _).mpr
        (Or.inr (Or.inl ⟨rfl, rfl, e.2⟩))⟩
  have hs : Function.Surjective edgeOf := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf v w =>
      rcases v with ⟨v, b⟩
      rcases w with ⟨w, c⟩
      have ha := (SimpleGraph.mem_edgeSet (splitGraph R)).mp he
      change (v = w ∧ b ≠ c) ∨ (b = 0 ∧ c = 1 ∧ R v w) ∨
        (b = 1 ∧ c = 0 ∧ R w v) at ha
      rcases ha with ⟨hvw, hbc⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
      · subst w
        fin_cases b <;> fin_cases c
        · exact (hbc rfl).elim
        · exact ⟨Sum.inl v, Subtype.ext rfl⟩
        · exact ⟨Sum.inl v, Subtype.ext Sym2.eq_swap⟩
        · exact (hbc rfl).elim
      · exact ⟨Sum.inr ⟨(v, w), h⟩, Subtype.ext rfl⟩
      · exact ⟨Sum.inr ⟨(w, v), h⟩, Subtype.ext Sym2.eq_swap⟩
  have h := Nat.card_le_card_of_surjective edgeOf hs
  simpa only [Nat.card_sum] using h

theorem split_isTree_of_connected_arrow_card (R : V → V → Prop)
    (hc : (splitGraph R).Connected)
    (hcard : Nat.card (ArrowSet R) + 1 ≤ Nat.card V) :
    (splitGraph R).IsTree := by
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  have hupper := split_edges_card_le R
  have hlower := hc.card_vert_le_card_edgeSet_add_one
  have hv : Nat.card (Vertex V) = 2 * Nat.card V := by
    simp only [Nat.card_eq_fintype_card, split_vertex_card R]
  omega

/-- Splitting each vertex of an arbitrarily oriented finite tree into its
matching pair preserves treehood. -/
theorem splitGraph_isTree (G : SimpleGraph V) (R : V → V → Prop)
    (hG : G.IsTree) (hcover : ∀ v w, G.Adj v w ↔ R v w ∨ R w v)
    (hasymm : ∀ v w, R v w → ¬ R w v) :
    (splitGraph R).IsTree := by
  apply split_isTree_of_connected_arrow_card R (split_connected G R hG.connected hcover)
  have ha := arrow_card_le_edges G R hcover hasymm
  have hg := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
  omega

theorem structural_arrow_card_le (R : V → V → Prop) (a b : V → ℕ) (p : ℕ) :
    Nat.card (ArrowSet (structuralArrow R a b p)) ≤
      Nat.card (ArrowSet R) + Nat.card (StructuralLeaf a b p) := by
  classical
  let arrowOf : ArrowSet R ⊕ StructuralLeaf a b p → ArrowSet (structuralArrow R a b p)
    | Sum.inl e => ⟨(Sum.inl e.1.1, Sum.inl e.1.2), e.2⟩
    | Sum.inr ⟨v, Sum.inl j⟩ =>
        ⟨(Sum.inl v, Sum.inr ⟨v, Sum.inl j⟩), rfl⟩
    | Sum.inr ⟨v, Sum.inr j⟩ =>
        ⟨(Sum.inr ⟨v, Sum.inr j⟩, Sum.inl v), rfl⟩
  have hs : Function.Surjective arrowOf := by
    rintro ⟨⟨x, y⟩, h⟩
    rcases x with v | ⟨v, j⟩
    · rcases y with w | ⟨w, l⟩
      · exact ⟨Sum.inl ⟨(v, w), h⟩, Subtype.ext rfl⟩
      · rcases l with l | l
        · change v = w at h
          subst w
          exact ⟨Sum.inr ⟨v, Sum.inl l⟩, Subtype.ext rfl⟩
        · exact h.elim
    · rcases j with j | j
      · rcases y with w | ⟨w, l⟩
        · exact h.elim
        · rcases l <;> exact h.elim
      · rcases y with w | ⟨w, l⟩
        · change v = w at h
          subst w
          exact ⟨Sum.inr ⟨v, Sum.inr j⟩, Subtype.ext rfl⟩
        · rcases l <;> exact h.elim
  have h := Nat.card_le_card_of_surjective arrowOf hs
  simpa only [Nat.card_sum] using h

theorem structural_connected (G : SimpleGraph V) (R : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (hc : G.Connected)
    (hcover : ∀ v w, G.Adj v w ↔ R v w ∨ R w v) :
    (structuralGraph R a b p).Connected := by
  let S := structuralArrow R a b p
  obtain ⟨r, hr⟩ := (SimpleGraph.connected_iff_exists_forall_reachable G).mp hc
  have hcore (v : V) :
      (splitGraph S).Reachable (Sum.inl r, 0) (Sum.inl v, 0) := by
    apply reachable_of_lift G (splitGraph S) (fun u => (Sum.inl u, 0)) _ (hr v)
    intro u w h
    rcases (hcover u w).mp h with h | h
    · exact split_arrow_reachable S (show S (Sum.inl u) (Sum.inl w) from h)
    · exact (split_arrow_reachable S (show S (Sum.inl w) (Sum.inl u) from h)).symm
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨(Sum.inl r, 0), ?_⟩
  rintro ⟨v, c⟩
  change (splitGraph S).Reachable (Sum.inl r, 0) (v, c)
  apply SimpleGraph.Reachable.trans _ (split_pair_reachable S v 0 c)
  rcases v with v | ⟨v, j⟩
  · exact hcore v
  · rcases j with j | j
    · exact (hcore v).trans (split_arrow_reachable S (show
        S (Sum.inl v) (Sum.inr ⟨v, Sum.inl j⟩) from rfl))
    · exact (hcore v).trans (split_arrow_reachable S (show
        S (Sum.inr ⟨v, Sum.inr j⟩) (Sum.inl v) from rfl)).symm

/-- The actual weighted pendant expansion and matching split is a tree for
every natural scale, including zero weights and scale zero. -/
theorem structuralGraph_isTree (G : SimpleGraph V) (R : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (hG : G.IsTree)
    (hcover : ∀ v w, G.Adj v w ↔ R v w ∨ R w v)
    (hasymm : ∀ v w, R v w → ¬ R w v) :
    (structuralGraph R a b p).IsTree := by
  apply split_isTree_of_connected_arrow_card _
    (structural_connected G R a b p hG.connected hcover)
  have ha := structural_arrow_card_le R a b p
  have hc := arrow_card_le_edges G R hcover hasymm
  have ht := (SimpleGraph.isTree_iff_connected_and_card.mp hG).2
  have hv : Nat.card (StructuralLabel a b p) =
      Nat.card V + Nat.card (StructuralLeaf a b p) := Nat.card_sum
  omega

def splitMate (v : Vertex V) : Vertex V := (v.1, if v.2 = 0 then 1 else 0)

theorem splitMate_involutive : Function.Involutive (@splitMate V) := by
  rintro ⟨v, c⟩
  fin_cases c <;> simp [splitMate]

theorem splitMate_adjacent (R : V → V → Prop) (v : Vertex V) :
    (splitGraph R).Adj v (splitMate v) := by
  rcases v with ⟨v, c⟩
  fin_cases c <;> simp [splitMate, splitGraph]

def splitMatching (R : V → V → Prop) : (splitGraph R).Subgraph where
  verts := Set.univ
  Adj v w := splitMate v = w
  adj_sub := by
    intro v w h
    rw [← h]
    exact splitMate_adjacent R v
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    intro v w h
    rw [← h]
    exact splitMate_involutive v⟩

theorem splitMatching_isPerfectMatching (R : V → V → Prop) :
    (splitMatching R).IsPerfectMatching := by
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro v
  exact ⟨splitMate v, rfl, fun _ h => Eq.symm h⟩

def splitAllPlus : Finset (Vertex V) := selected (fun _ => some 0)

theorem splitAllPlus_independent (R : V → V → Prop) :
    Independent (splitGraph R) ((splitAllPlus : Finset (Vertex V)) : Set (Vertex V)) := by
  apply (selected_independent_iff R _).mpr
  intro i j _ h
  exact (by decide : some (0 : Fin 2) ≠ some 1) h.2

theorem splitAllPlus_card : (splitAllPlus : Finset (Vertex V)).card = Fintype.card V := by
  classical
  have he : (splitAllPlus : Finset (Vertex V)) =
      Finset.univ.image (fun i : V => (i, (0 : Fin 2))) := by
    ext v
    rcases v with ⟨i, b⟩
    simp [splitAllPlus, selected]
  rw [he, Finset.card_image_of_injective]
  · exact Finset.card_univ
  · intro i j h
    exact congrArg Prod.fst h

theorem splitAllPlus_isMaximumIndepSet (R : V → V → Prop) :
    (splitGraph R).IsMaximumIndepSet (splitAllPlus : Finset (Vertex V)) where
  isIndepSet := splitAllPlus_independent R
  maximum t ht := by
    rw [splitAllPlus_card]
    exact independent_card_le R t ht

theorem split_indepNum (R : V → V → Prop) :
    (splitGraph R).indepNum = Fintype.card V := by
  have h := (splitGraph R).maximumIndepSet_card_eq_indepNum splitAllPlus
    (splitAllPlus_isMaximumIndepSet R)
  rw [splitAllPlus_card] at h
  exact h.symm

theorem split_matchingSize_le (R : V → V → Prop) (M : (splitGraph R).Subgraph)
    (hM : M.IsMatching) : RS42FixedK.matchingSize M ≤ Fintype.card V := by
  have he := RS42FixedK.matching_twice_edges_card M hM
  have hv : Nat.card M.verts ≤ 2 * Fintype.card V := by
    have h := Nat.card_le_card_of_injective (Subtype.val : M.verts → Vertex V)
      Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, split_vertex_card R] using h
  omega

theorem split_matchingSize_displayed (R : V → V → Prop) :
    RS42FixedK.matchingSize (splitMatching R) = Fintype.card V := by
  classical
  have he := RS42FixedK.matching_twice_edges_card (splitMatching R)
    (splitMatching_isPerfectMatching R).1
  have hv : Nat.card (splitMatching R).verts = 2 * Fintype.card V := by
    have h := (splitMatching_isPerfectMatching R).2.card_verts
    simpa only [Set.toFinset_card, Nat.card_eq_fintype_card, split_vertex_card R] using h
  omega

def splitMatchingSizes (R : V → V → Prop) : Set ℕ :=
  {n | ∃ M : (splitGraph R).Subgraph, M.IsMatching ∧ RS42FixedK.matchingSize M = n}

noncomputable def splitMatchingNumber (R : V → V → Prop) : ℕ := sSup (splitMatchingSizes R)

theorem split_matchingNumber (R : V → V → Prop) :
    splitMatchingNumber R = Fintype.card V := by
  have hg : IsGreatest (splitMatchingSizes R) (Fintype.card V) := by
    refine ⟨⟨splitMatching R, (splitMatching_isPerfectMatching R).1,
      split_matchingSize_displayed R⟩, ?_⟩
    rintro n ⟨M, hM, rfl⟩
    exact split_matchingSize_le R M hM
  have hb : BddAbove (splitMatchingSizes R) := ⟨Fintype.card V, hg.2⟩
  apply le_antisymm
  · exact csSup_le ⟨Fintype.card V, hg.1⟩ hg.2
  · exact le_csSup hb hg.1

theorem structural_vertex_card (R : V → V → Prop) (a b : V → ℕ) (p : ℕ) :
    Fintype.card (Vertex (StructuralLabel a b p)) =
      2 * (Fintype.card V + p * ∑ v, (a v + b v)) := by
  rw [split_vertex_card (structuralArrow R a b p), structural_label_card]

theorem structural_indepNum (R : V → V → Prop) (a b : V → ℕ) (p : ℕ) :
    (structuralGraph R a b p).indepNum = Fintype.card (StructuralLabel a b p) :=
  split_indepNum (structuralArrow R a b p)

theorem structural_matchingNumber (R : V → V → Prop) (a b : V → ℕ) (p : ℕ) :
    splitMatchingNumber (structuralArrow R a b p) = Fintype.card (StructuralLabel a b p) :=
  split_matchingNumber (structuralArrow R a b p)

theorem structural_matching_isPerfectMatching (R : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) :
    (splitMatching (structuralArrow R a b p)).IsPerfectMatching :=
  splitMatching_isPerfectMatching (structuralArrow R a b p)


end FormalProof.Research003.RS42Structural
