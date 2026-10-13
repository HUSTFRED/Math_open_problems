module

public import FormalProof.Research003.RS42FixedKBridge
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Matching
public meta import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

set_option linter.style.header false

/-!
The actual parameterized split graph is a tree and has an explicit perfect
matching.  The proofs are uniform in both natural parameters, including zero.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open FormalProof.Research003.RS42Counterexample90 (Vertex splitGraph)

private theorem tree_of_parent_data {V : Type*} [Finite V]
    (G : SimpleGraph V) (r : V) (parent : V → V) (rank : V → ℕ)
    (hdec : ∀ v, v ≠ r → rank (parent v) < rank v)
    (hadj : ∀ v w, G.Adj v w ↔
      (v ≠ r ∧ parent v = w) ∨ (w ≠ r ∧ parent w = v)) :
    G.IsTree := by
  classical
  let := Fintype.ofFinite V
  have hp (v : V) (hv : v ≠ r) : G.Adj v (parent v) :=
    (hadj v (parent v)).mpr (Or.inl ⟨hv, rfl⟩)
  have reach : ∀ v : V, G.Reachable v r := by
    intro v
    induction hn : rank v using Nat.strong_induction_on generalizing v with
    | h n ih =>
      by_cases hv : v = r
      · subst v
        exact SimpleGraph.Reachable.refl r
      · exact (hp v hv).reachable.trans
          (ih (rank (parent v)) (by simpa [hn] using hdec v hv) (parent v) rfl)
  have hc : G.Connected :=
    (SimpleGraph.connected_iff_exists_forall_reachable G).mpr
      ⟨r, fun v => (reach v).symm⟩
  let edgeOf : {v : V // v ≠ r} → G.edgeSet := fun v =>
    ⟨s(v.1, parent v.1), (SimpleGraph.mem_edgeSet G).mpr (hp v.1 v.2)⟩
  have hi : Function.Injective edgeOf := by
    intro v w he
    have he' : s(v.1, parent v.1) = s(w.1, parent w.1) := congrArg Subtype.val he
    rcases Sym2.eq_iff.mp he' with h | h
    · exact Subtype.ext h.1
    · have hv := hdec v.1 v.2
      have hw := hdec w.1 w.2
      rw [h.2, h.1] at hv
      omega
  have hs : Function.Surjective edgeOf := by
    rintro ⟨e, he⟩
    induction e using Sym2.inductionOn with
    | hf v w =>
      have ha : G.Adj v w := (SimpleGraph.mem_edgeSet G).mp he
      rcases (hadj v w).mp ha with h | h
      · refine ⟨⟨v, h.1⟩, Subtype.ext ?_⟩
        change s(v, parent v) = s(v, w)
        rw [h.2]
      · refine ⟨⟨w, h.1⟩, Subtype.ext ?_⟩
        change s(w, parent w) = s(v, w)
        rw [h.2, Sym2.eq_swap]
  have hequiv := Equiv.ofBijective edgeOf ⟨hi, hs⟩
  have hcard : Nat.card G.edgeSet = Fintype.card V - 1 := by
    rw [← Nat.card_congr hequiv, Nat.card_eq_fintype_card]
    simp
  apply SimpleGraph.isTree_iff_connected_and_card.mpr
  refine ⟨hc, ?_⟩
  rw [hcard, Nat.card_eq_fintype_card]
  have hpos : 0 < Fintype.card V := Fintype.card_pos_iff.mpr ⟨r⟩
  omega

def root (q p : ℕ) : Vertex (Label q p) := (z q p, 1)

def parent {q p : ℕ} (v : Vertex (Label q p)) : Vertex (Label q p) :=
  match v.1 with
  | Sum.inl (Sum.inl i) => if v.2 = 0 then root q p else (u i, 0)
  | Sum.inl (Sum.inr _) => root q p
  | Sum.inr (Sum.inl (i, j)) =>
      if v.2 = 0 then (outLeaf i j, 1) else (u i, 0)
  | Sum.inr (Sum.inr (Sum.inl (i, j))) =>
      if v.2 = 0 then (u i, 1) else (inLeaf i j, 0)
  | Sum.inr (Sum.inr (Sum.inr j)) =>
      if v.2 = 0 then (zLeaf j, 1) else (z q p, 0)

def rank {q p : ℕ} (v : Vertex (Label q p)) : ℕ :=
  match v.1 with
  | Sum.inl (Sum.inl _) => if v.2 = 0 then 1 else 2
  | Sum.inl (Sum.inr _) => if v.2 = 0 then 1 else 0
  | Sum.inr (Sum.inl _) => if v.2 = 0 then 3 else 2
  | Sum.inr (Sum.inr (Sum.inl _)) => if v.2 = 0 then 3 else 4
  | Sum.inr (Sum.inr (Sum.inr _)) => if v.2 = 0 then 3 else 2

theorem rank_parent_lt {q p : ℕ} (v : Vertex (Label q p))
    (hv : v ≠ root q p) : rank (parent v) < rank v := by
  rcases v with ⟨l, b⟩
  rcases l with ((i | ⟨⟩) | (⟨i, j⟩ | (⟨i, j⟩ | j))) <;>
    fin_cases b <;>
    simp [parent, rank, root, u, z, outLeaf, inLeaf, zLeaf] at hv ⊢

theorem parent_adj {q p : ℕ} (v : Vertex (Label q p))
    (hv : v ≠ root q p) : (graph q p).Adj v (parent v) := by
  rcases v with ⟨l, b⟩
  rcases l with ((i | ⟨⟩) | (⟨i, j⟩ | (⟨i, j⟩ | j))) <;>
    fin_cases b <;>
    simp [graph, splitGraph, parent, root, arrow, u, z, outLeaf, inLeaf, zLeaf]
      at hv ⊢

private theorem pair_parent {q p : ℕ} (l : Label q p) :
    ((l, (0 : Fin 2)) ≠ root q p ∧ parent (l, 0) = (l, 1)) ∨
      ((l, (1 : Fin 2)) ≠ root q p ∧ parent (l, 1) = (l, 0)) := by
  rcases l with ((i | ⟨⟩) | (⟨i, j⟩ | (⟨i, j⟩ | j))) <;>
    simp [parent, root, u, z, outLeaf, inLeaf, zLeaf]

private theorem arrow_parent {q p : ℕ} (v w : Label q p) (h : arrow q p v w) :
    ((v, (0 : Fin 2)) ≠ root q p ∧ parent (v, 0) = (w, 1)) ∨
      ((w, (1 : Fin 2)) ≠ root q p ∧ parent (w, 1) = (v, 0)) := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ <;>
    simp [parent, root, u, z, outLeaf, inLeaf, zLeaf]

theorem graph_adj_iff_parent {q p : ℕ} (v w : Vertex (Label q p)) :
    (graph q p).Adj v w ↔
      (v ≠ root q p ∧ parent v = w) ∨
      (w ≠ root q p ∧ parent w = v) := by
  constructor
  · rcases v with ⟨i, b⟩
    rcases w with ⟨j, c⟩
    intro ha
    change (i = j ∧ b ≠ c) ∨ (b = 0 ∧ c = 1 ∧ arrow q p i j) ∨
      (b = 1 ∧ c = 0 ∧ arrow q p j i) at ha
    rcases ha with ⟨hij, hbc⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
    · subst j
      fin_cases b <;> fin_cases c
      · exact (hbc rfl).elim
      · exact pair_parent i
      · exact (pair_parent i).symm
      · exact (hbc rfl).elim
    · exact arrow_parent i j h
    · exact (arrow_parent j i h).symm
  · rintro (⟨hv, hp⟩ | ⟨hw, hp⟩)
    · rw [← hp]
      exact parent_adj v hv
    · rw [← hp]
      exact (parent_adj w hw).symm

theorem graph_isTree (q p : ℕ) : (graph q p).IsTree :=
  tree_of_parent_data (graph q p) (root q p) parent rank
    rank_parent_lt graph_adj_iff_parent

theorem vertex_card (q p : ℕ) :
    Fintype.card (Vertex (Label q p)) = 2 * m q p := by
  simp only [Vertex, Fintype.card_prod, Fintype.card_fin, label_card, Nat.mul_comm]

def mate {q p : ℕ} (v : Vertex (Label q p)) : Vertex (Label q p) :=
  (v.1, if v.2 = 0 then 1 else 0)

theorem mate_involutive {q p : ℕ} : Function.Involutive (@mate q p) := by
  rintro ⟨i, b⟩
  fin_cases b <;> simp [mate]

theorem mate_adjacent {q p : ℕ} (v : Vertex (Label q p)) :
    (graph q p).Adj v (mate v) := by
  rcases v with ⟨i, b⟩
  fin_cases b <;> simp [mate, graph, splitGraph]

def matching (q p : ℕ) : (graph q p).Subgraph where
  verts := Set.univ
  Adj v w := mate v = w
  adj_sub := by
    intro v w h
    rw [← h]
    exact mate_adjacent v
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    intro v w h
    rw [← h]
    exact mate_involutive v⟩

theorem matching_isPerfectMatching (q p : ℕ) :
    (matching q p).IsPerfectMatching := by
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro v
  exact ⟨mate v, rfl, fun _ h => Eq.symm h⟩

theorem allPlus_isMaximumIndepSet (q p : ℕ) :
    (graph q p).IsMaximumIndepSet (allPlus q p) where
  isIndepSet := allPlus_independent q p
  maximum t ht := by
    rw [allPlus_card]
    exact independent_card_le q p t ht

theorem graph_indepNum (q p : ℕ) : (graph q p).indepNum = m q p := by
  have h := (graph q p).maximumIndepSet_card_eq_indepNum (allPlus q p)
    (allPlus_isMaximumIndepSet q p)
  rw [allPlus_card] at h
  exact h.symm

set_option linter.hashCommand false

end FormalProof.Research003.RS42FixedK
