module

public import FormalProof.Research003.RS42Counterexample90Library
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public meta import Mathlib.Tactic.FinCases
public meta import Lean.Elab.Tactic.Omega

set_option linter.style.header false

/-!
Structural certification of the fixed 90-vertex graph.

The graph has a parent map with strictly decreasing rank. Nonroot vertices
are in bijection with edges, so connectedness and the edge cardinality imply
treehood. The certificate's literal edge list is independently identified
with seven short interval descriptions. No independent sets are enumerated.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

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

def rootBlock90 : Vertex (Fin 45) := (2, 1)

def incomingBlock90 (i : Fin 45) : Prop :=
  (9 ≤ i.val ∧ i.val ≤ 20) ∨ (27 ≤ i.val ∧ i.val ≤ 38)

instance (i : Fin 45) : Decidable (incomingBlock90 i) := by
  unfold incomingBlock90
  infer_instance

def attachmentEnd90 (i : Fin 45) : Fin 2 :=
  if incomingBlock90 i then 0 else 1

def hubBlock90 (i : Fin 45) : Vertex (Fin 45) :=
  if i.val < 9 then (0, 0)
  else if i.val < 21 then (0, 1)
  else if i.val < 27 then (1, 0)
  else if i.val < 39 then (1, 1)
  else (2, 0)

def parentBlock90 (v : Vertex (Fin 45)) : Vertex (Fin 45) :=
  if v.1.val < 3 then
    if v.2 = 0 then rootBlock90
    else if v.1 = 2 then rootBlock90 else (v.1, 0)
  else if v.2 = attachmentEnd90 v.1 then hubBlock90 v.1
  else (v.1, attachmentEnd90 v.1)

def rankBlock90 (v : Vertex (Fin 45)) : ℕ :=
  if v.1.val < 3 then
    if v.2 = 0 then 1 else if v.1 = 2 then 0 else 2
  else if incomingBlock90 v.1 then
    if v.2 = 0 then 3 else 4
  else if v.2 = 1 then 2 else 3

private theorem block_interval_cases90 (i : Fin 45) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨
    (3 ≤ i.val ∧ i.val ≤ 8) ∨
    (9 ≤ i.val ∧ i.val ≤ 20) ∨
    (21 ≤ i.val ∧ i.val ≤ 26) ∨
    (27 ≤ i.val ∧ i.val ≤ 38) ∨
    (39 ≤ i.val ∧ i.val ≤ 44) := by
  have hi := i.isLt
  simp only [Fin.ext_iff]
  omega

private theorem out_normal90 (i : Fin 45) (hi : 3 ≤ i.val)
    (hout : ¬ incomingBlock90 i) :
    parentBlock90 (i, 0) = (i, 1) ∧
    parentBlock90 (i, 1) = hubBlock90 i ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 2 := by
  have h3 : ¬ i.val < 3 := by omega
  simp [parentBlock90, rankBlock90, attachmentEnd90, h3, hout]

private theorem in_normal90 (i : Fin 45) (hi : 3 ≤ i.val)
    (hin : incomingBlock90 i) :
    parentBlock90 (i, 0) = hubBlock90 i ∧
    parentBlock90 (i, 1) = (i, 0) ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 4 := by
  have h3 : ¬ i.val < 3 := by omega
  simp [parentBlock90, rankBlock90, attachmentEnd90, h3, hin]

private theorem out_u_normal90 (i : Fin 45) (hi : 3 ≤ i.val ∧ i.val ≤ 8) :
    parentBlock90 (i, 0) = (i, 1) ∧ parentBlock90 (i, 1) = (0, 0) ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 2 := by
  have hout : ¬ incomingBlock90 i := by unfold incomingBlock90; omega
  have h9 : i.val < 9 := by omega
  simpa [hubBlock90, h9] using out_normal90 i hi.1 hout

private theorem in_u_normal90 (i : Fin 45) (hi : 9 ≤ i.val ∧ i.val ≤ 20) :
    parentBlock90 (i, 0) = (0, 1) ∧ parentBlock90 (i, 1) = (i, 0) ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 4 := by
  have hin : incomingBlock90 i := Or.inl hi
  have h9 : ¬ i.val < 9 := by omega
  have h21 : i.val < 21 := by omega
  simpa [hubBlock90, h9, h21] using in_normal90 i (by omega) hin

private theorem out_v_normal90 (i : Fin 45) (hi : 21 ≤ i.val ∧ i.val ≤ 26) :
    parentBlock90 (i, 0) = (i, 1) ∧ parentBlock90 (i, 1) = (1, 0) ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 2 := by
  have hout : ¬ incomingBlock90 i := by unfold incomingBlock90; omega
  have h9 : ¬ i.val < 9 := by omega
  have h21 : ¬ i.val < 21 := by omega
  have h27 : i.val < 27 := by omega
  simpa [hubBlock90, h9, h21, h27] using out_normal90 i (by omega) hout

private theorem in_v_normal90 (i : Fin 45) (hi : 27 ≤ i.val ∧ i.val ≤ 38) :
    parentBlock90 (i, 0) = (1, 1) ∧ parentBlock90 (i, 1) = (i, 0) ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 4 := by
  have hin : incomingBlock90 i := Or.inr hi
  have h9 : ¬ i.val < 9 := by omega
  have h21 : ¬ i.val < 21 := by omega
  have h27 : ¬ i.val < 27 := by omega
  have h39 : i.val < 39 := by omega
  simpa [hubBlock90, h9, h21, h27, h39] using in_normal90 i (by omega) hin

private theorem out_z_normal90 (i : Fin 45) (hi : 39 ≤ i.val ∧ i.val ≤ 44) :
    parentBlock90 (i, 0) = (i, 1) ∧ parentBlock90 (i, 1) = (2, 0) ∧
    rankBlock90 (i, 0) = 3 ∧ rankBlock90 (i, 1) = 2 := by
  have hout : ¬ incomingBlock90 i := by unfold incomingBlock90; omega
  have h9 : ¬ i.val < 9 := by omega
  have h21 : ¬ i.val < 21 := by omega
  have h27 : ¬ i.val < 27 := by omega
  have h39 : ¬ i.val < 39 := by omega
  simpa [hubBlock90, h9, h21, h27, h39] using out_normal90 i (by omega) hout

private theorem leaf_ne_root90 (i : Fin 45) (hi : 3 ≤ i.val) (b : Fin 2) :
    (i, b) ≠ rootBlock90 := by
  intro h
  have he := congrArg (fun v : Vertex (Fin 45) => v.1.val) h
  change i.val = 2 at he
  omega

set_option linter.unusedSimpArgs false in
theorem rankBlock90_parent_lt (v : Vertex (Fin 45)) (hv : v ≠ rootBlock90) :
    rankBlock90 (parentBlock90 v) < rankBlock90 v := by
  rcases v with ⟨i, b⟩
  rcases block_interval_cases90 i with rfl | rfl | rfl | hi | hi | hi | hi | hi
  · rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp [parentBlock90, rankBlock90, rootBlock90] at hv ⊢
  · rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp [parentBlock90, rankBlock90, rootBlock90] at hv ⊢
  · rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp [parentBlock90, rankBlock90, rootBlock90] at hv ⊢
  · obtain ⟨h0, h1, r0, r1⟩ := out_u_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1, r0, r1] <;> simp [rankBlock90]
  · obtain ⟨h0, h1, r0, r1⟩ := in_u_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1, r0, r1] <;> simp [rankBlock90]
  · obtain ⟨h0, h1, r0, r1⟩ := out_v_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1, r0, r1] <;> simp [rankBlock90]
  · obtain ⟨h0, h1, r0, r1⟩ := in_v_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1, r0, r1] <;> simp [rankBlock90]
  · obtain ⟨h0, h1, r0, r1⟩ := out_z_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1, r0, r1] <;> simp [rankBlock90]

set_option linter.unusedSimpArgs false in
theorem parentBlock90_adj (v : Vertex (Fin 45)) (hv : v ≠ rootBlock90) :
    blockGraph90.Adj v (parentBlock90 v) := by
  rcases v with ⟨i, b⟩
  rcases block_interval_cases90 i with rfl | rfl | rfl | hi | hi | hi | hi | hi
  · rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp [parentBlock90, rootBlock90, blockGraph90, splitGraph, arrow45] at hv ⊢
  · rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp [parentBlock90, rootBlock90, blockGraph90, splitGraph, arrow45] at hv ⊢
  · rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp [parentBlock90, rootBlock90, blockGraph90, splitGraph, arrow45] at hv ⊢
  · obtain ⟨h0, h1, _, _⟩ := out_u_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1] <;>
      (simp [blockGraph90, splitGraph, arrow45, Fin.ext_iff, -Fin.val_eq_zero_iff]
       all_goals omega)
  · obtain ⟨h0, h1, _, _⟩ := in_u_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1] <;>
      (simp [blockGraph90, splitGraph, arrow45, Fin.ext_iff, -Fin.val_eq_zero_iff]
       all_goals omega)
  · obtain ⟨h0, h1, _, _⟩ := out_v_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1] <;>
      (simp [blockGraph90, splitGraph, arrow45, Fin.ext_iff, -Fin.val_eq_zero_iff]
       all_goals omega)
  · obtain ⟨h0, h1, _, _⟩ := in_v_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1] <;>
      (simp [blockGraph90, splitGraph, arrow45, Fin.ext_iff, -Fin.val_eq_zero_iff]
       all_goals omega)
  · obtain ⟨h0, h1, _, _⟩ := out_z_normal90 i hi
    rcases (show b = 0 ∨ b = 1 from by omega) with rfl | rfl <;>
      simp only [h0, h1] <;>
      (simp [blockGraph90, splitGraph, arrow45, Fin.ext_iff, -Fin.val_eq_zero_iff]
       all_goals omega)

set_option linter.unusedSimpArgs false in
private theorem pair90_parent (i : Fin 45) :
    ((i, (0 : Fin 2)) ≠ rootBlock90 ∧ parentBlock90 (i, 0) = (i, 1)) ∨
      ((i, (1 : Fin 2)) ≠ rootBlock90 ∧ parentBlock90 (i, 1) = (i, 0)) := by
  rcases block_interval_cases90 i with rfl | rfl | rfl | hi | hi | hi | hi | hi
  · simp [parentBlock90, rootBlock90]
  · simp [parentBlock90, rootBlock90]
  · simp [parentBlock90, rootBlock90]
  · exact Or.inl ⟨leaf_ne_root90 i hi.1 0, (out_u_normal90 i hi).1⟩
  · exact Or.inr ⟨leaf_ne_root90 i (by omega) 1, (in_u_normal90 i hi).2.1⟩
  · exact Or.inl ⟨leaf_ne_root90 i (by omega) 0, (out_v_normal90 i hi).1⟩
  · exact Or.inr ⟨leaf_ne_root90 i (by omega) 1, (in_v_normal90 i hi).2.1⟩
  · exact Or.inl ⟨leaf_ne_root90 i (by omega) 0, (out_z_normal90 i hi).1⟩

set_option linter.unusedSimpArgs false in
private theorem arrow45_parent (i k : Fin 45) (h : arrow45 i k) :
    ((i, (0 : Fin 2)) ≠ rootBlock90 ∧ parentBlock90 (i, 0) = (k, 1)) ∨
      ((k, (1 : Fin 2)) ≠ rootBlock90 ∧ parentBlock90 (k, 1) = (i, 0)) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, hk⟩ |
    ⟨hi, hi', rfl⟩ | ⟨rfl, hk⟩ | ⟨hi, hi', rfl⟩ | ⟨rfl, hk⟩
  · simp [parentBlock90, rootBlock90]
  · simp [parentBlock90, rootBlock90]
  · exact Or.inr ⟨leaf_ne_root90 k hk.1 1, (out_u_normal90 k hk).2.1⟩
  · exact Or.inl ⟨leaf_ne_root90 i (by omega) 0, (in_u_normal90 i ⟨hi, hi'⟩).1⟩
  · exact Or.inr ⟨leaf_ne_root90 k (by omega) 1, (out_v_normal90 k hk).2.1⟩
  · exact Or.inl ⟨leaf_ne_root90 i (by omega) 0, (in_v_normal90 i ⟨hi, hi'⟩).1⟩
  · exact Or.inr ⟨leaf_ne_root90 k (by omega) 1, (out_z_normal90 k hk).2.1⟩

theorem blockGraph90_adj_iff_parent (v w : Vertex (Fin 45)) :
    blockGraph90.Adj v w ↔
      (v ≠ rootBlock90 ∧ parentBlock90 v = w) ∨
      (w ≠ rootBlock90 ∧ parentBlock90 w = v) := by
  constructor
  · rcases v with ⟨i, b⟩
    rcases w with ⟨k, c⟩
    intro ha
    change (i = k ∧ b ≠ c) ∨ (b = 0 ∧ c = 1 ∧ arrow45 i k) ∨
      (b = 1 ∧ c = 0 ∧ arrow45 k i) at ha
    rcases ha with ⟨hik, hbc⟩ | ⟨rfl, rfl, h⟩ | ⟨rfl, rfl, h⟩
    · subst k
      fin_cases b <;> fin_cases c
      · exact (hbc rfl).elim
      · exact pair90_parent i
      · exact (pair90_parent i).symm
      · exact (hbc rfl).elim
    · exact arrow45_parent i k h
    · exact (arrow45_parent k i h).symm
  · rintro (⟨hv, hp⟩ | ⟨hw, hp⟩)
    · rw [← hp]
      exact parentBlock90_adj v hv
    · rw [← hp]
      exact (parentBlock90_adj w hw).symm

theorem blockGraph90_isTree : blockGraph90.IsTree :=
  tree_of_parent_data blockGraph90 rootBlock90 parentBlock90 rankBlock90
    rankBlock90_parent_lt blockGraph90_adj_iff_parent

def blockGraph90Iso : blockGraph90 ≃g graph90 where
  toEquiv := vertex90Equiv
  map_rel_iff' := by
    intro v w
    simp [graph90]

theorem graph90_isTree : graph90.IsTree :=
  blockGraph90Iso.isTree_iff.mp blockGraph90_isTree

/-- The literal certificate list, reorganized into the matching and five
pendant-arm intervals. This equality unfolds only the 89 listed edges. -/
theorem fixedEdges90_eq_ranges :
    fixedEdges90 =
      (List.range 45).map (fun i => (2 * i, 2 * i + 1)) ++
      [(0, 5), (2, 5)] ++
      (List.range 6).map (fun i => (0, 2 * (3 + i) + 1)) ++
      (List.range 12).map (fun i => (2 * (9 + i), 1)) ++
      (List.range 6).map (fun i => (2, 2 * (21 + i) + 1)) ++
      (List.range 12).map (fun i => (2 * (27 + i), 3)) ++
      (List.range 6).map (fun i => (4, 2 * (39 + i) + 1)) := by
  rfl

private theorem mem_shifted_map_range {α : Type*} (n lo : ℕ)
    (f : ℕ → α) (x : α) :
    x ∈ (List.range n).map (fun i => f (lo + i)) ↔
      ∃ k, lo ≤ k ∧ k < lo + n ∧ f k = x := by
  simp only [List.mem_map, List.mem_range]
  constructor
  · rintro ⟨i, hi, hx⟩
    exact ⟨lo + i, by omega, by omega, hx⟩
  · rintro ⟨k, hlo, hhi, hx⟩
    refine ⟨k - lo, by omega, ?_⟩
    have he : lo + (k - lo) = k := by omega
    simpa [he] using hx

private theorem matching_mem_range90 (i k : Fin 45) (b c : Fin 2) :
    (b.val + 2 * i.val, c.val + 2 * k.val) ∈
      (List.range 45).map (fun j => (2 * j, 2 * j + 1)) ↔
      b = 0 ∧ c = 1 ∧ i = k := by
  simp only [List.mem_map, List.mem_range, Prod.mk.injEq, Fin.ext_iff]
  have hi := i.isLt
  have hk := k.isLt
  have hb := b.isLt
  have hc := c.isLt
  constructor
  · rintro ⟨j, hj, h1, h2⟩
    omega
  · rintro ⟨hb0, hc1, hik⟩
    exact ⟨i.val, hi, by omega, by omega⟩

theorem fixedEdges90_block_membership (i k : Fin 45) (b c : Fin 2) :
    (b.val + 2 * i.val, c.val + 2 * k.val) ∈ fixedEdges90 ↔
      b = 0 ∧ c = 1 ∧ (i = k ∨ arrow45 i k) := by
  rw [fixedEdges90_eq_ranges]
  simp only [List.mem_append, matching_mem_range90, List.mem_cons,
    List.not_mem_nil, or_false]
  rw [mem_shifted_map_range 6 3 (fun j => (0, 2 * j + 1)),
    mem_shifted_map_range 12 9 (fun j => (2 * j, 1)),
    mem_shifted_map_range 6 21 (fun j => (2, 2 * j + 1)),
    mem_shifted_map_range 12 27 (fun j => (2 * j, 3)),
    mem_shifted_map_range 6 39 (fun j => (4, 2 * j + 1))]
  simp only [Prod.mk.injEq, arrow45, Fin.ext_iff, or_assoc]
  have hi := i.isLt
  have hk := k.isLt
  have hb := b.isLt
  have hc := c.isLt
  constructor
  · intro h
    rcases h with h | h | h | ⟨x, h⟩ | ⟨x, h⟩ | ⟨x, h⟩ | ⟨x, h⟩ | ⟨x, h⟩
    all_goals omega
  · rintro ⟨hb0, hc1, h⟩
    rcases h with hik | h0 | h1 | h2 | h3 | h4 | h5 | h6
    · exact Or.inl ⟨hb0, hc1, hik⟩
    · omega
    · omega
    · right; right; right; left
      exact ⟨k.val, by omega, by omega, by omega, by omega⟩
    · right; right; right; right; left
      exact ⟨i.val, by omega, by omega, by omega, by omega⟩
    · right; right; right; right; right; left
      exact ⟨k.val, by omega, by omega, by omega, by omega⟩
    · right; right; right; right; right; right; left
      exact ⟨i.val, by omega, by omega, by omega, by omega⟩
    · right; right; right; right; right; right; right
      exact ⟨k.val, by omega, by omega, by omega, by omega⟩

theorem graph90_adj_iff_fixedEdges (v w : Fin 90) :
    graph90.Adj v w ↔
      (v.val, w.val) ∈ fixedEdges90 ∨ (w.val, v.val) ∈ fixedEdges90 := by
  obtain ⟨⟨i, b⟩, rfl⟩ := vertex90Equiv.surjective v
  obtain ⟨⟨k, c⟩, rfl⟩ := vertex90Equiv.surjective w
  change blockGraph90.Adj
      (vertex90Equiv.symm (vertex90Equiv (i, b)))
      (vertex90Equiv.symm (vertex90Equiv (k, c))) ↔ _
  simp only [Equiv.symm_apply_apply]
  change blockGraph90.Adj (i, b) (k, c) ↔
    (b.val + 2 * i.val, c.val + 2 * k.val) ∈ fixedEdges90 ∨
      (c.val + 2 * k.val, b.val + 2 * i.val) ∈ fixedEdges90
  rw [fixedEdges90_block_membership, fixedEdges90_block_membership]
  fin_cases b <;> fin_cases c <;>
    simp [blockGraph90, splitGraph, eq_comm, or_comm]

set_option linter.hashCommand false in
#print axioms graph90_isTree
set_option linter.hashCommand false in
#print axioms graph90_adj_iff_fixedEdges

end FormalProof.Research003.RS42Counterexample90
