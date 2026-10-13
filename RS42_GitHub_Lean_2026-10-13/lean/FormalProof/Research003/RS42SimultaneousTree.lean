module
public import FormalProof.Research003.RS42SimultaneousCore
public import FormalProof.Research003.RS42StructuralTree
set_option linter.style.header false
set_option linter.hashCommand false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Simultaneous
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


def coreGraph (t : ℕ) : SimpleGraph (Core t) where
  Adj v w := arrow t v w ∨ arrow t w v
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h <;> rcases h with ⟨_,hv,hw⟩ | ⟨_,_,hn⟩
    · exact hv hw
    · omega
    · exact hv hw
    · omega⟩

def coreRoot (t : ℕ) (ht : 0 < t) : Core t := (⟨0,ht⟩,0)
def coreParent {t : ℕ} (v : Core t) : Core t :=
  if v.2 = 0 then (⟨v.1.val-1, (Nat.sub_le v.1.val 1).trans_lt v.1.isLt⟩,0)
  else (v.1,0)
def coreRank {t : ℕ} (v : Core t) : ℕ := 2*v.1.val + if v.2 = 0 then 0 else 1

theorem rank_decreases (t : ℕ) (ht : 0 < t) (v : Core t)
    (hv : v ≠ coreRoot t ht) : coreRank (coreParent v) < coreRank v := by
  rcases v with ⟨i,h⟩
  by_cases hh : h = 0
  · subst h
    have hi : i.val ≠ 0 := by
      intro he
      apply hv
      simp [coreRoot, Prod.ext_iff, Fin.ext_iff, he]
    simp [coreParent, coreRank]
    omega
  · simp [coreParent, coreRank, hh]

theorem adjacency_parent (t : ℕ) (ht : 0 < t) (v w : Core t) :
    (coreGraph t).Adj v w ↔
      (v ≠ coreRoot t ht ∧ coreParent v = w) ∨
      (w ≠ coreRoot t ht ∧ coreParent w = v) := by
  rcases v with ⟨i,h⟩
  rcases w with ⟨j,k⟩
  by_cases hh : h = 0 <;> by_cases hk : k = 0
  all_goals simp only [coreGraph, arrow, coreParent, coreRoot,
    hh, hk, ite_true, ite_false, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero]
  all_goals simp only [ne_eq, Prod.mk.injEq, Fin.ext_iff, Fin.val_zero] at *
  all_goals try simp only [true_and, and_true, false_and, and_false,
    false_or, not_true_eq_false]
  all_goals omega

theorem core_isTree (t : ℕ) (ht : 0 < t) : (coreGraph t).IsTree :=
  tree_of_parent_data (coreGraph t) (coreRoot t ht) coreParent coreRank
    (rank_decreases t ht) (adjacency_parent t ht)

theorem arrow_asymm (t : ℕ) (v w : Core t) : arrow t v w → ¬ arrow t w v := by
  intro hv hw
  rcases hv with ⟨he,hv,hz⟩ | ⟨hz,hv,he⟩ <;>
    rcases hw with ⟨he',hw,hz'⟩ | ⟨hz',hw,he'⟩
  · exact hv hz'
  · exact hv hw
  · exact hw hv
  · omega

end FormalProof.Research003.RS42Simultaneous
