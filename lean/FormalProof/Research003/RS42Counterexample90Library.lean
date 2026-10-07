module
public import FormalProof.Research003.RS42Counterexample90
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Matching

set_option linter.style.header false

/-!
Mathlib interfaces for the fixed 90-vertex graph: independence number,
perfect matching and actual independent-set count semantics. No numeric
coefficient values or complete counterexample are asserted here.
-/

@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Counterexample90

theorem independent_iff_mathlib {V : Type*} (G : SimpleGraph V) (s : Set V) :
    Independent G s ↔ G.IsIndepSet s := Iff.rfl

theorem allPlus90_isMaximumIndepSet : graph90.IsMaximumIndepSet allPlus90 where
  isIndepSet := allPlus90_independent
  maximum t ht := by
    rw [allPlus90_card]
    exact graph90_independent_card_le t ht

theorem graph90_indepNum : graph90.indepNum = 45 := by
  have h := graph90.maximumIndepSet_card_eq_indepNum allPlus90
    allPlus90_isMaximumIndepSet
  rw [allPlus90_card] at h
  exact h.symm

def matching90 : graph90.Subgraph where
  verts := Set.univ
  Adj v w := mate90 v = w
  adj_sub := by
    intro v w h
    rw [← h]
    exact mate90_adjacent v
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨by
    intro v w h
    rw [← h]
    exact mate90_involutive v⟩

theorem matching90_isPerfectMatching : matching90.IsPerfectMatching := by
  apply SimpleGraph.Subgraph.isPerfectMatching_iff.mpr
  intro v
  exact ⟨mate90 v, rfl, fun _ h => Eq.symm h⟩

noncomputable def mathlibCoefficientEquiv (k : ℕ) :
    {s : Finset (Fin 90) // graph90.IsNIndepSet k s} ≃
    {s : Finset (Fin 90) // Independent graph90 (s : Set (Fin 90)) ∧ s.card = k} where
  toFun s := ⟨s.1, s.2.isIndepSet, s.2.card_eq⟩
  invFun s := ⟨s.1, ⟨s.2.1, s.2.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem graph90_mathlib_count_eq_stateCount (k : ℕ) :
    Nat.card {s : Finset (Fin 90) // graph90.IsNIndepSet k s} =
      Nat.card {f : State (Fin 45) // legal arrow45 f ∧ (selected f).card = k} := by
  calc
    _ = coefficient graph90 k := Nat.card_congr (mathlibCoefficientEquiv k)
    _ = _ := graph90_coefficient_eq_stateCount k

#check graph90_indepNum
#check matching90_isPerfectMatching
#check graph90_mathlib_count_eq_stateCount
#print axioms independent_iff_mathlib
#print axioms graph90_indepNum
#print axioms matching90_isPerfectMatching
#print axioms graph90_mathlib_count_eq_stateCount

end FormalProof.Research003.RS42Counterexample90
