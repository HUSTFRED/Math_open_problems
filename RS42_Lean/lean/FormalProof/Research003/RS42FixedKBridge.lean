module

public import FormalProof.Research003.RS42Counterexample90
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Combinatorics.SimpleGraph.Clique

/-!
The imported matching-block definitions and equivalences are already generic
in the finite label type despite their module name.
This file only instantiates that interface at explicit parameterized labels.
It does not prove treehood, the deletion sum, coefficient bounds or failure.
-/

set_option linter.style.header false

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90

-- Reuse the generic matching-block interface.

/-- Core u-labels and z, followed by outgoing, incoming and z-leaf labels. -/
abbrev Label (q p : ℕ) :=
  (Fin q ⊕ Unit) ⊕ ((Fin q × Fin p) ⊕ ((Fin q × Fin (2 * p)) ⊕ Fin p))

def u {q p : ℕ} (i : Fin q) : Label q p := Sum.inl (Sum.inl i)
def z (q p : ℕ) : Label q p := Sum.inl (Sum.inr ())
def outLeaf {q p : ℕ} (i : Fin q) (j : Fin p) : Label q p :=
  Sum.inr (Sum.inl (i, j))
def inLeaf {q p : ℕ} (i : Fin q) (j : Fin (2 * p)) : Label q p :=
  Sum.inr (Sum.inr (Sum.inl (i, j)))
def zLeaf {q p : ℕ} (j : Fin p) : Label q p :=
  Sum.inr (Sum.inr (Sum.inr j))

def m (q p : ℕ) : ℕ := (3 * q + 1) * p + q + 1

def arrow (q p : ℕ) (v w : Label q p) : Prop :=
  (∃ i : Fin q, v = u i ∧ w = z q p) ∨
  (∃ (i : Fin q) (j : Fin p), v = u i ∧ w = outLeaf i j) ∨
  (∃ (i : Fin q) (j : Fin (2 * p)), v = inLeaf i j ∧ w = u i) ∨
  (∃ j : Fin p, v = z q p ∧ w = zLeaf j)

def graph (q p : ℕ) : SimpleGraph (Vertex (Label q p)) :=
  splitGraph (arrow q p)

theorem label_card (q p : ℕ) : Fintype.card (Label q p) = m q p := by
  simp [Label, m]
  ring

theorem independent_card_le (q p : ℕ)
    (s : Finset (Vertex (Label q p)))
    (hs : Independent (graph q p) (s : Set (Vertex (Label q p)))) :
    s.card ≤ m q p := by
  simpa only [label_card] using RS42Counterexample90.independent_card_le (arrow q p) s hs

def allPlus (q p : ℕ) : Finset (Vertex (Label q p)) :=
  selected (fun _ => some 0)

theorem allPlus_independent (q p : ℕ) :
    Independent (graph q p)
      (allPlus q p : Set (Vertex (Label q p))) := by
  apply (selected_independent_iff (arrow q p) _).mpr
  intro i j _ h
  exact (by decide : (some (0 : Fin 2)) ≠ some 1) h.2

theorem allPlus_card (q p : ℕ) : (allPlus q p).card = m q p := by
  classical
  have he : allPlus q p = Finset.univ.image
      (fun i : Label q p => (i, (0 : Fin 2))) := by
    ext v
    rcases v with ⟨i, b⟩
    simp [allPlus, selected]
  rw [he, Finset.card_image_of_injective]
  · exact label_card q p
  · intro i j h
    exact congrArg Prod.fst h

/-- True independent-set cardinalities, via the already generic state bridge. -/
theorem coefficient_eq_state_count (q p j : ℕ) :
    coefficient (graph q p) j =
      Nat.card {f : State (Label q p) //
        legal (arrow q p) f ∧ (selected f).card = j} := by
  exact coefficient_splitGraph (arrow q p) j

noncomputable def graphIndependentStateEquiv (q p : ℕ) (j : ℕ) :=
  independentCardStateEquiv (arrow q p) j

noncomputable def mathlibCoefficientEquiv (q p j : ℕ) :
    {s : Finset (Vertex (Label q p)) // (graph q p).IsNIndepSet j s} ≃
    {s : Finset (Vertex (Label q p)) //
      Independent (graph q p) (s : Set (Vertex (Label q p))) ∧ s.card = j} where
  toFun s := ⟨s.1, s.2.isIndepSet, s.2.card_eq⟩
  invFun s := ⟨s.1, ⟨s.2.1, s.2.2⟩⟩
  left_inv _ := Subtype.ext rfl
  right_inv _ := Subtype.ext rfl

theorem mathlib_count_eq_state_count (q p j : ℕ) :
    Nat.card {s : Finset (Vertex (Label q p)) // (graph q p).IsNIndepSet j s} =
      Nat.card {f : State (Label q p) //
        legal (arrow q p) f ∧ (selected f).card = j} := by
  exact (Nat.card_congr (mathlibCoefficientEquiv q p j)).trans
    (coefficient_eq_state_count q p j)

set_option linter.hashCommand false

end FormalProof.Research003.RS42FixedK

