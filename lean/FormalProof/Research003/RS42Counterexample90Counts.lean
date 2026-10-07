module

public import FormalProof.Research003.RS42Counterexample90Library
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Algebra.BigOperators.Fin
public meta import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.FinCases

set_option linter.style.header false

/-!
Exact counting of the fixed 90-vertex graph by three core blocks and
42 conditionally independent leaf blocks. The input is the actual arrow45
relation and the previously proved independent-set/state equivalence.
No numerical graph coefficient is an assumption.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

open scoped BigOperators

/-- A nonempty matching block selects exactly one vertex. -/
def occupied (b : Option (Fin 2)) : ℕ := if b.isSome then 1 else 0

theorem selected_card_eq_sum {ι : Type*} [Fintype ι] (f : State ι) :
    (selected f).card = ∑ i, occupied (f i) := by
  classical
  rw [selected, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [Fin.sum_univ_two]
  cases h : f i with
  | none => simp [occupied]
  | some b => fin_cases b <;> simp [occupied]

/-- Restrict the original graph arrows to its three core matching blocks. -/
def coreLegal90 (c : State (Fin 3)) : Prop :=
  legal (fun i k => arrow45 (i.castAdd 42) (k.castAdd 42)) c

/-- All constraints on one leaf block after the three core states are fixed. -/
def leafAllowed90 (c : State (Fin 3)) (l : Fin 42) (b : Option (Fin 2)) : Prop :=
  (∀ i : Fin 3, arrow45 (i.castAdd 42) (l.natAdd 3) →
    ¬ (c i = some 0 ∧ b = some 1)) ∧
  (∀ i : Fin 3, arrow45 (l.natAdd 3) (i.castAdd 42) →
    ¬ (b = some 0 ∧ c i = some 1))

theorem no_leaf_leaf_arrow90 (i k : Fin 42) :
    ¬ arrow45 (i.natAdd 3) (k.natAdd 3) := by
  have hne (l : Fin 42) (c : Fin 45) (hc : c.val < 3) : l.natAdd 3 ≠ c := by
    intro h
    have hv := congrArg Fin.val h
    change 3 + l.val = c.val at hv
    omega
  simp [arrow45, hne i 0 (by decide), hne i 1 (by decide),
    hne i 2 (by decide), hne k 0 (by decide), hne k 1 (by decide)]

theorem legal_append_iff (c : State (Fin 3)) (l : State (Fin 42)) :
    legal arrow45 (Fin.append c l) ↔
      coreLegal90 c ∧ ∀ i, leafAllowed90 c i (l i) := by
  constructor
  · intro h
    constructor
    · intro i k hik
      simpa using h (i.castAdd 42) (k.castAdd 42) hik
    · intro k
      constructor
      · intro i hik
        simpa using h (i.castAdd 42) (k.natAdd 3) hik
      · intro i hik
        simpa using h (k.natAdd 3) (i.castAdd 42) hik
  · rintro ⟨hc, hl⟩
    change ∀ i k : Fin (3 + 42), arrow45 i k →
      ¬ (Fin.append c l i = some 0 ∧ Fin.append c l k = some 1)
    refine Fin.addCases (m := 3) (n := 42) (fun i => ?_) (fun i => ?_)
    · refine Fin.addCases (m := 3) (n := 42) (fun k => ?_) (fun k => ?_)
      · simpa using hc i k
      · simpa using (hl k).1 i
    · refine Fin.addCases (m := 3) (n := 42) (fun k => ?_) (fun k => ?_)
      · simpa using (hl i).2 k
      · exact fun h => False.elim (no_leaf_leaf_arrow90 i k h)

theorem selected_append_card (c : State (Fin 3)) (l : State (Fin 42)) :
    (selected (Fin.append c l)).card =
      (∑ i, occupied (c i)) + ∑ i, occupied (l i) := by
  rw [selected_card_eq_sum, Fin.sum_univ_add]
  simp

/-- The state split is a genuine invertible restriction/concatenation. -/
def coreLeafStateEquiv90 : State (Fin 45) ≃ State (Fin 3) × State (Fin 42) where
  toFun f := (fun i => f (i.castAdd 42), fun i => f (i.natAdd 3))
  invFun z := Fin.append z.1 z.2
  left_inv _ := Fin.append_castAdd_natAdd
  right_inv z := by
    apply Prod.ext <;> funext i <;> simp

noncomputable def coreLeafCardEquiv90 (k : ℕ) :
    {f : State (Fin 45) // legal arrow45 f ∧ (selected f).card = k} ≃
    {z : State (Fin 3) × State (Fin 42) //
      coreLegal90 z.1 ∧ (∀ i, leafAllowed90 z.1 i (z.2 i)) ∧
        (∑ i, occupied (z.1 i)) + (∑ i, occupied (z.2 i)) = k} where
  toFun f := ⟨coreLeafStateEquiv90 f.1, by
    have hr := coreLeafStateEquiv90.left_inv f.1
    have hlegal := f.2.1
    rw [← hr] at hlegal
    have hc := (legal_append_iff _ _).mp hlegal
    refine ⟨hc.1, hc.2, ?_⟩
    have hcard := f.2.2
    rw [← hr] at hcard
    change (selected (Fin.append (coreLeafStateEquiv90 f.1).1
      (coreLeafStateEquiv90 f.1).2)).card = k at hcard
    rw [selected_append_card] at hcard
    exact hcard⟩
  invFun z := ⟨Fin.append z.1.1 z.1.2, by
    refine ⟨(legal_append_iff _ _).mpr ⟨z.2.1, z.2.2.1⟩, ?_⟩
    rw [selected_append_card]
    exact z.2.2.2⟩
  left_inv f := Subtype.ext (coreLeafStateEquiv90.left_inv f.1)
  right_inv z := Subtype.ext (coreLeafStateEquiv90.right_inv z.1)

theorem coefficient_graph90_eq_coreLeaf_count (k : ℕ) :
    coefficient graph90 k =
      Nat.card {z : State (Fin 3) × State (Fin 42) //
        coreLegal90 z.1 ∧ (∀ i, leafAllowed90 z.1 i (z.2 i)) ∧
          (∑ i, occupied (z.1 i)) + (∑ i, occupied (z.2 i)) = k} := by
  rw [graph90_coefficient_eq_stateCount]
  exact Nat.card_congr (coreLeafCardEquiv90 k)

end FormalProof.Research003.RS42Counterexample90
