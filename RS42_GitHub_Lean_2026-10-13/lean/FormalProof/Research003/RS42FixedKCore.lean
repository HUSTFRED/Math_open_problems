module

public import FormalProof.Research003.RS42FixedKBridge
public import FormalProof.Research003.RS42FixedKDeletion
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public meta import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
Exact induced-deletion counting by a finite core and independent original
leaves. All cardinalities below count actual legal assignments, through an
explicit equivalence with the zero fiber of the matching-block state model.
-/

@[expose] public section
set_option autoImplicit false
open scoped BigOperators

namespace FormalProof.Research003.RS42FixedK

open RS42Counterexample90 (State legal)
open RS42FixedKDeletion

abbrev LeafLabel (q p : ℕ) :=
  (Fin q × Fin p) ⊕ ((Fin q × Fin (2 * p)) ⊕ Fin p)

abbrev CoreState (q : ℕ) := (Fin q → Option (Fin 2)) × Option (Fin 2)

def deletedUs {q p : ℕ} (C : Finset (Fin q)) : Finset (Label q p) :=
  C.image u

def deletedUsAndZ {q p : ℕ} (C : Finset (Fin q)) : Finset (Label q p) :=
  insert (z q p) (deletedUs C)

def coreDelete {q p : ℕ} (C : Finset (Fin q)) (dz : Bool) : Finset (Label q p) :=
  if dz then deletedUsAndZ C else deletedUs C

@[simp] theorem mem_coreDelete_u {q p : ℕ} (C : Finset (Fin q))
    (dz : Bool) (i : Fin q) : u i ∈ (coreDelete C dz : Finset (Label q p)) ↔ i ∈ C := by
  cases dz <;> simp [coreDelete, deletedUsAndZ, deletedUs, u, z]

@[simp] theorem mem_coreDelete_z {q p : ℕ} (C : Finset (Fin q)) (dz : Bool) :
    z q p ∈ coreDelete C dz ↔ dz = true := by
  cases dz <;> simp [coreDelete, deletedUsAndZ, deletedUs, u, z]

@[simp] theorem not_mem_coreDelete_leaf {q p : ℕ} (C : Finset (Fin q))
    (dz : Bool) (l : LeafLabel q p) :
    Sum.inr l ∉ (coreDelete C dz : Finset (Label q p)) := by
  cases dz <;> simp [coreDelete, deletedUsAndZ, deletedUs, u, z]

theorem deletedUs_card {q p : ℕ} (C : Finset (Fin q)) :
    (deletedUs C : Finset (Label q p)).card = C.card := by
  apply Finset.card_image_of_injective
  intro i j h
  simpa [u] using h

theorem deletedUsAndZ_card {q p : ℕ} (C : Finset (Fin q)) :
    (deletedUsAndZ C : Finset (Label q p)).card = C.card + 1 := by
  rw [deletedUsAndZ, Finset.card_insert_of_notMem, deletedUs_card]
  simp [deletedUs, u, z]

def assemble {q p : ℕ} (c : CoreState q)
    (f : LeafLabel q p → Option (Fin 2)) : State (Label q p)
  | Sum.inl (Sum.inl i) => c.1 i
  | Sum.inl (Sum.inr _) => c.2
  | Sum.inr l => f l

def disassemble {q p : ℕ} (f : State (Label q p)) :
    CoreState q × (LeafLabel q p → Option (Fin 2)) :=
  ((fun i => f (u i), f (z q p)), fun l => f (Sum.inr l))

theorem assemble_disassemble {q p : ℕ} (f : State (Label q p)) :
    assemble (disassemble f).1 (disassemble f).2 = f := by
  funext v
  rcases v with ((i | ⟨⟩) | l) <;> rfl

theorem disassemble_assemble {q p : ℕ} (c : CoreState q)
    (f : LeafLabel q p → Option (Fin 2)) : disassemble (assemble c f) = (c, f) := by
  rcases c with ⟨cu, cz⟩
  rfl

def coreAllowed {q : ℕ} (C : Finset (Fin q)) (dz : Bool) (c : CoreState q) : Prop :=
  (c.2 = none ↔ dz = true) ∧
    ∀ i, (c.1 i = none ↔ i ∈ C) ∧ ¬ (c.1 i = some 0 ∧ c.2 = some 1)

def leafAllowed {q p : ℕ} (c : CoreState q) :
    LeafLabel q p → Option (Fin 2) → Prop
  | Sum.inl (i, _), b => b ≠ none ∧ ¬ (c.1 i = some 0 ∧ b = some 1)
  | Sum.inr (Sum.inl (i, _)), b => b ≠ none ∧ ¬ (b = some 0 ∧ c.1 i = some 1)
  | Sum.inr (Sum.inr _), b => b ≠ none ∧ ¬ (c.2 = some 0 ∧ b = some 1)

theorem assemble_zero_iff {q p : ℕ} (C : Finset (Fin q)) (dz : Bool)
    (c : CoreState q) (f : LeafLabel q p → Option (Fin 2)) :
    zeroSet (assemble c f) = coreDelete C dz ↔
      (∀ i, c.1 i = none ↔ i ∈ C) ∧
      (c.2 = none ↔ dz = true) ∧ (∀ l, f l ≠ none) := by
  constructor
  · intro h
    refine ⟨?_, ?_, ?_⟩
    · intro i
      have hi := Finset.ext_iff.mp h (u i)
      rw [mem_zeroSet, mem_coreDelete_u] at hi
      exact hi
    · have hz := Finset.ext_iff.mp h (z q p)
      rw [mem_zeroSet, mem_coreDelete_z] at hz
      exact hz
    · intro l
      have hl := Finset.ext_iff.mp h (Sum.inr l)
      simpa only [mem_zeroSet, assemble, not_mem_coreDelete_leaf, iff_false] using hl
  · rintro ⟨hu, hz, hl⟩
    ext v
    simp only [mem_zeroSet]
    rcases v with ((i | ⟨⟩) | l)
    · change assemble c f (u i) = none ↔ u i ∈ coreDelete C dz
      rw [mem_coreDelete_u]
      exact hu i
    · change assemble c f (z q p) = none ↔ z q p ∈ coreDelete C dz
      rw [mem_coreDelete_z]
      exact hz
    · simp only [assemble, not_mem_coreDelete_leaf, iff_false]
      exact hl l

theorem assemble_condition_iff {q p : ℕ} (C : Finset (Fin q)) (dz : Bool)
    (c : CoreState q) (f : LeafLabel q p → Option (Fin 2)) :
    legal (arrow q p) (assemble c f) ∧ zeroSet (assemble c f) = coreDelete C dz ↔
      coreAllowed C dz c ∧ ∀ l, leafAllowed c l (f l) := by
  rw [assemble_zero_iff]
  constructor
  · rintro ⟨hleg, hu, hz, hl⟩
    refine ⟨⟨hz, fun i => ⟨hu i, ?_⟩⟩, ?_⟩
    · exact hleg (u i) (z q p) (Or.inl ⟨i, rfl, rfl⟩)
    · intro l
      rcases l with ⟨i, j⟩ | (⟨i, j⟩ | j)
      · exact ⟨hl _, hleg (u i) (outLeaf i j) (Or.inr (Or.inl ⟨i, j, rfl, rfl⟩))⟩
      · exact ⟨hl _, hleg (inLeaf i j) (u i)
          (Or.inr (Or.inr (Or.inl ⟨i, j, rfl, rfl⟩)))⟩
      · exact ⟨hl _, hleg (z q p) (zLeaf j)
          (Or.inr (Or.inr (Or.inr ⟨j, rfl, rfl⟩)))⟩
  · rintro ⟨⟨hz, hu⟩, hl⟩
    refine ⟨?_, fun i => (hu i).1, hz, ?_⟩
    · intro v w h
      rcases h with ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ |
        ⟨i, j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩
      · exact (hu i).2
      · exact (hl (Sum.inl (i, j))).2
      · exact (hl (Sum.inr (Sum.inl (i, j)))).2
      · exact (hl (Sum.inr (Sum.inr j))).2
    · intro l
      rcases l with ⟨i, j⟩ | (⟨i, j⟩ | j)
      · exact (hl (Sum.inl (i, j))).1
      · exact (hl (Sum.inr (Sum.inl (i, j)))).1
      · exact (hl (Sum.inr (Sum.inr j))).1

def coreFiberEquiv {q p : ℕ} (C : Finset (Fin q)) (dz : Bool) :
    ZeroFiber (arrow q p) (coreDelete C dz) ≃
      {cf : CoreState q × (LeafLabel q p → Option (Fin 2)) //
        coreAllowed C dz cf.1 ∧ ∀ l, leafAllowed cf.1 l (cf.2 l)} where
  toFun f := ⟨disassemble f.1.1, by
    apply (assemble_condition_iff C dz _ _).mp
    rw [assemble_disassemble]
    exact ⟨f.1.2, f.2⟩⟩
  invFun cf := ⟨⟨assemble cf.1.1 cf.1.2,
    ((assemble_condition_iff C dz _ _).mpr cf.2).1⟩,
    ((assemble_condition_iff C dz _ _).mpr cf.2).2⟩
  left_inv f := Subtype.ext (Subtype.ext (assemble_disassemble f.1.1))
  right_inv cf := Subtype.ext (disassemble_assemble cf.1.1 cf.1.2)

open Classical in
private theorem card_core_leaf_choices {κ ι β : Type*}
    [Fintype κ] [Fintype ι] [Fintype β]
    (P : κ → Prop) (Q : κ → ι → β → Prop) :
    Nat.card {cf : κ × (ι → β) // P cf.1 ∧ ∀ i, Q cf.1 i (cf.2 i)} =
      ∑ c : κ, if P c then ∏ i : ι, Nat.card {b : β // Q c i b} else 0 := by
  classical
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype
    (fun (c : κ) (f : ι → β) => P c ∧ ∀ i, Q c i (f i))), Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro c _
  by_cases hc : P c
  · simp only [hc, true_and, ite_true]
    exact (Nat.card_congr (Equiv.subtypePiEquivPi)).trans Nat.card_pi
  · simp [hc]

open Classical in
/-- Actual induced-deletion cardinality as a finite core sum of independent
leaf products. This statement has no core-count formula as a hypothesis. -/
theorem omega_coreDelete_eq_core_sum (q p : ℕ) (C : Finset (Fin q)) (dz : Bool) :
    omegaCount (arrow q p) (coreDelete C dz) =
      ∑ c : CoreState q, if coreAllowed C dz c then
        ∏ l : LeafLabel q p, Nat.card {b : Option (Fin 2) // leafAllowed c l b}
      else 0 := by
  classical
  rw [← zeroFiber_card, Nat.card_congr (coreFiberEquiv C dz)]
  exact card_core_leaf_choices (coreAllowed C dz) (fun c => leafAllowed c)


end FormalProof.Research003.RS42FixedK
