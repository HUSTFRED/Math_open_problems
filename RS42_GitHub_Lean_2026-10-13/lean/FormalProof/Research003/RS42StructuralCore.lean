module

public import FormalProof.Research003.RS42FixedKCoreEvaluate
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Logic.Equiv.Prod
public meta import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false

/-!
Generic core with arbitrary linear outgoing/incoming leaf
multiplicities. The exact exponent formula is derived from a genuine zero-fiber
equivalence. No treehood or coefficient estimate is an assumption of the count.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural

open RS42Counterexample90 (State legal)
open RS42FixedKDeletion
open RS42FixedK (outWeight inWeight outgoing_leaf_card incoming_leaf_card)
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- All leaves have fresh dependent labels; the left summand is outgoing. -/
abbrev StructuralLeaf (a b : V → ℕ) (p : ℕ) :=
  Σ v : V, Fin (a v * p) ⊕ Fin (b v * p)

abbrev StructuralLabel (a b : V → ℕ) (p : ℕ) :=
  V ⊕ StructuralLeaf a b p

def structuralArrow (coreArrow : V → V → Prop) (a b : V → ℕ) (p : ℕ) :
    StructuralLabel a b p → StructuralLabel a b p → Prop
  | Sum.inl v, Sum.inl w => coreArrow v w
  | Sum.inl v, Sum.inr ⟨w, Sum.inl _⟩ => v = w
  | Sum.inr ⟨v, Sum.inr _⟩, Sum.inl w => v = w
  | _, _ => False

noncomputable def coreDelete (a b : V → ℕ) (p : ℕ) (C : Finset V) :
    Finset (StructuralLabel a b p) := by
  classical
  exact C.image Sum.inl

@[simp] theorem mem_coreDelete_core (a b : V → ℕ) (p : ℕ)
    (C : Finset V) (v : V) :
    Sum.inl v ∈ coreDelete a b p C ↔ v ∈ C := by
  classical
  simp [coreDelete]

@[simp] theorem not_mem_coreDelete_leaf (a b : V → ℕ) (p : ℕ)
    (C : Finset V) (l : StructuralLeaf a b p) :
    Sum.inr l ∉ coreDelete a b p C := by
  classical
  simp [coreDelete]

theorem coreDelete_card (a b : V → ℕ) (p : ℕ) (C : Finset V) :
    (coreDelete a b p C).card = C.card := by
  classical
  exact Finset.card_image_of_injective C Sum.inl_injective

def structuralAssemble (a b : V → ℕ) (p : ℕ)
    (c : State V) (f : StructuralLeaf a b p → Option (Fin 2)) :
    State (StructuralLabel a b p)
  | Sum.inl v => c v
  | Sum.inr l => f l

def structuralDisassemble (a b : V → ℕ) (p : ℕ)
    (f : State (StructuralLabel a b p)) :
    State V × (StructuralLeaf a b p → Option (Fin 2)) :=
  ((fun v => f (Sum.inl v)), fun l => f (Sum.inr l))

theorem structuralAssemble_disassemble (a b : V → ℕ) (p : ℕ)
    (f : State (StructuralLabel a b p)) :
    structuralAssemble a b p (structuralDisassemble a b p f).1
      (structuralDisassemble a b p f).2 = f := by
  funext v
  cases v <;> rfl

theorem structuralDisassemble_assemble (a b : V → ℕ) (p : ℕ)
    (c : State V) (f : StructuralLeaf a b p → Option (Fin 2)) :
    structuralDisassemble a b p (structuralAssemble a b p c f) = (c, f) := rfl

def structuralLeafAllowed (a b : V → ℕ) (p : ℕ) (c : State V) :
    StructuralLeaf a b p → Option (Fin 2) → Prop
  | ⟨v, Sum.inl _⟩, s => s ≠ none ∧ ¬ (c v = some 0 ∧ s = some 1)
  | ⟨v, Sum.inr _⟩, s => s ≠ none ∧ ¬ (s = some 0 ∧ c v = some 1)

theorem structural_zero_iff (a b : V → ℕ) (p : ℕ) (C : Finset V)
    (c : State V) (f : StructuralLeaf a b p → Option (Fin 2)) :
    zeroSet (structuralAssemble a b p c f) = coreDelete a b p C ↔
      zeroSet c = C ∧ ∀ l, f l ≠ none := by
  constructor
  · intro h
    constructor
    · ext v
      have hv := Finset.ext_iff.mp h (Sum.inl v)
      simpa only [mem_zeroSet, structuralAssemble, mem_coreDelete_core] using hv
    · intro l
      have hl := Finset.ext_iff.mp h (Sum.inr l)
      simpa only [mem_zeroSet, structuralAssemble, not_mem_coreDelete_leaf, iff_false]
        using hl
  · rintro ⟨hc, hf⟩
    ext v
    cases v with
    | inl v =>
      simpa only [mem_zeroSet, structuralAssemble, mem_coreDelete_core] using
        Finset.ext_iff.mp hc v
    | inr l =>
      simpa only [mem_zeroSet, structuralAssemble, not_mem_coreDelete_leaf, iff_false]
        using hf l

theorem structural_condition_iff (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (C : Finset V)
    (c : State V) (f : StructuralLeaf a b p → Option (Fin 2)) :
    legal (structuralArrow coreArrow a b p) (structuralAssemble a b p c f) ∧
        zeroSet (structuralAssemble a b p c f) = coreDelete a b p C ↔
      (legal coreArrow c ∧ zeroSet c = C) ∧
        ∀ l, structuralLeafAllowed a b p c l (f l) := by
  rw [structural_zero_iff]
  constructor
  · rintro ⟨hleg, hc, hf⟩
    refine ⟨⟨?_, hc⟩, ?_⟩
    · intro v w h
      exact hleg (Sum.inl v) (Sum.inl w) h
    · rintro ⟨v, j | j⟩
      · exact ⟨hf _, hleg (Sum.inl v) (Sum.inr ⟨v, Sum.inl j⟩) rfl⟩
      · exact ⟨hf _, hleg (Sum.inr ⟨v, Sum.inr j⟩) (Sum.inl v) rfl⟩
  · rintro ⟨⟨hcleg, hczero⟩, hf⟩
    refine ⟨?_, hczero, ?_⟩
    · intro v w h
      rcases v with v | ⟨v, j | j⟩ <;>
        rcases w with w | ⟨w, k | k⟩
      · exact hcleg v w h
      · change v = w at h
        subst w
        exact (hf ⟨v, Sum.inl k⟩).2
      · exact False.elim h
      · exact False.elim h
      · exact False.elim h
      · exact False.elim h
      · change v = w at h
        subst w
        exact (hf ⟨v, Sum.inr j⟩).2
      · exact False.elim h
      · exact False.elim h
    · rintro ⟨v, j | j⟩
      · exact (hf ⟨v, Sum.inl j⟩).1
      · exact (hf ⟨v, Sum.inr j⟩).1

/-- Actual graph zero fibers, separated into a legal retained core and all
independent original-leaf choices. The core fiber fixes exactly C as its zeros. -/
def structuralCoreFiberEquiv (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (C : Finset V) :
    ZeroFiber (structuralArrow coreArrow a b p) (coreDelete a b p C) ≃
      Σ c : ZeroFiber coreArrow C,
        {f : StructuralLeaf a b p → Option (Fin 2) //
          ∀ l, structuralLeafAllowed a b p c.1.1 l (f l)} where
  toFun s := by
    let cf := structuralDisassemble a b p s.1.1
    have h : (legal coreArrow cf.1 ∧ zeroSet cf.1 = C) ∧
        ∀ l, structuralLeafAllowed a b p cf.1 l (cf.2 l) := by
      apply (structural_condition_iff coreArrow a b p C cf.1 cf.2).mp
      change legal (structuralArrow coreArrow a b p)
          (structuralAssemble a b p (structuralDisassemble a b p s.1.1).1
            (structuralDisassemble a b p s.1.1).2) ∧ _
      rw [structuralAssemble_disassemble]
      exact ⟨s.1.2, s.2⟩
    exact ⟨⟨⟨cf.1, h.1.1⟩, h.1.2⟩, ⟨cf.2, h.2⟩⟩
  invFun cf := by
    have h := (structural_condition_iff coreArrow a b p C cf.1.1.1 cf.2.1).mpr
      ⟨⟨cf.1.1.2, cf.1.2⟩, cf.2.2⟩
    exact ⟨⟨structuralAssemble a b p cf.1.1.1 cf.2.1, h.1⟩, h.2⟩
  left_inv s := Subtype.ext (Subtype.ext (structuralAssemble_disassemble a b p s.1.1))
  right_inv cf := by
    rcases cf with ⟨⟨⟨c, hc⟩, hcz⟩, ⟨f, hf⟩⟩
    rfl

open Classical in
theorem omega_coreDelete_eq_leaf_product (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (C : Finset V) :
    omegaCount (structuralArrow coreArrow a b p) (coreDelete a b p C) =
      ∑ c : ZeroFiber coreArrow C,
        ∏ l : StructuralLeaf a b p,
          Nat.card {s : Option (Fin 2) // structuralLeafAllowed a b p c.1.1 l s} := by
  classical
  rw [← zeroFiber_card, Nat.card_congr (structuralCoreFiberEquiv coreArrow a b p C),
    Nat.card_sigma]
  apply Finset.sum_congr rfl
  intro c _
  exact (Nat.card_congr Equiv.subtypePiEquivPi).trans Nat.card_pi

def localExponent (av bv : ℕ) (s : Option (Fin 2)) : ℕ :=
  if s = none then av + bv else if s = some 0 then bv else av

def structuralExponent (a b : V → ℕ) (c : State V) : ℕ :=
  ∑ v : V, localExponent (a v) (b v) (c v)

theorem structural_leaf_card_out (a b : V → ℕ) (p : ℕ) (c : State V)
    (v : V) (j : Fin (a v * p)) :
    Nat.card {s : Option (Fin 2) //
      structuralLeafAllowed a b p c ⟨v, Sum.inl j⟩ s} = outWeight (c v) :=
  outgoing_leaf_card (c v)

theorem structural_leaf_card_in (a b : V → ℕ) (p : ℕ) (c : State V)
    (v : V) (j : Fin (b v * p)) :
    Nat.card {s : Option (Fin 2) //
      structuralLeafAllowed a b p c ⟨v, Sum.inr j⟩ s} = inWeight (c v) :=
  incoming_leaf_card (c v)

theorem local_leaf_weights (av bv p : ℕ) (s : Option (Fin 2)) :
    outWeight s ^ (av * p) * inWeight s ^ (bv * p) =
      2 ^ (p * localExponent av bv s) := by
  cases s with
  | none =>
    simp only [outWeight, inWeight, localExponent, reduceCtorEq, ite_false, ite_true]
    rw [← pow_add]
    congr 1
    ring
  | some s =>
    fin_cases s <;> simp [outWeight, inWeight, localExponent, Nat.mul_comm]

theorem structural_leaf_product_eq_power (a b : V → ℕ) (p : ℕ) (c : State V) :
    (∏ l : StructuralLeaf a b p,
      Nat.card {s : Option (Fin 2) // structuralLeafAllowed a b p c l s}) =
        2 ^ (p * structuralExponent a b c) := by
  classical
  simp only [Fintype.prod_sigma, Fintype.prod_sum_type,
    structural_leaf_card_out, structural_leaf_card_in, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  simp_rw [local_leaf_weights]
  rw [Finset.prod_pow_eq_pow_sum]
  simp only [structuralExponent, Finset.mul_sum]

open Classical in
/-- Exact exponent formula, indexing core assignments by their zero fiber. -/
theorem omega_coreDelete_eq_zeroFiber_exponent_sum (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (C : Finset V) :
    omegaCount (structuralArrow coreArrow a b p) (coreDelete a b p C) =
      ∑ c : ZeroFiber coreArrow C, 2 ^ (p * structuralExponent a b c.1.1) := by
  rw [omega_coreDelete_eq_leaf_product]
  simp only [structural_leaf_product_eq_power]

/-- The exponent expressed on genuine two-state functions on the retained core. -/
def retainedExponent (a b : V → ℕ) (C : Finset V) (σ : Remaining C → Fin 2) : ℕ :=
  structuralExponent a b (extend C σ)

theorem retainedExponent_eq (a b : V → ℕ) (C : Finset V)
    (σ : Remaining C → Fin 2) :
    retainedExponent a b C σ =
      ∑ v : V, if h : v ∈ C then a v + b v
        else if σ ⟨v, h⟩ = 0 then b v else a v := by
  classical
  unfold retainedExponent structuralExponent
  apply Finset.sum_congr rfl
  intro v _
  by_cases hv : v ∈ C <;> simp [extend, localExponent, hv]

open Classical in
/-- The exact induced core-deletion count: every term is the number of actual
leaf extensions of a legal two-state assignment on the induced retained core. -/
theorem omega_coreDelete_eq_exponent_sum (coreArrow : V → V → Prop)
    (a b : V → ℕ) (p : ℕ) (C : Finset V) :
    omegaCount (structuralArrow coreArrow a b p) (coreDelete a b p C) =
      ∑ σ : {σ : Remaining C → Fin 2 // deletionLegal coreArrow C σ},
        2 ^ (p * retainedExponent a b C σ.1) := by
  classical
  rw [omega_coreDelete_eq_zeroFiber_exponent_sum]
  apply Fintype.sum_equiv (zeroFiberEquiv coreArrow C)
  intro c
  change 2 ^ (p * structuralExponent a b c.1.1) =
    2 ^ (p * structuralExponent a b (extend C (restrict C c.1.1)))
  rw [extend_restrict C c.1.1 c.2]


end FormalProof.Research003.RS42Structural
