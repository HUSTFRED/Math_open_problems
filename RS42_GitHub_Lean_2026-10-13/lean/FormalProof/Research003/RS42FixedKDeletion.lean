module

public import FormalProof.Research003.RS42Counterexample90
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Logic.Equiv.Basic

set_option linter.style.header false
set_option linter.hashCommand false

/-!
The deletion identity for arbitrary finite matching-block split graphs.
The arrows in the deletion graph are precisely the original arrows whose two
endpoints survive. No transitive closure or inherited path constraint is used.
This module contains no numerical enumeration or parameter-family assumption.
-/

@[expose] public section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

namespace FormalProof.Research003.RS42FixedKDeletion

open FormalProof.Research003.RS42Counterexample90
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def zeroSet (f : State ι) : Finset ι :=
  Finset.univ.filter fun i => f i = none

@[simp] theorem mem_zeroSet (f : State ι) (i : ι) :
    i ∈ zeroSet f ↔ f i = none := by
  simp [zeroSet]

abbrev Remaining (Z : Finset ι) := {i : ι // i ∉ Z}

/-- The arrow relation restricted to the vertices remaining after deletion. -/
def deletionLegal (arrow : ι → ι → Prop) (Z : Finset ι)
    (g : Remaining Z → Fin 2) : Prop :=
  ∀ i j : Remaining Z, arrow i.1 j.1 → ¬ (g i = 0 ∧ g j = 1)

def extend (Z : Finset ι) (g : Remaining Z → Fin 2) : State ι :=
  fun i => if h : i ∈ Z then none else some (g ⟨i, h⟩)

@[simp] theorem extend_of_mem (Z : Finset ι) (g : Remaining Z → Fin 2)
    (i : ι) (hi : i ∈ Z) : extend Z g i = none := by
  simp [extend, hi]

@[simp] theorem extend_of_not_mem (Z : Finset ι) (g : Remaining Z → Fin 2)
    (i : ι) (hi : i ∉ Z) : extend Z g i = some (g ⟨i, hi⟩) := by
  simp [extend, hi]

@[simp] theorem zeroSet_extend (Z : Finset ι) (g : Remaining Z → Fin 2) :
    zeroSet (extend Z g) = Z := by
  ext i
  by_cases hi : i ∈ Z <;> simp [hi, extend]

theorem legal_extend_iff (arrow : ι → ι → Prop) (Z : Finset ι)
    (g : Remaining Z → Fin 2) :
    legal arrow (extend Z g) ↔ deletionLegal arrow Z g := by
  constructor
  · intro h i j hij hg
    apply h i.1 j.1 hij
    constructor
    · simpa [extend, i.2] using congrArg some hg.1
    · simpa [extend, j.2] using congrArg some hg.2
  · intro h i j hij hf
    have hi : i ∉ Z := by
      intro hi
      simpa [extend, hi] using hf.1
    have hj : j ∉ Z := by
      intro hj
      simpa [extend, hj] using hf.2
    apply h ⟨i, hi⟩ ⟨j, hj⟩ hij
    constructor
    · simpa [extend, hi] using hf.1
    · simpa [extend, hj] using hf.2

private theorem some_getD (a : Option (Fin 2)) (ha : a ≠ none) :
    some (a.getD 0) = a := by
  cases a with
  | none => exact False.elim (ha rfl)
  | some b => rfl

abbrev LegalState (arrow : ι → ι → Prop) := {f : State ι // legal arrow f}

abbrev ZeroFiber (arrow : ι → ι → Prop) (Z : Finset ι) :=
  {f : LegalState arrow // zeroSet f.1 = Z}

def restrict (Z : Finset ι) (f : State ι) : Remaining Z → Fin 2 :=
  fun i => (f i.1).getD 0

theorem some_restrict (Z : Finset ι) (f : State ι)
    (hf : zeroSet f = Z) (i : Remaining Z) :
    some (restrict Z f i) = f i.1 := by
  apply some_getD
  intro hi
  apply i.2
  exact (Finset.ext_iff.mp hf i.1).mp ((mem_zeroSet f i.1).mpr hi)

theorem restrict_legal (arrow : ι → ι → Prop) (Z : Finset ι)
    (f : ZeroFiber arrow Z) : deletionLegal arrow Z (restrict Z f.1.1) := by
  intro i j hij hg
  apply f.1.2 i.1 j.1 hij
  constructor
  · exact (some_restrict Z f.1.1 f.2 i).symm.trans (congrArg some hg.1)
  · exact (some_restrict Z f.1.1 f.2 j).symm.trans (congrArg some hg.2)

theorem extend_restrict (Z : Finset ι) (f : State ι)
    (hf : zeroSet f = Z) : extend Z (restrict Z f) = f := by
  funext i
  by_cases hi : i ∈ Z
  · rw [extend_of_mem Z _ i hi]
    apply Eq.symm
    apply (mem_zeroSet f i).mp
    simpa [hf] using hi
  · rw [extend_of_not_mem Z _ i hi]
    exact some_restrict Z f hf ⟨i, hi⟩

theorem restrict_extend (Z : Finset ι) (g : Remaining Z → Fin 2) :
    restrict Z (extend Z g) = g := by
  funext i
  simp [restrict, extend, i.2]

/-- Fixed-zero-set legal three-state assignments are exactly legal two-state
assignments on the induced deletion graph. -/
def zeroFiberEquiv (arrow : ι → ι → Prop) (Z : Finset ι) :
    ZeroFiber arrow Z ≃ {g : Remaining Z → Fin 2 // deletionLegal arrow Z g} where
  toFun f := ⟨restrict Z f.1.1, restrict_legal arrow Z f⟩
  invFun g := ⟨⟨extend Z g.1, (legal_extend_iff arrow Z g.1).mpr g.2⟩,
    zeroSet_extend Z g.1⟩
  left_inv f := Subtype.ext (Subtype.ext (extend_restrict Z f.1.1 f.2))
  right_inv g := Subtype.ext (restrict_extend Z g.1)

/-- The actual two-state assignment count on the induced deletion graph. -/
noncomputable def omegaCount (arrow : ι → ι → Prop) (Z : Finset ι) : ℕ :=
  Nat.card {g : Remaining Z → Fin 2 // deletionLegal arrow Z g}

theorem zeroFiber_card (arrow : ι → ι → Prop) (Z : Finset ι) :
    Nat.card (ZeroFiber arrow Z) = omegaCount arrow Z :=
  Nat.card_congr (zeroFiberEquiv arrow Z)

theorem selected_card_add_zeroSet_card (f : State ι) :
    (selected f).card + (zeroSet f).card = Fintype.card ι := by
  classical
  have hinj : Set.InjOn Prod.fst (selected f : Set (Vertex ι)) := by
    intro v hv w hw h
    apply Prod.ext h
    apply Option.some.inj
    exact ((mem_selected f v).mp hv).symm.trans
      ((congrArg f h).trans ((mem_selected f w).mp hw))
  have himage : (selected f).image Prod.fst =
      Finset.univ.filter (fun i => f i ≠ none) := by
    ext i
    constructor
    · intro hi
      obtain ⟨⟨j, b⟩, hj, hji⟩ := Finset.mem_image.mp hi
      have hj' := (mem_selected f (j, b)).mp hj
      change j = i at hji
      subst j
      simp [hj']
    · intro hi
      have hn : f i ≠ none := (Finset.mem_filter.mp hi).2
      cases hf : f i with
      | none => exact False.elim (hn hf)
      | some b =>
        exact Finset.mem_image.mpr ⟨(i, b), (mem_selected f (i, b)).mpr hf, rfl⟩
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset ι)) (fun i => f i = none)
  -- Use the image equality only through cardinalities.
  have heq : (selected f).card =
      (Finset.univ.filter (fun i => f i ≠ none)).card := by
    calc
      _ = ((selected f).image Prod.fst).card := (Finset.card_image_iff.mpr hinj).symm
      _ = _ := congrArg Finset.card himage
  rw [heq]
  simpa [zeroSet, Nat.add_comm] using hcard

/-- Fiber decomposition by the number of empty blocks. -/
noncomputable def zeroStratumEquiv (arrow : ι → ι → Prop) (r : ℕ) :
    {f : LegalState arrow // (zeroSet f.1).card = r} ≃
      Σ Z : {Z : Finset ι // Z.card = r},
        {g : Remaining Z.1 → Fin 2 // deletionLegal arrow Z.1 g} :=
  (Equiv.sigmaSubtypeFiberEquivSubtype
    (fun f : LegalState arrow => zeroSet f.1)
    (p := fun f => (zeroSet f.1).card = r)
    (q := fun Z => Z.card = r) (fun _ => Iff.rfl)).symm.trans
      (Equiv.sigmaCongrRight fun Z => zeroFiberEquiv arrow Z.1)

theorem zeroStratum_card (arrow : ι → ι → Prop) (r : ℕ) :
    Nat.card {f : LegalState arrow // (zeroSet f.1).card = r} =
      ∑ Z : {Z : Finset ι // Z.card = r}, omegaCount arrow Z.1 := by
  classical
  simpa only [Nat.card_sigma, omegaCount] using Nat.card_congr (zeroStratumEquiv arrow r)

/-- The matching-block coefficient is the sum of induced-deletion assignment
counts. The bound on r is essential because natural subtraction truncates. -/
theorem coefficient_splitGraph_deletion_sum (arrow : ι → ι → Prop) (r : ℕ)
    (hr : r ≤ Fintype.card ι) :
    coefficient (splitGraph arrow) (Fintype.card ι - r) =
      ∑ Z : {Z : Finset ι // Z.card = r}, omegaCount arrow Z.1 := by
  classical
  rw [coefficient_splitGraph]
  have e : {f : State ι // legal arrow f ∧ (selected f).card = Fintype.card ι - r} ≃
      {f : LegalState arrow // (zeroSet f.1).card = r} :=
    { toFun := fun f => ⟨⟨f.1, f.2.1⟩, by
        have h := selected_card_add_zeroSet_card f.1
        have hsize := f.2.2
        change (zeroSet f.1).card = r
        omega⟩
      invFun := fun f => ⟨f.1.1, f.1.2, by
        have h := selected_card_add_zeroSet_card f.1.1
        have hzero := f.2
        omega⟩
      left_inv := fun _ => Subtype.ext rfl
      right_inv := fun _ => Subtype.ext (Subtype.ext rfl) }
  exact (Nat.card_congr e).trans (zeroStratum_card arrow r)


end FormalProof.Research003.RS42FixedKDeletion
