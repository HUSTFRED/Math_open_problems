module

public import FormalProof.Research003.RS42FixedKDeletion
public import FormalProof.Research003.RS42FixedKLeaf

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false

/-! General deletion-loss bound for arbitrary finite directed relations.
This is a proved intermediate bridge, not the full structural criterion. -/

@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Structural
open RS42FixedKDeletion
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def restrictDeletion (C D : Finset ι) (f : Remaining C → Fin 2) :
    Remaining (C ∪ D) → Fin 2 :=
  fun i => f ⟨i.1, fun h => i.2 (Finset.mem_union.mpr (Or.inl h))⟩

theorem restrictDeletion_legal (arrow : ι → ι → Prop) (C D : Finset ι)
    (f : Remaining C → Fin 2) (hf : deletionLegal arrow C f) :
    deletionLegal arrow (C ∪ D) (restrictDeletion C D f) := by
  intro i j hij hbad
  exact hf _ _ hij hbad

def removedSigns (C D : Finset ι) (f : Remaining C → Fin 2) : D → Fin 2 :=
  fun i => if h : i.1 ∈ C then 0 else f ⟨i.1, h⟩

theorem restrict_removed_injective (C D : Finset ι) :
    Function.Injective (fun f : Remaining C → Fin 2 =>
      (restrictDeletion C D f, removedSigns C D f)) := by
  intro f g h
  funext i
  by_cases hi : i.1 ∈ D
  · have hh := congrFun (congrArg Prod.snd h) (⟨i.1, hi⟩ : D)
    simpa [removedSigns, i.2] using hh
  · have hh := congrFun (congrArg Prod.fst h)
      (⟨i.1, fun hu => (Finset.mem_union.mp hu).elim i.2 hi⟩ : Remaining (C ∪ D))
    exact hh

/-- Deleting D loses at most one factor 2 per removed label, with NO condition
on the arrows or on whether the labels are leaves. -/
theorem omegaCount_le_pow_card_mul (arrow : ι → ι → Prop) (C D : Finset ι) :
    omegaCount arrow C ≤ 2 ^ D.card * omegaCount arrow (C ∪ D) := by
  classical
  let e : {f : Remaining C → Fin 2 // deletionLegal arrow C f} →
      {f : Remaining (C ∪ D) → Fin 2 // deletionLegal arrow (C ∪ D) f} ×
        (D → Fin 2) :=
    fun f => (⟨restrictDeletion C D f.1, restrictDeletion_legal arrow C D f.1 f.2⟩,
      removedSigns C D f.1)
  have he : Function.Injective e := by
    intro f g h
    apply Subtype.ext
    apply restrict_removed_injective C D
    have h₁ : restrictDeletion C D f.1 = restrictDeletion C D g.1 :=
      congrArg (fun x => x.1.1) h
    have h₂ : removedSigns C D f.1 = removedSigns C D g.1 :=
      congrArg (fun x => x.2) h
    exact Prod.ext h₁ h₂
  have hc := Nat.card_le_card_of_injective e he
  simpa [omegaCount, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card,
    mul_comm] using hc

/-- Sharper loss bound counts only newly deleted labels. -/
theorem omegaCount_le_pow_sdiff_mul (arrow : ι → ι → Prop) (C D : Finset ι) :
    omegaCount arrow C ≤ 2 ^ (D \ C).card * omegaCount arrow (C ∪ D) := by
  have h := omegaCount_le_pow_card_mul arrow C (D \ C)
  have hu : C ∪ (D \ C) = C ∪ D := by
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  simpa only [hu] using h

end FormalProof.Research003.RS42Structural
