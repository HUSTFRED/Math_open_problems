module

public import FormalProof.Research003.RS42FixedKBridge
public import FormalProof.Research003.RS42FixedKDeletion

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false

/-!
Safe extension across deleted original leaves.
The comparison concerns actual two-state assignment sets on induced deletions.
It does not assert monotonicity for deletion of arbitrary core vertices.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42FixedKDeletion

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Restore the vertices in D using fixed safe signs; keep all other values. -/
def restoreSafe (C D : Finset ι) (safe : ι → Fin 2)
    (f : Remaining (C ∪ D) → Fin 2) : Remaining C → Fin 2 :=
  fun i => if hd : i.1 ∈ D then safe i.1 else
    f ⟨i.1, fun h => (Finset.mem_union.mp h).elim i.2 hd⟩

theorem restoreSafe_legal (arrow : ι → ι → Prop) (C D : Finset ι)
    (safe : ι → Fin 2)
    (hsource : ∀ i, i ∈ D → ∀ j, arrow i j → safe i ≠ 0)
    (htarget : ∀ j, j ∈ D → ∀ i, arrow i j → safe j ≠ 1)
    (f : Remaining (C ∪ D) → Fin 2) (hf : deletionLegal arrow (C ∪ D) f) :
    deletionLegal arrow C (restoreSafe C D safe f) := by
  intro i j hij hbad
  by_cases hi : i.1 ∈ D
  · apply hsource i.1 hi j.1 hij
    simpa [restoreSafe, hi] using hbad.1
  · by_cases hj : j.1 ∈ D
    · apply htarget j.1 hj i.1 hij
      simpa [restoreSafe, hj] using hbad.2
    · have hi' : i.1 ∉ C ∪ D := fun h => (Finset.mem_union.mp h).elim i.2 hi
      have hj' : j.1 ∉ C ∪ D := fun h => (Finset.mem_union.mp h).elim j.2 hj
      apply hf ⟨i.1, hi'⟩ ⟨j.1, hj'⟩ hij
      constructor
      · simpa [restoreSafe, hi] using hbad.1
      · simpa [restoreSafe, hj] using hbad.2

theorem restoreSafe_injective (C D : Finset ι) (safe : ι → Fin 2) :
    Function.Injective (restoreSafe C D safe) := by
  intro f g h
  funext i
  have hiC : i.1 ∉ C := fun hc => i.2 (Finset.mem_union.mpr (Or.inl hc))
  have hiD : i.1 ∉ D := fun hd => i.2 (Finset.mem_union.mpr (Or.inr hd))
  have he := congrFun h (⟨i.1, hiC⟩ : Remaining C)
  simpa [restoreSafe, hiD] using he

/-- A sufficient condition for deletion to decrease the assignment count:
each restored vertex admits a fixed sign safe at every incident arrow. -/
theorem omegaCount_union_le_of_safe (arrow : ι → ι → Prop) (C D : Finset ι)
    (safe : ι → Fin 2)
    (hsource : ∀ i, i ∈ D → ∀ j, arrow i j → safe i ≠ 0)
    (htarget : ∀ j, j ∈ D → ∀ i, arrow i j → safe j ≠ 1) :
    omegaCount arrow (C ∪ D) ≤ omegaCount arrow C := by
  let e : {f : Remaining (C ∪ D) → Fin 2 // deletionLegal arrow (C ∪ D) f} →
      {f : Remaining C → Fin 2 // deletionLegal arrow C f} :=
    fun f => ⟨restoreSafe C D safe f.1,
      restoreSafe_legal arrow C D safe hsource htarget f.1 f.2⟩
  apply Nat.card_le_card_of_injective e
  intro f g h
  apply Subtype.ext
  apply restoreSafe_injective C D safe
  exact congrArg Subtype.val h

end FormalProof.Research003.RS42FixedKDeletion

namespace FormalProof.Research003.RS42FixedK

open RS42FixedKDeletion

/-- The original noncore labels, before any induced deletion is taken. -/
def IsOriginalLeaf {q p : ℕ} : Label q p → Prop
  | Sum.inl _ => False
  | Sum.inr _ => True

/-- Incoming leaves are restored with sign 1; outgoing leaves with sign 0. -/
def safeLeafSign {q p : ℕ} : Label q p → Fin 2
  | Sum.inr (Sum.inr (Sum.inl _)) => 1
  | _ => 0

theorem safeLeafSign_source {q p : ℕ} (v w : Label q p)
    (hv : IsOriginalLeaf v) (h : arrow q p v w) : safeLeafSign v ≠ 0 := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ <;>
    simp_all [IsOriginalLeaf, safeLeafSign, u, z, inLeaf]

theorem safeLeafSign_target {q p : ℕ} (v w : Label q p)
    (hw : IsOriginalLeaf w) (h : arrow q p v w) : safeLeafSign w ≠ 1 := by
  rcases h with ⟨i, rfl, rfl⟩ | ⟨i, j, rfl, rfl⟩ |
    ⟨i, j, rfl, rfl⟩ | ⟨j, rfl, rfl⟩ <;>
    simp_all [IsOriginalLeaf, safeLeafSign, u, z, outLeaf, zLeaf]

/-- Original leaves can be deleted without increasing the assignment count,
after any prior deletion C. No restriction on C is needed. -/
theorem omegaCount_delete_original_leaves (q p : ℕ) (C D : Finset (Label q p))
    (hD : ∀ v, v ∈ D → IsOriginalLeaf v) :
    omegaCount (arrow q p) (C ∪ D) ≤ omegaCount (arrow q p) C := by
  apply omegaCount_union_le_of_safe (arrow q p) C D safeLeafSign
  · intro v hv w h
    exact safeLeafSign_source v w (hD v hv) h
  · intro w hw v h
    exact safeLeafSign_target v w (hD w hw) h

noncomputable def coreDeletion {q p : ℕ} (Z : Finset (Label q p)) :
    Finset (Label q p) := by
  classical
  exact Z.filter fun v => ¬ IsOriginalLeaf v

noncomputable def leafDeletion {q p : ℕ} (Z : Finset (Label q p)) :
    Finset (Label q p) := by
  classical
  exact Z.filter IsOriginalLeaf

theorem coreDeletion_union_leafDeletion {q p : ℕ} (Z : Finset (Label q p)) :
    coreDeletion Z ∪ leafDeletion Z = Z := by
  classical
  ext v
  by_cases hv : IsOriginalLeaf v <;> simp [coreDeletion, leafDeletion, hv]

theorem coreDeletion_card_le {q p : ℕ} (Z : Finset (Label q p)) :
    (coreDeletion Z).card ≤ Z.card := by
  classical
  exact Finset.card_le_card (Finset.filter_subset _ _)

/-- For any mixed deletion, restore its original leaves and retain exactly its
deleted core labels. This is the comparison required before the core bound. -/
theorem omegaCount_le_coreDeletion {q p : ℕ} (Z : Finset (Label q p)) :
    omegaCount (arrow q p) Z ≤ omegaCount (arrow q p) (coreDeletion Z) := by
  have h := omegaCount_delete_original_leaves q p (coreDeletion Z) (leafDeletion Z)
    (by
      intro v hv
      classical
      exact (Finset.mem_filter.mp hv).2)
  simpa only [coreDeletion_union_leafDeletion] using h


end FormalProof.Research003.RS42FixedK
