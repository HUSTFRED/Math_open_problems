module

public import FormalProof.Research003.RS42StructuralCounts
public import Mathlib.Algebra.BigOperators.Ring.Finset
public meta import Mathlib.Tactic.FinCases

set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.unusedSectionVars false

/-!
An inward core star with arbitrary incoming multiplicities
at least two. This is a specialization of the actual Structural graph and its
core exponent, with no maximum-value or counting inequality assumed.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Structural.Asymmetric

open RS42Counterexample90 (State legal)
open RS42FixedKDeletion
open scoped BigOperators

abbrev Core (q : ℕ) := Fin q ⊕ Unit

def starArrow (q : ℕ) : Core q → Core q → Prop
  | Sum.inl _, Sum.inr _ => True
  | _, _ => False

def outMultiplicity (q : ℕ) : Core q → ℕ := fun _ => 1

def inMultiplicity {q : ℕ} (weights : Fin q → ℕ) : Core q → ℕ
  | Sum.inl i => weights i
  | Sum.inr _ => 0

def totalIncoming {q : ℕ} (weights : Fin q → ℕ) : ℕ := ∑ i, weights i

noncomputable def graph (q p : ℕ) (weights : Fin q → ℕ) :=
  structuralGraph (starArrow q) (outMultiplicity q) (inMultiplicity weights) p

noncomputable def count (q p : ℕ) (weights : Fin q → ℕ) (j : ℕ) : ℕ :=
  structuralIndepCount (starArrow q) (outMultiplicity q) (inMultiplicity weights) p j

def zeroIndicator (s : Option (Fin 2)) : ℕ := if s = none then 1 else 0

def branchWeight (w : ℕ) : Option (Fin 2) → ℕ
  | none => 1 + w
  | some s => if s = 0 then w else 1

def rootWeight : Option (Fin 2) → ℕ
  | none => 1
  | some s => if s = 0 then 0 else 1

def branchZeroCount {q : ℕ} (f : State (Core q)) : ℕ :=
  ∑ i : Fin q, zeroIndicator (f (Sum.inl i))

theorem zero_card_split {q : ℕ} (f : State (Core q)) :
    (zeroSet f).card = branchZeroCount f + zeroIndicator (f (Sum.inr ())) := by
  classical
  have h : (zeroSet f).card = ∑ v : Core q, zeroIndicator (f v) := by
    simp [zeroSet, zeroIndicator]
  rw [h, Fintype.sum_sum_type]
  simp only [Fintype.sum_unique, branchZeroCount]

theorem exponent_split {q : ℕ} (weights : Fin q → ℕ) (f : State (Core q)) :
    coreExponent (outMultiplicity q) (inMultiplicity weights) f =
      (∑ i : Fin q, branchWeight (weights i) (f (Sum.inl i))) +
        rootWeight (f (Sum.inr ())) := by
  unfold coreExponent
  rw [Fintype.sum_sum_type]
  have hunit : (default : Unit) = () := Subsingleton.elim _ _
  simp only [Fintype.sum_unique, outMultiplicity, inMultiplicity, branchWeight, rootWeight,
    Nat.add_zero, hunit]
  rfl

theorem total_mass {q : ℕ} (weights : Fin q → ℕ) :
    (∑ v : Core q, (outMultiplicity q v + inMultiplicity weights v)) =
      totalIncoming weights + q + 1 := by
  simp [Fintype.sum_sum_type, outMultiplicity, inMultiplicity,
    Finset.sum_add_distrib, totalIncoming, Nat.add_comm]
  omega

theorem branchWeight_le (w : ℕ) (hw : 2 ≤ w) (s : Option (Fin 2)) :
    branchWeight w s ≤ w + zeroIndicator s := by
  cases s with
  | none => simp [branchWeight, zeroIndicator, Nat.add_comm]
  | some s =>
    fin_cases s
    · simp [branchWeight, zeroIndicator]
    · simp [branchWeight, zeroIndicator]
      omega

theorem branchWeight_lt_of_minus (w : ℕ) (hw : 2 ≤ w)
    (s : Option (Fin 2)) (hn : s ≠ none) (h0 : s ≠ some 0) :
    branchWeight w s < w + zeroIndicator s := by
  cases s with
  | none => exact False.elim (hn rfl)
  | some s =>
    fin_cases s
    · exact False.elim (h0 rfl)
    · simpa [branchWeight, zeroIndicator] using (show 1 < w by omega)

theorem exists_retained_branch {q : ℕ} (hq : 1 ≤ q) (f : State (Core q))
    (hf : (zeroSet f).card ≤ q - 1) :
    ∃ i : Fin q, f (Sum.inl i) ≠ none := by
  classical
  by_contra h
  push Not at h
  have hb : branchZeroCount f = q := by simp [branchZeroCount, zeroIndicator, h]
  have hz := zero_card_split f
  omega

/-- The only delicate case is root sign 1. There is then a retained branch,
whose forced sign 1 loses at least one exponent unit because its weight is ≥2. -/
theorem exponent_le_totalIncoming_add_zero {q : ℕ} (hq : 1 ≤ q)
    (weights : Fin q → ℕ) (hw : ∀ i, 2 ≤ weights i) (f : State (Core q))
    (hlegal : legal (starArrow q) f) (hzero : (zeroSet f).card ≤ q - 1) :
    coreExponent (outMultiplicity q) (inMultiplicity weights) f ≤
      totalIncoming weights + (zeroSet f).card := by
  classical
  have hpoint : ∀ i : Fin q,
      branchWeight (weights i) (f (Sum.inl i)) ≤
        weights i + zeroIndicator (f (Sum.inl i)) :=
    fun i => branchWeight_le (weights i) (hw i) _
  have hsum : (∑ i : Fin q, branchWeight (weights i) (f (Sum.inl i))) ≤
      totalIncoming weights + branchZeroCount f := by
    simpa only [Finset.sum_add_distrib, totalIncoming, branchZeroCount] using
      Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hpoint i)
  rw [exponent_split, zero_card_split]
  cases hz : f (Sum.inr ()) with
  | none => simpa [rootWeight, zeroIndicator, Nat.add_assoc] using Nat.add_le_add_right hsum 1
  | some s =>
    fin_cases s
    · simpa [rootWeight, zeroIndicator] using hsum
    · obtain ⟨i, hi⟩ := exists_retained_branch hq f hzero
      have h0 : f (Sum.inl i) ≠ some 0 := by
        intro hi0
        exact hlegal (Sum.inl i) (Sum.inr ()) trivial ⟨hi0, hz⟩
      have hstrict : (∑ i : Fin q, branchWeight (weights i) (f (Sum.inl i))) <
          totalIncoming weights + branchZeroCount f := by
        have hh := Finset.sum_lt_sum
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin q))) => hpoint i)
          ⟨i, Finset.mem_univ i,
            branchWeight_lt_of_minus (weights i) (hw i) _ hi h0⟩
        simpa only [Finset.sum_add_distrib, totalIncoming, branchZeroCount] using hh
      simpa [rootWeight, zeroIndicator] using hstrict

def plusWitness {q : ℕ} (C : Finset (Fin q)) : State (Core q)
  | Sum.inl i => if i ∈ C then none else some 0
  | Sum.inr _ => some 0

theorem plusWitness_legal {q : ℕ} (C : Finset (Fin q)) :
    legal (starArrow q) (plusWitness C) := by
  intro v w h hbad
  rcases v with i | t <;> rcases w with j | s
  · exact False.elim h
  · simpa [plusWitness] using hbad.2
  · exact False.elim h
  · exact False.elim h

theorem plusWitness_zero_card {q : ℕ} (C : Finset (Fin q)) :
    (zeroSet (plusWitness C)).card = C.card := by
  rw [zero_card_split]
  simp [branchZeroCount, plusWitness, zeroIndicator]

theorem plusWitness_exponent {q : ℕ} (weights : Fin q → ℕ) (C : Finset (Fin q)) :
    coreExponent (outMultiplicity q) (inMultiplicity weights) (plusWitness C) =
      totalIncoming weights + C.card := by
  rw [exponent_split]
  change (∑ i : Fin q, branchWeight (weights i) (if i ∈ C then none else some 0)) =
    totalIncoming weights + C.card
  calc
    _ = ∑ i : Fin q, (weights i + if i ∈ C then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : i ∈ C <;> simp [hi, branchWeight, Nat.add_comm]
    _ = _ := by simp [Finset.sum_add_distrib, totalIncoming]

/-- Every deletion budget below q has the exact maximum B+r. -/
theorem maxCoreExponent_below (q : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) (r : ℕ) (hr : r ≤ q - 1) :
    maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) r =
      totalIncoming weights + r := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro f hf
    have hf' : legal (starArrow q) f ∧ (zeroSet f).card ≤ r := by
      simpa only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and] using hf
    exact (exponent_le_totalIncoming_add_zero (by omega) weights hw f hf'.1
      (hf'.2.trans hr)).trans (Nat.add_le_add_left hf'.2 _)
  · obtain ⟨C, _, hC⟩ := Finset.exists_subset_card_eq
      (s := (Finset.univ : Finset (Fin q))) (n := r)
      (by simpa only [Finset.card_univ, Fintype.card_fin] using (show r ≤ q by omega))
    have hf : plusWitness C ∈ admissibleCoreStates (starArrow q) r := by
      simp only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨plusWitness_legal C, by rw [plusWitness_zero_card, hC]⟩
    have h := coreExponent_le_max (starArrow q) (outMultiplicity q)
      (inMultiplicity weights) r (plusWitness C) hf
    simpa only [plusWitness_exponent, hC] using h

def allDeletedWitness (q : ℕ) : State (Core q)
  | Sum.inl _ => none
  | Sum.inr _ => some 1

theorem allDeletedWitness_legal (q : ℕ) : legal (starArrow q) (allDeletedWitness q) := by
  intro v w h hbad
  rcases v with i | t <;> rcases w with j | s
  · exact False.elim h
  · simpa [allDeletedWitness] using hbad.1
  · exact False.elim h
  · exact False.elim h

theorem allDeletedWitness_zero_card (q : ℕ) :
    (zeroSet (allDeletedWitness q)).card = q := by
  rw [zero_card_split]
  simp [branchZeroCount, zeroIndicator, allDeletedWitness]

theorem allDeletedWitness_exponent (q : ℕ) (weights : Fin q → ℕ) :
    coreExponent (outMultiplicity q) (inMultiplicity weights) (allDeletedWitness q) =
      totalIncoming weights + q + 1 := by
  rw [exponent_split]
  simp [allDeletedWitness, branchWeight, rootWeight, Finset.sum_add_distrib,
    totalIncoming, Nat.add_comm]

/-- At budget q, deleting all branches and keeping the negative root attains
the entire incoming/outgoing mass. No lower bound on the weights is needed. -/
theorem maxCoreExponent_at_q (q : ℕ) (weights : Fin q → ℕ) :
    maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) q =
      totalIncoming weights + q + 1 := by
  classical
  apply le_antisymm
  · simpa only [total_mass] using
      maxCoreExponent_le_total (starArrow q) (outMultiplicity q) (inMultiplicity weights) q
  · have hf : allDeletedWitness q ∈ admissibleCoreStates (starArrow q) q := by
      simp only [admissibleCoreStates, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨allDeletedWitness_legal q, by rw [allDeletedWitness_zero_card]⟩
    simpa only [allDeletedWitness_exponent] using
      coreExponent_le_max (starArrow q) (outMultiplicity q) (inMultiplicity weights)
        q (allDeletedWitness q) hf

/-- Three exact maxima; their second difference is the integer +1. -/
theorem three_maxima (q : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) :
    maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 2) =
        totalIncoming weights + (q - 2) ∧
      maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 1) =
        totalIncoming weights + (q - 1) ∧
      maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) q =
        totalIncoming weights + q + 1 :=
  ⟨maxCoreExponent_below q hq weights hw (q - 2) (by omega),
    maxCoreExponent_below q hq weights hw (q - 1) le_rfl,
    maxCoreExponent_at_q q weights⟩

theorem exponent_gap_one (q : ℕ) (hq : 2 ≤ q) (weights : Fin q → ℕ)
    (hw : ∀ i, 2 ≤ weights i) :
    maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) (q - 2) +
      maxCoreExponent (starArrow q) (outMultiplicity q) (inMultiplicity weights) q =
      2 * maxCoreExponent (starArrow q) (outMultiplicity q)
        (inMultiplicity weights) (q - 1) + 1 := by
  obtain ⟨hlo, hmid, hhi⟩ := three_maxima q hq weights hw
  rw [hlo, hmid, hhi]
  omega


end FormalProof.Research003.RS42Structural.Asymmetric
