module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.SetTheory.Cardinal.Finite

set_option linter.style.header false

/-!
Matching-block semantics for the fixed 90-vertex Ramos--Sun counterexample.
This file does not assume any coefficient value and does not claim a completed
formal counterexample. The proved interface relates actual independent sets to
legal three-state assignments. Ordinary kernel-checked tactics only.
-/


@[expose] public section

set_option linter.unusedSectionVars false
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

def Independent {V : Type*} (G : SimpleGraph V) (s : Set V) : Prop :=
  s.Pairwise (fun v w => ¬ G.Adj v w)

variable {ι : Type*} [Fintype ι]

/-- Each block has two endpoints, indexed by 0 and 1. -/
abbrev Vertex (ι : Type*) := ι × Fin 2

/-- Splitting an oriented graph into matched pairs: every block has its pair
edge, and an arrow `i → k` adds the edge `(i,0)--(k,1)`. -/
def splitGraph (arrow : ι → ι → Prop) : SimpleGraph (Vertex ι) where
  Adj v w := (v.1 = w.1 ∧ v.2 ≠ w.2) ∨
    (v.2 = 0 ∧ w.2 = 1 ∧ arrow v.1 w.1) ∨
    (v.2 = 1 ∧ w.2 = 0 ∧ arrow w.1 v.1)
  symm := ⟨by
    intro v w h
    rcases h with h | h | h
    · exact Or.inl ⟨h.1.symm, Ne.symm h.2⟩
    · exact Or.inr (Or.inr ⟨h.2.1, h.1, h.2.2⟩)
    · exact Or.inr (Or.inl ⟨h.2.1, h.1, h.2.2⟩)⟩
  loopless := ⟨by
    intro v h
    rcases h with h | h | h
    · exact h.2 rfl
    · exact (by decide : (0 : Fin 2) ≠ 1) (h.1.symm.trans h.2.1)
    · exact (by decide : (1 : Fin 2) ≠ 0) (h.1.symm.trans h.2.1)⟩

/-- `none` is an empty block, and `some b` selects endpoint `b`. -/
abbrev State (ι : Type*) := ι → Option (Fin 2)

def legal (arrow : ι → ι → Prop) (f : State ι) : Prop :=
  ∀ i k, arrow i k → ¬ (f i = some 0 ∧ f k = some 1)

def selected (f : State ι) : Finset (Vertex ι) :=
  Finset.univ.filter fun v => f v.1 = some v.2

@[simp] theorem mem_selected (f : State ι) (v : Vertex ι) :
    v ∈ selected f ↔ f v.1 = some v.2 := by
  simp [selected]

theorem selected_independent_iff (arrow : ι → ι → Prop) (f : State ι) :
    Independent (splitGraph arrow) (selected f : Set (Vertex ι)) ↔ legal arrow f := by
  constructor
  · intro h i k hik ⟨hi, hk⟩
    apply h (x := (i, 0)) (y := (k, 1)) (by simpa using hi) (by simpa using hk)
    · intro heq
      have : (0 : Fin 2) = 1 := congrArg Prod.snd heq
      exact (by decide : (0 : Fin 2) ≠ 1) this
    · exact Or.inr (Or.inl ⟨rfl, rfl, hik⟩)
  · intro h v hv w hw _ hadj
    have hv' := (mem_selected f v).mp hv
    have hw' := (mem_selected f w).mp hw
    rcases hadj with hadj | hadj | hadj
    · apply hadj.2
      exact Option.some.inj (hv'.symm.trans ((congrArg f hadj.1).trans hw'))
    · exact h v.1 w.1 hadj.2.2 ⟨hv'.trans (congrArg some hadj.1),
        hw'.trans (congrArg some hadj.2.1)⟩
    · exact h w.1 v.1 hadj.2.2 ⟨hw'.trans (congrArg some hadj.2.1),
        hv'.trans (congrArg some hadj.1)⟩

variable [DecidableEq ι]

def decode (s : Finset (Vertex ι)) : State ι := fun i =>
  if (i, 0) ∈ s then some 0 else if (i, 1) ∈ s then some 1 else none

theorem decode_selected (f : State ι) : decode (selected f) = f := by
  funext i
  simp only [decode, mem_selected]
  cases h : f i with
  | none => simp
  | some b =>
    have hb : b = 0 ∨ b = 1 := (Fin.forall_fin_two (p := fun a : Fin 2 => a = 0 ∨ a = 1)).mpr
      ⟨Or.inl rfl, Or.inr rfl⟩ b
    rcases hb with rfl | rfl <;> simp

theorem selected_decode (arrow : ι → ι → Prop) (s : Finset (Vertex ι))
    (hs : Independent (splitGraph arrow) (s : Set (Vertex ι))) :
    selected (decode s) = s := by
  ext v
  rcases v with ⟨i, b⟩
  have hn : ¬ ((i, (0 : Fin 2)) ∈ s ∧ (i, (1 : Fin 2)) ∈ s) := by
    rintro ⟨h0, h1⟩
    exact hs h0 h1 (by simp) (Or.inl ⟨rfl, (by decide : (0 : Fin 2) ≠ 1)⟩)
  have hb : b = 0 ∨ b = 1 := (Fin.forall_fin_two (p := fun a : Fin 2 => a = 0 ∨ a = 1)).mpr
      ⟨Or.inl rfl, Or.inr rfl⟩ b
  rcases hb with rfl | rfl <;>
    by_cases h0 : (i, (0 : Fin 2)) ∈ s <;>
    by_cases h1 : (i, (1 : Fin 2)) ∈ s <;> simp_all [mem_selected, decode]

omit [DecidableEq ι] in
theorem independent_card_le (arrow : ι → ι → Prop)
    (s : Finset (Vertex ι))
    (hs : Independent (splitGraph arrow) (s : Set (Vertex ι))) :
    s.card ≤ Fintype.card ι := by
  classical
  have hi : Set.InjOn Prod.fst (s : Set (Vertex ι)) := by
    intro v hv w hw heq
    by_contra hne
    apply hs hv hw hne
    exact Or.inl ⟨heq, fun h => hne (Prod.ext heq h)⟩
  calc
    s.card = (s.image Prod.fst).card := (Finset.card_image_iff.mpr hi).symm
    _ ≤ Fintype.card ι := Finset.card_le_univ _

/-- A genuine bijection between graph-independent finite subsets and legal
three-state assignments. No graph counting oracle is used. -/
noncomputable def independentStateEquiv (arrow : ι → ι → Prop) :
    {s : Finset (Vertex ι) // Independent (splitGraph arrow) (s : Set (Vertex ι))} ≃
      {f : State ι // legal arrow f} where
  toFun s := ⟨decode s.1, by
    apply (selected_independent_iff arrow _).mp
    rw [selected_decode arrow s.1 s.2]
    exact s.2⟩
  invFun f := ⟨selected f.1, (selected_independent_iff arrow f.1).mpr f.2⟩
  left_inv s := Subtype.ext (selected_decode arrow s.1 s.2)
  right_inv f := Subtype.ext (decode_selected f.1)

/-- The true coefficient is the number of independent vertex subsets of size k. -/
noncomputable def coefficient {V : Type*} (G : SimpleGraph V) (k : ℕ) : ℕ :=
  Nat.card {s : Finset V // Independent G (s : Set V) ∧ s.card = k}

noncomputable def independentCardStateEquiv (arrow : ι → ι → Prop) (k : ℕ) :
    {s : Finset (Vertex ι) // Independent (splitGraph arrow) (s : Set (Vertex ι)) ∧
      s.card = k} ≃
    {f : State ι // legal arrow f ∧ (selected f).card = k} where
  toFun s := ⟨decode s.1, by
    refine ⟨?_, ?_⟩
    · apply (selected_independent_iff arrow _).mp
      rw [selected_decode arrow s.1 s.2.1]
      exact s.2.1
    · rw [selected_decode arrow s.1 s.2.1]
      exact s.2.2⟩
  invFun f := ⟨selected f.1,
    (selected_independent_iff arrow f.1).mpr f.2.1, f.2.2⟩
  left_inv s := Subtype.ext (selected_decode arrow s.1 s.2.1)
  right_inv f := Subtype.ext (decode_selected f.1)

omit [DecidableEq ι] in
theorem coefficient_splitGraph (arrow : ι → ι → Prop) (k : ℕ) :
    coefficient (splitGraph arrow) k =
      Nat.card {f : State ι // legal arrow f ∧ (selected f).card = k} := by
  classical
  exact Nat.card_congr (independentCardStateEquiv arrow k)

/-- The actual orientation on the 45 matching blocks for `p=6`. -/
def arrow45 (i k : Fin 45) : Prop :=
  (i = 0 ∧ k = 2) ∨ (i = 1 ∧ k = 2) ∨
  (i = 0 ∧ 3 ≤ k.val ∧ k.val ≤ 8) ∨
  (9 ≤ i.val ∧ i.val ≤ 20 ∧ k = 0) ∨
  (i = 1 ∧ 21 ≤ k.val ∧ k.val ≤ 26) ∨
  (27 ≤ i.val ∧ i.val ≤ 38 ∧ k = 1) ∨
  (i = 2 ∧ 39 ≤ k.val ∧ k.val ≤ 44)

def blockGraph90 : SimpleGraph (Vertex (Fin 45)) := splitGraph arrow45

/-- The certificate's numbering is `2*i + b`. -/
def vertex90Equiv : Vertex (Fin 45) ≃ Fin 90 := finProdFinEquiv

def graph90 : SimpleGraph (Fin 90) where
  Adj v w := blockGraph90.Adj (vertex90Equiv.symm v) (vertex90Equiv.symm w)
  symm := ⟨fun _ _ h => blockGraph90.adj_symm h⟩
  loopless := ⟨fun _ => blockGraph90.irrefl⟩

theorem blockGraph90_independent_card_le (s : Finset (Vertex (Fin 45)))
    (hs : Independent blockGraph90 (s : Set (Vertex (Fin 45)))) : s.card ≤ 45 :=
  independent_card_le arrow45 s hs

def allPlus : Finset (Vertex (Fin 45)) := selected (fun _ => some 0)

theorem allPlus_independent : Independent blockGraph90
    (allPlus : Set (Vertex (Fin 45))) := by
  apply (selected_independent_iff arrow45 _).mpr
  intro i k _ h
  exact (by decide : (some (0 : Fin 2)) ≠ some 1) h.2

theorem allPlus_card : allPlus.card = 45 := by
  have he : allPlus = Finset.univ.image (fun i : Fin 45 => (i, (0 : Fin 2))) := by
    ext ⟨i,b⟩
    simp [allPlus, selected]
  rw [he, Finset.card_image_of_injective]
  · simp
  · intro i k h
    exact congrArg Prod.fst h

theorem graph90_independent_card_le (s : Finset (Fin 90))
    (hs : Independent graph90 (s : Set (Fin 90))) : s.card ≤ 45 := by
  let t := s.map vertex90Equiv.symm.toEmbedding
  have ht : Independent blockGraph90 (t : Set (Vertex (Fin 45))) := by
    intro v hv w hw hne hadj
    obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
    obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
    exact hs hv' hw' (fun he => hne (congrArg vertex90Equiv.symm he)) hadj
  simpa [t] using blockGraph90_independent_card_le t ht

def allPlus90 : Finset (Fin 90) := allPlus.map vertex90Equiv.toEmbedding

theorem allPlus90_independent : Independent graph90 (allPlus90 : Set (Fin 90)) := by
  intro v hv w hw hne hadj
  obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
  obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
  apply allPlus_independent hv' hw' (fun he => hne (congrArg vertex90Equiv he))
  simpa [graph90] using hadj

theorem allPlus90_card : allPlus90.card = 45 := by
  simpa [allPlus90] using allPlus_card

/-- This is the full graph-theoretic statement that the independence number is
45, expressed without a second definition of a maximum or any count oracle. -/
theorem graph90_alpha_eq_45 :
    (∃ s : Finset (Fin 90), Independent graph90 (s : Set (Fin 90)) ∧ s.card = 45) ∧
    (∀ s : Finset (Fin 90), Independent graph90 (s : Set (Fin 90)) → s.card ≤ 45) :=
  ⟨⟨allPlus90, allPlus90_independent, allPlus90_card⟩, graph90_independent_card_le⟩

noncomputable def graph90CardStateEquiv (k : ℕ) :
    {s : Finset (Fin 90) // Independent graph90 (s : Set (Fin 90)) ∧ s.card = k} ≃
    {f : State (Fin 45) // legal arrow45 f ∧ (selected f).card = k} :=
  (show {s : Finset (Fin 90) // Independent graph90 (s : Set (Fin 90)) ∧ s.card = k} ≃
    {s : Finset (Vertex (Fin 45)) // Independent blockGraph90
      (s : Set (Vertex (Fin 45))) ∧ s.card = k} from
    { toFun := fun s => ⟨s.1.map vertex90Equiv.symm.toEmbedding, by
        refine ⟨?_, ?_⟩
        · intro v hv w hw hne hadj
          obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
          obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
          exact s.2.1 hv' hw' (fun he => hne (congrArg vertex90Equiv.symm he)) hadj
        · simpa using s.2.2⟩
      invFun := fun s => ⟨s.1.map vertex90Equiv.toEmbedding, by
        refine ⟨?_, ?_⟩
        · intro v hv w hw hne hadj
          obtain ⟨v', hv', rfl⟩ := Finset.mem_map.mp hv
          obtain ⟨w', hw', rfl⟩ := Finset.mem_map.mp hw
          apply s.2.1 hv' hw' (fun he => hne (congrArg vertex90Equiv he))
          simpa [graph90] using hadj
        · simpa using s.2.2⟩
      left_inv := by
        intro s
        apply Subtype.ext
        simp [Finset.map_eq_image, Finset.image_image, Function.comp_def]
      right_inv := by
        intro s
        apply Subtype.ext
        simp [Finset.map_eq_image, Finset.image_image, Function.comp_def] }).trans
    (independentCardStateEquiv arrow45 k)

theorem graph90_coefficient_eq_stateCount (k : ℕ) :
    coefficient graph90 k =
      Nat.card {f : State (Fin 45) // legal arrow45 f ∧ (selected f).card = k} :=
  Nat.card_congr (graph90CardStateEquiv k)


/-- A fixed-point-free adjacent involution is an explicit perfect matching. -/
def mate90 (v : Fin 90) : Fin 90 :=
  vertex90Equiv ((vertex90Equiv.symm v).1, (vertex90Equiv.symm v).2.rev)

theorem mate90_involutive : Function.Involutive mate90 := by
  intro v
  simp [mate90]

theorem mate90_adjacent (v : Fin 90) : graph90.Adj v (mate90 v) := by
  change blockGraph90.Adj (vertex90Equiv.symm v)
    (vertex90Equiv.symm (vertex90Equiv ((vertex90Equiv.symm v).1,
      (vertex90Equiv.symm v).2.rev)))
  rw [Equiv.symm_apply_apply]
  apply Or.inl
  refine ⟨rfl, ?_⟩
  change (vertex90Equiv.symm v).2 ≠ (vertex90Equiv.symm v).2.rev
  generalize (vertex90Equiv.symm v).2 = b
  have hb : b = 0 ∨ b = 1 := (Fin.forall_fin_two
    (p := fun a : Fin 2 => a = 0 ∨ a = 1)).mpr ⟨Or.inl rfl, Or.inr rfl⟩ b
  rcases hb with rfl | rfl <;> decide

theorem mate90_ne (v : Fin 90) : mate90 v ≠ v := by
  intro h
  have ha := mate90_adjacent v
  rw [h] at ha
  exact graph90.irrefl ha

/-- Literal edge table copied from the fixed p=6 graph certificate; no counts
or coefficient values enter this declaration. Endpoints are numbered 0..89. -/
def fixedEdges90 : List (ℕ × ℕ) :=
  [(0, 1),
   (2, 3),
   (4, 5),
   (6, 7),
   (8, 9),
   (10, 11),
   (12, 13),
   (14, 15),
   (16, 17),
   (18, 19),
   (20, 21),
   (22, 23),
   (24, 25),
   (26, 27),
   (28, 29),
   (30, 31),
   (32, 33),
   (34, 35),
   (36, 37),
   (38, 39),
   (40, 41),
   (42, 43),
   (44, 45),
   (46, 47),
   (48, 49),
   (50, 51),
   (52, 53),
   (54, 55),
   (56, 57),
   (58, 59),
   (60, 61),
   (62, 63),
   (64, 65),
   (66, 67),
   (68, 69),
   (70, 71),
   (72, 73),
   (74, 75),
   (76, 77),
   (78, 79),
   (80, 81),
   (82, 83),
   (84, 85),
   (86, 87),
   (88, 89),
   (0, 5),
   (2, 5),
   (0, 7),
   (0, 9),
   (0, 11),
   (0, 13),
   (0, 15),
   (0, 17),
   (18, 1),
   (20, 1),
   (22, 1),
   (24, 1),
   (26, 1),
   (28, 1),
   (30, 1),
   (32, 1),
   (34, 1),
   (36, 1),
   (38, 1),
   (40, 1),
   (2, 43),
   (2, 45),
   (2, 47),
   (2, 49),
   (2, 51),
   (2, 53),
   (54, 3),
   (56, 3),
   (58, 3),
   (60, 3),
   (62, 3),
   (64, 3),
   (66, 3),
   (68, 3),
   (70, 3),
   (72, 3),
   (74, 3),
   (76, 3),
   (4, 79),
   (4, 81),
   (4, 83),
   (4, 85),
   (4, 87),
   (4, 89)]

instance : DecidableRel arrow45 := fun i k => by
  unfold arrow45
  infer_instance

instance : DecidableRel graph90.Adj := fun v w => by
  change Decidable ((splitGraph arrow45).Adj (vertex90Equiv.symm v)
    (vertex90Equiv.symm w))
  dsimp [splitGraph]
  infer_instance

#print axioms mate90_involutive
#print axioms mate90_adjacent
#print axioms mate90_ne

#print axioms selected_independent_iff
#print axioms independentStateEquiv
#print axioms blockGraph90_independent_card_le
#print axioms allPlus_independent
#print axioms allPlus_card
#print axioms coefficient_splitGraph
#print axioms graph90_alpha_eq_45
#print axioms graph90_coefficient_eq_stateCount

end FormalProof.Research003.RS42Counterexample90
