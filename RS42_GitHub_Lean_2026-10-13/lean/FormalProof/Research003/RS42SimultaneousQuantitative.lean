module
public import FormalProof.Research003.RS42SimultaneousFinal
public import Mathlib.Topology.Order.Lattice
set_option linter.style.header false
set_option linter.hashCommand false
set_option linter.style.whitespace false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Simultaneous
open RS42Structural RS42Counterexample90
open scoped BigOperators Topology
open Filter

theorem ratio_geometric (t p s : ℕ) (hs : s < t) (hp : threshold t ≤ p) :
    0 < structuralRatio (arrow t) (outWeight t) (inWeight t) p (2*s+1) ∧
    structuralRatio (arrow t) (outWeight t) (inWeight t) p (2*s+1) ≤
      (1/(2:ℝ)^(44*structuralN (3*t) (7*t) (2*s+1)^2))*
        (2/3:ℝ)^(p-structuralThreshold (3*t) (7*t) (2*s+1)) ∧
    structuralRatio (arrow t) (outWeight t) (inWeight t) p (2*s+1) < 1 := by
  have h := (structural_quantitative_conclusion (arrow t) (outWeight t) (inWeight t)
    (2*s+1) (by omega) (mass_pos t (by omega)) (positive_gap t s hs)).1 p
      (threshold_transfer t p s hs hp)
  simpa only [core_card,mass_eq] using h

theorem all_counts_positive (t p j : ℕ) (hj : j ≤ labelCount t p) : 0 < count t p j := by
  have hj' : j ≤ Fintype.card (StructuralLabel (outWeight t) (inWeight t) p) := by
    simpa only [label_card] using hj
  have h := structuralS_pos (arrow t) (outWeight t) (inWeight t) p
    (Fintype.card (StructuralLabel (outWeight t) (inWeight t) p)-j) (Nat.sub_le _ _)
  simpa only [structuralS,Nat.sub_sub_self hj',count] using h

theorem targetNonempty (t : ℕ) (ht : 0 < t) : (Finset.univ : Finset (Fin t)).Nonempty :=
  ⟨⟨0,ht⟩,Finset.mem_univ _⟩
noncomputable def maxRatio (t p : ℕ) (ht : 0 < t) : ℝ :=
  Finset.univ.sup' (targetNonempty t ht)
    (fun s : Fin t => structuralRatio (arrow t) (outWeight t) (inWeight t) p (2*s.val+1))

/-- Fixed finite t; no claim is made for a set of indices growing with p. -/
theorem maxRatio_tendsto_zero (t : ℕ) (ht : 0 < t) :
    Tendsto (fun p => maxRatio t p ht) atTop (𝓝 (0:ℝ)) := by
  have h := Filter.Tendsto.finset_sup'_nhds_apply (targetNonempty t ht)
    (fun (s : Fin t) (_ : s ∈ (Finset.univ : Finset (Fin t))) => ratio_tendsto_zero t s.val s.isLt)
  simpa only [Finset.sup'_const,maxRatio] using h

theorem log_bound (t : ℕ) : structuralLog (3*t) (7*t) ≤ 10*t := by
  apply structuralLog_min
  have h := RS42FixedK.succ_le_two_pow (10*t)
  omega

theorem threshold_bound (t : ℕ) : threshold t ≤ 14400*t^2 := by
  have h := log_bound t
  have hsq := Nat.pow_le_pow_left (show 5*t+structuralLog (3*t) (7*t) ≤ 15*t by omega) 2
  unfold threshold
  nlinarith

theorem initial_size_bound (t : ℕ) : 2*labelCount t (threshold t) ≤ 6*t+201600*t^3 := by
  have h := Nat.mul_le_mul_left (14*t) (threshold_bound t)
  unfold labelCount
  nlinarith

theorem log_two : structuralLog 6 14 = 5 := by
  have hu := structuralLog_min 6 14 5 (by norm_num)
  have hl := structuralLog_spec 6 14
  by_contra hn
  have hh : structuralLog 6 14 ≤ 4 := by omega
  have hp := Nat.pow_le_pow_right (show 1 ≤ (2:ℕ) by omega) hh
  norm_num at hp hl
  omega

theorem threshold_two : threshold 2 = 14400 := by
  unfold threshold
  norm_num [log_two]

/-- The same explicit graph has two distinct internal failure positions for
every p >= 14400; both coefficients use mathlib IsNIndepSet counting. -/
theorem two_place_counterexample (p : ℕ) (hp : 14400 ≤ p) :
    let G := graph 2 p
    G.IsTree ∧ G.indepNum = 6+14*p ∧
    G.indepNum-1 ≠ G.indepNum-3 ∧
    (∀ k ∈ ({1,3} : Finset ℕ),
      1 ≤ G.indepNum-k ∧ G.indepNum-k < G.indepNum ∧
      count 2 p (G.indepNum-k)^2 < count 2 p (G.indepNum-k-1)*count 2 p (G.indepNum-k+1)) := by
  have hp' : threshold 2 ≤ p := by rwa [threshold_two]
  have h := simultaneous_counterexample 2 p (by omega) hp'
  dsimp only at h ⊢
  have h0 := strict_failure 2 p 0 (by omega) hp'
  have h1 := strict_failure 2 p 1 (by omega) hp'
  have halpha : (graph 2 p).indepNum = 6+14*p := by
    rw [graph_indepNum,labelCount]; ring
  refine ⟨h.1,halpha,?_,?_⟩
  · rw [halpha]
    omega
  · intro k hk
    simp only [Finset.mem_insert,Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · simpa only [graph_indepNum,Nat.mul_zero,Nat.zero_add] using h0
    · simpa only [graph_indepNum] using h1

end FormalProof.Research003.RS42Simultaneous
