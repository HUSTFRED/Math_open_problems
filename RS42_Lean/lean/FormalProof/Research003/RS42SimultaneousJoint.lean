module
public import FormalProof.Research003.RS42StructuralFinal
set_option linter.style.header false
set_option linter.hashCommand false
@[expose] public section
set_option autoImplicit false
namespace FormalProof.Research003.RS42Simultaneous
open RS42Structural
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem threshold_mono (d W : ℕ) : Monotone (structuralThreshold d W) := by
  intro k l h
  unfold structuralThreshold structuralN
  apply Nat.mul_le_mul_left
  exact Nat.pow_le_pow_left (by omega) 2

/-- All coefficients belong to one fixed actual graph, at one scale p. -/
theorem joint_failure (R : V → V → Prop) (a b : V → ℕ)
    (J : Finset ℕ) (K p : ℕ) (hW : 1 ≤ totalMultiplicity a b)
    (hJ : ∀ k ∈ J, 1 ≤ k ∧ k ≤ K ∧
      2 * maxCoreExponent R a b k <
        maxCoreExponent R a b (k - 1) + maxCoreExponent R a b (k + 1))
    (hp : structuralThreshold (Fintype.card V) (totalMultiplicity a b) K ≤ p) :
    let G := structuralGraph R a b p
    ∀ k ∈ J, 1 ≤ G.indepNum-k ∧ G.indepNum-k < G.indepNum ∧
      structuralIndepCount R a b p (G.indepNum-k)^2 <
        structuralIndepCount R a b p (G.indepNum-k-1) *
          structuralIndepCount R a b p (G.indepNum-k+1) := by
  dsimp only
  intro k hk
  obtain ⟨hpos, hle, hgap⟩ := hJ k hk
  have ht := (threshold_mono (Fintype.card V) (totalMultiplicity a b) hle).trans hp
  simpa only [structural_indepNum] using structural_strict_failure R a b p k hpos hW hgap ht

theorem distinct_indices (m k l : ℕ) (hk : k ≤ m) (hl : l ≤ m)
    (hne : k ≠ l) : m-k ≠ m-l := by omega

end FormalProof.Research003.RS42Simultaneous
