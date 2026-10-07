module

public import FormalProof.Research003.RS42Counterexample90Factors
public import FormalProof.Research003.RS42Counterexample90Polynomial

set_option linter.style.header false
set_option linter.hashCommand false

/-!
The actual graph-independent-set counts, obtained by composing the semantic
state decomposition with the symbolically verified fixed polynomial.
This file does not replace graph counts by externally supplied integers.
-/

@[expose] public section
set_option autoImplicit false

namespace FormalProof.Research003.RS42Counterexample90

theorem graph90_coefficient_eq_polynomial (k : ℕ) :
    coefficient graph90 k = independentPolynomial90.coeff k := by
  rw [coefficient_graph90_eq_corePolynomial]
  have h : corePolynomial90 = independentPolynomial90 := by
    simpa [independentPolynomial90] using corePolynomial90_closed
  rw [h]

theorem graph90_coefficient43 : coefficient graph90 43 = 4761097500672 := by
  rw [graph90_coefficient_eq_polynomial, independentPolynomial90_coeff43]

theorem graph90_coefficient44 : coefficient graph90 44 = 5965496320 := by
  rw [graph90_coefficient_eq_polynomial, independentPolynomial90_coeff44]

theorem graph90_coefficient45 : coefficient graph90 45 = 17567744 := by
  rw [graph90_coefficient_eq_polynomial, independentPolynomial90_coeff45]

theorem graph90_count_failure :
    coefficient graph90 44 ^ 2 < coefficient graph90 43 * coefficient graph90 45 := by
  simp only [graph90_coefficient_eq_polynomial]
  exact independentPolynomial90_strict_failure

theorem graph90_count_signed_difference :
    (coefficient graph90 44 : ℤ) ^ 2 -
      (coefficient graph90 43 : ℤ) * (coefficient graph90 45 : ℤ) =
        -48054595706911981568 := by
  simp only [graph90_coefficient_eq_polynomial]
  exact independentPolynomial90_signed_difference

theorem graph90_mathlib_count_failure :
    Nat.card {s : Finset (Fin 90) // graph90.IsNIndepSet 44 s} ^ 2 <
      Nat.card {s : Finset (Fin 90) // graph90.IsNIndepSet 43 s} *
        Nat.card {s : Finset (Fin 90) // graph90.IsNIndepSet 45 s} := by
  have h (k : ℕ) : Nat.card {s : Finset (Fin 90) // graph90.IsNIndepSet k s} =
      coefficient graph90 k := Nat.card_congr (mathlibCoefficientEquiv k)
  simp only [h]
  exact graph90_count_failure

#print axioms graph90_coefficient_eq_polynomial
#print axioms graph90_coefficient43
#print axioms graph90_coefficient44
#print axioms graph90_coefficient45
#print axioms graph90_count_failure
#print axioms graph90_count_signed_difference
#print axioms graph90_mathlib_count_failure

end FormalProof.Research003.RS42Counterexample90
