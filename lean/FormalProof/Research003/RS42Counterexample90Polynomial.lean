module

public import Mathlib.Algebra.Polynomial.Coeff
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum

set_option linter.style.header false
set_option linter.hashCommand false

/-!
Exact algebraic evaluation of the fixed 90-vertex candidate polynomial.
The graph/counting bridge is proved in the separate CountsFactors module.
The displayed expansion is a candidate identity checked by ordinary `ring`;
its integers are not used as axioms or as an externally trusted count.
-/

@[expose] public section
set_option autoImplicit false
set_option maxRecDepth 4096

namespace FormalProof.Research003.RS42Counterexample90
open Polynomial

/-- The closed expression to which the true finite-choice count is reduced. -/
noncomputable def independentPolynomial90 : ℕ[X] :=
  let A : ℕ[X] := 1 + 2 * X
  let C : ℕ[X] := 1 + X
  let W := A ^ 18 + X * A ^ 12 * C ^ 6 + X * A ^ 6 * C ^ 12
  let R := A ^ 18 + X * A ^ 6 * C ^ 12
  (A ^ 6 + X * C ^ 6) * W ^ 2 + X * A ^ 6 * R ^ 2

/-- Full expansion is verified by semiring normalization in the kernel. -/
theorem independentPolynomial90_expansion : independentPolynomial90 =
    1 +
    90 * X ^ 1 +
    3916 * X ^ 2 +
    109926 * X ^ 3 +
    2240986 * X ^ 4 +
    35405739 * X ^ 5 +
    451690547 * X ^ 6 +
    4786443926 * X ^ 7 +
    43004829390 * X ^ 8 +
    332741399909 * X ^ 9 +
    2244066627994 * X ^ 10 +
    13319144548616 * X ^ 11 +
    70111848084568 * X ^ 12 +
    329396383482143 * X ^ 13 +
    1388355716695485 * X ^ 14 +
    5272015588026557 * X ^ 15 +
    18098871688320222 * X ^ 16 +
    56330805139667047 * X ^ 17 +
    159306825980779435 * X ^ 18 +
    410083895315070717 * X ^ 19 +
    962097374082906740 * X ^ 20 +
    2058960643965441130 * X ^ 21 +
    4021244584210249302 * X ^ 22 +
    7167834268366389669 * X ^ 23 +
    11657180609263506754 * X ^ 24 +
    17284951435682133777 * X ^ 25 +
    23341171371585250217 * X ^ 26 +
    28659887479842213630 * X ^ 27 +
    31932203813085862722 * X ^ 28 +
    32199750415011335761 * X ^ 29 +
    29291229629718806724 * X ^ 30 +
    23941638929784194891 * X ^ 31 +
    17497780538089255302 * X ^ 32 +
    11366548333022974745 * X ^ 33 +
    6514648479312788200 * X ^ 34 +
    3264274944846258968 * X ^ 35 +
    1413456779478007296 * X ^ 36 +
    521056707965210864 * X ^ 37 +
    160315517837985024 * X ^ 38 +
    40055063684604928 * X ^ 39 +
    7808474198021632 * X ^ 40 +
    1114648009271040 * X ^ 41 +
    103770841843712 * X ^ 42 +
    4761097500672 * X ^ 43 +
    5965496320 * X ^ 44 +
    17567744 * X ^ 45 := by
  unfold independentPolynomial90
  ring

theorem independentPolynomial90_coeff43 :
    independentPolynomial90.coeff 43 = 4761097500672 := by
  rw [independentPolynomial90_expansion]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_natCast_ite,
    Polynomial.coeff_one, Polynomial.coeff_X]

theorem independentPolynomial90_coeff44 :
    independentPolynomial90.coeff 44 = 5965496320 := by
  rw [independentPolynomial90_expansion]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_natCast_ite,
    Polynomial.coeff_one, Polynomial.coeff_X]

theorem independentPolynomial90_coeff45 :
    independentPolynomial90.coeff 45 = 17567744 := by
  rw [independentPolynomial90_expansion]
  norm_num [Polynomial.coeff_add, Polynomial.coeff_X_pow,
    Polynomial.coeff_ofNat_mul, Polynomial.coeff_natCast_ite,
    Polynomial.coeff_one, Polynomial.coeff_X]

theorem independentPolynomial90_strict_failure :
    independentPolynomial90.coeff 44 ^ 2 <
      independentPolynomial90.coeff 43 * independentPolynomial90.coeff 45 := by
  rw [independentPolynomial90_coeff43, independentPolynomial90_coeff44,
    independentPolynomial90_coeff45]
  norm_num

theorem independentPolynomial90_signed_difference :
    (independentPolynomial90.coeff 44 : ℤ) ^ 2 -
      (independentPolynomial90.coeff 43 : ℤ) *
        (independentPolynomial90.coeff 45 : ℤ) = -48054595706911981568 := by
  rw [independentPolynomial90_coeff43, independentPolynomial90_coeff44,
    independentPolynomial90_coeff45]
  norm_num

#print axioms independentPolynomial90_expansion
#print axioms independentPolynomial90_coeff43
#print axioms independentPolynomial90_coeff44
#print axioms independentPolynomial90_coeff45
#print axioms independentPolynomial90_strict_failure
#print axioms independentPolynomial90_signed_difference
end FormalProof.Research003.RS42Counterexample90
