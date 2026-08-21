import Schanuel.AlgebraicExponentialInputs
import Schanuel.MixedObstruction
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# A logarithm--period boundary with algebraic exponentials

The family `(log 2, 2 * pi * I)` is rationally linearly independent and both of its exponential
values are algebraic (`2` and `1`).  Its Schanuel bound is therefore exactly algebraic
independence of the two coordinates.  This is a concrete tightness test for the boundary where all
exponentials are algebraic.
-/

namespace Schanuel.PeriodLogBoundary

open Complex

noncomputable section

def period : ℂ := 2 * Real.pi * Complex.I

def family : Fin 2 → ℂ := ![MixedObstruction.logTwo, period]

@[simp]
theorem family_zero : family 0 = MixedObstruction.logTwo := rfl

@[simp]
theorem family_one : family 1 = period := rfl

@[simp]
theorem exp_family_zero : Complex.exp (family 0) = 2 := by
  exact MixedObstruction.exp_logTwo

@[simp]
theorem exp_family_one : Complex.exp (family 1) = 1 := by
  exact Complex.exp_two_pi_mul_I

theorem family_linearIndependent : LinearIndependent ℚ family := by
  rw [linearIndependent_fin2]
  constructor
  · intro hzero
    have him := congrArg Complex.im hzero
    change (2 * Real.pi * Complex.I : ℂ).im = 0 at him
    norm_num at him
  · intro a ha
    have hre := congrArg Complex.re ha
    change ((a : ℂ) * (2 * Real.pi * Complex.I)).re =
      (MixedObstruction.logTwo).re at hre
    have hlogzero : MixedObstruction.logTwo = 0 := by
      apply Complex.ext
      · simpa [MixedObstruction.logTwo] using hre.symm
      · rfl
    exact MixedObstruction.logTwo_ne_zero hlogzero

theorem exponential_isAlgebraic (i : Fin 2) :
    IsAlgebraic ℚ (Complex.exp (family i)) := by
  fin_cases i
  · simpa [family] using
      (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (2 : ℚ))
  · simpa [family, period] using
      (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (1 : ℚ))

/-- The Schanuel bound here is precisely algebraic independence of `log 2` and the basic
period `2*pi*I`. -/
theorem bound_family_iff_algebraicIndependent :
    Bound family ↔ AlgebraicIndependent ℚ family :=
  bound_iff_algebraicIndependent_coordinate_of_exponential_isAlgebraic
    family exponential_isAlgebraic

theorem conjecture_implies_algebraicIndependent_logTwo_period
    (hS : Conjecture) : AlgebraicIndependent ℚ family := by
  exact conjecture_implies_algebraicIndependent_of_exponential_isAlgebraic
    hS family family_linearIndependent exponential_isAlgebraic

end

end Schanuel.PeriodLogBoundary
