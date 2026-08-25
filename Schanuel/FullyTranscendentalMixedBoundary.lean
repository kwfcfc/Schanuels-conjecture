import Schanuel.FullyTranscendentalReduction
import Schanuel.MixedObstruction

/-!
# A fully transcendental presentation of the mixed boundary

An elementary integral shear turns the mixed family `(log 2, log 2 + 1)` into
`(2 * log 2 + 1, log 2 + 1)`.  Both new coordinates and both of their exponentials are
transcendental, while the generated field is unchanged.  Thus the fully transcendental branch
already contains the exact algebraic-independence problem for `log 2` and `e`.
-/

namespace Schanuel.FullyTranscendentalMixedBoundary

open Complex

noncomputable section

open MixedObstruction

/-- Add the second mixed coordinate to the first and leave the second fixed. -/
def family : Fin 2 → ℂ :=
  integerShear MixedObstruction.family 0 1 1

@[simp]
theorem family_zero : family 0 = 2 * logTwo + 1 := by
  simp [family, integerShear, integerShearFamily, MixedObstruction.family]
  ring

@[simp]
theorem family_one : family 1 = logTwo + 1 := by
  simp [family, integerShear, integerShearFamily, MixedObstruction.family]

/-- The shear preserves the rational linear-independence hypothesis. -/
theorem family_linearIndependent : LinearIndependent ℚ family := by
  exact (linearIndependent_integerShear_iff MixedObstruction.family 0 1 1 (by decide)).2
    MixedObstruction.family_linearIndependent

/-- The shear preserves the complete coordinate-exponential generated field. -/
theorem generatedField_eq_mixed :
    generatedField family = generatedField MixedObstruction.family := by
  exact generatedField_integerShear_eq MixedObstruction.family 0 1 1 (by decide)

theorem exp_one_transcendental : Transcendental ℚ (Complex.exp 1) := by
  simpa using LindemannAttempt.exp_intCast_transcendental 1 (by norm_num)

/-- Every coordinate of the sheared family is transcendental. -/
theorem coordinate_transcendental : ∀ i, Transcendental ℚ (family i) := by
  intro i
  fin_cases i
  · have htwo : Transcendental ℚ ((2 : ℂ) * logTwo) :=
      transcendental_mul_of_isAlgebraic_left
        (isAlgebraic_algebraMap (A := ℂ) (2 : ℚ)) (by norm_num)
        logTwo_transcendental
    have hone : Transcendental ℚ ((1 : ℂ) + 2 * logTwo) :=
      transcendental_add_of_isAlgebraic_left
        isAlgebraic_one htwo
    simpa [add_comm] using hone
  · have hone : Transcendental ℚ ((1 : ℂ) + logTwo) :=
      transcendental_add_of_isAlgebraic_left
        isAlgebraic_one logTwo_transcendental
    simpa [add_comm] using hone

@[simp]
theorem exp_family_zero : Complex.exp (family 0) = 4 * Complex.exp 1 := by
  rw [family_zero]
  calc
    Complex.exp (2 * logTwo + 1) =
        Complex.exp logTwo * Complex.exp logTwo * Complex.exp 1 := by
          rw [show 2 * logTwo + 1 = logTwo + logTwo + 1 by ring]
          simp only [Complex.exp_add]
    _ = 4 * Complex.exp 1 := by rw [exp_logTwo]; ring

@[simp]
theorem exp_family_one : Complex.exp (family 1) = 2 * Complex.exp 1 := by
  rw [family_one, Complex.exp_add, exp_logTwo]

/-- Every exponential of the sheared family is transcendental as well. -/
theorem exponential_transcendental :
    ∀ i, Transcendental ℚ (Complex.exp (family i)) := by
  intro i
  fin_cases i
  · change Transcendental ℚ (Complex.exp (family 0))
    rw [exp_family_zero]
    exact transcendental_mul_of_isAlgebraic_left
      (isAlgebraic_algebraMap (A := ℂ) (4 : ℚ)) (by norm_num)
      exp_one_transcendental
  · change Transcendental ℚ (Complex.exp (family 1))
    rw [exp_family_one]
    exact transcendental_mul_of_isAlgebraic_left
      (isAlgebraic_algebraMap (A := ℂ) (2 : ℚ)) (by norm_num)
      exp_one_transcendental

/-- Even in the branch where all displayed values are transcendental, the desired bound is
exactly algebraic independence of `log 2` and `e`. -/
theorem bound_family_iff_algebraicIndependent_logTwo_exp_one :
    Bound family ↔ AlgebraicIndependent ℚ MixedObstruction.core := by
  constructor
  · intro hbound
    apply MixedObstruction.bound_family_iff_algebraicIndependent_logTwo_exp_one.mp
    unfold Bound at hbound ⊢
    calc
      Cardinal.mk (Fin 2) ≤ Algebra.trdeg ℚ (generatedField family) := hbound
      _ = Algebra.trdeg ℚ (generatedField MixedObstruction.family) :=
        (IntermediateField.equivOfEq generatedField_eq_mixed).trdeg_eq
  · intro hcore
    have hmixed : Bound MixedObstruction.family :=
      MixedObstruction.bound_family_iff_algebraicIndependent_logTwo_exp_one.mpr hcore
    unfold Bound at hmixed ⊢
    calc
      Cardinal.mk (Fin 2) ≤ Algebra.trdeg ℚ (generatedField MixedObstruction.family) := hmixed
      _ = Algebra.trdeg ℚ (generatedField family) :=
        (IntermediateField.equivOfEq generatedField_eq_mixed.symm).trdeg_eq

/-- The nominally generic fully transcendental branch already implies the concrete mixed
algebraic-independence problem. -/
theorem fullyTranscendentalConjecture_implies_algebraicIndependent_logTwo_exp_one
    (h : FullyTranscendentalConjecture) :
    AlgebraicIndependent ℚ MixedObstruction.core := by
  apply bound_family_iff_algebraicIndependent_logTwo_exp_one.mp
  exact h 2 family family_linearIndependent coordinate_transcendental
    exponential_transcendental

end

end Schanuel.FullyTranscendentalMixedBoundary
