import Schanuel.AlgebraicInputs
import Schanuel.IntegerShear

/-!
# Reduction to all-transcendental coordinate families

The all-algebraic coordinate branch is proved in `AlgebraicInputs`.  Every other linearly
independent family can be changed by an integral shear, without changing its generated field, so
that every coordinate is transcendental.  Hence the full conjecture is equivalent to its
restriction to all-transcendental coordinate families.
-/

namespace Schanuel

noncomputable section

/-- Schanuel's conjecture restricted to families whose individual coordinates are all
transcendental. -/
def AllTranscendentalConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    (∀ i, Transcendental ℚ (z i)) → Bound z

/-- The checked algebraic-input theorem and exact integer-shear invariance reduce the full
conjecture to its all-transcendental-coordinate restriction. -/
theorem conjecture_iff_allTranscendental :
    Conjecture ↔ AllTranscendentalConjecture := by
  constructor
  · intro hS n z hlin htrans
    exact hS n z hlin
  · intro htrans n z hlin
    rcases all_algebraic_or_exists_all_transcendental_integerShear hlin with
      halg | ⟨w, hwlin, hfield, hwtrans⟩
    · exact AlgebraicInputs.bound_of_isAlgebraic_coordinate z hlin halg
    · have hwbound : Bound w := htrans n w hwlin hwtrans
      unfold Bound at hwbound ⊢
      calc
        Cardinal.mk (Fin n) ≤ Algebra.trdeg ℚ (generatedField w) := hwbound
        _ = Algebra.trdeg ℚ (generatedField z) :=
          (IntermediateField.equivOfEq hfield).trdeg_eq

end

end Schanuel
