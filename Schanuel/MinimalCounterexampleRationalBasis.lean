import Schanuel.MinimalCounterexample
import Schanuel.RationalBasisInvariance

/-!
# Rational hyperplanes in a minimal counterexample

Combining rational-basis invariance with the minimal-counterexample theorem
shows that every rational hyperplane projection of a first failure has the
same transcendence degree as the full family and that the transformed full
field is algebraic over the projection field.
-/

namespace Schanuel

open Function Set

noncomputable section

set_option synthInstance.maxHeartbeats 100000 in
-- The two imported algebra-tower developments create a larger instance-search graph here.
/-- Every rational hyperplane projection of a first failure has the full
transcendence degree `n`. -/
theorem rational_hyperplane_trdeg_eq_predecessor_of_minimal_failure
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hz : LinearIndependent ℚ z)
    (hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w)
    (hfail : ¬ Bound z) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hB : B.det ≠ 0) (f : Fin n ↪ Fin (n + 1)) :
    Algebra.trdeg ℚ
      (generatedField ((rationalMatrixFamily B z) ∘ f)) =
        ((n : ℕ) : Cardinal) := by
  have hwz : LinearIndependent ℚ (rationalMatrixFamily B z) :=
    linearIndependent_rationalMatrixFamily B hB z hz
  have hwfail : ¬ Bound (rationalMatrixFamily B z) := by
    intro hw
    exact hfail ((bound_rationalMatrixFamily_iff B hB z).mp hw)
  exact restricted_trdeg_eq_predecessor_of_minimal_failure hwz hprev hwfail f

set_option synthInstance.maxHeartbeats 100000 in
-- As above, the combined algebra-tower imports enlarge typeclass search.
/-- The transformed full field of a first failure is algebraic over each of
its rational hyperplane projection fields. -/
theorem isAlgebraic_over_rational_hyperplane_of_minimal_failure
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hz : LinearIndependent ℚ z)
    (hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w)
    (hfail : ¬ Bound z) (B : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ)
    (hB : B.det ≠ 0) (f : Fin n ↪ Fin (n + 1)) :
    let w := rationalMatrixFamily B z
    letI : Algebra (generatedField (w ∘ f)) (generatedField w) :=
      (generatedFieldInclusion (generators_comp_subset w f)).toAlgebra
    Algebra.IsAlgebraic (generatedField (w ∘ f)) (generatedField w) := by
  have hwz : LinearIndependent ℚ (rationalMatrixFamily B z) :=
    linearIndependent_rationalMatrixFamily B hB z hz
  have hwfail : ¬ Bound (rationalMatrixFamily B z) := by
    intro hw
    exact hfail ((bound_rationalMatrixFamily_iff B hB z).mp hw)
  exact isAlgebraic_over_restriction_of_minimal_failure
    hwz hprev hwfail f

end

end Schanuel
