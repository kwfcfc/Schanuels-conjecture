import Schanuel.LindemannAttempt
import Mathlib.NumberTheory.Niven
import Mathlib.RingTheory.Algebraic.Integral

/-!
# Reduction of the Lindemann arithmetic step to algebraic integers

Every algebraic complex number has a nonzero integer multiple which is an
algebraic integer.  Since the exponential of an integer multiple is an integer
power of the original exponential, the arbitrary-algebraic Hermite--Lindemann
problem (and hence `LindemannArithmeticStep`) reduces to the case of algebraic
integer exponents.
-/

namespace Schanuel.LindemannAttempt

open Complex Polynomial

noncomputable section

/-- The arithmetic step restricted to algebraic integer exponents. -/
def IntegralLindemannArithmeticStep : Prop :=
  ∀ (z : ℂ) (q : ℤ[X]),
    IsIntegral ℤ z → z ≠ 0 → q.eval 0 ≠ 0 →
    HasLindemannApproximants (nonconstantExponents q z) →
    ((q.eval (0 : ℤ) : ℤ) : ℂ) +
      ∑ k ∈ q.support.erase 0,
        (q.coeff k : ℂ) * Complex.exp (k * z) ≠ 0

/-- Evaluating an integer polynomial at an algebraic integer again gives an
algebraic integer. -/
theorem isIntegral_aeval_intPolynomial {x : ℂ} (hx : IsIntegral ℤ x)
    (g : ℤ[X]) : IsIntegral ℤ (aeval x g) := by
  rw [aeval_def, eval₂_eq_sum]
  exact IsIntegral.sum _ fun k _ ↦
    (isIntegral_algebraMap.mul (hx.pow k))

/-- The polynomial-evaluation sum occurring in the Lindemann auxiliary value
is integral when the exponent is an algebraic integer. -/
theorem isIntegral_weighted_aeval_sum {z : ℂ} (hz : IsIntegral ℤ z)
    (q gp : ℤ[X]) :
    IsIntegral ℤ
      (∑ k ∈ q.support.erase 0,
        (q.coeff k : ℂ) * aeval ((k : ℂ) * z) gp) := by
  apply IsIntegral.sum
  intro k _
  apply isIntegral_algebraMap.mul
  apply isIntegral_aeval_intPolynomial
  exact (isIntegral_algebraMap.mul hz)

/-- The congruence part of the arithmetic argument works unchanged for an
algebraic-integer auxiliary value.  If `B` is integral, the value
`n*a + p*B` cannot vanish when neither integer factor is divisible by the
prime `p`.

This isolates the remaining issue in the arbitrary-algebraic proof: after
Galois symmetrization one must bound all conjugates of this nonzero integral
value (or arrange that it is rational), not merely its distinguished complex
embedding. -/
theorem integral_auxiliary_ne_zero_mod_prime
    {p : ℕ} (hp : p.Prime) {n a : ℤ} (hn : ¬ (p : ℤ) ∣ n)
    (ha0 : a ≠ 0) (ha : a.natAbs < p) {B : ℂ} (hB : IsIntegral ℤ B) :
    (n * a : ℂ) + (p : ℂ) * B ≠ 0 := by
  intro hzero
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hB_div : B = -((n : ℂ) * (a : ℂ)) / (p : ℂ) := by
    apply (eq_div_iff hp0).2
    linear_combination hzero
  have hB_rat : B = ((-(n * a : ℤ) / (p : ℚ) : ℚ) : ℂ) := by
    push_cast
    exact hB_div
  obtain ⟨b, hb⟩ := hB.exists_int_iff_exists_rat.mp ⟨_, hB_rat⟩
  have hInt : n * a + (p : ℤ) * b = 0 := by
    have hc : (n : ℂ) * (a : ℂ) + (p : ℂ) * (b : ℂ) = 0 := by
      simpa [hb] using hzero
    exact_mod_cast hc
  have hp_dvd : (p : ℤ) ∣ n * a := by
    refine ⟨-b, ?_⟩
    linear_combination hInt
  rcases Int.Prime.dvd_mul hp hp_dvd with hn' | ha'
  · exact hn ((Int.natCast_dvd).2 hn')
  · exact (not_le_of_gt ha) (Nat.le_of_dvd (Int.natAbs_pos.mpr ha0) ha')

/-- The actual auxiliary value built from `gₚ` is nonzero for an algebraic
integer exponent.  This is the exact algebraic-integer analogue of the `hD`
congruence argument in `exp_intCast_transcendental`; unlike that special case,
the value is generally an algebraic integer rather than a rational integer. -/
theorem lindemann_auxiliary_ne_zero_of_isIntegral
    {z : ℂ} (hz : IsIntegral ℤ z) (q gp : ℤ[X]) {p : ℕ}
    (hp : p.Prime) {n : ℤ} (hn : ¬ (p : ℤ) ∣ n)
    (hq0 : q.eval 0 ≠ 0) (hq : (q.eval 0).natAbs < p) :
    ((n * q.eval 0 : ℤ) : ℂ) + (p : ℂ) *
      (∑ k ∈ q.support.erase 0,
        (q.coeff k : ℂ) * aeval ((k : ℂ) * z) gp) ≠ 0 := by
  simpa using integral_auxiliary_ne_zero_mod_prime hp hn hq0 hq
    (isIntegral_weighted_aeval_sum hz q gp)

/-- The restricted arithmetic step proves Hermite--Lindemann for nonzero
algebraic integers. -/
theorem integral_exp_transcendental_of_integralArithmeticStep
    (harith : IntegralLindemannArithmeticStep) (z : ℂ)
    (hz : IsIntegral ℤ z) (hz0 : z ≠ 0) :
    Transcendental ℚ (Complex.exp z) := by
  intro hexp
  have hzalg : IsAlgebraic ℚ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hz.isAlgebraic
  obtain ⟨q, hq0, hrel⟩ :=
    normalized_integral_exp_relation_of_isAlgebraic hexp
  exact (harith z q hz hz0 hq0
    (hasLindemannApproximants_nonconstantExponents q hzalg hz0)) hrel

/-- It is enough to prove the arithmetic step for algebraic integer
exponents.  A nonzero integer multiple clears the denominator of an arbitrary
algebraic exponent. -/
theorem arithmeticStep_of_integralArithmeticStep
    (harith : IntegralLindemannArithmeticStep) : LindemannArithmeticStep := by
  apply arithmeticStep_of_hermiteLindemann
  intro z hz hz0 hexp
  have hz' : IsAlgebraic ℤ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr hz
  obtain ⟨d, hd0, hdint⟩ := hz'.exists_integral_multiple
  have hdz0 : d • z ≠ 0 := by
    rw [zsmul_eq_mul]
    exact mul_ne_zero (by exact_mod_cast hd0) hz0
  apply (integral_exp_transcendental_of_integralArithmeticStep harith
    (d • z) hdint hdz0)
  rw [zsmul_eq_mul, Complex.exp_int_mul]
  cases d with
  | ofNat n =>
      simpa using hexp.pow n
  | negSucc n =>
      rw [zpow_negSucc]
      exact (hexp.pow (n + 1)).isIntegral.inv.isAlgebraic

/-- Thus the unrestricted and algebraic-integer arithmetic steps are
equivalent. -/
theorem lindemannArithmeticStep_iff_integralArithmeticStep :
    LindemannArithmeticStep ↔ IntegralLindemannArithmeticStep := by
  constructor
  · intro h z q hz hz0 hq0 happ
    exact h z q
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hz.isAlgebraic)
      hz0 hq0 happ
  · exact arithmeticStep_of_integralArithmeticStep

end

end Schanuel.LindemannAttempt
