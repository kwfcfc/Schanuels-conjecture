import Schanuel
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.Localization.Integral
import Mathlib.FieldTheory.Minpoly.Field
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Data.Nat.Prime.Infinite

/-!
# The analytic boundary of the one-dimensional case

This file pushes the one-dimensional Schanuel argument into Mathlib's unfinished
Hermite--Lindemann development.  For a nonzero algebraic `z`, we clear denominators in its
minimal polynomial and specialize `LindemannWeierstrass.exp_polynomial_approx` at the root `z`.

The resulting estimate is the analytic half of the classical proof.  Finishing the argument
would require the missing arithmetic half: under the contrary assumption that `exp z` is
algebraic, take suitable conjugates/norms and derive a nonzero integer of absolute value less
than one.  This file carries out that endpoint completely for nonzero rational `z`, where all
polynomial evaluations can be kept in `ℤ`.  The Galois/integrality step for an arbitrary
algebraic `z` is not postulated here.
-/

namespace Schanuel.LindemannAttempt

open Complex Polynomial
open scoped Nat

noncomputable section

/-- The minimal polynomial over `ℚ`, scaled to have integer coefficients. -/
def integerMinpoly (z : ℂ) : ℤ[X] :=
  IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ z)

theorem integerMinpoly_ne_zero {z : ℂ} (hz : IsAlgebraic ℚ z) :
    integerMinpoly z ≠ 0 := by
  exact IsFractionRing.integerNormalization_eq_zero_iff.not.mpr
    (minpoly.ne_zero hz.isIntegral)

theorem integerMinpoly_aeval {z : ℂ} :
    aeval z (integerMinpoly z) = 0 := by
  apply IsLocalization.integerNormalization_aeval_eq_zero
      (nonZeroDivisors ℤ) (minpoly ℚ z)
  exact minpoly.aeval ℚ z

theorem integerMinpoly_mem_aroots {z : ℂ} (hz : IsAlgebraic ℚ z) :
    z ∈ (integerMinpoly z).aroots ℂ := by
  exact mem_aroots.mpr ⟨integerMinpoly_ne_zero hz, integerMinpoly_aeval⟩

theorem integerMinpoly_eval_zero_ne_zero {z : ℂ}
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    (integerMinpoly z).eval 0 ≠ 0 := by
  rw [← coeff_zero_eq_eval_zero]
  intro hzero
  obtain ⟨b, hb, hmap⟩ := IsLocalization.integerNormalization_spec
    (nonZeroDivisors ℤ) (minpoly ℚ z)
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hcoeff := congrArg (fun q : ℚ[X] ↦ q.coeff 0) hmap
  change (map (algebraMap ℤ ℚ)
      (IsLocalization.integerNormalization (nonZeroDivisors ℤ) (minpoly ℚ z))).coeff 0 =
    (b • minpoly ℚ z).coeff 0 at hcoeff
  rw [coeff_map] at hcoeff
  have hcoeff' : algebraMap ℤ ℚ ((integerMinpoly z).coeff 0) =
      b • (minpoly ℚ z).coeff 0 := by
    simpa [integerMinpoly] using hcoeff
  change algebraMap ℤ ℚ ((integerMinpoly z).coeff 0) =
    (b : ℚ) * (minpoly ℚ z).coeff 0 at hcoeff'
  rw [hzero] at hcoeff'
  simp only [map_zero] at hcoeff'
  have hbc : (b : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hb0
  exact (mul_ne_zero hbc (minpoly.coeff_zero_ne_zero hz.isIntegral hz0)) hcoeff'.symm

/-- Mathlib's analytic Lindemann estimate, specialized to a nonzero algebraic number `z`.

For every sufficiently large prime `p`, it supplies an integer `n` not divisible by `p` and an
integer polynomial `gₚ` for which `n * exp z` is factorially close to `p * gₚ(z)`. -/
theorem algebraic_exp_approximation {z : ℂ}
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    ∃ (f : ℤ[X]) (c : ℝ),
      f ≠ 0 ∧ f.eval 0 ≠ 0 ∧ z ∈ f.aroots ℂ ∧
      ∀ p > (f.eval 0).natAbs, p.Prime →
        ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧
          ∃ gp : ℤ[X], gp.natDegree ≤ p * f.natDegree - 1 ∧
            ‖n • Complex.exp z - p • aeval z gp‖ ≤ c ^ p / (p - 1).factorial := by
  let f := integerMinpoly z
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f
    (integerMinpoly_eval_zero_ne_zero hz hz0)
  refine ⟨f, c, integerMinpoly_ne_zero hz,
    integerMinpoly_eval_zero_ne_zero hz hz0, integerMinpoly_mem_aroots hz, ?_⟩
  intro p hp hprime
  obtain ⟨n, hn, gp, hdeg, happ⟩ := hc p hp hprime
  exact ⟨n, hn, gp, hdeg, happ (integerMinpoly_mem_aroots hz)⟩

/-- A common integer polynomial for a finite collection of algebraic exponents. -/
def commonIntegerPolynomial (s : Finset ℂ) : ℤ[X] :=
  ∏ z ∈ s, integerMinpoly z

theorem commonIntegerPolynomial_ne_zero (s : Finset ℂ)
    (halg : ∀ z ∈ s, IsAlgebraic ℚ z) :
    commonIntegerPolynomial s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact integerMinpoly_ne_zero (halg z hz)

theorem commonIntegerPolynomial_eval_zero_ne_zero (s : Finset ℂ)
    (halg : ∀ z ∈ s, IsAlgebraic ℚ z)
    (hne : ∀ z ∈ s, z ≠ 0) :
    (commonIntegerPolynomial s).eval 0 ≠ 0 := by
  rw [commonIntegerPolynomial, eval_prod]
  apply Finset.prod_ne_zero_iff.mpr
  intro z hz
  exact integerMinpoly_eval_zero_ne_zero (halg z hz) (hne z hz)

theorem mem_aroots_commonIntegerPolynomial (s : Finset ℂ)
    (halg : ∀ z ∈ s, IsAlgebraic ℚ z) {z : ℂ} (hz : z ∈ s) :
    z ∈ (commonIntegerPolynomial s).aroots ℂ := by
  apply mem_aroots.mpr
  refine ⟨commonIntegerPolynomial_ne_zero s halg, ?_⟩
  rw [commonIntegerPolynomial, map_prod]
  exact Finset.prod_eq_zero hz integerMinpoly_aeval

/-- `exp_polynomial_approx`, packaged for any finite family of nonzero algebraic exponents. -/
theorem finite_algebraic_exp_approximation (s : Finset ℂ)
    (halg : ∀ z ∈ s, IsAlgebraic ℚ z)
    (hne : ∀ z ∈ s, z ≠ 0) :
    ∃ (f : ℤ[X]) (c : ℝ),
      f ≠ 0 ∧ f.eval 0 ≠ 0 ∧ (∀ z ∈ s, z ∈ f.aroots ℂ) ∧
      ∀ p > (f.eval 0).natAbs, p.Prime →
        ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧
          ∃ gp : ℤ[X], gp.natDegree ≤ p * f.natDegree - 1 ∧
            ∀ z ∈ s,
              ‖n • Complex.exp z - p • aeval z gp‖ ≤
                c ^ p / (p - 1).factorial := by
  let f := commonIntegerPolynomial s
  have hf0 : f.eval 0 ≠ 0 := commonIntegerPolynomial_eval_zero_ne_zero s halg hne
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  refine ⟨f, c, commonIntegerPolynomial_ne_zero s halg, hf0,
    fun z hz ↦ mem_aroots_commonIntegerPolynomial s halg hz, ?_⟩
  intro p hp hprime
  obtain ⟨n, hn, gp, hdeg, happ⟩ := hc p hp hprime
  exact ⟨n, hn, gp, hdeg,
    fun z hz ↦ happ (mem_aroots_commonIntegerPolynomial s halg hz)⟩

theorem aeval_exp_eq_exp_sum (q : ℤ[X]) (z : ℂ) :
    aeval (Complex.exp z) q =
      q.sum fun k a ↦ (a : ℂ) * Complex.exp (k * z) := by
  rw [aeval_def, eval₂_eq_sum]
  rw [sum_def, sum_def]
  apply Finset.sum_congr rfl
  intro k _
  rw [Complex.exp_nat_mul]
  rfl

/-- Algebraicity of `exp z` produces a nontrivial integral exponential relation whose constant
coefficient is nonzero. -/
theorem integral_exp_relation_of_isAlgebraic {z : ℂ}
    (hexp : IsAlgebraic ℚ (Complex.exp z)) :
    ∃ q : ℤ[X], q ≠ 0 ∧ q.eval 0 ≠ 0 ∧
      q.sum (fun k a ↦ (a : ℂ) * Complex.exp (k * z)) = 0 := by
  let q := integerMinpoly (Complex.exp z)
  refine ⟨q, integerMinpoly_ne_zero hexp,
    integerMinpoly_eval_zero_ne_zero hexp (Complex.exp_ne_zero z), ?_⟩
  rw [← aeval_exp_eq_exp_sum]
  exact integerMinpoly_aeval

theorem normalized_integral_exp_relation_of_isAlgebraic {z : ℂ}
    (hexp : IsAlgebraic ℚ (Complex.exp z)) :
    ∃ q : ℤ[X], q.eval 0 ≠ 0 ∧
      ((q.eval (0 : ℤ) : ℤ) : ℂ) +
        ∑ k ∈ q.support.erase 0,
          (q.coeff k : ℂ) * Complex.exp (k * z) = 0 := by
  obtain ⟨q, -, hq0, hrel⟩ := integral_exp_relation_of_isAlgebraic hexp
  refine ⟨q, hq0, ?_⟩
  have hzero_mem : 0 ∈ q.support := by
    rw [mem_support_iff, coeff_zero_eq_eval_zero]
    exact hq0
  rw [sum_def] at hrel
  calc
    ((q.eval (0 : ℤ) : ℤ) : ℂ) +
          ∑ k ∈ q.support.erase 0,
            (q.coeff k : ℂ) * Complex.exp (k * z) =
        (∑ k ∈ q.support.erase 0,
            (q.coeff k : ℂ) * Complex.exp (k * z)) +
          (q.coeff 0 : ℂ) * Complex.exp (((0 : ℕ) : ℂ) * z) := by
            simp only [Nat.cast_zero, zero_mul, exp_zero, mul_one,
              coeff_zero_eq_eval_zero]
            rw [add_comm]
    _ = ∑ k ∈ q.support,
          (q.coeff k : ℂ) * Complex.exp (k * z) :=
      Finset.sum_erase_add q.support
        (fun k ↦ (q.coeff k : ℂ) * Complex.exp (k * z)) hzero_mem
    _ = 0 := hrel

/-- The nonzero exponents occurring in an integral polynomial relation in `exp z`. -/
def nonconstantExponents (q : ℤ[X]) (z : ℂ) : Finset ℂ :=
  (q.support.erase 0).image fun k : ℕ ↦ (k : ℂ) * z

theorem nonconstantExponents_isAlgebraic {q : ℤ[X]} {z u : ℂ}
    (hz : IsAlgebraic ℚ z) (hu : u ∈ nonconstantExponents q z) :
    IsAlgebraic ℚ u := by
  obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hu
  have hk : IsAlgebraic ℚ (k : ℂ) := by
    simpa using isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (k : ℚ)
  exact hk.mul hz

theorem nonconstantExponents_ne_zero {q : ℤ[X]} {z u : ℂ}
    (hz0 : z ≠ 0) (hu : u ∈ nonconstantExponents q z) : u ≠ 0 := by
  obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hu
  have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
  exact mul_ne_zero (Nat.cast_ne_zero.mpr hk0) hz0

/-- The exact simultaneous approximation data supplied by Mathlib, retaining estimates for every
root of the common integer polynomial (and hence for the Galois conjugates needed next). -/
def HasLindemannApproximants (s : Finset ℂ) : Prop :=
  ∃ (f : ℤ[X]) (c : ℝ),
    f ≠ 0 ∧ f.eval 0 ≠ 0 ∧ (∀ z ∈ s, z ∈ f.aroots ℂ) ∧
    ∀ p > (f.eval 0).natAbs, p.Prime →
      ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧
        ∃ gp : ℤ[X], gp.natDegree ≤ p * f.natDegree - 1 ∧
          ∀ {r : ℂ}, r ∈ f.aroots ℂ →
            ‖n • Complex.exp r - p • aeval r gp‖ ≤
              c ^ p / (p - 1).factorial

theorem hasLindemannApproximants_nonconstantExponents {z : ℂ} (q : ℤ[X])
    (hz : IsAlgebraic ℚ z) (hz0 : z ≠ 0) :
    HasLindemannApproximants (nonconstantExponents q z) := by
  let s := nonconstantExponents q z
  let f := commonIntegerPolynomial s
  have halg : ∀ u ∈ s, IsAlgebraic ℚ u :=
    fun _ hu ↦ nonconstantExponents_isAlgebraic hz hu
  have hne : ∀ u ∈ s, u ≠ 0 :=
    fun _ hu ↦ nonconstantExponents_ne_zero hz0 hu
  have hf0 : f.eval 0 ≠ 0 := commonIntegerPolynomial_eval_zero_ne_zero s halg hne
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  exact ⟨f, c, commonIntegerPolynomial_ne_zero s halg, hf0,
    fun u hu ↦ mem_aroots_commonIntegerPolynomial s halg hu, hc⟩

/-- The first missing arithmetic step after Mathlib's analytic approximation theorem.

The intended proof first constructs the correct Galois-symmetric auxiliary quantity, scales its
evaluations to algebraic integers, proves the resulting integer nonzero modulo a sufficiently
large prime, and then uses the factorial estimate to show that its absolute value is less than
one. One cannot simply transport the original relation through embeddings, since field embeddings
do not commute with the analytic exponential map. -/
def LindemannArithmeticStep : Prop :=
  ∀ (z : ℂ) (q : ℤ[X]),
    IsAlgebraic ℚ z → z ≠ 0 → q.eval 0 ≠ 0 →
    HasLindemannApproximants (nonconstantExponents q z) →
    ((q.eval (0 : ℤ) : ℤ) : ℂ) +
      ∑ k ∈ q.support.erase 0,
        (q.coeff k : ℂ) * Complex.exp (k * z) ≠ 0

/-- Once the missing arithmetic step is supplied, Mathlib's analytic estimate gives
Hermite--Lindemann. -/
theorem hermiteLindemann_of_arithmeticStep (harith : LindemannArithmeticStep) :
    HermiteLindemannStatement := by
  intro z hz hz0 hexp
  obtain ⟨q, hq0, hrel⟩ :=
    normalized_integral_exp_relation_of_isAlgebraic hexp
  exact (harith z q hz hz0 hq0
    (hasLindemannApproximants_nonconstantExponents q hz hz0)) hrel

/-- Conversely, Hermite--Lindemann rules out the integral exponential relation appearing in
`LindemannArithmeticStep`. The approximation data is not needed in this direction. -/
theorem arithmeticStep_of_hermiteLindemann
    (hHL : HermiteLindemannStatement) : LindemannArithmeticStep := by
  intro z q hz hz0 hq0 _ hrel
  have hq_ne : q ≠ 0 := by
    intro hq
    apply hq0
    rw [hq]
    simp
  have hzero_mem : 0 ∈ q.support := by
    rw [mem_support_iff, coeff_zero_eq_eval_zero]
    exact hq0
  have hsum :
      q.sum (fun k a ↦ (a : ℂ) * Complex.exp (k * z)) = 0 := by
    rw [sum_def, ← Finset.sum_erase_add q.support
      (fun k ↦ (q.coeff k : ℂ) * Complex.exp (k * z)) hzero_mem]
    simpa [coeff_zero_eq_eval_zero, add_comm] using hrel
  have hqeval : aeval (Complex.exp z) q = 0 := by
    rw [aeval_exp_eq_exp_sum]
    exact hsum
  have hexpZ : IsAlgebraic ℤ (Complex.exp z) :=
    ⟨q, hq_ne, hqeval⟩
  have hexpQ : IsAlgebraic ℚ (Complex.exp z) :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hexpZ
  exact (hHL z hz hz0) hexpQ

/-- The named arithmetic step is exactly equivalent to Hermite--Lindemann, not a weaker
near-final lemma. It packages the entire remaining arithmetic nonvanishing argument. -/
theorem lindemannArithmeticStep_iff_hermiteLindemann :
    LindemannArithmeticStep ↔ HermiteLindemannStatement := by
  constructor
  · exact hermiteLindemann_of_arithmeticStep
  · exact arithmeticStep_of_hermiteLindemann

/-- The factorial decay required at the end of the classical contradiction is already in
Mathlib. -/
theorem eventually_scaled_pow_div_factorial_pred_lt_one (a c : ℝ) :
    ∀ᶠ p : ℕ in Filter.atTop,
      a * c ^ p / (p - 1).factorial < 1 := by
  exact (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop a c 1).eventually_lt_const
    zero_lt_one

/-- An eventual condition on naturals can be met by a prime. -/
theorem exists_prime_of_eventually {P : ℕ → Prop}
    (hP : ∀ᶠ n : ℕ in Filter.atTop, P n) :
    ∃ p : ℕ, p.Prime ∧ P p := by
  rw [Filter.eventually_atTop] at hP
  obtain ⟨N, hN⟩ := hP
  obtain ⟨p, hNp, hp⟩ := Nat.exists_infinite_primes N
  exact ⟨p, hp, hN p hNp⟩

/-- The analytic approximation theorem already suffices to prove the transcendence of `exp m`
for every nonzero integer `m`.  In this case no Galois descent is needed: all exponents `k * m`
in a hypothetical integral relation are integers, so the weighted sum of the integer-polynomial
evaluations `gₚ(k * m)` is itself an integer.

The proof constructs an integer

`D = nₚ * q(0) + p * ∑ k, qₖ * gₚ(k * m)`.

It is nonzero modulo `p`, while the simultaneous analytic estimates and the assumed exponential
relation force `|D| < 1`, a contradiction. -/
theorem exp_intCast_transcendental (m : ℤ) (hm : m ≠ 0) :
    Transcendental ℚ (Complex.exp (m : ℂ)) := by
  intro hexp
  have hzalg : IsAlgebraic ℚ (m : ℂ) := by
    exact isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (m : ℚ)
  have hz0 : (m : ℂ) ≠ 0 := by exact_mod_cast hm
  obtain ⟨q, hq0, hrel⟩ :=
    normalized_integral_exp_relation_of_isAlgebraic hexp
  obtain ⟨f, c, -, -, hroots, happrox⟩ :=
    hasLindemannApproximants_nonconstantExponents q hzalg hz0
  let weight : ℝ :=
    ∑ k ∈ q.support.erase 0, ‖(q.coeff k : ℂ)‖
  have hevent : ∀ᶠ p : ℕ in Filter.atTop,
      (f.eval 0).natAbs < p ∧ (q.eval 0).natAbs < p ∧
        weight * |c| ^ p / (p - 1).factorial < 1 := by
    filter_upwards [Filter.eventually_gt_atTop (f.eval 0).natAbs,
      Filter.eventually_gt_atTop (q.eval 0).natAbs,
      eventually_scaled_pow_div_factorial_pred_lt_one weight |c|] with p hp_f hp_q hp_small
    exact ⟨hp_f, hp_q, hp_small⟩
  obtain ⟨p, hp, hp_f, hp_q, hp_small⟩ := exists_prime_of_eventually hevent
  obtain ⟨n, hn, gp, -, happ⟩ := happrox p hp_f hp
  let B : ℤ :=
    ∑ k ∈ q.support.erase 0, q.coeff k * gp.eval ((k : ℤ) * m)
  have hB :
      ∑ k ∈ q.support.erase 0,
          (q.coeff k : ℂ) * aeval ((k : ℂ) * (m : ℂ)) gp = (B : ℂ) := by
    simp only [B, Int.cast_sum, Int.cast_mul]
    apply Finset.sum_congr rfl
    intro k _
    congr 1
    rw [show (k : ℂ) * (m : ℂ) = (((k : ℤ) * m : ℤ) : ℂ) by
      push_cast
      rfl]
    rw [aeval_def]
    exact eval₂_at_apply _ _
  have hcpow (p : ℕ) : c ^ p ≤ |c| ^ p := by
    rw [← abs_pow]
    exact le_abs_self _
  have hterm (k : ℕ) (hk : k ∈ q.support.erase 0) :
      ‖(q.coeff k : ℂ) *
          (n • Complex.exp ((k : ℂ) * (m : ℂ)) -
            p • aeval ((k : ℂ) * (m : ℂ)) gp)‖ ≤
        ‖(q.coeff k : ℂ)‖ * (|c| ^ p / (p - 1).factorial) := by
    rw [norm_mul]
    gcongr
    refine (happ (hroots _ ?_)).trans ?_
    · exact Finset.mem_image.mpr ⟨k, hk, rfl⟩
    · exact div_le_div_of_nonneg_right (hcpow p) (Nat.cast_nonneg _)
  let E : ℂ :=
    ∑ k ∈ q.support.erase 0,
      (q.coeff k : ℂ) *
        (n • Complex.exp ((k : ℂ) * (m : ℂ)) -
          p • aeval ((k : ℂ) * (m : ℂ)) gp)
  have hEnorm : ‖E‖ ≤ weight * |c| ^ p / (p - 1).factorial := by
    calc
      ‖E‖ ≤ ∑ k ∈ q.support.erase 0,
          ‖(q.coeff k : ℂ)‖ * (|c| ^ p / (p - 1).factorial) := by
            exact norm_sum_le_of_le _ hterm
      _ = weight * (|c| ^ p / (p - 1).factorial) := by
            rw [Finset.sum_mul]
      _ = weight * |c| ^ p / (p - 1).factorial := by ring
  have hexpsum :
      ∑ k ∈ q.support.erase 0,
          (q.coeff k : ℂ) * Complex.exp ((k : ℂ) * (m : ℂ)) =
        -((q.eval (0 : ℤ) : ℤ) : ℂ) := by
    linear_combination hrel
  let D : ℤ := n * q.eval 0 + (p : ℤ) * B
  have hE : E = -(D : ℂ) := by
    dsimp only [E]
    simp_rw [zsmul_eq_mul, nsmul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    calc
      (∑ k ∈ q.support.erase 0,
          (q.coeff k : ℂ) * ((n : ℂ) *
            Complex.exp ((k : ℂ) * (m : ℂ)))) -
          ∑ k ∈ q.support.erase 0,
            (q.coeff k : ℂ) * ((p : ℂ) *
              aeval ((k : ℂ) * (m : ℂ)) gp) =
        (n : ℂ) *
            (∑ k ∈ q.support.erase 0,
              (q.coeff k : ℂ) * Complex.exp ((k : ℂ) * (m : ℂ))) -
          (p : ℂ) *
            (∑ k ∈ q.support.erase 0,
              (q.coeff k : ℂ) * aeval ((k : ℂ) * (m : ℂ)) gp) := by
                congr 1 <;> rw [Finset.mul_sum] <;>
                  apply Finset.sum_congr rfl <;> intro k hk <;> ring
      _ = -(D : ℂ) := by rw [hexpsum, hB]; dsimp only [D]; push_cast; ring
  have hD : D ≠ 0 := by
    intro hD0
    have hp_dvd : (p : ℤ) ∣ n * q.eval 0 := by
      refine ⟨-B, ?_⟩
      dsimp only [D] at hD0
      linear_combination hD0
    rcases Int.Prime.dvd_mul hp hp_dvd with hn' | hq'
    · exact hn ((Int.natCast_dvd).2 hn')
    · have hle : p ≤ (q.eval 0).natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr hq0) hq'
      omega
  have hDnorm : (1 : ℝ) ≤ ‖(D : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hD
  rw [hE, norm_neg] at hEnorm
  exact (not_lt_of_ge (hDnorm.trans hEnorm)) hp_small

/-- The exponential of every nonzero rational number is transcendental.  Raising a hypothetical
algebraic value `exp x` to the positive denominator of `x` would make `exp x.num` algebraic,
contradicting `exp_intCast_transcendental`. -/
theorem exp_ratCast_transcendental (x : ℚ) (hx : x ≠ 0) :
    Transcendental ℚ (Complex.exp (x : ℂ)) := by
  intro hexp
  have hmul : (x.den : ℚ) * x = x.num := by
    have hden : (x.den : ℚ) ≠ 0 := by exact_mod_cast x.den_nz
    have hnum : (x.num : ℚ) = x * x.den :=
      (div_eq_iff hden).mp x.num_div_den
    calc
      (x.den : ℚ) * x = x * x.den := mul_comm _ _
      _ = x.num := hnum.symm
  have halgNum : IsAlgebraic ℚ (Complex.exp (x.num : ℂ)) := by
    rw [show Complex.exp (x.num : ℂ) = Complex.exp (x : ℂ) ^ x.den by
      rw [← Complex.exp_nat_mul]
      congr 1
      exact_mod_cast hmul.symm]
    exact hexp.pow x.den
  exact (exp_intCast_transcendental x.num (Rat.num_ne_zero.mpr hx)) halgNum

/-- Schanuel's one-variable bound holds unconditionally at every nonzero rational input. -/
theorem bound_singleton_ratCast (x : ℚ) (hx : x ≠ 0) :
    Bound (singletonFamily (x : ℂ)) :=
  bound_singleton_of_exp_transcendental (exp_ratCast_transcendental x hx)

/-- The missing arithmetic step therefore implies Schanuel's one-dimensional bound. -/
theorem schanuel_one_of_arithmeticStep (harith : LindemannArithmeticStep)
    (z : ℂ) (hz : LinearIndependent ℚ (singletonFamily z)) :
    Bound (singletonFamily z) := by
  exact hermiteLindemann_implies_bound_singleton
    (hermiteLindemann_of_arithmeticStep harith) z hz

end

end Schanuel.LindemannAttempt
