import Schanuel.LindemannAttempt

/-!
# Denominator control for Lindemann approximants

The analytic approximation theorem produces integer-polynomial evaluations at algebraic complex
numbers.  Such evaluations need not be algebraic integers when the arguments are not integral.
This file proves the elementary scaling lemmas needed before a trace or Galois-descent argument:

* a finite set of algebraic complex numbers admits one nonzero integer scale making every member
  integral over `ℤ`;
* if `d * u` is integral and `g` has degree at most `N`, then
  `d ^ N * g(u)` is integral;
* the same scale works simultaneously for one polynomial evaluated on a finite algebraic set.

These results are unconditional.  They do not assert the symmetric nonvanishing statement still
needed for Hermite--Lindemann.
-/

namespace Schanuel.LindemannAttempt

open Complex Polynomial

noncomputable section

/-- A finite family of algebraic complex numbers has a common nonzero integer denominator whose
product makes every member integral over `ℤ`. -/
theorem exists_common_integral_scale (s : Finset ℂ)
    (halg : ∀ u ∈ s, IsAlgebraic ℚ u) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ u ∈ s, IsIntegral ℤ (d • u) := by
  have halgZ : ∀ u ∈ s, IsAlgebraic ℤ u := by
    intro u hu
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mpr (halg u hu)
  choose d hd0 hdint using fun u : s ↦
    (halgZ u u.property).exists_integral_multiple
  let D : ℤ := ∏ u : s, d u
  refine ⟨D, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun u _ ↦ hd0 u
  · intro u hu
    let us : s := ⟨u, hu⟩
    rw [show D = (∏ v ∈ Finset.univ.erase us, d v) * d us by
      change (∏ v : s, d v) = _
      rw [Finset.prod_erase_mul _ _ (Finset.mem_univ us)]]
    rw [mul_smul]
    exact (hdint us).smul (∏ v ∈ Finset.univ.erase us, d v)

/-- If `d * u` is integral, multiplying a degree-at-most-`N` integer-polynomial evaluation at
`u` by `d ^ N` makes the evaluation integral. -/
theorem scaled_aeval_isIntegral (u : ℂ) (d : ℤ) (g : ℤ[X]) (N : ℕ)
    (hdeg : g.natDegree ≤ N) (hu : IsIntegral ℤ (d • u)) :
    IsIntegral ℤ ((d : ℂ) ^ N * aeval u g) := by
  rw [aeval_def, eval₂_eq_sum, sum_def, Finset.mul_sum]
  apply IsIntegral.sum
  intro k hk
  have hkN : k ≤ N :=
    (le_natDegree_of_ne_zero (mem_support_iff.mp hk)).trans hdeg
  have hcoeff : IsIntegral ℤ (g.coeff k : ℂ) :=
    isIntegral_algebraMap
  have hscale : IsIntegral ℤ ((d : ℂ) ^ (N - k)) :=
    (isIntegral_algebraMap : IsIntegral ℤ (algebraMap ℤ ℂ d)).pow (N - k)
  have hterm := hcoeff.mul (hscale.mul (hu.pow k))
  convert hterm using 1
  have hdpow : (d : ℂ) ^ N = (d : ℂ) ^ (N - k) * (d : ℂ) ^ k := by
    conv_lhs => rw [show N = (N - k) + k by omega, pow_add]
  have hcast (x : ℤ) : algebraMap ℤ ℂ x = (x : ℂ) := by
    rw [algebraMap_int_eq]
    rfl
  rw [hdpow, Algebra.smul_def, mul_pow]
  rw [hcast, hcast]
  ring

/-- One nonzero integer scale simultaneously clears the denominators in all values `g(u)` for a
fixed bounded-degree integer polynomial and a finite algebraic set of arguments. -/
theorem exists_common_scale_aeval_isIntegral (s : Finset ℂ)
    (halg : ∀ u ∈ s, IsAlgebraic ℚ u) (g : ℤ[X]) (N : ℕ)
    (hdeg : g.natDegree ≤ N) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ u ∈ s,
      IsIntegral ℤ ((d : ℂ) ^ N * aeval u g) := by
  obtain ⟨d, hd0, hdint⟩ := exists_common_integral_scale s halg
  exact ⟨d, hd0, fun u hu ↦ scaled_aeval_isIntegral u d g N hdeg (hdint u hu)⟩

/-- The common scale can be chosen before the polynomial and its degree bound.  In particular,
one scale works for an entire prime-indexed family of Lindemann approximation polynomials. -/
theorem exists_uniform_common_scale_aeval_isIntegral (s : Finset ℂ)
    (halg : ∀ u ∈ s, IsAlgebraic ℚ u) :
    ∃ d : ℤ, d ≠ 0 ∧ ∀ (g : ℤ[X]) (N : ℕ), g.natDegree ≤ N →
      ∀ u ∈ s, IsIntegral ℤ ((d : ℂ) ^ N * aeval u g) := by
  obtain ⟨d, hd0, hdint⟩ := exists_common_integral_scale s halg
  exact ⟨d, hd0, fun g N hdeg u hu ↦
    scaled_aeval_isIntegral u d g N hdeg (hdint u hu)⟩

/-- A fixed denominator raised to a degree growing at most linearly with `p` only changes the
exponential base in the factorial-decay estimate. -/
theorem eventually_scaled_degree_pow_mul_pow_div_factorial_pred_lt_one
    (a c : ℝ) (d : ℤ) (D : ℕ) :
    ∀ᶠ p : ℕ in Filter.atTop,
      a * |(d : ℝ)| ^ (p * D) * |c| ^ p / (p - 1).factorial < 1 := by
  filter_upwards [eventually_scaled_pow_div_factorial_pred_lt_one
    a (|(d : ℝ)| ^ D * |c|)] with p hp
  simpa [mul_pow, pow_mul, Nat.mul_comm, mul_assoc] using hp

end

end Schanuel.LindemannAttempt
