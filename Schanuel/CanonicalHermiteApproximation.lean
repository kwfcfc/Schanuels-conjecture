import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Schanuel.CanonicalHermiteTail

/-!
# Canonical Hermite approximation

This makes the polynomial hidden in `LindemannWeierstrass.exp_polynomial_approx`
explicit: it is the factorial-divided Hermite tail from
`Schanuel.CanonicalHermiteTail`.
-/

namespace Schanuel.CanonicalHermiteApproximation

noncomputable section

open Finset Polynomial
open scoped Nat
open Complex

open Schanuel.CanonicalHermiteTail

/-- The analytic remainder associated to the sum of all iterated derivatives. -/
private def remainder (h : ℂ[X]) (s : ℂ) : ℂ :=
  exp s * h.sumIDeriv.eval 0 - h.sumIDeriv.eval s

private theorem remainder_eq_integral (h : ℂ[X]) (s : ℂ) :
    remainder h s =
      exp s * (s * ∫ x in 0..1, exp (-(x • s)) * h.eval (x • s)) := by
  rw [LindemannWeierstrass.integral_exp_mul_eval, mul_add, mul_neg, exp_neg,
    mul_inv_cancel_left₀ (exp_ne_zero s), neg_add_eq_sub, remainder]

set_option backward.isDefEq.respectTransparency false in
private theorem remainder_le_aux (h : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(h p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p : ℕ,
      ‖remainder (h p) s‖ ≤
        Real.exp s.re * (Real.exp ‖s‖ * c' ^ p * ‖s‖) := by
  refine ⟨|c|, abs_nonneg _, fun p => ?_⟩
  rw [remainder_eq_integral (h p) s, mul_comm s, norm_mul, norm_mul, norm_exp]
  gcongr
  rw [intervalIntegral.integral_of_le zero_le_one, ← mul_one (_ * _)]
  convert MeasureTheory.norm_setIntegral_le_of_norm_le_const _ _
  · rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero]
  · rw [Real.volume_Ioc, sub_zero]
    exact ENNReal.ofReal_lt_top
  intro x hx
  rw [norm_mul, norm_exp]
  gcongr
  · simp only [Set.mem_Ioc] at hx
    apply (re_le_norm _).trans
    rw [norm_neg, norm_smul, Real.norm_of_nonneg hx.1.le]
    exact mul_le_of_le_one_left (norm_nonneg _) hx.2
  · rw [← abs_pow]
    exact (hc p x hx).trans (le_abs_self _)

private theorem remainder_le (h : ℕ → ℂ[X]) (s : ℂ) (c : ℝ)
    (hc : ∀ p : ℕ, ∀ x ∈ Set.Ioc (0 : ℝ) 1, ‖(h p).eval (x • s)‖ ≤ c ^ p) :
    ∃ c' ≥ 0, ∀ p ≠ 0, ‖remainder (h p) s‖ ≤ c' ^ p := by
  obtain ⟨c', hc', h'⟩ := remainder_le_aux h s c hc
  let c₁ := max (Real.exp s.re) 1
  let c₂ := max (Real.exp ‖s‖) 1
  let c₃ := max ‖s‖ 1
  refine ⟨c₁ * (c₂ * c' * c₃), by positivity, fun p hp => (h' p).trans ?_⟩
  simp_rw [mul_pow]
  have le_max_one_pow {x : ℝ} : x ≤ max x 1 ^ p :=
    (max_cases x 1).elim (fun hx => by
      rw [hx.1]
      exact le_self_pow₀ hx.2 hp) (fun hx => by rw [hx.1, one_pow]; exact hx.2.le)
  gcongr <;> exact le_max_one_pow

private theorem remainder_special_le (f : ℤ[X]) (s : ℂ) :
    ∃ c ≥ 0, ∀ p ≠ 0,
      ‖remainder (map (algebraMap ℤ ℂ) (X ^ (p - 1) * f ^ p)) s‖ ≤ c ^ p := by
  have hb : Bornology.IsBounded
      ((fun x : ℝ => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1) := by
    have hsub :
        (fun x : ℝ => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Ioc 0 1 ⊆
          (fun x : ℝ => max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) '' Set.Icc 0 1 :=
      Set.image_mono Set.Ioc_subset_Icc_self
    refine (IsCompact.image isCompact_Icc ?_).isBounded.subset hsub
    fun_prop
  obtain ⟨c, hc⟩ := hb.exists_norm_le
  simp_rw [Real.norm_eq_abs] at hc
  refine remainder_le _ s c (fun p x hx => ?_)
  specialize hc (max (x * ‖s‖) 1 * ‖aeval (x * s) f‖) (Set.mem_image_of_mem _ hx)
  grw [← hc]
  simp only [Polynomial.map_mul, Polynomial.map_pow, map_X, eval_mul, eval_pow, eval_X,
    norm_mul, Complex.norm_pow, real_smul, norm_real, ← eval₂_eq_eval_map, ← aeval_def,
    abs_mul, abs_norm, mul_pow, Real.norm_of_nonneg hx.1.le]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg (norm_nonneg _) _)
  rw [← mul_pow, abs_of_nonneg (by positivity), max_def]
  split_ifs with hx1
  · rw [one_pow]
    exact pow_le_one₀ (mul_nonneg hx.1.le (norm_nonneg _)) hx1
  · push Not at hx1
    exact pow_le_pow_right₀ hx1.le (Nat.sub_le _ _)

private theorem canonical_error_mul_factorial
    (f : ℤ[X]) {p : ℕ} (hp : 0 < p) (hf0 : f.eval 0 ≠ 0) {r : ℂ}
    (hr : r ∈ f.aroots ℂ) :
    (((hermiteNumerator f p : ℤ) : ℂ) * exp r -
        (p : ℂ) * aeval r (hermiteTail (X ^ (p - 1) * f ^ p) p)) * (p - 1)! =
      remainder (map (algebraMap ℤ ℂ) (X ^ (p - 1) * f ^ p)) r := by
  let h : ℤ[X] := X ^ (p - 1) * f ^ p
  let gp : ℤ[X] := hermiteTail h p
  have hf : f ≠ 0 := fun hf => hf0 (by simp [hf])
  have hX : (X : ℤ[X]) ^ (p - 1) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hfp : f ^ p ≠ 0 := pow_ne_zero _ hf
  have hpdeg : p ≤ h.natDegree + 1 := by
    dsimp only [h]
    rw [natDegree_mul hX hfp, natDegree_pow, natDegree_X]
    omega
  have hroot : ((X : ℂ[X]) - C r) ^ p ∣ h.map (algebraMap ℤ ℂ) := by
    rw [mem_roots'] at hr
    dsimp only [h]
    simp only [Polynomial.map_mul, Polynomial.map_pow, map_X]
    exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd (dvd_iff_isRoot.mpr hr.2) p) _
  have hsumr : aeval r (sumIDeriv h) = p ! • aeval r gp :=
    aeval_sumIDeriv_eq_factorial_smul_hermiteTail_at_root h hpdeg r hroot
  have hsum0 : eval 0 (sumIDeriv h) = (p - 1)! • hermiteNumerator f p := by
    simpa only [h] using eval_sumIDeriv_special_eq_factorial_smul_hermiteNumerator f hp hf0
  have hsum0C : aeval (0 : ℂ) (sumIDeriv h) =
      ((p - 1)! : ℂ) * (hermiteNumerator f p : ℂ) := by
    rw [aeval_def, eval₂_at_zero]
    rw [coeff_zero_eq_eval_zero]
    have hc := congrArg (algebraMap ℤ ℂ) hsum0
    simpa only [eval₂_at_zero, map_nsmul, nsmul_eq_mul, map_mul, map_natCast] using hc
  have hfac : p * (p - 1)! = p ! := Nat.mul_factorial_pred hp.ne'
  have hfacC : (p : ℂ) * ((p - 1)! : ℂ) = (p ! : ℂ) := by exact_mod_cast hfac
  change (((hermiteNumerator f p : ℤ) : ℂ) * exp r -
      (p : ℂ) * aeval r gp) * (p - 1)! = remainder (map (algebraMap ℤ ℂ) h) r
  rw [remainder, ← aeval_sumIDeriv_eq_eval ℂ h 0, ← aeval_sumIDeriv_eq_eval ℂ h r]
  simp only [nsmul_eq_mul] at hsumr
  rw [hsum0C, hsumr]
  rw [← hfacC]
  ring

/--
The canonical form of the Hermite approximation theorem.  Unlike
`LindemannWeierstrass.exp_polynomial_approx`, both integer objects are fixed in
advance: `gp` is `hermiteTail (X ^ (p - 1) * f ^ p) p`, and its numerator is
`hermiteNumerator f p`.
-/
theorem canonical_exp_polynomial_approx (f : ℤ[X]) (hf0 : f.eval 0 ≠ 0) :
    ∃ c,
      ∀ p > (f.eval 0).natAbs, p.Prime →
        ¬ (p : ℤ) ∣ hermiteNumerator f p ∧
        (hermiteTail (X ^ (p - 1) * f ^ p) p).natDegree ≤
          p * f.natDegree - 1 ∧
        hermiteNumerator f p -
            p • eval 0 (hermiteTail (X ^ (p - 1) * f ^ p) p) = f.eval 0 ^ p ∧
        ∀ {r : ℂ}, r ∈ f.aroots ℂ →
          ‖(hermiteNumerator f p : ℤ) • exp r -
              p • aeval r (hermiteTail (X ^ (p - 1) * f ^ p) p)‖ ≤
            c ^ p / (p - 1)! := by
  simp_rw [nsmul_eq_mul, zsmul_eq_mul]
  choose c' hc' hrem using remainder_special_le f
  let roots := ((f.aroots ℂ).map c').toFinset
  refine ⟨if hroots : roots.Nonempty then roots.max' hroots else 0, ?_⟩
  intro p hpbig hpprime
  constructor
  · simp only [hermiteNumerator, nsmul_eq_mul]
    rw [dvd_add_left (dvd_mul_right _ _)]
    contrapose! hpbig with hpdiv
    exact Nat.le_of_dvd (Int.natAbs_pos.mpr hf0)
      (Int.natCast_dvd.mp (Int.Prime.dvd_pow' hpprime hpdiv))
  constructor
  · exact natDegree_hermiteTail_special_le f hpprime.pos
      (fun hf => hf0 (by simp [hf]))
  constructor
  · exact hermiteNumerator_normalization f p
  intro r hr
  rw [le_div_iff₀ (Nat.cast_pos.mpr (Nat.factorial_pos _) : (0 : ℝ) < _),
    ← norm_natCast, ← norm_mul, canonical_error_mul_factorial f hpprime.pos hf0 hr]
  refine (hrem r p hpprime.ne_zero).trans (pow_le_pow_left₀ (hc' r) ?_ _)
  have hrmem : c' r ∈ roots := by
    simpa only [roots, Multiset.mem_toFinset] using Multiset.mem_map_of_mem c' hr
  have hroots : roots.Nonempty := ⟨c' r, hrmem⟩
  simpa only [hroots, ↓reduceDIte] using Finset.le_max' roots (c' r) hrmem

/--
The canonical witnesses recover the complete public interface of
`LindemannWeierstrass.exp_polynomial_approx`.
-/
theorem exp_polynomial_approx_of_canonical (f : ℤ[X]) (hf0 : f.eval 0 ≠ 0) :
    ∃ c,
      ∀ p > (f.eval 0).natAbs, p.Prime →
        ∃ n : ℤ, ¬ (p : ℤ) ∣ n ∧ ∃ gp : ℤ[X],
          gp.natDegree ≤ p * f.natDegree - 1 ∧
          ∀ {r : ℂ}, r ∈ f.aroots ℂ →
            ‖n • exp r - p • aeval r gp‖ ≤ c ^ p / (p - 1)! := by
  obtain ⟨c, hc⟩ := canonical_exp_polynomial_approx f hf0
  refine ⟨c, fun p hp hpprime => ?_⟩
  obtain ⟨hn, hdeg, -, herr⟩ := hc p hp hpprime
  exact ⟨hermiteNumerator f p, hn,
    hermiteTail (X ^ (p - 1) * f ^ p) p, hdeg, herr⟩

end

end Schanuel.CanonicalHermiteApproximation
