import Schanuel.GaloisStableArithmetic

/-!
# The analytic endpoint for a stable integral exponential relation

Once a finite exponential relation has integral support, nonzero constant coefficient, and is
stable under the full Galois group, its polynomial-evaluation auxiliary sum descends to an
ordinary integer.  The simultaneous Lindemann approximations then make a nonzero integer have
absolute value less than one.
-/

namespace Schanuel.LindemannAttempt.GaloisStableRelation

open Complex Polynomial
open scoped AddMonoidAlgebra

noncomputable section

variable {K : Type*} [Field K] [CharZero K] [Algebra ℚ K]
  [FiniteDimensional ℚ K] [IsGalois ℚ K]

/-- A Galois-stable integral formal exponential relation with nonzero constant coefficient
cannot vanish under an embedding into `ℂ`.

The proof applies `finite_algebraic_exp_approximation` simultaneously to the nonzero support,
uses `weightedAevalSum_eq_intCast` to descend the polynomial-evaluation sum to `ℤ`, chooses a
prime avoiding the two constant coefficients, and finishes with factorial decay. -/
theorem exponentialEval_ne_zero_of_integralSupport_of_galoisStable
    (iota : K →+* ℂ) (A : AddMonoidAlgebra ℤ K)
    (hIntegral : HasIntegralSupport A) (hA0 : A 0 ≠ 0)
    (hstable : ∀ σ : K ≃ₐ[ℚ] K, twist σ A = A) :
    exponentialEval iota.toAddMonoidHom A ≠ 0 := by
  classical
  intro hAeval
  let s : Finset ℂ := (A.support.erase 0).image iota
  have hs_alg : ∀ u ∈ s, IsAlgebraic ℚ u := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    have hv_int : IsIntegral ℤ v :=
      hIntegral v (Finset.mem_of_mem_erase hv)
    have hiv_int : IsIntegral ℤ (iota v) := hv_int.map iota.toIntAlgHom
    exact (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hiv_int.isAlgebraic
  have hs_ne : ∀ u ∈ s, u ≠ 0 := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hu
    simpa using iota.injective.ne (Finset.mem_erase.mp hv).1
  obtain ⟨f, c, -, -, -, happrox⟩ :=
    finite_algebraic_exp_approximation s hs_alg hs_ne
  let weight : ℝ := ∑ u ∈ A.support.erase 0, ‖(A u : ℂ)‖
  have hevent : ∀ᶠ p : ℕ in Filter.atTop,
      (f.eval 0).natAbs < p ∧ (A 0).natAbs < p ∧
        weight * |c| ^ p / (p - 1).factorial < 1 := by
    filter_upwards [Filter.eventually_gt_atTop (f.eval 0).natAbs,
      Filter.eventually_gt_atTop (A 0).natAbs,
      eventually_scaled_pow_div_factorial_pred_lt_one weight |c|] with p hp_f hp_A hp_small
    exact ⟨hp_f, hp_A, hp_small⟩
  obtain ⟨p, hp, hp_f, hp_A, hp_small⟩ := exists_prime_of_eventually hevent
  obtain ⟨n, hn, gp, -, happ⟩ := happrox p hp_f hp
  obtain ⟨m, hm⟩ := weightedAevalSum_eq_intCast A gp hIntegral hstable
  have hmC :
      ∑ u ∈ A.support.erase 0,
          (A u : ℂ) * aeval (iota u) gp = (m : ℂ) := by
    calc
      ∑ u ∈ A.support.erase 0,
          (A u : ℂ) * aeval (iota u) gp =
          iota (weightedAevalSum A gp) := by
            symm
            rw [weightedAevalSum, map_sum]
            apply Finset.sum_congr rfl
            intro u hu
            have heval : iota (aeval u gp) = aeval (iota u) gp := by
              exact map_aeval_intPolynomial iota.toRatAlgHom u gp
            rw [map_mul, heval]
            simp
      _ = iota (algebraMap ℤ K m) := by rw [hm]
      _ = (m : ℂ) := by simp
  have hcpow (p : ℕ) : c ^ p ≤ |c| ^ p := by
    rw [← abs_pow]
    exact le_abs_self _
  have hterm (u : K) (hu : u ∈ A.support.erase 0) :
      ‖(A u : ℂ) *
          (n • Complex.exp (iota u) - p • aeval (iota u) gp)‖ ≤
        ‖(A u : ℂ)‖ * (|c| ^ p / (p - 1).factorial) := by
    rw [norm_mul]
    gcongr
    refine (happ (iota u) ?_).trans ?_
    · exact Finset.mem_image.mpr ⟨u, hu, rfl⟩
    · exact div_le_div_of_nonneg_right (hcpow p) (Nat.cast_nonneg _)
  let E : ℂ :=
    ∑ u ∈ A.support.erase 0,
      (A u : ℂ) *
        (n • Complex.exp (iota u) - p • aeval (iota u) gp)
  have hEnorm : ‖E‖ ≤ weight * |c| ^ p / (p - 1).factorial := by
    calc
      ‖E‖ ≤ ∑ u ∈ A.support.erase 0,
          ‖(A u : ℂ)‖ * (|c| ^ p / (p - 1).factorial) := by
            exact norm_sum_le_of_le _ hterm
      _ = weight * (|c| ^ p / (p - 1).factorial) := by
            rw [Finset.sum_mul]
      _ = weight * |c| ^ p / (p - 1).factorial := by ring
  have hzero_mem : 0 ∈ A.support := by
    exact Finsupp.mem_support_iff.mpr hA0
  have hexpsum :
      ∑ u ∈ A.support.erase 0,
          (A u : ℂ) * Complex.exp (iota u) = -(A 0 : ℂ) := by
    have hsum :
        ∑ u ∈ A.support,
            (A u : ℂ) * Complex.exp (iota u) = 0 := by
      simpa [exponentialEval, AddMonoidAlgebra.lift_apply, Finsupp.sum,
        Algebra.smul_def] using hAeval
    rw [← Finset.sum_erase_add _ _ hzero_mem] at hsum
    simpa using (eq_neg_of_add_eq_zero_left hsum)
  let D : ℤ := n * A 0 + (p : ℤ) * m
  have hE : E = -(D : ℂ) := by
    dsimp only [E]
    simp_rw [zsmul_eq_mul, nsmul_eq_mul, mul_sub]
    rw [Finset.sum_sub_distrib]
    calc
      (∑ u ∈ A.support.erase 0,
          (A u : ℂ) * ((n : ℂ) * Complex.exp (iota u))) -
          ∑ u ∈ A.support.erase 0,
            (A u : ℂ) * ((p : ℂ) * aeval (iota u) gp) =
        (n : ℂ) *
            (∑ u ∈ A.support.erase 0,
              (A u : ℂ) * Complex.exp (iota u)) -
          (p : ℂ) *
            (∑ u ∈ A.support.erase 0,
              (A u : ℂ) * aeval (iota u) gp) := by
                congr 1 <;> rw [Finset.mul_sum] <;>
                  apply Finset.sum_congr rfl <;> intro u hu <;> ring
      _ = -(D : ℂ) := by rw [hexpsum, hmC]; dsimp only [D]; push_cast; ring
  have hD : D ≠ 0 := by
    intro hD0
    have hp_dvd : (p : ℤ) ∣ n * A 0 := by
      refine ⟨-m, ?_⟩
      dsimp only [D] at hD0
      linear_combination hD0
    rcases Int.Prime.dvd_mul hp hp_dvd with hn' | hA'
    · exact hn ((Int.natCast_dvd).2 hn')
    · have hle : p ≤ (A 0).natAbs :=
        Nat.le_of_dvd (Int.natAbs_pos.mpr hA0) hA'
      omega
  have hDnorm : (1 : ℝ) ≤ ‖(D : ℂ)‖ := by
    rw [Complex.norm_intCast]
    exact_mod_cast Int.one_le_abs hD
  rw [hE, norm_neg] at hEnorm
  exact (not_lt_of_ge (hDnorm.trans hEnorm)) hp_small

end

end Schanuel.LindemannAttempt.GaloisStableRelation
