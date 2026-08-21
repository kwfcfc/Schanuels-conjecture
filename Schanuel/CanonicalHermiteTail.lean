import Mathlib.Algebra.Polynomial.SumIteratedDerivative

/-!
# A canonical factorial-divided Hermite tail

This isolates the algebraic normalization hidden by the existential witnesses in
`LindemannWeierstrass.exp_polynomial_approx`.
-/

namespace Schanuel.CanonicalHermiteTail

open Finset Polynomial
open scoped Nat

/-- The canonical quotient of the `k`-th derivative by `k!`. -/
noncomputable def dividedIteratedDerivative (h : ℤ[X]) (k : ℕ) : ℤ[X] :=
  ∑ x ∈ (derivative^[k] h).support,
    C ((x + k).choose k • h.coeff (x + k)) * X ^ x

theorem factorial_smul_dividedIteratedDerivative (h : ℤ[X]) (k : ℕ) :
    k ! • dividedIteratedDerivative h k = derivative^[k] h := by
  simpa [dividedIteratedDerivative] using
    (iterate_derivative_eq_factorial_smul_sum h k).symm

theorem natDegree_dividedIteratedDerivative_le (h : ℤ[X]) (k : ℕ) :
    (dividedIteratedDerivative h k).natDegree ≤ h.natDegree - k := by
  refine (natDegree_sum_le _ _).trans ?_
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun x hx ↦ ?_⟩
  exact (natDegree_C_mul_le _ _).trans <| (natDegree_X_pow_le _).trans <|
    (le_natDegree_of_mem_supp _ hx).trans <| natDegree_iterate_derivative h k

/-- The sum of all derivatives of order at least `p`, divided by `p!`. -/
noncomputable def hermiteTail (h : ℤ[X]) (p : ℕ) : ℤ[X] :=
  ∑ k ∈ Ico p (h.natDegree + 1),
    (k ! / p !) • dividedIteratedDerivative h k

theorem factorial_smul_hermiteTail (h : ℤ[X]) (p : ℕ) :
    p ! • hermiteTail h p =
      ∑ k ∈ Ico p (h.natDegree + 1), derivative^[k] h := by
  rw [hermiteTail, smul_sum]
  apply sum_congr rfl
  intro k hk
  rw [smul_smul]
  have hpk : p ! ∣ k ! := Nat.factorial_dvd_factorial (mem_Ico.mp hk).1
  rw [Nat.mul_div_cancel' hpk]
  exact factorial_smul_dividedIteratedDerivative h k

theorem natDegree_hermiteTail_le (h : ℤ[X]) (p : ℕ) :
    (hermiteTail h p).natDegree ≤ h.natDegree - p := by
  refine (natDegree_sum_le _ _).trans ?_
  rw [fold_max_le]
  refine ⟨Nat.zero_le _, fun k hk ↦ ?_⟩
  exact (natDegree_smul_le _ _).trans <|
    (natDegree_dividedIteratedDerivative_le h k).trans <|
      Nat.sub_le_sub_left (mem_Ico.mp hk).1 _

theorem eval_sumIDeriv_eq_factorial_smul_hermiteTail_at_root
    (h : ℤ[X]) {p : ℕ} (_hp : 0 < p) (hpdeg : p ≤ h.natDegree + 1) (r : ℤ)
    (hr : ((X : ℤ[X]) - C r) ^ p ∣ h) :
    eval r (sumIDeriv h) = p ! • eval r (hermiteTail h p) := by
  obtain ⟨h', hh'⟩ := hr
  rw [sumIDeriv_apply]
  have hrange : range (h.natDegree + 1) =
      range p ∪ Ico p (h.natDegree + 1) := by
    ext k
    simp only [mem_range, mem_union, mem_Ico]
    omega
  rw [hrange, sum_union]
  · rw [eval_add, eval_finset_sum, eval_finset_sum]
    have hlow : ∑ k ∈ range p, eval r (derivative^[k] h) = 0 := by
      apply sum_eq_zero
      intro k hk
      simpa using aeval_iterate_derivative_of_lt h p r (by simpa using hh')
        (mem_range.mp hk)
    rw [hlow, zero_add, ← eval_finset_sum, ← factorial_smul_hermiteTail h p,
      eval_smul]
  · rw [disjoint_left]
    intro k hkrange hkIco
    exact (mem_Ico.mp hkIco).1.not_gt (mem_range.mp hkrange)

theorem aeval_sumIDeriv_eq_factorial_smul_hermiteTail_at_root
    {A : Type*} [CommRing A] [Algebra ℤ A] (h : ℤ[X]) {p : ℕ}
    (hpdeg : p ≤ h.natDegree + 1) (r : A)
    (hr : ((X : A[X]) - C r) ^ p ∣ h.map (algebraMap ℤ A)) :
    aeval r (sumIDeriv h) = p ! • aeval r (hermiteTail h p) := by
  obtain ⟨h', hh'⟩ := hr
  rw [sumIDeriv_apply]
  have hrange : range (h.natDegree + 1) =
      range p ∪ Ico p (h.natDegree + 1) := by
    ext k
    simp only [mem_range, mem_union, mem_Ico]
    omega
  rw [hrange, sum_union]
  · rw [map_add, map_sum, map_sum]
    have hlow : ∑ k ∈ range p, aeval r (derivative^[k] h) = 0 := by
      apply sum_eq_zero
      intro k hk
      exact aeval_iterate_derivative_of_lt h p r (by simpa using hh') (mem_range.mp hk)
    rw [hlow, zero_add, ← map_sum, ← factorial_smul_hermiteTail h p, map_nsmul]
  · rw [disjoint_left]
    intro k hkrange hkIco
    exact (mem_Ico.mp hkIco).1.not_gt (mem_range.mp hkrange)

/-- Canonical form of `eval_sumIDeriv_of_pos`: the boundary derivative of order `p - 1`
is separated from the factorial-divided tail. -/
theorem eval_sumIDeriv_eq_boundary_add_tail
    (h : ℤ[X]) {p : ℕ} (hp : 0 < p) (hpdeg : p ≤ h.natDegree + 1) (r : ℤ)
    (h' : ℤ[X]) (hh : h = ((X : ℤ[X]) - C r) ^ (p - 1) * h') :
    eval r (sumIDeriv h) =
      (p - 1)! • h'.eval r + p ! • eval r (hermiteTail h p) := by
  rw [sumIDeriv_apply]
  have hrange : range (h.natDegree + 1) =
      range p ∪ Ico p (h.natDegree + 1) := by
    ext k
    simp only [mem_range, mem_union, mem_Ico]
    omega
  rw [hrange, sum_union]
  · rw [eval_add, eval_finset_sum, eval_finset_sum]
    have hlow : ∑ k ∈ range p, eval r (derivative^[k] h) =
        (p - 1)! • h'.eval r := by
      have hp' : p - 1 + 1 = p := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hp.ne')
      rw [← hp', sum_range_succ]
      have hvanish : ∑ k ∈ range (p - 1), eval r (derivative^[k] h) = 0 := by
        apply sum_eq_zero
        intro k hk
        simpa using aeval_iterate_derivative_of_lt h (p - 1) r (by simpa using hh)
          (mem_range.mp hk)
      rw [hvanish, zero_add]
      simpa using aeval_iterate_derivative_self h (p - 1) r (by simpa using hh)
    rw [hlow, ← eval_finset_sum, ← factorial_smul_hermiteTail h p, eval_smul]
  · rw [disjoint_left]
    intro k hkrange hkIco
    exact (mem_Ico.mp hkIco).1.not_gt (mem_range.mp hkrange)

/-- The integer numerator attached to the canonical tail. -/
noncomputable def hermiteNumerator (f : ℤ[X]) (p : ℕ) : ℤ :=
  f.eval 0 ^ p + p • eval 0 (hermiteTail (X ^ (p - 1) * f ^ p) p)

theorem hermiteNumerator_normalization (f : ℤ[X]) (p : ℕ) :
    hermiteNumerator f p - p • eval 0 (hermiteTail (X ^ (p - 1) * f ^ p) p) =
      f.eval 0 ^ p := by
  simp [hermiteNumerator]

theorem natDegree_hermiteTail_special_le
    (f : ℤ[X]) {p : ℕ} (hp : 0 < p) (hf : f ≠ 0) :
    (hermiteTail (X ^ (p - 1) * f ^ p) p).natDegree ≤ p * f.natDegree - 1 := by
  have hX : (X : ℤ[X]) ^ (p - 1) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hfp : f ^ p ≠ 0 := pow_ne_zero _ hf
  refine (natDegree_hermiteTail_le _ p).trans_eq ?_
  rw [natDegree_mul hX hfp, natDegree_X_pow, natDegree_pow]
  omega

theorem eval_sumIDeriv_special_eq_factorial_smul_hermiteNumerator
    (f : ℤ[X]) {p : ℕ} (hp : 0 < p) (hf0 : f.eval 0 ≠ 0) :
    eval 0 (sumIDeriv (X ^ (p - 1) * f ^ p)) =
      (p - 1)! • hermiteNumerator f p := by
  have hf : f ≠ 0 := fun hf ↦ hf0 (by simp [hf])
  have hX : (X : ℤ[X]) ^ (p - 1) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hfp : f ^ p ≠ 0 := pow_ne_zero _ hf
  have hpdeg : p ≤ (X ^ (p - 1) * f ^ p : ℤ[X]).natDegree + 1 := by
    rw [natDegree_mul hX hfp, natDegree_pow, natDegree_X]
    omega
  have hfac : p ! = (p - 1)! * p := by
    rw [show p = (p - 1) + 1 by omega, Nat.factorial_succ, Nat.mul_comm]
    simp
  rw [eval_sumIDeriv_eq_boundary_add_tail _ hp hpdeg 0 (f ^ p) (by simp)]
  simp only [eval_pow, hermiteNumerator]
  rw [smul_add, smul_smul, hfac]

end Schanuel.CanonicalHermiteTail
