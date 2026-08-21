import Schanuel.GaloisStableAnalytic2
import Schanuel.DistinctFrequencies
import Schanuel.FractionAlgebraicIndependence
import Schanuel.LindemannDenominators
import Schanuel.RationalScaling
import Schanuel.RelativeDescent
import Mathlib.Algebra.MvPolynomial.Eval

/-!
# Schanuel's bound for algebraic input families

This file begins the multivariate extension of the stable-relation argument.  A multivariate
integer polynomial in the exponentials is encoded as a formal integral relation whose exponent
at a monomial is the corresponding nonnegative integral linear combination of the input family.
Rational linear independence makes those formal frequencies distinct.
-/

namespace Schanuel.AlgebraicInputs

open Complex MvPolynomial
open scoped AddMonoidAlgebra BigOperators

open LindemannAttempt.GaloisStableRelation

noncomputable section

/-- The additive frequency of a multivariate monomial. -/
def finsuppFrequency {n : ℕ} {K : Type*} [Field K]
    (w : Fin n → K) (d : Fin n →₀ ℕ) : K :=
  ∑ i, d i • w i

theorem map_finsuppFrequency {n : ℕ} {K : Type*} [Field K]
    (iota : K →+* ℂ) (w : Fin n → K) (d : Fin n →₀ ℕ) :
    iota (finsuppFrequency w d) = natFrequency (fun i ↦ iota (w i)) d := by
  simp [finsuppFrequency, natFrequency, map_sum, nsmul_eq_mul]

/-- Rational linear independence makes the frequency map on finitely supported monomial
exponents injective, even before embedding the containing number field into `ℂ`. -/
def frequencyEmbedding {n : ℕ} {K : Type*} [Field K]
    (iota : K →+* ℂ) (w : Fin n → K)
    (hw : LinearIndependent ℚ (fun i ↦ iota (w i))) : (Fin n →₀ ℕ) ↪ K :=
  ⟨finsuppFrequency w, by
    intro d e hde
    apply Finsupp.ext
    have hcomplex : natFrequency (fun i ↦ iota (w i)) d =
        natFrequency (fun i ↦ iota (w i)) e := by
      rw [← map_finsuppFrequency, ← map_finsuppFrequency, hde]
    have hfun := natFrequency_injective hw hcomplex
    exact fun i ↦ congrFun hfun i⟩

/-- Reindex a multivariate integer polynomial by its formal additive frequencies. -/
def ofMvPolynomial {n : ℕ} {K : Type*} [Field K]
    (iota : K →+* ℂ) (w : Fin n → K)
    (hw : LinearIndependent ℚ (fun i ↦ iota (w i)))
    (P : MvPolynomial (Fin n) ℤ) : AddMonoidAlgebra ℤ K :=
  Finsupp.embDomain (frequencyEmbedding iota w hw) P

theorem ofMvPolynomial_ne_zero {n : ℕ} {K : Type*} [Field K]
    (iota : K →+* ℂ) (w : Fin n → K)
    (hw : LinearIndependent ℚ (fun i ↦ iota (w i)))
    {P : MvPolynomial (Fin n) ℤ} (hP : P ≠ 0) :
    ofMvPolynomial iota w hw P ≠ 0 := by
  exact Finsupp.embDomain_eq_zero.not.mpr hP

theorem finsuppFrequency_isIntegral {n : ℕ} {K : Type*} [Field K]
    {w : Fin n → K} (hw : ∀ i, IsIntegral ℤ (w i)) (d : Fin n →₀ ℕ) :
    IsIntegral ℤ (finsuppFrequency w d) := by
  apply IsIntegral.sum
  intro i hi
  exact (hw i).nsmul (d i)

theorem ofMvPolynomial_hasIntegralSupport {n : ℕ} {K : Type*} [Field K]
    (iota : K →+* ℂ) (w : Fin n → K)
    (hlin : LinearIndependent ℚ (fun i ↦ iota (w i)))
    (hw : ∀ i, IsIntegral ℤ (w i)) (P : MvPolynomial (Fin n) ℤ) :
    HasIntegralSupport (ofMvPolynomial iota w hlin P) := by
  intro u hu
  rw [ofMvPolynomial, Finsupp.support_embDomain] at hu
  obtain ⟨d, hd, hdu⟩ := Finset.mem_map.mp hu
  rw [← hdu]
  exact finsuppFrequency_isIntegral hw d

theorem exponentialEval_ofMvPolynomial {n : ℕ} {K : Type*} [Field K]
    (iota : K →+* ℂ) (w : Fin n → K)
    (hlin : LinearIndependent ℚ (fun i ↦ iota (w i)))
    (P : MvPolynomial (Fin n) ℤ) :
    exponentialEval iota.toAddMonoidHom (ofMvPolynomial iota w hlin P) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ)
        (fun i ↦ Complex.exp (iota (w i))) P := by
  rw [ofMvPolynomial]
  change (Finsupp.embDomain (frequencyEmbedding iota w hlin) P).sum
      (fun u a ↦ (a : ℂ) * Complex.exp (iota u)) = _
  rw [Finsupp.sum_embDomain]
  simp only [MvPolynomial.eval₂]
  apply Finsupp.sum_congr
  intro d a
  congr 1
  change Complex.exp (iota (finsuppFrequency w d)) = _
  rw [map_finsuppFrequency, natFrequency, Complex.exp_sum]
  rw [Finsupp.prod_fintype d (fun i e ↦ Complex.exp (iota (w i)) ^ e) (by simp)]
  apply Finset.prod_congr rfl
  intro i hi
  simpa [nsmul_eq_mul] using Complex.exp_nsmul (iota (w i)) (d i)

/-- The stable Lindemann endpoint rules out every nonzero multivariate integer-polynomial
relation among exponentials of a linearly independent family of algebraic integers in a finite
Galois number field. -/
theorem eval₂_exp_ne_zero_of_integral {n : ℕ} {K : Type*} [Field K] [CharZero K]
    [Algebra ℚ K] [FiniteDimensional ℚ K] [IsGalois ℚ K]
    (iota : K →+* ℂ) (w : Fin n → K)
    (hlin : LinearIndependent ℚ (fun i ↦ iota (w i)))
    (hw : ∀ i, IsIntegral ℤ (w i))
    {P : MvPolynomial (Fin n) ℤ} (hP : P ≠ 0) :
    MvPolynomial.eval₂ (Int.castRingHom ℂ)
      (fun i ↦ Complex.exp (iota (w i))) P ≠ 0 := by
  intro hPeval
  let F : AddMonoidAlgebra ℤ K := ofMvPolynomial iota w hlin P
  let A : AddMonoidAlgebra ℤ K :=
    stableRelation (Γ := K ≃ₐ[ℚ] K) F
  have hF0 : F ≠ 0 := ofMvPolynomial_ne_zero iota w hlin hP
  have hFIntegral : HasIntegralSupport F :=
    ofMvPolynomial_hasIntegralSupport iota w hlin hw P
  have hNIntegral : HasIntegralSupport
      (orbitProduct (Γ := K ≃ₐ[ℚ] K) F) :=
    orbitProduct_hasIntegralSupport F hFIntegral
  have hAIntegral : HasIntegralSupport A := hNIntegral.mul hNIntegral.reflect
  have hA0 : A 0 ≠ 0 :=
    (stableRelation_apply_zero_pos (Γ := K ≃ₐ[ℚ] K) hF0).ne'
  have hAstable : ∀ σ : K ≃ₐ[ℚ] K, twist σ A = A := by
    intro σ
    exact twist_stableRelation σ F
  have hFeval : exponentialEval iota.toAddMonoidHom F = 0 := by
    rw [exponentialEval_ofMvPolynomial]
    exact hPeval
  have hAeval : exponentialEval iota.toAddMonoidHom A = 0 :=
    exponentialEval_stableRelation_zero
      (Γ := K ≃ₐ[ℚ] K) iota.toAddMonoidHom hFeval
  exact (exponentialEval_ne_zero_of_integralSupport_of_galoisStable
    iota A hAIntegral hA0 hAstable) hAeval

/-- Exponentials of rationally linearly independent complex algebraic integers satisfy no
nonzero multivariate polynomial relation with integer coefficients. -/
theorem algebraicIndependent_int_exp_of_isIntegral {n : ℕ} (z : Fin n → ℂ)
    (hlin : LinearIndependent ℚ z) (hzint : ∀ i, IsIntegral ℤ (z i)) :
    AlgebraicIndependent ℤ (fun i ↦ Complex.exp (z i)) := by
  let Omega := algebraicClosure ℚ ℂ
  letI : IsAlgClosure ℚ Omega := by
    dsimp [Omega]
    exact algebraicClosure.isAlgClosure ℚ ℂ
  letI : IsGalois ℚ Omega := IsAlgClosure.isGalois ℚ Omega
  let zOmega : Fin n → Omega := fun i ↦
    ⟨z i, mem_algebraicClosure_iff.mpr
      ((IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp (hzint i).isAlgebraic)⟩
  let L : FiniteGaloisIntermediateField ℚ Omega :=
    FiniteGaloisIntermediateField.adjoin ℚ (Set.range zOmega)
  letI : FiniteDimensional ℚ L := L.finiteDimensional
  letI : IsGalois ℚ L := L.isGalois
  let w : Fin n → L := fun i ↦
    ⟨zOmega i, FiniteGaloisIntermediateField.subset_adjoin ℚ
      (Set.range zOmega) (Set.mem_range_self i)⟩
  let iota : L →+* ℂ :=
    Omega.val.toRingHom.comp L.toIntermediateField.val.toRingHom
  have hiota (i : Fin n) : iota (w i) = z i := rfl
  have hwlin : LinearIndependent ℚ (fun i ↦ iota (w i)) := by
    simpa only [hiota] using hlin
  have hwint : ∀ i, IsIntegral ℤ (w i) := by
    intro i
    apply (isIntegral_algHom_iff iota.toIntAlgHom iota.injective).mp
    simpa only [hiota] using hzint i
  rw [algebraicIndependent_iff]
  intro P hPeval
  by_contra hP
  apply eval₂_exp_ne_zero_of_integral iota w hwlin hwint hP
  simpa only [MvPolynomial.aeval_def, hiota] using hPeval

/-- The same algebraic independence over `ℚ`. -/
theorem algebraicIndependent_exp_of_isIntegral {n : ℕ} (z : Fin n → ℂ)
    (hlin : LinearIndependent ℚ z) (hzint : ∀ i, IsIntegral ℤ (z i)) :
    AlgebraicIndependent ℚ (fun i ↦ Complex.exp (z i)) :=
  Schanuel.AlgebraicIndependent.int_to_rat
    (algebraicIndependent_int_exp_of_isIntegral z hlin hzint)

/-- Schanuel's bound for a rationally linearly independent family of algebraic complex numbers.
The common scaling first makes every coordinate an algebraic integer; positive rational scaling
does not change the generated transcendence degree. -/
theorem bound_of_isAlgebraic_coordinate {n : ℕ} (z : Fin n → ℂ)
    (hlin : LinearIndependent ℚ z) (hzalg : ∀ i, IsAlgebraic ℚ (z i)) :
    Bound z := by
  let s : Finset ℂ := Finset.univ.image z
  have hsalg : ∀ u ∈ s, IsAlgebraic ℚ u := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    exact hzalg i
  obtain ⟨d, hd0, hdint⟩ :=
    LindemannAttempt.exists_common_integral_scale s hsalg
  let a : ℚ := (d : ℚ) ^ 2
  have ha : 0 < a := by
    dsimp [a]
    exact sq_pos_of_ne_zero (Int.cast_ne_zero.mpr hd0)
  let w : Fin n → ℂ := ratScaleFamily a z
  have hwint : ∀ i, IsIntegral ℤ (w i) := by
    intro i
    have hdi : IsIntegral ℤ (d • z i) :=
      hdint (z i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    have hddi := hdi.smul d
    simpa [w, ratScaleFamily, a, zsmul_eq_mul, pow_two, mul_assoc] using hddi
  have hwlin : LinearIndependent ℚ w := by
    let au : ℚˣ := Units.mk0 a ha.ne'
    have h := hlin.units_smul (fun _ ↦ au)
    convert h using 1
  have hwAI : AlgebraicIndependent ℚ (fun i ↦ Complex.exp (w i)) :=
    algebraicIndependent_exp_of_isIntegral w hwlin hwint
  have hwBound : Bound w := bound_of_algebraicIndependent_exponential hwAI
  exact (bound_ratScaleFamily_iff a ha z).mp hwBound

/-- The tightness statement for algebraic inputs: their generated exponential field has
transcendence degree exactly `n`. -/
theorem trdeg_generatedField_eq_of_isAlgebraic_coordinate {n : ℕ} (z : Fin n → ℂ)
    (hlin : LinearIndependent ℚ z) (hzalg : ∀ i, IsAlgebraic ℚ (z i)) :
    Algebra.trdeg ℚ (generatedField z) = Cardinal.mk (Fin n) := by
  apply le_antisymm
  · letI : Algebra.IsAlgebraic ℚ (coordinateField z) := by
      apply IntermediateField.isAlgebraic_adjoin
      intro u hu
      obtain ⟨i, rfl⟩ := hu
      exact (hzalg i).isIntegral
    calc
      Algebra.trdeg ℚ (generatedField z) =
          Algebra.trdeg ℚ (coordinateField z) +
            Algebra.trdeg (coordinateField z) (generatedField z) :=
        (trdeg_coordinate_add_relative z).symm
      _ = Algebra.trdeg (coordinateField z) (generatedField z) := by
        rw [trdeg_eq_zero, zero_add]
      _ ≤ Cardinal.mk (Fin n) := relative_trdeg_le_cardinalMk_fin z
  · exact bound_of_isAlgebraic_coordinate z hlin hzalg

end

end Schanuel.AlgebraicInputs
