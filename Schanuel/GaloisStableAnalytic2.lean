import Schanuel.LindemannStableEndpoint
import Schanuel.LindemannIntegralReduction

/-!
# From the stable endpoint to Hermite--Lindemann

This file supplies the final bridge from an algebraic-integer exponent in `ℂ` to the
finite Galois setting of `exponentialEval_ne_zero_of_integralSupport_of_galoisStable`.
-/

namespace Schanuel.LindemannAttempt

open Complex Polynomial
open scoped AddMonoidAlgebra

noncomputable section

open GaloisStableRelation

/-- The stable-relation endpoint proves the arithmetic step for algebraic-integer exponents. -/
theorem integralLindemannArithmeticStep_of_galoisStableEndpoint :
    IntegralLindemannArithmeticStep := by
  intro z q hzint hz0 hq0 _ hrel
  have hzalg : IsAlgebraic ℚ z :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ ℂ).mp hzint.isAlgebraic
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
  let Omega := algebraicClosure ℚ ℂ
  letI : IsAlgClosure ℚ Omega := by
    dsimp [Omega]
    exact algebraicClosure.isAlgClosure ℚ ℂ
  letI : IsGalois ℚ Omega := IsAlgClosure.isGalois ℚ Omega
  let zOmega : Omega :=
    ⟨z, mem_algebraicClosure_iff.mpr hzalg⟩
  let L : FiniteGaloisIntermediateField ℚ Omega :=
    FiniteGaloisIntermediateField.adjoin ℚ ({zOmega} : Set Omega)
  letI : FiniteDimensional ℚ L := L.finiteDimensional
  letI : IsGalois ℚ L := L.isGalois
  let w : L :=
    ⟨zOmega, FiniteGaloisIntermediateField.subset_adjoin ℚ
      ({zOmega} : Set Omega) (Set.mem_singleton zOmega)⟩
  let iota : L →+* ℂ :=
    Omega.val.toRingHom.comp L.toIntermediateField.val.toRingHom
  have hiota : iota w = z := rfl
  have hw0 : w ≠ 0 := by
    intro hw
    apply hz0
    have := congrArg iota hw
    simpa [hiota] using this
  have hwint : IsIntegral ℤ w := by
    apply (isIntegral_algHom_iff iota.toIntAlgHom iota.injective).mp
    simpa [hiota] using hzint
  let F : AddMonoidAlgebra ℤ L := ofPolynomial w q
  let A : AddMonoidAlgebra ℤ L :=
    stableRelation (Γ := L ≃ₐ[ℚ] L) F
  have hF0 : F ≠ 0 := ofPolynomial_ne_zero hw0 hq0
  have hFeval : exponentialEval iota.toAddMonoidHom F = 0 := by
    rw [exponentialEval_ofPolynomial]
    simpa [hiota] using hqeval
  have hAIntegral : HasIntegralSupport A := by
    exact stableRelation_ofPolynomial_hasIntegralSupport
      (Γ := L ≃ₐ[ℚ] L) hwint q
  have hA0 : A 0 ≠ 0 := by
    exact (stableRelation_apply_zero_pos
      (Γ := L ≃ₐ[ℚ] L) hF0).ne'
  have hAstable : ∀ σ : L ≃ₐ[ℚ] L, twist σ A = A := by
    intro σ
    exact twist_stableRelation σ F
  have hAeval : exponentialEval iota.toAddMonoidHom A = 0 := by
    exact exponentialEval_stableRelation_zero
      (Γ := L ≃ₐ[ℚ] L) iota.toAddMonoidHom hFeval
  exact (exponentialEval_ne_zero_of_integralSupport_of_galoisStable
    iota A hAIntegral hA0 hAstable) hAeval

/-- The previously isolated unrestricted arithmetic step is now discharged. -/
theorem lindemannArithmeticStep_of_galoisStableEndpoint :
    LindemannArithmeticStep :=
  arithmeticStep_of_integralArithmeticStep
    integralLindemannArithmeticStep_of_galoisStableEndpoint

/-- Hermite--Lindemann, obtained from the analytic approximants and Galois-stable descent. -/
theorem hermiteLindemann_of_galoisStableEndpoint : HermiteLindemannStatement := by
  exact hermiteLindemann_of_arithmeticStep
    lindemannArithmeticStep_of_galoisStableEndpoint

/-- Consequently the one-dimensional case of Schanuel's conjecture is unconditional. -/
theorem oneDimensionalConjecture_of_galoisStableEndpoint :
    OneDimensionalConjecture :=
  oneDimensionalConjecture_iff_hermiteLindemann.mpr
    hermiteLindemann_of_galoisStableEndpoint

end

end Schanuel.LindemannAttempt
