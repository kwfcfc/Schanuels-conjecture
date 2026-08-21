import Schanuel.LindemannAttempt
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Safe algebraic transport and fixed-field descent

This file records the parts of a future Galois argument that field embeddings really do
transport: integer-polynomial evaluations, finite weighted sums of such evaluations, and roots of
integer polynomials.  It deliberately makes no analogous claim about `Complex.exp`, since an
abstract field embedding of `ℂ` need not commute with the analytic exponential map.

It also packages the elementary fixed-field endpoint for a finite Galois extension of `ℚ`: an
algebraic integer fixed by every rational automorphism is an ordinary integer.
-/

namespace Schanuel.LindemannAttempt

open Polynomial

noncomputable section

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra ℚ A] [Algebra ℚ B]

/-- A rational algebra homomorphism commutes with evaluation of an integer polynomial. -/
theorem map_aeval_intPolynomial (σ : A →ₐ[ℚ] B) (u : A) (g : ℤ[X]) :
    σ (aeval u g) = aeval (σ u) g := by
  symm
  exact Polynomial.aeval_algHom_apply (σ.restrictScalars ℤ) u g

/-- The weighted polynomial-evaluation sum used in the Lindemann auxiliary value is equivariant
under rational algebra homomorphisms.  This statement involves no exponential values. -/
theorem map_weighted_aeval_sum (σ : A →ₐ[ℚ] B) (z : A) (q gp : ℤ[X]) :
    σ (∑ k ∈ q.support.erase 0,
      (q.coeff k : A) * aeval ((k : A) * z) gp) =
      ∑ k ∈ q.support.erase 0,
        (q.coeff k : B) * aeval ((k : B) * σ z) gp := by
  simp_rw [map_sum, map_mul, map_aeval_intPolynomial]
  simp

variable {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
  [Module.IsTorsionFree ℤ K] [Module.IsTorsionFree ℤ L]

/-- Rational algebra homomorphisms carry roots of an integer polynomial to roots of the same
polynomial. -/
theorem map_mem_aroots_intPolynomial (σ : K →ₐ[ℚ] L)
    {f : ℤ[X]} {u : K} (hu : u ∈ f.aroots K) :
    σ u ∈ f.aroots L := by
  apply mem_aroots.mpr
  refine ⟨(mem_aroots.mp hu).1, ?_⟩
  rw [← map_aeval_intPolynomial σ u f, (mem_aroots.mp hu).2, map_zero]

variable {E : Type*} [Field E] [Algebra ℚ E]
  [FiniteDimensional ℚ E] [IsGalois ℚ E]

/-- An algebraic integer in a finite Galois extension of `ℚ` that is fixed by every rational
automorphism comes from `ℤ`.

The invariance hypothesis must be proved for the particular algebraic auxiliary quantity; it
cannot be obtained by moving an exponential relation through field automorphisms. -/
theorem eq_intCast_of_isIntegral_of_galois_fixed {x : E}
    (hx : IsIntegral ℤ x) (hfix : ∀ σ : E ≃ₐ[ℚ] E, σ x = x) :
    ∃ m : ℤ, algebraMap ℤ E m = x := by
  obtain ⟨q, hq⟩ : ∃ q : ℚ, algebraMap ℚ E q = x :=
    (IsGalois.mem_range_algebraMap_iff_fixed x).mpr hfix
  have hqint : IsIntegral ℤ q := by
    apply (isIntegral_algebraMap_iff (FaithfulSMul.algebraMap_injective ℚ E)).mp
    rw [hq]
    exact hx
  obtain ⟨m, hm⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hqint
  refine ⟨m, ?_⟩
  rw [← hq, ← hm]
  exact IsScalarTower.algebraMap_apply ℤ ℚ E m

end

end Schanuel.LindemannAttempt
