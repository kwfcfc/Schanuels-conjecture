import Mathlib.RingTheory.AlgebraicIndependent.AlgebraicClosure
import Mathlib.RingTheory.Localization.Integral

/-!
# Algebraic independence over a fraction field

This file packages the standard passage from algebraic independence over an integral domain to
algebraic independence over any chosen fraction field.  The proof factors through mathlib's
general theorem that algebraic independence is preserved by algebraic scalar extension.
-/

namespace Schanuel

open Function

/-- A family algebraically independent over an integral domain remains algebraically independent
over any fraction field of that domain, provided the ambient algebra structures form a tower. -/
theorem AlgebraicIndependent.extendScalars_fractionRing
    {ι R K A : Type*} [CommRing R] [IsDomain R] [Field K] [CommRing A]
    [Algebra R K] [IsFractionRing R K] [Algebra R A] [Algebra K A]
    [IsScalarTower R K A] {x : ι → A} (hx : AlgebraicIndependent R x) :
    AlgebraicIndependent K x := by
  letI : Algebra.IsAlgebraic R K :=
    (IsFractionRing.comap_isAlgebraic_iff (A := R) (K := K) (C := K)).mpr inferInstance
  exact hx.extendScalars K

/-- The specialization most often needed in the Schanuel development: integer-coefficient
algebraic independence implies rational-coefficient algebraic independence. -/
theorem AlgebraicIndependent.int_to_rat
    {ι A : Type*} [CommRing A] [Algebra ℚ A]
    {x : ι → A} (hx : AlgebraicIndependent ℤ x) : AlgebraicIndependent ℚ x :=
  AlgebraicIndependent.extendScalars_fractionRing
    (R := ℤ) (K := ℚ) (A := A) (x := x) hx

end Schanuel
