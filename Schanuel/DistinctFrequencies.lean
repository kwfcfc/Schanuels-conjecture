import Schanuel

/-!
# Distinct exponential frequencies

The confluent-Vandermonde zero estimate for exponential polynomials uses the fact that
different nonnegative integral multi-indices give different frequencies when the underlying
complex numbers are linearly independent over `ℚ`.
-/

namespace Schanuel

open Function
open scoped BigOperators

noncomputable section

/-- The exponential frequency attached to a nonnegative integral multi-index. -/
def natFrequency {n : ℕ} (z : Fin n → ℂ) (β : Fin n → ℕ) : ℂ :=
  ∑ i, (β i : ℂ) * z i

/-- Rational linear independence makes the nonnegative integral frequencies distinct. -/
theorem natFrequency_injective {n : ℕ} {z : Fin n → ℂ}
    (hz : LinearIndependent ℚ z) : Function.Injective (natFrequency z) := by
  intro β γ hβγ
  funext i
  have hsum : ∑ j, (β j : ℚ) • z j = ∑ j, (γ j : ℚ) • z j := by
    simpa [natFrequency, Rat.smul_def] using hβγ
  have hi : (β i : ℚ) = (γ i : ℚ) := hz.eq_coords_of_eq hsum i
  exact_mod_cast hi

/-- The same distinct-frequency statement for a finite exponent box. -/
theorem finFrequency_injective {n E : ℕ} {z : Fin n → ℂ}
    (hz : LinearIndependent ℚ z) :
    Function.Injective
      (fun β : Fin n → Fin (E + 1) ↦ ∑ i, (β i : ℂ) * z i) := by
  intro β γ hβγ
  have hnat : (fun i ↦ (β i : ℕ)) = fun i ↦ (γ i : ℕ) :=
    natFrequency_injective hz (by simpa [natFrequency] using hβγ)
  funext i
  exact Fin.ext (congrFun hnat i)

end

end Schanuel
