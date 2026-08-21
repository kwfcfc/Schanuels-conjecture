import Schanuel.RationalBasisInvariance
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Rational multiplier spaces

For a finite-dimensional rational subspace `Z` of `ℂ`, the complex scalars preserving `Z`
form a rational subspace of dimension at most `dim Z`.  Evaluation at any nonzero member of
`Z` gives the elementary injection proving the bound.

We also record the corresponding exponential consequence: if multiplication by a complex
number sends every member of a finite family into its rational span, then the exponentials of
the multiplied family are integral, hence algebraic, over the original generated field.
-/

namespace Schanuel

open Function Set

noncomputable section

/-- Complex scalars whose multiplication action preserves the rational subspace `Z`. -/
def controlledMultipliers (Z : Submodule ℚ ℂ) : Submodule ℚ ℂ where
  carrier := {a | ∀ x, x ∈ Z → a * x ∈ Z}
  zero_mem' x hx := by simp
  add_mem' ha hb x hx := by
    simpa [add_mul] using Z.add_mem (ha x hx) (hb x hx)
  smul_mem' q a ha x hx := by
    rw [Rat.smul_def, mul_assoc]
    exact Z.smul_mem q (ha x hx)

/-- Evaluation of a controlled multiplier at a fixed member of `Z`. -/
def controlledMultiplierEval (Z : Submodule ℚ ℂ) (x : Z) :
    controlledMultipliers Z →ₗ[ℚ] Z where
  toFun a := ⟨(a : ℂ) * (x : ℂ), a.property x x.property⟩
  map_add' a b := by
    ext
    simp [add_mul]
  map_smul' q a := by
    ext
    simp [Rat.smul_def, mul_assoc]

/-- Evaluation at a nonzero member of `Z` distinguishes controlled multipliers. -/
theorem controlledMultiplierEval_injective (Z : Submodule ℚ ℂ) (x : Z)
    (hx : (x : ℂ) ≠ 0) :
    Function.Injective (controlledMultiplierEval Z x) := by
  intro a b hab
  apply Subtype.ext
  apply mul_right_cancel₀ hx
  exact congrArg Subtype.val hab

/-- The rational dimension of the multiplier space is at most that of the space it preserves. -/
theorem finrank_controlledMultipliers_le (Z : Submodule ℚ ℂ) [Module.Finite ℚ Z]
    (x : Z) (hx : (x : ℂ) ≠ 0) :
    Module.finrank ℚ (controlledMultipliers Z) ≤ Module.finrank ℚ Z := by
  let f := controlledMultiplierEval Z x
  letI : Module.Finite ℚ (controlledMultipliers Z) :=
    FiniteDimensional.of_injective f (controlledMultiplierEval_injective Z x hx)
  exact f.finrank_le_finrank_of_injective
    (controlledMultiplierEval_injective Z x hx)

/-- A two-dimensional rational subspace has at most two independent controlled multipliers. -/
theorem finrank_controlledMultipliers_le_two (Z : Submodule ℚ ℂ) [Module.Finite ℚ Z]
    (x : Z) (hx : (x : ℂ) ≠ 0) (hZ : Module.finrank ℚ Z ≤ 2) :
    Module.finrank ℚ (controlledMultipliers Z) ≤ 2 :=
  (finrank_controlledMultipliers_le Z x hx).trans hZ

/-- If multiplication by `a` sends a family into rational linear combinations of that family,
then every exponential in the multiplied family is integral over the original generated field. -/
theorem exp_mul_isIntegral_of_rational_combinations {n : ℕ} (z : Fin n → ℂ) (a : ℂ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : ∀ i, a * z i = ∑ j, B i j • z j) (i : Fin n) :
    IsIntegral (generatedField z) (Complex.exp (a * z i)) := by
  have hrow : rationalMatrixFamily B z i = a * z i := by
    simpa [rationalMatrixFamily] using (hB i).symm
  rw [← hrow]
  exact exp_rationalMatrixFamily_isIntegral B z i

/-- The algebraic version of `exp_mul_isIntegral_of_rational_combinations`. -/
theorem exp_mul_isAlgebraic_of_rational_combinations {n : ℕ} (z : Fin n → ℂ) (a : ℂ)
    (B : Matrix (Fin n) (Fin n) ℚ)
    (hB : ∀ i, a * z i = ∑ j, B i j • z j) (i : Fin n) :
    IsAlgebraic (generatedField z) (Complex.exp (a * z i)) :=
  (exp_mul_isIntegral_of_rational_combinations z a B hB i).isAlgebraic

end

end Schanuel
