import Schanuel.GaloisStableAnalytic2
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Additive and multiplicative algebraic ranks

For a finite complex tuple `z`, this file considers rational coefficient vectors `m` for
which either the linear combination `m · z`, or its exponential, is algebraic.  Both loci are
rational subspaces.  Hermite--Lindemann makes them disjoint when `z` is rationally linearly
independent, and finite-dimensional linear algebra then gives a complementary quotient-rank
inequality.

The conclusion is deliberately phrased only in terms of linear ranks.  Neither quotient rank
is, by itself, a lower bound for transcendence degree.
-/

namespace Schanuel

open Function

noncomputable section

/-- The rational linear combination of the entries of `z` with coefficient vector `m`. -/
def rationalCombination {n : ℕ} (z : Fin n → ℂ) : (Fin n → ℚ) →ₗ[ℚ] ℂ :=
  Fintype.linearCombination ℚ z

@[simp]
theorem rationalCombination_apply {n : ℕ} (z : Fin n → ℂ) (m : Fin n → ℚ) :
    rationalCombination z m = ∑ i, (m i : ℂ) * z i := by
  simp [rationalCombination, Fintype.linearCombination_apply, Algebra.smul_def]

/-- Rational coefficient vectors whose linear combination of `z` is algebraic. -/
def additiveAlgebraicKernel {n : ℕ} (z : Fin n → ℂ) : Submodule ℚ (Fin n → ℚ) where
  carrier := {m | IsAlgebraic ℚ (rationalCombination z m)}
  zero_mem' := by
    change IsAlgebraic ℚ (rationalCombination z 0)
    rw [map_zero]
    exact isAlgebraic_zero
  add_mem' := by
    intro x y hx hy
    change IsAlgebraic ℚ (rationalCombination z x) at hx
    change IsAlgebraic ℚ (rationalCombination z y) at hy
    change IsAlgebraic ℚ (rationalCombination z (x + y))
    rw [map_add]
    exact hx.add hy
  smul_mem' := by
    intro q x hx
    change IsAlgebraic ℚ (rationalCombination z x) at hx
    change IsAlgebraic ℚ (rationalCombination z (q • x))
    rw [map_smul]
    exact hx.smul q

@[simp]
theorem mem_additiveAlgebraicKernel {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℚ} :
    m ∈ additiveAlgebraicKernel z ↔ IsAlgebraic ℚ (rationalCombination z m) :=
  Iff.rfl

/-- Algebraicity of `exp x` is preserved after multiplying `x` by a rational number. -/
theorem isAlgebraic_exp_rat_smul (q : ℚ) {x : ℂ}
    (hx : IsAlgebraic ℚ (Complex.exp x)) :
    IsAlgebraic ℚ (Complex.exp (q • x)) := by
  have hden : 0 < q.den := q.den_pos
  apply IsAlgebraic.of_pow hden
  have hpow : Complex.exp (q • x) ^ q.den = Complex.exp ((q.num : ℂ) * x) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    simp only [Algebra.smul_def]
    have hq : (q.den : ℚ) * q = (q.num : ℚ) := by
      have hden0 : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
      have h := (div_eq_iff hden0).mp q.num_div_den
      calc
        (q.den : ℚ) * q = q * q.den := mul_comm _ _
        _ = (q.num : ℚ) := h.symm
    have hqC : (q.den : ℂ) * algebraMap ℚ ℂ q = (q.num : ℂ) := by
      calc
        (q.den : ℂ) * algebraMap ℚ ℂ q =
            algebraMap ℚ ℂ (q.den : ℚ) * algebraMap ℚ ℂ q := by simp
        _ = algebraMap ℚ ℂ ((q.den : ℚ) * q) := by rw [map_mul]
        _ = algebraMap ℚ ℂ (q.num : ℚ) := by rw [hq]
        _ = (q.num : ℂ) := by simp
    rw [← mul_assoc, hqC]
  rw [hpow, Complex.exp_int_mul]
  cases q.num with
  | ofNat n => simpa using hx.pow n
  | negSucc n =>
      rw [zpow_negSucc]
      exact (hx.pow (n + 1)).inv

/-- Rational coefficient vectors whose exponential linear combination is algebraic. -/
def multiplicativeAlgebraicKernel {n : ℕ} (z : Fin n → ℂ) :
    Submodule ℚ (Fin n → ℚ) where
  carrier := {m | IsAlgebraic ℚ (Complex.exp (rationalCombination z m))}
  zero_mem' := by
    change IsAlgebraic ℚ (Complex.exp (rationalCombination z 0))
    rw [map_zero, Complex.exp_zero]
    exact isAlgebraic_one
  add_mem' := by
    intro x y hx hy
    change IsAlgebraic ℚ (Complex.exp (rationalCombination z x)) at hx
    change IsAlgebraic ℚ (Complex.exp (rationalCombination z y)) at hy
    change IsAlgebraic ℚ (Complex.exp (rationalCombination z (x + y)))
    rw [map_add, Complex.exp_add]
    exact hx.mul hy
  smul_mem' := by
    intro q x hx
    change IsAlgebraic ℚ (Complex.exp (rationalCombination z x)) at hx
    change IsAlgebraic ℚ (Complex.exp (rationalCombination z (q • x)))
    rw [map_smul]
    exact isAlgebraic_exp_rat_smul q hx

@[simp]
theorem mem_multiplicativeAlgebraicKernel
    {n : ℕ} {z : Fin n → ℂ} {m : Fin n → ℚ} :
    m ∈ multiplicativeAlgebraicKernel z ↔
      IsAlgebraic ℚ (Complex.exp (rationalCombination z m)) :=
  Iff.rfl

/-- Hermite--Lindemann makes the additive and multiplicative algebraic kernels disjoint. -/
theorem disjoint_algebraicKernels {n : ℕ} {z : Fin n → ℂ}
    (hz : LinearIndependent ℚ z) :
    Disjoint (additiveAlgebraicKernel z) (multiplicativeAlgebraicKernel z) := by
  rw [Submodule.disjoint_def]
  intro m hmadd hmmul
  have hzero : rationalCombination z m = 0 := by
    by_contra hne
    have htrans :=
      LindemannAttempt.hermiteLindemann_of_galoisStableEndpoint
        (rationalCombination z m) hmadd hne
    exact htrans hmmul
  have hinj : Function.Injective (rationalCombination z) := by
    simpa [rationalCombination] using hz.fintypeLinearCombination_injective
  exact hinj (by simpa using hzero)

/-- The two algebraic-kernel dimensions have sum at most the tuple length. -/
theorem finrank_algebraicKernels_le {n : ℕ} {z : Fin n → ℂ}
    (hz : LinearIndependent ℚ z) :
    Module.finrank ℚ (additiveAlgebraicKernel z) +
        Module.finrank ℚ (multiplicativeAlgebraicKernel z) ≤ n := by
  simpa using Submodule.finrank_add_finrank_le_of_disjoint
    (disjoint_algebraicKernels hz)

/-- Complementary quotient-rank form: the additive and multiplicative non-algebraic ranks
have sum at least the tuple length. -/
theorem le_finrank_quotient_algebraicKernels {n : ℕ} {z : Fin n → ℂ}
    (hz : LinearIndependent ℚ z) :
    n ≤ Module.finrank ℚ ((Fin n → ℚ) ⧸ additiveAlgebraicKernel z) +
      Module.finrank ℚ ((Fin n → ℚ) ⧸ multiplicativeAlgebraicKernel z) := by
  have hadd := (additiveAlgebraicKernel z).finrank_quotient_add_finrank
  have hmul := (multiplicativeAlgebraicKernel z).finrank_quotient_add_finrank
  have hker := finrank_algebraicKernels_le hz
  have hambient : Module.finrank ℚ (Fin n → ℚ) = n := by simp
  omega

end

end Schanuel
