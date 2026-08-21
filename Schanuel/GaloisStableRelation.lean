import Schanuel.LindemannAttempt
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Ring.Action.Group
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.AlgebraicClosure
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.NumberTheory.NumberField.InfinitePlace.Embeddings

/-!
# Galois-stable exponential relations

This file isolates the finite group-ring symmetrization used in the arithmetic
half of Hermite--Lindemann.  An exponential relation is encoded in the additive
group algebra `ℤ[K]`.  We multiply all its translates under a finite group of
field automorphisms, and then multiply once more by the relation obtained by
negating every formal exponent.

The last multiplication is important: its coefficient at exponent zero is a
sum of squares, so it cannot disappear when distinct formal sums of conjugates
coincide.  Analytic evaluation is zero because the orbit product contains the
original relation as its identity factor.  At no point do we claim that a
field automorphism commutes with the analytic exponential map.
-/

namespace Schanuel.LindemannAttempt.GaloisStableRelation

open Complex Polynomial
open scoped AddMonoidAlgebra

noncomputable section

variable {K Γ : Type*}

/-- Negate every formal exponent in an additive group algebra. -/
def reflect [AddCommGroup K] : AddMonoidAlgebra ℤ K ≃ₐ[ℤ] AddMonoidAlgebra ℤ K :=
  AddMonoidAlgebra.domCongr ℤ ℤ (AddEquiv.neg K)

@[simp]
theorem reflect_apply [AddCommGroup K] (F : AddMonoidAlgebra ℤ K) (x : K) :
    reflect F x = F (-x) := by
  simp [reflect]

/-- The constant coefficient after multiplying by exponent-reversal is the
sum of the squares of all coefficients. -/
theorem mul_reflect_apply_zero [AddCommGroup K] (F : AddMonoidAlgebra ℤ K) :
    (F * reflect F) 0 = F.sum fun _ a ↦ a * a := by
  rw [AddMonoidAlgebra.mul_apply_left]
  simp only [add_zero, reflect_apply, neg_neg]
  rfl

/-- Consequently exponent-reversal supplies a nonzero constant coefficient
for every nonzero integral group-algebra relation. -/
theorem mul_reflect_apply_zero_pos [AddCommGroup K]
    {F : AddMonoidAlgebra ℤ K} (hF : F ≠ 0) :
    0 < (F * reflect F) 0 := by
  rw [mul_reflect_apply_zero, Finsupp.sum]
  apply Finset.sum_pos
  · intro x hx
    exact mul_self_pos.mpr (Finsupp.mem_support_iff.mp hx)
  · exact Finsupp.support_nonempty_iff.mpr hF

/-- Evaluation of a formal integral combination of elements of `K` by
`x ↦ exp(ι x)`. -/
def exponentialEval [AddCommGroup K] (iota : K →+ ℂ) :
    AddMonoidAlgebra ℤ K →+* ℂ :=
  (AddMonoidAlgebra.lift ℤ ℂ K
    { toFun := fun x ↦ Complex.exp (iota x.toAdd)
      map_one' := by simp
      map_mul' := by
        intro x y
        change Complex.exp (iota (x.toAdd + y.toAdd)) =
          Complex.exp (iota x.toAdd) * Complex.exp (iota y.toAdd)
        rw [map_add, Complex.exp_add] }).toRingHom

@[simp]
theorem exponentialEval_single [AddCommGroup K] (iota : K →+ ℂ)
    (x : K) (a : ℤ) :
    exponentialEval iota (AddMonoidAlgebra.single x a) =
      (a : ℂ) * Complex.exp (iota x) := by
  simp [exponentialEval]

/-- The group-algebra element representing `q(exp(ι z))`. -/
def ofPolynomial [AddCommGroup K] (z : K) (q : ℤ[X]) :
    AddMonoidAlgebra ℤ K :=
  ∑ k ∈ q.support, AddMonoidAlgebra.single (k • z) (q.coeff k)

theorem exponentialEval_ofPolynomial [AddCommGroup K] (iota : K →+ ℂ)
    (z : K) (q : ℤ[X]) :
    exponentialEval iota (ofPolynomial z q) =
      aeval (Complex.exp (iota z)) q := by
  rw [ofPolynomial, map_sum]
  simp_rw [exponentialEval_single, map_nsmul, Complex.exp_nsmul]
  rw [aeval_def, eval₂_eq_sum]
  rfl

/-- If `z ≠ 0`, the coefficient at exponent zero is exactly the constant
coefficient of the polynomial. -/
theorem ofPolynomial_apply_zero [Field K] [CharZero K]
    {z : K} (hz : z ≠ 0) (q : ℤ[X]) :
    ofPolynomial z q 0 = q.coeff 0 := by
  classical
  let ev0 : AddMonoidAlgebra ℤ K →+ ℤ :=
    { toFun := fun F ↦ F 0
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl }
  change ev0 (ofPolynomial z q) = q.coeff 0
  rw [ofPolynomial, map_sum]
  by_cases hmem : 0 ∈ q.support
  · rw [Finset.sum_eq_single 0]
    · simp [ev0]
    · intro k hk hk0
      simp [ev0, nsmul_eq_mul, hz, hk0]
    · simp [hmem]
  · rw [Finset.sum_eq_zero]
    · have hc : q.coeff 0 = 0 := by
        by_contra hc0
        exact hmem (mem_support_iff.mpr hc0)
      exact hc.symm
    · intro k hk
      have hk0 : k ≠ 0 := by
        intro hkzero
        exact hmem (hkzero ▸ hk)
      simp [ev0, nsmul_eq_mul, hz, hk0]

theorem ofPolynomial_ne_zero [Field K] [CharZero K]
    {z : K} (hz : z ≠ 0) {q : ℤ[X]} (hq0 : q.eval 0 ≠ 0) :
    ofPolynomial z q ≠ 0 := by
  intro hzero
  have := congrArg (fun F : AddMonoidAlgebra ℤ K ↦ F 0) hzero
  change ofPolynomial z q 0 = (0 : AddMonoidAlgebra ℤ K) 0 at this
  rw [ofPolynomial_apply_zero hz, coeff_zero_eq_eval_zero] at this
  exact hq0 this

section OrbitProduct

variable [Field K] [CharZero K] [Group Γ] [Fintype Γ]
variable [MulSemiringAction Γ K]

/-- Transport formal exponents by one member of the finite automorphism
group.  Coefficients are left untouched. -/
def twist (g : Γ) : AddMonoidAlgebra ℤ K ≃ₐ[ℤ] AddMonoidAlgebra ℤ K :=
  AddMonoidAlgebra.domCongr ℤ ℤ (DistribMulAction.toAddEquiv K g)

@[simp]
theorem twist_apply (g : Γ) (F : AddMonoidAlgebra ℤ K) (x : K) :
    twist g F x = F (g⁻¹ • x) := by
  simp [twist]

@[simp]
theorem twist_one (F : AddMonoidAlgebra ℤ K) :
    twist (1 : Γ) F = F := by
  ext x
  simp

/-- The formal Galois norm of a group-algebra relation. -/
def orbitProduct (F : AddMonoidAlgebra ℤ K) : AddMonoidAlgebra ℤ K :=
  ∏ g : Γ, twist g F

theorem orbitProduct_ne_zero {F : AddMonoidAlgebra ℤ K} (hF : F ≠ 0) :
    orbitProduct (Γ := Γ) F ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro g _
  exact (twist g).injective.ne hF

/-- Left translation permutes the factors of the orbit product. -/
theorem twist_orbitProduct (g : Γ) (F : AddMonoidAlgebra ℤ K) :
    twist g (orbitProduct (Γ := Γ) F) = orbitProduct (Γ := Γ) F := by
  rw [orbitProduct, map_prod]
  apply Fintype.prod_bijective (g * ·) (Group.mulLeft_bijective g)
  intro h
  ext x
  simp [twist, mul_smul]

/-- Transport by an additive automorphism commutes with exponent-reversal. -/
theorem twist_reflect (g : Γ) (F : AddMonoidAlgebra ℤ K) :
    twist g (reflect F) = reflect (twist g F) := by
  ext x
  simp [twist]

/-- The orbit product, multiplied by its exponent-reversal. -/
def stableRelation (F : AddMonoidAlgebra ℤ K) : AddMonoidAlgebra ℤ K :=
  orbitProduct (Γ := Γ) F * reflect (orbitProduct (Γ := Γ) F)

theorem twist_stableRelation (g : Γ) (F : AddMonoidAlgebra ℤ K) :
    twist g (stableRelation (Γ := Γ) F) = stableRelation (Γ := Γ) F := by
  rw [stableRelation, map_mul, twist_orbitProduct, twist_reflect,
    twist_orbitProduct]

theorem stableRelation_support (g : Γ) (F : AddMonoidAlgebra ℤ K) :
    (stableRelation (Γ := Γ) F).support.map
        (DistribMulAction.toAddEquiv K g).toEmbedding =
      (stableRelation (Γ := Γ) F).support := by
  have h := congrArg Finsupp.support (twist_stableRelation g F)
  simpa [twist] using h

theorem exponentialEval_orbitProduct_zero (iota : K →+ ℂ)
    {F : AddMonoidAlgebra ℤ K} (hF : exponentialEval iota F = 0) :
    exponentialEval iota (orbitProduct (Γ := Γ) F) = 0 := by
  rw [orbitProduct, map_prod]
  apply Finset.prod_eq_zero (Finset.mem_univ (1 : Γ))
  rw [twist_one]
  exact hF

theorem exponentialEval_stableRelation_zero (iota : K →+ ℂ)
    {F : AddMonoidAlgebra ℤ K} (hF : exponentialEval iota F = 0) :
    exponentialEval iota (stableRelation (Γ := Γ) F) = 0 := by
  rw [stableRelation, map_mul,
    exponentialEval_orbitProduct_zero iota hF, zero_mul]

theorem stableRelation_apply_zero_pos {F : AddMonoidAlgebra ℤ K} (hF : F ≠ 0) :
    0 < stableRelation (Γ := Γ) F 0 := by
  exact mul_reflect_apply_zero_pos (orbitProduct_ne_zero (Γ := Γ) hF)

theorem stableRelation_ne_zero {F : AddMonoidAlgebra ℤ K} (hF : F ≠ 0) :
    stableRelation (Γ := Γ) F ≠ 0 := by
  intro hzero
  have h := congrArg (fun A : AddMonoidAlgebra ℤ K ↦ A 0) hzero
  have hpos := stableRelation_apply_zero_pos (Γ := Γ) hF
  exact hpos.ne' h

/-- A finite integral relation at `exp(ι z)` yields a nonzero, finite,
Galois-stable integral relation with nonzero constant coefficient and the same
analytic vanishing.  The automorphisms act only on formal exponents. -/
theorem exists_stableRelation_of_aeval_eq_zero
    (iota : K →+ ℂ) {z : K} (hz : z ≠ 0) {q : ℤ[X]}
    (hq0 : q.eval 0 ≠ 0)
    (hrel : aeval (Complex.exp (iota z)) q = 0) :
    ∃ A : AddMonoidAlgebra ℤ K,
      A ≠ 0 ∧ A 0 ≠ 0 ∧ exponentialEval iota A = 0 ∧
        (∀ g : Γ, twist g A = A) ∧
        ∀ g : Γ,
          A.support.map (DistribMulAction.toAddEquiv K g).toEmbedding = A.support := by
  let F := ofPolynomial z q
  let A := stableRelation (Γ := Γ) F
  have hF0 : F ≠ 0 := ofPolynomial_ne_zero hz hq0
  have hFeval : exponentialEval iota F = 0 := by
    rw [exponentialEval_ofPolynomial]
    exact hrel
  refine ⟨A, stableRelation_ne_zero (Γ := Γ) hF0,
    (stableRelation_apply_zero_pos (Γ := Γ) hF0).ne',
    exponentialEval_stableRelation_zero (Γ := Γ) iota hFeval, ?_, ?_⟩
  · exact fun g ↦ twist_stableRelation g F
  · exact fun g ↦ stableRelation_support g F

end OrbitProduct

/-- Specialization to the full automorphism group of a normal number field.
This is the form needed after placing an algebraic exponent in a finite normal
extension of `ℚ`. -/
theorem exists_numberField_stableRelation
    (K : Type*) [Field K] [NumberField K] [Normal ℚ K]
    (iota : K →+* ℂ) {z : K} (hz : z ≠ 0) {q : ℤ[X]}
    (hq0 : q.eval 0 ≠ 0)
    (hrel : aeval (Complex.exp (iota z)) q = 0) :
    ∃ A : AddMonoidAlgebra ℤ K,
      A ≠ 0 ∧ A 0 ≠ 0 ∧ exponentialEval iota.toAddMonoidHom A = 0 ∧
        (∀ g : K ≃ₐ[ℚ] K, twist g A = A) ∧
        ∀ g : K ≃ₐ[ℚ] K,
          A.support.map (DistribMulAction.toAddEquiv K g).toEmbedding = A.support := by
  exact exists_stableRelation_of_aeval_eq_zero
    (K := K) (Γ := K ≃ₐ[ℚ] K) iota.toAddMonoidHom hz hq0 hrel

/-- The preceding construction applied directly to an algebraic complex
number.  The finite normal field is chosen inside the relative algebraic
closure of `ℚ` in `ℂ`, so its displayed embedding really sends `w` to the
original complex number `z`. -/
theorem exists_complex_stableRelation
    {z : ℂ} (hzalg : IsAlgebraic ℚ z) (hz0 : z ≠ 0) {q : ℤ[X]}
    (hq0 : q.eval 0 ≠ 0)
    (hrel : aeval (Complex.exp z) q = 0) :
    ∃ (L : FiniteGaloisIntermediateField ℚ
          (algebraicClosure ℚ ℂ))
      (iota : L →+* ℂ) (w : L) (A : AddMonoidAlgebra ℤ L),
      iota w = z ∧ A ≠ 0 ∧ A 0 ≠ 0 ∧
        exponentialEval iota.toAddMonoidHom A = 0 ∧
        (∀ g : L ≃ₐ[ℚ] L, twist g A = A) ∧
        ∀ g : L ≃ₐ[ℚ] L,
          A.support.map (DistribMulAction.toAddEquiv L g).toEmbedding = A.support := by
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
  letI : NumberField L :=
    { to_charZero := inferInstance
      to_finiteDimensional := inferInstance }
  letI : Normal ℚ L := IsGalois.to_normal
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
  have hrel' : aeval (Complex.exp (iota w)) q = 0 := by
    rw [hiota]
    exact hrel
  obtain ⟨A, hA0, hAc, hAe, hAt, hAs⟩ :=
    exists_numberField_stableRelation L iota hw0 hq0 hrel'
  exact ⟨L, iota, w, A, hiota, hA0, hAc, hAe, hAt, hAs⟩

end

end Schanuel.LindemannAttempt.GaloisStableRelation
