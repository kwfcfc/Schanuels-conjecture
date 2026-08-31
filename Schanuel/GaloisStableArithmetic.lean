import Schanuel.GaloisStableRelation
import Schanuel.GaloisDescent
import Mathlib.Algebra.MonoidAlgebra.Support

/-!
# Integral support and Galois descent for stable exponential relations

This file supplies the purely algebraic handoff from a Galois-stable formal
exponential relation to an ordinary integer.  It does not transport the
analytic exponential map through field automorphisms.
-/

namespace Schanuel.LindemannAttempt.GaloisStableRelation

open Polynomial
open scoped AddMonoidAlgebra

noncomputable section

variable {K Γ : Type*}

/-- Every formal exponent occurring in `F` is integral over `ℤ`. -/
def HasIntegralSupport [CommRing K] (F : AddMonoidAlgebra ℤ K) : Prop :=
  ∀ x ∈ F.support, IsIntegral ℤ x

theorem hasIntegralSupport_zero [CommRing K] :
    HasIntegralSupport (0 : AddMonoidAlgebra ℤ K) := by
  classical
  intro x hx
  rw [Finsupp.mem_support_iff] at hx
  exact False.elim (hx rfl)

theorem hasIntegralSupport_single [CommRing K] {x : K} (hx : IsIntegral ℤ x) (a : ℤ) :
    HasIntegralSupport (AddMonoidAlgebra.single x a) := by
  classical
  intro y hy
  have : y ∈ ({x} : Finset K) := Finsupp.support_single_subset hy
  have hyx : y = x := by simpa using this
  simpa [hyx] using hx

theorem HasIntegralSupport.add [CommRing K]
    {F G : AddMonoidAlgebra ℤ K}
    (hF : HasIntegralSupport F) (hG : HasIntegralSupport G) :
    HasIntegralSupport (F + G) := by
  classical
  intro x hx
  have hx' := Finsupp.support_add hx
  rw [Finset.mem_union] at hx'
  exact hx'.elim (hF x) (hG x)

theorem HasIntegralSupport.mul [CommRing K]
    {F G : AddMonoidAlgebra ℤ K}
    (hF : HasIntegralSupport F) (hG : HasIntegralSupport G) :
    HasIntegralSupport (F * G) := by
  classical
  intro x hx
  have hx' := AddMonoidAlgebra.support_mul F G hx
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.mem_add.mp hx'
  rw [← hyz]
  exact (hF y hy).add (hG z hz)

theorem hasIntegralSupport_sum [CommRing K] {I : Type*}
    (s : Finset I) (F : I → AddMonoidAlgebra ℤ K)
    (hF : ∀ i ∈ s, HasIntegralSupport (F i)) :
    HasIntegralSupport (∑ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [hasIntegralSupport_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hF i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hF j (Finset.mem_insert_of_mem hj))

theorem ofPolynomial_hasIntegralSupport [Field K] [CharZero K]
    {z : K} (hz : IsIntegral ℤ z) (q : ℤ[X]) :
    HasIntegralSupport (ofPolynomial z q) := by
  rw [ofPolynomial]
  apply hasIntegralSupport_sum
  intro k hk
  exact hasIntegralSupport_single (hz.nsmul k) _

section Orbit

variable [Field K] [Group Γ] [Fintype Γ]
variable [MulSemiringAction Γ K]

theorem HasIntegralSupport.reflect {F : AddMonoidAlgebra ℤ K}
    (hF : HasIntegralSupport F) : HasIntegralSupport (reflect F) := by
  intro x hx
  have hneg : -x ∈ F.support := by
    rw [Finsupp.mem_support_iff] at hx ⊢
    simpa [reflect_apply] using hx
  have := (hF (-x) hneg).neg
  simpa using this

omit [Fintype Γ] in
theorem HasIntegralSupport.twist (F : AddMonoidAlgebra ℤ K)
    (hF : HasIntegralSupport F) (g : Γ) : HasIntegralSupport (twist g F) := by
  intro x hx
  have hpre : g⁻¹ • x ∈ F.support := by
    rw [Finsupp.mem_support_iff] at hx ⊢
    simpa [twist_apply] using hx
  have hi := hF (g⁻¹ • x) hpre
  have himap := hi.map (MulSemiringAction.toRingHom Γ K g).toIntAlgHom
  simpa [mul_smul] using himap

theorem orbitProduct_hasIntegralSupport (F : AddMonoidAlgebra ℤ K)
    (hF : HasIntegralSupport F) :
    HasIntegralSupport (orbitProduct (Γ := Γ) F) := by
  rw [orbitProduct]
  classical
  induction (Finset.univ : Finset Γ) using Finset.induction_on with
  | empty =>
      simpa only [Finset.prod_empty] using
        (hasIntegralSupport_single (K := K) (x := 0) isIntegral_zero 1)
  | @insert g s hg ih =>
      rw [Finset.prod_insert hg]
      exact (hF.twist F g).mul ih

/-- If the original exponent is integral, every exponent in the support of
the symmetrized relation is integral, including after exponent-reversal. -/
theorem stableRelation_ofPolynomial_hasIntegralSupport [CharZero K]
    {z : K} (hz : IsIntegral ℤ z) (q : ℤ[X]) :
    HasIntegralSupport
      (stableRelation (Γ := Γ) (ofPolynomial z q)) := by
  let F := ofPolynomial z q
  have hF : HasIntegralSupport F := ofPolynomial_hasIntegralSupport hz q
  have hN : HasIntegralSupport (orbitProduct (Γ := Γ) F) :=
    orbitProduct_hasIntegralSupport F hF
  exact hN.mul hN.reflect

end Orbit

/-- The polynomial-weighted auxiliary value attached to a formal relation,
with its constant exponent omitted. -/
def weightedAevalSum [Field K] [CharZero K]
    (A : AddMonoidAlgebra ℤ K) (gp : ℤ[X]) : K := by
  classical
  exact ∑ u ∈ A.support.erase 0, (A u : K) * aeval u gp

theorem isIntegral_aeval_intPolynomial [Field K] [CharZero K]
    {u : K} (hu : IsIntegral ℤ u) (gp : ℤ[X]) :
    IsIntegral ℤ (aeval u gp) := by
  rw [aeval_def, eval₂_eq_sum, sum_def]
  apply IsIntegral.sum
  intro n hn
  exact isIntegral_algebraMap.mul (hu.pow n)

theorem weightedAevalSum_isIntegral [Field K] [CharZero K]
    {A : AddMonoidAlgebra ℤ K} (hA : HasIntegralSupport A) (gp : ℤ[X]) :
    IsIntegral ℤ (weightedAevalSum A gp) := by
  classical
  rw [weightedAevalSum]
  apply IsIntegral.sum
  intro u hu
  have hcoeff : IsIntegral ℤ (A u : K) := by
    change IsIntegral ℤ (algebraMap ℤ K (A u))
    exact isIntegral_algebraMap
  exact hcoeff.mul
    (isIntegral_aeval_intPolynomial (hA u (Finset.mem_of_mem_erase hu)) gp)

section Descent

variable [Field K] [CharZero K] [Algebra ℚ K]
  [FiniteDimensional ℚ K] [IsGalois ℚ K]

omit [FiniteDimensional ℚ K] [IsGalois ℚ K] in
theorem weightedAevalSum_galois_fixed
    (A : AddMonoidAlgebra ℤ K) (gp : ℤ[X])
    (hstable : ∀ σ : K ≃ₐ[ℚ] K, twist σ A = A) :
    ∀ σ : K ≃ₐ[ℚ] K, σ (weightedAevalSum A gp) = weightedAevalSum A gp := by
  classical
  intro σ
  have hcoeff (u : K) : A u = A (σ u) := by
    have h := congrArg (fun B : AddMonoidAlgebra ℤ K ↦ B (σ u)) (hstable σ)
    simpa [twist_apply] using h
  have hmem (u : K) :
      u ∈ A.support.erase 0 ↔ σ u ∈ A.support.erase 0 := by
    simp only [Finset.mem_erase, Finsupp.mem_support_iff]
    constructor
    · rintro ⟨hu0, huA⟩
      constructor
      · intro hσ0
        apply hu0
        apply σ.injective
        simpa using hσ0
      · rwa [← hcoeff u]
    · rintro ⟨hσ0, hσA⟩
      constructor
      · intro hu0
        apply hσ0
        simp [hu0]
      · rwa [hcoeff u]
  calc
    σ (weightedAevalSum A gp) =
        ∑ u ∈ A.support.erase 0, (A u : K) * aeval (σ u) gp := by
          rw [weightedAevalSum, map_sum]
          simp only [map_mul, map_intCast]
          apply Finset.sum_congr rfl
          intro u hu
          exact congrArg (fun v : K ↦ (A u : K) * v)
            (map_aeval_intPolynomial σ.toAlgHom u gp)
    _ = ∑ u ∈ A.support.erase 0, (A u : K) * aeval u gp := by
      apply Finset.sum_equiv σ.toEquiv hmem
      intro u hu
      change (A u : K) * aeval (σ u) gp =
        (A (σ u) : K) * aeval (σ u) gp
      rw [← hcoeff u]
    _ = weightedAevalSum A gp := by rw [weightedAevalSum]

/-- A Galois-stable weighted sum over integral formal exponents is an
ordinary integer inside the finite Galois field. -/
theorem weightedAevalSum_eq_intCast
    (A : AddMonoidAlgebra ℤ K) (gp : ℤ[X])
    (hIntegral : HasIntegralSupport A)
    (hstable : ∀ σ : K ≃ₐ[ℚ] K, twist σ A = A) :
    ∃ m : ℤ, algebraMap ℤ K m = weightedAevalSum A gp := by
  exact eq_intCast_of_isIntegral_of_galois_fixed
    (weightedAevalSum_isIntegral hIntegral gp)
    (weightedAevalSum_galois_fixed A gp hstable)

end Descent

end

end Schanuel.LindemannAttempt.GaloisStableRelation
