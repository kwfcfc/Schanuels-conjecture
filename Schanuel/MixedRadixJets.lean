import Schanuel.ConfluentVandermonde
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Polynomial.DegreeLT

/-!
# Confluent and mixed-radix jet isomorphisms

This file isolates the finite-dimensional algebraic core of the mixed-radix
auxiliary-function construction.

First, polynomials of degree less than `nodes * multiplicity` are identified
with their confluent jets at the consecutive nodes.  The injectivity is exactly
`polynomial_eq_zero_of_confluent_zeros` from `ConfluentVandermonde`.

Second, a family whose columns have distinct mixed-radix initial orders has an
invertible initial-jet matrix.  This is the tensor-scalarization step: after a
one-coordinate confluent jet basis is normalized, adjoining a block of size
`inner` sends the pair of local jet indices `(outer, innerIndex)` to the order
`innerIndex + inner * outer`.  Iteration gives the usual mixed-radix orders.

The results are purely algebraic.  They make no transcendence, exponential, or
linear-independence assumption.
-/

namespace Schanuel

open Polynomial Matrix

noncomputable section

section ConfluentJet

variable (K : Type*) [Field K] [CharZero K]

/-- The confluent jet map at the consecutive nodes `0, ..., nodes - 1`.

The input is a polynomial of degree less than `nodes * multiplicity`; the
output records derivatives of orders below `multiplicity` at every node. -/
def consecutiveConfluentJet (nodes multiplicity : ℕ) :
    degreeLT K (nodes * multiplicity) →ₗ[K] (Fin nodes → Fin multiplicity → K) where
  toFun p i k :=
    eval (i : K) ((derivative^[k.1]) p.1)
  map_add' p q := by
    funext i k
    simp
  map_smul' c p := by
    funext i k
    simp

theorem consecutiveConfluentJet_injective (nodes multiplicity : ℕ) :
    Function.Injective (consecutiveConfluentJet K nodes multiplicity) := by
  intro p q hpq
  apply Subtype.ext
  have hinj : Function.Injective (fun i : Fin nodes ↦ (i : K)) :=
    Nat.cast_injective.comp Fin.val_injective
  by_cases hpq0 : p.1 - q.1 = 0
  · exact sub_eq_zero.mp hpq0
  apply sub_eq_zero.mp
  apply polynomial_eq_zero_of_confluent_zeros (p.1 - q.1)
      (fun i : Fin nodes ↦ (i : K)) hinj multiplicity
  · intro i k hk
    have h := congrFun (congrFun hpq i) ⟨k, hk⟩
    change eval (i : K) ((derivative^[k]) p.1) =
      eval (i : K) ((derivative^[k]) q.1) at h
    rw [iterate_derivative_sub, eval_sub, h, sub_self]
  · simpa using (natDegree_lt_iff_degree_lt hpq0).mpr
      (mem_degreeLT.mp (Submodule.sub_mem _ p.2 q.2))

/-- Confluent interpolation at consecutive nodes: the first
`nodes * multiplicity` polynomial coefficients and the corresponding repeated
node jets are linearly equivalent. -/
def consecutiveConfluentJetEquiv (nodes multiplicity : ℕ) :
    degreeLT K (nodes * multiplicity) ≃ₗ[K] (Fin nodes → Fin multiplicity → K) := by
  let f := consecutiveConfluentJet K nodes multiplicity
  apply LinearEquiv.ofBijective f
  have hinj := consecutiveConfluentJet_injective K nodes multiplicity
  refine ⟨hinj, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank ?_).mp hinj⟩
  calc
    Module.finrank K (degreeLT K (nodes * multiplicity)) = nodes * multiplicity := by
      rw [Module.finrank_eq_card_basis (degreeLT.basis K (nodes * multiplicity))]
      simp
    _ = Module.finrank K (Fin nodes → Fin multiplicity → K) := by
      simp [Module.finrank_pi_fintype]

/-- The normalized polynomial whose confluent jet is the coordinate vector at
`a`.  These polynomials are the algebraic normalization used before the
mixed-radix tensor step. -/
def normalizedConfluentPolynomial (nodes multiplicity : ℕ)
    (a : Fin nodes × Fin multiplicity) : degreeLT K (nodes * multiplicity) :=
  (consecutiveConfluentJetEquiv K nodes multiplicity).symm
    (Pi.single a.1 (Pi.single a.2 1))

@[simp] theorem normalizedConfluentPolynomial_jet (nodes multiplicity : ℕ)
    (a : Fin nodes × Fin multiplicity) (i : Fin nodes) (k : Fin multiplicity) :
    eval (i : K) ((derivative^[k.1])
      (normalizedConfluentPolynomial K nodes multiplicity a).1) =
      if i = a.1 then if k = a.2 then 1 else 0 else 0 := by
  classical
  change (consecutiveConfluentJetEquiv K nodes multiplicity)
      ((consecutiveConfluentJetEquiv K nodes multiplicity).symm
        (Pi.single a.1 (Pi.single a.2 1))) i k = _
  rw [LinearEquiv.apply_symm_apply]
  by_cases hi : i = a.1 <;> simp [hi, Pi.single_apply]

end ConfluentJet

section MixedRadix

variable {K : Type*} [Field K]

/-- The two-block mixed-radix code.  `innerIndex` is the low digit. -/
def twoBlockMixedRadixCode {outer inner : ℕ}
    (a : Fin outer × Fin inner) : Fin (outer * inner) :=
  finProdFinEquiv a

@[simp] theorem twoBlockMixedRadixCode_val {outer inner : ℕ}
    (a : Fin outer × Fin inner) :
    (twoBlockMixedRadixCode a).1 = a.2.1 + inner * a.1.1 :=
  rfl

theorem twoBlockMixedRadixCode_injective {outer inner : ℕ} :
    Function.Injective
      (twoBlockMixedRadixCode : Fin outer × Fin inner → Fin (outer * inner)) :=
  finProdFinEquiv.injective

@[simp] theorem twoBlockMixedRadixCode_symm {outer inner : ℕ}
    (a : Fin (outer * inner)) :
    twoBlockMixedRadixCode (finProdFinEquiv.symm a) = a :=
  finProdFinEquiv.apply_symm_apply a

/-- The initial-jet matrix of a family indexed by two mixed-radix digits. -/
def mixedRadixJetMatrix {outer inner : ℕ}
    (jet : (Fin outer × Fin inner) → ℕ → K) :
    Matrix (Fin (outer * inner)) (Fin (outer * inner)) K :=
  fun k a ↦ jet (finProdFinEquiv.symm a) k.1

/-- Exact determinant of a mixed-radix triangular jet family. -/
theorem mixedRadixJetMatrix_det_eq_prod {outer inner : ℕ}
    (jet : (Fin outer × Fin inner) → ℕ → K)
    (hzero : ∀ a k, k < (twoBlockMixedRadixCode a).1 → jet a k = 0) :
    (mixedRadixJetMatrix jet).det =
      ∏ a : Fin (outer * inner), jet (finProdFinEquiv.symm a) a.1 := by
  classical
  apply Matrix.det_of_lowerTriangular
  intro i j hij
  apply hzero
  simpa only [twoBlockMixedRadixCode_symm] using hij

/-- A family with zero coefficients below its mixed-radix code and a nonzero
coefficient at that code has a nonzero initial-jet determinant. -/
theorem mixedRadixJetMatrix_det_ne_zero {outer inner : ℕ}
    (jet : (Fin outer × Fin inner) → ℕ → K)
    (hzero : ∀ a k, k < (twoBlockMixedRadixCode a).1 → jet a k = 0)
    (hdiag : ∀ a, jet a (twoBlockMixedRadixCode a).1 ≠ 0) :
    (mixedRadixJetMatrix jet).det ≠ 0 := by
  classical
  rw [mixedRadixJetMatrix_det_eq_prod jet hzero]
  exact Finset.prod_ne_zero_iff.mpr fun a _ ↦ by
    simpa only [twoBlockMixedRadixCode_symm] using
      hdiag (finProdFinEquiv.symm a)

/-- Mixed-radix initial jets determine all coefficients. -/
theorem mixedRadixJetMatrix_mulVec_injective {outer inner : ℕ}
    (jet : (Fin outer × Fin inner) → ℕ → K)
    (hzero : ∀ a k, k < (twoBlockMixedRadixCode a).1 → jet a k = 0)
    (hdiag : ∀ a, jet a (twoBlockMixedRadixCode a).1 ≠ 0) :
    Function.Injective (mixedRadixJetMatrix jet).mulVec := by
  rw [Matrix.mulVec_injective_iff_isUnit]
  apply (mixedRadixJetMatrix jet).isUnit_iff_isUnit_det.mpr
  exact isUnit_iff_ne_zero.mpr
    (mixedRadixJetMatrix_det_ne_zero jet hzero hdiag)

/-- Exact two-block mixed-radix zero estimate.  A nonzero coefficient family
has a nonzero jet of order strictly below `outer * inner`. -/
theorem exists_nonzero_mixedRadix_jet {outer inner : ℕ}
    (jet : (Fin outer × Fin inner) → ℕ → K)
    (hzero : ∀ a k, k < (twoBlockMixedRadixCode a).1 → jet a k = 0)
    (hdiag : ∀ a, jet a (twoBlockMixedRadixCode a).1 ≠ 0)
    (c : Fin outer × Fin inner → K) (hc : c ≠ 0) :
    ∃ k : Fin (outer * inner), ∑ a, c a * jet a k.1 ≠ 0 := by
  let c' : Fin (outer * inner) → K := c ∘ finProdFinEquiv.symm
  have hc' : c' ≠ 0 := by
    intro hc0
    apply hc
    funext a
    have := congrFun hc0 (finProdFinEquiv a)
    simpa [c'] using this
  have hmul : (mixedRadixJetMatrix jet).mulVec c' ≠ 0 := by
    intro hzeroVec
    apply hc'
    apply mixedRadixJetMatrix_mulVec_injective jet hzero hdiag
    simpa using hzeroVec
  obtain ⟨k, hk⟩ := Function.ne_iff.mp hmul
  refine ⟨k, ?_⟩
  have hsum :
      (∑ j : Fin (outer * inner),
        mixedRadixJetMatrix jet k j * c' j) =
        ∑ a, c a * jet a k.1 := by
    rw [Fintype.sum_equiv finProdFinEquiv
      (fun a ↦ c a * jet a k.1)
      (fun j ↦ mixedRadixJetMatrix jet k j * c' j)]
    intro a
    simp [mixedRadixJetMatrix, c', mul_comm]
  rw [← hsum]
  simpa [Matrix.mulVec] using hk

end MixedRadix

end

end Schanuel
