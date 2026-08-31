import Schanuel.AffineEndpointInterpolation
import Mathlib.LinearAlgebra.StdBasis

/-!
# Finite rectangular jet systems

This module realizes the abstract endpoint-escape obstruction on a finite
rectangular coefficient box.  The coefficient space has a canonical basis
indexed by pairs `(a,b)`.  A jet system is therefore determined by the jet
vector assigned to each basis monomial.

The construction is intentionally finite-dimensional and algebraic.  It does
not yet assert the arithmetic nonexistence of a dual certificate.
-/

namespace Schanuel

open Module

noncomputable section

section BoxJets

variable {K α β ι : Type*} [Field K] [Fintype α] [Fintype β]

/-- Canonical basis of the rectangular coefficient space. -/
def boxBasisBasis :
    Basis (Σ _ : α, β) K (α → β → K) :=
  Pi.basis (fun _ : α => Pi.basisFun K β)

/-- Standard coefficient vector supported on the monomial indexed by `(a,b)`. -/
def boxBasis (a : α) (b : β) : α → β → K := by
  classical
  exact Pi.single a (Pi.single b 1)

/-- The explicit standard vector is the corresponding vector of the canonical
rectangular basis. -/
theorem boxBasis_eq_basis (a : α) (b : β) :
    boxBasis (K := K) a b =
      boxBasisBasis (K := K) (α := α) (β := β) ⟨a, b⟩ := by
  classical
  simp [boxBasis, boxBasisBasis]

/-- Linear jet map determined by the jet vector of every basis monomial. -/
def boxJetMap (jetCoeff : α → β → ι → K) :
    (α → β → K) →ₗ[K] (ι → K) :=
  (boxBasisBasis (K := K) (α := α) (β := β)).constr K
    (fun ab => jetCoeff ab.1 ab.2)

@[simp] theorem boxJetMap_boxBasis (jetCoeff : α → β → ι → K)
    (a : α) (b : β) :
    boxJetMap jetCoeff (boxBasis (K := K) a b) = jetCoeff a b := by
  change
    (boxBasisBasis (K := K) (α := α) (β := β)).constr K
      (fun ab => jetCoeff ab.1 ab.2) (boxBasis (K := K) a b) =
        jetCoeff a b
  rw [boxBasis_eq_basis]
  exact (boxBasisBasis (K := K) (α := α) (β := β)).constr_basis K
    (fun ab => jetCoeff ab.1 ab.2) ⟨a, b⟩

@[simp] theorem boxEndpoint_boxBasis_same (a : α) (b : β) :
    boxEndpoint (K := K) (β := β) a (boxBasis (K := K) a b) = 1 := by
  classical
  simp [boxEndpoint, boxBasis]

theorem boxEndpoint_boxBasis_of_ne {a₀ a : α} (b : β) (h : a₀ ≠ a) :
    boxEndpoint (K := K) (β := β) a₀ (boxBasis (K := K) a b) = 0 := by
  classical
  have h' : a ≠ a₀ := Ne.symm h
  simp [boxEndpoint, boxBasis, h']

/-- Linear maps out of the coefficient box are determined by their values on
box monomials. -/
theorem linearMap_eq_of_boxBasis_eq
    {W : Type*} [AddCommGroup W] [Module K W]
    (f g : (α → β → K) →ₗ[K] W)
    (h : ∀ a b, f (boxBasis (K := K) a b) =
      g (boxBasis (K := K) a b)) :
    f = g := by
  apply (boxBasisBasis (K := K) (α := α) (β := β)).ext
  rintro ⟨a, b⟩
  simpa only [boxBasis_eq_basis] using h a b

/-- The concrete finite-box endpoint problem is the abstract row-span
obstruction specialized to the box jet map. -/
theorem boxEndpointEscape_iff_not_mem_range_dualMap
    (jetCoeff : α → β → ι → K) (a₀ : α) :
    EndpointEscape (boxJetMap jetCoeff)
        (boxEndpoint (K := K) (β := β) a₀) ↔
      boxEndpoint (K := K) (β := β) a₀ ∉
        LinearMap.range (boxJetMap jetCoeff).dualMap :=
  endpointEscape_iff_not_mem_range_dualMap _ _

end BoxJets

end

end Schanuel
