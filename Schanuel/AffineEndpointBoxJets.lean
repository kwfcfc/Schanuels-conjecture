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

/-- A dual certificate for failure of endpoint escape.  One linear functional
on the jet-value space takes value one on every basis jet in the distinguished
endpoint row and vanishes on every basis jet outside that row. -/
def BoxJetDualCertificate (jetCoeff : α → β → ι → K) (a₀ : α) : Prop :=
  ∃ φ : Module.Dual K (ι → K),
    (∀ b, φ (jetCoeff a₀ b) = 1) ∧
      ∀ a, a₀ ≠ a → ∀ b, φ (jetCoeff a b) = 0

/-- The endpoint functional kills every homogeneous jet solution exactly when
a dual certificate exists. -/
theorem boxEndpointKillsJetKernel_iff_dualCertificate
    (jetCoeff : α → β → ι → K) (a₀ : α) :
    EndpointKillsJetKernel (boxJetMap jetCoeff)
        (boxEndpoint (K := K) (β := β) a₀) ↔
      BoxJetDualCertificate jetCoeff a₀ := by
  rw [endpointKillsJetKernel_iff_mem_range_dualMap]
  constructor
  · intro h
    rw [LinearMap.mem_range] at h
    obtain ⟨φ, hφ⟩ := h
    refine ⟨φ, ?_, ?_⟩
    · intro b
      calc
        φ (jetCoeff a₀ b) =
            (boxJetMap jetCoeff).dualMap φ
              (boxBasis (K := K) a₀ b) := by simp
        _ = boxEndpoint (K := K) (β := β) a₀
              (boxBasis (K := K) a₀ b) := by rw [hφ]
        _ = 1 := boxEndpoint_boxBasis_same (K := K) a₀ b
    · intro a ha b
      calc
        φ (jetCoeff a b) =
            (boxJetMap jetCoeff).dualMap φ
              (boxBasis (K := K) a b) := by simp
        _ = boxEndpoint (K := K) (β := β) a₀
              (boxBasis (K := K) a b) := by rw [hφ]
        _ = 0 := boxEndpoint_boxBasis_of_ne
          (K := K) (β := β) (a₀ := a₀) (a := a) b ha
  · rintro ⟨φ, hrow, hoff⟩
    rw [LinearMap.mem_range]
    refine ⟨φ, ?_⟩
    apply linearMap_eq_of_boxBasis_eq
    intro a b
    by_cases ha : a₀ = a
    · subst a
      calc
        (boxJetMap jetCoeff).dualMap φ
              (boxBasis (K := K) a₀ b) =
            φ (jetCoeff a₀ b) := by simp
        _ = 1 := hrow b
        _ = boxEndpoint (K := K) (β := β) a₀
              (boxBasis (K := K) a₀ b) :=
          (boxEndpoint_boxBasis_same (K := K) a₀ b).symm
    · calc
        (boxJetMap jetCoeff).dualMap φ
              (boxBasis (K := K) a b) =
            φ (jetCoeff a b) := by simp
        _ = 0 := hoff a ha b
        _ = boxEndpoint (K := K) (β := β) a₀
              (boxBasis (K := K) a b) :=
          (boxEndpoint_boxBasis_of_ne
            (K := K) (β := β) (a₀ := a₀) (a := a) b ha).symm

/-- Endpoint escape is equivalently the nonexistence of a dual certificate. -/
theorem boxEndpointEscape_iff_no_dualCertificate
    (jetCoeff : α → β → ι → K) (a₀ : α) :
    EndpointEscape (boxJetMap jetCoeff)
        (boxEndpoint (K := K) (β := β) a₀) ↔
      ¬ BoxJetDualCertificate jetCoeff a₀ := by
  rw [endpointEscape_iff_not_endpointKillsJetKernel,
    boxEndpointKillsJetKernel_iff_dualCertificate]

end BoxJets

end

end Schanuel
