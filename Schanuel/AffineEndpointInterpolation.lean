import Mathlib.LinearAlgebra.Basic

/-!
# Affine endpoint interpolation

The mixed-radix jet calculation shows that homogeneous jet constraints alone are
not enough: one also needs the auxiliary polynomial to escape the endpoint
kernel, i.e. to have a nonzero value at the second endpoint.

This file isolates that distinction in finite-dimensional linear algebra.

For a linear jet map `jet : V →ₗ[K] W` and endpoint functional
`endpoint : V →ₗ[K] K`, `EndpointEscape jet endpoint` means that some vector
annihilated by all jet constraints still has nonzero endpoint value.  Over a
field, any such witness can be rescaled to endpoint value exactly `1`.

The final example shows that a nontrivial homogeneous jet kernel does *not*
imply endpoint escape: take the same first-coordinate projection for both the
jet map and the endpoint functional on `K × K`.  Its kernel is nontrivial,
but the endpoint vanishes identically on that kernel.  This is the abstract
linear-algebra obstruction behind the failure of ordinary homogeneous Siegel
dimension counting to force `P(0,1) ≠ 0`.
-/

namespace Schanuel

section EndpointEscape

variable {K V W : Type*} [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- A homogeneous jet solution escapes the endpoint kernel when its endpoint
value is nonzero. -/
def EndpointEscape (jet : V →ₗ[K] W) (endpoint : V →ₗ[K] K) : Prop :=
  ∃ v, jet v = 0 ∧ endpoint v ≠ 0

/-- The endpoint functional kills the entire homogeneous jet kernel. -/
def EndpointKillsJetKernel (jet : V →ₗ[K] W) (endpoint : V →ₗ[K] K) : Prop :=
  ∀ v, jet v = 0 → endpoint v = 0

/-- Endpoint escape is exactly the failure of the endpoint functional to vanish
on every homogeneous jet solution. -/
theorem endpointEscape_iff_not_endpointKillsJetKernel
    (jet : V →ₗ[K] W) (endpoint : V →ₗ[K] K) :
    EndpointEscape jet endpoint ↔ ¬ EndpointKillsJetKernel jet endpoint := by
  constructor
  · rintro ⟨v, hvjet, hvend⟩ hkills
    exact hvend (hkills v hvjet)
  · intro hnot
    by_contra hescape
    apply hnot
    intro v hvjet
    by_contra hvend
    exact hescape ⟨v, hvjet, hvend⟩

/-- Over a field, any endpoint-escape witness can be normalized so that the
endpoint value is exactly one. -/
theorem endpointEscape_iff_exists_normalized
    (jet : V →ₗ[K] W) (endpoint : V →ₗ[K] K) :
    EndpointEscape jet endpoint ↔
      ∃ v, jet v = 0 ∧ endpoint v = 1 := by
  constructor
  · rintro ⟨v, hvjet, hvend⟩
    refine ⟨(endpoint v)⁻¹ • v, ?_, ?_⟩
    · simp [hvjet]
    · simp [hvend]
  · rintro ⟨v, hvjet, hvend⟩
    refine ⟨v, hvjet, ?_⟩
    rw [hvend]
    exact one_ne_zero

end EndpointEscape

section HomogeneousCounterexample

variable (K : Type*) [Field K]

/-- First-coordinate projection, used as both a jet map and an endpoint
functional in the counterexample below. -/
def firstProjection : (K × K) →ₗ[K] K where
  toFun v := v.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The first-coordinate jet map has a nontrivial homogeneous kernel. -/
theorem firstProjection_has_nontrivial_kernel :
    ∃ v : K × K, v ≠ 0 ∧ firstProjection K v = 0 := by
  refine ⟨(0, 1), ?_, rfl⟩
  simp

/-- Nevertheless, using the same functional as the endpoint gives no endpoint
escape at all: every homogeneous jet solution has endpoint zero. -/
theorem firstProjection_no_endpointEscape :
    ¬ EndpointEscape (firstProjection K) (firstProjection K) := by
  rintro ⟨v, hvjet, hvend⟩
  exact hvend hvjet

/-- A nontrivial homogeneous jet kernel by itself does not imply endpoint
escape.  Thus dimension counting that only produces a nonzero kernel vector
cannot solve the affine endpoint condition. -/
theorem nontrivial_jet_kernel_does_not_force_endpointEscape :
    (∃ v : K × K, v ≠ 0 ∧ firstProjection K v = 0) ∧
      ¬ EndpointEscape (firstProjection K) (firstProjection K) :=
  ⟨firstProjection_has_nontrivial_kernel K,
    firstProjection_no_endpointEscape K⟩

end HomogeneousCounterexample

end Schanuel
