import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas

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

/-- The endpoint kills every homogeneous jet solution exactly when it belongs
to the row span of the jet map, expressed invariantly as the range of the
dual map. -/
theorem endpointKillsJetKernel_iff_mem_range_dualMap
    (jet : V →ₗ[K] W) (endpoint : V →ₗ[K] K) :
    EndpointKillsJetKernel jet endpoint ↔
      endpoint ∈ LinearMap.range jet.dualMap := by
  rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker,
    Submodule.mem_dualAnnihilator]
  simp only [EndpointKillsJetKernel, LinearMap.mem_ker]

/-- Endpoint escape is equivalently the assertion that the endpoint functional
is not a linear combination of the jet constraints.  This is the exact
row-span obstruction that an affine/congruence construction must overcome. -/
theorem endpointEscape_iff_not_mem_range_dualMap
    (jet : V →ₗ[K] W) (endpoint : V →ₗ[K] K) :
    EndpointEscape jet endpoint ↔
      endpoint ∉ LinearMap.range jet.dualMap := by
  rw [endpointEscape_iff_not_endpointKillsJetKernel,
    endpointKillsJetKernel_iff_mem_range_dualMap]

end EndpointEscape

section BoxEndpoint

variable {K α β : Type*} [Field K] [Fintype β]

/-- Endpoint evaluation on a rectangular coefficient box.

Think of `c a b` as the coefficient of an input monomial indexed by `a`
and an exponential monomial indexed by `b`.  At the global endpoint
`(x,y)=(0,1)`, only the distinguished zero-input row `a₀` survives, while
every exponential monomial evaluates to one.  Thus the endpoint is the sum of
that row. -/
def boxEndpoint (a₀ : α) : (α → β → K) →ₗ[K] K where
  toFun c := ∑ b, c a₀ b
  map_add' c d := by
    simp [Finset.sum_add_distrib]
  map_smul' r c := by
    simp [Finset.mul_sum]

@[simp] theorem boxEndpoint_apply (a₀ : α) (c : α → β → K) :
    boxEndpoint a₀ c = ∑ b, c a₀ b :=
  rfl

/-- As soon as the exponential block has one coefficient, the endpoint
functional is surjective: a single coefficient in the distinguished row can
realize any prescribed endpoint value. -/
theorem boxEndpoint_surjective [Nonempty β] (a₀ : α) :
    Function.Surjective (boxEndpoint (K := K) (β := β) a₀) := by
  classical
  let b₀ : β := Classical.choice (inferInstance : Nonempty β)
  intro y
  refine ⟨Pi.single a₀ (Pi.single b₀ y), ?_⟩
  simp [boxEndpoint, b₀]

/-- In particular the box endpoint is a nonzero linear functional whenever
the exponential block is nonempty. -/
theorem boxEndpoint_ne_zero [Nonempty β] (a₀ : α) :
    boxEndpoint (K := K) (β := β) a₀ ≠ 0 := by
  intro hzero
  obtain ⟨c, hc⟩ := boxEndpoint_surjective (K := K) (β := β) a₀ 1
  rw [hzero, LinearMap.zero_apply] at hc
  exact one_ne_zero hc.symm

end BoxEndpoint


section BoxJets

variable {K α β ι : Type*} [Field K] [Fintype α] [Fintype β]

/-- The finite jet map attached to a rectangular coefficient box.  The value
`jetCoeff a b k` is the `k`-th jet of the basis monomial indexed by
`(a,b)`; the jet of a general coefficient family is obtained by linear
superposition. -/
def boxJetMap (jetCoeff : α → β → ι → K) :
    (α → β → K) →ₗ[K] (ι → K) where
  toFun c k := ∑ a, ∑ b, c a b * jetCoeff a b k
  map_add' c d := by
    funext k
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' r c := by
    funext k
    simp [Finset.mul_sum, mul_assoc]

@[simp] theorem boxJetMap_apply (jetCoeff : α → β → ι → K)
    (c : α → β → K) (k : ι) :
    boxJetMap jetCoeff c k = ∑ a, ∑ b, c a b * jetCoeff a b k :=
  rfl

/-- The standard coefficient vector supported on one box monomial. -/
noncomputable def boxBasis (a : α) (b : β) : α → β → K := by
  classical
  exact Pi.single a (Pi.single b 1)

@[simp] theorem boxJetMap_boxBasis (jetCoeff : α → β → ι → K)
    (a : α) (b : β) (k : ι) :
    boxJetMap jetCoeff (boxBasis (K := K) a b) k = jetCoeff a b k := by
  classical
  simp [boxJetMap, boxBasis]

@[simp] theorem boxEndpoint_boxBasis_same (a : α) (b : β) :
    boxEndpoint (K := K) (β := β) a (boxBasis (K := K) a b) = 1 := by
  classical
  simp [boxEndpoint, boxBasis]

theorem boxEndpoint_boxBasis_of_ne {a₀ a : α} (b : β) (h : a₀ ≠ a) :
    boxEndpoint (K := K) (β := β) a₀ (boxBasis (K := K) a b) = 0 := by
  classical
  simp [boxEndpoint, boxBasis, h]

/-- Every finite rectangular coefficient family is the sum of its standard
basis monomials. -/
theorem boxCoefficients_eq_sum_basis (c : α → β → K) :
    c = ∑ a, ∑ b, c a b • boxBasis (K := K) a b := by
  classical
  funext a b
  simp [boxBasis]

/-- The concrete box endpoint-escape problem is exactly the abstract row-span
obstruction for the finite jet map. -/
theorem boxEndpointEscape_iff_not_mem_range_dualMap
    (jetCoeff : α → β → ι → K) (a₀ : α) :
    EndpointEscape (boxJetMap jetCoeff) (boxEndpoint (K := K) (β := β) a₀) ↔
      boxEndpoint (K := K) (β := β) a₀ ∉
        LinearMap.range (boxJetMap jetCoeff).dualMap :=
  endpointEscape_iff_not_mem_range_dualMap _ _

end BoxJets

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
