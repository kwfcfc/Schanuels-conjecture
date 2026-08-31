import Schanuel
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Differential transversality of exponential graph tuples

This file isolates an unconditional linear-algebra fact about Kähler differentials.  Given
families `z y : ι → K`, the logarithmic defect form at `i` is

`y i⁻¹ • d(y i) - d(z i)`.

When every `y i` is nonzero, a derivation annihilates all these forms exactly when it satisfies
the exponential compatibility equations `D (y i) = y i * D (z i)`.  The universal property of
Kähler differentials and separation of a proper subspace by the algebraic dual then show that
the defect forms span the whole cotangent space exactly when the only compatible derivation
`K → K` is zero.

No differential or functional form of Schanuel's conjecture is used here.
-/

namespace Schanuel

open Set

noncomputable section

variable {ι K : Type*} [Field K] [Algebra ℚ K]

/-- The logarithmic defect `dlog(y_i) - d(z_i)` in `Ω[K⁄ℚ]`. -/
def logarithmicDefect (z y : ι → K) (i : ι) : Ω[K⁄ℚ] :=
  (y i)⁻¹ • KaehlerDifferential.D ℚ K (y i) - KaehlerDifferential.D ℚ K (z i)

/-- A rational derivation is compatible with the displayed exponential graph equations when
it obeys `D(y_i) = y_i D(z_i)` at every index. -/
def IsExpCompatible (z y : ι → K) (D : Derivation ℚ K K) : Prop :=
  ∀ i, D (y i) = y i * D (z i)

@[simp]
theorem liftKaehlerDifferential_logarithmicDefect
    (z y : ι → K) (D : Derivation ℚ K K) (i : ι) :
    D.liftKaehlerDifferential (logarithmicDefect z y i) =
      (y i)⁻¹ * D (y i) - D (z i) := by
  simp [logarithmicDefect]

/-- For nonzero `y_i`, exponential compatibility is exactly annihilation of every logarithmic
defect form under the linear map associated to the derivation. -/
theorem isExpCompatible_iff_lift_logarithmicDefect_eq_zero
    (z y : ι → K) (hy : ∀ i, y i ≠ 0) (D : Derivation ℚ K K) :
    IsExpCompatible z y D ↔
      ∀ i, D.liftKaehlerDifferential (logarithmicDefect z y i) = 0 := by
  constructor
  · intro hD i
    rw [liftKaehlerDifferential_logarithmicDefect, hD i]
    simp [hy i]
  · intro hD i
    have hi := hD i
    rw [liftKaehlerDifferential_logarithmicDefect] at hi
    have hinv : (y i)⁻¹ * D (y i) = D (z i) := sub_eq_zero.mp hi
    calc
      D (y i) = y i * ((y i)⁻¹ * D (y i)) := by simp [hy i]
      _ = y i * D (z i) := by rw [hinv]

/-- If the logarithmic defect forms span the cotangent space, every compatible derivation is
zero. -/
theorem compatibleDerivation_eq_zero_of_span_logarithmicDefect_eq_top
    (z y : ι → K) (hy : ∀ i, y i ≠ 0)
    (hspan : Submodule.span K (Set.range (logarithmicDefect z y)) = ⊤)
    (D : Derivation ℚ K K) (hD : IsExpCompatible z y D) :
    D = 0 := by
  have hann : ∀ i, D.liftKaehlerDifferential (logarithmicDefect z y i) = 0 :=
    (isExpCompatible_iff_lift_logarithmicDefect_eq_zero z y hy D).mp hD
  have hle : Submodule.span K (Set.range (logarithmicDefect z y)) ≤
      LinearMap.ker D.liftKaehlerDifferential := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact LinearMap.mem_ker.mpr (hann i)
  rw [hspan] at hle
  have hker : LinearMap.ker D.liftKaehlerDifferential = ⊤ := top_unique hle
  have hlift : D.liftKaehlerDifferential = 0 := LinearMap.ker_eq_top.mp hker
  ext x
  rw [← Derivation.liftKaehlerDifferential_comp_D D x, hlift]
  rfl

/-- If every compatible rational derivation `K → K` is zero, the logarithmic defect forms span
the whole cotangent space. -/
theorem span_logarithmicDefect_eq_top_of_compatibleDerivation_eq_zero
    (z y : ι → K) (hy : ∀ i, y i ≠ 0)
    (hzero : ∀ D : Derivation ℚ K K, IsExpCompatible z y D → D = 0) :
    Submodule.span K (Set.range (logarithmicDefect z y)) = ⊤ := by
  by_contra hne
  have hlt : Submodule.span K (Set.range (logarithmicDefect z y)) < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  obtain ⟨f, hf, hmap⟩ :=
    Submodule.exists_dual_map_eq_bot_of_lt_top hlt inferInstance
  let D : Derivation ℚ K K :=
    KaehlerDifferential.linearMapEquivDerivation ℚ K f
  have hliftD : D.liftKaehlerDifferential = f := by
    change (KaehlerDifferential.linearMapEquivDerivation ℚ K).symm
        (KaehlerDifferential.linearMapEquivDerivation ℚ K f) = f
    exact (KaehlerDifferential.linearMapEquivDerivation ℚ K).symm_apply_apply f
  have hann : ∀ i, f (logarithmicDefect z y i) = 0 := by
    intro i
    have hi : f (logarithmicDefect z y i) ∈
        (Submodule.span K (Set.range (logarithmicDefect z y))).map f := by
      exact ⟨logarithmicDefect z y i, Submodule.subset_span ⟨i, rfl⟩, rfl⟩
    rw [hmap] at hi
    exact hi
  have hDann : ∀ i, D.liftKaehlerDifferential (logarithmicDefect z y i) = 0 := by
    intro i
    rw [hliftD]
    exact hann i
  have hcompat : IsExpCompatible z y D :=
    (isExpCompatible_iff_lift_logarithmicDefect_eq_zero z y hy D).mpr hDann
  have hDz : D = 0 := hzero D hcompat
  apply hf
  apply (KaehlerDifferential.linearMapEquivDerivation ℚ K).injective
  simpa [D] using hDz

/-- The defect forms span the cotangent space if and only if the zero derivation is the only
rational derivation compatible with all displayed exponential graph equations. -/
theorem span_logarithmicDefect_eq_top_iff
    (z y : ι → K) (hy : ∀ i, y i ≠ 0) :
    Submodule.span K (Set.range (logarithmicDefect z y)) = ⊤ ↔
      ∀ D : Derivation ℚ K K, IsExpCompatible z y D → D = 0 := by
  constructor
  · intro hspan D hD
    exact compatibleDerivation_eq_zero_of_span_logarithmicDefect_eq_top z y hy hspan D hD
  · exact span_logarithmicDefect_eq_top_of_compatibleDerivation_eq_zero z y hy

/-! ## The actual finite exponential graph field -/

/-- The logarithmic defect forms for the displayed generators of `generatedField z`. -/
def generatedFieldLogarithmicDefect {n : ℕ} (z : Fin n → ℂ) (i : Fin n) :
    Ω[generatedField z⁄ℚ] :=
  logarithmicDefect (coordinate z) (exponential z) i

/-- In the actual coordinate-exponential field, the graph defect forms span the cotangent space
exactly when no nonzero rational derivation differentiates the displayed exponentials according
to the exponential rule. -/
theorem generatedField_span_logarithmicDefect_eq_top_iff
    {n : ℕ} (z : Fin n → ℂ) :
    Submodule.span (generatedField z)
        (Set.range (generatedFieldLogarithmicDefect z)) = ⊤ ↔
      ∀ D : Derivation ℚ (generatedField z) (generatedField z),
        IsExpCompatible (coordinate z) (exponential z) D → D = 0 := by
  apply span_logarithmicDefect_eq_top_iff
  intro i hzero
  have hzero' := congrArg ((↑) : generatedField z → ℂ) hzero
  exact Complex.exp_ne_zero (z i) hzero'

end

end Schanuel
