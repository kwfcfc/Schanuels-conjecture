import Schanuel.ConjugationStableTerminal

/-!
# Real and imaginary sectors of a conjugation-stable failure

On a finite rational subspace preserved by complex conjugation, the half-sum and half-difference
operators split the space into the `+1` and `-1` eigensubspaces.  For a subspace containing the
canonical anchor, those sectors contain `1` and the standard period respectively.  This module
keeps the graph fields of the two sectors separate and records their exact compositum; comparison
with an original graph field uses an explicit common integral denominator.
-/

namespace Schanuel

open Function Set

noncomputable section

namespace ConjugationStableSectorBoundary

open ConjugationStableNormalForm ConjugationStableMinimalFailure
  ConjugationStableTerminal

/-- The fixed subspace of conjugation restricted to a stable rational subspace. -/
def plusSector (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) : Submodule ℚ R :=
  LinearMap.ker (restrictedConjugation R hR - LinearMap.id)

/-- The anti-fixed subspace of conjugation restricted to a stable rational subspace. -/
def minusSector (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) : Submodule ℚ R :=
  LinearMap.ker (restrictedConjugation R hR + LinearMap.id)

@[simp]
theorem mem_plusSector_iff (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    x ∈ plusSector R hR ↔ restrictedConjugation R hR x = x := by
  rw [plusSector, LinearMap.mem_ker]
  exact sub_eq_zero

@[simp]
theorem mem_minusSector_iff (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    x ∈ minusSector R hR ↔ restrictedConjugation R hR x = -x := by
  simp [minusSector, LinearMap.mem_ker, eq_neg_iff_add_eq_zero]

/-- Rational projection onto the fixed sector. -/
def plusProjection (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) : R :=
  (1 / 2 : ℚ) • (x + restrictedConjugation R hR x)

/-- Rational projection onto the anti-fixed sector. -/
def minusProjection (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) : R :=
  (1 / 2 : ℚ) • (x - restrictedConjugation R hR x)

theorem restrictedConjugation_apply_apply (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    restrictedConjugation R hR (restrictedConjugation R hR x) = x := by
  have hx := LinearMap.congr_fun (restrictedConjugation_involutive R hR) x
  simpa [LinearMap.comp_apply] using hx

theorem plusProjection_mem (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    plusProjection R hR x ∈ plusSector R hR := by
  rw [mem_plusSector_iff]
  simp [plusProjection, restrictedConjugation_apply_apply, add_comm]

theorem minusProjection_mem (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    minusProjection R hR x ∈ minusSector R hR := by
  rw [mem_minusSector_iff]
  simp [minusProjection, restrictedConjugation_apply_apply]
  module

theorem plusProjection_add_minusProjection (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    plusProjection R hR x + minusProjection R hR x = x := by
  simp [plusProjection, minusProjection]
  module

/-- The two rational conjugation sectors have zero intersection. -/
theorem sectors_disjoint (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) :
    Disjoint (plusSector R hR) (minusSector R hR) := by
  rw [Submodule.disjoint_def]
  intro x hxplus hxminus
  have hp := (mem_plusSector_iff R hR x).mp hxplus
  have hm := (mem_minusSector_iff R hR x).mp hxminus
  have hneg : x = -x := hp.symm.trans hm
  have htwo : (2 : ℚ) • x = 0 := by
    calc
      (2 : ℚ) • x = x + x := two_smul ℚ x
      _ = -x + x := congrArg (fun y ↦ y + x) hneg
      _ = 0 := neg_add_cancel x
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Every vector is the sum of its fixed and anti-fixed rational projections. -/
theorem sectors_sup_eq_top (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) :
    plusSector R hR ⊔ minusSector R hR = ⊤ := by
  apply top_unique
  intro x _
  rw [← plusProjection_add_minusProjection R hR x]
  exact (plusSector R hR ⊔ minusSector R hR).add_mem
    (Submodule.mem_sup_left (plusProjection_mem R hR x))
    (Submodule.mem_sup_right (minusProjection_mem R hR x))

/-- Restricted conjugation gives an internal direct sum of its two rational eigenspaces. -/
theorem sectors_isCompl (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) :
    IsCompl (plusSector R hR) (minusSector R hR) :=
  ⟨sectors_disjoint R hR, codisjoint_iff.mpr (by
    rw [sectors_sup_eq_top R hR])⟩

/-! ## The two canonical directions -/

/-- A rational subspace containing the canonical anchor contains the real direction `1`. -/
theorem one_mem_of_anchor_le (R : Submodule ℚ ℂ)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) : (1 : ℂ) ∈ R := by
  have ha : canonicalAnchor 0 ∈ R :=
    haR (Submodule.subset_span (Set.mem_range_self 0))
  have hb : canonicalAnchor 1 ∈ R :=
    haR (Submodule.subset_span (Set.mem_range_self 1))
  have h := R.sub_mem (R.smul_mem (2 : ℚ) ha) hb
  convert h using 1
  simp [Rat.smul_def]
  ring

/-- A rational subspace containing the canonical anchor contains the imaginary period. -/
theorem standardPeriod_mem_of_anchor_le (R : Submodule ℚ ℂ)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) : standardPeriod ∈ R := by
  have ha : canonicalAnchor 0 ∈ R :=
    haR (Submodule.subset_span (Set.mem_range_self 0))
  have hb : canonicalAnchor 1 ∈ R :=
    haR (Submodule.subset_span (Set.mem_range_self 1))
  have h := R.sub_mem hb ha
  convert h using 1
  simp
  ring

/-- The real unit, viewed in a stable subspace containing the canonical anchor. -/
def oneInStableSubspace (R : Submodule ℚ ℂ)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) : R :=
  ⟨1, one_mem_of_anchor_le R haR⟩

/-- The standard imaginary period, viewed in a stable subspace containing the anchor. -/
def periodInStableSubspace (R : Submodule ℚ ℂ)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) : R :=
  ⟨standardPeriod, standardPeriod_mem_of_anchor_le R haR⟩

@[simp]
theorem oneInStableSubspace_coe (R : Submodule ℚ ℂ)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) :
    (oneInStableSubspace R haR : ℂ) = 1 := rfl

@[simp]
theorem periodInStableSubspace_coe (R : Submodule ℚ ℂ)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) :
    (periodInStableSubspace R haR : ℂ) = standardPeriod := rfl

theorem star_standardPeriod : star standardPeriod = -standardPeriod := by
  change star (2 * Real.pi * Complex.I) = -(2 * Real.pi * Complex.I)
  simp

/-- The anchor's real direction lies in the fixed sector. -/
theorem one_mem_plusSector (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) :
    oneInStableSubspace R haR ∈ plusSector R hR := by
  rw [mem_plusSector_iff]
  apply Subtype.ext
  simp

/-- The anchor's period direction lies in the anti-fixed sector. -/
theorem period_mem_minusSector (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) :
    periodInStableSubspace R haR ∈ minusSector R hR := by
  rw [mem_minusSector_iff]
  apply Subtype.ext
  simpa using star_standardPeriod

/-! ## Finite sector bases with their anchor directions first -/

/-- A finite-dimensional subspace containing a nonzero vector has a finite basis whose first
vector is the prescribed one. -/
theorem exists_fin_basis_with_first
    {V : Type*} [AddCommGroup V] [Module ℚ V]
    (P : Submodule ℚ V) [FiniteDimensional ℚ P]
    (x : V) (hxP : x ∈ P) (hx0 : x ≠ 0) :
    ∃ (n : ℕ) (b : Fin (n + 1) → V),
      LinearIndependent ℚ b ∧ Submodule.span ℚ (Set.range b) = P ∧ b 0 = x := by
  let xP : Fin 1 → P := fun _ ↦ ⟨x, hxP⟩
  have hxPind : LinearIndependent ℚ xP := by
    rw [linearIndependent_unique_iff]
    intro hzero
    apply hx0
    exact congrArg ((↑) : P → V) hzero
  let bSum := Module.Basis.sumExtend hxPind
  letI : Fintype (Fin 1 ⊕ Module.Basis.sumExtendIndex hxPind) :=
    FiniteDimensional.fintypeBasisIndex bSum
  letI : Finite (Module.Basis.sumExtendIndex hxPind) :=
    Finite.of_injective
      (fun y : Module.Basis.sumExtendIndex hxPind ↦
        (Sum.inr y : Fin 1 ⊕ Module.Basis.sumExtendIndex hxPind)) Sum.inr_injective
  letI : Fintype (Module.Basis.sumExtendIndex hxPind) := Fintype.ofFinite _
  let n := Fintype.card (Module.Basis.sumExtendIndex hxPind)
  let eComplement : Module.Basis.sumExtendIndex hxPind ≃ Fin n := Fintype.equivFin _
  let eAll : (Fin 1 ⊕ Module.Basis.sumExtendIndex hxPind) ≃ Fin (n + 1) :=
    (Equiv.sumCongr (Equiv.refl (Fin 1)) eComplement).trans
      (finSumFinEquiv.trans (finCongr (Nat.add_comm 1 n)))
  let bFinal : Module.Basis (Fin (n + 1)) ℚ P := bSum.reindex eAll
  let b : Fin (n + 1) → V := P.subtype ∘ bFinal
  have hezero : eAll (Sum.inl 0) = 0 := by
    apply Fin.ext
    rfl
  have hindexzero : eAll.symm 0 = Sum.inl 0 := by
    rw [← hezero]
    exact eAll.symm_apply_apply _
  have hbzero : bFinal 0 = xP 0 := by
    change (bSum.reindex eAll) 0 = xP 0
    rw [Module.Basis.reindex_apply, hindexzero]
    exact basis_sumExtend_apply_inl hxPind 0
  refine ⟨n, b, ?_, ?_, ?_⟩
  · exact bFinal.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  · change Submodule.span ℚ (Set.range (P.subtype ∘ bFinal)) = P
    rw [Set.range_comp, Submodule.span_image, bFinal.span_eq,
      Submodule.map_subtype_top]
  · simpa [b, xP] using congrArg ((↑) : P → V) hbzero

/-- The fixed sector has a finite basis beginning with the real anchor direction `1`. -/
theorem exists_plusSector_basis_with_one (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R)
    [FiniteDimensional ℚ R] :
    ∃ (p : ℕ) (u : Fin (p + 1) → R),
      LinearIndependent ℚ u ∧
      Submodule.span ℚ (Set.range u) = plusSector R hR ∧
      u 0 = oneInStableSubspace R haR := by
  let P := plusSector R hR
  letI : FiniteDimensional ℚ P :=
    FiniteDimensional.of_injective P.subtype P.subtype_injective
  exact exists_fin_basis_with_first P (oneInStableSubspace R haR)
    (one_mem_plusSector R hR haR) (by
      intro h
      have := congrArg ((↑) : R → ℂ) h
      norm_num at this)

/-- The anti-fixed sector has a finite basis beginning with the standard period. -/
theorem exists_minusSector_basis_with_period (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R)
    [FiniteDimensional ℚ R] :
    ∃ (q : ℕ) (v : Fin (q + 1) → R),
      LinearIndependent ℚ v ∧
      Submodule.span ℚ (Set.range v) = minusSector R hR ∧
      v 0 = periodInStableSubspace R haR := by
  let P := minusSector R hR
  letI : FiniteDimensional ℚ P :=
    FiniteDimensional.of_injective P.subtype P.subtype_injective
  exact exists_fin_basis_with_first P (periodInStableSubspace R haR)
    (period_mem_minusSector R hR haR) (by
      intro h
      have := congrArg ((↑) : R → ℂ) h
      exact FullyTranscendentalPeriodBoundary.period_ne_zero (by simpa using this))

/-! ## Joining sector bases and joining their graph fields -/

/-- The range of an appended finite family is the union of the two ranges. -/
theorem range_append {m n : ℕ} {X : Type*} (u : Fin m → X) (v : Fin n → X) :
    Set.range (Fin.append u v) = Set.range u ∪ Set.range v := by
  ext x
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (motive := fun i ↦
      Fin.append u v i ∈ Set.range u ∪ Set.range v)
      (fun j ↦ Or.inl ⟨j, ?_⟩) (fun j ↦ Or.inr ⟨j, ?_⟩) i
    · exact (Fin.append_left u v j).symm
    · exact (Fin.append_right u v j).symm
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, Fin.append_left u v i⟩
    · exact ⟨Fin.natAdd m i, Fin.append_right u v i⟩

/-- Appending independent families with disjoint spans preserves independence. -/
theorem linearIndependent_append_of_disjoint_spans
    {m n : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V]
    {u : Fin m → V} {v : Fin n → V}
    (hu : LinearIndependent ℚ u) (hv : LinearIndependent ℚ v)
    (hdisj : Disjoint (Submodule.span ℚ (Set.range u))
      (Submodule.span ℚ (Set.range v))) :
    LinearIndependent ℚ (Fin.append u v) := by
  have hsum : LinearIndependent ℚ (Sum.elim u v) :=
    hu.sum_type hv hdisj
  have heq : Fin.append u v ∘ finSumFinEquiv = Sum.elim u v := by
    ext (i | j) <;> simp
  exact (linearIndependent_equiv' finSumFinEquiv heq).mp hsum

/-- Appending families spans the supremum of their two spans. -/
theorem span_append {m n : ℕ} {V : Type*} [AddCommGroup V] [Module ℚ V]
    (u : Fin m → V) (v : Fin n → V) :
    Submodule.span ℚ (Set.range (Fin.append u v)) =
      Submodule.span ℚ (Set.range u) ⊔ Submodule.span ℚ (Set.range v) := by
  rw [range_append, Submodule.span_union]

/-- Two bases of the complementary sectors append to a basis of the whole stable subspace. -/
theorem sector_bases_append_linearIndependent
    (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    {p q : ℕ} {u : Fin p → R} {v : Fin q → R}
    (hu : LinearIndependent ℚ u)
    (hv : LinearIndependent ℚ v)
    (huspan : Submodule.span ℚ (Set.range u) = plusSector R hR)
    (hvspan : Submodule.span ℚ (Set.range v) = minusSector R hR) :
    LinearIndependent ℚ (R.subtype ∘ Fin.append u v) := by
  have happend : LinearIndependent ℚ (Fin.append u v) := by
    apply linearIndependent_append_of_disjoint_spans hu hv
    rw [huspan, hvspan]
    exact sectors_disjoint R hR
  exact happend.map' R.subtype (Submodule.ker_subtype R)

/-- The appended sector bases, viewed in `ℂ`, span the original stable subspace exactly. -/
theorem sector_bases_append_span
    (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    {p q : ℕ} {u : Fin p → R} {v : Fin q → R}
    (huspan : Submodule.span ℚ (Set.range u) = plusSector R hR)
    (hvspan : Submodule.span ℚ (Set.range v) = minusSector R hR) :
    Submodule.span ℚ (Set.range (R.subtype ∘ Fin.append u v)) = R := by
  rw [Set.range_comp, Submodule.span_image, span_append, huspan, hvspan,
    sectors_sup_eq_top R hR, Submodule.map_subtype_top]

/-- The graph-generator set of an appended family is the union of the two generator sets. -/
theorem generators_append {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) :
    generators (Fin.append u v) = generators u ∪ generators v := by
  ext z
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine Fin.addCases (motive := fun i ↦
        Fin.append u v i ∈ generators u ∪ generators v)
        (fun j ↦ Or.inl (Or.inl ⟨j, ?_⟩))
        (fun j ↦ Or.inr (Or.inl ⟨j, ?_⟩)) i
      · exact (Fin.append_left u v j).symm
      · exact (Fin.append_right u v j).symm
    · refine Fin.addCases (motive := fun i ↦
        Complex.exp (Fin.append u v i) ∈ generators u ∪ generators v)
        (fun j ↦ Or.inl (Or.inr ⟨j, ?_⟩))
        (fun j ↦ Or.inr (Or.inr ⟨j, ?_⟩)) i
      · exact congrArg Complex.exp (Fin.append_left u v j).symm
      · exact congrArg Complex.exp (Fin.append_right u v j).symm
  · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨i, rfl⟩ | ⟨i, rfl⟩))
    · exact Or.inl ⟨Fin.castAdd n i, Fin.append_left u v i⟩
    · exact Or.inr ⟨Fin.castAdd n i,
        congrArg Complex.exp (Fin.append_left u v i)⟩
    · exact Or.inl ⟨Fin.natAdd m i, Fin.append_right u v i⟩
    · exact Or.inr ⟨Fin.natAdd m i,
        congrArg Complex.exp (Fin.append_right u v i)⟩

/-- The graph field of the combined sectors is exactly the compositum of the two sector graph
fields.  No algebraic-disjointness assertion is made. -/
theorem generatedField_append {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) :
    generatedField (Fin.append u v) = generatedField u ⊔ generatedField v := by
  rw [generatedField, generatedField, generatedField, generators_append,
    IntermediateField.adjoin_union]

/-- The complex family obtained by appending a fixed-sector basis and an anti-fixed-sector
basis. -/
def sectorJoin {m n : ℕ} (R : Submodule ℚ ℂ)
    (u : Fin m → R) (v : Fin n → R) : Fin (m + n) → ℂ :=
  Fin.append (R.subtype ∘ u) (R.subtype ∘ v)

theorem sectorJoin_eq {m n : ℕ} (R : Submodule ℚ ℂ)
    (u : Fin m → R) (v : Fin n → R) :
    sectorJoin R u v = R.subtype ∘ Fin.append u v := by
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [sectorJoin]

/-- A pair of sector bases joins to an independent family in `ℂ`. -/
theorem sectorJoin_linearIndependent
    (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    {p q : ℕ} {u : Fin p → R} {v : Fin q → R}
    (hu : LinearIndependent ℚ u)
    (hv : LinearIndependent ℚ v)
    (huspan : Submodule.span ℚ (Set.range u) = plusSector R hR)
    (hvspan : Submodule.span ℚ (Set.range v) = minusSector R hR) :
    LinearIndependent ℚ (sectorJoin R u v) := by
  rw [sectorJoin_eq]
  exact sector_bases_append_linearIndependent R hR hu hv huspan hvspan

/-- A pair of sector bases joins to a basis of the original subspace in `ℂ`. -/
theorem sectorJoin_span
    (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    {p q : ℕ} {u : Fin p → R} {v : Fin q → R}
    (huspan : Submodule.span ℚ (Set.range u) = plusSector R hR)
    (hvspan : Submodule.span ℚ (Set.range v) = minusSector R hR) :
    Submodule.span ℚ (Set.range (sectorJoin R u v)) = R := by
  rw [sectorJoin_eq]
  exact sector_bases_append_span R hR huspan hvspan

/-- The graph field of the joined eigenbasis is exactly the compositum of the two sector graph
fields. -/
theorem generatedField_sectorJoin {m n : ℕ} (R : Submodule ℚ ℂ)
    (u : Fin m → R) (v : Fin n → R) :
    generatedField (sectorJoin R u v) =
      generatedField (R.subtype ∘ u) ⊔ generatedField (R.subtype ∘ v) := by
  exact generatedField_append (R.subtype ∘ u) (R.subtype ∘ v)

/-- Complete finite sector-basis data, including the distinguished real and period directions. -/
structure SectorBasisData (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R) where
  plusComplementCount : ℕ
  minusComplementCount : ℕ
  plusBasis : Fin (plusComplementCount + 1) → R
  minusBasis : Fin (minusComplementCount + 1) → R
  plusLinearIndependent : LinearIndependent ℚ plusBasis
  minusLinearIndependent : LinearIndependent ℚ minusBasis
  plusSpan : Submodule.span ℚ (Set.range plusBasis) = plusSector R hR
  minusSpan : Submodule.span ℚ (Set.range minusBasis) = minusSector R hR
  plus_zero : plusBasis 0 = oneInStableSubspace R haR
  minus_zero : minusBasis 0 = periodInStableSubspace R haR

/-- Every finite stable rational subspace containing the canonical anchor has finite bases of
its two sectors with `1` and the standard period first. -/
theorem nonempty_sectorBasisData (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R)
    (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R)
    [FiniteDimensional ℚ R] : Nonempty (SectorBasisData R hR haR) := by
  obtain ⟨p, u, hu, huspan, hu0⟩ := exists_plusSector_basis_with_one R hR haR
  obtain ⟨q, v, hv, hvspan, hv0⟩ := exists_minusSector_basis_with_period R hR haR
  exact ⟨{
    plusComplementCount := p
    minusComplementCount := q
    plusBasis := u
    minusBasis := v
    plusLinearIndependent := hu
    minusLinearIndependent := hv
    plusSpan := huspan
    minusSpan := hvspan
    plus_zero := hu0
    minus_zero := hv0 }⟩

/-- The combined family attached to sector-basis data. -/
def SectorBasisData.joined
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Fin ((D.plusComplementCount + 1) + (D.minusComplementCount + 1)) → ℂ :=
  sectorJoin R D.plusBasis D.minusBasis

theorem SectorBasisData.joined_linearIndependent
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    LinearIndependent ℚ D.joined :=
  sectorJoin_linearIndependent R hR D.plusLinearIndependent D.minusLinearIndependent
    D.plusSpan D.minusSpan

theorem SectorBasisData.joined_span
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Submodule.span ℚ (Set.range D.joined) = R :=
  sectorJoin_span R hR D.plusSpan D.minusSpan

theorem SectorBasisData.joined_generatedField
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    generatedField D.joined =
      generatedField (R.subtype ∘ D.plusBasis) ⊔
        generatedField (R.subtype ∘ D.minusBasis) :=
  generatedField_sectorJoin R D.plusBasis D.minusBasis

/-- Honest Kummer comparison with any original family spanning `R`: one positive integer clears
all rational denominators of the joined eigenbasis before its graph field embeds into the
original graph field. -/
theorem SectorBasisData.exists_scale_generatedField_le
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} (w : Fin n → ℂ)
    (hwspan : Submodule.span ℚ (Set.range w) = R) :
    ∃ d : ℤ, 0 < d ∧
      generatedField (ratScaleFamily (d : ℚ) D.joined) ≤ generatedField w := by
  apply exists_pos_integer_scale_generatedField_le_of_span_le D.joined w
  rw [D.joined_span, hwspan]

/-! ## The least stable boundary -/

/-- Every proper, stable, canonically anchored subspace represented by a finite independent
family satisfies its Schanuel bound at a least stable failure.  This is the exact statement
needed for any proper sector-plus-anchor subspace; it deliberately assumes properness rather
than asserting that either sector has surplus dimension. -/
theorem bound_of_proper_stable_anchored_subspace_of_least_failure
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    {k : ℕ} {u : Fin (k + 2) → ℂ}
    (hulin : LinearIndependent ℚ u) (huanchor : CanonicallyAnchored u)
    (hustable : ConjugationStable u)
    (huspan : Submodule.span ℚ (Set.range u) <
      Submodule.span ℚ (Set.range w)) : Bound u := by
  letI : FiniteDimensional ℚ (Submodule.span ℚ (Set.range w)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  have hrank := Submodule.finrank_lt_finrank_of_lt huspan
  have huRank : Module.finrank ℚ (Submodule.span ℚ (Set.range u)) = k + 2 := by
    simpa using finrank_span_eq_card hulin
  have hwRank : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) = n + 2 := by
    simpa using finrank_span_eq_card hwlin
  have hkn : k < n := by
    rw [huRank, hwRank] at hrank
    omega
  by_contra huFail
  exact hmin k hkn ⟨u, hulin, huanchor, hustable, huFail⟩

/-- A proper conjugation-stable subspace containing the canonical anchor has a finite anchored
basis satisfying `Bound` at a least stable failure.  In particular, this applies verbatim to a
proper fixed-sector-plus-anchor or anti-fixed-sector-plus-anchor subspace once its properness is
known. -/
theorem exists_bound_basis_of_proper_stable_anchored_subspace
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (P : Submodule ℚ ℂ)
    (haP : Submodule.span ℚ (Set.range canonicalAnchor) ≤ P)
    (hPstable : P.map conjugationLinearEquiv.toLinearMap = P)
    (hPlt : P < Submodule.span ℚ (Set.range w)) :
    ∃ (k : ℕ) (u : Fin (k + 2) → ℂ),
      LinearIndependent ℚ u ∧ CanonicallyAnchored u ∧ ConjugationStable u ∧
      Submodule.span ℚ (Set.range u) = P ∧ Bound u := by
  obtain ⟨r, t, htlin, htspan⟩ := exists_fin_basis_of_le_span P w hPlt.le
  obtain ⟨k, u, hulin, huspanT, hu0, hu1⟩ :=
    exists_fin_basis_with_canonicalAnchor (by rwa [htspan])
  have huspan : Submodule.span ℚ (Set.range u) = P := huspanT.trans htspan
  have hustable : ConjugationStable u := by
    unfold ConjugationStable
    rw [← map_span_conjugation_eq, huspan, hPstable]
  have huBound := bound_of_proper_stable_anchored_subspace_of_least_failure
    hwlin hmin hulin ⟨hu0, hu1⟩ hustable (huspan.symm ▸ hPlt)
  exact ⟨k, u, hulin, ⟨hu0, hu1⟩, hustable, huspan, huBound⟩

/-- The two sector dimensions add to the dimension of the full stable subspace. -/
theorem SectorBasisData.total_count_eq
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hwspan : Submodule.span ℚ (Set.range w) = R) :
    (D.plusComplementCount + 1) + (D.minusComplementCount + 1) = n + 2 := by
  have hjoinedRank :
      Module.finrank ℚ (Submodule.span ℚ (Set.range D.joined)) =
        (D.plusComplementCount + 1) + (D.minusComplementCount + 1) := by
    simpa using finrank_span_eq_card D.joined_linearIndependent
  have hwRank : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) = n + 2 := by
    simpa using finrank_span_eq_card hwlin
  have hspanEq : Submodule.span ℚ (Set.range D.joined) =
      Submodule.span ℚ (Set.range w) := D.joined_span.trans hwspan.symm
  let e : Submodule.span ℚ (Set.range D.joined) ≃ₗ[ℚ]
      Submodule.span ℚ (Set.range w) :=
    LinearEquiv.ofEq _ _ hspanEq
  calc
    (D.plusComplementCount + 1) + (D.minusComplementCount + 1) =
        Module.finrank ℚ (Submodule.span ℚ (Set.range D.joined)) := hjoinedRank.symm
    _ = Module.finrank ℚ (Submodule.span ℚ (Set.range w)) := e.finrank_eq
    _ = n + 2 := hwRank

/-- CS14: for a defect-one stable family, the compositum of the real-sector and imaginary-sector
graph fields has transcendence degree exactly one below the total input dimension.  This is an
identity for the compositum only; it does not assert algebraic disjointness of the sector fields. -/
theorem SectorBasisData.compositum_trdeg_of_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w) :
    Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          generatedField (R.subtype ∘ D.minusBasis))) =
      (((n + 1 : ℕ) : Cardinal)) := by
  rw [← D.joined_generatedField]
  calc
    Algebra.trdeg ℚ (generatedField D.joined) =
        Algebra.trdeg ℚ (generatedField w) :=
      trdeg_generatedField_eq_of_span_eq D.joined w
        (D.joined_span.trans hwspan.symm)
    _ = (((n + 1 : ℕ) : Cardinal)) := hwdefect

end ConjugationStableSectorBoundary

end

end Schanuel
