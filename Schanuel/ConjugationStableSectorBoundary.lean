import Schanuel.ConjugationStableTerminal
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree
import Mathlib.FieldTheory.Relrank
import Mathlib.GroupTheory.SpecificGroups.KleinFour
import Mathlib.RingTheory.Norm.Transitivity

/-!
# Real and imaginary sectors of a conjugation-stable failure

On a finite rational subspace preserved by complex conjugation, the half-sum and half-difference
operators split the space into the `+1` and `-1` eigensubspaces.  For a subspace containing the
canonical anchor, those sectors contain `1` and the standard period respectively.  This module
keeps the graph fields of the two sectors separate and records their exact compositum; comparison
with an original graph field uses an explicit common integral denominator.
-/

namespace Schanuel

open Function Set Filter Topology

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

/-- The graph field of the singleton standard period is just the field generated by the period:
its exponential is `1`. -/
theorem generatedField_periodSingleton_eq :
    generatedField (fun _ : Fin 1 ↦ standardPeriod) =
      IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) := by
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    · change Complex.exp standardPeriod ∈ _
      rw [exp_standardPeriod]
      exact (IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ)).one_mem
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)

/-- The singleton period graph field contributes at most one transcendence unit. -/
theorem trdeg_generatedField_periodSingleton_le_one :
    Algebra.trdeg ℚ (generatedField (fun _ : Fin 1 ↦ standardPeriod)) ≤ 1 := by
  rw [generatedField_periodSingleton_eq, ← cRk_eq_trdeg_adjoin]
  calc
    complexAlgebraicMatroid.cRk ({standardPeriod} : Set ℂ) ≤
        Cardinal.mk ({standardPeriod} : Set ℂ) :=
      complexAlgebraicMatroid.cRk_le_cardinalMk _
    _ = 1 := by simp

/-- The graph field of the singleton real unit is just the field generated by `exp 1`. -/
theorem generatedField_oneSingleton_eq :
    generatedField (fun _ : Fin 1 ↦ (1 : ℂ)) =
      IntermediateField.adjoin ℚ ({Complex.exp (1 : ℂ)} : Set ℂ) := by
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact (IntermediateField.adjoin ℚ ({Complex.exp (1 : ℂ)} : Set ℂ)).one_mem
    · exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨0, rfl⟩)

/-- The singleton real-unit graph field contributes at most one transcendence unit. -/
theorem trdeg_generatedField_oneSingleton_le_one :
    Algebra.trdeg ℚ (generatedField (fun _ : Fin 1 ↦ (1 : ℂ))) ≤ 1 := by
  rw [generatedField_oneSingleton_eq, ← cRk_eq_trdeg_adjoin]
  calc
    complexAlgebraicMatroid.cRk ({Complex.exp (1 : ℂ)} : Set ℂ) ≤
        Cardinal.mk ({Complex.exp (1 : ℂ)} : Set ℂ) :=
      complexAlgebraicMatroid.cRk_le_cardinalMk _
    _ = 1 := by simp

/-- The singleton real-unit graph field contributes exactly one transcendence unit. -/
theorem trdeg_generatedField_oneSingleton_eq_one :
    Algebra.trdeg ℚ (generatedField (fun _ : Fin 1 ↦ (1 : ℂ))) = 1 := by
  apply le_antisymm trdeg_generatedField_oneSingleton_le_one
  have hb := LindemannAttempt.bound_singleton_ratCast (1 : ℚ) (by norm_num)
  have hf : singletonFamily ((1 : ℚ) : ℂ) = (fun _ : Fin 1 ↦ (1 : ℂ)) := by
    funext i
    norm_num [singletonFamily]
  rw [hf] at hb
  simpa [Bound] using hb

/-- The transcendence degree of a compositum is at most the sum of the two field degrees. -/
theorem trdeg_sup_le_add (K L : IntermediateField ℚ ℂ) :
    Algebra.trdeg ℚ (↥(K ⊔ L)) ≤
      Algebra.trdeg ℚ K + Algebra.trdeg ℚ L := by
  calc
    Algebra.trdeg ℚ (↥(K ⊔ L)) =
        0 + Algebra.trdeg ℚ (↥(K ⊔ L)) := by simp
    _ ≤ Algebra.trdeg ℚ (↥(K ⊓ L)) + Algebra.trdeg ℚ (↥(K ⊔ L)) := by
      exact add_le_add
        (show (0 : Cardinal) ≤ Algebra.trdeg ℚ (↥(K ⊓ L)) from bot_le) le_rfl
    _ ≤ Algebra.trdeg ℚ K + Algebra.trdeg ℚ L :=
      trdeg_inf_add_trdeg_sup_le K L

/-! ## A real core for an anti-fixed graph field -/

/-- The intermediate field of complex numbers fixed pointwise by conjugation. -/
def conjugationFixedField : IntermediateField ℚ ℂ where
  carrier := {z | star z = z}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    change star x = x at hx
    change star y = y at hy
    change star (x + y) = x + y
    rw [star_add, hx, hy]
  mul_mem' := by
    intro x y hx hy
    change star x = x at hx
    change star y = y at hy
    change star (x * y) = x * y
    rw [star_mul', hx, hy]
  algebraMap_mem' := by
    intro q
    simp
  inv_mem' := by
    intro x hx
    change star x = x at hx
    change star x⁻¹ = x⁻¹
    rw [star_inv₀, hx]

@[simp]
theorem mem_conjugationFixedField_iff (z : ℂ) :
    z ∈ conjugationFixedField ↔ star z = z := Iff.rfl

/-- The full graph field of a pointwise fixed family is pointwise fixed by conjugation. -/
theorem generatedField_le_conjugationFixedField_of_fixed {n : ℕ} (u : Fin n → ℂ)
    (hfixed : ∀ i, star (u i) = u i) :
    generatedField u ≤ conjugationFixedField := by
  rw [generatedField, IntermediateField.adjoin_le_iff]
  rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact hfixed i
  · have hi : (starRingEnd ℂ) (u i) = u i := by
      simpa only [starRingEnd_apply] using hfixed i
    change (starRingEnd ℂ) (Complex.exp (u i)) = Complex.exp (u i)
    rw [← Complex.exp_conj, hi]

/-- The square of the standard imaginary period is fixed by conjugation. -/
theorem star_standardPeriod_sq : star (standardPeriod ^ 2) = standardPeriod ^ 2 := by
  have hω := star_standardPeriod
  rw [Complex.star_def] at hω ⊢
  rw [map_pow, hω]
  ring

/-- The squared standard period is exactly the rational multiple `-4` of `pi^2`. -/
theorem standardPeriod_sq_eq_neg_four_pi_sq :
    standardPeriod ^ 2 = -4 * (Real.pi : ℂ) ^ 2 := by
  change (2 * Real.pi * Complex.I : ℂ) ^ 2 = -4 * (Real.pi : ℂ) ^ 2
  rw [mul_pow, mul_pow, Complex.I_sq]
  norm_num

/-- The square of `pi`, viewed in `C`, is transcendental. -/
theorem pi_sq_transcendental : Transcendental ℚ ((Real.pi : ℂ) ^ 2) := by
  intro hpi
  apply FullyTranscendentalPeriodBoundary.period_transcendental.pow
    (n := 2) (by norm_num)
  rw [standardPeriod_sq_eq_neg_four_pi_sq]
  simpa using (isAlgebraic_algebraMap (A := ℂ) (-4 : ℚ)).mul hpi

/-- The algebraic-matroid rank of the singleton `pi^2` is exactly one.  Together with
`cRk_eq_trdeg_adjoin`, this says that `Q(pi^2)` has transcendence degree one. -/
theorem cRk_pi_sq_singleton_eq_one :
    complexAlgebraicMatroid.cRk ({(Real.pi : ℂ) ^ 2} : Set ℂ) = 1 := by
  have hAI : AlgebraicIndependent ℚ (fun _ : Fin 1 ↦ (Real.pi : ℂ) ^ 2) := by
    rw [algebraicIndependent_unique_type_iff]
    exact pi_sq_transcendental
  have hIndep : complexAlgebraicMatroid.Indep
      (Set.range fun _ : Fin 1 ↦ (Real.pi : ℂ) ^ 2) :=
    AlgebraicIndependent.matroid_indep_iff.mpr hAI.to_subtype_range
  calc
    complexAlgebraicMatroid.cRk ({(Real.pi : ℂ) ^ 2} : Set ℂ) =
        complexAlgebraicMatroid.cRk
          (Set.range fun _ : Fin 1 ↦ (Real.pi : ℂ) ^ 2) := by simp
    _ = Cardinal.mk (Set.range fun _ : Fin 1 ↦ (Real.pi : ℂ) ^ 2) :=
      hIndep.cRk_eq_cardinalMk.symm
    _ = 1 := by simp

/-- Adjoining the squared standard period is literally the same as adjoining `pi^2`. -/
theorem adjoin_standardPeriod_sq_eq_adjoin_pi_sq :
    IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) =
      IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    rw [standardPeriod_sq_eq_neg_four_pi_sq]
    exact (IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ)).mul_mem
      (by simp)
      (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    have hω : standardPeriod ^ 2 ∈
        IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) :=
      IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)
    have hc : (-(1 / 4 : ℚ) : ℂ) ∈
        IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) := by
      simp
    have hmul :=
      (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ)).mul_mem hc hω
    convert hmul using 1
    change (Real.pi : ℂ) ^ 2 = (-(1 / 4 : ℚ) : ℂ) * standardPeriod ^ 2
    rw [standardPeriod_sq_eq_neg_four_pi_sq]
    norm_num
    ring

/-- Dividing an anti-fixed input by the standard period produces a conjugation-fixed number. -/
theorem star_antiFixed_ratio {n : ℕ} (u : Fin (n + 1) → ℂ)
    (hanti : ∀ i, star (u i) = -u i) (i) :
    star (u i / standardPeriod) = u i / standardPeriod := by
  have hi : (starRingEnd ℂ) (u i) = -u i := by
    simpa only [starRingEnd_apply] using hanti i
  have hω : (starRingEnd ℂ) standardPeriod = -standardPeriod := by
    simpa only [starRingEnd_apply] using star_standardPeriod
  change (starRingEnd ℂ) (u i / standardPeriod) = u i / standardPeriod
  rw [map_div₀ (starRingEnd ℂ), hi, hω]
  simp

/-- The trace-like sum of an anti-fixed exponential value and its inverse is real. -/
theorem star_antiFixed_trace {n : ℕ} (u : Fin (n + 1) → ℂ)
    (hanti : ∀ i, star (u i) = -u i) (i) :
    star (Complex.exp (u i) + (Complex.exp (u i))⁻¹) =
      Complex.exp (u i) + (Complex.exp (u i))⁻¹ := by
  have hi : (starRingEnd ℂ) (u i) = -u i := by
    simpa only [starRingEnd_apply] using hanti i
  change (starRingEnd ℂ) (Complex.exp (u i) + (Complex.exp (u i))⁻¹) = _
  rw [map_add, map_inv₀, ← Complex.exp_conj, hi, Complex.exp_neg]
  simp only [inv_inv]
  exact add_comm (Complex.exp (u i))⁻¹ (Complex.exp (u i))

/-- The skew trace divided by the anti-fixed period is also real. -/
theorem star_antiFixed_skew {n : ℕ} (u : Fin (n + 1) → ℂ)
    (hanti : ∀ i, star (u i) = -u i) (i) :
    star ((Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod) =
      (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod := by
  have hi : (starRingEnd ℂ) (u i) = -u i := by
    simpa only [starRingEnd_apply] using hanti i
  have hω : (starRingEnd ℂ) standardPeriod = -standardPeriod := by
    simpa only [starRingEnd_apply] using star_standardPeriod
  change (starRingEnd ℂ)
    ((Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod) = _
  rw [map_div₀ (starRingEnd ℂ), map_sub, map_inv₀, ← Complex.exp_conj, hi,
    Complex.exp_neg, hω]
  simp only [inv_inv]
  ring

/-- The explicit conjugation-fixed core generated by the squared period, normalized anti-fixed
inputs, traces of their exponential values, and normalized skew traces. -/
def antiFixedRealCore {n : ℕ} (u : Fin (n + 1) → ℂ) : IntermediateField ℚ ℂ :=
  ((IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
      IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod)) ⊔
    IntermediateField.adjoin ℚ
      (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹)) ⊔
  IntermediateField.adjoin ℚ
    (Set.range fun i ↦ (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod)

/-- For an anti-fixed family, every element of the explicit core is pointwise fixed by
conjugation. -/
theorem antiFixedRealCore_le_conjugationFixedField {n : ℕ}
    (u : Fin (n + 1) → ℂ) (hanti : ∀ i, star (u i) = -u i) :
    antiFixedRealCore u ≤ conjugationFixedField := by
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact star_standardPeriod_sq
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact star_antiFixed_ratio u hanti i
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact star_antiFixed_trace u hanti i
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact star_antiFixed_skew u hanti i

/-- The squared period belongs to every explicit anti-fixed real core. -/
theorem period_sq_mem_antiFixedRealCore {n : ℕ} (u : Fin (n + 1) → ℂ) :
    standardPeriod ^ 2 ∈ antiFixedRealCore u := by
  unfold antiFixedRealCore
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
        IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod) ⊔
      IntermediateField.adjoin ℚ
        (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹)) ≤ _
    from le_sup_left)
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
      IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod)) ≤ _
    from le_sup_left)
  apply (show IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ≤ _
    from le_sup_left)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

/-- The period is algebraic of degree at most two over the explicit real core because its square
already lies there. -/
theorem standardPeriod_isAlgebraic_antiFixedRealCore {n : ℕ}
    (u : Fin (n + 1) → ℂ) : IsAlgebraic (antiFixedRealCore u) standardPeriod := by
  let s : antiFixedRealCore u := ⟨standardPeriod ^ 2,
    period_sq_mem_antiFixedRealCore u⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.C s,
    (Polynomial.monic_X_pow_sub_C s (by norm_num)).ne_zero, ?_⟩
  simp [s]

/-- If the anti-fixed family starts with the period, its real core is contained in its graph
field. -/
theorem antiFixedRealCore_le_generatedField {n : ℕ} (u : Fin (n + 1) → ℂ)
    (hu0 : u 0 = standardPeriod) :
    antiFixedRealCore u ≤ generatedField u := by
  have hω : standardPeriod ∈ generatedField u := by
    rw [← hu0]
    exact IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact (generatedField u).pow_mem hω 2
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    exact (generatedField u).div_mem
      (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)) hω
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have hy : Complex.exp (u i) ∈ generatedField u :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)
    exact (generatedField u).add_mem hy ((generatedField u).inv_mem hy)
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨i, rfl⟩
    have hy : Complex.exp (u i) ∈ generatedField u :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)
    exact (generatedField u).div_mem
      ((generatedField u).sub_mem hy ((generatedField u).inv_mem hy)) hω

theorem ratio_mem_antiFixedRealCore {n : ℕ} (u : Fin (n + 1) → ℂ) (i) :
    u i / standardPeriod ∈ antiFixedRealCore u := by
  unfold antiFixedRealCore
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
        IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod) ⊔
      IntermediateField.adjoin ℚ
        (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹)) ≤ _
    from le_sup_left)
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
      IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod)) ≤ _
    from le_sup_left)
  apply (show IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod) ≤ _
    from le_sup_right)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)

theorem trace_mem_antiFixedRealCore {n : ℕ} (u : Fin (n + 1) → ℂ) (i) :
    Complex.exp (u i) + (Complex.exp (u i))⁻¹ ∈ antiFixedRealCore u := by
  unfold antiFixedRealCore
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
        IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod) ⊔
      IntermediateField.adjoin ℚ
        (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹)) ≤ _
    from le_sup_left)
  apply (show IntermediateField.adjoin ℚ
      (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹) ≤ _
    from le_sup_right)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)

theorem skew_mem_antiFixedRealCore {n : ℕ} (u : Fin (n + 1) → ℂ) (i) :
    (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod ∈
      antiFixedRealCore u := by
  apply (show IntermediateField.adjoin ℚ
      (Set.range fun i ↦ (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod) ≤
      antiFixedRealCore u from by simp [antiFixedRealCore])
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)

/-- Exact reconstruction of an anti-fixed graph field from its explicit real core and the
standard period.  The formulas are `uᵢ=(uᵢ/ω)ω` and
`exp(uᵢ)=(cᵢ+ωdᵢ)/2`. -/
theorem generatedField_eq_antiFixedRealCore_adjoin_period {n : ℕ}
    (u : Fin (n + 1) → ℂ) (hu0 : u 0 = standardPeriod) :
    generatedField u = antiFixedRealCore u ⊔
      IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) := by
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · have ha : u i / standardPeriod ∈ antiFixedRealCore u :=
        ratio_mem_antiFixedRealCore u i
      have ha' : u i / standardPeriod ∈ antiFixedRealCore u ⊔
          IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) :=
        (show antiFixedRealCore u ≤ _ from le_sup_left) ha
      have hω : standardPeriod ∈ antiFixedRealCore u ⊔
          IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) :=
        (show IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) ≤ _ from le_sup_right)
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
      convert (antiFixedRealCore u ⊔
        IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ)).mul_mem ha' hω using 1
      field_simp [FullyTranscendentalPeriodBoundary.period_ne_zero]
    · have hc : Complex.exp (u i) + (Complex.exp (u i))⁻¹ ∈ antiFixedRealCore u :=
        trace_mem_antiFixedRealCore u i
      have hd : (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod ∈
          antiFixedRealCore u := skew_mem_antiFixedRealCore u i
      have hc' : Complex.exp (u i) + (Complex.exp (u i))⁻¹ ∈
          antiFixedRealCore u ⊔ IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) :=
        (show antiFixedRealCore u ≤ _ from le_sup_left) hc
      have hd' : (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod ∈
          antiFixedRealCore u ⊔ IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) :=
        (show antiFixedRealCore u ≤ _ from le_sup_left) hd
      have hω : standardPeriod ∈ antiFixedRealCore u ⊔
          IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) :=
        (show IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) ≤ _ from le_sup_right)
          (IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _))
      have hsum := (antiFixedRealCore u ⊔
        IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ)).add_mem hc'
          ((antiFixedRealCore u ⊔ IntermediateField.adjoin ℚ
            ({standardPeriod} : Set ℂ)).mul_mem hω hd')
      have hhalf := (antiFixedRealCore u ⊔
        IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ)).mul_mem
          (IntermediateField.algebraMap_mem _ (1 / 2 : ℚ)) hsum
      convert hhalf using 1
      field_simp [FullyTranscendentalPeriodBoundary.period_ne_zero]
      norm_num
      ring
  · apply sup_le
    · exact antiFixedRealCore_le_generatedField u hu0
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      subst x
      rw [← hu0]
      exact IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)

/-- Adjoining the period back to the explicit real core changes no transcendence degree.  Hence
an anti-fixed graph field beginning with the period and its real core have exactly the same
degree over `ℚ`. -/
theorem trdeg_generatedField_eq_antiFixedRealCore {n : ℕ}
    (u : Fin (n + 1) → ℂ) (hu0 : u 0 = standardPeriod) :
    Algebra.trdeg ℚ (generatedField u) = Algebra.trdeg ℚ (antiFixedRealCore u) := by
  let C := antiFixedRealCore u
  let L : IntermediateField C ℂ :=
    IntermediateField.adjoin C ({standardPeriod} : Set ℂ)
  have homega : IsAlgebraic C standardPeriod :=
    standardPeriod_isAlgebraic_antiFixedRealCore u
  letI : Algebra.IsAlgebraic C L := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact homega.isIntegral
  letI : IsScalarTower ℚ C L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have htower : Algebra.trdeg ℚ C + Algebra.trdeg C L = Algebra.trdeg ℚ L :=
    trdeg_add_eq ℚ C
  have hrel : Algebra.trdeg C L = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at htower
  have hL : L.restrictScalars ℚ = generatedField u := by
    rw [show L.restrictScalars ℚ = C ⊔
        IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) from
      IntermediateField.restrictScalars_adjoin_eq_sup ℚ C _]
    exact (generatedField_eq_antiFixedRealCore_adjoin_period u hu0).symm
  have heq := (IntermediateField.equivOfEq hL).trdeg_eq
  exact heq.symm.trans htower.symm

/-! ### Removing the algebraic skew-trace generators -/

/-- The smaller even core: squared period, normalized anti-fixed inputs, and exponential traces.
The normalized skew traces omitted here are quadratic over this field. -/
def antiFixedEvenCore {n : ℕ} (u : Fin (n + 1) → ℂ) : IntermediateField ℚ ℂ :=
  (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
      IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod)) ⊔
    IntermediateField.adjoin ℚ
      (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹)

theorem period_sq_mem_antiFixedEvenCore {n : ℕ} (u : Fin (n + 1) → ℂ) :
    standardPeriod ^ 2 ∈ antiFixedEvenCore u := by
  unfold antiFixedEvenCore
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
      IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod)) ≤ _
    from le_sup_left)
  apply (show IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ≤ _
    from le_sup_left)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

theorem ratio_mem_antiFixedEvenCore {n : ℕ} (u : Fin (n + 1) → ℂ) (i) :
    u i / standardPeriod ∈ antiFixedEvenCore u := by
  unfold antiFixedEvenCore
  apply (show
    (IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) ⊔
      IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod)) ≤ _
    from le_sup_left)
  apply (show IntermediateField.adjoin ℚ (Set.range fun i ↦ u i / standardPeriod) ≤ _
    from le_sup_right)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)

theorem trace_mem_antiFixedEvenCore {n : ℕ} (u : Fin (n + 1) → ℂ) (i) :
    Complex.exp (u i) + (Complex.exp (u i))⁻¹ ∈ antiFixedEvenCore u := by
  unfold antiFixedEvenCore
  apply (show IntermediateField.adjoin ℚ
      (Set.range fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹) ≤ _
    from le_sup_right)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)

/-- With no non-period anti-fixed direction, the even core has no generators beyond the squared
standard period. -/
theorem antiFixedEvenCore_fin1_eq_adjoin_period_sq
    (u : Fin 1 → ℂ) (hu0 : u 0 = standardPeriod) :
    antiFixedEvenCore u =
      IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ) := by
  let A := IntermediateField.adjoin ℚ ({standardPeriod ^ 2} : Set ℂ)
  apply le_antisymm
  · unfold antiFixedEvenCore
    apply sup_le
    · apply sup_le le_rfl
      rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
      change u 0 / standardPeriod ∈ A
      rw [hu0]
      simp [FullyTranscendentalPeriodBoundary.period_ne_zero]
    · rw [IntermediateField.adjoin_le_iff]
      rintro _ ⟨i, rfl⟩
      have hi : i = 0 := Fin.eq_zero i
      rw [hi]
      change Complex.exp (u 0) + (Complex.exp (u 0))⁻¹ ∈ A
      rw [hu0, exp_standardPeriod]
      exact A.add_mem A.one_mem (A.inv_mem A.one_mem)
  · exact le_sup_left.trans le_sup_left

/-- The singleton even core is literally `Q(pi^2)`. -/
theorem antiFixedEvenCore_fin1_eq_adjoin_pi_sq
    (u : Fin 1 → ℂ) (hu0 : u 0 = standardPeriod) :
    antiFixedEvenCore u =
      IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ) :=
  (antiFixedEvenCore_fin1_eq_adjoin_period_sq u hu0).trans
    adjoin_standardPeriod_sq_eq_adjoin_pi_sq

/-- The completely real form of the two-generator canonical anchor field. -/
def realAnchorField : IntermediateField ℚ ℂ :=
  generatedField (fun _ : Fin 1 ↦ (1 : ℂ)) ⊔
    IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ)

theorem realAnchorField_eq_exp_one_sup_pi_sq :
    realAnchorField =
      IntermediateField.adjoin ℚ ({Complex.exp (1 : ℂ)} : Set ℂ) ⊔
        IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ) := by
  rw [realAnchorField, generatedField_oneSingleton_eq]

theorem realAnchorField_eq_adjoin_exp_one_pi_sq :
    realAnchorField = IntermediateField.adjoin ℚ
      ({Complex.exp (1 : ℂ), (Real.pi : ℂ) ^ 2} : Set ℂ) := by
  rw [realAnchorField_eq_exp_one_sup_pi_sq, ← IntermediateField.adjoin_union]
  congr 1

/-- Every element of the real anchor field `Q(e, pi^2)` is fixed by complex conjugation. -/
theorem realAnchorField_le_conjugationFixedField :
    realAnchorField ≤ conjugationFixedField := by
  unfold realAnchorField
  apply sup_le
  · apply generatedField_le_conjugationFixedField_of_fixed
    intro i
    simp
  · rw [← adjoin_standardPeriod_sq_eq_adjoin_pi_sq,
      IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact star_standardPeriod_sq

theorem antiFixedEvenCore_le_antiFixedRealCore {n : ℕ} (u : Fin (n + 1) → ℂ) :
    antiFixedEvenCore u ≤ antiFixedRealCore u := by
  exact le_sup_left

/-- For an anti-fixed family, the smaller even core is pointwise fixed by conjugation. -/
theorem antiFixedEvenCore_le_conjugationFixedField {n : ℕ}
    (u : Fin (n + 1) → ℂ) (hanti : ∀ i, star (u i) = -u i) :
    antiFixedEvenCore u ≤ conjugationFixedField :=
  (antiFixedEvenCore_le_antiFixedRealCore u).trans
    (antiFixedRealCore_le_conjugationFixedField u hanti)

/-- The normalized skew trace is quadratic over the even core.  This is the algebraic form of
`ω² dᵢ² = cᵢ² - 4`. -/
theorem skew_isAlgebraic_antiFixedEvenCore {n : ℕ}
    (u : Fin (n + 1) → ℂ) (i) :
    IsAlgebraic (antiFixedEvenCore u)
      ((Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod) := by
  let y := Complex.exp (u i)
  let c := y + y⁻¹
  have hω2 : standardPeriod ^ 2 ∈ antiFixedEvenCore u :=
    period_sq_mem_antiFixedEvenCore u
  have hc : c ∈ antiFixedEvenCore u := trace_mem_antiFixedEvenCore u i
  have hcoef : (c ^ 2 - 4) / standardPeriod ^ 2 ∈ antiFixedEvenCore u := by
    exact (antiFixedEvenCore u).div_mem
      ((antiFixedEvenCore u).sub_mem ((antiFixedEvenCore u).pow_mem hc 2)
        (IntermediateField.algebraMap_mem _ (4 : ℚ))) hω2
  let a : antiFixedEvenCore u := ⟨(c ^ 2 - 4) / standardPeriod ^ 2, hcoef⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a,
    (Polynomial.monic_X_pow_sub_C a (by norm_num)).ne_zero, ?_⟩
  simp [a, c, y]
  field_simp [FullyTranscendentalPeriodBoundary.period_ne_zero, Complex.exp_ne_zero]
  ring

theorem antiFixedRealCore_eq_evenCore_sup_skew {n : ℕ} (u : Fin (n + 1) → ℂ) :
    antiFixedRealCore u = antiFixedEvenCore u ⊔
      IntermediateField.adjoin ℚ
        (Set.range fun i ↦
          (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod) := rfl

/-- The real core and the smaller even core have equal transcendence degree: every omitted skew
trace is quadratic over the even core. -/
theorem trdeg_antiFixedRealCore_eq_evenCore {n : ℕ} (u : Fin (n + 1) → ℂ) :
    Algebra.trdeg ℚ (antiFixedRealCore u) = Algebra.trdeg ℚ (antiFixedEvenCore u) := by
  let C := antiFixedEvenCore u
  let S : Set ℂ := Set.range fun i ↦
    (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod
  let L : IntermediateField C ℂ := IntermediateField.adjoin C S
  letI : Algebra.IsAlgebraic C L := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (skew_isAlgebraic_antiFixedEvenCore u i).isIntegral
  letI : IsScalarTower ℚ C L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have htower : Algebra.trdeg ℚ C + Algebra.trdeg C L = Algebra.trdeg ℚ L :=
    trdeg_add_eq ℚ C
  have hrel : Algebra.trdeg C L = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at htower
  have hL : L.restrictScalars ℚ = antiFixedRealCore u := by
    calc
      L.restrictScalars ℚ = C ⊔ IntermediateField.adjoin ℚ S :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ C _
      _ = antiFixedRealCore u := by
        rw [antiFixedRealCore_eq_evenCore_sup_skew]
  have heq := (IntermediateField.equivOfEq hL).trdeg_eq
  exact heq.symm.trans htower.symm

/-- A normalized skew trace remains algebraic after adjoining any other intermediate field to
the even core. -/
theorem skew_isAlgebraic_sup_antiFixedEvenCore
    (K : IntermediateField ℚ ℂ) {n : ℕ} (u : Fin (n + 1) → ℂ) (i) :
    IsAlgebraic (↥(K ⊔ antiFixedEvenCore u))
      ((Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod) := by
  let C := K ⊔ antiFixedEvenCore u
  let y := Complex.exp (u i)
  let c := y + y⁻¹
  have hω2 : standardPeriod ^ 2 ∈ C :=
    (show antiFixedEvenCore u ≤ C from le_sup_right)
      (period_sq_mem_antiFixedEvenCore u)
  have hc : c ∈ C :=
    (show antiFixedEvenCore u ≤ C from le_sup_right)
      (trace_mem_antiFixedEvenCore u i)
  have hcoef : (c ^ 2 - 4) / standardPeriod ^ 2 ∈ C := by
    exact C.div_mem (C.sub_mem (C.pow_mem hc 2)
      (IntermediateField.algebraMap_mem _ (4 : ℚ))) hω2
  let a : C := ⟨(c ^ 2 - 4) / standardPeriod ^ 2, hcoef⟩
  refine ⟨Polynomial.X ^ 2 - Polynomial.C a,
    (Polynomial.monic_X_pow_sub_C a (by norm_num)).ne_zero, ?_⟩
  simp [a, c, y]
  field_simp [FullyTranscendentalPeriodBoundary.period_ne_zero, Complex.exp_ne_zero]
  ring

/-- Compositing with an arbitrary field does not change the equality of transcendence degrees
between the real core and the smaller even core. -/
theorem trdeg_sup_antiFixedRealCore_eq_sup_evenCore
    (K : IntermediateField ℚ ℂ) {n : ℕ} (u : Fin (n + 1) → ℂ) :
    Algebra.trdeg ℚ (↥(K ⊔ antiFixedRealCore u)) =
      Algebra.trdeg ℚ (↥(K ⊔ antiFixedEvenCore u)) := by
  let C := K ⊔ antiFixedEvenCore u
  let S : Set ℂ := Set.range fun i ↦
    (Complex.exp (u i) - (Complex.exp (u i))⁻¹) / standardPeriod
  let L : IntermediateField C ℂ := IntermediateField.adjoin C S
  letI : Algebra.IsAlgebraic C L := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (skew_isAlgebraic_sup_antiFixedEvenCore K u i).isIntegral
  letI : IsScalarTower ℚ C L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have htower : Algebra.trdeg ℚ C + Algebra.trdeg C L = Algebra.trdeg ℚ L :=
    trdeg_add_eq ℚ C
  have hrel : Algebra.trdeg C L = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at htower
  have hL : L.restrictScalars ℚ = K ⊔ antiFixedRealCore u := by
    calc
      L.restrictScalars ℚ = C ⊔ IntermediateField.adjoin ℚ S :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ C _
      _ = K ⊔ (antiFixedEvenCore u ⊔ IntermediateField.adjoin ℚ S) := by
        simp only [C, sup_assoc]
      _ = K ⊔ antiFixedRealCore u := by
        rw [← antiFixedRealCore_eq_evenCore_sup_skew]
  have heq := (IntermediateField.equivOfEq hL).trdeg_eq
  exact heq.symm.trans htower.symm

/-- Replacing an anti-fixed graph field by its explicit real core preserves transcendence degree
after compositing with any other intermediate field.  Algebraically, the only omitted generator
is the period, whose square already lies in the core. -/
theorem trdeg_sup_generatedField_eq_sup_antiFixedRealCore
    (K : IntermediateField ℚ ℂ) {n : ℕ} (u : Fin (n + 1) → ℂ)
    (hu0 : u 0 = standardPeriod) :
    Algebra.trdeg ℚ (↥(K ⊔ generatedField u)) =
      Algebra.trdeg ℚ (↥(K ⊔ antiFixedRealCore u)) := by
  let C := K ⊔ antiFixedRealCore u
  have hs : standardPeriod ^ 2 ∈ C :=
    (show antiFixedRealCore u ≤ C from le_sup_right)
      (period_sq_mem_antiFixedRealCore u)
  have homega : IsAlgebraic C standardPeriod := by
    let s : C := ⟨standardPeriod ^ 2, hs⟩
    refine ⟨Polynomial.X ^ 2 - Polynomial.C s,
      (Polynomial.monic_X_pow_sub_C s (by norm_num)).ne_zero, ?_⟩
    simp [s]
  let L : IntermediateField C ℂ :=
    IntermediateField.adjoin C ({standardPeriod} : Set ℂ)
  letI : Algebra.IsAlgebraic C L := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact homega.isIntegral
  letI : IsScalarTower ℚ C L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have htower : Algebra.trdeg ℚ C + Algebra.trdeg C L = Algebra.trdeg ℚ L :=
    trdeg_add_eq ℚ C
  have hrel : Algebra.trdeg C L = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at htower
  have hL : L.restrictScalars ℚ = K ⊔ generatedField u := by
    calc
      L.restrictScalars ℚ = C ⊔
          IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ C _
      _ = K ⊔ (antiFixedRealCore u ⊔
          IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ)) := by
        simp only [C, sup_assoc]
      _ = K ⊔ generatedField u := by
        rw [← generatedField_eq_antiFixedRealCore_adjoin_period u hu0]
  have heq := (IntermediateField.equivOfEq hL).trdeg_eq
  exact heq.symm.trans htower.symm

/-- The anti-fixed graph field can be replaced directly by the smaller even core inside any
compositum without changing transcendence degree. -/
theorem trdeg_sup_generatedField_eq_sup_antiFixedEvenCore
    (K : IntermediateField ℚ ℂ) {n : ℕ} (u : Fin (n + 1) → ℂ)
    (hu0 : u 0 = standardPeriod) :
    Algebra.trdeg ℚ (↥(K ⊔ generatedField u)) =
      Algebra.trdeg ℚ (↥(K ⊔ antiFixedEvenCore u)) :=
  (trdeg_sup_generatedField_eq_sup_antiFixedRealCore K u hu0).trans
    (trdeg_sup_antiFixedRealCore_eq_sup_evenCore K u)

/-- The canonical anchor graph field and the entirely real field `Q(e, pi^2)` have exactly the
same transcendence degree. -/
theorem trdeg_canonicalAnchor_eq_realAnchorField :
    Algebra.trdeg ℚ (generatedField canonicalAnchor) =
      Algebra.trdeg ℚ realAnchorField := by
  let u : Fin 1 → ℂ := fun _ ↦ standardPeriod
  let K := generatedField (fun _ : Fin 1 ↦ (1 : ℂ))
  have hu0 : u 0 = standardPeriod := rfl
  have h := trdeg_sup_generatedField_eq_sup_antiFixedEvenCore K u hu0
  rw [antiFixedEvenCore_fin1_eq_adjoin_pi_sq u hu0] at h
  have hreal : Algebra.trdeg ℚ (↥(K ⊔ generatedField u)) =
      Algebra.trdeg ℚ realAnchorField := by
    simpa [realAnchorField, K] using h
  have happend : Fin.append (fun _ : Fin 1 ↦ (1 : ℂ)) u =
      FullyTranscendentalPeriodBoundary.base := by
    funext i
    fin_cases i <;> rfl
  calc
    Algebra.trdeg ℚ (generatedField canonicalAnchor) =
        Algebra.trdeg ℚ (generatedField FullyTranscendentalPeriodBoundary.base) := by
          rw [FullyTranscendentalPeriodBoundary.generatedField_family_eq_base]
    _ = Algebra.trdeg ℚ (↥(K ⊔ generatedField u)) := by
      rw [← generatedField_append, happend]
    _ = Algebra.trdeg ℚ realAnchorField := hreal

theorem trdeg_realAnchorField_le_two :
    Algebra.trdeg ℚ realAnchorField ≤ (2 : Cardinal) := by
  let K := generatedField (fun _ : Fin 1 ↦ (1 : ℂ))
  let L := IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ)
  change Algebra.trdeg ℚ (↥(K ⊔ L)) ≤ (2 : Cardinal)
  have hK : Algebra.trdeg ℚ K ≤ 1 := by
    simpa [K] using trdeg_generatedField_oneSingleton_le_one
  have hL : Algebra.trdeg ℚ L ≤ 1 := by
    dsimp [L]
    rw [← cRk_eq_trdeg_adjoin]
    calc
      complexAlgebraicMatroid.cRk ({(Real.pi : ℂ) ^ 2} : Set ℂ) ≤
          Cardinal.mk ({(Real.pi : ℂ) ^ 2} : Set ℂ) :=
        complexAlgebraicMatroid.cRk_le_cardinalMk _
      _ = 1 := by simp
  calc
    Algebra.trdeg ℚ (↥(K ⊔ L)) ≤
        Algebra.trdeg ℚ K + Algebra.trdeg ℚ L := trdeg_sup_le_add _ _
    _ ≤ 1 + 1 := add_le_add hK hL
    _ = 2 := by norm_num

/-- The explicit ordered pair `(pi^2, e)` generating the real anchor field. -/
def realAnchorCore : Fin 2 → ℂ :=
  ![(Real.pi : ℂ) ^ 2, Complex.exp (1 : ℂ)]

@[simp] theorem realAnchorCore_zero :
    realAnchorCore 0 = (Real.pi : ℂ) ^ 2 := rfl

@[simp] theorem realAnchorCore_one :
    realAnchorCore 1 = Complex.exp (1 : ℂ) := rfl

theorem realAnchorField_eq_adjoin_realAnchorCore :
    realAnchorField = IntermediateField.adjoin ℚ (Set.range realAnchorCore) := by
  rw [realAnchorField_eq_adjoin_exp_one_pi_sq]
  congr 1
  ext x
  constructor
  · intro hx
    rcases hx with (rfl | hx)
    · exact ⟨1, rfl⟩
    · simp only [Set.mem_singleton_iff] at hx
      subst x
      exact ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i
    · exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))
    · exact Set.mem_insert_iff.mpr (Or.inl rfl)

def liftedRealAnchorCore : Fin 2 → realAnchorField := fun i ↦
  ⟨realAnchorCore i, by
    rw [realAnchorField_eq_adjoin_realAnchorCore]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

@[simp] theorem coe_liftedRealAnchorCore (i : Fin 2) :
    (liftedRealAnchorCore i : ℂ) = realAnchorCore i := rfl

theorem image_val_range_liftedRealAnchorCore :
    Subtype.val '' Set.range liftedRealAnchorCore = Set.range realAnchorCore := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨liftedRealAnchorCore i, ⟨i, rfl⟩, rfl⟩

theorem fieldRange_realAnchorField_val :
    realAnchorField.val.fieldRange = realAnchorField := by
  ext x
  constructor
  · rintro ⟨y, rfl⟩
    exact y.2
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩

theorem adjoin_range_liftedRealAnchorCore_eq_top :
    IntermediateField.adjoin ℚ (Set.range liftedRealAnchorCore) = ⊤ := by
  apply IntermediateField.map_injective realAnchorField.val
  calc
    IntermediateField.map realAnchorField.val
        (IntermediateField.adjoin ℚ (Set.range liftedRealAnchorCore)) =
        IntermediateField.adjoin ℚ
          (realAnchorField.val '' Set.range liftedRealAnchorCore) :=
      IntermediateField.adjoin_map ℚ (Set.range liftedRealAnchorCore)
        realAnchorField.val
    _ = IntermediateField.adjoin ℚ (Set.range realAnchorCore) := by
      rw [show realAnchorField.val '' Set.range liftedRealAnchorCore =
          Subtype.val '' Set.range liftedRealAnchorCore by rfl]
      rw [image_val_range_liftedRealAnchorCore]
    _ = realAnchorField := realAnchorField_eq_adjoin_realAnchorCore.symm
    _ = realAnchorField.val.fieldRange := fieldRange_realAnchorField_val.symm
    _ = IntermediateField.map realAnchorField.val ⊤ :=
      AlgHom.fieldRange_eq_map realAnchorField.val

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isAlgebraic_adjoin_range_liftedRealAnchorCore :
    Algebra.IsAlgebraic
      (Algebra.adjoin ℚ (Set.range liftedRealAnchorCore)) realAnchorField := by
  let f :
      IntermediateField.adjoin ℚ (Set.range liftedRealAnchorCore) →ₐ[
        Algebra.adjoin ℚ (Set.range liftedRealAnchorCore)] realAnchorField :=
    IsScalarTower.toAlgHom _ _ _
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [adjoin_range_liftedRealAnchorCore_eq_top]
    exact IntermediateField.mem_top
  let e := AlgEquiv.ofBijective f ⟨f.injective, hf_surj⟩
  exact e.isAlgebraic

/-- The real anchor field has maximal possible transcendence degree exactly when its explicit
generators `(pi^2, e)` are algebraically independent. -/
theorem trdeg_realAnchorField_eq_two_iff_algebraicIndependent :
    Algebra.trdeg ℚ realAnchorField = (2 : Cardinal) ↔
      AlgebraicIndependent ℚ realAnchorCore := by
  constructor
  · intro htd
    letI : Algebra.IsAlgebraic
        (Algebra.adjoin ℚ (Set.range liftedRealAnchorCore)) realAnchorField :=
      isAlgebraic_adjoin_range_liftedRealAnchorCore
    have htb : IsTranscendenceBasis ℚ liftedRealAnchorCore :=
      Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg ℚ liftedRealAnchorCore
        (by rw [htd]; exact Cardinal.natCast_lt_aleph0 (n := 2)) (by simp [htd])
    have hcomplex := htb.1.map' realAnchorField.val.injective
    simpa [Function.comp_def] using hcomplex
  · intro hcore
    have hlifted : AlgebraicIndependent ℚ liftedRealAnchorCore := by
      apply AlgebraicIndependent.of_comp realAnchorField.val
      simpa [Function.comp_def] using hcore
    apply le_antisymm trdeg_realAnchorField_le_two
    simpa using hlifted.cardinalMk_le_trdeg

/-- The Schanuel bound for the canonical anchor is exactly the assertion that the real field
`Q(e, pi^2)` has transcendence degree two. -/
theorem bound_canonicalAnchor_iff_trdeg_realAnchorField_eq_two :
    Bound canonicalAnchor ↔
      Algebra.trdeg ℚ realAnchorField = (2 : Cardinal) := by
  rw [Bound, trdeg_canonicalAnchor_eq_realAnchorField]
  constructor
  · intro h
    apply le_antisymm
    · exact trdeg_realAnchorField_le_two
    · simpa using h
  · intro h
    simp [h]

/-- The canonical-anchor instance of Schanuel is precisely algebraic independence of the
concrete pair `(pi^2, e)`. -/
theorem bound_canonicalAnchor_iff_algebraicIndependent_realAnchorCore :
    Bound canonicalAnchor ↔ AlgebraicIndependent ℚ realAnchorCore :=
  bound_canonicalAnchor_iff_trdeg_realAnchorField_eq_two.trans
    trdeg_realAnchorField_eq_two_iff_algebraicIndependent

/-- Squaring the period and passing to the entirely real pair loses no algebraic-independence
information: `(pi^2, e)` is independent exactly when `(2*pi*I, e)` is. -/
theorem algebraicIndependent_realAnchorCore_iff_period_exp_one :
    AlgebraicIndependent ℚ realAnchorCore ↔
      AlgebraicIndependent ℚ CanonicalAnchorRelativeTerminal.core := by
  constructor
  · intro hreal
    apply CanonicalAnchorRelativeTerminal.trdeg_canonicalAnchor_eq_two_iff_algebraicIndependent.mp
    rw [trdeg_canonicalAnchor_eq_realAnchorField]
    exact trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hreal
  · intro hperiod
    apply trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mp
    rw [← trdeg_canonicalAnchor_eq_realAnchorField]
    exact CanonicalAnchorRelativeTerminal.trdeg_canonicalAnchor_eq_two_iff_algebraicIndependent.mpr
      hperiod

/-- The real anchor field has exactly one or two transcendence degrees. -/
theorem trdeg_realAnchorField_eq_one_or_two :
    Algebra.trdeg ℚ realAnchorField = (1 : Cardinal) ∨
      Algebra.trdeg ℚ realAnchorField = (2 : Cardinal) := by
  rcases CanonicalAnchorRelativeTerminal.trdeg_canonicalAnchor_eq_one_or_two with h | h
  · exact Or.inl (trdeg_canonicalAnchor_eq_realAnchorField ▸ h)
  · exact Or.inr (trdeg_canonicalAnchor_eq_realAnchorField ▸ h)

/-- The degree-one real-anchor boundary is exactly algebraic dependence of `(pi^2, e)`. -/
theorem trdeg_realAnchorField_eq_one_iff_not_algebraicIndependent :
    Algebra.trdeg ℚ realAnchorField = (1 : Cardinal) ↔
      ¬ AlgebraicIndependent ℚ realAnchorCore := by
  constructor
  · intro htd hcore
    have htwo :=
      trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore
    rw [htd] at htwo
    norm_num at htwo
  · intro hcore
    rcases trdeg_realAnchorField_eq_one_or_two with h | h
    · exact h
    · exact False.elim (hcore
        (trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mp h))

/-- The stable terminal dichotomy with its zero-complement branch written entirely inside the
real field `Q(e, pi^2)`. -/
def RealConjugationStableTerminalDichotomy : Prop :=
  Algebra.trdeg ℚ realAnchorField = (1 : Cardinal) ∨
    ∃ (n : ℕ) (w : Fin (n + 3) → ℂ), PositiveConjugationStableTerminalWitness w

/-- A failure of Schanuel is equivalently either the degree-one real anchor boundary or a
positive stable terminal witness. -/
theorem not_conjecture_iff_realConjugationStableTerminalDichotomy :
    ¬ Conjecture ↔ RealConjugationStableTerminalDichotomy := by
  rw [not_conjecture_iff_conjugationStableTerminalDichotomy]
  unfold ConjugationStableTerminalDichotomy RealConjugationStableTerminalDichotomy
  rw [trdeg_canonicalAnchor_eq_realAnchorField]

/-- A failure of Schanuel is equivalently either algebraic dependence of the concrete pair
`(pi^2, e)` or a positive conjugation-stable terminal witness. -/
theorem not_conjecture_iff_realAnchorCore_dependent_or_positiveTerminal :
    ¬ Conjecture ↔
      (¬ AlgebraicIndependent ℚ realAnchorCore) ∨
        ∃ (n : ℕ) (w : Fin (n + 3) → ℂ), PositiveConjugationStableTerminalWitness w := by
  rw [not_conjecture_iff_realConjugationStableTerminalDichotomy]
  unfold RealConjugationStableTerminalDichotomy
  rw [trdeg_realAnchorField_eq_one_iff_not_algebraicIndependent]

/-- A positive least stable failure retains the minimality hypothesis needed to apply Schanuel
to every proper stable anchored sector subspace. -/
def PositiveLeastConjugationStableFailure {n : ℕ}
    (w : Fin (n + 2) → ℂ) : Prop :=
  0 < n ∧ LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧ ConjugationStable w ∧
    ¬ Bound w ∧
    ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k

/-- Every positive least stable failure has exact defect one. -/
theorem PositiveLeastConjugationStableFailure.defectOne
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (H : PositiveLeastConjugationStableFailure w) : DefectOne w := by
  rcases H with ⟨-, hwlin, hwanchor, hwstable, hwfail, hmin⟩
  exact defectOne_of_no_smaller_conjugationStableCanonicalAnchored_failure
    hwlin hwanchor hwstable hwfail hmin

/-- A positive least stable failure carries the sharp scaled terminal-deletion field. -/
theorem PositiveLeastConjugationStableFailure.nonempty_stableTerminalDeletionData
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (H : PositiveLeastConjugationStableFailure w) :
    Nonempty (StableTerminalDeletionData w) := by
  rcases H with ⟨hn, hwlin, hwanchor, hwstable, hwfail, hmin⟩
  exact exists_stableTerminalDeletionData_of_least_failure
    hwlin hwanchor hwstable hwfail hmin hn

/-- Global failure terminates either at dependence of `(pi^2, e)` or at a positive least stable
failure carrying the proper-subspace minimality needed by the sector endpoint. -/
theorem not_conjecture_iff_realAnchorCore_dependent_or_positiveLeastStableFailure :
    ¬ Conjecture ↔
      (¬ AlgebraicIndependent ℚ realAnchorCore) ∨
        ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
          PositiveLeastConjugationStableFailure w := by
  constructor
  · intro hnot
    obtain ⟨n, ⟨w, hwlin, hwanchor, hwstable, hwfail⟩, hmin⟩ :=
      exists_first_conjugationStableCanonicalAnchored_failure hnot
    by_cases hn : n = 0
    · subst n
      apply Or.inl
      intro hcore
      apply hwfail
      have hw : w = canonicalAnchor := by
        funext i
        fin_cases i
        · exact hwanchor.1
        · exact hwanchor.2
      rw [hw]
      exact bound_canonicalAnchor_iff_algebraicIndependent_realAnchorCore.mpr hcore
    · exact Or.inr ⟨n, w, Nat.pos_of_ne_zero hn, hwlin, hwanchor, hwstable,
        hwfail, hmin⟩
  · rintro (hcore | ⟨n, w, -, hwlin, -, -, hwfail, -⟩)
    · exact not_conjecture_iff_realAnchorCore_dependent_or_positiveTerminal.mpr
        (Or.inl hcore)
    · intro hC
      exact hwfail (hC (n + 2) w hwlin)

/-- Conjugation commutes with appending two finite families. -/
theorem conjugateFamily_append {m n : ℕ} (u : Fin m → ℂ) (v : Fin n → ℂ) :
    conjugateFamily (Fin.append u v) =
      Fin.append (conjugateFamily u) (conjugateFamily v) := by
  ext i
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i <;>
    simp [conjugateFamily]

/-- Appending conjugation-stable finite families preserves conjugation stability. -/
theorem conjugationStable_append {m n : ℕ} {u : Fin m → ℂ} {v : Fin n → ℂ}
    (hu : ConjugationStable u) (hv : ConjugationStable v) :
    ConjugationStable (Fin.append u v) := by
  unfold ConjugationStable at hu hv ⊢
  rw [conjugateFamily_append, span_append, span_append, hu, hv]

/-- Reindexing a finite family by an equivalence between possibly differently presented finite
index types preserves its generated field exactly. -/
theorem generatedField_comp_finEquiv {m n : ℕ} (z : Fin n → ℂ)
    (e : Fin m ≃ Fin n) : generatedField (z ∘ e) = generatedField z := by
  rw [generatedField, generators, e.surjective.range_comp]
  have hexp : (fun i ↦ Complex.exp ((z ∘ e) i)) =
      (fun i ↦ Complex.exp (z i)) ∘ e := rfl
  rw [hexp, e.surjective.range_comp]
  rfl

/-- The explicit even anti-fixed core is invariant under reindexing by an equivalence. -/
theorem antiFixedEvenCore_comp_finEquiv {m n : ℕ} (u : Fin (n + 1) → ℂ)
    (e : Fin (m + 1) ≃ Fin (n + 1)) :
    antiFixedEvenCore (u ∘ e) = antiFixedEvenCore u := by
  unfold antiFixedEvenCore
  rw [show (fun i ↦ (u ∘ e) i / standardPeriod) =
      (fun i ↦ u i / standardPeriod) ∘ e by rfl,
    e.surjective.range_comp]
  rw [show (fun i ↦ Complex.exp ((u ∘ e) i) +
      (Complex.exp ((u ∘ e) i))⁻¹) =
      (fun i ↦ Complex.exp (u i) + (Complex.exp (u i))⁻¹) ∘ e by rfl,
    e.surjective.range_comp]

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

/-- Every distinguished minus-sector basis vector is anti-fixed after coercion to `ℂ`. -/
theorem SectorBasisData.minusBasis_antiFixed
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) (i) :
    star ((R.subtype ∘ D.minusBasis) i) = -((R.subtype ∘ D.minusBasis) i) := by
  have hmem : D.minusBasis i ∈ minusSector R hR := by
    rw [← D.minusSpan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have heq := (mem_minusSector_iff R hR (D.minusBasis i)).mp hmem
  have hcoe := congrArg ((↑) : R → ℂ) heq
  simpa [restrictedConjugation_apply] using hcoe

/-- Every distinguished plus-sector basis vector is fixed after coercion to `ℂ`. -/
theorem SectorBasisData.plusBasis_fixed
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) (i) :
    star ((R.subtype ∘ D.plusBasis) i) = (R.subtype ∘ D.plusBasis) i := by
  have hmem : D.plusBasis i ∈ plusSector R hR := by
    rw [← D.plusSpan]
    exact Submodule.subset_span (Set.mem_range_self i)
  have heq := (mem_plusSector_iff R hR (D.plusBasis i)).mp hmem
  have hcoe := congrArg ((↑) : R → ℂ) heq
  simpa [restrictedConjugation_apply] using hcoe

/-- The distinguished plus-sector graph field is pointwise fixed by conjugation. -/
theorem SectorBasisData.generatedField_plusBasis_le_conjugationFixedField
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    generatedField (R.subtype ∘ D.plusBasis) ≤ conjugationFixedField :=
  generatedField_le_conjugationFixedField_of_fixed _ D.plusBasis_fixed

/-- The explicit core of the distinguished minus-sector basis is pointwise fixed by
conjugation. -/
theorem SectorBasisData.minusRealCore_le_conjugationFixedField
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    antiFixedRealCore (R.subtype ∘ D.minusBasis) ≤ conjugationFixedField :=
  antiFixedRealCore_le_conjugationFixedField _ D.minusBasis_antiFixed

/-- The smaller even core of the distinguished minus-sector basis is pointwise fixed by
conjugation. -/
theorem SectorBasisData.minusEvenCore_le_conjugationFixedField
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    antiFixedEvenCore (R.subtype ∘ D.minusBasis) ≤ conjugationFixedField :=
  antiFixedEvenCore_le_conjugationFixedField _ D.minusBasis_antiFixed

/-- The anti-fixed basis normalized by the standard imaginary period.  Its zeroth entry is `1`,
and its remaining entries are the real angular parameters visible in the even core. -/
def SectorBasisData.normalizedMinusBasis
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Fin (D.minusComplementCount + 1) → ℂ :=
  fun i ↦ R.subtype (D.minusBasis i) / standardPeriod

/-- Dividing the distinguished anti-fixed basis by the nonzero standard period preserves rational
linear independence. -/
theorem SectorBasisData.normalizedMinusBasis_linearIndependent
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    LinearIndependent ℚ D.normalizedMinusBasis := by
  have hu : LinearIndependent ℚ (R.subtype ∘ D.minusBasis) :=
    D.minusLinearIndependent.map' R.subtype (Submodule.ker_subtype R)
  let f : ℂ →ₗ[ℚ] ℂ := LinearMap.mulLeft ℚ standardPeriod⁻¹
  have hf : LinearMap.ker f = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    change standardPeriod⁻¹ * x = 0 at hx
    exact (mul_eq_zero.mp hx).resolve_left
      (inv_ne_zero FullyTranscendentalPeriodBoundary.period_ne_zero)
  have hscaled := hu.map' f hf
  have heq : D.normalizedMinusBasis = f ∘ (R.subtype ∘ D.minusBasis) := by
    funext i
    simp only [normalizedMinusBasis, f, Function.comp_apply, LinearMap.mulLeft_apply,
      div_eq_mul_inv, mul_comm]
  rw [heq]
  exact hscaled

@[simp]
theorem SectorBasisData.normalizedMinusBasis_zero
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    D.normalizedMinusBasis 0 = 1 := by
  have hu0 : R.subtype (D.minusBasis 0) = standardPeriod := by
    simpa using congrArg ((↑) : R → ℂ) D.minus_zero
  simp [normalizedMinusBasis, hu0, FullyTranscendentalPeriodBoundary.period_ne_zero]

/-- Every normalized anti-fixed basis vector belongs to the smaller even core. -/
theorem SectorBasisData.normalizedMinusBasis_mem_evenCore
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) (i) :
    D.normalizedMinusBasis i ∈
      antiFixedEvenCore (R.subtype ∘ D.minusBasis) := by
  exact ratio_mem_antiFixedEvenCore (R.subtype ∘ D.minusBasis) i

/-- The graph field of the distinguished anti-fixed basis is reconstructed exactly from its
explicit real core and the standard period. -/
theorem SectorBasisData.generatedField_minusBasis_eq_realCore_adjoin_period
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    generatedField (R.subtype ∘ D.minusBasis) =
      antiFixedRealCore (R.subtype ∘ D.minusBasis) ⊔
        IntermediateField.adjoin ℚ ({standardPeriod} : Set ℂ) := by
  apply generatedField_eq_antiFixedRealCore_adjoin_period
  simpa using congrArg ((↑) : R → ℂ) D.minus_zero

/-- The distinguished anti-fixed graph field has exactly the transcendence degree of its
explicit pointwise-real core. -/
theorem SectorBasisData.trdeg_minusBasis_eq_realCore
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.minusBasis)) =
      Algebra.trdeg ℚ (antiFixedRealCore (R.subtype ∘ D.minusBasis)) := by
  apply trdeg_generatedField_eq_antiFixedRealCore
  simpa using congrArg ((↑) : R → ℂ) D.minus_zero

/-- The distinguished anti-fixed graph field has exactly the transcendence degree of the smaller
even core generated by the squared period, normalized inputs, and exponential traces. -/
theorem SectorBasisData.trdeg_minusBasis_eq_evenCore
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.minusBasis)) =
      Algebra.trdeg ℚ (antiFixedEvenCore (R.subtype ∘ D.minusBasis)) :=
  D.trdeg_minusBasis_eq_realCore.trans
    (trdeg_antiFixedRealCore_eq_evenCore (R.subtype ∘ D.minusBasis))

/-- The real-sector basis followed by the standard imaginary period. -/
def SectorBasisData.plusWithPeriod
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Fin ((D.plusComplementCount + 1) + 1) → ℂ :=
  Fin.append (R.subtype ∘ D.plusBasis) (fun _ ↦ standardPeriod)

/-- The real unit followed by the anti-fixed-sector basis. -/
def SectorBasisData.oneWithMinus
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Fin (1 + (D.minusComplementCount + 1)) → ℂ :=
  Fin.append (fun _ ↦ (1 : ℂ)) (R.subtype ∘ D.minusBasis)

theorem SectorBasisData.generatedField_plusWithPeriod
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    generatedField D.plusWithPeriod =
      generatedField (R.subtype ∘ D.plusBasis) ⊔
        generatedField (fun _ : Fin 1 ↦ standardPeriod) := by
  exact generatedField_append (R.subtype ∘ D.plusBasis)
    (fun _ : Fin 1 ↦ standardPeriod)

theorem SectorBasisData.generatedField_oneWithMinus
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    generatedField D.oneWithMinus =
      generatedField (fun _ : Fin 1 ↦ (1 : ℂ)) ⊔
        generatedField (R.subtype ∘ D.minusBasis) := by
  exact generatedField_append (fun _ : Fin 1 ↦ (1 : ℂ))
    (R.subtype ∘ D.minusBasis)

/-- If the fixed sector has no direction beyond `1`, its graph field is literally `Q(e)`. -/
theorem SectorBasisData.generatedField_plusBasis_eq_oneSingleton_of_eq_zero
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hp : D.plusComplementCount = 0) :
    generatedField (R.subtype ∘ D.plusBasis) =
      generatedField (fun _ : Fin 1 ↦ (1 : ℂ)) := by
  let e : Fin (D.plusComplementCount + 1) ≃ Fin 1 :=
    finCongr (by omega)
  have hfamily : R.subtype ∘ D.plusBasis =
      (fun _ : Fin 1 ↦ (1 : ℂ)) ∘ e := by
    funext i
    have hi : i = 0 := by
      apply Fin.ext
      omega
    subst i
    simpa using congrArg ((↑) : R → ℂ) D.plus_zero
  rw [hfamily, generatedField_comp_finEquiv]

/-- If the anti-fixed sector has no direction beyond the period, its even core is literally
`Q(pi^2)`. -/
theorem SectorBasisData.minusEvenCore_eq_adjoin_pi_sq_of_eq_zero
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hq : D.minusComplementCount = 0) :
    antiFixedEvenCore (R.subtype ∘ D.minusBasis) =
      IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ) := by
  let e : Fin (D.minusComplementCount + 1) ≃ Fin 1 :=
    finCongr (by omega)
  have hfamily : R.subtype ∘ D.minusBasis =
      (fun _ : Fin 1 ↦ standardPeriod) ∘ e := by
    funext i
    have hi : i = 0 := by
      apply Fin.ext
      omega
    subst i
    simpa using congrArg ((↑) : R → ℂ) D.minus_zero
  rw [hfamily, antiFixedEvenCore_comp_finEquiv]
  exact antiFixedEvenCore_fin1_eq_adjoin_pi_sq
    (fun _ : Fin 1 ↦ standardPeriod) rfl

/-- A singleton fixed sector has graph-field transcendence degree exactly one. -/
theorem SectorBasisData.plusBasis_trdeg_eq_one_of_eq_zero
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hp : D.plusComplementCount = 0) :
    Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis)) = 1 := by
  rw [D.generatedField_plusBasis_eq_oneSingleton_of_eq_zero hp]
  exact trdeg_generatedField_oneSingleton_eq_one

/-- A singleton anti-fixed sector has even-core transcendence degree exactly one. -/
theorem SectorBasisData.minusEvenCore_trdeg_eq_one_of_eq_zero
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hq : D.minusComplementCount = 0) :
    Algebra.trdeg ℚ (antiFixedEvenCore (R.subtype ∘ D.minusBasis)) = 1 := by
  rw [D.minusEvenCore_eq_adjoin_pi_sq_of_eq_zero hq,
    ← cRk_eq_trdeg_adjoin]
  exact cRk_pi_sq_singleton_eq_one

/-- Every distinguished fixed- or anti-fixed-sector input, together with its exponential, is
algebraic over the sharp scaled terminal-deletion field.  This links the terminal tower directly
to the explicit real/imaginary sector variables rather than only to one omitted original
coordinate. -/
theorem StableTerminalDeletionData.sectorBasis_pairs_isAlgebraic
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (T : StableTerminalDeletionData w)
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hwspan : Submodule.span ℚ (Set.range w) = R) :
    (∀ i,
      IsAlgebraic (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
          (R.subtype (D.plusBasis i)) ∧
        IsAlgebraic (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
          (Complex.exp (R.subtype (D.plusBasis i)))) ∧
      ∀ i,
      IsAlgebraic (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
          (R.subtype (D.minusBasis i)) ∧
        IsAlgebraic (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
          (Complex.exp (R.subtype (D.minusBasis i))) := by
  constructor
  · intro i
    apply T.span_pair_isAlgebraic
    rw [hwspan]
    exact (D.plusBasis i).2
  · intro i
    apply T.span_pair_isAlgebraic
    rw [hwspan]
    exact (D.minusBasis i).2

/-- All displayed generators of the minimal even anti-fixed core are algebraic over the same
sharp terminal-deletion field: the squared period, normalized imaginary inputs, and cosine
traces. -/
theorem StableTerminalDeletionData.evenCore_generators_isAlgebraic
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (T : StableTerminalDeletionData w)
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hwspan : Submodule.span ℚ (Set.range w) = R) :
    IsAlgebraic (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
        (standardPeriod ^ 2) ∧
      (∀ i, IsAlgebraic
        (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
        (D.normalizedMinusBasis i)) ∧
      ∀ i, IsAlgebraic
        (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
        (Complex.exp ((R.subtype ∘ D.minusBasis) i) +
          (Complex.exp ((R.subtype ∘ D.minusBasis) i))⁻¹) := by
  have hpairs := StableTerminalDeletionData.sectorBasis_pairs_isAlgebraic
    T D hwspan
  have hperiod : IsAlgebraic
      (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
      standardPeriod := by
    have heq : R.subtype (D.minusBasis 0) = standardPeriod := by
      simpa using congrArg ((↑) : R → ℂ) D.minus_zero
    rw [← heq]
    exact (hpairs.2 (0 : Fin (D.minusComplementCount + 1))).1
  refine ⟨hperiod.pow 2, ?_, ?_⟩
  · intro i
    have hu := (hpairs.2 i).1
    simpa [SectorBasisData.normalizedMinusBasis, div_eq_mul_inv] using
      hu.mul hperiod.inv
  · intro i
    have hy := (hpairs.2 i).2
    exact hy.add hy.inv

/-- The sharp scaled terminal-deletion field literally contains the standard period.  The two
anchored deletion coordinates remain anchored after the common scale, and their difference is
the scale times the period. -/
theorem StableTerminalDeletionData.standardPeriod_mem_scaledDeletionField
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    standardPeriod ∈ generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) := by
  let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
  have hzero : ratScaleFamily (T.scale : ℚ) T.deletion 0 ∈ K :=
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)
  have hone : ratScaleFamily (T.scale : ℚ) T.deletion 1 ∈ K :=
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨1, rfl⟩)
  have hsub := K.sub_mem hone hzero
  have hscale : ((T.scale : ℚ) : ℂ) ∈ K :=
    IntermediateField.algebraMap_mem _ (T.scale : ℚ)
  have hdiv := K.div_mem hsub hscale
  have hscale_ne : ((T.scale : ℚ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt T.scale_pos)
  convert hdiv using 1
  simp only [ratScaleFamily, T.deletionAnchored.1,
    T.deletionAnchored.2, canonicalAnchor_zero, canonicalAnchor_one]
  field_simp
  ring

/-- Consequently the sharp scaled deletion field literally contains `pi^2`. -/
theorem StableTerminalDeletionData.pi_sq_mem_scaledDeletionField
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    (Real.pi : ℂ) ^ 2 ∈
      generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) := by
  let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
  have hperiod : standardPeriod ∈ K :=
    StableTerminalDeletionData.standardPeriod_mem_scaledDeletionField T
  have hsq := K.pow_mem hperiod 2
  have hc : (-(1 / 4 : ℚ) : ℂ) ∈ K :=
    by simp
  have hmul := K.mul_mem hc hsq
  convert hmul using 1
  calc
    (Real.pi : ℂ) ^ 2 =
        (-(1 / 4 : ℚ) : ℂ) * (-4 * (Real.pi : ℂ) ^ 2) := by
      norm_num
      ring
    _ = (-(1 / 4 : ℚ) : ℂ) * standardPeriod ^ 2 := by
      rw [standardPeriod_sq_eq_neg_four_pi_sq]

/-- The other real-anchor generator `e` is integral over the sharp scaled deletion field. -/
theorem StableTerminalDeletionData.exp_one_isIntegral_scaledDeletionField
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    IsIntegral (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
      (Complex.exp (1 : ℂ)) := by
  have hscaleQ : (0 : ℚ) < T.scale := by exact_mod_cast T.scale_pos
  have h := exp_isIntegral_over_ratScale
    (T.scale : ℚ) hscaleQ T.deletion (0 : Fin (T.complementCount + 2))
  have hexp : Complex.exp (T.deletion 0) = Complex.exp (1 : ℂ) := by
    rw [T.deletionAnchored.1, canonicalAnchor_zero, Complex.exp_add,
      exp_standardPeriod]
    simp
  rwa [hexp] at h

/-- Because `pi^2` already belongs to the scaled deletion field, adjoining the entire real
anchor is exactly the same as adjoining the single element `e`. -/
theorem StableTerminalDeletionData.sup_realAnchorField_eq_adjoin_exp_one
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔ realAnchorField =
      (IntermediateField.adjoin
        (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
        ({Complex.exp (1 : ℂ)} : Set ℂ)).restrictScalars ℚ := by
  let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
  let E := IntermediateField.adjoin ℚ ({Complex.exp (1 : ℂ)} : Set ℂ)
  let P := IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ)
  have hP : P ≤ K := by
    change IntermediateField.adjoin ℚ ({(Real.pi : ℂ) ^ 2} : Set ℂ) ≤ K
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact StableTerminalDeletionData.pi_sq_mem_scaledDeletionField T
  have hsup : K ⊔ realAnchorField = K ⊔ E := by
    rw [realAnchorField_eq_exp_one_sup_pi_sq]
    change K ⊔ (E ⊔ P) = K ⊔ E
    apply le_antisymm
    · apply sup_le
      · exact (show K ≤ K ⊔ E from le_sup_left)
      · apply sup_le
        · exact (show E ≤ K ⊔ E from le_sup_right)
        · exact hP.trans (show K ≤ K ⊔ E from le_sup_left)
    · apply sup_le
      · exact (show K ≤ K ⊔ (E ⊔ P) from le_sup_left)
      · exact (show E ≤ E ⊔ P from le_sup_left).trans
          (show E ⊔ P ≤ K ⊔ (E ⊔ P) from le_sup_right)
  calc
    K ⊔ realAnchorField = K ⊔ E := hsup
    _ = (IntermediateField.adjoin K
        ({Complex.exp (1 : ℂ)} : Set ℂ)).restrictScalars ℚ :=
      (IntermediateField.restrictScalars_adjoin_eq_sup ℚ K _).symm

/-- The finite Kummer step needed to absorb the real anchor has degree at most the positive
integer scaling denominator.  This is quantitative: `e` satisfies a power polynomial over the
scaled deletion field of precisely that displayed degree. -/
theorem StableTerminalDeletionData.finrank_adjoin_exp_one_le_scale
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    Module.finrank
        (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
        (IntermediateField.adjoin
          (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
          ({Complex.exp (1 : ℂ)} : Set ℂ)) ≤ T.scale.toNat := by
  let a : ℚ := T.scale
  let K := generatedField (ratScaleFamily a T.deletion)
  let e : ℂ := Complex.exp (1 : ℂ)
  change Module.finrank K
      (IntermediateField.adjoin K ({e} : Set ℂ)) ≤ T.scale.toNat
  have ha : (0 : ℚ) < a := by
    change (0 : ℚ) < (T.scale : ℚ)
    exact_mod_cast T.scale_pos
  have hscaledexp : Complex.exp ((a : ℂ) * T.deletion 0) ∈ K :=
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨0, rfl⟩)
  have hpowscaled : Complex.exp ((a : ℂ) * T.deletion 0) ^ a.den ∈ K :=
    K.pow_mem hscaledexp a.den
  have hpow : Complex.exp (T.deletion 0) ^ a.num.toNat ∈ K := by
    rw [exp_pow_num_eq_exp_rat_mul_pow a ha]
    exact hpowscaled
  have hexp : Complex.exp (T.deletion 0) = e := by
    rw [T.deletionAnchored.1, canonicalAnchor_zero, Complex.exp_add,
      exp_standardPeriod]
    simp [e]
  have hepow : e ^ a.num.toNat ∈ K := by
    rw [← hexp]
    exact hpow
  let c : K := ⟨e ^ a.num.toNat, hepow⟩
  let p : Polynomial K := Polynomial.X ^ a.num.toNat - Polynomial.C c
  have hmpos : 0 < a.num.toNat := rat_num_toNat_pos ha
  have hpmonic : p.Monic :=
    Polynomial.monic_X_pow_sub_C c hmpos.ne'
  have hpeval : Polynomial.aeval e p = 0 := by
    simp [p, c]
  have hint : IsIntegral K e :=
    StableTerminalDeletionData.exp_one_isIntegral_scaledDeletionField T
  have hdvd : minpoly K e ∣ p := minpoly.dvd K e hpeval
  calc
    Module.finrank K (IntermediateField.adjoin K ({e} : Set ℂ)) =
        (minpoly K e).natDegree := IntermediateField.adjoin.finrank hint
    _ ≤ p.natDegree := Polynomial.natDegree_le_of_dvd hdvd hpmonic.ne_zero
    _ = a.num.toNat := Polynomial.natDegree_X_pow_sub_C
    _ = T.scale.toNat := by simp [a]

/-- Both entries of the explicit real anchor tuple `(pi^2, e)` are algebraic over every sharp
positive terminal-deletion field. -/
theorem StableTerminalDeletionData.realAnchorCore_isAlgebraic
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    ∀ i, IsAlgebraic
      (generatedField (ratScaleFamily (T.scale : ℚ) T.deletion))
      (realAnchorCore i) := by
  intro i
  fin_cases i
  · exact (isIntegral_of_mem_intermediateField _
      (StableTerminalDeletionData.pi_sq_mem_scaledDeletionField T)).isAlgebraic
  · exact (StableTerminalDeletionData.exp_one_isIntegral_scaledDeletionField T).isAlgebraic

/-- Adjoining the real anchor to the sharp scaled deletion field does not change its absolute
transcendence degree.  This packages the literal containment of `pi^2` and algebraicity of `e`
into an exact compositum statement. -/
theorem StableTerminalDeletionData.trdeg_sup_realAnchorField_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    Algebra.trdeg ℚ
        (↥(generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔
          realAnchorField)) =
      (((T.complementCount + 2 : ℕ) : Cardinal)) := by
  let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
  let L : IntermediateField K ℂ :=
    IntermediateField.adjoin K (Set.range realAnchorCore)
  letI : Algebra.IsAlgebraic K L := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    exact (StableTerminalDeletionData.realAnchorCore_isAlgebraic T i).isIntegral
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have htower : Algebra.trdeg ℚ K + Algebra.trdeg K L = Algebra.trdeg ℚ L :=
    trdeg_add_eq ℚ K
  have hrel : Algebra.trdeg K L = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at htower
  have hL : L.restrictScalars ℚ = K ⊔ realAnchorField := by
    calc
      L.restrictScalars ℚ =
          K ⊔ IntermediateField.adjoin ℚ (Set.range realAnchorCore) :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ K _
      _ = K ⊔ realAnchorField := by
        rw [← realAnchorField_eq_adjoin_realAnchorCore]
  have heq := (IntermediateField.equivOfEq hL).trdeg_eq
  exact (heq.symm.trans htower.symm).trans
    (ConjugationStableTerminal.scaledDeletionSharp T)

/-- If the explicit real anchor pair is algebraically independent, the sharp terminal deletion
field has relative transcendence degree exactly equal to its number of complementary inputs over
the real anchor field. -/
theorem StableTerminalDeletionData.relative_trdeg_realAnchor_compositum_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    let M := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔
      realAnchorField
    letI : Algebra realAnchorField M :=
      (IntermediateField.inclusion
        (show realAnchorField ≤ M from le_sup_right)).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField M = ((T.complementCount : ℕ) : Cardinal) := by
  let M := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔
    realAnchorField
  letI : Algebra realAnchorField M :=
    (IntermediateField.inclusion
      (show realAnchorField ≤ M from le_sup_right)).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField M := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ realAnchorField (A := M)
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    StableTerminalDeletionData.trdeg_sup_realAnchorField_eq T] at hadd
  have hcancel : Algebra.trdeg realAnchorField M + 2 =
      (T.complementCount : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField M + 2 =
          2 + Algebra.trdeg realAnchorField M := add_comm _ _
      _ = (((T.complementCount + 2 : ℕ) : Cardinal)) := hadd
      _ = (T.complementCount : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- The entirely real anchor field is literally contained in the graph field of every
canonically anchored family.  The period is the difference of the two anchored inputs, while
`e` is their common exponential. -/
theorem realAnchorField_le_generatedField_of_canonicallyAnchored
    {n : ℕ} {w : Fin (n + 2) → ℂ} (hanchor : CanonicallyAnchored w) :
    realAnchorField ≤ generatedField w := by
  rw [realAnchorField_eq_adjoin_realAnchorCore,
    IntermediateField.adjoin_le_iff]
  intro x hx
  obtain ⟨i, rfl⟩ := hx
  have hzero : w 0 ∈ generatedField w :=
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)
  have hone : w 1 ∈ generatedField w :=
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨1, rfl⟩)
  have hperiod : standardPeriod ∈ generatedField w := by
    have hsub := (generatedField w).sub_mem hone hzero
    convert hsub using 1
    rw [hanchor.1, hanchor.2, canonicalAnchor_zero, canonicalAnchor_one]
    ring
  fin_cases i
  · have hsq := (generatedField w).pow_mem hperiod 2
    have hc : (-(1 / 4 : ℚ) : ℂ) ∈ generatedField w := by simp
    have hmul := (generatedField w).mul_mem hc hsq
    convert hmul using 1
    calc
      (Real.pi : ℂ) ^ 2 =
          (-(1 / 4 : ℚ) : ℂ) * (-4 * (Real.pi : ℂ) ^ 2) := by
        norm_num
        ring
      _ = (-(1 / 4 : ℚ) : ℂ) * standardPeriod ^ 2 := by
        rw [standardPeriod_sq_eq_neg_four_pi_sq]
  · have hexp : Complex.exp (w 0) ∈ generatedField w :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨0, rfl⟩)
    convert hexp using 1
    rw [hanchor.1, canonicalAnchor_zero, Complex.exp_add, exp_standardPeriod]
    simp

/-- Scale only the coordinates beyond the two canonical anchors.  Unlike uniform rational
scaling, this preserves the anchor literally. -/
def anchorPreservingScaleFamily {n : ℕ} (d : ℤ) (z : Fin (n + 2) → ℂ) :
    Fin (n + 2) → ℂ := fun i ↦
  if i = 0 ∨ i = 1 then z i else ((d : ℚ) • z i)

@[simp]
theorem anchorPreservingScaleFamily_zero {n : ℕ} (d : ℤ)
    (z : Fin (n + 2) → ℂ) :
    anchorPreservingScaleFamily d z 0 = z 0 := by
  simp [anchorPreservingScaleFamily]

@[simp]
theorem anchorPreservingScaleFamily_one {n : ℕ} (d : ℤ)
    (z : Fin (n + 2) → ℂ) :
    anchorPreservingScaleFamily d z 1 = z 1 := by
  simp [anchorPreservingScaleFamily]

/-- Anchor-preserving coordinate scaling preserves rational linear independence. -/
theorem anchorPreservingScaleFamily_linearIndependent
    {n : ℕ} {d : ℤ} (hd : d ≠ 0) {z : Fin (n + 2) → ℂ}
    (hz : LinearIndependent ℚ z) :
    LinearIndependent ℚ (anchorPreservingScaleFamily d z) := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  let c : Fin (n + 2) → ℚˣ := fun i ↦
    if i = 0 ∨ i = 1 then 1 else Units.mk0 (d : ℚ) hdQ
  have hfamily : anchorPreservingScaleFamily d z = c • z := by
    funext i
    by_cases hi : i = 0 ∨ i = 1
    · simp [anchorPreservingScaleFamily, c, hi]
    · simp [anchorPreservingScaleFamily, c, hi]
  rw [hfamily]
  exact hz.units_smul c

/-- Nonzero anchor-preserving coordinate scaling also preserves the rational input span. -/
theorem span_anchorPreservingScaleFamily_eq
    {n : ℕ} {d : ℤ} (hd : d ≠ 0) (z : Fin (n + 2) → ℂ) :
    Submodule.span ℚ (Set.range (anchorPreservingScaleFamily d z)) =
      Submodule.span ℚ (Set.range z) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0 ∨ i = 1
    · rw [anchorPreservingScaleFamily, if_pos hi]
      exact Submodule.subset_span (Set.mem_range_self i)
    · rw [anchorPreservingScaleFamily, if_neg hi]
      exact (Submodule.span ℚ (Set.range z)).smul_mem (d : ℚ)
        (Submodule.subset_span (Set.mem_range_self i))
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    by_cases hi : i = 0 ∨ i = 1
    · have hv : anchorPreservingScaleFamily d z i ∈
          Submodule.span ℚ (Set.range (anchorPreservingScaleFamily d z)) :=
        Submodule.subset_span (Set.mem_range_self i)
      simpa [anchorPreservingScaleFamily, hi] using hv
    · have hv : anchorPreservingScaleFamily d z i ∈
          Submodule.span ℚ (Set.range (anchorPreservingScaleFamily d z)) :=
        Submodule.subset_span (Set.mem_range_self i)
      have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
      have hscaled :=
        (Submodule.span ℚ (Set.range (anchorPreservingScaleFamily d z))).smul_mem
          ((d : ℚ)⁻¹) hv
      convert hscaled using 1
      rw [anchorPreservingScaleFamily, if_neg hi]
      simp [← smul_assoc, smul_eq_mul, hdQ]

/-- Anchor-preserving scaling preserves canonical anchoring. -/
theorem canonicallyAnchored_anchorPreservingScaleFamily
    {n : ℕ} (d : ℤ) {z : Fin (n + 2) → ℂ} (hz : CanonicallyAnchored z) :
    CanonicallyAnchored (anchorPreservingScaleFamily d z) := by
  exact ⟨by simp [hz.1], by simp [hz.2]⟩

/-- Positive integer scaling turns an exponential into the corresponding positive power. -/
theorem exp_int_scale_eq_pow {d : ℤ} (hd : 0 < d) (z : ℂ) :
    Complex.exp (((d : ℚ) : ℂ) * z) = Complex.exp z ^ d.toNat := by
  have hdQ : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
  simpa using (exp_pow_num_eq_exp_rat_mul_pow (d : ℚ) hdQ z).symm

@[simp]
theorem exp_anchorPreservingScaleFamily_zero
    {n : ℕ} (d : ℤ) {z : Fin (n + 2) → ℂ} (hz : CanonicallyAnchored z) :
    Complex.exp (anchorPreservingScaleFamily d z 0) = Complex.exp (1 : ℂ) := by
  rw [anchorPreservingScaleFamily_zero, hz.1, canonicalAnchor_zero,
    Complex.exp_add, exp_standardPeriod]
  simp

@[simp]
theorem exp_anchorPreservingScaleFamily_one
    {n : ℕ} (d : ℤ) {z : Fin (n + 2) → ℂ} (hz : CanonicallyAnchored z) :
    Complex.exp (anchorPreservingScaleFamily d z 1) = Complex.exp (1 : ℂ) := by
  rw [anchorPreservingScaleFamily_one, hz.2, canonicalAnchor_one,
    Complex.exp_add]
  have hperiod2 : Complex.exp (2 * standardPeriod) = 1 := by
    rw [show 2 * standardPeriod = standardPeriod + standardPeriod by ring,
      Complex.exp_add, exp_standardPeriod]
    norm_num
  rw [hperiod2]
  simp

/-- Anchor-preserving scaling by a nonzero integer preserves conjugation stability because it
preserves the rational input span. -/
theorem conjugationStable_anchorPreservingScaleFamily
    {n : ℕ} {d : ℤ} (hd : d ≠ 0) {z : Fin (n + 2) → ℂ}
    (hz : ConjugationStable z) :
    ConjugationStable (anchorPreservingScaleFamily d z) := by
  unfold ConjugationStable
  rw [← map_span_conjugation_eq,
    span_anchorPreservingScaleFamily_eq hd z,
    map_span_conjugation_eq, hz]

/-- Replacing uniform scaling by anchor-preserving scaling realizes the deletion--anchor
compositum as an honest exponential graph field.  The non-anchor coordinates remain scaled,
while the two anchor exponentials adjoin precisely the missing Kummer element `e`. -/
theorem StableTerminalDeletionData.generatedField_anchorPreservingScaleFamily_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w) :
    generatedField (anchorPreservingScaleFamily T.scale T.deletion) =
      generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔
        realAnchorField := by
  let v := anchorPreservingScaleFamily T.scale T.deletion
  let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
  let G := generatedField v
  have hd : T.scale ≠ 0 := ne_of_gt T.scale_pos
  have hdQ : (T.scale : ℚ) ≠ 0 := by exact_mod_cast hd
  have hvanchor : CanonicallyAnchored v :=
    canonicallyAnchored_anchorPreservingScaleFamily T.scale T.deletionAnchored
  have he : Complex.exp (1 : ℂ) ∈ realAnchorField := by
    rw [realAnchorField_eq_adjoin_realAnchorCore]
    exact IntermediateField.subset_adjoin ℚ _ ⟨1, rfl⟩
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · apply (show K ≤ K ⊔ realAnchorField from le_sup_left)
      by_cases hi : i = 0 ∨ i = 1
      · change anchorPreservingScaleFamily T.scale T.deletion i ∈ K
        rw [anchorPreservingScaleFamily, if_pos hi]
        exact mem_generatedField_ratScale_coordinate
          (T.scale : ℚ) hdQ T.deletion i
      · have hscaled : ratScaleFamily (T.scale : ℚ) T.deletion i ∈ K :=
          IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
        simpa [v, anchorPreservingScaleFamily, hi, ratScaleFamily,
          Rat.smul_def] using hscaled
    · by_cases hi : i = 0 ∨ i = 1
      · apply (show realAnchorField ≤ K ⊔ realAnchorField from le_sup_right)
        rcases hi with rfl | rfl
        · change Complex.exp
              (anchorPreservingScaleFamily T.scale T.deletion 0) ∈ realAnchorField
          rw [exp_anchorPreservingScaleFamily_zero T.scale T.deletionAnchored]
          exact he
        · change Complex.exp
              (anchorPreservingScaleFamily T.scale T.deletion 1) ∈ realAnchorField
          rw [exp_anchorPreservingScaleFamily_one T.scale T.deletionAnchored]
          exact he
      · apply (show K ≤ K ⊔ realAnchorField from le_sup_left)
        have hscaled :
            Complex.exp (ratScaleFamily (T.scale : ℚ) T.deletion i) ∈ K :=
          IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)
        simpa [v, anchorPreservingScaleFamily, hi, ratScaleFamily,
          Rat.smul_def] using hscaled
  · apply sup_le
    · rw [generatedField, IntermediateField.adjoin_le_iff]
      rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
      · by_cases hi : i = 0 ∨ i = 1
        · have hv : v i ∈ G :=
            IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
          have hmul : (T.scale : ℚ) • v i ∈ G := G.smul_mem hv
          simpa [v, anchorPreservingScaleFamily, hi, ratScaleFamily,
            Rat.smul_def] using hmul
        · have hv : v i ∈ G :=
            IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
          simpa [v, anchorPreservingScaleFamily, hi, ratScaleFamily,
            Rat.smul_def] using hv
      · by_cases hi : i = 0 ∨ i = 1
        · have hv : Complex.exp (v i) ∈ G :=
            IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)
          have hv' : Complex.exp (T.deletion i) ∈ G := by
            simpa only [v, anchorPreservingScaleFamily, if_pos hi] using hv
          change Complex.exp ((((T.scale : ℚ) : ℂ) * T.deletion i)) ∈ G
          rw [exp_int_scale_eq_pow T.scale_pos]
          exact G.pow_mem hv' T.scale.toNat
        · have hv : Complex.exp (v i) ∈ G :=
            IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)
          simpa [v, anchorPreservingScaleFamily, hi, ratScaleFamily,
            Rat.smul_def] using hv
    · exact realAnchorField_le_generatedField_of_canonicallyAnchored hvanchor

/-- Denominator-free form of the stable terminal deletion.  Its deletion remains literally
anchored, independent, and stable, while its graph field is now an actual subfield of the full
graph field and the latter is algebraic over it. -/
structure AnchorPreservingStableTerminalDeletionData {n : ℕ}
    (w : Fin (n + 2) → ℂ) where
  complementCount : ℕ
  deletion : Fin (complementCount + 2) → ℂ
  omitted : Fin (n + 2)
  deletionLinearIndependent : LinearIndependent ℚ deletion
  deletionAnchored : CanonicallyAnchored deletion
  deletionStable : ConjugationStable deletion
  deletionSpanLt : Submodule.span ℚ (Set.range deletion) <
    Submodule.span ℚ (Set.range w)
  complementCount_succ : complementCount + 1 = n
  fieldLe : generatedField deletion ≤ generatedField w
  deletionSharp : Algebra.trdeg ℚ (generatedField deletion) =
    (((complementCount + 2 : ℕ) : Cardinal))
  fullAlgebraic :
    letI : Algebra (generatedField deletion) (generatedField w) :=
      (IntermediateField.inclusion fieldLe).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic (generatedField deletion) (generatedField w)
  omittedOutside : w omitted ∉ Submodule.span ℚ (Set.range deletion)

/-- Every scaled terminal deletion of an anchored full witness can be upgraded to the
denominator-free anchor-preserving form. -/
def StableTerminalDeletionData.toAnchorPreserving
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w)
    (hanchor : CanonicallyAnchored w) :
    AnchorPreservingStableTerminalDeletionData w := by
  let v := anchorPreservingScaleFamily T.scale T.deletion
  have hd : T.scale ≠ 0 := ne_of_gt T.scale_pos
  have hvlin : LinearIndependent ℚ v :=
    anchorPreservingScaleFamily_linearIndependent hd T.deletionLinearIndependent
  have hvanchor : CanonicallyAnchored v :=
    canonicallyAnchored_anchorPreservingScaleFamily T.scale T.deletionAnchored
  have hvstable : ConjugationStable v :=
    conjugationStable_anchorPreservingScaleFamily hd T.deletionStable
  have hvspan : Submodule.span ℚ (Set.range v) =
      Submodule.span ℚ (Set.range T.deletion) :=
    span_anchorPreservingScaleFamily_eq hd T.deletion
  have hfield : generatedField v ≤ generatedField w := by
    rw [StableTerminalDeletionData.generatedField_anchorPreservingScaleFamily_eq T]
    exact sup_le T.fieldLe
      (realAnchorField_le_generatedField_of_canonicallyAnchored hanchor)
  have hvsharp : Algebra.trdeg ℚ (generatedField v) =
      (((T.complementCount + 2 : ℕ) : Cardinal)) := by
    rw [StableTerminalDeletionData.generatedField_anchorPreservingScaleFamily_eq T]
    exact StableTerminalDeletionData.trdeg_sup_realAnchorField_eq T
  have hfull : Algebra.trdeg ℚ (generatedField w) =
      (((T.complementCount + 2 : ℕ) : Cardinal)) :=
    T.scaledDeletion_sameTrdeg.symm.trans
      (ConjugationStableTerminal.scaledDeletionSharp T)
  have hsame : Algebra.trdeg ℚ (generatedField v) =
      Algebra.trdeg ℚ (generatedField w) := hvsharp.trans hfull.symm
  have hfinite : Algebra.trdeg ℚ (generatedField v) < Cardinal.aleph0 := by
    rw [hvsharp]
    exact Cardinal.natCast_lt_aleph0
  have halg := ConjugationStableTerminal.isAlgebraic_of_le_of_trdeg_eq_of_lt_aleph0
    hfield hsame hfinite
  exact {
    complementCount := T.complementCount
    deletion := v
    omitted := T.omitted
    deletionLinearIndependent := hvlin
    deletionAnchored := hvanchor
    deletionStable := hvstable
    deletionSpanLt := hvspan.trans_lt T.deletionSpanLt
    complementCount_succ := T.complementCount_succ
    fieldLe := hfield
    deletionSharp := hvsharp
    fullAlgebraic := halg
    omittedOutside := by
      rw [hvspan]
      exact T.omittedOutside }

/-- A positive least stable failure therefore carries terminal deletion data requiring no
subsequent common scaling or Kummer anchor adjunction. -/
theorem PositiveLeastConjugationStableFailure.nonempty_anchorPreservingTerminalDeletionData
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (H : PositiveLeastConjugationStableFailure w) :
    Nonempty (AnchorPreservingStableTerminalDeletionData w) := by
  obtain ⟨T⟩ := H.nonempty_stableTerminalDeletionData
  exact ⟨StableTerminalDeletionData.toAnchorPreserving T H.2.2.1⟩

/-- The denominator-free anchored deletion field literally contains the entirely real anchor
field. -/
theorem AnchorPreservingStableTerminalDeletionData.realAnchorField_le
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : AnchorPreservingStableTerminalDeletionData w) :
    realAnchorField ≤ generatedField D.deletion :=
  realAnchorField_le_generatedField_of_canonicallyAnchored D.deletionAnchored

/-- Algebraicity of the full graph field over the denominator-free deletion makes their exact
absolute transcendence degrees equal. -/
theorem AnchorPreservingStableTerminalDeletionData.full_trdeg_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : AnchorPreservingStableTerminalDeletionData w) :
    Algebra.trdeg ℚ (generatedField w) =
      (((D.complementCount + 2 : ℕ) : Cardinal)) := by
  let K := generatedField D.deletion
  let L := generatedField w
  letI : Algebra K L :=
    (IntermediateField.inclusion D.fieldLe).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ K L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  letI : Algebra.IsAlgebraic K L := D.fullAlgebraic
  have hadd := trdeg_add_eq ℚ K (A := L)
  have hzero : Algebra.trdeg K L = 0 := trdeg_eq_zero
  rw [hzero, add_zero, D.deletionSharp] at hadd
  exact hadd.symm

/-- The full family in denominator-free terminal data is a defect-one family. -/
theorem AnchorPreservingStableTerminalDeletionData.full_defectOne
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : AnchorPreservingStableTerminalDeletionData w) : DefectOne w := by
  rw [DefectOne, D.full_trdeg_eq]
  norm_cast
  have hcount := D.complementCount_succ
  omega

/-- Conditional on independence of `(pi^2,e)`, the honest anchored deletion graph field has
exactly one relative transcendence unit for each complementary deletion input. -/
theorem AnchorPreservingStableTerminalDeletionData.relative_trdeg_realAnchor_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : AnchorPreservingStableTerminalDeletionData w)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    letI : Algebra realAnchorField (generatedField D.deletion) :=
      (IntermediateField.inclusion D.realAnchorField_le).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField (generatedField D.deletion) =
      ((D.complementCount : ℕ) : Cardinal) := by
  letI : Algebra realAnchorField (generatedField D.deletion) :=
    (IntermediateField.inclusion D.realAnchorField_le).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField (generatedField D.deletion) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ realAnchorField (A := generatedField D.deletion)
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    D.deletionSharp] at hadd
  have hcancel : Algebra.trdeg realAnchorField (generatedField D.deletion) + 2 =
      (D.complementCount : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField (generatedField D.deletion) + 2 =
          2 + Algebra.trdeg realAnchorField (generatedField D.deletion) := add_comm _ _
      _ = (((D.complementCount + 2 : ℕ) : Cardinal)) := hadd
      _ = (D.complementCount : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- Every rational direction in the full input span, together with its exponential, is
algebraic over the honest denominator-free deletion graph field. -/
theorem AnchorPreservingStableTerminalDeletionData.span_pair_isAlgebraic
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : AnchorPreservingStableTerminalDeletionData w) {x : ℂ}
    (hx : x ∈ Submodule.span ℚ (Set.range w)) :
    IsAlgebraic (generatedField D.deletion) x ∧
      IsAlgebraic (generatedField D.deletion) (Complex.exp x) := by
  let K := generatedField D.deletion
  let L := generatedField w
  letI : Algebra K L :=
    (IntermediateField.inclusion D.fieldLe).toRingHom.toRatAlgHom.toAlgebra
  haveI : IsScalarTower K L ℂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rfl
  letI : Algebra.IsAlgebraic K L := D.fullAlgebraic
  have hxL : x ∈ L := ConjugationStableTerminal.mem_generatedField_of_mem_span w hx
  have hxAlgL : IsAlgebraic L x :=
    (isIntegral_of_mem_intermediateField L hxL).isAlgebraic
  have hxAlgK : IsAlgebraic K x := hxAlgL.restrictScalars K
  have hsingleton : Submodule.span ℚ (Set.range (fun _ : Fin 1 ↦ x)) ≤
      Submodule.span ℚ (Set.range w) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hx
  obtain ⟨d, hd, hfield⟩ :=
    exists_pos_integer_scale_generatedField_le_of_span_le
      (fun _ : Fin 1 ↦ x) w hsingleton
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  let E := generatedField (ratScaleFamily (d : ℚ) (fun _ : Fin 1 ↦ x))
  letI : Algebra E L :=
    (IntermediateField.inclusion hfield).toRingHom.toRatAlgHom.toAlgebra
  haveI : IsScalarTower E L ℂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext a
    rfl
  have hexpIntE : IsIntegral E (Complex.exp x) := by
    simpa [E] using exp_isIntegral_over_ratScale
      (d : ℚ) hdQ (fun _ : Fin 1 ↦ x) (0 : Fin 1)
  have hexpIntL : IsIntegral L (Complex.exp x) := hexpIntE.tower_top
  have hexpAlgL : IsAlgebraic L (Complex.exp x) := hexpIntL.isAlgebraic
  exact ⟨hxAlgK, hexpAlgL.restrictScalars K⟩

/-- The disjoint global endpoint using the honest anchor-preserving terminal deletion rather
than the auxiliary uniformly scaled field. -/
def RealAnchorPreservingStableTerminalDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ realAnchorCore ∨
    (AlgebraicIndependent ℚ realAnchorCore ∧
      ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
        PositiveLeastConjugationStableFailure w ∧
          Nonempty (AnchorPreservingStableTerminalDeletionData w))

/-- Failure of Schanuel is exactly the disjoint denominator-free real terminal dichotomy. -/
theorem not_conjecture_iff_realAnchorPreservingStableTerminalDichotomy :
    ¬ Conjecture ↔ RealAnchorPreservingStableTerminalDichotomy := by
  constructor
  · intro hnot
    by_cases hcore : AlgebraicIndependent ℚ realAnchorCore
    · apply Or.inr
      refine ⟨hcore, ?_⟩
      rcases
          not_conjecture_iff_realAnchorCore_dependent_or_positiveLeastStableFailure.mp hnot with
        hdep | ⟨n, w, H⟩
      · exact False.elim (hdep hcore)
      · exact ⟨n, w, H, H.nonempty_anchorPreservingTerminalDeletionData⟩
    · exact Or.inl hcore
  · rintro (hdep | ⟨-, n, w, H, -⟩)
    · exact
        not_conjecture_iff_realAnchorCore_dependent_or_positiveLeastStableFailure.mpr
          (Or.inl hdep)
    · exact
        not_conjecture_iff_realAnchorCore_dependent_or_positiveLeastStableFailure.mpr
          (Or.inr ⟨n, w, H⟩)

/-- The missing direction over an honest anchor-preserving terminal deletion can be chosen as an
actual conjugation eigenvector.  Both that direction and its genuine exponential are algebraic
over the smaller equality graph field. -/
theorem PositiveLeastConjugationStableFailure.exists_algebraic_eigenvector_complement
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (H : PositiveLeastConjugationStableFailure w)
    (D : AnchorPreservingStableTerminalDeletionData w) :
    ∃ b : ℂ,
      b ∈ Submodule.span ℚ (Set.range w) ∧
      b ∉ Submodule.span ℚ (Set.range D.deletion) ∧
      (star b = b ∨ star b = -b) ∧
      IsAlgebraic (generatedField D.deletion) b ∧
      IsAlgebraic (generatedField D.deletion) (Complex.exp b) := by
  rcases H with ⟨-, hwlin, -, hwstable, -, -⟩
  let R : Submodule ℚ ℂ := Submodule.span ℚ (Set.range w)
  let P : Submodule ℚ ℂ := Submodule.span ℚ (Set.range D.deletion)
  have hPR : P ≤ R := D.deletionSpanLt.le
  have hRstable : R.map conjugationLinearEquiv.toLinearMap = R := by
    rw [map_span_conjugation_eq]
    exact hwstable
  have hPstable : P.map conjugationLinearEquiv.toLinearMap = P := by
    change (Submodule.span ℚ (Set.range D.deletion)).map
      conjugationLinearEquiv.toLinearMap =
        Submodule.span ℚ (Set.range D.deletion)
    rw [map_span_conjugation_eq]
    exact D.deletionStable
  letI : FiniteDimensional ℚ R :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  let A : Submodule ℚ R := P.comap R.subtype
  have hRrank : Module.finrank ℚ R = n + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq hwlin rfl
  have hPrank : Module.finrank ℚ P = D.complementCount + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq D.deletionLinearIndependent rfl
  have hArank : Module.finrank ℚ A = D.complementCount + 2 := by
    let e := Submodule.comapSubtypeEquivOfLe hPR
    exact e.finrank_eq.trans hPrank
  have hAtop : A < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have htopRank : Module.finrank ℚ A = Module.finrank ℚ R := by
      rw [htop]
      simp
    rw [hArank, hRrank] at htopRank
    have hcount := D.complementCount_succ
    omega
  let c : R →ₗ[ℚ] R := restrictedConjugation R hRstable
  have hc : c.comp c = LinearMap.id := restrictedConjugation_involutive R hRstable
  have hAstable : ∀ x ∈ A, c x ∈ A := by
    intro x hx
    change star (x : ℂ) ∈ P
    have hxP : (x : ℂ) ∈ P := hx
    have hmem : star (x : ℂ) ∈ P.map conjugationLinearEquiv.toLinearMap :=
      ⟨(x : ℂ), hxP, rfl⟩
    rwa [hPstable] at hmem
  obtain ⟨g, b, -, hgA, hgb, hsign, -⟩ :=
    ConjugationStableTerminal.exists_eigenvector_complement_to_invariant_hyperplane
      c hc A hAstable hAtop
  have hbnotA : b ∉ A := by
    intro hb
    exact hgb (LinearMap.mem_ker.mp (hgA hb))
  have hbnotP : (b : ℂ) ∉ P := by
    intro hb
    exact hbnotA hb
  have heigen : star (b : ℂ) = (b : ℂ) ∨ star (b : ℂ) = -(b : ℂ) := by
    rcases hsign with ⟨-, hb⟩ | ⟨-, hb⟩
    · apply Or.inl
      have hcoe := congrArg ((↑) : R → ℂ) hb
      simpa [c, restrictedConjugation_apply] using hcoe
    · apply Or.inr
      have hcoe := congrArg ((↑) : R → ℂ) hb
      simpa [c, restrictedConjugation_apply] using hcoe
  have hpairs := D.span_pair_isAlgebraic b.2
  exact ⟨b, b.2, hbnotP, heigen, hpairs⟩

/-- An honest terminal deletion together with an algebraic conjugation eigenvector completing
its missing rational direction. -/
structure EigenvectorCompletedStableTerminalData {n : ℕ}
    (w : Fin (n + 2) → ℂ) where
  deletionData : AnchorPreservingStableTerminalDeletionData w
  eigenvector : ℂ
  eigenvectorMem : eigenvector ∈ Submodule.span ℚ (Set.range w)
  eigenvectorOutside : eigenvector ∉
    Submodule.span ℚ (Set.range deletionData.deletion)
  eigenvectorSign : star eigenvector = eigenvector ∨ star eigenvector = -eigenvector
  eigenvectorAlgebraic :
    IsAlgebraic (generatedField deletionData.deletion) eigenvector
  expEigenvectorAlgebraic :
    IsAlgebraic (generatedField deletionData.deletion) (Complex.exp eigenvector)

/-- The completed terminal family appends the distinguished eigenvector to the honest deletion. -/
def EigenvectorCompletedStableTerminalData.completed
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    Fin ((E.deletionData.complementCount + 2) + 1) → ℂ :=
  Fin.snoc E.deletionData.deletion E.eigenvector

/-- Appending the missing eigenvector restores linear independence. -/
theorem EigenvectorCompletedStableTerminalData.completedLinearIndependent
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    LinearIndependent ℚ E.completed := by
  rw [EigenvectorCompletedStableTerminalData.completed, linearIndependent_fin_snoc]
  exact ⟨E.deletionData.deletionLinearIndependent, E.eigenvectorOutside⟩

/-- The eigenvector completion is a basis of the original least-failure input span. -/
theorem EigenvectorCompletedStableTerminalData.completedSpan_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w)
    (H : PositiveLeastConjugationStableFailure w) :
    Submodule.span ℚ (Set.range E.completed) =
      Submodule.span ℚ (Set.range w) := by
  have hle : Submodule.span ℚ (Set.range E.completed) ≤
      Submodule.span ℚ (Set.range w) := by
    apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    refine Fin.lastCases ?_ (fun j ↦ ?_) i
    · simpa [EigenvectorCompletedStableTerminalData.completed] using E.eigenvectorMem
    · simpa [EigenvectorCompletedStableTerminalData.completed] using
        E.deletionData.deletionSpanLt.le (Submodule.subset_span ⟨j, rfl⟩)
  letI : FiniteDimensional ℚ (Submodule.span ℚ (Set.range w)) :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  apply Submodule.eq_of_le_of_finrank_eq hle
  rw [finrank_span_eq_card E.completedLinearIndependent,
    finrank_span_eq_card H.2.1]
  simp only [Fintype.card_fin]
  have hcount := E.deletionData.complementCount_succ
  omega

/-- The eigenvector completion retains the two literal real anchors. -/
theorem EigenvectorCompletedStableTerminalData.completedAnchored
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    CanonicallyAnchored E.completed := by
  rcases E.deletionData.deletionAnchored with ⟨hzero, hone⟩
  exact ⟨by simpa [EigenvectorCompletedStableTerminalData.completed] using hzero,
    by simpa [EigenvectorCompletedStableTerminalData.completed] using hone⟩

/-- The eigenvector completion is conjugation-stable because it spans the original stable
least-failure space. -/
theorem EigenvectorCompletedStableTerminalData.completedStable
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w)
    (H : PositiveLeastConjugationStableFailure w) :
    ConjugationStable E.completed := by
  unfold ConjugationStable
  rw [← map_span_conjugation_eq, E.completedSpan_eq H,
    map_span_conjugation_eq, H.2.2.2.1]

/-- The last coordinate of the completion is the distinguished conjugation eigenvector. -/
theorem EigenvectorCompletedStableTerminalData.completed_last
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    E.completed (Fin.last (E.deletionData.complementCount + 2)) = E.eigenvector := by
  simp [EigenvectorCompletedStableTerminalData.completed]

/-- Removing the last coordinate of the completion recovers the honest deletion literally. -/
@[simp]
theorem EigenvectorCompletedStableTerminalData.completed_init
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    Fin.init E.completed = E.deletionData.deletion := by
  simp [EigenvectorCompletedStableTerminalData.completed]

/-- The predecessor graph field embeds literally into the eigenvector-completed graph field. -/
theorem EigenvectorCompletedStableTerminalData.deletionField_le_completedField
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    generatedField E.deletionData.deletion ≤ generatedField E.completed := by
  exact generatedField_le_generatedField_snoc
    E.deletionData.deletion E.eigenvector

/-- Both new graph generators are algebraic, so the completed graph field is algebraic over
its literal predecessor graph field. -/
theorem EigenvectorCompletedStableTerminalData.completedAlgebraic
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    letI : Algebra (generatedField E.deletionData.deletion)
        (generatedField E.completed) :=
      (IntermediateField.inclusion
        E.deletionField_le_completedField).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic (generatedField E.deletionData.deletion)
      (generatedField E.completed) := by
  letI : Algebra (generatedField E.deletionData.deletion)
      (generatedField E.completed) :=
    (IntermediateField.inclusion E.deletionField_le_completedField).toRingHom.toRatAlgHom.toAlgebra
  simpa only [EigenvectorCompletedStableTerminalData.completed] using
    (isAlgebraic_generatedField_snoc_of_pair_isAlgebraic
      E.deletionData.deletion E.eigenvector
        E.eigenvectorAlgebraic E.expEigenvectorAlgebraic)

/-- The completed graph field has exactly the predecessor's sharp transcendence degree. -/
theorem EigenvectorCompletedStableTerminalData.completedSharp
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    Algebra.trdeg ℚ (generatedField E.completed) =
      (((E.deletionData.complementCount + 2 : ℕ) : Cardinal)) := by
  simpa only [EigenvectorCompletedStableTerminalData.completed] using
    (trdeg_generatedField_snoc_eq_of_pair_isAlgebraic
      E.deletionData.deletion E.eigenvector
        E.eigenvectorAlgebraic E.expEigenvectorAlgebraic).trans
          E.deletionData.deletionSharp

/-- The eigenvector completion is itself an anchored stable defect-one family. -/
theorem EigenvectorCompletedStableTerminalData.completedDefectOne
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w) :
    DefectOne E.completed := by
  exact E.completedSharp

/-- The completion is not merely a defect-one normal form: it remains a positive least stable
failure at the same complementary arity as the original witness. -/
theorem EigenvectorCompletedStableTerminalData.completed_positiveLeastFailure
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w)
    (H : PositiveLeastConjugationStableFailure w) :
    PositiveLeastConjugationStableFailure E.completed := by
  have hstable := E.completedStable H
  obtain ⟨-, -, -, -, -, hmin⟩ := H
  refine ⟨by omega, E.completedLinearIndependent, E.completedAnchored,
    hstable, not_bound_of_defectOne E.completedDefectOne, ?_⟩
  intro k hk
  apply hmin k
  have hcount := E.deletionData.complementCount_succ
  omega

/-- Every positive least stable failure has an algebraically trivial final adjunction whose
last input is fixed or anti-fixed by conjugation. -/
theorem PositiveLeastConjugationStableFailure.nonempty_eigenvectorCompletedTerminalData
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (H : PositiveLeastConjugationStableFailure w) :
    Nonempty (EigenvectorCompletedStableTerminalData w) := by
  obtain ⟨D⟩ := H.nonempty_anchorPreservingTerminalDeletionData
  obtain ⟨b, hbmem, hboutside, hbsign, hbAlg, hexpAlg⟩ :=
    H.exists_algebraic_eigenvector_complement D
  exact ⟨{
    deletionData := D
    eigenvector := b
    eigenvectorMem := hbmem
    eigenvectorOutside := hboutside
    eigenvectorSign := hbsign
    eigenvectorAlgebraic := hbAlg
    expEigenvectorAlgebraic := hexpAlg }⟩

/-- All geometric and field-theoretic conclusions of the eigenvector completion in one normal
form statement. -/
theorem EigenvectorCompletedStableTerminalData.completed_normalForm
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w)
    (H : PositiveLeastConjugationStableFailure w) :
    LinearIndependent ℚ E.completed ∧
      CanonicallyAnchored E.completed ∧
      ConjugationStable E.completed ∧
      DefectOne E.completed ∧
      Submodule.span ℚ (Set.range E.completed) =
        Submodule.span ℚ (Set.range w) ∧
      (star (E.completed (Fin.last (E.deletionData.complementCount + 2))) =
          E.completed (Fin.last (E.deletionData.complementCount + 2)) ∨
        star (E.completed (Fin.last (E.deletionData.complementCount + 2))) =
          -E.completed (Fin.last (E.deletionData.complementCount + 2))) := by
  refine ⟨E.completedLinearIndependent, E.completedAnchored,
    E.completedStable H, E.completedDefectOne, E.completedSpan_eq H, ?_⟩
  simpa only [E.completed_last] using E.eigenvectorSign

/-- The strongest current disjoint terminal endpoint: either the real anchor pair is dependent,
or a positive least stable failure admits an honest algebraically trivial eigenvector completion. -/
def RealEigenvectorCompletedStableTerminalDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ realAnchorCore ∨
    (AlgebraicIndependent ℚ realAnchorCore ∧
      ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
        PositiveLeastConjugationStableFailure w ∧
          Nonempty (EigenvectorCompletedStableTerminalData w))

/-- Failure of Schanuel is exactly the disjoint eigenvector-completed terminal dichotomy. -/
theorem not_conjecture_iff_realEigenvectorCompletedStableTerminalDichotomy :
    ¬ Conjecture ↔ RealEigenvectorCompletedStableTerminalDichotomy := by
  constructor
  · intro hnot
    rcases not_conjecture_iff_realAnchorPreservingStableTerminalDichotomy.mp hnot with
      hdep | ⟨hcore, n, w, H, -⟩
    · exact Or.inl hdep
    · exact Or.inr
        ⟨hcore, n, w, H, H.nonempty_eigenvectorCompletedTerminalData⟩
  · rintro (hdep | ⟨hcore, n, w, H, E⟩)
    · exact not_conjecture_iff_realAnchorPreservingStableTerminalDichotomy.mpr
        (Or.inl hdep)
    · exact not_conjecture_iff_realAnchorPreservingStableTerminalDichotomy.mpr
        (Or.inr ⟨hcore, n, w, H,
          E.map EigenvectorCompletedStableTerminalData.deletionData⟩)

/-- A self-contained eigenvector terminal witness.  Its literal initial segment is the sharp
stable anchored hyperplane, and its literal last input-output pair is algebraic over that
predecessor graph field. -/
def PositiveEigenvectorTerminalWitness {n : ℕ}
    (u : Fin (n + 3) → ℂ) : Prop :=
  PositiveLeastConjugationStableFailure u ∧
    LinearIndependent ℚ (Fin.init u) ∧
    CanonicallyAnchored (Fin.init u) ∧
    ConjugationStable (Fin.init u) ∧
    Algebra.trdeg ℚ (generatedField (Fin.init u)) =
      (((n + 2 : ℕ) : Cardinal)) ∧
    u (Fin.last (n + 2)) ∉ Submodule.span ℚ (Set.range (Fin.init u)) ∧
    (star (u (Fin.last (n + 2))) = u (Fin.last (n + 2)) ∨
      star (u (Fin.last (n + 2))) = -u (Fin.last (n + 2))) ∧
    IsAlgebraic (generatedField (Fin.init u)) (u (Fin.last (n + 2))) ∧
    IsAlgebraic (generatedField (Fin.init u))
      (Complex.exp (u (Fin.last (n + 2))))

/-- The literal prefix graph field embeds in the full terminal graph field. -/
theorem PositiveEigenvectorTerminalWitness.initialField_le
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (_W : PositiveEigenvectorTerminalWitness u) :
    generatedField (Fin.init u) ≤ generatedField u := by
  exact generatedField_init_le_generatedField u

/-- The literal prefix has its displayed sharp absolute transcendence degree. -/
theorem PositiveEigenvectorTerminalWitness.initialSharp
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Algebra.trdeg ℚ (generatedField (Fin.init u)) =
      (((n + 2 : ℕ) : Cardinal)) := by
  exact W.2.2.2.2.1

/-- The full literal terminal tuple has the same sharp absolute transcendence degree. -/
theorem PositiveEigenvectorTerminalWitness.fullSharp
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Algebra.trdeg ℚ (generatedField u) = (((n + 2 : ℕ) : Cardinal)) := by
  exact W.1.defectOne

/-- The literal prefix satisfies Schanuel's bound sharply. -/
theorem PositiveEigenvectorTerminalWitness.initialBound
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) : Bound (Fin.init u) := by
  unfold Bound
  rw [W.initialSharp]
  simp

/-- The full terminal graph field is algebraic over its literal prefix graph field. -/
theorem PositiveEigenvectorTerminalWitness.fullAlgebraic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    letI : Algebra (generatedField (Fin.init u)) (generatedField u) :=
      (IntermediateField.inclusion W.initialField_le).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic (generatedField (Fin.init u)) (generatedField u) := by
  letI : Algebra (generatedField (Fin.init u)) (generatedField u) :=
    (IntermediateField.inclusion W.initialField_le).toRingHom.toRatAlgHom.toAlgebra
  have hsame : Algebra.trdeg ℚ (generatedField (Fin.init u)) =
      Algebra.trdeg ℚ (generatedField u) := W.initialSharp.trans W.fullSharp.symm
  have hfinite : Algebra.trdeg ℚ (generatedField (Fin.init u)) < Cardinal.aleph0 := by
    rw [W.initialSharp]
    exact Cardinal.natCast_lt_aleph0
  exact ConjugationStableTerminal.isAlgebraic_of_le_of_trdeg_eq_of_lt_aleph0
    W.initialField_le hsame hfinite

/-- Equivalently, the full field has relative transcendence degree zero over the literal prefix. -/
theorem PositiveEigenvectorTerminalWitness.relative_trdeg_full_eq_zero
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    letI : Algebra (generatedField (Fin.init u)) (generatedField u) :=
      (IntermediateField.inclusion W.initialField_le).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg (generatedField (Fin.init u)) (generatedField u) = 0 := by
  letI : Algebra (generatedField (Fin.init u)) (generatedField u) :=
    (IntermediateField.inclusion W.initialField_le).toRingHom.toRatAlgHom.toAlgebra
  letI : Algebra.IsAlgebraic (generatedField (Fin.init u)) (generatedField u) :=
    W.fullAlgebraic
  exact trdeg_eq_zero

/-- The entirely real anchor field lies literally in the prefix graph field. -/
theorem PositiveEigenvectorTerminalWitness.realAnchorField_le_initial
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    realAnchorField ≤ generatedField (Fin.init u) := by
  exact realAnchorField_le_generatedField_of_canonicallyAnchored W.2.2.1

/-- Conditional on independence of `(pi^2,e)`, the literal prefix has exactly `n` relative
transcendence units over the real anchor. -/
theorem PositiveEigenvectorTerminalWitness.relative_trdeg_initial_realAnchor_eq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    letI : Algebra realAnchorField (generatedField (Fin.init u)) :=
      (IntermediateField.inclusion
        W.realAnchorField_le_initial).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField (generatedField (Fin.init u)) =
      ((n : ℕ) : Cardinal) := by
  letI : Algebra realAnchorField (generatedField (Fin.init u)) :=
    (IntermediateField.inclusion
      W.realAnchorField_le_initial).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField (generatedField (Fin.init u)) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ realAnchorField
    (A := generatedField (Fin.init u))
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    W.initialSharp] at hadd
  have hcancel : Algebra.trdeg realAnchorField (generatedField (Fin.init u)) + 2 =
      (n : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField (generatedField (Fin.init u)) + 2 =
          2 + Algebra.trdeg realAnchorField (generatedField (Fin.init u)) := add_comm _ _
      _ = (((n + 2 : ℕ) : Cardinal)) := hadd
      _ = (n : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- The entirely real anchor field also lies in the full terminal graph field. -/
theorem PositiveEigenvectorTerminalWitness.realAnchorField_le_full
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    realAnchorField ≤ generatedField u := by
  exact realAnchorField_le_generatedField_of_canonicallyAnchored W.1.2.2.1

/-- Conditional on independence of `(pi^2,e)`, the full literal terminal graph field has the
same exact relative degree `n` over the real anchor. -/
theorem PositiveEigenvectorTerminalWitness.relative_trdeg_full_realAnchor_eq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    letI : Algebra realAnchorField (generatedField u) :=
      (IntermediateField.inclusion
        W.realAnchorField_le_full).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField (generatedField u) = ((n : ℕ) : Cardinal) := by
  letI : Algebra realAnchorField (generatedField u) :=
    (IntermediateField.inclusion
      W.realAnchorField_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField (generatedField u) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ realAnchorField (A := generatedField u)
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    W.fullSharp] at hadd
  have hcancel : Algebra.trdeg realAnchorField (generatedField u) + 2 =
      (n : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField (generatedField u) + 2 =
          2 + Algebra.trdeg realAnchorField (generatedField u) := add_comm _ _
      _ = (((n + 2 : ℕ) : Cardinal)) := hadd
      _ = (n : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- The final eigenvector lies outside even the rational span of the canonical anchor. -/
theorem PositiveEigenvectorTerminalWitness.last_not_mem_canonicalAnchor_span
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    u (Fin.last (n + 2)) ∉ Submodule.span ℚ (Set.range canonicalAnchor) := by
  rcases W with ⟨-, -, hanchor, -, -, hout, -, -, -⟩
  intro hmem
  exact hout (span_canonicalAnchor_le_of_canonicallyAnchored hanchor hmem)

/-- In particular, the final eigenvector is nonzero. -/
theorem PositiveEigenvectorTerminalWitness.last_ne_zero
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    u (Fin.last (n + 2)) ≠ 0 := by
  intro hzero
  apply W.last_not_mem_canonicalAnchor_span
  rw [hzero]
  exact Submodule.zero_mem _

/-- The mixed terminal invariant obtained by multiplying the odd input coordinate by the odd
part of its exponential.  It is conjugation-fixed for either sign of the terminal eigenvector. -/
def eigenvectorTerminalCrossInvariant {n : ℕ} (u : Fin (n + 3) → ℂ) : ℂ :=
  let b := u (Fin.last (n + 2))
  b * (Complex.exp b - (Complex.exp b)⁻¹)

/-- The mixed terminal invariant as a literal element of the full graph field. -/
def eigenvectorTerminalCrossInFull {n : ℕ} (u : Fin (n + 3) → ℂ) : generatedField u :=
  selectedInputInFull u (Fin.last (n + 2)) *
    (selectedExpInFull u (Fin.last (n + 2)) -
      (selectedExpInFull u (Fin.last (n + 2)))⁻¹)

@[simp]
theorem coe_eigenvectorTerminalCrossInFull
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    (eigenvectorTerminalCrossInFull u : ℂ) = eigenvectorTerminalCrossInvariant u :=
  rfl

/-- Whether the final input is fixed or anti-fixed, its square is conjugation-fixed. -/
theorem PositiveEigenvectorTerminalWitness.star_last_sq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    star (u (Fin.last (n + 2)) ^ 2) = u (Fin.last (n + 2)) ^ 2 := by
  rcases W with ⟨-, -, -, -, -, -, hsign, -, -⟩
  rcases hsign with hfixed | hanti
  · rw [Complex.star_def] at hfixed ⊢
    rw [map_pow, hfixed]
  · rw [Complex.star_def] at hanti ⊢
    rw [map_pow, hanti]
    ring

/-- The exponential trace of the final eigenvector is conjugation-fixed in both sign cases. -/
theorem PositiveEigenvectorTerminalWitness.star_last_exp_trace
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    star (Complex.exp (u (Fin.last (n + 2))) +
        (Complex.exp (u (Fin.last (n + 2))))⁻¹) =
      Complex.exp (u (Fin.last (n + 2))) +
        (Complex.exp (u (Fin.last (n + 2))))⁻¹ := by
  rcases W with ⟨-, -, -, -, -, -, hsign, -, -⟩
  rcases hsign with hfixed | hanti
  · have hi : (starRingEnd ℂ) (u (Fin.last (n + 2))) =
        u (Fin.last (n + 2)) := by
      simpa only [starRingEnd_apply] using hfixed
    change (starRingEnd ℂ) (Complex.exp (u (Fin.last (n + 2))) +
      (Complex.exp (u (Fin.last (n + 2))))⁻¹) = _
    rw [map_add, map_inv₀, ← Complex.exp_conj, hi]
  · have hi : (starRingEnd ℂ) (u (Fin.last (n + 2))) =
        -u (Fin.last (n + 2)) := by
      simpa only [starRingEnd_apply] using hanti
    change (starRingEnd ℂ) (Complex.exp (u (Fin.last (n + 2))) +
      (Complex.exp (u (Fin.last (n + 2))))⁻¹) = _
    rw [map_add, map_inv₀, ← Complex.exp_conj, hi, Complex.exp_neg]
    simp only [inv_inv]
    exact add_comm _ _

/-- The mixed input-output terminal invariant is conjugation-fixed in both eigenvalue cases. -/
theorem PositiveEigenvectorTerminalWitness.star_terminalCrossInvariant
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    star (eigenvectorTerminalCrossInvariant u) =
      eigenvectorTerminalCrossInvariant u := by
  let b := u (Fin.last (n + 2))
  change star (b * (Complex.exp b - (Complex.exp b)⁻¹)) =
    b * (Complex.exp b - (Complex.exp b)⁻¹)
  rcases W with ⟨-, -, -, -, -, -, hsign, -, -⟩
  rcases hsign with hfixed | hanti
  · have hi : (starRingEnd ℂ) b = b := by
      simpa only [starRingEnd_apply] using hfixed
    change (starRingEnd ℂ) (b * (Complex.exp b - (Complex.exp b)⁻¹)) = _
    rw [map_mul, map_sub, map_inv₀, ← Complex.exp_conj, hi]
  · have hi : (starRingEnd ℂ) b = -b := by
      simpa only [starRingEnd_apply] using hanti
    change (starRingEnd ℂ) (b * (Complex.exp b - (Complex.exp b)⁻¹)) = _
    rw [map_mul, map_sub, map_inv₀, ← Complex.exp_conj, hi, Complex.exp_neg]
    simp only [inv_inv]
    ring

/-- The squared final input belongs to the pointwise real field. -/
theorem PositiveEigenvectorTerminalWitness.last_sq_mem_conjugationFixedField
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    u (Fin.last (n + 2)) ^ 2 ∈ conjugationFixedField :=
  W.star_last_sq

/-- The final exponential trace belongs to the pointwise real field. -/
theorem PositiveEigenvectorTerminalWitness.last_exp_trace_mem_conjugationFixedField
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Complex.exp (u (Fin.last (n + 2))) +
        (Complex.exp (u (Fin.last (n + 2))))⁻¹ ∈ conjugationFixedField :=
  W.star_last_exp_trace

/-- The mixed terminal invariant belongs to the pointwise real field. -/
theorem PositiveEigenvectorTerminalWitness.terminalCrossInvariant_mem_conjugationFixedField
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    eigenvectorTerminalCrossInvariant u ∈ conjugationFixedField :=
  W.star_terminalCrossInvariant

/-- The squared final input is algebraic over the literal prefix graph field. -/
theorem PositiveEigenvectorTerminalWitness.last_sq_isAlgebraic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    IsAlgebraic (generatedField (Fin.init u))
      (u (Fin.last (n + 2)) ^ 2) := by
  rcases W with ⟨-, -, -, -, -, -, -, hb, -⟩
  exact hb.pow 2

/-- The real exponential trace of the final input is algebraic over the literal prefix graph
field. -/
theorem PositiveEigenvectorTerminalWitness.last_exp_trace_isAlgebraic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    IsAlgebraic (generatedField (Fin.init u))
      (Complex.exp (u (Fin.last (n + 2))) +
        (Complex.exp (u (Fin.last (n + 2))))⁻¹) := by
  rcases W with ⟨-, -, -, -, -, -, -, -, hexp⟩
  exact hexp.add hexp.inv

/-- The mixed terminal invariant is algebraic over the literal prefix graph field. -/
theorem PositiveEigenvectorTerminalWitness.terminalCrossInvariant_isAlgebraic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    IsAlgebraic (generatedField (Fin.init u))
      (eigenvectorTerminalCrossInvariant u) := by
  rcases W with ⟨-, -, -, -, -, -, -, hb, hexp⟩
  exact hb.mul (hexp.sub hexp.inv)

/-- The two-generator pointwise-real core attached to the literal final graph pair. -/
def eigenvectorTerminalRealCore {n : ℕ} (u : Fin (n + 3) → ℂ) :
    IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    ({u (Fin.last (n + 2)) ^ 2,
      Complex.exp (u (Fin.last (n + 2))) +
        (Complex.exp (u (Fin.last (n + 2))))⁻¹} : Set ℂ)

/-- The square of the mixed invariant already belongs to the original two-generator real core. -/
theorem terminalCrossInvariant_sq_mem_realCore
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    eigenvectorTerminalCrossInvariant u ^ 2 ∈ eigenvectorTerminalRealCore u := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let C := eigenvectorTerminalRealCore u
  have hb2 : b ^ 2 ∈ C :=
    IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have htrace : y + y⁻¹ ∈ C :=
    IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hid : eigenvectorTerminalCrossInvariant u ^ 2 =
      b ^ 2 * ((y + y⁻¹) ^ 2 - 4) := by
    change (b * (y - y⁻¹)) ^ 2 = b ^ 2 * ((y + y⁻¹) ^ 2 - 4)
    have hy0 : y ≠ 0 := Complex.exp_ne_zero b
    field_simp [hy0]
    ring
  rw [hid]
  exact C.mul_mem hb2 (C.sub_mem (C.pow_mem htrace 2) (C.natCast_mem 4))

/-- The final real core is pointwise fixed by conjugation. -/
theorem PositiveEigenvectorTerminalWitness.eigenvectorTerminalRealCore_le_fixed
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    eigenvectorTerminalRealCore u ≤ conjugationFixedField := by
  rw [eigenvectorTerminalRealCore, IntermediateField.adjoin_le_iff]
  rintro x (rfl | hx)
  · exact W.last_sq_mem_conjugationFixedField
  · rcases hx with rfl
    exact W.last_exp_trace_mem_conjugationFixedField

/-- The final real core is already contained in the field generated by the last input and its
exponential. -/
theorem eigenvectorTerminalRealCore_le_adjoin_last_pair
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    eigenvectorTerminalRealCore u ≤ IntermediateField.adjoin ℚ
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) := by
  rw [eigenvectorTerminalRealCore, IntermediateField.adjoin_le_iff]
  rintro x (rfl | hx)
  · exact (IntermediateField.adjoin ℚ
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ)).pow_mem
        (IntermediateField.subset_adjoin ℚ _
          (Set.mem_insert _ {Complex.exp (u (Fin.last (n + 2)))})) 2
  · rcases hx with rfl
    let A := IntermediateField.adjoin ℚ
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ)
    have hy : Complex.exp (u (Fin.last (n + 2))) ∈ A := by
      exact IntermediateField.subset_adjoin ℚ _
        (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
    exact A.add_mem hy (A.inv_mem hy)

/-- The analytically diagonal real core augments the separate square and reciprocal-trace
invariants by their conjugation-fixed mixed product. -/
def eigenvectorTerminalAnalyticRealCore {n : ℕ} (u : Fin (n + 3) → ℂ) :
    IntermediateField ℚ ℂ :=
  eigenvectorTerminalRealCore u ⊔
    IntermediateField.adjoin ℚ ({eigenvectorTerminalCrossInvariant u} : Set ℂ)

/-- The original two-generator real core is contained in the analytic real core. -/
theorem eigenvectorTerminalRealCore_le_analyticRealCore
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    eigenvectorTerminalRealCore u ≤ eigenvectorTerminalAnalyticRealCore u :=
  le_sup_left

/-- Joining the same prefix preserves containment of the original real core in the analytic real
core. -/
theorem initialRealCore_le_initialAnalyticRealCore
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u ≤
      generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u :=
  sup_le le_sup_left (eigenvectorTerminalRealCore_le_analyticRealCore u |>.trans le_sup_right)

/-- The mixed invariant belongs to the analytic real core. -/
theorem terminalCrossInvariant_mem_analyticRealCore
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    eigenvectorTerminalCrossInvariant u ∈ eigenvectorTerminalAnalyticRealCore u := by
  apply (show IntermediateField.adjoin ℚ
    ({eigenvectorTerminalCrossInvariant u} : Set ℂ) ≤
      eigenvectorTerminalAnalyticRealCore u from le_sup_right)
  exact IntermediateField.subset_adjoin ℚ _ (Set.mem_singleton _)

/-- The analytic terminal real core remains pointwise fixed by complex conjugation. -/
theorem PositiveEigenvectorTerminalWitness.eigenvectorTerminalAnalyticRealCore_le_fixed
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    eigenvectorTerminalAnalyticRealCore u ≤ conjugationFixedField := by
  rw [eigenvectorTerminalAnalyticRealCore]
  apply sup_le W.eigenvectorTerminalRealCore_le_fixed
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl : x = eigenvectorTerminalCrossInvariant u)
  exact W.terminalCrossInvariant_mem_conjugationFixedField

/-- The analytic real core is contained in the field generated by the literal terminal graph
pair. -/
theorem eigenvectorTerminalAnalyticRealCore_le_adjoin_last_pair
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    eigenvectorTerminalAnalyticRealCore u ≤ IntermediateField.adjoin ℚ
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) := by
  rw [eigenvectorTerminalAnalyticRealCore]
  apply sup_le (eigenvectorTerminalRealCore_le_adjoin_last_pair u)
  rw [IntermediateField.adjoin_le_iff]
  rintro x (rfl : x = eigenvectorTerminalCrossInvariant u)
  let A := IntermediateField.adjoin ℚ
    ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ)
  have hb : u (Fin.last (n + 2)) ∈ A :=
    IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert _ {Complex.exp (u (Fin.last (n + 2)))})
  have hy : Complex.exp (u (Fin.last (n + 2))) ∈ A :=
    IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  exact A.mul_mem hb (A.sub_mem hy (A.inv_mem hy))

/-- The full graph field is exactly the prefix graph field with the literal final input-output
pair adjoined. -/
theorem PositiveEigenvectorTerminalWitness.fullField_eq_initial_sup_adjoin_last_pair
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (_W : PositiveEigenvectorTerminalWitness u) :
    generatedField u = generatedField (Fin.init u) ⊔ IntermediateField.adjoin ℚ
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) := by
  have hsnoc : Fin.snoc (Fin.init u) (u (Fin.last (n + 2))) = u :=
    Fin.snoc_init_self u
  calc
    generatedField u =
        generatedField (Fin.snoc (Fin.init u) (u (Fin.last (n + 2)))) := by
      exact congrArg generatedField hsnoc.symm
    _ = generatedField (Fin.init u) ⊔ IntermediateField.adjoin ℚ
        ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) :=
      generatedField_snoc_eq_sup_adjoin_pair _ _

/-- Lossless real-shadow reconstruction: adjoining the last graph pair to the prefix joined with
the pointwise-real terminal core recovers the full graph field exactly. -/
theorem PositiveEigenvectorTerminalWitness.fullField_eq_initialRealCore_sup_lastPair
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    generatedField u =
      (generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u) ⊔
        IntermediateField.adjoin ℚ
          ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) := by
  let K := generatedField (Fin.init u)
  let C := eigenvectorTerminalRealCore u
  let A := IntermediateField.adjoin ℚ
    ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ)
  have hCA : C ≤ A := eigenvectorTerminalRealCore_le_adjoin_last_pair u
  rw [W.fullField_eq_initial_sup_adjoin_last_pair]
  change K ⊔ A = (K ⊔ C) ⊔ A
  apply le_antisymm
  · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  · exact sup_le (sup_le le_sup_left (hCA.trans le_sup_right)) le_sup_right

/-- Adjoining the terminal graph pair to the prefix joined with the analytic real core still
recovers the full graph field exactly. -/
theorem PositiveEigenvectorTerminalWitness.fullField_eq_initialAnalyticRealCore_sup_lastPair
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    generatedField u =
      (generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u) ⊔
        IntermediateField.adjoin ℚ
          ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) := by
  let K := generatedField (Fin.init u)
  let C := eigenvectorTerminalAnalyticRealCore u
  let A := IntermediateField.adjoin ℚ
    ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ)
  have hCA : C ≤ A := eigenvectorTerminalAnalyticRealCore_le_adjoin_last_pair u
  rw [W.fullField_eq_initial_sup_adjoin_last_pair]
  change K ⊔ A = (K ⊔ C) ⊔ A
  apply le_antisymm
  · exact sup_le (le_sup_left.trans le_sup_left) le_sup_right
  · exact sup_le (sup_le le_sup_left (hCA.trans le_sup_right)) le_sup_right

/-- Over the analytic real-shadow field, the last exponential is already a rational expression
in the last input: its reciprocal trace and mixed odd product recover it. -/
theorem PositiveEigenvectorTerminalWitness.terminalExp_mem_adjoin_lastInput_initialAnalytic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    Complex.exp (u (Fin.last (n + 2))) ∈ IntermediateField.adjoin A
      ({u (Fin.last (n + 2))} : Set ℂ) := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let c := eigenvectorTerminalCrossInvariant u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let N : IntermediateField A ℂ := IntermediateField.adjoin A ({b} : Set ℂ)
  have hbN : b ∈ N :=
    IntermediateField.subset_adjoin A _ (Set.mem_singleton b)
  have htA : y + y⁻¹ ∈ A := by
    apply (show eigenvectorTerminalAnalyticRealCore u ≤ A from le_sup_right)
    apply eigenvectorTerminalRealCore_le_analyticRealCore u
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hcA : c ∈ A := by
    apply (show eigenvectorTerminalAnalyticRealCore u ≤ A from le_sup_right)
    exact terminalCrossInvariant_mem_analyticRealCore u
  have htN : y + y⁻¹ ∈ N := by
    simpa using IntermediateField.algebraMap_mem N (⟨y + y⁻¹, htA⟩ : A)
  have hcN : c ∈ N := by
    simpa using IntermediateField.algebraMap_mem N (⟨c, hcA⟩ : A)
  have hcdiv : c * b⁻¹ = y - y⁻¹ := by
    change (b * (y - y⁻¹)) * b⁻¹ = y - y⁻¹
    calc
      (b * (y - y⁻¹)) * b⁻¹ = (b * b⁻¹) * (y - y⁻¹) := by ring
      _ = y - y⁻¹ := by rw [mul_inv_cancel₀ W.last_ne_zero, one_mul]
  have hid : y = (y + y⁻¹ + c * b⁻¹) / 2 := by
    rw [hcdiv]
    ring
  change y ∈ N
  rw [hid]
  exact N.div_mem (N.add_mem htN (N.mul_mem hcN (N.inv_mem hbN))) (N.natCast_mem 2)

/-- Consequently the full graph field is obtained from the analytic real shadow by adjoining
only the last input; the last exponential is not a second generator. -/
theorem PositiveEigenvectorTerminalWitness.restrictScalars_adjoin_lastInput_eq_fullField
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    (IntermediateField.adjoin A
      ({u (Fin.last (n + 2))} : Set ℂ)).restrictScalars ℚ = generatedField u := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  let N : IntermediateField A ℂ := IntermediateField.adjoin A ({b} : Set ℂ)
  have hrestrict : N.restrictScalars ℚ = A ⊔ IntermediateField.adjoin ℚ ({b} : Set ℂ) :=
    IntermediateField.restrictScalars_adjoin_eq_sup ℚ A _
  have hbN : b ∈ N :=
    IntermediateField.subset_adjoin A _ (Set.mem_singleton b)
  have hyN : y ∈ N := W.terminalExp_mem_adjoin_lastInput_initialAnalytic
  have hA : A ≤ N.restrictScalars ℚ := by
    rw [hrestrict]
    exact le_sup_left
  have hpair : IntermediateField.adjoin ℚ ({b, y} : Set ℂ) ≤ N.restrictScalars ℚ := by
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact hbN
    · rcases hx with rfl
      exact hyN
  have hAF : A ≤ F := by
    change A ≤ generatedField u
    rw [W.fullField_eq_initialAnalyticRealCore_sup_lastPair]
    exact le_sup_left
  change N.restrictScalars ℚ = F
  apply le_antisymm
  · rw [hrestrict]
    apply sup_le hAF
    rw [IntermediateField.adjoin_le_iff]
    rintro x (rfl : x = b)
    exact (coordinate u (Fin.last (n + 2))).property
  · change generatedField u ≤ N.restrictScalars ℚ
    rw [W.fullField_eq_initialAnalyticRealCore_sup_lastPair]
    exact sup_le hA hpair

/-- An element whose square belongs to the base field is integral of degree at most two. -/
theorem isIntegral_of_sq_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ) (hx : x ^ 2 ∈ K) :
    IsIntegral K x := by
  let c : K := ⟨x ^ 2, hx⟩
  let p : Polynomial K := Polynomial.X ^ 2 - Polynomial.C c
  have hpmonic : p.Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  have hpeval : Polynomial.aeval x p = 0 := by
    simp [p, c]
  exact ⟨p, hpmonic, hpeval⟩

/-- Adjoining a square root costs degree at most two. -/
theorem finrank_adjoin_le_two_of_sq_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ) (hx : x ^ 2 ∈ K) :
    Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) ≤ 2 := by
  have hint : IsIntegral K x := isIntegral_of_sq_mem K x hx
  let c : K := ⟨x ^ 2, hx⟩
  let p : Polynomial K := Polynomial.X ^ 2 - Polynomial.C c
  have hpmonic : p.Monic := Polynomial.monic_X_pow_sub_C c (by norm_num)
  have hpeval : Polynomial.aeval x p = 0 := by
    simp [p, c]
  have hdvd : minpoly K x ∣ p := minpoly.dvd K x hpeval
  calc
    Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) =
        (minpoly K x).natDegree := IntermediateField.adjoin.finrank hint
    _ ≤ p.natDegree := Polynomial.natDegree_le_of_dvd hdvd hpmonic.ne_zero
    _ = 2 := Polynomial.natDegree_X_pow_sub_C

/-- A square root not already belonging to the base generates an extension of degree exactly
two. -/
theorem finrank_adjoin_eq_two_of_sq_mem_of_not_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ)
    (hx : x ^ 2 ∈ K) (hnot : x ∉ K) :
    Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) = 2 := by
  let N : IntermediateField K ℂ := IntermediateField.adjoin K ({x} : Set ℂ)
  letI : FiniteDimensional K N :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_of_sq_mem K x hx)
  have hpos : 1 ≤ Module.finrank K N := Module.finrank_pos
  have hle : Module.finrank K N ≤ 2 := finrank_adjoin_le_two_of_sq_mem K x hx
  have hne : Module.finrank K N ≠ 1 := by
    intro hone
    have hbot : N = ⊥ := IntermediateField.finrank_eq_one_iff.mp hone
    have hxN : x ∈ N := IntermediateField.subset_adjoin K _ (Set.mem_singleton x)
    rw [hbot, IntermediateField.mem_bot] at hxN
    rcases hxN with ⟨k, hk⟩
    apply hnot
    rw [← hk]
    exact k.property
  change Module.finrank K N = 2
  omega

/-- In a finite tower, total degree four and left degree two force right degree two. -/
theorem finrank_right_eq_two_of_total_eq_four_of_left_eq_two
    (K L E : Type*) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    (hleft : Module.finrank K L = 2)
    (htotal : Module.finrank K E = 4) : Module.finrank L E = 2 := by
  letI : FiniteDimensional K L := FiniteDimensional.of_finrank_eq_succ hleft
  letI : FiniteDimensional K E := FiniteDimensional.of_finrank_eq_succ htotal
  letI : FiniteDimensional L E := FiniteDimensional.right K L E
  have htower : Module.finrank K L * Module.finrank L E = Module.finrank K E :=
    Module.finrank_mul_finrank K L E
  rw [hleft, htotal] at htower
  omega

/-- In a finite tower, a total degree at most two forces the right-hand degree to be at most
two. -/
theorem finrank_right_le_two_of_total_le_two
    (K L E : Type*) [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    [FiniteDimensional K L] [FiniteDimensional L E]
    (htotal : Module.finrank K E ≤ 2) : Module.finrank L E ≤ 2 := by
  have htower : Module.finrank K L * Module.finrank L E = Module.finrank K E :=
    Module.finrank_mul_finrank K L E
  have hleft : 0 < Module.finrank K L := Module.finrank_pos
  calc
    Module.finrank L E ≤ Module.finrank K L * Module.finrank L E :=
      Nat.le_mul_of_pos_left _ hleft
    _ = Module.finrank K E := htower
    _ ≤ 2 := htotal

/-- Canonical inclusion algebras attached to three nested intermediate fields form a scalar
tower.  Keeping this variable-level fact separate prevents large concrete field expressions
from being duplicated in kernel proof terms. -/
theorem isScalarTower_intermediateField_inclusions
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    (K L N : IntermediateField F E)
    (hKL : K ≤ L) (hLN : L ≤ N) (hKN : K ≤ N) :
    letI : Algebra K L :=
      (IntermediateField.inclusion hKL).toRingHom.toAlgebra
    letI : Algebra L N :=
      (IntermediateField.inclusion hLN).toRingHom.toAlgebra
    letI : Algebra K N :=
      (IntermediateField.inclusion hKN).toRingHom.toAlgebra
    IsScalarTower K L N := by
  letI : Algebra K L :=
    (IntermediateField.inclusion hKL).toRingHom.toAlgebra
  letI : Algebra L N :=
    (IntermediateField.inclusion hLN).toRingHom.toAlgebra
  letI : Algebra K N :=
    (IntermediateField.inclusion hKN).toRingHom.toAlgebra
  apply IsScalarTower.of_algebraMap_eq'
  ext x
  rfl

/-- A nonzero element whose sum with its inverse belongs to the base field is integral of degree
at most two. -/
theorem isIntegral_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ) (hx0 : x ≠ 0)
    (htrace : x + x⁻¹ ∈ K) : IsIntegral K x := by
  let c : K := ⟨x + x⁻¹, htrace⟩
  let p : Polynomial K :=
    Polynomial.X ^ 2 - Polynomial.C c * Polynomial.X + Polynomial.C 1
  have hpdegree : Polynomial.IsMonicOfDegree p 2 := by
    exact Polynomial.isMonicOfDegree_sub_add_two c 1
  have hpeval : Polynomial.aeval x p = 0 := by
    simp [p, c, add_mul, hx0]
    ring
  exact ⟨p, hpdegree.monic, hpeval⟩

/-- In a field, a nonzero element is determined up to inversion by its reciprocal trace. -/
theorem eq_or_eq_inv_of_add_inv_eq
    {K : Type*} [Field K] {x y : K} (hx : x ≠ 0) (hy : y ≠ 0)
    (h : x + x⁻¹ = y + y⁻¹) : x = y ∨ x = y⁻¹ := by
  have hprod : (x - y) * (x * y - 1) = 0 := by
    calc
      (x - y) * (x * y - 1) =
          (x + x⁻¹ - (y + y⁻¹)) * (x * y) := by
            field_simp [hx, hy]
            all_goals ring
      _ = 0 := by rw [h]; simp
  rcases mul_eq_zero.mp hprod with hxy | hxy
  · exact Or.inl (sub_eq_zero.mp hxy)
  · exact Or.inr (eq_inv_of_mul_eq_one_left (sub_eq_zero.mp hxy))

/-- Adjoining a nonzero element whose sum with its inverse is already in the base costs degree
at most two. -/
theorem finrank_adjoin_le_two_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ) (hx0 : x ≠ 0)
    (htrace : x + x⁻¹ ∈ K) :
    Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) ≤ 2 := by
  have hint : IsIntegral K x := isIntegral_of_add_inv_mem K x hx0 htrace
  let c : K := ⟨x + x⁻¹, htrace⟩
  let p : Polynomial K :=
    Polynomial.X ^ 2 - Polynomial.C c * Polynomial.X + Polynomial.C 1
  have hpdegree : Polynomial.IsMonicOfDegree p 2 := by
    exact Polynomial.isMonicOfDegree_sub_add_two c 1
  have hpeval : Polynomial.aeval x p = 0 := by
    simp [p, c, add_mul, hx0]
    ring
  have hdvd : minpoly K x ∣ p := minpoly.dvd K x hpeval
  calc
    Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) =
        (minpoly K x).natDegree := IntermediateField.adjoin.finrank hint
    _ ≤ p.natDegree :=
      Polynomial.natDegree_le_of_dvd hdvd hpdegree.monic.ne_zero
    _ = 2 := hpdegree.natDegree_eq

/-- A square root and a reciprocal-trace root together cost degree at most four. -/
theorem finrank_adjoin_pair_le_four_of_sq_mem_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K) :
    Module.finrank K (IntermediateField.adjoin K ({x, y} : Set ℂ)) ≤ 4 := by
  have hxdeg := finrank_adjoin_le_two_of_sq_mem K x hx
  have hydeg := finrank_adjoin_le_two_of_add_inv_mem K y hy0 hy
  have hpair : IntermediateField.adjoin K ({x, y} : Set ℂ) =
      IntermediateField.adjoin K ({x} : Set ℂ) ⊔
        IntermediateField.adjoin K ({y} : Set ℂ) := by
    rw [← IntermediateField.adjoin_union]
    congr 1
  rw [hpair]
  calc
    Module.finrank K
        (↥(IntermediateField.adjoin K ({x} : Set ℂ) ⊔
          IntermediateField.adjoin K ({y} : Set ℂ))) ≤
        Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) *
          Module.finrank K (IntermediateField.adjoin K ({y} : Set ℂ)) :=
      IntermediateField.finrank_sup_le
        (IntermediateField.adjoin K ({x} : Set ℂ))
        (IntermediateField.adjoin K ({y} : Set ℂ))
    _ ≤ 2 * 2 := Nat.mul_le_mul hxdeg hydeg
    _ = 4 := by norm_num

/-- The compositum of the displayed two quadratic simple extensions has degree exactly one, two,
or four; the coarse upper bound cannot hide a cubic extension. -/
theorem finrank_adjoin_pair_eq_one_or_two_or_four_of_sq_mem_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K) :
    Module.finrank K (IntermediateField.adjoin K ({x, y} : Set ℂ)) = 1 ∨
      Module.finrank K (IntermediateField.adjoin K ({x, y} : Set ℂ)) = 2 ∨
      Module.finrank K (IntermediateField.adjoin K ({x, y} : Set ℂ)) = 4 := by
  let E : IntermediateField K ℂ := IntermediateField.adjoin K ({x} : Set ℂ)
  let N : IntermediateField E ℂ := IntermediateField.adjoin E ({y} : Set ℂ)
  let L : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
  letI : Algebra K N :=
    ((algebraMap E N).comp (algebraMap K E)).toAlgebra
  letI : IsScalarTower K E N := by
    apply IsScalarTower.of_algebraMap_eq
    intro z
    rfl
  have hyE : y + y⁻¹ ∈ E := by
    exact E.algebraMap_mem ⟨y + y⁻¹, hy⟩
  letI : FiniteDimensional K E :=
    IntermediateField.adjoin.finiteDimensional (isIntegral_of_sq_mem K x hx)
  letI : FiniteDimensional E N :=
    IntermediateField.adjoin.finiteDimensional
      (isIntegral_of_add_inv_mem E y hy0 hyE)
  have hxpos : 1 ≤ Module.finrank K E := Module.finrank_pos
  have hxle : Module.finrank K E ≤ 2 := finrank_adjoin_le_two_of_sq_mem K x hx
  have hypos : 1 ≤ Module.finrank E N := Module.finrank_pos
  have hyle : Module.finrank E N ≤ 2 :=
    finrank_adjoin_le_two_of_add_inv_mem E y hy0 hyE
  have htower :
      Module.finrank K E * Module.finrank E N = Module.finrank K N :=
    Module.finrank_mul_finrank K E N
  have hNL : N.restrictScalars K = L := by
    calc
      N.restrictScalars K = E ⊔ IntermediateField.adjoin K ({y} : Set ℂ) :=
        IntermediateField.restrictScalars_adjoin_eq_sup K E ({y} : Set ℂ)
      _ = L := by
        change IntermediateField.adjoin K ({x} : Set ℂ) ⊔
            IntermediateField.adjoin K ({y} : Set ℂ) =
          IntermediateField.adjoin K ({x, y} : Set ℂ)
        rw [← IntermediateField.adjoin_union]
        congr 1
  have hfin : Module.finrank K N = Module.finrank K L :=
    (IntermediateField.equivOfEq hNL).toLinearEquiv.finrank_eq
  have hxcase : Module.finrank K E = 1 ∨ Module.finrank K E = 2 := by
    omega
  have hycase : Module.finrank E N = 1 ∨ Module.finrank E N = 2 := by
    omega
  have hdegree : Module.finrank K L =
      Module.finrank K E * Module.finrank E N :=
    hfin.symm.trans htower.symm
  change Module.finrank K L = 1 ∨ Module.finrank K L = 2 ∨
    Module.finrank K L = 4
  rcases hxcase with hxone | hxtwo
  · rcases hycase with hyone | hytwo
    · exact Or.inl (hdegree.trans (by rw [hxone, hyone]))
    · exact Or.inr (Or.inl (hdegree.trans (by rw [hxone, hytwo])))
  · rcases hycase with hyone | hytwo
    · exact Or.inr (Or.inl (hdegree.trans (by rw [hxtwo, hyone])))
    · exact Or.inr (Or.inr (hdegree.trans (by rw [hxtwo, hytwo])))

/-- A finite simple extension of degree at most two is normal.  This formulation includes both
the trivial and genuinely quadratic cases. -/
theorem normal_adjoin_simple_of_finrank_le_two
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ) (hint : IsIntegral K x)
    (hdegree : Module.finrank K (IntermediateField.adjoin K ({x} : Set ℂ)) ≤ 2) :
    Normal K (IntermediateField.adjoin K ({x} : Set ℂ)) := by
  let E : IntermediateField K ℂ := IntermediateField.adjoin K ({x} : Set ℂ)
  change Normal K E
  letI : FiniteDimensional K E := IntermediateField.adjoin.finiteDimensional hint
  have hdegreeE : Module.finrank K E ≤ 2 := hdegree
  have hpos : 1 ≤ Module.finrank K E := Module.finrank_pos
  have hcase : Module.finrank K E = 1 ∨ Module.finrank K E = 2 := by
    omega
  rcases hcase with hone | htwo
  · have hbot : E = ⊥ := IntermediateField.finrank_eq_one_iff.mp hone
    rw [hbot]
    infer_instance
  · letI : Algebra.IsQuadraticExtension K E := ⟨htwo⟩
    infer_instance

/-- The field generated by the square-root and reciprocal-trace reconstructions is normal over
the base: it is a compositum of two trivial-or-quadratic normal extensions. -/
theorem normal_adjoin_pair_of_sq_mem_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K) :
    Normal K (IntermediateField.adjoin K ({x, y} : Set ℂ)) := by
  let E₁ : IntermediateField K ℂ := IntermediateField.adjoin K ({x} : Set ℂ)
  let E₂ : IntermediateField K ℂ := IntermediateField.adjoin K ({y} : Set ℂ)
  let L : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
  letI : Normal K E₁ := normal_adjoin_simple_of_finrank_le_two K x
    (isIntegral_of_sq_mem K x hx) (finrank_adjoin_le_two_of_sq_mem K x hx)
  letI : Normal K E₂ := normal_adjoin_simple_of_finrank_le_two K y
    (isIntegral_of_add_inv_mem K y hy0 hy)
    (finrank_adjoin_le_two_of_add_inv_mem K y hy0 hy)
  have hpair : E₁ ⊔ E₂ = L := by
    change IntermediateField.adjoin K ({x} : Set ℂ) ⊔
        IntermediateField.adjoin K ({y} : Set ℂ) =
      IntermediateField.adjoin K ({x, y} : Set ℂ)
    rw [← IntermediateField.adjoin_union]
    congr 1
  exact Normal.of_algEquiv (IntermediateField.equivOfEq hpair)

/-- The two quadratic reconstruction equations define a finite Galois extension of degree one,
two, or four. -/
theorem isGalois_adjoin_pair_of_sq_mem_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K) :
    IsGalois K (IntermediateField.adjoin K ({x, y} : Set ℂ)) := by
  let L : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
  letI : FiniteDimensional K L := IntermediateField.finiteDimensional_adjoin_pair
    (isIntegral_of_sq_mem K x hx)
    (isIntegral_of_add_inv_mem K y hy0 hy)
  letI : Normal K L := normal_adjoin_pair_of_sq_mem_of_add_inv_mem K x y hx hy0 hy
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

/-- Every relative automorphism of the square-root/reciprocal-trace reconstruction field is an
involution.  It acts on the two generators by independent choices from `x ↦ ±x` and
`y ↦ y or y⁻¹`. -/
theorem galoisGroup_adjoin_pair_exponent_two_of_sq_mem_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K) :
    ∀ σ : Gal((IntermediateField.adjoin K ({x, y} : Set ℂ))/K), σ * σ = 1 := by
  let N : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
  let xN : N := ⟨x, IntermediateField.subset_adjoin K _
    (Set.mem_insert x {y})⟩
  let yN : N := ⟨y, IntermediateField.subset_adjoin K _
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩
  intro σ
  have hxsquare : (σ xN) ^ 2 = xN ^ 2 := by
    calc
      (σ xN) ^ 2 = σ (xN ^ 2) := by rw [map_pow]
      _ = σ (algebraMap K N (⟨x ^ 2, hx⟩ : K)) := by rfl
      _ = algebraMap K N (⟨x ^ 2, hx⟩ : K) := σ.commutes _
      _ = xN ^ 2 := by rfl
  have hxcase : σ xN = xN ∨ σ xN = -xN :=
    eq_or_eq_neg_of_sq_eq_sq (σ xN) xN hxsquare
  have hxx : σ (σ xN) = xN := by
    rcases hxcase with h | h <;> simp [h]
  have hyN0 : yN ≠ 0 := by
    intro h
    exact hy0 (congrArg Subtype.val h)
  have htrace : σ yN + (σ yN)⁻¹ = yN + yN⁻¹ := by
    calc
      σ yN + (σ yN)⁻¹ = σ (yN + yN⁻¹) := by simp
      _ = σ (algebraMap K N (⟨y + y⁻¹, hy⟩ : K)) := by rfl
      _ = algebraMap K N (⟨y + y⁻¹, hy⟩ : K) := σ.commutes _
      _ = yN + yN⁻¹ := by rfl
  have hycase : σ yN = yN ∨ σ yN = yN⁻¹ :=
    eq_or_eq_inv_of_add_inv_eq ((map_ne_zero σ).mpr hyN0) hyN0 htrace
  have hyy : σ (σ yN) = yN := by
    rcases hycase with h | h <;> simp [h]
  apply AlgEquiv.ext
  intro a
  apply IntermediateField.adjoin_induction K
    (p := fun z hz ↦ (σ * σ) (⟨z, hz⟩ : N) = ⟨z, hz⟩)
  · intro z hz
    rcases hz with rfl | hz
    · exact hxx
    · rcases hz with rfl
      exact hyy
  · intro z
    change σ (σ (algebraMap K N z)) = algebraMap K N z
    rw [σ.commutes, σ.commutes]
  · intro a b haMem hbMem ha hb
    change σ (σ (⟨a, haMem⟩ : N)) = ⟨a, haMem⟩ at ha
    change σ (σ (⟨b, hbMem⟩ : N)) = ⟨b, hbMem⟩ at hb
    change σ (σ ((⟨a, haMem⟩ : N) + ⟨b, hbMem⟩)) =
      (⟨a, haMem⟩ : N) + ⟨b, hbMem⟩
    rw [map_add, map_add, ha, hb]
  · intro a haMem ha
    change σ (σ (⟨a, haMem⟩ : N)) = ⟨a, haMem⟩ at ha
    change σ (σ ((⟨a, haMem⟩ : N)⁻¹)) = (⟨a, haMem⟩ : N)⁻¹
    rw [map_inv₀, map_inv₀, ha]
  · intro a b haMem hbMem ha hb
    change σ (σ (⟨a, haMem⟩ : N)) = ⟨a, haMem⟩ at ha
    change σ (σ (⟨b, hbMem⟩ : N)) = ⟨b, hbMem⟩ at hb
    change σ (σ ((⟨a, haMem⟩ : N) * ⟨b, hbMem⟩)) =
      (⟨a, haMem⟩ : N) * ⟨b, hbMem⟩
    rw [map_mul, map_mul, ha, hb]

/-- Two relative automorphisms of a one-generator adjoin field agree once they agree on the
displayed generator. -/
theorem galoisGroup_adjoin_single_ext
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x : ℂ)
    {σ τ : Gal((IntermediateField.adjoin K ({x} : Set ℂ))/K)}
    (hx : σ ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_singleton x)⟩ =
      τ ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_singleton x)⟩) : σ = τ := by
  apply AlgEquiv.ext
  intro a
  have hhom : σ.toAlgHom = τ.toAlgHom := by
    apply IntermediateField.adjoin_algHom_ext K
    intro z hz
    rcases hz with rfl
    exact hx
  exact DFunLike.congr_fun hhom a

/-- Two relative automorphisms of a two-generator adjoin field agree once they agree on both
displayed generators. -/
theorem galoisGroup_adjoin_pair_ext
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    {σ τ : Gal((IntermediateField.adjoin K ({x, y} : Set ℂ))/K)}
    (hx : σ ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_insert x {y})⟩ =
      τ ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_insert x {y})⟩)
    (hy : σ ⟨y, IntermediateField.subset_adjoin K _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩ =
      τ ⟨y, IntermediateField.subset_adjoin K _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩) : σ = τ := by
  let N : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
  apply AlgEquiv.ext
  intro a
  apply IntermediateField.adjoin_induction K
    (p := fun z hz ↦ σ (⟨z, hz⟩ : N) = τ ⟨z, hz⟩)
  · intro z hz
    rcases hz with rfl | hz
    · exact hx
    · rcases hz with rfl
      exact hy
  · intro z
    change σ (algebraMap K N z) = τ (algebraMap K N z)
    rw [σ.commutes, τ.commutes]
  · intro a b haMem hbMem ha hb
    change σ ((⟨a, haMem⟩ : N) + ⟨b, hbMem⟩) =
      τ ((⟨a, haMem⟩ : N) + ⟨b, hbMem⟩)
    rw [map_add, map_add, ha, hb]
  · intro a haMem ha
    change σ ((⟨a, haMem⟩ : N)⁻¹) = τ ((⟨a, haMem⟩ : N)⁻¹)
    rw [map_inv₀, map_inv₀, ha]
  · intro a b haMem hbMem ha hb
    change σ ((⟨a, haMem⟩ : N) * ⟨b, hbMem⟩) =
      τ ((⟨a, haMem⟩ : N) * ⟨b, hbMem⟩)
    rw [map_mul, map_mul, ha, hb]

/-- In the degree-four case, the two generator actions give all four possible sign codes.  Thus
the Galois group is identified set-theoretically with the independent choices `x ↦ x or -x` and
`y ↦ y or y⁻¹`. -/
theorem galoisGroup_adjoin_pair_signMap_bijective_of_finrank_eq_four
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K)
    (hdegree : Module.finrank K
      (IntermediateField.adjoin K ({x, y} : Set ℂ)) = 4) :
    let N : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
    let xN : N := ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_insert x {y})⟩
    let yN : N := ⟨y, IntermediateField.subset_adjoin K _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩
    Function.Bijective (fun σ : Gal(N/K) ↦
      (decide (σ xN = xN), decide (σ yN = yN))) := by
  classical
  dsimp only
  let N : IntermediateField K ℂ := IntermediateField.adjoin K ({x, y} : Set ℂ)
  let xN : N := ⟨x, IntermediateField.subset_adjoin K _ (Set.mem_insert x {y})⟩
  let yN : N := ⟨y, IntermediateField.subset_adjoin K _
    (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩
  have hx_cases (σ : Gal(N/K)) : σ xN = xN ∨ σ xN = -xN := by
    apply eq_or_eq_neg_of_sq_eq_sq
    calc
      (σ xN) ^ 2 = σ (xN ^ 2) := by simp
      _ = σ (algebraMap K N (⟨x ^ 2, hx⟩ : K)) := by rfl
      _ = algebraMap K N (⟨x ^ 2, hx⟩ : K) := σ.commutes _
      _ = xN ^ 2 := by rfl
  have hyN0 : yN ≠ 0 := by
    intro h
    exact hy0 (congrArg Subtype.val h)
  have hy_cases (σ : Gal(N/K)) : σ yN = yN ∨ σ yN = yN⁻¹ := by
    apply eq_or_eq_inv_of_add_inv_eq ((map_ne_zero σ).mpr hyN0) hyN0
    calc
      σ yN + (σ yN)⁻¹ = σ (yN + yN⁻¹) := by simp
      _ = σ (algebraMap K N (⟨y + y⁻¹, hy⟩ : K)) := by rfl
      _ = algebraMap K N (⟨y + y⁻¹, hy⟩ : K) := σ.commutes _
      _ = yN + yN⁻¹ := by rfl
  let signMap : Gal(N/K) → Bool × Bool := fun σ ↦
    (decide (σ xN = xN), decide (σ yN = yN))
  have hinjective : Function.Injective signMap := by
    intro σ τ hsign
    have hxsign := congrArg Prod.fst hsign
    have hysign := congrArg Prod.snd hsign
    have hxeq : σ xN = τ xN := by
      by_cases hσ : σ xN = xN
      · by_cases hτ : τ xN = xN
        · exact hσ.trans hτ.symm
        · simp [signMap, hσ, hτ] at hxsign
      · by_cases hτ : τ xN = xN
        · simp [signMap, hσ, hτ] at hxsign
        · rcases hx_cases σ with hσ' | hσ'
          · exact False.elim (hσ hσ')
          · rcases hx_cases τ with hτ' | hτ'
            · exact False.elim (hτ hτ')
            · exact hσ'.trans hτ'.symm
    have hyeq : σ yN = τ yN := by
      by_cases hσ : σ yN = yN
      · by_cases hτ : τ yN = yN
        · exact hσ.trans hτ.symm
        · simp [signMap, hσ, hτ] at hysign
      · by_cases hτ : τ yN = yN
        · simp [signMap, hσ, hτ] at hysign
        · rcases hy_cases σ with hσ' | hσ'
          · exact False.elim (hσ hσ')
          · rcases hy_cases τ with hτ' | hτ'
            · exact False.elim (hτ hτ')
            · exact hσ'.trans hτ'.symm
    exact galoisGroup_adjoin_pair_ext K x y hxeq hyeq
  letI : FiniteDimensional K N := IntermediateField.finiteDimensional_adjoin_pair
    (isIntegral_of_sq_mem K x hx)
    (isIntegral_of_add_inv_mem K y hy0 hy)
  letI : IsGalois K N :=
    isGalois_adjoin_pair_of_sq_mem_of_add_inv_mem K x y hx hy0 hy
  have hcard : Nat.card Gal(N/K) = 4 :=
    (IsGalois.card_aut_eq_finrank K N).trans hdegree
  have htarget : Nat.card (Bool × Bool) = 4 := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_bool]
  exact hinjective.bijective_of_nat_card_le (by rw [htarget, hcard])

/-- A group in which every element has square one is commutative. -/
theorem isMulCommutative_of_mul_self_eq_one
    {G : Type*} [Group G] (h : ∀ g : G, g * g = 1) : IsMulCommutative G := by
  refine ⟨⟨fun (a b : G) ↦ ?_⟩⟩
  have ha : a = a⁻¹ := eq_inv_of_mul_eq_one_left (h a)
  have hb : b = b⁻¹ := eq_inv_of_mul_eq_one_left (h b)
  calc
    a * b = (a * b)⁻¹ := eq_inv_of_mul_eq_one_left (h (a * b))
    _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [← hb, ← ha]

/-- The relative Galois group of the two quadratic reconstruction field is commutative (indeed,
every element is an involution). -/
theorem isMulCommutative_galoisGroup_adjoin_pair_of_sq_mem_of_add_inv_mem
    {F : Type*} [Field F] [Algebra F ℂ]
    (K : IntermediateField F ℂ) (x y : ℂ)
    (hx : x ^ 2 ∈ K) (hy0 : y ≠ 0) (hy : y + y⁻¹ ∈ K) :
    IsMulCommutative Gal((IntermediateField.adjoin K ({x, y} : Set ℂ))/K) :=
  isMulCommutative_of_mul_self_eq_one
    (galoisGroup_adjoin_pair_exponent_two_of_sq_mem_of_add_inv_mem
      K x y hx hy0 hy)

/-- The explicit quadratic reconstruction field restricts back to the full terminal graph field. -/
theorem PositiveEigenvectorTerminalWitness.restrictScalars_adjoin_lastPair_eq_fullField
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    (IntermediateField.adjoin M
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} :
        Set ℂ)).restrictScalars ℚ = generatedField u := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let S : Set ℂ :=
    {u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))}
  change (IntermediateField.adjoin M S).restrictScalars ℚ = generatedField u
  calc
    (IntermediateField.adjoin M S).restrictScalars ℚ =
        M ⊔ IntermediateField.adjoin ℚ S :=
      IntermediateField.restrictScalars_adjoin_eq_sup ℚ M S
    _ = generatedField u := W.fullField_eq_initialRealCore_sup_lastPair.symm

/-- Quantitative lossless real-shadow reconstruction: over the prefix joined with the
pointwise-real terminal core, recovering the final input and exponential costs degree at most
four. -/
theorem PositiveEigenvectorTerminalWitness.finrank_adjoin_lastPair_le_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (_W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    Module.finrank M (IntermediateField.adjoin M
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} :
        Set ℂ)) ≤ 4 := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2)
        {Complex.exp b + (Complex.exp b)⁻¹})
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  exact finrank_adjoin_pair_le_four_of_sq_mem_of_add_inv_mem
    M b y hb2 (Complex.exp_ne_zero b) hytrace

/-- Adjoining the pointwise-real terminal core to the prefix costs no absolute transcendence
degree. -/
theorem PositiveEigenvectorTerminalWitness.trdeg_initial_sup_terminalRealCore_eq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Algebra.trdeg ℚ
      (↥(generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u)) =
        (((n + 2 : ℕ) : Cardinal)) := by
  let K := generatedField (Fin.init u)
  let S : Set ℂ :=
    {u (Fin.last (n + 2)) ^ 2,
      Complex.exp (u (Fin.last (n + 2))) +
        (Complex.exp (u (Fin.last (n + 2))))⁻¹}
  let L : IntermediateField K ℂ := IntermediateField.adjoin K S
  letI : Algebra.IsAlgebraic K L := by
    apply IntermediateField.isAlgebraic_adjoin
    intro x hx
    rcases hx with rfl | hx
    · exact W.last_sq_isAlgebraic.isIntegral
    · rcases hx with rfl
      exact W.last_exp_trace_isAlgebraic.isIntegral
  letI : IsScalarTower ℚ K L := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have htower : Algebra.trdeg ℚ K + Algebra.trdeg K L = Algebra.trdeg ℚ L :=
    trdeg_add_eq ℚ K
  have hrel : Algebra.trdeg K L = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at htower
  have hL : L.restrictScalars ℚ = K ⊔ eigenvectorTerminalRealCore u := by
    calc
      L.restrictScalars ℚ = K ⊔ IntermediateField.adjoin ℚ S :=
        IntermediateField.restrictScalars_adjoin_eq_sup ℚ K S
      _ = K ⊔ eigenvectorTerminalRealCore u := by
        rfl
  have heq := (IntermediateField.equivOfEq hL).trdeg_eq
  exact (heq.symm.trans htower.symm).trans W.initialSharp

/-- The prefix joined with the terminal real core is literally an intermediate field of the
full terminal graph field. -/
theorem PositiveEigenvectorTerminalWitness.initial_sup_terminalRealCore_le_full
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u ≤ generatedField u := by
  rw [W.fullField_eq_initialRealCore_sup_lastPair]
  exact le_sup_left

/-- Adjoining the mixed invariant over the original real-shadow base has underlying rational
carrier equal to the prefix joined with the analytic real core. -/
theorem restrictScalars_adjoin_terminalCrossInvariant_eq_initialAnalyticRealCore
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    (IntermediateField.adjoin M
      ({eigenvectorTerminalCrossInvariant u} : Set ℂ)).restrictScalars ℚ =
        generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u := by
  let K := generatedField (Fin.init u)
  let C := eigenvectorTerminalRealCore u
  let D := IntermediateField.adjoin ℚ
    ({eigenvectorTerminalCrossInvariant u} : Set ℂ)
  let M := K ⊔ C
  calc
    (IntermediateField.adjoin M
        ({eigenvectorTerminalCrossInvariant u} : Set ℂ)).restrictScalars ℚ =
        M ⊔ D := IntermediateField.restrictScalars_adjoin_eq_sup ℚ M _
    _ = K ⊔ (C ⊔ D) := sup_assoc K C D
    _ = generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u := by
      rfl

/-- The prefix joined with the analytic real core is literally contained in the full graph
field. -/
theorem PositiveEigenvectorTerminalWitness.initial_sup_analyticRealCore_le_full
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u ≤
      generatedField u := by
  rw [W.fullField_eq_initialAnalyticRealCore_sup_lastPair]
  exact le_sup_left

/-- The canonical inclusion algebra from the original terminal real-shadow field to its
analytic enlargement.  Naming this structure keeps later concrete tower terms small. -/
@[implicit_reducible] noncomputable def terminalInitialRealToAnalyticAlgebra
    {n : ℕ} (u : Fin (n + 3) → ℂ) :
    Algebra
      (generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u :
        IntermediateField ℚ ℂ)
      (generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u :
        IntermediateField ℚ ℂ) :=
  (IntermediateField.inclusion
    (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra

/-- The canonical inclusion algebra from the analytic terminal real-shadow field to the full
terminal graph field. -/
@[implicit_reducible] noncomputable def
    PositiveEigenvectorTerminalWitness.terminalInitialAnalyticToFullAlgebra
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Algebra
      (generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u :
        IntermediateField ℚ ℂ)
      (generatedField u) :=
  (IntermediateField.inclusion
    W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra

/-- The canonical inclusion algebra from the original terminal real-shadow field to the full
terminal graph field. -/
@[implicit_reducible] noncomputable def
    PositiveEigenvectorTerminalWitness.terminalInitialRealToFullAlgebra
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Algebra
      (generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u :
        IntermediateField ℚ ℂ)
      (generatedField u) :=
  (IntermediateField.inclusion
    W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra

/-- The full graph field remains algebraic over the prefix joined with its pointwise-real
terminal core. -/
theorem PositiveEigenvectorTerminalWitness.fullAlgebraic_initial_sup_terminalRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic M (generatedField u) := by
  let K := generatedField (Fin.init u)
  let M := K ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra K M :=
    (IntermediateField.inclusion (show K ≤ M from le_sup_left)).toRingHom.toRatAlgHom.toAlgebra
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : Algebra K F :=
    (IntermediateField.inclusion W.initialField_le).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower K M F := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  letI : Algebra.IsAlgebraic K F := W.fullAlgebraic
  exact Algebra.IsAlgebraic.tower_top (K := K) M

/-- Conditional on independence of `(pi^2,e)`, adjoining the final pointwise-real core preserves
the exact relative degree `n` over the real anchor. -/
theorem PositiveEigenvectorTerminalWitness.relative_trdeg_initialRealCore_realAnchor_eq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra realAnchorField M :=
      (IntermediateField.inclusion
        (W.realAnchorField_le_initial.trans le_sup_left)).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField M = ((n : ℕ) : Cardinal) := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  letI : Algebra realAnchorField M :=
    (IntermediateField.inclusion
      (W.realAnchorField_le_initial.trans le_sup_left)).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField M := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ realAnchorField (A := M)
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    W.trdeg_initial_sup_terminalRealCore_eq] at hadd
  have hcancel : Algebra.trdeg realAnchorField M + 2 = (n : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField M + 2 =
          2 + Algebra.trdeg realAnchorField M := add_comm _ _
      _ = (((n + 2 : ℕ) : Cardinal)) := hadd
      _ = (n : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- The quadratic reconstruction field and the actual full graph field are algebra-equivalent
over the prefix joined with the pointwise-real terminal core. -/
noncomputable def PositiveEigenvectorTerminalWitness.terminalRealCoreFullAlgEquiv
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    IntermediateField.adjoin M
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) ≃ₐ[M]
        generatedField u := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hN : N.restrictScalars ℚ = F := by
    exact W.restrictScalars_adjoin_lastPair_eq_fullField
  let e : N ≃ₐ[M] F :=
    { toFun := fun x ↦
        ⟨x, by
          have hx : (x : ℂ) ∈ N.restrictScalars ℚ := x.property
          rw [hN] at hx
          exact hx⟩
      invFun := fun x ↦
        ⟨x, by
          let z : ℂ := x
          have hx : z ∈ F := x.property
          rw [← hN] at hx
          exact hx⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact e

/-- Adjoining the mixed invariant over the original real-shadow base is algebra-equivalent to
the literal prefix joined with the analytic real core. -/
noncomputable def PositiveEigenvectorTerminalWitness.terminalCrossAnalyticRealCoreAlgEquiv
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (_W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    IntermediateField.adjoin M
      ({eigenvectorTerminalCrossInvariant u} : Set ℂ) ≃ₐ[M] A := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M
    ({eigenvectorTerminalCrossInvariant u} : Set ℂ)
  letI : Algebra M A :=
    (IntermediateField.inclusion
      (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
  have hN : N.restrictScalars ℚ = A :=
    restrictScalars_adjoin_terminalCrossInvariant_eq_initialAnalyticRealCore u
  let e : N ≃ₐ[M] A :=
    { toFun := fun x ↦
        ⟨x, by
          have hx : (x : ℂ) ∈ N.restrictScalars ℚ := x.property
          rw [hN] at hx
          exact hx⟩
      invFun := fun x ↦
        ⟨x, by
          let z : ℂ := x
          have hx : z ∈ A := x.property
          rw [← hN] at hx
          exact hx⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact e

/-- Adjoining only the last input over the analytic real shadow is algebra-equivalent to the
literal full terminal graph field. -/
noncomputable def PositiveEigenvectorTerminalWitness.terminalAnalyticLastInputFullAlgEquiv
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    IntermediateField.adjoin A ({u (Fin.last (n + 2))} : Set ℂ) ≃ₐ[A]
      generatedField u := by
  let b := u (Fin.last (n + 2))
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  let N : IntermediateField A ℂ := IntermediateField.adjoin A ({b} : Set ℂ)
  letI : Algebra A F :=
    (IntermediateField.inclusion
      W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hN : N.restrictScalars ℚ = F :=
    W.restrictScalars_adjoin_lastInput_eq_fullField
  let e : N ≃ₐ[A] F :=
    { toFun := fun x ↦
        ⟨x, by
          have hx : (x : ℂ) ∈ N.restrictScalars ℚ := x.property
          rw [hN] at hx
          exact hx⟩
      invFun := fun x ↦
        ⟨x, by
          let z : ℂ := x
          have hx : z ∈ F := x.property
          rw [← hN] at hx
          exact hx⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      commutes' := fun _ ↦ rfl }
  exact e

/-- The analytic real-shadow enlargement is always finite-dimensional over the original
separate square/trace shadow. -/
theorem PositiveEigenvectorTerminalWitness.finiteDimensional_initialAnalytic_over_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    FiniteDimensional M A := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M
    ({eigenvectorTerminalCrossInvariant u} : Set ℂ)
  letI : Algebra M A :=
    (IntermediateField.inclusion
      (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
  have hsq : eigenvectorTerminalCrossInvariant u ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact terminalCrossInvariant_sq_mem_realCore u
  letI : FiniteDimensional M N :=
    IntermediateField.adjoin.finiteDimensional
      (isIntegral_of_sq_mem M (eigenvectorTerminalCrossInvariant u) hsq)
  exact W.terminalCrossAnalyticRealCoreAlgEquiv.toLinearEquiv.finiteDimensional

/-- The analytic real-shadow enlargement is algebraic over the original real shadow. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalyticRealCoreAlgebraic_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic M A := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  letI : Algebra M A :=
    (IntermediateField.inclusion
      (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
  letI : FiniteDimensional M A :=
    W.finiteDimensional_initialAnalytic_over_initialRealCore
  exact Algebra.IsAlgebraic.of_finite M A

/-- Adding the mixed analytic invariant changes no absolute transcendence degree. -/
theorem PositiveEigenvectorTerminalWitness.trdeg_initial_sup_terminalAnalyticRealCore_eq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    Algebra.trdeg ℚ
      (↥(generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u)) =
        (((n + 2 : ℕ) : Cardinal)) := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  letI : Algebra M A :=
    (IntermediateField.inclusion
      (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ M A := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  letI : Algebra.IsAlgebraic M A :=
    W.initialAnalyticRealCoreAlgebraic_initialRealCore
  have hadd : Algebra.trdeg ℚ M + Algebra.trdeg M A = Algebra.trdeg ℚ A :=
    trdeg_add_eq ℚ M
  have hrel : Algebra.trdeg M A = 0 := trdeg_eq_zero
  rw [hrel, add_zero] at hadd
  exact hadd.symm.trans W.trdeg_initial_sup_terminalRealCore_eq

/-- Conditional on independence of `(pi^2,e)`, the analytic real-shadow field has the same
exact real-anchor relative transcendence degree `n` as the original real shadow. -/
theorem PositiveEigenvectorTerminalWitness.relative_trdeg_initialAnalyticRealCore_realAnchor_eq
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra realAnchorField A :=
      (IntermediateField.inclusion
        (W.realAnchorField_le_initial.trans le_sup_left)).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField A = ((n : ℕ) : Cardinal) := by
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  letI : Algebra realAnchorField A :=
    (IntermediateField.inclusion
      (W.realAnchorField_le_initial.trans le_sup_left)).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField A := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ realAnchorField (A := A)
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    W.trdeg_initial_sup_terminalAnalyticRealCore_eq] at hadd
  have hcancel : Algebra.trdeg realAnchorField A + 2 = (n : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField A + 2 =
          2 + Algebra.trdeg realAnchorField A := add_comm _ _
      _ = (((n + 2 : ℕ) : Cardinal)) := hadd
      _ = (n : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- The linear equivalence underlying the exact terminal real-shadow algebra equivalence. -/
noncomputable def PositiveEigenvectorTerminalWitness.terminalRealCoreFullLinearEquiv
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    IntermediateField.adjoin M
      ({u (Fin.last (n + 2)), Complex.exp (u (Fin.last (n + 2)))} : Set ℂ) ≃ₗ[M]
        generatedField u := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  letI : Algebra M (generatedField u) :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  exact W.terminalRealCoreFullAlgEquiv.toLinearEquiv

/-- The actual full terminal graph field is finite-dimensional over the prefix joined with the
pointwise-real terminal core. -/
theorem PositiveEigenvectorTerminalWitness.finiteDimensional_full_over_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    FiniteDimensional M (generatedField u) := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  letI : FiniteDimensional M N := by
    exact IntermediateField.finiteDimensional_adjoin_pair
      (isIntegral_of_sq_mem M b hb2)
      (isIntegral_of_add_inv_mem M y (Complex.exp_ne_zero b) hytrace)
  exact W.terminalRealCoreFullLinearEquiv.finiteDimensional

/-- The full terminal graph field is finite-dimensional over the enlarged analytic real shadow,
without any degree-four hypothesis. -/
theorem PositiveEigenvectorTerminalWitness.finiteDimensional_full_over_initialAnalyticRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) := W.terminalInitialAnalyticToFullAlgebra
    FiniteDimensional A (generatedField u) := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  letI : FiniteDimensional M A :=
    W.finiteDimensional_initialAnalytic_over_initialRealCore
  letI : FiniteDimensional M F := W.finiteDimensional_full_over_initialRealCore
  exact FiniteDimensional.right M A F

/-- The full terminal graph field is algebraic over the enlarged analytic real shadow. -/
theorem PositiveEigenvectorTerminalWitness.fullAlgebraic_initial_sup_terminalAnalyticRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) := W.terminalInitialAnalyticToFullAlgebra
    Algebra.IsAlgebraic A (generatedField u) := by
  dsimp only
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  exact Algebra.IsAlgebraic.of_finite A F

/-- The literal full terminal graph field is a finite Galois extension of the prefix joined with
the pointwise-real terminal core. -/
theorem PositiveEigenvectorTerminalWitness.isGalois_full_over_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    IsGalois M (generatedField u) := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  letI : IsGalois M N :=
    isGalois_adjoin_pair_of_sq_mem_of_add_inv_mem
      M b y hb2 (Complex.exp_ne_zero b) hytrace
  exact IsGalois.of_algEquiv W.terminalRealCoreFullAlgEquiv

/-- The full terminal graph field is Galois over the analytic real shadow as well. -/
theorem PositiveEigenvectorTerminalWitness.isGalois_full_over_initialAnalyticRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) := W.terminalInitialAnalyticToFullAlgebra
    IsGalois A (generatedField u) := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  letI : IsGalois M F := W.isGalois_full_over_initialRealCore
  exact IsGalois.tower_top_of_isGalois M A F

/-- The degree-four real-shadow bound applies to the actual full terminal graph field, not merely
to an abstractly isomorphic adjoin field. -/
theorem PositiveEigenvectorTerminalWitness.finrank_full_over_initialRealCore_le_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) ≤ 4 := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  change Module.finrank M F ≤ 4
  rw [← W.terminalRealCoreFullLinearEquiv.finrank_eq]
  exact W.finrank_adjoin_lastPair_le_four

/-- The literal full terminal graph field has a genuine positive finite degree, between one and
four, over its pointwise-real shadow. -/
theorem PositiveEigenvectorTerminalWitness.finrank_full_over_initialRealCore_interval
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    1 ≤ Module.finrank M (generatedField u) ∧
      Module.finrank M (generatedField u) ≤ 4 := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : FiniteDimensional M F := W.finiteDimensional_full_over_initialRealCore
  exact ⟨Module.finrank_pos, W.finrank_full_over_initialRealCore_le_four⟩

/-- The genuine finite degree of the full terminal graph field over its pointwise-real shadow is
one, two, or four.  In particular the two quadratic reconstructions cannot combine to produce a
cubic cover. -/
theorem PositiveEigenvectorTerminalWitness.finrank_full_over_initialRealCore_eq_one_two_or_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 1 ∨
      Module.finrank M (generatedField u) = 2 ∨
      Module.finrank M (generatedField u) = 4 := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hN : Module.finrank M N = 1 ∨ Module.finrank M N = 2 ∨
      Module.finrank M N = 4 :=
    finrank_adjoin_pair_eq_one_or_two_or_four_of_sq_mem_of_add_inv_mem
      M b y hb2 (Complex.exp_ne_zero b) hytrace
  have heq : Module.finrank M N = Module.finrank M F :=
    W.terminalRealCoreFullLinearEquiv.finrank_eq
  change Module.finrank M F = 1 ∨ Module.finrank M F = 2 ∨
    Module.finrank M F = 4
  rcases hN with hone | htwo | hfour
  · exact Or.inl (heq.symm.trans hone)
  · exact Or.inr (Or.inl (heq.symm.trans htwo))
  · exact Or.inr (Or.inr (heq.symm.trans hfour))

/-- The relative Galois group of the literal terminal graph field has exactly one, two, or four
elements. -/
theorem PositiveEigenvectorTerminalWitness.natCard_galoisGroup_full_over_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Nat.card Gal((generatedField u)/M) = 1 ∨
      Nat.card Gal((generatedField u)/M) = 2 ∨
      Nat.card Gal((generatedField u)/M) = 4 := by
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : FiniteDimensional M F := W.finiteDimensional_full_over_initialRealCore
  letI : IsGalois M F := W.isGalois_full_over_initialRealCore
  have hcard : Nat.card Gal(F/M) = Module.finrank M F :=
    IsGalois.card_aut_eq_finrank M F
  change Nat.card Gal(F/M) = 1 ∨ Nat.card Gal(F/M) = 2 ∨
    Nat.card Gal(F/M) = 4
  rw [hcard]
  exact W.finrank_full_over_initialRealCore_eq_one_two_or_four

/-- Every automorphism in the relative Galois group of the literal terminal graph field squares
to the identity. -/
theorem PositiveEigenvectorTerminalWitness.galoisGroup_full_over_initialRealCore_exponent_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    ∀ σ : Gal((generatedField u)/M), σ * σ = 1 := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  let e : Gal(N/M) ≃* Gal(F/M) := W.terminalRealCoreFullAlgEquiv.autCongr
  change ∀ σ : Gal(F/M), σ * σ = 1
  intro σ
  have hsquare : e.symm σ * e.symm σ = 1 :=
    galoisGroup_adjoin_pair_exponent_two_of_sq_mem_of_add_inv_mem
      M b y hb2 (Complex.exp_ne_zero b) hytrace (e.symm σ)
  have himage := congrArg e hsquare
  simpa using himage

/-- The relative Galois group of the literal terminal graph field is commutative (indeed,
elementary of exponent two). -/
theorem PositiveEigenvectorTerminalWitness.isMulCommutative_galoisGroup_full_over_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    IsMulCommutative Gal((generatedField u)/M) := by
  exact isMulCommutative_of_mul_self_eq_one
    W.galoisGroup_full_over_initialRealCore_exponent_two

/-- When the terminal reconstruction has degree four, its literal relative Galois group is a
Klein four-group in Mathlib's structural sense: it has cardinality four and exponent two. -/
theorem PositiveEigenvectorTerminalWitness.isKleinFour_terminalGalois_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      IsKleinFour Gal((generatedField u)/M) := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : FiniteDimensional M F := W.finiteDimensional_full_over_initialRealCore
  letI : IsGalois M F := W.isGalois_full_over_initialRealCore
  have hcard : Nat.card Gal(F/M) = 4 :=
    (IsGalois.card_aut_eq_finrank M F).trans hfour
  haveI : Nontrivial Gal(F/M) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine { card_four := hcard, exponent_two := ?_ }
  apply (Monoid.exponent_eq_prime_iff Nat.prime_two).2
  intro σ hσ
  apply orderOf_eq_prime
  · simpa [pow_two] using
      W.galoisGroup_full_over_initialRealCore_exponent_two σ
  · exact hσ

/-- Equivalently, the degree-four terminal Galois group is abstractly isomorphic to the standard
Klein group `(ZMod 2) × (ZMod 2)`. -/
theorem PositiveEigenvectorTerminalWitness.nonempty_terminalGalois_mulEquiv_kleinFour
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      Nonempty (Gal((generatedField u)/M) ≃*
        Multiplicative (ZMod 2 × ZMod 2)) := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  letI : IsKleinFour Gal(F/M) :=
    W.isKleinFour_terminalGalois_of_finrank_eq_four hfour
  exact IsKleinFour.nonempty_mulEquiv

/-- In the degree-four branch, the actual terminal Galois group realizes all four independent
choices of fixing or switching the final input and its exponential. -/
theorem PositiveEigenvectorTerminalWitness.terminalSignMap_bijective_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      Function.Bijective (fun σ : Gal((generatedField u)/M) ↦
        (decide (σ (selectedInputInFull u (Fin.last (n + 2))) =
            selectedInputInFull u (Fin.last (n + 2))),
          decide (σ (selectedExpInFull u (Fin.last (n + 2))) =
            selectedExpInFull u (Fin.last (n + 2))))) := by
  classical
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let bN : N :=
    ⟨b, IntermediateField.subset_adjoin M _ (Set.mem_insert b {y})⟩
  let yN : N :=
    ⟨y, IntermediateField.subset_adjoin M _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩
  let φ : N ≃ₐ[M] F := W.terminalRealCoreFullAlgEquiv
  let E : Gal(N/M) ≃* Gal(F/M) := φ.autCongr
  have hφb : φ bN = bF := by
    apply Subtype.ext
    rfl
  have hφy : φ yN = yF := by
    apply Subtype.ext
    rfl
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hdegreeN : Module.finrank M N = 4 :=
    W.terminalRealCoreFullLinearEquiv.finrank_eq.trans hfour
  have hsource :=
    galoisGroup_adjoin_pair_signMap_bijective_of_finrank_eq_four
      M b y hb2 (Complex.exp_ne_zero b) hytrace hdegreeN
  let sourceSign : Gal(N/M) → Bool × Bool := fun σ ↦
    (decide (σ bN = bN), decide (σ yN = yN))
  let actualSign : Gal(F/M) → Bool × Bool := fun σ ↦
    (decide (σ bF = bF), decide (σ yF = yF))
  have hcomp : actualSign = sourceSign ∘ E.symm := by
    funext σ
    apply Prod.ext
    · simp only [actualSign, sourceSign, Function.comp_apply]
      congr 1
      apply propext
      constructor
      · intro h
        apply φ.injective
        simpa [E, AlgEquiv.autCongr_apply, hφb] using h
      · intro h
        have h' := congrArg φ h
        simpa [E, AlgEquiv.autCongr_apply, hφb] using h'
    · simp only [actualSign, sourceSign, Function.comp_apply]
      congr 1
      apply propext
      constructor
      · intro h
        apply φ.injective
        simpa [E, AlgEquiv.autCongr_apply, hφy] using h
      · intro h
        have h' := congrArg φ h
        simpa [E, AlgEquiv.autCongr_apply, hφy] using h'
  change Function.Bijective actualSign
  rw [hcomp]
  exact hsource.comp E.symm.bijective

/-- The three nontrivial sign patterns in the degree-four terminal reconstruction are all
realized by actual relative automorphisms: input-only switching, output-only switching, and
simultaneous switching. -/
theorem PositiveEigenvectorTerminalWitness.exists_galoisAutomorphisms_realizing_sign_patterns
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∃ σ τ ρ : Gal((generatedField u)/M),
        σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            selectedExpInFull u (Fin.last (n + 2)) ∧
          τ (selectedInputInFull u (Fin.last (n + 2))) =
            selectedInputInFull u (Fin.last (n + 2)) ∧
          τ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ ∧
          ρ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          ρ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ := by
  classical
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let signMap : Gal(F/M) → Bool × Bool := fun σ ↦
    (decide (σ bF = bF), decide (σ yF = yF))
  have hsurj : Function.Surjective signMap := by
    exact (W.terminalSignMap_bijective_of_finrank_eq_four hfour).2
  obtain ⟨σ, hσ⟩ := hsurj (false, true)
  obtain ⟨τ, hτ⟩ := hsurj (true, false)
  obtain ⟨ρ, hρ⟩ := hsurj (false, false)
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hb_cases (γ : Gal(F/M)) : γ bF = bF ∨ γ bF = -bF := by
    apply eq_or_eq_neg_of_sq_eq_sq
    calc
      (γ bF) ^ 2 = γ (bF ^ 2) := by simp
      _ = γ (algebraMap M F (⟨b ^ 2, hb2⟩ : M)) := by rfl
      _ = algebraMap M F (⟨b ^ 2, hb2⟩ : M) := γ.commutes _
      _ = bF ^ 2 := by rfl
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hyF0 : yF ≠ 0 := by
    intro h
    exact Complex.exp_ne_zero b (congrArg Subtype.val h)
  have hy_cases (γ : Gal(F/M)) : γ yF = yF ∨ γ yF = yF⁻¹ := by
    apply eq_or_eq_inv_of_add_inv_eq ((map_ne_zero γ).mpr hyF0) hyF0
    calc
      γ yF + (γ yF)⁻¹ = γ (yF + yF⁻¹) := by simp
      _ = γ (algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M)) := by rfl
      _ = algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M) := γ.commutes _
      _ = yF + yF⁻¹ := by rfl
  have hσb : σ bF = -bF := by
    rcases hb_cases σ with h | h
    · have hcode := congrArg Prod.fst hσ
      simp [signMap, h] at hcode
    · exact h
  have hσy : σ yF = yF := by
    have hcode := congrArg Prod.snd hσ
    simpa [signMap] using hcode
  have hτb : τ bF = bF := by
    have hcode := congrArg Prod.fst hτ
    simpa [signMap] using hcode
  have hτy : τ yF = yF⁻¹ := by
    rcases hy_cases τ with h | h
    · have hcode := congrArg Prod.snd hτ
      simp [signMap, h] at hcode
    · exact h
  have hρb : ρ bF = -bF := by
    rcases hb_cases ρ with h | h
    · have hcode := congrArg Prod.fst hρ
      simp [signMap, h] at hcode
    · exact h
  have hρy : ρ yF = yF⁻¹ := by
    rcases hy_cases ρ with h | h
    · have hcode := congrArg Prod.snd hρ
      simp [signMap, h] at hcode
    · exact h
  exact ⟨σ, τ, ρ, hσb, hσy, hτb, hτy, hρb, hρy⟩

/-- Quartic terminal reconstruction forces the exponential generator to differ from its inverse;
otherwise the output sign could not contribute an independent quadratic sheet. -/
theorem PositiveEigenvectorTerminalWitness.terminalExp_ne_inv_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      selectedExpInFull u (Fin.last (n + 2)) ≠
        (selectedExpInFull u (Fin.last (n + 2)))⁻¹ := by
  classical
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let signMap : Gal(F/M) → Bool × Bool := fun σ ↦
    (decide (σ bF = bF), decide (σ yF = yF))
  have hsurj : Function.Surjective signMap :=
    (W.terminalSignMap_bijective_of_finrank_eq_four hfour).2
  obtain ⟨τ, hτ⟩ := hsurj (true, false)
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hyF0 : yF ≠ 0 := by
    intro h
    exact Complex.exp_ne_zero b (congrArg Subtype.val h)
  have hy_cases : τ yF = yF ∨ τ yF = yF⁻¹ := by
    apply eq_or_eq_inv_of_add_inv_eq ((map_ne_zero τ).mpr hyF0) hyF0
    calc
      τ yF + (τ yF)⁻¹ = τ (yF + yF⁻¹) := by simp
      _ = τ (algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M)) := by rfl
      _ = algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M) := τ.commutes _
      _ = yF + yF⁻¹ := by rfl
  have hnot : τ yF ≠ yF := by
    intro h
    have hcode := congrArg Prod.snd hτ
    simp [signMap, h] at hcode
  intro heq
  rcases hy_cases with h | h
  · exact hnot h
  · exact hnot (h.trans heq.symm)

/-- In the quartic branch, the mixed conjugation-fixed invariant is not already in the prefix
joined with the separate square and trace invariants.  An input-only deck switch fixes the base
but negates this nonzero cross term. -/
theorem PositiveEigenvectorTerminalWitness.terminalCrossInvariant_not_mem_initialRealCore
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      eigenvectorTerminalCrossInvariant u ∉ M := by
  classical
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let cF : F := bF * (yF - yF⁻¹)
  obtain ⟨σ, -, -, hσb, hσy, -, -, -, -⟩ :=
    W.exists_galoisAutomorphisms_realizing_sign_patterns hfour
  change σ bF = -bF at hσb
  change σ yF = yF at hσy
  have hbF0 : bF ≠ 0 := by
    intro h
    exact W.last_ne_zero (congrArg Subtype.val h)
  have hyne : yF ≠ yF⁻¹ := W.terminalExp_ne_inv_of_finrank_eq_four hfour
  have hcF0 : cF ≠ 0 := mul_ne_zero hbF0 (sub_ne_zero.mpr hyne)
  intro hc
  have hfix : σ cF = cF := by
    calc
      σ cF = σ (algebraMap M F
          (⟨eigenvectorTerminalCrossInvariant u, hc⟩ : M)) := by rfl
      _ = algebraMap M F
          (⟨eigenvectorTerminalCrossInvariant u, hc⟩ : M) := σ.commutes _
      _ = cF := by rfl
  have hneg : σ cF = -cF := by
    simp only [cF, map_mul, map_sub, map_inv₀, hσb, hσy]
    ring
  apply hcF0
  exact CharZero.eq_neg_self_iff.mp (hfix.symm.trans hneg)

/-- In the quartic branch, adjoining the mixed invariant to the original terminal real-shadow
base has degree exactly two. -/
theorem PositiveEigenvectorTerminalWitness.finrank_adjoin_terminalCrossInvariant_eq_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      Module.finrank M (IntermediateField.adjoin M
        ({eigenvectorTerminalCrossInvariant u} : Set ℂ)) = 2 := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  have hsq : eigenvectorTerminalCrossInvariant u ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact terminalCrossInvariant_sq_mem_realCore u
  exact finrank_adjoin_eq_two_of_sq_mem_of_not_mem M
    (eigenvectorTerminalCrossInvariant u) hsq
    (W.terminalCrossInvariant_not_mem_initialRealCore hfour)

/-- The literal analytic real-shadow field has degree exactly two over the original separate
square/trace shadow in the quartic branch. -/
theorem PositiveEigenvectorTerminalWitness.finrank_initialAnalytic_over_initialRealCore_eq_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 → Module.finrank M A = 2 := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  letI : Algebra M A :=
    (IntermediateField.inclusion
      (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
  change Module.finrank M A = 2
  rw [← W.terminalCrossAnalyticRealCoreAlgEquiv.toLinearEquiv.finrank_eq]
  exact W.finrank_adjoin_terminalCrossInvariant_eq_two hfour

/-- After adjoining the mixed conjugation-fixed invariant, the quartic terminal cover collapses
to a quadratic extension. -/
theorem PositiveEigenvectorTerminalWitness.finrank_full_over_initialAnalyticRealCore_eq_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 → Module.finrank A F = 2 := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  have hMA : Module.finrank M A = 2 :=
    W.finrank_initialAnalytic_over_initialRealCore_eq_two hfour
  exact finrank_right_eq_two_of_total_eq_four_of_left_eq_two M A F hMA hfour

/-- In the quartic branch, the remaining analytic sheet is literally the quadratic simple
extension generated by the last input alone. -/
theorem PositiveEigenvectorTerminalWitness.finrank_adjoin_lastInput_initialAnalytic_eq_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra A F :=
      (IntermediateField.inclusion
        W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra M F :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M F = 4 →
      Module.finrank A (IntermediateField.adjoin A
        ({u (Fin.last (n + 2))} : Set ℂ)) = 2 := by
  dsimp only
  intro hfour
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F :=
    (IntermediateField.inclusion
      W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  rw [W.terminalAnalyticLastInputFullAlgEquiv.toLinearEquiv.finrank_eq]
  exact W.finrank_full_over_initialAnalyticRealCore_eq_two hfour

/-- Thus the terminal input is genuinely absent from the analytic real-shadow base in the
quartic branch. -/
theorem PositiveEigenvectorTerminalWitness.lastInput_not_mem_initialAnalytic_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      u (Fin.last (n + 2)) ∉ A := by
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  have htwo : Module.finrank A (IntermediateField.adjoin A ({b} : Set ℂ)) = 2 :=
    W.finrank_adjoin_lastInput_initialAnalytic_eq_two hfour
  intro hb
  have hbot : b ∈ (⊥ : IntermediateField A ℂ) := by
    rw [IntermediateField.mem_bot]
    exact ⟨⟨b, hb⟩, rfl⟩
  have hone : Module.finrank A (IntermediateField.adjoin A ({b} : Set ℂ)) = 1 :=
    IntermediateField.finrank_adjoin_simple_eq_one_iff.mpr hbot
  omega

/-- The analytically diagonal real shadow reduces the terminal graph cover from degree at most
four to degree at most two in every branch. -/
theorem PositiveEigenvectorTerminalWitness.finrank_full_over_initialAnalyticRealCore_le_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) := W.terminalInitialAnalyticToFullAlgebra
    Module.finrank A (generatedField u) ≤ 2 := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  letI : FiniteDimensional M A :=
    W.finiteDimensional_initialAnalytic_over_initialRealCore
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  rcases W.finrank_full_over_initialRealCore_eq_one_two_or_four with h | h | h
  · exact finrank_right_le_two_of_total_le_two M A F (h.le.trans (by norm_num))
  · exact finrank_right_le_two_of_total_le_two M A F h.le
  · exact (W.finrank_full_over_initialAnalyticRealCore_eq_two h).le

/-- Consequently the analytic real-shadow cover has degree exactly one or exactly two. -/
theorem PositiveEigenvectorTerminalWitness.finrank_full_over_initialAnalyticRealCore_eq_one_or_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) := W.terminalInitialAnalyticToFullAlgebra
    Module.finrank A (generatedField u) = 1 ∨
      Module.finrank A (generatedField u) = 2 := by
  dsimp only
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  have hpos : 0 < Module.finrank A F := Module.finrank_pos
  have hle : Module.finrank A F ≤ 2 :=
    W.finrank_full_over_initialAnalyticRealCore_le_two
  rcases (Order.le_two_iff.mp hle) with hzero | hone | htwo
  · exact False.elim (Nat.ne_of_gt hpos hzero)
  · exact Or.inl hone
  · exact Or.inr htwo

/-- The relative Galois group over the analytic real shadow consequently has order one or two. -/
theorem PositiveEigenvectorTerminalWitness.natCard_galoisGroup_over_initialAnalytic_eq_one_or_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    letI : Algebra A (generatedField u) := W.terminalInitialAnalyticToFullAlgebra
    Nat.card Gal((generatedField u)/A) = 1 ∨
      Nat.card Gal((generatedField u)/A) = 2 := by
  dsimp only
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  have hcard : Nat.card Gal(F/A) = Module.finrank A F :=
    IsGalois.card_aut_eq_finrank A F
  change Nat.card Gal(F/A) = 1 ∨ Nat.card Gal(F/A) = 2
  rw [hcard]
  exact W.finrank_full_over_initialAnalyticRealCore_eq_one_or_two

/-- Every relative automorphism acts on each terminal generator through its quadratic root
alternative. -/
theorem PositiveEigenvectorTerminalWitness.terminalGenerator_sign_cases
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    ∀ σ : Gal((generatedField u)/M),
      (σ (selectedInputInFull u (Fin.last (n + 2))) =
          selectedInputInFull u (Fin.last (n + 2)) ∨
        σ (selectedInputInFull u (Fin.last (n + 2))) =
          -selectedInputInFull u (Fin.last (n + 2))) ∧
      (σ (selectedExpInFull u (Fin.last (n + 2))) =
          selectedExpInFull u (Fin.last (n + 2)) ∨
        σ (selectedExpInFull u (Fin.last (n + 2))) =
          (selectedExpInFull u (Fin.last (n + 2)))⁻¹) := by
  classical
  dsimp only
  intro σ
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hb_cases : σ bF = bF ∨ σ bF = -bF := by
    apply eq_or_eq_neg_of_sq_eq_sq
    calc
      (σ bF) ^ 2 = σ (bF ^ 2) := by simp
      _ = σ (algebraMap M F (⟨b ^ 2, hb2⟩ : M)) := by rfl
      _ = algebraMap M F (⟨b ^ 2, hb2⟩ : M) := σ.commutes _
      _ = bF ^ 2 := by rfl
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hyF0 : yF ≠ 0 := by
    intro h
    exact Complex.exp_ne_zero b (congrArg Subtype.val h)
  have hy_cases : σ yF = yF ∨ σ yF = yF⁻¹ := by
    apply eq_or_eq_inv_of_add_inv_eq ((map_ne_zero σ).mpr hyF0) hyF0
    calc
      σ yF + (σ yF)⁻¹ = σ (yF + yF⁻¹) := by simp
      _ = σ (algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M)) := by rfl
      _ = algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M) := σ.commutes _
      _ = yF + yF⁻¹ := by rfl
  exact ⟨hb_cases, hy_cases⟩

/-- In the quartic branch, an automorphism preserves complex exponentiation on the literal
terminal pair exactly when its two generator signs are diagonal: it fixes both generators or
switches both. -/
theorem PositiveEigenvectorTerminalWitness.exp_compatible_iff_diagonal_sign_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∀ σ : Gal((generatedField u)/M),
        (((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) =
          Complex.exp
            (((σ (selectedInputInFull u (Fin.last (n + 2))) :
              generatedField u) : ℂ)) ↔
          (σ (selectedInputInFull u (Fin.last (n + 2))) =
              selectedInputInFull u (Fin.last (n + 2)) ∧
            σ (selectedExpInFull u (Fin.last (n + 2))) =
              selectedExpInFull u (Fin.last (n + 2))) ∨
          (σ (selectedInputInFull u (Fin.last (n + 2))) =
              -selectedInputInFull u (Fin.last (n + 2)) ∧
            σ (selectedExpInFull u (Fin.last (n + 2))) =
              (selectedExpInFull u (Fin.last (n + 2)))⁻¹)) := by
  classical
  dsimp only
  intro hfour σ
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  obtain ⟨hb_cases, hy_cases⟩ := W.terminalGenerator_sign_cases σ
  have hyne : yF ≠ yF⁻¹ := W.terminalExp_ne_inv_of_finrank_eq_four hfour
  change (((σ yF : F) : ℂ) = Complex.exp (((σ bF : F) : ℂ)) ↔
    (σ bF = bF ∧ σ yF = yF) ∨ (σ bF = -bF ∧ σ yF = yF⁻¹))
  constructor
  · intro hcompat
    rcases hb_cases with hb | hb <;> rcases hy_cases with hy | hy
    · exact Or.inl ⟨hb, hy⟩
    · exfalso
      apply hyne
      apply Subtype.ext
      calc
        ((yF : F) : ℂ) = Complex.exp b := rfl
        _ = Complex.exp (((σ bF : F) : ℂ)) := by rw [hb]; rfl
        _ = ((σ yF : F) : ℂ) := hcompat.symm
        _ = ((yF⁻¹ : F) : ℂ) := congrArg Subtype.val hy
    · exfalso
      apply hyne
      apply Subtype.ext
      calc
        ((yF : F) : ℂ) = ((σ yF : F) : ℂ) := congrArg Subtype.val hy.symm
        _ = Complex.exp (((σ bF : F) : ℂ)) := hcompat
        _ = Complex.exp (-b) := by rw [hb]; rfl
        _ = (Complex.exp b)⁻¹ := Complex.exp_neg b
        _ = ((yF⁻¹ : F) : ℂ) := rfl
    · exact Or.inr ⟨hb, hy⟩
  · rintro (⟨hb, hy⟩ | ⟨hb, hy⟩)
    · rw [hb, hy]
      rfl
    · rw [hb, hy]
      change (Complex.exp b)⁻¹ = Complex.exp (-b)
      rw [Complex.exp_neg]

/-- In the quartic branch, fixing the mixed invariant is exactly the diagonal sign condition. -/
theorem PositiveEigenvectorTerminalWitness.crossInFull_fixed_iff_diagonal_sign_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∀ σ : Gal((generatedField u)/M),
        (σ (eigenvectorTerminalCrossInFull u) = eigenvectorTerminalCrossInFull u ↔
          (σ (selectedInputInFull u (Fin.last (n + 2))) =
              selectedInputInFull u (Fin.last (n + 2)) ∧
            σ (selectedExpInFull u (Fin.last (n + 2))) =
              selectedExpInFull u (Fin.last (n + 2))) ∨
          (σ (selectedInputInFull u (Fin.last (n + 2))) =
              -selectedInputInFull u (Fin.last (n + 2)) ∧
            σ (selectedExpInFull u (Fin.last (n + 2))) =
              (selectedExpInFull u (Fin.last (n + 2)))⁻¹)) := by
  classical
  dsimp only
  intro hfour σ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let cF : F := bF * (yF - yF⁻¹)
  obtain ⟨hb_cases, hy_cases⟩ := W.terminalGenerator_sign_cases σ
  change σ bF = bF ∨ σ bF = -bF at hb_cases
  change σ yF = yF ∨ σ yF = yF⁻¹ at hy_cases
  have hbF0 : bF ≠ 0 := by
    intro h
    exact W.last_ne_zero (congrArg Subtype.val h)
  have hyne : yF ≠ yF⁻¹ := W.terminalExp_ne_inv_of_finrank_eq_four hfour
  have hcF0 : cF ≠ 0 := mul_ne_zero hbF0 (sub_ne_zero.mpr hyne)
  change (σ cF = cF ↔
    (σ bF = bF ∧ σ yF = yF) ∨ (σ bF = -bF ∧ σ yF = yF⁻¹))
  constructor
  · intro hfix
    rcases hb_cases with hb | hb <;> rcases hy_cases with hy | hy
    · exact Or.inl ⟨hb, hy⟩
    · exfalso
      have hneg : σ cF = -cF := by
        simp only [cF, map_mul, map_sub, map_inv₀, hb, hy, inv_inv]
        ring
      exact hcF0 (CharZero.eq_neg_self_iff.mp (hfix.symm.trans hneg))
    · exfalso
      have hneg : σ cF = -cF := by
        simp only [cF, map_mul, map_sub, map_inv₀, hb, hy]
        ring
      exact hcF0 (CharZero.eq_neg_self_iff.mp (hfix.symm.trans hneg))
    · exact Or.inr ⟨hb, hy⟩
  · rintro (⟨hb, hy⟩ | ⟨hb, hy⟩)
    · simp only [cF, map_mul, map_sub, map_inv₀, hb, hy]
    · simp only [cF, map_mul, map_sub, map_inv₀, hb, hy, inv_inv]
      ring

/-- Therefore analytic compatibility on the terminal pair is exactly stabilization of the mixed
invariant that defines the analytic real-shadow enlargement. -/
theorem PositiveEigenvectorTerminalWitness.exp_compatible_iff_crossInFull_fixed_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∀ σ : Gal((generatedField u)/M),
        (((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) =
            Complex.exp
              (((σ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)) ↔
          σ (eigenvectorTerminalCrossInFull u) = eigenvectorTerminalCrossInFull u) := by
  dsimp only
  intro hfour σ
  exact (W.exp_compatible_iff_diagonal_sign_of_finrank_eq_four hfour σ).trans
    (W.crossInFull_fixed_iff_diagonal_sign_of_finrank_eq_four hfour σ).symm

/-- The stabilizer of the mixed invariant inside the original relative Galois group. -/
noncomputable def PositiveEigenvectorTerminalWitness.terminalAnalyticCompatibleSubgroup
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Subgroup Gal((generatedField u)/M) := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  exact MulAction.stabilizer Gal(F/M) (eigenvectorTerminalCrossInFull u)

/-- In the quartic branch, membership in the mixed-invariant stabilizer is exactly analytic
compatibility on the terminal graph pair. -/
theorem PositiveEigenvectorTerminalWitness.mem_terminalAnalyticCompatibleSubgroup_iff
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∀ σ : Gal((generatedField u)/M),
        (σ ∈ W.terminalAnalyticCompatibleSubgroup ↔
          ((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) =
            Complex.exp
              (((σ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ))) := by
  dsimp only
  intro hfour σ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  change (σ ∈ MulAction.stabilizer Gal(F/M) (eigenvectorTerminalCrossInFull u) ↔ _)
  rw [MulAction.mem_stabilizer_iff]
  change (σ (eigenvectorTerminalCrossInFull u) = eigenvectorTerminalCrossInFull u ↔ _)
  exact (W.exp_compatible_iff_crossInFull_fixed_of_finrank_eq_four hfour σ).symm

/-- Exactly two elements of the quartic terminal Galois group preserve complex exponentiation on
the literal terminal graph pair: the identity sheet and the simultaneous-switch sheet. -/
theorem PositiveEigenvectorTerminalWitness.natCard_exp_compatible_galois_eq_two_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      Nat.card {σ : Gal((generatedField u)/M) //
        ((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) =
          Complex.exp
            (((σ (selectedInputInFull u (Fin.last (n + 2))) :
              generatedField u) : ℂ))} = 2 := by
  classical
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let compatible : Gal(F/M) → Prop := fun σ ↦
    (((σ yF : F) : ℂ) = Complex.exp (((σ bF : F) : ℂ)))
  let signMap : Gal(F/M) → Bool × Bool := fun σ ↦
    (decide (σ bF = bF), decide (σ yF = yF))
  have hbij : Function.Bijective signMap :=
    W.terminalSignMap_bijective_of_finrank_eq_four hfour
  let e : Gal(F/M) ≃ Bool × Bool := Equiv.ofBijective signMap hbij
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hb_cases (σ : Gal(F/M)) : σ bF = bF ∨ σ bF = -bF := by
    apply eq_or_eq_neg_of_sq_eq_sq
    calc
      (σ bF) ^ 2 = σ (bF ^ 2) := by simp
      _ = σ (algebraMap M F (⟨b ^ 2, hb2⟩ : M)) := by rfl
      _ = algebraMap M F (⟨b ^ 2, hb2⟩ : M) := σ.commutes _
      _ = bF ^ 2 := by rfl
  have hytrace : y + y⁻¹ ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _)))
  have hyF0 : yF ≠ 0 := by
    intro h
    exact Complex.exp_ne_zero b (congrArg Subtype.val h)
  have hy_cases (σ : Gal(F/M)) : σ yF = yF ∨ σ yF = yF⁻¹ := by
    apply eq_or_eq_inv_of_add_inv_eq ((map_ne_zero σ).mpr hyF0) hyF0
    calc
      σ yF + (σ yF)⁻¹ = σ (yF + yF⁻¹) := by simp
      _ = σ (algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M)) := by rfl
      _ = algebraMap M F (⟨y + y⁻¹, hytrace⟩ : M) := σ.commutes _
      _ = yF + yF⁻¹ := by rfl
  have hyne : yF ≠ yF⁻¹ := W.terminalExp_ne_inv_of_finrank_eq_four hfour
  have hdiag (σ : Gal(F/M)) : compatible σ ↔
      (signMap σ).1 = (signMap σ).2 := by
    have hcompat := W.exp_compatible_iff_diagonal_sign_of_finrank_eq_four hfour σ
    change compatible σ ↔
      (σ bF = bF ∧ σ yF = yF) ∨ (σ bF = -bF ∧ σ yF = yF⁻¹) at hcompat
    change compatible σ ↔ decide (σ bF = bF) = decide (σ yF = yF)
    constructor
    · intro h
      rcases hcompat.mp h with hfix | hswitch
      · simp [hfix.1, hfix.2]
      · have hbnfix : σ bF ≠ bF := by
          intro hfix
          apply W.last_ne_zero
          apply CharZero.eq_neg_self_iff.mp
          exact congrArg Subtype.val (hfix.symm.trans hswitch.1)
        have hynfix : σ yF ≠ yF := by
          intro hfix
          exact hyne (hfix.symm.trans hswitch.2)
        simp [hbnfix, hynfix]
    · intro h
      by_cases hbfix : σ bF = bF
      · have hyfix : σ yF = yF := by
          by_contra hynfix
          simp [hbfix, hynfix] at h
        exact hcompat.mpr (Or.inl ⟨hbfix, hyfix⟩)
      · have hynfix : σ yF ≠ yF := by
          intro hyfix
          simp [hbfix, hyfix] at h
        exact hcompat.mpr (Or.inr
          ⟨(hb_cases σ).resolve_left hbfix, (hy_cases σ).resolve_left hynfix⟩)
  let ed : {σ : Gal(F/M) // compatible σ} ≃
      {p : Bool × Bool // p.1 = p.2} := e.subtypeEquiv hdiag
  change Nat.card {σ : Gal(F/M) // compatible σ} = 2
  calc
    Nat.card {σ : Gal(F/M) // compatible σ} =
        Nat.card {p : Bool × Bool // p.1 = p.2} := Nat.card_congr ed
    _ = 2 := by
      rw [Nat.card_eq_fintype_card]
      decide

/-- The analytic-compatible stabilizer is therefore an actual order-two subgroup of the
quartic relative Galois group. -/
theorem PositiveEigenvectorTerminalWitness.natCard_terminalAnalyticCompatibleSubgroup_eq_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      Nat.card W.terminalAnalyticCompatibleSubgroup = 2 := by
  classical
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let compatible : Gal(F/M) → Prop := fun σ ↦
    (((σ (selectedExpInFull u (Fin.last (n + 2))) : F) : ℂ) =
      Complex.exp (((σ (selectedInputInFull u (Fin.last (n + 2))) : F) : ℂ)))
  let H : Subgroup Gal(F/M) := W.terminalAnalyticCompatibleSubgroup
  let e : H ≃ {σ : Gal(F/M) // compatible σ} :=
    { toFun := fun σ ↦
        ⟨σ, (W.mem_terminalAnalyticCompatibleSubgroup_iff hfour σ).mp σ.property⟩
      invFun := fun σ ↦
        ⟨σ, (W.mem_terminalAnalyticCompatibleSubgroup_iff hfour σ).mpr σ.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  change Nat.card H = 2
  calc
    Nat.card H = Nat.card {σ : Gal(F/M) // compatible σ} := Nat.card_congr e
    _ = 2 := W.natCard_exp_compatible_galois_eq_two_of_finrank_eq_four hfour

/-- Every automorphism over the analytic real shadow restricts to the compatible stabilizer;
hence in the quartic branch it preserves the genuine terminal exponential graph. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_exp_compatible_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra A F :=
      (IntermediateField.inclusion
        W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra M F :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A),
        (((σ (selectedExpInFull u (Fin.last (n + 2))) : F) : ℂ) =
          Complex.exp (((σ (selectedInputInFull u (Fin.last (n + 2))) : F) : ℂ))) := by
  dsimp only
  intro hfour σ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  let σM : Gal(F/M) := σ.restrictScalars M
  have hcA : eigenvectorTerminalCrossInvariant u ∈ A := by
    apply (show eigenvectorTerminalAnalyticRealCore u ≤ A from le_sup_right)
    exact terminalCrossInvariant_mem_analyticRealCore u
  let cA : A := ⟨eigenvectorTerminalCrossInvariant u, hcA⟩
  have hfix : σM (eigenvectorTerminalCrossInFull u) =
      eigenvectorTerminalCrossInFull u := by
    calc
      σM (eigenvectorTerminalCrossInFull u) = σ (algebraMap A F cA) := by rfl
      _ = algebraMap A F cA := σ.commutes _
      _ = eigenvectorTerminalCrossInFull u := by rfl
  have hcompat :=
    (W.exp_compatible_iff_crossInFull_fixed_of_finrank_eq_four hfour σM).mpr hfix
  simpa [σM, AlgEquiv.restrictScalars_apply] using hcompat

/-- In the quartic branch, every deck transformation over the analytic real shadow is diagonal
on the terminal pair: it either fixes both the last input and its exponential, or simultaneously
negates the input and inverts the exponential. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_diagonal_sign_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra A F :=
      (IntermediateField.inclusion
        W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra M F :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A),
        (σ (selectedInputInFull u (Fin.last (n + 2))) =
            selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            selectedExpInFull u (Fin.last (n + 2))) ∨
        (σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹) := by
  dsimp only
  intro hfour σ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  let σM : Gal(F/M) := σ.restrictScalars M
  have hcompat := W.galois_over_initialAnalytic_exp_compatible_of_quartic hfour σ
  have hdiag :=
    (W.exp_compatible_iff_diagonal_sign_of_finrank_eq_four hfour σM).mp (by
      simpa [σM, AlgEquiv.restrictScalars_apply] using hcompat)
  simpa [σM, AlgEquiv.restrictScalars_apply] using hdiag

/-- Therefore a nonidentity deck transformation of the analytic quadratic cover must be the
simultaneous terminal switch. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_nontrivial_switch_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A :=
      (IntermediateField.inclusion
        (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra A F :=
      (IntermediateField.inclusion
        W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    letI : Algebra M F :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A), σ ≠ 1 →
        σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ := by
  dsimp only
  intro hfour σ hσ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  rcases W.galois_over_initialAnalytic_diagonal_sign_of_quartic hfour σ with
    hfix | hswitch
  · exfalso
    apply hσ
    apply AlgEquiv.restrictScalars_injective M
    apply (W.terminalSignMap_bijective_of_finrank_eq_four hfour).1
    simp only [AlgEquiv.restrictScalars_apply, Prod.mk.injEq, decide_eq_decide]
    exact ⟨by simpa using hfix.1, by simpa using hfix.2⟩
  · exact hswitch

/-- The analytic real-shadow Galois group has exactly two elements in the quartic branch. -/
theorem PositiveEigenvectorTerminalWitness.natCard_initialAnalyticGalois_eq_two_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 → Nat.card Gal(F/A) = 2 := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  calc
    Nat.card Gal(F/A) = Module.finrank A F := IsGalois.card_aut_eq_finrank A F
    _ = 2 := W.finrank_full_over_initialAnalyticRealCore_eq_two hfour

/-- More explicitly, the analytic quadratic cover has a unique nonidentity deck transformation,
and it is characterized by negating the last input while inverting its exponential. -/
theorem PositiveEigenvectorTerminalWitness.existsUnique_initialAnalytic_nontrivial_switch_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∃! σ : Gal(F/A), σ ≠ 1 ∧
        σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ := by
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  have hcard : Nat.card Gal(F/A) = 2 :=
    W.natCard_initialAnalyticGalois_eq_two_of_quartic hfour
  obtain ⟨σ, hσ, hunique⟩ :=
    (Nat.card_eq_two_iff' (1 : Gal(F/A))).mp hcard
  have hσswitch :=
    W.galois_over_initialAnalytic_nontrivial_switch_of_quartic hfour σ hσ
  refine ⟨σ, ⟨hσ, hσswitch⟩, ?_⟩
  intro τ hτ
  exact hunique τ hτ.1

/-- Every analytic-shadow deck transformation preserves the exponential graph on the entire
completed terminal tuple.  It fixes the prefix coordinates pointwise because their graph field
lies in the base, and the final coordinate is handled by the mixed-invariant criterion. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_exp_compatible_all_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∀ (σ : Gal(F/A)) (i : Fin (n + 3)),
        (((σ (selectedExpInFull u i) : F) : ℂ) =
          Complex.exp (((σ (selectedInputInFull u i) : F) : ℂ))) := by
  dsimp only
  intro hfour σ i
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact W.galois_over_initialAnalytic_exp_compatible_of_quartic hfour σ
  · have hxK : u (Fin.castSucc j) ∈ generatedField (Fin.init u) :=
      IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩)
    have hyK : Complex.exp (u (Fin.castSucc j)) ∈ generatedField (Fin.init u) :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)
    have hxA : u (Fin.castSucc j) ∈ A :=
      (show generatedField (Fin.init u) ≤ A from le_sup_left) hxK
    have hyA : Complex.exp (u (Fin.castSucc j)) ∈ A :=
      (show generatedField (Fin.init u) ≤ A from le_sup_left) hyK
    let xA : A := ⟨u (Fin.castSucc j), hxA⟩
    let yA : A := ⟨Complex.exp (u (Fin.castSucc j)), hyA⟩
    have hxfix : σ (selectedInputInFull u (Fin.castSucc j)) =
        selectedInputInFull u (Fin.castSucc j) := by
      calc
        σ (selectedInputInFull u (Fin.castSucc j)) =
            σ (algebraMap A F xA) := by rfl
        _ = algebraMap A F xA := σ.commutes _
        _ = selectedInputInFull u (Fin.castSucc j) := by rfl
    have hyfix : σ (selectedExpInFull u (Fin.castSucc j)) =
        selectedExpInFull u (Fin.castSucc j) := by
      calc
        σ (selectedExpInFull u (Fin.castSucc j)) =
            σ (algebraMap A F yA) := by rfl
        _ = algebraMap A F yA := σ.commutes _
        _ = selectedExpInFull u (Fin.castSucc j) := by rfl
    rw [hxfix, hyfix]
    rfl

/-- The element of the full graph field represented by an integral combination of the displayed
inputs. -/
def integralInputInFull {r : ℕ} (u : Fin r → ℂ) (m : Fin r → ℤ) : generatedField u :=
  ∑ i, (m i) • selectedInputInFull u i

/-- The product of the corresponding displayed exponential generators with the same integral
exponents. -/
def integralExpInFull {r : ℕ} (u : Fin r → ℂ) (m : Fin r → ℤ) : generatedField u :=
  ∏ i, (selectedExpInFull u i) ^ (m i)

@[simp]
theorem integralInputInFull_coe {r : ℕ} (u : Fin r → ℂ) (m : Fin r → ℤ) :
    ((integralInputInFull u m : generatedField u) : ℂ) =
      ∑ i, (m i : ℂ) * u i := by
  simp [integralInputInFull, selectedInputInFull, zsmul_eq_mul]

/-- The integral product of the graph generators is the genuine exponential of the integral
input combination. -/
@[simp]
theorem integralExpInFull_coe {r : ℕ} (u : Fin r → ℂ) (m : Fin r → ℤ) :
    ((integralExpInFull u m : generatedField u) : ℂ) =
      Complex.exp ((integralInputInFull u m : generatedField u) : ℂ) := by
  rw [integralInputInFull_coe]
  unfold integralExpInFull
  change algebraMap (generatedField u) ℂ
      (∏ i, (selectedExpInFull u i) ^ (m i)) =
    Complex.exp (∑ i, (m i : ℂ) * u i)
  rw [map_prod]
  simp only [map_zpow₀]
  rw [Complex.exp_sum]
  apply Finset.prod_congr rfl
  intro i _
  rw [Complex.exp_int_mul]
  rfl

/-- In the quartic branch, every analytic-shadow deck transformation commutes with the genuine
complex exponential on the entire integral lattice generated by the completed terminal tuple. -/
theorem PositiveEigenvectorTerminalWitness.galois_initialAnalytic_exp_integralSpan_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∀ (σ : Gal(F/A)) (m : Fin (n + 3) → ℤ),
        (((σ (integralExpInFull u m) : F) : ℂ) =
          Complex.exp (((σ (integralInputInFull u m) : F) : ℂ))) := by
  dsimp only
  intro hfour σ m
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  have hcoord :=
    W.galois_over_initialAnalytic_exp_compatible_all_of_quartic hfour σ
  unfold integralExpInFull integralInputInFull
  rw [map_prod, map_sum]
  simp only [map_zpow₀, map_zsmul]
  change algebraMap F ℂ (∏ i, (σ (selectedExpInFull u i)) ^ (m i)) =
    Complex.exp (algebraMap F ℂ
      (∑ i, (m i) • σ (selectedInputInFull u i)))
  rw [map_prod, map_sum, Complex.exp_sum]
  simp only [map_zpow₀, map_zsmul]
  apply Finset.prod_congr rfl
  intro i _
  rw [zsmul_eq_mul, Complex.exp_int_mul]
  change ((((σ (selectedExpInFull u i) : F) : ℂ) ^ (m i)) =
    (Complex.exp (((σ (selectedInputInFull u i) : F) : ℂ))) ^ (m i))
  exact congrArg (fun z : ℂ ↦ z ^ (m i)) (hcoord i)

/-- Real coordinates relative to `1` and the standard period give a homeomorphism from the real
plane to the complex plane. -/
noncomputable def standardPeriodCoordHomeomorph : ℝ × ℝ ≃ₜ ℂ where
  toFun p := (p.1 : ℂ) + (p.2 : ℂ) * standardPeriod
  invFun z := (z.re, (z.im / (2 * Real.pi) : ℝ))
  left_inv p := by
    apply Prod.ext
    · simp [standardPeriod, PeriodLogBoundary.period]
    · simp [standardPeriod, PeriodLogBoundary.period, Real.pi_ne_zero]
  right_inv z := by
    apply Complex.ext
    · simp [standardPeriod, PeriodLogBoundary.period, Complex.div_im]
    · simp only [standardPeriod, PeriodLogBoundary.period, Complex.add_im,
        Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, Complex.I_im,
        Complex.I_re, zero_mul, mul_zero, add_zero]
      field_simp [Real.pi_ne_zero]
      norm_num
      ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Rational combinations of `1` and the standard period form a dense subset of `ℂ`. -/
theorem denseRange_rat_standardPeriod :
    DenseRange (fun p : ℚ × ℚ ↦ (p.1 : ℂ) + (p.2 : ℂ) * standardPeriod) := by
  let f : ℚ × ℚ → ℝ × ℝ := Prod.map ((↑) : ℚ → ℝ) ((↑) : ℚ → ℝ)
  let g : ℝ × ℝ → ℂ := standardPeriodCoordHomeomorph
  have hf : DenseRange f := Rat.denseRange_cast.prodMap Rat.denseRange_cast
  have hg : DenseRange g := standardPeriodCoordHomeomorph.surjective.denseRange
  have hcomp : DenseRange (g ∘ f) :=
    hg.comp hf standardPeriodCoordHomeomorph.continuous
  simpa [f, g, standardPeriodCoordHomeomorph] using hcomp

/-- A dense map into an ambient space stays dense after lifting its range to any containing
subtype. -/
theorem denseRange_subtype_mk {α X : Type*} [TopologicalSpace X]
    {p : X → Prop} {f : α → X} (hf : DenseRange f) (hmem : ∀ a, p (f a)) :
    DenseRange (fun a ↦ (⟨f a, hmem a⟩ : Subtype p)) := by
  rw [DenseRange]
  apply Subtype.dense_iff.mpr
  have hsubset : Set.range f ⊆ ((↑) : Subtype p → X) ''
      Set.range (fun a ↦ (⟨f a, hmem a⟩ : Subtype p)) := by
    rintro _ ⟨a, rfl⟩
    exact ⟨⟨f a, hmem a⟩, ⟨a, rfl⟩, rfl⟩
  intro x _
  apply closure_mono hsubset
  rw [hf.closure_range]
  exact Set.mem_univ x

/-- If an intermediate-field base contains the standard period, then its image is dense in every
larger intermediate field of `ℂ`. -/
theorem denseRange_algebraMap_of_standardPeriod_mem
    (A F : IntermediateField ℚ ℂ) (hAF : A ≤ F) (hω : standardPeriod ∈ A) :
    letI : Algebra A F :=
      (IntermediateField.inclusion hAF).toRingHom.toRatAlgHom.toAlgebra
    DenseRange (algebraMap A F) := by
  letI : Algebra A F :=
    (IntermediateField.inclusion hAF).toRingHom.toRatAlgHom.toAlgebra
  let g : ℚ × ℚ → ℂ :=
    fun p ↦ (p.1 : ℂ) + (p.2 : ℂ) * standardPeriod
  have hg : DenseRange g := denseRange_rat_standardPeriod
  have hmemA (p : ℚ × ℚ) : g p ∈ A := by
    exact A.add_mem (IntermediateField.algebraMap_mem A p.1)
      (A.mul_mem (IntermediateField.algebraMap_mem A p.2) hω)
  have hmemF (p : ℚ × ℚ) : g p ∈ F := hAF (hmemA p)
  let hA : ℚ × ℚ → A := fun p ↦ ⟨g p, hmemA p⟩
  let hF : ℚ × ℚ → F := fun p ↦ ⟨g p, hmemF p⟩
  have hhF : DenseRange hF := denseRange_subtype_mk hg hmemF
  rw [DenseRange] at hhF ⊢
  apply hhF.mono
  rintro x ⟨p, rfl⟩
  refine ⟨hA p, ?_⟩
  apply Subtype.ext
  rfl

/-- A continuous relative automorphism of complex intermediate fields is trivial as soon as its
base contains the standard period: it fixes the dense rational period lattice pointwise. -/
theorem continuous_galois_eq_one_of_standardPeriod_mem
    (A F : IntermediateField ℚ ℂ) (hAF : A ≤ F) (hω : standardPeriod ∈ A) :
    letI : Algebra A F :=
      (IntermediateField.inclusion hAF).toRingHom.toRatAlgHom.toAlgebra
    ∀ σ : Gal(F/A), Continuous σ → σ = 1 := by
  letI : Algebra A F :=
    (IntermediateField.inclusion hAF).toRingHom.toRatAlgHom.toAlgebra
  intro σ hσ
  have hd : DenseRange (algebraMap A F) :=
    denseRange_algebraMap_of_standardPeriod_mem A F hAF hω
  have hfun : (σ : F → F) = id := by
    apply hd.equalizer hσ continuous_id
    funext a
    exact σ.commutes a
  apply AlgEquiv.ext
  intro x
  exact congrFun hfun x

/-- A canonically anchored graph field contains the standard period, obtained as the difference
of its first two input generators. -/
theorem standardPeriod_mem_generatedField_of_canonicallyAnchored
    {n : ℕ} {u : Fin (n + 2) → ℂ} (hu : CanonicallyAnchored u) :
    standardPeriod ∈ generatedField u := by
  have h0 : u 0 ∈ generatedField u :=
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)
  have h1 : u 1 ∈ generatedField u :=
    IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨1, rfl⟩)
  have hsub := (generatedField u).sub_mem h1 h0
  have heq : u 1 - u 0 = standardPeriod := by
    rw [hu.1, hu.2]
    simp
    ring
  rw [heq] at hsub
  exact hsub

/-- The unique nonidentity analytic-shadow deck transformation in the quartic branch is
necessarily discontinuous in the subspace topology inherited from `ℂ`. -/
theorem PositiveEigenvectorTerminalWitness.nontrivial_initialAnalyticGalois_discontinuous_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A), σ ≠ 1 → ¬ Continuous σ := by
  dsimp only
  intro _ σ hσ hcont
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  have hωK : standardPeriod ∈ generatedField (Fin.init u) :=
    standardPeriod_mem_generatedField_of_canonicallyAnchored W.2.2.1
  have hωA : standardPeriod ∈ A :=
    (show generatedField (Fin.init u) ≤ A from le_sup_left) hωK
  exact hσ (continuous_galois_eq_one_of_standardPeriod_mem A F
    W.initial_sup_analyticRealCore_le_full hωA σ hcont)

/-- The discontinuity of a nonidentity analytic-shadow deck transformation has an explicit
sequential witness: a sequence converges to zero while its image converges to twice the nonzero
last input. -/
theorem PositiveEigenvectorTerminalWitness.exists_discontinuity_sequence_of_quartic
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A), σ ≠ 1 →
        ∃ x : ℕ → F,
          Tendsto x atTop (𝓝 0) ∧
          Tendsto (fun k ↦ σ (x k)) atTop
            (𝓝 (2 * selectedInputInFull u (Fin.last (n + 2)))) ∧
          2 * selectedInputInFull u (Fin.last (n + 2)) ≠ 0 := by
  dsimp only
  intro hfour σ hσ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsTopologicalAddGroup F :=
    Topology.IsInducing.topologicalAddGroup
      F.toSubalgebra.toSubring.subtype IsInducing.subtypeVal
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  have hωK : standardPeriod ∈ generatedField (Fin.init u) :=
    standardPeriod_mem_generatedField_of_canonicallyAnchored W.2.2.1
  have hωA : standardPeriod ∈ A :=
    (show generatedField (Fin.init u) ≤ A from le_sup_left) hωK
  have hd : DenseRange (algebraMap A F) :=
    denseRange_algebraMap_of_standardPeriod_mem A F
      W.initial_sup_analyticRealCore_le_full hωA
  have hbcl : bF ∈ closure (Set.range (algebraMap A F)) := by
    rw [hd.closure_range]
    exact Set.mem_univ bF
  obtain ⟨a, haRange, halim⟩ := mem_closure_iff_seq_limit.mp hbcl
  have hafix (k : ℕ) : σ (a k) = a k := by
    rcases haRange k with ⟨c, hc⟩
    calc
      σ (a k) = σ (algebraMap A F c) := congrArg σ hc.symm
      _ = algebraMap A F c := σ.commutes c
      _ = a k := hc
  have hswitch :=
    W.galois_over_initialAnalytic_nontrivial_switch_of_quartic hfour σ hσ
  have hswitchb : σ bF = -bF := by
    simpa [bF] using hswitch.1
  let x : ℕ → F := fun k ↦ a k - bF
  refine ⟨x, ?_, ?_, ?_⟩
  · have hconst : Tendsto (fun _ : ℕ ↦ bF) atTop (𝓝 bF) :=
      tendsto_const_nhds
    simpa [x] using halim.sub hconst
  · have hlim : Tendsto (fun k ↦ a k + bF) atTop (𝓝 (bF + bF)) :=
      halim.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ bF) atTop (𝓝 bF))
    have heq : (fun k ↦ σ (x k)) = fun k ↦ a k + bF := by
      funext k
      simp [x, hafix k, hswitchb]
    rw [heq]
    simpa [bF, two_mul] using hlim
  · have hb0 : bF ≠ 0 := by
      intro hb
      exact W.last_ne_zero (congrArg Subtype.val hb)
    exact mul_ne_zero (by norm_num) hb0

/-- In fact the nonidentity analytic-shadow deck transformation already fails continuity at
zero: the explicit sequence has incompatible limits `0` and `2b`. -/
theorem PositiveEigenvectorTerminalWitness.nontrivial_initialAnalyticGalois_not_continuousAt_zero
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A), σ ≠ 1 → ¬ ContinuousAt σ 0 := by
  dsimp only
  intro hfour σ hσ hcont
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  obtain ⟨x, hx, hσx, hne⟩ :=
    W.exists_discontinuity_sequence_of_quartic hfour σ hσ
  have hσx0 : Tendsto (fun k ↦ σ (x k)) atTop (𝓝 0) := by
    simpa only [map_zero] using hcont.tendsto.comp hx
  exact hne (tendsto_nhds_unique hσx hσx0)

/-- A nonidentity analytic-shadow deck transformation is nowhere continuous: continuity at any
point would transport back to continuity at zero by additivity. -/
theorem PositiveEigenvectorTerminalWitness.nontrivial_initialAnalyticGalois_nowhere_continuous
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank M F = 4 →
      ∀ σ : Gal(F/A), σ ≠ 1 → ∀ z : F, ¬ ContinuousAt σ z := by
  dsimp only
  intro hfour σ hσ z hcont
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsTopologicalAddGroup F :=
    Topology.IsInducing.topologicalAddGroup
      F.toSubalgebra.toSubring.subtype IsInducing.subtypeVal
  apply W.nontrivial_initialAnalyticGalois_not_continuousAt_zero hfour σ hσ
  have htrans : Tendsto (fun x : F ↦ z + x) (𝓝 0) (𝓝 z) := by
    simpa only [add_zero] using
      (tendsto_const_nhds.add
        (tendsto_id : Tendsto (id : F → F) (𝓝 0) (𝓝 0)))
  have himage : Tendsto (fun x : F ↦ σ (z + x)) (𝓝 0) (𝓝 (σ z)) :=
    hcont.tendsto.comp htrans
  have hzero : Tendsto (fun x : F ↦ σ (z + x) - σ z) (𝓝 0) (𝓝 0) := by
    simpa only [sub_self] using
      himage.sub (tendsto_const_nhds : Tendsto (fun _ : F ↦ σ z) (𝓝 0) (𝓝 (σ z)))
  change Tendsto (σ : F → F) (𝓝 0) (𝓝 (σ 0))
  simpa only [map_add, add_sub_cancel_left, map_zero] using hzero

/-- A deck transformation over the anchored analytic shadow is continuous at one (equivalently
every) point exactly when it is the identity; no quartic assumption is needed. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalyticGalois_continuousAt_iff_eq_one
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ (σ : Gal(F/A)) (z : F), ContinuousAt σ z ↔ σ = 1 := by
  dsimp only
  intro σ z
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsTopologicalAddGroup F :=
    Topology.IsInducing.topologicalAddGroup
      F.toSubalgebra.toSubring.subtype IsInducing.subtypeVal
  constructor
  · intro hcont
    have htrans : Tendsto (fun x : F ↦ z + x) (𝓝 0) (𝓝 z) := by
      simpa only [add_zero] using
        (tendsto_const_nhds.add
          (tendsto_id : Tendsto (id : F → F) (𝓝 0) (𝓝 0)))
    have himage : Tendsto (fun x : F ↦ σ (z + x)) (𝓝 0) (𝓝 (σ z)) :=
      hcont.tendsto.comp htrans
    have hzero' : Tendsto (fun x : F ↦ σ (z + x) - σ z) (𝓝 0) (𝓝 0) := by
      simpa only [sub_self] using
        himage.sub
          (tendsto_const_nhds : Tendsto (fun _ : F ↦ σ z) (𝓝 0) (𝓝 (σ z)))
    have hzero : ContinuousAt σ 0 := by
      change Tendsto (σ : F → F) (𝓝 0) (𝓝 (σ 0))
      simpa only [map_add, add_sub_cancel_left, map_zero] using hzero'
    have hωK : standardPeriod ∈ generatedField (Fin.init u) :=
      standardPeriod_mem_generatedField_of_canonicallyAnchored W.2.2.1
    have hωA : standardPeriod ∈ A :=
      (show generatedField (Fin.init u) ≤ A from le_sup_left) hωK
    exact continuous_galois_eq_one_of_standardPeriod_mem A F
      W.initial_sup_analyticRealCore_le_full hωA σ
        (continuous_of_continuousAt_zero σ hzero)
  · intro hσ
    subst σ
    simpa using (continuousAt_id : ContinuousAt (id : F → F) z)

/-- The analytic-shadow cover has degree one exactly when every relative deck transformation is
continuous at zero. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_finrank_one_iff_continuousAt_zero
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank A F = 1 ↔ ∀ σ : Gal(F/A), ContinuousAt σ 0 := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  constructor
  · intro hfin σ
    apply (W.initialAnalyticGalois_continuousAt_iff_eq_one σ 0).2
    have hcard : Nat.card Gal(F/A) = 1 :=
      (IsGalois.card_aut_eq_finrank A F).trans hfin
    exact (Nat.card_eq_one_iff_unique.mp hcard).1.elim σ 1
  · intro hall
    letI : Subsingleton Gal(F/A) :=
      ⟨fun σ τ ↦
        ((W.initialAnalyticGalois_continuousAt_iff_eq_one σ 0).mp (hall σ)).trans
          ((W.initialAnalyticGalois_continuousAt_iff_eq_one τ 0).mp (hall τ)).symm⟩
    exact (IsGalois.card_aut_eq_finrank A F).symm.trans Nat.card_unique

/-- Complementarily, the analytic-shadow cover has degree two exactly when it has a deck
transformation that is discontinuous at every point. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_finrank_two_iff_nowhere_continuous
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank A F = 2 ↔
      ∃ σ : Gal(F/A), ∀ z : F, ¬ ContinuousAt σ z := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  constructor
  · intro htwo
    have hcard : Nat.card Gal(F/A) = 2 :=
      (IsGalois.card_aut_eq_finrank A F).trans htwo
    obtain ⟨σ, hσ, _⟩ := (Nat.card_eq_two_iff' (1 : Gal(F/A))).mp hcard
    refine ⟨σ, fun z hcont ↦ ?_⟩
    exact hσ ((W.initialAnalyticGalois_continuousAt_iff_eq_one σ z).mp hcont)
  · rintro ⟨σ, hσ⟩
    rcases W.finrank_full_over_initialAnalyticRealCore_eq_one_or_two with hone | htwo
    · exfalso
      apply hσ 0
      apply (W.initialAnalyticGalois_continuousAt_iff_eq_one σ 0).2
      have hcard : Nat.card Gal(F/A) = 1 :=
        (IsGalois.card_aut_eq_finrank A F).trans hone
      exact (Nat.card_eq_one_iff_unique.mp hcard).1.elim σ 1
    · exact htwo

/-- Relative degree one is exactly literal equality of the analytic shadow and the full graph
field. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_eq_full_iff_finrank_one
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    A = F ↔ Module.finrank A F = 1 := by
  dsimp only
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  have hAF : A ≤ F := W.initial_sup_analyticRealCore_le_full
  constructor
  · intro hEq
    have hFA : F ≤ A := hEq.symm.le
    have hrel : IntermediateField.relfinrank A F = 1 :=
      IntermediateField.relfinrank_eq_one_of_le hFA
    rwa [IntermediateField.relfinrank_eq_finrank_of_le hAF] at hrel
  · intro hfin
    apply le_antisymm hAF
    apply IntermediateField.relfinrank_eq_one_iff.mp
    rwa [IntermediateField.relfinrank_eq_finrank_of_le hAF]

/-- Hence literal collapse of the analytic-shadow cover is exactly automatic continuity at the
additive identity for all of its deck transformations. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_eq_full_iff_continuousAt_zero
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    A = F ↔ ∀ σ : Gal(F/A), ContinuousAt σ 0 := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  change A = F ↔ ∀ σ : Gal(F/A), ContinuousAt σ 0
  have heq := W.initialAnalytic_eq_full_iff_finrank_one
  have hcont := W.initialAnalytic_finrank_one_iff_continuousAt_zero
  dsimp only at heq hcont
  exact heq.trans hcont

/-- Since the full graph field is generated over the analytic shadow by the last input alone,
that input belongs to the base exactly in the degree-one branch. -/
theorem PositiveEigenvectorTerminalWitness.lastInput_mem_initialAnalytic_iff_finrank_one
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    u (Fin.last (n + 2)) ∈ A ↔ Module.finrank A F = 1 := by
  dsimp only
  let b := u (Fin.last (n + 2))
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  rw [← W.terminalAnalyticLastInputFullAlgEquiv.toLinearEquiv.finrank_eq,
    IntermediateField.finrank_adjoin_simple_eq_one_iff]
  change b ∈ A ↔ b ∈ (⊥ : IntermediateField A ℂ)
  rw [IntermediateField.mem_bot]
  constructor
  · intro hb
    exact ⟨⟨b, hb⟩, rfl⟩
  · rintro ⟨a, ha⟩
    rw [← ha]
    exact a.property

/-- Literal collapse of the analytic-shadow cover is equivalently membership of its sole last
input generator in the base. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_eq_full_iff_lastInput_mem
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    A = F ↔ u (Fin.last (n + 2)) ∈ A := by
  dsimp only
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  change A = F ↔ u (Fin.last (n + 2)) ∈ A
  have heq := W.initialAnalytic_eq_full_iff_finrank_one
  have hmem := W.lastInput_mem_initialAnalytic_iff_finrank_one
  dsimp only at heq hmem
  exact heq.trans hmem.symm

/-- Membership of the last input in the analytic shadow is exactly automatic continuity at zero
for every relative deck transformation. -/
theorem PositiveEigenvectorTerminalWitness.lastInput_mem_initialAnalytic_iff_continuousAt_zero
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    u (Fin.last (n + 2)) ∈ A ↔
      ∀ σ : Gal(F/A), ContinuousAt σ 0 := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  change u (Fin.last (n + 2)) ∈ A ↔
    ∀ σ : Gal(F/A), ContinuousAt σ 0
  have hmem := W.lastInput_mem_initialAnalytic_iff_finrank_one
  have hcont := W.initialAnalytic_finrank_one_iff_continuousAt_zero
  dsimp only at hmem hcont
  exact hmem.trans hcont

/-- Exclusion of the last input from the analytic shadow is exactly the degree-two branch. -/
theorem PositiveEigenvectorTerminalWitness.lastInput_not_mem_initialAnalytic_iff_finrank_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    u (Fin.last (n + 2)) ∉ A ↔ Module.finrank A F = 2 := by
  dsimp only
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  have hmem := W.lastInput_mem_initialAnalytic_iff_finrank_one
  dsimp only at hmem
  constructor
  · intro hb
    rcases W.finrank_full_over_initialAnalyticRealCore_eq_one_or_two with hone | htwo
    · exact False.elim (hb (hmem.mpr hone))
    · exact htwo
  · intro htwo hb
    have hone := hmem.mp hb
    omega

/-- Thus the last input is absent from the analytic shadow exactly when the cover contains a
nowhere-continuous deck transformation. -/
theorem PositiveEigenvectorTerminalWitness.lastInput_not_mem_initialAnalytic_iff_nowhere_continuous
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    u (Fin.last (n + 2)) ∉ A ↔
      ∃ σ : Gal(F/A), ∀ z : F, ¬ ContinuousAt σ z := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  change u (Fin.last (n + 2)) ∉ A ↔
    ∃ σ : Gal(F/A), ∀ z : F, ¬ ContinuousAt σ z
  have hmem := W.lastInput_not_mem_initialAnalytic_iff_finrank_two
  have htop := W.initialAnalytic_finrank_two_iff_nowhere_continuous
  dsimp only at hmem htop
  exact hmem.trans htop

/-- Every nonidentity automorphism over the analytic shadow is the simultaneous terminal switch,
without any assumption on the old square/trace-cover degree. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_nontrivial_switch
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ σ : Gal(F/A), σ ≠ 1 →
      σ (selectedInputInFull u (Fin.last (n + 2))) =
          -selectedInputInFull u (Fin.last (n + 2)) ∧
        σ (selectedExpInFull u (Fin.last (n + 2))) =
          (selectedExpInFull u (Fin.last (n + 2)))⁻¹ := by
  dsimp only
  intro σ hσ
  let b := u (Fin.last (n + 2))
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField A ℂ := IntermediateField.adjoin A ({b} : Set ℂ)
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsScalarTower M A F :=
    isScalarTower_intermediateField_inclusions M A F
      (initialRealCore_le_initialAnalyticRealCore u)
      W.initial_sup_analyticRealCore_le_full
      W.initial_sup_terminalRealCore_le_full
  let bN : N := ⟨b, IntermediateField.subset_adjoin A _ (Set.mem_singleton b)⟩
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let cF : F := bF * (yF - yF⁻¹)
  let φ : N ≃ₐ[A] F := W.terminalAnalyticLastInputFullAlgEquiv
  let E : Gal(N/A) ≃* Gal(F/A) := φ.autCongr
  have hφb : φ bN = bF := by
    apply Subtype.ext
    rfl
  obtain ⟨hb_cases, hy_cases⟩ := W.terminalGenerator_sign_cases (σ.restrictScalars M)
  change σ bF = bF ∨ σ bF = -bF at hb_cases
  change σ yF = yF ∨ σ yF = yF⁻¹ at hy_cases
  have hb : σ bF = -bF := by
    rcases hb_cases with hb | hb
    · exfalso
      apply hσ
      have hbN : E.symm σ bN = bN := by
        apply φ.injective
        simpa [E, AlgEquiv.autCongr_apply, hφb] using hb
      have hsource : E.symm σ = 1 :=
        galoisGroup_adjoin_single_ext A b (by simpa using hbN)
      have himage := congrArg E hsource
      simpa using himage
    · exact hb
  refine ⟨hb, ?_⟩
  rcases hy_cases with hy | hy
  · have hcA : eigenvectorTerminalCrossInvariant u ∈ A := by
      apply (show eigenvectorTerminalAnalyticRealCore u ≤ A from le_sup_right)
      exact terminalCrossInvariant_mem_analyticRealCore u
    let cA : A := ⟨eigenvectorTerminalCrossInvariant u, hcA⟩
    have hfix : σ cF = cF := by
      calc
        σ cF = σ (algebraMap A F cA) := by rfl
        _ = algebraMap A F cA := σ.commutes cA
        _ = cF := by rfl
    have hneg : σ cF = -cF := by
      simp only [cF, map_mul, map_sub, map_inv₀, hb, hy]
      ring
    have hc0 : cF = 0 :=
      CharZero.eq_neg_self_iff.mp (hfix.symm.trans hneg)
    have hb0 : bF ≠ 0 := by
      intro h
      exact W.last_ne_zero (congrArg Subtype.val h)
    exact hy.trans (sub_eq_zero.mp ((mul_eq_zero.mp hc0).resolve_left hb0))
  · exact hy

/-- In every branch, each deck transformation over the analytic shadow preserves the genuine
terminal exponential equation. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_exp_compatible
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ σ : Gal(F/A),
      (((σ (selectedExpInFull u (Fin.last (n + 2))) : F) : ℂ) =
        Complex.exp (((σ (selectedInputInFull u (Fin.last (n + 2))) : F) : ℂ))) := by
  dsimp only
  intro σ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  by_cases hσ : σ = 1
  · subst σ
    rfl
  · obtain ⟨hb, hy⟩ := W.galois_over_initialAnalytic_nontrivial_switch σ hσ
    rw [hy, hb]
    change (Complex.exp (u (Fin.last (n + 2))))⁻¹ =
      Complex.exp (-u (Fin.last (n + 2)))
    rw [Complex.exp_neg]

/-- Every analytic-shadow deck transformation preserves the exponential graph on the entire
completed terminal tuple, with no quartic assumption. -/
theorem PositiveEigenvectorTerminalWitness.galois_over_initialAnalytic_exp_compatible_all
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ (σ : Gal(F/A)) (i : Fin (n + 3)),
      (((σ (selectedExpInFull u i) : F) : ℂ) =
        Complex.exp (((σ (selectedInputInFull u i) : F) : ℂ))) := by
  dsimp only
  intro σ i
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · exact W.galois_over_initialAnalytic_exp_compatible σ
  · have hxK : u (Fin.castSucc j) ∈ generatedField (Fin.init u) :=
      IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩)
    have hyK : Complex.exp (u (Fin.castSucc j)) ∈ generatedField (Fin.init u) :=
      IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)
    have hxA : u (Fin.castSucc j) ∈ A :=
      (show generatedField (Fin.init u) ≤ A from le_sup_left) hxK
    have hyA : Complex.exp (u (Fin.castSucc j)) ∈ A :=
      (show generatedField (Fin.init u) ≤ A from le_sup_left) hyK
    let xA : A := ⟨u (Fin.castSucc j), hxA⟩
    let yA : A := ⟨Complex.exp (u (Fin.castSucc j)), hyA⟩
    have hxfix : σ (selectedInputInFull u (Fin.castSucc j)) =
        selectedInputInFull u (Fin.castSucc j) := by
      calc
        σ (selectedInputInFull u (Fin.castSucc j)) =
            σ (algebraMap A F xA) := by rfl
        _ = algebraMap A F xA := σ.commutes _
        _ = selectedInputInFull u (Fin.castSucc j) := by rfl
    have hyfix : σ (selectedExpInFull u (Fin.castSucc j)) =
        selectedExpInFull u (Fin.castSucc j) := by
      calc
        σ (selectedExpInFull u (Fin.castSucc j)) =
            σ (algebraMap A F yA) := by rfl
        _ = algebraMap A F yA := σ.commutes _
        _ = selectedExpInFull u (Fin.castSucc j) := by rfl
    rw [hxfix, hyfix]
    rfl

/-- Every analytic-shadow deck transformation commutes with the genuine exponential on the
entire integral lattice generated by the completed terminal tuple, with no quartic assumption. -/
theorem PositiveEigenvectorTerminalWitness.galois_initialAnalytic_exp_integralSpan
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ (σ : Gal(F/A)) (m : Fin (n + 3) → ℤ),
      (((σ (integralExpInFull u m) : F) : ℂ) =
        Complex.exp (((σ (integralInputInFull u m) : F) : ℂ))) := by
  dsimp only
  intro σ m
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  have hcoord := W.galois_over_initialAnalytic_exp_compatible_all σ
  unfold integralExpInFull integralInputInFull
  rw [map_prod, map_sum]
  simp only [map_zpow₀, map_zsmul]
  change algebraMap F ℂ (∏ i, (σ (selectedExpInFull u i)) ^ (m i)) =
    Complex.exp (algebraMap F ℂ
      (∑ i, (m i) • σ (selectedInputInFull u i)))
  rw [map_prod, map_sum, Complex.exp_sum]
  simp only [map_zpow₀, map_zsmul]
  apply Finset.prod_congr rfl
  intro i _
  rw [zsmul_eq_mul, Complex.exp_int_mul]
  change ((((σ (selectedExpInFull u i) : F) : ℂ) ^ (m i)) =
    (Complex.exp (((σ (selectedInputInFull u i) : F) : ℂ))) ^ (m i))
  exact congrArg (fun z : ℂ ↦ z ^ (m i)) (hcoord i)

/-- In the degree-two branch, there is a unique nonidentity analytic-shadow deck transformation,
and it is the simultaneous terminal switch. -/
theorem PositiveEigenvectorTerminalWitness.existsUnique_initialAnalytic_switch_of_finrank_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank A F = 2 →
      ∃! σ : Gal(F/A), σ ≠ 1 ∧
        σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ := by
  dsimp only
  intro htwo
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  have hcard : Nat.card Gal(F/A) = 2 :=
    (IsGalois.card_aut_eq_finrank A F).trans htwo
  obtain ⟨σ, hσ, hunique⟩ :=
    (Nat.card_eq_two_iff' (1 : Gal(F/A))).mp hcard
  refine ⟨σ, ⟨hσ, W.galois_over_initialAnalytic_nontrivial_switch σ hσ⟩, ?_⟩
  intro τ hτ
  exact hunique τ hτ.1

/-- Abstractly, the degree-two analytic-shadow Galois group is the cyclic group of order two. -/
theorem PositiveEigenvectorTerminalWitness.nonempty_initialAnalyticGalois_mulEquiv_zmod_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank A F = 2 →
      Nonempty (Gal(F/A) ≃* Multiplicative (ZMod 2)) := by
  dsimp only
  intro htwo
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  have hcard : Nat.card Gal(F/A) = 2 :=
    (IsGalois.card_aut_eq_finrank A F).trans htwo
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨mulEquivOfPrimeCardEq hcard ?_⟩
  simp

/-- The analytic-shadow cover has an exhaustive concrete dichotomy: it either collapses
literally, or it has a unique nowhere-continuous simultaneous switch. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_branch_dichotomy
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    (A = F ∧ ∀ σ : Gal(F/A), σ = 1) ∨
      (u (Fin.last (n + 2)) ∉ A ∧ Module.finrank A F = 2 ∧
        ∃! σ : Gal(F/A), σ ≠ 1 ∧
          σ (selectedInputInFull u (Fin.last (n + 2))) =
              -selectedInputInFull u (Fin.last (n + 2)) ∧
            σ (selectedExpInFull u (Fin.last (n + 2))) =
              (selectedExpInFull u (Fin.last (n + 2)))⁻¹ ∧
            ∀ z : F, ¬ ContinuousAt σ z) := by
  dsimp only
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  rcases W.finrank_full_over_initialAnalyticRealCore_eq_one_or_two with hone | htwo
  · left
    refine ⟨(W.initialAnalytic_eq_full_iff_finrank_one).mpr hone, ?_⟩
    have hcont := (W.initialAnalytic_finrank_one_iff_continuousAt_zero).mp hone
    intro σ
    exact (W.initialAnalyticGalois_continuousAt_iff_eq_one σ 0).mp (hcont σ)
  · right
    refine ⟨(W.lastInput_not_mem_initialAnalytic_iff_finrank_two).mpr htwo,
      htwo, ?_⟩
    obtain ⟨σ, ⟨hσ, hb, hy⟩, hunique⟩ :=
      W.existsUnique_initialAnalytic_switch_of_finrank_two htwo
    refine ⟨σ, ⟨hσ, hb, hy, ?_⟩, ?_⟩
    · intro z hcont
      exact hσ ((W.initialAnalyticGalois_continuousAt_iff_eq_one σ z).mp hcont)
    · intro τ hτ
      exact hunique τ ⟨hτ.1, hτ.2.1, hτ.2.2.1⟩

/-- The reusable proposition underlying the analytic-shadow branch dichotomy.  Naming it makes
the concrete collapse/wild-switch alternative available inside package-free existential normal
forms without repeating its field-tower data. -/
def PositiveEigenvectorTerminalWitness.InitialAnalyticBranchDichotomy
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) : Prop :=
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  (A = F ∧ ∀ σ : Gal(F/A), σ = 1) ∨
    (u (Fin.last (n + 2)) ∉ A ∧ Module.finrank A F = 2 ∧
      ∃! σ : Gal(F/A), σ ≠ 1 ∧
        σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ ∧
          ∀ z : F, ¬ ContinuousAt σ z)

/-- Every terminal witness satisfies its named analytic-shadow branch proposition. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalyticBranchDichotomy
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    W.InitialAnalyticBranchDichotomy := by
  exact W.initialAnalytic_branch_dichotomy

/-- In the residual quadratic branch, field trace and norm record the simultaneous switch
exactly: the last input has trace zero and norm minus its square, while its exponential has its
reciprocal trace and norm one. -/
theorem PositiveEigenvectorTerminalWitness.initialAnalytic_trace_norm_of_finrank_two
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank A F = 2 →
      algebraMap A F (Algebra.trace A F
          (selectedInputInFull u (Fin.last (n + 2)))) = 0 ∧
        algebraMap A F (Algebra.norm A
          (selectedInputInFull u (Fin.last (n + 2)))) =
            -(selectedInputInFull u (Fin.last (n + 2))) ^ 2 ∧
        algebraMap A F (Algebra.trace A F
          (selectedExpInFull u (Fin.last (n + 2)))) =
            selectedExpInFull u (Fin.last (n + 2)) +
              (selectedExpInFull u (Fin.last (n + 2)))⁻¹ ∧
        algebraMap A F (Algebra.norm A
          (selectedExpInFull u (Fin.last (n + 2)))) = 1 := by
  dsimp only
  classical
  intro htwo
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  let b := selectedInputInFull u (Fin.last (n + 2))
  let y := selectedExpInFull u (Fin.last (n + 2))
  have hcard : Nat.card Gal(F/A) = 2 :=
    (IsGalois.card_aut_eq_finrank A F).trans htwo
  obtain ⟨σ, hσ, hunique⟩ :=
    (Nat.card_eq_two_iff' (1 : Gal(F/A))).mp hcard
  have hswitch := W.galois_over_initialAnalytic_nontrivial_switch σ hσ
  have huniv : (Finset.univ : Finset Gal(F/A)) =
      ({σ, 1} : Finset Gal(F/A)) := by
    ext τ
    simp only [Finset.mem_univ, Finset.mem_insert, Finset.mem_singleton, true_iff]
    by_cases hτ : τ = 1
    · exact Or.inr hτ
    · exact Or.inl (hunique τ hτ)
  have htraceb := trace_eq_sum_automorphisms (K := A) (L := F) b
  have hnormb := Algebra.norm_eq_prod_automorphisms (K := A) (L := F) b
  have htracey := trace_eq_sum_automorphisms (K := A) (L := F) y
  have hnormy := Algebra.norm_eq_prod_automorphisms (K := A) (L := F) y
  rw [huniv] at htraceb hnormb htracey hnormy
  simp [hσ] at htraceb hnormb htracey hnormy
  rw [hswitch.1] at htraceb hnormb
  rw [hswitch.2] at htracey hnormy
  have hy0 : selectedExpInFull u (Fin.last (n + 2)) ≠ 0 := by
    intro hzero
    have hcoe := congrArg ((↑) : F → ℂ) hzero
    exact Complex.exp_ne_zero (u (Fin.last (n + 2))) hcoe
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa [b] using htraceb
  · simpa [b, pow_two] using hnormb
  · simpa [y, add_comm] using htracey
  · simpa [y, hy0] using hnormy

/-- The unique quadratic simultaneous switch has no accidental fixed elements: its fixed
subfield is exactly the embedded analytic shadow. -/
theorem PositiveEigenvectorTerminalWitness.existsUnique_initialAnalytic_switch_with_fixedField
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    Module.finrank A F = 2 →
      ∃! σ : Gal(F/A), σ ≠ 1 ∧
        σ (selectedInputInFull u (Fin.last (n + 2))) =
            -selectedInputInFull u (Fin.last (n + 2)) ∧
          σ (selectedExpInFull u (Fin.last (n + 2))) =
            (selectedExpInFull u (Fin.last (n + 2)))⁻¹ ∧
          ∀ z : F, σ z = z ↔ z ∈ Set.range (algebraMap A F) := by
  dsimp only
  intro htwo
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : FiniteDimensional A F :=
    W.finiteDimensional_full_over_initialAnalyticRealCore
  letI : IsGalois A F := W.isGalois_full_over_initialAnalyticRealCore
  obtain ⟨σ, ⟨hσ, hb, hy⟩, hunique⟩ :=
    W.existsUnique_initialAnalytic_switch_of_finrank_two htwo
  refine ⟨σ, ⟨hσ, hb, hy, ?_⟩, ?_⟩
  · intro z
    constructor
    · intro hz
      apply (IsGalois.mem_range_algebraMap_iff_fixed z).mpr
      intro τ
      by_cases hτ : τ = 1
      · rw [hτ]
        rfl
      · rw [hunique τ (by
          exact ⟨hτ, W.galois_over_initialAnalytic_nontrivial_switch τ hτ⟩)]
        exact hz
    · rintro ⟨a, rfl⟩
      exact σ.commutes a
  · intro τ hτ
    exact hunique τ ⟨hτ.1, hτ.2.1, hτ.2.2.1⟩

/-- Every nonidentity analytic-shadow deck transformation has an explicit discontinuity
sequence at zero, without any quartic assumption. -/
theorem PositiveEigenvectorTerminalWitness.exists_initialAnalytic_discontinuity_sequence
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ σ : Gal(F/A), σ ≠ 1 →
      ∃ x : ℕ → F,
        Tendsto x atTop (𝓝 0) ∧
        Tendsto (fun k ↦ σ (x k)) atTop
          (𝓝 (2 * selectedInputInFull u (Fin.last (n + 2)))) ∧
        2 * selectedInputInFull u (Fin.last (n + 2)) ≠ 0 := by
  dsimp only
  intro σ hσ
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsTopologicalAddGroup F :=
    Topology.IsInducing.topologicalAddGroup
      F.toSubalgebra.toSubring.subtype IsInducing.subtypeVal
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  have hωK : standardPeriod ∈ generatedField (Fin.init u) :=
    standardPeriod_mem_generatedField_of_canonicallyAnchored W.2.2.1
  have hωA : standardPeriod ∈ A :=
    (show generatedField (Fin.init u) ≤ A from le_sup_left) hωK
  have hd : DenseRange (algebraMap A F) :=
    denseRange_algebraMap_of_standardPeriod_mem A F
      W.initial_sup_analyticRealCore_le_full hωA
  have hbcl : bF ∈ closure (Set.range (algebraMap A F)) := by
    rw [hd.closure_range]
    exact Set.mem_univ bF
  obtain ⟨a, haRange, halim⟩ := mem_closure_iff_seq_limit.mp hbcl
  have hafix (k : ℕ) : σ (a k) = a k := by
    rcases haRange k with ⟨c, hc⟩
    calc
      σ (a k) = σ (algebraMap A F c) := congrArg σ hc.symm
      _ = algebraMap A F c := σ.commutes c
      _ = a k := hc
  have hswitch := W.galois_over_initialAnalytic_nontrivial_switch σ hσ
  have hswitchb : σ bF = -bF := by
    simpa [bF] using hswitch.1
  let x : ℕ → F := fun k ↦ a k - bF
  refine ⟨x, ?_, ?_, ?_⟩
  · have hconst : Tendsto (fun _ : ℕ ↦ bF) atTop (𝓝 bF) :=
      tendsto_const_nhds
    simpa [x] using halim.sub hconst
  · have hlim : Tendsto (fun k ↦ a k + bF) atTop (𝓝 (bF + bF)) :=
      halim.add (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ bF) atTop (𝓝 bF))
    have heq : (fun k ↦ σ (x k)) = fun k ↦ a k + bF := by
      funext k
      simp [x, hafix k, hswitchb]
    rw [heq]
    simpa [bF, two_mul] using hlim
  · have hb0 : bF ≠ 0 := by
      intro hb
      exact W.last_ne_zero (congrArg Subtype.val hb)
    exact mul_ne_zero (by norm_num) hb0

/-- Translating the zero sequence gives an explicit incompatible limiting pair at every point of
the full graph field. -/
theorem PositiveEigenvectorTerminalWitness.exists_initialAnalytic_discontinuity_sequence_at
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
    let F := generatedField u
    letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
    letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
    letI : Algebra M F := W.terminalInitialRealToFullAlgebra
    ∀ σ : Gal(F/A), σ ≠ 1 → ∀ z : F,
      ∃ x : ℕ → F,
        Tendsto x atTop (𝓝 z) ∧
        Tendsto (fun k ↦ σ (x k)) atTop
          (𝓝 (σ z + 2 * selectedInputInFull u (Fin.last (n + 2)))) ∧
        σ z + 2 * selectedInputInFull u (Fin.last (n + 2)) ≠ σ z := by
  dsimp only
  intro σ hσ z
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
  let F := generatedField u
  letI : Algebra M A := terminalInitialRealToAnalyticAlgebra u
  letI : Algebra A F := W.terminalInitialAnalyticToFullAlgebra
  letI : Algebra M F := W.terminalInitialRealToFullAlgebra
  letI : IsTopologicalAddGroup F :=
    Topology.IsInducing.topologicalAddGroup
      F.toSubalgebra.toSubring.subtype IsInducing.subtypeVal
  obtain ⟨d, hd, hσd, hne⟩ :=
    W.exists_initialAnalytic_discontinuity_sequence σ hσ
  let x : ℕ → F := fun k ↦ z + d k
  refine ⟨x, ?_, ?_, ?_⟩
  · simpa [x, add_zero] using
      (tendsto_const_nhds.add hd :
        Tendsto (fun k ↦ z + d k) atTop (𝓝 (z + 0)))
  · have hlim :=
      (tendsto_const_nhds : Tendsto (fun _ : ℕ ↦ σ z) atTop (𝓝 (σ z))).add hσd
    have heq : (fun k ↦ σ (x k)) = fun k ↦ σ z + σ (d k) := by
      funext k
      simp only [x, map_add]
    rw [heq]
    exact hlim
  · intro h
    exact hne (add_eq_left.mp h)

/-- Among the three nontrivial quartic sign sheets, the two single-generator switches fail to
preserve the analytic exponential graph, while the simultaneous switch preserves it. -/
theorem PositiveEigenvectorTerminalWitness.exists_galois_analytic_sign_patterns_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∃ σ τ ρ : Gal((generatedField u)/M),
        ((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) ≠
            Complex.exp
              (((σ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)) ∧
          ((τ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) ≠
            Complex.exp
              (((τ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)) ∧
          ((ρ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) =
            Complex.exp
              (((ρ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)) := by
  classical
  dsimp only
  intro hfour
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  obtain ⟨σ, τ, ρ, hσb, hσy, hτb, hτy, hρb, hρy⟩ :=
    W.exists_galoisAutomorphisms_realizing_sign_patterns hfour
  have hyne : yF ≠ yF⁻¹ := W.terminalExp_ne_inv_of_finrank_eq_four hfour
  have hyneC : ((yF : F) : ℂ) ≠ (((yF⁻¹ : F) : F) : ℂ) := by
    exact fun h ↦ hyne (Subtype.ext h)
  refine ⟨σ, τ, ρ, ?_, ?_, ?_⟩
  · rw [hσy, hσb]
    simpa [bF, yF, Complex.exp_neg] using hyneC
  · rw [hτy, hτb]
    exact hyneC.symm
  · rw [hρy, hρb]
    change (Complex.exp (u (Fin.last (n + 2))))⁻¹ =
      Complex.exp (-u (Fin.last (n + 2)))
    rw [Complex.exp_neg]

/-- In the genuine degree-four branch, some relative Galois automorphism fails to intertwine
complex exponentiation on the literal terminal graph pair.  Otherwise every automorphism would
be determined by the sign of its action on the terminal input, embedding a four-element Galois
group into `Bool`. -/
theorem PositiveEigenvectorTerminalWitness.exists_non_exp_compatible_galois_of_finrank_eq_four
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    Module.finrank M (generatedField u) = 4 →
      ∃ σ : Gal((generatedField u)/M),
        ((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) ≠
          Complex.exp
            (((σ (selectedInputInFull u (Fin.last (n + 2))) : generatedField u) : ℂ)) := by
  classical
  dsimp only
  intro hfour
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  change ∃ σ : Gal(F/M),
    ((σ (selectedExpInFull u (Fin.last (n + 2))) : F) : ℂ) ≠
      Complex.exp (((σ (selectedInputInFull u (Fin.last (n + 2))) : F) : ℂ))
  let bF : F := selectedInputInFull u (Fin.last (n + 2))
  let yF : F := selectedExpInFull u (Fin.last (n + 2))
  let bN : N :=
    ⟨b, IntermediateField.subset_adjoin M _ (Set.mem_insert b {y})⟩
  let yN : N :=
    ⟨y, IntermediateField.subset_adjoin M _
      (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton y)))⟩
  let φ : N ≃ₐ[M] F := W.terminalRealCoreFullAlgEquiv
  let E : Gal(N/M) ≃* Gal(F/M) := φ.autCongr
  have hφb : φ bN = bF := by
    apply Subtype.ext
    rfl
  have hφy : φ yN = yF := by
    apply Subtype.ext
    rfl
  letI : FiniteDimensional M F := W.finiteDimensional_full_over_initialRealCore
  letI : IsGalois M F := W.isGalois_full_over_initialRealCore
  have hcard : Nat.card Gal(F/M) = 4 :=
    (IsGalois.card_aut_eq_finrank M F).trans hfour
  have hb2 : b ^ 2 ∈ M := by
    apply (show eigenvectorTerminalRealCore u ≤ M from le_sup_right)
    exact IntermediateField.subset_adjoin ℚ _
      (Set.mem_insert (b ^ 2) {y + y⁻¹})
  have hb_cases (σ : Gal(F/M)) : σ bF = bF ∨ σ bF = -bF := by
    apply eq_or_eq_neg_of_sq_eq_sq
    calc
      (σ bF) ^ 2 = σ (bF ^ 2) := by simp
      _ = σ (algebraMap M F (⟨b ^ 2, hb2⟩ : M)) := by rfl
      _ = algebraMap M F (⟨b ^ 2, hb2⟩ : M) := σ.commutes _
      _ = bF ^ 2 := by rfl
  by_contra hnone
  push Not at hnone
  let sign : Gal(F/M) → Bool := fun σ ↦ decide (σ bF = bF)
  have hsign_injective : Function.Injective sign := by
    intro σ τ hsign
    have hb : σ bF = τ bF := by
      by_cases hσ : σ bF = bF
      · by_cases hτ : τ bF = bF
        · exact hσ.trans hτ.symm
        · simp [sign, hσ, hτ] at hsign
      · by_cases hτ : τ bF = bF
        · simp [sign, hσ, hτ] at hsign
        · rcases hb_cases σ with hσ' | hσ'
          · exact False.elim (hσ hσ')
          · rcases hb_cases τ with hτ' | hτ'
            · exact False.elim (hτ hτ')
            · exact hσ'.trans hτ'.symm
    have hy : σ yF = τ yF := by
      apply Subtype.ext
      calc
        ((σ yF : F) : ℂ) = Complex.exp (((σ bF : F) : ℂ)) := hnone σ
        _ = Complex.exp (((τ bF : F) : ℂ)) := by rw [hb]
        _ = ((τ yF : F) : ℂ) := (hnone τ).symm
    have hbN : E.symm σ bN = E.symm τ bN := by
      apply φ.injective
      simpa [E, AlgEquiv.autCongr_apply, hφb] using hb
    have hyN : E.symm σ yN = E.symm τ yN := by
      apply φ.injective
      simpa [E, AlgEquiv.autCongr_apply, hφy] using hy
    have hsource : E.symm σ = E.symm τ :=
      galoisGroup_adjoin_pair_ext M b y hbN hyN
    exact E.symm.injective hsource
  have hle : Nat.card Gal(F/M) ≤ Nat.card Bool :=
    Nat.card_le_card_of_injective sign hsign_injective
  have hbool : Nat.card Bool = 2 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_bool]
  omega

/-- The degree-one branch is exactly literal equality between the full terminal graph field and
the prefix joined with its pointwise-real shadow. -/
theorem PositiveEigenvectorTerminalWitness.initialRealCore_eq_full_iff_finrank_eq_one
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    M = generatedField u ↔ Module.finrank M (generatedField u) = 1 := by
  let b := u (Fin.last (n + 2))
  let y := Complex.exp b
  let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
  let F := generatedField u
  let N : IntermediateField M ℂ := IntermediateField.adjoin M ({b, y} : Set ℂ)
  letI : Algebra M F :=
    (IntermediateField.inclusion
      W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
  have hrestrict : N.restrictScalars ℚ = F :=
    W.restrictScalars_adjoin_lastPair_eq_fullField
  have heq : Module.finrank M N = Module.finrank M F :=
    W.terminalRealCoreFullLinearEquiv.finrank_eq
  constructor
  · intro hMF
    have hNM : N.restrictScalars ℚ = M := hrestrict.trans hMF.symm
    have hNbot : N = ⊥ := by
      apply le_antisymm
      · intro z hz
        have hzM : (z : ℂ) ∈ M := by
          have hz' : (z : ℂ) ∈ N.restrictScalars ℚ := hz
          rw [hNM] at hz'
          exact hz'
        rw [IntermediateField.mem_bot]
        exact ⟨⟨z, hzM⟩, rfl⟩
      · exact bot_le
    exact heq.symm.trans (IntermediateField.finrank_eq_one_iff.mpr hNbot)
  · intro hdegree
    have hNbot : N = ⊥ :=
      IntermediateField.finrank_eq_one_iff.mp (heq.trans hdegree)
    have hbot : (⊥ : IntermediateField M ℂ).restrictScalars ℚ = M := by
      ext z
      rw [IntermediateField.mem_restrictScalars, IntermediateField.mem_bot]
      constructor
      · rintro ⟨m, rfl⟩
        exact m.property
      · intro hz
        exact ⟨⟨z, hz⟩, rfl⟩
    exact hbot.symm.trans
      ((congrArg (IntermediateField.restrictScalars ℚ) hNbot.symm).trans hrestrict)

/-- An eigenvector completion yields the self-contained literal-last-coordinate terminal
normal form. -/
theorem EigenvectorCompletedStableTerminalData.completed_positiveEigenvectorTerminalWitness
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (E : EigenvectorCompletedStableTerminalData w)
    (H : PositiveLeastConjugationStableFailure w) :
    PositiveEigenvectorTerminalWitness E.completed := by
  change PositiveEigenvectorTerminalWitness
    (Fin.snoc E.deletionData.deletion E.eigenvector)
  unfold PositiveEigenvectorTerminalWitness
  simp only [Fin.init_snoc, Fin.snoc_last]
  refine ⟨?_, E.deletionData.deletionLinearIndependent,
    E.deletionData.deletionAnchored, E.deletionData.deletionStable,
    ?_, E.eigenvectorOutside, E.eigenvectorSign, ?_, ?_⟩
  · simpa only [EigenvectorCompletedStableTerminalData.completed] using
      E.completed_positiveLeastFailure H
  · exact (trdeg_generatedField_init_snoc
      E.deletionData.deletion E.eigenvector).trans
        E.deletionData.deletionSharp
  · exact (isAlgebraic_generatedField_init_snoc_iff
      E.deletionData.deletion E.eigenvector E.eigenvector).mpr
        E.eigenvectorAlgebraic
  · exact (isAlgebraic_generatedField_init_snoc_iff
      E.deletionData.deletion E.eigenvector (Complex.exp E.eigenvector)).mpr
        E.expEigenvectorAlgebraic

/-- The package-free disjoint endpoint using only a tuple, its literal initial segment, and its
literal last coordinate. -/
def RealEigenvectorTerminalNormalFormDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ realAnchorCore ∨
    (AlgebraicIndependent ℚ realAnchorCore ∧
      ∃ (n : ℕ) (u : Fin (n + 3) → ℂ),
        PositiveEigenvectorTerminalWitness u)

/-- Failure of Schanuel is exactly the self-contained real eigenvector terminal normal form. -/
theorem not_conjecture_iff_realEigenvectorTerminalNormalFormDichotomy :
    ¬ Conjecture ↔ RealEigenvectorTerminalNormalFormDichotomy := by
  constructor
  · intro hnot
    rcases not_conjecture_iff_realEigenvectorCompletedStableTerminalDichotomy.mp hnot with
      hdep | ⟨hcore, n, w, H, hE⟩
    · exact Or.inl hdep
    · obtain ⟨E⟩ := hE
      exact Or.inr
        ⟨hcore, E.deletionData.complementCount, E.completed,
          E.completed_positiveEigenvectorTerminalWitness H⟩
  · rintro (hdep | ⟨-, n, u, hu⟩)
    · exact
        not_conjecture_iff_realAnchorCore_dependent_or_positiveLeastStableFailure.mpr
          (Or.inl hdep)
    · exact
        not_conjecture_iff_realAnchorCore_dependent_or_positiveLeastStableFailure.mpr
          (Or.inr ⟨n + 1, u, hu.1⟩)

/-- A package-free terminal witness together with the genuine finite quartic cover of its
pointwise-real shadow. -/
def PositiveQuarticRealEigenvectorTerminalWitness
    {n : ℕ} (u : Fin (n + 3) → ℂ) : Prop :=
  ∃ W : PositiveEigenvectorTerminalWitness u,
    let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
    letI : Algebra M (generatedField u) :=
      (IntermediateField.inclusion
        W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
    IsGalois M (generatedField u) ∧
      FiniteDimensional M (generatedField u) ∧
      IsMulCommutative Gal((generatedField u)/M) ∧
      (∀ σ : Gal((generatedField u)/M), σ * σ = 1) ∧
      (Module.finrank M (generatedField u) = 1 ∨
        Module.finrank M (generatedField u) = 2 ∨
        Module.finrank M (generatedField u) = 4) ∧
      (Module.finrank M (generatedField u) = 4 →
        IsKleinFour Gal((generatedField u)/M)) ∧
      (Module.finrank M (generatedField u) = 4 →
        Nonempty (Gal((generatedField u)/M) ≃*
          Multiplicative (ZMod 2 × ZMod 2))) ∧
      (Module.finrank M (generatedField u) = 4 →
        Function.Bijective (fun σ : Gal((generatedField u)/M) ↦
          (decide (σ (selectedInputInFull u (Fin.last (n + 2))) =
              selectedInputInFull u (Fin.last (n + 2))),
            decide (σ (selectedExpInFull u (Fin.last (n + 2))) =
              selectedExpInFull u (Fin.last (n + 2)))))) ∧
      (Module.finrank M (generatedField u) = 4 →
        ∃ σ τ ρ : Gal((generatedField u)/M),
          ((σ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) ≠
            Complex.exp
              (((σ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)) ∧
          ((τ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) ≠
            Complex.exp
              (((τ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)) ∧
          ((ρ (selectedExpInFull u (Fin.last (n + 2))) : generatedField u) : ℂ) =
            Complex.exp
              (((ρ (selectedInputInFull u (Fin.last (n + 2))) :
                generatedField u) : ℂ)))

/-- Every package-free terminal witness automatically has the finite quartic real-shadow
refinement. -/
theorem PositiveEigenvectorTerminalWitness.positiveQuarticRealEigenvectorTerminalWitness
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    PositiveQuarticRealEigenvectorTerminalWitness u := by
  refine ⟨W, W.isGalois_full_over_initialRealCore,
    W.finiteDimensional_full_over_initialRealCore,
    W.isMulCommutative_galoisGroup_full_over_initialRealCore,
    W.galoisGroup_full_over_initialRealCore_exponent_two,
    W.finrank_full_over_initialRealCore_eq_one_two_or_four,
    W.isKleinFour_terminalGalois_of_finrank_eq_four,
    W.nonempty_terminalGalois_mulEquiv_kleinFour,
    W.terminalSignMap_bijective_of_finrank_eq_four, ?_⟩
  exact W.exists_galois_analytic_sign_patterns_of_finrank_eq_four

/-- The strongest analytic-shadow endpoint package: it retains the full quartic Galois
description over the separate square/trace shadow, while adjoining the conjugation-fixed mixed
invariant reduces the actual graph cover to degree one or two. -/
def PositiveQuadraticAnalyticRealEigenvectorTerminalWitness
    {n : ℕ} (u : Fin (n + 3) → ℂ) : Prop :=
  PositiveQuarticRealEigenvectorTerminalWitness u ∧
    ∃ W : PositiveEigenvectorTerminalWitness u,
      let M := generatedField (Fin.init u) ⊔ eigenvectorTerminalRealCore u
      let A := generatedField (Fin.init u) ⊔ eigenvectorTerminalAnalyticRealCore u
      let F := generatedField u
      letI : Algebra M A :=
        (IntermediateField.inclusion
          (initialRealCore_le_initialAnalyticRealCore u)).toRingHom.toRatAlgHom.toAlgebra
      letI : Algebra A F :=
        (IntermediateField.inclusion
          W.initial_sup_analyticRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
      letI : Algebra M F :=
        (IntermediateField.inclusion
          W.initial_sup_terminalRealCore_le_full).toRingHom.toRatAlgHom.toAlgebra
      eigenvectorTerminalAnalyticRealCore u ≤ conjugationFixedField ∧
        Algebra.trdeg ℚ A = (((n + 2 : ℕ) : Cardinal)) ∧
        FiniteDimensional A F ∧
        IsGalois A F ∧
        Algebra.IsAlgebraic A F ∧
        (Module.finrank A F = 1 ∨ Module.finrank A F = 2) ∧
        (Nat.card Gal(F/A) = 1 ∨ Nat.card Gal(F/A) = 2) ∧
        (Module.finrank M F = 4 →
          Module.finrank M A = 2 ∧ Module.finrank A F = 2) ∧
        (Module.finrank M F = 4 → Nat.card Gal(F/A) = 2) ∧
        (Module.finrank M F = 4 →
          Nat.card W.terminalAnalyticCompatibleSubgroup = 2) ∧
        (Module.finrank M F = 4 →
          ∀ σ : Gal(F/A),
            (((σ (selectedExpInFull u (Fin.last (n + 2))) : F) : ℂ) =
              Complex.exp
                (((σ (selectedInputInFull u (Fin.last (n + 2))) : F) : ℂ)))) ∧
        (Module.finrank M F = 4 →
          ∀ (σ : Gal(F/A)) (i : Fin (n + 3)),
            (((σ (selectedExpInFull u i) : F) : ℂ) =
              Complex.exp (((σ (selectedInputInFull u i) : F) : ℂ)))) ∧
        (Module.finrank M F = 4 →
          ∀ (σ : Gal(F/A)) (m : Fin (n + 3) → ℤ),
            (((σ (integralExpInFull u m) : F) : ℂ) =
              Complex.exp (((σ (integralInputInFull u m) : F) : ℂ)))) ∧
        (Module.finrank M F = 4 →
          ∀ σ : Gal(F/A), σ ≠ 1 → ¬ Continuous σ) ∧
        (Module.finrank M F = 4 →
          ∀ σ : Gal(F/A), σ ≠ 1 →
            ∃ x : ℕ → F,
              Tendsto x atTop (𝓝 0) ∧
              Tendsto (fun k ↦ σ (x k)) atTop
                (𝓝 (2 * selectedInputInFull u (Fin.last (n + 2)))) ∧
              2 * selectedInputInFull u (Fin.last (n + 2)) ≠ 0) ∧
        (Module.finrank M F = 4 →
          ∀ σ : Gal(F/A), σ ≠ 1 → ¬ ContinuousAt σ 0) ∧
        (Module.finrank M F = 4 →
          ∀ σ : Gal(F/A), σ ≠ 1 → ∀ z : F, ¬ ContinuousAt σ z) ∧
        (∀ (σ : Gal(F/A)) (z : F), ContinuousAt σ z ↔ σ = 1) ∧
        (Module.finrank A F = 1 ↔
          ∀ σ : Gal(F/A), ContinuousAt σ 0) ∧
        (Module.finrank A F = 2 ↔
          ∃ σ : Gal(F/A), ∀ z : F, ¬ ContinuousAt σ z) ∧
        (A = F ↔ Module.finrank A F = 1) ∧
        (A = F ↔ ∀ σ : Gal(F/A), ContinuousAt σ 0) ∧
        (u (Fin.last (n + 2)) ∈ A ↔ Module.finrank A F = 1) ∧
        (A = F ↔ u (Fin.last (n + 2)) ∈ A) ∧
        (u (Fin.last (n + 2)) ∈ A ↔
          ∀ σ : Gal(F/A), ContinuousAt σ 0) ∧
        (u (Fin.last (n + 2)) ∉ A ↔ Module.finrank A F = 2) ∧
        (u (Fin.last (n + 2)) ∉ A ↔
          ∃ σ : Gal(F/A), ∀ z : F, ¬ ContinuousAt σ z) ∧
        (∀ σ : Gal(F/A), σ ≠ 1 →
          σ (selectedInputInFull u (Fin.last (n + 2))) =
              -selectedInputInFull u (Fin.last (n + 2)) ∧
            σ (selectedExpInFull u (Fin.last (n + 2))) =
              (selectedExpInFull u (Fin.last (n + 2)))⁻¹) ∧
        (∀ σ : Gal(F/A),
          (((σ (selectedExpInFull u (Fin.last (n + 2))) : F) : ℂ) =
            Complex.exp
              (((σ (selectedInputInFull u (Fin.last (n + 2))) : F) : ℂ)))) ∧
        (∀ (σ : Gal(F/A)) (i : Fin (n + 3)),
          (((σ (selectedExpInFull u i) : F) : ℂ) =
            Complex.exp (((σ (selectedInputInFull u i) : F) : ℂ)))) ∧
        (∀ (σ : Gal(F/A)) (m : Fin (n + 3) → ℤ),
          (((σ (integralExpInFull u m) : F) : ℂ) =
            Complex.exp (((σ (integralInputInFull u m) : F) : ℂ)))) ∧
        (Module.finrank A F = 2 →
          ∃! σ : Gal(F/A), σ ≠ 1 ∧
            σ (selectedInputInFull u (Fin.last (n + 2))) =
                -selectedInputInFull u (Fin.last (n + 2)) ∧
              σ (selectedExpInFull u (Fin.last (n + 2))) =
                (selectedExpInFull u (Fin.last (n + 2)))⁻¹) ∧
        (Module.finrank A F = 2 →
          Nonempty (Gal(F/A) ≃* Multiplicative (ZMod 2))) ∧
        ((A = F ∧ ∀ σ : Gal(F/A), σ = 1) ∨
          (u (Fin.last (n + 2)) ∉ A ∧ Module.finrank A F = 2 ∧
            ∃! σ : Gal(F/A), σ ≠ 1 ∧
              σ (selectedInputInFull u (Fin.last (n + 2))) =
                  -selectedInputInFull u (Fin.last (n + 2)) ∧
                σ (selectedExpInFull u (Fin.last (n + 2))) =
                  (selectedExpInFull u (Fin.last (n + 2)))⁻¹ ∧
                ∀ z : F, ¬ ContinuousAt σ z)) ∧
        (∀ σ : Gal(F/A), σ ≠ 1 →
          ∃ x : ℕ → F,
            Tendsto x atTop (𝓝 0) ∧
            Tendsto (fun k ↦ σ (x k)) atTop
              (𝓝 (2 * selectedInputInFull u (Fin.last (n + 2)))) ∧
            2 * selectedInputInFull u (Fin.last (n + 2)) ≠ 0) ∧
        (∀ σ : Gal(F/A), σ ≠ 1 → ∀ z : F,
          ∃ x : ℕ → F,
            Tendsto x atTop (𝓝 z) ∧
            Tendsto (fun k ↦ σ (x k)) atTop
              (𝓝 (σ z + 2 * selectedInputInFull u (Fin.last (n + 2)))) ∧
            σ z + 2 * selectedInputInFull u (Fin.last (n + 2)) ≠ σ z) ∧
        (Module.finrank M F = 4 →
          ∃! σ : Gal(F/A), σ ≠ 1 ∧
            σ (selectedInputInFull u (Fin.last (n + 2))) =
                -selectedInputInFull u (Fin.last (n + 2)) ∧
              σ (selectedExpInFull u (Fin.last (n + 2))) =
                (selectedExpInFull u (Fin.last (n + 2)))⁻¹) ∧
        (IntermediateField.adjoin A
          ({u (Fin.last (n + 2))} : Set ℂ)).restrictScalars ℚ = F ∧
        (Module.finrank M F = 4 → u (Fin.last (n + 2)) ∉ A)

/-- Every package-free terminal witness automatically admits the quadratic analytic-shadow
refinement. -/
theorem PositiveEigenvectorTerminalWitness.positiveQuadraticAnalyticRealEigenvectorTerminalWitness
    {n : ℕ} {u : Fin (n + 3) → ℂ}
    (W : PositiveEigenvectorTerminalWitness u) :
    PositiveQuadraticAnalyticRealEigenvectorTerminalWitness u := by
  refine ⟨W.positiveQuarticRealEigenvectorTerminalWitness, W,
    W.eigenvectorTerminalAnalyticRealCore_le_fixed,
    W.trdeg_initial_sup_terminalAnalyticRealCore_eq,
    W.finiteDimensional_full_over_initialAnalyticRealCore,
    W.isGalois_full_over_initialAnalyticRealCore,
    W.fullAlgebraic_initial_sup_terminalAnalyticRealCore,
    W.finrank_full_over_initialAnalyticRealCore_eq_one_or_two,
    W.natCard_galoisGroup_over_initialAnalytic_eq_one_or_two, ?_,
    W.natCard_initialAnalyticGalois_eq_two_of_quartic,
    ?_,
    W.galois_over_initialAnalytic_exp_compatible_of_quartic,
    W.galois_over_initialAnalytic_exp_compatible_all_of_quartic,
    W.galois_initialAnalytic_exp_integralSpan_of_quartic,
    W.nontrivial_initialAnalyticGalois_discontinuous_of_quartic,
    W.exists_discontinuity_sequence_of_quartic,
    W.nontrivial_initialAnalyticGalois_not_continuousAt_zero,
    W.nontrivial_initialAnalyticGalois_nowhere_continuous,
    W.initialAnalyticGalois_continuousAt_iff_eq_one,
    W.initialAnalytic_finrank_one_iff_continuousAt_zero,
    W.initialAnalytic_finrank_two_iff_nowhere_continuous,
    W.initialAnalytic_eq_full_iff_finrank_one,
    W.initialAnalytic_eq_full_iff_continuousAt_zero,
    W.lastInput_mem_initialAnalytic_iff_finrank_one,
    W.initialAnalytic_eq_full_iff_lastInput_mem,
    W.lastInput_mem_initialAnalytic_iff_continuousAt_zero,
    W.lastInput_not_mem_initialAnalytic_iff_finrank_two,
    W.lastInput_not_mem_initialAnalytic_iff_nowhere_continuous,
    W.galois_over_initialAnalytic_nontrivial_switch,
    W.galois_over_initialAnalytic_exp_compatible,
    W.galois_over_initialAnalytic_exp_compatible_all,
    W.galois_initialAnalytic_exp_integralSpan,
    W.existsUnique_initialAnalytic_switch_of_finrank_two,
    W.nonempty_initialAnalyticGalois_mulEquiv_zmod_two,
    W.initialAnalytic_branch_dichotomy,
    W.exists_initialAnalytic_discontinuity_sequence,
    W.exists_initialAnalytic_discontinuity_sequence_at,
    W.existsUnique_initialAnalytic_nontrivial_switch_of_quartic,
    W.restrictScalars_adjoin_lastInput_eq_fullField, ?_⟩
  · intro hfour
    exact ⟨W.finrank_initialAnalytic_over_initialRealCore_eq_two hfour,
      W.finrank_full_over_initialAnalyticRealCore_eq_two hfour⟩
  · exact W.natCard_terminalAnalyticCompatibleSubgroup_eq_two
  · exact W.lastInput_not_mem_initialAnalytic_of_finrank_eq_four

/-- The fully quantitative package-free endpoint: either the real anchor is dependent, or a
least stable failure is a finite degree-at-most-four cover of its pointwise-real shadow. -/
def QuarticRealEigenvectorTerminalNormalFormDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ realAnchorCore ∨
    (AlgebraicIndependent ℚ realAnchorCore ∧
      ∃ (n : ℕ) (u : Fin (n + 3) → ℂ),
        PositiveQuarticRealEigenvectorTerminalWitness u)

/-- Failure of Schanuel is exactly the finite-quartic real eigenvector terminal normal form. -/
theorem not_conjecture_iff_quarticRealEigenvectorTerminalNormalFormDichotomy :
    ¬ Conjecture ↔ QuarticRealEigenvectorTerminalNormalFormDichotomy := by
  rw [not_conjecture_iff_realEigenvectorTerminalNormalFormDichotomy]
  constructor
  · rintro (hdep | ⟨hcore, n, u, W⟩)
    · exact Or.inl hdep
    · exact Or.inr
        ⟨hcore, n, u, W.positiveQuarticRealEigenvectorTerminalWitness⟩
  · rintro (hdep | ⟨hcore, n, u, W, -, -⟩)
    · exact Or.inl hdep
    · exact Or.inr ⟨hcore, n, u, W⟩

/-- The sharpened endpoint dichotomy using the analytically diagonal pointwise-real shadow. -/
def QuadraticAnalyticRealEigenvectorTerminalNormalFormDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ realAnchorCore ∨
    (AlgebraicIndependent ℚ realAnchorCore ∧
      ∃ (n : ℕ) (u : Fin (n + 3) → ℂ),
        PositiveQuadraticAnalyticRealEigenvectorTerminalWitness u)

/-- Failure of Schanuel is exactly the quadratic analytic real-shadow terminal normal form. -/
theorem not_conjecture_iff_quadraticAnalyticRealEigenvectorTerminalNormalFormDichotomy :
    ¬ Conjecture ↔ QuadraticAnalyticRealEigenvectorTerminalNormalFormDichotomy := by
  rw [not_conjecture_iff_realEigenvectorTerminalNormalFormDichotomy]
  constructor
  · rintro (hdep | ⟨hcore, n, u, W⟩)
    · exact Or.inl hdep
    · exact Or.inr
        ⟨hcore, n, u, W.positiveQuadraticAnalyticRealEigenvectorTerminalWitness⟩
  · rintro (hdep | ⟨hcore, n, u, ⟨-, W, -⟩⟩)
    · exact Or.inl hdep
    · exact Or.inr ⟨hcore, n, u, W⟩

/-- A positive terminal witness together with its explicit analytic collapse/wild-switch
alternative, stripped of the larger quantitative conjunction package. -/
def PositiveAnalyticBranchEigenvectorTerminalWitness
    {n : ℕ} (u : Fin (n + 3) → ℂ) : Prop :=
  ∃ W : PositiveEigenvectorTerminalWitness u,
    W.InitialAnalyticBranchDichotomy

/-- The package-free global endpoint exposing the analytic-shadow branch literally. -/
def AnalyticBranchEigenvectorTerminalNormalFormDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ realAnchorCore ∨
    (AlgebraicIndependent ℚ realAnchorCore ∧
      ∃ (n : ℕ) (u : Fin (n + 3) → ℂ),
        PositiveAnalyticBranchEigenvectorTerminalWitness u)

/-- Failure of Schanuel is exactly anchor dependence or a positive terminal witness whose
analytic shadow either equals the full graph field or has one unique nowhere-continuous
simultaneous sign switch. -/
theorem not_conjecture_iff_analyticBranchEigenvectorTerminalNormalFormDichotomy :
    ¬ Conjecture ↔ AnalyticBranchEigenvectorTerminalNormalFormDichotomy := by
  rw [not_conjecture_iff_realEigenvectorTerminalNormalFormDichotomy]
  constructor
  · rintro (hdep | ⟨hcore, n, u, W⟩)
    · exact Or.inl hdep
    · exact Or.inr ⟨hcore, n, u, W, W.initialAnalyticBranchDichotomy⟩
  · rintro (hdep | ⟨hcore, n, u, W, -⟩)
    · exact Or.inl hdep
    · exact Or.inr ⟨hcore, n, u, W⟩

/-- On the original anchored terminal graph field, the real-anchor relative transcendence degree
is again exactly the deletion complement count.  The scaled deletion compositum proves the same
number without literal `e`-containment; canonical anchoring supplies the latter for the full
field. -/
theorem StableTerminalDeletionData.relative_trdeg_realAnchor_full_eq
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w)
    (hanchor : CanonicallyAnchored w)
    (hcore : AlgebraicIndependent ℚ realAnchorCore) :
    letI : Algebra realAnchorField (generatedField w) :=
      (IntermediateField.inclusion
        (realAnchorField_le_generatedField_of_canonicallyAnchored
          hanchor)).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg realAnchorField (generatedField w) =
      ((T.complementCount : ℕ) : Cardinal) := by
  letI : Algebra realAnchorField (generatedField w) :=
    (IntermediateField.inclusion
      (realAnchorField_le_generatedField_of_canonicallyAnchored
        hanchor)).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower ℚ realAnchorField (generatedField w) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hfull : Algebra.trdeg ℚ (generatedField w) =
      (((T.complementCount + 2 : ℕ) : Cardinal)) :=
    T.scaledDeletion_sameTrdeg.symm.trans
      (ConjugationStableTerminal.scaledDeletionSharp T)
  have hadd := trdeg_add_eq ℚ realAnchorField (A := generatedField w)
  rw [trdeg_realAnchorField_eq_two_iff_algebraicIndependent.mpr hcore,
    hfull] at hadd
  have hcancel : Algebra.trdeg realAnchorField (generatedField w) + 2 =
      (T.complementCount : Cardinal) + 2 := by
    calc
      Algebra.trdeg realAnchorField (generatedField w) + 2 =
          2 + Algebra.trdeg realAnchorField (generatedField w) := add_comm _ _
      _ = (((T.complementCount + 2 : ℕ) : Cardinal)) := hadd
      _ = (T.complementCount : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- The full anchored graph field is algebraic over the compositum of its sharp scaled deletion
field with the real anchor.  Thus the two exact relative-degree computations above are the same
terminal tower up to an algebraic top extension. -/
theorem StableTerminalDeletionData.full_isAlgebraic_realAnchor_compositum
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w)
    (hanchor : CanonicallyAnchored w) :
    let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
    let M := K ⊔ realAnchorField
    let L := generatedField w
    letI : Algebra M L :=
      (IntermediateField.inclusion
        (show M ≤ L from sup_le T.fieldLe
          (realAnchorField_le_generatedField_of_canonicallyAnchored
            hanchor))).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic M L := by
  let K := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion)
  let M := K ⊔ realAnchorField
  let L := generatedField w
  letI : Algebra K L := (stableDeletionInclusion T.fieldLe).toAlgebra
  letI : Algebra K M :=
    (IntermediateField.inclusion
      (show K ≤ M from le_sup_left)).toRingHom.toRatAlgHom.toAlgebra
  letI : Algebra M L :=
    (IntermediateField.inclusion
      (show M ≤ L from sup_le T.fieldLe
        (realAnchorField_le_generatedField_of_canonicallyAnchored
          hanchor))).toRingHom.toRatAlgHom.toAlgebra
  letI : IsScalarTower K M L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  letI : Algebra.IsAlgebraic K L := T.fullAlgebraic
  exact Algebra.IsAlgebraic.tower_top (K := K) M

/-- Equivalently, the last extension in the real-anchor terminal tower has relative
transcendence degree zero. -/
theorem StableTerminalDeletionData.relative_trdeg_full_over_realAnchor_compositum_eq_zero
    {n : ℕ} {w : Fin (n + 2) → ℂ} (T : StableTerminalDeletionData w)
    (hanchor : CanonicallyAnchored w) :
    let M := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔
      realAnchorField
    let L := generatedField w
    letI : Algebra M L :=
      (IntermediateField.inclusion
        (show M ≤ L from sup_le T.fieldLe
          (realAnchorField_le_generatedField_of_canonicallyAnchored
            hanchor))).toRingHom.toRatAlgHom.toAlgebra
    Algebra.trdeg M L = 0 := by
  let M := generatedField (ratScaleFamily (T.scale : ℚ) T.deletion) ⊔
    realAnchorField
  let L := generatedField w
  letI : Algebra M L :=
    (IntermediateField.inclusion
      (show M ≤ L from sup_le T.fieldLe
        (realAnchorField_le_generatedField_of_canonicallyAnchored
          hanchor))).toRingHom.toRatAlgHom.toAlgebra
  letI : Algebra.IsAlgebraic M L :=
    StableTerminalDeletionData.full_isAlgebraic_realAnchor_compositum T hanchor
  exact trdeg_eq_zero

/-- The real-sector basis remains independent after the standard period is appended. -/
theorem SectorBasisData.plusWithPeriod_linearIndependent
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    LinearIndependent ℚ D.plusWithPeriod := by
  have hu : LinearIndependent ℚ (R.subtype ∘ D.plusBasis) :=
    D.plusLinearIndependent.map' R.subtype (Submodule.ker_subtype R)
  have hv : LinearIndependent ℚ (fun _ : Fin 1 ↦ standardPeriod) := by
    rw [linearIndependent_unique_iff]
    exact FullyTranscendentalPeriodBoundary.period_ne_zero
  apply linearIndependent_append_of_disjoint_spans hu hv
  have hplus : Submodule.span ℚ (Set.range (R.subtype ∘ D.plusBasis)) =
      (plusSector R hR).map R.subtype := by
    rw [Set.range_comp, Submodule.span_image, D.plusSpan]
  have hperiod : Submodule.span ℚ (Set.range (fun _ : Fin 1 ↦ standardPeriod)) ≤
      (minusSector R hR).map R.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨periodInStableSubspace R haR, period_mem_minusSector R hR haR, rfl⟩
  rw [hplus]
  exact (Submodule.disjoint_map R.subtype_injective (sectors_disjoint R hR)).mono
    le_rfl hperiod

/-- The real-sector basis followed by the period has stable rational span. -/
theorem SectorBasisData.plusWithPeriod_conjugationStable
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    ConjugationStable D.plusWithPeriod := by
  apply conjugationStable_append
  · unfold ConjugationStable
    have hfixed : conjugateFamily (R.subtype ∘ D.plusBasis) =
        R.subtype ∘ D.plusBasis := by
      funext i
      have hi : D.plusBasis i ∈ plusSector R hR := by
        rw [← D.plusSpan]
        exact Submodule.subset_span (Set.mem_range_self i)
      have hci := (mem_plusSector_iff R hR (D.plusBasis i)).mp hi
      exact congrArg ((↑) : R → ℂ) hci
    rw [hfixed]
  · unfold ConjugationStable
    have hanti : conjugateFamily (fun _ : Fin 1 ↦ standardPeriod) =
        fun _ : Fin 1 ↦ -standardPeriod := by
      funext i
      simpa [conjugateFamily] using star_standardPeriod
    rw [hanti]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (Submodule.span ℚ (Set.range (fun _ : Fin 1 ↦ standardPeriod))).neg_mem
        (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hmem := (Submodule.span ℚ
        (Set.range (fun _ : Fin 1 ↦ -standardPeriod))).neg_mem
          (Submodule.subset_span (Set.mem_range_self i))
      simpa using hmem

theorem SectorBasisData.one_mem_span_plusWithPeriod
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    (1 : ℂ) ∈ Submodule.span ℚ (Set.range D.plusWithPeriod) := by
  have hmem : D.plusWithPeriod
      (Fin.castAdd 1 (0 : Fin (D.plusComplementCount + 1))) ∈
      Submodule.span ℚ (Set.range D.plusWithPeriod) :=
    Submodule.subset_span (Set.mem_range_self _)
  simpa [SectorBasisData.plusWithPeriod, D.plus_zero] using hmem

theorem SectorBasisData.period_mem_span_plusWithPeriod
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    standardPeriod ∈ Submodule.span ℚ (Set.range D.plusWithPeriod) := by
  have hmem : D.plusWithPeriod
      (Fin.natAdd (D.plusComplementCount + 1) (0 : Fin 1)) ∈
      Submodule.span ℚ (Set.range D.plusWithPeriod) :=
    Submodule.subset_span (Set.mem_range_self _)
  simpa [SectorBasisData.plusWithPeriod] using hmem

theorem SectorBasisData.anchor_le_span_plusWithPeriod
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range D.plusWithPeriod) :=
  canonicalAnchor_span_le_of_one_period_mem D.one_mem_span_plusWithPeriod
    D.period_mem_span_plusWithPeriod

theorem SectorBasisData.span_plusWithPeriod_le
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Submodule.span ℚ (Set.range D.plusWithPeriod) ≤ R := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simp [SectorBasisData.plusWithPeriod]
  · simpa [SectorBasisData.plusWithPeriod] using standardPeriod_mem_of_anchor_le R haR

/-- If the anti-fixed sector has a direction beyond the period, the real sector plus the period
is a proper stable anchored subspace of the full space. -/
theorem SectorBasisData.span_plusWithPeriod_lt
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hq : 0 < D.minusComplementCount) :
    Submodule.span ℚ (Set.range D.plusWithPeriod) < R := by
  apply Submodule.lt_of_le_of_finrank_lt_finrank D.span_plusWithPeriod_le
  have hleft : Module.finrank ℚ (Submodule.span ℚ (Set.range D.plusWithPeriod)) =
      (D.plusComplementCount + 1) + 1 := by
    simpa using finrank_span_eq_card D.plusWithPeriod_linearIndependent
  have hright : Module.finrank ℚ R =
      (D.plusComplementCount + 1) + (D.minusComplementCount + 1) := by
    have h := finrank_span_eq_card D.joined_linearIndependent
    rw [D.joined_span] at h
    simpa using h
  rw [hleft, hright]
  omega

/-- The anti-fixed-sector basis remains independent after the real unit is prepended. -/
theorem SectorBasisData.oneWithMinus_linearIndependent
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    LinearIndependent ℚ D.oneWithMinus := by
  have hu : LinearIndependent ℚ (fun _ : Fin 1 ↦ (1 : ℂ)) := by
    rw [linearIndependent_unique_iff]
    norm_num
  have hv : LinearIndependent ℚ (R.subtype ∘ D.minusBasis) :=
    D.minusLinearIndependent.map' R.subtype (Submodule.ker_subtype R)
  apply linearIndependent_append_of_disjoint_spans hu hv
  have hone : Submodule.span ℚ (Set.range (fun _ : Fin 1 ↦ (1 : ℂ))) ≤
      (plusSector R hR).map R.subtype := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact ⟨oneInStableSubspace R haR, one_mem_plusSector R hR haR, rfl⟩
  have hminus : Submodule.span ℚ (Set.range (R.subtype ∘ D.minusBasis)) =
      (minusSector R hR).map R.subtype := by
    rw [Set.range_comp, Submodule.span_image, D.minusSpan]
  rw [hminus]
  exact (Submodule.disjoint_map R.subtype_injective (sectors_disjoint R hR)).mono
    hone le_rfl

/-- The real unit followed by the anti-fixed-sector basis has stable rational span. -/
theorem SectorBasisData.oneWithMinus_conjugationStable
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    ConjugationStable D.oneWithMinus := by
  apply conjugationStable_append
  · unfold ConjugationStable
    have hfixed : conjugateFamily (fun _ : Fin 1 ↦ (1 : ℂ)) =
        fun _ : Fin 1 ↦ (1 : ℂ) := by
      funext i
      simp [conjugateFamily]
    rw [hfixed]
  · unfold ConjugationStable
    have hanti : conjugateFamily (R.subtype ∘ D.minusBasis) =
        fun i ↦ -(R.subtype (D.minusBasis i)) := by
      funext i
      have hi : D.minusBasis i ∈ minusSector R hR := by
        rw [← D.minusSpan]
        exact Submodule.subset_span (Set.mem_range_self i)
      have hci := (mem_minusSector_iff R hR (D.minusBasis i)).mp hi
      exact congrArg ((↑) : R → ℂ) hci
    rw [hanti]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      exact (Submodule.span ℚ (Set.range (R.subtype ∘ D.minusBasis))).neg_mem
        (Submodule.subset_span ⟨i, rfl⟩)
    · apply Submodule.span_le.mpr
      rintro _ ⟨i, rfl⟩
      have hmem := (Submodule.span ℚ
        (Set.range (fun i ↦ -(R.subtype (D.minusBasis i))))).neg_mem
          (Submodule.subset_span (Set.mem_range_self i))
      simpa using hmem

theorem SectorBasisData.one_mem_span_oneWithMinus
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    (1 : ℂ) ∈ Submodule.span ℚ (Set.range D.oneWithMinus) := by
  have hmem : D.oneWithMinus
      (Fin.castAdd (D.minusComplementCount + 1) (0 : Fin 1)) ∈
      Submodule.span ℚ (Set.range D.oneWithMinus) :=
    Submodule.subset_span (Set.mem_range_self _)
  simpa [SectorBasisData.oneWithMinus] using hmem

theorem SectorBasisData.period_mem_span_oneWithMinus
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    standardPeriod ∈ Submodule.span ℚ (Set.range D.oneWithMinus) := by
  have hmem : D.oneWithMinus
      (Fin.natAdd 1 (0 : Fin (D.minusComplementCount + 1))) ∈
      Submodule.span ℚ (Set.range D.oneWithMinus) :=
    Submodule.subset_span (Set.mem_range_self _)
  simpa [SectorBasisData.oneWithMinus, D.minus_zero] using hmem

theorem SectorBasisData.anchor_le_span_oneWithMinus
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range D.oneWithMinus) :=
  canonicalAnchor_span_le_of_one_period_mem D.one_mem_span_oneWithMinus
    D.period_mem_span_oneWithMinus

theorem SectorBasisData.span_oneWithMinus_le
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR) :
    Submodule.span ℚ (Set.range D.oneWithMinus) ≤ R := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) i
  · simpa [SectorBasisData.oneWithMinus] using one_mem_of_anchor_le R haR
  · simp [SectorBasisData.oneWithMinus]

/-- If the fixed sector has a direction beyond `1`, the anti-fixed sector plus `1` is a proper
stable anchored subspace of the full space. -/
theorem SectorBasisData.span_oneWithMinus_lt
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    (hp : 0 < D.plusComplementCount) :
    Submodule.span ℚ (Set.range D.oneWithMinus) < R := by
  apply Submodule.lt_of_le_of_finrank_lt_finrank D.span_oneWithMinus_le
  have hleft : Module.finrank ℚ (Submodule.span ℚ (Set.range D.oneWithMinus)) =
      1 + (D.minusComplementCount + 1) := by
    simpa using finrank_span_eq_card D.oneWithMinus_linearIndependent
  have hright : Module.finrank ℚ R =
      (D.plusComplementCount + 1) + (D.minusComplementCount + 1) := by
    have h := finrank_span_eq_card D.joined_linearIndependent
    rw [D.joined_span] at h
    simpa using h
  rw [hleft, hright]
  omega

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

/-- The preceding least-failure bound is independent of the chosen basis of the proper stable
anchored subspace.  In particular, the basis used to compute its graph field need not itself
display the canonical anchor in its first two coordinates. -/
theorem bound_of_basis_of_proper_stable_anchored_subspace
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    {m : ℕ} {v : Fin m → ℂ} (hvlin : LinearIndependent ℚ v)
    (P : Submodule ℚ ℂ)
    (haP : Submodule.span ℚ (Set.range canonicalAnchor) ≤ P)
    (hPstable : P.map conjugationLinearEquiv.toLinearMap = P)
    (hPlt : P < Submodule.span ℚ (Set.range w))
    (hvspan : Submodule.span ℚ (Set.range v) = P) : Bound v := by
  obtain ⟨k, u, hulin, _, _, huspan, huBound⟩ :=
    exists_bound_basis_of_proper_stable_anchored_subspace
      hwlin hmin P haP hPstable hPlt
  have hcard : m = k + 2 := by
    calc
      m = Module.finrank ℚ (Submodule.span ℚ (Set.range v)) := by
        simpa using (finrank_span_eq_card hvlin).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range u)) := by
        rw [hvspan, huspan]
      _ = k + 2 := by simpa using finrank_span_eq_card hulin
  unfold Bound at huBound ⊢
  rw [trdeg_generatedField_eq_of_span_eq v u (hvspan.trans huspan.symm)]
  simpa [hcard] using huBound

/-- CS12, in basis-level form: at a least stable failure, if the anti-fixed sector has a
direction beyond the period, then the full real-sector basis together with the period satisfies
its Schanuel bound. -/
theorem SectorBasisData.bound_plusWithPeriod_of_least_failure
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hq : 0 < D.minusComplementCount) : Bound D.plusWithPeriod := by
  apply bound_of_basis_of_proper_stable_anchored_subspace
    hwlin hmin D.plusWithPeriod_linearIndependent
    (Submodule.span ℚ (Set.range D.plusWithPeriod))
    D.anchor_le_span_plusWithPeriod
  · rw [map_span_conjugation_eq]
    exact D.plusWithPeriod_conjugationStable
  · calc
      Submodule.span ℚ (Set.range D.plusWithPeriod) < R :=
        D.span_plusWithPeriod_lt hq
      _ = Submodule.span ℚ (Set.range w) := hwspan.symm
  · rfl

/-- CS13, in basis-level form: at a least stable failure, if the fixed sector has a direction
beyond `1`, then `1` together with the full anti-fixed-sector basis satisfies its Schanuel
bound. -/
theorem SectorBasisData.bound_oneWithMinus_of_least_failure
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hp : 0 < D.plusComplementCount) : Bound D.oneWithMinus := by
  apply bound_of_basis_of_proper_stable_anchored_subspace
    hwlin hmin D.oneWithMinus_linearIndependent
    (Submodule.span ℚ (Set.range D.oneWithMinus))
    D.anchor_le_span_oneWithMinus
  · rw [map_span_conjugation_eq]
    exact D.oneWithMinus_conjugationStable
  · calc
      Submodule.span ℚ (Set.range D.oneWithMinus) < R :=
        D.span_oneWithMinus_lt hp
      _ = Submodule.span ℚ (Set.range w) := hwspan.symm
  · rfl

/-- CS12: once there is a non-period anti-fixed direction, the real-sector graph field itself
has at least its full sector dimension in transcendence degree. -/
theorem SectorBasisData.plusSector_trdeg_ge_of_least_failure
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hq : 0 < D.minusComplementCount) :
    (((D.plusComplementCount + 1 : ℕ) : Cardinal)) ≤
      Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis)) := by
  have hb := D.bound_plusWithPeriod_of_least_failure hwlin hmin hwspan hq
  unfold Bound at hb
  have htd := (IntermediateField.equivOfEq D.generatedField_plusWithPeriod).trdeg_eq
  have hb' : Cardinal.mk (Fin ((D.plusComplementCount + 1) + 1)) ≤
      Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          generatedField (fun _ : Fin 1 ↦ standardPeriod))) :=
    hb.trans_eq htd
  have hsup := trdeg_sup_le_add
    (generatedField (R.subtype ∘ D.plusBasis))
    (generatedField (fun _ : Fin 1 ↦ standardPeriod))
  have hupper : Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          generatedField (fun _ : Fin 1 ↦ standardPeriod))) ≤
      Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis)) + 1 :=
    hsup.trans (add_le_add le_rfl trdeg_generatedField_periodSingleton_le_one)
  have htotal := hb'.trans hupper
  apply Cardinal.add_one_le_add_one_iff.mp
  simpa [Nat.cast_add] using htotal

/-- CS13: once there is a non-unit fixed direction, the anti-fixed-sector graph field itself
has at least its full sector dimension in transcendence degree. -/
theorem SectorBasisData.minusSector_trdeg_ge_of_least_failure
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hp : 0 < D.plusComplementCount) :
    (((D.minusComplementCount + 1 : ℕ) : Cardinal)) ≤
      Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.minusBasis)) := by
  have hb := D.bound_oneWithMinus_of_least_failure hwlin hmin hwspan hp
  unfold Bound at hb
  have htd := (IntermediateField.equivOfEq D.generatedField_oneWithMinus).trdeg_eq
  have hb' : Cardinal.mk (Fin (1 + (D.minusComplementCount + 1))) ≤
      Algebra.trdeg ℚ
        (↥(generatedField (fun _ : Fin 1 ↦ (1 : ℂ)) ⊔
          generatedField (R.subtype ∘ D.minusBasis))) :=
    hb.trans_eq htd
  have hsup := trdeg_sup_le_add
    (generatedField (fun _ : Fin 1 ↦ (1 : ℂ)))
    (generatedField (R.subtype ∘ D.minusBasis))
  have hupper : Algebra.trdeg ℚ
        (↥(generatedField (fun _ : Fin 1 ↦ (1 : ℂ)) ⊔
          generatedField (R.subtype ∘ D.minusBasis))) ≤
      1 + Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.minusBasis)) :=
    hsup.trans (add_le_add trdeg_generatedField_oneSingleton_le_one le_rfl)
  have htotal := hb'.trans hupper
  have htotal' : (((D.minusComplementCount + 1 : ℕ) : Cardinal)) + 1 ≤
      Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.minusBasis)) + 1 := by
    simpa [Nat.cast_add, add_comm] using htotal
  exact Cardinal.add_one_le_add_one_iff.mp htotal'

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

/-- The defect-one compositum degree is exactly one below the sum of the two sector dimensions. -/
theorem SectorBasisData.compositum_trdeg_add_one_eq_total_of_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w) :
    Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          generatedField (R.subtype ∘ D.minusBasis))) + 1 =
      (((D.plusComplementCount + 1 : ℕ) : Cardinal)) +
        (((D.minusComplementCount + 1 : ℕ) : Cardinal)) := by
  rw [D.compositum_trdeg_of_defectOne hwspan hwdefect]
  have htotal := D.total_count_eq hwlin hwspan
  norm_cast
  omega

/-- The one-unit compositum deficit remains exact after replacing the anti-fixed graph field by
its minimal even core; unlike the individual sector lower bounds, this identity requires no
positivity assumption on either sector complement. -/
theorem SectorBasisData.compositum_evenCore_trdeg_add_one_eq_total_of_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w) :
    Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          antiFixedEvenCore (R.subtype ∘ D.minusBasis))) + 1 =
      (((D.plusComplementCount + 1 : ℕ) : Cardinal)) +
        (((D.minusComplementCount + 1 : ℕ) : Cardinal)) := by
  have h := D.compositum_trdeg_add_one_eq_total_of_defectOne
    hwlin hwspan hwdefect
  have hu0 : (R.subtype ∘ D.minusBasis) 0 = standardPeriod := by
    simpa using congrArg ((↑) : R → ℂ) D.minus_zero
  rw [← trdeg_sup_generatedField_eq_sup_antiFixedEvenCore
    (generatedField (R.subtype ∘ D.plusBasis))
    (R.subtype ∘ D.minusBasis) hu0]
  exact h

/-- Exact one-sided real boundary when the fixed sector is only the distinguished unit: that
sector is `Q(e)` of degree one, and its compositum with the even anti-fixed core has degree equal
to the full anti-fixed-sector dimension. -/
theorem SectorBasisData.plusSingleton_evenBoundary_of_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w)
    (hp : D.plusComplementCount = 0) :
    Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis)) = 1 ∧
      Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          antiFixedEvenCore (R.subtype ∘ D.minusBasis))) =
        (((D.minusComplementCount + 1 : ℕ) : Cardinal)) := by
  refine ⟨D.plusBasis_trdeg_eq_one_of_eq_zero hp, ?_⟩
  apply Cardinal.add_one_inj.mp
  have h := D.compositum_evenCore_trdeg_add_one_eq_total_of_defectOne
    hwlin hwspan hwdefect
  simpa [hp, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h

/-- Exact one-sided real boundary when the anti-fixed sector is only the distinguished period:
its even core is `Q(pi^2)` of degree one, and the compositum has degree equal to the full fixed
sector dimension. -/
theorem SectorBasisData.minusSingleton_evenBoundary_of_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w)
    (hq : D.minusComplementCount = 0) :
    Algebra.trdeg ℚ (antiFixedEvenCore (R.subtype ∘ D.minusBasis)) = 1 ∧
      Algebra.trdeg ℚ
        (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
          antiFixedEvenCore (R.subtype ∘ D.minusBasis))) =
        (((D.plusComplementCount + 1 : ℕ) : Cardinal)) := by
  refine ⟨D.minusEvenCore_trdeg_eq_one_of_eq_zero hq, ?_⟩
  apply Cardinal.add_one_inj.mp
  have h := D.compositum_evenCore_trdeg_add_one_eq_total_of_defectOne
    hwlin hwspan hwdefect
  simpa [hq, Nat.cast_add, add_comm, add_left_comm, add_assoc] using h

/-- CS12--CS14 in one statement: away from the two one-dimensional sector boundaries, each
sector field meets its own dimensional lower bound, while their compositum has exactly one unit
less than the sum of those dimensions.  The remaining obstruction is therefore genuinely
cross-sector. -/
theorem SectorBasisData.exact_two_sector_boundary_of_least_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w)
    (hp : 0 < D.plusComplementCount)
    (hq : 0 < D.minusComplementCount) :
    (((D.plusComplementCount + 1 : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis))) ∧
      (((D.minusComplementCount + 1 : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.minusBasis))) ∧
      Algebra.trdeg ℚ
          (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
            generatedField (R.subtype ∘ D.minusBasis))) + 1 =
        (((D.plusComplementCount + 1 : ℕ) : Cardinal)) +
          (((D.minusComplementCount + 1 : ℕ) : Cardinal)) := by
  exact ⟨D.plusSector_trdeg_ge_of_least_failure hwlin hmin hwspan hq,
    D.minusSector_trdeg_ge_of_least_failure hwlin hmin hwspan hp,
    D.compositum_trdeg_add_one_eq_total_of_defectOne hwlin hwspan hwdefect⟩

/-- Lossless real form of CS12--CS14: the plus-sector graph field and the explicit pointwise-real
core of the minus sector each meet their sector dimension, while their compositum has the same
exact one-unit deficit. -/
theorem SectorBasisData.exact_two_real_sector_boundary_of_least_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w)
    (hp : 0 < D.plusComplementCount)
    (hq : 0 < D.minusComplementCount) :
    (((D.plusComplementCount + 1 : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis))) ∧
      (((D.minusComplementCount + 1 : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (antiFixedRealCore (R.subtype ∘ D.minusBasis))) ∧
      Algebra.trdeg ℚ
          (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
            antiFixedRealCore (R.subtype ∘ D.minusBasis))) + 1 =
        (((D.plusComplementCount + 1 : ℕ) : Cardinal)) +
          (((D.minusComplementCount + 1 : ℕ) : Cardinal)) := by
  have h := D.exact_two_sector_boundary_of_least_defectOne
    hwlin hmin hwspan hwdefect hp hq
  refine ⟨h.1, ?_, ?_⟩
  · rw [← D.trdeg_minusBasis_eq_realCore]
    exact h.2.1
  · have hu0 : (R.subtype ∘ D.minusBasis) 0 = standardPeriod := by
      simpa using congrArg ((↑) : R → ℂ) D.minus_zero
    rw [← trdeg_sup_generatedField_eq_sup_antiFixedRealCore
      (generatedField (R.subtype ∘ D.plusBasis))
      (R.subtype ∘ D.minusBasis) hu0]
    exact h.2.2

/-- Minimal-generator real form of CS12--CS14: the imaginary side is reduced further to the
field generated by the squared period, normalized imaginary inputs, and cosine traces.  The
normalized sine generators are only quadratic and do not affect any displayed degree. -/
theorem SectorBasisData.exact_two_even_sector_boundary_of_least_defectOne
    {R : Submodule ℚ ℂ} {hR} {haR} (D : SectorBasisData R hR haR)
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hwspan : Submodule.span ℚ (Set.range w) = R)
    (hwdefect : DefectOne w)
    (hp : 0 < D.plusComplementCount)
    (hq : 0 < D.minusComplementCount) :
    (((D.plusComplementCount + 1 : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (generatedField (R.subtype ∘ D.plusBasis))) ∧
      (((D.minusComplementCount + 1 : ℕ) : Cardinal) ≤
        Algebra.trdeg ℚ (antiFixedEvenCore (R.subtype ∘ D.minusBasis))) ∧
      Algebra.trdeg ℚ
          (↥(generatedField (R.subtype ∘ D.plusBasis) ⊔
            antiFixedEvenCore (R.subtype ∘ D.minusBasis))) + 1 =
        (((D.plusComplementCount + 1 : ℕ) : Cardinal)) +
          (((D.minusComplementCount + 1 : ℕ) : Cardinal)) := by
  have h := D.exact_two_sector_boundary_of_least_defectOne
    hwlin hmin hwspan hwdefect hp hq
  refine ⟨h.1, ?_, ?_⟩
  · rw [← D.trdeg_minusBasis_eq_evenCore]
    exact h.2.1
  · have hu0 : (R.subtype ∘ D.minusBasis) 0 = standardPeriod := by
      simpa using congrArg ((↑) : R → ℂ) D.minus_zero
    rw [← trdeg_sup_generatedField_eq_sup_antiFixedEvenCore
      (generatedField (R.subtype ∘ D.plusBasis))
      (R.subtype ∘ D.minusBasis) hu0]
    exact h.2.2

/-- Every positive least stable failure admits distinguished sector bases whose dimensions add
to the full arity.  If both sectors contain a non-anchor direction, the minimal-generator real
CS12--CS14 endpoint follows automatically.  This packages all hypotheses retained by the global
positive-least terminal alternative. -/
theorem PositiveLeastConjugationStableFailure.exists_evenSectorBoundary
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (H : PositiveLeastConjugationStableFailure w) :
    ∃ (hR : (Submodule.span ℚ (Set.range w)).map
          conjugationLinearEquiv.toLinearMap = Submodule.span ℚ (Set.range w))
      (haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤
        Submodule.span ℚ (Set.range w))
      (D : SectorBasisData (Submodule.span ℚ (Set.range w)) hR haR),
      (D.plusComplementCount + 1) + (D.minusComplementCount + 1) = n + 2 ∧
      ((D.plusComplementCount = 0 ∧ 0 < D.minusComplementCount) ∨
        (0 < D.plusComplementCount ∧ D.minusComplementCount = 0) ∨
        (0 < D.plusComplementCount ∧ 0 < D.minusComplementCount)) ∧
      (0 < D.plusComplementCount ∧ 0 < D.minusComplementCount →
        (((D.plusComplementCount + 1 : ℕ) : Cardinal) ≤
            Algebra.trdeg ℚ (generatedField
              ((Submodule.span ℚ (Set.range w)).subtype ∘ D.plusBasis))) ∧
          (((D.minusComplementCount + 1 : ℕ) : Cardinal) ≤
            Algebra.trdeg ℚ (antiFixedEvenCore
              ((Submodule.span ℚ (Set.range w)).subtype ∘ D.minusBasis))) ∧
          Algebra.trdeg ℚ
              (↥(generatedField
                  ((Submodule.span ℚ (Set.range w)).subtype ∘ D.plusBasis) ⊔
                antiFixedEvenCore
                  ((Submodule.span ℚ (Set.range w)).subtype ∘ D.minusBasis))) + 1 =
            (((D.plusComplementCount + 1 : ℕ) : Cardinal)) +
              (((D.minusComplementCount + 1 : ℕ) : Cardinal))) := by
  rcases H with ⟨hn, hwlin, hwanchor, hwstable, hwfail, hmin⟩
  let R := Submodule.span ℚ (Set.range w)
  letI : FiniteDimensional ℚ R :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  have hR : R.map conjugationLinearEquiv.toLinearMap = R := by
    rw [map_span_conjugation_eq]
    exact hwstable
  have haR : Submodule.span ℚ (Set.range canonicalAnchor) ≤ R :=
    span_canonicalAnchor_le_of_canonicallyAnchored hwanchor
  obtain ⟨D⟩ := nonempty_sectorBasisData R hR haR
  have hwdefect :=
    defectOne_of_no_smaller_conjugationStableCanonicalAnchored_failure
      hwlin hwanchor hwstable hwfail hmin
  have htotal := D.total_count_eq hwlin rfl
  have hcases :
      (D.plusComplementCount = 0 ∧ 0 < D.minusComplementCount) ∨
        (0 < D.plusComplementCount ∧ D.minusComplementCount = 0) ∨
        (0 < D.plusComplementCount ∧ 0 < D.minusComplementCount) := by
    by_cases hp : D.plusComplementCount = 0
    · exact Or.inl ⟨hp, by omega⟩
    · by_cases hq : D.minusComplementCount = 0
      · exact Or.inr (Or.inl ⟨Nat.pos_of_ne_zero hp, hq⟩)
      · exact Or.inr (Or.inr ⟨Nat.pos_of_ne_zero hp, Nat.pos_of_ne_zero hq⟩)
  refine ⟨hR, haR, D, htotal, hcases, ?_⟩
  rintro ⟨hp, hq⟩
  exact D.exact_two_even_sector_boundary_of_least_defectOne
    hwlin hmin rfl hwdefect hp hq

end ConjugationStableSectorBoundary

end

end Schanuel
