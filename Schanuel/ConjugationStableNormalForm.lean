import Schanuel.CanonicalAnchorRelativeTerminal
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Combinatorics.Matroid.Rank.Cardinal
import Mathlib.FieldTheory.AlgebraicClosure

/-!
# Conjugation-stable canonical-anchor normal forms

This module packages the conjugation-stability condition on a finite rational input family and
the linear stable-closure construction.  The condition is basis-independent: it is equality of
the rational span with the span of the coordinatewise conjugate family.
-/

namespace Schanuel

open Function Set

noncomputable section

namespace ConjugationStableNormalForm

/-- The algebraic matroid of complex numbers over the rationals. -/
abbrev complexAlgebraicMatroid : Matroid ℂ := AlgebraicIndependent.matroid ℚ ℂ

/-- The cardinal rank of the carrier of an intermediate field is its transcendence degree. -/
theorem cRk_coe_intermediateField_eq_trdeg (L : IntermediateField ℚ ℂ) :
    complexAlgebraicMatroid.cRk (L : Set ℂ) = Algebra.trdeg ℚ L := by
  apply le_antisymm
  · obtain ⟨I, hI⟩ := complexAlgebraicMatroid.exists_isBasis' (L : Set ℂ)
    let x : I → L := fun i ↦ ⟨i.1, hI.subset i.2⟩
    have hxC : AlgebraicIndependent ℚ ((↑) : I → ℂ) := by
      exact AlgebraicIndependent.matroid_indep_iff.mp hI.indep
    have hx : AlgebraicIndependent ℚ x := by
      apply AlgebraicIndependent.of_comp L.val
      simpa [x, Function.comp_def] using hxC
    rw [← hI.cardinalMk_eq_cRk]
    exact hx.cardinalMk_le_trdeg
  · obtain ⟨ι, x, hx⟩ := exists_isTranscendenceBasis' ℚ L
    let y : ι → ℂ := fun i ↦ (x i : ℂ)
    have hy : AlgebraicIndependent ℚ y := by
      exact hx.1.map (f := L.val) L.val.injective.injOn
    have hyIndep : complexAlgebraicMatroid.Indep (Set.range y) := by
      exact AlgebraicIndependent.matroid_indep_iff.mpr hy.to_subtype_range
    calc
      Algebra.trdeg ℚ L = Cardinal.mk ι := hx.cardinalMk_eq_trdeg.symm
      _ = Cardinal.mk (Set.range y) := by
        simpa using (Cardinal.mk_range_eq_of_injective hy.injective).symm
      _ = complexAlgebraicMatroid.cRk (Set.range y) := hyIndep.cRk_eq_cardinalMk
      _ ≤ complexAlgebraicMatroid.cRk (L : Set ℂ) :=
        complexAlgebraicMatroid.cRk_le_of_subset (by
          rintro z ⟨i, rfl⟩
          exact (x i).2)

/-- Algebraic-matroid rank of a set is the transcendence degree of its generated field. -/
theorem cRk_eq_trdeg_adjoin (X : Set ℂ) :
    complexAlgebraicMatroid.cRk X =
      Algebra.trdeg ℚ (IntermediateField.adjoin ℚ X) := by
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ X
  have hXL : X ⊆ (L : Set ℂ) := IntermediateField.subset_adjoin ℚ X
  have hLcl : (L : Set ℂ) ⊆ complexAlgebraicMatroid.closure X := by
    intro z hz
    rw [AlgebraicIndependent.matroid_closure_eq, SetLike.mem_coe,
      Subalgebra.mem_algebraicClosure]
    let A : Subalgebra ℚ ℂ := Algebra.adjoin ℚ X
    let zL : L := ⟨z, hz⟩
    letI : Algebra A L :=
      (Subalgebra.inclusion (IntermediateField.algebra_adjoin_le_adjoin ℚ X)).toAlgebra
    letI : IsScalarTower ℚ A L := by
      apply IsScalarTower.of_algebraMap_eq'
      ext q
      rfl
    letI : Algebra.IsAlgebraic A L := by
      change Algebra.IsAlgebraic (Algebra.adjoin ℚ X)
        (IntermediateField.adjoin ℚ X)
      open scoped IntermediateField.algebraAdjoinAdjoin in
        infer_instance
    let f : L →ₐ[A] ℂ :=
      { L.val with
        commutes' := fun _ ↦ rfl }
    have hzAlg : IsAlgebraic A zL := Algebra.IsAlgebraic.isAlgebraic zL
    simpa [A, zL, f] using hzAlg.algHom f
  apply le_antisymm
  · calc
      complexAlgebraicMatroid.cRk X ≤
          complexAlgebraicMatroid.cRk (L : Set ℂ) :=
        complexAlgebraicMatroid.cRk_le_of_subset hXL
      _ = Algebra.trdeg ℚ L := cRk_coe_intermediateField_eq_trdeg L
  · calc
      Algebra.trdeg ℚ L = complexAlgebraicMatroid.cRk (L : Set ℂ) :=
        (cRk_coe_intermediateField_eq_trdeg L).symm
      _ ≤ complexAlgebraicMatroid.cRk (complexAlgebraicMatroid.closure X) :=
        complexAlgebraicMatroid.cRk_le_of_subset hLcl
      _ = complexAlgebraicMatroid.cRk X :=
        complexAlgebraicMatroid.cRk_closure X

/-- Transcendence degree is submodular on intermediate subfields of `ℂ / ℚ`. -/
theorem trdeg_inf_add_trdeg_sup_le (K L : IntermediateField ℚ ℂ) :
    Algebra.trdeg ℚ (↥(K ⊓ L)) + Algebra.trdeg ℚ (↥(K ⊔ L)) ≤
      Algebra.trdeg ℚ K + Algebra.trdeg ℚ L := by
  have h := complexAlgebraicMatroid.cRk_inter_add_cRk_union_le
    (K : Set ℂ) (L : Set ℂ)
  rw [show (K : Set ℂ) ∩ (L : Set ℂ) = ((K ⊓ L : IntermediateField ℚ ℂ) : Set ℂ) by
      rfl,
    cRk_coe_intermediateField_eq_trdeg,
    cRk_eq_trdeg_adjoin,
    ← IntermediateField.sup_def,
    cRk_coe_intermediateField_eq_trdeg,
    cRk_coe_intermediateField_eq_trdeg] at h
  exact h

/-- A finite transcendence-degree field has finite-degree intersections with every other
intermediate field. -/
theorem trdeg_inf_lt_aleph0_of_left {K L : IntermediateField ℚ ℂ}
    (hK : Algebra.trdeg ℚ K < Cardinal.aleph0) :
    Algebra.trdeg ℚ (↥(K ⊓ L)) < Cardinal.aleph0 := by
  exact (trdeg_le_of_injective (IntermediateField.inclusion inf_le_left)
    (IntermediateField.inclusion_injective inf_le_left)).trans_lt hK

/-- Coordinatewise complex conjugation of a finite family. -/
def conjugateFamily {n : ℕ} (w : Fin n → ℂ) : Fin n → ℂ :=
  fun i ↦ star (w i)

/-- The rational-linear involution underlying complex conjugation. -/
def conjugationLinearEquiv : ℂ ≃ₗ[ℚ] ℂ :=
  (Complex.conjAe.restrictScalars ℚ).toLinearEquiv

/-- Complex conjugation as a rational algebra automorphism. -/
def conjugationAlgEquiv : ℂ ≃ₐ[ℚ] ℂ :=
  Complex.conjAe.restrictScalars ℚ

@[simp]
theorem conjugationLinearEquiv_apply (z : ℂ) :
    conjugationLinearEquiv z = star z := rfl

@[simp]
theorem conjugateFamily_apply {n : ℕ} (w : Fin n → ℂ) (i : Fin n) :
    conjugateFamily w i = star (w i) := rfl

@[simp]
theorem conjugateFamily_conjugateFamily {n : ℕ} (w : Fin n → ℂ) :
    conjugateFamily (conjugateFamily w) = w := by
  funext i
  simp [conjugateFamily]

/-- A family followed by its coordinatewise conjugate. -/
def conjugationJoin {n : ℕ} (w : Fin n → ℂ) : Fin (n + n) → ℂ :=
  Fin.append w (conjugateFamily w)

/-- The input set of the conjugation join is the union of the two input sets. -/
theorem range_conjugationJoin {n : ℕ} (w : Fin n → ℂ) :
    Set.range (conjugationJoin w) =
      Set.range w ∪ Set.range (conjugateFamily w) := by
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    refine Fin.addCases (motive := fun i ↦
      conjugationJoin w i ∈ Set.range w ∪ Set.range (conjugateFamily w))
      (fun j ↦ Or.inl ⟨j, ?_⟩) (fun j ↦ Or.inr ⟨j, ?_⟩) i
    · exact (Fin.append_left w (conjugateFamily w) j).symm
    · exact (Fin.append_right w (conjugateFamily w) j).symm
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact ⟨Fin.castAdd n i, Fin.append_left w (conjugateFamily w) i⟩
    · exact ⟨Fin.natAdd n i, Fin.append_right w (conjugateFamily w) i⟩

/-- The coordinate-exponential generators of the conjugation join are the union of the two
generator sets. -/
theorem generators_conjugationJoin {n : ℕ} (w : Fin n → ℂ) :
    generators (conjugationJoin w) =
      generators w ∪ generators (conjugateFamily w) := by
  ext z
  constructor
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine Fin.addCases (motive := fun i ↦
        conjugationJoin w i ∈ generators w ∪ generators (conjugateFamily w))
        (fun j ↦ Or.inl (Or.inl ⟨j, ?_⟩))
        (fun j ↦ Or.inr (Or.inl ⟨j, ?_⟩)) i
      · exact (Fin.append_left w (conjugateFamily w) j).symm
      · exact (Fin.append_right w (conjugateFamily w) j).symm
    · refine Fin.addCases (motive := fun i ↦
        Complex.exp (conjugationJoin w i) ∈
          generators w ∪ generators (conjugateFamily w))
        (fun j ↦ Or.inl (Or.inr ⟨j, ?_⟩))
        (fun j ↦ Or.inr (Or.inr ⟨j, ?_⟩)) i
      · exact congrArg Complex.exp (Fin.append_left w (conjugateFamily w) j).symm
      · exact congrArg Complex.exp (Fin.append_right w (conjugateFamily w) j).symm
  · rintro ((⟨i, rfl⟩ | ⟨i, rfl⟩) | (⟨i, rfl⟩ | ⟨i, rfl⟩))
    · exact Or.inl ⟨Fin.castAdd n i, Fin.append_left w (conjugateFamily w) i⟩
    · exact Or.inr ⟨Fin.castAdd n i,
        congrArg Complex.exp (Fin.append_left w (conjugateFamily w) i)⟩
    · exact Or.inl ⟨Fin.natAdd n i, Fin.append_right w (conjugateFamily w) i⟩
    · exact Or.inr ⟨Fin.natAdd n i,
        congrArg Complex.exp (Fin.append_right w (conjugateFamily w) i)⟩

/-- Conjugation carries the coordinate-exponential generator set to the conjugated one. -/
theorem image_generators_conjugation {n : ℕ} (w : Fin n → ℂ) :
    conjugationAlgEquiv '' generators w = generators (conjugateFamily w) := by
  ext z
  constructor
  · rintro ⟨x, (⟨i, rfl⟩ | ⟨i, rfl⟩), rfl⟩
    · exact Or.inl ⟨i, rfl⟩
    · apply Or.inr
      refine ⟨i, ?_⟩
      simp [conjugationAlgEquiv, conjugateFamily, Complex.exp_conj]
  · rintro (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine ⟨w i, Or.inl ⟨i, rfl⟩, ?_⟩
      rfl
    · refine ⟨Complex.exp (w i), Or.inr ⟨i, rfl⟩, ?_⟩
      simp [conjugationAlgEquiv, conjugateFamily, Complex.exp_conj]

/-- The generated field of the conjugated family is the conjugate image field. -/
theorem generatedField_conjugateFamily {n : ℕ} (w : Fin n → ℂ) :
    generatedField (conjugateFamily w) =
      (generatedField w).map conjugationAlgEquiv.toAlgHom := by
  rw [generatedField, generatedField, IntermediateField.adjoin_map]
  congr 1
  simpa using (image_generators_conjugation w).symm

/-- Coordinatewise conjugation preserves generated-field transcendence degree. -/
theorem trdeg_conjugateFamily {n : ℕ} (w : Fin n → ℂ) :
    Algebra.trdeg ℚ (generatedField (conjugateFamily w)) =
      Algebra.trdeg ℚ (generatedField w) := by
  rw [generatedField_conjugateFamily]
  let e : generatedField w ≃ₐ[ℚ]
      (generatedField w).map conjugationAlgEquiv.toAlgHom :=
    IntermediateField.equivMap (generatedField w) conjugationAlgEquiv.toAlgHom
  exact le_antisymm
    (trdeg_le_of_injective e.symm.toAlgHom e.symm.injective)
    (trdeg_le_of_injective e.toAlgHom e.injective)

/-- Joining a family to its conjugate generates the compositum of the two generated fields. -/
theorem generatedField_conjugationJoin {n : ℕ} (w : Fin n → ℂ) :
    generatedField (conjugationJoin w) =
      generatedField w ⊔ generatedField (conjugateFamily w) := by
  rw [generatedField, generatedField, generatedField, generators_conjugationJoin,
    IntermediateField.adjoin_union]

/-- A family is conjugation-stable when its rational input span is invariant under conjugation. -/
def ConjugationStable {n : ℕ} (w : Fin n → ℂ) : Prop :=
  Submodule.span ℚ (Set.range (conjugateFamily w)) =
    Submodule.span ℚ (Set.range w)

/-- The conjugation-stable closure of a rational input span. -/
def stableClosure {n : ℕ} (w : Fin n → ℂ) : Submodule ℚ ℂ :=
  Submodule.span ℚ (Set.range w) ⊔
    (Submodule.span ℚ (Set.range w)).map conjugationLinearEquiv.toLinearMap

/-- The requested basis-level stable canonical normal-form predicate. -/
def ConjugationStableCanonicalDefectOne {n : ℕ} (w : Fin (n + 2) → ℂ) : Prop :=
  CanonicallyAnchoredFullyTranscendentalDefectOne w ∧ ConjugationStable w

/-- Conjugating a rational span is the span of the conjugated family. -/
theorem map_span_conjugation_eq {n : ℕ} (w : Fin n → ℂ) :
    (Submodule.span ℚ (Set.range w)).map conjugationLinearEquiv.toLinearMap =
      Submodule.span ℚ (Set.range (conjugateFamily w)) := by
  rw [Submodule.map_span]
  congr 1
  ext z
  constructor
  · rintro ⟨x, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨w i, ⟨i, rfl⟩, rfl⟩

/-- The stable closure is exactly the rational span of the conjugation join. -/
theorem span_conjugationJoin {n : ℕ} (w : Fin n → ℂ) :
    Submodule.span ℚ (Set.range (conjugationJoin w)) = stableClosure w := by
  rw [range_conjugationJoin, Submodule.span_union, stableClosure,
    map_span_conjugation_eq]

/-- Stability is unchanged by replacing a family by another basis of the same rational span. -/
theorem conjugationStable_iff_of_span_eq {m n : ℕ}
    {w : Fin m → ℂ} {v : Fin n → ℂ}
    (hspan : Submodule.span ℚ (Set.range w) =
      Submodule.span ℚ (Set.range v)) :
    ConjugationStable w ↔ ConjugationStable v := by
  unfold ConjugationStable
  rw [← map_span_conjugation_eq, ← map_span_conjugation_eq, hspan]

/-- The stable closure contains the original input span. -/
theorem span_le_stableClosure {n : ℕ} (w : Fin n → ℂ) :
    Submodule.span ℚ (Set.range w) ≤ stableClosure w :=
  le_sup_left

/-- The stable closure is invariant under complex conjugation. -/
theorem map_stableClosure_conjugation {n : ℕ} (w : Fin n → ℂ) :
    (stableClosure w).map conjugationLinearEquiv.toLinearMap = stableClosure w := by
  rw [stableClosure, Submodule.map_sup]
  have hdouble : ((Submodule.span ℚ (Set.range w)).map
      conjugationLinearEquiv.toLinearMap).map
        conjugationLinearEquiv.toLinearMap =
      Submodule.span ℚ (Set.range w) := by
    ext z
    constructor
    · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
      simpa [conjugationLinearEquiv] using hx
    · intro hz
      refine ⟨conjugationLinearEquiv z, ⟨z, hz, rfl⟩, ?_⟩
      simp [conjugationLinearEquiv]
  rw [hdouble, sup_comm]

/-- Any basis of the stable closure has conjugation-stable span. -/
theorem conjugationStable_of_span_eq_stableClosure {m n : ℕ}
    {w : Fin m → ℂ} {v : Fin n → ℂ}
    (hspan : Submodule.span ℚ (Set.range v) = stableClosure w) :
    ConjugationStable v := by
  unfold ConjugationStable
  rw [← map_span_conjugation_eq, hspan, map_stableClosure_conjugation]

/-- If a finite input span contains the canonical anchor, its stable closure has a finite
canonical-anchor basis, and every such basis is conjugation-stable. -/
theorem exists_fin_basis_stableClosure_with_canonicalAnchor {n : ℕ}
    {w : Fin n → ℂ}
    (hanchor : Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range w)) :
    ∃ (m : ℕ) (v : Fin (m + 2) → ℂ),
      LinearIndependent ℚ v ∧ CanonicallyAnchored v ∧
      Submodule.span ℚ (Set.range v) = stableClosure w ∧
      ConjugationStable v := by
  have hanchorJoin : Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range (conjugationJoin w)) := by
    exact hanchor.trans (by
      rw [range_conjugationJoin, Submodule.span_union]
      exact le_sup_left)
  obtain ⟨m, v, hvlin, hvspan, hvzero, hvone⟩ :=
    exists_fin_basis_with_canonicalAnchor hanchorJoin
  have hvstableSpan : Submodule.span ℚ (Set.range v) = stableClosure w :=
    hvspan.trans (span_conjugationJoin w)
  exact ⟨m, v, hvlin, ⟨hvzero, hvone⟩, hvstableSpan,
    conjugationStable_of_span_eq_stableClosure hvstableSpan⟩

/-- Exact submodular amplification criterion for the stable closure.  It isolates the only
arithmetic input not supplied by linear conjugation: a sufficiently large transcendence-degree
intersection of the two conjugate generated fields. -/
theorem not_bound_of_stableClosure_basis_of_submodular_gap {m n : ℕ}
    {w : Fin n → ℂ} {v : Fin m → ℂ}
    (hspan : Submodule.span ℚ (Set.range v) = stableClosure w)
    (hfinite : Algebra.trdeg ℚ
      (↥(generatedField w ⊓ generatedField (conjugateFamily w))) < Cardinal.aleph0)
    (hgap : Algebra.trdeg ℚ (generatedField w) +
        Algebra.trdeg ℚ (generatedField (conjugateFamily w)) <
      Cardinal.mk (Fin m) + Algebra.trdeg ℚ
        (↥(generatedField w ⊓ generatedField (conjugateFamily w)))) :
    ¬ Bound v := by
  let K : IntermediateField ℚ ℂ := generatedField w
  let L : IntermediateField ℚ ℂ := generatedField (conjugateFamily w)
  have hsubmod : Algebra.trdeg ℚ (↥(K ⊓ L)) +
      Algebra.trdeg ℚ (↥(K ⊔ L)) ≤
      Algebra.trdeg ℚ K + Algebra.trdeg ℚ L :=
    trdeg_inf_add_trdeg_sup_le K L
  have hsup : Algebra.trdeg ℚ (↥(K ⊔ L)) < Cardinal.mk (Fin m) := by
    apply (Cardinal.add_lt_add_iff_of_left_lt_aleph0
      (c := Algebra.trdeg ℚ (↥(K ⊓ L))) hfinite).mp
    calc
      Algebra.trdeg ℚ (↥(K ⊓ L)) + Algebra.trdeg ℚ (↥(K ⊔ L)) ≤
          Algebra.trdeg ℚ K + Algebra.trdeg ℚ L := hsubmod
      _ < Cardinal.mk (Fin m) + Algebra.trdeg ℚ (↥(K ⊓ L)) := hgap
      _ = Algebra.trdeg ℚ (↥(K ⊓ L)) + Cardinal.mk (Fin m) := add_comm _ _
  have htd : Algebra.trdeg ℚ (generatedField v) =
      Algebra.trdeg ℚ (↥(K ⊔ L)) := by
    calc
      Algebra.trdeg ℚ (generatedField v) =
          Algebra.trdeg ℚ (generatedField (conjugationJoin w)) :=
        trdeg_generatedField_eq_of_span_eq v (conjugationJoin w)
          (hspan.trans (span_conjugationJoin w).symm)
      _ = Algebra.trdeg ℚ (↥(K ⊔ L)) := by
        rw [generatedField_conjugationJoin]
  intro hvBound
  have hm : Cardinal.mk (Fin m) ≤ Algebra.trdeg ℚ (↥(K ⊔ L)) := by
    simpa [Bound, htd] using hvBound
  exact (not_le_of_gt hsup) hm

/-- Defect one makes the stable-closure criterion completely numerical: the two conjugate
fields each have degree `n`, so the only remaining datum is the degree of their intersection. -/
theorem not_bound_of_defectOne_stableClosure_basis_of_intersection_gap {m n : ℕ}
    {w : Fin (n + 1) → ℂ} {v : Fin m → ℂ}
    (hdefect : DefectOne w)
    (hspan : Submodule.span ℚ (Set.range v) = stableClosure w)
    (hgap : (n : Cardinal) + (n : Cardinal) <
      Cardinal.mk (Fin m) + Algebra.trdeg ℚ
        (↥(generatedField w ⊓ generatedField (conjugateFamily w)))) :
    ¬ Bound v := by
  apply not_bound_of_stableClosure_basis_of_submodular_gap hspan
  · apply trdeg_inf_lt_aleph0_of_left
    rw [hdefect]
    exact Cardinal.natCast_lt_aleph0
  · rw [trdeg_conjugateFamily, hdefect]
    simpa using hgap

/-- A stable canonical defect-one family is immediately a counterexample. -/
theorem not_conjecture_of_conjugationStableCanonicalDefectOne
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hw : ConjugationStableCanonicalDefectOne w) : ¬ Conjecture := by
  exact not_conjecture_iff_exists_canonicallyAnchoredFullyTranscendentalDefectOne.mpr
    ⟨n, w, hw.1⟩

/-- If the checked canonical normal-form witness already has stable span, it realizes the
conjugation-stable normal form without changing its basis. -/
theorem exists_conjugationStableCanonicalDefectOne_of_not_conjecture_of_stable_witness
    (h : ¬ Conjecture)
    (hstable : ∀ (n : ℕ) (w : Fin (n + 2) → ℂ),
      CanonicallyAnchoredFullyTranscendentalDefectOne w → ConjugationStable w) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ), ConjugationStableCanonicalDefectOne w := by
  obtain ⟨n, w, hw⟩ :=
    not_conjecture_iff_exists_canonicallyAnchoredFullyTranscendentalDefectOne.mp h
  exact ⟨n, w, hw, hstable n w hw⟩

end ConjugationStableNormalForm

end

end Schanuel
