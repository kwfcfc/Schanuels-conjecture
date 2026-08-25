import Schanuel.ConjugationStableNormalForm

/-!
# Conjugation-stable minimal failures

This module develops the remaining arithmetic input for conjugation-stable amplification.
The key point is literal field intersection, not merely two separate transcendence-degree
inequalities: one common positive integral scale clears the rational coordinates of a finite
family in two ambient rational spans at once.
-/

namespace Schanuel

open Function Set

noncomputable section

namespace ConjugationStableMinimalFailure

open ConjugationStableNormalForm

/-- A positive integral rational scaling introduces no new coordinate-exponential generators. -/
theorem generatedField_ratScale_int_le {n : ℕ} (d : ℤ) (u : Fin n → ℂ) :
    generatedField (ratScaleFamily (d : ℚ) u) ≤ generatedField u := by
  rw [generatedField, IntermediateField.adjoin_le_iff]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · exact (generatedField u).mul_mem
      (IntermediateField.algebraMap_mem _ (d : ℚ))
      (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩))
  · change Complex.exp ((d : ℚ) • u i) ∈ generatedField u
    rw [Rat.smul_def, Rat.cast_intCast, Complex.exp_int_mul]
    exact (generatedField u).pow_mem
      (IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)) d

/-- Clearing the denominators of a rational-span inclusion gives a literal generated-field
inclusion after one positive integral scaling. -/
theorem exists_pos_integer_scale_generatedField_le_of_span_le {m n : ℕ}
    (u : Fin m → ℂ) (w : Fin n → ℂ)
    (hspan : Submodule.span ℚ (Set.range u) ≤ Submodule.span ℚ (Set.range w)) :
    ∃ d : ℤ, 0 < d ∧
      generatedField (ratScaleFamily (d : ℚ) u) ≤ generatedField w := by
  have humem : ∀ i, u i ∈ Submodule.span ℚ (Set.range w) := fun i ↦
    hspan (Submodule.subset_span (Set.mem_range_self i))
  choose c hc using fun i ↦ (Submodule.mem_span_range_iff_exists_fun ℚ).mp (humem i)
  let B : Fin m → Fin n → ℚ := fun i ↦ c i
  have heq : rectangularRationalFamily B w = u := by
    funext i
    exact hc i
  obtain ⟨d, hd, A, hA⟩ := exists_pos_integer_rectangular_scale B
  refine ⟨d, hd, ?_⟩
  have hscaled : rectangularIntegerFamily A w = ratScaleFamily (d : ℚ) u := by
    rw [← heq]
    exact rectangularIntegerFamily_eq_ratScaleFamily B d A hA w
  rw [← hscaled]
  exact generatedField_rectangularIntegerFamily_le A w

set_option maxHeartbeats 400000 in
-- Two independent denominator clearings and their common scaled-field inclusion elaborate deeply.
/-- One common positive integral scale puts a finite rational family literally inside the
intersection of the generated fields of any two ambient spanning families. -/
theorem exists_pos_integer_scale_generatedField_le_inf_of_span_le {r m n : ℕ}
    (u : Fin r → ℂ) (w : Fin m → ℂ) (v : Fin n → ℂ)
    (huw : Submodule.span ℚ (Set.range u) ≤ Submodule.span ℚ (Set.range w))
    (huv : Submodule.span ℚ (Set.range u) ≤ Submodule.span ℚ (Set.range v)) :
    ∃ d : ℤ, 0 < d ∧
      generatedField (ratScaleFamily (d : ℚ) u) ≤
        generatedField w ⊓ generatedField v := by
  obtain ⟨a, ha, hfieldA⟩ :=
    exists_pos_integer_scale_generatedField_le_of_span_le u w huw
  obtain ⟨b, hb, hfieldB⟩ :=
    exists_pos_integer_scale_generatedField_le_of_span_le u v huv
  refine ⟨a * b, mul_pos ha hb, ?_⟩
  apply le_inf
  · have hscale := generatedField_ratScale_int_le b (ratScaleFamily (a : ℚ) u)
    have heq : ratScaleFamily (b : ℚ) (ratScaleFamily (a : ℚ) u) =
        ratScaleFamily ((a * b : ℤ) : ℚ) u := by
      funext i
      simp only [ratScaleFamily]
      push_cast
      ring_nf
    rw [heq] at hscale
    exact hscale.trans hfieldA
  · have hscale := generatedField_ratScale_int_le a (ratScaleFamily (b : ℚ) u)
    have heq : ratScaleFamily (a : ℚ) (ratScaleFamily (b : ℚ) u) =
        ratScaleFamily ((a * b : ℤ) : ℚ) u := by
      funext i
      simp only [ratScaleFamily]
      push_cast
      ring_nf
    rw [heq] at hscale
    exact hscale.trans hfieldB

/-- A finite family contained in two rational input spans contributes its full generated-field
transcendence degree to the literal intersection of the two ambient generated fields. -/
theorem trdeg_generatedField_le_inf_of_two_span_le {r m n : ℕ}
    (u : Fin r → ℂ) (w : Fin m → ℂ) (v : Fin n → ℂ)
    (huw : Submodule.span ℚ (Set.range u) ≤ Submodule.span ℚ (Set.range w))
    (huv : Submodule.span ℚ (Set.range u) ≤ Submodule.span ℚ (Set.range v)) :
    Algebra.trdeg ℚ (generatedField u) ≤
      Algebra.trdeg ℚ (↥(generatedField w ⊓ generatedField v)) := by
  obtain ⟨d, hd, hfield⟩ :=
    exists_pos_integer_scale_generatedField_le_inf_of_span_le u w v huw huv
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  let f : generatedField (ratScaleFamily (d : ℚ) u) →ₐ[ℚ]
      ↥(generatedField w ⊓ generatedField v) :=
    (IntermediateField.inclusion hfield).toRingHom.toRatAlgHom
  have hle : Algebra.trdeg ℚ (generatedField (ratScaleFamily (d : ℚ) u)) ≤
      Algebra.trdeg ℚ (↥(generatedField w ⊓ generatedField v)) :=
    trdeg_le_of_injective f (IntermediateField.inclusion_injective hfield)
  calc
    Algebra.trdeg ℚ (generatedField u) =
        Algebra.trdeg ℚ (generatedField (ratScaleFamily (d : ℚ) u)) :=
      (trdeg_ratScaleFamily_eq (d : ℚ) hdQ u).symm
    _ ≤ Algebra.trdeg ℚ (↥(generatedField w ⊓ generatedField v)) :=
      hle

/-! ## Finite bases of the conjugation intersection -/

/-- Every subspace of the span of a finite family has a finite basis, viewed as a family in
the ambient complex vector space. -/
theorem exists_fin_basis_of_le_span {m : ℕ} (P : Submodule ℚ ℂ)
    (w : Fin m → ℂ) (hP : P ≤ Submodule.span ℚ (Set.range w)) :
    ∃ (r : ℕ) (u : Fin r → ℂ),
      LinearIndependent ℚ u ∧ Submodule.span ℚ (Set.range u) = P := by
  let Q : Submodule ℚ ℂ := Submodule.span ℚ (Set.range w)
  letI : FiniteDimensional ℚ Q :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  let f : P →ₗ[ℚ] Q := Submodule.inclusion hP
  letI : FiniteDimensional ℚ P :=
    FiniteDimensional.of_injective f (Submodule.inclusion_injective hP)
  let r := Module.finrank ℚ P
  let b : Module.Basis (Fin r) ℚ P := Module.finBasis ℚ P
  let u : Fin r → ℂ := P.subtype ∘ b
  refine ⟨r, u, ?_, ?_⟩
  · exact b.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  · change Submodule.span ℚ (Set.range (P.subtype ∘ b)) = P
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_subtype_top]

/-- The literal canonical anchor spans a conjugation-stable rational subspace. -/
theorem conjugationStable_canonicalAnchor : ConjugationStable canonicalAnchor := by
  unfold ConjugationStable
  have hperiod : star FullyTranscendentalPeriodBoundary.period =
      -FullyTranscendentalPeriodBoundary.period := by
    change star (2 * Real.pi * Complex.I) = -(2 * Real.pi * Complex.I)
    simp
  have hle : Submodule.span ℚ (Set.range (conjugateFamily canonicalAnchor)) ≤
      Submodule.span ℚ (Set.range canonicalAnchor) := by
    apply Submodule.span_le.mpr
    rintro z ⟨i, rfl⟩
    fin_cases i
    · have ha : canonicalAnchor 0 ∈ Submodule.span ℚ (Set.range canonicalAnchor) :=
        Submodule.subset_span (Set.mem_range_self 0)
      have hb : canonicalAnchor 1 ∈ Submodule.span ℚ (Set.range canonicalAnchor) :=
        Submodule.subset_span (Set.mem_range_self 1)
      have h := (Submodule.span ℚ (Set.range canonicalAnchor)).sub_mem
        ((Submodule.span ℚ (Set.range canonicalAnchor)).smul_mem (3 : ℚ) ha)
        ((Submodule.span ℚ (Set.range canonicalAnchor)).smul_mem (2 : ℚ) hb)
      convert h using 1
      simp [conjugateFamily, hperiod, Rat.smul_def]
      ring
    · have ha : canonicalAnchor 0 ∈ Submodule.span ℚ (Set.range canonicalAnchor) :=
        Submodule.subset_span (Set.mem_range_self 0)
      have hb : canonicalAnchor 1 ∈ Submodule.span ℚ (Set.range canonicalAnchor) :=
        Submodule.subset_span (Set.mem_range_self 1)
      have h := (Submodule.span ℚ (Set.range canonicalAnchor)).sub_mem
        ((Submodule.span ℚ (Set.range canonicalAnchor)).smul_mem (4 : ℚ) ha)
        ((Submodule.span ℚ (Set.range canonicalAnchor)).smul_mem (3 : ℚ) hb)
      convert h using 1
      simp [conjugateFamily, hperiod, Rat.smul_def]
      ring
  apply le_antisymm hle
  have hmap := Submodule.map_mono (f := conjugationLinearEquiv.toLinearMap) hle
  rw [map_span_conjugation_eq, conjugateFamily_conjugateFamily,
    map_span_conjugation_eq] at hmap
  exact hmap

/-- A literally canonically anchored family contains the anchor's rational span. -/
theorem span_canonicalAnchor_le_of_canonicallyAnchored {n : ℕ}
    {w : Fin (n + 2) → ℂ} (hanchor : CanonicallyAnchored w) :
    Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range w) := by
  apply Submodule.span_le.mpr
  rintro z ⟨i, rfl⟩
  fin_cases i
  · exact Submodule.subset_span ⟨0, hanchor.1⟩
  · exact Submodule.subset_span ⟨1, hanchor.2⟩

/-- The intersection of an anchored input span with its conjugate span still contains the
canonical anchor and therefore admits a finite basis beginning literally with that anchor. -/
theorem exists_fin_basis_conjugationIntersection_with_canonicalAnchor {n : ℕ}
    {w : Fin (n + 2) → ℂ} (hanchor : CanonicallyAnchored w) :
    ∃ (k : ℕ) (u : Fin (k + 2) → ℂ),
      LinearIndependent ℚ u ∧ CanonicallyAnchored u ∧
      Submodule.span ℚ (Set.range u) =
        Submodule.span ℚ (Set.range w) ⊓
          Submodule.span ℚ (Set.range (conjugateFamily w)) := by
  let S : Submodule ℚ ℂ := Submodule.span ℚ (Set.range w)
  let C : Submodule ℚ ℂ := Submodule.span ℚ (Set.range (conjugateFamily w))
  let H : Submodule ℚ ℂ := S ⊓ C
  have haS : Submodule.span ℚ (Set.range canonicalAnchor) ≤ S :=
    span_canonicalAnchor_le_of_canonicallyAnchored hanchor
  have haC : Submodule.span ℚ (Set.range canonicalAnchor) ≤ C := by
    calc
      Submodule.span ℚ (Set.range canonicalAnchor) =
          Submodule.span ℚ (Set.range (conjugateFamily canonicalAnchor)) :=
        conjugationStable_canonicalAnchor.symm
      _ ≤ Submodule.span ℚ (Set.range (conjugateFamily w)) := by
        rw [← map_span_conjugation_eq, ← map_span_conjugation_eq]
        exact Submodule.map_mono (f := conjugationLinearEquiv.toLinearMap) haS
  have haH : Submodule.span ℚ (Set.range canonicalAnchor) ≤ H :=
    le_inf haS haC
  obtain ⟨r, t, htlin, htspan⟩ :=
    exists_fin_basis_of_le_span H w (show H ≤ S from inf_le_left)
  have haT : Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range t) := by
    rwa [htspan]
  obtain ⟨k, u, hulin, huspan, huzero, huone⟩ :=
    exists_fin_basis_with_canonicalAnchor haT
  refine ⟨k, u, hulin, ⟨huzero, huone⟩, ?_⟩
  exact huspan.trans htspan

/-- If an intersection basis is proper inside an independent ambient family, then its number
of complementary anchor coordinates is strictly smaller. -/
theorem intersection_complementIndex_lt_of_not_conjugationStable {k n : ℕ}
    {w : Fin (n + 2) → ℂ} {u : Fin (k + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hulin : LinearIndependent ℚ u)
    (huspan : Submodule.span ℚ (Set.range u) =
      Submodule.span ℚ (Set.range w) ⊓
        Submodule.span ℚ (Set.range (conjugateFamily w)))
    (hnotStable : ¬ ConjugationStable w) : k < n := by
  let S : Submodule ℚ ℂ := Submodule.span ℚ (Set.range w)
  let C : Submodule ℚ ℂ := Submodule.span ℚ (Set.range (conjugateFamily w))
  let H : Submodule ℚ ℂ := S ⊓ C
  have hHlt : H < S := by
    apply lt_of_le_of_ne inf_le_left
    intro hHS
    have hSC : S ≤ C := by
      rw [← hHS]
      exact inf_le_right
    have hCS : C ≤ S := by
      calc
        C = S.map conjugationLinearEquiv.toLinearMap := by
          exact (map_span_conjugation_eq w).symm
        _ ≤ C.map conjugationLinearEquiv.toLinearMap :=
          Submodule.map_mono (f := conjugationLinearEquiv.toLinearMap) hSC
        _ = S := by
          dsimp [C, S]
          rw [map_span_conjugation_eq, conjugateFamily_conjugateFamily]
    exact hnotStable (le_antisymm hCS hSC)
  letI : FiniteDimensional ℚ S :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  have hdim : Module.finrank ℚ H < Module.finrank ℚ S :=
    Submodule.finrank_lt_finrank_of_lt hHlt
  have huRank : Module.finrank ℚ H = k + 2 := by
    let e : H ≃ₗ[ℚ] Submodule.span ℚ (Set.range u) :=
      LinearEquiv.ofEq H (Submodule.span ℚ (Set.range u)) (by
        exact huspan.symm)
    calc
      Module.finrank ℚ H =
          Module.finrank ℚ (Submodule.span ℚ (Set.range u)) := e.finrank_eq
      _ = k + 2 := by simpa using finrank_span_eq_card hulin
  have hwRank : Module.finrank ℚ S = n + 2 := by
    dsimp [S]
    simpa using finrank_span_eq_card hwlin
  rw [huRank, hwRank] at hdim
  omega

/-- Minimality among anchored failures forces the proper conjugation intersection to satisfy
its Schanuel bound. -/
theorem bound_conjugationIntersection_basis_of_minimal_failure {k n : ℕ}
    {w : Fin (n + 2) → ℂ} {u : Fin (k + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hulin : LinearIndependent ℚ u)
    (huanchor : CanonicallyAnchored u)
    (huspan : Submodule.span ℚ (Set.range u) =
      Submodule.span ℚ (Set.range w) ⊓
        Submodule.span ℚ (Set.range (conjugateFamily w)))
    (hnotStable : ¬ ConjugationStable w)
    (hmin : ∀ j < n, ¬ CanonicalAnchoredFailureAt j) : Bound u := by
  have hkn := intersection_complementIndex_lt_of_not_conjugationStable
    hwlin hulin huspan hnotStable
  by_contra huFail
  exact hmin k hkn ⟨u, hulin, huanchor, huFail⟩

/-- Exact arithmetic bridge: for a proper conjugation intersection of a least anchored failure,
the literal intersection of the two conjugate generated fields has transcendence degree at
least the full rational dimension `k + 2` of that intersection. -/
theorem trdeg_fieldIntersection_ge_intersectionDimension_of_minimal_failure {k n : ℕ}
    {w : Fin (n + 2) → ℂ} {u : Fin (k + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hulin : LinearIndependent ℚ u)
    (huanchor : CanonicallyAnchored u)
    (huspan : Submodule.span ℚ (Set.range u) =
      Submodule.span ℚ (Set.range w) ⊓
        Submodule.span ℚ (Set.range (conjugateFamily w)))
    (hnotStable : ¬ ConjugationStable w)
    (hmin : ∀ j < n, ¬ CanonicalAnchoredFailureAt j) :
    ((k + 2 : ℕ) : Cardinal) ≤ Algebra.trdeg ℚ
      (↥(generatedField w ⊓ generatedField (conjugateFamily w))) := by
  have huBound := bound_conjugationIntersection_basis_of_minimal_failure
    hwlin hulin huanchor huspan hnotStable hmin
  have huField : Algebra.trdeg ℚ (generatedField u) ≤ Algebra.trdeg ℚ
      (↥(generatedField w ⊓ generatedField (conjugateFamily w))) := by
    apply trdeg_generatedField_le_inf_of_two_span_le u w (conjugateFamily w)
    · exact huspan.le.trans inf_le_left
    · exact huspan.le.trans inf_le_right
  have huLower : ((k + 2 : ℕ) : Cardinal) ≤
      Algebra.trdeg ℚ (generatedField u) := by
    simpa [Bound] using huBound
  exact huLower.trans huField

/-! ## Stable-closure amplification -/

/-- Grassmann's dimension identity for the span of a family and its conjugate, expressed using
the stable closure and conjugation intersection used in this module. -/
theorem finrank_stableClosure_add_finrank_conjugationIntersection {n : ℕ}
    (w : Fin n → ℂ) :
    Module.finrank ℚ (stableClosure w) +
        Module.finrank ℚ (↥(Submodule.span ℚ (Set.range w) ⊓
          Submodule.span ℚ (Set.range (conjugateFamily w)))) =
      Module.finrank ℚ (Submodule.span ℚ (Set.range w)) +
        Module.finrank ℚ (Submodule.span ℚ (Set.range w)) := by
  let S : Submodule ℚ ℂ := Submodule.span ℚ (Set.range w)
  let C : Submodule ℚ ℂ := Submodule.span ℚ (Set.range (conjugateFamily w))
  letI : FiniteDimensional ℚ S :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  letI : FiniteDimensional ℚ C :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range (conjugateFamily w))
  have hgrass := Submodule.finrank_sup_add_finrank_inf_eq S C
  have hC : Module.finrank ℚ C = Module.finrank ℚ S := by
    calc
      Module.finrank ℚ C =
          Module.finrank ℚ (S.map conjugationLinearEquiv.toLinearMap) := by
        rw [map_span_conjugation_eq]
      _ = Module.finrank ℚ S :=
        conjugationLinearEquiv.finrank_map_eq S
  rw [hC] at hgrass
  have hstable : stableClosure w = S ⊔ C := by
    rw [stableClosure, map_span_conjugation_eq]
  have hStableRank : Module.finrank ℚ (stableClosure w) =
      Module.finrank ℚ (↥(S ⊔ C)) :=
    (LinearEquiv.ofEq (stableClosure w) (S ⊔ C) hstable).finrank_eq
  calc
    Module.finrank ℚ (stableClosure w) +
          Module.finrank ℚ (↥(Submodule.span ℚ (Set.range w) ⊓
            Submodule.span ℚ (Set.range (conjugateFamily w)))) =
        Module.finrank ℚ (↥(S ⊔ C)) + Module.finrank ℚ (↥(S ⊓ C)) := by
      rw [hStableRank]
    _ = Module.finrank ℚ S + Module.finrank ℚ S := hgrass

/-- A finite independent spanning family computes the finrank of its target submodule. -/
theorem finrank_eq_card_of_linearIndependent_span_eq {r : ℕ}
    {u : Fin r → ℂ} {P : Submodule ℚ ℂ}
    (hulin : LinearIndependent ℚ u)
    (huspan : Submodule.span ℚ (Set.range u) = P) :
    Module.finrank ℚ P = r := by
  let e : P ≃ₗ[ℚ] Submodule.span ℚ (Set.range u) :=
    LinearEquiv.ofEq P (Submodule.span ℚ (Set.range u)) huspan.symm
  calc
    Module.finrank ℚ P =
        Module.finrank ℚ (Submodule.span ℚ (Set.range u)) := e.finrank_eq
    _ = r := by simpa using finrank_span_eq_card hulin

/-- A proper, non-stable least anchored defect-one failure amplifies to a failing basis of its
conjugation-stable closure.  This is the complete arithmetic amplification step; no stable
minimal-subspace deletion is used here. -/
theorem not_bound_stableClosure_basis_of_minimal_nonstable_failure {k m n : ℕ}
    {w : Fin (n + 2) → ℂ} {u : Fin (k + 2) → ℂ} {v : Fin (m + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hwdefect : DefectOne w)
    (hulin : LinearIndependent ℚ u) (huanchor : CanonicallyAnchored u)
    (huspan : Submodule.span ℚ (Set.range u) =
      Submodule.span ℚ (Set.range w) ⊓
        Submodule.span ℚ (Set.range (conjugateFamily w)))
    (hvlin : LinearIndependent ℚ v)
    (hvspan : Submodule.span ℚ (Set.range v) = stableClosure w)
    (hnotStable : ¬ ConjugationStable w)
    (hmin : ∀ j < n, ¬ CanonicalAnchoredFailureAt j) : ¬ Bound v := by
  have hInter := trdeg_fieldIntersection_ge_intersectionDimension_of_minimal_failure
    hwlin hulin huanchor huspan hnotStable hmin
  have hvRank : Module.finrank ℚ (stableClosure w) = m + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq hvlin hvspan
  have huRank : Module.finrank ℚ
      (↥(Submodule.span ℚ (Set.range w) ⊓
        Submodule.span ℚ (Set.range (conjugateFamily w)))) = k + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq hulin huspan
  have hwRank : Module.finrank ℚ (Submodule.span ℚ (Set.range w)) = n + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq hwlin rfl
  have hdim := finrank_stableClosure_add_finrank_conjugationIntersection w
  rw [hvRank, huRank, hwRank] at hdim
  have hnat : (n + 1) + (n + 1) < (m + 2) + (k + 2) := by omega
  have hcard : ((n + 1 : ℕ) : Cardinal) + ((n + 1 : ℕ) : Cardinal) <
      ((m + 2 : ℕ) : Cardinal) + ((k + 2 : ℕ) : Cardinal) := by
    exact_mod_cast hnat
  have hgap : ((n + 1 : ℕ) : Cardinal) + ((n + 1 : ℕ) : Cardinal) <
      Cardinal.mk (Fin (m + 2)) + Algebra.trdeg ℚ
        (↥(generatedField w ⊓ generatedField (conjugateFamily w))) := by
    apply hcard.trans_le
    simpa using add_le_add_right hInter ((m + 2 : ℕ) : Cardinal)
  exact not_bound_of_defectOne_stableClosure_basis_of_intersection_gap
    hwdefect hvspan hgap

/-- A least anchored defect-one failure which is not already stable produces a finite
independent, canonically anchored, conjugation-stable failing basis of its stable closure. -/
theorem exists_conjugationStable_anchored_failure_of_minimal_nonstable {n : ℕ}
    {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hwanchor : CanonicallyAnchored w)
    (hwdefect : DefectOne w) (hnotStable : ¬ ConjugationStable w)
    (hmin : ∀ j < n, ¬ CanonicalAnchoredFailureAt j) :
    ∃ (m : ℕ) (v : Fin (m + 2) → ℂ),
      LinearIndependent ℚ v ∧ CanonicallyAnchored v ∧
      ConjugationStable v ∧ ¬ Bound v := by
  obtain ⟨k, u, hulin, huanchor, huspan⟩ :=
    exists_fin_basis_conjugationIntersection_with_canonicalAnchor hwanchor
  have haS := span_canonicalAnchor_le_of_canonicallyAnchored hwanchor
  obtain ⟨m, v, hvlin, hvanchor, hvspan, hvstable⟩ :=
    exists_fin_basis_stableClosure_with_canonicalAnchor haS
  have hvfail := not_bound_stableClosure_basis_of_minimal_nonstable_failure
    hwlin hwdefect hulin huanchor huspan hvlin hvspan hnotStable hmin
  exact ⟨m, v, hvlin, hvanchor, hvstable, hvfail⟩

/-- Failure of Schanuel's conjecture always has a finite independent, canonically anchored,
conjugation-stable failing input space.  The result is a stable *failure*; it does not yet claim
that the chosen stable basis has defect exactly one. -/
theorem exists_conjugationStable_canonicalAnchored_failure_of_not_conjecture
    (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
      LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧
      ConjugationStable w ∧ ¬ Bound w := by
  obtain ⟨n, w, hwlin, hwanchor, hwfail, hwdefect, hmin⟩ :=
    exists_canonicalAnchored_defectOne_minimal_failure h
  by_cases hwstable : ConjugationStable w
  · exact ⟨n, w, hwlin, hwanchor, hwstable, hwfail⟩
  · exact exists_conjugationStable_anchored_failure_of_minimal_nonstable
      hwlin hwanchor hwdefect hwstable hmin

/-- The exact stable-failure frontier: global failure is equivalent to existence of an
independent canonically anchored failure whose rational input span is conjugation-stable. -/
theorem not_conjecture_iff_exists_conjugationStable_canonicalAnchored_failure :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
        LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧
        ConjugationStable w ∧ ¬ Bound w := by
  constructor
  · exact exists_conjugationStable_canonicalAnchored_failure_of_not_conjecture
  · rintro ⟨n, w, hwlin, -, -, hwfail⟩ hC
    exact hwfail (hC (n + 2) w hwlin)

/-! ## Invariant-hyperplane linear algebra -/

/-- A proper invariant subspace of a rational vector space with a linear involution is contained
in the kernel of a nonzero invariant or anti-invariant functional.  Its kernel is therefore an
invariant hyperplane.  This is the linear-algebra core of the remaining stable-minimality step. -/
theorem exists_invariant_hyperplane_functional
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (c : V →ₗ[ℚ] V) (hc : c.comp c = LinearMap.id)
    (A : Submodule ℚ V) (hA : ∀ x ∈ A, c x ∈ A) (hAtop : A < ⊤) :
    ∃ g : V →ₗ[ℚ] ℚ,
      g ≠ 0 ∧ A ≤ LinearMap.ker g ∧
      (∀ x, g (c x) = g x ∨ g (c x) = -g x) ∧
      Module.finrank ℚ (LinearMap.ker g) + 1 = Module.finrank ℚ V := by
  obtain ⟨f, hf, hfA⟩ := A.exists_le_ker_of_lt_top hAtop
  let fc : V →ₗ[ℚ] ℚ := f.comp c
  let fp : V →ₗ[ℚ] ℚ := f + fc
  let fm : V →ₗ[ℚ] ℚ := f - fc
  have hc_apply : ∀ x, c (c x) = x := by
    intro x
    have hx := LinearMap.congr_fun hc x
    simpa [LinearMap.comp_apply] using hx
  have hfpA : A ≤ LinearMap.ker fp := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hfx : f x = 0 := LinearMap.mem_ker.mp (hfA hx)
    have hfcx : f (c x) = 0 := LinearMap.mem_ker.mp (hfA (hA x hx))
    simp [fp, fc, hfx, hfcx]
  have hfmA : A ≤ LinearMap.ker fm := by
    intro x hx
    rw [LinearMap.mem_ker]
    have hfx : f x = 0 := LinearMap.mem_ker.mp (hfA hx)
    have hfcx : f (c x) = 0 := LinearMap.mem_ker.mp (hfA (hA x hx))
    simp [fm, fc, hfx, hfcx]
  have hfpInv : ∀ x, fp (c x) = fp x := by
    intro x
    simp [fp, fc, hc_apply, add_comm]
  have hfmAnti : ∀ x, fm (c x) = -fm x := by
    intro x
    simp [fm, fc, hc_apply]
  have hcodim (g : V →ₗ[ℚ] ℚ) (hg : g ≠ 0) :
      Module.finrank ℚ (LinearMap.ker g) + 1 = Module.finrank ℚ V := by
    obtain ⟨x, hx⟩ := DFunLike.ne_iff.mp hg
    have hsurj : Function.Surjective g := by
      intro y
      refine ⟨(y / g x) • x, ?_⟩
      simp [div_mul_cancel₀ y hx]
    have hrange : Module.finrank ℚ (LinearMap.range g) = 1 := by
      rw [LinearMap.range_eq_top.mpr hsurj]
      simp
    have hrank := g.finrank_range_add_finrank_ker
    rw [hrange] at hrank
    omega
  by_cases hfp : fp ≠ 0
  · refine ⟨fp, hfp, hfpA, fun x ↦ Or.inl (hfpInv x), hcodim fp hfp⟩
  · have hfm : fm ≠ 0 := by
      intro hfm0
      apply hf
      apply LinearMap.ext
      intro x
      have hpX := LinearMap.congr_fun (not_ne_iff.mp hfp) x
      have hmX := LinearMap.congr_fun hfm0 x
      simp [fp, fm, fc] at hpX hmX
      have hzero : f x = 0 := by linarith
      simpa using hzero
    refine ⟨fm, hfm, hfmA, fun x ↦ Or.inr (hfmAnti x), hcodim fm hfm⟩

/-- Complex conjugation restricted to an invariant rational subspace. -/
def restrictedConjugation (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) : R →ₗ[ℚ] R :=
  LinearMap.codRestrict R
    (conjugationLinearEquiv.toLinearMap.domRestrict R) (fun x ↦ by
      have hx : star (x : ℂ) ∈ R.map conjugationLinearEquiv.toLinearMap :=
        ⟨x, x.2, rfl⟩
      rw [hR] at hx
      exact hx)

@[simp]
theorem restrictedConjugation_apply (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) (x : R) :
    (restrictedConjugation R hR x : ℂ) = star (x : ℂ) := rfl

/-- Restricted conjugation remains an involution. -/
theorem restrictedConjugation_involutive (R : Submodule ℚ ℂ)
    (hR : R.map conjugationLinearEquiv.toLinearMap = R) :
    (restrictedConjugation R hR).comp (restrictedConjugation R hR) = LinearMap.id := by
  ext x
  simp [LinearMap.comp_apply]

/-- Every positive-dimensional complement of the stable canonical anchor admits a
codimension-one, canonically anchored, conjugation-stable subspace basis. -/
theorem exists_canonicalAnchored_conjugationStable_codimOne_basis {n : ℕ}
    {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hwanchor : CanonicallyAnchored w)
    (hwstable : ConjugationStable w) (hn : 0 < n) :
    ∃ (k : ℕ) (u : Fin (k + 2) → ℂ),
      LinearIndependent ℚ u ∧ CanonicallyAnchored u ∧ ConjugationStable u ∧
      Submodule.span ℚ (Set.range u) < Submodule.span ℚ (Set.range w) ∧
      k < n ∧ k + 1 = n := by
  let R : Submodule ℚ ℂ := Submodule.span ℚ (Set.range w)
  let anchorSpan : Submodule ℚ ℂ := Submodule.span ℚ (Set.range canonicalAnchor)
  have haR : anchorSpan ≤ R := span_canonicalAnchor_le_of_canonicallyAnchored hwanchor
  have hRstable : R.map conjugationLinearEquiv.toLinearMap = R := by
    rw [map_span_conjugation_eq]
    exact hwstable
  letI : FiniteDimensional ℚ R :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range w)
  let A : Submodule ℚ R := anchorSpan.comap R.subtype
  have hRrank : Module.finrank ℚ R = n + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq hwlin rfl
  have hArank : Module.finrank ℚ A = 2 := by
    let e := Submodule.comapSubtypeEquivOfLe haR
    calc
      Module.finrank ℚ A = Module.finrank ℚ anchorSpan := e.finrank_eq
      _ = 2 := by
        exact finrank_eq_card_of_linearIndependent_span_eq
          canonicalAnchor_linearIndependent rfl
  have hAtop : A < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro htop
    have htopRank : Module.finrank ℚ A = Module.finrank ℚ R := by
      rw [htop]
      simp
    rw [hArank, hRrank] at htopRank
    omega
  let c : R →ₗ[ℚ] R := restrictedConjugation R hRstable
  have hc : c.comp c = LinearMap.id := restrictedConjugation_involutive R hRstable
  have hAstable : ∀ x ∈ A, c x ∈ A := by
    intro x hx
    change star (x : ℂ) ∈ anchorSpan
    have hx' : (x : ℂ) ∈ anchorSpan := hx
    have hmem : star (x : ℂ) ∈ anchorSpan.map conjugationLinearEquiv.toLinearMap :=
      ⟨(x : ℂ), hx', rfl⟩
    have hAnchorMap : anchorSpan.map conjugationLinearEquiv.toLinearMap = anchorSpan := by
      rw [map_span_conjugation_eq]
      exact conjugationStable_canonicalAnchor
    rwa [hAnchorMap] at hmem
  obtain ⟨g, hg, hgA, hginv, hgcodim⟩ :=
    exists_invariant_hyperplane_functional c hc A hAstable hAtop
  let P : Submodule ℚ ℂ := (LinearMap.ker g).map R.subtype
  have hPR : P ≤ R := by
    rintro z ⟨x, -, rfl⟩
    exact x.2
  have haP : anchorSpan ≤ P := by
    intro z hz
    refine ⟨⟨z, haR hz⟩, hgA ?_, rfl⟩
    exact hz
  have hPmap_le : P.map conjugationLinearEquiv.toLinearMap ≤ P := by
    rintro z ⟨y, ⟨x, hx, rfl⟩, rfl⟩
    have hgx : g x = 0 := LinearMap.mem_ker.mp hx
    have hgcx : g (c x) = 0 := by
      rcases hginv x with hplus | hminus
      · rw [hplus, hgx]
      · rw [hminus, hgx, neg_zero]
    exact ⟨c x, LinearMap.mem_ker.mpr hgcx, by
      exact restrictedConjugation_apply R hRstable x⟩
  have hPstable : P.map conjugationLinearEquiv.toLinearMap = P := by
    apply le_antisymm hPmap_le
    have hmap := Submodule.map_mono
      (f := conjugationLinearEquiv.toLinearMap) hPmap_le
    have hdouble : (P.map conjugationLinearEquiv.toLinearMap).map
        conjugationLinearEquiv.toLinearMap = P := by
      ext z
      constructor
      · rintro ⟨y, ⟨x, hx, rfl⟩, rfl⟩
        simpa using hx
      · intro hz
        exact ⟨star z, ⟨z, hz, rfl⟩, by simp⟩
    rwa [hdouble] at hmap
  obtain ⟨r, t, htlin, htspan⟩ := exists_fin_basis_of_le_span P w hPR
  have haT : anchorSpan ≤ Submodule.span ℚ (Set.range t) := by rwa [htspan]
  obtain ⟨k, u, hulin, huspanT, huzero, huone⟩ :=
    exists_fin_basis_with_canonicalAnchor haT
  have huspan : Submodule.span ℚ (Set.range u) = P := huspanT.trans htspan
  have hustable : ConjugationStable u := by
    unfold ConjugationStable
    rw [← map_span_conjugation_eq, huspan, hPstable]
  have hPrank : Module.finrank ℚ P + 1 = Module.finrank ℚ R := by
    simpa [P] using hgcodim
  have huRank : Module.finrank ℚ P = k + 2 :=
    finrank_eq_card_of_linearIndependent_span_eq hulin huspan
  have hkn : k < n := by
    rw [huRank, hRrank] at hPrank
    omega
  have hkOne : k + 1 = n := by
    rw [huRank, hRrank] at hPrank
    omega
  have hPlt : P < R := by
    apply lt_of_le_of_ne hPR
    intro hEq
    have hEqRank : Module.finrank ℚ P = Module.finrank ℚ R := by
      let e : P ≃ₗ[ℚ] R := LinearEquiv.ofEq P R hEq
      exact e.finrank_eq
    rw [hEqRank] at hPrank
    omega
  exact ⟨k, u, hulin, ⟨huzero, huone⟩, hustable,
    huspan.symm ▸ hPlt, hkn, hkOne⟩

/-! ## Least stable failures and exact defect one -/

/-- Failure at a fixed complementary arity with conjugation-stable rational input span. -/
def ConjugationStableCanonicalAnchoredFailureAt (n : ℕ) : Prop :=
  ∃ w : Fin (n + 2) → ℂ,
    LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧
      ConjugationStable w ∧ ¬ Bound w

/-- Stable anchored failures have a least complementary arity. -/
theorem exists_first_conjugationStableCanonicalAnchored_failure (h : ¬ Conjecture) :
    ∃ n, ConjugationStableCanonicalAnchoredFailureAt n ∧
      ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k := by
  classical
  have hex : ∃ n, ConjugationStableCanonicalAnchoredFailureAt n := by
    obtain ⟨n, w, hwlin, hwanchor, hwstable, hwfail⟩ :=
      exists_conjugationStable_canonicalAnchored_failure_of_not_conjecture h
    exact ⟨n, w, hwlin, hwanchor, hwstable, hwfail⟩
  let n := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  intro k hk hkfail
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hkfail)) hk

/-- A least conjugation-stable anchored failure has exact defect one.  For positive arity the
lower bound comes from the invariant codimension-one hyperplane; the zero-complement case uses
the first transcendental anchor coordinate. -/
theorem defectOne_of_no_smaller_conjugationStableCanonicalAnchored_failure
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hwanchor : CanonicallyAnchored w)
    (hwstable : ConjugationStable w) (hwfail : ¬ Bound w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k) :
    DefectOne w := by
  unfold DefectOne
  apply le_antisymm
  · have hlt : Algebra.trdeg ℚ (generatedField w) <
        (((n + 1) + 1 : ℕ) : Cardinal) := by
      apply lt_of_not_ge
      simpa [Bound, Nat.add_assoc] using hwfail
    rw [show ((((n + 1) + 1 : ℕ) : Cardinal)) =
        Order.succ ((n + 1 : ℕ) : Cardinal) by
      calc
        ((((n + 1) + 1 : ℕ) : Cardinal)) =
            ((n + 1 : ℕ) : Cardinal) + 1 := by norm_num
        _ = Order.succ ((n + 1 : ℕ) : Cardinal) :=
          (Cardinal.succ_natCast (n + 1)).symm] at hlt
    exact Order.lt_succ_iff.mp hlt
  · cases n with
    | zero =>
        let f : Fin 1 ↪ Fin 2 := Fin.castSuccEmb
        have hsubTrans : Transcendental ℚ ((w ∘ f) 0) := by
          change Transcendental ℚ (w 0)
          rw [hwanchor.1]
          exact canonicalAnchor_coordinate_transcendental 0
        have hsubBound : Bound (w ∘ f) := by
          apply bound_of_algebraicIndependent_coordinate
          rw [algebraicIndependent_unique_type_iff]
          exact hsubTrans
        have hsub := hsubBound
        change Cardinal.mk (Fin 1) ≤
          Algebra.trdeg ℚ (generatedField (w ∘ f)) at hsub
        simpa using hsub.trans (trdeg_comp_le w f)
    | succ q =>
        obtain ⟨k, u, hulin, huanchor, hustable, huspanlt, hklt, hkOne⟩ :=
          exists_canonicalAnchored_conjugationStable_codimOne_basis
            hwlin hwanchor hwstable (Nat.zero_lt_succ q)
        have huBound : Bound u := by
          by_contra huFail
          exact hmin k hklt ⟨u, hulin, huanchor, hustable, huFail⟩
        have huLower : ((k + 2 : ℕ) : Cardinal) ≤
            Algebra.trdeg ℚ (generatedField u) := by
          simpa [Bound] using huBound
        have hmono := trdeg_generatedField_le_of_span_le u w huspanlt.le
        have hlower := huLower.trans hmono
        have hkTwo : k + 2 = (q + 1) + 1 := by omega
        rwa [hkTwo] at hlower

/-- Every global failure has a least stable anchored defect-one witness. -/
theorem exists_conjugationStable_canonicalAnchored_defectOne_of_not_conjecture
    (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
      LinearIndependent ℚ w ∧ DefectOne w ∧ CanonicallyAnchored w ∧
        ConjugationStable w := by
  obtain ⟨n, ⟨w, hwlin, hwanchor, hwstable, hwfail⟩, hmin⟩ :=
    exists_first_conjugationStableCanonicalAnchored_failure h
  exact ⟨n, w, hwlin,
    defectOne_of_no_smaller_conjugationStableCanonicalAnchored_failure
      hwlin hwanchor hwstable hwfail hmin,
    hwanchor, hwstable⟩

/-- Exact stable defect-one frontier, before the final full-transcendence shear. -/
theorem not_conjecture_iff_exists_conjugationStable_canonicalAnchored_defectOne :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
        LinearIndependent ℚ w ∧ DefectOne w ∧ CanonicallyAnchored w ∧
          ConjugationStable w := by
  constructor
  · exact exists_conjugationStable_canonicalAnchored_defectOne_of_not_conjecture
  · rintro ⟨n, w, hwlin, hwdefect, -, -⟩ hC
    exact (noDefectOneIndependentFamilies_of_conjecture hC (n + 1) w hwlin) hwdefect

/-! ## Stable full-transcendence shear -/

/-- A simultaneous integral shear fixing its pivot preserves the rational input span exactly. -/
theorem span_integerShearFamily_eq {n : ℕ} (z : Fin n → ℂ) (j : Fin n)
    (a : Fin n → ℤ) (ha : a j = 0) :
    Submodule.span ℚ (Set.range (integerShearFamily z j a)) =
      Submodule.span ℚ (Set.range z) := by
  have hle (x : Fin n → ℂ) (b : Fin n → ℤ) :
      Submodule.span ℚ (Set.range (integerShearFamily x j b)) ≤
        Submodule.span ℚ (Set.range x) := by
    apply Submodule.span_le.mpr
    rintro y ⟨i, rfl⟩
    rw [integerShearFamily_apply]
    exact (Submodule.span ℚ (Set.range x)).add_mem
      (Submodule.subset_span (Set.mem_range_self i))
      ((Submodule.span ℚ (Set.range x)).smul_mem (b i : ℚ)
        (Submodule.subset_span (Set.mem_range_self j)))
  apply le_antisymm (hle z a)
  have hback := hle (integerShearFamily z j a) (fun i ↦ -a i)
  rw [integerShearFamily_neg_cancel z j a ha] at hback
  exact hback

/-- The canonical full-transcendence shear preserves not only the generated field but also the
rational input span, hence it preserves conjugation stability. -/
theorem exists_fullyTranscendental_canonicalAnchor_stable_shear
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hwanchor : CanonicallyAnchored w)
    (hwstable : ConjugationStable w) :
    ∃ v : Fin (n + 2) → ℂ,
      LinearIndependent ℚ v ∧ CanonicallyAnchored v ∧
      generatedField v = generatedField w ∧ ConjugationStable v ∧
      (∀ i, Transcendental ℚ (v i)) ∧
      ∀ i, Transcendental ℚ (Complex.exp (v i)) := by
  have hwzero : Transcendental ℚ (w 0) := by
    rw [hwanchor.1]
    exact canonicalAnchor_coordinate_transcendental 0
  have hwone : Transcendental ℚ (w 1) := by
    rw [hwanchor.2]
    exact canonicalAnchor_coordinate_transcendental 1
  let u := transcendentalShear w 0
  have hulin : LinearIndependent ℚ u :=
    (linearIndependent_transcendentalShear_iff hwzero).2 hwlin
  have hufield : generatedField u = generatedField w :=
    generatedField_transcendentalShear_eq hwzero
  have huspan : Submodule.span ℚ (Set.range u) =
      Submodule.span ℚ (Set.range w) := by
    exact span_integerShearFamily_eq w 0 (algebraicEliminationCoeffs w)
      (algebraicEliminationCoeffs_pivot_eq_zero hwzero)
  have hucoord : ∀ i, Transcendental ℚ (u i) :=
    transcendental_transcendentalShear hwzero
  have huzero : u 0 = canonicalAnchor 0 := by
    have hwzero' : ¬ IsAlgebraic ℚ (w 0) := hwzero
    calc
      u 0 = w 0 := by
        simp [u, transcendentalShear, algebraicEliminationCoeffs, hwzero']
      _ = canonicalAnchor 0 := hwanchor.1
  have huone : u 1 = canonicalAnchor 1 := by
    have hwone' : ¬ IsAlgebraic ℚ (w 1) := hwone
    calc
      u 1 = w 1 := by
        simp [u, transcendentalShear, algebraicEliminationCoeffs, hwone']
      _ = canonicalAnchor 1 := hwanchor.2
  have huexpzero : Transcendental ℚ (Complex.exp (u 0)) := by
    rw [huzero]
    exact canonicalAnchor_exp_transcendental 0
  have huexpone : Transcendental ℚ (Complex.exp (u 1)) := by
    rw [huone]
    exact canonicalAnchor_exp_transcendental 1
  let v := fullTranscendenceShear u 0
  have hvlin : LinearIndependent ℚ v :=
    (linearIndependent_fullTranscendenceShear_iff huexpzero).2 hulin
  have hvfield : generatedField v = generatedField w :=
    (generatedField_fullTranscendenceShear_eq huexpzero).trans hufield
  have hvspanU : Submodule.span ℚ (Set.range v) =
      Submodule.span ℚ (Set.range u) := by
    exact span_integerShearFamily_eq u 0 (fullTranscendenceCoeffs u 0)
      (fullTranscendenceCoeffs_pivot_eq_zero huexpzero)
  have hvspan : Submodule.span ℚ (Set.range v) =
      Submodule.span ℚ (Set.range w) := hvspanU.trans huspan
  have hvstable : ConjugationStable v :=
    (conjugationStable_iff_of_span_eq hvspan).mpr hwstable
  have hvcoord : ∀ i, Transcendental ℚ (v i) :=
    transcendental_fullTranscendenceShear hucoord
  have hvexp : ∀ i, Transcendental ℚ (Complex.exp (v i)) :=
    transcendental_exp_fullTranscendenceShear huexpzero
  have hvzero : v 0 = canonicalAnchor 0 := by
    calc
      v 0 = u 0 := by
        simp [v, fullTranscendenceShear, fullTranscendenceCoeffs, huexpzero]
      _ = canonicalAnchor 0 := huzero
  have hvone : v 1 = canonicalAnchor 1 := by
    calc
      v 1 = u 1 := by
        simp [v, fullTranscendenceShear, fullTranscendenceCoeffs, huexpone]
      _ = canonicalAnchor 1 := huone
  exact ⟨v, hvlin, ⟨hvzero, hvone⟩, hvfield, hvstable, hvcoord, hvexp⟩

/-- The full requested stable canonical normal form. -/
theorem not_conjecture_iff_exists_conjugationStableCanonicalDefectOne :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
        ConjugationStableCanonicalDefectOne w := by
  constructor
  · intro h
    obtain ⟨n, w, hwlin, hwdefect, hwanchor, hwstable⟩ :=
      exists_conjugationStable_canonicalAnchored_defectOne_of_not_conjecture h
    obtain ⟨v, hvlin, hvanchor, hvfield, hvstable, hvcoord, hvexp⟩ :=
      exists_fullyTranscendental_canonicalAnchor_stable_shear
        hwlin hwanchor hwstable
    exact ⟨n, v, ⟨hvlin, (defectOne_congr_generatedField hvfield).2 hwdefect,
      hvanchor, hvcoord, hvexp⟩, hvstable⟩
  · rintro ⟨n, w, hw⟩
    exact not_conjecture_of_conjugationStableCanonicalDefectOne hw

end ConjugationStableMinimalFailure

end

end Schanuel
