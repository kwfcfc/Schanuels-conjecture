import Schanuel.MinimalCounterexampleFullyTranscendental
import Schanuel.PeriodLogBoundary

/-!
# Period-bearing fully transcendental defect-one counterexamples

This file strengthens the positive fully transcendental normal form by arranging that the
standard period `2 * pi * I` belongs to the rational span of the inputs.  The construction uses
one of the two shifts `period + z` and `period + 2 * z`.  In the algebraic branch it replaces a
deleted coordinate; in the transcendental branch it appends the shift.
-/

namespace Schanuel

open Function Set

noncomputable section

/-- The standard period used by the period-bearing normal form. -/
abbrev standardPeriod : ℂ := PeriodLogBoundary.period

/-- Shift an input by the standard period and a positive integral multiple of a pivot. -/
def periodShift (k : ℕ) (x : ℂ) : ℂ :=
  standardPeriod + (k : ℂ) * x

@[simp]
theorem exp_standardPeriod : Complex.exp standardPeriod = 1 := by
  simpa [standardPeriod, PeriodLogBoundary.period] using Complex.exp_two_pi_mul_I

@[simp]
theorem exp_periodShift (k : ℕ) (x : ℂ) :
    Complex.exp (periodShift k x) = Complex.exp x ^ k := by
  rw [periodShift, Complex.exp_add, exp_standardPeriod, one_mul]
  simpa only using Complex.exp_nat_mul x k

/-- For a transcendental pivot with transcendental exponential, one of the first two period
shifts has both properties again. -/
theorem exists_transcendental_periodShift {x : ℂ}
    (hx : Transcendental ℚ x)
    (hexp : Transcendental ℚ (Complex.exp x)) :
    ∃ k : ℕ, (k = 1 ∨ k = 2) ∧
      Transcendental ℚ (periodShift k x) ∧
      Transcendental ℚ (Complex.exp (periodShift k x)) := by
  by_cases hfirst : Transcendental ℚ (periodShift 1 x)
  · refine ⟨1, Or.inl rfl, hfirst, ?_⟩
    simpa using hexp
  · have hfirstAlg : IsAlgebraic ℚ (periodShift 1 x) := not_not.mp hfirst
    have hsecond : Transcendental ℚ (periodShift 2 x) := by
      have hadd := transcendental_add_of_isAlgebraic_left hfirstAlg hx
      convert hadd using 1 <;> simp [periodShift] <;> ring
    refine ⟨2, Or.inr rfl, hsecond, ?_⟩
    simpa using hexp.pow (by norm_num : 0 < 2)

/-- The old generated field embeds in the generated field obtained by appending one input. -/
theorem generatedField_le_generatedField_snoc {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    generatedField v ≤ generatedField (Fin.snoc v h) := by
  apply IntermediateField.adjoin.mono
  rintro x (hx | hx)
  · rcases hx with ⟨i, rfl⟩
    exact Or.inl ⟨i.castSucc, by simp⟩
  · rcases hx with ⟨i, rfl⟩
    exact Or.inr ⟨i.castSucc, by simp⟩

/-- The graph field of the literal initial segment embeds in the graph field of the full tuple. -/
theorem generatedField_init_le_generatedField {r : ℕ} (u : Fin (r + 1) → ℂ) :
    generatedField (Fin.init u) ≤ generatedField u := by
  apply IntermediateField.adjoin.mono
  rintro x (hx | hx)
  · rcases hx with ⟨i, rfl⟩
    exact Or.inl ⟨i.castSucc, rfl⟩
  · rcases hx with ⟨i, rfl⟩
    exact Or.inr ⟨i.castSucc, rfl⟩

/-- Appending one input enlarges the old graph field by exactly that input and its exponential. -/
theorem generatedField_snoc_eq_sup_adjoin_pair {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    generatedField (Fin.snoc v h) =
      generatedField v ⊔ IntermediateField.adjoin ℚ
        ({h, Complex.exp h} : Set ℂ) := by
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.snoc_last] using
          (show IntermediateField.adjoin ℚ
              ({h, Complex.exp h} : Set ℂ) ≤ _ from le_sup_right)
            (IntermediateField.subset_adjoin ℚ _ (Set.mem_insert h {Complex.exp h}))
      · simpa only [Fin.snoc_castSucc] using
          (show generatedField v ≤ _ from le_sup_left)
            (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩))
    · refine Fin.lastCases ?_ (fun j ↦ ?_) i
      · simpa only [Fin.snoc_last] using
          (show IntermediateField.adjoin ℚ
              ({h, Complex.exp h} : Set ℂ) ≤ _ from le_sup_right)
            (IntermediateField.subset_adjoin ℚ _
              (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))
      · simpa only [Fin.snoc_castSucc] using
          (show generatedField v ≤ _ from le_sup_left)
            (IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩))
  · apply sup_le
    · exact generatedField_le_generatedField_snoc v h
    · rw [IntermediateField.adjoin_le_iff]
      rintro x (rfl | hx)
      · exact IntermediateField.subset_adjoin ℚ _
          (Or.inl ⟨Fin.last r, by simp⟩)
      · rcases hx with rfl
        exact IntermediateField.subset_adjoin ℚ _
          (Or.inr ⟨Fin.last r, by simp⟩)

noncomputable instance generatedFieldAlgebraSnoc {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    Algebra (generatedField v) (generatedField (Fin.snoc v h)) :=
  (IntermediateField.inclusion (generatedField_le_generatedField_snoc v h)).toRingHom.toAlgebra

instance generatedFieldSnocIsScalarTower {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    IsScalarTower ℚ (generatedField v) (generatedField (Fin.snoc v h)) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- The appended coordinate, regarded as an element of the enlarged generated field. -/
def snocCoordinate {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    generatedField (Fin.snoc v h) :=
  ⟨h, IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨Fin.last r, by simp⟩)⟩

@[simp]
theorem coe_snocCoordinate {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    (snocCoordinate v h : ℂ) = h := rfl

/-- The exponential of the appended coordinate, regarded as an element of the enlarged
generated field. -/
def snocExponential {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    generatedField (Fin.snoc v h) :=
  ⟨Complex.exp h,
    IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨Fin.last r, by simp⟩)⟩

@[simp]
theorem coe_snocExponential {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    (snocExponential v h : ℂ) = Complex.exp h := rfl

/-- Over the old graph field, the graph field after appending one coordinate is generated by
that coordinate and its exponential. -/
theorem adjoin_snocPair_eq_top {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    IntermediateField.adjoin (generatedField v)
      ({snocCoordinate v h, snocExponential v h} :
        Set (generatedField (Fin.snoc v h))) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ -
  let E := generatedField (Fin.snoc v h)
  let F := generatedField v
  let p : ∀ y ∈ E, Prop := fun y hy ↦
    (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin F
      ({snocCoordinate v h, snocExponential v h} : Set E)
  exact IntermediateField.adjoin_induction ℚ (p := p)
    (fun y hy ↦ by
      rcases hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [p, E, F, snocCoordinate] using
            (IntermediateField.subset_adjoin F
              ({snocCoordinate v h, snocExponential v h} : Set E)
              (Set.mem_insert (snocCoordinate v h) {snocExponential v h}))
        · dsimp [p, E, F]
          simpa only [Fin.snoc_castSucc] using
            (IntermediateField.adjoin (generatedField v)
              ({snocCoordinate v h, snocExponential v h} : Set E)).algebraMap_mem
                ⟨v j, IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩)⟩
      · refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [p, E, F, snocExponential] using
            (IntermediateField.subset_adjoin F
              ({snocCoordinate v h, snocExponential v h} : Set E)
              (Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton _))))
        · dsimp [p, E, F]
          simpa only [Fin.snoc_castSucc] using
            (IntermediateField.adjoin (generatedField v)
              ({snocCoordinate v h, snocExponential v h} : Set E)).algebraMap_mem
                ⟨Complex.exp (v j),
                  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)⟩)
    (fun q ↦ by
      exact (IntermediateField.adjoin F
        ({snocCoordinate v h, snocExponential v h} : Set E)).algebraMap_mem
          ⟨(q : ℂ), IntermediateField.algebraMap_mem _ q⟩)
    (fun _ _ _ _ ha hb ↦ IntermediateField.add_mem _ ha hb)
    (fun _ _ ha ↦ IntermediateField.inv_mem _ ha)
    (fun _ _ _ _ ha hb ↦ IntermediateField.mul_mem _ ha hb)
    hx

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The enlarged graph field is algebraic over the algebra generated by the appended coordinate
and its exponential. -/
theorem isAlgebraic_adjoin_snocPair {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    Algebra.IsAlgebraic
      (Algebra.adjoin (generatedField v)
        ({snocCoordinate v h, snocExponential v h} :
          Set (generatedField (Fin.snoc v h))))
      (generatedField (Fin.snoc v h)) := by
  let f :
      IntermediateField.adjoin (generatedField v)
          ({snocCoordinate v h, snocExponential v h} :
            Set (generatedField (Fin.snoc v h))) →ₐ[
        Algebra.adjoin (generatedField v)
          ({snocCoordinate v h, snocExponential v h} :
            Set (generatedField (Fin.snoc v h)))]
        generatedField (Fin.snoc v h) :=
    IsScalarTower.toAlgHom _ _ _
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [adjoin_snocPair_eq_top v h]
    exact IntermediateField.mem_top
  let e := AlgEquiv.ofBijective f ⟨f.injective, hf_surj⟩
  exact e.isAlgebraic

/-- If an appended coordinate and its exponential are both algebraic over the old graph field,
then the enlarged graph field is algebraic over the old one. -/
theorem isAlgebraic_generatedField_snoc_of_pair_isAlgebraic {r : ℕ}
    (v : Fin r → ℂ) (h : ℂ)
    (hh : IsAlgebraic (generatedField v) h)
    (hexp : IsAlgebraic (generatedField v) (Complex.exp h)) :
    Algebra.IsAlgebraic (generatedField v) (generatedField (Fin.snoc v h)) := by
  let P := generatedField (Fin.snoc v h)
  let F := generatedField v
  haveI : IsScalarTower F P ℂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let A : Subalgebra F P := Algebra.adjoin F
    ({snocCoordinate v h, snocExponential v h} : Set P)
  letI : Algebra F A := A.algebra
  letI : Algebra A P := A.toAlgebra
  letI : IsScalarTower F A P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hhP : IsAlgebraic F (snocCoordinate v h) := by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom F P ℂ)
      Subtype.val_injective]
    exact hh
  have hexpP : IsAlgebraic F (snocExponential v h) := by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom F P ℂ)
      Subtype.val_injective]
    exact hexp
  letI : Algebra.IsAlgebraic A P := isAlgebraic_adjoin_snocPair v h
  have hsubAlg : A.IsAlgebraic := by
    rw [Algebra.isAlgebraic_adjoin_iff]
    rintro x (rfl | hx)
    · exact hhP
    · rcases hx with rfl
      exact hexpP
  letI : Algebra.IsAlgebraic F A :=
    ⟨fun x ↦ Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (hsubAlg x x.2)⟩
  exact Algebra.IsAlgebraic.trans F A P

/-- Appending a coordinate whose value and exponential are algebraic over the old graph field
does not change absolute transcendence degree. -/
theorem trdeg_generatedField_snoc_eq_of_pair_isAlgebraic {r : ℕ}
    (v : Fin r → ℂ) (h : ℂ)
    (hh : IsAlgebraic (generatedField v) h)
    (hexp : IsAlgebraic (generatedField v) (Complex.exp h)) :
    Algebra.trdeg ℚ (generatedField (Fin.snoc v h)) =
      Algebra.trdeg ℚ (generatedField v) := by
  letI : Algebra.IsAlgebraic (generatedField v) (generatedField (Fin.snoc v h)) :=
    isAlgebraic_generatedField_snoc_of_pair_isAlgebraic v h hh hexp
  have hadd := trdeg_add_eq ℚ (generatedField v)
    (A := generatedField (Fin.snoc v h))
  have hzero : Algebra.trdeg (generatedField v) (generatedField (Fin.snoc v h)) = 0 :=
    trdeg_eq_zero
  rw [hzero, add_zero] at hadd
  exact hadd.symm

/-- Taking the initial segment after appending a coordinate leaves the graph-field
transcendence degree unchanged, with the dependent tuple coercions made explicit. -/
theorem trdeg_generatedField_init_snoc {r : ℕ} (v : Fin r → ℂ) (h : ℂ) :
    Algebra.trdeg ℚ (generatedField
      (Fin.init (Fin.snoc (α := fun _ : Fin (r + 1) ↦ ℂ) v h))) =
      Algebra.trdeg ℚ (generatedField v) := by
  have hi : Fin.init (Fin.snoc (α := fun _ : Fin (r + 1) ↦ ℂ) v h) = v :=
    @Fin.init_snoc r (fun _ : Fin (r + 1) ↦ ℂ) h v
  exact congrArg (fun t : Fin r → ℂ ↦ Algebra.trdeg ℚ (generatedField t)) hi

/-- Algebraicity over the graph field of an initial segment after `snoc` is exactly
algebraicity over the original graph field. -/
theorem isAlgebraic_generatedField_init_snoc_iff {r : ℕ}
    (v : Fin r → ℂ) (h x : ℂ) :
    IsAlgebraic (generatedField
      (Fin.init (Fin.snoc (α := fun _ : Fin (r + 1) ↦ ℂ) v h))) x ↔
      IsAlgebraic (generatedField v) x := by
  have hi : Fin.init (Fin.snoc (α := fun _ : Fin (r + 1) ↦ ℂ) v h) = v :=
    @Fin.init_snoc r (fun _ : Fin (r + 1) ↦ ℂ) h v
  exact (congrArg
    (fun t : Fin r → ℂ ↦ IsAlgebraic (generatedField t) x) hi).to_iff

/-- If the exponential of the appended coordinate is already in the old field, the enlarged
field is generated over the old field by that coordinate alone. -/
theorem adjoin_snocCoordinate_eq_top {r : ℕ} (v : Fin r → ℂ) (h : ℂ)
    (hexp : Complex.exp h ∈ generatedField v) :
    IntermediateField.adjoin (generatedField v)
      ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h))) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ -
  let E := generatedField (Fin.snoc v h)
  let F := generatedField v
  let p : ∀ y ∈ E, Prop := fun y hy ↦
    (⟨y, hy⟩ : E) ∈ IntermediateField.adjoin F ({snocCoordinate v h} : Set E)
  exact IntermediateField.adjoin_induction ℚ (p := p)
    (fun y hy ↦ by
      rcases hy with ⟨i, rfl⟩ | ⟨i, rfl⟩
      · refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · simpa [p, E, F, snocCoordinate] using
            (IntermediateField.subset_adjoin F ({snocCoordinate v h} : Set E)
              (Set.mem_singleton (snocCoordinate v h)))
        · dsimp [p, E, F]
          simpa only [Fin.snoc_castSucc] using
            (IntermediateField.adjoin (generatedField v)
              ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h)))).algebraMap_mem
                ⟨v j, IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩)⟩
      · refine Fin.lastCases ?_ (fun j ↦ ?_) i
        · dsimp [p, E, F]
          simpa only [Fin.snoc_last] using
            (IntermediateField.adjoin (generatedField v)
              ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h)))).algebraMap_mem
                ⟨Complex.exp h, hexp⟩
        · dsimp [p, E, F]
          simpa only [Fin.snoc_castSucc] using
            (IntermediateField.adjoin (generatedField v)
              ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h)))).algebraMap_mem
                ⟨Complex.exp (v j),
                  IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)⟩)
    (fun q ↦ by
      exact (IntermediateField.adjoin F ({snocCoordinate v h} : Set E)).algebraMap_mem
        ⟨(q : ℂ), IntermediateField.algebraMap_mem _ q⟩)
    (fun _ _ _ _ ha hb ↦ IntermediateField.add_mem _ ha hb)
    (fun _ _ ha ↦ IntermediateField.inv_mem _ ha)
    (fun _ _ _ _ ha hb ↦ IntermediateField.mul_mem _ ha hb)
    hx

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The enlarged generated field is algebraic over the algebra generated by the one appended
coordinate, provided its exponential was already in the old field. -/
theorem isAlgebraic_adjoin_snocCoordinate {r : ℕ} (v : Fin r → ℂ) (h : ℂ)
    (hexp : Complex.exp h ∈ generatedField v) :
    Algebra.IsAlgebraic
      (Algebra.adjoin (generatedField v)
        ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h))))
      (generatedField (Fin.snoc v h)) := by
  let f :
      IntermediateField.adjoin (generatedField v)
          ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h))) →ₐ[
        Algebra.adjoin (generatedField v)
          ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h)))]
        generatedField (Fin.snoc v h) :=
    IsScalarTower.toAlgHom _ _ _
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [adjoin_snocCoordinate_eq_top v h hexp]
    exact IntermediateField.mem_top
  let e := AlgEquiv.ofBijective f ⟨f.injective, hf_surj⟩
  exact e.isAlgebraic

/-- Appending one coordinate whose exponential is old costs at most one relative
transcendence degree. -/
theorem relative_trdeg_generatedField_snoc_le_one {r : ℕ} (v : Fin r → ℂ) (h : ℂ)
    (hexp : Complex.exp h ∈ generatedField v) :
    Algebra.trdeg (generatedField v) (generatedField (Fin.snoc v h)) ≤ 1 := by
  letI : Algebra.IsAlgebraic
      (Algebra.adjoin (generatedField v)
        ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h))))
      (generatedField (Fin.snoc v h)) :=
    isAlgebraic_adjoin_snocCoordinate v h hexp
  simpa using (Algebra.IsAlgebraic.trdeg_le_cardinalMk
    (generatedField v)
      ({snocCoordinate v h} : Set (generatedField (Fin.snoc v h))))

/-- If the appended coordinate is algebraic over the old field and its exponential is old, then
the enlarged generated field is algebraic over the old one. -/
theorem isAlgebraic_generatedField_snoc {r : ℕ} (v : Fin r → ℂ) (h : ℂ)
    (hh : IsAlgebraic (generatedField v) h)
    (hexp : Complex.exp h ∈ generatedField v) :
    Algebra.IsAlgebraic (generatedField v) (generatedField (Fin.snoc v h)) := by
  let P := generatedField (Fin.snoc v h)
  let F := generatedField v
  haveI : IsScalarTower F P ℂ := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let A : Subalgebra F P := Algebra.adjoin F ({snocCoordinate v h} : Set P)
  letI : Algebra F A := A.algebra
  letI : Algebra A P := A.toAlgebra
  letI : IsScalarTower F A P := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hhP : IsAlgebraic F (snocCoordinate v h) := by
    rw [← isAlgebraic_algHom_iff (IsScalarTower.toAlgHom F P ℂ)
      Subtype.val_injective]
    exact hh
  letI : Algebra.IsAlgebraic A P :=
    isAlgebraic_adjoin_snocCoordinate v h hexp
  have hsubAlg : A.IsAlgebraic :=
    Algebra.isAlgebraic_adjoin_singleton_iff.mpr hhP
  letI : Algebra.IsAlgebraic F A :=
    ⟨fun x ↦ Subalgebra.isAlgebraic_iff_isAlgebraic_val.mpr (hsubAlg x x.2)⟩
  exact Algebra.IsAlgebraic.trans F A P

/-- Appending an algebraic coordinate whose exponential is old does not change the absolute
transcendence degree. -/
theorem trdeg_generatedField_snoc_eq_of_isAlgebraic {r : ℕ} (v : Fin r → ℂ) (h : ℂ)
    (hh : IsAlgebraic (generatedField v) h)
    (hexp : Complex.exp h ∈ generatedField v) :
    Algebra.trdeg ℚ (generatedField (Fin.snoc v h)) =
      Algebra.trdeg ℚ (generatedField v) := by
  letI : Algebra.IsAlgebraic (generatedField v) (generatedField (Fin.snoc v h)) :=
    isAlgebraic_generatedField_snoc v h hh hexp
  have hadd := trdeg_add_eq ℚ (generatedField v)
    (A := generatedField (Fin.snoc v h))
  have hzero : Algebra.trdeg (generatedField v) (generatedField (Fin.snoc v h)) = 0 :=
    trdeg_eq_zero
  rw [hzero, add_zero] at hadd
  exact hadd.symm

/-- Appending a coordinate transcendental over the old field, while its exponential is old,
raises the absolute transcendence degree by exactly one. -/
theorem trdeg_generatedField_snoc_eq_add_one_of_transcendental {r : ℕ}
    (v : Fin r → ℂ) (h : ℂ)
    (hh : Transcendental (generatedField v) h)
    (hexp : Complex.exp h ∈ generatedField v) :
    Algebra.trdeg ℚ (generatedField (Fin.snoc v h)) =
      Algebra.trdeg ℚ (generatedField v) + 1 := by
  have hle := relative_trdeg_generatedField_snoc_le_one v h hexp
  haveI : IsScalarTower (generatedField v) (generatedField (Fin.snoc v h)) ℂ :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have hne : Algebra.trdeg (generatedField v) (generatedField (Fin.snoc v h)) ≠ 0 := by
    intro hzero
    letI : Algebra.IsAlgebraic (generatedField v) (generatedField (Fin.snoc v h)) :=
      trdeg_eq_zero_iff.mp hzero
    have hcoordAlg : IsAlgebraic (generatedField v) (snocCoordinate v h) :=
      Algebra.IsAlgebraic.isAlgebraic _
    apply hh
    rw [← isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom (generatedField v) (generatedField (Fin.snoc v h)) ℂ)
      Subtype.val_injective] at hcoordAlg
    exact hcoordAlg
  have hrel : Algebra.trdeg (generatedField v) (generatedField (Fin.snoc v h)) = 1 := by
    rcases Cardinal.le_one_iff.mp hle with hzero | hone
    · exact (hne hzero).elim
    · exact hone
  have hadd := trdeg_add_eq ℚ (generatedField v)
    (A := generatedField (Fin.snoc v h))
  simpa [hrel] using hadd.symm

/-- The exponential of an integral period shift of an old coordinate lies in the old generated
field. -/
theorem exp_periodShift_mem_generatedField {r : ℕ} (v : Fin r → ℂ) (i : Fin r)
    (k : ℕ) : Complex.exp (periodShift k (v i)) ∈ generatedField v := by
  rw [exp_periodShift]
  exact (generatedField v).pow_mem
    (IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)) k

/-- Appending a period shift puts the standard period in the rational span. -/
theorem standardPeriod_mem_span_snoc_periodShift {r : ℕ} (v : Fin r → ℂ)
    (i : Fin r) (k : ℕ) :
    standardPeriod ∈ Submodule.span ℚ (Set.range (Fin.snoc v (periodShift k (v i)))) := by
  let S := Submodule.span ℚ (Set.range (Fin.snoc v (periodShift k (v i))))
  have hlast : periodShift k (v i) ∈ S := by
    simpa [S] using
      (Submodule.subset_span
        (s := Set.range (Fin.snoc v (periodShift k (v i))))
        (Set.mem_range_self (Fin.last r)))
  have hi : v i ∈ S := by
    simpa only [Fin.snoc_castSucc] using
      (Submodule.subset_span
        (s := Set.range (Fin.snoc v (periodShift k (v i))))
        (Set.mem_range_self i.castSucc))
  have hsub := S.sub_mem hlast (S.smul_mem (k : ℚ) hi)
  simpa [S, periodShift, Rat.smul_def] using hsub

/-- If the old family is independent and does not already span the standard period, appending
one of its period shifts preserves independence. -/
theorem linearIndependent_snoc_periodShift {r : ℕ} {v : Fin r → ℂ}
    (hlin : LinearIndependent ℚ v)
    (hperiod : standardPeriod ∉ Submodule.span ℚ (Set.range v))
    (i : Fin r) (k : ℕ) :
    LinearIndependent ℚ (Fin.snoc v (periodShift k (v i))) := by
  rw [linearIndependent_fin_snoc]
  refine ⟨hlin, ?_⟩
  intro hshift
  have hi : v i ∈ Submodule.span ℚ (Set.range v) :=
    Submodule.subset_span (Set.mem_range_self i)
  have hsub := (Submodule.span ℚ (Set.range v)).sub_mem hshift
    ((Submodule.span ℚ (Set.range v)).smul_mem (k : ℚ) hi)
  apply hperiod
  simpa [periodShift, Rat.smul_def] using hsub

/-- Pointwise transcendence is preserved when a transcendental last coordinate is appended. -/
theorem transcendental_snoc {r : ℕ} {v : Fin r → ℂ} {h : ℂ}
    (hv : ∀ i, Transcendental ℚ (v i)) (hh : Transcendental ℚ h) :
    ∀ i, Transcendental ℚ ((Fin.snoc v h : Fin (r + 1) → ℂ) i) := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using hh
  · simpa using hv j

/-- Pointwise exponential transcendence is preserved when a suitable last coordinate is
appended. -/
theorem transcendental_exp_snoc {r : ℕ} {v : Fin r → ℂ} {h : ℂ}
    (hv : ∀ i, Transcendental ℚ (Complex.exp (v i)))
    (hh : Transcendental ℚ (Complex.exp h)) :
    ∀ i, Transcendental ℚ
      (Complex.exp ((Fin.snoc v h : Fin (r + 1) → ℂ) i)) := by
  intro i
  refine Fin.lastCases ?_ (fun j ↦ ?_) i
  · simpa using hh
  · simpa using hv j

/-- Every failure of Schanuel's conjecture has a positive-arity fully transcendental defect-one
witness whose rational input span contains the standard period. -/
theorem exists_positive_fullyTranscendental_defectOne_periodBearing
    (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
      0 < n ∧
      LinearIndependent ℚ w ∧
      DefectOne w ∧
      (∀ i, Transcendental ℚ (w i)) ∧
      (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
      (2 * Real.pi * Complex.I : ℂ) ∈ Submodule.span ℚ (Set.range w) := by
  obtain ⟨n, z, hn, hlin, hfail, hdefect, hcoord, hexp, hmin⟩ :=
    exists_positive_fullyTranscendental_defectOne_minimal_failure h
  by_cases hperiod : standardPeriod ∈ Submodule.span ℚ (Set.range z)
  · exact ⟨n, z, hn, hlin, hdefect, hcoord, hexp, hperiod⟩
  · by_cases homega : IsAlgebraic (generatedField z) standardPeriod
    · let f : Fin n ↪ Fin (n + 1) := Fin.castSuccEmb
      let v : Fin n → ℂ := z ∘ f
      let i : Fin n := ⟨0, hn⟩
      have hvlin : LinearIndependent ℚ v := hlin.comp f f.injective
      have hvcoord : ∀ j, Transcendental ℚ (v j) := fun j ↦ hcoord (f j)
      have hvexp : ∀ j, Transcendental ℚ (Complex.exp (v j)) := fun j ↦ hexp (f j)
      obtain ⟨k, hk, hshift, hshiftExp⟩ :=
        exists_transcendental_periodShift (hvcoord i) (hvexp i)
      have hrange : Set.range v ⊆ Set.range z := by
        rintro x ⟨j, rfl⟩
        exact ⟨f j, rfl⟩
      have hperiodV : standardPeriod ∉ Submodule.span ℚ (Set.range v) := by
        intro hv
        exact hperiod (Submodule.span_mono hrange hv)
      have hwlin : LinearIndependent ℚ (Fin.snoc v (periodShift k (v i))) :=
        linearIndependent_snoc_periodShift hvlin hperiodV i k
      have hwcoord : ∀ j, Transcendental ℚ
          ((Fin.snoc v (periodShift k (v i)) : Fin (n + 1) → ℂ) j) :=
        transcendental_snoc hvcoord hshift
      have hwexp : ∀ j, Transcendental ℚ
          (Complex.exp
            ((Fin.snoc v (periodShift k (v i)) : Fin (n + 1) → ℂ) j)) :=
        transcendental_exp_snoc hvexp hshiftExp
      have hprev : ¬ FullyTranscendentalFailureAt n :=
        hmin n (Nat.lt_succ_self n)
      have htdv : Algebra.trdeg ℚ (generatedField v) = ((n : ℕ) : Cardinal) := by
        simpa [v] using
          restricted_trdeg_eq_of_no_fullyTranscendental_predecessor_failure
            hlin hcoord hexp hfail hprev f
      let hgen := generators_comp_subset z f
      letI : Algebra (generatedField v) (generatedField z) :=
        (generatedFieldInclusion hgen).toAlgebra
      haveI : IsScalarTower ℚ (generatedField v) (generatedField z) := by
        apply IsScalarTower.of_algebraMap_eq'
        ext x
        rfl
      letI : Algebra.IsAlgebraic (generatedField v) (generatedField z) := by
        simpa [v, f] using
          (isAlgebraic_over_restriction_of_no_fullyTranscendental_predecessor_failure
            hlin hcoord hexp hfail hprev f)
      haveI : IsScalarTower (generatedField v) (generatedField z) ℂ := by
        apply IsScalarTower.of_algebraMap_eq'
        ext x
        rfl
      have homegaV : IsAlgebraic (generatedField v) standardPeriod :=
        homega.restrictScalars (generatedField v)
      have hvi : IsAlgebraic (generatedField v) (v i) := by
        have hmem : v i ∈ generatedField v :=
          IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
        have halg := isAlgebraic_algebraMap (R := generatedField v) (A := ℂ)
          (⟨v i, hmem⟩ : generatedField v)
        simpa using halg
      have hkalg : IsAlgebraic (generatedField v) (k : ℂ) := by
        have halg := isAlgebraic_algebraMap (R := generatedField v) (A := ℂ)
          (k : generatedField v)
        simpa using halg
      have hshiftAlg : IsAlgebraic (generatedField v) (periodShift k (v i)) := by
        simpa [periodShift] using homegaV.add (hkalg.mul hvi)
      have hexpMem : Complex.exp (periodShift k (v i)) ∈ generatedField v :=
        exp_periodShift_mem_generatedField v i k
      have htdw : Algebra.trdeg ℚ
          (generatedField (Fin.snoc v (periodShift k (v i)))) = ((n : ℕ) : Cardinal) := by
        rw [trdeg_generatedField_snoc_eq_of_isAlgebraic v _ hshiftAlg hexpMem]
        exact htdv
      have hwdefect : DefectOne (Fin.snoc v (periodShift k (v i))) := by
        exact htdw
      exact ⟨n, Fin.snoc v (periodShift k (v i)), hn, hwlin, hwdefect,
        hwcoord, hwexp, standardPeriod_mem_span_snoc_periodShift v i k⟩
    · have homegaTrans : Transcendental (generatedField z) standardPeriod := homega
      let i : Fin (n + 1) := 0
      have hzi : IsAlgebraic (generatedField z) (z i) := by
        have hmem : z i ∈ generatedField z :=
          IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)
        have halg := isAlgebraic_algebraMap (R := generatedField z) (A := ℂ)
          (⟨z i, hmem⟩ : generatedField z)
        simpa using halg
      have hshiftTrans : Transcendental (generatedField z) (periodShift 1 (z i)) := by
        intro hshiftAlg
        apply homegaTrans
        have hsub := hshiftAlg.sub hzi
        simpa [periodShift] using hsub
      have hshiftTransQ : Transcendental ℚ (periodShift 1 (z i)) :=
        Transcendental.of_tower_top ℚ hshiftTrans
      have hshiftExpTransQ : Transcendental ℚ
          (Complex.exp (periodShift 1 (z i))) := by
        simpa using hexp i
      have hexpMem : Complex.exp (periodShift 1 (z i)) ∈ generatedField z :=
        exp_periodShift_mem_generatedField z i 1
      have htdw := trdeg_generatedField_snoc_eq_add_one_of_transcendental
        z (periodShift 1 (z i)) hshiftTrans hexpMem
      have hwdefect : DefectOne (Fin.snoc z (periodShift 1 (z i))) := by
        unfold DefectOne at hdefect ⊢
        rw [htdw, hdefect]
        norm_cast
      exact ⟨n + 1, Fin.snoc z (periodShift 1 (z i)), Nat.zero_lt_succ n,
        linearIndependent_snoc_periodShift hlin hperiod i 1, hwdefect,
        transcendental_snoc hcoord hshiftTransQ,
        transcendental_exp_snoc hexp hshiftExpTransQ,
        standardPeriod_mem_span_snoc_periodShift z i 1⟩

/-- Failure of Schanuel's conjecture is equivalent to the existence of a positive fully
transcendental defect-one family whose rational span contains `2 * pi * I`. -/
theorem not_conjecture_iff_exists_periodBearing_fullyTranscendental_defectOne :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
        0 < n ∧
        LinearIndependent ℚ w ∧
        DefectOne w ∧
        (∀ i, Transcendental ℚ (w i)) ∧
        (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
        (2 * Real.pi * Complex.I : ℂ) ∈ Submodule.span ℚ (Set.range w) := by
  constructor
  · exact exists_positive_fullyTranscendental_defectOne_periodBearing
  · rintro ⟨n, w, -, hlin, hdefect, -, -, -⟩ hC
    exact (noDefectOneIndependentFamilies_of_conjecture hC n w hlin) hdefect

end

end Schanuel
