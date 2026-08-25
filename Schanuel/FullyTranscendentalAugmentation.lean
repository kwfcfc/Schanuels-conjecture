import Schanuel.AlgebraicRanks
import Schanuel.FullyTranscendentalReduction

/-!
# Reduction to the fully transcendental branch by augmentation

For a rationally linearly independent family `u` whose exponentials are algebraic, adjoining
`1` remains linearly independent: a rational relation would make `exp 1` algebraic.  Two
elementary integral shears then replace

`(1, u₀, u₁, ...)`

by

`(u₀ + 2, u₀ + 1, u₁ + 1, ...)`.

Every displayed coordinate and exponential is transcendental.  The new generated field is
exactly the old generated field with `exp 1` adjoined, so its transcendence degree exceeds that
of the old field by at most one.  This proves that Schanuel's conjecture is equivalent to its
restriction to tuples for which every coordinate and every exponential is transcendental.
-/

namespace Schanuel

open Function Set

noncomputable section

/-- Adjoin `1` as the first coordinate of a finite family. -/
def prependOne {n : ℕ} (u : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  Fin.cons 1 u

/-- Coefficients which add the new first coordinate `1` to every old coordinate. -/
def prependOneShearCoeffs {n : ℕ} : Fin (n + 1) → ℤ :=
  Fin.cons 0 (fun _ ↦ 1)

/-- First add `1` to every original coordinate. -/
def addOneToOldCoordinates {n : ℕ} (u : Fin n → ℂ) : Fin (n + 1) → ℂ :=
  integerShearFamily (prependOne u) 0 prependOneShearCoeffs

/-- For a nonempty original family, additionally add `u₀ + 1` to the leading `1`.
The result is `(u₀ + 2, u₀ + 1, u₁ + 1, ...)`. -/
def fullyTranscendentalAugmentation {n : ℕ} (u : Fin (n + 1) → ℂ) :
    Fin (n + 2) → ℂ :=
  integerShear (addOneToOldCoordinates u) 0 1 1

@[simp]
theorem prependOne_zero {n : ℕ} (u : Fin n → ℂ) : prependOne u 0 = 1 := by
  simp [prependOne]

@[simp]
theorem prependOne_succ {n : ℕ} (u : Fin n → ℂ) (i : Fin n) :
    prependOne u i.succ = u i := by
  simp [prependOne]

@[simp]
theorem prependOneShearCoeffs_zero {n : ℕ} :
    (prependOneShearCoeffs : Fin (n + 1) → ℤ) 0 = 0 := by
  simp [prependOneShearCoeffs]

@[simp]
theorem addOneToOldCoordinates_zero {n : ℕ} (u : Fin n → ℂ) :
    addOneToOldCoordinates u 0 = 1 := by
  simp [addOneToOldCoordinates]

@[simp]
theorem addOneToOldCoordinates_succ {n : ℕ} (u : Fin n → ℂ) (i : Fin n) :
    addOneToOldCoordinates u i.succ = u i + 1 := by
  simp [addOneToOldCoordinates, prependOneShearCoeffs]

@[simp]
theorem fullyTranscendentalAugmentation_zero {n : ℕ} (u : Fin (n + 1) → ℂ) :
    fullyTranscendentalAugmentation u 0 = u 0 + 2 := by
  rw [fullyTranscendentalAugmentation, integerShear_apply_same,
    addOneToOldCoordinates_zero]
  rw [show (1 : Fin (n + 2)) = (0 : Fin (n + 1)).succ by rfl,
    addOneToOldCoordinates_succ]
  ring

@[simp]
theorem fullyTranscendentalAugmentation_succ {n : ℕ} (u : Fin (n + 1) → ℂ)
    (i : Fin (n + 1)) :
    fullyTranscendentalAugmentation u i.succ = u i + 1 := by
  rw [fullyTranscendentalAugmentation, integerShear_apply_of_ne]
  · exact addOneToOldCoordinates_succ u i
  · exact Fin.succ_ne_zero i

/-- If all `exp (u i)` are algebraic, then adjoining the coordinate `1` preserves rational
linear independence. -/
theorem linearIndependent_prependOne_of_exp_isAlgebraic {n : ℕ} {u : Fin n → ℂ}
    (hlin : LinearIndependent ℚ u)
    (hexp : ∀ i, IsAlgebraic ℚ (Complex.exp (u i))) :
    LinearIndependent ℚ (prependOne u) := by
  apply hlin.fin_cons
  intro hone
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hone
  have halg : IsAlgebraic ℚ (Complex.exp 1) := by
    rw [← hc, Complex.exp_sum]
    exact Finset.prod_induction
      (fun i ↦ Complex.exp (c i • u i)) (IsAlgebraic ℚ)
      (fun _ _ ha hb ↦ ha.mul hb) isAlgebraic_one
      (fun i _ ↦ isAlgebraic_exp_rat_smul (c i) (hexp i))
  have htrans : Transcendental ℚ (Complex.exp (1 : ℂ)) := by
    simpa using LindemannAttempt.exp_intCast_transcendental (1 : ℤ) (by norm_num)
  exact htrans halg

/-- The explicit two-shear augmentation preserves rational linear independence. -/
theorem linearIndependent_fullyTranscendentalAugmentation {n : ℕ}
    {u : Fin (n + 1) → ℂ} (hlin : LinearIndependent ℚ u)
    (hexp : ∀ i, IsAlgebraic ℚ (Complex.exp (u i))) :
    LinearIndependent ℚ (fullyTranscendentalAugmentation u) := by
  have hpre : LinearIndependent ℚ (prependOne u) :=
    linearIndependent_prependOne_of_exp_isAlgebraic hlin hexp
  have hadd : LinearIndependent ℚ (addOneToOldCoordinates u) :=
    (linearIndependent_integerShearFamily_iff (prependOne u) 0
      prependOneShearCoeffs (by simp)).2 hpre
  exact (linearIndependent_integerShear_iff (addOneToOldCoordinates u) 0 1 1
    (by exact Fin.zero_ne_one')).2 hadd

/-- Every coordinate of the augmentation is transcendental. -/
theorem transcendental_fullyTranscendentalAugmentation {n : ℕ}
    {u : Fin (n + 1) → ℂ} (htrans : ∀ i, Transcendental ℚ (u i)) :
    ∀ i, Transcendental ℚ (fullyTranscendentalAugmentation u i) := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [fullyTranscendentalAugmentation_zero]
    have h := transcendental_add_of_isAlgebraic_left
      (isAlgebraic_algebraMap (A := ℂ) (2 : ℚ)) (htrans 0)
    simpa [add_comm] using h
  · rw [fullyTranscendentalAugmentation_succ]
    have h := transcendental_add_of_isAlgebraic_left isAlgebraic_one (htrans j)
    simpa [add_comm] using h

/-- Every exponential of the augmentation is transcendental. -/
theorem transcendental_exp_fullyTranscendentalAugmentation {n : ℕ}
    {u : Fin (n + 1) → ℂ}
    (hexp : ∀ i, IsAlgebraic ℚ (Complex.exp (u i))) :
    ∀ i, Transcendental ℚ (Complex.exp (fullyTranscendentalAugmentation u i)) := by
  intro i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · rw [fullyTranscendentalAugmentation_zero, Complex.exp_add]
    exact transcendental_mul_of_isAlgebraic_left (hexp 0) (Complex.exp_ne_zero _)
      (LindemannAttempt.exp_intCast_transcendental 2 (by norm_num))
  · rw [fullyTranscendentalAugmentation_succ, Complex.exp_add]
    exact transcendental_mul_of_isAlgebraic_left (hexp j) (Complex.exp_ne_zero _)
      (by simpa using (LindemannAttempt.exp_intCast_transcendental 1 (by norm_num)))

/-- Adjoining `1` adds exactly one possible new generator, namely `exp 1`. -/
def expOneAdjoinField {n : ℕ} (u : Fin n → ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ (insert (Complex.exp 1) (generators u))

/-- Exact generated-field identity for the tuple with `1` prepended. -/
theorem generatedField_prependOne_eq_expOneAdjoinField {n : ℕ} (u : Fin n → ℂ) :
    generatedField (prependOne u) = expOneAdjoinField u := by
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact IntermediateField.one_mem _
      · exact IntermediateField.subset_adjoin ℚ _
          (mem_insert_of_mem _ (Or.inl ⟨j, rfl⟩))
    · refine Fin.cases ?_ (fun j ↦ ?_) i
      · exact IntermediateField.subset_adjoin ℚ _ (mem_insert _ _)
      · exact IntermediateField.subset_adjoin ℚ _
          (mem_insert_of_mem _ (Or.inr ⟨j, rfl⟩))
  · rw [expOneAdjoinField, IntermediateField.adjoin_le_iff]
    rintro x (rfl | hx)
    · exact IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨0, by simp [prependOne]⟩)
    · rcases hx with ⟨j, rfl⟩ | ⟨j, rfl⟩
      · exact IntermediateField.subset_adjoin ℚ _
          (Or.inl ⟨j.succ, by simp [prependOne]⟩)
      · exact IntermediateField.subset_adjoin ℚ _
          (Or.inr ⟨j.succ, by simp [prependOne]⟩)

/-- Exact generated-field identity for the fully transcendental augmentation. -/
theorem generatedField_fullyTranscendentalAugmentation_eq_expOneAdjoinField {n : ℕ}
    (u : Fin (n + 1) → ℂ) :
    generatedField (fullyTranscendentalAugmentation u) = expOneAdjoinField u := by
  calc
    generatedField (fullyTranscendentalAugmentation u) =
      generatedField (addOneToOldCoordinates u) :=
      generatedField_integerShear_eq (addOneToOldCoordinates u) 0 1 1
        (by exact Fin.zero_ne_one')
    _ = generatedField (prependOne u) :=
      generatedField_integerShearFamily_eq (prependOne u) 0 prependOneShearCoeffs (by simp)
    _ = expOneAdjoinField u := generatedField_prependOne_eq_expOneAdjoinField u

/-- The old generated field embeds in the field obtained by adjoining `exp 1`. -/
theorem generatedField_le_expOneAdjoinField {n : ℕ} (u : Fin n → ℂ) :
    generatedField u ≤ expOneAdjoinField u := by
  apply IntermediateField.adjoin.mono
  exact subset_insert _ _

noncomputable instance generatedFieldAlgebraExpOneAdjoinField {n : ℕ} (u : Fin n → ℂ) :
    Algebra (generatedField u) (expOneAdjoinField u) :=
  (IntermediateField.inclusion (generatedField_le_expOneAdjoinField u)).toRingHom.toAlgebra

instance generatedFieldExpOneAdjoinFieldIsScalarTower {n : ℕ} (u : Fin n → ℂ) :
    IsScalarTower ℚ (generatedField u) (expOneAdjoinField u) :=
  IsScalarTower.of_algebraMap_eq fun _ ↦ rfl

/-- `exp 1`, as an element of the one-element augmented field. -/
def expOneInAdjoinField {n : ℕ} (u : Fin n → ℂ) : expOneAdjoinField u :=
  ⟨Complex.exp 1, IntermediateField.subset_adjoin ℚ _ (mem_insert _ _)⟩

@[simp]
theorem coe_expOneInAdjoinField {n : ℕ} (u : Fin n → ℂ) :
    (expOneInAdjoinField u : ℂ) = Complex.exp 1 :=
  rfl

/-- Over the old generated field, the augmented field is generated by the singleton `exp 1`. -/
theorem adjoin_expOneInAdjoinField_eq_top {n : ℕ} (u : Fin n → ℂ) :
    IntermediateField.adjoin (generatedField u)
      ({expOneInAdjoinField u} : Set (expOneAdjoinField u)) = ⊤ := by
  apply top_unique
  rintro ⟨x, hx⟩ -
  let p : ∀ y ∈ expOneAdjoinField u, Prop :=
    fun y hy ↦ (⟨y, hy⟩ : expOneAdjoinField u) ∈
      IntermediateField.adjoin (generatedField u)
        ({expOneInAdjoinField u} : Set (expOneAdjoinField u))
  exact IntermediateField.adjoin_induction ℚ (p := p)
    (fun y hy ↦ by
      rcases hy with rfl | hy
      · exact IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)
      · have hyF : y ∈ generatedField u := IntermediateField.subset_adjoin ℚ _ hy
        exact (IntermediateField.adjoin (generatedField u)
          ({expOneInAdjoinField u} : Set (expOneAdjoinField u))).algebraMap_mem ⟨y, hyF⟩)
    (fun q ↦ by
      have hqF : (q : ℂ) ∈ generatedField u := IntermediateField.algebraMap_mem _ q
      exact (IntermediateField.adjoin (generatedField u)
        ({expOneInAdjoinField u} : Set (expOneAdjoinField u))).algebraMap_mem ⟨(q : ℂ), hqF⟩)
    (fun _ _ _ _ ha hb ↦ IntermediateField.add_mem _ ha hb)
    (fun _ _ ha ↦ IntermediateField.inv_mem _ ha)
    (fun _ _ _ _ ha hb ↦ IntermediateField.mul_mem _ ha hb)
    hx

open scoped IntermediateField.algebraAdjoinAdjoin in
/-- The augmented field is algebraic over the algebra generated by its one new element. -/
theorem isAlgebraic_adjoin_expOneInAdjoinField {n : ℕ} (u : Fin n → ℂ) :
    Algebra.IsAlgebraic
      (Algebra.adjoin (generatedField u) ({expOneInAdjoinField u} : Set (expOneAdjoinField u)))
      (expOneAdjoinField u) := by
  let f :
      IntermediateField.adjoin (generatedField u)
          ({expOneInAdjoinField u} : Set (expOneAdjoinField u)) →ₐ[
        Algebra.adjoin (generatedField u)
          ({expOneInAdjoinField u} : Set (expOneAdjoinField u))]
        expOneAdjoinField u :=
    IsScalarTower.toAlgHom _ _ _
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [adjoin_expOneInAdjoinField_eq_top]
    exact IntermediateField.mem_top
  let e := AlgEquiv.ofBijective f ⟨f.injective, hf_surj⟩
  exact e.isAlgebraic

/-- Adjoining `exp 1` costs at most one relative transcendence degree. -/
theorem relative_trdeg_expOneAdjoinField_le_one {n : ℕ} (u : Fin n → ℂ) :
    Algebra.trdeg (generatedField u) (expOneAdjoinField u) ≤ 1 := by
  letI : Algebra.IsAlgebraic
      (Algebra.adjoin (generatedField u)
        ({expOneInAdjoinField u} : Set (expOneAdjoinField u)))
      (expOneAdjoinField u) :=
    isAlgebraic_adjoin_expOneInAdjoinField u
  simpa using (Algebra.IsAlgebraic.trdeg_le_cardinalMk
    (generatedField u) ({expOneInAdjoinField u} : Set (expOneAdjoinField u)))

/-- Absolute transcendence degree rises by at most one after adjoining `exp 1`. -/
theorem trdeg_expOneAdjoinField_le_add_one {n : ℕ} (u : Fin n → ℂ) :
    Algebra.trdeg ℚ (expOneAdjoinField u) ≤
      Algebra.trdeg ℚ (generatedField u) + 1 := by
  calc
    Algebra.trdeg ℚ (expOneAdjoinField u) =
        Algebra.trdeg ℚ (generatedField u) +
          Algebra.trdeg (generatedField u) (expOneAdjoinField u) :=
      (trdeg_add_eq ℚ (generatedField u)).symm
    _ ≤ Algebra.trdeg ℚ (generatedField u) + 1 :=
      add_le_add_right (relative_trdeg_expOneAdjoinField_le_one u) _

/-- The fully transcendental conjecture proves the formerly residual branch where all
coordinates are transcendental and all exponentials are algebraic. -/
theorem transcendentalAlgebraicExpConjecture_of_fullyTranscendental
    (hfull : FullyTranscendentalConjecture) :
    TranscendentalAlgebraicExpConjecture := by
  intro n u hlin htrans hexp
  cases n with
  | zero => exact bound_zero u
  | succ n =>
      have haug := hfull (n + 2) (fullyTranscendentalAugmentation u)
        (linearIndependent_fullyTranscendentalAugmentation hlin hexp)
        (transcendental_fullyTranscendentalAugmentation htrans)
        (transcendental_exp_fullyTranscendentalAugmentation hexp)
      unfold Bound at haug ⊢
      have hdegree :
          Algebra.trdeg ℚ (generatedField (fullyTranscendentalAugmentation u)) ≤
            Algebra.trdeg ℚ (generatedField u) + 1 := by
        rw [generatedField_fullyTranscendentalAugmentation_eq_expOneAdjoinField]
        exact trdeg_expOneAdjoinField_le_add_one u
      have hcancel : ((n + 1 : ℕ) : Cardinal) ≤
          Algebra.trdeg ℚ (generatedField u) := by
        have hwithOne : ((n + 1 : ℕ) : Cardinal) + 1 ≤
            Algebra.trdeg ℚ (generatedField u) + 1 := by
          calc
            ((n + 1 : ℕ) : Cardinal) + 1 = Cardinal.mk (Fin (n + 2)) := by
              rw [Cardinal.mk_fin]
              norm_cast
            _ ≤ Algebra.trdeg ℚ (generatedField (fullyTranscendentalAugmentation u)) := haug
            _ ≤ Algebra.trdeg ℚ (generatedField u) + 1 := hdegree
        simpa using hwithOne
      simpa using hcancel

/-- Schanuel's conjecture is equivalent to its restriction to tuples for which every coordinate
and every exponential is individually transcendental. -/
theorem conjecture_iff_fullyTranscendental :
    Conjecture ↔ FullyTranscendentalConjecture := by
  constructor
  · intro hS n z hlin _ _
    exact hS n z hlin
  · intro hfull
    exact conjecture_iff_uniformTranscendental_branches.mpr
      ⟨transcendentalAlgebraicExpConjecture_of_fullyTranscendental hfull, hfull⟩

end

end Schanuel
