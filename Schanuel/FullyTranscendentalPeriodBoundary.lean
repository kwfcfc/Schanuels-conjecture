import Schanuel.FullyTranscendentalMixedBoundary
import Schanuel.PeriodLogBoundary

/-!
# A fully transcendental duplicate-value period boundary

The family `(1 + 2*pi*I, 1 + 4*pi*I)` is rationally linearly independent, all four displayed
coordinates and exponentials are transcendental, and its two exponential values are both `e`.
Its Schanuel bound is exactly algebraic independence of `2*pi*I` and `e`.
-/

namespace Schanuel.FullyTranscendentalPeriodBoundary

open Complex Set

noncomputable section

abbrev period : ℂ := PeriodLogBoundary.period

/-- The unsheared basis `(1, 2*pi*I)`. -/
def base : Fin 2 → ℂ := ![1, period]

/-- First replace `1` by `1 + 2*pi*I`. -/
def firstShear : Fin 2 → ℂ :=
  integerShear base 0 1 1

/-- Then replace the period by its sum with the first coordinate. -/
def family : Fin 2 → ℂ :=
  integerShear firstShear 1 0 1

/-- The two genuinely unresolved generators. -/
def core : Fin 2 → ℂ := ![period, Complex.exp 1]

@[simp]
theorem base_zero : base 0 = 1 := rfl

@[simp]
theorem base_one : base 1 = period := rfl

@[simp]
theorem firstShear_zero : firstShear 0 = 1 + period := by
  simp [firstShear, base, integerShear, integerShearFamily]

@[simp]
theorem firstShear_one : firstShear 1 = period := by
  simp [firstShear, base, integerShear, integerShearFamily]

@[simp]
theorem family_zero : family 0 = 1 + period := by
  simp [family]

@[simp]
theorem family_one : family 1 = 1 + 2 * period := by
  simp [family]
  ring

/-- The two fully transcendental inputs differ by exactly one standard period. -/
theorem family_one_sub_family_zero : family 1 - family 0 = period := by
  rw [family_one, family_zero]
  ring

@[simp]
theorem core_zero : core 0 = period := rfl

@[simp]
theorem core_one : core 1 = Complex.exp 1 := rfl

theorem period_ne_zero : period ≠ 0 := by
  intro hzero
  have him := congrArg Complex.im hzero
  change (2 * Real.pi * Complex.I : ℂ).im = 0 at him
  norm_num at him

/-- The basic complex period is transcendental, using the checked Hermite--Lindemann endpoint. -/
theorem period_transcendental : Transcendental ℚ period := by
  intro halg
  have h := LindemannAttempt.hermiteLindemann_of_galoisStableEndpoint
    period halg period_ne_zero
  apply h
  rw [show Complex.exp period = 1 by exact Complex.exp_two_pi_mul_I]
  exact isAlgebraic_one

theorem base_linearIndependent : LinearIndependent ℚ base := by
  rw [linearIndependent_fin2]
  constructor
  · exact period_ne_zero
  · intro a ha
    have hre := congrArg Complex.re ha
    change ((a : ℂ) * period).re = (1 : ℂ).re at hre
    simp [period, PeriodLogBoundary.period] at hre

/-- The two integral shears preserve rational linear independence. -/
theorem family_linearIndependent : LinearIndependent ℚ family := by
  apply (linearIndependent_integerShear_iff firstShear 1 0 1 (by decide)).2
  exact (linearIndependent_integerShear_iff base 0 1 1 (by decide)).2
    base_linearIndependent

/-- The two shears preserve the generated field exactly. -/
theorem generatedField_family_eq_base :
    generatedField family = generatedField base := by
  calc
    generatedField family = generatedField firstShear :=
      generatedField_integerShear_eq firstShear 1 0 1 (by decide)
    _ = generatedField base :=
      generatedField_integerShear_eq base 0 1 1 (by decide)

theorem exp_one_transcendental : Transcendental ℚ (Complex.exp 1) := by
  simpa using LindemannAttempt.exp_intCast_transcendental 1 (by norm_num)

/-- Both sheared coordinates are transcendental. -/
theorem coordinate_transcendental : ∀ i, Transcendental ℚ (family i) := by
  intro i
  fin_cases i
  · change Transcendental ℚ (family 0)
    rw [family_zero]
    exact transcendental_add_of_isAlgebraic_left isAlgebraic_one period_transcendental
  · change Transcendental ℚ (family 1)
    rw [family_one]
    have htwo : Transcendental ℚ ((2 : ℂ) * period) :=
      transcendental_mul_of_isAlgebraic_left
        (isAlgebraic_algebraMap (A := ℂ) (2 : ℚ)) (by norm_num)
        period_transcendental
    exact transcendental_add_of_isAlgebraic_left isAlgebraic_one htwo

@[simp]
theorem exp_family_zero : Complex.exp (family 0) = Complex.exp 1 := by
  rw [family_zero, Complex.exp_add]
  have hperiod : Complex.exp period = 1 := by
    change Complex.exp (2 * Real.pi * Complex.I) = 1
    exact Complex.exp_two_pi_mul_I
  rw [hperiod]
  simp

@[simp]
theorem exp_family_one : Complex.exp (family 1) = Complex.exp 1 := by
  rw [family_one, Complex.exp_add]
  have hperiod : Complex.exp period = 1 := by
    change Complex.exp (2 * Real.pi * Complex.I) = 1
    exact Complex.exp_two_pi_mul_I
  rw [show 2 * period = period + period by ring, Complex.exp_add, hperiod]
  simp

/-- The two displayed exponential values coincide. -/
theorem exp_family_one_eq_exp_family_zero :
    Complex.exp (family 1) = Complex.exp (family 0) := by
  rw [exp_family_one, exp_family_zero]

/-- Both exponential values are the same transcendental number `e`. -/
theorem exponential_transcendental :
    ∀ i, Transcendental ℚ (Complex.exp (family i)) := by
  intro i
  fin_cases i
  · change Transcendental ℚ (Complex.exp (family 0))
    rw [exp_family_zero]
    exact exp_one_transcendental
  · change Transcendental ℚ (Complex.exp (family 1))
    rw [exp_family_one]
    exact exp_one_transcendental

/-- The generated field is exactly `Q(2*pi*I, e)`. -/
theorem generatedField_eq_adjoin_core :
    generatedField family = IntermediateField.adjoin ℚ (Set.range core) := by
  apply le_antisymm
  · rw [generatedField, IntermediateField.adjoin_le_iff]
    rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · fin_cases i
      · change family 0 ∈ IntermediateField.adjoin ℚ (Set.range core)
        rw [family_zero]
        have hone : (1 : ℂ) ∈ IntermediateField.adjoin ℚ (Set.range core) := by
          simp
        exact (IntermediateField.adjoin ℚ (Set.range core)).add_mem
          hone
          (IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩)
      · change family 1 ∈ IntermediateField.adjoin ℚ (Set.range core)
        rw [family_one]
        have hone : (1 : ℂ) ∈ IntermediateField.adjoin ℚ (Set.range core) := by
          simp
        exact (IntermediateField.adjoin ℚ (Set.range core)).add_mem
          hone
          ((IntermediateField.adjoin ℚ (Set.range core)).mul_mem
            (IntermediateField.algebraMap_mem _ (2 : ℚ))
            (IntermediateField.subset_adjoin ℚ _ ⟨0, rfl⟩))
    · fin_cases i
      · change Complex.exp (family 0) ∈ IntermediateField.adjoin ℚ (Set.range core)
        rw [exp_family_zero]
        exact IntermediateField.subset_adjoin ℚ _ ⟨1, rfl⟩
      · change Complex.exp (family 1) ∈ IntermediateField.adjoin ℚ (Set.range core)
        rw [exp_family_one]
        exact IntermediateField.subset_adjoin ℚ _ ⟨1, rfl⟩
  · rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    fin_cases i
    · have hx0 : family 0 ∈ generatedField family :=
        IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨0, rfl⟩)
      have hone : (1 : ℂ) ∈ generatedField family :=
        by simp
      rw [family_zero] at hx0
      simpa using (generatedField family).sub_mem hx0 hone
    · exact IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨0, exp_family_zero⟩)

/-- The reduced pair, regarded inside the Schanuel field. -/
def liftedCore : Fin 2 → generatedField family := fun i ↦
  ⟨core i, by
    rw [generatedField_eq_adjoin_core]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self i)⟩

@[simp]
theorem coe_liftedCore (i : Fin 2) : (liftedCore i : ℂ) = core i := rfl

theorem image_val_range_liftedCore :
    Subtype.val '' Set.range liftedCore = Set.range core := by
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨liftedCore i, ⟨i, rfl⟩, rfl⟩

theorem adjoin_range_liftedCore_eq_top :
    IntermediateField.adjoin ℚ (Set.range liftedCore) = ⊤ := by
  apply IntermediateField.map_injective (inclusion family)
  rw [IntermediateField.adjoin_map, ← AlgHom.fieldRange_eq_map]
  rw [show inclusion family '' Set.range liftedCore =
      Subtype.val '' Set.range liftedCore by rfl]
  rw [image_val_range_liftedCore, fieldRange_inclusion, generatedField_eq_adjoin_core]

open scoped IntermediateField.algebraAdjoinAdjoin in
theorem isAlgebraic_adjoin_range_liftedCore :
    Algebra.IsAlgebraic
      (Algebra.adjoin ℚ (Set.range liftedCore)) (generatedField family) := by
  let f :
      IntermediateField.adjoin ℚ (Set.range liftedCore) →ₐ[
        Algebra.adjoin ℚ (Set.range liftedCore)] generatedField family :=
    IsScalarTower.toAlgHom _ _ _
  have hf_surj : Function.Surjective f := by
    intro x
    refine ⟨⟨x, ?_⟩, rfl⟩
    rw [adjoin_range_liftedCore_eq_top]
    exact IntermediateField.mem_top
  let e := AlgEquiv.ofBijective f ⟨f.injective, hf_surj⟩
  exact e.isAlgebraic

/-- The Schanuel bound for the fully transcendental duplicate-value family is exactly algebraic
independence of the basic period and `e`. -/
theorem bound_family_iff_algebraicIndependent_period_exp_one :
    Bound family ↔ AlgebraicIndependent ℚ core := by
  constructor
  · intro hbound
    letI : Algebra.IsAlgebraic
        (Algebra.adjoin ℚ (Set.range liftedCore)) (generatedField family) :=
      isAlgebraic_adjoin_range_liftedCore
    have htb : IsTranscendenceBasis ℚ liftedCore :=
      Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg ℚ liftedCore
        (trdeg_lt_aleph0 family) hbound
    have hcomplex := htb.1.map' (generatedField family).val.injective
    simpa [Function.comp_def] using hcomplex
  · intro hcore
    have hlifted : AlgebraicIndependent ℚ liftedCore := by
      apply AlgebraicIndependent.of_comp (generatedField family).val
      simpa [Function.comp_def] using hcore
    exact hlifted.cardinalMk_le_trdeg

/-- The fully transcendental conjecture would imply algebraic independence of `e` and the basic
complex period even on a family whose two exponential values coincide. -/
theorem fullyTranscendentalConjecture_implies_algebraicIndependent_period_exp_one
    (h : FullyTranscendentalConjecture) :
    AlgebraicIndependent ℚ core := by
  apply bound_family_iff_algebraicIndependent_period_exp_one.mp
  exact h 2 family family_linearIndependent coordinate_transcendental
    exponential_transcendental

end

end Schanuel.FullyTranscendentalPeriodBoundary
