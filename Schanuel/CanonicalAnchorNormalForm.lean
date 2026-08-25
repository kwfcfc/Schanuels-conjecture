import Schanuel.AdjacentPeriodNormalForm
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-!
# Canonical-anchor defect-one normal form

This file strengthens the adjacent-period normal form by fixing its first two inputs literally
at `1 + 2*pi*I` and `1 + 4*pi*I`.  The main ingredients are a rectangular rational-family
Kummer comparison, a finite basis extension with two prescribed leading vectors, least-arity
descent among anchored failures, and one simultaneous integral shear.
-/

namespace Schanuel

open Function Set

noncomputable section

/-! ## Rectangular rational-family comparison -/

/-- A finite family of rational linear combinations; unlike `rationalMatrixFamily`, the source
and target arities may differ. -/
def rectangularRationalFamily {m n : ℕ} (B : Fin m → Fin n → ℚ)
    (z : Fin n → ℂ) : Fin m → ℂ :=
  fun i ↦ ∑ j, B i j • z j

/-- The integral version of a rectangular rational family. -/
def rectangularIntegerFamily {m n : ℕ} (A : Fin m → Fin n → ℤ)
    (z : Fin n → ℂ) : Fin m → ℂ :=
  fun i ↦ ∑ j, (A i j : ℚ) • z j

/-- One positive integral scalar clears every denominator of a finite rectangular rational
matrix. -/
theorem exists_pos_integer_rectangular_scale {m n : ℕ} (B : Fin m → Fin n → ℚ) :
    ∃ d : ℤ, 0 < d ∧ ∃ A : Fin m → Fin n → ℤ,
      ∀ i j, (A i j : ℚ) = (d : ℚ) * B i j := by
  let f : Fin m × Fin n → ℚ := fun ij ↦ B ij.1 ij.2
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite
    (nonZeroDivisors ℤ) f
  choose A hA using fun i j ↦ hb (i, j)
  let d : ℤ := (b : ℤ) ^ 2
  let C : Fin m → Fin n → ℤ := fun i j ↦ (b : ℤ) * A i j
  refine ⟨d, sq_pos_of_ne_zero (nonZeroDivisors.coe_ne_zero b), C, ?_⟩
  intro i j
  have hij := hA i j
  change algebraMap ℤ ℚ (A i j) = ((b : ℤ) : ℚ) • B i j at hij
  change (((b : ℤ) * A i j : ℤ) : ℚ) = (((b : ℤ) ^ 2 : ℤ) : ℚ) * B i j
  calc
    (((b : ℤ) * A i j : ℤ) : ℚ) = ((b : ℤ) : ℚ) * (A i j : ℚ) := by
      exact_mod_cast rfl
    _ = ((b : ℤ) : ℚ) * (((b : ℤ) : ℚ) * B i j) := by congr 1
    _ = (((b : ℤ) ^ 2 : ℤ) : ℚ) * B i j := by
      push_cast
      ring

/-- Clearing a rectangular matrix is the same as scaling its output family. -/
theorem rectangularIntegerFamily_eq_ratScaleFamily {m n : ℕ}
    (B : Fin m → Fin n → ℚ) (d : ℤ) (A : Fin m → Fin n → ℤ)
    (hA : ∀ i j, (A i j : ℚ) = (d : ℚ) * B i j) (z : Fin n → ℂ) :
    rectangularIntegerFamily A z = ratScaleFamily (d : ℚ) (rectangularRationalFamily B z) := by
  funext i
  simp only [rectangularIntegerFamily, rectangularRationalFamily, ratScaleFamily]
  simp_rw [hA, mul_smul]
  change (∑ j, (d : ℚ) • (B i j • z j)) = (d : ℚ) • ∑ j, B i j • z j
  exact Finset.smul_sum.symm

/-- Integral rectangular combinations introduce no new coordinate or exponential generators. -/
theorem generatedField_rectangularIntegerFamily_le {m n : ℕ}
    (A : Fin m → Fin n → ℤ) (z : Fin n → ℂ) :
    generatedField (rectangularIntegerFamily A z) ≤ generatedField z := by
  rw [generatedField, IntermediateField.adjoin_le_iff]
  rintro x (⟨i, rfl⟩ | ⟨i, rfl⟩)
  · change (∑ j, (A i j : ℚ) • z j) ∈ generatedField z
    apply (generatedField z).sum_mem
    intro j _
    rw [Rat.smul_def]
    exact (generatedField z).mul_mem
      (IntermediateField.algebraMap_mem _ (A i j : ℚ))
      (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨j, rfl⟩))
  · change Complex.exp (∑ j, (A i j : ℚ) • z j) ∈ generatedField z
    rw [Complex.exp_sum]
    apply (generatedField z).prod_mem
    intro j _
    rw [Rat.smul_def, Rat.cast_intCast, Complex.exp_int_mul]
    exact (generatedField z).pow_mem
      (IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨j, rfl⟩)) (A i j)

/-- A rectangular rational family has no larger generated-field transcendence degree than its
source.  Denominator clearing is the Kummer step. -/
theorem trdeg_rectangularRationalFamily_le {m n : ℕ}
    (B : Fin m → Fin n → ℚ) (z : Fin n → ℂ) :
    Algebra.trdeg ℚ (generatedField (rectangularRationalFamily B z)) ≤
      Algebra.trdeg ℚ (generatedField z) := by
  obtain ⟨d, hd, A, hA⟩ := exists_pos_integer_rectangular_scale B
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  rw [← trdeg_ratScaleFamily_eq (d : ℚ) hdQ (rectangularRationalFamily B z),
    ← rectangularIntegerFamily_eq_ratScaleFamily B d A hA z]
  exact trdeg_generatedField_le_of_le (generatedField_rectangularIntegerFamily_le A z)

/-- Span inclusion gives generated-field transcendence-degree monotonicity, including all
denominator/Kummer effects of rational linear combinations. -/
theorem trdeg_generatedField_le_of_span_le {m n : ℕ}
    (w : Fin m → ℂ) (z : Fin n → ℂ)
    (hspan : Submodule.span ℚ (Set.range w) ≤ Submodule.span ℚ (Set.range z)) :
    Algebra.trdeg ℚ (generatedField w) ≤ Algebra.trdeg ℚ (generatedField z) := by
  have hwmem : ∀ i, w i ∈ Submodule.span ℚ (Set.range z) := fun i ↦
    hspan (Submodule.subset_span (Set.mem_range_self i))
  choose c hc using fun i ↦ (Submodule.mem_span_range_iff_exists_fun ℚ).mp (hwmem i)
  let B : Fin m → Fin n → ℚ := fun i ↦ c i
  have heq : rectangularRationalFamily B z = w := by
    funext i
    exact hc i
  rw [← heq]
  exact trdeg_rectangularRationalFamily_le B z

/-- Two finite families spanning the same rational subspace have equal generated-field
transcendence degree. -/
theorem trdeg_generatedField_eq_of_span_eq {m n : ℕ}
    (w : Fin m → ℂ) (z : Fin n → ℂ)
    (hspan : Submodule.span ℚ (Set.range w) = Submodule.span ℚ (Set.range z)) :
    Algebra.trdeg ℚ (generatedField w) = Algebra.trdeg ℚ (generatedField z) :=
  le_antisymm
    (trdeg_generatedField_le_of_span_le w z hspan.le)
    (trdeg_generatedField_le_of_span_le z w hspan.ge)

/-! ## A finite basis with the canonical anchor first -/

/-- The fixed canonical anchor `(1 + omega, 1 + 2*omega)`. -/
abbrev canonicalAnchor : Fin 2 → ℂ :=
  FullyTranscendentalPeriodBoundary.family

@[simp]
theorem canonicalAnchor_zero : canonicalAnchor 0 = 1 + standardPeriod := by
  exact FullyTranscendentalPeriodBoundary.family_zero

@[simp]
theorem canonicalAnchor_one : canonicalAnchor 1 = 1 + 2 * standardPeriod := by
  exact FullyTranscendentalPeriodBoundary.family_one

theorem canonicalAnchor_linearIndependent : LinearIndependent ℚ canonicalAnchor :=
  FullyTranscendentalPeriodBoundary.family_linearIndependent

theorem canonicalAnchor_coordinate_transcendental :
    ∀ i, Transcendental ℚ (canonicalAnchor i) :=
  FullyTranscendentalPeriodBoundary.coordinate_transcendental

theorem canonicalAnchor_exp_transcendental :
    ∀ i, Transcendental ℚ (Complex.exp (canonicalAnchor i)) :=
  FullyTranscendentalPeriodBoundary.exponential_transcendental

@[simp]
theorem basis_sumExtend_apply_inl {K V ι : Type*} [DivisionRing K]
    [AddCommGroup V] [Module K V] {v : ι → V} (hv : LinearIndependent K v) (i : ι) :
    Module.Basis.sumExtend hv (Sum.inl i) = v i := by
  unfold Module.Basis.sumExtend
  rw [Module.Basis.reindex_apply]
  simp only [Equiv.symm_symm, Trans.trans]
  exact Module.Basis.extend_apply_self _ _

/-- Any finite independent family whose span contains the canonical anchor has a finite basis of
the same span with the two anchor vectors in positions `0` and `1`. -/
theorem exists_fin_basis_with_canonicalAnchor {m : ℕ} {t : Fin m → ℂ}
    (hanchor : Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range t)) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
      LinearIndependent ℚ w ∧
      Submodule.span ℚ (Set.range w) = Submodule.span ℚ (Set.range t) ∧
      w 0 = canonicalAnchor 0 ∧ w 1 = canonicalAnchor 1 := by
  let P : Submodule ℚ ℂ := Submodule.span ℚ (Set.range t)
  letI : FiniteDimensional ℚ P :=
    FiniteDimensional.span_of_finite ℚ (Set.finite_range t)
  have ha_mem : ∀ i, canonicalAnchor i ∈ P := fun i ↦
    hanchor (Submodule.subset_span (Set.mem_range_self i))
  let aP : Fin 2 → P := fun i ↦ ⟨canonicalAnchor i, ha_mem i⟩
  have haP : LinearIndependent ℚ aP := by
    apply LinearIndependent.of_comp P.subtype
    simpa [aP, Function.comp_def] using canonicalAnchor_linearIndependent
  let bSum := Module.Basis.sumExtend haP
  letI : Fintype (Fin 2 ⊕ Module.Basis.sumExtendIndex haP) :=
    FiniteDimensional.fintypeBasisIndex bSum
  letI : Finite (Module.Basis.sumExtendIndex haP) :=
    Finite.of_injective
      (fun x : Module.Basis.sumExtendIndex haP ↦ (Sum.inr x :
        Fin 2 ⊕ Module.Basis.sumExtendIndex haP)) Sum.inr_injective
  letI : Fintype (Module.Basis.sumExtendIndex haP) := Fintype.ofFinite _
  let n := Fintype.card (Module.Basis.sumExtendIndex haP)
  let eComplement : Module.Basis.sumExtendIndex haP ≃ Fin n :=
    Fintype.equivFin _
  let eAll : (Fin 2 ⊕ Module.Basis.sumExtendIndex haP) ≃ Fin (n + 2) :=
    (Equiv.sumCongr (Equiv.refl (Fin 2)) eComplement).trans
      (finSumFinEquiv.trans (finCongr (Nat.add_comm 2 n)))
  let bFinal : Module.Basis (Fin (n + 2)) ℚ P :=
    bSum.reindex eAll
  let w : Fin (n + 2) → ℂ := P.subtype ∘ bFinal
  have hezero : eAll (Sum.inl 0) = 0 := by
    apply Fin.ext
    rfl
  have heone : eAll (Sum.inl 1) = 1 := by
    apply Fin.ext
    rfl
  have hindexzero : eAll.symm 0 = Sum.inl 0 := by
    rw [← hezero]
    exact eAll.symm_apply_apply _
  have hindexone : eAll.symm 1 = Sum.inl 1 := by
    rw [← heone]
    exact eAll.symm_apply_apply _
  have hbzero : bFinal 0 = aP 0 := by
    change (bSum.reindex eAll) 0 = aP 0
    rw [Module.Basis.reindex_apply, hindexzero]
    exact basis_sumExtend_apply_inl haP 0
  have hbone : bFinal 1 = aP 1 := by
    change (bSum.reindex eAll) 1 = aP 1
    rw [Module.Basis.reindex_apply, hindexone]
    exact basis_sumExtend_apply_inl haP 1
  refine ⟨n, w, ?_, ?_, ?_, ?_⟩
  · exact bFinal.linearIndependent.map' P.subtype (Submodule.ker_subtype P)
  · change Submodule.span ℚ (Set.range (P.subtype ∘ bFinal)) = P
    rw [Set.range_comp, Submodule.span_image, bFinal.span_eq,
      Submodule.map_subtype_top]
  · simpa [w, aP] using congrArg ((↑) : P → ℂ) hbzero
  · simpa [w, aP] using congrArg ((↑) : P → ℂ) hbone

/-! ## Existence and least arity of an anchored failure -/

/-- The first two entries of a family are literally the canonical anchor. -/
def CanonicallyAnchored {n : ℕ} (w : Fin (n + 2) → ℂ) : Prop :=
  w 0 = canonicalAnchor 0 ∧ w 1 = canonicalAnchor 1

/-- Failure at a fixed number of complementary inputs. -/
def CanonicalAnchoredFailureAt (n : ℕ) : Prop :=
  ∃ w : Fin (n + 2) → ℂ,
    LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧ ¬ Bound w

/-- A defect-one independent family always fails its Schanuel bound. -/
theorem not_bound_of_defectOne {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hdefect : DefectOne z) : ¬ Bound z := by
  intro hb
  have hbad : (((n + 1 : ℕ) : Cardinal)) ≤ (n : Cardinal) := by
    unfold Bound at hb
    have hb' : (((n + 1 : ℕ) : Cardinal)) ≤
        Algebra.trdeg ℚ (generatedField z) := by simpa using hb
    rwa [hdefect] at hb'
  exact (by omega : ¬ n + 1 ≤ n) (by exact_mod_cast hbad)

/-- The canonical anchor lies in any rational span containing both `1` and the standard period. -/
theorem canonicalAnchor_span_le_of_one_period_mem {m : ℕ} {t : Fin m → ℂ}
    (hone : (1 : ℂ) ∈ Submodule.span ℚ (Set.range t))
    (hperiod : standardPeriod ∈ Submodule.span ℚ (Set.range t)) :
    Submodule.span ℚ (Set.range canonicalAnchor) ≤
      Submodule.span ℚ (Set.range t) := by
  apply Submodule.span_le.mpr
  rintro x ⟨i, rfl⟩
  fin_cases i
  · change canonicalAnchor 0 ∈ Submodule.span ℚ (Set.range t)
    rw [canonicalAnchor_zero]
    exact (Submodule.span ℚ (Set.range t)).add_mem hone hperiod
  · change canonicalAnchor 1 ∈ Submodule.span ℚ (Set.range t)
    rw [canonicalAnchor_one]
    exact (Submodule.span ℚ (Set.range t)).add_mem hone
      ((Submodule.span ℚ (Set.range t)).smul_mem (2 : ℚ) hperiod)

/-- `Bound` is invariant under replacing a finite independent family by another basis of the
same rational input span. -/
theorem bound_iff_of_span_eq {m n : ℕ} {w : Fin m → ℂ} {z : Fin n → ℂ}
    (hwlin : LinearIndependent ℚ w) (hzlin : LinearIndependent ℚ z)
    (hspan : Submodule.span ℚ (Set.range w) = Submodule.span ℚ (Set.range z)) :
    Bound w ↔ Bound z := by
  have hmn : m = n := by
    calc
      m = Module.finrank ℚ (Submodule.span ℚ (Set.range w)) := by
        simpa using (finrank_span_eq_card hwlin).symm
      _ = Module.finrank ℚ (Submodule.span ℚ (Set.range z)) := by rw [hspan]
      _ = n := by simpa using finrank_span_eq_card hzlin
  have htd := trdeg_generatedField_eq_of_span_eq w z hspan
  unfold Bound
  rw [htd, hmn]

/-- Prepending `1` to an independent family not already spanning it preserves independence. -/
theorem linearIndependent_prependOne_of_not_mem_span {m : ℕ} {z : Fin m → ℂ}
    (hzlin : LinearIndependent ℚ z)
    (hone : (1 : ℂ) ∉ Submodule.span ℚ (Set.range z)) :
    LinearIndependent ℚ (prependOne z) := by
  exact hzlin.fin_cons hone

/-- Prepending `1` to a defect-one family not already spanning it still gives a failure: the
only new field generator is `exp 1`. -/
theorem not_bound_prependOne_of_defectOne {m : ℕ} {z : Fin (m + 1) → ℂ}
    (hdefect : DefectOne z) : ¬ Bound (prependOne z) := by
  intro hb
  have hlower : (m : Cardinal) + 1 + 1 ≤
      Algebra.trdeg ℚ (generatedField (prependOne z)) := by
    simpa [Bound] using hb
  have hupper : Algebra.trdeg ℚ (generatedField (prependOne z)) ≤
      ((m + 1 : ℕ) : Cardinal) := by
    rw [generatedField_prependOne_eq_expOneAdjoinField]
    calc
      Algebra.trdeg ℚ (expOneAdjoinField z) ≤
          Algebra.trdeg ℚ (generatedField z) + 1 :=
        trdeg_expOneAdjoinField_le_add_one z
      _ = (m : Cardinal) + 1 := by rw [hdefect]
      _ = ((m + 1 : ℕ) : Cardinal) := by norm_cast
  have hupper' : Algebra.trdeg ℚ (generatedField (prependOne z)) ≤
      (m : Cardinal) + 1 := by
    simpa using hupper
  have hbad : (m : Cardinal) + 1 + 1 ≤ (m : Cardinal) + 1 :=
    hlower.trans hupper'
  have hbad' : m + 2 ≤ m + 1 := by exact_mod_cast hbad
  omega

/-- Any failure of Schanuel's conjecture produces an independent failing basis whose first two
entries are the canonical anchor. -/
theorem exists_canonicalAnchored_failure (h : ¬ Conjecture) :
    ∃ n, CanonicalAnchoredFailureAt n := by
  obtain ⟨r, z, hzlin, hzdefect, -, -, hpair⟩ :=
    exists_periodPairedDefectOne_of_not_conjecture h
  let S := Submodule.span ℚ (Set.range z)
  have hperiod : standardPeriod ∈ S := by
    have hz0 : z 0 ∈ S := Submodule.subset_span (Set.mem_range_self 0)
    have hz1 : z 1 ∈ S := Submodule.subset_span (Set.mem_range_self 1)
    rw [← hpair]
    exact S.sub_mem hz1 hz0
  by_cases hone : (1 : ℂ) ∈ S
  · have hanchor := canonicalAnchor_span_le_of_one_period_mem hone hperiod
    obtain ⟨n, w, hwlin, hwspan, hwzero, hwone⟩ :=
      exists_fin_basis_with_canonicalAnchor hanchor
    refine ⟨n, w, hwlin, ⟨hwzero, hwone⟩, ?_⟩
    exact fun hwbound ↦ (not_bound_of_defectOne hzdefect)
      ((bound_iff_of_span_eq hwlin hzlin hwspan).mp hwbound)
  · let t : Fin (r + 3) → ℂ := prependOne z
    have htlin : LinearIndependent ℚ t :=
      linearIndependent_prependOne_of_not_mem_span hzlin hone
    have honeT : (1 : ℂ) ∈ Submodule.span ℚ (Set.range t) := by
      exact Submodule.subset_span ⟨0, by simp [t, prependOne]⟩
    have hzspan : S ≤ Submodule.span ℚ (Set.range t) := by
      apply Submodule.span_mono
      rintro x ⟨i, rfl⟩
      exact ⟨i.succ, by simp [t, prependOne]⟩
    have hperiodT : standardPeriod ∈ Submodule.span ℚ (Set.range t) := hzspan hperiod
    have hanchor := canonicalAnchor_span_le_of_one_period_mem honeT hperiodT
    obtain ⟨n, w, hwlin, hwspan, hwzero, hwone⟩ :=
      exists_fin_basis_with_canonicalAnchor hanchor
    refine ⟨n, w, hwlin, ⟨hwzero, hwone⟩, ?_⟩
    exact fun hwbound ↦ (not_bound_prependOne_of_defectOne hzdefect)
      ((bound_iff_of_span_eq hwlin htlin hwspan).mp hwbound)

/-- Anchored failures have a least number of complementary inputs. -/
theorem exists_first_canonicalAnchored_failure (h : ¬ Conjecture) :
    ∃ n, CanonicalAnchoredFailureAt n ∧
      ∀ k < n, ¬ CanonicalAnchoredFailureAt k := by
  classical
  have hex := exists_canonicalAnchored_failure h
  let n := Nat.find hex
  refine ⟨n, Nat.find_spec hex, ?_⟩
  intro k hk hkfail
  exact (Nat.not_lt_of_ge (Nat.find_min' hex hkfail)) hk

/-- A failing anchored family, minimal among smaller anchored arities, has exact defect one.
For zero complementary inputs the lower bound comes from the transcendental first anchor;
for positive arity it comes from deleting the final complementary input. -/
theorem defectOne_of_no_smaller_canonicalAnchored_failure
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hlin : LinearIndependent ℚ w) (hanchor : CanonicallyAnchored w)
    (hfail : ¬ Bound w)
    (hmin : ∀ k < n, ¬ CanonicalAnchoredFailureAt k) :
    DefectOne w := by
  unfold DefectOne
  apply le_antisymm
  · have hlt : Algebra.trdeg ℚ (generatedField w) <
        (((n + 1) + 1 : ℕ) : Cardinal) := by
      apply lt_of_not_ge
      simpa [Bound, Nat.add_assoc] using hfail
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
          rw [hanchor.1]
          exact canonicalAnchor_coordinate_transcendental 0
        have hsubBound : Bound (w ∘ f) := by
          apply bound_of_algebraicIndependent_coordinate
          rw [algebraicIndependent_unique_type_iff]
          exact hsubTrans
        have hsub := hsubBound
        change Cardinal.mk (Fin 1) ≤
          Algebra.trdeg ℚ (generatedField (w ∘ f)) at hsub
        simpa using hsub.trans (trdeg_comp_le w f)
    | succ k =>
        let f : Fin (k + 2) ↪ Fin (k + 3) := Fin.castSuccEmb
        have hsubLin : LinearIndependent ℚ (w ∘ f) :=
          hlin.comp f f.injective
        have hsubAnchor : CanonicallyAnchored (w ∘ f) := by
          constructor
          · simpa [f] using hanchor.1
          · simpa [f] using hanchor.2
        have hsubBound : Bound (w ∘ f) := by
          by_contra hsubFail
          exact hmin k (Nat.lt_succ_self k)
            ⟨w ∘ f, hsubLin, hsubAnchor, hsubFail⟩
        have hsub := hsubBound
        change Cardinal.mk (Fin (k + 2)) ≤
          Algebra.trdeg ℚ (generatedField (w ∘ f)) at hsub
        simpa [Nat.add_assoc] using hsub.trans (trdeg_comp_le w f)

/-- Every global failure has a least-arity canonically anchored, independent, defect-one
failure.  The statement retains the zero-complement case. -/
theorem exists_canonicalAnchored_defectOne_minimal_failure (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
      LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧ ¬ Bound w ∧
      DefectOne w ∧ ∀ k < n, ¬ CanonicalAnchoredFailureAt k := by
  obtain ⟨n, ⟨w, hlin, hanchor, hfail⟩, hmin⟩ :=
    exists_first_canonicalAnchored_failure h
  exact ⟨n, w, hlin, hanchor, hfail,
    defectOne_of_no_smaller_canonicalAnchored_failure hlin hanchor hfail hmin, hmin⟩

/-! ## Anchor-preserving full-transcendence shear -/

/-- The standard two-stage simultaneous shear can be chosen without moving either canonical
anchor.  First algebraic coordinates are shifted by the first anchor; then algebraic
exponentials are eliminated using the same pivot. -/
theorem exists_fullyTranscendental_canonicalAnchor_shear
    {n : ℕ} {w : Fin (n + 2) → ℂ}
    (hlin : LinearIndependent ℚ w) (hanchor : CanonicallyAnchored w) :
    ∃ v : Fin (n + 2) → ℂ,
      LinearIndependent ℚ v ∧ CanonicallyAnchored v ∧
      generatedField v = generatedField w ∧
      (∀ i, Transcendental ℚ (v i)) ∧
      ∀ i, Transcendental ℚ (Complex.exp (v i)) := by
  have hwzero : Transcendental ℚ (w 0) := by
    rw [hanchor.1]
    exact canonicalAnchor_coordinate_transcendental 0
  have hwone : Transcendental ℚ (w 1) := by
    rw [hanchor.2]
    exact canonicalAnchor_coordinate_transcendental 1
  let u := transcendentalShear w 0
  have hulin : LinearIndependent ℚ u :=
    (linearIndependent_transcendentalShear_iff hwzero).2 hlin
  have hufield : generatedField u = generatedField w :=
    generatedField_transcendentalShear_eq hwzero
  have hucoord : ∀ i, Transcendental ℚ (u i) :=
    transcendental_transcendentalShear hwzero
  have huzero : u 0 = canonicalAnchor 0 := by
    have hwzero' : ¬ IsAlgebraic ℚ (w 0) := hwzero
    calc
      u 0 = w 0 := by
        simp [u, transcendentalShear, algebraicEliminationCoeffs, hwzero']
      _ = canonicalAnchor 0 := hanchor.1
  have huone : u 1 = canonicalAnchor 1 := by
    have hwone' : ¬ IsAlgebraic ℚ (w 1) := hwone
    calc
      u 1 = w 1 := by
        simp [u, transcendentalShear, algebraicEliminationCoeffs, hwone']
      _ = canonicalAnchor 1 := hanchor.2
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
  exact ⟨v, hvlin, ⟨hvzero, hvone⟩, hvfield, hvcoord, hvexp⟩

/-- A fully transcendental defect-one family with the literal canonical anchor. -/
def CanonicallyAnchoredFullyTranscendentalDefectOne {n : ℕ}
    (w : Fin (n + 2) → ℂ) : Prop :=
  LinearIndependent ℚ w ∧ DefectOne w ∧ CanonicallyAnchored w ∧
    (∀ i, Transcendental ℚ (w i)) ∧
    ∀ i, Transcendental ℚ (Complex.exp (w i))

/-- The exact canonical-anchor normal form, including the case with no complementary inputs:
Schanuel fails iff a fully transcendental defect-one witness begins literally with
`1 + 2*pi*I, 1 + 4*pi*I`. -/
theorem not_conjecture_iff_exists_canonicallyAnchoredFullyTranscendentalDefectOne :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
        CanonicallyAnchoredFullyTranscendentalDefectOne w := by
  constructor
  · intro h
    obtain ⟨n, w, hlin, hanchor, -, hdefect, -⟩ :=
      exists_canonicalAnchored_defectOne_minimal_failure h
    obtain ⟨v, hvlin, hvanchor, hvfield, hvcoord, hvexp⟩ :=
      exists_fullyTranscendental_canonicalAnchor_shear hlin hanchor
    exact ⟨n, v, hvlin, (defectOne_congr_generatedField hvfield).2 hdefect,
      hvanchor, hvcoord, hvexp⟩
  · rintro ⟨n, w, hlin, hdefect, -, -, -⟩ hC
    exact (noDefectOneIndependentFamilies_of_conjecture hC (n + 1) w hlin) hdefect

end

end Schanuel
