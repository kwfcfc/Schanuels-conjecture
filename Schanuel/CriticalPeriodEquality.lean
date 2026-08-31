import Schanuel.MinimalCounterexamplePeriodBearing
import Schanuel.FullyTranscendentalPeriodBoundary
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Critical-period equality normal form

Failure of Schanuel's conjecture is equivalent to a sharp equality tuple whose generated
coordinate-exponential field algebraizes the standard period without rationally spanning it.
-/

namespace Schanuel

open Function Set

noncomputable section

/-- A positive fully transcendental equality family which does not rationally span the standard
period, although that period is algebraic over its generated field. -/
def CriticalPeriodEquality {m : ℕ} (v : Fin m → ℂ) : Prop :=
  0 < m ∧
  LinearIndependent ℚ v ∧
  (∀ i, Transcendental ℚ (v i)) ∧
  (∀ i, Transcendental ℚ (Complex.exp (v i))) ∧
  Algebra.trdeg ℚ (generatedField v) = ((m : ℕ) : Cardinal) ∧
  standardPeriod ∉ Submodule.span ℚ (Set.range v) ∧
  IsAlgebraic (generatedField v) standardPeriod

/-- Every rational linear combination of the inputs belongs to their generated field. -/
theorem span_range_subset_generatedField {m : ℕ} (v : Fin m → ℂ) :
    ∀ {x : ℂ}, x ∈ Submodule.span ℚ (Set.range v) → x ∈ generatedField v := by
  intro x hx
  rcases ((Submodule.mem_span_range_iff_exists_fun ℚ).mp hx) with ⟨c, rfl⟩
  apply (generatedField v).sum_mem
  intro i hi
  rw [Rat.smul_def]
  exact (generatedField v).mul_mem
    (IntermediateField.algebraMap_mem _ (c i))
    (IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩))

/-- A nonzero vector misses at least one coordinate hyperplane of a finite independent family. -/
theorem exists_deletion_not_mem_span {n : ℕ} {v : Fin (n + 1) → ℂ}
    (hv : LinearIndependent ℚ v) {x : ℂ} (hx0 : x ≠ 0) :
    ∃ i : Fin (n + 1),
      x ∉ Submodule.span ℚ (Set.range (v ∘ i.succAboveEmb)) := by
  by_cases hx : x ∈ Submodule.span ℚ (Set.range v)
  · let S := Submodule.span ℚ (Set.range v)
    let b : Module.Basis (Fin (n + 1)) ℚ S := Module.Basis.span hv
    let xs : S := ⟨x, hx⟩
    have hxs0 : xs ≠ 0 := by
      intro hzero
      apply hx0
      exact Subtype.ext_iff.mp hzero
    have hrepr0 : b.repr xs ≠ 0 := by
      intro hzero
      exact hxs0 (b.repr.injective (by simpa using hzero))
    have hi : ∃ i, b.repr xs i ≠ 0 := by
      by_contra hall
      apply hrepr0
      ext i
      simp only [Finsupp.zero_apply]
      exact not_not.mp (not_exists.mp hall i)
    obtain ⟨i, hi⟩ := hi
    refine ⟨i, ?_⟩
    intro hdel
    rcases ((Submodule.mem_span_range_iff_exists_fun ℚ).mp hdel) with ⟨c, hc⟩
    have hxsdel : xs ∈ Submodule.span ℚ (b '' Set.range i.succAboveEmb) := by
      rw [← Set.range_comp]
      apply (Submodule.mem_span_range_iff_exists_fun ℚ).mpr
      refine ⟨c, ?_⟩
      apply Subtype.ext
      rw [Submodule.coe_sum]
      simp only [SetLike.val_smul, Function.comp_apply]
      simp_rw [show ∀ k, (b k : ℂ) = v k by
        intro k
        exact Module.Basis.coe_span_apply hv k]
      exact hc
    have hsupp := b.repr_support_subset_of_mem_span (Set.range i.succAboveEmb) hxsdel
    have himem : i ∈ Set.range i.succAboveEmb :=
      hsupp (Finsupp.mem_support_iff.mpr hi)
    rcases himem with ⟨j, hij⟩
    exact i.succAbove_ne j hij
  · refine ⟨0, ?_⟩
    intro hdel
    apply hx
    exact Submodule.span_mono (by
      rintro y ⟨j, rfl⟩
      exact ⟨(0 : Fin (n + 1)).succAbove j, rfl⟩) hdel

/-- Transcendence of an element of a concrete generated field's ambient field follows from
excluding algebraicity over that field. -/
theorem transcendental_of_not_isAlgebraic {F : IntermediateField ℚ ℂ} {x : ℂ}
    (h : ¬ IsAlgebraic F x) : Transcendental F x := h

/-- In the transcendental-period branch, adjoining the shifted replacement to a deletion field
has the exact next absolute transcendence degree. -/
theorem trdeg_replacement_eq_succ
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hD : Algebra.trdeg ℚ (generatedField (z ∘ Fin.castSuccEmb)) =
      ((n : ℕ) : Cardinal))
    (hK : Algebra.trdeg ℚ (generatedField z) = ((n : ℕ) : Cardinal))
    (homega : Transcendental (generatedField z) standardPeriod) :
    let u : Fin n → ℂ := z ∘ Fin.castSuccEmb
    let h := standardPeriod + z (Fin.last n)
    Algebra.trdeg ℚ (generatedField (Fin.snoc u h)) =
      (((n + 1 : ℕ) : Cardinal)) := by
  let u : Fin n → ℂ := z ∘ Fin.castSuccEmb
  let zi := z (Fin.last n)
  let h := standardPeriod + zi
  let v : Fin (n + 1) → ℂ := Fin.snoc u h
  have hzi : IsAlgebraic (generatedField z) zi := by
    have hmem : zi ∈ generatedField z :=
      IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨Fin.last n, rfl⟩)
    have halg := isAlgebraic_algebraMap (R := generatedField z) (A := ℂ)
      (⟨zi, hmem⟩ : generatedField z)
    simpa using halg
  have hhK : Transcendental (generatedField z) h := by
    intro hh
    apply homega
    have hsub := hh.sub hzi
    simpa [h, zi] using hsub
  have hexp : Complex.exp h ∈ generatedField z := by
    have heq : Complex.exp h = Complex.exp zi := by
      simp [h, Complex.exp_add, exp_standardPeriod]
    rw [heq]
    exact IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨Fin.last n, rfl⟩)
  let L : Fin (n + 2) → ℂ := Fin.snoc z h
  have htdL : Algebra.trdeg ℚ (generatedField L) =
      (((n + 1 : ℕ) : Cardinal)) := by
    dsimp [L]
    rw [trdeg_generatedField_snoc_eq_add_one_of_transcendental z h hhK hexp, hK]
    norm_cast
  let f : Fin (n + 1) → Fin (n + 2) :=
    Fin.snoc (fun j : Fin n ↦ j.castSucc.castSucc) (Fin.last (n + 1))
  have hvcomp : L ∘ f = v := by
    funext j
    refine Fin.lastCases ?_ (fun k ↦ ?_) j
    · simp [L, f, v]
    · simp [L, f, v, u]
  have hupper : Algebra.trdeg ℚ (generatedField v) ≤
      (((n + 1 : ℕ) : Cardinal)) := by
    rw [← htdL, ← hvcomp]
    exact trdeg_comp_le L f
  have hgen := generatedField_le_generatedField_snoc u h
  letI : Algebra (generatedField u) (generatedField v) := by
    simpa [v] using (IntermediateField.inclusion hgen).toRingHom.toAlgebra
  haveI : IsScalarTower ℚ (generatedField u) (generatedField v) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext q
    rfl
  haveI : IsScalarTower (generatedField u) (generatedField v) ℂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext q
    rfl
  have huK : generatedField u ≤ generatedField z :=
    generatedField_mono (generators_comp_subset z Fin.castSuccEmb)
  letI : Algebra (generatedField u) (generatedField z) :=
    (IntermediateField.inclusion huK).toRingHom.toAlgebra
  haveI : IsScalarTower (generatedField u) (generatedField z) ℂ := by
    apply IsScalarTower.of_algebraMap_eq'
    ext q
    rfl
  have hhD : Transcendental (generatedField u) h :=
    Transcendental.of_tower_top (generatedField u) hhK
  have hrel0 : Algebra.trdeg (generatedField u) (generatedField v) ≠ 0 := by
    intro hzero
    letI : Algebra.IsAlgebraic (generatedField u) (generatedField v) :=
      trdeg_eq_zero_iff.mp hzero
    have hcoordAlg : IsAlgebraic (generatedField u) (snocCoordinate u h) :=
      Algebra.IsAlgebraic.isAlgebraic _
    apply hhD
    rw [← isAlgebraic_algHom_iff
      (IsScalarTower.toAlgHom (generatedField u) (generatedField v) ℂ)
      Subtype.val_injective] at hcoordAlg
    simpa [v] using hcoordAlg
  have hrel : 1 ≤ Algebra.trdeg (generatedField u) (generatedField v) :=
    Cardinal.one_le_iff_ne_zero.mpr hrel0
  have hadd := trdeg_add_eq ℚ (generatedField u) (A := generatedField v)
  have hlower : Algebra.trdeg ℚ (generatedField u) + 1 ≤
      Algebra.trdeg ℚ (generatedField v) := by
    calc
      Algebra.trdeg ℚ (generatedField u) + 1 =
          1 + Algebra.trdeg ℚ (generatedField u) := add_comm _ _
      _ ≤ Algebra.trdeg (generatedField u) (generatedField v) +
          Algebra.trdeg ℚ (generatedField u) :=
        add_le_add_left hrel _
      _ = Algebra.trdeg ℚ (generatedField u) +
          Algebra.trdeg (generatedField u) (generatedField v) := add_comm _ _
      _ = Algebra.trdeg ℚ (generatedField v) := hadd
  have hDu : Algebra.trdeg ℚ (generatedField u) = ((n : ℕ) : Cardinal) := by
    simpa [u] using hD
  apply le_antisymm hupper
  simpa [v, hDu] using hlower

/-- Failure of Schanuel's conjecture is exactly the existence of a critical-period equality
family. -/
theorem not_conjecture_iff_exists_criticalPeriodEquality :
    ¬ Conjecture ↔ ∃ (m : ℕ) (v : Fin m → ℂ), CriticalPeriodEquality v := by
  constructor
  · intro hnot
    obtain ⟨n, z, hn, hlin, hfail, hdefect, hcoord, hexp, hmin⟩ :=
      exists_positive_fullyTranscendental_defectOne_minimal_failure hnot
    have hprev : ¬ FullyTranscendentalFailureAt n :=
      hmin n (Nat.lt_succ_self n)
    have hperiod0 : standardPeriod ≠ 0 := by
      exact FullyTranscendentalPeriodBoundary.period_ne_zero
    by_cases homega : IsAlgebraic (generatedField z) standardPeriod
    · obtain ⟨i, hperiod⟩ := exists_deletion_not_mem_span hlin hperiod0
      let f : Fin n ↪ Fin (n + 1) := i.succAboveEmb
      let v : Fin n → ℂ := z ∘ f
      have hvlin : LinearIndependent ℚ v := hlin.comp f f.injective
      have hvcoord : ∀ j, Transcendental ℚ (v j) := fun j ↦ hcoord (f j)
      have hvexp : ∀ j, Transcendental ℚ (Complex.exp (v j)) := fun j ↦ hexp (f j)
      have htdv : Algebra.trdeg ℚ (generatedField v) = ((n : ℕ) : Cardinal) := by
        simpa [v] using
          restricted_trdeg_eq_of_no_fullyTranscendental_predecessor_failure
            hlin hcoord hexp hfail hprev f
      let hgen := generators_comp_subset z f
      letI : Algebra (generatedField v) (generatedField z) :=
        (generatedFieldInclusion hgen).toAlgebra
      haveI : IsScalarTower ℚ (generatedField v) (generatedField z) := by
        apply IsScalarTower.of_algebraMap_eq'
        ext q
        rfl
      letI : Algebra.IsAlgebraic (generatedField v) (generatedField z) := by
        simpa [v, f] using
          (isAlgebraic_over_restriction_of_no_fullyTranscendental_predecessor_failure
            hlin hcoord hexp hfail hprev f)
      haveI : IsScalarTower (generatedField v) (generatedField z) ℂ := by
        apply IsScalarTower.of_algebraMap_eq'
        ext q
        rfl
      have homegaV : IsAlgebraic (generatedField v) standardPeriod :=
        homega.restrictScalars (generatedField v)
      exact ⟨n, v, hn, hvlin, hvcoord, hvexp, htdv, by simpa [v, f] using hperiod,
        homegaV⟩
    · have homegaTrans : Transcendental (generatedField z) standardPeriod := homega
      let u : Fin n → ℂ := z ∘ Fin.castSuccEmb
      let zi : ℂ := z (Fin.last n)
      let shift : ℂ := standardPeriod + zi
      let v : Fin (n + 1) → ℂ := Fin.snoc u shift
      have htdU : Algebra.trdeg ℚ (generatedField u) = ((n : ℕ) : Cardinal) := by
        simpa [u] using
          restricted_trdeg_eq_of_no_fullyTranscendental_predecessor_failure
            hlin hcoord hexp hfail hprev Fin.castSuccEmb
      have htdK : Algebra.trdeg ℚ (generatedField z) = ((n : ℕ) : Cardinal) := by
        simpa [DefectOne] using hdefect
      have hziK : IsAlgebraic (generatedField z) zi := by
        have hmem : zi ∈ generatedField z :=
          IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨Fin.last n, rfl⟩)
        have halg := isAlgebraic_algebraMap (R := generatedField z) (A := ℂ)
          (⟨zi, hmem⟩ : generatedField z)
        simpa using halg
      have hshiftK : Transcendental (generatedField z) shift := by
        intro hshift
        apply homegaTrans
        have hsub := hshift.sub hziK
        simpa [shift, zi] using hsub
      have hshiftQ : Transcendental ℚ shift :=
        Transcendental.of_tower_top ℚ hshiftK
      have hshiftExp : Transcendental ℚ (Complex.exp shift) := by
        have heq : Complex.exp shift = Complex.exp zi := by
          simp [shift, Complex.exp_add, exp_standardPeriod]
        rw [heq]
        exact hexp (Fin.last n)
      have hzsnoc : Fin.snoc u zi = z := by
        funext j
        refine Fin.lastCases ?_ (fun k ↦ ?_) j
        · simp [u, zi]
        · simp [u, zi]
      have hperiodZ : standardPeriod ∉ Submodule.span ℚ (Set.range z) := by
        intro hspan
        apply homegaTrans
        have hmem : standardPeriod ∈ generatedField z :=
          span_range_subset_generatedField z hspan
        have halg := isAlgebraic_algebraMap (R := generatedField z) (A := ℂ)
          (⟨standardPeriod, hmem⟩ : generatedField z)
        simpa using halg
      have hbaseLin : LinearIndependent ℚ (Fin.snoc u zi) := by
        rw [hzsnoc]
        exact hlin
      let a : Fin (n + 2) → ℂ := Fin.snoc (Fin.snoc u zi) standardPeriod
      have haLin : LinearIndependent ℚ a := by
        dsimp [a]
        rw [linearIndependent_fin_snoc]
        refine ⟨hbaseLin, ?_⟩
        simpa [hzsnoc] using hperiodZ
      let target : Fin (n + 2) := (Fin.last n).castSucc
      let pivot : Fin (n + 2) := Fin.last (n + 1)
      have htarget : target ≠ pivot := by
        exact Fin.castSucc_ne_last (Fin.last n)
      let t : Fin (n + 2) → ℂ := integerShear a target pivot 1
      have htLin : LinearIndependent ℚ t := by
        exact (linearIndependent_integerShear_iff a target pivot 1 htarget).2 haLin
      have ht : t = Fin.snoc v standardPeriod := by
        funext j
        refine Fin.lastCases ?_ (fun q ↦ ?_) j
        · rw [Fin.snoc_last]
          change integerShear a target pivot 1 pivot = standardPeriod
          rw [integerShear_apply_of_ne a target pivot pivot 1 htarget.symm]
          simp [a, pivot]
        · refine Fin.lastCases ?_ (fun k ↦ ?_) q
          · simp [t, target, pivot, a, v, shift, zi]
            ring
          · have hne : k.castSucc.castSucc ≠ target := by
              intro heq
              have := congrArg Fin.val heq
              simp only [Fin.val_castSucc, Fin.val_last, target] at this
              exact (Nat.ne_of_lt k.isLt) this
            simp [t, target, pivot, a, v, u, hne]
      have hvperiod : LinearIndependent ℚ v ∧
          standardPeriod ∉ Submodule.span ℚ (Set.range v) := by
        rw [ht, linearIndependent_fin_snoc] at htLin
        exact htLin
      have hvcoord : ∀ j, Transcendental ℚ (v j) := by
        apply transcendental_snoc
        · intro j
          exact hcoord j.castSucc
        · exact hshiftQ
      have hvexp : ∀ j, Transcendental ℚ (Complex.exp (v j)) := by
        apply transcendental_exp_snoc
        · intro j
          exact hexp j.castSucc
        · exact hshiftExp
      have htdV : Algebra.trdeg ℚ (generatedField v) =
          (((n + 1 : ℕ) : Cardinal)) := by
        simpa [u, zi, shift, v] using
          (trdeg_replacement_eq_succ htdU htdK homegaTrans)
      let hgen := generators_comp_subset z Fin.castSuccEmb
      letI : Algebra (generatedField u) (generatedField z) :=
        (generatedFieldInclusion hgen).toAlgebra
      haveI : IsScalarTower ℚ (generatedField u) (generatedField z) := by
        apply IsScalarTower.of_algebraMap_eq'
        ext q
        rfl
      letI : Algebra.IsAlgebraic (generatedField u) (generatedField z) := by
        simpa [u] using
          (isAlgebraic_over_restriction_of_no_fullyTranscendental_predecessor_failure
            hlin hcoord hexp hfail hprev Fin.castSuccEmb)
      haveI : IsScalarTower (generatedField u) (generatedField z) ℂ := by
        apply IsScalarTower.of_algebraMap_eq'
        ext q
        rfl
      have hziU : IsAlgebraic (generatedField u) zi := by
        have hziSub : IsAlgebraic (generatedField u)
            (⟨zi, IntermediateField.subset_adjoin ℚ _
              (Or.inl ⟨Fin.last n, rfl⟩)⟩ : generatedField z) :=
          Algebra.IsAlgebraic.isAlgebraic _
        rw [← isAlgebraic_algHom_iff
          (IsScalarTower.toAlgHom (generatedField u) (generatedField z) ℂ)
          Subtype.val_injective] at hziSub
        simpa [zi] using hziSub
      have hgenUV := generatedField_le_generatedField_snoc u shift
      letI : Algebra (generatedField u) (generatedField v) := by
        simpa [v] using (IntermediateField.inclusion hgenUV).toRingHom.toAlgebra
      haveI : IsScalarTower (generatedField u) (generatedField v) ℂ := by
        apply IsScalarTower.of_algebraMap_eq'
        ext q
        rfl
      have hziV : IsAlgebraic (generatedField v) zi :=
        hziU.tower_top (generatedField v)
      have hshiftV : IsAlgebraic (generatedField v) shift := by
        have hmem : shift ∈ generatedField v :=
          IntermediateField.subset_adjoin ℚ _
            (Or.inl ⟨Fin.last n, by simp [v]⟩)
        have halg := isAlgebraic_algebraMap (R := generatedField v) (A := ℂ)
          (⟨shift, hmem⟩ : generatedField v)
        simpa using halg
      have homegaV : IsAlgebraic (generatedField v) standardPeriod := by
        have hsub := hshiftV.sub hziV
        simpa [shift, zi] using hsub
      exact ⟨n + 1, v, Nat.zero_lt_succ n, hvperiod.1, hvcoord, hvexp, htdV,
        hvperiod.2, homegaV⟩
  · rintro ⟨m, v, -, hlin, -, -, htd, hperiod, homega⟩
    apply not_conjecture_iff_exists_defect_one.mpr
    let w : Fin (m + 1) → ℂ := Fin.snoc v standardPeriod
    have hwlin : LinearIndependent ℚ w := by
      dsimp [w]
      rw [linearIndependent_fin_snoc]
      exact ⟨hlin, hperiod⟩
    have hexp : Complex.exp standardPeriod ∈ generatedField v := by
      rw [exp_standardPeriod]
      exact (generatedField v).one_mem
    have htdw : Algebra.trdeg ℚ (generatedField w) = ((m : ℕ) : Cardinal) := by
      dsimp [w]
      rw [trdeg_generatedField_snoc_eq_of_isAlgebraic v standardPeriod homega hexp]
      exact htd
    exact ⟨m, w, hwlin, htdw⟩

end

end Schanuel
