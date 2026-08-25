import Schanuel.FullyTranscendentalAugmentation
import Schanuel.MinimalCounterexample

/-!
# Fully transcendental defect-one minimal counterexamples

The equivalence with the fully transcendental restriction permits the least-failure argument to
be carried out entirely inside that restriction.  For the predecessor lower bound we delete one
coordinate of the selected tuple.  Linear independence and the two pointwise transcendence
conditions persist under this deletion, so minimality supplies the required bound for this one
restricted tuple; no conjecture for arbitrary predecessor tuples is assumed.
-/

namespace Schanuel

open Function

noncomputable section

/-- A counterexample of arity `n` lying entirely in the fully transcendental restriction. -/
def FullyTranscendentalFailureAt (n : ℕ) : Prop :=
  ∃ z : Fin n → ℂ,
    LinearIndependent ℚ z ∧
    (∀ i, Transcendental ℚ (z i)) ∧
    (∀ i, Transcendental ℚ (Complex.exp (z i))) ∧
    ¬ Bound z

/-- Failure of the full conjecture supplies a failure in the fully transcendental restriction. -/
theorem exists_fullyTranscendental_failure (h : ¬ Conjecture) :
    ∃ n, FullyTranscendentalFailureAt n := by
  have hnot : ¬ FullyTranscendentalConjecture := by
    intro hfull
    exact h (conjecture_iff_fullyTranscendental.mpr hfull)
  by_contra hnone
  apply hnot
  intro n z hlin hcoord hexp
  by_contra hfail
  exact hnone ⟨n, z, hlin, hcoord, hexp, hfail⟩

/-- The fully transcendental failures have a least arity. -/
theorem exists_first_fullyTranscendental_failure (h : ¬ Conjecture) :
    ∃ N : ℕ, FullyTranscendentalFailureAt N ∧
      ∀ m < N, ¬ FullyTranscendentalFailureAt m := by
  classical
  have hbad : ∃ n, FullyTranscendentalFailureAt n :=
    exists_fullyTranscendental_failure h
  let N := Nat.find hbad
  refine ⟨N, Nat.find_spec hbad, ?_⟩
  intro m hm hmfail
  exact (Nat.not_lt_of_ge (Nat.find_min' hbad hmfail)) hm

/-- A fully transcendental singleton cannot fail: its coordinate alone already supplies the
required transcendence degree. -/
theorem not_fullyTranscendentalFailureAt_one :
    ¬ FullyTranscendentalFailureAt 1 := by
  rintro ⟨w, -, hcoord, -, hfail⟩
  apply hfail
  apply bound_of_algebraicIndependent_coordinate
  rw [algebraicIndependent_unique_type_iff]
  simpa using hcoord (0 : Fin 1)

/-- A fully transcendental failure whose predecessor arity has no fully transcendental failure
has exact defect one.  The lower bound uses only the deletion `w ∘ Fin.castSuccEmb`. -/
theorem defectOne_of_no_fullyTranscendental_predecessor_failure
    {n : ℕ} {w : Fin (n + 1) → ℂ}
    (hlin : LinearIndependent ℚ w)
    (hcoord : ∀ i, Transcendental ℚ (w i))
    (hexp : ∀ i, Transcendental ℚ (Complex.exp (w i)))
    (hfail : ¬ Bound w)
    (hprev : ¬ FullyTranscendentalFailureAt n) :
    DefectOne w := by
  let f : Fin n ↪ Fin (n + 1) := Fin.castSuccEmb
  have hsubLin : LinearIndependent ℚ (w ∘ f) := hlin.comp f f.injective
  have hsubCoord : ∀ i, Transcendental ℚ ((w ∘ f) i) := fun i ↦ hcoord (f i)
  have hsubExp : ∀ i, Transcendental ℚ (Complex.exp ((w ∘ f) i)) :=
    fun i ↦ hexp (f i)
  have hsubBound : Bound (w ∘ f) := by
    by_contra hsubFail
    exact hprev ⟨w ∘ f, hsubLin, hsubCoord, hsubExp, hsubFail⟩
  have hlower : ((n : ℕ) : Cardinal) ≤ Algebra.trdeg ℚ (generatedField w) := by
    have hsub := hsubBound
    change Cardinal.mk (Fin n) ≤ Algebra.trdeg ℚ (generatedField (w ∘ f)) at hsub
    simpa using hsub.trans (trdeg_comp_le w f)
  unfold DefectOne
  apply le_antisymm
  · have hlt : Algebra.trdeg ℚ (generatedField w) < ((n + 1 : ℕ) : Cardinal) := by
      apply lt_of_not_ge
      simpa [Bound] using hfail
    rw [show ((n + 1 : ℕ) : Cardinal) = Order.succ (n : Cardinal) by
      simp [Cardinal.succ_natCast]] at hlt
    exact Order.lt_succ_iff.mp hlt
  · exact hlower

/-- Every one-coordinate deletion of a fully transcendental predecessor-minimal failure has the
same transcendence degree as the full family. -/
theorem restricted_trdeg_eq_of_no_fullyTranscendental_predecessor_failure
    {n : ℕ} {w : Fin (n + 1) → ℂ}
    (hlin : LinearIndependent ℚ w)
    (hcoord : ∀ i, Transcendental ℚ (w i))
    (hexp : ∀ i, Transcendental ℚ (Complex.exp (w i)))
    (hfail : ¬ Bound w)
    (hprev : ¬ FullyTranscendentalFailureAt n)
    (f : Fin n ↪ Fin (n + 1)) :
    Algebra.trdeg ℚ (generatedField (w ∘ f)) = ((n : ℕ) : Cardinal) := by
  have hfull : Algebra.trdeg ℚ (generatedField w) = ((n : ℕ) : Cardinal) := by
    simpa [DefectOne] using
      defectOne_of_no_fullyTranscendental_predecessor_failure
        hlin hcoord hexp hfail hprev
  apply le_antisymm
  · exact (trdeg_comp_le w f).trans_eq hfull
  · have hsubLin : LinearIndependent ℚ (w ∘ f) := hlin.comp f f.injective
    have hsubCoord : ∀ i, Transcendental ℚ ((w ∘ f) i) := fun i ↦ hcoord (f i)
    have hsubExp : ∀ i, Transcendental ℚ (Complex.exp ((w ∘ f) i)) :=
      fun i ↦ hexp (f i)
    have hsubBound : Bound (w ∘ f) := by
      by_contra hsubFail
      exact hprev ⟨w ∘ f, hsubLin, hsubCoord, hsubExp, hsubFail⟩
    change Cardinal.mk (Fin n) ≤
      Algebra.trdeg ℚ (generatedField (w ∘ f)) at hsubBound
    simpa using hsubBound

/-- The full generated field of a fully transcendental predecessor-minimal failure is algebraic
over the field generated by any one-coordinate deletion. -/
theorem isAlgebraic_over_restriction_of_no_fullyTranscendental_predecessor_failure
    {n : ℕ} {w : Fin (n + 1) → ℂ}
    (hlin : LinearIndependent ℚ w)
    (hcoord : ∀ i, Transcendental ℚ (w i))
    (hexp : ∀ i, Transcendental ℚ (Complex.exp (w i)))
    (hfail : ¬ Bound w)
    (hprev : ¬ FullyTranscendentalFailureAt n)
    (f : Fin n ↪ Fin (n + 1)) :
    letI : Algebra (generatedField (w ∘ f)) (generatedField w) :=
      (generatedFieldInclusion (generators_comp_subset w f)).toAlgebra
    Algebra.IsAlgebraic (generatedField (w ∘ f)) (generatedField w) := by
  let hgen := generators_comp_subset w f
  letI : Algebra (generatedField (w ∘ f)) (generatedField w) :=
    (generatedFieldInclusion hgen).toAlgebra
  haveI : IsScalarTower ℚ (generatedField (w ∘ f)) (generatedField w) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hrest :=
    restricted_trdeg_eq_of_no_fullyTranscendental_predecessor_failure
      hlin hcoord hexp hfail hprev f
  have hfull : Algebra.trdeg ℚ (generatedField w) = ((n : ℕ) : Cardinal) := by
    simpa [DefectOne] using
      defectOne_of_no_fullyTranscendental_predecessor_failure
        hlin hcoord hexp hfail hprev
  have hadd := trdeg_add_eq ℚ (generatedField (w ∘ f)) (A := generatedField w)
  rw [hrest, hfull] at hadd
  have hzero : Algebra.trdeg (generatedField (w ∘ f)) (generatedField w) = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hadd with hlarge | hzero
    · have haleph : Cardinal.aleph0 ≤ ((n : ℕ) : Cardinal) :=
        (le_max_left _ _).trans hlarge
      exact False.elim ((not_le_of_gt Cardinal.natCast_lt_aleph0) haleph)
    · exact hzero
  exact trdeg_eq_zero_iff.mp hzero

/-- Any failure has a least positive-arity, fully transcendental witness with exact defect one.
The final clause records minimality only inside the fully transcendental restriction. -/
theorem exists_fullyTranscendental_defectOne_minimal_failure (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
      LinearIndependent ℚ w ∧
      ¬ Bound w ∧
      DefectOne w ∧
      (∀ i, Transcendental ℚ (w i)) ∧
      (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
      ∀ m < n + 1, ¬ FullyTranscendentalFailureAt m := by
  classical
  obtain ⟨N, ⟨w, hlin, hcoord, hexp, hfail⟩, hmin⟩ :=
    exists_first_fullyTranscendental_failure h
  have hN : N ≠ 0 := by
    intro hzero
    subst N
    exact hfail (bound_zero w)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hprev : ¬ FullyTranscendentalFailureAt n :=
    hmin n (Nat.lt_succ_self n)
  exact ⟨n, w, hlin, hfail,
    defectOne_of_no_fullyTranscendental_predecessor_failure
      hlin hcoord hexp hfail hprev,
    hcoord, hexp, hmin⟩

/-- The strongest least-failure package may be chosen with predecessor index `n > 0`; equivalently,
the least fully transcendental failure has arity at least two. -/
theorem exists_positive_fullyTranscendental_defectOne_minimal_failure
    (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
      0 < n ∧
      LinearIndependent ℚ w ∧
      ¬ Bound w ∧
      DefectOne w ∧
      (∀ i, Transcendental ℚ (w i)) ∧
      (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
      ∀ m < n + 1, ¬ FullyTranscendentalFailureAt m := by
  obtain ⟨n, w, hlin, hfail, hdefect, hcoord, hexp, hmin⟩ :=
    exists_fullyTranscendental_defectOne_minimal_failure h
  have hn : 0 < n := by
    apply Nat.pos_of_ne_zero
    intro hnzero
    apply not_fullyTranscendentalFailureAt_one
    have hself : FullyTranscendentalFailureAt (n + 1) :=
      ⟨w, hlin, hcoord, hexp, hfail⟩
    have harity : n + 1 = 1 := by simp [hnzero]
    exact harity ▸ hself
  exact ⟨n, w, hn, hlin, hfail, hdefect, hcoord, hexp, hmin⟩

/-- Failure of Schanuel's conjecture is exactly the existence of a rationally independent,
fully transcendental defect-one family. -/
theorem not_conjecture_iff_exists_fullyTranscendental_defect_one :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
        LinearIndependent ℚ w ∧
        DefectOne w ∧
        (∀ i, Transcendental ℚ (w i)) ∧
        ∀ i, Transcendental ℚ (Complex.exp (w i)) := by
  constructor
  · intro h
    obtain ⟨n, w, hlin, -, hdefect, hcoord, hexp, -⟩ :=
      exists_fullyTranscendental_defectOne_minimal_failure h
    exact ⟨n, w, hlin, hdefect, hcoord, hexp⟩
  · rintro ⟨n, w, hlin, hdefect, -, -⟩ hC
    exact (noDefectOneIndependentFamilies_of_conjecture hC n w hlin) hdefect

/-- The positive-index form of the fully transcendental defect-one equivalence. -/
theorem not_conjecture_iff_exists_positive_fullyTranscendental_defect_one :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
        0 < n ∧
        LinearIndependent ℚ w ∧
        DefectOne w ∧
        (∀ i, Transcendental ℚ (w i)) ∧
        ∀ i, Transcendental ℚ (Complex.exp (w i)) := by
  constructor
  · intro h
    obtain ⟨n, w, hn, hlin, -, hdefect, hcoord, hexp, -⟩ :=
      exists_positive_fullyTranscendental_defectOne_minimal_failure h
    exact ⟨n, w, hn, hlin, hdefect, hcoord, hexp⟩
  · rintro ⟨n, w, -, hlin, hdefect, -, -⟩ hC
    exact (noDefectOneIndependentFamilies_of_conjecture hC n w hlin) hdefect

/-- Failure is equivalently witnessed by the entire positive, least fully transcendental
defect-one package. -/
theorem not_conjecture_iff_exists_positive_fullyTranscendental_defectOne_minimal_failure :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
        0 < n ∧
        LinearIndependent ℚ w ∧
        ¬ Bound w ∧
        DefectOne w ∧
        (∀ i, Transcendental ℚ (w i)) ∧
        (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
        ∀ m < n + 1, ¬ FullyTranscendentalFailureAt m := by
  constructor
  · exact exists_positive_fullyTranscendental_defectOne_minimal_failure
  · rintro ⟨n, w, -, hlin, hfail, -, -, -, -⟩ hC
    exact hfail (hC (n + 1) w hlin)

end

end Schanuel
