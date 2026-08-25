import Schanuel

/-!
# The exact shape of a minimal counterexample

If Schanuel's bound is known for `n` inputs, then every linearly independent
`(n + 1)`-tuple already generates a field of transcendence degree at least `n`.
Consequently, a first counterexample can miss the conjectured bound by exactly
one and no more.  We construct a least-arity witness from any global failure,
prove that every one-coordinate deletion has the same transcendence degree and
that the full field is algebraic over it, and package defect one as an exact
equivalent negation of the conjecture.
-/

namespace Schanuel

open Function Set

noncomputable section

/-- The conjecture in arity `n` gives the predecessor lower bound for any
linearly independent family of arity `n + 1`. -/
theorem predecessor_lower_bound
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hz : LinearIndependent ℚ z)
    (hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w) :
    ((n : ℕ) : Cardinal) ≤ Algebra.trdeg ℚ (generatedField z) := by
  let f : Fin n ↪ Fin (n + 1) := Fin.castSuccEmb
  have hsub : LinearIndependent ℚ (z ∘ f) := hz.comp f f.injective
  have hb := hprev (z ∘ f) hsub
  change Cardinal.mk (Fin n) ≤ Algebra.trdeg ℚ (generatedField (z ∘ f)) at hb
  simpa using hb.trans (trdeg_comp_le z f)

/-- A first failure of Schanuel's bound has transcendence degree exactly one
below the size of the family. -/
theorem trdeg_eq_predecessor_of_minimal_failure
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hz : LinearIndependent ℚ z)
    (hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w)
    (hfail : ¬ Bound z) :
    Algebra.trdeg ℚ (generatedField z) = ((n : ℕ) : Cardinal) := by
  apply le_antisymm
  · have hlt : Algebra.trdeg ℚ (generatedField z) < ((n + 1 : ℕ) : Cardinal) := by
      apply lt_of_not_ge
      simpa [Bound] using hfail
    rw [show ((n + 1 : ℕ) : Cardinal) = Order.succ (n : Cardinal) by
      simp [Cardinal.succ_natCast]] at hlt
    exact Order.lt_succ_iff.mp hlt
  · exact predecessor_lower_bound hz hprev

/-- A family of arity `n + 1` has transcendence degree exactly `n`. -/
def DefectOne {n : ℕ} (z : Fin (n + 1) → ℂ) : Prop :=
  Algebra.trdeg ℚ (generatedField z) = ((n : ℕ) : Cardinal)

/-- Defect one is invariant under an equality of generated fields. -/
theorem defectOne_congr_generatedField {n : ℕ}
    {w z : Fin (n + 1) → ℂ} (hfield : generatedField w = generatedField z) :
    DefectOne w ↔ DefectOne z := by
  have htrdeg := (IntermediateField.equivOfEq hfield).trdeg_eq
  constructor
  · exact fun hw ↦ htrdeg.symm.trans hw
  · exact fun hz ↦ htrdeg.trans hz

/-- In a first failure, every restriction obtained by deleting one input has
the same transcendence degree as the full family. -/
theorem restricted_trdeg_eq_predecessor_of_minimal_failure
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hz : LinearIndependent ℚ z)
    (hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w)
    (hfail : ¬ Bound z) (f : Fin n ↪ Fin (n + 1)) :
    Algebra.trdeg ℚ (generatedField (z ∘ f)) = ((n : ℕ) : Cardinal) := by
  apply le_antisymm
  · exact (trdeg_comp_le z f).trans_eq
      (trdeg_eq_predecessor_of_minimal_failure hz hprev hfail)
  · have hsub : LinearIndependent ℚ (z ∘ f) := hz.comp f f.injective
    have hb := hprev (z ∘ f) hsub
    change Cardinal.mk (Fin n) ≤
      Algebra.trdeg ℚ (generatedField (z ∘ f)) at hb
    simpa using hb

/-- Equivalently, in a first failure the full generated field is algebraic
over every restriction obtained by deleting one input. -/
theorem isAlgebraic_over_restriction_of_minimal_failure
    {n : ℕ} {z : Fin (n + 1) → ℂ}
    (hz : LinearIndependent ℚ z)
    (hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w)
    (hfail : ¬ Bound z) (f : Fin n ↪ Fin (n + 1)) :
    letI : Algebra (generatedField (z ∘ f)) (generatedField z) :=
      (generatedFieldInclusion (generators_comp_subset z f)).toAlgebra
    Algebra.IsAlgebraic (generatedField (z ∘ f)) (generatedField z) := by
  let hgen := generators_comp_subset z f
  letI : Algebra (generatedField (z ∘ f)) (generatedField z) :=
    (generatedFieldInclusion hgen).toAlgebra
  haveI : IsScalarTower ℚ (generatedField (z ∘ f)) (generatedField z) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hrest :=
    restricted_trdeg_eq_predecessor_of_minimal_failure hz hprev hfail f
  have hfull := trdeg_eq_predecessor_of_minimal_failure hz hprev hfail
  have hadd := trdeg_add_eq ℚ (generatedField (z ∘ f)) (A := generatedField z)
  rw [hrest, hfull] at hadd
  have hzero : Algebra.trdeg (generatedField (z ∘ f)) (generatedField z) = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hadd with hlarge | hzero
    · have haleph : Cardinal.aleph0 ≤ ((n : ℕ) : Cardinal) :=
        (le_max_left _ _).trans hlarge
      exact False.elim ((not_le_of_gt Cardinal.natCast_lt_aleph0) haleph)
    · exact hzero
  exact trdeg_eq_zero_iff.mp hzero

/-- There is a counterexample in arity `n`. -/
def FailureAt (n : ℕ) : Prop :=
  ∃ z : Fin n → ℂ, LinearIndependent ℚ z ∧ ¬ Bound z

/-- If the conjecture fails, the set of failing arities has a least member. -/
theorem exists_first_failure (h : ¬ Conjecture) :
    ∃ n : ℕ, FailureAt n ∧ ∀ m < n, ¬ FailureAt m := by
  classical
  have hbad : ∃ n, FailureAt n := by
    by_contra hnone
    apply h
    intro n z hz
    by_contra hfail
    exact hnone ⟨n, z, hz, hfail⟩
  let n := Nat.find hbad
  refine ⟨n, Nat.find_spec hbad, ?_⟩
  intro m hm hmfail
  exact (Nat.not_lt_of_ge (Nat.find_min' hbad hmfail)) hm

/-- Every failure of Schanuel's conjecture produces a first-arity witness
whose generated field has exact defect one. -/
theorem exists_defect_one_minimal_failure (h : ¬ Conjecture) :
    ∃ (n : ℕ) (z : Fin (n + 1) → ℂ),
      LinearIndependent ℚ z ∧ ¬ Bound z ∧
      (∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w) ∧
      Algebra.trdeg ℚ (generatedField z) = ((n : ℕ) : Cardinal) := by
  classical
  obtain ⟨N, ⟨z, hz, hfail⟩, hmin⟩ := exists_first_failure h
  have hN : N ≠ 0 := by
    intro hzero
    subst N
    exact hfail (bound_zero z)
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN
  have hprev : ∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w := by
    intro w hw
    by_contra hwfail
    exact hmin n (Nat.lt_succ_self n) ⟨w, hw, hwfail⟩
  exact ⟨n, z, hz, hfail, hprev,
    trdeg_eq_predecessor_of_minimal_failure hz hprev hfail⟩

/-- A compact version of the least-failure theorem using `DefectOne`. -/
theorem exists_defectOne_minimal_failure (h : ¬ Conjecture) :
    ∃ (n : ℕ) (z : Fin (n + 1) → ℂ),
      LinearIndependent ℚ z ∧ ¬ Bound z ∧
      (∀ w : Fin n → ℂ, LinearIndependent ℚ w → Bound w) ∧
      DefectOne z := by
  obtain ⟨n, z, hz, hfail, hprev, htrdeg⟩ :=
    exists_defect_one_minimal_failure h
  exact ⟨n, z, hz, hfail, hprev, htrdeg⟩

/-- There is no linearly independent family whose generated field has
transcendence degree exactly one less than the size of the family. -/
def NoDefectOneIndependentFamilies : Prop :=
  ∀ (n : ℕ) (z : Fin (n + 1) → ℂ), LinearIndependent ℚ z →
    Algebra.trdeg ℚ (generatedField z) ≠ ((n : ℕ) : Cardinal)

/-- Schanuel's conjecture excludes every defect-one independent family. -/
theorem noDefectOneIndependentFamilies_of_conjecture
    (h : Conjecture) : NoDefectOneIndependentFamilies := by
  intro n z hz htrdeg
  have hb := h (n + 1) z hz
  rw [Bound, htrdeg] at hb
  have hcard : Cardinal.mk (Fin (n + 1)) = Order.succ (n : Cardinal) := by
    simp [Cardinal.succ_natCast]
  have hlt : ((n : ℕ) : Cardinal) < Cardinal.mk (Fin (n + 1)) := by
    rw [hcard]
    exact Order.lt_succ _
  exact (not_lt_of_ge hb) hlt

/-- Excluding defect-one independent families implies every arity of
Schanuel's conjecture, by induction through the predecessor lower bound. -/
theorem conjecture_of_noDefectOneIndependentFamilies
    (h : NoDefectOneIndependentFamilies) : Conjecture := by
  intro n
  induction n with
  | zero =>
      intro z hz
      simp [Bound]
  | succ n ih =>
      intro z hz
      by_contra hfail
      exact h n z hz
        (trdeg_eq_predecessor_of_minimal_failure hz ih hfail)

/-- Schanuel's conjecture is exactly the assertion that defect-one independent
families do not exist. -/
theorem conjecture_iff_noDefectOneIndependentFamilies :
    Conjecture ↔ NoDefectOneIndependentFamilies :=
  ⟨noDefectOneIndependentFamilies_of_conjecture,
    conjecture_of_noDefectOneIndependentFamilies⟩

/-- The negation of Schanuel's conjecture has an exact existential normal
form: a rationally independent defect-one family. -/
theorem not_conjecture_iff_exists_defect_one :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (z : Fin (n + 1) → ℂ), LinearIndependent ℚ z ∧
        Algebra.trdeg ℚ (generatedField z) = ((n : ℕ) : Cardinal) := by
  constructor
  · intro h
    obtain ⟨n, z, hz, -, -, htrdeg⟩ := exists_defect_one_minimal_failure h
    exact ⟨n, z, hz, htrdeg⟩
  · rintro ⟨n, z, hz, htrdeg⟩ hC
    exact (noDefectOneIndependentFamilies_of_conjecture hC n z hz) htrdeg

end

end Schanuel
