import Schanuel.ConjugationStableMinimalFailure

/-!
# Terminal algebraicity for least conjugation-stable failures

A positive least stable anchored failure has an invariant codimension-one deletion.  Rational
denominators in a basis of that hyperplane are cleared once, so the scaled deletion field is a
literal subfield of the full coordinate-exponential field.  Minimality makes the deletion sharp;
equality of the two finite transcendence degrees then makes the full field algebraic over it.
-/

namespace Schanuel

open Function Set

noncomputable section

namespace ConjugationStableTerminal

open ConjugationStableNormalForm ConjugationStableMinimalFailure

/-- Inclusion of a scaled stable-deletion field into the full generated field. -/
def stableDeletionInclusion {r n : ℕ} {d : ℤ}
    {u : Fin r → ℂ} {w : Fin n → ℂ}
    (h : generatedField (ratScaleFamily (d : ℚ) u) ≤ generatedField w) :
    generatedField (ratScaleFamily (d : ℚ) u) →ₐ[ℚ] generatedField w :=
  (IntermediateField.inclusion h).toRingHom.toRatAlgHom

/-- A selected full-field input. -/
def selectedInputInFull {n : ℕ} (w : Fin n → ℂ) (i : Fin n) : generatedField w :=
  ⟨w i, IntermediateField.subset_adjoin ℚ _ (Or.inl ⟨i, rfl⟩)⟩

/-- The exponential paired with a selected full-field input. -/
def selectedExpInFull {n : ℕ} (w : Fin n → ℂ) (i : Fin n) : generatedField w :=
  ⟨Complex.exp (w i), IntermediateField.subset_adjoin ℚ _ (Or.inr ⟨i, rfl⟩)⟩

/-- Equal finite absolute transcendence degree along an intermediate-field inclusion forces
the larger field to be algebraic over the smaller one. -/
theorem isAlgebraic_of_le_of_trdeg_eq_of_lt_aleph0
    {K L : IntermediateField ℚ ℂ} (hKL : K ≤ L)
    (heq : Algebra.trdeg ℚ K = Algebra.trdeg ℚ L)
    (hfinite : Algebra.trdeg ℚ K < Cardinal.aleph0) :
    letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toRatAlgHom.toAlgebra
    Algebra.IsAlgebraic K L := by
  letI : Algebra K L := (IntermediateField.inclusion hKL).toRingHom.toRatAlgHom.toAlgebra
  haveI : IsScalarTower ℚ K L := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ K (A := L)
  rw [← heq] at hadd
  have hzero : Algebra.trdeg K L = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hadd with hlarge | hzero
    · have haleph : Cardinal.aleph0 ≤ Algebra.trdeg ℚ K :=
        (le_max_left _ _).trans hlarge
      exact False.elim ((not_le_of_gt hfinite) haleph)
    · exact hzero
  exact trdeg_eq_zero_iff.mp hzero

/-- Data carried by the invariant codimension-one deletion of a positive least stable failure.
The unscaled family records the literal canonical anchor and stability; the common integral
scale records the honest subfield inclusion needed for tower algebraicity. -/
structure StableTerminalDeletionData {n : ℕ} (w : Fin (n + 2) → ℂ) where
  complementCount : ℕ
  deletion : Fin (complementCount + 2) → ℂ
  scale : ℤ
  omitted : Fin (n + 2)
  deletionLinearIndependent : LinearIndependent ℚ deletion
  deletionAnchored : CanonicallyAnchored deletion
  deletionStable : ConjugationStable deletion
  deletionSpanLt : Submodule.span ℚ (Set.range deletion) <
    Submodule.span ℚ (Set.range w)
  complementCount_succ : complementCount + 1 = n
  scale_pos : 0 < scale
  fieldLe : generatedField (ratScaleFamily (scale : ℚ) deletion) ≤ generatedField w
  deletionSharp : Algebra.trdeg ℚ (generatedField deletion) =
    (((complementCount + 2 : ℕ) : Cardinal))
  scaledDeletion_sameTrdeg :
    Algebra.trdeg ℚ (generatedField (ratScaleFamily (scale : ℚ) deletion)) =
      Algebra.trdeg ℚ (generatedField w)
  fullAlgebraic :
    letI : Algebra (generatedField (ratScaleFamily (scale : ℚ) deletion))
        (generatedField w) := (stableDeletionInclusion fieldLe).toAlgebra
    Algebra.IsAlgebraic (generatedField (ratScaleFamily (scale : ℚ) deletion))
      (generatedField w)
  omittedOutside : w omitted ∉ Submodule.span ℚ (Set.range deletion)

/-- Denominator clearing preserves the sharp equality of the invariant-hyperplane deletion. -/
theorem scaledDeletionSharp {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : StableTerminalDeletionData w) :
    Algebra.trdeg ℚ (generatedField (ratScaleFamily (D.scale : ℚ) D.deletion)) =
      (((D.complementCount + 2 : ℕ) : Cardinal)) := by
  have hdQ : (0 : ℚ) < D.scale := by exact_mod_cast D.scale_pos
  rw [trdeg_ratScaleFamily_eq (D.scale : ℚ) hdQ D.deletion]
  exact D.deletionSharp

/-- Terminal algebraicity explicitly applies to the selected omitted input and its exponential. -/
theorem omitted_pair_isAlgebraic {n : ℕ} {w : Fin (n + 2) → ℂ}
    (D : StableTerminalDeletionData w) :
    letI : Algebra (generatedField (ratScaleFamily (D.scale : ℚ) D.deletion))
        (generatedField w) := (stableDeletionInclusion D.fieldLe).toAlgebra
    IsAlgebraic (generatedField (ratScaleFamily (D.scale : ℚ) D.deletion))
        (selectedInputInFull w D.omitted) ∧
      IsAlgebraic (generatedField (ratScaleFamily (D.scale : ℚ) D.deletion))
        (selectedExpInFull w D.omitted) := by
  letI : Algebra (generatedField (ratScaleFamily (D.scale : ℚ) D.deletion))
      (generatedField w) := (stableDeletionInclusion D.fieldLe).toAlgebra
  letI : Algebra.IsAlgebraic
      (generatedField (ratScaleFamily (D.scale : ℚ) D.deletion))
      (generatedField w) := D.fullAlgebraic
  exact ⟨Algebra.IsAlgebraic.isAlgebraic _, Algebra.IsAlgebraic.isAlgebraic _⟩

/-- A positive least stable anchored failure has sharp invariant-hyperplane deletion data. -/
theorem exists_stableTerminalDeletionData_of_least_failure {n : ℕ}
    {w : Fin (n + 2) → ℂ}
    (hwlin : LinearIndependent ℚ w) (hwanchor : CanonicallyAnchored w)
    (hwstable : ConjugationStable w) (hwfail : ¬ Bound w)
    (hmin : ∀ k < n, ¬ ConjugationStableCanonicalAnchoredFailureAt k)
    (hn : 0 < n) : Nonempty (StableTerminalDeletionData w) := by
  have hwdefect :=
    defectOne_of_no_smaller_conjugationStableCanonicalAnchored_failure
      hwlin hwanchor hwstable hwfail hmin
  obtain ⟨k, u, hulin, huanchor, hustable, huspanlt, hklt, hkOne⟩ :=
    exists_canonicalAnchored_conjugationStable_codimOne_basis
      hwlin hwanchor hwstable hn
  have huBound : Bound u := by
    by_contra huFail
    exact hmin k hklt ⟨u, hulin, huanchor, hustable, huFail⟩
  have huSharp : Algebra.trdeg ℚ (generatedField u) =
      (((k + 2 : ℕ) : Cardinal)) := by
    apply le_antisymm
    · have hmono := trdeg_generatedField_le_of_span_le u w huspanlt.le
      rw [hwdefect] at hmono
      have hnat : k + 2 = n + 1 := by omega
      simpa [hnat] using hmono
    · simpa [Bound] using huBound
  obtain ⟨d, hd, hfield⟩ :=
    exists_pos_integer_scale_generatedField_le_of_span_le u w huspanlt.le
  have hdQ : (0 : ℚ) < d := by exact_mod_cast hd
  have hsame : Algebra.trdeg ℚ (generatedField (ratScaleFamily (d : ℚ) u)) =
      Algebra.trdeg ℚ (generatedField w) := by
    rw [trdeg_ratScaleFamily_eq (d : ℚ) hdQ u, huSharp, hwdefect]
    congr 1
    omega
  have hfinite : Algebra.trdeg ℚ (generatedField (ratScaleFamily (d : ℚ) u)) <
      Cardinal.aleph0 := by
    rw [hsame, hwdefect]
    exact Cardinal.natCast_lt_aleph0
  have halg :
      letI : Algebra (generatedField (ratScaleFamily (d : ℚ) u))
          (generatedField w) := (stableDeletionInclusion hfield).toAlgebra
      Algebra.IsAlgebraic (generatedField (ratScaleFamily (d : ℚ) u))
        (generatedField w) := by
    exact isAlgebraic_of_le_of_trdeg_eq_of_lt_aleph0 hfield hsame hfinite
  have hex : ∃ i, w i ∉ Submodule.span ℚ (Set.range u) := by
    by_contra hall
    have hall' : ∀ i, w i ∈ Submodule.span ℚ (Set.range u) := by
      intro i
      by_contra hi
      exact hall ⟨i, hi⟩
    have hle : Submodule.span ℚ (Set.range w) ≤
        Submodule.span ℚ (Set.range u) := by
      apply Submodule.span_le.mpr
      rintro z ⟨i, rfl⟩
      exact hall' i
    exact (not_le_of_gt huspanlt) hle
  obtain ⟨i, hi⟩ := hex
  exact ⟨{
      complementCount := k
      deletion := u
      scale := d
      omitted := i
      deletionLinearIndependent := hulin
      deletionAnchored := huanchor
      deletionStable := hustable
      deletionSpanLt := huspanlt
      complementCount_succ := hkOne
      scale_pos := hd
      fieldLe := hfield
      deletionSharp := huSharp
      scaledDeletion_sameTrdeg := hsame
      fullAlgebraic := halg
      omittedOutside := hi }⟩

/-! ## Stable terminal dichotomy -/

/-- A positive stable terminal witness consists of a stable defect-one full family and its
sharp invariant-hyperplane deletion data. -/
def PositiveConjugationStableTerminalWitness {n : ℕ}
    (w : Fin (n + 3) → ℂ) : Prop :=
  LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧ ConjugationStable w ∧
    DefectOne w ∧ Nonempty (StableTerminalDeletionData w)

/-- The stable terminal alternative.  The zero-complement branch is the canonical anchor
boundary; the positive branch carries the invariant-hyperplane algebraic extension. -/
def ConjugationStableTerminalDichotomy : Prop :=
  Algebra.trdeg ℚ (generatedField canonicalAnchor) = (1 : Cardinal) ∨
    ∃ (n : ℕ) (w : Fin (n + 3) → ℂ), PositiveConjugationStableTerminalWitness w

/-- Failure of Schanuel's conjecture is exactly the stable terminal dichotomy. -/
theorem not_conjecture_iff_conjugationStableTerminalDichotomy :
    ¬ Conjecture ↔ ConjugationStableTerminalDichotomy := by
  constructor
  · intro h
    obtain ⟨n, ⟨w, hwlin, hwanchor, hwstable, hwfail⟩, hmin⟩ :=
      exists_first_conjugationStableCanonicalAnchored_failure h
    have hwdefect :=
      defectOne_of_no_smaller_conjugationStableCanonicalAnchored_failure
        hwlin hwanchor hwstable hwfail hmin
    cases n with
    | zero =>
        apply Or.inl
        have hw : w = canonicalAnchor := by
          funext i
          fin_cases i
          · exact hwanchor.1
          · exact hwanchor.2
        simpa [hw] using hwdefect
    | succ n =>
        apply Or.inr
        have hdata := exists_stableTerminalDeletionData_of_least_failure
          hwlin hwanchor hwstable hwfail hmin (Nat.zero_lt_succ n)
        exact ⟨n, w, hwlin, hwanchor, hwstable, hwdefect, hdata⟩
  · intro hterm hC
    rcases hterm with hzero | ⟨n, w, hwlin, -, -, hwdefect, -⟩
    · have hanchorDefect : DefectOne canonicalAnchor := by
        simpa [DefectOne] using hzero
      exact (noDefectOneIndependentFamilies_of_conjecture hC 1 canonicalAnchor
        canonicalAnchor_linearIndependent) hanchorDefect
    · exact (noDefectOneIndependentFamilies_of_conjecture hC (n + 2) w hwlin) hwdefect

/-! ## Eigenvector complement selection -/

/-- The pointwise invariant/anti-invariant alternative for a nonzero functional under an
involution has a single global sign. -/
theorem exists_globally_invariant_or_antiInvariant_hyperplane_functional
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (c : V →ₗ[ℚ] V) (hc : c.comp c = LinearMap.id)
    (A : Submodule ℚ V) (hA : ∀ x ∈ A, c x ∈ A) (hAtop : A < ⊤) :
    ∃ g : V →ₗ[ℚ] ℚ,
      g ≠ 0 ∧ A ≤ LinearMap.ker g ∧
      ((∀ x, g (c x) = g x) ∨ (∀ x, g (c x) = -g x)) ∧
      Module.finrank ℚ (LinearMap.ker g) + 1 = Module.finrank ℚ V := by
  obtain ⟨g, hg, hgA, hsign, hcodim⟩ :=
    exists_invariant_hyperplane_functional c hc A hA hAtop
  obtain ⟨x, hxraw⟩ := DFunLike.ne_iff.mp hg
  have hx : g x ≠ 0 := by simpa using hxraw
  rcases hsign x with hxplus | hxminus
  · refine ⟨g, hg, hgA, Or.inl ?_, hcodim⟩
    intro y
    rcases hsign y with hyplus | hyminus
    · exact hyplus
    · rcases hsign (x + y) with hsumplus | hsumminus
      · have hgy : g y = 0 := by
          simp only [map_add, hxplus, hyminus] at hsumplus
          linarith
        rw [hyminus, hgy, neg_zero]
      · simp only [map_add, hxplus, hyminus] at hsumminus
        exfalso
        apply hx
        linarith
  · refine ⟨g, hg, hgA, Or.inr ?_, hcodim⟩
    intro y
    rcases hsign y with hyplus | hyminus
    · rcases hsign (x + y) with hsumplus | hsumminus
      · simp only [map_add, hxminus, hyplus] at hsumplus
        exfalso
        apply hx
        linarith
      · have hgy : g y = 0 := by
          simp only [map_add, hxminus, hyplus] at hsumminus
          linarith
        rw [hyplus, hgy, neg_zero]
    · exact hyminus

/-- The complementary direction to an invariant hyperplane can be selected as an actual
eigenvector of the involution.  The `+1` branch is fixed; the `-1` branch is negated.  Since
`g b ≠ 0`, this eigenvector lies outside the deletion hyperplane and spans its missing direction. -/
theorem exists_eigenvector_complement_to_invariant_hyperplane
    {V : Type*} [AddCommGroup V] [Module ℚ V] [FiniteDimensional ℚ V]
    (c : V →ₗ[ℚ] V) (hc : c.comp c = LinearMap.id)
    (A : Submodule ℚ V) (hA : ∀ x ∈ A, c x ∈ A) (hAtop : A < ⊤) :
    ∃ (g : V →ₗ[ℚ] ℚ) (b : V),
      g ≠ 0 ∧ A ≤ LinearMap.ker g ∧ g b ≠ 0 ∧
      (((∀ x, g (c x) = g x) ∧ c b = b) ∨
        ((∀ x, g (c x) = -g x) ∧ c b = -b)) ∧
      Module.finrank ℚ (LinearMap.ker g) + 1 = Module.finrank ℚ V := by
  obtain ⟨g, hg, hgA, hsign, hcodim⟩ :=
    exists_globally_invariant_or_antiInvariant_hyperplane_functional c hc A hA hAtop
  obtain ⟨x, hxraw⟩ := DFunLike.ne_iff.mp hg
  have hx : g x ≠ 0 := by simpa using hxraw
  have hc_apply : ∀ y, c (c y) = y := by
    intro y
    have hy := LinearMap.congr_fun hc y
    simpa [LinearMap.comp_apply] using hy
  rcases hsign with hplus | hminus
  · let b : V := (1 / 2 : ℚ) • (x + c x)
    have hcb : c b = b := by
      simp [b, hc_apply, add_comm]
    have hgb : g b = g x := by
      simp [b, hplus]
      ring
    exact ⟨g, b, hg, hgA, hgb.symm ▸ hx, Or.inl ⟨hplus, hcb⟩, hcodim⟩
  · let b : V := (1 / 2 : ℚ) • (x - c x)
    have hcb : c b = -b := by
      simp [b, hc_apply]
      module
    have hgb : g b = g x := by
      simp [b, hminus]
      ring
    exact ⟨g, b, hg, hgA, hgb.symm ▸ hx, Or.inr ⟨hminus, hcb⟩, hcodim⟩

end ConjugationStableTerminal

end

end Schanuel
