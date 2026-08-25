import Schanuel.CanonicalAnchorNormalForm

/-!
# Canonical-anchor terminal dichotomy

A least canonically anchored failure either has no complementary input, or deleting its final
complementary input is sharp and the full generated field is algebraic over the deletion field.
This packages the last one-step algebraic extension left by the canonical normal form.
-/

namespace Schanuel

open Function Set

noncomputable section

/-- Delete the final complementary input from a positive canonically anchored family. -/
def complementaryDeletion {n : ℕ} (w : Fin (n + 3) → ℂ) : Fin (n + 2) → ℂ :=
  w ∘ Fin.castSuccEmb

/-- The deletion generators form a subset of the full generators. -/
theorem generators_complementaryDeletion_subset {n : ℕ} (w : Fin (n + 3) → ℂ) :
    generators (complementaryDeletion w) ⊆ generators w := by
  simpa [complementaryDeletion] using
    (generators_comp_subset w Fin.castSuccEmb)

/-- The field inclusion associated to the final complementary deletion. -/
def complementaryDeletionInclusion {n : ℕ} (w : Fin (n + 3) → ℂ) :
    generatedField (complementaryDeletion w) →ₐ[ℚ] generatedField w :=
  generatedFieldInclusion (generators_complementaryDeletion_subset w)

/-- The full field is algebraic over the field obtained by deleting the final complementary
input. -/
def AlgebraicOverComplementaryDeletion {n : ℕ} (w : Fin (n + 3) → ℂ) : Prop :=
  letI : Algebra (generatedField (complementaryDeletion w)) (generatedField w) :=
    (complementaryDeletionInclusion w).toAlgebra
  Algebra.IsAlgebraic (generatedField (complementaryDeletion w)) (generatedField w)

/-- The missing input, regarded as an element of the full generated field. -/
def missingComplementaryInputInFull {n : ℕ} (w : Fin (n + 3) → ℂ) :
    generatedField w :=
  ⟨w (Fin.last (n + 2)), IntermediateField.subset_adjoin ℚ _
    (Or.inl ⟨Fin.last (n + 2), rfl⟩)⟩

/-- The exponential of the missing input, regarded as an element of the full generated field. -/
def missingComplementaryExpInFull {n : ℕ} (w : Fin (n + 3) → ℂ) :
    generatedField w :=
  ⟨Complex.exp (w (Fin.last (n + 2))), IntermediateField.subset_adjoin ℚ _
    (Or.inr ⟨Fin.last (n + 2), rfl⟩)⟩

/-- The terminal algebraic extension explicitly makes both the missing input and its exponential
algebraic over the deletion field. -/
theorem missing_complementary_pair_isAlgebraic {n : ℕ} {w : Fin (n + 3) → ℂ}
    (halg : AlgebraicOverComplementaryDeletion w) :
    letI : Algebra (generatedField (complementaryDeletion w)) (generatedField w) :=
      (complementaryDeletionInclusion w).toAlgebra
    IsAlgebraic (generatedField (complementaryDeletion w))
        (missingComplementaryInputInFull w) ∧
      IsAlgebraic (generatedField (complementaryDeletion w))
        (missingComplementaryExpInFull w) := by
  letI : Algebra (generatedField (complementaryDeletion w)) (generatedField w) :=
    (complementaryDeletionInclusion w).toAlgebra
  letI : Algebra.IsAlgebraic (generatedField (complementaryDeletion w))
      (generatedField w) := halg
  exact ⟨Algebra.IsAlgebraic.isAlgebraic _, Algebra.IsAlgebraic.isAlgebraic _⟩

/-- A positive terminal witness: its deletion is a sharp canonically anchored equality tuple,
and adjoining the missing input-exponential pair is algebraic. -/
def PositiveCanonicalTerminalWitness {n : ℕ} (w : Fin (n + 3) → ℂ) : Prop :=
  LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧ DefectOne w ∧
    (∀ i, Transcendental ℚ (w i)) ∧
    (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
    Algebra.trdeg ℚ (generatedField (complementaryDeletion w)) =
      (((n + 2 : ℕ) : Cardinal)) ∧
    AlgebraicOverComplementaryDeletion w

/-- Exact terminal alternative for the canonical normal form.  The left branch is the literal
two-input boundary `Q(2*pi*I,e)` of transcendence degree one. -/
def CanonicalAnchorTerminalDichotomy : Prop :=
  Algebra.trdeg ℚ (generatedField canonicalAnchor) = (1 : Cardinal) ∨
    ∃ (n : ℕ) (w : Fin (n + 3) → ℂ), PositiveCanonicalTerminalWitness w

/-- The final deletion of a positive least anchored failure still begins with the fixed anchor. -/
theorem canonicallyAnchored_complementaryDeletion {n : ℕ} {w : Fin (n + 3) → ℂ}
    (hanchor : CanonicallyAnchored w) :
    CanonicallyAnchored (complementaryDeletion w) := by
  constructor
  · simpa [complementaryDeletion] using hanchor.1
  · simpa [complementaryDeletion] using hanchor.2

/-- Restricted minimality makes the final complementary deletion sharp. -/
theorem trdeg_complementaryDeletion_eq_of_minimal_anchored_failure
    {n : ℕ} {w : Fin (n + 3) → ℂ}
    (hlin : LinearIndependent ℚ w) (hanchor : CanonicallyAnchored w)
    (hdefect : DefectOne w)
    (hmin : ∀ k < n + 1, ¬ CanonicalAnchoredFailureAt k) :
    Algebra.trdeg ℚ (generatedField (complementaryDeletion w)) =
      (((n + 2 : ℕ) : Cardinal)) := by
  let f : Fin (n + 2) ↪ Fin (n + 3) := Fin.castSuccEmb
  have hsubLin : LinearIndependent ℚ (complementaryDeletion w) := by
    exact hlin.comp f f.injective
  have hsubAnchor : CanonicallyAnchored (complementaryDeletion w) :=
    canonicallyAnchored_complementaryDeletion hanchor
  have hsubBound : Bound (complementaryDeletion w) := by
    by_contra hsubFail
    exact hmin n (Nat.lt_succ_self n)
      ⟨complementaryDeletion w, hsubLin, hsubAnchor, hsubFail⟩
  apply le_antisymm
  · exact (trdeg_comp_le w f).trans_eq hdefect
  · unfold Bound at hsubBound
    simpa [complementaryDeletion] using hsubBound

/-- Equality of the full and deletion transcendence degrees makes the full field algebraic over
the deletion field. -/
theorem algebraicOverComplementaryDeletion_of_minimal_anchored_failure
    {n : ℕ} {w : Fin (n + 3) → ℂ}
    (hlin : LinearIndependent ℚ w) (hanchor : CanonicallyAnchored w)
    (hdefect : DefectOne w)
    (hmin : ∀ k < n + 1, ¬ CanonicalAnchoredFailureAt k) :
    AlgebraicOverComplementaryDeletion w := by
  letI : Algebra (generatedField (complementaryDeletion w)) (generatedField w) :=
    (complementaryDeletionInclusion w).toAlgebra
  haveI : IsScalarTower ℚ (generatedField (complementaryDeletion w))
      (generatedField w) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hrest := trdeg_complementaryDeletion_eq_of_minimal_anchored_failure
    hlin hanchor hdefect hmin
  have hfull : Algebra.trdeg ℚ (generatedField w) =
      (((n + 2 : ℕ) : Cardinal)) := hdefect
  have hadd := trdeg_add_eq ℚ (generatedField (complementaryDeletion w))
    (A := generatedField w)
  rw [hrest, hfull] at hadd
  have hzero : Algebra.trdeg (generatedField (complementaryDeletion w))
      (generatedField w) = 0 := by
    rcases Cardinal.add_eq_left_iff.mp hadd with hlarge | hzero
    · have haleph : Cardinal.aleph0 ≤ (((n + 2 : ℕ) : Cardinal)) :=
        (le_max_left _ _).trans hlarge
      exact False.elim ((not_le_of_gt Cardinal.natCast_lt_aleph0) haleph)
    · exact hzero
  exact trdeg_eq_zero_iff.mp hzero

/-- The selected least anchored failure may be made fully transcendental without moving its
anchor or changing its minimal-arity clause. -/
theorem exists_fullyTranscendental_canonicalAnchored_defectOne_minimal_failure
    (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ),
      LinearIndependent ℚ w ∧ CanonicallyAnchored w ∧ DefectOne w ∧
      (∀ i, Transcendental ℚ (w i)) ∧
      (∀ i, Transcendental ℚ (Complex.exp (w i))) ∧
      ∀ k < n, ¬ CanonicalAnchoredFailureAt k := by
  obtain ⟨n, u, hulin, huanchor, -, hudefect, humin⟩ :=
    exists_canonicalAnchored_defectOne_minimal_failure h
  obtain ⟨w, hwlin, hwanchor, hwfield, hwcoord, hwexp⟩ :=
    exists_fullyTranscendental_canonicalAnchor_shear hulin huanchor
  exact ⟨n, w, hwlin, hwanchor,
    (defectOne_congr_generatedField hwfield).2 hudefect,
    hwcoord, hwexp, humin⟩

/-- Failure of Schanuel's conjecture is exactly the terminal canonical-anchor dichotomy. -/
theorem not_conjecture_iff_canonicalAnchorTerminalDichotomy :
    ¬ Conjecture ↔ CanonicalAnchorTerminalDichotomy := by
  constructor
  · intro h
    obtain ⟨n, w, hlin, hanchor, hdefect, hcoord, hexp, hmin⟩ :=
      exists_fullyTranscendental_canonicalAnchored_defectOne_minimal_failure h
    cases n with
    | zero =>
        apply Or.inl
        have hw : w = canonicalAnchor := by
          funext i
          fin_cases i
          · exact hanchor.1
          · exact hanchor.2
        simpa [hw] using hdefect
    | succ n =>
        apply Or.inr
        refine ⟨n, w, hlin, hanchor, hdefect, hcoord, hexp, ?_, ?_⟩
        · exact trdeg_complementaryDeletion_eq_of_minimal_anchored_failure
            hlin hanchor hdefect hmin
        · exact algebraicOverComplementaryDeletion_of_minimal_anchored_failure
            hlin hanchor hdefect hmin
  · intro hterm hC
    rcases hterm with hzero | ⟨n, w, hlin, -, hdefect, -, -, -, -⟩
    · have hanchorDefect : DefectOne canonicalAnchor := by
        simpa [DefectOne] using hzero
      exact (noDefectOneIndependentFamilies_of_conjecture hC 1 canonicalAnchor
        canonicalAnchor_linearIndependent) hanchorDefect
    · exact (noDefectOneIndependentFamilies_of_conjecture hC (n + 2) w hlin) hdefect

end

end Schanuel
