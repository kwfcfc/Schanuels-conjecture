import Schanuel.MinimalCounterexample
import Schanuel.FullyTranscendentalReduction

/-!
# A uniform transcendental normal form for a first failure

Any failure of Schanuel's conjecture has a least-arity defect-one witness.
The checked integral-shear trichotomy then moves that witness, without
changing its generated field, into one of the two remaining uniform
transcendental branches.
-/

namespace Schanuel

noncomputable section

set_option synthInstance.maxHeartbeats 200000 in
-- Their algebra towers also create a larger instance-search graph.
/-- If Schanuel's conjecture fails, there is a rationally independent
defect-one witness whose coordinates are all transcendental and whose
exponentials are either all algebraic or all transcendental. -/
theorem exists_uniform_defect_one_minimal_failure (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
      LinearIndependent ℚ w ∧ ¬ Bound w ∧
      (∀ v : Fin n → ℂ, LinearIndependent ℚ v → Bound v) ∧
      DefectOne w ∧
      (((∀ i, Transcendental ℚ (w i)) ∧
          ∀ i, IsAlgebraic ℚ (Complex.exp (w i))) ∨
        ((∀ i, Transcendental ℚ (w i)) ∧
          ∀ i, Transcendental ℚ (Complex.exp (w i)))) := by
  obtain ⟨n, z, hz, hfail, hprev, hzdefect⟩ :=
    exists_defectOne_minimal_failure h
  rcases algebraic_or_uniformTranscendental_integerShear hz with
    halg | ⟨w, hw, hwfield, hwtrans, hwexp⟩ |
      ⟨w, hw, hwfield, hwtrans, hwexp⟩
  · exact False.elim
      (hfail (AlgebraicInputs.bound_of_isAlgebraic_coordinate z hz halg))
  · have hwfail : ¬ Bound w := by
      intro hwbound
      apply hfail
      unfold Bound at hwbound ⊢
      exact hwbound.trans_eq (IntermediateField.equivOfEq hwfield).trdeg_eq
    have hwdefect : DefectOne w :=
      (defectOne_congr_generatedField hwfield).2 hzdefect
    exact ⟨n, w, hw, hwfail, hprev, hwdefect, Or.inl ⟨hwtrans, hwexp⟩⟩
  · have hwfail : ¬ Bound w := by
      intro hwbound
      apply hfail
      unfold Bound at hwbound ⊢
      exact hwbound.trans_eq (IntermediateField.equivOfEq hwfield).trdeg_eq
    have hwdefect : DefectOne w :=
      (defectOne_congr_generatedField hwfield).2 hzdefect
    exact ⟨n, w, hw, hwfail, hprev, hwdefect, Or.inr ⟨hwtrans, hwexp⟩⟩

set_option synthInstance.maxHeartbeats 200000 in
-- This repeats the combined normal-form statement on the right side of an equivalence.
/-- Failure of Schanuel's conjecture is exactly the existence of a first
defect-one witness in one of the two uniform transcendental branches. -/
theorem not_conjecture_iff_exists_uniform_defect_one_minimal_failure :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 1) → ℂ),
        LinearIndependent ℚ w ∧ ¬ Bound w ∧
        (∀ v : Fin n → ℂ, LinearIndependent ℚ v → Bound v) ∧
        DefectOne w ∧
        (((∀ i, Transcendental ℚ (w i)) ∧
            ∀ i, IsAlgebraic ℚ (Complex.exp (w i))) ∨
          ((∀ i, Transcendental ℚ (w i)) ∧
            ∀ i, Transcendental ℚ (Complex.exp (w i)))) := by
  constructor
  · exact exists_uniform_defect_one_minimal_failure
  · rintro ⟨n, w, hw, hwfail, -, -, -⟩ hC
    exact hwfail (hC (n + 1) w hw)

end

end Schanuel
