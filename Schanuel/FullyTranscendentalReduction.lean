import Schanuel.TranscendentalReduction

/-!
# Reduction to two uniform transcendence branches

After the all-algebraic coordinate case, `TranscendentalReduction` reduces Schanuel's
conjecture to tuples all of whose coordinates are transcendental.  This file makes the
remaining reduction uniform on the exponential side as well.

If some exponential is transcendental, use its coordinate as a pivot.  An exponential which
is already transcendental is left alone.  If `exp (z i)` is algebraic, adding either one or two
copies of the pivot makes its exponential transcendental.  Coefficient two is needed only when
coefficient one would make the coordinate algebraic.  Thus the coefficients `0`, `1`, and `2`
simultaneously avoid coordinate cancellation and make every exponential transcendental.
-/

namespace Schanuel

noncomputable section

/-- Multiplication by a nonzero algebraic number preserves transcendence. -/
theorem transcendental_mul_of_isAlgebraic_left {a t : ℂ}
    (ha : IsAlgebraic ℚ a) (ha0 : a ≠ 0) (ht : Transcendental ℚ t) :
    Transcendental ℚ (a * t) := by
  intro hat
  apply ht
  have hquot : IsAlgebraic ℚ ((a * t) * a⁻¹) := hat.mul ha.inv
  have heq : (a * t) * a⁻¹ = t := by
    calc
      (a * t) * a⁻¹ = t * (a * a⁻¹) := by ring
      _ = t := by simp [ha0]
  rwa [heq] at hquot

/-- Use coefficient zero for an already-transcendental exponential.  Otherwise use one,
unless adding the pivot once would make the coordinate algebraic, in which case use two. -/
def fullTranscendenceCoeffs {n : ℕ} (z : Fin n → ℂ) (j : Fin n) : Fin n → ℤ :=
  fun i ↦
    @ite ℤ (Transcendental ℚ (Complex.exp (z i))) (Classical.propDecidable _) 0
      (@ite ℤ (Transcendental ℚ (z i + z j)) (Classical.propDecidable _) 1 2)

/-- The simultaneous integer shear selected by `fullTranscendenceCoeffs`. -/
def fullTranscendenceShear {n : ℕ} (z : Fin n → ℂ) (j : Fin n) : Fin n → ℂ :=
  integerShearFamily z j (fullTranscendenceCoeffs z j)

theorem fullTranscendenceCoeffs_pivot_eq_zero {n : ℕ} {z : Fin n → ℂ}
    {j : Fin n} (hjexp : Transcendental ℚ (Complex.exp (z j))) :
    fullTranscendenceCoeffs z j j = 0 := by
  simp [fullTranscendenceCoeffs, hjexp]

/-- The selected coefficients never destroy coordinate transcendence. -/
theorem transcendental_fullTranscendenceShear {n : ℕ} {z : Fin n → ℂ}
    {j : Fin n} (hz : ∀ i, Transcendental ℚ (z i)) :
    ∀ i, Transcendental ℚ (fullTranscendenceShear z j i) := by
  intro i
  by_cases hexp : Transcendental ℚ (Complex.exp (z i))
  · simpa [fullTranscendenceShear, fullTranscendenceCoeffs, hexp] using hz i
  by_cases hone : Transcendental ℚ (z i + z j)
  · simpa [fullTranscendenceShear, fullTranscendenceCoeffs, hexp, hone] using hone
  · have honeAlg : IsAlgebraic ℚ (z i + z j) := not_not.mp hone
    have htwo : Transcendental ℚ ((z i + z j) + z j) :=
      transcendental_add_of_isAlgebraic_left honeAlg (hz j)
    convert htwo using 1 <;>
      simp [fullTranscendenceShear, fullTranscendenceCoeffs, hexp, hone] <;> ring

/-- If the pivot exponential is transcendental, the selected shear makes every exponential
transcendental. -/
theorem transcendental_exp_fullTranscendenceShear {n : ℕ} {z : Fin n → ℂ}
    {j : Fin n} (hjexp : Transcendental ℚ (Complex.exp (z j))) :
    ∀ i, Transcendental ℚ (Complex.exp (fullTranscendenceShear z j i)) := by
  intro i
  by_cases hexp : Transcendental ℚ (Complex.exp (z i))
  · simpa [fullTranscendenceShear, fullTranscendenceCoeffs, hexp] using hexp
  have hexpAlg : IsAlgebraic ℚ (Complex.exp (z i)) := not_not.mp hexp
  have hexp0 : Complex.exp (z i) ≠ 0 := Complex.exp_ne_zero _
  by_cases hone : Transcendental ℚ (z i + z j)
  · have hprod : Transcendental ℚ (Complex.exp (z i) * Complex.exp (z j)) :=
      transcendental_mul_of_isAlgebraic_left hexpAlg hexp0 hjexp
    simpa [fullTranscendenceShear, fullTranscendenceCoeffs, hexp, hone,
      Complex.exp_add] using hprod
  · have hpivSq : Transcendental ℚ ((Complex.exp (z j)) ^ 2) :=
      hjexp.pow (by norm_num)
    have hprod : Transcendental ℚ (Complex.exp (z i) * (Complex.exp (z j)) ^ 2) :=
      transcendental_mul_of_isAlgebraic_left hexpAlg hexp0 hpivSq
    have hjtwo : Complex.exp (((2 : ℤ) : ℂ) * z j) = (Complex.exp (z j)) ^ 2 := by
      rw [Complex.exp_int_mul]
      rfl
    rw [fullTranscendenceShear, integerShearFamily_apply,
      fullTranscendenceCoeffs, if_neg hexp, if_neg hone, Complex.exp_add, hjtwo]
    exact hprod

theorem linearIndependent_fullTranscendenceShear_iff {n : ℕ} {z : Fin n → ℂ}
    {j : Fin n} (hjexp : Transcendental ℚ (Complex.exp (z j))) :
    LinearIndependent ℚ (fullTranscendenceShear z j) ↔ LinearIndependent ℚ z := by
  exact linearIndependent_integerShearFamily_iff z j _
    (fullTranscendenceCoeffs_pivot_eq_zero hjexp)

theorem generatedField_fullTranscendenceShear_eq {n : ℕ} {z : Fin n → ℂ}
    {j : Fin n} (hjexp : Transcendental ℚ (Complex.exp (z j))) :
    generatedField (fullTranscendenceShear z j) = generatedField z := by
  exact generatedField_integerShearFamily_eq z j _
    (fullTranscendenceCoeffs_pivot_eq_zero hjexp)

/-- Starting from an all-transcendental-coordinate tuple with one transcendental exponential,
one simultaneous shear gives an all-transcendental tuple on both sides and preserves the field
exactly. -/
theorem exists_fullyTranscendental_integerShear {n : ℕ} {z : Fin n → ℂ}
    (hzlin : LinearIndependent ℚ z) (hz : ∀ i, Transcendental ℚ (z i))
    (hexp : ∃ j, Transcendental ℚ (Complex.exp (z j))) :
    ∃ w : Fin n → ℂ,
      LinearIndependent ℚ w ∧ generatedField w = generatedField z ∧
        (∀ i, Transcendental ℚ (w i)) ∧
        ∀ i, Transcendental ℚ (Complex.exp (w i)) := by
  obtain ⟨j, hjexp⟩ := hexp
  exact ⟨fullTranscendenceShear z j,
    (linearIndependent_fullTranscendenceShear_iff hjexp).2 hzlin,
    generatedField_fullTranscendenceShear_eq hjexp,
    transcendental_fullTranscendenceShear hz,
    transcendental_exp_fullTranscendenceShear hjexp⟩

/-- Exact trichotomy after integral shears: algebraic coordinates, transcendental coordinates
with algebraic exponentials, or transcendental coordinates with transcendental exponentials. -/
theorem algebraic_or_uniformTranscendental_integerShear {n : ℕ} {z : Fin n → ℂ}
    (hzlin : LinearIndependent ℚ z) :
    (∀ i, IsAlgebraic ℚ (z i)) ∨
      (∃ w : Fin n → ℂ,
        LinearIndependent ℚ w ∧ generatedField w = generatedField z ∧
          (∀ i, Transcendental ℚ (w i)) ∧
          ∀ i, IsAlgebraic ℚ (Complex.exp (w i))) ∨
      ∃ w : Fin n → ℂ,
        LinearIndependent ℚ w ∧ generatedField w = generatedField z ∧
          (∀ i, Transcendental ℚ (w i)) ∧
          ∀ i, Transcendental ℚ (Complex.exp (w i)) := by
  rcases all_algebraic_or_exists_all_transcendental_integerShear hzlin with
    halg | ⟨u, hulin, hufield, hu⟩
  · exact Or.inl halg
  by_cases hualgexp : ∀ i, IsAlgebraic ℚ (Complex.exp (u i))
  · exact Or.inr (Or.inl ⟨u, hulin, hufield, hu, hualgexp⟩)
  · have hutransExp : ∃ j, Transcendental ℚ (Complex.exp (u j)) := by
      simpa only [Transcendental] using not_forall.mp hualgexp
    obtain ⟨w, hwlin, hwfield, hw, hwexp⟩ :=
      exists_fullyTranscendental_integerShear hulin hu hutransExp
    exact Or.inr (Or.inr ⟨w, hwlin, hwfield.trans hufield, hw, hwexp⟩)

/-- Schanuel restricted to transcendental coordinates whose exponentials are all algebraic. -/
def TranscendentalAlgebraicExpConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    (∀ i, Transcendental ℚ (z i)) →
    (∀ i, IsAlgebraic ℚ (Complex.exp (z i))) → Bound z

/-- Schanuel restricted to tuples whose coordinates and exponentials are individually all
transcendental. -/
def FullyTranscendentalConjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z →
    (∀ i, Transcendental ℚ (z i)) →
    (∀ i, Transcendental ℚ (Complex.exp (z i))) → Bound z

/-- The full conjecture is exactly the conjunction of its two uniform transcendental
branches.  The omitted all-algebraic-coordinate branch is unconditional. -/
theorem conjecture_iff_uniformTranscendental_branches :
    Conjecture ↔ TranscendentalAlgebraicExpConjecture ∧ FullyTranscendentalConjecture := by
  constructor
  · intro hS
    exact ⟨fun n z hz _ _ ↦ hS n z hz, fun n z hz _ _ ↦ hS n z hz⟩
  · rintro ⟨hAlgExp, hFull⟩ n z hzlin
    rcases algebraic_or_uniformTranscendental_integerShear hzlin with
      halg | ⟨w, hwlin, hwfield, hw, hwexp⟩ | ⟨w, hwlin, hwfield, hw, hwexp⟩
    · exact AlgebraicInputs.bound_of_isAlgebraic_coordinate z hzlin halg
    · have hwbound : Bound w := hAlgExp n w hwlin hw hwexp
      unfold Bound at hwbound ⊢
      calc
        Cardinal.mk (Fin n) ≤ Algebra.trdeg ℚ (generatedField w) := hwbound
        _ = Algebra.trdeg ℚ (generatedField z) :=
          (IntermediateField.equivOfEq hwfield).trdeg_eq
    · have hwbound : Bound w := hFull n w hwlin hw hwexp
      unfold Bound at hwbound ⊢
      calc
        Cardinal.mk (Fin n) ≤ Algebra.trdeg ℚ (generatedField w) := hwbound
        _ = Algebra.trdeg ℚ (generatedField z) :=
          (IntermediateField.equivOfEq hwfield).trdeg_eq

end

end Schanuel
