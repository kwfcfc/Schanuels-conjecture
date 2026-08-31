import Mathlib.Algebra.Ring.SumsOfSquares
import Mathlib.FieldTheory.IsRealClosed.Basic

/-!
# An order obstruction to sign-switching automorphisms

An automorphism of an ordered field cannot send a nonzero sum of squares to its negative.
Consequently, a nonzero element switched with its negative lies in neither sign of the
sum-of-squares cone.  This is a conditional algebraic obstruction; no claim is made that a
particular terminal element is a sum of squares.
-/

namespace Schanuel

namespace OrderSwitchObstruction

/-- Ring equivalences preserve finite sums of squares. -/
theorem isSumSq_map_ringEquiv
    {R S : Type*} [Semiring R] [Semiring S]
    (e : R ≃+* S) {x : R} (hx : IsSumSq x) : IsSumSq (e x) := by
  induction hx with
  | zero => simp
  | sq_add a _ ih =>
      simpa using IsSumSq.sq_add (e a) ih

/-- If an ordered-field automorphism sends a nonzero element to its negative, that element is
not a sum of squares. -/
theorem not_isSumSq_of_map_eq_neg
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (e : R ≃+* R) {r : R} (hr0 : r ≠ 0) (her : e r = -r) :
    ¬ IsSumSq r := by
  intro hr
  have hr_nonneg : 0 ≤ r := hr.nonneg
  have hneg : IsSumSq (-r) := by
    simpa [her] using isSumSq_map_ringEquiv e hr
  have hr_nonpos : r ≤ 0 := neg_nonneg.mp hneg.nonneg
  exact hr0 (le_antisymm hr_nonpos hr_nonneg)

/-- If an ordered-field automorphism sends a nonzero element to its negative, its negative is
not a sum of squares either. -/
theorem not_isSumSq_neg_of_map_eq_neg
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (e : R ≃+* R) {r : R} (hr0 : r ≠ 0) (her : e r = -r) :
    ¬ IsSumSq (-r) := by
  intro hneg
  have hr_nonpos : r ≤ 0 := neg_nonneg.mp hneg.nonneg
  have hr : IsSumSq r := by
    have hmap := isSumSq_map_ringEquiv e hneg
    simpa [her] using hmap
  have hr_nonneg : 0 ≤ r := hr.nonneg
  exact hr0 (le_antisymm hr_nonpos hr_nonneg)

/-- The two-sided sum-of-squares obstruction, packaged as one statement. -/
theorem not_isSumSq_and_not_isSumSq_neg_of_map_eq_neg
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    (e : R ≃+* R) {r : R} (hr0 : r ≠ 0) (her : e r = -r) :
    ¬ IsSumSq r ∧ ¬ IsSumSq (-r) :=
  ⟨not_isSumSq_of_map_eq_neg e hr0 her,
    not_isSumSq_neg_of_map_eq_neg e hr0 her⟩

/-- In an ordered real-closed field, an automorphism can send an element to its negative only
when that element is zero. -/
theorem eq_zero_of_map_eq_neg_of_isRealClosed
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (e : R ≃+* R) {r : R} (her : e r = -r) : r = 0 := by
  by_contra hr0
  have hobs := not_isSumSq_and_not_isSumSq_neg_of_map_eq_neg e hr0 her
  rcases IsRealClosed.isSquare_or_isSquare_neg r with hr | hr
  · exact hobs.1 hr.isSumSq
  · exact hobs.2 hr.isSumSq

/-- Equivalently, no ordered real-closed-field automorphism switches a nonzero element with its
negative. -/
theorem map_ne_neg_of_isRealClosed
    {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R]
    (e : R ≃+* R) {r : R} (hr0 : r ≠ 0) : e r ≠ -r := by
  intro her
  exact hr0 (eq_zero_of_map_eq_neg_of_isRealClosed e her)

end OrderSwitchObstruction

end Schanuel
