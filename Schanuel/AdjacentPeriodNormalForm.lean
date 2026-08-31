import Schanuel.AdjacentPeriodDeletion
import Schanuel.FullyTranscendentalPeriodBoundary
import Schanuel.RationalBasisInvariance

/-!
# Adjacent-period normal form

An explicit invertible rational row operation turns any positive fully transcendental
period-bearing defect-one family into one whose first two inputs differ by the standard period.
Together with `AdjacentPeriodDeletion`, this gives the exact adjacent-period normal form for a
failure of Schanuel's conjecture.
-/

namespace Schanuel

open Function Set
open scoped Matrix

noncomputable section

/-- Reindexing a finite family by a permutation does not change its generated field. -/
theorem generatedField_comp_equiv {m : ℕ} (z : Fin m → ℂ)
    (σ : Equiv.Perm (Fin m)) :
    generatedField (z ∘ σ) = generatedField z := by
  rw [generatedField, generators, σ.surjective.range_comp]
  have hexp : (fun i ↦ Complex.exp ((z ∘ σ) i)) =
      (fun i ↦ Complex.exp (z i)) ∘ σ := rfl
  rw [hexp, σ.surjective.range_comp]
  rfl

/-- Replace row `1` of the identity matrix by the coefficient row `c`. -/
def coefficientRowMatrix {n : ℕ} (c : Fin (n + 2) → ℚ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ :=
  Matrix.updateRow 1 1 c

/-- The explicit two-row transformation producing consecutive period shifts.

Starting from the reordered family `u` and a coefficient row `c` with `c ⬝ u = omega`, its
first two output rows are `u 0 + k omega` and `u 0 + (k + 1) omega`; all later rows are unchanged.
-/
def adjacentPeriodMatrix {n : ℕ} (c : Fin (n + 2) → ℚ) (k : ℚ) :
    Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ := by
  let C := coefficientRowMatrix c
  let D := Matrix.updateRow C 0 (C 0 + k • C 1)
  exact Matrix.updateRow D 1 (D 1 + D 0)

theorem det_coefficientRowMatrix {n : ℕ} (c : Fin (n + 2) → ℚ) :
    (coefficientRowMatrix c).det = c 1 := by
  have hrow : (∑ i, c i • (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ) i) = c := by
    funext j
    simp [Matrix.one_apply]
  have hdet := Matrix.det_updateRow_sum
    (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ) (1 : Fin (n + 2)) c
  rw [hrow] at hdet
  simpa [coefficientRowMatrix] using hdet

theorem det_adjacentPeriodMatrix {n : ℕ} (c : Fin (n + 2) → ℚ) (k : ℚ) :
    (adjacentPeriodMatrix c k).det = c 1 := by
  let C := coefficientRowMatrix c
  let D := Matrix.updateRow C 0 (C 0 + k • C 1)
  calc
    (adjacentPeriodMatrix c k).det =
        (Matrix.updateRow D 1 (D 1 + (1 : ℚ) • D 0)).det := by
      simp [adjacentPeriodMatrix, C, D]
    _ = D.det := Matrix.det_updateRow_add_smul_self D (by norm_num) 1
    _ = C.det := Matrix.det_updateRow_add_smul_self C (by norm_num) k
    _ = c 1 := det_coefficientRowMatrix c

/-- The first transformed row is the first input plus `k` times the coefficient combination. -/
theorem rationalMatrixFamily_adjacentPeriodMatrix_zero {n : ℕ}
    (c : Fin (n + 2) → ℚ) (k : ℚ) (u : Fin (n + 2) → ℂ) :
    rationalMatrixFamily (adjacentPeriodMatrix c k) u 0 =
      u 0 + k • (∑ i, c i • u i) := by
  have hone : (∑ i, (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ) 0 i • u i) = u 0 := by
    simpa [rationalMatrixFamily] using congrFun (rationalMatrixFamily_one u) 0
  simp only [rationalMatrixFamily, adjacentPeriodMatrix, coefficientRowMatrix, ne_eq,
    zero_ne_one, not_false_eq_true, Matrix.updateRow_ne, Matrix.updateRow_self, one_ne_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  rw [hone]

/-- The second transformed row is the first input plus `(k+1)` times the coefficient
combination. -/
theorem rationalMatrixFamily_adjacentPeriodMatrix_one {n : ℕ}
    (c : Fin (n + 2) → ℚ) (k : ℚ) (u : Fin (n + 2) → ℂ) :
    rationalMatrixFamily (adjacentPeriodMatrix c k) u 1 =
      u 0 + (k + 1) • (∑ i, c i • u i) := by
  have hone : (∑ i, (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ) 0 i • u i) = u 0 := by
    simpa [rationalMatrixFamily] using congrFun (rationalMatrixFamily_one u) 0
  simp only [rationalMatrixFamily, adjacentPeriodMatrix, coefficientRowMatrix, ne_eq,
    zero_ne_one, not_false_eq_true, Matrix.updateRow_ne, Matrix.updateRow_self, one_ne_zero,
    Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  simp only [add_smul, Finset.sum_add_distrib, mul_smul, Finset.smul_sum]
  rw [hone]
  simp only [one_smul]
  abel

/-- Rows after the first two are unchanged. -/
theorem rationalMatrixFamily_adjacentPeriodMatrix_of_ne {n : ℕ}
    (c : Fin (n + 2) → ℚ) (k : ℚ) (u : Fin (n + 2) → ℂ)
    (i : Fin (n + 2)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) :
    rationalMatrixFamily (adjacentPeriodMatrix c k) u i = u i := by
  have hone : (∑ j, (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℚ) i j • u j) = u i := by
    simpa [rationalMatrixFamily] using congrFun (rationalMatrixFamily_one u) i
  simpa [adjacentPeriodMatrix, coefficientRowMatrix, rationalMatrixFamily, hi0, hi1]
    using hone

/-- Shift by a nonnegative integral multiple of the standard period. -/
def forwardPeriodShift (k : ℕ) (x : ℂ) : ℂ :=
  x + (k : ℂ) * standardPeriod

@[simp]
theorem exp_forwardPeriodShift (k : ℕ) (x : ℂ) :
    Complex.exp (forwardPeriodShift k x) = Complex.exp x := by
  rw [forwardPeriodShift, Complex.exp_add, Complex.exp_nat_mul]
  simp

/-- Among the pairs of shifts starting at `0` and `2`, one pair consists of transcendental
numbers.  The gap is what makes the assertion elementary: if the first period shift is
algebraic, then adding one or two transcendental periods to it gives the shifts at `2` and `3`.
-/
theorem exists_two_consecutive_transcendental_forwardPeriodShifts {x : ℂ}
    (hx : Transcendental ℚ x) :
    ∃ k : ℕ, (k = 0 ∨ k = 2) ∧
      Transcendental ℚ (forwardPeriodShift k x) ∧
      Transcendental ℚ (forwardPeriodShift (k + 1) x) := by
  by_cases hfirst : Transcendental ℚ (forwardPeriodShift 1 x)
  · exact ⟨0, Or.inl rfl, by simpa [forwardPeriodShift] using hx, by simpa using hfirst⟩
  · have hfirstAlg : IsAlgebraic ℚ (forwardPeriodShift 1 x) := not_not.mp hfirst
    have htwo : Transcendental ℚ (forwardPeriodShift 2 x) := by
      have h := transcendental_add_of_isAlgebraic_left hfirstAlg
        FullyTranscendentalPeriodBoundary.period_transcendental
      have heq : forwardPeriodShift 2 x =
          forwardPeriodShift 1 x + FullyTranscendentalPeriodBoundary.period := by
        simp [forwardPeriodShift, standardPeriod,
          FullyTranscendentalPeriodBoundary.period]
        ring
      rw [heq]
      exact h
    have htwoperiod : Transcendental ℚ ((2 : ℂ) * standardPeriod) :=
      transcendental_mul_of_isAlgebraic_left
        (isAlgebraic_algebraMap (A := ℂ) (2 : ℚ)) (by norm_num)
        FullyTranscendentalPeriodBoundary.period_transcendental
    have hthree : Transcendental ℚ (forwardPeriodShift 3 x) := by
      have h := transcendental_add_of_isAlgebraic_left hfirstAlg htwoperiod
      have heq : forwardPeriodShift 3 x =
          forwardPeriodShift 1 x + (2 : ℂ) * standardPeriod := by
        simp [forwardPeriodShift]
        ring
      rw [heq]
      exact h
    exact ⟨2, Or.inr rfl, htwo, by simpa using hthree⟩

/-- The hard direction of the adjacent-period normal form.  An explicit invertible rational
matrix turns a positive fully transcendental period-bearing defect-one witness into a fully
transcendental defect-one witness whose first two inputs differ by exactly one period. -/
theorem exists_periodPairedDefectOne_of_not_conjecture (h : ¬ Conjecture) :
    ∃ (n : ℕ) (w : Fin (n + 2) → ℂ), PeriodPairedDefectOne w := by
  obtain ⟨m, z, hm, hzlin, hzdefect, hzcoord, hzexp, hperiod⟩ :=
    exists_positive_fullyTranscendental_defectOne_periodBearing h
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
  change standardPeriod ∈ Submodule.span ℚ (Set.range z) at hperiod
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℚ).mp hperiod
  have hc_nonzero : ∃ p, c p ≠ 0 := by
    by_contra hall
    have hall' : ∀ p, c p = 0 := by
      simpa only [not_exists, not_not] using hall
    have hc_zero : c = 0 := funext hall'
    rw [hc_zero] at hc
    simp only [Pi.zero_apply, zero_smul, Finset.sum_const_zero] at hc
    exact FullyTranscendentalPeriodBoundary.period_ne_zero hc.symm
  obtain ⟨p, hp⟩ := hc_nonzero
  let σ : Equiv.Perm (Fin (n + 2)) := Equiv.swap 1 p
  let u : Fin (n + 2) → ℂ := z ∘ σ
  let d : Fin (n + 2) → ℚ := c ∘ σ
  have hd_one : d 1 ≠ 0 := by
    simpa [d, σ] using hp
  have hdu : ∑ i, d i • u i = standardPeriod := by
    calc
      ∑ i, d i • u i = ∑ i, (fun j ↦ c j • z j) (σ i) := rfl
      _ = ∑ i, c i • z i := σ.bijective.sum_comp (fun j ↦ c j • z j)
      _ = standardPeriod := hc
  have hulin : LinearIndependent ℚ u := hzlin.comp σ σ.injective
  have hufield : generatedField u = generatedField z := generatedField_comp_equiv z σ
  have hudefect : DefectOne u := (defectOne_congr_generatedField hufield).2 hzdefect
  have hucoord : ∀ i, Transcendental ℚ (u i) := fun i ↦ hzcoord (σ i)
  have huexp : ∀ i, Transcendental ℚ (Complex.exp (u i)) := fun i ↦ hzexp (σ i)
  obtain ⟨k, hk, hkcoord, hk1coord⟩ :=
    exists_two_consecutive_transcendental_forwardPeriodShifts (hucoord 0)
  let B := adjacentPeriodMatrix d (k : ℚ)
  let w := rationalMatrixFamily B u
  have hB : B.det ≠ 0 := by
    simpa [B, det_adjacentPeriodMatrix] using hd_one
  have hwzero : w 0 = forwardPeriodShift k (u 0) := by
    change rationalMatrixFamily (adjacentPeriodMatrix d (k : ℚ)) u 0 = _
    rw [rationalMatrixFamily_adjacentPeriodMatrix_zero, hdu]
    simp [forwardPeriodShift, Rat.smul_def]
  have hwone : w 1 = forwardPeriodShift (k + 1) (u 0) := by
    change rationalMatrixFamily (adjacentPeriodMatrix d (k : ℚ)) u 1 = _
    rw [rationalMatrixFamily_adjacentPeriodMatrix_one, hdu]
    simp [forwardPeriodShift, Rat.smul_def]
  have hwother (i : Fin (n + 2)) (hi0 : i ≠ 0) (hi1 : i ≠ 1) : w i = u i := by
    exact rationalMatrixFamily_adjacentPeriodMatrix_of_ne d (k : ℚ) u i hi0 hi1
  have hwlin : LinearIndependent ℚ w :=
    linearIndependent_rationalMatrixFamily B hB u hulin
  have hwdefect : DefectOne w := by
    unfold DefectOne at hudefect ⊢
    exact (trdeg_rationalMatrixFamily_eq B hB u).trans hudefect
  have hwcoord : ∀ i, Transcendental ℚ (w i) := by
    intro i
    by_cases hi0 : i = 0
    · simpa [hi0, hwzero] using hkcoord
    by_cases hi1 : i = 1
    · simpa [hi1, hwone] using hk1coord
    · rw [hwother i hi0 hi1]
      exact hucoord i
  have hwexp : ∀ i, Transcendental ℚ (Complex.exp (w i)) := by
    intro i
    by_cases hi0 : i = 0
    · rw [hi0, hwzero, exp_forwardPeriodShift]
      exact huexp 0
    by_cases hi1 : i = 1
    · rw [hi1, hwone, exp_forwardPeriodShift]
      exact huexp 0
    · rw [hwother i hi0 hi1]
      exact huexp i
  have hwpair : w 1 - w 0 = standardPeriod := by
    rw [hwone, hwzero]
    simp [forwardPeriodShift]
    ring
  exact ⟨n, w, hwlin, hwdefect, hwcoord, hwexp, hwpair⟩

/-- Schanuel's conjecture fails exactly when a fully transcendental defect-one family exists
whose first two inputs differ by the standard period. -/
theorem not_conjecture_iff_exists_periodPairedDefectOne :
    ¬ Conjecture ↔ ∃ (n : ℕ) (w : Fin (n + 2) → ℂ), PeriodPairedDefectOne w :=
  ⟨exists_periodPairedDefectOne_of_not_conjecture,
    not_conjecture_of_exists_periodPairedDefectOne⟩

end

end Schanuel
