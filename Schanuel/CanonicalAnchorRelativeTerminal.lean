import Schanuel.CanonicalAnchorTerminalDichotomy

/-!
# The terminal dichotomy relative to the canonical anchor field

The canonical-anchor terminal alternative can be made disjoint.  Either the two-element core
`(2*pi*I, e)` is algebraically dependent, or it is algebraically independent and a positive
terminal witness remains.  In the second branch, the sharp deletion field has relative
transcendence degree exactly equal to the number of complementary anchor inputs.
-/

namespace Schanuel

open Function Set

noncomputable section

namespace CanonicalAnchorRelativeTerminal

abbrev core : Fin 2 → ℂ := FullyTranscendentalPeriodBoundary.core

/-- The canonical anchor field has transcendence degree at most two. -/
theorem trdeg_canonicalAnchor_le_two :
    Algebra.trdeg ℚ (generatedField canonicalAnchor) ≤ (2 : Cardinal) := by
  letI : Algebra.IsAlgebraic
      (Algebra.adjoin ℚ
        (Set.range FullyTranscendentalPeriodBoundary.liftedCore))
      (generatedField canonicalAnchor) :=
    FullyTranscendentalPeriodBoundary.isAlgebraic_adjoin_range_liftedCore
  have h := Algebra.IsAlgebraic.trdeg_le_cardinalMk ℚ
    (Set.range FullyTranscendentalPeriodBoundary.liftedCore)
  simpa using h.trans Cardinal.mk_range_le

/-- Algebraic independence of `(2*pi*I,e)` makes the anchor field have degree exactly two. -/
theorem trdeg_canonicalAnchor_eq_two_of_algebraicIndependent
    (hcore : AlgebraicIndependent ℚ core) :
    Algebra.trdeg ℚ (generatedField canonicalAnchor) = (2 : Cardinal) := by
  apply le_antisymm trdeg_canonicalAnchor_le_two
  have hbound : Bound canonicalAnchor :=
    FullyTranscendentalPeriodBoundary.bound_family_iff_algebraicIndependent_period_exp_one.mpr
      hcore
  simpa [Bound] using hbound

/-- Degree two of the anchor field is equivalent to algebraic independence of its core. -/
theorem trdeg_canonicalAnchor_eq_two_iff_algebraicIndependent :
    Algebra.trdeg ℚ (generatedField canonicalAnchor) = (2 : Cardinal) ↔
      AlgebraicIndependent ℚ core := by
  constructor
  · intro htd
    apply FullyTranscendentalPeriodBoundary.bound_family_iff_algebraicIndependent_period_exp_one.mp
    simp [Bound, htd]
  · exact trdeg_canonicalAnchor_eq_two_of_algebraicIndependent

/-- The degree-one anchor boundary is exactly algebraic dependence of `2*pi*I` and `e`. -/
theorem trdeg_canonicalAnchor_eq_one_iff_not_algebraicIndependent :
    Algebra.trdeg ℚ (generatedField canonicalAnchor) = (1 : Cardinal) ↔
      ¬ AlgebraicIndependent ℚ core := by
  constructor
  · intro htd hcore
    have htwo := trdeg_canonicalAnchor_eq_two_of_algebraicIndependent hcore
    rw [htd] at htwo
    norm_num at htwo
  · intro hcore
    have hnotBound : ¬ Bound canonicalAnchor := by
      intro hbound
      exact hcore
        (FullyTranscendentalPeriodBoundary.bound_family_iff_algebraicIndependent_period_exp_one.mp
          hbound)
    have hupper : Algebra.trdeg ℚ (generatedField canonicalAnchor) ≤ (1 : Cardinal) := by
      have hlt : Algebra.trdeg ℚ (generatedField canonicalAnchor) < (2 : Cardinal) := by
        apply lt_of_not_ge
        simpa [Bound] using hnotBound
      rw [show (2 : Cardinal) = Order.succ (1 : Cardinal) by
        calc
          (2 : Cardinal) = (((1 + 1 : ℕ) : Cardinal)) := by norm_num
          _ = Order.succ (1 : Cardinal) := by
            rw [Nat.cast_add]
            exact (Cardinal.succ_natCast 1).symm] at hlt
      exact Order.lt_succ_iff.mp hlt
    have hlower : (1 : Cardinal) ≤
        Algebra.trdeg ℚ (generatedField canonicalAnchor) := by
      let f : Fin 1 ↪ Fin 2 := Fin.castSuccEmb
      have hsubBound : Bound (canonicalAnchor ∘ f) := by
        apply bound_of_algebraicIndependent_coordinate
        rw [algebraicIndependent_unique_type_iff]
        change Transcendental ℚ (canonicalAnchor 0)
        exact canonicalAnchor_coordinate_transcendental 0
      have hsub := hsubBound
      change Cardinal.mk (Fin 1) ≤
        Algebra.trdeg ℚ (generatedField (canonicalAnchor ∘ f)) at hsub
      simpa using hsub.trans (trdeg_comp_le canonicalAnchor f)
    exact le_antisymm hupper hlower

/-- The canonical anchor field has exactly one or two transcendence degrees. -/
theorem trdeg_canonicalAnchor_eq_one_or_two :
    Algebra.trdeg ℚ (generatedField canonicalAnchor) = (1 : Cardinal) ∨
      Algebra.trdeg ℚ (generatedField canonicalAnchor) = (2 : Cardinal) := by
  by_cases hcore : AlgebraicIndependent ℚ core
  · exact Or.inr (trdeg_canonicalAnchor_eq_two_of_algebraicIndependent hcore)
  · exact Or.inl
      (trdeg_canonicalAnchor_eq_one_iff_not_algebraicIndependent.mpr hcore)

/-- An anchored family contains every coordinate and exponential of the canonical anchor. -/
theorem generators_canonicalAnchor_subset_of_anchored {n : ℕ}
    {v : Fin (n + 2) → ℂ} (hanchor : CanonicallyAnchored v) :
    generators canonicalAnchor ⊆ generators v := by
  rintro x (hx | hx)
  · rcases hx with ⟨i, rfl⟩
    apply Or.inl
    fin_cases i
    · exact ⟨0, hanchor.1⟩
    · exact ⟨1, hanchor.2⟩
  · rcases hx with ⟨i, rfl⟩
    apply Or.inr
    fin_cases i
    · exact ⟨0, congrArg Complex.exp hanchor.1⟩
    · exact ⟨1, congrArg Complex.exp hanchor.2⟩

/-- The field inclusion from the fixed anchor field into an anchored generated field. -/
def canonicalAnchorInclusion {n : ℕ} (v : Fin (n + 2) → ℂ)
    (hanchor : CanonicallyAnchored v) :
    generatedField canonicalAnchor →ₐ[ℚ] generatedField v :=
  generatedFieldInclusion (generators_canonicalAnchor_subset_of_anchored hanchor)

/-- A sharp anchored family has exactly one relative transcendence unit for each complementary
input once the anchor core is algebraically independent. -/
theorem relative_trdeg_eq_complementCount {n : ℕ} {v : Fin (n + 2) → ℂ}
    (hanchor : CanonicallyAnchored v)
    (hcore : AlgebraicIndependent ℚ core)
    (hfull : Algebra.trdeg ℚ (generatedField v) = (((n + 2 : ℕ) : Cardinal))) :
    letI : Algebra (generatedField canonicalAnchor) (generatedField v) :=
      (canonicalAnchorInclusion v hanchor).toAlgebra
    Algebra.trdeg (generatedField canonicalAnchor) (generatedField v) =
      ((n : ℕ) : Cardinal) := by
  letI : Algebra (generatedField canonicalAnchor) (generatedField v) :=
    (canonicalAnchorInclusion v hanchor).toAlgebra
  letI : IsScalarTower ℚ (generatedField canonicalAnchor) (generatedField v) := by
    apply IsScalarTower.of_algebraMap_eq'
    ext x
    rfl
  have hadd := trdeg_add_eq ℚ (generatedField canonicalAnchor)
    (A := generatedField v)
  rw [trdeg_canonicalAnchor_eq_two_of_algebraicIndependent hcore, hfull] at hadd
  have hcancel :
      Algebra.trdeg (generatedField canonicalAnchor) (generatedField v) + 2 =
        ((n : Cardinal) + 2) := by
    calc
      Algebra.trdeg (generatedField canonicalAnchor) (generatedField v) + 2 =
          2 + Algebra.trdeg (generatedField canonicalAnchor) (generatedField v) :=
        add_comm _ _
      _ = (((n + 2 : ℕ) : Cardinal)) := hadd
      _ = (n : Cardinal) + 2 := by norm_num
  exact (Cardinal.add_nat_inj 2).mp hcancel

/-- In the positive terminal branch, the deletion is a relative equality family over the
independent anchor core. -/
theorem positiveTerminal_relative_trdeg_eq {n : ℕ} {w : Fin (n + 3) → ℂ}
    (hcore : AlgebraicIndependent ℚ core)
    (hw : PositiveCanonicalTerminalWitness w) :
    let hanchor : CanonicallyAnchored (complementaryDeletion w) :=
      canonicallyAnchored_complementaryDeletion hw.2.1
    letI : Algebra (generatedField canonicalAnchor)
        (generatedField (complementaryDeletion w)) :=
      (canonicalAnchorInclusion (complementaryDeletion w) hanchor).toAlgebra
    Algebra.trdeg (generatedField canonicalAnchor)
        (generatedField (complementaryDeletion w)) = ((n : ℕ) : Cardinal) := by
  exact relative_trdeg_eq_complementCount
    (canonicallyAnchored_complementaryDeletion hw.2.1) hcore hw.2.2.2.2.2.1

/-- The disjoint version of the terminal normal form. -/
def DisjointCanonicalAnchorTerminalDichotomy : Prop :=
  ¬ AlgebraicIndependent ℚ core ∨
    (AlgebraicIndependent ℚ core ∧
      ∃ (n : ℕ) (w : Fin (n + 3) → ℂ), PositiveCanonicalTerminalWitness w)

/-- Dependence of the fixed anchor core already gives a two-input counterexample. -/
theorem not_conjecture_of_not_algebraicIndependent_core
    (hcore : ¬ AlgebraicIndependent ℚ core) : ¬ Conjecture := by
  apply not_conjecture_iff_canonicalAnchorTerminalDichotomy.mpr
  exact Or.inl
    (trdeg_canonicalAnchor_eq_one_iff_not_algebraicIndependent.mpr hcore)

/-- Conditional on independence of the anchor core, failure is exactly the positive terminal
branch; the degree-one boundary has been removed. -/
theorem not_conjecture_iff_exists_positiveTerminal_of_algebraicIndependent_core
    (hcore : AlgebraicIndependent ℚ core) :
    ¬ Conjecture ↔
      ∃ (n : ℕ) (w : Fin (n + 3) → ℂ), PositiveCanonicalTerminalWitness w := by
  constructor
  · intro hfail
    rcases not_conjecture_iff_canonicalAnchorTerminalDichotomy.mp hfail with htd | hpos
    · exact False.elim
        ((trdeg_canonicalAnchor_eq_one_iff_not_algebraicIndependent.mp htd) hcore)
    · exact hpos
  · intro hpos
    exact not_conjecture_iff_canonicalAnchorTerminalDichotomy.mpr (Or.inr hpos)

/-- Failure is equivalent to either dependence of `(2*pi*I,e)`, or a positive terminal
algebraic graph extension over an independent anchor field. -/
theorem not_conjecture_iff_disjointCanonicalAnchorTerminalDichotomy :
    ¬ Conjecture ↔ DisjointCanonicalAnchorTerminalDichotomy := by
  constructor
  · intro hfail
    by_cases hcore : AlgebraicIndependent ℚ core
    · apply Or.inr
      refine ⟨hcore, ?_⟩
      rcases not_conjecture_iff_canonicalAnchorTerminalDichotomy.mp hfail with htd | hpos
      · exact False.elim
          ((trdeg_canonicalAnchor_eq_one_iff_not_algebraicIndependent.mp htd) hcore)
      · exact hpos
    · exact Or.inl hcore
  · rintro (hcore | ⟨-, hpos⟩)
    · apply not_conjecture_iff_canonicalAnchorTerminalDichotomy.mpr
      exact Or.inl
        (trdeg_canonicalAnchor_eq_one_iff_not_algebraicIndependent.mpr hcore)
    · apply not_conjecture_iff_canonicalAnchorTerminalDichotomy.mpr
      exact Or.inr hpos

end CanonicalAnchorRelativeTerminal

end

end Schanuel
