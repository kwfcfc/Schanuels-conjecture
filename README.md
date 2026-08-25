# Schanuel's conjecture: a Lean 4 formalization in progress

[`PROMPT.md`](./PROMPT.md) is the authoritative target: prove Schanuel's transcendence-degree
bound for every finite rationally linearly independent complex family. The repository does not
yet prove `Schanuel.Conjecture`; in particular, the completed one-dimensional argument below is
not presented as a solution of the full task.

## Checked results

- [`Schanuel.lean`](./Schanuel.lean) defines the generated field, `Bound`, and `Conjecture`, and
  proves the elementary field-theoretic bounds and the equivalence of the one-dimensional case
  with Hermite--Lindemann.
- [`Schanuel/Structural.lean`](./Schanuel/Structural.lean) gives the exact finite-selection
  reformulation using algebraically independent displayed generators.
- [`Schanuel/MinimalCounterexample.lean`](./Schanuel/MinimalCounterexample.lean) proves that if
  the conjecture first fails in arity `n + 1`, the generated field has transcendence degree
  exactly `n`; a minimal failure can miss the target by only one. Every `n`-coordinate
  restriction has that same transcendence degree, and the full field is algebraic over each
  such restriction. It constructs a least-arity defect-one witness from any failure and proves
  that the full conjecture is equivalent to the nonexistence of any independent defect-one
  family.
- [`Schanuel/MinimalCounterexampleFullyTranscendental.lean`](./Schanuel/MinimalCounterexampleFullyTranscendental.lean)
  chooses the least failure inside the equivalent fully transcendental restriction. Deleting one
  coordinate preserves both pointwise transcendence conditions, so restricted minimality alone
  gives the predecessor lower bound and an exact defect-one witness. Every one-coordinate
  deletion has the same transcendence degree, and the full field is algebraic over its deletion
  field. The least failure has arity at least two, so failure of the full conjecture is equivalent
  to existence of a fully transcendental independent defect-one family with positive predecessor
  index.
- [`Schanuel/MinimalCounterexamplePeriodBearing.lean`](./Schanuel/MinimalCounterexamplePeriodBearing.lean)
  strengthens this normal form using the analytic period `2*pi*I`.  Any failure is equivalent to
  a fully transcendental independent defect-one family of length at least two whose rational input
  span contains that period.  The algebraic branch replaces one deleted coordinate, while the
  transcendental branch appends one period shift and raises the transcendence degree exactly once.
- [`Schanuel/CriticalPeriodEquality.lean`](./Schanuel/CriticalPeriodEquality.lean) proves that
  failure is equivalently witnessed by a positive fully transcendental independent tuple `v`
  with exact equality `trdeg Q(v,exp v)=len(v)`, which does not rationally span `2*pi*I` although
  that period is algebraic over its generated field.  The forward proof handles the algebraic-
  period branch by a selected coordinate deletion and the transcendental-period branch by an
  exact deletion-and-replacement tower argument; the converse appends the period and loses one
  unit.
- [`Schanuel/AdjacentPeriodDeletion.lean`](./Schanuel/AdjacentPeriodDeletion.lean) proves the
  exact deletion-tower identity for a family whose first two inputs differ by `2*pi*I`: the full
  generated field is the deletion field with that single period adjoined. Its relative
  transcendence degree is therefore zero or one; for a fully transcendental defect-one family,
  deletion either attains the sharp full bound or produces a smaller fully transcendental
  defect-one family.
- [`Schanuel/AdjacentPeriodNormalForm.lean`](./Schanuel/AdjacentPeriodNormalForm.lean) completes
  the adjacent-period equivalence.  An explicit invertible rational matrix, with determinant the
  selected nonzero period coefficient, changes any positive period-bearing witness into a fully
  transcendental defect-one family whose first two inputs differ by exactly `2*pi*I`.
- [`Schanuel/CanonicalAnchorNormalForm.lean`](./Schanuel/CanonicalAnchorNormalForm.lean) proves
  the exact canonical-anchor equivalence.  Rectangular rational denominator clearing gives
  transcendence-degree monotonicity under finite rational-span inclusion, a prescribed basis
  extension fixes the leading inputs literally at `1+2*pi*I` and `1+4*pi*I`, least anchored
  arity gives exact defect one (including the two-input case), and anchor-preserving integral
  shears make every displayed coordinate and exponential transcendental.
- [`Schanuel/CanonicalAnchorTerminalDichotomy.lean`](./Schanuel/CanonicalAnchorTerminalDichotomy.lean)
  proves the exact last-step alternative.  Either the literal two-anchor field
  `Q(2*pi*I,e)` has transcendence degree one, or deleting the last complementary coordinate
  gives a sharp canonically anchored equality tuple and the full field is algebraic over that
  deletion field.  In particular both the missing input and its exponential are algebraic over
  the equality field.  This dichotomy is itself equivalent to failure of the conjecture.
- [`Schanuel/CanonicalAnchorRelativeTerminal.lean`](./Schanuel/CanonicalAnchorRelativeTerminal.lean)
  makes that alternative disjoint.  Either `(2*pi*I,e)` is algebraically dependent, or it is
  algebraically independent and a positive terminal witness exists.  In the second branch the
  deletion field has relative transcendence degree exactly `n` over the anchor field for `n`
  complementary inputs, while the final input and exponential still form an algebraic extension.
- [`Schanuel/ConjugationStableNormalForm.lean`](./Schanuel/ConjugationStableNormalForm.lean)
  formalizes the field-theoretic amplification behind conjugation stability.  It proves
  transcendence-degree submodularity for the intersection and compositum of intermediate fields,
  exact identities for conjugated and joined graph fields, and construction of a canonical basis
  for the stable closure.  A checked gap theorem turns the requisite intersection degree into a
  stable failing family.
- [`Schanuel/ConjugationStableMinimalFailure.lean`](./Schanuel/ConjugationStableMinimalFailure.lean)
  completes the stable normal form.  A common integer scale puts the graph field of the rational
  span intersection literally inside both conjugate graph fields; Grassmann dimension then
  amplifies every least nonstable failure to a stable one.  Symmetrized rational functionals give
  invariant codimension-one deletions, and stable least arity plus anchor-preserving shears proves
  that failure is exactly equivalent to a fully transcendental, canonical, conjugation-stable
  defect-one witness.
- [`Schanuel/ConjugationStableTerminal.lean`](./Schanuel/ConjugationStableTerminal.lean)
  gives the stable terminal dichotomy.  A positive least stable failure has a sharp invariant
  codimension-one deletion; after one common integral scale, its graph field embeds literally in
  the full field with equal transcendence degree, so the full field and an omitted input-output
  pair are algebraic over it.  A separate checked lemma selects the complementary direction as
  an actual real or purely imaginary conjugation eigenvector.
- [`Schanuel/MinimalCounterexampleRationalBasis.lean`](./Schanuel/MinimalCounterexampleRationalBasis.lean)
  combines that result with rational-basis invariance: every rational hyperplane projection of
  a first failure has the same transcendence degree as the full family, which is algebraic over
  the projection field after the chosen rational basis change.
- [`Schanuel/MinimalCounterexampleUniformBoundary.lean`](./Schanuel/MinimalCounterexampleUniformBoundary.lean)
  combines least-arity defect one with the checked integral-shear trichotomy: any global failure
  has a defect-one witness whose coordinates are all transcendental and whose exponentials are
  uniformly either all algebraic or all transcendental. It also proves the converse, so the
  existence of such a first uniform-boundary witness is exactly equivalent to failure of the
  full conjecture.
- [`Schanuel/LindemannAttempt.lean`](./Schanuel/LindemannAttempt.lean),
  [`Schanuel/LindemannIntegralReduction.lean`](./Schanuel/LindemannIntegralReduction.lean), and
  [`Schanuel/LindemannDenominators.lean`](./Schanuel/LindemannDenominators.lean) package Mathlib's
  analytic approximation theorem, the integral-exponent reduction, and denominator estimates.
- [`Schanuel/GaloisStableRelation.lean`](./Schanuel/GaloisStableRelation.lean),
  [`Schanuel/GaloisDescent.lean`](./Schanuel/GaloisDescent.lean), and
  [`Schanuel/GaloisStableArithmetic.lean`](./Schanuel/GaloisStableArithmetic.lean) construct a
  Galois-stable formal exponential relation and prove that its integral weighted auxiliary sum
  descends to an ordinary integer. No field automorphism is asserted to commute with analytic
  exponentiation.
- [`Schanuel/LindemannStableEndpoint.lean`](./Schanuel/LindemannStableEndpoint.lean) proves the
  modular nonvanishing and factorial-decay contradiction for any stable integral relation.
- [`Schanuel/GaloisStableAnalytic2.lean`](./Schanuel/GaloisStableAnalytic2.lean) connects the
  endpoint to an arbitrary algebraic complex exponent. It proves, without extra hypotheses,
  `HermiteLindemannStatement` and `OneDimensionalConjecture`.
- [`Schanuel/DistinctFrequencies.lean`](./Schanuel/DistinctFrequencies.lean) proves injectivity of
  nonnegative integral frequencies for a rationally linearly independent family.
- [`Schanuel/RationalScaling.lean`](./Schanuel/RationalScaling.lean) contains supporting
  integrality lemmas and proves that positive rational scaling preserves the generated
  transcendence degree.
- [`Schanuel/FractionAlgebraicIndependence.lean`](./Schanuel/FractionAlgebraicIndependence.lean)
  upgrades algebraic independence from an integral domain to its fraction field.
- [`Schanuel/AlgebraicInputs.lean`](./Schanuel/AlgebraicInputs.lean) uses the multivariate stable
  relation to prove algebraic independence of the exponentials for algebraic-integer inputs, and
  then uses common scaling to prove `Bound` (indeed exact transcendence degree `n`) for every
  rationally linearly independent family of algebraic complex inputs.
- [`Schanuel/RelativeDescent.lean`](./Schanuel/RelativeDescent.lean) splits the total
  transcendence degree into the coordinate and relative exponential contributions and records
  precise obstructions to specialization preserving the exponential graph.
- [`Schanuel/ConfluentVandermonde.lean`](./Schanuel/ConfluentVandermonde.lean) proves the sharp
  repeated-node polynomial zero estimate used in the audited auxiliary-function counts.
- [`Schanuel/MixedObstruction.lean`](./Schanuel/MixedObstruction.lean) proves that the bound for
  the linearly independent family `(log 2, log 2 + 1)` is exactly algebraic independence of
  `(log 2, e)`.
- [`Schanuel/IteratedExponentialBoundary.lean`](./Schanuel/IteratedExponentialBoundary.lean)
  proves that, for nonzero algebraic `a`, the bound for `(a, exp a)` is exactly algebraic
  independence of `(exp a, exp (exp a))` and identifies why finite Galois support stops there.
- [`Schanuel/AlgebraicExponentialInputs.lean`](./Schanuel/AlgebraicExponentialInputs.lean) proves
  that when every `exp (z i)` is algebraic, the desired bound is exactly algebraic independence
  of the coordinate family `z`.
- [`Schanuel/PeriodLogBoundary.lean`](./Schanuel/PeriodLogBoundary.lean) checks the concrete
  all-algebraic-exponential family `(log 2, 2*pi*I)` and reduces its bound exactly to algebraic
  independence of those two logarithmic/period coordinates.
- [`Schanuel/IntegerShear.lean`](./Schanuel/IntegerShear.lean) proves that fixed-pivot integral
  shears preserve linear independence and the generated field exactly.  Consequently every
  linearly independent tuple is either all algebraic or has a same-field all-transcendental shear.
- [`Schanuel/TranscendentalReduction.lean`](./Schanuel/TranscendentalReduction.lean) packages this
  with the all-algebraic theorem and proves that the full conjecture is equivalent to its
  restriction to families whose every coordinate is transcendental.
- [`Schanuel/FullyTranscendentalReduction.lean`](./Schanuel/FullyTranscendentalReduction.lean)
  refines the normal form with `{0,1,2}` shears: the remaining target is exactly the conjunction
  of the all-transcendental-coordinate/all-algebraic-exponential branch and the branch where all
  `2n` displayed values are individually transcendental.
- [`Schanuel/FullyTranscendentalAugmentation.lean`](./Schanuel/FullyTranscendentalAugmentation.lean)
  eliminates the residual algebraic-exponential branch by adjoining `1` and applying two explicit
  integral shears.  The resulting tuple has every coordinate and exponential transcendental, its
  field is exactly the old field with `e` adjoined, and one-step trdeg descent proves that the full
  conjecture is equivalent to the fully transcendental restriction alone.
- [`Schanuel/FullyTranscendentalMixedBoundary.lean`](./Schanuel/FullyTranscendentalMixedBoundary.lean)
  gives an explicit fully transcendental presentation of the mixed stress: both coordinates and
  both exponentials of `(2*log 2+1, log 2+1)` are transcendental, while its bound is still exactly
  algebraic independence of `(log 2,e)`.
- [`Schanuel/FullyTranscendentalPeriodBoundary.lean`](./Schanuel/FullyTranscendentalPeriodBoundary.lean)
  checks the fully transcendental duplicate-value family `(1+2*pi*I,1+4*pi*I)`: both
  exponentials equal `e`, and its bound is exactly algebraic independence of `(2*pi*I,e)`.
- [`Schanuel/AlgebraicRanks.lean`](./Schanuel/AlgebraicRanks.lean) defines the rational coefficient
  subspaces giving algebraic additive values and algebraic exponential values.  Hermite--Lindemann
  makes them disjoint and yields a checked complementary quotient-rank inequality.
- [`Schanuel/RationalBasisInvariance.lean`](./Schanuel/RationalBasisInvariance.lean) proves that
  every invertible rational matrix preserves rational linear independence, the transcendence
  degree of the coordinate-exponential generated field, and `Bound`.  Denominator clearing gives
  integer transforms in both directions, so the fields are mutually algebraic even when they are
  not concretely equal.
- [`Schanuel/ControlledMultipliers.lean`](./Schanuel/ControlledMultipliers.lean) defines the
  rational space of complex scalars preserving a finite rational subspace.  Evaluation at a
  nonzero vector bounds its dimension by that of the original space; controlled multiplier
  exponentials are integral over the original generated field after denominator clearing.
- [`Schanuel/ControlledMultiplierBridge.lean`](./Schanuel/ControlledMultiplierBridge.lean) gives
  this multiplier space its natural rational-subalgebra structure, represents multiplication on
  a finitely generated rational span by an explicit rational matrix, and applies the preceding
  denominator-clearing result directly from the intrinsic span-preservation hypothesis.
- [`Schanuel/CanonicalHermiteTail.lean`](./Schanuel/CanonicalHermiteTail.lean) makes explicit the
  factorial-divided derivative tail hidden in Mathlib's existential approximation witnesses.  It
  proves the canonical root-evaluation, degree, and zero-boundary normalization identities.
- [`Schanuel/CanonicalHermiteApproximation.lean`](./Schanuel/CanonicalHermiteApproximation.lean)
  proves that this explicit tail and numerator satisfy the full simultaneous analytic estimate,
  prime nondivisibility, degree bound, and exact congruence normalization.  It rederives the
  private analytic remainder bound using Mathlib's public integral identity.

The exact remaining scope and the audit of attempted higher-dimensional routes are recorded in
[`PROGRESS.md`](./PROGRESS.md). The unresolved part is arbitrary `n >= 2` with arbitrary complex
inputs; no theorem in the repository weakens or hides that requirement.

## Building

Mathlib and Lean are pinned to `v4.29.1`.

```sh
nix develop -c lake build
```

The registered modules build with no `sorry`, `admit`, or project axiom. The only current output
is harmless linter advice.
