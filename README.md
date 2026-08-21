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
