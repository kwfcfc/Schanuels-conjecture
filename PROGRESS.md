# Checked progress toward `PROMPT.md`

## Target and current boundary

The target is the exact finite-family statement in [`PROMPT.md`](./PROMPT.md): for every
`n` and every rationally linearly independent `z : Fin n -> C`, prove

```text
Cardinal.mk (Fin n) <= Algebra.trdeg Q (generatedField z).
```

The repository does not yet contain a proof of `Schanuel.Conjecture`. It now does contain a
complete checked proof of the one-dimensional case, including Hermite--Lindemann, but that result
does not discharge the arbitrary-dimensional target.

No registered source file contains `sorry`, `admit`, or a project axiom.

## Fully checked results

### Statement and structural reductions

- [`Schanuel.lean`](./Schanuel.lean) defines `expPair`, `generatedField`, `Bound`, and `Conjecture`.
- A linearly independent `Fin n` family has rational span of finrank `n`.
- The empty-family bound, the unconditional upper bound `trdeg <= 2n`, subfamily monotonicity,
  and the bounds obtained when either displayed half is already algebraically independent are
  proved.
- [`Schanuel/Structural.lean`](./Schanuel/Structural.lean) proves that `Bound z` is equivalent to
  selecting `n` algebraically independent members among the `2n` displayed coordinates and
  exponentials.
- [`Schanuel/MinimalCounterexample.lean`](./Schanuel/MinimalCounterexample.lean) proves the exact
  minimal-failure shape: if the bound holds for every independent `n`-tuple but fails for an
  independent `(n+1)`-tuple, then the latter generated field has transcendence degree exactly
  `n`.  Thus a first counterexample is necessarily a codimension-one deficit, not an arbitrary
  collapse.  The file also proves that restriction along every injection `Fin n -> Fin (n+1)`
  has the same transcendence degree `n`, and that the full generated field is algebraic over
  every such restricted field; no deleted coordinate lowers the field dimension. Defining a
  defect-one family by this exact equality, the same file uses least-arity well-ordering to
  construct such a minimal witness from any failure, and proves by induction that excluding all
  independent defect-one families is equivalent to the full `Schanuel.Conjecture`.
- [`Schanuel/MinimalCounterexampleRationalBasis.lean`](./Schanuel/MinimalCounterexampleRationalBasis.lean)
  combines this with the checked invariance under `GL_n(Q)`: restriction of every invertible
  rational transform along `Fin n -> Fin (n+1)` still has transcendence degree exactly `n`, and
  the transformed full field is algebraic over every such rational hyperplane projection.
- [`Schanuel/MinimalCounterexampleUniformBoundary.lean`](./Schanuel/MinimalCounterexampleUniformBoundary.lean)
  combines least-arity defect one with the exact `{0,1,2}` integral-shear trichotomy.  Every
  global failure therefore has a defect-one witness with all coordinates transcendental and with
  its exponentials uniformly either all algebraic or all transcendental.  Conversely, the
  failure carried by such a witness immediately refutes the full conjecture, yielding an exact
  equivalence with this uniform first-failure normal form.
- [`Schanuel/FullyTranscendentalAugmentation.lean`](./Schanuel/FullyTranscendentalAugmentation.lean)
  adjoins `1` to the residual all-algebraic-exponential branch and applies two integral shears.
  The resulting tuple has every coordinate and exponential transcendental, while its generated
  field is the old field with only `exp 1` adjoined.  The one-unit arity and transcendence-degree
  bookkeeping proves the exact equivalence
  `Conjecture ↔ FullyTranscendentalConjecture`.
- [`Schanuel/MinimalCounterexampleFullyTranscendental.lean`](./Schanuel/MinimalCounterexampleFullyTranscendental.lean)
  performs least-arity descent entirely inside that equivalent restriction.  Failure is exactly
  equivalent to a fully transcendental independent defect-one family of arity at least two.
  Every one-coordinate deletion of the selected restricted-minimal witness has the same
  transcendence degree, and the full generated field is algebraic over every deletion field.
- [`Schanuel/MinimalCounterexamplePeriodBearing.lean`](./Schanuel/MinimalCounterexamplePeriodBearing.lean)
  strengthens this equivalence using the standard analytic period.  Failure is exactly equivalent
  to a fully transcendental independent defect-one family of arity at least two whose rational
  input span contains `2*pi*I`.  If the period is algebraic over the old witness field, one
  coordinate is replaced and deletion algebraicity preserves the defect; if it is transcendental,
  one period shift is appended and the transcendence degree rises exactly once.
- [`Schanuel/CriticalPeriodEquality.lean`](./Schanuel/CriticalPeriodEquality.lean) formalizes
  `(CE1)--(CE15)`: `¬ Conjecture` is equivalent to a positive fully transcendental independent
  equality tuple `v` with `trdeg Q(v,exp v)=len(v)`, with the standard period outside its rational
  span but algebraic over its generated field.  A generic basis-coordinate lemma selects the
  deletion in the algebraic-period branch.  In the transcendental-period branch the last
  coordinate is replaced by `omega+z_i`; a checked shear proves independence and period exclusion,
  while a two-sided tower squeeze proves the exact one-unit transcendence-degree rise.  Conversely,
  adjoining `omega` gives an independent defect-one family because `exp(omega)=1`.
- [`Schanuel/AdjacentPeriodDeletion.lean`](./Schanuel/AdjacentPeriodDeletion.lean) proves that when
  two inputs differ by `2*pi*I`, deleting the second loses exactly the period: the full generated
  field is the deletion field with that one element adjoined.  Its relative transcendence degree
  is zero or one, with zero exactly when the period is algebraic over the deletion.  For a fully
  transcendental defect-one family this gives the checked dichotomy between a sharp deletion and
  a smaller fully transcendental defect-one family.
- [`Schanuel/AdjacentPeriodNormalForm.lean`](./Schanuel/AdjacentPeriodNormalForm.lean) completes
  the exact equivalence between failure and an adjacent-period fully transcendental defect-one
  family.  After permuting a nonzero period coefficient into position `1`, the checked matrix has
  rows `e_0+k*c`, `e_0+(k+1)*c`, and `e_i` for `i>=2`, and determinant `c_1`.  One of `k=0` or
  `k=2` makes both consecutive period shifts transcendental; rational-basis invariance preserves
  linear independence and defect one.
- [`Schanuel/CanonicalAnchorNormalForm.lean`](./Schanuel/CanonicalAnchorNormalForm.lean) formalizes
  `(CA1)--(CA6)`.  It proves rectangular rational-family Kummer monotonicity, extends the fixed
  independent anchor `(1+omega,1+2*omega)` to a finite `Fin (n+2)` basis of any containing input
  span, chooses a least anchored failure, and proves exact defect one without excluding `n=0`.
  Two simultaneous integral shears fix both anchors and make every coordinate and exponential
  transcendental.  Thus failure is exactly equivalent to the literal canonical-anchor fully
  transcendental defect-one normal form.
- [`Schanuel/CanonicalAnchorTerminalDichotomy.lean`](./Schanuel/CanonicalAnchorTerminalDichotomy.lean)
  extracts the exact terminal alternative from least anchored arity.  At zero complementary
  arity the field `Q(2*pi*I,e)` has transcendence degree one.  At positive arity, deleting the
  final complement gives a canonically anchored tuple whose transcendence degree equals its full
  length, while the original defect-one field is algebraic over the deletion field.  The module
  explicitly records that both the missing input and its exponential are algebraic over the
  deletion field, and proves the two-branch dichotomy equivalent to `¬ Conjecture`.
- [`Schanuel/CanonicalAnchorRelativeTerminal.lean`](./Schanuel/CanonicalAnchorRelativeTerminal.lean)
  separates the anchor boundary from the higher-arity terminal branch.  It proves that the anchor
  field has degree one exactly when `(2*pi*I,e)` is algebraically dependent, and degree two when
  the pair is independent.  In the independent positive branch, a sharp deletion with `n`
  complementary inputs has relative transcendence degree exactly `n` over the anchor field.
  Thus failure is equivalently a disjoint choice between anchor dependence and a finite terminal
  graph extension over an independent anchor equality field.
- [`Schanuel/ConjugationStableNormalForm.lean`](./Schanuel/ConjugationStableNormalForm.lean)
  checks the arithmetic amplification layer used in `(CS4)--(CS9)`.  It proves submodularity of
  transcendence degree for intermediate-field intersection and compositum, exact conjugation and
  join identities for generated graph fields, a canonical-anchor basis of the stable closure,
  and a theorem turning the precise intersection-degree gap into a conjugation-stable failing
  basis.  The reverse implication from a stable canonical defect-one family to failure is also
  checked.
- [`Schanuel/ConjugationStableMinimalFailure.lean`](./Schanuel/ConjugationStableMinimalFailure.lean)
  completes the forward implication in `(CS4)--(CS9)`.  It formalizes common-denominator descent
  into the literal field intersection, the stable-closure dimension amplification, an invariant
  codimension-one hyperplane obtained by symmetrizing a rational functional, least stable arity,
  exact defect one, and a stability-preserving full-transcendence shear.  Its terminal theorem is
  the full equivalence with a conjugation-stable canonical fully transcendental defect-one family.
- [`Schanuel/ConjugationStableTerminal.lean`](./Schanuel/ConjugationStableTerminal.lean)
  formalizes the next stable endpoint.  It records a sharp stable codimension-one deletion, clears
  its rational denominators once to obtain a literal graph-field inclusion, proves the full field
  algebraic over that deletion, and exposes an omitted algebraic input/exponential pair.  Its
  terminal dichotomy is exactly equivalent to failure; separately, the missing direction is
  shown selectable as a genuine real or purely imaginary conjugation eigenvector.
- [`Schanuel/ConjugationStableSectorBoundary.lean`](./Schanuel/ConjugationStableSectorBoundary.lean)
  formalizes the exact rational `+1`/`-1` eigenspace decomposition of a stable subspace.  It selects
  finite sector bases beginning with `1` and the standard period, proves their appended family is a
  basis of the full space, and identifies its graph field with the sector-field compositum.  A
  common integral scale compares that compositum to any original spanning graph field.  At a least
  stable failure every proper stable anchored subspace satisfies its bound, while a defect-one
  witness gives compositum transcendence degree exactly one below the total sector dimension;
  this deliberately makes no algebraic-disjointness claim.  Basis invariance is made explicit,
  and the real-sector-plus-period and one-plus-anti-fixed-sector families are each proved
  independent, anchored, stable, proper when the opposite complement is nonzero, and subject to
  the least-failure Schanuel bound.  The singleton period and real-unit graph fields are each
  identified with a one-generator field; compositum submodularity and finite-cardinal cancellation
  then prove that the real and anti-fixed sector graph fields themselves have degree at least their
  respective sector dimensions.  These are the checked forms of `(CS12)--(CS13)`.
  The final combined theorem identifies the remaining obstruction exactly: when both sector
  complements are nonzero, both individual lower bounds hold and the compositum degree plus one
  equals the sum of the two sector dimensions.
- `OneDimensionalConjecture` is proved equivalent to `HermiteLindemannStatement`.

### Completed one-dimensional analytic argument

[`Schanuel/LindemannAttempt.lean`](./Schanuel/LindemannAttempt.lean) specializes Mathlib's
`LindemannWeierstrass.exp_polynomial_approx`, normalizes a hypothetical polynomial relation in
`exp z`, and records the simultaneous factorial estimates. The older named
`LindemannArithmeticStep` is exactly equivalent to Hermite--Lindemann; it was never treated as a
smaller arithmetic lemma.

The missing arithmetic proof is now supplied by five modules:

1. [`Schanuel/LindemannIntegralReduction.lean`](./Schanuel/LindemannIntegralReduction.lean)
   reduces arbitrary algebraic exponents to algebraic integers by multiplying by a nonzero
   integer and using the exponential power identity.
2. [`Schanuel/GaloisStableRelation.lean`](./Schanuel/GaloisStableRelation.lean) encodes an
   exponential relation in `Z[K_add]`, multiplies all formal Galois translates, and then multiplies
   by exponent-reversal. The resulting relation is nonzero, remains analytically zero, is stable
   under every automorphism, and has positive constant coefficient (a sum of integer squares).
   This construction never claims that field automorphisms commute with analytic `exp`.
3. [`Schanuel/GaloisDescent.lean`](./Schanuel/GaloisDescent.lean) proves only safe algebraic
   equivariance: integer-polynomial evaluation and root transport. It also proves that a Galois-
   fixed algebraic integer in a finite Galois extension of `Q` is an ordinary integer.
4. [`Schanuel/GaloisStableArithmetic.lean`](./Schanuel/GaloisStableArithmetic.lean) proves integral
   support, integrality of the weighted polynomial-evaluation sum, invariance of that sum under
   the full Galois group, and its descent to an integer.
5. [`Schanuel/LindemannStableEndpoint.lean`](./Schanuel/LindemannStableEndpoint.lean) applies the
   simultaneous analytic approximation to every nonzero support exponent. It constructs
   `D = n*A(0) + p*m`, proves `D != 0` modulo `p`, rewrites `D` as a sum of approximation errors,
   and contradicts `1 <= |D| < 1` using factorial decay.

[`Schanuel/GaloisStableAnalytic2.lean`](./Schanuel/GaloisStableAnalytic2.lean) supplies the final
number-field bridge and proves, with no extra hypothesis:

```lean
lindemannArithmeticStep_of_galoisStableEndpoint : LindemannArithmeticStep
hermiteLindemann_of_galoisStableEndpoint : HermiteLindemannStatement
oneDimensionalConjecture_of_galoisStableEndpoint : OneDimensionalConjecture
```

An adversarial audit checked the reflection coefficient, the finite Galois closure construction,
the support reindexing, and the absence of exponential equivariance. `#print axioms` on the core
theorems reports only Lean's standard `propext`, `Classical.choice`, and `Quot.sound`.

### Other reusable lemmas

- [`Schanuel/LindemannDenominators.lean`](./Schanuel/LindemannDenominators.lean) proves a uniform
  common integral scale for a finite algebraic set and shows that its exponential growth is
  absorbed by factorial decay.
- [`Schanuel/DistinctFrequencies.lean`](./Schanuel/DistinctFrequencies.lean) proves that distinct
  nonnegative multi-indices give distinct frequencies for a rationally linearly independent
  family.
- [`Schanuel/RationalScaling.lean`](./Schanuel/RationalScaling.lean) proves mutual integrality under
  positive rational scaling and the resulting equality of generated transcendence degrees.
- [`Schanuel/FractionAlgebraicIndependence.lean`](./Schanuel/FractionAlgebraicIndependence.lean)
  proves that algebraic independence over an integral domain extends to a fraction field.
- [`Schanuel/AlgebraicInputs.lean`](./Schanuel/AlgebraicInputs.lean) encodes multivariate integer
  polynomials by formal additive frequencies and applies the stable endpoint. It proves that the
  exponentials of algebraic-integer, rationally linearly independent inputs are algebraically
  independent over `Q`, and concludes `Bound` and exact transcendence degree `n` for arbitrary
  algebraic inputs after a common positive rational scaling.
- [`Schanuel/RelativeDescent.lean`](./Schanuel/RelativeDescent.lean) proves the exact coordinate/
  relative transcendence-degree split, generation by the exponentials over the coordinate field,
  and the sharp relative upper bound `<= n`.
- [`Schanuel/ConfluentVandermonde.lean`](./Schanuel/ConfluentVandermonde.lean) formalizes the sharp
  repeated-node polynomial zero estimate and its threshold example.
- [`Schanuel/MixedObstruction.lean`](./Schanuel/MixedObstruction.lean) gives a checked elementary
  mixed boundary: `(log 2, log 2 + 1)` is rationally linearly independent, its generated field is
  `Q(log 2, e)`, and its Schanuel bound is equivalent to algebraic independence of `(log 2, e)`.
- [`Schanuel/IteratedExponentialBoundary.lean`](./Schanuel/IteratedExponentialBoundary.lean) gives
  a second checked boundary: for nonzero algebraic `a`, the bound for `(a, exp a)` is equivalent
  to algebraic independence of `(exp a, exp (exp a))`.  The corresponding formal frequencies
  `m*a + n*exp a` are transcendental when `n != 0`, so they cannot enter the finite-number-field
  stable endpoint.
- [`Schanuel/AlgebraicExponentialInputs.lean`](./Schanuel/AlgebraicExponentialInputs.lean) proves
  the exact opposite boundary to `AlgebraicInputs`: if every exponential value is algebraic, then
  `Bound z` is equivalent to algebraic independence of the coordinates `z`.  Thus the equality
  configurations consisting of logarithms of algebraic numbers retain the full relative problem.
- [`Schanuel/PeriodLogBoundary.lean`](./Schanuel/PeriodLogBoundary.lean) instantiates that theorem
  at the rationally independent pair `(log 2, 2*pi*I)`, whose exponential values are `(2,1)`.
  Its bound is exactly algebraic independence of `log 2` and the basic exponential period.
- [`Schanuel/IntegerShear.lean`](./Schanuel/IntegerShear.lean) proves exact invariance of rational
  linear independence and `generatedField` under simultaneous fixed-pivot integral shears.  If a
  tuple has any transcendental coordinate, adding that pivot to every algebraic coordinate makes
  all coordinates transcendental without changing the field.  Together with `AlgebraicInputs`,
  this reduces the unresolved coordinate side to all-transcendental representatives.
- [`Schanuel/TranscendentalReduction.lean`](./Schanuel/TranscendentalReduction.lean) states the
  resulting exact equivalence `Conjecture <-> AllTranscendentalConjecture`; this is a scope
  reduction, not a proof of the remaining all-transcendental branch.
- [`Schanuel/FullyTranscendentalReduction.lean`](./Schanuel/FullyTranscendentalReduction.lean)
  uses a transcendental-exponential pivot and coefficients in `{0,1,2}` to avoid both coordinate
  cancellation and algebraic exponential values.  It proves the exact trichotomy and the iff
  between `Conjecture` and the conjunction of `TranscendentalAlgebraicExpConjecture` with
  `FullyTranscendentalConjecture`.  Both restricted branches remain theorem-strength targets.
- [`Schanuel/FullyTranscendentalMixedBoundary.lean`](./Schanuel/FullyTranscendentalMixedBoundary.lean)
  sharpens the checked mixed stress by an explicit integral shear.  Every coordinate and every
  exponential of `(2*log 2+1, log 2+1)` is transcendental, its generated field is still
  `Q(log 2,e)`, and its bound is exactly algebraic independence of `(log 2,e)`.  Thus individual
  transcendence of all displayed values does not make the remaining uniform branch generic.
- [`Schanuel/FullyTranscendentalPeriodBoundary.lean`](./Schanuel/FullyTranscendentalPeriodBoundary.lean)
  checks the duplicate-value period stress `(1+2*pi*I,1+4*pi*I)`.  Both coordinates and both
  exponential values are transcendental, the two exponential values coincide at `e`, and the
  Schanuel bound is exactly algebraic independence of `(2*pi*I,e)`.  The proof includes a checked
  Hermite--Lindemann derivation of transcendence of the period and an exact generated-field
  identity with `Q(2*pi*I,e)`.
- [`Schanuel/AlgebraicRanks.lean`](./Schanuel/AlgebraicRanks.lean) formalizes the additive and
  multiplicative algebraic coefficient kernels.  Their intersection is zero by the checked
  Hermite--Lindemann theorem, so their dimensions sum to at most `n` and the two complementary
  quotient ranks sum to at least `n`.  The matroid audit below explains why this linear-rank
  statement alone does not bound transcendence degree.
- [`Schanuel/RationalBasisInvariance.lean`](./Schanuel/RationalBasisInvariance.lean) formalizes
  arbitrary invertible rational coordinate changes.  It proves linear-independence invariance,
  equality of coordinate fields, mutual algebraicity of the full generated fields after common
  denominator clearing, equality of transcendence degrees, and invariance of `Bound`.
- [`Schanuel/ControlledMultipliers.lean`](./Schanuel/ControlledMultipliers.lean) formalizes the
  rational multiplier space preserving a finite subspace of `C`.  Evaluation at a nonzero vector
  injects it into the original subspace, giving the rank-at-most-two obstruction for pairs; it
  also proves that exponentials obtained from controlled rational combinations are integral and
  algebraic over the original generated field.
- [`Schanuel/ControlledMultiplierBridge.lean`](./Schanuel/ControlledMultiplierBridge.lean)
  upgrades the controlled multipliers to a rational subalgebra and constructs, row by row, the
  rational matrix representing multiplication on any finite spanning family.  It therefore
  derives integrality and algebraicity of every controlled exponential directly from intrinsic
  span preservation, including for linearly dependent and empty families.
- [`Schanuel/CanonicalHermiteTail.lean`](./Schanuel/CanonicalHermiteTail.lean) constructs the
  canonical integer polynomial `G_p(h)=(1/p!)*sum_(k>=p) h^(k)` coefficientwise.  It proves its
  degree bound, its evaluation identity at every root of multiplicity `p`, and, for
  `h=X^(p-1)*f^p`, the exact normalization
  `n=f(0)^p+p*G_p(0)`.  This exposes a useful witness hidden by Mathlib's existential API.
- [`Schanuel/CanonicalHermiteApproximation.lean`](./Schanuel/CanonicalHermiteApproximation.lean)
  proves the full public canonical approximation theorem: that explicit `G_p` and `n` satisfy
  prime nondivisibility, the sharp degree bound, the exact normalization, and the simultaneous
  root error `c^p/(p-1)!`.  The analytic bound is rederived from Mathlib's public integral identity,
  so it does not depend on or identify the two opaque witnesses in the upstream theorem.  A
  separate audit checked constant polynomials, negative constant terms, `p=2`, natural-degree
  subtraction, all casts, and the empty root set; the theorem recovers the complete upstream
  approximation interface and uses only Lean's standard axioms.

## Higher-dimensional approach registry

These audits are negative results about particular mechanisms, not assumptions in the formal
development.

### Auxiliary polynomials and multiplicity estimates

For the box of monomials `X^a Y^b` with coordinatewise degrees at most `R`, the exact
one-coordinate jet determinant is the confluent Vandermonde determinant

```text
exp(m*t0*sum lambda_b) * product(a!) * product_{b<c}(lambda_c-lambda_b)^(m^2),
```

where `m = D+1`. Tensoring gives the sharp zero threshold
`sum_i ((D_i+1)(E_i+1)-1)`. A Hilbert/Siegel count over
`A = Q[z_i, exp z_i]` of transcendence degree `d` produces only
`T = O(R^(2-d/n))` jets, whereas the sharp zero estimate needs order `R^2`. The deficit is the
factor `R^(d/n)`; at the threshold, dimension counting cannot force vanishing.

Using the whole lattice of low-jet auxiliaries does not recover that factor.  The coefficient
lattice has rank `N` of order `R^(2n)`, while jets below `T` expand to at most
`U` of order `R^d*T^n` rational scalar rows.  Its kernel rank is only `N-rank(J_T)`; at the sharp
leaf threshold `T=R^2`, the confluent zero estimate makes this rank zero although there are
`R^d*N` scalar conditions.  Bombieri--Vaaler/Minkowski bounds distribute the kernel covolume among
successive minima with geometric-mean cost proportional to `rank(J_T)/(N-rank(J_T))`, which blows
up as the count boundary is approached.  Products of `ell` auxiliaries have order `ell*T` but
effective degree `ell*R` and threshold `(ell*R)^2`; Wronskians and Plücker determinants have the
same worsening ratio and multiply the successive-minimum heights.  Divided jets move
`log(k!)` from the archimedean norm into the finite-place covolume, cancelling term by term in
every exterior power.  Thus many short vectors or favorable lattice bases change heights but not
the missing rank/high-jet injectivity.

[`Schanuel/DistinctFrequencies.lean`](./Schanuel/DistinctFrequencies.lean) formalizes the frequency
injectivity input to this calculation. The determinant and Hilbert estimates have not yet been
formalized as repository theorems.

Replacing jets by scalar finite differences does not change the count.  For a sequence
`sum_j P_j(k) * lambda_j^k` with distinct nonzero nodes, the first `sum_j degBound(P_j)` finite
differences form the same confluent-Vandermonde system as the first values.  On a rationally
independent tuple, adjoining suitable prime-th roots separates the nodes and is only an algebraic
extension, but scalar restriction still collapses all coordinate monomials of the same total
degree.  More decisively, over a transcendence base the congruence output has the form
`c + p*M(T)` in `Z[T]`, not a nonzero integer.  At a fixed transcendental value `T = tau`, density
of `Z + Z*tau` makes such nonzero congruence classes arbitrarily small, so there is no replacement
for the endpoint inequality `1 <= |D|`.

Powering a finite exponential relation creates multiplicity but spends it exactly on new support.
If `F(t)=sum_(u in A)c_u*exp(tu)` has `s` distinct frequencies and order `r` at `t=1`, the
Vandermonde matrix gives `r<=s-1`; for every `M`,
`ord_1(F^M)=M*r<=|supp(mu^(*M))|-1`.  A binomial relation attains equality with `M+1`
frequencies and order `M`, and its first nonzero normalized jet is not small.  Applying Hermite
approximation to the expanded convolution gives one error per enlarged support term, not `M`
independent errors; raising an already-small auxiliary to the `M`-th power raises its height,
degree, and nonvanishing by the same power.  Reflection and Galois orbit products enlarge support
without multiplying the chosen analytic zero, while finite Fourier powering preserves rather than
enlarges the transform's zero set.  Transcendental frequency differences also remain
transcendental under convolution, so powering never enters the number-field endpoint.

Difference--differential operators cannot propagate the one known zero.  An exponential
polynomial `sum p_lambda(t)*exp(lambda*t)` has a constant-coefficient Ore annihilator of order
`sum(deg p_lambda+1)`, and its full jet at one point is freely specifiable; imposing the value zero
leaves every other derivative unconstrained.  For the exact stress `F(t)=exp((log 2)*t)-2`,
`F^(k)(1)=2*(log 2)^k`, while a step `1/q` gives
`Delta^M F(1)=2*(2^(1/q)-1)^M`; the selected `q^-M` gain has norm one after all Kummer conjugates.
Multiplying `M` translates manufactures `M` zeros but also at least `M+1` modes (and quadratic
Ore complexity for mixed polynomial-prefactor relations).  Kummer traces delete the nonzero
frequency characters and hence the cancellation that made the original value zero.  Operators,
shifts, and traces therefore require rather than generate the missing derivative/translated
relations.

Reflection cannot replace discreteness by positivity.  A translation kernel `g(u-v)` that is
positive semidefinite on the real line must satisfy `|g(t)|<=g(0)`, whereas the symmetric part of
the exponential is `cosh t>1`.  Already on `{0,a}`, any PSD kernel approximating `exp` at
`0,+a,-a` has uniform error at least `(cosh(a)-1)/2`.  On complex support a holomorphic entire
globally positive-definite translation kernel is bounded and hence constant.  Exact integer PSD
kernels can be built on finite algebraic support by squaring the minimal polynomials of all
nonzero differences; they vanish off the diagonal and retain mod-`p` residues, but therefore
discard the exponential approximation entirely.  Adding enough of this diagonal kernel to repair
positivity incurs exactly the fixed error lower bound above.

For the actual reflected auxiliary, the moment matrix is symmetric bilinear rather than
Hermitian: its generating series is `F(t)*F(-t)`, not `|F(t)|^2`.  At `a=log 2`, the valid relation
`-2+3*exp(a)-exp(2a)=0` makes the quadratic Taylor moment `-a^2`, while the two-term relation at the
same point gives the opposite sign.  Multiplying an approximation by its complex conjugate gives
a true Gram square, but it is a two-variable kernel and no longer has the nonzero mod-`p` constant
expression; it is merely a small nonnegative transcendental value with no lower bound.
The sign is not even invariant under the Hermite API: adding `C*f` to an approximant, where `f`
is the common root polynomial, preserves every nonzero-support value and every analytic estimate,
but shifts the full reflected moment by `C*A(0)*f(0)` through arbitrary signs while leaving the
actual endpoint expression unchanged.

Choosing the canonical witness from `CanonicalHermiteTail` removes that normalization freedom but
still gives no positivity.  It makes `n-p*G_p(0)=f(0)^p` exactly.  Nevertheless, at the stress
identity `exp(log 2)=2`, the canonical expressions from the two-term relation and its square take
opposite signs as the harmless parameter in `f=X-c` changes; the reflected-square expression also
changes sign between explicit `c` values.  These calculations diagnose the sign functional only:
they are not applications of Mathlib's approximation theorem, because `log 2` is transcendental
and hence is not a root of a nonzero integer polynomial.  Thus even a canonical normalization
controls the value at zero but supplies neither a PSD kernel nor a lower bound at translated
support points.

Squaring a real relation changes differences to sums and makes the exact kernel
`exp(u_i+u_j)` rank-one positive, but polynomial approximation again loses that structure.  A
Hankel kernel `g(s+t)` that is PSD on every finite real support is exponentially convex; a
globally Hankel-PSD polynomial is necessarily constant.  For the integer-normalized Taylor
approximants, squaring `exp(log 2)-2=0` gives a negative auxiliary moment at every sufficiently
large truncation, while squaring `-2+3*exp(a)-exp(2a)=0` makes the sign change with truncation
order.  Positive exponential mixtures are no longer integer polynomials and can make the
quadratic value arbitrarily small anyway.  On complex support the sum kernel is bilinear
`a*a^T`, not Hermitian `a*a*`; inserting conjugation breaks the one-variable polynomial and
mod-`p` construction.

The exact canonical normalization also admits no support-vanishing correction that repairs
positivity.  If `H in Z[X]` vanishes on the nonzero convolution support, its possible values at
zero form the lattice `M_T(0)*Z`, where `M_T` is the primitive product of the distinct minimal
polynomials of that support.  Replacing the canonical tail by `G_p+H` changes a reflected
difference kernel only by a diagonal scalar and a squared-sum kernel only on the entries whose
node sum is zero;
the simultaneous change from `f(0)^p` to `f(0)^p-p*H(0)` leaves the endpoint expression exactly
invariant.  Hence real positivity after correction is equivalent to the already-unknown sign of
the original endpoint, while the integral lattice constraint is strictly stronger.

There is an explicit canonical algebraic-support matrix obstruction.  For nodes `(-1,0,1)`,
`f=(X^2-1)*(X^2-4)`, and `p=5`, the exact tail values at `-2,-1,0,1,2` make the reflected
`{-1,1}` principal block indefinite for every admissible correction
`H(0) in 4*Z` with `f(0)^p-5*H(0)>0`.  For the squared-sum matrix, its principal-minor conditions
would imply `B^4<=A^3*E`, whereas the exact integer difference `B^4-A^3*E` is positive.  Explicit
integer coefficient vectors also make the normalized endpoint negative in both kernels.  These
vectors are deliberately not exponential relations—Lindemann--Weierstrass forbids such a relation
on algebraic nodes—but they prove that canonical normalization alone supplies no coefficient-
uniform PSD or sign theorem.  A valid positivity argument would need a new property of the
analytic relation, not the exposed Hermite identities.

Total positivity of the genuine real exponential kernel fixes crossing directions but supplies no
arithmetic magnitude.  For ordered real nodes and scales,
`det(exp(u_i*t_j))>0`; clustering `t_j=1+(j-1)*epsilon` makes this determinant asymptotic to
`exp(sum u_i)*epsilon^(n*(n-1)/2)*product_(i<j)(u_j-u_i)`, so making the translated relation
values small consumes exactly the full confluent-Vandermonde margin.  At `u_i=i*log 2`, the
two-scale determinant is `2*(2^(1/N)-1)`, which tends to zero at the ordered embedding although
its exact algebraic norm is `+/-2^N`.  Galois conjugates therefore erase the real sign advantage.
The relation `-2+3*2^t-4^t=-(2^t-1)*(2^t-2)` has two coefficient sign changes and exactly the two
real zeros `0,1`, attaining the variation-diminishing threshold.

There is not even a tuple-dependent quantitative crossing gap under the original independence
hypothesis.  For `N>=2`, the real nodes
`(1-log N, 1, 1+log((N+1)/N))` are rationally linearly independent, their exponentials satisfy the
coefficient relation `(1,1,-1)` at `t=1`, but the derivative there is
`-e*((log N)/N+((N+1)/N)*log((N+1)/N))`, which tends to zero.  Positive Taylor kernels retain total
positivity, but integer normalization multiplies their remainder by the factorial and loses the
gain; canonical Hermite tails have mixed coefficients and need not be totally positive.  Complex
or period-separated nodes can make the exponential minors vanish outright.  Thus Chebyshev and
total-positivity theory gives an exact zero count and sign, not a discrete endpoint.

Bargmann--Fock positivity has a sharper field-of-definition obstruction.  The Hermitian kernel
`K(z,w)=exp(z*conj(w))` is strictly positive definite, but for two nodes its determinant is
`exp(2*Re(z_1*conj(z_2)))*(exp(|z_1-z_2|^2)-1)`, which has no uniform positive gap.  At the mixed
stress `(1,log 2)` the Gram matrix is
`[[e,2],[2,exp((log 2)^2)]]`; positivity imports the new value `exp((log 2)^2)` before it gives an
inequality in `Q(e,log 2)`.  At `(log 2,2*pi*I)` the determinant is
`exp((log 2)^2+4*pi^2)-1`, with off-diagonal entries `exp(+/-2*pi*I*log 2)`, so it leaves the
period field even more drastically.  If one instead uses the feature vectors
`(1,y_i,...,y_i^(n-1))`, `y_i=exp(z_i)`, the Gram determinant stays in the joint conjugate field
but is only `|product_(i<j)(y_j-y_i)|^2`; it forgets every input coordinate.  It equals
`(e-2)^2` in the mixed stress and the exact integer `1` for the period outputs `(2,1)`, showing
that an arithmetic lower bound can hold while the desired input independence remains untouched.

The solved algebraic-input case saturates the missing norm quantitatively.  For odd `N`, take
`alpha_1=1`, `alpha_2=1+sqrt(2)/N`, put `y_j=exp(alpha_j)`, `M=N^2`, and
`r=exp(2/N^2)`.  These inputs are rationally independent and the exact Fock determinant is
`y_2^2*(r-1)`, asymptotic to `2*y_2^2/N^2`.  Over
`Qbar(y_1,exp(sqrt(2)/N))`, the element `r` has degree `M`, satisfies `r^M=e^2`, and
`Norm(r-1)=e^2-1`; hence
`Norm(det)=y_2^(2M)*(e^2-1)`.  The other Kummer branches compensate the small positive embedding
exactly.  Thus even where Lindemann--Weierstrass already proves the target, strict Gram positivity
plus relative norms supplies neither a subunit height exponent nor a new integer endpoint.

### Small-value criteria

Exact parameter comparison with Roy/Philippon-style criteria reaches the same boundary from the
other side. Dirichlet construction gives the exponent `beta + 2 - tau`, while the criterion needs
strictly more than that value (and, for `1 < tau < 2`, an additional positive term). Thus the
available construction and criterion have no overlapping parameter range.

The concrete mixed boundary `(log 2, e)` also defeats a combination of separate transcendence
measures.  If a relation has bidegree `(m,d)` and an integer polynomial `L` of degree `D` gives a
small value at `e`, the resultant in the second variable has degree at most `m*D` at `log 2` and
height raised to the `d`-th power.  Even with optimal one-variable measures, a contradiction would
require `D - d + 1 > d*m*D`; its deficit is `D*(m*d - 1) + (d - 1)`, and the sole equality case
`m=d=1` still misses the required strict inequality.  Swapping the variables gives the symmetric
deficit.  Thus Hermite--Padé plus independent one-variable measures cannot establish the needed
two-variable algebraic independence.

Coupling the two classical approximation sequences through structured determinants does not
improve this boundary.  The canonical Hermite rows `(N_p,A_p)` for `e` have error
`N_p*e-A_p=exp(-p log p+O(p))`, height `exp(p log p+O(p))`, and exact adjacent Casoratian
`N_p*A_(p+1)-A_p*N_(p+1)=(-1)^p*(2p+1)`.  The standard Padé rows for `log 2` have exponential
height/error with bases `3+2*sqrt 2`, while their adjacent Casoratian becomes the nonzero integer
`2*lcm(1,...,n)*lcm(1,...,n+1)/(n+1)` after denominator clearing.  For a hypothetical bilinear
relation `u^T*C*v=0`, `u=(1,e)` and `v=(1,log 2)`, the adjacent coupled `2 x 2` determinant factors
exactly as `det(C)` times these two Casoratians.  It is therefore an integer of magnitude at least
one, not a smaller mixed value.  Entrywise estimates already have incompatible requirements:
one error term needs `n > 1.31*p*log p`, while the other needs `n < 0.362*p*log p`.

The same rank count closes the higher rectangular variant.  If the two one-variable row families
have lengths `a` and `b`, a `k x k` coupled minor can contain each rank-one main term at most once,
so its lowest possible total error degree is `2*k-2`; since `k <= min(a,b)`, this is strictly less
than the `a*b-1` errors required by a determinant lower bound in the full tensor dimension.
Taking the full tensor determinant merely raises the two separate Casoratians to powers.  Even the
favorable exact Bézout identity for the direct logarithm approximants balances at its denominator;
using diagonal exponential Padé instead replaces the Casoratian by a high power of the relation's
linear factor, after which elimination restores the same degree and factorial cost.

Allowing rational rather than polynomial Padé auxiliaries only moves the missing factor into the
pole divisor.  The primitive diagonal exponential Padé polynomials
`A_n(X)=sum_(k<=n)(2n-k)!/(k!*(n-k)!)*X^k` and `B_n(X)=A_n(-X)` have height
`H_n=(2n)!/n!` and satisfy
`B_n(X)*exp X-A_n(X)=(-1)^n*X^(2n+1)/n!*integral_0^1 exp(tX)t^n(1-t)^n dt`.
At `X=1`, the integral linear form has size `asymp 1/(n*H_n)`, while the rational quotient error
looks like `1/(n*H_n^2)` only because `B_n(1)asymp H_n`.  Their exact adjacent Casoratian is
`A_n*B_(n+1)-A_(n+1)*B_n=2*(-1)^(n+1)*X^(2n+1)`, so clearing the two denominators restores the
nonzero integer `+/-2`.

Norming over algebraic support has the same divisor balance.  For `exp(a)=2`, the selected factor
`2*B_n(a)-A_n(a)` contributes one inverse `H_n`, each uncontrolled conjugate contributes one
positive `H_n`, and retaining the quotient merely places the missing product in `N(B_n(a))`.
For a hypothetical bilinear relation between `e` and `log 2`, substituting its Mobius expression
for `log 2` and multiplying by the `n`-th power of the linear denominator produces an integral
polynomial of height `H_n*C^n` and value only `H_n^(-1)*C^n`.  Pole collisions are measured by
the same resultant, and primitive common zeros cancel before use.  Function-field pushforward
expresses the obstruction invariantly: zeros and poles of a rational function have equal total
degree, and making a global/integral endpoint multiplies by the norm of the pole divisor, exactly
undoing the selected-place attenuation.

Sparse/toric resultants cannot lower this cost below one.  The unit-square bilinear relation gives
exactly `Res(R_n,R_(n+1))=+/-2*(ad-bc)/(n+1)`, and the unit-triangle trinomial already attains the
same normalized BKK mixed-volume boundary.  If the Newton support is a segment, an integral
monomial change leaves one equation in one torus monomial and a free complementary coordinate;
the mixed monomials `e^r*(log 2)^s` are themselves unresolved.  Otherwise every effective
normalized mixed volume is a positive integer at least one.  A degree-`D` norm scales Newton width
and coefficient homogeneity by `D` while only one conjugate factor is small.  Integral monomial
changes preserve the volume, rational changes pay a Kummer index, powers dilate the polytope, and
Galois symmetrization takes its Minkowski sum; nonzero extreme norm coefficients prevent
cancellation from shrinking it.  Sparsity can shorten a computation but yields no subunit
arithmetic exponent.

Coherence across infinitely many primes does not add a missing small factor.  Already the
canonical `f=X-1` forms `H_p(U)=N_p*U-A_p` have degree one, height
`exp(p log p+O(p))`, factorial-small value at the fixed transcendental point `U=e`, the exact
Frobenius congruence `H_p(U)=(-1)^p*U (mod p)`, and one fixed second-order holonomic recurrence in
`p`.  Their adjacent resultant is `+/- (2p+1)`; more generally the recurrence has positive
transfer coefficients, so every pair of distinct prime orders has a nonzero integer minor, while
every coefficient determinant of order at least three vanishes for dimensional reasons.  Under
a hypothetical bilinear relation `P(e,log 2)=0`, the induced degree-one polynomials in `log 2`
retain the same recurrence, congruence, and factorial smallness, and consecutive resultants become
`+/- det(P)*(2p+1)`.  Thus Frobenius congruences, P-recursiveness, all-prime smallness, and exact
determinants coexist at the boundary; their exterior powers yield growing integers, not an
accumulating contradiction.  As an auxiliary-data countermodel (not an exponential tuple),
multiplying these forms by `(1+T)^p` supplies the same complete package over a transcendence base,
even at an ultra-Liouville specialization independent of `e`;
the product over primes gains exactly as much logarithmic height as pointwise decay.  A singleton
has logarithmic capacity zero, so adelic capacity estimates favor these small polynomials rather
than prohibit them.

Trying to iterate the completed one-dimensional Hermite argument through the relative field has
an exact quantitative failure on the same pair.  For a hypothetical irreducible
`P(e,log 2)=0`, an explicit first Hermite polynomial `D_p(z)` has degree `p`, height
`exp(O(p log p))`, and logarithmic size `-p log p+O(p)` at roots with `exp z=2`, but
`+p log p+O(p)` at every other conjugate root.  Hence
`Res_Y(P(X,Y),D_p(Y))` has degree linear in `p` and at best only `exp(-O(p log p))` size at `e`.
A second Hermite step does produce a nonzero integer, but making its error small requires order
`q` at least quadratic in the first degree even for the sparsest support; its canonical numerator
then has logarithm of size `q log q`, overwhelming the first gain of order `p log p`.  The first
norm has descended only to `Q(e)`, and forcing the remaining transcendental residue to `Z` costs
more than was gained.

Approximating `log 2` inside `Q(2^(1/N))` exhibits the same cancellation without asymptotic
bookkeeping.  Truncating the logarithm at the positive real root gains `N^(-T)`, but the product
over all Kummer conjugates has nonnegative exponential rate because
`product_j |2^(1/N)*zeta_N^j-1|=1`; conjugates outside the unit disk exactly compensate the chosen
branch.  Clearing `lcm(1,...,T)` only increases the resultant height.  Thus recursive relative
Hermite descent and canonical-root approximation both restore the function-field norm
obstruction rather than bypassing it.

Approximating the input itself by tuples from the solved algebraic branch also meets an exact
height boundary.  In the mandatory bilinear stress, let a primitive quadratic polynomial of
height `H` have a root `alpha` near `log 2`, and eliminate `alpha` from the hypothetical relation.
The resultant is a degree-at-most-two integer polynomial at `e` of height `O(H)`.  The stable
Hermite endpoint, including avoidance of primes dividing its constant coefficient, gives only
`|P(e,alpha)| >= exp(-O(log H*log log H))` uniformly.  Under the ideal normalization where every
small prime is available, it improves to `H^(-3-o(1))`: degree two contributes `H^(-2)` and
removing the other conjugate costs one more height factor.  This is exactly the
Davenport--Schmidt quadratic-approximation exponent, with no strict room.  Elementary irrational
perturbations of rational approximants achieve much worse `H^(-1/2)` once their height and linear-
independence cost are counted.  Increasing algebraic degree enlarges the Galois support,
normalizer exponent, and prime-avoidance cost; ordinary density supplies no uniform rate that
overcomes the resulting lower bound.

A cloud of algebraic approximants cannot amplify the boundary.  For `M` points in one degree-`D`
field inside a disk of radius `epsilon`, clearing denominators in their Vandermonde and taking its
norm raises both the small radius and height cost to `S=M*(M-1)/2`; taking the `S`-th root removes
the entire sample gain.  Independent quadratic fields instead make the compositum degree grow
generically like `2^M`.  In the bilinear stress, the small values
`P(e,alpha_j)=(b+d*e)*(alpha_j-log 2)` lie in the span of `1,alpha_j`, so divided differences only
recover the nonsmall slope and higher interpolation determinants vanish.  Multiplying all
quadratic resultants produces a polynomial at `e` of degree `2M` and height `exp(O(M log H))`;
one joint Hermite endpoint then has normalizer cost `O(M^2 log H)`, while applying the endpoints
separately merely multiplies the `M` exponent-three boundary estimates.  Thus discriminants,
interpolation, and joint norms spend rather than improve the number of nearby algebraic samples.

Hilbert-scheme compactness retains the wrong locus even when degree and conjugate geometry are
fixed.  Take `q_m=2^m` and an odd `p_m` within one of `q_m*log 2`, and put
`alpha_m=(p_m+sqrt(2))/q_m`.  Then `(1,alpha_m)` is rationally independent and algebraic, so
Lindemann--Weierstrass makes `exp(1),exp(alpha_m)` algebraically independent.  Its exact
`Q`-locus is the two-dimensional variety with `X_1=1`, both `Y` coordinates free, and

`F_m(X_2)=q_m^2*X_2^2-2*p_m*q_m*X_2+p_m^2-2=0`.

The displayed polynomial is primitive, its degree is constantly two, both conjugates
`(p_m+/-sqrt(2))/q_m` tend to `log 2`, and its coefficient height is `Theta(q_m^2)`.  After
projective normalization,
`F_m -> (X_2-log 2)^2`.  Thus the flat Hilbert limit is a nonreduced complex fiber defined over
`Q(log 2)`, still of dimension two, with both exponential coordinates free.  It contains
`(1,log 2,e,2)` but forgets the limiting rational equation `Y_2=2`; it is not the point's
`Q`-Zariski locus in either possible transcendence-degree case.

The period stress has the same fixed-degree degeneration.  Along with `alpha_m` choose
`b_m=2^m` and an odd `a_m` within one of `2*pi*b_m`, and set
`beta_m=I*a_m/b_m -> 2*pi*I`.  The inputs are rationally independent (one is real and the other
purely imaginary), their joint algebraic degree is four, and their coordinate locus is cut out by
`F_m(X_1)` and `b_m^2*X_2^2+a_m^2`.  Its complex flat limit has equations
`(X_1-log 2)^2=0` and `X_2^2+4*pi^2=0`, while both multiplicative coordinates remain free; it
therefore forgets the limiting values `(2,1)`.  The defining heights grow like `q_m^2` and
`b_m^2`, so the corresponding rational Hilbert points have unbounded arithmetic height despite
lying in one projective Hilbert component.

This is unavoidable by Northcott: bounded degree and bounded height would leave only finitely
many algebraic approximants.  Properness of the Hilbert scheme controls algebraic families, not
analytic sequences of rational points of unbounded height, and a rational sequence may converge
to a Hilbert point with transcendental coefficients.  Hurwitz preserves the coalescing complex
intersection points and their multiplicities, but not their fields of definition.  Already
`alpha_m=1/m` gives exact one-dimensional exponential loci
`{X=1/m} x Gm` converging flatly to `{X=0} x Gm`, whereas the limiting exponential point `(0,1)`
has zero-dimensional `Q`-locus.  Rational linear independence is a countable intersection of
hyperplane complements, not a finite-type constructible condition that repairs this failure.

Hence fixing a Hilbert polynomial avoids degree growth only by moving all arithmetic cost into
the Hilbert height and the residue field of the limiting parameter.  Forcing the flat limit to
equal the minimal `Q`-locus, rather than merely contain the limiting point, would require a new
specialization theorem preventing exactly this drop; in the mixed and period examples that
statement is the original algebraic-independence problem.

A genuinely joint Hermite--Padé system for
`exp(k*x)*log(1+x)^j` also has no parameter range.  Factorial-normalized Taylor rows are integral,
but forcing order `T=theta(N)` at zero gives coefficient height
`exp(c*N*log N)`.  Multiplying the logarithmic columns by `(1+x)^S` is the strongest exact
rational cancellation at the branch point: Lindemann--Weierstrass prevents cancellation between
distinct `exp(-k)` coefficients.  The exact remaining coefficient is
`S!*(m-S-1)!/m! = 1/(m*binom(m-1,S))`, so even with `S=theta(N)` the tail gain is only
`exp(-O(N))`, not the tempting `exp(-O(N*log N))`.  It cannot offset the factorial Siegel height.
Wronskian nonvanishing may require linearly many derivatives and worsens the same balance; under a
hypothetical mixed relation the resulting value still lies in a one-dimensional function field,
where no Liouville lower bound is available.

Borel normalization moves but does not remove this factorial loss.  For the analytic Borel
transform, the joint coefficients are integral only after division by `(n!)^2`; the inverse
Laplace identity `integral_0^infty exp(-t)*t^n/n! dt = 1` restores exactly the factorial gained by
high-order Borel vanishing at the Gamma saddle `t near n`.  The transformed Siegel system still
has height `exp(c*N*log N)` and inversion supplies no negative `N*log N` term.  The alternative
E-function normalization makes `exp(k*x)` rational but sends `log(1+x)` to a factorially divergent
series.  Branch softening remains only `exp(-O(N))` under either faithful formulation.

Gamma and Mellin functional equations give the same normalized copies.  With
`a=log 2` and `w=(1-1/a)/2`, duplication writes
`Gamma(w)*Gamma(w+1/2)=e*sqrt(pi)*Gamma(2w)`, but shifting `w -> w+n` cancels exactly to the
original equation through `(2w)_(2n)=4^n*(w)_n*(w+1/2)_n`; retaining the Pochhammer factors costs
degree `n` and factorial height.  Multiplication formulas add as many uncontrolled Gamma values as
new equations, reflection adds trigonometric periods, and differentiation adds successive zeta
values.  The digamma shifts expressing `log 2` only add harmonic corrections whose denominators
have exponential least common multiple.  Incomplete Gamma is precisely the ordinary Taylor
polynomial plus its remainder, while a genuinely mixed Mellin kernel already introduces
`Ei(2)-Ei(1)` or hypergeometric constants.  Eliminating those values returns the separate Padé
systems; the identity `integral exp(-t)*t^n/n! = 1` is again the exact saddle cancellation.

A single Beta kernel tying the two constants has an exact reciprocal-saddle obstruction.  Put
`R_n(x)=x^n*(1-x)^n/(1+x)^(n+1)`, `rho=3-2*sqrt(2)`, and
`lambda=3+2*sqrt(2)=rho^(-1)`.  The logarithmic integral
`I_n=integral_0^1 R_n(x) dx` is `a_n*log 2+b_n`, where
`a_n=[t^n](t-1)^n*(2-t)^n=P_n(3)` is an integer Legendre value and satisfies
`(n+1)*a_(n+1)=3*(2*n+1)*a_n-n*a_(n-1)`.  If
`A=4+3*sqrt(2)` and `xi=4/A`, saddle asymptotics give
`I_n~rho^n*sqrt(2*pi/(A*n))/sqrt(2)` and
`a_n~lambda^n/sqrt(2*pi*xi*n)`, hence the sharp equality
`a_n*I_n~1/(2*sqrt(2)*n)`.  The least-common-multiple and endpoint powers of two used to clear
`b_n` consume the same exponential scale up to the familiar narrow irrationality margin.

Using exactly `R_n` for the exponential does not give a form in only `1,e,log 2`.  Rational
Hermite reduction has
`R_n=S_n'+S_n+c_n/(1+x)`, and therefore
`H_n:=integral_0^1 exp(x)*R_n(x) dx=e*S_n(1)-S_n(0)+c_n*J`, where
`J=integral_0^1 exp(x)/(1+x) dx=e^(-1)*(Ei(2)-Ei(1))` is a new period and
`c_n=[t^n] exp(t)*(t-1)^n*(2-t)^n`.  The same saddles give
`c_n~exp(-sqrt(2))*lambda^n/sqrt(2*pi*xi*n)`,
`H_n~exp(sqrt(2)-1)*rho^n*sqrt(2*pi/(A*n))/sqrt(2)`, and thus
`c_n*H_n~1/(2*sqrt(2)*e*n)`.  Eliminating `J` between adjacent rows yields the exact leading
balance `c_(n+1)*H_n-c_n*H_(n+1)~2/(e*n)`, not exponential decay.  Moreover the pole reduction
`(1+x)^(-k) -> (1+x)^(-1)/(k-1)!` shows that clearing the endpoint coefficients costs `n!`
(and powers of two), overwhelming the Beta decay.  Thus creative telescoping either keeps the
new `Ei` value or cancels it at precisely the inverse asymptotic/denominator cost.

The period stress is the closed-contour version of the same equality.  If `gamma_k` is the path
from `0` to `1` winding `k` times around `-1`, then
`integral_(gamma_k) R_n(x) dx=I_n+k*(2*pi*I)*a_n`.  Only the principal branch is small; every
nonzero winding adds the large exact residue `a_n*(2*pi*I)`.  Shrinking the loop does not shrink
that period, and a Casoratian of open and closed periods merely records the residue.  Hence the
common holonomic sequence supplies no correlated small form in `(log 2,2*pi*I)` either.

Hardy, Nevanlinna, and Paley--Wiener factorization see the known zero only as an inner factor.  For
`F(t)=P(tz,exp(tz))` of additive/exponential degrees `(d,m)`, the indicator segment is `[0,mz]`;
Jensen permits linearly many zeros in the radius, while the one zero at `t=1` costs only `log R`.
The exact stress `F(t)=exp((log 2)*t)-2`, on the rotated line
`t=1+i*s/log 2`, is `4i*exp(i*s/2)*sin(s/2)`: its full period zero set has density exactly the
critical type-`1/2` Paley--Wiener density, attained by this nonzero sine-type function.  Integer
sampling has only the original zero, and rational near-zeros have Kummer norms
`+/- (2^s-2^r)` that erase the selected-branch gain.  Mixed translates remain in a fixed
finite-dimensional confluent space; products create `M` zeros but increase exponential type and
arithmetic height by at least `M` (quadratically for dilates).  Sampling determinants still lie in
the original transcendental field, so analytic norm inequalities provide no discrete lower bound.

The compact-distribution transform gives an exact version of the last obstruction.  Write any
scaled polynomial relation as
`F(t)=P(tz,exp(tz))=sum_j sum_(k<d_j) a_(j,k)*t^k*exp(lambda_j*t)`, with the active degrees chosen so
`a_(j,d_j-1) != 0`.  It is the Laplace transform of
`sum_(j,k)(-1)^k*a_(j,k)*delta_(lambda_j)^(k)`.  Rational independence of the `z_i` makes the
distinct lattice frequencies `lambda_j=m_j dot z` genuinely distinct.  If `M=sum_j d_j`, direct
confluent-Vandermonde factorization gives the derivative Hankel determinant

`det(F^((r+s))(t))_(0<=r,s<M)
 =(-1)^(sum_j d_j*(d_j-1)/2)
  *product_j(((d_j-1)!*a_(j,d_j-1))^d_j)
  *exp(t*sum_j d_j*lambda_j)
  *product_(i<j)(lambda_j-lambda_i)^(2*d_i*d_j)`.

Thus the determinant is nonzero and yields the sharp multiplicity bound `ord_(t=1) F < M`, but
`F(1)=0` merely makes its upper-left entry zero.  The determinant belongs to
`Q(z,exp z)`, not to a discrete ring.  Symmetrizing the spectrum cancels the displayed exponential
factor but leaves the top coefficients and confluent Vandermonde in `Q(z)`.  Integer sampling is
worse: its determinant uses `exp(lambda_j)-exp(lambda_i)`, which can vanish when a nonzero support
difference is a period `2*pi*i*k`, something rational independence of the `z_i` does not exclude.
The multiplicity estimate is attained by `(2^t-2)^(M-1)`, the transform of the convolution power
`(delta_(log 2)-2*delta_0)^(*(M-1))`, which has `M` support points and a zero of order `M-1`.

There is also a sharp two-frequency uncertainty counterfeit that includes the scalar stress and a
fully transcendental translation.  Put `delta_N=log((N+1)/N)` and
`F_(N,u)(t)=N*exp((u+delta_N)*t)-(N+1)*exp(u*t)`.  Then `F_(N,u)(1)=0` and exactly
`F_(N,u)(1+i*s)=2*i*(N+1)*exp(u)*exp(i*s*(u+delta_N/2))*sin(s*delta_N/2)`.
The case `(N,u)=(1,0)` is `exp(t*log 2)-2`.  One may choose real `u` outside a countable union of
analytic zero sets so that, simultaneously, `(u,exp u)` is algebraically independent over the
countable field generated by the `delta_N`; hence `u,u+delta_N,exp u,exp(u+delta_N)` are all
transcendental and the two support points are rationally independent.  Translation only adds the
harmless modulation shown above.  The exact `2 x 2` spectral determinant is
`det(F^((r+s))(1))_(0<=r,s<2)=-((N+1)*exp u*delta_N)^2`.
After normalizing the coefficient height and common value, it is `-delta_N^2 -> 0`; before
normalizing, `(N+1)*delta_N -> 1`, so height restores exactly the lost gap.

Positive kernels do not recover an arithmetic margin.  The normalized shifted measure is
`delta_(u+delta_N)-delta_u`; with Gaussian Fourier weight its Gram matrix is
`[[1,exp(-delta_N^2/4)],[exp(-delta_N^2/4),1]]`, whose determinant
`1-exp(-delta_N^2/2)~delta_N^2/2` tends to zero despite rational independence.  Squaring the
Fourier transform only gives the nonnegative function `4*sin(s*delta_N/2)^2`, the exact
Fejer--Riesz boundary.  A genuinely positive atomic measure cannot encode the original relation
at all, since its Laplace mass at `t=1` is strictly positive.  For a hypothetical fully mixed
relation, the same determinant formula has frequencies in the lattice generated by all `z_i` and
coefficients in `Q(z)`; no Fourier, uncertainty, or positivity operation creates the missing norm
from `Q(z,exp z)` to `Q`.

Poincare--Lelong currents give the same equality with boundary mass.  With
`dd^c log|F|=[Z_F]`, Jensen's formula for a one-variable leaf is
`sum_(|a|<R) ord_a(F)*log(R/|a|)
 =(1/(2*pi))*integral log|F(R*exp(i*theta))|dtheta-log|F(0)|`.
For `F(t)=P(tz,exp(tz))`, additive degree `d` contributes `d*log(1+R)` and the convex hull of the
exponential frequencies contributes its support function, whose circular mean is linear in `R`.
The selected zero at `t=1` contributes only `log R`.  Most importantly,
`dd^c log|cF|=dd^c log|F|`: the positive current forgets primitive integral normalization.  Putting
that normalization back through a Green function restores exactly the constant and boundary term
on the right side of Jensen, so positivity alone has no arithmetic lower bound.

Rational dilation gives an exact moving-divisor obstruction.  For `phi_q(t)=q*t`,
`[Z_(F∘phi_q)]=phi_q^*[Z_F]` and `N_(F∘phi_q)(R)=N_F(qR)`.  Hence for
`G_B(t)=product_(q<=B)F(qt)` the known zeros `1/q` contribute
`sum_(q<=B)log(Rq)=B*log R+log(B!)`, while exponential type and boundary mass grow as
`type(F)*sum_(q<=B)q=Theta(B^2)`.  If the currents are normalized by `sum q` to have bounded mass,
the combined weight of these `B` selected zeros is `B/sum q -> 0`; normalizing by `B` to retain
their mass makes the total mass diverge linearly.  Products, rational shears, and powers obey the
same identities: pullback or addition of divisor currents is accompanied by exactly the same
pullback or addition of boundary class.

The mixed current calculation is completely explicit.  On the two-variable exponential leaf the
hypothetical curve is pulled back by
`f_1=t_1-1`, `f_2=exp(t_2)-2`, and `f_3=P(exp(t_1),t_2)`.  The first two divisors intersect as
`[Z_(f_1)] wedge [Z_(f_2)]=sum_(k in Z) delta_(1,ell+2*pi*I*k)`, each with multiplicity one; its
mass in a radius-`R` bidisc is `Theta(R)`, exactly the boundary type of `exp(t_2)-2`.  The third
equation selects only the finitely many terms for which `P(e,ell+2*pi*I*k)=0`, including the
target, but three divisor currents cannot be intersected in complex dimension two to create an
additional positive mass.  The ideal-theoretic Monge--Ampere mass at the target is just the already
computed local length one.

For the period stress the first two leaf equations are `exp(t_1)-2` and `exp(t_2)-1`; their
intersection current is the grid
`(ell+2*pi*I*k_1,2*pi*I*k_2)`, of mass `Theta(R^2)` in a bidisc.  The relation
`P(t_1,t_2)` merely selects isolated grid points and supplies no extra positive wedge.  Along the
one-parameter radial restriction `F_0(t)=P(t*ell,t*2*pi*I)`, a nonzero polynomial of degree `D`,
the product `product_(q<=B)F_0(qt)` has degree `D*B` and leading-coefficient scaling `(B!)^D`.
Its boundary term therefore contains `D*log(B!)`, while the selected zeros `1/q` gain only
`log(B!)`; this is equality for `D=1` and a loss for `D>1`.  If `F_0` is identically zero because
of homogeneity, the two multiplicative equations above still cut the scaling curve to the same
isolated lattice intersection.

Diagonal Pade gives a numerical saturation of the current formula.  For
`E_m=B_m*exp-A_m`, the exact remainder has a zero of order `2m+1` at zero and leading normalized
coefficient `1/((2m+1)*H_m)`.  Jensen applied to `E_m/t^(2m+1)` therefore restores
`log H_m+log(2m+1)` in its constant term.  Since
`R_m-exp=-E_m/B_m`, Poincare--Lelong reads
`dd^c log|R_m-exp|=[Z_(E_m)]-[Z_(B_m)]`; at a fixed point the pole divisor with
`|B_m| asymp H_m` restores the second `log H_m`.  This is precisely the observed
`H_m^(-2+o(1))` Pade error.  Discarding pole or boundary mass creates the apparent gain; retaining
the global current cancels it exactly.

Arithmetic intersection theory cannot remove that boundary term because the exponential leaf is
not an algebraic cycle over a number field.  Its map `t -> (tz,exp(tz))` has transcendental
coefficients and an essential singularity at infinity; pulling an integral divisor back produces
the Nevanlinna current above, not a metrized algebraic line bundle of fixed degree.  Replacing the
leaf by Taylor or Pade graphs makes the map algebraic only by adding graph degree `m`, pole degree
`m`, and coefficient height `log H_m`; arithmetic Bezout then reproduces the same resultant and
pole-divisor costs.  Spreading `W` over `Q` does not spread the selected exponential comparison
map, so there is no global arithmetic intersection number whose positivity contains the isolated
complex zero but omits its compensating boundary mass.

Integer-valued entire-function theorems hit their own sharp constants.  If
`Q in Z[X,Y]` has positive `Y`-degree `m`, then `f(z)=Q(z,2^z)` takes integer values at all
nonnegative integers but has exact exponential type `m*log 2`; every nonpolynomial component is
therefore at or above Pólya's strict `<log 2` threshold.  The basic equality case
`2^z-2` has `Delta^k f(0)=1` for every `k>=1`.  In the hypothetical mixed relation
`A(log 2,e)=0`, the parametrization `G(s)=A(log 2,2^s)` has its desired zero at
`s=1/log 2` and values only in the nondiscrete ring `Z[log 2]`.  That loss is essential: for
arbitrarily small nonzero `c=q*log 2-p`, the nonpolynomial function `(1+c)^z` maps nonnegative
integers into `Z[log 2]` and has type `|log(1+c)|` tending to zero; its coefficient heights grow
like `q^n` and exactly pay the small selected type.

Rescaling the zero to `1` changes the values to `Z[log 2,e]`.  A finite norm stops in
`Q(log 2)`, since there is no norm from this transcendental field to `Q`; denominator clearing is
linear in the sample index but still lands in the same nondiscrete ring.  Specializing `log 2` to
an algebraic value destroys both `A(log 2,e)=0` and `exp(log 2)=2`.  Periodizing the zero is also
critical: if `r=deg_X A`, then
`exp(-pi*I*r*w)*A(log 2,e*exp(2*pi*I*w))` vanishes on every integer but has exact type
`pi*r>=pi`, while Carlson needs `<pi`; the scalar case is exactly `4*I*sin(pi*w)`.  Centering the
frequencies hides a quadratic product of denominators, and taking `q`-th roots lowers the selected
type only while a degree-`q` Kummer norm restores `log 2`.  Thus neither integer interpolation nor
finite differences offers a strict uniqueness range.

At a fixed transcendental complex embedding, generic height lower bounds fail even more directly.
After choosing a transcendence basis `T` for the generated field, a relative norm of an auxiliary
value has the form `P(T)/s(T)^M`. At the selected values `T = tau`, algebraic independence proves
only `P(tau) != 0`. For an ultra-Liouville coordinate `tau`, primitive linear polynomials
`qT-p` can be smaller than any proposed function of degree and coefficient height. Function-field
product formulas contain divisorial places, not the point `tau`; Arakelov formulas average over
the complex locus, where one point has measure zero. P-adic integrality therefore cannot replace
the missing pointwise archimedean lower bound.

Averaging over all complex embeddings cannot assign useful positive mass to the one embedding
where `Y=exp X`.  On a hypothetical curve for `(e,log 2)`, preservation of the rational relation
holds at every generic complex point, but the conditions `X=e` and `exp Y=2` select at most a
finite, hence equilibrium-measure-zero, subset.  Adding an atom `epsilon*delta_tau` to an
Arakelov or harmonic measure changes the principal-divisor formula by the Green/local-proximity
term `epsilon*(log|f(tau)|-integral log|f|)`, which is uncontrolled.  On `P^1`, for a Liouville
`tau` and `f_N(T)=q_N*T-p_N`, Jensen gives average `log q_N` but
`log|f_N(tau)|<-(N-1)log q_N`; every fixed positive atomic weight drives the modified average to
minus infinity.  Restoring a lower bound requires adding exactly this missing local-height term,
while sending the weight to zero erases the genuine exponential estimate.  Smooth,
non-pluripolar, and finite-energy measures therefore miss the point, and atomic metrics merely
restate the needed transcendence measure.

The same conclusion is intrinsic to heights over finitely generated fields.  If `K/Q` has
transcendence degree `d`, choose a normal projective arithmetic model `B` and a nef hermitian
polarization `Hbar_1,...,Hbar_d`.  For every `f in K^*`, the identity
`widehat_deg(widehat_div(f)*product Hbar_i)=0` expands into the weighted sum of its codimension-one
orders plus the integral of `log|f|` against
`mu_H=product c_1(Hbar_i)` on `B(C)`.  The distinguished embedding `K -> C` is one point of this
complex fiber and has `mu_H`-measure zero.  The numerical identity `y=exp z` at that point is not
an identity of rational functions on `B`, so it contributes no additional archimedean place.
Changing the model or smooth metrics redistributes the divisorial and archimedean terms while the
principal intersection remains zero; no polarization is canonically selected by the exponential
comparison.

Giving the distinguished point positive atomic weight is incompatible with a product formula
without adding a new local-height correction.  On the rational subfield `Q(T)`, primitive
`f_N=q_N*T-p_N` have every model/divisor contribution of size `O(log q_N)`, whereas at an
ultra-Liouville embedding `T -> tau` the value `log|f_N(tau)|` can be less than
`-N*log q_N`.  Thus no fixed positive coefficient of that embedding can be balanced by the
standard places.  For a particular non-Liouville point, proving the required balance is precisely
a pointwise transcendence measure not supplied by the arithmetic model.  Dirac curvature is also
singular/pluripolar, so its Green self-intersection reintroduces the same uncontrolled local term.

Division points exhibit exact adelic compensation.  On a full degree-`m` Kummer cover
`beta^m=a`, normalized heights satisfy
`h_H(beta)=h_H(a)/m`, while
`N_(K(beta)/K)(beta-1)=+/-(a-1)` and
`pi_* div(beta-1)=div(a-1)`.  Pointwise on every unramified complex fiber,
`sum_(k<m) log|zeta_m^k*beta-1|=log|a-1|`.  Hence the analytically selected root may approach one
at rate `1/m`, but intersection with the polarization, integration over the sheets, and every
product formula restore the other `m-1` roots.  Multiplying the number of division coordinates
only raises the cover degree and repeats this equality.

In the hypothetical mixed field `K=Q(e,ell)` of degree one, take the normalized arithmetic
surface model of the curve `P(Y,X)=0`.  The selected complex point is `(Y,X)=(e,ell)`; the further
conditions `Y=exp(1)` and `exp(X)=2` hold only there.  On the Kummer cover
`U_m^m=Y`, `V_m^m=2`, the selected sheets satisfy
`U_m-1~1/m`, `V_m-1~ell/m`, but over `K(mu_m)`
`N(U_m-1)=+/-(Y-1)` and `N(V_m-1)=+/-1` (with the appropriate repeated powers in the joint
degree-`m^2` cover).  Also `h(U_m)=h(Y)/m` and `h(V_m)=log(2)/m`.  Thus neither the curve model nor
its polarization distinguishes the positive analytic sheets; the exact mixed Kummer degree found
above is fully compatible with `trdeg_Q K=1`.

For the period stress the hypothetical model has function field
`Q(ell,2*pi*I)` and curve equation `P(X_1,X_2)=0`, while both exponential coordinates are the
constants `(2,1)`.  Its division tower is therefore a constant-field tower: the selected roots are
`2^(1/m)` and `zeta_m`, with heights `log(2)/m` and zero.  The identities
`N(1-2^(1/m))=+/-1` and, for prime `p`, `N(1-zeta_p)=p` compensate the respective sizes
`asymp ell/m` and `asymp 2*pi/p`.  These calculations do not involve the arithmetic surface or
the alleged relation `P` at all, so no choice of Moriwaki polarization can recover the complex
period branch.

Low-dimensional discontinuous exponentials satisfy the identical adelic bookkeeping.  Over
`Q(T)`, the assignment `E(q+r*T)=3^q*2^r` sends the independent pair `(1,T)` to `(3,2)` and has
total degree one; its division roots have heights `log(3)/m,log(2)/m` and norms
`N(3^(1/m)-1)=+/-(3-1)`, `N(2^(1/m)-1)=+/-1`.  The period-shaped counterfeit
`(T,T^2;2,1)` has the same constant Kummer and cyclotomic tower as the genuine period stress.
Every arithmetic model, divisor pushforward, and polarized product formula remains valid for
these counterfeits.  Excluding them requires the pointwise analytic normalization of `exp`, which
is exactly the datum assigned zero mass by the adelic height.

Specialization cannot insert that datum.  Closed points of the mixed curve have algebraic
coordinates and therefore cannot satisfy `exp(X)=2` at `X=ell`; closed points of the period curve
do not remember which logarithm of `1` is `2*pi*I`.  Approximate specializations acquire growing
degree and height and return to the algebraic-approximation/Padé boundary.  Consequently adelic
heights over `K` provide a correct global equality, but its standard places omit the unique
complex comparison point, and adding that point simply restates the missing local inequality.

Controlling a Taylor jet of that norm instead of only its value does not evade the obstruction.
For `R in Z[T]` of degree `L`, the normalized `L`-th derivative at every point is its nonzero
integer leading coefficient; multivariately, a top total-degree derivative similarly exposes a
nonzero integer coefficient.  Thus leading-coefficient discreteness requires the entire total
jet through the polynomial's degree.  At `a=log 2`, diagonal Padé gives an integer polynomial
`D_n` of degree `n` and height `exp(n log n+O(n))` with
`|D_n(a)|=exp(-n log n+O(n))`, an exactly balanced gain.  For `D_n^M`, derivative bounds remain
small only below order `(1/2-o(1))*M`, while its degree is `M*n`; taking a resultant commutes with
the power and preserves this bad ratio.  Truncating `(exp z-2)^M` directly fails more sharply:
the analytic function has contact exactly `M` and a large `M`-th derivative, while an integer
polynomial of degree below `M` already exposes a top integral jet.  In `d` variables the useful
jet-count ratio is at most `(2*ell)^(-d)` for a base norm of degree `ell`, so extra basis variables
worsen rather than close the deficit.

Dense exponent lattices do use continuity, but at the wrong scale. Packing gives integer vectors
of size `H` with `|m dot z| = O(H^(1-n/r))`, where `r <= 2` is the real span dimension, and
holomorphy only transfers this to `|product exp(z_i)^(m_i) - 1|` of the same polynomial order.
The associated rational function has divisor degree and logarithmic height `O(H)`, so even a
number-field-style exponential lower bound would be compatible with the upper bound.  For
`(log 2, 1)`, continued-fraction approximants give `2^q * e^(-p) - 1 = O(1/q)`, but clearing
`e^p` makes `2^q - e^p` exponentially large. Higher Taylor contact loses its factorial gain when
denominators are cleared, and the elimination polynomial changes with `(p,q)`, so the identity
theorem never sees a fixed analytic function with accumulating zeros.

### Differential and specialization routes

The natural deformation

```text
X_i = z_i(1+u),   Y_i = exp(z_i) exp(z_i u)
```

does satisfy `Y_i = exp(X_i)` along the formal arc, and Ax's functional theorem gives the expected
generic transcendence. However specialization at `u = 0` drops transcendence degree by exactly
`n+1` in a smooth family. The corresponding valuation has value-group rank one and transcendence
defect `n`; bounding that defect in the required direction is already the desired numerical
inequality. Ordinary flatness, semicontinuity, and Abhyankar's inequality do not prevent the drop.

Separating the deformation into arbitrarily many infinitesimal scales does not distribute this
defect back into the residue field.  For every `1 <= r <= n`, in an iterated Laurent field over
`K=Q(z,exp z)` take
`ell_i=z_i*tau_1+tau_(i+1)` for `i<r` and `ell_i=z_i*tau_1` otherwise, and set
`X_i=z_i+ell_i`, `Y_i=exp(z_i)*exp(ell_i)`.  The `ell_i` are rationally independent modulo `K`
and have Jacobian rank `r`; after an algebraic extension of the constant field, functional Ax and
algebraic base-change invariance give the exact relative degree `n+r`.  The composite
`tau`-adic valuation has value group `Z^r` and residue field exactly `K`.  Its Abhyankar
decomposition is therefore
`d+n+r = d + r + n`: all `n` exponential dimensions are transcendence defect, for every number
of scales.  Along the iterated flag the first defect is `n-r+1` and each of the remaining `r-1`
stages has defect one.  Taylor renormalization cannot reveal an extra residue: after subtracting
the first `k-1` terms, the residue of the normalized exponential remainder is only `a^k/k!` in
`K`.  Thus the associated graded field sees the value directions and constants but none of the
`n` immediate exponential directions.

Centering the whole exponential family at the rational singular point does not remove the free
constants.  The rational system `t*X_i'=X_i`, `t*Y_i'=X_i*Y_i` has solutions
`X_i=z_i*t`, `Y_i=exp(z_i*t)` through `(t,X,Y)=(0,0,1)`.  Blowing up with `Z_i=X_i/t`
desingularizes it to `Z_i'=0`, `Y_i'=Z_i*Y_i`; the exceptional fiber is the full affine slope
space `A^n_Z`.  At every finite order the solution-jet scheme is exactly this affine space, with
coefficients `Y_(i,m)=Z_i^m/m!`.  Thus slopes `(T,T^2,...,T^n)` are rationally independent over
`Q` but all jets live over the transcendence-degree-one field `Q(T)`.  In the mixed stress all
finite jets lie in `Q(log 2)`; the endpoint value `e` enters only through infinite summation.

The arithmetic singularity is unfavorable rather than algebraizing.  After blowup the connection
`d-Z_i*dt` has p-curvature `-Z_i^p`, nonzero away from the zero slope.  Equivalently the original
Euler field satisfies `(Theta^p-Theta)(Y_i)=X_i^p*Y_i` in characteristic `p`.  The recurrence
`Z_i^m/m!` fails integrally at `m=p`, and the common denominator through order `N` is `N!`, with
the exact `N log N` cost already present in the Hermite estimates.  The `X` equation has trivial
monodromy and merely transports the arbitrary integration constant, while infinity is irregular
with exponential type `Z_i`.  Rationality of the singular base point therefore imposes no
arithmetic condition on the tangent parameters.

Arc spaces and motivic integration measure the same formal codimension while remaining blind to
the residue field.  Over the center field `K`, put coordinates `(U,V_1,...,V_n)` and
`F_i=V_i-(exp(z_i*U)-1)`.  The triangular formal change `(U,V)->(U,F)` has Jacobian one and turns
the formal exponential graph into a coordinate line.  In the centered `m`-jet fiber of dimension
`(n+1)*m`, solution jets have dimension `m` and codimension `n*m`; more generally
`ord(F)>=q` has codimension `n*(q-1)` and conditional motivic measure `L^(-n*(q-1))`, while
`mu(F=0)=0`.  These classes and the associated zeta series are identical for an algebraic linear
graph because the coordinate change induces a triangular polynomial automorphism at every jet
level.

In the mixed family, the normalized arc
`(t,exp(t)-1,log(1+t/2))` is Zariski dense in `A^3_K` by exponential-polynomial independence and
logarithmic monodromy, although every Taylor coefficient lies in `K=Qbar(e,log 2)`.  Under a
hypothetical relation, the true locus pulls back to the maximal ideal `(u,v)` on the exponential
graph, so its contact cylinders have the universal smooth-point measures
`L^(-2*(q-1))`; they are compatible with either possible value of `trdeg_Q K`.  Spreading out over
a `Q`-model of `K` adds the base dimension to both ambient and contact spaces and leaves every
codimension unchanged.  The induced valuation has value rank one, residue `K`, and the same `n`
units of transcendence defect already computed above.  Nash blowups are trivial on these smooth
models, and iterated Taylor blowups expose only residues `z_i^r/r!` in `K`.  Thus arc dimension,
motivic volume, and contact order cannot force the missing residue transcendence.

Ultraproduct rescaling loses precisely the bounded complexity needed for an identity theorem.
For `epsilon=[1/q]`, the points `X_i=epsilon*z_i`, `Y_i=exp(epsilon*z_i)` have residues `(0,1)`;
all normalized Taylor residues lie in `Q(z)`, while recovering `exp(z_i)` requires the nonstandard
power `Y_i^(1/epsilon)`.  Accordingly a fixed relation becomes `P(qX,Y^q)=0`, of unbounded degree,
and Loś transfer does not turn this hyperdegree sequence into a standard polynomial identity.
Already `2^(1/q)` has irreducible degree `q` but standard part one.  At a hypothetical mixed
relation, rescaling around its isolated zero retains only the leading monomial recording finite
intersection multiplicity.  For
`L=Q(z)(t,exp(z_1*t),...,exp(z_n*t))`, the `t=1` residue is the original field and the exact
transcendence defect is `trdeg Q(z)+n-trdeg Q(z,exp z)`; at `t=0` it is `n`.  A single fixed
bounded-degree relation at infinitely many rescaled points would indeed force a functional
identity, but rational divisions and shears supply only the unbounded-degree relations above.

Mahler dilation identities retain the same free constants.  On a logarithm branch,
`F_c(u)=u^c` satisfies `F_c(u^p)=F_c(u)^p`; for the transcendental
`c=log(3)/log(2)`, the rationally independent pair `(1,c)` nevertheless specializes at the
algebraic point `u=2` to the algebraic values `(2,3)`.  Near the attracting point zero, `u^c` is
not holomorphic for arbitrary `c`; on the logarithmic cover, every normalized analytic solution
of the dilation equation is `exp(c*t)` with unconstrained slope `c`.  For the actual
`H_i(t)=exp(z_i*t)`, rational division gives fields mutually algebraic with the original one, and
a relation at `t=1/q` is only the moving dilate `R_q(t)=R_1(q*t)`, whose degree grows with `q`.
Thus Mahler specialization either inserts the unknown coordinates into the coefficients or
repackages the target in a degree-growing family.

### Exact E/G-function and differential-Galois audit

Put both mixed values at the same algebraic ordinary point:

`E(z)=exp(z)`,  `L(z)=-log(1-z/2)=sum_(m>=1) z^m/(m*2^m)`.

Then `(E(1),L(1))=(e,log 2)`.  Here `E` is an E-function and `L` is a G-function: the common
denominator of the first `N` coefficients of `L` divides
`2^N*lcm(1,...,N)`.  Conversely, `L` is not an E-function because it has a logarithmic
singularity at `z=2`, and `E` is not a G-function because the common denominator of its first
`N` ordinary Taylor coefficients is `N!`, of superexponential growth.  With `Y=(E,L,1)^t`,

`Y'=[[1,0,0],[0,0,1/(2-z)],[0,0,0]]Y`.

This rational system is ordinary at `z=1`.  Its Picard--Vessiot group over `C(z)` is exactly
`G_m x G_a`: continuation around `2` translates `L` and fixes `E`, while `E` is transcendental
over `C(z)`.  Hence `E,L` are algebraically independent over `C(z)`.  This functional conclusion
does not specialize arithmetically.  Beukers's refined Siegel--Shidlovskii theorem (using
Andre's E-operator theorem) completely lifts relations among values only when all functions are
E-functions.  The logarithmic coordinate violates that hypothesis.  Its refinement at
exceptional or singular evaluation points cannot help, since `1` is already ordinary; the
failure is the arithmetic class of the solution, not local continuation.  Direct-sum and tensor
systems retain both offending coordinates, and mixed monomials containing `L` still have its
singularity, so they do not convert the problem into an all-E system.

The exact missing statement is injectivity of

`ev_1: Qbar[X,Y] -> C`,  `X |-> E(1)=e`,  `Y |-> L(1)=log 2`.

The analogous functional map from `Qbar(z)[X,Y]` is injective.  Thus a mixed E/G lifting theorem
saying that every relation in `ker(ev_1)` specializes from a functional relation would prove the
desired algebraic independence, but in this example that conclusion is literally
`ker(ev_1)=0`, the `(1,log 2)` instance of Schanuel.  Evaluation is not a differential-field
homomorphism, so the group `G_m x G_a` supplies no map forcing it.  The recent mixed E/G results
of Vargas-Montoya concern functional algebraic independence over p-adic fields of analytic
elements under Frobenius and MOM hypotheses, not injectivity of complex evaluation at an
algebraic point.  The unconditional output here is therefore the separate transcendence of `e`
and `log 2`; these methods supply no cross algebraic independence (or even a new cross linear
independence theorem).

The period control has the same defect inside the G-class.  Set

`A(z)=8*i*arctan(z)`,  so `A(1)=2*pi*i` and `A'=8*i/(1+z^2)`.

Both `L,A` are analytically continued G-functions and `z=1` is ordinary for their system.
Their Picard--Vessiot group is `G_a^2`.  Indeed a nonzero constant combination of
`L'=1/(2-z)` and `A'=8*i/(1+z^2)` cannot be a rational derivative: its residues at the disjoint
poles `2,i,-i` force both coefficients to vanish.  Thus `L,A` are functionally algebraically
independent, yet injectivity of

`Qbar[X,Y] -> C`,  `(X,Y) |-> (log 2,2*pi*i)`

is still precisely the missing numerical algebraic independence.  Baker's theorem does give
`Qbar`-linear independence here (apply it to the Q-linearly independent logarithms `log 2` and
`log(-1)=pi*i`), but it does not give polynomial independence.  A general G-value lifting
theorem of the strength required would already settle this period instance.

Finally, ordinary-point differential-Galois data alone provably cannot support such a lifting
principle.  The functions `f(z)=exp(z)` and `g(z)=exp(z^2)` solve the first-order rational
equations `f'=f`, `g'=2*z*g`, are algebraically independent over `C(z)`, and are evaluated at an
ordinary point, but `f(1)=g(1)=e`.  Here `g` is not an E-function, exactly confirming that the
arithmetic E-function hypothesis in Siegel--Shidlovskii, rather than the differential system or
its Galois group, does the specialization work.

### The 2025 p-adic mixed E/G criteria and the 2026 logarithmic E-value theorem

The exact scope of the new results leaves the mixed value fiber untouched.  In
[Vargas--Montoya, Part I, arXiv:2502.00768v2 (2025)](https://arxiv.org/abs/2502.00768), put
`delta=z*d/dz`.  For a Frobenius field `K` (in particular a finite totally ramified extension of
`Q_p`), `MF(K)` consists of `f in 1+z*K[[z]]` annihilated by a monic operator

`L=delta^r+a_1(z)*delta^(r-1)+...+a_r(z)`

over the ring of analytic elements on the open unit disk, with `|a_i|_G<=1`, with MOM at zero
(`a_i` is regular at zero and `a_i(0)=0` for every `i`), and with strong Frobenius structure
(the companion matrix is gauge-equivalent over the field of analytic elements to its iterated
Frobenius pullback).  Theorem 2.3 says that `f_1,...,f_m in MF(K)` are algebraically dependent
over `E_K` exactly when some nonzero integral multiplicative combination
`prod_i f_i^(a_i)` lies in `E_(0,K)`.  Its key Theorem 3.1 also forces every member of `MF(K)` to
belong to `1+z*O_K[[z]]` and puts `f'/f` in `E_(0,K)`.  The effective criterion in
[Part II, arXiv:2507.20429v1 (2025)](https://arxiv.org/abs/2507.20429) adds hypotheses on distinct
poles and nonzero residues of the logarithmic derivatives, assumes the selected points are
regular singular modulo the square of the maximal ideal, and requires at least one selected
residue modulo that square not to be a local exponent (Theorem 3.7), but has the same `MF(K)`
input and the same functional conclusion over `E_K`.  Both cited 2025 papers are arXiv preprints;
neither states a theorem about complex values at algebraic points.

The target functions fail these hypotheses for two separate, computable reasons.  For

`F(z)=exp(z),    H(z)=log(1+z)/z=sum_(n>=0) (-1)^n*z^n/(n+1),`

one has `(F(1),H(1))=(e,log 2)`.  The operator `L_F=delta-z` is MOM and has Gauss norm one.
Nevertheless it cannot have strong Frobenius structure: otherwise Theorem 3.1(i) would put
`F` in `1+z*Z_p[[z]]`, whereas

`v_p(1/n!)=-v_p(n!)`

is negative and unbounded.  For `H`, homogenizing
`(1+z)*(delta+1)H=1` gives the monic operator

`L_H=delta^2+((1+2*z)/(1+z))*delta+z/(1+z).`

Its indicial polynomial at zero is `X*(X+1)`: the coefficient of `delta` has value one at zero,
so `L_H` is not MOM.  Independently, the coefficients `1/(n+1)` have unbounded negative
`p`-adic valuation, contradicting the integrality forced on `MF(K)`.  This is the standard
hypergeometric presentation `H={}_2F_1(1,1;2;-z)`; the exponential is `{}_0F_0(z)`.  Taking their
direct sum or a parameter family does not alter either failed block.

The Dwork repair changes the value problem.  If `pi_p^(p-1)=-p`, then
`exp(pi_p*z)` is annihilated by the MOM operator `delta-pi_p*z`, which does have strong Frobenius
structure, and

`v_p(pi_p^n/n!)=n/(p-1)-v_p(n!)=s_p(n)/(p-1)>=0.`

Thus it belongs to `MF(Q_p(pi_p))`, exactly as in the Vargas--Montoya examples.  It introduces
the new algebraic Dwork constant `pi_p`; to recover the complex value `e` one must evaluate at
`z=1/pi_p`.  But `|1/pi_p|_p=p^(1/(p-1))>1`, and the resulting terms are again `1/n!`, so this
evaluation diverges.  Already at the original point `z=1`, neither target Taylor series is a
`p`-adic value: `1/n!` does not tend to zero, and `(-1)^n/(n+1)` has infinitely many terms of
`p`-adic norm one.  A separately defined `log_p(2)` for odd `p` lies on another residue disk and
is not the complex number `log 2`; for `p=2`, the usual extension has `log_2(2)=0`.  Hence there
is no local value to which the functional theorem could be specialized.  Part II even notes
that `exp(pi_p*z)^p` lies in the analytic-elements field: the Frobenius normalization is designed
for a p-adic differential module, not for preserving the archimedean value `e`.

In fact the relevant complex functional independence is already elementary.  With
`Lambda(z)=log(1+z)` and `Y=(F,Lambda,1)^t`,

`Y'=[[1,0,0],[0,0,1/(1+z)],[0,0,0]]Y,`

and `z=1` is ordinary.  Monodromy around `-1` replaces `Lambda` by `Lambda+2*pi*i` and fixes
`F`; iterating the loop in a polynomial relation first removes `Lambda`, and the transcendence
of `exp(z)` then removes the remaining relation.  Thus `F` and `H=Lambda/z` are algebraically
independent over `C(z)`.  A hypothetical `P(e,log 2)=0` is precisely a new element of the kernel
of evaluation at one, not a functional relation.  Functional independence by itself cannot
control that kernel: for algebraic irrational `alpha` the strict E-functions

`f(z)=exp(z),    g(z)=exp(z)+(z-1)*exp(alpha*z)`

are algebraically independent over `C(z)` (recover `exp(alpha*z)` by dividing by `z-1`), but
`f(1)=g(1)=e`.  The selected two-dimensional differential system necessarily acquires an
apparent singularity at one.  This is exactly the kind of fiber-rank condition supplied by an
E-function lifting theorem and absent from the p-adic functional criteria; no such mixed E/G
lifting theorem is proved in either Vargas--Montoya preprint.

The archimedean theorem of
[Fischler--Rivoal, *Math. Ann.* 394 (2026), article 12](https://doi.org/10.1007/s00208-026-03374-z)
is a genuine special-value theorem, but only for one logarithm.  Their Theorem 1 gives finiteness
of intersections of the algebraic-value sets of two transcendental E-functions unless one is a
algebraic dilation of the other.  Its Corollary 1 says that if an E-function `f` is not
`exp(beta*z)` for algebraic `beta`, then, outside an effectively determinable finite set of
algebraic `xi`, any fixed complex determination of `log(f(xi))` is transcendental.  Their
quantitative Theorem 2 assumes a strict `f in Q[[z]]`, rational nonzero `xi`, `f(xi)>0`, and
`ln(f(xi)) notin Q`; it gives effective `c,d>0` such that

`|ln(f(xi))-a/b| >= exp(-c*b^d)`

for all `a in Z`, `b>=1`.  Taking `f(z)=1+z`, `xi=1`, yields the genuine unconditional inequality

`|log 2-a/b| >= exp(-c*b^d).`

It is an individual irrationality measure, not a two-variable polynomial lower bound.

One strict E-function packages the exact target without improving this conclusion:

`Phi(z)=(1+z)*exp(z),    (1+z)*Phi'(z)-(z+2)*Phi(z)=0.`

At one, `Phi(1)=2*e` and `ln(Phi(1))=1+log 2`, so

`Q(Phi(1),ln(Phi(1)))=Q(e,log 2).`

The logarithm is transcendental (if it were algebraic, Hermite--Lindemann applied after
subtracting one would contradict `exp(log 2)=2`), and the quantitative theorem gives it an
irrationality measure.  But Fischler--Rivoal never assert algebraic independence between an
E-value and its logarithm.  The excluded case `f(z)=exp(beta*z)` is also exact: at `z=1`, the
logarithm of `exp(z)` is the algebraic number one.  A relation `P(e,log 2)=0` makes `log 2`
algebraic over an E-value, not algebraic over `Q`, and creates neither an equality of two E-values
nor an algebraic logarithm, so none of their hypotheses detects it.

Consequently the combined unconditional output for the stress is still only
`trdeg_Q Q(e,log 2)>=1`, together with the displayed one-dimensional irrationality measure.
The desired bound is two.  Vargas--Montoya supplies functional p-adic injectivity after a Dwork
normalization that changes the point and the value; Fischler--Rivoal supplies individual
archimedean transcendence of a logarithm.  The missing bridge is exactly injectivity of the
mixed evaluation map at `z=1`, not a Frobenius, MOM, or logarithmic-E-value hypothesis furnished
by these papers.

### Quantitative elimination from the packaged E-value is exactly saturated

The packaging does not improve the approximation exponent.  Put

`A=Phi(1)=2*e,    lambda=log(A)=1+log 2`

and suppose that a primitive irreducible `P in Z[X,Y]`, of bidegree `(r,s)`, satisfies
`P(A,lambda)=0`.  Individual transcendence gives `r,s>=1`.  Moreover
`P_Y(A,lambda)!=0`: since `P` is irreducible and depends on `Y`, the coprime plane curves `P=0`
and `P_Y=0` have only algebraic intersection points.  Thus a common zero with `A` transcendental
is impossible.  Consequently there are fixed `c_1,c_2>0` such that, for `x` sufficiently close
to `lambda`,

`c_1*|x-lambda| <= |P(A,x)| <= c_2*|x-lambda|.`                 `(QE1)`

The sharp available one-variable measure at `A` is also explicit in the relevant exponents.
Apply the Shidlovskii linear-independence measure recalled and made effective in the
Fischler--Rivoal paper to the strict E-functions

`1, 2*exp(z), 2^2*exp(2*z), ..., 2^N*exp(N*z).`

They are linearly independent over `Q(z)`, their values at one are `1,A,...,A^N`, and their
diagonal differential system has no finite singularity.  Hence for fixed `N` and every
`epsilon>0` there is an effective `C_(N,epsilon)>0` such that every nonzero
`Q in Z[X]` of degree at most `N` satisfies

`|Q(A)| >= C_(N,epsilon)*H(Q)^(-N-epsilon).`                   `(QE2)`

The exponent `N` is Dirichlet-optimal.  Using any of the less sharp fully explicit general
E-value measures only weakens `(QE2)`, so it is enough to test the proposed mechanism against
this favorable bound.

Let `a/b` run through continued-fraction convergents to `lambda`; then
`|lambda-a/b|<b^(-2)` and `|a|=O(b)`.  Clear the denominator by

`Q_b(X)=b^s*P(X,a/b) in Z[X].`

For all sufficiently large `b`, this is nonzero, has degree `r`, and has height
`H(Q_b)=Theta_P(b^s)`: writing `P=sum_j p_j(Y)X^j`, any nonzero `p_j` satisfies
`p_j(lambda)!=0` because `lambda` is transcendental.  Equations `(QE1)` and `(QE2)` give

`C*b^(-s*(r+epsilon)) <= |Q_b(A)| <= C'*b^(s-2).`             `(QE3)`

For the right side to contradict the left as `b` grows one would need the strict inequality

`2 > s*(r+1+epsilon).`                                       `(QE4)`

It has no solution with `r,s>=1`.  The sole limiting case `r=s=1` is the equality `2=2` when
`epsilon=0`; higher bidegree loses strictly.  This is precisely the rational/quadratic
approximation boundary, now expressed for the single packaged E-value.

Fischler--Rivoal's new logarithmic estimate does not change `(QE4)`.  For this `Phi` it supplies
computable constants `c,d>0` (the paper does not print a numerical value of `d` for `Phi`) with

`exp(-c*b^d) <= |lambda-a/b| < b^(-2).`                       `(QE5)`

By `(QE1)`, its contribution to the eliminated value is the additional *lower* bound

`|Q_b(A)| >= c'*b^s*exp(-c*b^d).`

For every `d>0` this is asymptotically much weaker than the polynomial lower bound in `(QE3)`.
It neither constructs approximants better than exponent two nor bounds the ordinary irrationality
exponent by a finite constant; it only excludes an ultra-Liouville scale.  If approximants of
exponent `mu` were supplied independently, the crossing condition would be
`mu>s*(r+1+epsilon)`, so even the tight bilinear case would require `mu>2`.  The logarithmic-E
theorem supplies the opposite kind of inequality.

Algebraic approximation reproduces the same equality with all normalization costs visible.  Let
`alpha` have fixed degree `D`, primitive minimal polynomial `M` of naive height `H`, and, to give
the route its favorable benchmark, suppose one real embedding satisfies
`|alpha-lambda|<=H^(-(D+1))`.  This is the continued-fraction scale for `D=1` and the
Davenport--Schmidt scale for `D=2`; for general `D` it is the expected optimal Wirsing scale and
is stronger than what the general unconditional construction supplies.  Form

`R_alpha(X)=Res_Y(M(Y),P(X,Y)) in Z[X].`

It is nonzero, `deg R_alpha<=r*D`, and resultant homogeneity gives

`H(R_alpha)<=C_(P,D)*H^s.`

Writing the resultant as the product over the `D` conjugates and using the Mahler-measure bound
for the other `D-1` factors gives

`|R_alpha(A)| <= C_(P,D,A)*H^s*|alpha-lambda|
                <= C_(P,D,A)*H^(s-D-1).`                     `(QE6)`

On the other hand `(QE2)`, now with `N=r*D`, gives

`|R_alpha(A)| >= C*H^(-s*(r*D+epsilon)).`                    `(QE7)`

A contradiction would require

`D+1 > s*(r*D+1+epsilon),`                                   `(QE8)`

again impossible for `r,s>=1`.  Equality before `epsilon` occurs only for `r=s=1`.  In the
recorded quadratic stress `D=2`, a Davenport--Schmidt approximant contributes
`|alpha-lambda|=O(H^(-3))`; the other conjugate costs `H`, so the degree-two resultant at `A`
is only `O(H^(-2))`, exactly matching the optimal E-value lower exponent `H^(-2-epsilon)`.

Thus rational substitution, algebraic norms, and resultants all give the same decisive no-go:
even the favorable benchmark gain `D+1` does not cross the elimination requirement
`s*(r*D+1)`.  The 2026 logarithmic-E measure is a lower bound on approximation error at a much
smaller, exponential-in-`b^d` scale and changes none of these polynomial exponents.  Any crossing
would require a new source of better-than-benchmark approximants (already a strict gain over two
in the bilinear rational case) or a genuinely mixed small-value theorem; it cannot be obtained by
combining the two separate one-variable measures.

### Arithmetic differential operators do not descend to the value fiber

For the same functions, the Euler derivation `theta=z*d/dz` gives

`theta(E)=z*E`,  `theta(L)=z/(2-z)`,  hence `(theta(E)(1),theta(L)(1))=(e,1)`.

More generally `theta^r(E)(1)=B_r*e`, where `B_r` is a Bell number, and
`theta^r(L)(1)=sum_(k=1)^r S(r,k)*(k-1)!` is an integer.  These unusually arithmetic jets still
cannot be applied to a hypothetical equality `P(e,log 2)=0`: it says only that
`F(z)=P(E(z),L(z))` has `F(1)=0`, not that `theta(F)(1)=0`.  Indeed

`theta(F)(1)=e*P_X(e,log 2)+P_Y(e,log 2)`

is unrestricted.  Categorically, evaluation kills `z-1` while `theta(z-1)(1)=1`, so its kernel
is not a differential ideal and no derivation descends to the value fiber.

This failure is exactly the target, not a technical inconvenience.  If a `Qbar`-derivation on
`Qbar(e,log 2)` with `D(e)=e` and `D(log 2)=1` did exist, the evaluation ideal would be stable
under `Delta=X*d/dX+d/dY`.  An irreducible stable plane curve away from `X=0` cannot exist.  For
if `P` defines it, then `P` divides `Delta(P)`; comparison of degrees makes
`Delta(P)=lambda*P`, and writing `P=sum_j a_j(Y)X^j` gives
`a_j'=(lambda-j)*a_j`.  A nonzero polynomial solution forces `lambda=j` and `a_j` constant, so
only one `j` occurs and the curve is `X=0`.  Since `e!=0`, the compatible derivation would force
the evaluation ideal to be zero and prove algebraic independence.  Thus manufacturing this
derivation is equivalent to proving the required tangency/injectivity.

The arithmetic-jet version has an equally exact free-variable obstruction.  For a p-derivation
`delta`, put `phi(a)=a^p+p*delta(a)`.  If a hypersurface is `P(X,Y)=0`, its first Buium jet has
coordinates `(X,Y,X',Y')` and the additional equation

`delta(P)=(P^phi(X^p+pX',Y^p+pY')-P(X,Y)^p)/p=0`.

This is an equation for the new jet variables, not a second equation on `(X,Y)`.  At a smooth
curve point its fiber is a formal affine line; at order `r` there are `2*(r+1)` coordinates and
`r+1` equations, hence local relative dimension `r+1`.  Iterating `delta` therefore never
overdetermines the original curve.  Over a characteristic-zero field one may take the Frobenius
lift `phi=id`, so `delta(a)=(a-a^p)/p`; then
`a^p+p*delta(a)=a`, and every iterated jet equation obtained from `P(a,b)=0` is tautological.
Arithmetic content requires a fixed integral p-adic model and a distinguished Frobenius lift,
neither of which is supplied by the complex transcendental point.

There are compatible local equations, but for different local periods.  On its convergence disc,

`psi_p(u):=(1/p)*log_p(phi(u)/u^p)`

is the multiplicative arithmetic logarithmic derivative, and
`psi_p(exp_p(x))=(phi(x)-p*x)/p`.  However `exp_p(1)` diverges for every `p`; for odd `p` one may
replace it by `exp_p(p)`.  Likewise
`log_p(2)=log_p(2^(p-1))/(p-1)` uses the element `2^(p-1)` in `1+p*Z_p`.
Thus the natural local pair is `(exp_p(p),log_p(2))`, not the image of `(e,log 2)` under a known
place comparison.  A hypothetical complex relation can be eliminated to a relation at
`(e^p,(p-1)*log 2)`, but substituting
`(exp_p(p),log_p(2^(p-1)))` is unjustified.  Requiring an embedding to make both substitutions is
exactly requiring the unknown relation to hold in the p-adic realization; arbitrary embeddings
of the transcendental complex residue field do not preserve analytic exponential or logarithm.

The branch loss is decisive in the period control.  The p-adic logarithm kills roots of unity, so
the naive counterpart of the complex branch value `2*pi*i=log(1)` is `log_p(1)=0`; the pair
`(log_p(2),0)` has already lost a dimension.  The genuine p-adic Tate period corresponding to
`2*pi*i` is Fontaine's `t=log([epsilon])`, which lives in a period ring such as `B_dR^+` (and has
`phi(t)=p*t` in `B_cris`), not in `C_p` where the arithmetic jet is evaluated.  Supplying a
comparison that transports polynomial relations among `log 2` and `2*pi*i` to relations among
their p-adic periods is a period-injectivity conjecture, not a consequence of p-derivations.
Consequently Euler jets, Fermat quotients, and arithmetic jet spaces produce no independent
relation in either mandatory stress case.

### Hadamard and Fourier--Laplace closure changes the special value

The ordinary tensor product stays in neither arithmetic class.  With `F=E*L`, the logarithmic
singularity of `L` at `2` shows that `F` is not an E-function.  It is not a G-function either:

`F'=F+E/(2-z)`,  hence `E=(2-z)*(F'-F)`.

Were `F` a G-function, closure under derivative and polynomial multiplication would make `E` a
G-function, contrary to the factorial common denominator `N!` of the first `N` Taylor
coefficients of `exp(z)`.  Direct sums merely retain the mixed blocks.  A nonconstant algebraic
pullback cannot repair the logarithm: every finite map of algebraic curves has a point over `2`,
and locally `L(r(w))` has nontrivial logarithmic monodromy there.  The nonalgebraic substitution
`r(w)=2*(1-exp(-w))` does give `L(r(w))=w`, but moves `L(1)=log 2` to the transcendental
evaluation point `w=log 2`, outside Siegel--Shidlovskii specialization.

Coefficientwise Borel transform is the one genuine all-E conversion.  The Hadamard product

`H(z):=(E hadamard L)(z)=sum_(n>=1) z^n/(n*2^n*n!)`

is an E-function: in E-normalization its coefficient is `1/(n*2^n)`, whose first `N` common
denominator divides `2^N*lcm(1,...,N)`, and

`H'(z)=(exp(z/2)-1)/z`.

Moreover `E,H` are algebraically independent over `C(z)`.  Indeed, after adjoining
`W=exp(z/2)`, an algebraic primitive for `(W-1)/z` would yield by trace a rational primitive in
`C(z,W)`.  The standard pole-order argument in this exponential extension first makes such a
primitive Laurent-polynomial in `W`; comparison of its `W^0` coefficient would then require a
rational primitive of `-1/z`, impossible by residues.  Beukers's refined
Siegel--Shidlovskii theorem therefore
does prove the unconditional positive statement

`trdeg_Qbar Qbar(e,H(1))=2`.

But the transformed value is

`H(1)=Ei(1/2)-gamma+log 2`,

not `log 2`.  Thus the theorem proves independence after adjoining the new connection constant
`Ei(1/2)-gamma`; it gives no elimination of that constant from the original pair.

The inverse operation exposes why this loss is invariant.  Recovering `L` coefficientwise from
`H` multiplies the `n`-th coefficient by `n!`; its Hadamard multiplier
`sum_(n>=0)n!*z^n` has radius zero (and satisfies
`z^2*S'+(z-1)*S=-1`).  Analytically the inverse is the nonlocal Laplace integral

`L(1)=integral_0^infinity exp(-t)*H(t) dt=log 2`.

Hence factorial normalization converts a finite-radius G-value into an entire E-function only by
moving the original value to asymptotic/connection data at infinity.  Fischler--Rivoal's
arithmetic theory of E-operators makes this boundary general: finite connection constants are
E-values, whereas Stokes constants at infinity involve G-values and Gamma derivatives.  It is a
classification of the new constants, not a Siegel--Shidlovskii injectivity theorem for them.

The period control is identical.  For `A(z)=8*i*arctan(z)`, its Borel transform is the E-function

`K(z)=8*i*sum_(n>=0)(-1)^n*z^(2*n+1)/((2*n+1)*(2*n+1)!)=8*i*Si(z)`,

with `K'=8*i*sin(z)/z`.  At the algebraic point one obtains the new E-value `8*i*Si(1)`, while

`2*pi*i=A(1)=integral_0^infinity exp(-t)*K(t) dt`.

Thus even the pure period is recovered only as Laplace/Stokes data, not as the transformed
function's value at an algebraic point.

Finally, rational diagonals remain on the G-side: their coefficient denominators have exponential
growth, so they cannot represent `exp(z)`, whose ordinary denominators grow like `N!`.
Allowing exponential entries in the diagonal merely inserts the original E-period into the
integrand.  The unrestricted holonomic class is closed under tensor, Hadamard product, algebraic
pullback, and Fourier--Laplace transform, but has no value theorem; the functionally independent
holonomic pair `exp(z),exp(z^2)` with equal values at `1` is an exact counterexample to one.
Consequently the invariant obstruction is the arithmetic Gevrey order: algebraic operations
preserve the logarithm's finite monodromy, while factorial Borel damping removes it only by
changing point evaluation into a new connection/Stokes period.  None of these standard closure
operations produces an all-E pair with values exactly `(e,log 2)` and no extra constant.

### Difference-Galois independence collapses at the limit functional

Let

`e_n=sum_(k=0)^n 1/k!`,  `l_n=sum_(k=1)^n 1/(k*2^k)`.

Their exact scalar recurrences are

`(n+1)*e_(n+1)-(n+2)*e_n+e_(n-1)=0`,

`2*(n+1)*l_(n+1)-(3*n+2)*l_n+n*l_(n-1)=0`.

For the solution bases `(1,e_n)` and `(1,l_n)`, the Casoratians are respectively

`W_n^e=e_(n+1)-e_n=1/(n+1)!`,

`W_n^l=l_(n+1)-l_n=1/((n+1)*2^(n+1))`.

Thus both bases, and their block direct sum, are independent at every finite index; the joint
Casoratian is

`1/((n+1)!*(n+1)*2^(n+1))`.

It nevertheless tends to zero.  The two independent recurrence directions become proportional
to the constant solution at the boundary `n=infinity`, exactly where the desired values occur.

This is also the exact Picard--Vessiot calculation.  Over `C(n)` with `sigma(n)=n+1`, put
`a_n=1/n!` and `b_n=1/(n*2^n)`.  Fundamental matrices are

`Y_e=[[1,e_n],[0,a_n]]`,  `Y_l=[[1,l_n],[0,b_n]]`,

and the joint difference-Galois group is

`Aff_1 x Aff_1=(G_a semidirect G_m)^2`,

acting by `a -> c*a`, `e -> c*e+d` in each block.  The multiplicative characters are independent:
the shift ratio of `a^r*b^s` is
`2^(-s)*n^s/(n+1)^(r+s)`, which can be `sigma(f)/f` for rational `f` only when `r=s=0`
(compare degree and limit at infinity).  The two additive extensions do not split: rational
telescopers would solve

`r(n+1)-(n+1)*r(n)=1`,

`n*r(n+1)-2*(n+1)*r(n)=n`,

respectively.  Pole propagation makes any rational solution a polynomial, and degree comparison
then rules it out.  Hence the sequence-level Galois group is already maximal; there is no missing
functional or recurrence independence to extract.

The limit map itself is a noninjective ring homomorphism on convergent sequences, with every
geometric sequence `q^n`, `|q|<1`, in its kernel.  A sharp P-recursive counterfeit is

`u_n=e_n`,  `v_n=e_n+2^(-n)`.

The sequences `u,v` are algebraically independent over `C(n)` (their difference supplies the
independent multiplicative solution `2^(-n)`, while `u` supplies the nonsplit affine block), but
both limits equal `e`.  Thus even maximal difference-Galois independence can specialize to the
relation `X-Y=0`.  For the actual pair, a hypothetical `P(e,log 2)=0` says only that the nonzero
P-recursive sequence `P(e_n,l_n)` tends to zero; it does not make it an exact sequence identity.

The arithmetic normalization has no hidden small-value range.  Write
`Lambda_n=lcm(1,...,n)` and `D_n=2^n*Lambda_n`.  Then

`n!*e_n in Z`,  `D_n*l_n in Z`,

while the remainders satisfy

`e-e_n=(1+O(1/n))/(n+1)!`,

`log 2-l_n=(1+O(1/n))/(n*2^n)`.

If an integral relation `P` has bidegree `(d_e,d_l)` and vanishes at `(e,log 2)`, individual
transcendence forces `d_e,d_l>=1`.  Let `j` be the multiplicity of `log 2` as a root of the
nonzero polynomial `P(e,Y)`; then `1<=j<=d_l`, and the factorially smaller first remainder gives

`|P(e_n,l_n)|=Theta_P(2^(-j*n)*n^(-j))`.

The natural nonzero integer candidate

`Q_n=(n!)^(d_e)*D_n^(d_l)*P(e_n,l_n)`

therefore has logarithmic scale

`log|Q_n|=d_e*log(n!)+d_l*(n*log 2+log Lambda_n)-j*(n*log 2+log n)+O_P(1)`.

Since `log Lambda_n=n+o(n)` and `d_e>=1`, this tends to `+infinity`, dominated by
`d_e*n*log n`; integrality cannot force a contradiction.  The factorial error for `e_n` is paid
back exactly by its factorial denominator, while the slower logarithmic tail is overwhelmed by
that same mixed denominator.

The period control is even more visibly a boundary value.  Gregory's rational P-recursive sums

`p_n=4*sum_(k=0)^n (-1)^k/(2*k+1) -> pi`

satisfy
`(2*n+3)*p_(n+1)-2*p_n-(2*n+1)*p_(n-1)=0`, with Casoratian increment
`4*(-1)^(n+1)/(2*n+3)` and remainder `Theta(1/n)`.  Clearing the odd denominators costs
`exp((2+o(1))*n)`, so recurrence independence again gives no arithmetic endpoint.  General
results identifying limits of convergent P-recursive sequences with regular holonomic constants
classify `e`, `log 2`, and `pi` inside one closure class, but supply no injectivity of the limit
functional; the explicit `u_n,v_n` counterfeit proves that no such theorem can hold without an
additional arithmetic lower bound.

### Gamma and Beta identities isolate a missing special-jet theorem

The multiplication and reflection formulas give exact digamma coordinates for the period stress.
Writing `psi=Gamma'/Gamma`, logarithmic differentiation of

`product_(k=0)^(m-1) Gamma(z+k/m)
 =(2*pi)^((m-1)/2)*m^(1/2-m*z)*Gamma(m*z)`

and of `Gamma(z)*Gamma(1-z)=pi/sin(pi*z)` gives

`sum_(k=0)^(m-1) psi(z+k/m)=m*psi(m*z)-m*log(m)`,

`psi(1-z)-psi(z)=pi*cot(pi*z)`.

In particular,

`psi(1)-psi(1/2)=2*log 2`,  `psi(3/4)-psi(1/4)=pi`,

and explicitly

`psi(1)=-gamma`,  `psi(1/2)=-gamma-2*log 2`,

`psi(1/4)=-gamma-pi/2-3*log 2`,
`psi(3/4)=-gamma+pi/2-3*log 2`.

Thus the formulas cancel Euler's constant in the desired differences, but do not create any
nonlinear constraint.  In Gamma-jet coordinates the exact field is

`Qbar(Gamma(1/2),Gamma'(1),Gamma'(1/2))
 =Qbar(sqrt(pi),gamma,log 2)`.

Consequently a transcendence-degree-three theorem for these three jet values would prove the
period stress, but even the irrationality of the extra constant `gamma` is unknown.

Beta removes that extra constant completely.  Since

`B(x,y)=Gamma(x)*Gamma(y)/Gamma(x+y)`

and `B_x=B*(psi(x)-psi(x+y))`, one has the lossless identities

`B(1/2,1/2)=pi`,

`B_x(1/2,1/2)=-2*pi*log 2`.

Therefore

`Qbar(B(1/2,1/2),B_x(1/2,1/2))=Qbar(pi,log 2)`.

Algebraic independence of this Beta value and its parameter derivative is not merely sufficient:
it is exactly algebraic independence of `(log 2,2*pi*i)`.  No known Gamma/Beta special-value
theorem applies to this value--derivative pair.  Baker's theorem recovers their `Qbar`-linear
independence after the displayed reduction to logarithms, but not polynomial independence.

Holder's theorem is functional and cannot fill this gap.  It says that `Gamma(z)` satisfies no
algebraic differential equation over `C(z)`, so in particular `Gamma,Gamma'` are algebraically
independent as functions.  Yet at the algebraic point `z=1` their values already satisfy
`Gamma(1)-1=0`.  Thus differential hypertranscendence admits an immediate specialization defect
inside the very function under consideration.  The multiplication/reflection identities are
functional identities and may be differentiated before evaluation; a hypothetical numerical
relation among the remaining jets cannot be differentiated.

The strongest famous numerical Gamma result has disjoint scope.  Nesterenko proves the algebraic
independence of

`pi`,  `exp(pi)`,  `Gamma(1/4)`.

It contains neither digamma values nor `log 2`.  Although
`Gamma(1/4)*Gamma(3/4)=sqrt(2)*pi`, differentiating the corresponding functional formula
introduces `psi(1/4),psi(3/4)` rather than expressing them algebraically through the Gamma values.
Also `exp(pi)` is not an algebraic function of `(e,pi)`, so taking a transcendental `pi`-th root
does not transport Nesterenko's theorem to `e`.  The Lang--Rohrlich conjecture itself concerns
relations among Gamma values at rational points and `2*pi*i`; the derivative/digamma extension
needed here is strictly stronger.

For the mixed stress, `e` has no nontrivial finite Gamma-value encoding.  The tautology
`e=exp(Gamma(1))` leaves the class of Gamma values, while Stirling gives only the moving-point
boundary formula

`e=lim_(n->infinity) n/Gamma(n+1)^(1/n)`.

Every `Gamma(n+1)=n!` in this limit is algebraic, so special-value information at the finite
points plainly does not control the limit.  Combining it with
`log 2=-B_x(1/2,1/2)/(2*B(1/2,1/2))` would require a mixed exponential--Beta-jet injectivity
theorem whose conclusion is exactly algebraic independence of `(e,log 2)`.  Hence reflection and
multiplication do eliminate `gamma` at the level of identities, but neither Holder's functional
theorem nor known Gamma-value independence supplies the missing numerical jet specialization.

The strongest unconstrained Ax--Schanuel deformation makes the constants obstruction exact.  For
independent parameters `t_i`, set
`X_i=z_i+t_i` and `Y_i=exp(z_i)*exp(t_i)`.  Over the constant field containing
`z_i,exp(z_i)`, functional Ax has Jacobian rank `n` and gives the maximal relative degree `2n`;
the generic field is simply `K(t_i,exp(t_i))` for `K=Q(z,exp z)`.  Specializing `t=0` kills all
`2n` relative generators and leaves residue field `K`, so the functional inequality contains no
term capable of bounding `trdeg_Q K`.  A rational polynomial relation at the center pulls back
to an exponential polynomial with one zero there, not an identity.  Taking its `M`-th power
raises contact and degree by the same factor, so multiplicity and zero estimates remain exactly
balanced.

The two mandatory logarithmic stresses show equality in the functional theorem.  Near `(1,2)`,
the family `(u,Log(v),exp(u),v)` specializes to `(1,log 2,e,2)`.  If
`A(e,log 2)=0`, then `A(exp(u),Log(v))=0` defines, after normalization if necessary, an analytic
curve through that point.  Along the curve the logarithmic coordinates have derivative rank one;
Ax--Schanuel gives degree at least three, while the single displayed relation gives degree at most
three.  Thus it is sharp, not contradictory.  Likewise
`(Log(a),Log(b)+2*pi*I,a,b)` at `(a,b)=(2,1)` treats `(log 2,2*pi*I)`: a hypothetical relation
continues to a rank-one zero curve and again saturates the bound.  Logarithmic monodromy would
propagate a relation only if it were already a germ identity; a zero at the selected branch does
not continue around a loop.

Even the differential equations, finite exponential type, and trivial monodromy admit a sharp
counterfeit.  Over the constant field `Qbar(T)`, the functions
`X=(T+t_1,T^2+t_2)` and `Y=((T+1)*exp(t_1),(T+2)*exp(t_2))` satisfy
`dlog(Y_i)=dX_i`, have full two-parameter functional Ax degree, and specialize to a tuple whose
`Q`-field is `Q(T)` of degree one, although `T,T^2` are rationally linearly independent.  The
only missing condition is the numerical normalization `Y_i(0)=exp(X_i(0))`; imposing that
condition returns exactly the original value problem.  Hence a useful specialization theorem
would have to force injectivity on the constant residue field from this normalization, which in
the mixed and period stresses is precisely algebraic independence of `(e,log 2)` and of
`(log 2,2*pi*I)` respectively.

Local analytic intersection theory cannot manufacture the missing germ.  If a hypothetical
relation made `Q(log 2,e)` one-dimensional, its locus would be an algebraic curve, smooth at the
chosen point, cut out by
`Z_1=1`, `Y_2=2`, `P(Z_2,Y_1)=0`.  Pulling this ideal back to the exponential graph at
`(1,log 2)` gives the maximal ideal `(u,v)`: the intersection is isolated, reduced, and has local
length one.  This is sharp—`log 2` is itself generic over `Q` on the affine line and is a simple
zero of `exp T-2`.  Excess codimension gives only the vacuous lower bound `d-n`, and monodromy or
analytic continuation requires a germ identity that a single generic zero does not provide.

Replacing the exponential graph by algebraic Taylor or Padé graphs does not preserve this point:
the intersection is overdetermined because `d+n<2n`, so it has no local topological intersection
number and a generic perturbation removes it.  One may discard `n-d` equations and choose an
`n`-dimensional complete intersection `W` containing the locus; then a proper intersection with
an approximating graph can persist and produces algebraic points, but those points lie on `W`,
not on the original locus.  In the mixed stress, choosing
`W=(X_1-1,Y_2-2)` merely produces algebraic roots of `T_N(X_2)=2` and forgets `P`; choosing
`W=(X_1-1,P(X_2,Y_1))` produces a root of `P(X_2,T_N(1))` but forgets `Y_2=2`.  Restoring the
omitted equation asks for a quantitative lower bound on its small algebraic value, exactly the
quadratic-approximation/Padé boundary above.  Algebraic graph approximation therefore trades the
specialization defect for the same missing small-value inequality rather than supplying a stable
intersection class.

The failure can be made exact for diagonal Padé graphs.  Put
`A_m(X)=sum_(k<=m)(2m-k)!/(k!*(m-k)!)*X^k`, `B_m(X)=A_m(-X)`,
`R_m=A_m/B_m`, and `H_m=(2m)!/m!`.  The integral remainder and beta concentration give, uniformly
at each fixed nonzero `x`,
`epsilon_m(x):=R_m(x)-exp(x)=(-1)^(m+1)*x^(2m+1)*exp(x)/((2m+1)*H_m^2)*(1+O_x(1/m))`.
For the mixed locus write
`P(Y,X)=a+bY+cX+dYX`, `ell=log 2`, `A=P_Y(e,ell)=b+d*ell`, and
`C=P_X(e,ell)=c+d*e`.  Irreducibility and transcendence of `e,ell` force `A*C != 0`.  Moreover
`epsilon_m(ell)/epsilon_m(1)=(2/e)*ell^(2m+1)*(1+o(1))`.  The three coordinate complete
intersections give respectively

* retaining `(X_1-1,Y_2-2)` produces `beta=R_m(1)` and a root
  `alpha=ell-epsilon_m(ell)/2+o(epsilon_m(ell))` of `R_m(alpha)=2`; the omitted value is
  `P(beta,alpha)=A*epsilon_m(1)-(C/2)*epsilon_m(ell)+o(epsilon_m(1))`;
* retaining `(X_1-1,P)` produces the rational point
  `gamma=-(a+b*beta)/(c+d*beta)`; the omitted value is
  `R_m(gamma)-2=(-2/C)*(A*epsilon_m(1)-(C/2)*epsilon_m(ell))+o(epsilon_m(1))`;
* retaining `(Y_2-2,P)` first chooses the same algebraic `alpha` and then a root near `1`; the
  omitted value `X_1-1` is
  `-(A*epsilon_m(1)-(C/2)*epsilon_m(ell))/(e*A)+o(epsilon_m(1))`.

Thus no coordinate choice cancels the leading term: all three defects are nonzero and of size
`Theta(H_m^(-2)/m)`.  Intrinsically, if `f=(X_1-1,Y_2-2,P)` and one restricts to a nearby graph,
the left null vector `(-A*e,-C/2,1)` of the two parameter tangent matrix gives the same normal
obstruction `Omega_m=A*epsilon_m(1)-(C/2)*epsilon_m(ell)`.  A fixed transverse pair of linear
combinations of the `f_i` only redistributes `Omega_m` among the omitted coordinates.  Making the
pair depend on `m` can balance the two displayed errors only with a coefficient of size
`asymp ell^(-2m)`; this adds logarithmic height `Theta(m)` and gains only `Theta(m)` beyond
`2*log H_m`.  More invariantly, after a primitive integral change of the three generators by a
matrix of height `Q_m`, retaining two rows gives
`f=g_3*column_3(L_m^(-1))` on the complete intersection.  The adjugate bound is `O(Q_m^2)`, so a
smaller tuned omitted generator merely requires multiplication by `O(Q_m^2)` to recover an
original locus equation; the same coefficient height occurs in every conjugate factor of the
resultant.  Extremely good conditioning obtained by evaluating higher-degree rational
polynomials at `(e,ell)` would itself require an unavailable small-value bound for that mixed
point.  If a tuning makes the transverse linearization singular enough for quadratic terms to
cancel `Omega_m`, the branch displacement is at least `Omega_m^(1/2)` and some original locus
equation has the larger size `Omega_m^(1/2)`.

The arithmetic counts make the missing range explicit.  In the first choice, `alpha` has degree
at most `m`, while `beta` has numerator and denominator `O(H_m)`.  Clearing the denominator turns
the omitted value into a linear polynomial `Q_m(alpha)` of coefficient height `O(H_m)` and size
`Theta(1/(m*H_m))`.  Its resultant with `A_m-2B_m` has `m` conjugate factors, so integrality only
forces a lower scale `H_m^(-m+O(1))`: the required strict inequality would be `1>m`.  In the
second choice the point is rational of height `O(log H_m)`, but evaluating the omitted degree-`m`
graph equation introduces denominator height `H_m^(m+O(1))`, again requiring `2>m+O(1)`.  In the
third choice the total algebraic degree is at most `m^2`, which is worse.  Taylor graphs have
`H=N!` and only `H^(-1+o(1))` rather than Padé's `H^(-2+o(1))`, so they have no hidden range either.
The bilinear assumption only makes the coordinates explicit.  For an arbitrary irreducible
`P(e,ell)=0`, the point is generic on its plane curve; if either partial derivative vanished there,
`P` would divide that lower-degree derivative, forcing `P` to omit one variable and making `e` or
`ell` algebraic.  Hence both partials are again nonzero, the same first-order `Omega_m` results,
and all displayed algebraic degrees are merely multiplied by the fixed partial degrees of `P`.

The boundary with all exponential values algebraic gives the same obstruction in `n` variables.
Over the fixed number field containing `a_i=exp(z_i)`, the complete intersection `Y_i=a_i`
(and, over `Q`, its fixed-degree conjugate descent) drops every hypothetical algebraic relation
among the `z_i`.  The Padé intersection has branches `alpha_(i,m)` satisfying
`R_m(alpha_(i,m))=a_i` and
`alpha_(i,m)-z_i=-epsilon_m(z_i)/a_i+o(epsilon_m(z_i))`; their joint degree is at most `m^n`.
If a fixed polynomial relation `Q(z)=0` has order `r`, then
`Q(alpha_m)=O(H_m^(-2r)*exp(O(m*r)))`.  But its product norm over the Cartesian root set has
`m^n` factors; multihomogeneous resultant height costs
`O(deg(Q)*m^(n-1)*log H_m)`.  Since `r<=deg(Q)`, a strict comparison would require
`2r>deg(Q)*m^(n-1)`, impossible for large `m` when `n>=2`.  The actual algebraic points also obey
`exp(alpha_(i,m))-a_i=-epsilon_m(alpha_(i,m)) != 0`, so no uniform Lindemann stable endpoint can
force the Padé equations to become exponential equations; these moving degree/height examples
already realize the purportedly forbidden small values.  At the other tight boundary, algebraic
`z_i`, the `Q`-locus has dimension exactly `n` and meets every Padé graph properly at the genuine
algebraic points `(z_i,R_m(z_i))` (and their conjugates), with no equation omitted.  Their limit is
the Lindemann--Weierstrass equality case, so persistence of algebraic intersections by itself
cannot yield a dimension contradiction.

Derived or excess intersection theory cancels exactly in the forbidden range.  In the regular
analytic local ring of the `2n`-dimensional ambient group, let `A` be the local ring of the
exponential graph and `B` that of a `d`-dimensional rational locus, with isolated intersection.
Serre's vanishing theorem gives
`chi(A tensor^L B)=sum_i(-1)^i*length Tor_i(A,B)=0` whenever `d<n`.  In the smooth lci model, the
restricted equations are `n` local parameters plus `n-d` redundant zeros, so the excess homology
is the exterior algebra of an `(n-d)`-space and its Euler characteristic is exactly
`(1-1)^(n-d)=0`.  Any nonzero `n x n` minor has necessarily discarded the excess equations and
measures a chosen supervariety rather than the actual locus.

For `(1,log 2;e,2)`, the known surface `(X_1-1,Y_2-2)` has proper multiplicity one with the graph;
adding a hypothetical curve relation creates one excess Koszul factor and changes the Euler
characteristic to zero.  Thus nonzero derived intersection is equivalent here to the desired
two-dimensional locus.  The Lambert surface above also has transverse multiplicity one despite
being noncoisotropic; if its actual locus were a curve, the extra excess factor would again
cancel.  Algebraic independent inputs have multiplicity one only after Lindemann--Weierstrass has
already identified their `n`-dimensional locus.  Crofton averaging cannot retain the point and
cut the locus: every rational polynomial through the generic point already lies in its ideal,
while a generic rational slice misses it.  The excess class `lambda_(-1)(E*)` has rank
`(1-1)^(n-d)=0`, and sums of squared minors depend on rescalable choices of generators rather than
on an arithmetic intersection invariant.

A multiplicity estimate formulated intrinsically on that locus is either meaningless or already
the desired theorem.  If `I` is the evaluation ideal, a nonzero class in `Q[X,Y]/I` cannot even
have positive order at the chosen generic point: vanishing of its zeroth jet means the class is
zero.  First jets descend to the quotient only if every `Delta_i` preserves `I`; if they all did,
their values on the `X_j` would give `n` linearly independent derivations of `Frac(Q[X,Y]/I)`, so
`n <= dim Der_Q(K)=trdeg_Q K` immediately.  In the mixed stress locus,
`Delta_1(X_1-1)=1` and `Delta_2(Y_2-2)=2` at the point, explicitly showing the failure of descent.

Representative-based bounds are false even when the locus meets the leaf transversely with
length one.  At the unconditional non-independent test point `(1,2,e,e^2)`, the evaluation ideal
is `(X_1-1,X_2-2,Y_2-Y_1^2)`, and its leaf pullback is again `(t_1,t_2)`.  Nevertheless box-degree
`R` polynomials have `(R+1)^4` coefficients, while every total `Delta`-jet value lies in the
`(3R+1)`-dimensional span of `1,e,...,e^(3R)`.  Thus a nonzero rational polynomial can have all
total jets below `T` zero whenever
`(R+1)^4>(3R+1)*T*(T+1)/2`, giving multiplicity of order `R^(3/2)`.  Its leaf restriction is not
identically zero by exponential-polynomial independence.  This reconciles the simple
scheme-theoretic intersection with the Hilbert count: the latter selects the zero quotient class,
represented by hypersurfaces containing the locus but having arbitrarily high tangency.  Any
low-degree relative multiplicity theorem using rational independence strongly enough to exclude
this phenomenon would itself supply the missing Schanuel inequality.

The monodromy calculation is exact.  Irreducibility forces both partial derivatives of
`P(e,log 2)` to be nonzero, so the algebraic branch through the point is unique.  The comparison
germ `C(X)=Log(1+Log X)` has `C(e)=log 2`, but equality of values imposes no equality of first
derivatives.  A loop around the transcendental point `X=e^-1` leaves the algebraic branch
unramified while sending `C` to `C+2*pi*I`; hence the two germs cannot agree and their intersection
has finite multiplicity.  Taking powers merely makes that isolated intersection nonreduced.
Norming over every algebraic branch reconstructs `P(X,C(X))`, while successive logarithm branches
give `P(e,log 2+2*pi*I*k)`, nonzero for all but finitely many `k`.  Thus neither all-branch norms
nor continuation turns the one value relation into accumulating zeros of a fixed function.

The full exponential covering makes the same obstruction structural.  Let
`q:C_X^n x C_U^n -> C_X^n x (C^*)_Y^n` be `q(X,U)=(X,exp U)` and let
`Gamma=(2*pi*I*Z)^n` act by translating `U`.  If `W` is connected and smooth, the components of
`q^(-1)(W)` correspond to cosets of
`H=image(pi_1(W)->pi_1((C^*)^n)) subset Z^n`, where the map is induced by the coordinate units
`Y_i`; `H` is the deck stabilizer of each component.  Every component still has dimension
`dim W`, because `q` is locally biholomorphic.  The group `H` records only winding numbers of the
algebraic functions `Y_i` and is unrelated to rational independence of the value coordinates
`X_i`.  Discrete invariance gives no tangent vector and no larger analytic component.  For example
the curve `X=Y+Y^(-1)` has full winding subgroup `Z`, so its logarithmic lift
`X=exp U+exp(-U)` is invariant under `U -> U+2*pi*I`, but a direct substitution shows that the
curve has no nontrivial translation stabilizer in `G_a x G_m`.

The desired branch condition is the diagonal `D={U=X}`, which is not deck invariant.  The deck
orbit of `(z,z)` is `(z,z+2*pi*I*k)` and lies on the parallel diagonals
`D_k={U=X+2*pi*I*k}`, not at new points of `D`.  Its quotient collapses back to the single original
point.  The `Gamma`-saturation `union_k D_k` is Zariski dense in `A^(2n)`: for fixed `X`, a
polynomial vanishing at every `U=X+2*pi*I*k` vanishes on the Zariski-dense integer lattice in
`U`, and hence identically.  At a fixed `X=z`, the orbit's algebraic closure is already the full
vertical `U`-fiber.  Thus replacing the deck orbit by a fixed algebraic object destroys all the
equations; retaining only `B` translates gives an object whose degree grows at least linearly in
`B`.

The mixed pullback is completely explicit.  For
`W=(X_1-1,Y_2-2,P(Y_1,X_2))`,

`q^(-1)(W)=(X_1-1, exp(U_2)-2, P(exp(U_1),X_2))`.

At `(X,U)=((1,ell),(1,ell))`, restriction to `D` gives
`X_1-1`, `exp(X_2)-2`, and `P(exp(X_1),X_2)`.  The first two generate the maximal ideal because
their Jacobian is `diag(1,2)`, so the intersection is isolated, reduced, and of length one.
The constant coordinate `Y_2=2` makes the second component of `H` zero; any winding in `Y_1`
does not alter this local calculation.  A translated component can meet `D` only with the first
deck index zero and at a root `P(e,ell+2*pi*I*k)=0`.  The polynomial `P(e,T)` is nonzero and hence
has only finitely many such roots.  Thus the complete deck orbit produces no accumulating family
of diagonal intersections.

For the period stress
`W=(Y_1-2,Y_2-1,P(X_1,X_2))`, every lift component is

`U_1=ell+2*pi*I*k_1`, `U_2=2*pi*I*k_2`, `P(X_1,X_2)=0`.

Both units are constant, so `H=0` and the components are indexed by all of `Z^2`.  The target lies
on `(k_1,k_2)=(0,1)`, and its intersection with `D` again fixes both `X` coordinates on the smooth
generic plane curve, giving local length one.  Other components meet `D` only when
`P(ell+2*pi*I*k_1,2*pi*I*k_2)=0`.  Even infinitely many such isolated lattice points would not
force a subgroup: a fixed algebraic curve such as `Y=X^2` already contains infinitely many
integer-lattice points, with no finite accumulation.  Rational independence rules out the
relevant rational line, not nonlinear lattice curves.  Crucially, deck invariance itself supplies
none of these shifted diagonal zeros.

Finite algebraic covers do not retain the branch either.  Quotienting the deck group modulo `N`
is the Kummer cover `V_i^N=Y_i`, of degree `N^n`.  Selecting the desired sheet requires the
branch-specific values `exp(z_i/N)`, which are not defined over the base field; norming over all
sheets forgets the selection and returns the original equations in `Y_i`.  In the period case
these are algebraic roots of unity, but choosing the sheet requires adjoining cyclotomic fields of
unbounded degree.  Letting `N` grow to recover logarithms makes the cover degree grow as `N^n`.
Hence fundamental-group monodromy presents an exact alternative: quotient by all deck
translations and lose the analytic logarithm branch, or retain more branches at unbounded degree.
It cannot turn an isolated exceptional intersection into a fixed finite-degree anomalous locus.

Arithmetic formal-leaf/slope methods reproduce the same jet deficit and fail their algebraization
hypotheses.  For `Delta_i=d/dX_i+Y_i*d/dY_i`, reduction modulo every prime satisfies
`Delta_i^p=Y_i*d/dY_i`, which is not in the span of the `Delta_j`; the foliation has nonzero
p-curvature at every prime.  Normalized jets gain `1/k!` archimedean size but pay exactly `k!` in
finite-place denominators, while ordinary jets merely move the same cost.  The optimized slope
construction again gives `T<D^(2-d/n)` against the sharp `T>=D^2` leaf zero threshold.  Translating
the leaf to the rational identity moves the low-dimensional locus to the transcendental field
`K`; retaining a `Q`-model leaves the center transcendental.  Neither setting has the arithmetic
point required by formal-leaf algebraization.

Reducing the rational locus modulo primes supplies no replacement exponential graph.  The
transcendental complex point has no canonical reduction; closed-point specializations of a model
over a transcendence base do not preserve analytic `exp`.  Absolute Frobenius stabilizes every
`F_p`-variety tautologically, whereas the relevant characteristic-zero group map
`[p](X,Y)=(pX,Y^p)` reduces to `(0,Y^p)` and is generally not a self-map.  In the conditional
`(1,log 2;e,2)` curve, `[p]` is disjoint from the locus because it sends `X_1=1` to `X_1=0`, and
the exponential distribution has zero tangent intersection with the curve; Frobenius itself has
zero differential.  Lang--Weil therefore returns only the ordinary order-`p` points of a curve.
More fundamentally, every homomorphism from the additive group of `Fbar_p` to its multiplicative
group is trivial, since the former is `p`-torsion and the latter has no nontrivial `p`-torsion.
Truncated divided-power exponentials live only on nilpotent thickenings and reduce to `Y=1` on
field-valued points.  Thus neither reductions nor Frobenius intersections retain the complex
analytic datum needed to bound the dimension of the original locus.

Real o-minimality has the sharp constants obstruction at definable rank zero.  In `R_exp`, both
`e=exp(1)` and `log 2=exp^{-1}(2)` lie in parameter-free definable closure, so the stress singleton
`{(log 2,e)}` has `dcl`- and exponential-algebraic-closure dimension zero even though the required
pure-field transcendence degree is two.  In general `dcl(z,exp z)=dcl(z)`, and rational linear
independence gives no lower bound on this pregeometry rank.  O-minimal dimension proves the bound
on the generic stratum of the exponential graph, but dimension is a set/generic-point invariant;
model completeness, Pfaffian zero bounds, and Pila counting do not transfer it to a prescribed
zero-dimensional definable fiber.  Definable closure has no Northcott height property.

Difference and Mahler formulations collapse for the same reason.  For a polynomial `F`, the
integer-dilate values `F(k*z, exp(z)^k)` form an exponential-polynomial recurrence, but an assumed
relation gives only its value at `k=1`; further zeros would assert, without justification, that the
relation ideal is stable under `(x,y) -> (k*x,y^k)`.  Transporting the relation to rationally
scaled points makes its exponential degree grow linearly at the reciprocal of the distance to the
identity.  Difference Picard--Vessiot dimension lives over a constant field already containing
the nodes and is annihilated by evaluation at a fixed integer.  The natural Mahler identity
`exp(z*q*T)=exp(z*T)^q` is nonlinear and closes no finite monomial system, while its Taylor
coefficients contain the arbitrary constants `z`.  Hence recurrence zeros, difference Galois
groups, and Mahler specialization do not provide the missing numerical independence.

Combining the differential and difference equations still leaves the logarithms in the constant
field.  For `sigma(t)=t+1`, `delta=d/dt`, a scalar system `sigma(y)=a*y`, `delta(y)=b*y` is
compatible exactly when `delta(a)/a=sigma(b)-b`; for constant `a,b` this is the tautology zero
equals zero and does not encode `a=exp(b)`.  If only the shift equation is given and `a` is
algebraic, then `delta(y)/y` is a `sigma`-constant, so parametrized PV theory takes the desired
logarithm as part of its base constants.  This is sharp: over `Qbar(T)`, the diagonal constant
systems with `A=diag(T,2)` and `B=diag(1,T)` have maximal difference and differential groups
`Gm^2`, although their coefficient field has transcendence degree one.  Maximal functional
groups therefore do not bound the coefficient transcendence degree.

Finite exponential type selects an analytic branch only externally: a finite-type solution of a
constant shift equation is a finite Fourier sum of branches `exp((b+2*pi*I*k)t)`, and the
differential equation chooses one summand.  In the period stress, `exp(2*pi*I*t)` is itself a new
shift constant; in the mixed stress, both functional groups are maximal but compatibility says
nothing about independence of `e` and `log 2`.  Root rescaling makes
`exp((log 2)t/q)` have type `(log 2)/q`, while norming the `q` logarithmic branches restores total
type `log 2` (and an additional `pi` contribution for the negative norm sign).  Parameter
derivations cease to move the multiplier after algebraic specialization.  Thus simultaneous
differential--difference Galois theory captures branch selection, not arithmetic independence of
the constants selected.

### Algebraic groups and motives

The smallest connected subgroup of `Ga^n x Gm^n` containing the point can have dimension at least
`n` while the point itself has much smaller transcendence degree, so the analytic subgroup theorem
does not supply the pointwise bound. The relevant 1-motive period-dimension equality would imply
the desired statement but is a conjectural replacement of the target, not a proof mechanism used
here.

Universal vector extensions make this boundary completely explicit.  For a toric 1-motive
`M=[Z^r -> Gm^s]`, the universal extension is `Gm^s x Ga^r`, and in Betti/de Rham bases its
comparison matrix is
`[[2*pi*I*I_s,Z],[0,I_r]]`; its determinant is `(2*pi*I)^s`, independent of every logarithm in
`Z`.  Exterior and tensor determinants are only powers of this determinant.  In a family,
horizontality gives `dZ=dA/A` for an analytic logarithm germ, but the algebraic coordinate `z` on
the rational locus agrees with that germ only at the selected point, so it cannot be
differentiated there.  Over `K=Q(z,a)`, `a=exp z`, the exact missing forms are
`omega_i=da_i/a_i-dz_i`; their independence in `Omega_(K/Q)` would immediately give
`n<=trdeg_Q K`, but universal-extension comparison supplies no such independence theorem.

The determinants are already sharp on the two mandatory stresses.  For `(1,log 2)`, the forms
are `(de/e,-d log 2)`, independent exactly when `e` and `log 2` are algebraically independent.
For `(log 2,2*pi*I)`, they are `(-d log 2,-d(2*pi*I))`, giving exactly the period stress target.
The Kummer motive `[Z -> Gm]`, `1 -> 2`, has tensor-period torsor
`Spec Qbar[t,t^-1,u]` with evaluation `(t,u) -> (2*pi*I,log 2)`; genericity of that point is
literally the desired algebraic independence.  Passing to a transcendental base does not help:
for the mixed motive with units `(e,2)`, the formal logarithm of `e` evaluates to `1`, so after
quotienting this known relation the remaining chart evaluates `(A,U) -> (e,log 2)` and is generic
exactly when the mixed stress bound holds.  A height on the tensor torsor first needs nonvanishing
of every polynomial at this transcendental point, which is the same missing injectivity.  The
unconditional 1-motive period theorem controls linear periods only; tensor-period injectivity is
the period-conjecture-strength replacement explicitly forbidden by the target.

Nonabelian and mixed-Tate periods encode more monomials but do not make their numerical
evaluation injective.  For the Kummer motive of `2`, the period torsor is already
`Spec Qbar[t,t^-1,u]`, `(t,u)=(2*pi*I,log 2)`; every monomial `t^a*u^b` occurs as a matrix entry of
tensor powers.  Hence a polynomial relation is a linear relation among tensor-period entries, but
the unconditional 1-motive theorem controls only the affine-linear period space before tensoring.
On `P^1-{0,1,infinity}`, pure iterated-integral words give
`(2*pi*I)^a/a!` and `(log 2)^b/b!`; the shuffle law records their multiplication without proving
that evaluation at the fixed endpoint has zero kernel.  Mixed words introduce genuinely new
periods (`Li_3(1/2)` already brings in `zeta(3)`), while quotienting them away returns the same
two-variable Kummer torsor.  Functional Chen injectivity and formal motivic-Galois faithfulness
do not imply numerical injectivity at one path.  The mixed stress `(1,log 2)` is even outside the
ordinary mixed-Tate algebra: encoding `e` needs an irregular exponential motive or a new endpoint
coordinate, after which injectivity on `Qbar[e,log 2]` is literally the desired statement.

Symplectic or Poisson involutivity of the numerical locus is false even for an actual
rationally independent exponential point.  Choose `u in (0,1)` solving
`u=exp(-2*exp(-u))` and set `v=2*exp(-u)`.  Then `u*exp(v)=1` and `v*exp(u)=2`; the pair `(u,v)`
is rationally linearly independent, since a rational ratio would combine the two equations into
an algebraic nonzero exponential of an algebraic number, contradicting Hermite--Lindemann.  The
point lies on the smooth irreducible rational surface
`V=(X_1*Y_2-1,X_2*Y_1-2)` in `Ga^2 x Gm^2`.  For
`omega=sum dX_i wedge dlog Y_i`, its restriction is
`(1/X_1-1/X_2)*dX_1 wedge dX_2`, nonzero at the point; equivalently the Poisson bracket of the two
displayed equations is `Y_1*Y_2*(X_2-X_1)`.  Thus `V` is not Lagrangian/coisotropic.  The actual
`Q`-locus is contained in `V`: if it has dimension below two it cannot be coisotropic in a
symplectic fourfold, and if it has dimension two it equals the same noncoisotropic surface.

The intersection with the exponential graph is transverse: the Jacobian determinant of
`(x_1*exp(x_2)-1,x_2*exp(x_1)-2)` is `2*(1/(u*v)-1)`, which is nonzero.  Point membership is
zeroth-order data and gives no invariance of the ideal under the graph-tangent vector fields.
In the two named stresses, natural half-dimensional containing varieties are Lagrangian, but the
*actual* locus is coisotropic exactly when its dimension is the desired two, so invoking that
property is circular.  D-module characteristic supports do not restore it: they must be conic
and involutive, whereas this numerical locus is neither, and principal symbols of exponential
connections forget the numerical value data and yield the zero section instead.

For the Zariski locus `V` of `(z, exp z)`, demanding rotundity
`dim [M]V >= rank M` for every integer matrix `M` is already the family of Schanuel inequalities;
the case `M = I` is the target itself. Analytic intersection theory gives no lower bound when the
intersection with the exponential graph is isolated. Functional Ax--Schanuel is also vacuous
there because all coordinate germs are constants, so their rank modulo the constant field is
zero. Group-law and freeness arguments alone cannot repair this: discontinuous exponential
homomorphisms can send a rationally independent tuple to algebraic, multiplicatively independent
values.

Minimal-counterexample predimension sharpens this only to defect one.  For a rational subspace
`U` of `span_Q(z)`, let `d(U)` be the transcendence degree of the coordinate-exponential field of
an integer basis of `U`; rational changes of basis make this well defined up to algebraic
extension.  If `z` is a counterexample of minimal rational dimension `n`, every proper `U`
satisfies `d(U)>=dim U`.  Taking a rational hyperplane gives
`n-1<=d(U)<=d(V)<n`, hence necessarily

`d(V)=n-1` and `d(U)=n-1` for every rational hyperplane `U`.

The full field is algebraic over each hyperplane projection field.  More generally every integer
matrix `M` of rank `r<n` has `dim [M]V>=r`, while a full-rank `M` is an isogeny and has image
dimension `n-1`.  Thus a minimal locus is exactly "properly rotund": every proper-rank inequality
holds and every full-rank inequality fails by one.  Transcendence-degree submodularity cannot fill
that last unit: explicitly
`d(U+W)+d(U intersect W)<=d(U)+d(W)`.  The displayed algebraic matroid has rank `n-1`, and after
any rational basis change deleting one coordinate direction still leaves full rank `n-1`, so no
direction is essential.  The profile `rho(U)=min(dim U,n-1)` is itself submodular, with
predimension zero on every proper subspace and `-1` only at the identity.

For `n=2` this has an elementary curve classification.  For an irreducible `Qbar`-curve `C` in
`Ga^2 x Gm^2`, put
`A_C={m in Z^2 : m dot X is constant on C}` and
`M_C={m in Z^2 : Y^m is constant on C}`.  The row projection
`phi_m=(m dot X,Y^m)` has zero-dimensional image exactly when `m` lies in
`A_C intersect M_C`; hence all proper inequalities are equivalent to
`A_C intersect M_C={0}`.  If `C` contains a genuine exponential point with rationally independent
inputs, any common nonzero `m` would make both `m dot z` and `exp(m dot z)` algebraic.
Hermite--Lindemann then forces `m dot z=0`, a contradiction.  Consequently every proper
projection inequality for a hypothetical two-dimensional counterexample is already automatic.

The conditional mixed curve makes the structure explicit.  If an irreducible
`P(e,log 2)=0` existed, then
`C=(X_1-1,Y_2-2,P(Y_1,X_2))` would have dimension one.  Its constant lattices are generated by
`(1,0)` additively and `(0,1)` multiplicatively, so their intersection is zero: for a row
`(a,b)`, `a+b*X_2` varies when `b!=0`, while `Y_1^a*2^b` varies when `b=0,a!=0`.
Its algebraic matroid has the constant loops `X_1,Y_2` and the parallel pair `X_2,Y_1`.
On the exponential graph the first two equations pull back to a regular parameter pair; the
third lies in their ideal.  The derived local complex is therefore `K(u,v,0)`, with one copy of
`C` in degrees zero and one and Euler characteristic zero.  The conditional period curve
`(Y_1-2,Y_2-1,P(X_1,X_2))` behaves identically, with the two multiplicative loops and one
additive parallel pair.

There is an exact algebraic counterfeit in every dimension.  Let
`H=(product_i X_i=1)` and choose a generic complex point `z` of `H`, avoiding all rational
hyperplanes, so the `z_i` are rationally independent and `Q(z)` has degree `n-1`.  Fix nonzero
rational constants `c_i` and put `W=H x {Y_i=c_i}`.  Every rank-`r<n` rational linear projection
of `H` is dominant: for rank `n-1`, a generic line parallel to the kernel meets the product
hypersurface in finitely many points, and lower ranks follow by composition.  Hence `W` realizes
exactly `rho(U)=min(dim U,n-1)` and every proper rotundity inequality.  Divisibility of `C^*`
extends the assignments `E(z_i)=c_i` to an abstract exponential homomorphism on the rational
span.  For `n=2` the concrete curve
`X_1*X_2=1,Y_1=2,Y_2=3` at `(T,T^-1;2,3)` already supplies the model.  Only continuity and the
pointwise analytic normalization distinguish it, and those give no submodular relation capable
of recovering the missing identity projection.

Closed logarithmic forms do not strengthen this defect-one structure.  On a smooth model of an
`(n-1)`-dimensional locus put `theta_i=dlog(Y_i)-dX_i`.  Each `theta_i` is closed.  If they have
maximal function-field rank `n-1`, their unique relation is represented projectively by the
cofactor web/Gauss map

`gamma=[(-1)^(i-1)*theta_1 wedge ... wedge hat(theta_i) wedge ... wedge theta_n]_i`.

Differentiating a relation `sum a_i*theta_i=0` yields only
`sum da_i wedge theta_i=0`; it does not make the rational functions `a_i` constant.  Each
individual kernel foliation is integrable, but at maximal rank the common characteristic
distribution `intersection_i ker(theta_i)` is zero, so there is no leaf along which a pointwise
exponential identity can propagate.

There is one rigorous constant-coefficient consequence, and proper rotundity already exhausts
it.  If an integer vector `m` satisfied `sum m_i*theta_i=0`, then in the function field
`dlog(Y^m)=d(m dot X)`.  On a smooth projective model, residues force `Y^m` to have no zeros or
poles and hence to be constant; then `m dot X` is constant as well.  Thus a nonzero constant
integer relation is exactly a forbidden zero-dimensional row projection.  Proper rotundity says
the `theta_i` are independent over `Q`, not that their unavoidable relation over `Q(W)` descends
to `Q`.  In fact even descent merely to the complex constant field would not yet define an
algebraic subgroup: one still needs the projective coefficient vector to be rational (hence,
after scaling, integral), and neither closedness nor Frobenius supplies that arithmetic descent.

The mixed conditional curve gives the exact varying relation.  Write `s=Y_1`, `t=X_2`, with
`P(s,t)=0`; then `theta_1=dlog(s)` and `theta_2=-dt`, so on the normalization

`s*P_s*theta_1-P_t*theta_2=0`.

Its projective coefficient ratio `[s*P_s:-P_t]` cannot be constant: that would give
`dlog(s)=c*dt` for a constant `c`, and the same projective residue argument would force both
`s` and `t` constant.  At the selected exponential point the forms vanish on the tangent space
of the exponential graph, not on the tangent line of this algebraic curve; the intersection is
isolated, so pointwise normalization supplies no tangent invariance.

The all-dimensional product counterfeit is stronger.  On
`W=(product_i X_i=1,Y_i=c_i)`, one has `theta_i=-dX_i` and the unique relation

`sum_i (1/X_i)*theta_i=0`.

The Gauss map `[1/X_1:...:1/X_n]` is nonconstant and in fact generically finite, while every
proper integer projection inequality holds.  A local analytic graph through its chosen point can
be written `Y_i=c_i*exp(X_i-z_i)`; it has `theta_i=0` identically but meets `W` only at the
selected point locally.  Replacing the constants by the actual normalization `c_i=exp(z_i)` is
exactly the original arithmetic condition, not a consequence of the web geometry.  Therefore
closedness, Frobenius integrability, the Gauss map, and characteristic foliations do not turn
proper rotundity into the missing identity inequality.

Integer-linear orbit density does not repair this.  For the stress tuple
`(a,1,exp a,e)` with `a=log 2`, the explicit `SL_2(Z)` matrices
`[[1+k*l,k],[l,1]]` produce a Zariski-dense orbit in `Ga^2 x Gm^2`, by two successive
exponential-polynomial independence arguments.  Thus a hypothetical transcendence-degree-one
field `Q(log 2,e)` would already contain a dense orbit of low-degree points.  Rational scalings
also accumulate at the identity, but a relation of bidegree `(r,s)` transports to
`F(N*X_1,Y_2^N)`, whose degree grows like `N*s` while the distance shrinks like `1/N`.  The
relation therefore changes at exactly the scale needed to evade the identity theorem, finite
pigeonhole arguments, and Noetherianity.

Baire category makes the density defect precise but cannot upgrade it to emptiness.  Let
`gamma(z)=(z,exp z)` and

`D_n={z in C^n : td_Q Q(gamma(z))<n}`.

There are only countably many varieties over `Q`, and exactly

`D_n=union_(V/Q, dim V<n) gamma^(-1)(V)`.

Every member of this union is a closed proper complex-analytic subset.  Properness follows from
the functional linear independence of distinct exponential monomials over `C[z_1,...,z_n]`, so
no nonzero polynomial vanishes identically on the exponential graph.  Consequently `D_n` is a
null meagre `F_sigma` set (and intersecting with the `Q`-linearly-independent locus does not
improve this).  It is nevertheless `GL_n(Q)`-invariant.  Indeed, for `w=A*z`, choose `d` with
`M=d*A` integral.  Each `exp(w_i)` is a root of
`T^d-product_j exp(z_j)^(M_(ij))`, so `Q(w,exp w)` is algebraic over `Q(z,exp z)`; applying the
same argument to `A^(-1)` gives equality of transcendence degrees.

The orbit closures show why the usual invariant-set rigidity has the wrong conclusion.  Write
`z=x+I*y` and regard `[x y]` as an `n` by `2` real matrix.  Since `GL_n(Q)` is dense in
`GL_n(R)`, if `x,y` are real-linearly independent then `GL_n(Q)*z` is dense in the rank-two locus
and hence in `C^n`; in rank one write `(x,y)=(a*u,b*u)` with fixed nonzero `(a,b) in R^2`, and
the orbit is dense in the fixed slice `{(a+I*b)*v:v in R^n}`, with zero added in the closure.  On
either orbit stratum every orbit is dense.  An invariant set with the Baire property is therefore
meagre or comeagre there: if it is
comeagre on one nonempty open set, invariance and the countable translates of that set make it
comeagre everywhere.  On a rank-one slice, the intersection with each proper complex-analytic
stratum is still nowhere dense because the slice is maximally totally real and hence a uniqueness
set for holomorphic functions.  Thus the analytic-stratum description puts `D_n` on the permitted
meagre side in both cases.  Measure-theoretic ergodicity, where a quasi-invariant measure is
available, likewise
distinguishes only null from conull and cannot turn a nonempty null orbit into the empty set.

There are unconditional sharp analogues.  The set

`A_n={z:td_Q Q(z_1,...,z_n)<n}=union_(0!=P in Q[X_1,...,X_n]) Z(P)`

is `GL_n(Q)`-invariant, dense, null, meagre, and `F_sigma`, while still containing a dense set of
`Q`-linearly-independent tuples.  More minimally, the orbit of any rank-two point is itself a
countable invariant dense meagre set in the rank-two locus.  Thus neither definability as a
countable union of rational algebraic strata nor rational linear independence supplies the
missing passage from `nonempty` to `nonmeagre`.

The two stresses realize the orbit geometry exactly.  For `ell=log 2`, the mixed vector
`(1,ell)` has rank one, so its rational-basis orbit is dense in `R^2`.  At
`A=[[a,b],[c,d]] in GL_2(Q)` it becomes

`(a+b*ell,c+d*ell)` with exponentials `(exp(a)*2^b,exp(c)*2^d)`,

and the new generated field is algebraic over `Q(e,ell)`.  Hence a hypothetical
`P(e,ell)=0` would make this whole countable dense real orbit defective.  For the integral shear
`A_k=[[1,k],[0,1]]`, if `r=deg_U P`, the relation at
`(1+k*ell,ell;e*2^k,2)` is the moving Laurent-cleared polynomial

`R_k(Y_1,X_2,Y_2)=Y_2^(k*r)*P(Y_1*Y_2^(-k),X_2)=0`  (`k>=0`),

whose `Y_2` degree grows by `k*r`.  Pulling it back by `A_k^(-1)` gives only the original
relation, not infinitely many equations at one point.

For the period vector `(ell,omega)`, `omega=2*pi*I`, the real and imaginary columns are
independent, so `GL_2(Q)*(ell,omega)` is countable and dense in `C^2`.  If `A=M/d` is rational,
then every transformed exponential satisfies
`exp((A*z)_i)^d=2^(M_(i1))`; it is algebraic, and the transformed field is algebraic over
`Q(ell,omega)`.  Thus a hypothetical `P(ell,omega)=0` would place a dense orbit inside the
meagre defect set.  Along the same shears the precise relation is

`P_k(X_1,X_2)=P(X_1-k*X_2,X_2)=0`

at `(ell+k*omega,omega)`.  Its degree stays `D=deg P`, but its logarithmic coefficient height is
at most `h(P)+D*log(1+|k|)+O(D)`.  For irreducible `P` these polynomials are pairwise
nonassociate: a nonzero shear stabilizer would force `P` into the invariant ring `Q[X_2]`, which
cannot vanish at the transcendental number `omega`.  Analytic rigidity applies to one fixed
stratum; here the group permutes infinitely many distinct strata.  Their invariant union may be
dense and meagre, exactly as the category zero-one law permits.

Projective or tropical compactness of these moving loci loses the same information.  For shears
of `(1,log 2)`, a projective Hilbert limit sends the growing additive and multiplicative
coordinates to coordinate-boundary components; inside the affine torus the corresponding initial
degeneration is empty, while recentering by the inverse shear returns the original ideal.  The
union of the sheared loci is Zariski dense apart from the fixed torus equation, so there is no
nontrivial common limiting relation.  A counterfeit additive-to-multiplicative homomorphism with
`E(1)=3`, `E(log 2)=2`, and algebraic image has exactly the same `2^k` escape face but total
transcendence degree one, showing that the leading tropical data do not use analytic `exp`.
For the period stress `(log 2,2*pi*I)`, there is no exponential escape at all: normalized sheared
polynomials converge only to reducible coordinate-boundary initial forms.  Pullback keeps degree
only by increasing coefficient height, while torus pullback keeps height only by increasing
Newton width; neither gives bounded complexity for a compactness argument.

Tropicalizing the fixed hypothetical locus is equally insensitive.  Let `W/Q` be the irreducible
locus of `(z,y)` in `(G_m)^(2n)` (all `z_i` are nonzero by rational independence), let
`K=Q(W)=Q(z,y)`, and put `d=trdeg_Q K`.  Over the trivial valuation,
`Trop(W)` consists of the vectors `(v(z_i),v(y_i))` furnished by valuations `v` of `K/Q`, and is a
pure rational polyhedral set of dimension `d`.  The equality `y_i=exp(z_i)` holds only at the
chosen complex embedding of `K`; it gives no identity in `K` and hence no relation between these
valuation coordinates.  Rational independence merely says that the ideal contains no homogeneous
rational linear form in the `X_i`.  It does not force tropical dimension: in `Q(t)` the elements
`t,t^2,...,t^n` are rationally linearly independent, while the `t`-adic valuation gives only the
one-dimensional weight ray `(1,2,...,n)`.

There is no nonzero toric weight compatible with the analytic graph that could be imposed by
hand.  A one-parameter scaling `X -> s^u X`, `Y -> s^v Y` would have to satisfy
`s^v*exp(X)=exp(s^u*X)` on an open set; differentiating in `X` forces `s^u=1` and then `s^v=1`.
Equivalently every algebraic homomorphism `G_m -> G_a` and `G_a -> G_m` is trivial.  Formal
nonarchimedean exponentiation near zero does not help: if `v(X)>0`, then
`v(exp(X))=0` and only the non-toric translated coordinate satisfies
`v(exp(X)-1)=v(X)`.  Translating at the target point uses the coefficients `y_i` themselves and
moves the residue field back to `K`, so its initial form cannot give an arithmetic constraint over
`Q`.

The mixed and period boundaries admit the expected low-dimensional fans.  Under a hypothetical
irreducible relation `P(e,ell)=0`, the mixed ideal
`(X_1-1,Y_2-2,P(Y_1,X_2))` has
`Trop(W)={w_(X_1)=w_(Y_2)=0} x Trop(P)`, a one-dimensional fan.  For a full-support bilinear `P`,
`Trop(P)` is exactly the union of the two coordinate axes.  Under a hypothetical relation between
`ell=log 2` and `tau=2*pi*I`, the period ideal
`(Y_1-2,Y_2-1,P(X_1,X_2))` likewise has a one-dimensional tropical plane curve with both
multiplicative weights zero.  Rational independence excludes a linear equation through the
origin, not any of these nonlinear curves.

Two explicit abstract-exponential counterfeits realize the same rank patterns.  In
`K=Qbar(t)^alg`, set
`(x_1,x_2,y_1,y_2)=(1,t,t,2)` for the mixed case and
`(t,t^2,2,1)` for the period case.  Both additive pairs are rationally independent.  Since
`K^*` is divisible, the assignments `E(1)=t,E(t)=2` in the first case and
`E(t)=2,E(t^2)=1` in the second extend to group homomorphisms from `(K,+)` to `(K^*,*)`.
Their prime ideals and tropicalizations are respectively

`(X_1-1,Y_2-2,Y_1-X_2)`, with weight line `(0,s,s,0)`, and
`(X_2-X_1^2,Y_1-2,Y_2-1)`, with weight line `(s,2s,0,0)`.

Both generated fields have transcendence degree one.  More generally this is an exact
universality obstruction: for the generic point of any `W` whose `x_i` are rationally independent,
the map `Z^n -> K^*`, `m -> product y_i^m`, extends to their `Q`-span and then to all of `K_add`
because a divisible abelian group is injective.  The resulting discontinuous exponential has
*the identical ideal, every initial ideal, and the identical tropical variety* as `W`.  Thus no
argument using only tropical data, rational independence, and the abstract exponential group law
can distinguish the analytic exponential.

Matroid submodularity cannot add the missing information.  In the mixed counterfeit the
algebraic matroid has two constant loops and one parallel pair, of total rank one, while the
additive `Q`-linear matroid has rank two.  In the period counterfeit the two additive coordinates
are algebraically parallel but rationally linearly independent, and both multiplicative
coordinates are loops.  These are representable algebraic matroids satisfying every ordinary
submodular and Ingleton inequality.  Tropical projection dimensions recover precisely their
algebraic-matroid ranks, so deriving total rank at least `n` would require a new compatibility
axiom that distinguishes analytic `exp` from the counterfeit; it is not present in initial ideals
or logarithmic limit sets.

There is also no larger hidden class of rational graph-preserving normalizations.  In the
rational function field of `Ga^n x Gm^n`, put
`delta_i = d/dX_i + Y_i*d/dY_i`.  Injectivity of evaluation on the exponential graph and a
prime-divisor argument show that any rational pair satisfying
`H(z,exp z)=exp(F(z,exp z))` on a nonempty analytic open set has uniquely
`F=c+sum m_i*X_i` and `H=exp(c)*product Y_i^(m_i)`, with integral `m_i`.  Coordinatewise, every
rational graph self-map is therefore `(X,Y) -> (M*X+c, exp(c)*Y^M)` for an integer matrix `M`;
over `Q`, Hermite--Lindemann forces `c=0`, and the birational maps are exactly `GL_n(Z)`.  Hence
ordinary nonlinear Noether normalization cannot be made graph-preserving.  For example, the
(non-linearly-independent) genuine graph point `(0,1;1,e)` has locus `Gm`; its finite
normalization uses `Y+Y^-1`, whereas every graph-preserving coordinate restricts to a monomial,
which does not give a finite map to `A^1`.  This example is only an obstruction to the proposed
normalization principle, not a counterexample to the target.

Allowing finite algebraic correspondences enlarges this class only by rational matrices.  On an
analytic branch `(z,exp z;w,exp w)` of a `2n`-dimensional correspondence finite over the source,
functional Ax--Schanuel and the Jacobian rank of `z` force
`w=B*z+c` with `B` rational.  The exact irreducible closure is cut out by this affine relation and
all saturated character-lattice equations
`u^a*v^b=exp(b*c)` with `a+B^T*b=0`; using only rowwise power equations can introduce spurious
Kummer components.  A two-sided finite correspondence has `B in GL_n(Q)`.  If it is defined over
`Qbar`, its character equations make `exp(q*c_j)` algebraic, so Hermite--Lindemann again gives
`c=0`.  Therefore correspondence-level graph preservation is exactly the rational-basis
invariance already formalized: it preserves both rational rank and transcendence degree and adds
no nonlinear normalization.

Mahler-measure and equidistribution averages do not stabilize the moving relation.  For the
stress shear `(1+m*log 2,log 2; e*2^m,2)`, the transported Laurent polynomial has unchanged
coefficient height and exactly the same torus Mahler measure as the original, because the monomial
shear preserves Haar measure; only its degree grows linearly in `m`.  Orbit products therefore
have quadratic degree but only linear Mahler measure, compatible with sparse nonzero polynomials.
The nodes are positive real rather than angularly equidistributed, while a torsion coordinate can
freeze the exponential orbit entirely.  Truncating `log|P|` makes a single exact zero disappear in
the Følner average, and pulling all relations back to one torus collapses the data to the original
single zero.

Trying to force one common relation on a bounded matrix orbit reaches the universal interpolation
boundary.  A coordinate-degree-`D` polynomial has `U` of order `D^(2n)` coefficients.  Matrices
with entries of size `R` give order `R^(n^2)` samples, and the sharp group zero estimate needs
`R^(n^2) >= U`.  But values lie in a filtered piece of the generated field of dimension
`O((R*D)^d)`, so a rational Siegel kernel requires
`D^(2n-d) > R^(n^2+d)`.  At the zero threshold `R=D^(2/n)` this is impossible for every `d>0`.
For `n=2,d=1`, construction needs `R<D^(3/5)` while uniqueness needs `R>=D`, a factor-`D^2`
constraint deficit at the boundary.  Anisotropic degrees, derivatives, or coefficients from a
filtered piece of the field reproduce the same `U` versus sample-count equality before adding the
Hilbert loss.  The infinite orbit can be Zariski dense even under the hypothetical low-degree
stress field, so low pointwise transcendence degree supplies no fixed orbit variety.

Additive-combinatorial amplification sees exactly the permitted group-like case.  For the box
`0<=m_i<N`, rational independence gives additive and multiplicative product-set sizes
`(2N-1)^n` and energies `((2N^3+N)/3)^n`; the graph is a rank-`n` approximate subgroup of the
abelian group `Ga x Gm`.  A one-generator slice `(m,lambda^m)` is already Zariski dense for every
non-root-of-unity `lambda` by confluent-Vandermonde independence.  Interpolating the `N^n` box
points needs `D^2` at least of order `N^n`, while fixed-curve uniqueness on a slice needs
`N>D^2`; these inequalities cannot overlap.  The discontinuous homomorphism
`E(q+r*log 2)=3^q*2^r` has algebraic image and preserves every indexed group-law incidence, while
the rational box `{2^m*3^n}` already has large sum-product expansion at transcendence degree zero.
Analytic near-collision estimates distinguish this counterfeit only metrically; turning them into
a field-dimension statement requires a lower bound for a nonzero rational function at the chosen
transcendental point, exactly the missing transcendence-measure input.

The real Lie closure of the rational span makes the topological/algebraic mismatch exact.  Put
`D=sum_i Q*z_i`, `V=span_R(z_i)`, and `K=Q(z_i,exp(z_i))`.  Rational independence makes `D`
dense in the real space `V`, but `dim_R V<=2` independently of `n`.  For
`w=sum_i q_i*z_i`, clearing a common denominator `m` gives
`exp(w)^m=product_i exp(z_i)^(m*q_i)`, so every `(w,exp(w))` is algebraic over `K`.  The field
generated by the entire dense subgroup contains `K` and is algebraic over it, hence has exactly
the same transcendence degree as the single original tuple.

Nevertheless the Zariski closure of this subgroup in `Ga x Gm` is the full two-dimensional
algebraic group.  The closure is an algebraic subgroup and both projections are infinite; a
one-dimensional connected algebraic subgroup cannot project nontrivially to both factors,
because every algebraic homomorphism `Ga -> Gm` and `Gm -> Ga` is trivial.  Equivalently a
polynomial vanishing on the dense graph vanishes on `graph(exp|V)` by continuity and then
identically by holomorphy.  Thus an infinite union of pointwise `Q`-loci of dimension at most
`trdeg_Q K` acquires algebraic dimension two without increasing their common field.  Noetherianity
does not make the infinite intersection of their ideals finite, just as infinitely many rational
points can be Zariski dense.

For `(1,log 2)`, the points are
`(q+r*log 2, exp(q)*2^r)` and are dense in the real exponential graph; all lie in
`Q(e,log 2)^alg`, whether that field has degree one or two.  Its real algebraic/Nash envelope has
dimension two.  For `(log 2,2*pi*I)`, the points
`(q*log 2+r*2*pi*I,2^q*exp(2*pi*I*r))` are dense in the full complex exponential graph, all lie
in `Q(log 2,2*pi*I)^alg`, and their complex algebraic envelope is again `Ga x Gm`.  A fixed
`Q`-variety containing every division point must therefore be the whole envelope; the individual
low-dimensional loci necessarily move.

Continuity is genuinely extra rather than arithmetic.  On the dense span of `T,T^2` for a real
transcendental `T`, the coherent homomorphism
`E(q*T+r*T^2)=2^q` preserves all rational divisions and group-law incidences, has total field
`Q(T)` of degree one, and is discontinuous.  The earlier mixed counterfeit
`E(q+r*log 2)=3^q*2^r` has the same defect.  Requiring continuity uniquely extends a homomorphism
to `exp(L(w))` for a real-linear `L`; requiring the actual holomorphic normalization `L(w)=w`
recovers complex exponentiation but supplies no inequality for the field of one selected dense
subgroup point.  Topological density, Nash envelopes, and pointwise field dimension therefore
decouple completely.

Algebraic dynamics likewise acts on moving loci.  For `[M]` on a projective compactification of
`Ga^n x Gm^n`, the dynamical degrees `M^min(k,n)` depend only on the ambient map, not on the
dimension of `V=Loc_Q(z,exp z)`, and the transcendental point has no Weil canonical height.  In
the conditional mixed stress, `[m]V` has fixed coordinates `X_1=m`, `Y_2=2^m`, so it is disjoint
from `V` for `m!=1`; division loci have Kummer degree and defining degree growing with `m`.
A nontrivial return `[m]p in V` would force `[m]V=V`, but exp supplies only the tautological moving
membership `[m]p in [m]V`.  The counterfeit `(1,log 2;3,2)` has a degree-one locus whose iterates
remain lines while their Chow heights grow maximally.  Thus dynamical Mordell--Lang, Northcott,
Bogomolov, and arithmetic-degree statements lack a fixed invariant variety or bounded-degree
algebraic orbit on which to operate.

Normalizing a hypothetical mixed relation produces an analytic correspondence, not an algebraic
self-map.  Let `P(E,L)=0` be irreducible through `(e,log 2)` and let `L=phi(E)` be a local branch
on its normalization.  Then `T(E)=exp(phi(E))` has the exact first orbit
`e -> 2 -> exp(alpha)`, where `alpha` is a root of `P(2,Y)`, hence is algebraic of degree at most
`deg_L P` and height at most `log H(P)+(deg_E P)*log 2+O(log deg P)`.  If `alpha` is irrational
algebraic, the checked algebraic-input theorem makes `e` and `exp(alpha)` algebraically
independent; if it is rational, `exp(alpha)` is algebraic over `Q(e)`.  Both outcomes are
compatible with a degree-one initial field.  The next lift is only algebraic over
`Qbar(exp(alpha))`, and exponentiating it is the registered iterated-exponential boundary; an
absolute Weil height is already unavailable at `exp(alpha)`.  The possible equality
`P(2,1)=0` gives the allowed isolated two-cycle `e -> 2 -> e`, so preperiodicity does not force a
functional identity.

For a period relation `P(U,V)=0` through `(log 2,2*pi*I)`, the same construction sends
`log 2 -> 1 -> exp(alpha)` with algebraic `alpha` satisfying `P(1,alpha)=0`; it forgets the
nonzero logarithm period on the first step.  A return to `1` merely asks for `alpha=0`, while a
return to `log 2` asks for the open iterated equation `exp(alpha)=log 2`.  Analytic continuation
does not stabilize the situation: an algebraic branch has finite monodromy, but taking a logarithm
of its exponential adds all `2*pi*I*Z` branches.  Conversely distinct algebraic branches cannot
have identical exponentials on an open set, since their difference would be a nonzero
transcendental constant period.  Thus the `k`-fold analytic correspondence has generically
`(deg_L P)^k` branch choices or nested exponential depth `k`; eliminating them creates a moving
degree-growing relation rather than one invariant algebraic curve.  Functional Ax--Schanuel
controls the generic branch family but is vacuous at the selected zero-dimensional orbit.

This failure is sharp without analytic compatibility.  For real transcendental `T`, the line
`E=L` and an abstract exponential with `E(1)=T`, `E(T)=2` can be extended so that the orbit
`T,2,T^2,4,T^4,...` stays in `Q(T)` while every algebraic lift remains on the same normalized
correspondence.  For the period pattern, the parabola `V=U^2` with
`E(T)=2,E(T^2)=1` likewise has rationally independent inputs and total transcendence degree one.
These models retain correspondence degree, finite algebraic monodromy, powering, and all field
growth counts; only holomorphic exponentiation excludes them, and pointwise holomorphy supplies
no dynamical height inequality.

Period translations have the same defect even though relation degree can remain fixed.  With
`omega = 2*pi*I`, the independent tuple `(omega^2, omega)` satisfies `X_1-X_2^2=0`; the points
`(omega^2+k*omega, omega)` have the same exponentials and generated field, but the fixed relation
takes the value `k*omega`.  Only the moving relation `X_1-X_2^2-k*X_2` vanishes.  These moving
relations are pairwise coprime, so a common polynomial obtained by orbit multiplication has degree
linear in the number of translations.  On scalar integer samples a relation gives only one zero
of a polynomial-exponential recurrence.  If a period occurs, integer sampling also aliases
frequencies (`exp(2*pi*I*t)-1` vanishes on every integer); without a period, the exact confluent
Vandermonde theorem still requires a full block of consecutive zeros that the pointwise relation
does not supply.

Infinite period regularization cannot retain the three needed properties simultaneously.  The
canonical genus-one product with zeros `z+2*pi*I*Z` is, after periodic normalization,
`exp(w-z)-1=exp(w)/exp(z)-1`: exact invariance forgets the logarithm branch and returns only the
original exponential relation.  Gaussian averages acquire theta moments, are not exactly
translation invariant, and do not preserve a single identity zero; genuine theta kernels add
uncontrolled nomes and normalization constants.  Finite products retain arithmetic coefficients
and the zero but recover the original orbit support/degree growth.  There is no nonzero summable
translation-invariant weight on `Z`, so Poisson summation cannot provide both analytic convergence
and exact arithmetic descent.

The theta obstruction can be made completely explicit.  For a positive-definite integral
`n` by `n` matrix `B`, an integer `N>=2`, and `z in C^n`, put

`Theta_(B,N)(z)=sum_(m in Z^n) N^(-m^T*B*m)*exp(m dot z)`.

The sum converges absolutely and normally, since a linear exponential is dominated by half of the
negative quadratic Gaussian.  Its coefficients are rational, but it is a holomorphic Laurent
function only of `y_i=exp(z_i)` and is exactly invariant under `z -> z+2*pi*I*a`, `a in Z^n`.
Poisson summation, with `lambda=log N`, gives the exact formula

`Theta_(B,N)(z)=(pi/lambda)^(n/2)*(det B)^(-1/2)
 *sum_(k in Z^n) exp((z-2*pi*I*k)^T*B^(-1)*(z-2*pi*I*k)/(4*lambda))`

`=(pi/lambda)^(n/2)*(det B)^(-1/2)*exp(z^T*B^(-1)*z/(4*lambda))
 *sum_k exp(-pi^2*k^T*B^(-1)*k/lambda)
          *exp(-pi*I*k^T*B^(-1)*z/lambda)`.

Thus arithmetic coefficients on the original side become the new dual nome
`exp(-pi^2/lambda)`, a quadratic exponential in `z`, phases involving `pi*z/lambda`, and a
`pi/lambda` normalization on the dual side.  A nondiagonal `B` merely puts the desired cross
products into the new quadratic exponential and the inverse theta series; it does not isolate
them.  Conversely taking a self-dual Gaussian makes the nome `exp(-pi)`, already transcendental,
and loses arithmetic coefficients.  Applying Poisson inversion a second time sends
`(lambda/pi,z)` to its reciprocal parameter and then returns `z` as `-z`; the two Gaussian
prefactors cancel and `Theta(z)=Theta(-z)`.  Modular inversion is therefore one invertible
analytic identity, not two independent arithmetic equations.

For the mixed stress write `ell=log 2`, take `B=I_2,N=2`, and set
`F_q(x)=sum_(m in Z)q^(m^2)*x^m`, `Q=exp(-pi^2/ell)`.  Then

`Theta_(I,2)(1,ell)=F_(1/2)(e)*F_(1/2)(2)`

`=(pi/ell)*2^(1/4)*exp(1/(4*ell))
  *F_Q(exp(-pi*I/ell))*F_Q(-1)`.

The arithmetic-side invariant sees `e` and `2` but not the logarithm `ell`; the dual expression
sees it only after adjoining `Q`, `exp(1/(4*ell))`, `exp(-pi*I/ell)`, and theta values.  The
Laurent function `F_q(x)` has essential singularities at both zero and infinity, so it is not an
algebraic function of `x`; at the selected numerical point no theorem makes these new values
algebraic over `Q(e,ell)`.  A hypothetical `P(e,ell)=0` consequently gives no norm or height on
the theta factors with which to isolate the displayed quadratic exponential.

The period stress is sharper.  For `z=(ell,2*pi*I)` the original sum is simply

`Theta_(I,2)(ell,2*pi*I)=F_(1/2)(2)*F_(1/2)(1)`
`=(pi/ell)*2^(1/4)*F_Q(-1)*F_Q(1)`.

Indeed the one-dimensional transform at `z=2*pi*I` initially contains
`Q*F_Q(Q^(-2))`, but the exact quasiperiod formula
`F_Q(Q^(-2))=Q^(-1)*F_Q(1)` cancels it.  Equivalently, the period shift is just the reindexing
`k -> k-1` in the dual lattice.  Hence every theta value and every theta derivative built from
integer characters gives exactly the same answer at `2*pi*I` and at zero; Poisson summation
cannot constrain the missing logarithm period.

Nor does inserting the alleged polynomial relation make its one zero propagate.  For a Laurent
polynomial `P(X,Y)=sum_(alpha,beta)c_(alpha,beta)*X^alpha*Y^beta` and the scalar power orbit
`[r](z,y)=(r*z,y^r)`, its convergent Gaussian average is exactly

`sum_r q^(r^2)*P(r*z,y^r)
 =sum_(alpha,beta)c_(alpha,beta)*z^alpha
   *(d/du)^(|alpha|)F_q(exp u)|_(u=beta dot z)`.

The equality `P(z,y)=0` removes only the `r=1` summand and says nothing about this average.  If
one instead multiplies every summand by the fixed zero, the result is merely
`P(z,y)*Theta_(B,N)(z)=0`, equivalent to the original relation wherever the theta factor is
nonzero.  Averaging period translates gives the equally exact obstruction

`sum_m q^(m^2)*P(E,L+2*pi*I*m)
 =sum_(j>=0) (2*pi*I)^(2*j)*mu_(2*j)(q)/(2*j)! *partial_L^(2*j)P(E,L)`,

where `mu_j(q)=sum_m m^j*q^(m^2)` and the sum stops at half the degree of `P`; after `P(E,L)=0`,
the higher theta moments remain rather than vanish.  Exact translation invariance cannot repair
this: a translation-invariant `l^1(Z^n)` weight is constant and hence zero.

Finally, positivity detects only distinct exponential characters.  For real `x_1,x_2`, the Gram
matrix of the vectors `(q^(m^2/2)*exp(m*x_i))_m` has entries
`G_(ij)=F_q(exp(x_i+x_j))` and positive determinant exactly when `x_1!=x_2`.  At the mixed stress
this reads
`F_q(e^2)*F_q(4)-F_q(2*e)^2>0`.  At the period stress the Hermitian determinant is
`F_q(4)*F_q(1)-F_q(2)^2>0`, exactly the same determinant obtained by replacing `2*pi*I` by zero.
Its entries are new theta values, not algebraic numbers with a norm lower bound.  Theta
regularization therefore either forgets the logarithmic coordinates on its arithmetic side or
reintroduces them together with uncontrolled quadratic exponentials and modular constants on its
dual side; positivity and Poisson inversion do not close that gap.

Complex conjugation gives only a joint real/pure-imaginary reformulation.  If `K` is the original
field, `D=td(K*Kbar)`, and `e=td(K intersect Kbar)`, then `D+e<=2*td(K)`.  Writing `z=x+v` with
real `x` and purely imaginary `v`, rational independence gives
`rank_Q(x)+rank_Q(v)>=n`, and the joint conjugate field is algebraically equivalent to the
generated field of rational bases of those two spans.  Even a bound
`D>=rank_Q(x)+rank_Q(v)` yields only half the desired inequality unless one also controls the
intersection.  For `(1,log 2)` conjugation is trivial; for `(log 2,2*pi*I)` it merely separates
the two exact missing coordinates.  Norms `a*conj(a)>0` land in a real function field containing
arbitrarily small positive elements, not in a discrete ordered ring.

The exact rank accounting shows that this is a decomposition into two Schanuel instances.  Put
`r=rank_Q{x_i}` and `s=rank_Q{v_i}`.  The compositum is algebraically equivalent to
`Q(x,v,exp(2*x),exp(2*v))`, since `y_i*conj(y_i)=exp(2*x_i)`,
`y_i/conj(y_i)=exp(2*v_i)`, and `y_i^2` is the product of those last two values.  Choosing rational
bases of the real and purely imaginary spans therefore turns `D>=r+s` into Schanuel for a
linearly independent tuple of length `r+s`.  On the other side, the coefficient spaces
`A=ker(q -> q dot v)` and `B=ker(q -> q dot x)` have dimensions `n-s` and `n-r` and intersect
trivially.  Integer bases of `A` and `B` give `2*n-r-s` rationally independent real or purely
imaginary combinations of the original inputs; both those combinations and their exponentials
lie in `K intersect Kbar`.  Schanuel for this kernel tuple would give
`e>=2*n-r-s`.  Together these two still-unproved bounds give
`D+e>=2*n` and hence the target, but neither follows from real algebraic geometry or Hermitian
positivity.

The stresses make the circularity exact.  For `(1,log 2)`, `K=Kbar`, `(r,s)=(2,0)`, and the
kernel tuple is the original real pair, so both required intersection/compositum bounds are the
claim `td Q(e,log 2)>=2`.  For `(log 2,2*pi*I)`, again `K=Kbar`, `(r,s)=(1,1)`, and both projected
and kernel tuples recover the original period pair.  Conversely, for algebraic inputs the checked
Lindemann--Weierstrass theorem applies to both auxiliary tuples and forces the exact equalities
`D=r+s` and `e=2*n-r-s`; conjugate doubling merely repartitions the already-known total `2*n`.
The factor-of-two inequality itself is sharp: for the single algebraic input `1+I`, the fields
`Q(I,exp(1+I))` and its conjugate have transcendence-degree-one each, compositum degree two, and
transcendence-degree-zero intersection.

Real/Hermitian data cannot exclude low-rank abstract exponentials.  With real transcendental `T`,
the mixed model `(z_1,z_2;y_1,y_2)=(1,T;T,2)` has `K=Kbar=Q(T)`, while the period-shaped model
`(T,I*T^2;2,1)` has the same stable field `Q(I,T)` and ranks `(r,s)=(1,1)`.  Both input pairs are
rationally independent, and divisibility of `C^*` extends the displayed assignments to abstract
exponential homomorphisms.  Their moduli, phases, real loci, and all Hermitian products still have
transcendence degree one.  Excluding them requires the pointwise analytic exponential, exactly the
compatibility absent from conjugate doubling.

### Galois symmetrization beyond algebraic inputs

The completed stable-relation argument fundamentally requires a finite number field and algebraic
support exponents. For an arbitrary tuple, choosing a transcendence basis makes the remaining
generators algebraic only over a function field. Specializing that basis does not preserve the
analytic identities `Y_i = exp(X_i)`. No valid relative descent from this observation has yet been
proved.

Finite symmetrization of a transcendence basis does not remove that base.  For
`Qbar(T_1,...,T_d)` the scaling group `mu_m^d` fixes `Qbar(T_1^m,...,T_d^m)`, which has the same
transcendence degree.  Passing to a stable normal closure can require at least `m^d` orbit factors,
so support and coefficient norms grow exponentially in `m^d`.  More sharply, take
`alpha=1/(T-1)` and specialize `T=1+1/log 2`.  The orbit product of `[alpha]-2[0]`, followed by
reflection, is stable and analytically zero, but its quadratic weighted moment is
`-4*m*((m-1)*T^m+1)/(T^m-1)^2`, nonconstant for every `m>=3` despite auxiliary degree `2<m`.
Clearing poles restores degree `2m` and no lower bound at the selected transcendental value.

Even for polynomial support the threshold is exact rather than favorable.  The orbit product of
`[T]-2[0]` has all positive moments below `m` equal to zero by symmetry, but its `m`-th moment is a
nonzero multiple of `T^m`.  Simultaneous approximation of the orbit support needs a root
polynomial of degree at least `m` (generically `m^d`), so the Hermite auxiliary degree grows at the
same scale.  Choosing the group after constructing the auxiliary approximates the wrong support;
rebuilding it reinstates the loss.  Varying `m` produces different invariant elements, so the
intersection of the fixed fields cannot be applied to one common auxiliary value.

Reduction modulo `p` and additive translations have an equally explicit failure.  With
`alpha=1/T`, specialize `T=1/log 2` and take the product of `[1/(T+a)]-2[0]` for
`a=0,...,p-1`.  The identity factor gives analytic vanishing and, modulo `p`, translation by one
makes the reflected relation stable.  Its quadratic moment is
`-4/(T^p-T)^2`, a nonconstant invariant despite degree `2<p`.  Clearing the denominator gives a
polynomial congruent to `-4` modulo `p`, but evaluation has the form `-4+p*Q(tau)` rather than a
nonzero integer.  Thus Frobenius supplies coefficientwise constancy without the pointwise
archimedean discreteness needed by the number-field endpoint.

### Complex-to-p-adic transfer

Changing completions does not transport the analytic graph.  For the stress pair
`(log 2, e)`, an abstract embedding of a hypothetical field `Q(log 2, e)` into `C_p`
can send `log 2` to the canonical p-adic logarithm, but then sends `e` to an arbitrary
root of the specialized algebraic relation; there is no reason for that root to be the
p-adic exponential of `1`.  Requiring both images is precisely the missing mixed
algebraic-independence statement in another completion.

This remains exact after rational rescaling.  One may choose `q = N/M` simultaneously
small at infinity and p-adically, so that chosen branches of `2^q - 1` and the Taylor
series for `exp(q)` are small at both places.  The product formula has no slack: the
denominator `M^m`, the other factorial valuations, and the remaining `M - 1` conjugates
of `2^q - 1` compensate the two small branches exactly.  Taking norms therefore restores
the uncontrolled conjugate factors, while an abstract field embedding still need not
identify the image of the complex limit with the p-adic limit.  The corresponding
resultant has degree growing with `M`, and asserting that it vanishes on the canonical
p-adic pair is a p-adic analogue of the original target, not a transfer theorem.

Integer powering makes the branch mismatch explicit rather than repairing it.  For an odd prime
`p`, take `m=p*(p-1)` and write `L_p=log_p(2)`.  Then both convergent identities
`exp_p(m*L_p)=2^m` and `exp_p(m)=sum_k m^k/k!` hold, the first because `p-1` kills the
Teichmuller factor of `2`.  If a hypothetical complex relation is
`P(e,log 2)=0`, then
`R_m(E,L)=Res_A(P(A,L),A^m-E)` satisfies `R_m(e^m,log 2)=0`.  An embedding of the resulting
function field with `L -> L_p` sends `E` to some root of `R_m(E,L_p)`; it has no reason to select
the canonical root `exp_p(m)`.  Requiring
`R_m(exp_p(m),L_p)=0` is exactly the p-adic mixed algebraic-dependence assertion one was trying to
deduce.  The p-adic analytic subgroup theorem cannot supply it: the group point
`(exp_p(m),2^m)` is not algebraic in its first coordinate, while discarding that coordinate leaves
only the known logarithm of `2`.  Spreading `P` over a number field therefore spreads the
algebraic curve, not the archimedean exponential branch on it.

The period stress loses a whole direction at every finite place.  The algebraic torus point
`(2,1)` has complex logarithm branch `(log 2,2*pi*I)`, but its canonical p-adic logarithm is
`(L_p,0)`; after every integer power it remains `(m*L_p,0)`.  The p-adic exponential is injective
on its convergence ball, so there is no nonzero `C_p` period that could be the image of
`2*pi*I`.  Fontaine's nonzero analogue `t_p=log([epsilon])` lives in `B_dR`, not `C_p`, and has no
place in a number-field product formula or a `C_p` analytic-subgroup estimate.  Thus an abstract
embedding of a hypothetical `Q(log 2,2*pi*I)` curve sends the period coordinate to an arbitrary
root of its algebraic relation, never to a canonical finite-place period.  Function-field product
formulas then sum divisorial valuations and omit both selected analytic comparison points;
specializing to algebraic points restores a number-field product formula only by destroying the
two exponential identities.

There is no global integral divided-power or Witt object whose comparison value is ordinary
complex `exp` on arbitrary constants.  In big-Witt coordinates, `exp(z*t)` has ghost components
`w_1=z` and `w_m=0` for `m>1`; integral Witt data would require
`w_p=w_1^p (mod p)`, already impossible at `z=1`.  Equivalently its Witt coordinates begin
`z,-z^2/2,-z^3/3,...`, and a special lambda-ring law with this exponential would have
`psi^1(z)=z`, `psi^m(z)=0` for `m>1`, contradicting the Frobenius congruence.  The divided-power
identity `z^p=p!*gamma_p(z)` has the same obstruction for a unit modulo `p`.

Artin--Hasse integrality avoids that contradiction only by changing the comparison prime by prime:
`E_p(T)^p/E_p(T^p)=exp(p*T)`, so recovering `exp(T)` still requires a chosen Kummer root.  At
`T=1` the p-adic series is outside its convergence domain.  At the convergent logarithmic stress
coordinate `L_p=log_p(2)`, the quotient gives the principal unit
`2^p/omega_p(2)`, not the complex value `2^p`; the missing Teichmüller factor depends on `p`.
Thus Witt, lambda, and crystalline packaging cannot glue the local branches into the global
integer invariant that the transfer argument needs.  Taking the unrestricted product of the
separate `p`-typical objects is only bookkeeping: its components are not completions of one
global element, it has no canonical complex absolute value or discreteness, and the ghost
congruence proves that the required diagonal global Witt vector does not exist.

Discrete Fourier projection over Kummer conjugates cannot select the missing branch over the
base field.  If `W^b=y`, the Fourier transform of `A(zeta^k W)` separates the residue-class
monomials of `A`; it removes, rather than preserves, the cancellation making `A(W)` small.  The
exact selector `(1/b)*sum_(m<b)(T/W)^m` is one at the chosen root and zero at the others, but its
coefficients contain `W`.  Its conjugates are permuted and their trace is one.  In `n` variables
the character matrix has size `B=b^n`, determinant magnitude `B^(B/2)`, and inverse denominator
`B`; every invariant determinant is the full norm.  Thus Fourier descent either forgets the
analytic branch or restores all conjugate factors, and multiple compatible division scales only
enlarge the same Kummer torsor.

The full inverse-limit Kummer tower retains no additional analytic datum.  For the mixed stress
`F=Q(e,log 2)`, put `q=ell^n`, `B_q=F(mu_q)`, `u_q=e^(1/q)`, and `v_q=2^(1/q)`.  For every
sufficiently large prime `ell`, divisorial valuations of the nonconstant element `e` and a place
above `2` show
`[B_q(u_q,v_q):B_q]=q^2` and `[B_q:F]=phi(q)`: the joint tower has maximal Kummer rank even under
the hypothetical assumption `trdeg_Q F=1`.  Its compatible systems form a torsor under
`Zhat(1)^2`, and the Galois cocycle records only the two multiplicative Kummer classes.  Changing
coherent roots changes it by a coboundary.  Systems obtained from the logarithms
`1+2*pi*I*a` and `log 2+2*pi*I*b` are all coherent and tend to one; only the non-Galois-invariant
limits `m*(u_m-1)` and `m*(v_m-1)` select the desired analytic branches.

The norm compensation is exact: for odd `q` and primitive fixed `(r,s)`,
`N_(B_q(u_q,v_q)/B_q)(u_q^r*v_q^s-1)=(e^r*2^s-1)^q`.  In particular
`N(v_q-1)=1`, although `v_q-1` is asymptotic to `(log 2)/q` at the positive real embedding.
Also `[Q(2^(1/m)):Q]=m`, its height is `(log 2)/m`, and the discriminant of `X^m-2` is
`+/-m^m*2^(m-1)`: shrinking height is exactly paid by degree and discriminant.  This is sharp
against analytic-free substitutes.  Over `Q(log 2)`, the homomorphism
`E(q+r*log 2)=3^q*2^r` has total transcendence degree one but the same maximal two-dimensional
Kummer/Iwasawa tower, positivity, coherent roots, and valuation regulator.  Milnor symbols merely
detect multiplicative rank (`{T,2}` is already nonzero over `Q(T)`); a p-adic regulator linking the
tower to `log 2` would have to impose the missing compatible exponential embedding by hand.

The analytic selection among these conjugates can be classified exactly, but is not Galois
invariant.  Let `L=directsum_i Z*z_i`, `D=L tensor Q`, and fix the actual character
`chi_0(w)=exp(w)`.  For `a=(a_i) in Zhat^n`, define on `D/L`

`rho_a(sum_i (r_i/m)*z_i)=zeta_m^(sum_i (a_i mod m)*r_i)`,  `chi_a=chi_0*rho_a`.

Compatibility of the residues `a_i mod m` makes this well defined.  These are exactly the coherent
root-of-unity twists of all finite Kummer conjugates; they agree with `chi_0` on `L`, take values
in the algebraic division hull over `K`, and satisfy `|chi_a(w)|=|chi_0(w)|` at every complex
point.  If one coordinate of `a` is a profinite integer not lying in `Z`, restriction to the
corresponding dense rational line is discontinuous: a continuous character would extend to `R`
and have the form `q -> exp(2*pi*I*c*q)`, while triviality on `Z` forces the ordinary integer
`c`.  Thus the tower contains continuum many exact, wildly discontinuous conjugate characters
with identical absolute values, heights, and finite-level spectra.

Finite-level normal families cannot select the branch.  All holomorphic solutions of
`f(w)^m=exp(w)` are `f_(m,k)(w)=zeta_m^k*exp(w/m)`, and on every compact set their sup norms and
all derivative norms are independent of `k`.  If `k/m -> theta`, they converge normally to the
constant `exp(2*pi*I*theta)`; every fixed `k` converges to one and even satisfies
`m*(f_(m,k)-1) -> w+2*pi*I*k`.  Exact normalization `f(0)=1` singles out `k=0`, but that condition
is changed by every nontrivial Kummer automorphism and simply inserts the desired analytic sheet
at an auxiliary point.  The companion matrix of `T^m-y` is no better: every eigenvalue has modulus
`|y|^(1/m)`, so spectral radius and operator norm see the whole orbit symmetrically.  Isolating one
eigenvalue requires the same degree-`m` Fourier/Lagrange projector already accounted for above.

For the mixed span `D=Q+Q*ell`, the ordinary coherent twists are
`chi_(a,b)(q+r*ell)=exp(q)*2^r*exp(2*pi*I*(a*q+b*r))`.  Because `D` is dense in `R`, this character
is continuous only for `(a,b)=(0,0)`: a continuous unitary ratio would be `exp(2*pi*I*c*x)`, and
agreement on every rational division of `1,ell` requires the exact equalities `c=a` and
`c*ell=b`, impossible for transcendental `ell` unless both integers vanish.  At any fixed level
`m`, the failure is arbitrarily local: for
every nonzero residue pair `(a,b) mod m`, each neighborhood of zero contains
`(p+q*ell)/m` with `a*p+b*q` fixed nonzero modulo `m`, since every congruence class of the lattice
is dense.  Continuity therefore does uniquely select the analytic character here, but the
selection holds at just one archimedean embedding and is not inherited by its Galois conjugates.

The period span shows why even ordinary continuity is insufficient.  For
`D=Q*ell+Q*(2*pi*I)`, every integer pair `(a,b)` gives a continuous real-linear character obtained
from the logarithms `ell+2*pi*I*a` and `2*pi*I*(1+b)`.  Only `(0,0)` is complex-linear and hence
holomorphic: complex linearity would require
`1+b=1+(2*pi*I/ell)*a`, forcing `a=b=0`.  At level `m` the actual second root is
`exp(2*pi*I/m)=zeta_m`, while the other Galois branches are the equally bounded roots
`zeta_m^c`; positivity would incorrectly choose the root `1`.  For prime `p`, the exact product
`N_(Q(zeta_p)/Q)(1-zeta_p)=p` compensates
`|1-zeta_p| asymp 2*pi/p`, just as `N(1-2^(1/m))=+/-1` compensates the positive real root in the
first coordinate.  Heights, product formulas, and spectral radii therefore cannot see the unique
holomorphic normalization.

This explains why continuity selection cannot become a dimension estimate.  A large-Galois-orbit
argument needs many conjugates satisfying the same analytic condition, whereas here precisely the
selected conjugate is continuous or holomorphic and all arithmetic invariants are symmetric.
Using the topology can identify that one point in each orbit, but supplies no lower bound for the
transcendence degree of the base field containing the orbit.  Taking norms restores all the wildly
discontinuous branches and exactly cancels the selected small value.

### Dense transcendental conjugates give small values, not arithmetic zeros

The `Aut(C/Q)` orbit really is analytically dense in the appropriate rational locus, but this
does not produce Galois conjugates in the finite-degree sense needed by a norm.  Let
`p in W(C)` be generic over `Q`, where `W=Loc_Q(p)` is irreducible and
`d=trdeg_Q Q(p)>0`.  The relative algebraic closure `k` of `Q` in `Q(p)` is a number field.
On the geometric component through `p`, the points generic over `k` are the complement of a
countable union of proper algebraic subsets and hence are Euclidean dense.  Any such point `q`
defines a `k`-isomorphism `Q(p) -> Q(q)`.  Extending across algebraic closures and then matching
transcendence bases of `C` extends this isomorphism to an element of `Aut(C/k)`.  Thus even the
stabilizer of `k` has a dense orbit near `p`.

The mixed stress makes the resulting small values completely explicit.  Put `ell=log 2` and,
conditionally on `trdeg_Q Q(e,ell)=1`, let `P(U,V) in Q[U,V]` generate the prime ideal of
relations of `(e,ell)`.  The point is smooth on `P=0`: otherwise both partial derivatives would
lie in the height-one prime `(P)`, which is impossible in characteristic zero.  Choose
`a,b in Q` so that `T=a*U+b*V` is a local parameter at `(e,ell)`, put
`t_0=a*e+b*ell`, and write the local algebraic branches as

`U=u(t),  V=v(t),  u(t_0)=e,  v(t_0)=ell`.

For every sufficiently small nonzero `h in Q`, `t_0+h` is transcendental and
`q_h=(u(t_0+h),v(t_0+h))` is again generic on the same component.  Hence there is
`sigma_h in Aut(C/Q)` with

`sigma_h(e)=u(t_0+h),  sigma_h(ell)=v(t_0+h)`.

For the full mixed point `(1,ell;e,2)`, its conjugate is
`(1,v(t_0+h);u(t_0+h),2)`, and its two analytic graph defects are

`D(h)=(u(t_0+h)-e, 2-exp(v(t_0+h)))`.

Since `a*u'(t_0)+b*v'(t_0)=1`, Taylor expansion gives

`D(h)=(u'(t_0),-2*v'(t_0))*h+O(h^2)`.

Consequently there are constants `0<c<C` such that

`c*|h| <= ||D(h)||_infinity <= C*|h|`

for all sufficiently small `h`.  Moreover `D(h)=0` locally forces first `u=e` and then
`v=ell` (the other logarithms of `2` are separated by `2*pi*I`), so it forces `h=0`.
Taking `h_(N,j)=j/N^3`, `1<=j<=N`, gives `N` distinct field-conjugate generic points in an
`O(N^-2)` neighborhood, all with nonzero defect, and

`c^N*N!/N^(3*N) <= product_j ||D(h_(N,j))||_infinity
                         <= C^N*N!/N^(3*N)`.

Thus the product is `exp(-2*N*log N+O(N))`; replacing `N^-3` by an arbitrarily smaller positive
rational scale forces arbitrarily faster decay.  No identity-theorem conclusion follows, since
these are small nonzero values of one holomorphic map, not accumulating zeros.

The all-algebraic-exponential period stress is identical.  Conditional on a curve relation for
`(ell,omega)`, where `omega=2*pi*I`, choose a local parameter and branches
`(u(t),v(t))` through `(ell,omega)`.  The conjugates of `(ell,omega;2,1)` have defects

`D_per(h)=(2-exp(u(t_0+h)),1-exp(v(t_0+h)))
          =(-2*u'(t_0),-v'(t_0))*h+O(h^2)`.

The derivative vector is nonzero, and in a sufficiently small neighborhood the simultaneous
equations `exp(u)=2`, `exp(v)=1` select only `(ell,omega)`.  Hence the same two-sided linear bound
and the same arbitrarily large nonzero clusters occur at the period boundary.

There is an unconditional sharp saturation already in dimension one.  On the rational line
`W_0: Y=2`, the graph point `p_0=(ell,2)` is generic.  For every nonzero `r in Q`, the map
`ell -> ell+r` is a `Q`-automorphism of `Q(ell)` and extends to `Aut(C/Q)`, so
`q_r=(ell+r,2)` is a field conjugate of `p_0`.  Nevertheless its exact graph defect is

`Delta_r=2-exp(ell+r)=2*(1-exp(r)) != 0`.

For `0<r<=1`, one has the concrete bounds

`2*r <= |Delta_r| <= 2*e*r`.

In particular, for `r_j=j/N^3`,

`2^N*N!/N^(3*N) <= product_(j=1)^N |Delta_(r_j)|
                         <= (2*e)^N*N!/N^(3*N)`.

Every factor is transcendental by Hermite--Lindemann, despite being arbitrarily small.  This
example uses the actual complex exponential and has exactly the same orbit-density mechanism as
the hypothetical mixed curve.

Three exact obstructions prevent symmetrization from repairing the argument.

1. These are conjugates in a transcendental extension, not roots of a finite minimal polynomial.
   A finite `Aut(C/Q)`-stable multiset containing a tuple of positive transcendence degree cannot
   exist: applying coordinate projections and taking the finite root polynomial would make every
   coordinate algebraic over the fixed field.  An arbitrarily selected finite cluster is not
   stable, so its elementary symmetric functions need not lie in `Q` or in any number field.
2. The defect map is not Galois equivariant.  In the explicit line example,
   `sigma_r(exp(ell))=sigma_r(2)=2`, whereas `exp(sigma_r(ell))=2*exp(r)`.
   Thus even a stable set of algebraic-coordinate conjugates would not give a stable set of
   analytic defect values.
3. A finite relative norm after choosing a transcendence parameter lands in a function field
   such as `Q(t_0)`, not in a discrete ring.  It can be arbitrarily small at the distinguished
   complex embedding, with the missing mass carried by other complex or divisorial places.
   Specializing `t` to Gaussian rationals of denominator `M` gives algebraic curve points of
   degree bounded by twice the projection degree, distance `O(M^-1)`, and height `O(log M)`;
   their defects still contain `e` or exponentials of nonzero algebraic numbers and therefore
   are not algebraic numbers to which a number-field norm applies.

Accordingly orbit density supplies arbitrarily many arbitrarily small defects but neither one
additional exact graph intersection nor an arithmetic nonvanishing determinant.  Turning this
topological statement into a norm lower bound would require precisely the missing compatibility
`sigma(exp x)=exp(sigma x)`, which is false even in the boundary line `Y=2`.

### Schneider--Lang on an algebraic exponential correspondence

The exact Schneider--Lang criterion does not turn a single algebraic endpoint of an algebraic
correspondence into a second transcendence-degree contribution.  In its relevant one-variable
form, let `F` be a number field and let `f_1,...,f_m` be meromorphic on the whole complex plane.
If two of them are algebraically independent and of finite orders `rho_1,rho_2`, and

`(d/dz) F[f_1,...,f_m] subset F[f_1,...,f_m]`,

then the set of points where every `f_j` is regular and takes its value in `F` is finite.  The
quantitative sharp form bounds its cardinality by
`(rho_1+rho_2)*[F:Q]`.  Both the common number field and the simultaneous values of every
generator in a differential ring are essential.

Assume conditionally that `P(e,ell)=0`, with `ell=log 2`, and write the local algebraic branch as
`L=phi(E)`, `phi(e)=ell`.  Then `f(E)=exp(phi(E))` satisfies `f(e)=2`, but this is not a
Schneider--Lang value point.  In the best global case, where `phi in Qbar[E]` is a nonconstant
polynomial, the natural differential ring is

`Qbar[E,exp(phi(E))]`, with `E'=1` and
`(exp(phi(E)))'=phi'(E)*exp(phi(E))`.

The two displayed functions are algebraically independent and have orders `0` and `deg phi`,
but at the selected argument `E=e` the first value is transcendental.  Omitting `E` generally
destroys differential closure; when it does not, only one transcendental function remains, so
the required pair of algebraically independent functions is gone.  Replacing the number field by
`Q(e,ell)` is not permitted under the hypothetical defect-one assumption: it is a function field
of transcendence degree one.  Even if one informally made that replacement, the criterion's
conclusion that the value field is not a number field would say only what is already known.

The alternative parameter `E=exp(t)` fares worse.  Put

`G(t)=exp(phi(exp(t)))`.

At `t=1`, the endpoint values `t=1` and `G(1)=2` are algebraic.  However derivative closure
requires adjoining `exp(t)` and `phi(exp(t))`, whose values are respectively `e` and `ell`.
Moreover, if `phi` is a polynomial of degree `d>0`, then `G` has infinite order: choosing a
direction on which the leading term of `phi(exp(t))` has positive real part gives

`log M_G(R) >= c*exp(d*R)`

along an unbounded sequence.  A rational `phi` with a nonzero finite pole gives essential
singularities at its logarithmic preimages; a pole at zero still gives double-exponential growth.
For a genuinely algebraic branch, branch points also prevent a single meromorphic function on
the whole plane.  Thus the reparametrization simultaneously loses finite order and fails the
common-number-field value condition.

Continuation on the normalization of `P=0` does not help.  There `E` and `phi` are meromorphic
on a compact curve, while `exp(phi)` has an essential singularity at every pole of the
nonconstant meromorphic function `phi`.  If a pole has order `r` in a local coordinate `s`, the
solutions of `exp(phi)=2` are

`phi(s)=ell+2*pi*I*k`,  with  |s| asymp |k|^(-1/r)`.

They accumulate only at the deleted pole.  Their intermediate `phi`-values contain `ell` and
the period, so they are not common algebraic-value points; accumulation at an essential
singularity also gives no identity theorem.

Polynomial and algebraic stress models show that this failure is sharp.

* For `phi(E)=E^d`, the entire function `exp(E^d)` has order `d` and takes the algebraic value
  `2` at every root of `E^d=ell+2*pi*I*k`.  All these arguments are transcendental.  The number
  of such roots in `|E|<=R`, counted with multiplicity, is
  `(d/pi)*R^d+O(1)`, exactly the order-`d` value-distribution scale.
* For `phi(E)=1/E`, the exact points `E_k=1/(ell+2*pi*I*k)` satisfy
  `exp(phi(E_k))=2` and accumulate at the essential singularity `E=0`, with no interior zero
  accumulation.
* On the algebraic correspondence `S^2=E`, taking `phi=S` reduces on the normalization to
  the ordinary function `exp(S)`.  Its algebraic value `2` occurs at
  `S=ell+2*pi*I*k`, `E=(ell+2*pi*I*k)^2`; normalization changes neither the transcendental
  arguments nor the missing number field.
* The quantitative Schneider--Lang bound itself can be saturated.  For
  `Q(E)=product_(j=0)^(d-1)(E-j)`, the pair `E,exp(Q(E))` has orders `0,d`, a stable differential
  ring over `Q`, and exactly the `d` rational points `E=0,...,d-1` at which both values are
  algebraic.  An additional equality `exp(Q(e))=2` would not add a counted point because its
  argument `e` is transcendental.

The usual multiplication trick also fails at an exact algebraic identity.  From
`P(e,ell)=0` one obtains moving relations through `(e^m,m*ell)` by eliminating `U` from

`P(U,L/m)=0,  U^m=E`.

It does not follow that the original branch satisfies `phi(e^m)=m*ell`.  If one demanded the
fixed functional propagation

`phi(E^m)=m*phi(E)`

for an algebraic branch regular near `E=1`, then writing `E=exp(t)` gives
`g(m*t)=m*g(t)` for `g(t)=phi(exp(t))`.  Coefficient comparison forces
`g(t)=c*t`; hence `phi(E)=c*log E` locally.  Since a nonzero logarithm has infinite monodromy and
is not algebraic over `C(E)`, an algebraic branch satisfying this identity must be zero.  Thus
the only mechanism that would propagate the one value into the infinite arithmetic grid required
by Schneider--Lang is precisely the nonalgebraic logarithm that the hypothetical relation was
supposed to replace.

At the original point the data form a two-step chain

`1 --exp--> e --phi--> ell --exp--> 2`.

Schneider--Lang requires two algebraically independent finite-order functions to take values in
one number field at the same collection of arguments.  Here the two endpoints are algebraic only
after discarding the two transcendental intermediate values; differential closure restores those
values, and composition raises the growth to infinite order.  Therefore algebraic continuation,
Nevanlinna value distribution, and the strongest classical Schneider--Lang criterion all permit
`f(e)=2`; a contradiction would require a new theorem controlling algebraic endpoints across a
transcendental intermediate field, which is exactly the missing defect-one statement.

### Rational division points and o-minimal counting

For reduced `t=a/b`, the point `(t*z, exp(t*z))` is algebraic over
`K=Q(z,exp z)` of degree at most `b^n`, and for `a != 0` its field has the same absolute
transcendence degree as `K`.  Denominators at most `B` therefore give order `B^2` samples, but on
the diagonal degree scale `D` is order `B^n`; fixed-degree Pila--Wilkie estimates say nothing.
More decisively, the Kummer conjugates multiply the selected roots by roots of unity, and every
nontrivial conjugate leaves the exponential graph.  Thus the usual large-Galois-orbit engine
contributes exactly one analytic point.

Replacing point counting by logarithmic capacity does not make the rational divisions uniform.
For a hypothetical `P(e,log 2)=0`, the transported polynomial
`Q_m(X,Y)=P(X^m,mY)` vanishes at `(e^(1/m),(log 2)/m)`, but on the analytic graph it is simply
`F(m*t)` for `F(t)=P(e^t,t*log 2)`: every new zero is the original one after recentering.  The exact
pullback formula `cap(phi_m^-1 K)=cap(K)^(1/m)` for `phi_m(z)=z^m` cancels the degree multiplication
`deg(R∘phi_m)=m*deg R`, and `Y -> mY` only increases height.  For all Farey fractions of
denominator at most `B`, there are order `B^2` zeros but the product relation has degree order
`B^3` and log-height `O(B^3 log B)`; its Markov derivative bound exceeds the Farey mesh gain by
order `B^4`.  Shears have the same exact equality between capacity dilation and coefficient-height
dilation, and the adelic scaling factors cancel by the product formula.  Thus the orbit has a
positive-capacity closure only because the defining polynomial varies with degree and height; a
single uniformly small integer polynomial never emerges.

If the slope `z` is admitted as a parameter, the logarithmic lift of the whole family is the
straight semialgebraic line `t*(z,z)`, which lies in the positive-dimensional block discarded by
the counting theorem.  If absolute rationality is required instead, the coordinates are not
algebraic over `Q`.  Already the unconditional curve `t -> (t,2^t)` contains order `B^2`
algebraic points at rational parameters with growing radical degree, so a uniform estimate strong
enough for this diagonal is false.  Specializing a transcendence basis to recover absolute
algebraic points again destroys `Y=exp X`.

### Compact-strip o-minimal branch audit

O-minimal branch selection does not alter the defect-one normal form.  A globally minimal
counterexample has `td_Q Q(z,exp z)=n-1`, lies in `C_E`, and is a nonsingular isolated zero of a
square Khovanskii system after finitely many auxiliary coordinates are added.  Choose compact
rectangles around those coordinates whose imaginary widths are less than `2*pi`.  Complex
exponentiation on such a box is definable in `R_an,exp`, using real exponentiation and restricted
sine and cosine.  The inverse-function theorem makes the selected Khovanskii zero an isolated
zero-dimensional definable germ.  Its Pila--Wilkie count is therefore `O(1)` (usually zero when
only algebraic points are counted), independently of its ordinary transcendence degree.

There is one valid positive statement, but its missing hypothesis is exact.  For a fixed
algebraic locus and a fixed compact strip, infinitely many common graph points force a
positive-dimensional definable/analytic component: a zero-dimensional complex-analytic set is
discrete and hence finite in a compact set.  Functional Ax--Lindemann or Ax--Schanuel can then
analyze that component and force the usual weakly special alternatives.  A branch-selected
Khovanskii point supplies only one isolated point.  Period translation either leaves the compact
strip, is identified with the same point in the fundamental quotient, or moves the algebraic
relation; it never supplies the required accumulation on one fixed locus.

For the mixed stress, on the strip `|Im V|<=pi` the system

`X=1,  exp(V)=2`

has the unique solution `(1,ell)`.  Adding a hypothetical `P(exp(X),V)=0` still gives this one
point.  Its logarithmic coordinate is transcendental, so the full point contributes no rational
or bounded-degree algebraic point to count.  The other branches `ell+k*omega` leave the strip,
and the same fixed polynomial `P(e,V)` can vanish on at most `deg_V P` of them.  Preserving the
chosen zero by writing `P(e,V-k*omega)` introduces the transcendental coefficient `omega` and a
different locus for every `k`.

Kummer division quantifies why projecting to the algebraic coordinate does not help.  For
`1<=b<=B` and `0<=k<b`, put

`w_(b,k)=(ell+k*omega)/b,   y_(b,k)=exp(w_(b,k))=2^(1/b)*zeta_b^k`.

The `B*(B+1)/2` values `y_(b,k)` are distinct, have exact degree `b` by Eisenstein applied to
`T^b-2`, and multiplicative Weil height `2^(1/b)<=2`.  Every lift `w_(b,k)` is transcendental by
Hermite--Lindemann.  Thus fixed-degree algebraic-point counting sees no full graph points; allowing
degree `b<=B` leaves the fixed-degree regime.  Projecting to `y` produces many algebraic points
inside an annulus, which is entirely semialgebraic algebraic part and is deliberately discarded by
the counting theorem.

For the period stress choose a width-`2*pi` strip centered at `omega`; the equations

`exp(U)=2,  exp(V)=1`

select only `(ell,omega)` locally.  Both inputs are transcendental, while projection to the
multiplicative coordinates is the single rational point `(2,1)`.  Period divisions
`V=omega*k/b`, with reduced `0<=k<b`, give roots of unity of height one and degree
`phi(b)<=b`; their number through denominator `B` is
`sum_(b<=B)phi(b)~3*B^2/pi^2`.  Every nonzero logarithmic lift is transcendental, and the projected
points lie on the algebraic unit circle.  Again the full graph has no such algebraic points and
the projection lies in the algebraic part.

The moving relation has the same exact cost.  If `P(ell,omega)=0`, then at
`(ell+k*omega,omega)` the rational polynomial is

`P_k(X_1,X_2)=P(X_1-k*X_2,X_2)`,

with `deg P_k=deg P=D` and
`h(P_k)<=h(P)+D*log(1+|k|)+O(D)`.  These are different fibers, not many zeros of one polynomial.
Putting `k` into a real definable family does not restore the graph: the identity
`exp(ell+k*omega)=2` selects `k in Z`, and an infinite discrete integer set is not definable in an
o-minimal structure.  Restricting to `|k|<=B` uses sine and cosine on an interval whose oscillation
count and definable complexity grow with `B`; quotienting by the deck group collapses all integer
fibers to the original point.

An unconditional counterfeit family isolates the arithmetic mismatch.  The definable curve

`L={(x,t):0<=x<=1, t=exp(x)}`

has order `H^2` rational target parameters `t in [1,e]` of height at most `H`.  Except for
`(0,1)`, their lifts `x=log t` are transcendental by Hermite--Lindemann, so they are not rational
or algebraic points of `L`; after projection they fill an interval, an algebraic block.  This is
exactly what happens to the logarithm and period divisions above.  Pila--Wilkie counts algebraic
points in all coordinates of one fixed definable set, while Ax--Lindemann requires a
positive-dimensional algebraic/semialgebraic source.  The minimal defect point supplies neither:
compact branch selection makes it a singleton, and branch amplification sacrifices a fixed
definable locus, fixed algebraic degree, or algebraicity of the logarithmic coordinates.

### Exact mixed two-dimensional stress tests

The two registered boundary modules rule out treating the mixed case as routine scalar extension.
For `(log 2, log 2 + 1)`, the desired lower bound is precisely algebraic independence of `log 2`
and `e`; separate transcendence of each generator is insufficient.  For `(a, exp a)` with
nonzero algebraic `a`, the desired lower bound is precisely algebraic independence of `exp a` and
`exp (exp a)`.  Both families satisfy the original rational linear-independence hypothesis, and
both have coordinate transcendence degree one and require one genuinely relative exponential
degree.

When all exponential values are algebraic, Baker's theorem and the analytic subgroup theorem
control only degree-one expressions: under the relevant independence hypothesis, nonzero
`Qbar`-linear forms in the logarithms are transcendental. Algebraic independence requires control
of all monomials in those logarithms. Tensor, symmetric-power, and exterior-power representations
do not promote such monomials to logarithms of algebraic group points: the differential of every
torus representation remains linear in the logarithms. For `(log 2, 2*pi*I)`, this is the exact
gap between `Qbar`-linear independence and the checked target `trdeg Q(log 2, pi) = 2`.
Multiplicative independence cannot be assumed either: the independent family
`(log 2, log 2 + 2*pi*I)` has identical exponential values.

Noncommutative matrix groups do not promote the missing products to usable logarithmic
coordinates.  First, if `z` is transcendental, `H in M_r(Qbar)`, and `exp(zH)` is an algebraic
matrix, then `H` is semisimple.  Indeed, in an algebraic Jordan basis a nontrivial nilpotent part
would give an entry `exp(lambda*z)*z*N` immediately above the diagonal; the eigenvalue
`exp(lambda*z)` is algebraic and nonzero, so this would make `z` algebraic.  If such semisimple
directions lie in a nilpotent matrix Lie algebra, `ad H` is both semisimple (as the restriction of
the semisimple operator on `M_r`) and nilpotent (by nilpotence of the Lie algebra), hence zero.
They therefore commute.  Conversely, the Heisenberg construction
`exp(x*E_12)*exp(y*E_23)=I+x*E_12+y*E_23+x*y*E_13` does retain the desired product, but its first
two off-diagonal entries show that the factors can be algebraic only when `x,y` already are.
Using only the commutator hides those entries but gives `I+x*y*E_13`, whose algebraicity is exactly
the unproved algebraicity of the product.  Thus every finite nilpotent BCH encoding is circular.

The smallest solvable nonnilpotent example displays the complementary cancellation.  Put
`H=diag(1,0)`, `K=[[0,1],[0,1]]`, and `X=E_12`; then `K^2=K`, `[H,K]=X`, `[H,X]=X`, and
`[K,X]=-X`.  For `a=exp x`, `b=exp y`,
`A=exp(xH)=diag(a,1)` and `B=exp(yK)=[[1,b-1],[0,b]]` are algebraic whenever `a,b` are, while

`log(A*B)=[[x, a*(b-1)*(x-y)/(a-b)],[0,y]]`

for the branch with diagonal values `(x,y)` and `a!=b`.  The formal BCH term
`(x*y/2)[H,K]` is present, but the infinite weight string `ad(H)^k X=X` resums it into the displayed
algebraic-linear combination of `x,y`.  Even more sharply,
`A*B*A^(-1)*B^(-1)=I+(a-1)*(1-b^(-1))*X`; its logarithm is already algebraic and the formal leading
term `x*y*X` has been cancelled by all higher commutators.  At the period stress take
`x=log 2`, `y=pi*I` (so the original second scalar is `2*pi*I` and its algebraic generator is
`K/2`).  Then
`A=[[2,0],[0,1]]`, `B=[[1,-2],[0,-1]]`,
`log(AB)=[[log 2,-(4/3)*log 2+(4/3)*pi*I],[0,pi*I]]`, and
`log(ABA^(-1)B^(-1))=2*E_12`.  The apparent `(pi*I)*(log 2)` coordinate has vanished exactly.

This resummation persists in every triangular solvable representation.  For an algebraic upper
triangular matrix
`M=[[a,p,r],[0,b,q],[0,0,c]]` with distinct diagonal entries and chosen logarithms `l_a,l_b,l_c`,
functional calculus gives
`(log M)_12=p*(l_a-l_b)/(a-b)` and

`(log M)_13=r*(l_a-l_c)/(a-c)
 +p*q*(l_a/((a-b)*(a-c))+l_b/((b-a)*(b-c))+l_c/((c-a)*(c-b)))`.

All coefficients are algebraic and the logarithms occur only linearly.  Coincident eigenvalues
replace divided differences by derivatives of `log`, which are algebraic at algebraic nonzero
eigenvalues, so they introduce no products either.  Lie--Kolchin weights explain the dichotomy:
a nonzero torus weight gives `ad(H)^kN=chi(H)^kN` and hence an infinite, resumming BCH series; zero
weight makes the semisimple direction commute with the nilradical and removes the cross term.

The mixed stress `(1,log 2)` reaches the same boundary with algebraic matrices.  With
`N=E_12`, both `exp((log 2)*H)=diag(2,1)` and `exp(N)=I+N` are algebraic, but
`log(exp((log 2)*H)*exp(N))=[[log 2,2*log 2],[0,0]]`: only the already known linear logarithm is
recovered.  Putting the algebraic scalar `1` in a semisimple direction in order to expose `e`
instead gives `exp(H)=diag(e,1)`, which is not an algebraic matrix, so no algebraic logarithm
theorem applies.  Finally, the Zariski closure of the cyclic subgroup generated by any algebraic
matrix word is commutative; its primary logarithm is exactly of the divided-difference form above.
Applying the analytic subgroup theorem there sees only linear logarithms of algebraic eigenvalues,
while applying it to the noncommuting factors is outside its commutative hypothesis.  BCH therefore
adds no unconditional route from Baker's linear theorem to products of logarithms.

Regulators stop at the same linear boundary.  For the period stress pair, the `K_1` regulator of
the `S`-unit `2` records `log 2`, while `2*pi*I` is the kernel period of complex exponential, not a
second non-torsion `K_1(Q)` class.  Rational `K_2(Q)` vanishes, so exterior symbols cannot encode
their wedge; Bloch regulators add dilogarithmic or branch-dependent secondary terms.  The correct
Kummer 1-motive has period coordinates `t=2*pi*I` and `u=log 2`.  Baker/AST identifies its linear
period relations, but injectivity of `Qbar[t,t^-1,u] -> C` is exactly algebraic independence of
those two coordinates—the period-conjecture formulation is theorem-strength equal to the target.

Embedding the multiplicative uniformization into an elliptic/modular one adds fresh coordinates.
For `q=e^z` with `|q|<1`, the Tate quotient has
`j=J(q)=q^-1+744+196884q+...`; this infinite series is transcendental as a function of `q` and is
not an algebraic field operation on `Q(z,q)`.  Modular polynomials make every `J(q^N)` algebraic
over the first new value `J(q)` but never eliminate it, while period shifts leave `J` unchanged
and therefore forget the logarithm branch.  In the stress `(1,log 2)`, modularization adjoins
`2*pi*I`, `J(e^-1)`, and `J(1/2)`, which can absorb every modular lower bound; even geodesic
independence can require an uncontrolled relation between `log 2` and `2*pi*I`.  The exact period
stress `(log 2,2*pi*I)` sends the second nome to `1`, a cusp where the Tate curve degenerates and
`j` has a pole; all purely imaginary inputs likewise lie on the modular boundary.  Modular
Ax--Schanuel is functional and a point relation does not persist along the required family.
Theta and Eisenstein coordinates introduce the same fresh modular values and elliptic periods.

Classical four/six-exponentials amplification introduces uncontrolled values rather than a
relative degree.  The rational multiplier algebra
`{alpha : alpha*span_Q(z_1,z_2) subset span_Q(z_1,z_2)}` has dimension at most two (evaluation at
one nonzero basis vector is injective), whereas six exponentials requires three independent
multipliers.  Outside this algebra, `exp(alpha*z_i)` has no polynomial equation over the original
generated field.  In the stress field `K=Q(e,log 2)` of hypothetical degree one, algebraic
multipliers such as `sqrt 2,sqrt 3` actually make the first-row values algebraically independent
over `K` by Lindemann--Weierstrass, so they enlarge the field and discharge the classical theorem
without constraining `log 2`.  Baker controls the opposite linear logarithm boundary only.

The complementary additive/multiplicative coefficient matroids still do not control the
algebraic matroid.  Disjoint algebraic-value kernels imply restricted rank inequalities and, by
matroid union, a partition of the indices into an additively free part and a multiplicatively free
part.  But over `Qbar(t)`, the families `t^i` and `t+c_i` have maximally free coefficient
matroids while their combined algebraic-matroid rank is only one.  A block variant can also
satisfy exactly the algebraic-input independence supplied by Lindemann--Weierstrass and the
degree-one logarithm independence supplied by Baker, yet have total rank below `n`.  These are
representable matroids satisfying Ingleton: the mismatch is that coefficient relations use
constant `Q` scalars, whereas transcendence degree is the dimension of Kähler differentials over
the entire function field.  Excluding the models requires pointwise analytic compatibility with
`exp`, not another abstract rank inequality.

Divisors, logarithmic differentials, and the function-field Subspace Theorem give the same
constant-coefficient ranks in different language.  On a projective model, the kernels of
`q -> sum q_i*dz_i` and `q -> sum q_i*div(y_i)` are disjoint by Hermite--Lindemann, but their
`Q`-ranks need not be bounded by the model dimension.  In `Qbar(t)`, the counterfeit
`z=(t,t^2)`, `y=(t,t+1)` has both kernels zero and even satisfies the nondegenerate S-unit equation
`(t+1)-t=1`, while the combined Kähler-differential span and transcendence degree are one.
The identity `y=exp z` at a selected complex value does not imply `dz=dlog y` for abstract
derivations of the function field; in fact that identity of rational differentials would force
`y` and `z` to be constant on a projective model.  S-unit rank is controlled by divisor support,
not by variety dimension, and its product formula again omits the selected transcendental
archimedean point.

A rational basis can put the two disjoint coefficient kernels into canonical coordinate blocks:
algebraic-coordinate directions, algebraic-exponential directions, and a residual block.  Such a
`GL_n(Q)` change preserves transcendence degree because the coordinate fields agree and the two
exponential fields are mutually algebraic after clearing denominators.  The blocks nevertheless
do not add.  The canonical tuple `(1, log 2)` has one direction of each first type and no residual
direction, but its generated field is `Q(e, log 2)`; the required cross-block independence is
exactly the checked mixed obstruction.

Adding many algebraic perturbations also cannot transfer a bound back.  If `R` algebraic
`n`-blocks have jointly independent exponentials `E_r`, a tower count does show that at least
`R-d` blocks are jointly algebraically independent over a field `K` of transcendence degree `d`;
the deficit bound `sum_r(n-rank_K E_r)<=d` is sharp.  But the actual perturbed field for
`z+a_r` contains the products `y_i*E_{r,i}`, not `y_i` and `E_{r,i}` separately.  A good block
therefore contributes `n` fresh independent variables and makes the individual perturbed bound
automatic, regardless of the original `d`.  For symmetric perturbations `z+a,z-a`, the combined
rational basis change gives `(2z,2a)`; demanding the combined `2n` bound is equivalent to
`d+n>=2n`, exactly the original conjecture.  Abstract rational-function-field models realize all
the block ranks and intersections with arbitrary `d<n`.

Homogeneous dynamics gives an exact reformulation of polynomial dependence, but no pointwise
arithmetic gain.  For box degree `D`, put `N=(D+1)^2-1` and let `v_D(a,b)` list the nonconstant
monomials `a^i*b^j`.  The Gaussian lattice

`Lambda_D(a,b)={(c_0+c dot v_D,c): c_0 in Z[i], c in Z[i]^N}`

and flow `g_t=diag(exp(N*t),exp(-t),...,exp(-t))` are unimodular.  The vector belonging to the
polynomial `P=c_0+c dot v_D` satisfies

`||g_t*w_P||_infinity=max(exp(N*t)*|P(a,b)|,exp(-t)*||c||_infinity)`.

Thus `P(a,b)=0` exactly when one fixed nonzero lattice vector tends to zero, and minimization in
`t` gives `(||c||^N*|P(a,b)|)^(1/(N+1))`.  Boundedness of the orbit would require a uniform
lower bound `|P(a,b)| >= delta^(N+1)*H^(-N)`, while Minkowski's theorem already puts the sharp
Dirichlet exponent at `H^(-N)`.  The dynamics has repackaged the missing strict arithmetic margin.

Nor can quantitative nondivergence transfer generic functional independence to the selected
point.  The functions `a(s)=exp s`, `b(s)=log(1+s)` are algebraically independent by logarithmic
monodromy and the transcendence of `exp s` over `C(s)`.  If nevertheless
`P(e,log 2)=0` and `P(a(s),b(s))=kappa*(s-1)^r+...`, then the corresponding lattice vector is
`O(exp(-t))` throughout an interval
`|s-1| << exp(-(N+1)*t/r)`.  This exceptional interval shrinks to measure zero, exactly as allowed
by Kleinbock--Margulis type metric theorems.  The period deformation
`a(s)=log(1+s)`, `b(s)=2*pi*I*s` has the same defect at `s=1`; Baker excludes the affine-linear
fixed vectors, but a higher-degree escaping vector is precisely the desired algebraic relation.

The lattice construction uses neither the rational linear independence of the original inputs nor
the compatibility of the second coordinates with complex exponentiation.  Sharp counterfeits
therefore survive: `E(q+r*log 2)=3^q*2^r` on `Q+Q*log 2` has total transcendence degree one and
the lattice at `(3,log 2)` escapes along `X-3`; for a transcendental `T`, the independent inputs
`(T,T^2)` with `E(q*T+r*T^2)=2^q` have total transcendence degree one and escape along `Y-X^2`.
Dani correspondence detects dependence once present, but available homogeneous dynamics permits
exactly the prescribed exceptional point that Schanuel would have to rule out.

Pfaffian zero bounds make the specialization defect quantitative but do not remove it.  Suppose
conditionally that an irreducible `P in Q[U,V]` of total degree `D` satisfies
`P(e,log 2)=0`, and on `x>-1` put

`F(x)=P(exp(x),log(1+x))`.

The chain

`f_1=(1+x)^(-1),  f_2=log(1+x),  f_3=exp(x)`

has `f_1'=-f_1^2`, `f_2'=f_1`, and `f_3'=f_3`.  Thus `F` has Pfaffian format
`(r,alpha,beta)=(3,2,D)`, and the univariate Khovanskii bound for nondegenerate real zeros is

`2^(r*(r-1)/2)*beta*(alpha+beta)^r=8*D*(D+2)^3`.

The known relation forces only the single zero `F(1)=0`, comfortably inside this allowance even
for `D=1`.  Moreover `F` is not identically zero: continuation around `x=-1` fixes `exp(x)` and
replaces `log(1+x)` by `log(1+x)+2*pi*I*k`; infinitely many branches would force the polynomial
in its second argument, and then `P`, to vanish identically.  A sharp geometric counterfeit is
`P(U,V)=U*V-1`: on `x>0`, the function `exp(x)*log(1+x)-1` has exactly one simple zero, since its
derivative is positive, and its local degree is `+1`.  Thus all of the proposed local Pfaffian and
topological data coexist with an isolated algebraic relation between the two moving coordinates.
For comparison,
`P(exp(x),x)` has format `(1,1,D)` and Khovanskii bound `D*(D+1)`; more sharply it belongs to the
extended Chebyshev space spanned by `x^j*exp(k*x)` for nonnegative `j,k` with `j+k<=D`, of dimension
`(D+1)*(D+2)/2`, so it has at most that dimension minus one real zeros, with multiplicity.  It
does not pass through `(e,log 2)`: when its second coordinate is `log 2`, its first is `2`, and
reparametrization does not change that image.  A target-coordinate shear that forces the mixed
point must instead insert `log 2`, or an equally unproved relation involving it, into the
coefficients.

Reparametrization cannot overload the bound at fixed complexity.  For a polynomial `phi(t)` of
degree `q`, the chain for

`F(phi(t))=P(exp(phi(t)),log(1+phi(t)))`

has derivative degree `alpha=q+1`: explicitly
`((1+phi)^(-1))'=-phi'*(1+phi)^(-2)`,
`(log(1+phi))'=phi'*(1+phi)^(-1)`, and
`(exp(phi))'=phi'*exp(phi)`.  Its zero bound is therefore
`8*D*(D+q+1)^3`.  Producing `M` distinct copies of the known zero by imposing `phi(t)=1` already
requires `q>=M`.  Alternatively, multiplying `M` rational translates
`product_k F(t+r_k)` uses one exponential and two reciprocal/logarithm chain entries per
translate, so `r=2*M+1` and output degree `beta=M*D`; its Khovanskii allowance grows as
`2^(r*(r-1)/2)*M*D*(M*D+2)^r`.  The translates merely relabel the same selected zero, and
combining them necessarily increases the format.  Power or shear constructions instead move
the polynomial: for example the relation for `(e^q,q*log 2)` is obtained by a resultant and is a
different polynomial, with second-variable degree at most `q*deg_V(P)`.  There is consequently no
fixed-complexity family containing more forced sign changes than the zero theorem allows.

Real topological degree retains still less information.  On a small interval `I=(a,b)` containing
no zero of `F` other than `1`,

`deg(F,I,0)=(sgn(F(b))-sgn(F(a)))/2`

is `+1` or `-1` for an odd-order zero and zero for an even-order zero.  Hence an arbitrarily high
local intersection multiplicity contributes at most one signed unit.  This index persists under
uniform boundary approximation but supplies no arithmetic constraint.  Concretely, take degree
at most `m` rational Pade approximants `E_m=A_m/B_m` and `L_m=C_m/Q_m` to `exp(x)` and
`log(1+x)` near `x=1`.  If `d_U=deg_U(P)` and `d_V=deg_V(P)`, then clearing denominators in
`P(E_m,L_m)` gives

`N_m=B_m^d_U*Q_m^d_V*P(A_m/B_m,C_m/Q_m)`,

with `deg N_m<=m*(d_U+d_V)<=2*m*D`.  Rouche's theorem retains the local complex multiplicity, and
real degree retains a sign-changing root, but the available Bezout budget grows with `m`; the
nearby root need not remain `x=1` or encode the original field.  A fixed-degree algebraic family
cannot converge to both transcendental graph functions, so every algebraic approximation pays
exactly this unbounded-degree cost.

The period/complex stress is even less compatible with the proposed invariant.  A hypothetical
`P(log 2,2*pi*I)=0` gives one complex zero of
`P(log(1+t),2*pi*I*t)` at `t=1`; as a map from one real variable to two real coordinates it has no
one-dimensional Brouwer degree and a perturbation can remove the zero.  Introducing two real
parameters can define a local degree, but again only for one isolated point and with no arithmetic
normalization.  If the exponential coordinate is included, then
`exp(2*pi*I*t)=cos(2*pi*t)+I*sin(2*pi*t)` is not globally Pfaffian: it has infinitely many period
zeros.  On each interval avoiding a half-integer it becomes Pfaffian through
`h=tan(pi*t)` and `k=(1+h^2)^(-1)`, with
`h'=pi*(1+h^2)` and `k'=-2*pi*h*k`; covering a long interval requires a number of charts linear
in its length.  Periodicity therefore spends chart complexity at exactly the rate at which it
creates zeros.  Pfaffian finiteness, local degree, and algebraic graph approximation all tolerate
the single exceptional mixed zero and yield no Schanuel inequality.

Universal exponential differentials reverse, rather than complete, the continuity route.  Put

`Omega^E=Omega_(C/Q)/<d(exp(x))-exp(x)*d(x) : x in C>`

and write `d_E x` for the image of `d(x)`.  Its `C`-linear dual is exactly the space of
exponential derivations

`Der_E(C)={D:C->C : D is a derivation and D(exp(x))=exp(x)*D(x)}`.

Indeed this is the universal property of Kahler differentials followed by the displayed
quotient.  If `K=Q(z_1,...,z_n,y_1,...,y_n)` with `y_i=exp(z_i)` and `d=trdeg_Q K`, the map

`Omega_(K/Q) tensor_K C -> Omega^E`

has image exactly `span_C{d_E z_i}`, since `d_E y_i=y_i*d_E z_i`.  Consequently, if
`rho=dim_C span{d_E z_i}`, then `rho<=d`; equivalently the restrictions
`{(D(z_1),...,D(z_n)):D in Der_E(C)}` have dimension exactly `rho`.  Thus `rho=n` would prove
the desired bound immediately, but it is a strictly stronger condition, not a reformulation of
Schanuel.

For every algebraic relation `R(z,y)=0`, differentiation gives the explicit row relation

`sum_i (R_(X_i)(z,y)+y_i*R_(Y_i)(z,y))*d_E z_i=0`.

Thus all derivation-value vectors lie in the kernel of the exponential Jacobian `J_E`, whose rows
are the displayed coefficients.  When the algebraic locus `W` is smooth, this kernel is the local
tangent intersection `T_(z,y)W intersection T_(z,y)Gamma_exp`, after identifying the exponential
tangent with the `z`-coordinates.  The global restriction rank `rho` is at most this local kernel
dimension: a pointwise tangent vector need not extend to an exponential derivation of all of `C`,
and that extension is precisely the exponential-closure problem.

There is an exact unconditional rank estimate in the hypothetical defect-one case.  Let
`C_E=ecl_C(Q)`, the exponential-algebraic closure defined by nonsingular Khovanskii systems, put

`ell=ldim_Q(z/C_E),  t=trdeg_(C_E) C_E(z,exp(z))`,

and retain `rho=dim_C span{d_E z_i}`.  Kirby's derivation-closure theorem identifies `rho` with
the `ecl`-dimension of `z` over `C_E`, and its weak Schanuel inequality gives

`t-ell>=rho`.

Also `rho<=ell`, because every rational linear relation modulo `C_E` gives the corresponding
linear relation among the `d_E z_i`.  If `d=n-1`, then `t<=d`, hence

`ell+rho<=n-1,  2*rho<=n-1,  rho<=floor((n-1)/2)`.

Therefore the exact universal-differential rank defect is `n-rho`, at least
`ceil((n+1)/2)`, not merely one.  In dimension two a hypothetical defect-one tuple has `rho=0`:
every exponential derivation annihilates both inputs.  More generally, if `ell=n` then the weak
inequality already proves `d>=n`; any counterexample must lose a nonzero rational direction into
the fixed constant pregeometry `C_E`.  Minimality under proper rational projections does not
exclude this, because `C_E` contains many transcendental numbers.

There is nevertheless a useful exact localization theorem: full Schanuel over `C` is equivalent
to Schanuel restricted to finite `Q`-linearly-independent tuples contained in `C_E`.  To prove the
nontrivial direction, let `z=(z_1,...,z_n)` be `Q`-linearly independent, put
`V=span_Q{z_i}`, and set `k=dim_Q(V intersection C_E)`.  Choose a `Q`-basis
`a=(a_1,...,a_k)` of this intersection and extend it by `b=(b_1,...,b_m)`, `m=n-k`, to a basis
of `V`.  This is a rational basis change, so

`td_Q Q(z,exp z)=td_Q Q(a,b,exp a,exp b)`.

Moreover `ldim_Q(b/C_E)=m`: if a rational combination of the `b_j` lay in `C_E`, it would lie in
`V intersection C_E=span_Q(a)` and contradict that `(a,b)` is a basis.

Put `F_a=Q(a,exp a)` and `F=F_a(b,exp b)`.  The field `C_E` is an `ecl`-closed exponential
subfield, and `F_a subset C_E`.  Kirby's unconditional relative Ax inequality,
with `rho=ecldim(b/C_E)=dim_C span{d_E b_j}`, is

`t=td_(C_E) C_E(b,exp b) >= ldim_Q(b/C_E)+rho=m+rho`.

There is no field-intersection loss in bringing this estimate back to `F`.  For fields
`F_a subset C_E` and a finite generating list `S=(b,exp b)`, choose a maximal subset
`T subset S` algebraically independent over `C_E`.  Then `|T|=td_(C_E) C_E(S)=t`, while the
same `T subset F` is algebraically independent over the smaller field `F_a`.  Hence

`td_(F_a) F>=t>=m+rho`.

The exact tower formula now yields

`td_Q F=td_Q F_a+td_(F_a)F >= td_Q Q(a,exp a)+m+rho`.

In particular, with `delta(u)=td_Q Q(u,exp u)-length(u)`, one has the structural inequality

`delta(z)>=delta(a)+rho`.

If Schanuel holds for tuples in `C_E`, the first term on the right is nonnegative, and therefore
`td_Q F>=k+m=n`.  The converse restriction is immediate.  Equivalently, any counterexample in
`C` would produce a counterexample basis `a` entirely inside `C_E`; if `V intersection C_E=0`,
the relative theorem already proves Schanuel (indeed with the additional surplus `rho`).

More strongly, suppose a counterexample is chosen with globally minimal positive length `n`.
Since `delta(z)<0` and `delta(z)>=delta(a)+rho` with `rho>=0`, one has `delta(a)<0`; in
particular `k>0`, and `a` is itself a counterexample of length `k`.  Minimality rules out `k<n`,
so `k=n`, `m=0`, and `V=V intersection C_E`.  Every original `z_i` therefore lies in `C_E`, not
merely some rationally equivalent tuple, and `rho=dim_C span{d_E z_i}=0`.  Thus any globally
minimal failure is forced wholly into the exponential-algebraic constant core, where the
derivation method is exactly blind.

This proof does not assert the generally false-looking additive formula
`td_Q F=td_Q C_E+td_(C_E)C_EF`, and it does not require `F intersection C_E=F_a`.  That
intersection may be much larger.  It can only add elements to the extension `F/F_a`; it cannot
make the displayed relative basis `T`, already independent over all of `C_E`, dependent over
`F_a`.  Nor must a relative basis be chosen from the inputs `b` alone: choosing it from the
original field generators `(b,exp b)` is both always possible and exactly what the tower argument
requires.

The mandatory stresses show where the theorem localizes, rather than solves, the difficulty.
Both `1` and `ell=log 2` lie in `C_E`: the latter is a nonsingular zero of `exp(X)-2`, and closure
under exponentiation also puts `e` in `C_E`.  Thus for `(1,ell)` one has `(k,m,rho)=(2,0,0)`, and
the restricted assertion is exactly `td_Q Q(e,ell)>=2`.  Likewise `omega=2*pi*I` is a
nonsingular zero of `exp(X)-1`, so `(ell,omega)` is wholly in `C_E` and the reduction is exactly
the missing algebraic independence of `ell` and `omega`.  Rationally independent algebraic inputs
also have `k=n,m=rho=0`; Lindemann--Weierstrass supplies equality there.  Hence the equivalence is
valid and isolates all possible failures inside the countable field `C_E`, but the two hardest
mixed/period configurations already lie entirely in that restricted core.

Presenting that core by Khovanskii equations does not make an extra algebraic relation
overdetermined.  By finite character of `ecl`, after adjoining finitely many auxiliary coordinates
any finite `u subset C_E` occurs inside a tuple `x=(u,v) in C^m` satisfying a square system of
exponential polynomials over `Q`,

`F_1(x)=...=F_m(x)=0,   det(partial F_i/partial x_j)(x)!=0`.

A Schanuel defect supplies a nonzero `P in Q[U,Y]` with `G(x)=P(u,exp u)=0`.  But in the local
analytic ring at `x`, the inverse-function theorem says that `(F_1,...,F_m)` is the maximal ideal:
the `F_i` are local coordinates.  Hence every such `G`, with no arithmetic hypothesis at all, has

`G=sum_i H_i*F_i`

for analytic germs `H_i`.  The extra row is therefore automatically redundant at the selected
point.  The coefficients `H_i` depend on the chosen zero and need not be rational exponential
polynomials, so this local identity has no global arithmetic content.

For the mixed witness this is completely explicit.  Set

`F_1=x_1-1,  F_2=exp(x_2)-2,  G=P(exp(x_1),x_2)`.

At `(1,ell)` the Jacobian determinant of `(F_1,F_2)` is `2`.  With local coordinates
`s=x_1-1,t=exp(x_2)-2`, the extra germ is

`H(s,t)=P(exp(1+s),Log(2+t))`,

using the branch with `Log 2=ell`; `H(0,0)=0` gives `H=s*A+t*B` by its convergent Taylor series.
Globally the square system has the branch lattice
`(1,ell+k*omega)`, `k in Z`.  Since `e` is transcendental, the nonzero polynomial `P(e,T)` cannot
vanish identically, so `G` vanishes on at most `deg_T P` of these branches.  A point relation has
not propagated to the infinite common-zero set required by a factor theorem.

For the period witness take

`F_1=exp(x_1)-2,  F_2=exp(x_2)-1,  G=P(x_1,x_2)`.

At `(ell,omega)` the square Jacobian again has determinant `2`, and the inverse coordinates are
`x_1=Log(2+s)`, `x_2=omega+Log(1+t)`.  Thus `G` is again in `(F_1,F_2)` only in the local analytic
ring.  The global zero set is
`(ell+k*omega,l*omega)`, `(k,l) in Z^2`.  On the selected row `l=1`, the polynomial
`P(X,omega)` is nonzero because `omega` is transcendental, and hence has at most `deg_X P` zeros.
Indeed a nonzero rational polynomial cannot vanish on the whole grid: infinite vanishing in each
row first makes it identically zero in `X`, and infinitely many rows then make every coefficient
zero in `Y`.

Ordinary resultants see even less.  On replacing `exp(x_i)` by algebraic coordinates `Y_i`, the
mixed ideal is

`(X_1-1,Y_2-2,P(Y_1,X_2))`,

whose quotient is `Q[X_2,Y_1,Y_1^(-1)]/(P)` and has Krull dimension one.  The period ideal
`(Y_1-2,Y_2-1,P(X_1,X_2))` has quotient `Q[X_1,X_2]/(P)`, also of dimension one.  The missing
equations `Y_i=exp(X_i)` are analytic, not algebraic, so neither a multivariate resultant nor the
ordinary Nullstellensatz produces `1` from either ideal.

The strongest relevant unconditional Shapiro-type result has exactly the absent hypothesis:
van der Poorten--Tijdeman prove that a simple one-variable exponential polynomial and an arbitrary
exponential polynomial with infinitely many common zeros have a common exponential-polynomial
factor.  The general irreducible version is known only conditional on Schanuel.  After fixing
`x_1=1` in the mixed case, the pair is `exp(T)-2` and `P(e,T)` and has only finitely many common
zeros; after fixing `x_2=omega` in the period case, it is `exp(X)-2` and `P(X,omega)`, again with
only finitely many.  Exponential-ideal Nullstellensatz statements concern vanishing on an entire
zero set (or existence in an auxiliary exponential domain), not one distinguished complex zero,
so their radical-membership hypotheses also fail.

Zero-dimensional traces collapse for the same local reason.  The local algebra
`O_(C^m,x)/(F_1,...,F_m)` has length one and is `C`; multiplication by `G` is zero and its trace
and Grothendieck residue are tautologically zero.  Globally, the stress systems have infinitely
many period branches, so there is no finite `Q`-algebra whose field trace symmetrizes the selected
zero.  Restricting to a fundamental strip selects a logarithm branch by transcendental analytic
inequalities and does not create an arithmetic trace.

Two branch-selection examples make the no-go sharp on the mandatory points.  At `(1,ell)`, the
square system

`x_1-1=0,  exp(2*x_2)-4=0`

has Jacobian determinant `8`, while the extra rational exponential equation
`exp(x_2)-2=0` holds.  It is not in the global radical of the square ideal, since the branch
`(1,ell+pi*I)` satisfies the square system but not the extra equation.  At `(ell,omega)`, use

`exp(2*x_1)-4=0,  exp(x_2)-1=0`

with the extra equation `exp(x_1)-2=0`; the determinant is again `8`, and
`(ell+pi*I,omega)` is the opposite branch.  Thus a nonsingular square Khovanskii system plus an
additional rational relation is fully compatible even for rationally independent inputs.  Any
principle excluding the hypothetical cross-relation must distinguish the chosen analytic branch
arithmetically; Nullstellensatz, resultant, common-factor, and local-trace mechanisms do not.

An analytic or zeta-regularized resultant makes the same new-value obstruction quantitative.
Assume that an irreducible primitive

`P(U,V)=a_d(U)*V^d+a_(d-1)(U)*V^(d-1)+...`

satisfies `P(e,ell)=0`.  Since `e` is transcendental, `Q(V)=P(e,V)` remains irreducible and
separable over `Q(e)`; write its complex roots as `alpha_1=ell,alpha_2,...,alpha_d`.  The most
direct finite analytic resultant is

`R_P(e)=product_(j=1)^d (exp(alpha_j)-2)=0`.

Although invariant under permutations of the roots, this is not the field norm of an algebraic
element.  An embedding over `Q(e)` sends `ell` to `alpha_j` but sends the actual field element
`exp(ell)=2` to `2`, not to `exp(alpha_j)`.  Applying the analytic exponential after conjugating
therefore introduces the new values `exp(alpha_j)` rather than an algebraic symmetric function of
the coefficients.

The logarithm lattice gives an exact equivalent formula.  With `omega=2*pi*I` and `w=V-ell`,
Hadamard factorization is

`exp(V)-2=2*w*exp(w/2)*product_(k>=1)(1+w^2/(4*pi^2*k^2))`.

Use symmetric zeta regularization, normalized by
`product_(k>=1)^zeta (4*pi^2*k^2)=1`; equivalently

`product_(k in Z)^zeta (w+omega*k)=2*sinh(w/2)`.

Concretely, with `w_j=ell-alpha_j`, define the multiplicative symmetric product by the convergent
formula

`product_(k!=0)^(sym,zeta) Q(ell+omega*k)
 :=a_d(e)^(-1)*product_j product_(k>=1)(1+w_j^2/(4*pi^2*k^2))`.

This fixes the normalization and avoids any multiplicative-anomaly convention.

Removing the common factor at `k=0` gives the canonical reduced lattice determinant

`D_P=Q'(ell)*product_(k in Z, k!=0)^zeta Q(ell+omega*k)`
`   =product_(j=2)^d 2*sinh((ell-alpha_j)/2)`.

Here the regularized number of nonzero lattice points is `2*zeta(0)=-1`, so the product of the
leading coefficients contributes `a_d(e)^(-1)` and is cancelled exactly by `Q'(ell)`.  Since

`2*sinh((ell-alpha_j)/2)
 =-(1/2)*exp((ell-alpha_j)/2)*(exp(alpha_j)-2)`,

Vieta's formula yields the fully explicit identity

`D_P=(-1)^(d-1)*2^(1-d/2)
 *exp(a_(d-1)(e)/(2*a_d(e)))
 *product_(j=2)^d(exp(alpha_j)-2)`.

Thus regularization removes the universal powers of `2*pi` but not the exponentials of the
algebraic branches or the new value `exp(a_(d-1)(e)/(2*a_d(e)))`.  The unreduced product is zero
for the tautological reason that `alpha_1=ell`; the reduced product has no known arithmetic norm
or lower bound.

Low degree already saturates the construction.  If `P(U,V)=q(U)*V-p(U)`, with
`phi=p/q`, its analytic resultant is simply

`exp(phi(U))-2`,

and `(R+2)'=phi'*(R+2)`.  Rational coefficients and a first-order differential equation do not
control its transcendental zero set: for `phi(U)=U` the zeros are exactly `ell+omega*Z`.  At
`U=e`, the assertion `exp(phi(e))-2=0` is just the original special algebraic relation
`phi(e)=ell+omega*k`, not a consequence of the differential equation.  In degree two, writing
the roots as `(s+-sqrt(Delta))/2`, the finite resultant is

`exp(s)-4*exp(s/2)*cosh(sqrt(Delta)/2)+4`.

The new `cosh` and exponential values cannot be rewritten algebraically using the elementary
symmetric functions `s` and the product of the roots.  In general the finite resultant is a sum of
`exp(sum_(j in S)alpha_j)` over subsets `S`; these functions are monodromy-invariant and satisfy a
linear differential system over the algebraic function field, but holonomicity supplies no
arithmetic information at the transcendental parameter `U=e`.

The period analogue has the same exact form twice.  Suppose `P(ell,omega)=0` and, as a polynomial
in `V`, write

`P(U,V)=a_d(U)*product_j(V-beta_j(U))`, with `beta_1(ell)=omega`.

The first analytic resultant

`A(U)=product_j(exp(beta_j(U))-1)`

is a single-valued symmetric analytic function away from the discriminant and satisfies
`A(ell)=0`, but it adjoins all `exp(beta_j(U))`.  Centering the period lattice at `omega` gives

`D_(P,V)=partial_V P(ell,omega)
 *product_(k!=0)^zeta P(ell,omega+k*omega)`
` =product_(j=2)^d 2*sinh((omega-beta_j(ell))/2)`
` =-exp(a_(d-1)(ell)/(2*a_d(ell)))
   *product_(j=2)^d(exp(beta_j(ell))-1)`.

The last sign uses `exp(d*omega/2)=(-1)^d`.  One must then compare the new function `A(U)` with
`exp(U)-2`; they share the single zero `U=ell`, but `A` is generally an exponential of algebraic
branches, not an exponential polynomial to which Shapiro's theorem applies.  A two-dimensional
product over `(ell+omega*k,omega*l)` has no value until an ordering, logarithm branch, and spectral
cut are chosen; already for linear factors the standard zeta choices are Epstein/Barnes
determinants and add double-gamma or modular constants.  Such a regularization cannot remove the
already visible branch exponentials.

Hence symmetry, Vieta relations, differential equations, Hadamard products, and zeta
regularization all produce rigorous analytic invariants, but none is an arithmetic function of
`e` or `ell`.  Making the reduced analytic resultant algebraic over the original generated field,
or proving it nonzero there by a norm estimate, would require exactly the missing compatibility
between algebraic conjugation and complex exponentiation.

The sharp closure equivalence is algebraic, not Schanuel's conjecture.  For every `A subset C`,
Kirby's theorem gives

`a in ecl_C(A)  iff  D(a)=0 for every D in Der_E(C) with D|_A=0`.

Equivalently, `d_E a` lies in the span of the `d_E A`; in particular
`d_E a!=0` iff some exponential derivation is nonzero at `a`.  Thus existence of a derivation
separating a prescribed element is equivalent to exponential transcendence of that element, not
to its contribution to ordinary transcendence degree.  The standard complex exponential has the
countable-closure property: over a countable set there are countably many Khovanskii systems, and
their nonsingular analytic zeroes form a countable set.  Hence `C_E` is countable, so there are
unconditionally many nonzero exponential derivations on `C`; they are not consequences of
Schanuel.

All of those nonzero derivations are necessarily discontinuous in the usual topology.  Any
ordinary derivation kills `Qbar`, which is dense in `C`, so a continuous derivation is zero.  An
additive map with closed graph is continuous by the closed-graph theorem for locally compact
Polish groups; likewise Borel measurability, local boundedness, or the Baire property implies
continuity.  Thus automatic-continuity hypotheses kill every useful `E`-derivation.  Conversely,
the algebraically constructed derivations obtained by assigning values on an `ecl`-basis have
nonclosed graphs.  The same construction works in free and pseudoexponential fields, showing
that the derivation-closure theorem contains no hidden analytic normalization.  Concretely, on a
free exponential generator `b`, prescribing `D(b)=1` forces only
`D(exp(b))=exp(b)` and extends along an `ecl`-basis; pseudoexponential predimension axioms permit
exactly this derivation while providing no topology in which it should be continuous.

The mandatory equality cases expose the loss exactly.  For `(1,log 2)` every `E`-derivation has

`D(1)=0,  D(e)=e*D(1)=0,  0=D(2)=2*D(log 2)`,

so all four relevant exponential differentials vanish, even though the target equality is the
algebraic independence of `e` and `log 2`.  For `(log 2,2*pi*I)`, the equations
`exp(log 2)=2` and `exp(2*pi*I)=1` similarly force both input differentials to vanish, while their
conjectural algebraic independence remains invisible.  If the `z_i` are rationally independent
algebraic numbers, then `d_E z_i=d_E exp(z_i)=0` for every `i`, although
Lindemann--Weierstrass proves the exponentials algebraically independent and gives equality in
Schanuel.  Universal exponential differentials measure `ecl`-dimension; they deliberately erase
the transcendence contributed by exponentials of exponential-algebraic constants.  Hence neither
analytic continuity nor discontinuous derivation closure can supply the missing ordinary
transcendence-degree bound.

Adjoining a finite Khovanskii witness for the lost rational direction only makes the constants
obstruction explicit.  The precise local statement is the following isolated-constant adjunction
lemma.  Let `F=(F_1,...,F_m)` be exponential polynomials over `Q`, let `u^0 in C^m` satisfy

`F(u^0)=0,  det J_F(u^0)!=0`,

write `c=u^0_1`, and let `q in Q^n` be nonzero.  In variables `(u,z)`, the combined equations

`F(u)=0,  u_1=q dot z`

have Jacobian rank `m+1`.  Their analytic solution germ is smooth of dimension `n-1`, with

`du=0,  q dot dz=0`.

This follows immediately from the inverse function theorem applied to `F`; the witness variables
are locally fixed, and the coupling is just one affine hyperplane in the input variables.  After
a rational basis change the germ is `(c,w_2,...,w_n)`, so functional Ax--Schanuel treats
`c,exp(c)` as constants and sees at most the `n-1` varying directions.  It cannot recover their
ordinary transcendence over `Q`, which is exactly the missing unit.

Nonsingularity also defeats a multiplicity or excess-intersection argument.  In the convergent
local ring `R=C{u-u^0}`, the functions `F_1,...,F_m` are a regular system of parameters, so

`(F_1,...,F_m)=(u_1-u^0_1,...,u_m-u^0_m)`.

Every additional analytic equation `H(u)` with `H(u^0)=0` therefore has
`H=sum A_i F_i` locally.  Adding `H` does not change the length-one reduced point or the Jacobian
rank.  More exactly, the overdetermined Koszul complex `K_R(F_1,...,F_m,H)` has

`H_0=C,  H_1=C,  H_j=0 for j>=2`,

and Euler characteristic zero: the extra vanishing equation creates one derived syzygy, not a
positive-dimensional germ or positive intersection number.  The coefficients `A_i` live in the
complex analytic local ring and can contain the selected constants; this membership is not a
Bezout identity over `Q` and gives no global algebraic eliminant.

If an additional equation depends also on `z`, reduction modulo `F` and `u_1-q dot z` leaves an
arbitrary analytic germ in the remaining `n-1` coordinates.  It may cut their dimension or may
vanish identically and produce the preceding syzygy; nonsingular isolation of `u^0` forces
neither alternative and never creates a new positive-dimensional component.

The basic witnesses already realize every obstruction.  They are

`c=1:       F(T)=T-1,       F'(c)=1`,
`c=log 2:   F(T)=exp(T)-2,  F'(c)=2`,
`c=2*pi*I:  F(T)=exp(T)-1,  F'(c)=1`.

The last equation has all period roots, but each is a separate nonsingular local point;
exponential algebraicity is local isolation, not algebraic conjugacy.  Eliminating a Khovanskii
witness cannot generally produce a nonzero ordinary polynomial for `c`: doing so in the second
or third examples would make `log 2` or `2*pi*I` algebraic.  Flattening exponential terms by new
variables merely leaves equations of the form `Y=exp(X)`, so algebraic elimination never removes
the exponential graph condition.

For the mixed stress, suppose conditionally that `P(e,log 2)=0`.  In variables `(a,b)` take

`F_1=a-1,  F_2=exp(b)-2,  H=P(exp(a),b)`.

At `(1,log 2)` the first two equations have Jacobian `diag(1,2)` and already define a reduced
point.  In
`R=C{a-1,b-log 2}` one has `(F_1,F_2)=(a-1,b-log 2)`, hence `H` lies in this ideal.  Its
differential

`dH=e*P_U(e,log 2)*da+P_V(e,log 2)*db`

is automatically in the span of `dF_1=da` and `dF_2=2*db`.  Thus the hypothetical polynomial
relation is a redundant third local equation; the Koszul homology is `C` in degrees zero and one
and its selected zero has no excess multiplicity.  Globally, `b=log 2+2*pi*I*k`, while the
nonzero polynomial `P(e,V)` can vanish at only finitely many branches.  There is no monodromy
principle forcing the relation from the selected logarithm to every branch.

The period stress is identical.  At `(a,b)=(log 2,2*pi*I)`, the square system

`exp(a)-2=0,  exp(b)-1=0`

has Jacobian `diag(2,1)`.  A hypothetical ordinary relation `P(a,b)=0` is again already in its
maximal analytic ideal and contributes only the degree-one Koszul syzygy.  For `c=1`, the witness
`T-1=0` is even algebraic, but it still says nothing about the ordinary transcendence of
`exp(1)=e`; this is the one-dimensional algebraic-input equality case.

If a defect-one algebraic locus `W` is adjoined as well, the same bookkeeping persists.  For
transcendental `c`, a `Qbar`-defined irreducible `W` cannot have the rational function `q dot X`
identically equal to `c`, so the coupling cuts a fiber rather than enlarging `W`; for algebraic
`c` it may already be an equation of `W`, as `X_1=1` is in the mixed locus.  Critical fibers can
raise local multiplicity but nonsingularity of `F` imposes no condition on that criticality and
no positive-dimensional component.  Isolation plus a second algebraic relation therefore
reproduces precisely the zero-dimensional constants block.  Any theorem turning this adjunction
into one unit of ordinary transcendence would already have to assert that exponential-algebraic
constants such as `e`, `log 2`, and `2*pi*I` acquire the missing relative algebraic independence,
which is the original mixed/period problem.

Global residues of a Khovanskii witness retain the whole logarithm lattice and do not make its
selected branch arithmetic.  Let `a` be positive algebraic, choose the real logarithm `L=log a`,
put `tau=2*pi*I`, and set

`F(T)=exp(T)-a,  T_k=L+tau*k  (k in Z)`.

All zeroes are simple and `F'(T_k)=a`.  If a rectangle `R_N` contains exactly the zeroes with
`-N<=k<=N` and `h` is holomorphic on it, the argument principle and the one-variable residue
formula give

`(1/(2*pi*I))*integral_(boundary R_N) h(T)*F'(T)/F(T) dT
   =sum_(k=-N)^N h(T_k)`,

`(1/(2*pi*I))*integral_(boundary R_N) h(T)/F(T) dT
   =(1/a)*sum_(k=-N)^N h(T_k)`.

For `h=1` the first expression is the integer `2*N+1`; more generally a periodic
rational-exponential weight gives the same algebraic value on every branch, but detects no
logarithm.  For `h(T)=T^j`, write

`sigma_0(N)=2*N+1,  sigma_(2r)(N)=2*sum_(k=1)^N k^(2r)`.

Then the exact symmetric trace is

`S_j(N)=sum_(r=0)^floor(j/2) binom(j,2*r)*L^(j-2*r)*tau^(2*r)*sigma_(2*r)(N)`.

Thus rational coefficients of `F` do not make weighted residues rational.  For `exp(T)-2`,
already `S_1(N)=(2*N+1)*log 2`; the Grothendieck residue sum is half of this.  For
`exp(T)-1`, `L=0`, the odd traces vanish by the chosen symmetric cutoff but

`S_2(N)=-4*pi^2*N*(N+1)*(2*N+1)/3`.

The period has merely moved from the zeroes into the boundary term.  Higher traces are Faulhaber
polynomials in `N` with coefficients in `Q[L,tau^2]`.  They diverge as `N` grows, and zeta or
Hadamard regularization replaces them by branch-dependent Bernoulli expressions in `L/tau`; it
does not produce a canonical `Q`-linear trace.

The contour calculation explains the obstruction exactly.  The logarithmic derivative `F'/F`
is `tau`-periodic.  Periodicity cancels the horizontal sides when `h` is also periodic, in which
case all branches receive the same value and no logarithm is detected.  A nonperiodic weight
capable of distinguishing `T_0` has a jump `h(T+tau)-h(T)` on the horizontal boundary; its
boundary contribution supplies the powers of `log a` and `2*pi*I` in the displayed formula.  A strip of height
`2*pi` can select the real branch of `log 2`, but choosing that strip uses the real order and the
cuts at imaginary height `+-pi`.  Shifting the strip selects another branch.  For `exp(T)-1` the
principal logarithm is `0`, not `2*pi*I`; selecting the latter requires the external winding label
`k=1`.

The standard branch projector does not avoid this cost.  The elementary interpolator

`W_0(T)=(exp(T)-a)/(a*(T-L))`

has value one at `L` and zero at all `L+tau*k`, `k!=0`, but it explicitly contains the selected
logarithm `L`.  Inserting it in the residue integral cancels the rational witness denominator and
leaves the nonarithmetic pole `1/(T-L)`.  Finite Fourier weights constructed from the rational
exponential witness can select congruence classes of branches, never one integer in the infinite
lattice.  Sine or Weierstrass interpolation of a single lattice point imports the lattice origin
and period; finite approximations pay growing degree or exponential type.

The mixed square system makes the same boundary leakage transparent.  Suppose conditionally that
`P(e,log 2)=0` and take

`F_1(A)=A-1,  F_2(B)=exp(B)-2,  H(A,B)=P(exp(A),B)`.

Its witness zeroes are `(1,log 2+tau*k)` and the Jacobian determinant of `(F_1,F_2)` is `2` at
each.  On the product of a small circle around `A=1` with `R_N` in the `B`-plane,

`(1/(2*pi*I)^2)*integral H(A,B) dA dB/(F_1(A)*F_2(B))
  =(1/2)*sum_(k=-N)^N P(e,log 2+tau*k)`.

Writing `P(U,V)=sum_j p_j(U)*V^j`, the right side is
`(1/2)*sum_j p_j(e)*S_j(N)`, an element of `Q[e,log 2,tau^2,N]` with no forced descent to `Q`.
The hypothetical
relation removes only the `k=0` summand.  Since `e` is transcendental, `P(e,V)` is a nonzero
polynomial and can vanish at only finitely many lattice branches; neither analytic continuation
nor the rational witness propagates the selected zero to the other summands.

This is precisely where algebraic trace arguments cease to apply.  A zero-dimensional polynomial
complete intersection over `Q` has a finite-dimensional coordinate algebra, and the sum of local
residues is a field trace controlled over `Q`.  The quotient represented by `exp(T)-a` has an
infinite zero lattice and no finite trace algebra.  Exponentiation has an essential singularity at
infinity, so compactification adds nonalgebraic boundary contributions rather than a finite
residue at infinity.  Adding `H` makes an overdetermined analytic system and may leave finitely
many common zeroes, but it does not turn the ambient exponential quotient into a finite
`Q`-algebra; its common branches need not be Galois conjugate.

Multidimensional argument principles and exponential-polynomial zero estimates therefore give
only counts or density bounds, paid for by vertical boundary length.  Weighted traces retain
`log 2` and `2*pi*I`, and a principal-branch trace requires exactly the nonarithmetic branch choice
one hoped to eliminate.  Globalizing the nonsingular witness thus reproduces the local
zero-dimensional constants obstruction: no residue, trace, or zero-counting formula turns an
alleged relation at one isolated branch into the missing ordinary transcendence inequality.

Geometric invariant theory does not furnish a compact moduli space for rational basis changes.
For `A in GL_n(Z)` there is an honest automorphism

`Phi_A(X,Y)=(A*X,Y^A),  (Y^A)_i=product_j Y_j^(a_ij)`,

and `Phi_A(z,exp(z))=(A*z,exp(A*z))`.  But the automorphism group of the algebraic torus is
discrete on its character lattice `X^*(Gm^n)=Z^n`; the monomial action does not extend to an
algebraic `GL_n(C)`-action.  If `A=B/q` is merely rational, the second coordinate requires choosing
`q`-th roots of `Y^B`, so it is a finite correspondence, not an action.  Thus there is no
reductive `GL_n`-linearization to which Hilbert--Mumford or a projective GIT quotient can be
applied.

Nor is there a fixed projective Hilbert problem for the full integral action.  General monomial
automorphisms do not extend regularly to `(P^1)^n`, and their degrees are unbounded.  More
intrinsically, no finite complete fan is invariant under all of `GL_n(Z)`: such a fan would give a
finite permutation action on its rays, while a finite-index family of unipotent shears cannot fix
the finitely many spanning rays.  Hence every fixed toric compactification sees some basis changes
only as birational maps with boundary indeterminacy.  Chow compactness at a fixed degree can add
limits of selected sequences, but those limits need not remain in the orbit, rotund, or inside the
affine exponential graph.

The mixed shear gives exact degree and height escape.  Conditionally let

`W: X_1=1,  Y_2=2,  P(Y_1,X_2)=0`

through `(1,log 2;e,2)`, and first take `A_m=[[1,0],[m,1]]`.  In transformed coordinates,

`Phi_(A_m)(W): X'_1=1,
                    Y'_2-2*(Y'_1)^m=0,
                    P(Y'_1,X'_2-m)=0`.

The marked exponential point is `(1,m+log 2;e,2*e^m)`.  In the standard compactification the
torus equation has bidegree `(m,1)`, so these cycles leave every fixed Hilbert polynomial; the
coefficient height of the translated `P` is `deg_(X_2)(P)*log m+O_P(1)`.  Exact graph
normalization survives throughout, so it supplies no boundedness.

The opposite shear `B_m=[[1,m],[0,1]]` keeps the degrees bounded but makes the Chow point run to
the boundary:

`X'_1-m*X'_2=1,  Y'_2=2,  P(2^(-m)*Y'_1,X'_2)=0`.

If `d=deg_(Y_1)P`, irreducibility and `P(e,log 2)=0` imply that the minimum `Y_1`-exponent is zero
and the maximum is `d`.  The projective coefficient height is
`m*d*log 2+O_P(log m)`.  After projective normalization, the hyperplane tends to `X'_2=0` and the
last equation tends to its `Y_1`-weight-zero part `P(0,X'_2)`.  Meanwhile the marked point
`(1+m*log 2,log 2;2^m*e,2)` goes to the additive and toric boundary.  Compactness has produced an
initial degeneration, not a bounded representative carrying the analytic normalization.

The period shear is even cleaner.  Under a hypothetical `P(log 2,2*pi*I)=0`, put

`W: Y_1=2,  Y_2=1,  P(X_1,X_2)=0`

and use `B_m`.  Then

`Phi_(B_m)(W): Y'_1=2,  Y'_2=1,
                    P(X'_1-m*X'_2,X'_2)=0`,

while the marked point is
`(log 2+m*2*pi*I,2*pi*I;2,1)`.  If
`P(U,V)=sum_(i=0)^d U^i*p_i(V)` with `p_d!=0`, its coefficient height is
`d*log m+O_P(1)`, and division by `m^d` gives the exact initial limit

`(-X'_2)^d*p_d(X'_2)`.

Since both inputs are transcendental, `P` depends on each variable and `d>=1`; the limit contains
the coordinate hyperplane `X'_2=0` with multiplicity `d`, and may have the additional factors of
`p_d`.  The exponential values remain exactly `(2,1)`
for every `m`, so even a fixed normalized torus point does not prevent the additive Chow point
from escaping.  The shear is unipotent rather than an algebraic one-parameter subgroup of the
nonexistent torus-compatible `GL_n` action, so this initial form is an orbit-closure obstruction,
not a Hilbert--Mumford invariant.

The all-dimensional counterfeit has the same degeneration while satisfying every proper
projection inequality.  For

`W=(product_i X_i=1,  Y_i=c_i)`

and `B_m=I+m*E_(1,2)`, the transformed additive equation is

`(X'_1-m*X'_2)*X'_2*product_(i>=3)X'_i=1`.

Its logarithmic coefficient height is `log m+O(1)`, and its projective initial cycle is

`(X'_2)^2*product_(i>=3)X'_i=0`,

a union of coordinate hyperplanes with multiplicity.  The constants transform as
`Y'_1=c_1*c_2^m`, `Y'_2=c_2`; for rational `|c_2|!=1` their height grows linearly in `m` and the
marked point tends to the toric boundary.  Nevertheless this `W` has the exact proper-rotund rank
function `min(r,n-1)`, and a shifted local exponential graph through its chosen point has the same
logarithmic differential normalization and intersects it only there.  Proper rotundity therefore
does not prevent boundary degeneration or supply semistability for a chosen fixed
compactification.

These calculations also dispose of a hypothetical rational invariant.  An invariant constant on
the integer orbit cannot control the displayed coefficient heights, and a compact projective
quotient records the common orbit-closure value while allowing representatives to run into the
degenerate initial cycles.  GIT quotients are not proper parameterizations of individual orbits.
Every orbit of course contains its starting finite-height representative; choosing a height
minimum merely performs arithmetic reduction and exists equally for the product counterfeit.  It
does not turn the minimum into a transcendence-degree inequality.  Likewise, a coordinate-subgroup
cycle in the orbit closure says that the chosen compactification is unstable along that sequence,
not that the original affine locus contains an algebraic subgroup.
Moreover a Hilbert or Chow point records `W`, not the transcendental assertion that its marked
point satisfies `Y=exp(X)`; after adding the point, the integer shears preserve that assertion but
send the point to the compactification boundary where exponentiation has no algebraic extension.
Thus neither semistability, invariant heights, nor orbit compactification turns analytic graph
normalization into a subgroup contradiction.  The exact obstruction is the absence of a fixed
algebraic `GL_n(Q)` action, followed by explicit noncompact integer orbits with rotund counterfeit
limits.

### Khovanskii Jacobian division has no arithmetic coefficient ring

The coefficients in local analytic division can be computed exactly, and they make the
zero-dimensional constants obstruction sharper.  Let `F=(F_1,...,F_m)` be a rational
exponential-polynomial Khovanskii witness at `c`, let `J=J_F(c)` be invertible, and let

`H(u)=R(u,exp(u))`,  `R in Q[X_1,...,X_m,Y_1,...,Y_m]`,  `H(c)=0`.

Writing `H=sum_i A_i F_i` in the analytic local ring and differentiating at `c` gives

`q=A(c)*J`,  where  `q_j=R_(X_j)(c,exp c)+exp(c_j)*R_(Y_j)(c,exp c)`.

Hence the exact adjugate formula is

`A(c)=q*J^(-1)=q*adj(J)/det(J)`.

Equivalently, `A_i(c)` is the determinant obtained by replacing row `i` of `J` by `q`, divided
by `det(J)`.  Rational coefficients of `F` and `R` put these values only in the field generated
by the selected Khovanskii point and its exponential values.  They do not put them in `Qbar`, let
alone in an algebraic-integer lattice.  This remains true below when `det(J)` is the ordinary
integer `1` or `2`.

There is also an exact formula for every higher coefficient.  Let `v=F(u)` and let `u=psi(v)` be
the local analytic inverse, with `psi(0)=c`.  For `h(v)=H(psi(v))`, one valid division is

`A_i(psi(v))=integral_0^1 (partial h/partial v_i)(t*v) dt`.

Thus, for every multi-index `alpha`,

`partial_v^alpha(A_i o psi)(0)
   =(1/(|alpha|+1))*partial_v^(alpha+e_i)h(0)`.

The inverse-function recursion expresses these jets using the jets of `F,H` and powers of
`det(J)^(-1)`, but all evaluations still lie in the same nondiscrete field.  Higher multiplicity
does not improve the coefficient field.

No algebraicity theorem for these quotients can follow merely from rationality of the
exponential polynomials.  For every `N>=1`, take

`F(T)=exp(T)-2`,  `H_N(T)=T^N*(exp(T)-2)`.

Both lie in `Z[T,exp(T)]`, and the local quotient is identically `A_N(T)=T^N`.  At the real root
`ell=log 2`,

`F'(ell)=2`,  `A_N(ell)=ell^N`.

Thus even an integral Jacobian and global, rather than merely local, ideal membership return
arbitrary powers of the selected logarithm.  At the period root `omega=2*pi*I`, the equally
integral example

`F(T)=exp(T)-1`,  `H_N(T)=T^N*(exp(T)-1)`

has `F'(omega)=1` and `A_N(omega)=omega^N`.  These examples exclude integrality, algebraicity,
bounded height, or a denominator bound for local division coefficients.

For a hypothetical independent mixed relation, the leakage occurs in the first jet.  Suppose
`P(e,ell)=0` and use

`F_1(A,B)=A-1`,  `F_2(A,B)=exp(B)-2`,  `H(A,B)=P(exp(A),B)`.

In the exact witness coordinates `v_1=F_1`, `v_2=F_2`,

`A=1+v_1`,  `B=ell+log(1+v_2/2)`,

so

`H=P(e*exp(v_1),ell+log(1+v_2/2))`.

Writing all derivatives of `P` below at `(e,ell)`, its expansion starts

`H=(e*P_U)*v_1+(P_V/2)*v_2
   +(e*P_U+e^2*P_UU)*v_1^2/2
   +(e*P_UV/2)*v_1*v_2
   +(P_VV-P_V)*v_2^2/8+O(||v||^3)`.

Thus `J=diag(1,2)`, but the division vector is exactly
`A(c)=(e*P_U(e,ell),P_V(e,ell)/2)`.  Every higher coefficient is a rational polynomial in `e`,
`ell`, and derivatives of `P` at that same point.  The determinant `2` clears only the visible
factor two; it supplies no norm on the hypothetical transcendence-degree-one field `Q(e,ell)`.

For the period stress, with `P(ell,omega)=0`, take

`F_1(A,B)=exp(A)-2`,  `F_2(A,B)=exp(B)-1`,  `H(A,B)=P(A,B)`.

Now

`A=ell+log(1+v_1/2)`,  `B=omega+log(1+v_2)`,

and, evaluating derivatives at `(ell,omega)`,

`H=(P_U/2)*v_1+P_V*v_2
   +(P_UU-P_U)*v_1^2/8
   +(P_UV/2)*v_1*v_2
   +(P_VV-P_V)*v_2^2/2+O(||v||^3)`.

Here `J=diag(2,1)` and `A(c)=(P_U/2,P_V)`.  The selected logarithm and period enter through the
evaluation of the polynomial derivatives even though the inverse-Jacobian coefficients are
rational.

Finite branch symmetrization separates the Jacobian from exactly the information one needs.  For
the roots `T_k=ell+k*omega`, `-M<=k<=M`, one has

`product_k F'(T_k)=2^(2*M+1)`,

but the quotients in the preceding integral example satisfy

`sum_k A_1(T_k)=(2*M+1)*ell`,

`product_k A_1(T_k)=ell*product_(k=1)^M(ell^2-k^2*omega^2)`.

At the period roots, symmetrizing the nonzero branches gives

`product_(k=1)^M A_1(k*omega)*A_1(-k*omega)
   =(4*pi^2)^M*(M!)^2`.

Thus the Jacobian product descends only because it forgets the logarithmic coordinates; every
weight or quotient that remembers the chosen root retains `ell` or `pi`.  These branches are not
finite algebraic conjugates, and there is no number-field norm over the infinite logarithm
lattice.  Ordinary `Aut(C/Q)` conjugation is even less compatible: from
`sigma(exp(c))=sigma(2)=2` one cannot infer `exp(sigma(c))=2`.

Consequently neither adjugates, higher jets, local Grothendieck residues, nor branch products
turn rational Khovanskii data into a nonzero integer attached to an additional relation.  The
only discrete determinants are products of witness Jacobians, which retain the exponential
outputs and erase the selected logarithms; inserting any coefficient that detects the selected
branch restores precisely the mixed or period constants whose algebraic independence is sought.

### Automorphisms and atomicity of the exponential-algebraic core

The closure core `C_E=ecl_C(Q)` has strong model-theoretic isolation but that isolation is
orthogonal to ordinary transcendence degree.  Kirby's closure theorem makes `C_E` an
`ecl`-closed exponential subfield.  It is also algebraically closed as a pure field: if `a` is
algebraic over `C_E`, its separable minimal polynomial and nonzero derivative form a one-equation
Khovanskii system, so `a in ecl_C(C_E)=C_E`.

As a pure field, `C_E` is far from algebraic over `Q`.  Choose an infinite rationally independent
family of algebraic numbers `alpha_i`, for example square roots of distinct primes.  Every
`alpha_i` and `exp(alpha_i)` lies in `C_E`, and Lindemann--Weierstrass applied to the distinct
algebraic sums `sum m_i*alpha_i` shows that the `exp(alpha_i)` are algebraically independent.
Since `C_E` is countable, it follows that

`trdeg_Q C_E=aleph_0`.

Thus, after forgetting exponentiation, `C_E` is a countable algebraically closed field of
countably infinite transcendence degree.  Its pure-field automorphism group is correspondingly
large: any two elements transcendental over `Qbar` can be interchanged after extending them to
transcendence bases.  Such automorphisms have no reason to commute with the analytic exponential.

Exponential-field automorphisms give the opposite orbit picture.  Any
`sigma in Aut(C_E,+,*,exp/Q)` satisfies

`sigma(e)=sigma(exp(1))=exp(1)=e`.

It maps the kernel of the restricted exponential bijectively to itself.  Since the complex
kernel is `omega*Z`, `omega=2*pi*I`, its restriction is an automorphism of an infinite cyclic
group, and hence

`sigma(omega) in {omega,-omega}`.

Finally `exp(log 2)=2` implies only

`sigma(log 2)=log 2+k*omega` for some `k in Z`.

It is not known from closure theory that every such branch translation extends to an
exponential-field automorphism; hidden algebraic and exponential relations can shrink the orbit.
This uncertainty cannot help with ordinary transcendence.  The element `e` already has singleton
exponential-field orbit and `omega` has orbit of size at most two, while Hermite--Lindemann proves
both are ordinarily transcendental.  Finite orbit or definable closure in the expanded language
therefore does not imply pure-field algebraicity.

Khovanskii isolation is similarly weaker than atomic isolation.  A finite tuple from `C_E` can be
included, with finitely many auxiliary variables, in a nonsingular square exponential-polynomial
system over `Q`.  The corresponding analytic zero is locally isolated, but the formula need not
have finitely many global solutions or isolate a complete exponential-field type.  The basic
formulas already show the distinction:

`e:       X-exp(1)=0` has one solution,
`log 2:   exp(X)-2=0` has the infinite set `log 2+omega*Z`,
`omega:   exp(X)-1=0` has the infinite set `omega*Z`.

All the displayed Jacobians are nonzero.  Hence `ecl` records local nonsingularity, not a finite
algebraic orbit.  Even if a stronger atomicity statement for `C_E` were available, an isolated
formula in the language containing `exp` can define a pure-transcendental element, as the term
`exp(1)` already does.

The countable-closure property alone also gives no quasiminimal homogeneity theorem for the
standard complex exponential field.  Quasiminimal excellence would control generic elements
outside closed sets; every element under discussion lies in the closed core `C_E` and has
pregeometry dimension zero.  Assuming the much stronger homogeneity or categoricity properties
of a pseudoexponential field for the actual `C_exp` would import an unproved model-theoretic
identification, and still would not identify expanded-language closure dimension with pure-field
transcendence degree.

Topological branch selection only strengthens the counterexample to that identification.  In an
enrichment with complex conjugation or the real predicate, `log 2` is the unique real solution of
`exp(X)=2`.  With modulus and an orientation, `omega` is the positively oriented nonzero kernel
element of least modulus.  These rules select the analytic branches, but selected or definable
constants can remain transcendental.  For the tuple `(1,log 2)` they leave the ordinary locus
dimension equal to `trdeg_Q Q(e,log 2)`, and for `(log 2,omega)` they leave
`trdeg_Q Q(log 2,omega)`; the desired lower bound in either case is exactly the original mixed or
period algebraic-independence problem.

There is a sharp algebraic exponential-field counterfeit showing that no argument using only
closure, isolation, or automorphism structure can supply the missing inequality.  Let
`F=Q(T)^alg` with `T` transcendental.  Choose a `Q`-basis of its additive group containing
`1,T,T^2`.  Since `F^*` is divisible, prescribed homomorphisms on those basis lines extend to a
total exponential homomorphism `E:(F,+)->(F^*,*)`.

For a mixed counterfeit prescribe

`E(1)=T,  E(T^2)=2`.

Then `(1,T^2)` is rationally independent, is contained even in `dcl_E(Q)`, and is isolated by
the nonsingular equations `X_1-1=0`, `E(X_2)-2=0`, but

`trdeg_Q Q(1,T^2,E(1),E(T^2))=trdeg_Q Q(T)=1<2`.

For the all-algebraic-exponential period pattern prescribe simultaneously

`E(1)=T,  E(T)=2,  E(T^2)=1`.

The rationally independent tuple `(T,T^2)` again lies in `dcl_E(Q)`, both exponential values are
algebraic, the witness Jacobian is `diag(2,1)`, and its total generated field is `Q(T)` of
transcendence degree one.  These total exponential fields are not proposed as models of the
analytic complex exponential; they prove that pregeometry, atomicity, finite orbit, and
Khovanskii nonsingularity contain no hidden arithmetic substitute for analyticity.

Consequently localizing a minimal counterexample to `C_E` is exact and useful, but no orbit or
branch-selection principle internal to the closure core forces its pure `Q`-locus to have
dimension at least its rational linear rank.  Such a principle would already rule out the mixed
and period counterfeits and, on the actual selected branches, would assert the missing Schanuel
inequality itself.

Holonomic packaging loses either finite rank or the selected logarithm branch.  The algebraic
exponential connection

`E^b=D_(A^1)/D_(A^1)*(partial_b-1)`

remembers the differential equation for `exp(b)`, but not the normalization of a horizontal
solution.  In particular the condition `exp(b)=2` is not a linear `D`-module condition.  If
`f=exp(b)-2`, then for the column `(1,f)` one has

`partial_b(1,f)^T=[[0,0],[2,1]]*(1,f)^T`.

The rational constant gauge `f -> f+2=exp(b)` diagonalizes this as the split connection
`O direct_sum E^b`.  Hence its characteristic cycle is twice the zero section; its
Fourier--Laplace transform is `delta_0 direct_sum delta_1` (up to the sign convention for the
Fourier coordinate), independent of `2`.  Algebraic de Rham pushforward of `E^b` to a point is
zero because the de Rham map on its polynomial realization is
`p -> p'+p`, a bijection of `C[b]` (the sign changes with the connection convention).  None of
these finite-rank objects sees the zeroes of the selected section `f`.

There is no algebraic correspondence `b -> exp(b)` to push along.  Replacing the exponential by
an algebraic torus coordinate `y` turns the witness into the rational point `y=2`, whose delta
module is finite rank but contains no logarithm.  The missing information is precisely the lift of
`2` through the analytic universal covering.

The Stokes computation is equally empty.  The split rank-two connection has formal exponential
factors `0` and `b` at infinity.  Its comparison rays satisfy `Re(b)=0`, but its Stokes matrices
are the identity because the connection is globally split.  Replacing the split basis by
`(1,exp(b)-2)` changes a chosen solution section, not the formal type or Stokes matrices.  The
zeroes `log 2+2*pi*I*k` lie along the oscillatory boundary directions; choosing a sector or a
fundamental strip to label one of them is extra analytic data and is not defined over `Q`.

One can impose the zero set only after passing to analytic differential operators.  Let
`D^an_b` be the analytic `D`-sheaf and set

`M_2=D^an_b/D^an_b*(exp(b)-2)`.

Locally at `b_k=log 2+2*pi*I*k`, the multiplier `exp(b)-2` is a unit times `b-b_k`, so `M_2` is
the delta module `delta_(b_k)` with characteristic cycle `T^*_(b_k)C`, multiplicity one.  Globally
it is a locally finite analytic sum over all `k in Z`, not an algebraic holonomic module of finite
support.  Its ordinary or proper-support pushforward to a point has respectively a product or
direct sum of one-dimensional branch contributions, and is infinite-dimensional.

Equivalently, push along the analytic covering `exp:C->C^*`.  Keeping the lifts gives the regular
representation with basis `{epsilon_k:k in Z}` of the deck group; it has infinite rank over the
point `2`.  Quotienting by the deck action first gives the finite delta module `delta_2`, but
forgets `k`.  No finite-dimensional equivariant quotient can retain one branch vector: the orbit
of `epsilon_0` under the shift contains every `epsilon_k` and is linearly independent.  More
generally, matrix coefficients of finite-dimensional monodromy satisfy a fixed linear recurrence,
whereas a nonzero Kronecker delta on the two-sided branch lattice cannot.  Finite rank and exact
branch selection are therefore incompatible.

For the mixed system the analytic module can be computed completely.  Put

`F_1=a-1,  F_2=exp(b)-2,  H=P(exp(a),b)`

and

`M_0=D^an_(a,b)/D^an_(a,b)*(F_1,F_2)`.

It has one delta summand at each `(1,log 2+2*pi*I*k)`.  Adding `H` deletes the branches where
`P(e,log 2+2*pi*I*k)!=0`; at a branch where it vanishes, `H` already lies in the analytic ideal
`(F_1,F_2)`, so the local `D`-module and its multiplicity-one characteristic cycle are unchanged.
Since `e` is transcendental, `P(e,V)` is nonzero, and the surviving set

`S_P={k in Z:P(e,log 2+2*pi*I*k)=0}`

has at most `deg_V(P)` elements.  Thus the extra relation can make the direct image finite, but
only after assuming exactly the common zero in question; the result has rank `|S_P|`, and its
determinant is merely the determinant line of a finite set.  Microlocally at the selected branch
the characteristic cycle is just `T^*_(1,log 2)C^2`, exactly the same cycle with or without `H`.
It records deletion/counting, not the value or arithmetic nature of the relation.

The appearance of `e` has also not become algebraic.  Restricting the connection `E^a` to the
algebraic delta module at `a=1` gives a one-dimensional de Rham fiber, while the value `exp(1)=e`
belongs to its Betti--de Rham comparison normalization.  Encoding the polynomial
`P(exp(a),b)` by symmetric powers of exponential connections retains those comparison periods.
A determinant theorem making them algebraically independent from `log 2` would be a period
conjecture at least as strong as the mixed target.

For the period system set

`N_0=D^an_(a,b)/D^an_(a,b)*(exp(a)-2,exp(b)-1)`.

Its support is the full lattice
`(log 2+2*pi*I*j,2*pi*I*k)`, `(j,k) in Z^2`, with one cotangent-fiber cycle at each point.  The
direct image to a point is infinite rank, while descent under the two deck shifts gives the
single delta module at `(2,1)` and forgets both branch labels.  If a hypothetical
`P(log 2,2*pi*I)=0` is imposed, then at the selected lattice point `(j,k)=(0,1)` the polynomial
`P(a,b)` is locally redundant because the witness Jacobian is `diag(2,1)`.  The characteristic
cycle there remains one reduced cotangent fiber.  Globally the surviving lattice subset

`{(j,k):P(log 2+2*pi*I*j,2*pi*I*k)=0}`

need not be finite; finiteness would itself require arithmetic information about the polynomial on
the period lattice.  Even if it is finite, pushforward remembers only its cardinality and a
determinant line, not the distinguished point `(0,1)`.

Thus every direct-image construction faces an exact trilemma.  The algebraic exponential
connection is finite rank but forgets the equation `exp(b)=2`; the analytic delta module remembers
all its zeroes but has infinite-rank pushforward; imposing the extra polynomial may cut to finite
rank, but then its characteristic cycle sees only unit delta multiplicities and has already
assumed the alleged relation.  Fourier--Laplace support, monodromy, Stokes matrices, and
determinants contain no branch arithmetic.  A sector or branch choice that singles out `log 2` or
`2*pi*I` is precisely the nonalgebraic normalization the proposed holonomic package was meant to
derive.

### Deforming the holomorphic character does not control the special fiber

There is a clean positive functional statement for the deformation
`E_a(z)=exp(a*z)`, but its arithmetic specialization is maximally false.  Let
`z_1,...,z_n` be rationally independent constants and regard `a` as a complex variable.  In the
differential field of meromorphic functions of `a`, put

`x_i=a*z_i`,  `y_i=exp(a*z_i)`.

The `x_i` are rationally independent modulo constants and their derivative matrix has rank one.
Ax--Schanuel therefore gives

`td_C C(a,y_1,...,y_n)>=n+1`.

The reverse inequality is the generator count, so the `exp(a*z_i)` are algebraically independent
over `C(a)`.  This is the strongest possible generic-fiber conclusion.  It gives no information
after evaluating `a`: algebraic independence of meromorphic functions is not preserved by an
evaluation homomorphism.

The fixed-input stresses attain the failure exactly.  For `(1,ell)`, with `ell=log 2`, the two
functions

`E_a(1)=exp(a)`,  `E_a(ell)=2^a`

are algebraically independent over `C(a)`, while at `a=1` they specialize to `(e,2)`.  The
functional constant field already contains `ell`, so Ax's estimate never measures its ordinary
transcendence relative to `e`.  For `(ell,omega)`, `omega=2*pi*I`, the functions

`2^a,  exp(omega*a)`

are likewise algebraically independent over `C(a)`, but their value at `a=1` is the completely
algebraic pair `(2,1)`.  Thus generic functional independence can lose every exponential
contribution at the desired fiber.

Nonsingular Khovanskii witnesses deform smoothly but do not repair this loss.  The mixed witness

`F(a,B)=exp(a*B)-2`

has the principal branch

`B=c_a=ell/a`,  `partial F/partial B=2*a`,

for `a` near one.  The mixed tuple `(1,c_a)` has `E_a`-values `(exp(a),2)`.  Under a hypothetical
relation `P(e,ell)=0`, the transported defect is the one-variable analytic function

`H(a)=P(exp(a),ell/a)`,  `H(1)=0`,

with exact first derivative

`H'(1)=e*P_U(e,ell)-ell*P_V(e,ell)`.

If this derivative vanishes, only the order of the isolated zero increases.  The function cannot
vanish identically for nonzero `P`: that would make `exp(a)` algebraic over `C(a)` after
substituting `ell/a`, contradicting the one-function case of the functional statement.  Hence
deformation turns the hypothetical relation into one finite-order zero at `a=1`, not a functional
identity.  Requiring the first output to remain exactly `e` leaves only

`exp(a)=e`,  that is  `a=1+2*pi*I*k`,

a discrete set with no generic parameter.

For the period stress, keeping both algebraic outputs gives the moving branches

`c_a=ell/a`,  `d_a=omega/a`,

with witness equations

`exp(a*c_a)-2=0`,  `exp(a*d_a)-1=0`

and input Jacobian determinant `2*a^2`.  The relevant standard exponential arguments are
`a*c_a=ell` and `a*d_a=omega`, both constant, so the Ax derivative rank is zero.  A hypothetical
ordinary relation contributes

`P(c_a,d_a)=P(ell/a,omega/a)`.

It may have only an isolated zero at one; if `P` is homogeneous it can persist identically, but
then it merely transports the assumed relation along scalar dilation.  In either case the total
function field is

`Q(a,ell,omega)`.

Under the defect-one hypothesis `td_Q Q(ell,omega)=1`, its generic transcendence degree is two
only because of the new parameter `a`, while the fiber at `a=1` still has degree one.  Keeping the
inputs fixed and both outputs `(2,1)` is even more rigid:
`exp(a*omega)=1` forces `a in Z`, and `exp(a*ell)=2` then forces `a=1`.

This is not a violation of algebraic semicontinuity.  The Zariski closure over `C` of

`a mapsto (a,exp(a*z_1),...,exp(a*z_n))`

is the full `A^1 x G_m^n` by the functional independence just proved; its fiber at `a=1` is the
full torus, not the selected analytic value.  Retaining the selected value requires the
transcendental analytic section, whose evaluation can land on an arbitrarily special point.
Likewise the total zero set of a deformed nonsingular Khovanskii system is a smooth analytic curve
with a reduced point in each nearby fiber, but its algebraic closure forgets the exponential
normalization.

Consequently holomorphic-character deformation offers an exact dichotomy.  Fixed inputs give
maximal generic Ax--Schanuel transcendence but allow complete collapse at `a=1`; moving branches
preserve the algebraic exponential outputs only by freezing the standard exponential arguments,
so their functional rank is zero and the parameter supplies the missing generic dimension.  No
generic-fiber or specialization theorem transfers that artificial parameter contribution to the
ordinary transcendence degree of the defect-one `C_E` fiber.

### Finite complementary correspondences do not preserve the exponential graph

The strengthened minimal-counterexample structure does produce genuine finite algebraic
correspondences.  Let `z=(z_1,...,z_n)` be a counterexample of least arity, let
`y_i=exp(z_i)`, and suppose its full field `K=Q(z,y)` has the forced transcendence degree `n-1`.
For every `i`, the deleted tuple is still rationally independent, so minimality and field
inclusion give

`td_Q K_hat_i=n-1=td_Q K`,

where `K_hat_i=Q(z_j,y_j:j!=i)`.  Consequently `K/K_hat_i` is finite: both omitted elements
`z_i,y_i` are algebraic over the complementary field.  Geometrically, the `(n-1)`-dimensional
`Q`-locus `W=Loc_Q(z,y)` maps generically finitely to every complementary projection.

This conclusion is sharp but purely algebraic.  A conjugate of the omitted pair over
`K_hat_i` remains on `W`, but a pure-field embedding satisfies neither

`sigma(exp(z_i))=exp(sigma(z_i))`

nor the corresponding equations for the fixed coordinates.  Thus monodromy supplies a finite
fiber of algebraic pairs, with only the selected pair known to lie on the analytic exponential
graph.

The mixed stress makes the mismatch exact.  Conditional on `td_Q Q(e,ell)=1`, choose an
irreducible relation `P(e,ell)=0`.  The full locus of `(1,ell;e,2)` is the curve

`X_1=1,  Y_2=2,  P(Y_1,X_2)=0`.

Its normalization gives finite maps to the `E=Y_1` and `L=X_2` lines, with degrees at most
`deg_L P` and `deg_E P`.  Over `Q(e)`, the conjugates of `ell` are roots `L_j` of `P(e,L)`.
Although a field embedding sends the equality `exp(ell)=2`, viewed merely as the field equality
`2=2`, to itself, it gives no analytic equality `exp(L_j)=2`; that would additionally require
`L_j=ell+k*2*pi*I`.  In the opposite projection, a conjugate `E_j` of `e` over `Q(ell)` need not
equal the fixed analytic value `exp(1)=e`.  Since both `e` and `ell` are real, complex
conjugation fixes the original point and creates no second branch.

Hence the actual graph points in a fiber over `E=e` are only

`(E,L)=(e,ell+k*2*pi*I)` with `P(e,ell+k*2*pi*I)=0`.

There are at most `deg_L P` of them, and only `k=0` is forced.  Algebraic monodromy permutes all
roots of `P(e,L)`; it does not force any additional root into this logarithm lattice.

The period stress has one, and only one, automatic compatible symmetry.  Under a hypothetical
relation `P(ell,omega)=0`, the locus of `(ell,omega;2,1)` is

`Y_1=2,  Y_2=1,  P(X_1,X_2)=0`.

Pure algebraic conjugates of either input again need not remain logarithms of `(2,1)`.  However
ordinary complex conjugation commutes with the analytic exponential and gives the second graph
point `(ell,-omega;2,1)`.  Applying it again returns the original point.  Accordingly
`P(ell,V)` already has the two roots `+/-omega` and degree at least two in that fiber; the two
zeros exactly consume the available conjugation symmetry and do not force `P` to vanish
identically.  Further monodromy branches have no exponential compatibility.

Alternating the complementary correspondences does not improve this.  If their generic degrees
are bounded by `D`, the `r`-fold fiber product has degree at most `D^r`; eliminating its internal
coordinates produces resultants of the same multiplicative degree scale.  The number of
algebraic branch paths can therefore grow exponentially, but the number of paths known to remain
on the exponential graph stays one (or the conjugate pair in the period case).  Imposing the
graph equations branch by branch either discards almost every path or creates a moving
exponential polynomial whose degree grows at the same rate as the path count.  No fixed-format
zero theorem is overloaded.

An exact exponential-field counterfeit shows that all projection ranks and finite degrees can
hold while every nontrivial monodromy branch leaves the graph.  Let `T` be transcendental in an
algebraically closed field and fix `d>=2`.  Extend prescribed values on an additive rational
basis to a total exponential homomorphism.

For the mixed pattern prescribe

`E(1)=T,  E(T^d)=2`.

The tuple `(1,T^d;T,2)` lies on the rational curve

`X_1=1,  Y_2=2,  X_2=Y_1^d`.

Its full field and both deleted-coordinate fields have transcendence degree one.  Projection to
`X_2` has degree `d`, with monodromy branches `Y_1=zeta_d^j*T`; only `j=0` equals the required
graph value `E(1)=T`.  All other branches satisfy the algebraic correspondence and fail the
graph equation.

For the all-algebraic-exponential period pattern prescribe

`E(T)=2,  E(T^d)=1`.

Then `(T,T^d;2,1)` has the same full/deleted transcendence degrees and lies on
`X_2=X_1^d`, `Y_1=2`, `Y_2=1`.  Its `d` algebraic branches over `X_2` are
`zeta_d^j*T`, but the homomorphism law controls only rational multiples, not multiplication by
algebraic roots of unity; no branch other than the prescribed one is forced to have exponential
value `2`.  These models retain the exact finite-correspondence and monodromy data of a minimal
defect-one locus while having only one graph-compatible branch.

There is therefore a rigorous positive algebraic lemma--every complementary projection of a
minimal counterexample is generically finite--but it has no analytic propagation content.
Turning its conjugates into new exponential zeros would require field embeddings to commute with
the complex exponential, which fails in the mixed fiber and holds only for the order-two complex
conjugation symmetry in the period fiber.  Iteration pays degree at exactly the rate it creates
off-graph branches.

### Deletion algebraicity gives no-coloops, not constant logarithmic relations

The algebraic-over-every-deletion property gives a precise no-coloop lemma, but no constant
logarithmic relation.  Let

`K=Q(x_1,...,x_n,y_1,...,y_n)`,  `trdeg_Q K=n-1`,

and let `K_i` be the field generated by all pairs except `(x_i,y_i)`.  If `K/K_i` is algebraic
for every `i`, characteristic zero gives

`K tensor_(K_i) Omega_(K_i/Q) -> Omega_(K/Q) -> 0`.

Thus `dx_i` and `dy_i` are in the `K`-span of the other coordinate differentials.  After passing
to universal exponential differentials `omega_i=d_E x_i`, where `d_E y_i=y_i*omega_i`, one gets

`omega_i in span_C{omega_j:j!=i}`.

So the `E`-differential matroid has no coloop.  This is the whole formal consequence: it neither
raises its rank `rho` nor improves the previous bound `2*rho<=n-1`.

The recovery coefficients are intrinsically rational functions.  If a separable recovery
equation is written `R_i(x_i;other coordinates)=0`, then

`dx_i=-(sum_(j!=i) R_(X_j)*dx_j+R_(Y_j)*dy_j)/R_(X_i)`,

and similarly for `dy_i`.  The inverse separant and the Jacobian cofactors lie in `K`, not in the
constant field.  Different deletions can be different orientations of the same algebraic-matroid
circuit, so the resulting rows need not be independent.

This remains true for the logarithmic forms

`theta_i=dy_i/y_i-dx_i`.

Choose a `K`-basis of `Omega_(K/Q)` and put the columns of the `theta_i` in an `(n-1) by n`
matrix `M`.  If they have maximal rank, their unique relation is the cofactor vector

`a_i=(-1)^(i-1)*det(M with column i deleted)`.

Nothing in deletion algebraicity makes the projective vector `[a_1:...:a_n]` constant.  A
constant rational vector `q` would give

`dlog(Y^q)=d(q dot X)`.

After clearing denominators and passing to a smooth projective model, residues force `Y^q` to be
constant and then `q dot X` to be constant.  Hence such a vector is exactly a forbidden
zero-dimensional rational row projection, already excluded by proper rotundity; the recovery
equations supply no descent from `K` to `Q`.

The mixed conditional curve shows that its two recoveries are the same circuit.  If irreducible
`P(U,V) in Q[U,V]` satisfies `P(e,log 2)=0`, then for

`(x_1,y_1;x_2,y_2)=(1,e;log 2,2)`

each pair is algebraic over the other and `Omega_(K/Q)` has dimension one.  On the normalization
of `P(U,V)=0`,

`theta_1=dU/U,  theta_2=-dV`,

and the exact relation is

`U*P_U*theta_1-P_V*theta_2=0`.

Its coefficient ratio is not rational constant.  Indeed a relation
`q_1*dlog(U)-q_2*dV=0` with `q_1!=0` would, by residues, force the nonconstant function `U` to be
constant; if `q_1=0`, then `q_2!=0` would force the nonconstant `V` to be constant.  The two forms span the
one-dimensional cotangent space, so the quotient by the exponential equations is zero: there is
no nonzero restricted exponential derivation despite algebraic recovery from both deletions.

For the period stress, conditionally `P(log 2,2*pi*I)=0`, one has

`theta_1=-dU,  theta_2=-dV,  P_U*theta_1+P_V*theta_2=0`.

Again both deleted fields equal the full transcendence-degree-one field up to algebraic extension.
A rational constant relation would make `q_1*log 2+q_2*2*pi*I` algebraic.  Its exponential is
algebraic, so Hermite--Lindemann forces the linear form to be zero, and rational independence then
forces `q_1=q_2=0`.  Thus the recovery cofactors vary here as well, and the `theta_i` again span
the cotangent line.

There is an all-dimensional function-field counterfeit satisfying every deletion exactly.  Let

`F=Qbar(x_1,...,x_(n-1))`,  `x_n=(product_(i<n)x_i)^(-1)`,  `y_i=p_i`,

where the `p_i` are distinct rational primes.  Then `trdeg F=n-1`, and deleting any pair still
generates `F`: the missing `x_i` is the reciprocal product of the others and `y_i` is algebraic.
The recovery polynomial for every `i` is just the same circuit `product_j X_j-1`; its
differential gives

`sum_i dx_i/x_i=0`,  equivalently  `sum_i (1/x_i)*theta_i=0`,

because `theta_i=-dx_i`.  This relation is unique and its cofactor vector
`[1/x_1:...:1/x_n]` is nonconstant.  No nonzero rational constant relation exists: the Laurent
monomials `x_1,...,x_(n-1),(product_(i<n)x_i)^(-1),1` are distinct, so
`d(sum q_i*x_i)=0` forces every `q_i=0`.

It is also an exact partial-exponential counterfeit.  On the rational span of the `x_i`, choose
compatible roots of the primes and define

`E(sum_i r_i*x_i)=product_i p_i^(r_i),  r_i in Q`.

The `x_i` are rationally independent and prime valuations make this homomorphism injective, while
`E(x_i)=y_i` and the generated field still has transcendence degree `n-1`.  Every exponential
derivation kills the tuple, since `0=D(p_i)=p_i*D(x_i)`; hence `rho=0`.  The model has all
deletion, Jacobian-cofactor, proper-projection, and abstract exponential-homomorphism data, but not
the standard analytic normalization.  Excluding it requires exactly that missing analytic input,
not another use of algebraic recovery or Kahler differentials.

All rational shears of the exponential graph have an exact linear normal form, so they cannot
amplify local intersection multiplicity.  At a graph point `p=(z,y)` choose local logarithms of
the `Y_i` with `log(y_i)=z_i` and put

`s_i=X_i-log(Y_i),  u_i=exp(X_i)/Y_i=exp(s_i)`.

For `q in Z^n`, with Laurent monomials allowed because every `Y_i` is a unit,

`G_q=exp(q dot X)-Y^q=Y^q*(exp(q dot s)-1)`.

Since `(exp(w)-1)/w` is an analytic unit at `w=0`, one has the exact equality of principal local
ideals

`(G_q)=(q dot s)`.

Consequently a family `Q subset Z^n` generates the same ideal as the ordinary linear forms
`{q dot s:q in Q}`.  If their rational span has rank `r`, any `r` independent rows already give a
reduced codimension-`r` normal ideal; adding further shears produces no multiplicity.

The same fact can be written without logarithms as explicit membership in the base graph ideal.
Let `G_i=exp(X_i)-Y_i` and for an integer `m` define the Laurent polynomial

`S_m(U)=(U^m-1)/(U-1)`,  `S_m(1)=m`.

Ordered telescoping gives

`G_q=sum_i C_(q,i)*G_i`,

`C_(q,i)=Y^q*(product_(j<i)u_j^(q_j))*S_(q_i)(u_i)/Y_i`.

In particular

`G_q congruent Y^q*sum_i q_i*G_i/Y_i  mod (G_1,...,G_n)^2`.

For rows `q^(1),...,q^(n)` forming a matrix `Q`, the coefficient matrix at `p` has determinant

`det(C(p))=(product_a y^(q^(a)))*(det Q)/(product_i y_i)`.

Thus if `det Q!=0` it is an analytic unit and

`(G_(q^(1)),...,G_(q^(n)))=(G_1,...,G_n)`

locally.  In particular every integral basis change preserves the complete graph ideal and every
isolated intersection length with an algebraic locus `W`.

Jets give no hidden gain.  The complete expansion is

`G_q/Y^q=sum_(k>=1) (q dot s)^k/k!`.

After restriction to `W`, its order is exactly the order of `(q dot s)|_W`.  For a positive
integer `m`, one also has

`G_(m*q)=G_q*sum_(r=0)^(m-1) exp((m-1-r)*q dot X)*(Y^q)^r`,

and the second factor has value `m*y^((m-1)*q)` at `p`, hence is a unit.  Therefore
`ord_p(G_(m*q)|_W)=ord_p(G_q|_W)` and the two principal local ideals agree.  Scaling a shear raises
its Laurent degree and exponential type linearly while producing zero order gain.

More generally, write the Taylor series on a local parametrization of `W` as

`s_i(t)=sum_alpha c_(i,alpha)*t^alpha`.

The condition `ord_p(q dot s)>=nu` is the collection of linear equations
`sum_i q_i*c_(i,alpha)=0` for `|alpha|<nu`.  Higher contact comes only from a fixed rational vector
lying in nested jet kernels; using many different vectors does not add their orders.  If
`q dot s` vanished identically on an irreducible algebraic `W`, then `exp(q dot X)=Y^q` would hold
on a germ and hence on the analytic normalization, giving the forbidden rational subgroup
projection.  Otherwise every order is finite, but no shear-counting argument makes it large at
fixed coefficient cost.  A product of shear equations adds vanishing orders only while adding
their degrees and types by the same sum, and there are only finitely many integer vectors of
bounded height.

The mixed conditional curve is completely transverse as an ideal even if one shear is tangent.
Assume `P(e,log 2)=0` and use coordinates

`W: X_1=1,  Y_2=2,  P(Y_1,X_2)=0`.

Write `S=Y_1`, `T=X_2`, `L=log 2`.  For `q=(q_1,q_2)`,

`G_q=exp(q_1+q_2*T)-S^(q_1)*2^(q_2)`,

and its logarithmic normal form on `W` is

`q_1*(1-log S)+q_2*(T-L)`.

At the selected point, first-order tangency is exactly

`q_1*P_T(e,L)+q_2*e*P_S(e,L)=0`.

This can occur for an integer `q` only if the projective Gauss ratio
`[e*P_S(e,L):-P_T(e,L)]` is rational at that point; neither deletion algebraicity nor the
hypothetical relation forces it.  Even if it occurs, every multiple has the same order.  The two
base restrictions `exp(1)-S` and `exp(T)-2` generate `(S-e,T-L)` on the smooth curve, hence the
local graph intersection has length one; any two independent shear rows generate that same ideal.

For the period curve

`W: Y_1=2,  Y_2=1,  P(X_1,X_2)=0`

at `(L,2*pi*I;2,1)`, the exact shear equation is

`G_q=exp(q_1*X_1+q_2*X_2)-2^(q_1)`

and its logarithmic normal form is

`q_1*(X_1-L)+q_2*(X_2-2*pi*I)`.

It is tangent to the curve exactly when
`[q_1:q_2]=[P_(X_1)(L,2*pi*I):P_(X_2)(L,2*pi*I)]` projectively.  Again rationality of this Gauss
value is not forced.  The base functions `exp(X_1)-2` and `exp(X_2)-1` generate the maximal ideal
`(X_1-L,X_2-2*pi*I)` on the smooth curve, so the complete local intersection length is one and
all full-rank shear systems reproduce it.

Rational rows do not help.  If `q=a/d in Q^n`, pass to the local Kummer cover with the branch of
`Y^q` normalized by `Y^q(p)=exp(q dot z)`.  Then

`G_a=G_q*sum_(r=0)^(d-1) exp((d-1-r)*q dot X)*(Y^q)^r`,

whose second factor is the unit `d*y^((d-1)*q)` at `p`.  Thus clearing denominators gives exactly
the same ideal and order, while the cover/degree cost grows with `d`.  Other Kummer branches
multiply `Y^q` by a nontrivial root of unity and make the alleged shear equation nonzero at `p`;
only the externally normalized branch participates.

Hence all integer and rational shears merely change generators of the same local graph ideal.
Their first jets transform by the rational row matrix times analytic units, their higher jets are
powers of the same linear logarithmic forms, and Kummer denominators add cost without contact.
No number of shears can create a fixed-complexity high-multiplicity zero or a new zero-estimate
contradiction at a defect-one/Khovanskii point.

### Rational-direction maps have bounded degree but unbounded complexity

There is a useful exact degree statement in arity two, but it does not contradict a defect-one
counterexample.  Put

`K=Q(z_1,z_2,y_1,y_2)`,  `y_i=exp(z_i)`,  `trdeg_Q K=1`,

and, for a primitive integer row `r=(a,b)`, put

`u_r=a*z_1+b*z_2`,  `v_r=y_1^a*y_2^b=exp(u_r)`,  `F_r=Q(u_r,v_r)`.

Rational independence makes `u_r` nonzero.  The one-variable case of Schanuel
(Hermite--Lindemann) gives `trdeg_Q F_r>=1`, hence `K/F_r` is finite for every `r`.
After replacing the algebraic constant field of `K` by a number field `k`, let `C/k` be the
smooth projective curve with function field `K` and let

`D_X=max((z_1)_infinity,(z_2)_infinity)`

pointwise.  Whenever `u_r` is nonconstant,

`[K:k(u_r,v_r)] <= [K:k(u_r)] = deg(u_r) <= deg(D_X)`.

The rational directions for which `u_r` is constant form a rational linear subspace of
`Q^2`.  Unless both `z_1,z_2` are constant functions, this gives at most one primitive direction
up to sign.  Adding its one finite degree shows that the whole spectrum `[K:F_r]` is uniformly
bounded.  Thus uniform degree is not a hoped-for extra consequence: it is automatic from the
fixed three-dimensional linear system spanned by `1,z_1,z_2`.  If both inputs are constant
functions, no uniform bound follows; then all the variation can occur in the monomials `v_r`.

Neither gonality nor Castelnuovo--Severi turns this into a contradiction.  Two rows forming a
matrix in `GL_2(Z)` recover both additive coordinates and both multiplicative coordinates from
their two direction pairs, so their fields have compositum `K`.  Castelnuovo--Severi gives only

`g(K) <= d_r*g(F_r)+d_s*g(F_s)+(d_r-1)*(d_s-1)`,

where `d_r=[K:F_r]`.  This is an upper bound on the already fixed genus.  In the period boundary,
where every `F_r` is rational, it reduces to `g(C)<=(d_r-1)(d_s-1)`, the usual bound for two
maps to `P^1`.  Infinitely many members of one bounded-degree linear system are entirely normal.

The missing finiteness is arithmetic height.  Geometrically

`deg(v_r)=deg((a*div(y_1)+b*div(y_2))_+)`

is at most linear in `|a|+|b|` and is generally unbounded.  The coefficients of `u_r` have height
`log max(|a|,|b|)+O(1)`, while the monomial presentation of `v_r` has height linear in
`|a|+|b|` (already the constant `2^a` has height `|a|*log 2`).  Consequently Northcott and
Arakelov finiteness never see a family of simultaneously bounded degree and height.  Changing the
model or polarization merely redistributes these terms; it does not bound them.

The mixed stress makes the spectrum explicit.  Conditionally let `P(E,L)=0` be the irreducible
curve through `(e,log 2)`, so

`(z_1,z_2;y_1,y_2)=(1,L;E,2)`.

For primitive `(a,b)`, if `b!=0` then

`F_(a,b)=Q(L,E^a)` for `a!=0`, and `F_(0,+/-1)=Q(L)`;

if `b=0`, then `a=+/-1` and `F_(a,0)=Q(E)`.  Hence every directional degree is bounded by the
larger of the two projection degrees `[K:Q(E)]` and `[K:Q(L)]`.  The infinitely many powers
`E^a` increase presentation/divisor height but not the extension degree over `Q(L)`.

For the period stress, conditionally `P(U,V)=0` through `(log 2,2*pi*I)`, one has

`(z_1,z_2;y_1,y_2)=(U,V;2,1)`,  `F_(a,b)=Q(a*U+b*V)`.

All maps are simply the rational functions in the fixed linear system
`span{1,U,V}` and have degree at most
`deg(max((U)_infinity,(V)_infinity))`.  Their selected values still satisfy
`exp(a*log 2+b*2*pi*I)=2^a`, but the constants `2^a` have unbounded arithmetic height.  The two
coordinate projections give only the standard genus bound associated to the bidegrees of `P`.

Exact abstract exponential countermodels show sharpness.  Let `T` be transcendental in an
algebraically closed characteristic-zero field, fix `d>=2`, prescribe an exponential homomorphism
on the indicated rational span using coherent roots, and extend it to the additive group.
For the mixed pattern prescribe

`E(1)=T`,  `E(T^d)=2`.

Then `K=Q(T)` for the tuple `(1,T^d;T,2)`, and its primitive-direction degrees are exactly

`d_(a,b)=1` if `b=0`, and `d_(a,b)=gcd(d,|a|)` if `a*b!=0`,

while `d_(0,+/-1)=d`.  Indeed `Q(u_r,v_r)=Q(T^d,T^a)=Q(T^g)` in the middle case.  Thus the
whole spectrum is uniformly bounded by `d` and every selected exponential identity holds.

For the period pattern prescribe

`E(T)=2`,  `E(T^d)=1`.

The tuple `(T,T^d;2,1)` again has `K=Q(T)`, and

`d_(a,b)=1` for `b=0`,  `d_(a,b)=d` for `b!=0`,

because `a*T+b*T^d` has polynomial degree `d` in the latter case.  This genus-zero model realizes
the uniform degree, gonality, common-pole, and selected-value data with no contradiction.

Finally, the all-algebraic-input model shows that even uniform degree is not formal.  Prescribe

`E(1)=T`,  `E(sqrt(2))=T+1`.

For `(z_1,z_2;y_1,y_2)=(1,sqrt(2);T,T+1)`, the full field and both deleted fields have
transcendence degree one, but over the constant field

`[k(T):k(T^a*(T+1)^b)]`
` = max(a,0)+max(b,0)+max(-a-b,0)`
` = (|a|+|b|+|a+b|)/2`.

This is unbounded even on primitive rows, for example `(a,b)=(m,1)`.  It is exactly the degree of
the divisor
`a*[0]+b*[-1]-(a+b)*[infinity]`.

At the distinguished complex point all direction equations vanish, but they are different
equations at the same point, not many zeros of a fixed exponential polynomial.  Locally, after
choosing logarithms, write `g_i=log(y_i)-z_i`; then the directional discrepancy is
`a*g_1+b*g_2`, and all these functions vanish at the point merely because `g_1=g_2=0` there.
This creates neither extra multiplicity nor an identity on `C`.  A zero theorem would require
uniform global format/height or many distinct zeros of one function, and the exact spectra above
show that neither is supplied by the strengthened deletion property.

Invariant algebraic ideals under graph vector fields admit a complete classification, and it shows
that stability is far stronger than pointwise graph membership.  Work over a characteristic-zero
field `k` in

`R=k[X_1,...,X_n,Y_1^(+-1),...,Y_n^(+-1)]`

with commuting derivations

`Delta_i=partial_(X_i)+Y_i*partial_(Y_i)`.

For a primitive `q in Z^n`, put `Delta_q=sum_i q_i*Delta_i`.  Choose `A in GL_n(Z)` with
`A*q=e_1` and make the monomial-linear coordinate change

`X'=A*X,  Y'=Y^A`.

Then `Delta_q=partial_(X'_1)+Y'_1*partial_(Y'_1)` and it kills every other transformed
coordinate.  If

`R=R_0[X'_1,(Y'_1)^(+-1)]`,
`R_0=k[X'_2,...,X'_n,(Y'_2)^(+-1),...,(Y'_n)^(+-1)]`,

the exact classification is

`I is Delta_q-stable  iff  I=(I intersection R_0)*R`.

To prove it, expand `f in I` as `sum_m p_m(X'_1)*(Y'_1)^m`.  On the finite-dimensional space
containing its terms, `Delta_q` has distinct generalized eigenvalues `m`; polynomial spectral
projectors in `Delta_q` isolate each `p_m*(Y'_1)^m`.  Repeated application of
`Delta_q-m=partial_(X'_1)` extracts its leading coefficient in `R_0`.  Subtraction and induction
extract every coefficient, proving the formula.  Hence a height-one stable prime is pulled back
from an irreducible equation in the complementary invariants, and its variety is a cylinder along
the full analytic exponential `q`-leaf.  No proper finite-colength (equivalently, zero-dimensional)
ideal is stable under even one nonzero `Delta_q`.

Applying the same extraction in all coordinates proves differential simplicity:

`I stable under every Delta_i  implies  I=0 or I=R`.

Indeed multivariate spectral projection first isolates a Laurent monomial `p(X)*Y^m`, and the
operators `Delta_i-m_i` reduce to the partial derivatives of `p`; a derivative of a top-total-degree
monomial yields a nonzero constant times the unit `Y^m`.  Thus there are no nonzero proper
fully stable primes, in height one or any other height.  Geometrically, a full stable variety would
contain the `n`-dimensional analytic leaf

`t -> (X+t,Y*exp(t))`,

whose Zariski closure is the whole `Ga^n times Gm^n`; the algebraic proof above is the exact
finite-support version of that density statement.

The mixed stress fails stability in the strongest possible way.  Conditionally write

`I_W=(X_1-1,Y_2-2,P(Y_1,X_2))`.

Then

`Delta_1(X_1-1)=1,  Delta_2(Y_2-2)=Y_2 congruent 2 mod I_W`,

so `I_W` is not stable.  Even the circuit equation alone has

`Delta_1 P=Y_1*P_(Y_1),  Delta_2 P=P_(X_2)`.

For irreducible `P` depending on both variables, it cannot divide either lower-degree derivative.
At the selected point `P(e,log 2)=0` says nothing about the two displayed derivatives; at a smooth
point they are not both zero.  The arithmetic-differential contradiction from assuming stability
therefore audits an assumption that evaluation does not provide.

For the period stress,

`I_W=(Y_1-2,Y_2-1,P(X_1,X_2))`,

and already `Delta_1(Y_1-2) congruent 2`, `Delta_2(Y_2-1) congruent 1`.  On the remaining circuit,
`Delta_i P=P_(X_i)`, again excluding stability for a nonconstant irreducible `P`.  The same
calculation holds whether or not the hypothetical value `P(log 2,2*pi*I)` vanishes.

Khovanskii isolation is actually incompatible with stability.  For a square exponential-polynomial
system `F=(F_1,...,F_m)` at an isolated root `c`, formal application of the graph derivations gives
the exponential Jacobian entries

`Delta_j F_i(c)=(J_F(c))_(i,j)`.

If the relation ideal were stable, every entry would vanish at `c`, contradicting
`det J_F(c)!=0`.  In ordinary local coordinates the same fact is immediate: the maximal ideal of
an isolated point contains `X_j-c_j`, while `Delta_j(X_j-c_j)=1`.  Isolation supplies transversality
to the graph distribution, not invariance under it.

Algebraicity over every deletion also supplies no stability.  Its differentiated recovery
equations express coordinate differentials using rational-function cofactors, whereas stability
would require `Delta_i R in I_W` for every relation `R` and every `i`.  At a smooth point this
would place all `n` independent vectors `Delta_i`, whose `X`-components are the standard basis,
inside `T W`; a defect-one locus has dimension only `n-1`.  Thus full stability is pointwise
dimensionally impossible before any arithmetic argument is used.

Discrete branches do not repair the gap.  Translation by a period acts as

`X_i -> X_i+2*pi*I*k,  Y_i -> Y_i`.

Its infinitesimal Zariski closure is additive translation `partial_(X_i)`, not
`Delta_i=partial_(X_i)+Y_i*partial_(Y_i)`.  For `exp(T)-2`, the full branch lattice is Zariski
dense in the additive `T`-line and its algebraic closure forgets the logarithm equation.  In the
mixed circuit, the nonzero polynomial `P(e,T)` meets only finitely many branches, so there is not
even discrete invariance.  Closing the full analytic graph leaf instead gives the whole ambient
space and the zero ideal, the only proper fully stable prime.

The all-dimensional deletion counterfeit makes the failure concrete.  For

`W=(product_i X_i=1,Y_i=c_i)`,

`Delta_i(product_j X_j-1)=product_(j!=i)X_j congruent 1/X_i mod I_W`,

and `Delta_i(Y_i-c_i)=Y_i congruent c_i`; neither is zero.  Nevertheless this locus has every
proper projection inequality, algebraic recovery from every deletion, and the variable cofactor
relation `sum_i X_i^(-1)*theta_i=0`.  Hence pointwise graph membership, deletion algebraicity,
Khovanskii isolation, branch
translation, and Zariski closure all fail to descend to `Delta`-stability.  Any argument using a
stable relation ideal has already promoted one graph intersection point to an entire Zariski-dense
exponential leaf, which is precisely the unjustified step.

### Exponential theorems force one new value outside the countertuple field

Four/Six Exponentials do give a genuine relative statement for a defect-one tuple, but the
new transcendence occurs outside its field.  Let

`K=Q(z_1,z_2,y_1,y_2)`,  `y_i=exp(z_i)`,  `trdeg_Q K=1`,

with `z_1,z_2` rationally independent.  For every `q=m/n in Q`,

`exp(q*z_i)^n=y_i^m`,

so rational multipliers give values algebraic over `K`.  This is the full containment supplied
by the exponential homomorphism and by deletion algebraicity.  Any two rational multipliers are
Q-linearly dependent, whereas Four Exponentials needs two independent multipliers and Six
Exponentials needs three.  Passing to algebraic irrational multipliers crosses exactly the point
where no polynomial over `K` is available for the new exponential values.

Choose algebraic numbers `alpha_1=1,alpha_2=sqrt(2),alpha_3=sqrt(3)`, which are Q-linearly
independent.  The algebraic-independence refinement of Six Exponentials says, for two independent
`x_i` and three independent `alpha_j`, that at least two of

`x_i, alpha_j, exp(alpha_j*x_i)  (i=1,2; j=1,2,3)`

are algebraically independent.  Apply this with `x_i=z_i`.  Since the `alpha_j` are algebraic
and `Q(z_1,z_2)` is contained in the transcendence-degree-one field `K`, it follows rigorously
that

`trdeg_K K(exp(alpha_j*z_i): i=1,2, j=1,2,3) >= 1`.                 `(E6)`

Thus minimal deletion algebraicity cannot keep all six values in an algebraic extension of `K`.
This is stronger than the ordinary Six Exponentials conclusion, which merely says that one value
is transcendental over `Q` and can already be satisfied by `y_1` or `y_2`.  Because `z_i` and the
algebraic multipliers lie in `C_E=ecl_C(Q)`, and this exponential subfield is closed under field
operations and definable exponentiation, all six values in `(E6)` still lie in `C_E`.  The result
therefore proves only `trdeg_K C_E>=1`; it does not increase `trdeg_Q K`.

Nor can repeated multiplier triples make `(E6)` accumulate.  The theorem requires total
transcendence degree at least two, exactly one more than `K`.  All values from arbitrarily many
applications may be algebraic over one common element transcendental over `K`; the theorem is
not relative to the field generated in preceding applications.

The proved transcendence-degree-one case of the Four Exponentials conjecture is weaker here.
For algebraic independent multipliers `alpha,beta`, its input field
`Q(z_1,z_2,alpha,beta)` has transcendence degree at most one, so at least one of the four
`exp(alpha*z_i),exp(beta*z_i)` is transcendental over `Q`.  All four can nevertheless be
algebraic over `K`, because `K` itself already has transcendence degree one.  A useful ratio
specialization makes this failure concrete.  Take multiplier columns `1,z_2/z_1`; the four
products are

`z_1, z_2, z_2, z_2^2/z_1`.

If `exp(z_1),exp(z_2)` are algebraic, Four Exponentials forces
`exp(z_2^2/z_1)` to be transcendental over `Q`; swapping the indices similarly forces
`exp(z_1^2/z_2)` to be transcendental.  It gives no reason for either value to be transcendental
over `K`.

The mixed stress shows why even this absolute conclusion can be absorbed.  Conditionally take

`(z_1,z_2;y_1,y_2)=(1,ell;e,2)`,  `ell=log 2`,  `trdeg Q(e,ell)=1`.

With multipliers `1,sqrt(2),sqrt(3)`, `(E6)` forces at least one of

`exp(sqrt(2)), exp(sqrt(3)), 2^sqrt(2), 2^sqrt(3)`

to be transcendental over `K=Q(e,ell)`.  This is genuine but external.  The ratio version of
Four Exponentials has the already transcendental entry `exp(1)=e`, so it forces nothing new.
There is also only one rational direction with algebraic exponential value: a direction
`a+b*ell` has exponential `e^a*2^b`, algebraic only when `a=0`.  Hence one cannot form two
independent columns of logarithms of algebraic numbers inside this mixed `K`.

The period stress admits a sharper two-by-two statement.  Conditionally take

`(z_1,z_2;y_1,y_2)=(ell,omega;2,1)`,  `omega=2*pi*I`,
`trdeg Q(ell,omega)=1`.

For any algebraic irrational `alpha`, use rows `1,alpha` and columns `ell,omega`.  The first row
has algebraic exponentials `2,1`.  The two-by-two Gel'fond algebraic-independence theorem then
says that at least two of

`1, alpha, ell, omega, 2^alpha, exp(alpha*omega)`

are algebraically independent.  Since the first four generate a field of transcendence degree
one, at least one of

`2^alpha`,  `exp(2*pi*I*alpha)`

is transcendental over `K`.  The ratio specialization is stronger than mere absolute
transcendence here.  With rows `ell,omega` and columns `1,omega/ell`, the first-row exponentials
are `2,1`; the special `d=l=2` conclusion gives total transcendence degree at least two.  Since
the input field is `K` of transcendence degree one, `exp(omega^2/ell)` is transcendental over
`K`.  Swapping `ell` and `omega` similarly makes `exp(ell^2/omega)` transcendental over `K`.

The analytic subgroup theorem stops at the same boundary.  In the period case
`(ell,omega)` is a logarithm of the algebraic torus point `(2,1)`; the theorem (equivalently here,
Baker's linear-independence theorem) promotes Q-linear independence of `ell,omega` to linear
independence over the algebraic numbers.  It excludes algebraic linear equations, not the
hypothetical nonlinear curve `P(ell,omega)=0`.  In the mixed case one may use
`G_a x G_m`, whose analytic exponential sends `(1,ell)` to the algebraic point `(1,2)`; this
again proves only the known algebraic linear independence of `1,ell`.  Treating `(e,2)` as an
algebraic point over `K` is invalid: the complex analytic subgroup theorem is over algebraic
numbers and has no version obtained by replacing `Qbar` with the transcendental field `K`.

Finally, exact abstract exponential models show saturation of the extension bound.  In the mixed
countermodel `E(1)=T,E(T^d)=2`, or the period countermodel `E(T)=2,E(T^d)=1`, take algebraic
`alpha,beta` so that the relevant products form new rational-basis elements.  Introduce one
element `S` algebraically independent from `T`, prescribe all their exponential values as
nonzero rational functions of `S` (for example `S,S+1,S+2,S+3`), and extend the homomorphism.
Then the original tuple field is still `K=Q(T)` with every deletion algebraic, while every
algebraic-multiplier value lies in `K(S)` and

`trdeg_K K(S)=1`.

This exactly realizes the amount forced by `(E6)`.  Four/Six Exponentials and analytic subgroup
theorems do provide one new transcendental direction in `C_E`, but rational-direction minimality
cannot pull it back into `K`, and their absolute/total rank bounds allow the same single external
parameter to satisfy every application.

Finite-dimensional graph-jet recurrences give a sharp zero estimate, but one selected zero is one
free initial condition.  For a finite `B subset Z^n` and degree bounds `D_i`, let

`V_(D,B)=span_k{X^a*Y^b: 0<=a_i<=D_i, b in B}`.

Every `Delta_i=partial_(X_i)+Y_i*partial_(Y_i)` preserves this space.  If `B_i` is the set of
`i`-th coordinates occurring in `B`, then every `P in V_(D,B)` satisfies the exact operator
identity

`product_(m in B_i) (Delta_i-m)^(D_i+1) P=0`.                 `(J_i)`

Consequently the jets `u_r=(Delta_i^r P)(z,exp z)` obey the constant-coefficient recurrence whose
characteristic polynomial is the product in `(J_i)`.  Equivalently, along the coordinate graph
flow they are the derivatives at zero of a linear combination of

`t^a*exp(m*t),  0<=a<=D_i, m in B_i`.

Their confluent Wronskian is, up to sign,

`product_m product_(a=0)^D_i a! * product_(m<m') (m'-m)^((D_i+1)^2)`,

and is nonzero.  Thus the first `N=(D_i+1)*#B_i` jets determine the whole flow, but `u_0=0`
alone leaves `N-1` independent initial data.  The arithmetic (indeed integral) Wronskian proves
uniqueness only after all those data are supplied; it does not manufacture them from evaluation.

The mixed stress makes this exact.  At

`p=(1,ell;e,2)`,  `ell=log 2`,

the Khovanskii witness in input variables is `(x_1-1,exp(x_2)-2)`, with exponential Jacobian
`diag(1,2)`.  A hypothetical circuit `C(e,ell)=0` contributes the graph-gradient row
`(e*C_U(e,ell),C_V(e,ell))`.  Taking `C` irreducible, this row is nonzero: a singular point of an
irreducible rational plane curve lies in its zero-dimensional rational singular scheme and hence
has algebraic coordinates, whereas `e` and `ell` are transcendental.  The augmented Jacobian
therefore has no extra rank defect; the witness already has full rank independently of `C`.

For the period stress

`p=(ell,omega;2,1)`,  `omega=2*pi*I`,

the witness `(exp(x_1)-2,exp(x_2)-1)` has Jacobian `diag(2,1)`.  A hypothetical irreducible
`C(ell,omega)=0` has nonzero row `(C_U,C_V)` by the same singular-locus argument.  Hence in both
stress cases the circuit zero is simple in at least one graph direction, the opposite of the
additional vanishing a multiplicity argument would need.

There is also an exact fixed-box counterfamily.  At the mixed point, for `1<=j<=D`,

`P_j=(Y_2-2)^j`,  `P_j(p)=0`,  `P_j(flow_2(t))=2^j*(exp(t)-1)^j`;

at the period point use `P_j=(Y_2-1)^j`, whose flow is `(exp(t)-1)^j`.  The matrix of their first
`D` nonconstant jets is triangular with nonzero rational diagonal `2^j*j!`, respectively `j!`.
Rational linear combinations therefore realize arbitrary rational jets `u_1,...,u_D` while
keeping `u_0=0`, all inside the single degree-`D` box.  The last member has a zero of order exactly
`D`, showing that the usual degree-dependent multiplicity bound is sharp; the irreducible linear
member has a completely unconstrained simple zero.

Resultants say the same thing in algebraic language.  For a non-stable irreducible circuit,
`gcd(C,Delta_i C)=1` in some graph direction, so its corresponding resultant is nonzero; the
single equation `C(p)=0` gives no reason for that resultant or `Delta_i C(p)` to vanish.  Deletion
algebraicity only places all evaluated jets in the same algebraic extensions of the deletion
fields, and the displayed jets `1` and `2` show that this is compatible with nonvanishing.
Therefore finite-dimensionality propagates a full block of zero initial jets, not one zero.  Any
Wronskian or zero-estimate proof would first need a new arithmetic theorem forcing the missing
`N-1` vanishings; Khovanskii nonsingularity instead certifies transversality.

Strongly connected decomposition of a Khovanskii witness controls analytic solving order, not
ordinary transcendence between the selected blocks.  Let a square exponential-polynomial system
`F_1,...,F_m` have invertible exponential Jacobian `J(c)`.  Its bipartite support graph at `c` has
an edge `(F_i,x_j)` when `J_(i,j)(c)!=0`, hence has a perfect matching.  After matching equations
with variables, direct an edge `j -> i` when the equation matched to `x_i` depends on `x_j`.
Topologically ordering the strongly connected components makes `J(c)` block triangular, with

`det J(c)=product_s det J_s(c)`.

This point-support construction only decomposes the linearization.  If edges instead mean that
the formal partial derivative is not identically zero, the same ordering gives a structural
block-triangular system: after predecessor blocks are fixed, the implicit-function theorem solves
the next diagonal block.  But its coefficients now include the selected predecessor values and
are generally transcendental, so it is no longer a Khovanskii system over `Q` to which an
arithmetic induction can be applied.

Even genuinely disconnected rational blocks give only a Cartesian product of analytic zero
sets.  Let `K_s` be the ordinary field generated by the selected inputs and exponential values in
block `s`.  Separate block estimates give bounds on each `td_Q K_s`, whereas the union has only

`max_s td_Q K_s <= td_Q(K_1...K_r) <= sum_s td_Q K_s`.

Obtaining the sum requires the new statement that the selected block fields are algebraically
disjoint (successively, that adjoining `K_s` loses no transcendence over `K_1...K_(s-1)`).
Analytic product structure does not impose this on a distinguished tuple of zeros.

The two mandatory diagonal witnesses identify this missing assertion exactly.  For

`(1,ell)`, use `F_1=x_1-1`, `F_2=exp(x_2)-2`;

their Jacobian is `diag(1,2)` and the block fields relevant to Schanuel are `Q(e)` and `Q(ell)`.
Each has transcendence degree one, while additivity is precisely the unknown algebraic
independence of `e` and `ell`.  For

`(ell,omega)`, use `F_1=exp(x_1)-2`, `F_2=exp(x_2)-1`;

the Jacobian is `diag(2,1)`, the block fields are `Q(ell)` and `Q(omega)`, and additivity is
precisely the unknown algebraic independence of `log 2` and `2*pi*I`.  A hypothetical defect-one
relation is an edge between these fields, not an equation in either square witness.  Adding it
makes the system overdetermined; it does not retroactively make the blocks independent.

Minimality does not force a strongly connected witness.  A witness minimal in its number of
variables cannot discard a disconnected component containing a distinguished tuple coordinate;
both diagonal systems above are already of minimal size for their displayed two-coordinate
tuples.  Global minimality of a Schanuel counterexample concerns rational input projections, not
auxiliary witness variables.  At most, witness minimality removes a disconnected component that
contains no target and feeds no target block.  It does not remove two target-bearing components or
a necessary triangular chain of auxiliaries.

More basically, strong connectivity is presentation-dependent.  From any two equations
`F_1,F_2`, replace them by

`G_1=F_1+F_2,  G_2=F_1+2*F_2`.

This invertible rational row operation preserves the zero set, generated ideal, number of
variables, and nonsingularity.  Applied to either diagonal stress witness, both `G_i` depend on
both variables and the matched dependency graph is strongly connected; applying the inverse row
operation recovers two components.  Thus no ordinary-transcendence conclusion can depend merely
on strong connectivity of a chosen list of equations.

An exact analytic counterfeit shows how disconnected selected blocks correlate.  In one block
take `exp(x)-2=0`; in a disjoint block take

`exp(u)-2=0,  y-u^2=0`.

At `(x;u,y)=(ell;ell,ell^2)` the block-diagonal Jacobian determinant is `4`, and the distinguished
coordinates `(x,y)=(ell,ell^2)` are Q-linearly independent, yet

`td_Q Q(x,y)=1 < 2`.

The cross-block identity `x=u` is true of the selected branches but is absent from the product
system.  To include exponential values as well, the same construction is an exact abstract
exponential-field defect: take a transcendental `T`, extend an exponential homomorphism with
`E(T)=2,E(T^2)=3`, and select `(x;u,y)=(T;T,T^2)`.  The rational block system above is formally
nonsingular, `(x,y)` is Q-linearly independent, but

`td_Q Q(x,y,E(x),E(y))=td_Q Q(T)=1`.

This counterfeit need not model the analytic complex exponential; it isolates exactly what the
block graph and Jacobian fail to encode.  The algebraic-input equality case succeeds because
Lindemann--Weierstrass supplies the missing cross-block algebraic independence of the exponential
values, not because its diagonal witnesses are nonsingular.  Therefore a block induction would
require an arithmetic disjointness theorem for selected zeros of independent rational
Khovanskii systems.  On the mixed and period witnesses that statement is already the original
unproved boundary case.

### A full Gel'fond matrix forces unbounded transcendence only outside the logarithm span

The preceding statement about repeated `2 by 3` blocks must be distinguished from one growing
matrix.  The full quantitative theorem does accumulate, provided a Diophantine hypothesis is
available.  The exact source is G. Diaz's theorem as stated in Michel Waldschmidt,
*Algebraic Independence in Algebraic Groups*, Theorems 2.7 and 2.9:

`https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/LN1752-14-2001.pdf`.

For Q-linearly independent rows `x_1,...,x_d` and columns `a_1,...,a_l`, set

`E_0=Q(exp(x_i*a_j):i<=d,j<=l)`,
`E_1=E_0(x_1,...,x_d)`,  `E_2=E_1(a_1,...,a_l)`,

and `t_r=trdeg_Q E_r`.  Without any quantitative hypothesis, the classical small-degree theorem
states exactly

`d*l >= 2*(d+l)  => t_0>=2`,
`d*l >= d+2*l    => t_1>=2`,
`d*l > d+l       => t_2>=2`.

It also has the special `d=l=2` conclusion recorded in the preceding section.  These conclusions
do not grow beyond two, no matter how large the matrix becomes.

For large transcendence degree, Diaz assumes that each row and column tuple satisfies the
Technical Hypothesis: for every `epsilon>0`, every sufficiently large `H`, and every nonzero
integer coefficient vector `h` of norm at most `H`,

`|sum h_i*u_i| >= exp(-H^epsilon)`.

Under this hypothesis and `d*l>d+l`, the exact bounds are

`t_0 > d*l/(d+l)-1`,
`t_1 > (d-1)*l/(d+l)`,
`t_2 >= d*l/(d+l)`.

In particular `t_0>=floor(d*l/(d+l))` and `t_2>=ceil(d*l/(d+l))`.  Algebraic
Q-linearly independent multipliers satisfy the Technical Hypothesis by Liouville estimates.
There is no theorem saying that an arbitrary Q-linearly independent tuple in a
transcendence-degree-one subfield of `C` satisfies it: a transcendental generator can have
arbitrarily strong Liouville approximations.

Now let the rows lie in a defect-one field `K`, so `trdeg_Q K=1`, and let the multipliers be
algebraic.  The field `E_2` is contained in
`K(a_1,...,a_l,exp(x_i*a_j):i<=d,j<=l)`.  This latter field is algebraic over
`K(exp(x_i*a_j):i<=d,j<=l)`, because the `a_j` are algebraic over `Q`.  Thus the sharp relative
consequence of the displayed theorem is

`trdeg_K K(exp(x_i*a_j):i<=d,j<=l)`
`    >= ceil(d*l/(d+l))-1`.                                      `(GM)`

For `d=l=N` this is `ceil(N/2)-1`, hence is unbounded.  For fixed `d`, it approaches
`d-1` as `l` grows.  This is a genuine improvement over separately applying the `2 by 3`
theorem, whose conclusions can all be witnessed by the same single external parameter.

It cannot, however, be used with growing rows while retaining the original graph data.  Inside
`span_Q{z_1,z_2}` one has `d<=2`.  Even with arbitrarily many algebraic multipliers, `(GM)` then
gives at most one dimension over `K`:

`ceil(2*l/(l+2))-1=1` for `l>=3`.

To make `d` grow one must choose additional Q-linearly independent elements of `K`, such as
powers of a transcendence generator.  Minimal deletion algebraicity says nothing about their
exponentials, even for the multiplier `a_1=1`; only rational linear combinations of the original
`z_i` have exponential values algebraic over `K`.  Thus every extra dimension forced by `(GM)`
is allowed to occur in `C_E` outside the countertuple field.

There is one precise multiplier-stabilizer restriction.  For a Technical-Hypothesis tuple
`X=(x_1,...,x_d)` in `K`, define

`A_K(X)={a in Qbar : exp(a*x_i) is algebraic over K for every i}`.

This is a Q-vector space.  Formula `(GM)` implies

`dim_Q A_K(X)<=2` if `d=2`, and `dim_Q A_K(X)<=1` if `d>=3`.

Indeed three independent multipliers for `d=2`, or two for `d>=3`, make `d*l>d+l` and force
positive relative transcendence.  If additionally every `exp(x_i)` is algebraic over `K`, then
`1 in A_K(X)`; for `d>=3` the conclusion sharpens to `A_K(X)=Q`.  Minimality supplies such
controlled rows only in the two-dimensional rational span of the original logarithms, so this
restriction gives no new relation on the minimal tuple itself.

Both boundary stresses realize the unbounded external conclusion.  For the mixed conditional
field `K=Q(e,ell)`, use

`x_i=e^(i-1)  (1<=i<=N)`.

For the period conditional field `K=Q(ell,omega)`, use

`x_i=ell^(i-1)  (1<=i<=N)`.

The powers are Q-linearly independent.  Fixed-degree transcendence measures for `e` and for
`log 2` imply the Technical Hypothesis for each finite tuple (Waldschmidt,
*Transcendence measures for exponentials and logarithms*, J. Austral. Math. Soc. 25 (1978),
445--465).  Choose an algebraic `beta` of degree at least `N` and multipliers
`a_j=beta^(j-1)`.  Diaz then gives, respectively,

`trdeg_K K(exp(e^(i-1)*beta^(j-1)):i,j<=N) >= ceil(N/2)-1`,

and

`trdeg_K K(exp(ell^(i-1)*beta^(j-1)):i,j<=N) >= ceil(N/2)-1`.

All these values lie in `C_E`, so either stress implies `trdeg_K C_E=infinity`.  This is fully
compatible with a finite-transcendence countertuple field and in fact describes the size of the
ambient exponential-algebraic closure, not a contradiction inside `K`.

For completeness, a recent unrefereed preprint gives an unconditional but weaker real-grid
version: Heinrich Massold, *Transcendence degrees of fields generated by exponentials of
products*, arXiv:2506.01123v1, Corollary 1, proves for real Q-linearly independent row and column
tuples

`trdeg_Q Q(exp(x_i*a_j):i<=d,j<=l)`
`    >= floor(sqrt((min(d,l)+1)/2))`.

This also tends to infinity in the two real stress constructions, without invoking their known
transcendence measures, but it remains a statement about new exponential values outside `K` and
does not change the obstruction.

The exact outcome is therefore two-sided.  Full matrix theorems can force arbitrarily many
ordinary transcendence dimensions over a defect-one `K` once one allows many suitable rows from
`K`; they cannot do so within the rational logarithm span where deletion algebraicity applies.
No theorem moves the externally forced grid values back into `K`, so the strengthened estimate
imposes only the multiplier-stabilizer bound above and no contradiction to the minimal
counterexample normal form.

Tensor products of local Khovanskii algebras are presentation-invariant, but at a nonsingular
selected zero they retain only multiplicity one.  For a square block `F=(F_1,...,F_m)` and a zero
`c` with `det J_F(c)!=0`, its convergent analytic local algebra is

`A_(F,c)=O_(C^m,c)/(F_1,...,F_m) congruent C`.

The isomorphism is evaluation at `c`; its length is one, multiplication trace is
`Tr(M_h)=h(c)`, and the discriminant of the basis `{1}` is `1`.  For two independent blocks,

`A_(F,c) completed_tensor_C A_(G,d) congruent A_((F,G),(c,d)) congruent C`.

Thus the tensor algebra, trace pairing, and discriminant are identical whether the coordinates
of `c` and `d` are algebraically independent or satisfy arbitrarily many cross-relations.

The Grothendieck residue makes the surviving Jacobian datum explicit.  With
`ell=log 2`, `omega=2*pi*I`, the period blocks

`f(X)=exp(X)-2`,  `g(Y)=exp(Y)-1`

have local algebras `C`, Jacobians `2` and `1`, and

`Res_((ell,omega)) h(X,Y)dX dY/(f(X)g(Y))=h(ell,omega)/2`.

For the mixed blocks take `f(U)=U-exp(1)` at `U=e` and `g(V)=exp(V)-2` at `V=ell`.
Their Jacobians are `1` and `2`, and the product residue is likewise

`Res_((e,ell)) h(U,V)dU dV/(f(U)g(V))=h(e,ell)/2`.

If a hypothetical rational `P` vanishes at either selected pair, its class and multiplication
trace in the corresponding length-one algebra are simply zero.  In local coordinates the period
inverse branches are

`X=ell+Log(1+s/2),  Y=omega+Log(1+t)`,

and the mixed inverse branches are `U=e+s`, `V=ell+Log(1+t/2)`.  Hence any such `P` is
`s*A+t*B` with convergent complex-coefficient germs `A,B`.  This is the local maximal-ideal
identity again, not a rational exponential-polynomial relation between the blocks.

Raw Jacobian determinants cannot repair the loss.  Replacing one equation by a nonzero rational
multiple changes its determinant and residue by reciprocal rational factors while preserving its
zero, ideal, and local algebra.  Only nonvanishing, or the residue pairing up to the corresponding
choice of generators, is intrinsic.  For a reduced length-one algebra its intrinsic discriminant
remains `1`.

There is an exact base-field dichotomy.  Over `C`, analytic localization makes the quotient finite
but all selected coordinates are already scalars, so arithmetic dependence is forgotten.  Over
`Q`, let `K_c` and `K_d` be the fields generated by the evaluated coordinates and exponential
values.  The canonical multiplication map

`mu: K_c tensor_Q K_d -> C,  a tensor b |-> a*b`

is injective exactly when the two selected fields have no cross-block algebraic dependence of the
relevant kind.  Proving injectivity is the desired disjointness theorem, not a consequence of
local nonsingularity.  Moreover these residue fields contain `e`, `ell`, or `omega` and are not
finite over `Q`; hence the witness does not produce a finite Q-algebra on which an arithmetic
field trace or discriminant is available.  Taking all global branches instead produces an
infinite logarithm lattice, again not a finite Q-algebra.

The failure occurs even for honest analytic blocks.  Take one block `exp(x)-2=0` and a disjoint
block

`exp(u)-2=0,  y-u^2=0`.

At `(x;u,y)=(ell;ell,ell^2)` the local tensor algebra still has length one and the product
Jacobian determinant is `4`.  The distinguished coordinates `(x,y)` are Q-linearly independent,
but `td_Q Q(x,y)=1`; the multiplication map for the selected block fields kills the nonzero
cross-element represented by `x tensor 1-1 tensor u`, and also records `y-x^2=0`.  Neither
relation belongs to the disconnected rational system.

There is a sharper abstract counterfeit including both inputs and exponential values.  In a
sufficiently large algebraically closed field choose a transcendental `T` and extend an
exponential homomorphism from the Q-span of `T,T^2` so that

`E(T)=2,  E(T^2)=3`.

The two one-variable rational blocks `E(X)-2=0` and `E(Y)-3=0` at `(T,T^2)` have formal
Jacobians `2,3`, formal multiplicity-one data, product determinant `6`, and Q-linearly independent
inputs.  Nevertheless

`td_Q Q(T,T^2,E(T),E(T^2))=1<2`.

All tensor-length, determinant, trace, and discriminant data have their optimal nonsingular
values while block disjointness fails.  Finite etale algebra methods can detect intersections of
finite algebraic residue fields, but a Khovanskii zero supplies either a complex length-one fiber
or a transcendental, non-finite Q-residue field.  A presentation-invariant tensor argument must
therefore assume injectivity of `mu`; on `Q(e)` versus `Q(log 2)`, or `Q(log 2)` versus
`Q(2*pi*I)`, that assumption is exactly the original algebraic-independence boundary.

### Galois-orbit norms give one descended character, not descended roots

Complete algebraic conjugate orbits create a genuine analytic identity, but its exact character
rank is too small.  Let `L/Q` be a finite Galois extension of degree `l`, choose a normal element
`beta`, and write its conjugates as `beta_1,...,beta_l`.  After rational scaling one may assume
that

`t=Tr_(L/Q)(beta)`

is a nonzero integer.  Normality says that the `beta_j` are Q-linearly independent; in particular
the trace cannot be zero.  For any complex `x`, put `U_j=exp(beta_j*x)`.  Then

`product_j U_j = exp(t*x)`.                                      `(N)`

If `x` is in the rational span of the original logarithms, the right side is algebraic over the
countertuple field `K`.

This is the only character descent supplied by the orbit.  Indeed, because the `beta_j` form a
Q-basis of `L` and `1=(1/t)*sum_j beta_j`,

`{m in Z^l : sum_j m_j*beta_j in Q}=Z*(1,...,1)`.                 `(CL)`

Thus the lattice of monomials in the `U_j` whose exponent is a rational multiple of `x` has rank
one.  With `d` rows that are linearly independent over `Qbar`, the same argument row by row gives
exactly `d` independent norm characters among `d*l` grid entries.  The mixed and period rows
below have the required algebraic linear independence (in the period case by Baker's theorem).

The other symmetric functions do not descend as values.  Formally

`F_x(T)=product_j (T-exp(beta_j*x))`.

Its constant coefficient is `(-1)^l*exp(t*x)` and is controlled by `(N)`.  For
`1<=r<l`, its other coefficients are exponential sums

`c_r(x)=sum_(|I|=r) exp(x*sum_(j in I) beta_j)`.

As functions of a variable `X`, the `c_r(X)` have rational Taylor coefficients because the
subset sums form Galois-stable sets.  This is descent to `Q[[X]]`, not descent of the value
`c_r(x)` to `K`.  These are nonconstant exponential polynomials and are transcendental over
`Q(X)`; evaluating at one transcendental `x` supplies no algebraic equation over `K`.

Already a quadratic normal element displays the failure.  For
`beta=1+sqrt(2)` with conjugate `beta'=1-sqrt(2)`,

`U*U'=exp(2*x)`,
`U+U'=2*exp(x)*cosh(sqrt(2)*x)`.

Only the product is controlled when `exp(x)` is.  The putative root polynomial is

`T^2-2*exp(x)*cosh(sqrt(2)*x)*T+exp(2*x)`,

whose middle coefficient is precisely a new exponential value, not an element of `K`.
Consequently no resultant may treat the `U_j` as conjugates over `K`; the coefficient field
needed to form that resultant already contains the external data one hoped to eliminate.

Exterior powers give the same identity in disguise.  The `r`th exterior weights are the subset
sums `sum_(j in I) beta_j`, and the product of their exponential values is

`exp(binomial(l-1,r-1)*t*x)`.

The top exterior power is `(N)`; lower exterior powers again have just their total norm
controlled.  All weights remain in the `l`-dimensional field `L`, so taking exterior or symmetric
powers cannot increase the independent multiplier rank beyond `l`.

Several complete orbits do not improve the ratio.  If orbit `s` has trace `t_s!=0`, then any two
orbits satisfy the rational multiplier relation

`t_2*sum_(j in orbit 1) beta_j - t_1*sum_(j in orbit 2) beta_j=0`.

Hence the union of `s` orbits of total size `M` has Q-rank at most `M-s+1`.  Selecting an
independent multiplier basis omits `s-1` values; each omitted exponential is already determined,
up to a rational root, by the selected values and the norm identities.  A trace-zero orbit is
even more direct: its full orbit is Q-dependent, and after one column is removed the identity
`product U_j=1` merely recovers the omitted value.  Tensoring fields or using products of
conjugates produces one larger orbit in the compositum and returns to the same single-trace
situation.

The two exact stresses show the remaining room.  In the mixed conditional field

`K=Q(e,ell)`,  `(x_1,x_2)=(1,ell)`,

the two norm equations are

`product_j exp(beta_j)=e^t`,
`product_j exp(beta_j*ell)=2^t`.

Each `exp(beta_j)` is transcendental by Lindemann--Weierstrass, and each `2^beta_j` is
transcendental by Gel'fond--Schneider, but neither theorem puts the individual values in `K`.
For a normal orbit of length `l>=3`, the full Gel'fond matrix estimate with `d=2` forces exactly
the already found lower bound

`trdeg_K K(exp(beta_j),2^beta_j:j<=l)>=1`,

and never more, since `ceil(2*l/(l+2))-1=1`.

In the period conditional field

`K=Q(ell,omega)`,  `(x_1,x_2)=(ell,omega)`,  `omega=2*pi*I`,

the norm equations are

`product_j 2^beta_j=2^t`,
`product_j exp(beta_j*omega)=1`.

Baker's theorem makes the character calculation exact for algebraic targets: if algebraic
`A,B` satisfy `exp(A*ell+B*omega)` algebraic, then adjoining a logarithm of that algebraic value
and applying algebraic linear independence of logarithms shows `A,B in Q`.  Thus no hidden
algebraic-coefficient character enlarges `(CL)`.  Nevertheless one external parameter still
satisfies both norm equations and the Diaz lower bound.

An abstract exponential saturation makes the obstruction literal.  Start with either previous
defect-one countermodel, with two rows `x_1,x_2`, controlled values `y_i=E(x_i)`, and tuple field
`K=Q(T)`.  Take a normal orbit as above and one new element `S` transcendental over `K`.  For
each row choose nonzero rational functions of `S`, for example

`V_(i,j)=S+c_(i,j)  (j<l)`,
`V_(i,l)=y_i^t/product_(j<l)(S+c_(i,j))`,

with distinct rational constants `c_(i,j)`.  Prescribe

`E(beta_j*x_i)=V_(i,j)`

and extend the homomorphism on a rational basis.  The only forced additive relation is
`sum_j beta_j*x_i=t*x_i`, and the displayed definition satisfies it exactly.  All grid values,
all orbit norms, and all symmetric coefficients lie in `K(S)`, with

`trdeg_K K(S)=1`.

This saturates the `d=2` Gel'fond lower bound while preserving both genuine analytic norm
identities.  Trace, determinants, exterior powers, symmetric functions, multiple orbits, and
resultants therefore do not pull the external transcendence back into `K`: they either reproduce
the single norm character, sacrifice the same number of independent multiplier columns, or
introduce coefficients containing the external parameter itself.

### Mahler and q-difference specialization do not absorb the logarithmic stresses

Fix an integer `q>=2`.  A one-variable Mahler system has the form

`F(z)=A(z)F(z^q)`,  `A(z) in GL_m(Qbar(z))`,  `F(z) in Qbar[[z]]^m`.

For an algebraic `alpha` with `0<|alpha|<1`, regularity means that every
`A(alpha^(q^k))` is defined and invertible.  Nishioka's theorem then gives the exact equality

`trdeg_Qbar Qbar(F(alpha))=trdeg_Qbar(z) Qbar(z,F(z))`.

The accompanying lifting theorem lifts homogeneous algebraic relations at `alpha` to functional
relations.  These hypotheses and conclusions are Theorems 1.1 and 1.2 of Adamczewski--Faverjon,
*A new proof of Nishioka's theorem in Mahler's method*:

`https://arxiv.org/abs/2210.14528`.

They would be strong enough if the logarithm generating function were Mahler, but it is not.  At
the common algebraic point `alpha=1/2`, put

`E(z)=exp(2z)`,  `L(z)=-log(1-z)`.

Then `(E(alpha),L(alpha))=(e,log 2)`.  Both functions are D-finite, with

`E'-2E=0`,  `(1-z)L''-L'=0`,

and both are nonrational.  Bezivin's intersection theorem says that a D-finite Mahler power series
is rational.  Thus neither `L` nor `E` is a Mahler function for any base.  A primary modern proof
is Bell--Coons--Rowland, *The rational-transcendental dichotomy of Mahler functions*:

`https://arxiv.org/abs/1210.2070`.

The analogous q-dilation escape also fails.  The Ramis intersection theorem, in the form proved by
Schafke--Singer, says that a formal power series satisfying both a linear differential equation
and a linear q-difference equation over `C(z)` is rational when `q` is nonzero and not a root of
unity.  Hence the same two nonrational D-finite functions satisfy no such linear q-difference
equation.  See Corollary 3 of *Consistent systems of linear differential and difference
equations*:

`https://singer.math.ncsu.edu/papers/Schaefke_Singer_revised.pdf`.

This exclusion is not hiding a functional dependence.  In fact `E(z)` and `L(z)` are algebraically
independent over `C(z)`: continuation around `z=1` fixes `E` and replaces `L` by
`L-2*pi*i*k` for every integer `k`.  A polynomial relation would therefore have infinitely many
translates in its `L` variable; all of its coefficients as polynomials in `E` would vanish, and
the transcendence of `exp(2z)` over `C(z)` finishes the argument.  Thus a specialization theorem
covering this functionally independent E/D-finite pair at `1/2` would prove precisely the open
algebraic independence of `e` and `log 2`.  Reclassifying the second function as Mahler is blocked
by the intersection theorem, not by a poor choice of presentation.

There are two exact but inadmissible Mahler-looking presentations.  On a chosen logarithm branch,

`H(z)=-log z`,  `H(z^q)=q H(z)`,  `H(1/2)=log 2`.

The coefficient is rational and the scalar system is regular, but `H` is not a power series at
the attracting fixed point `0`; the orbit `(1/2)^(q^k)` runs directly into its logarithmic
singularity.  Alternatively, for `|z|<1`,

`1/(1-z)=prod_(j>=0)(1+z^(2^j))`,
`L(z)=log(1+z)+L(z^2)`.

The first identity is a rational Mahler identity only after exponentiating; the second retains the
additive value but has the nonrational coefficient `log(1+z)`.  The parameter family
`(1-z)^(-s)=(1+z)^s(1-z^2)^(-s)` recovers `L` by differentiating at `s=0`, but
`(1+z)^s` is not in `Qbar(s,z)` and the parameter jet is outside Mahler's theorem.

Nor can the E-block be appended to a Mahler or linear q-difference system.  Under the Mahler map,
`exp(2z)` produces the unbounded family `exp(2z^(q^k))`; Bezivin's theorem rules out any finite
rational-linear closure.  Under q-dilation one has, for integral `q`,

`E(qz)=E(z)^q`,

which is nonlinear, while the rank-one linear ratio `E(qz)/E(z)=exp(2(q-1)z)` is not rational.
The 2024 theorem of Adamczewski--Faverjon, despite its translated title *Algebraic relations
between values of Siegel E-functions and Mahler M-functions*, proves two parallel assertions:
Theorem 1(E) treats a tuple consisting of E-functions by differential degeneration, and Theorem
1(Mq) treats a tuple consisting of `Mq`-functions by `sigma_q`-degeneration.  It states no mixed
E--Mahler relation theorem:

`https://www.numdam.org/articles/10.5802/crmath.634/`.

Functional independence alone cannot be substituted for such a mixed theorem.  Let

`T(z)=sum_(n>=0) z^(2^n)`,  so `T(z)=z+T(z^2)`,
`G(z)=(z-1/2)T(z)`.

Then `G` is an `M_2`-function.  A nonrational Mahler function is differentially transcendental,
so `G` is algebraically independent from the differentially algebraic E-function `E` over
`C(z)`.  Nevertheless

`(E(1/2),G(1/2))=(e,0)`

is algebraically dependent.  The exact Mahler system for `(1,G)` has lower row

`(z(z-1/2), (z-1/2)/(z^2-1/2))`.

Its determinant vanishes at `z=1/2`.  This is a sharp specialization counterfeit: separate
functional Galois information does not combine across the two operators, and the missing datum is
exactly a mixed regular specialization theorem.  For the actual mixed stress the situation is
strictly worse, since `L` does not belong to the Mahler block at all.

The period control has the same obstruction.  The natural function

`A(z)=arctan z=(log(1+i*z)-log(1-i*z))/(2*i)`

is D-finite and nonrational, hence neither Mahler nor linear q-difference.  Its direct value
`A(1)=pi/4` is also on the forbidden unit-circle boundary.  Machin's identity moves all arguments
inside the disk,

`pi/4=4*arctan(1/5)-arctan(1/239)`,

and, at a common point `alpha=1/2`, these are the values of
`arctan(2z/5)` and `arctan(2z/239)`.  Both functions remain nonrational D-finite functions, so the
intersection theorems still exclude them.  More explicitly, set

`Omega(z)=8*i*(4*arctan(2z/5)-arctan(2z/239))`.

Then

`(L(1/2),Omega(1/2))=(log 2,2*pi*i)`.

This pair is even functionally algebraically independent: monodromy about `z=1` translates `L`
and fixes `Omega`, while monodromy about `z=5*i/2` shows that `Omega` is transcendental over
`C(z)`.  Hence a specialization theorem covering it would yield the still-open algebraic
independence of `log 2` and `2*pi*i`; Mahler and q-difference lifting do not apply to either
coordinate.  The tautological alternative
`-i*Log(-1)=pi` uses a Mahler eigenfunction `Log(z^q)=q Log(z)`, but both its singularity at zero
and the boundary point `-1` violate the special-value hypotheses.

Finally, a genuine q-logarithm does not repair the identification.  If
`Theta_q(qz)=z^(-1)Theta_q(z)` and
`ell_q(z)=-z*Theta_q'(z)/Theta_q(z)`, then

`ell_q(qz)=ell_q(z)+1`.

It follows that `ell_q(z)-log(z)/log(q)` is q-periodic.  Thus replacing the classical logarithm by
`ell_q` introduces theta logarithmic derivatives and a q-periodic constant; recovering the
classical logarithm also multiplies by `log(q)`, which for `q=1/2` is the target `-log 2` itself.
Likewise q-exponentials converge to the classical exponential only in a singular `q->1` limit and
introduce q-Pochhammer/theta periods at fixed algebraic `q`.  No introduced constant is eliminated
by the functional equations.

This route is therefore closed.  The strongest unconditional specialization theorems are exact
within the E-class and within a fixed Mahler class.  The mixed pair lies in neither one common
class, the singular logarithm encodings miss the attracting-germ hypothesis, and a theorem that
coupled the two regular blocks strongly enough to handle `(e,log 2)` would already be the missing
algebraic-independence theorem rather than a consequence of current Mahler or q-difference
methods.

### The restriction-of-scalars norm fiber has no relative analytic-subgroup theorem

The torus formulation identifies exactly what Galois descent does and does not provide.  Keep the
Galois extension `L/Q`, normal element `beta`, conjugates `beta_j`, degree `l`, and nonzero
integer trace `t` from the preceding section.  Let

`T=Res_(L/Q) G_m`,  `T^1=ker(N_(L/Q):T->G_m)`.

Over `Qbar`, `T` is `G_m^l`, its character lattice is `Z^l` with the Galois permutation action,
and the Q-defined norm character is `(1,...,1)`.  For a logarithm `x`, the analytic point and its
logarithm are

`P_x=(exp(beta_1*x),...,exp(beta_l*x)) in T(C)`,
`u_x=x*(beta_1,...,beta_l) in Lie(T)_C`,

with `N(P_x)=exp(t*x)`.  If `x` is in the rational span of the countertuple logarithms, this norm
is algebraic over `K`, so `P_x` lies on the `K`-defined fiber

`N^(-1)(exp(t*x))`.

This says neither that `P_x` is `K`-rational nor that its split coordinates are field conjugates
over `K`.  A complex point of a variety defined over `K` can have arbitrary coordinate
transcendence.  The geometric Galois action on `T_Qbar` permutes coordinate slots; it does not act
on the analytic values by the nonexistent rule

`sigma(exp(beta*x))=exp(sigma(beta)*x)`.

One can remove the descended scalar explicitly.  Put

`w_j=beta_j-t/l`,  `Q_x=(exp(w_1*x),...,exp(w_l*x))`.

Then `sum_j w_j=0`, so `Q_x in T^1(C)`, and `P_x` differs from `Q_x` by the diagonal scalar
`exp(t*x/l)`, which is algebraic over `K`.  The only integer relation among the `w_j` is the
all-ones relation:

`{m in Z^l:sum_j m_j*w_j=0}=Z*(1,...,1)`.

Consequently the analytic one-parameter map

`z |-> (exp(w_1*z),...,exp(w_l*z))`

is Zariski dense in the `(l-1)`-dimensional norm-one torus.  Its one-dimensional analytic image
is not an algebraic subtorus.

This is also the exact stopping point of the analytic subgroup theorem.  The line
`C*(beta_1,...,beta_l)` in `Lie(T)_C` is defined over `Qbar`.  If `P_x` were an algebraic-number
point, the theorem would force a positive-dimensional algebraic subtorus whose Lie algebra lies
in that line.  A one-dimensional subtorus has an integral cocharacter direction, whereas the
Q-independent conjugates `beta_j` are not proportional to an integer vector.  Thus `P_x` cannot
have all coordinates algebraic over `Qbar`.  Applied after normalization, the same argument works
in `T^1` for `l>=3`; for `l=2`, `T^1` itself is one-dimensional and the conclusion instead comes
from Gel'fond--Schneider in the boundary examples.

The needed hypothetical statement is much stronger: it would have to apply when `P_x` is only
algebraic over the transcendence-degree-one field `K`.  Wuestholz's complex analytic subgroup
theorem is formulated for algebraic groups, Lie subspaces, and endpoints over `Qbar`; replacing
`Qbar` by `Kbar` is not a base change of that theorem.  If every coordinate of `P_x` were
algebraic over `K`, the point would lie in `T(Kbar)` and all conclusions above over `Qbar` would
remain unavailable.  The full Gel'fond grid is precisely the separate input that rules out all
such coordinates lying in `Kbar` for sufficiently many columns.

The period boundary makes the distinction especially stark.  For

`x=ell=log 2`,  `N(P_x)=2^t`,

and for

`x=omega=2*pi*I`,  `N(P_x)=1`.

Both norm fibers are defined over `Q`, not merely over `K=Q(ell,omega)`.  Nevertheless every
coordinate `2^beta_j` and `exp(2*pi*I*beta_j)` is transcendental by
Gel'fond--Schneider.  The normalized points lie in the Q-defined torus `T^1` and, modulo the norm
character, have no multiplicative character relation.  Being on a Q-defined norm fiber therefore
does not move even one coordinate toward `Qbar`, much less toward the defect field `K`.

For the mixed boundary, the two rows give

`N(P_1)=e^t`,  `N(P_ell)=2^t`.

The first fiber is only defined over `Q(e) subset K`, while the second is defined over `Q`.
The analytic subgroup theorem proves absolute transcendence for the orbit coordinates but has no
relative conclusion over `Q(e,ell)`.  Normalizing by `e^(t/l)` or `2^(t/l)` changes no relative
transcendence degree because those scalars are algebraic over `K`.

Weil-restriction heights have the same one-way behavior.  For an algebraic point, a standard
height on `T` is comparable to the sum of the heights of its split coordinates, while the norm
map gives only an inequality of the form

`h(N(P)) <= sum_j h(P_j)+O(1)`.

A small or fixed norm gives no upper bound for the coordinate heights; norm-one torus points can
have unbounded height.  For the present transcendental coordinates the number-field height is not
defined at all.  If one assumes they are algebraic over the function field `K` and chooses a
model, the product formula says at every divisorial place

`sum_j ord_v(Q_j)=0`.

Positive and negative coordinate divisors cancel, so no individual height vanishes.

There is an exact restriction-of-scalars saturation, not merely a split-torus counterfeit.  Let
`f(Z)=product_j (Z-beta_j) in Q[Z]` and let `S` be transcendental.  The element

`q(S)=(S-beta)^l/f(S) in L(S)^* = T(Q(S))`

has norm one.  In split coordinates,

`q_j(S)=(S-beta_j)^l/f(S)`,  `product_j q_j(S)=1`.

These coordinates are genuine Galois conjugates as rational functions.  Each has function-field
height `l-1`: it has a zero of order `l-1` at `S=beta_j` and simple poles at the other conjugates.
The powers `q(S)^m` retain norm one and have height `m*(l-1)`, giving exact unbounded-height
cancellation on the fixed Q-defined torus.

To incorporate the exponential rows, use distinct rational shifts `c_i` and set

`q_(i,j)(S)=(S-c_i-beta_j)^l/f(S-c_i)`.

In either previous abstract defect-one exponential model, prescribe

`E((beta_j-t/l)*x_i)=q_(i,j)(S)`

and then

`E(beta_j*x_i)=E(x_i)^(t/l)*q_(i,j)(S)`,

using compatible rational roots.  The product in each row is exactly `E(x_i)^t`; every normalized
row is an actual `T^1(Q(S))` point with the correct Galois permutation law; and the entire grid
lies in `Kbar(S)` with relative transcendence degree one.  The character lattice has no further
relation, and all divisorial norm cancellations and height identities hold exactly.

Restriction of scalars thus adds no descent beyond the norm character already audited.  The
norm-one torus packages the external degrees cleanly, but neither its subgroup lattice, the
analytic subgroup theorem, nor Weil heights can turn a geometric point on a `K`-defined fiber
into a `K`-algebraic point.

### Finite Khovanskii character does not stabilize the Diaz tower

The unbounded full-grid conclusion can be converted into an actual strictly increasing tower
inside `C_E=ecl_C(Q)`.  It does not conflict with finite character.  Use, for each `N`, an
algebraic number `beta_N` of degree at least `N` and the two Technical-Hypothesis tuples

`1,e,...,e^(N-1)` and `1,beta_N,...,beta_N^(N-1)`.

Diaz's exponential-only estimate gives

`trdeg_Q Q(exp(e^i*beta_N^j):0<=i,j<N) >= floor(N/2)`.            `(DT)`

Every entry of this grid lies in `C_E`: `e=exp(1)` is definable over `Q`, `beta_N` is algebraic,
and `C_E` is a field closed under definable exponentiation.

Let `K_0` be any finitely generated subfield of `C_E`; in particular it may be the hypothetical
defect-one tuple field.  Inductively, suppose `K_m` is finitely generated and put
`r_m=trdeg_Q K_m`.  Choose `N` with `floor(N/2)>r_m`.  By `(DT)`, not every entry of the finite
`N by N` grid can be algebraic over `K_m`.  Choose one entry `a_m` transcendental over `K_m` and
put

`K_(m+1)=K_m(a_m)`.

Then, exactly,

`trdeg_(K_m) K_(m+1)=1`,
`dim_ecl(a_m/K_m)=0`.

The second equality holds because `a_m in ecl_C(Q) subset ecl_C(K_m)`.  Thus

`K_0 proper-subset K_1 proper-subset ... subset C_E`

has unbounded ordinary transcendence degree while every extension has exponential-closure rank
zero.  In particular `trdeg_(K_0) C_E=infinity`.  This construction works over the actual complex
exponential field, not only in a counterfeit model.

Each entry also has a concrete finite Khovanskii witness.  If `p_N(B)` is the separable minimal
polynomial of `beta_N` and

`a=exp(e^i*beta_N^j)`,

use the two equations in variables `(B,A)`

`p_N(B)=0`,
`A-exp(exp(1)^i*B^j)=0`.

At `(beta_N,a)` the Jacobian is triangular with determinant `p_N'(beta_N)!=0`.  Hence every new
tower generator is exponentially algebraic over `Q` by an explicit nonsingular finite system,
even though it is ordinarily transcendental over all earlier stages.

The stress-specific towers can remain inside their natural row fields.  In the mixed case
`K=Q(e,ell)` already contains `e`, so the preceding construction applies verbatim.  In the period
case use rows `1,ell,...,ell^(N-1)` instead.  Fixed-degree transcendence measures for `ell=log 2`
give the Technical Hypothesis, and each grid entry

`a=exp(ell^i*beta_N^j)`

has the triangular Khovanskii system

`exp(L)-2=0`,  `p_N(B)=0`,  `A-exp(L^i*B^j)=0`,

whose Jacobian determinant at `(ell,beta_N,a)` is `2*p_N'(beta_N)`.  Therefore both the mixed and
all-algebraic-exponential boundaries contain the same strictly increasing zero-ecl-rank tower.

Finite character says only that membership `a in ecl(A)` is witnessed over a finite subset of
`A`.  It does not give a finite generating set for `ecl(A)`, a uniform bound on the number or
complexity of witnesses, or any comparison between ecl rank and ordinary transcendence degree.
Noetherianity is equally local: each fixed algebraic ideal in finitely many variables is finitely
generated, while the tower uses unbounded degrees, numbers of variables, and exponential terms.
Even a fixed exponential equation can have infinitely many nonsingular analytic zeros, so a
finite Khovanskii system is not a finite algebraic fiber.

There is a sharper abstract countermodel in which even witness complexity stays constant.  Let

`F=Qbar(t_1,t_2,...)^alg`

with the `t_m` algebraically independent.  On the rational span of the `t_m`, prescribe a total
exponential homomorphism by

`E(t_m)=t_m`

using compatible rational roots, and extend it to the additive group of `F` (the divisible group
`F^*` is injective).  Every `t_m` is a nonsingular zero of the same one-variable equation

`E(X)-X=0`,

because its formal derivative is `E(X)-1` and `t_m-1!=0`.  Hence every `t_m` lies in
`ecl_F(Q)`, and field-theoretic algebraic closure then gives

`ecl_F(Q)=F`,  `dim_ecl(F/Q)=0`,  `trdeg_Q F=infinity`.

Taking `K=Q(t_1)` yields a finitely generated transcendence-degree-one subfield with
`trdeg_K ecl_F(Q)=infinity`, although all new generators use one equation of fixed arity and
fixed formal complexity.  This rules out any formal lemma asserting that finite generation of
`K`, finite Khovanskii character, or bounded witness format makes `C_E/K` algebraic or of finite
ordinary transcendence degree.

The strengthened all-deletion property is confined to the original countertuple:

`K/K_(delete i) is algebraic`.

It does not say that an arbitrary exponentially algebraic element of `C_E` is algebraic over
`K`, and applying it to a grid element would amount to assuming the missing conclusion.  To make
the tower return a dimension to `K`, one would need a genuinely uniform theorem asserting either
that all sufficiently complex grid values are algebraic over one fixed finite extension of `K`,
or that `C_E` has finite ordinary transcendence degree over `K`.  The Diaz tower proves the latter
false, and the explicit fixed-equation model shows that finite character and Noetherianity cannot
supply the former.  The exact missing input is relative arithmetic control tying new Khovanskii
branches to the original tuple field, not finiteness of their individual witnesses.

### Cartan targets from all rational deletions have a common base locus

The uniform first-failure normal form gives a precise Nevanlinna test, but its sharp inequality
goes in the wrong direction.  Write `N=n+1`, let `p=(z,exp z)`, and let `W` be its Q-Zariski
locus.  Then `dim W=N-1`, and algebraicity over every rational hyperplane deletion says that each
corresponding projection of `W` is generically finite onto its image.  Clearing a recovery
equation gives a rational algebraic divisor `D_A` containing `W`.  This is a family of divisors
with the fixed base locus `W`, not a family of targets in general position.

Use the radial entire curve in a projective compactification,

`gamma_z(t)=[1,t*z_1,...,t*z_N,exp(t*z_1),...,exp(t*z_N)]`.

Directly from the definition of the Cartan characteristic,

`T_(gamma_z)(r)=c(z)*r+O(log r)`,

where

`c(z)=(1/(2*pi))*integral_0^(2*pi)
        max(0,max_i Re(z_i*exp(I*theta))) dtheta > 0`.             `(NC)`

The additive coordinates contribute only `O(log r)`; the displayed support function is the
linear exponential contribution.  If a fixed divisor `D` contains `p` but not the whole radial
curve and its pullback has multiplicity `m` at `t=1`, that selected point contributes exactly
`m*log r` to `N_(gamma_z)(r,D)` for `r>1`.  Therefore for any fixed recovery divisors
`D_1,...,D_q`, with multiplicities `m_j`, the complete information forced at the selected point is

`sum_j N_(gamma_z,{1})(r,D_j)=(sum_j m_j)*log r=o(T_(gamma_z)(r))`. `(BASE)`

This is the sharp inequality: one algebraic intersection point is asymptotically invisible to an
order-one exponential curve.  The first main theorem supplies only the compatible upper bounds
`N(r,D_j)<=deg(D_j)*T_(gamma_z)(r)+O(1)`.

Taking more rational hyperplanes cannot activate Cartan's second main theorem.  In projective
dimension `M`, a useful Cartan coefficient requires more than `M+1` admissible hyperplanes, but
`M+1` hyperplanes all passing through `p` are not admissible: their intersection contains `p`.
For recovery hypersurfaces the failure is stronger because all of them contain `W`.  This is
exactly the general-position hypothesis in Cartan's theorem; see Alexandre Eremenko,
*On the Second Main Theorem of Cartan*, arXiv:1409.4850, equation (4).  If instead one solves a
recovery polynomial for the omitted pair, its coefficients become meromorphic functions of the
retained graph coordinates.  Their characteristics are `O(T_gamma)`, and generally have the same
linear term.  They are not slowly moving targets, for which the standard hypothesis is
`T_target(r)=o(T_gamma(r))`; this normalization is explicit, for example, in Cao--Nie,
*The second main theorem for holomorphic curves intersecting hypersurfaces*, Ann. Acad. Sci.
Fenn. Math. 42 (2017), 979--996.

There is also an exact interpolation-determinant form of the base-locus loss.  Put
`F_j(t)=P_j(gamma_z(t))` for recovery equations `P_j in I(W)`.  Every `F_j(1)=0`.  A determinant
whose first row is the values at `1` vanishes tautologically, while after writing

`F_j(t)=(t-1)^(m_j)*G_j(t)`

the reduced jets of the `G_j` are unconstrained elements of `K=Q(z,exp z)`.  If all multiplicities
equal `m`, the Wronskian identity

`Wr((t-1)^m*G_1,...,(t-1)^m*G_q)=(t-1)^(m*q)*Wr(G_1,...,G_q)`

shows that the common zero is precisely a removable projective base factor; Cartan's ramification
term pays for the same factor.  Sampling at rational `t=a/b` only moves the entries into Kummer
extensions algebraic over `K`.  Norming them through a deletion returns values in a field of
transcendence degree `N-1`, not a discrete number field, so no nonzero determinant lower bound
results.

The fully transcendental mixed stress realizes every part of this calculation without a
hypothetical polynomial.  Let `ell=log 2` and use the sheared family

`w=(2*ell+1,ell+1)`,  `exp(w)=(4*e,2*e)`.

Both coordinates and both exponentials are transcendental and

`Q(w_0,exp(w_0))=Q(ell,e)=Q(w_1,exp(w_1))`.

Thus each coordinate deletion already gives field equality, stronger than algebraicity, whether
or not `ell,e` are algebraically independent.  The two rational recovery equations

`R_X=X_0-2*X_1+1`,  `R_Y=Y_0-2*Y_1`

pull back radially to

`R_X(gamma_w(t))=1-t`,
`R_Y(gamma_w(t))=exp((ell+1)*t)*(exp(ell*t)-2)`.

The first selected zero has only logarithmic counting weight.  The second has the full lattice
`t=1+2*pi*I*k/ell`, and

`T(r,exp(ell*t))=ell*r/pi`,
`N(r,1/(exp(ell*t)-2))=ell*r/pi+O(log r)`.

It saturates the characteristic rather than violating it.  The derivative of the original
pullback at `t=1`, equivalently the value there after division by `t-1`, is `4*e*ell`, already in
the nondiscrete field whose dimension is at issue.

For the period stress `z=(ell,omega)`, `omega=2*pi*I`, the two fixed value divisors pull back to
`exp(ell*t)-2` and `exp(omega*t)-1`.  Their zero counts have the sharp leading terms
`ell*r/pi` and `2*r`, respectively, equal to their characteristics.  A conditional rational
relation `P(ell,omega)=0` pulls back to the ordinary polynomial `P(t*ell,t*omega)` and contributes
only `O(log r)` at its finitely many radial zeros unless it vanishes identically.  The available
targets therefore either attain the ordinary SMT scale or are negligible; none creates an excess.

The algebraic-input equality case confirms that the issue is arithmetic, not growth.  For
Q-linearly independent algebraic `alpha_i`, the curve `gamma_alpha` has the same order-one
characteristic, and every equation `exp(alpha_i*t)=exp(alpha_i)` has a critical-density period
lattice.  The full field is not algebraic over an `(N-1)`-coordinate deletion: the missing
exponential adds the missing transcendence degree by Lindemann--Weierstrass.  Its proof supplies
arithmetic independence that the identical Nevanlinna growth calculation does not see.

Finally, the entire package except analyticity has an all-dimensional discontinuous exponential
counterfeit.  Take algebraically independent `T_1,...,T_(N-1)` and

`z_i=T_i (i<N)`,  `z_N=(product_(i<N)T_i)^(-1)`.

The `z_i` are Q-linearly independent: multiplying a rational linear relation by
`product T_i` gives a sum of distinct monomials and a constant.  They generate the function field
`F=Q(T_1,...,T_(N-1))`, of transcendence degree `N-1`.  For every rank-`N-1` rational linear map
`A`, its kernel is a line with direction `v!=0`; on a fiber, the equation `product_i z_i=1`
becomes

`product_i (x_i+s*v_i)-1=0`.

Its coefficient of `s^(#support(v))` is
`product_(v_i!=0)v_i * product_(v_j=0)x_j!=0`, so the generic fiber is finite.  Hence `F` is
algebraic over `Q(Az)` for every rational hyperplane projection.

Choose the `T_i` inside `C`.  Prescribe a group homomorphism from their rational span either by
`E(z_i)=c_i in Qbar^*` for the uniform algebraic-exponential branch, or by `E(z_i)=z_i` for the
fully transcendental branch, using compatible rational roots, and extend it to the additive group
of `C` because `C^*` is divisible.  In both cases

`td_Q Q(z,E(z))=N-1`,

and every transformed full field is algebraic over every rational hyperplane deletion; rational
transforms add only Kummer-algebraic exponential values.  The homomorphism can be forced
discontinuous by also choosing `a_m -> 0`, Q-linearly independent over the prescribed span, and
setting `E(a_m)=2`.  Thus the exact uniform defect-one and all-rational-deletion axioms are
algebraically consistent.  What the standard complex exponential adds is the radial entire curve,
but `(NC)` and `(BASE)` show that its one forced common point has zero asymptotic Nevanlinna mass.

Consequently a Cartan or interpolation proof would need a new arithmetic theorem making the
recovery divisors base-point-free with bounded complexity, making their moving coefficients small
relative to `gamma_z`, or making a nonzero jet determinant discrete.  Deletion algebraicity gives
none of these; in the mixed boundary the first option would already imply algebraic independence
of `e` and `log 2`.

### The entire rational-hyperplane package is automatic and admits bounded-degree countermodels

Let `z=(z_1,...,z_n)` be a first counterexample, put `y_i=exp(z_i)`, and let

`K=Q(z_1,...,z_n,y_1,...,y_n)`,  `trdeg_Q K=n-1`.

For every integer matrix `M in Mat_(r,n)(Z)` of rank `r<n`, define

`w_j=sum_i M_(j,i)z_i`,  `v_j=product_i y_i^(M_(j,i))=exp(w_j)`,
`K_M=Q(w_1,...,w_r,v_1,...,v_r)`.

The rows of `M` give a Q-linearly independent `r`-tuple `w`.  Minimality of the first failure
therefore gives `trdeg_Q K_M>=r`.  In particular, if `r=n-1`, then

`trdeg_Q K_M=n-1` and `K/K_M` is algebraic.                    `(RH)`

This is the higher-dimensional form of the whole rational-hyperplane package.  Clearing
denominators changes the corresponding exponential values only by adjoining roots, so integer
matrices lose no rational hyperplanes.  For lower rank one obtains only
`r<=trdeg_Q K_M<=n-1`; algebraicity of `K/K_M` is special to hyperplanes.

In arity two, for every primitive `(p,q) in Z^2`, `(RH)` reads

`K algebraic over F_(p,q)=Q(p*z_1+q*z_2,y_1^p*y_2^q)`.          `(S_(p,q))`

The infinite family is already automatic from the one-dimensional theorem.  Indeed
`p*z_1+q*z_2!=0` by rational linear independence.  If both it and its exponential were
algebraic, Hermite--Lindemann would force the linear form to be zero.  Hence
`trdeg_Q F_(p,q)>=1`; since `F_(p,q) subset K` and `trdeg_Q K=1`, equality and algebraicity
follow.  There is no extra compatibility assertion left after imposing all primitive slopes.

Even uniform boundedness of the extension degrees adds nothing in the curve case.  Work over an
algebraically closed constant field `k` and let `L=k(C)` be the function field of a smooth
projective curve carrying functions `X_1,X_2,Y_1,Y_2`.  Put

`A={m in Z^2:m dot X in k}`,  `B={m in Z^2:Y^m in k}`.

Assume `A intersection B={0}` and `rank A<=1`, as for a defect-one exponential locus.  Choose an
effective divisor `D` containing the pole divisors of `X_1` and `X_2`.  If a primitive `m` is not
in `A`, then

`[L:k(m dot X,Y^m)] <= [L:k(m dot X)]`
`                         = deg((m dot X)_infinity) <= deg D`.  `(BD)`

There are at most two primitive vectors in `A`, namely `a` and `-a`; for them `Y^a` is
nonconstant by `A intersection B=0`, and its fixed degree supplies the remaining bound.  Thus a
single constant bounds the degrees in all `(S_(p,q))`.  The rank condition is automatic for an
actual defect-one exponential curve: if both `X_i` were constant, their selected values would be
algebraic, and Lindemann--Weierstrass applied to all monomials in their exponentials would give
transcendence degree two, not one.

An exact abstract exponential model shows why neither these bounded maps nor product formulas can
produce a contradiction.  Let `T` be transcendental, take

`z_1=T`,  `z_2=T^(-1)`,  `E(z_1)=2`,  `E(z_2)=3`,  `K=Q(T)`,

and extend `E` multiplicatively on `Q*T+Q*T^(-1)` (using the positive rational powers of `2` and
`3`).  The inputs are Q-linearly independent and the exponential map is injective on their
rational span.  For every primitive `(p,q)`,

`f_(p,q)=p*T+q*T^(-1)=(p*T^2+q)/T`,
`E(f_(p,q))=2^p*3^q`,
`F_(p,q)=Q(f_(p,q))`.

If `p*q!=0`, then

`p*T^2-f_(p,q)*T+q=0`,
`[K:F_(p,q)]=2`,
`Tr_(K/F_(p,q))(T)=f_(p,q)/p`,  `Nm_(K/F_(p,q))(T)=q/p`.       `(Q_(p,q))`

The nontrivial involution is `T |-> q/(p*T)`.  On the two primitive coordinate slopes the degree
is one.  Thus all infinitely many hyperplane fields occur simultaneously with degree at most two.
Two nonparallel slopes already recover the full field: if `Delta=p*s-q*r!=0`, then

`T=(s*f_(p,q)-q*f_(r,s))/Delta`,
`T^(-1)=(-r*f_(p,q)+p*f_(r,s))/Delta`.

The exact height bookkeeping is equally harmless.  As a map of projective lines,

`f_(p,q):[X:Y] |-> [p*X^2+q*Y^2:X*Y]`

has geometric degree two and logarithmic coefficient height
`log max(1,|p|,|q|)` when `p*q!=0`.  Over `Qbar`,

`div(f_(p,q))=[sqrt(-q/p)]+[-sqrt(-q/p)]-[0]-[infinity]`,

so the function-field product formula has the same two zeros and two poles for every slope.  The
projected exponential is a constant and has function-field height zero.  Its arithmetic Weil
height is exactly

`h(2^p*3^q)`
` =max(p_+*log 2+q_+*log 3, p_-*log 2+q_-*log 3)`,

where `a_+=max(a,0)` and `a_-=max(-a,0)`.  Hence arithmetic coefficient heights grow with the
slope rather than lying in a Northcott-bounded set.  Product formulas for `(Q_(p,q))` are separate
norm identities over different fixed fields; they do not sum to a relation in `K`.

The same counterfeit works in every dimension with uniformly bounded geometric degree.  Let

`H_n: product_i X_i=1`,  `K=Q(H_n)`,

take its generic point `z`, choose multiplicatively independent rational constants `c_i` (for
example distinct primes), and set `E(z_i)=c_i`.  Extend this assignment to the rational span.
Then `trdeg_Q K=n-1`, the `z_i` are Q-linearly independent, and for every rank `n-1` matrix `M`,

`K_M=Q(M*z,c^M)` and `K/K_M` is finite.

If the primitive kernel vector of `M` is `a=(a_1,...,a_n)`, a generic fiber is the line
`x=x_0+t*a`; substituting in `product_i x_i=1` gives

`product_i (x_(0,i)+t*a_i)-1=0`.

Consequently

`[K:K_M]=#{i:a_i!=0}<=n`.                                      `(HD)`

The coordinates `a_i` are signed maximal minors of `M` up to their common gcd.  If
`max|M_(j,i)|<=H`, Hadamard's inequality gives

`log max_i|a_i| <= (n-1)log H+((n-1)/2)log(n-1)`.

Thus the fiber degree remains at most `n` while the coefficient heights grow only logarithmically
in the additive projection and linearly in the exponents of the constants `c^M`.  This realizes
all of `(RH)`, including a uniform degree bound far stronger than minimality provides.

Finally the infinite package cannot force a nonzero graph-compatible derivation.  In the model,
every `E(z_i)=c_i` is constant.  A Q-derivation `D` satisfying
`D(E(z_i))=E(z_i)D(z_i)` must therefore have `D(z_i)=0` for all `i`, and hence `D=0` on `K`.
Differentiating every projected identity gives only the same equations
`D(c^m)=c^m D(m dot z)=0`.  The package is compatible with no nontrivial graph tangent at all.

The route is therefore closed.  Infinite rational shears, bounded-degree maps, their exact norms,
and function-field product formulas merely restate proper rotundity at every rational
hyperplane.  The abstract hypersurface models satisfy the entire family with stronger uniform
degree control, so an argument that distinguishes the complex exponential must add genuinely
analytic information not present in the rational-hyperplane algebraicity data.

### Least fully transcendental failures have exact defect one

The new equivalence

`Conjecture <-> FullyTranscendentalConjecture`                         `(FT)`

makes the proposed Lindemann--Weierstrass shift selection unnecessary.  It gives the following
strictly cleaner exact normal form.  Here `K(z)=Q(z_i,exp(z_i):i)`.

**Proposition (fully transcendental defect-one normal form).**  The negation of Schanuel's
conjecture is equivalent to the existence of `n>=1` and
`z:Fin(n+1)->C` such that

1. `z` is Q-linearly independent;
2. every `z_i` and every `exp(z_i)` is transcendental; and
3. `trdeg_Q K(z)=n`.

Moreover, the forward implication can choose `z` with `not Bound z` and with the restricted
predecessor statement

`forall w:Fin n->C, LI_Q(w) -> (forall i, w_i trans)`
`  -> (forall i, exp(w_i) trans) -> Bound(w)`.                          `(FTP)`

Proof: by `(FT)`, a failure of the full conjecture gives a fully transcendental failure.  Choose
the least failing arity `M`.  Arity zero cannot fail by `bound_zero`, so write `M=n+1`.  The
minimality of `M` is exactly `(FTP)`.  Restrict `z` along `Fin.castSuccEmb`.  Linear independence
and both coordinatewise transcendence conditions survive restriction, so `(FTP)` and
`trdeg_comp_le` give

`n <= trdeg_Q K(z|Fin n) <= trdeg_Q K(z)`.                              `(LOW)`

On the other hand, failure says

`trdeg_Q K(z) < (n+1 : Cardinal) = succ(n : Cardinal)`.

Thus `Order.lt_succ_iff` gives `trdeg_Q K(z)<=n`; together with `(LOW)` this is the asserted
equality.  Conversely, an independent `(n+1)`-tuple with transcendence degree `n` contradicts
the Schanuel bound, so the displayed existential condition implies failure without using its
extra transcendence clauses.

There is no endpoint gap.  The `M=0` exclusion is made before applying
`Nat.exists_eq_succ_of_ne_zero`.  The cardinal argument itself remains valid when its predecessor
`n` is zero: `td<succ(0)` implies `td<=0`.  In fact the output can be strengthened to `n>0`, since
if `n=0` then `z` is a singleton and transcendence of its sole coordinate makes that singleton
algebraically independent, whence `bound_of_algebraicIndependent_coordinate` contradicts the
failure.  Thus the first fully transcendental failure has arity at least two.

For every *coordinate deletion* `f:Fin n hookrightarrow Fin(n+1)`, the same argument gives

`trdeg_Q K(z o f)=trdeg_Q K(z)=n`,

and the transcendence-degree tower formula then shows that `K(z)` is algebraic over
`K(z o f)`.  The qualification is essential: a rational linear combination of fully
transcendental coordinates can itself, or after exponentiation, be algebraic.  Least arity only
inside the fully transcendental branch therefore does not by itself give the corresponding
statement for every rational-hyperplane projection.

The earlier shift construction is nevertheless correct, but weaker for minimality.  Given a
length-`m` independent tuple `u` with algebraic exponentials and `trdeg_Q K(u)=m-1`, choose `m`
Q-linearly independent algebraic numbers `a_j` (for example the first `m` powers of an algebraic
number of degree at least `m`).  Lindemann--Weierstrass, applied to all distinct integral linear
combinations of the `a_j`, makes the `exp(a_j)` algebraically independent.  Hence at least one
`exp(a)` is transcendental over `K(u)`; it stays transcendental over `K(u)(a)` because `a` is
algebraic.  If `a` lay in the rational span of `u`, clearing denominators and exponentiating
would make `exp(a)` algebraic, so `(a,u)` is independent.  The two integral shears give

`w=(u_0+2a,u_0+a,u_1+a,...,u_(m-1)+a)`.

Hermite--Lindemann first makes each `u_i` transcendental (independence excludes zero), and then
every displayed coordinate and exponential of `w` is transcendental.  The inverse formulas

`a=w_0-w_1`,  `u_0=2w_1-w_0`,  `u_i=w_(i+1)-a`

and `exp(a)=exp(w_0)/exp(w_1)` show

`K(w)=K(u)(a,exp(a))`,  hence `trdeg_Q K(w)=m`.

Thus this augmentation also produces a fully transcendental defect-one tuple of length `m+1`.
For `m=1` the same two-coordinate formulas are valid, although the assumed source witness is
already ruled out by the unconditional singleton theorem.  The construction increases arity and
does not retain least-arity predecessor minimality, which is why the direct least-failure proof
from `(FT)` is the sharp statement.

This is now formalized in
[`Schanuel/MinimalCounterexampleFullyTranscendental.lean`](./Schanuel/MinimalCounterexampleFullyTranscendental.lean).
Besides `FullyTranscendentalFailureAt` and the least-failure theorem, the module proves the
strengthened witness with `n>0`, the exact deletion transcendence degree, algebraicity of the
full field over every deletion field, and the exact equivalence

`not Conjecture <-> exists n z, 0<n and LI_Q(z)`
`  and (forall i, z_i trans) and (forall i, exp(z_i) trans) and DefectOne(z)`.

The proof uses only `conjecture_iff_fullyTranscendental`, `bound_zero`, the singleton algebraic-
independence bound, `trdeg_comp_le`, the transcendence-degree tower formula, and the existing
finite-cardinal successor calculation.

### Divisorial valuations do not couple to the selected archimedean exponential modulus

Take a fully transcendental first failure, so

`K=Q(z_1,...,z_n,y_1,...,y_n)`,  `y_i=exp(z_i)`,  `trdeg_Q K=n-1`,

and every displayed `z_i,y_i` is transcendental.  On a normal projective Q-model `B` of `K`, a
prime divisor `xi` gives the valuation vector

`u_xi=(ord_xi(z_1),...,ord_xi(z_n);ord_xi(y_1),...,ord_xi(y_n)) in Z^(2n)`. `(V)`

For a rank-`r` integer matrix `M`, put `w=M*z` and `v=y^M`.  The valuation transformation is
asymmetric:

`ord_xi(v_j)=sum_i M_(j,i)ord_xi(y_i)`,
`ord_xi(w_j)>=min_(M_(j,i)!=0) ord_xi(z_i)`.                    `(TV)`

Equality in the second formula fails exactly when the terms of least order cancel in the residue
field.  Thus a rational additive shear is not the linear map `M` on tropical weights, whereas its
multiplicative half is linear.  The rational-hyperplane package says only that for
`rank M=n-1` the inclusion

`Q(w,y^M) subset K`

is finite.  Consequently each divisorial valuation of `K` restricts to one on the projected
field with a finite ramification index.  It imposes no equality or inequality between the two
halves of `(V)`.  For lower-rank matrices, minimality gives only the corresponding projection-rank
inequality.  This is exactly the tropical algebraic-matroid data: projection dimensions and
finite pullback of divisors, with no graph-compatible valuation rule.

In arity two the picture can be computed completely.  A normal projective model is a curve, and
the fully transcendental hypothesis makes the algebraic matroid on
`{z_1,z_2,y_1,y_2}` the rank-one matroid with no loops: every singleton has rank one and every
pair is algebraically dependent.  For every polynomial relation `P`, a valuation vector `u`
lies in its tropical hypersurface precisely when the minimum of the weights of the monomials in
the Newton polytope of `P` is achieved at least twice.  This condition contains no trace of
`y_i=exp(z_i)` at one complex embedding.

The following fully transcendental counterfeit realizes the whole fan and also the full
archimedean modulus identities.  In `K=Q(T)`, set

`x_1=T`,  `x_2=T^(-1)`,
`Y_1=(T-1)/(T+1)`,  `Y_2=(T-2)/(T+2)`.                         `(C)`

The inputs are Q-linearly independent, and `Y_1,Y_2` are multiplicatively independent by their
distinct zero and pole divisors.  Hence the assignment `E(x_i)=Y_i` extends injectively on
`Q*x_1+Q*x_2`, after choosing compatible rational roots.  All four functions are nonconstant,
and their field has transcendence degree one.

The prime ideal of `(C)` is

`I=(X_1*X_2-1, Y_1*(X_1+1)-(X_1-1), Y_2*(X_1+2)-(X_1-2))`.    `(NI)`

After eliminating `X_2`, each of the last two relations has the square Newton polygon with
support `{1,X_1,Y_i,X_1*Y_i}`.  The nonzero divisorial valuation vectors are exactly

`u_0       =( 1,-1, 0, 0)`,  `u_infinity=(-1, 1, 0, 0)`,
`u_1       =( 0, 0, 1, 0)`,  `u_(-1)    =( 0, 0,-1, 0)`,
`u_2       =( 0, 0, 0, 1)`,  `u_(-2)    =( 0, 0, 0,-1)`.       `(FAN)`

They give three complete tropical lines, all with weight one, and balance exactly:
`sum_a u_a=0`.  Coordinatewise this is just the product formula for the four principal
divisors.  It is a rank-one tropical realization with four nonloops, exactly the matroid shape of
a fully transcendental defect-one quadruple.

For every primitive slope `(p,q)`, the projected functions are

`w_(p,q)=p*T+q*T^(-1)`,
`eta_(p,q)=Y_1^p*Y_2^q`.

The field `K` has degree at most two over `Q(w_(p,q),eta_(p,q))`, because it already has degree at
most two over `Q(w_(p,q))`.  In fact the projected field equals `K` for every primitive slope.
This is immediate on the coordinate slopes.  If `p*q!=0`, then `K/Q(w_(p,q))` is quadratic with
involution `T |-> q/(p*T)`.  Were `eta_(p,q)` fixed, its divisor would be invariant.  Invariance
of its support `{1,-1,2,-2}` first forces `|q/p|=2`, while comparison of the coefficients at the
interchanged points then gives `|p|=|q|`, a contradiction.  Hence `eta_(p,q)` separates the two
quadratic sheets and

`Q(w_(p,q),eta_(p,q))=K` for every primitive `(p,q)`.            `(EQ_(p,q))`

For `p*q!=0`, the two relevant principal divisors are exactly

`div(w_(p,q))=[sqrt(-q/p)]+[-sqrt(-q/p)]-[0]-[infinity]`,
`div(eta_(p,q))=p*([1]-[-1])+q*([2]-[-2])`.                    `(PF_(p,q))`

Both have degree zero separately.  As slopes vary, zeros of the additive form move through the
curve while the multiplicative divisor changes its integer weights.  Finite algebraicity of every
slope field provides no term that pairs these two equations.  Possible coincidences of a moving
zero with `1,-1,2,-2` are isolated slope phenomena and still satisfy the same two product
formulas.

Now select the embedding `T |-> tau=i*pi`.  It is a field embedding because `pi` is
transcendental, and

`z_1=tau`,  `z_2=tau^(-1)`,
`y_1=(tau-1)/(tau+1)`,  `y_2=(tau-2)/(tau+2)`

are all transcendental.  The two inputs are Q-linearly independent: a relation between them
would make `pi^2` rational.  Each `y_i` is transcendental because solving its displayed Mobius
formula for `tau` would otherwise make `tau` algebraic.  Moreover

`|y_1|=|y_2|=1`,  `Re(z_1)=Re(z_2)=0`,

and therefore, simultaneously for every integer slope,

`log|eta_(p,q)|=0=Re(w_(p,q))`.                                `(ARCH)`

Thus `(C)` satisfies the entire divisorial fan, every rational-hyperplane algebraicity statement,
all product formulas, full transcendence of the four displayed values, and every archimedean
modulus identity that follows from `|exp z|=exp(Re z)`.  It is not the analytic exponential: the
missing information is precisely the phase and analytic compatibility.  Any argument using only
the proposed valuation and modulus data would also apply to `(C)` and hence cannot yield a
contradiction.

The Arakelov formulation makes the separation intrinsic.  For `d=trdeg_Q K`, choose a normal
projective arithmetic model and a nef smooth hermitian polarization
`Hbar_1,...,Hbar_d`.  For `f in K^*`, the principal arithmetic intersection identity is

`widehat_deg(widehat_div(f)*product_i Hbar_i)=0`.               `(APF)`

It expands into weighted codimension-one orders and an integral of `log|f|` over the complex
fiber against the smooth measure `product_i c_1(Hbar_i)`.  The chosen embedding `K -> C` is one
complex point and has measure zero.  The equalities `(ARCH)` therefore contribute no discrete
archimedean term to `(APF)`.  They are also only `n` real equalities: all rational-slope versions
are their integer linear combinations.

No Arakelov polarization is canonically selected by the exponential graph at that one point.
Giving the point positive mass requires a singular metric and adds its local Green/proximity
correction to `(APF)`; that correction is an uncontrolled pointwise value, not a consequence of
the divisorial orders.  The counterfeit `(C)` shows that even arranging all exponential modulus
equalities at the atom would leave the balanced fan unchanged.  Hence there is no global height
inequality stronger than the principal-divisor equality available from these data, and this
valuation/Arakelov route is closed.

### Fully transcendental defect one has an exact two-unit conjugation shortfall

The fully transcendental minimal-counterexample theorem permits a sharper conjugation audit than
the general factor-of-two observation above.  Let

`z_i=x_i+I*y_i`,  `x_i,y_i in R`,  `a_i=exp(z_i)`,

and suppose that `z=(z_1,...,z_n)` is the exact fully transcendental defect-one witness, so

`K=Q(z,a)`,  `td_Q K=n-1`,

while every `z_i` and every `a_i` is transcendental.  Put

`r=rank_Q{x_1,...,x_n}`,  `s=rank_Q{y_1,...,y_n}`.

The coefficient map

`Q^n -> span_Q(x) direct_sum span_Q(y)`,  `q |-> (q dot x,q dot y)`

is injective, because its kernel is exactly the space of rational relations on `z`.  Hence

`n <= r+s <= 2*n`.                                               `(CR1)`

This also computes exactly what rational shearing can accomplish.  Let

`R=ker(q |-> q dot y)`,  `I_0=ker(q |-> q dot x)`.

The vectors in `R` give real combinations of `z`, while those in `I_0` give purely imaginary
combinations.  They satisfy

`dim R=n-s`,  `dim I_0=n-r`,  `R intersection I_0=0`.

Consequently an invertible rational shear can have at most

`t=dim(R+I_0)=2*n-r-s`                                           `(CR2)`

rows which are individually real or purely imaginary, and this maximum is attained by taking
bases of `R` and `I_0` and extending their union to a basis of `Q^n`.  Thus every rational basis
has at least

`delta=(r+s)-n`                                                  `(CR3)`

genuinely mixed rows, and a completely split real/pure-imaginary basis exists exactly when
`r+s=n`.  This is an invariant count, not a qualitative overlap objection.

The polar field bookkeeping is equally exact up to algebraic extensions.  Let

`L=K*conj(K)`,  `F=K intersection conj(K)`,
`D=td_Q L`,  `J=td_Q F`.

Since

`a_i*conj(a_i)=exp(2*x_i)`,  `a_i/conj(a_i)=exp(2*I*y_i)`,

choose rational bases `u_1,...,u_r` of the `x_i` and `v_1,...,v_s` of the `y_i`.  Clearing the
finitely many rational denominators shows that

`Q(u_1,...,u_r,I*v_1,...,I*v_s,
   exp(u_1),...,exp(u_r),exp(I*v_1),...,exp(I*v_s))`

and `L` are algebraic over one another (adjoining `I` and the necessary roots is algebraic).
Thus `D` is exactly the transcendence degree of a rationally independent exponential tuple of
length `r+s`.  On the intersection side, clear denominators in bases of `R` and `I_0` to obtain
integer rows.  Their `t=2*n-r-s` combinations of `z` are rationally independent; every such
combination and its exponential belongs to both `K` and `conj(K)`.  Their generated field is
therefore a subfield of `F`.

The tower formula over `F`, followed by subadditivity over `F`, gives the unconditional inequality

`D=J+td_F L
  <=J+td_F K+td_F conj(K)
  =J+(n-1-J)+(n-1-J)=2*n-2-J`,

and hence

`D+J <= td_Q K+td_Q conj(K)=2*n-2`.                              `(CR4)`

The two auxiliary Schanuel targets have lengths `r+s` and `2*n-r-s`, whose sum is `2*n`.
Equivalently, their signed shortfalls obey

`[(r+s)-D]+[(2*n-r-s)-J]=2*n-(D+J) >= 2`.                       `(CR5)`

Thus conjugation of an exact defect-one witness is missing at least two full transcendence units,
not an unspecified overlapping contribution.  Proving Schanuel separately for the compositum
basis and the intersection kernel basis would make both bracketed terms nonpositive and would
contradict `(CR5)`; that proposal is exactly two new Schanuel applications in disguise.  The
bound is sharp: the countermodels below have equality in `(CR4)` and each bracket in `(CR5)` is
exactly one.

There is also a sharp limit on the algebraic logarithm theorems available after shearing.  Define

`C_mul={q in Q^n:exp(q dot z) is algebraic}`.

This is a rational subspace.  Because every displayed `a_i` is transcendental, no standard basis
vector belongs to it, so `dim C_mul<=n-1`.  The maximum number of sheared rows which are real or
purely imaginary and simultaneously have algebraic exponential is exactly

`dim(C_mul intersection R)+dim(C_mul intersection I_0)
 <= min(n-1,2*n-r-s)`.                                         `(CR6)`

Baker's theorem upgrades any rationally independent selection of these logarithms of algebraic
numbers to linear independence over `Qbar`; the toric analytic subgroup theorem gives the same
kind of algebraic-subgroup exclusion.  Neither gives ordinary transcendence degree equal to the
number of logarithms.  In particular, `(CR6)` says that no rational shear of the fully
transcendental tuple can even turn all `n` multiplicative coordinates into an algebraic torus
point.  The exact period subspace

`{q:q dot z belongs to 2*pi*I*Q}`

has dimension at most one, by injectivity of `q |-> q dot z`.  Unit-circle values therefore do
not manufacture several independent period directions.  If additive-algebraic directions are
also allowed, the additive and multiplicative algebraic kernels are disjoint by
Hermite--Lindemann and their dimensions sum to at most `n`.  Equality can occur, but the analytic
subgroup theorem then supplies only its usual algebraic-subgroup constraints on the algebraic
point.  It cannot even make several algebraic additive coordinates `Qbar`-linearly independent,
and its logarithmic linear conclusions remain compatible with ordinary transcendence degree one.

The actual exponential stresses attain this stopping point exactly.  For `ell=log 2`, the fully
transcendental mixed presentation

`w=(2*ell+1,ell+1)`,  `exp(w)=(4*e,2*e)`

is real, so `(r,s,t)=(2,0,2)` and `K=conj(K)=Q(ell,e)`.  Under the hypothetical defect-one
relation `td_Q Q(ell,e)=1`, one has `D=J=1`, and `(CR5)` is the exact split `1+1=2`.  The
unimodular shear

`(w_0,w_1) |-> (2*w_1-w_0,w_0-w_1)=(1,ell)`

changes the exponentials to `(e,2)`.  It exposes one algebraic logarithm direction, on which
Hermite--Lindemann/Baker gives the already-known transcendence of `ell`, while the missing
relation between `ell` and `e` is untouched.  No unit-circle direction exists.

For the period stress `omega=2*pi*I`, augmentation gives the unconditionally fully
transcendental triple

`w=(ell+2,ell+1,omega+1)`,  `exp(w)=(2*e^2,2*e,e)`.

Here `(r,s,t)=(2,1,3)` and `K=conj(K)=Q(ell,omega,e)`.  The determinant-one integer shear with
rows

`(1,-1,0)`, `(-1,2,0)`, `(-1,1,1)`

sends it exactly to `(1,ell,omega)` with exponentials `(e,2,1)`.  Baker's theorem gives the
`Qbar`-linear independence of the logarithms `ell,omega`; it gives no algebraic independence of
`e,ell,omega`.  If the displayed fully transcendental triple were defect one, then again
`D=J=2`, while both auxiliary rank targets equal three, so `(CR5)` is again exactly `1+1=2`.

Finally, two explicit fully transcendental abstract exponentials saturate every piece of the
real/polar data.  Choose a positive real transcendental `T`.  On

`V=Q*T+Q*T^(-1)`

set

`E(q*T+r*T^(-1))=T^q*(T+1)^r`,

using the coherent positive rational roots, and extend to `(C,+)` because `C^*` is divisible.
The inputs `(T,T^(-1))` and their displayed `E`-values `(T,T+1)` are all transcendental and the
inputs are rationally independent, but

`Q(T,T^(-1),E(T),E(T^(-1)))=Q(T)`

has defect one.  It is fixed by conjugation, all rational shears remain real with positive real
`E`-values, `(r,s)=(2,0)`, and `(D,J)=(1,1)`.  Thus both brackets of `(CR5)` equal one even in the
strongest all-real polar branch.  On the prescribed span, `E` also commutes with conjugation.

For a split real/unit-circle counterfeit, put

`z=(T,I*T^2)`,  `U=(T-I)/(T+I)`,  `E(T)=T`,  `E(I*T^2)=U`.

The divisor valuations at `0,I,-I` show that `T` and `U` are multiplicatively independent; choose
coherent rational roots and extend the resulting homomorphism.  Both inputs and both exponential
values are transcendental, `|U|=1`, and

`K=Q(I,T)`,  `td_Q K=1`,  `K=conj(K)`,
`(r,s,t)=(1,1,2)`,  `(D,J)=(1,1)`.

This realizes a completely split real/pure-imaginary basis, a positive polar value and a
unit-circle polar value; on its rational span, `E(conj(v))=conj(E(v))` and the modulus/phase
factorization is exact.  It still saturates `(CR4)` and `(CR5)`.  Baker and the analytic subgroup
theorem are inapplicable precisely because the polar values are transcendental.  Therefore the
route is closed: realification and polar decomposition provide the exact invariant counts
`(CR1)--(CR6)`, but the analytic compatibility capable of ruling out these saturated abstract
characters is the original pointwise exponential relation, not a consequence of conjugation,
positivity, rational shearing, or the unconditional theory of algebraic logarithms.

### Multiplication images are an unbounded moving-target package

Let `m=n+1>=2`, let

`G=Ga^m x Gm^m`,  `[k](x,y)=(k*x,y^k)`,  `Gamma={(x,exp(x))}`,

and let `W` be the irreducible Q-locus of a positive fully transcendental defect-one point
`P=(z,exp(z))`.  Thus `dim W=m-1`, `[k](Gamma)=Gamma`, and

`[k]P in W_k intersect Gamma`,  where `W_k=[k]W`.                       `(MD1)`

The degree calculation is exact.  Compactify in `X=(P^1)^(2m)`, let `A` be the sum of the
hyperplane classes in the additive factors, `T` the corresponding sum in the toric factors, and
put `H=A+T`.  The multiplication map extends to a finite morphism with

`[k]^*H=A+k*T`.

If `d=dim W=m-1` and `delta_k` is the generic degree of `W -> W_k`, the projection formula gives

`delta_k*deg_H(W_k)=((A+k*T)^d . [W])`
` =sum_(j=0)^d binom(d,j) k^j (A^(d-j)*T^j . [W])`.                    `(MD2)`

This is the usual degree projection formula for a generically finite map; compare the
[Stacks Project, Lemma 33.45.7](https://stacks.math.columbia.edu/tag/0BET).  There is also an exact
stabilizer interpretation.  If `S=Stab_G(W)`, then

`delta_k=#(S intersect ({0}^m x mu_k^m))`.                             `(MD3)`

Indeed, the fiber through a generic `p in W` consists of `p+t` for `t in ker[k]`.  A fixed `t`
occurs generically exactly when `W+t=W`; otherwise `W intersect (W-t)` is proper.  If the toric
part of `S^0` has dimension `s`, `(MD3)` is `k^s` times a bounded periodic factor.  Thus the
degree of `W_k` is a nonnegative intersection polynomial of degree at most `d`, divided by the
torsion-stabilizer factor.  In particular

`deg_H(W_k)=O_W(k^(m-1))`.                                            `(MD4)`

The same compactification gives only growing arithmetic complexity.  The coordinate formulas
for `[k]` have degree at most `k` and logarithmic coefficient height `log k`; standard Chow-form
elimination (or the arithmetic projection formula) gives the coarse bound

`h_H(W_k)=O_W(k^m log k)`.                                            `(MD5)`

Neither `(MD4)` nor `(MD5)` places the images in a bounded-degree, bounded-height Hilbert or
Chow family.  A canonical-height argument is weaker still: the fully transcendental point `P`
is not a `Qbar`-point, and `H` is not polarized by a fixed multiplier because
`[r]^*H=A+r*T`, not `qH`.

The graph intersections in `(MD1)` do not meet the hypotheses of dynamical Mordell--Lang.  For
a fixed `r>=2` one has

`[r^j]P in W_(r^j)`,

but the target changes with `j`.  Dynamical Mordell--Lang fixes one self-map, one orbit, and one
closed target; see Bell--Ghioca--Tucker's
[formulation](https://arxiv.org/abs/1401.6659).  Pulling back the moving target merely recovers
the tautology `P in W`.  The increasing degrees also prevent packaging all `W_(r^j)` in one
finite-type Hilbert component.

Nor does a single repetition have the claimed rigidity.  If `W_(ak)=W_k`, then `W_k` is
`[a]`-invariant, but `G` is not semiabelian: its additive factor admits arbitrary homogeneous
cones.  For example

`{x_1*x_2=x_3^2} x {1}^3 subset Ga^3 x Gm^3`

is irreducible, invariant under every `[a]`, has trivial additive translation stabilizer, and is
not a subgroup or a coset.  The invariant-subvariety results that produce translates of
subgroups require a semiabelian ambient variety (and further hypotheses); compare
[Pink--Roessler](https://www.ams.org/jag/2004-13-04/S1056-3911-04-00368-6/).  If merely
`W_k=W_l` with neither index an integral multiple of the other, even invariance does not follow:
one obtains only `[l]W_k=[k]W_l`.

The checked fully transcendental mixed boundary makes the moving-target defect concrete.  Put

`a=log 2`,
`P_mix=(2*a+1,a+1;4*e,2*e)`.

If this point were defect one, its Q-locus would be a curve.  Its additive projection is the
line `X_1-2*X_2=-1`, while the additive projection of `W_k` is

`X_1-2*X_2=-k`.                                                       `(MD6)`

Hence all positive-index images `W_k` are pairwise distinct, even though each contains the graph
point

`[k]P_mix=(2*k*a+k,k*a+k;(4*e)^k,(2*e)^k)`.

The unknown algebraic relation between `a` and `e` supplies no second point on any one of these
curves and no fixed target to which a zero estimate or dynamical theorem applies.

There is a sharp purely algebraic counterfeit with exact degree and height growth.  Choose a
transcendental `t in C`, set

`z=(t,t^(-1))`,  `y=(t+1,t+2)`,

and let `W subset Ga^2 x Gm^2` be the rational curve

`X_1*X_2=1`,  `Y_1=X_1+1`,  `Y_2=X_1+2`.                              `(MD7)`

The two inputs are Q-linearly independent, all four displayed entries are transcendental, and
`Q(z,y)=Q(t)` has transcendence degree one.  Choose logarithms `ell_i` of `y_i`, define a
Q-linear map `L` by `L(t)=ell_1`, `L(t^(-1))=ell_2`, and extend it on a Hamel basis so that it is
discontinuous.  Then

`E(x)=exp(L(x))`

is a discontinuous exponential homomorphism with `E(z_i)=y_i`.  (If `E` were continuous, its
continuous lift on the simply connected additive group would differ from `L` by an additive map
to `2*pi*I*Z`; divisibility forces that difference to vanish, contradicting the choice of `L`.)

The image `W_k` has the parametrization

`(k*t,k/t;(t+1)^k,(t+2)^k)`

and the exact affine equations

`X_1*X_2=k^2`,
`k^k*Y_1=(X_1+k)^k`,
`k^k*Y_2=(X_1+2*k)^k`.                                                `(MD8)`

Its stabilizer is trivial: translation invariance of the additive hyperbola forces both additive
translations to vanish, after which the two nonconstant `Y`-coordinates force both toric
multipliers to be one.  Thus `delta_k=1`.  In the Segre polarization, the parametrizing
coordinate degrees are `1,1,k,k`, so `(MD2)` is the exact identity

`deg_H(W_k)=2+2*k`.                                                    `(MD9)`

The three equations in `(MD8)` have degrees `2,k,k` and exact logarithmic coefficient heights
`2*log k`, `k*log k`, and `k*log(2*k)`, respectively: in each binomial expansion the constant
coefficient is maximal.  Finally `W_k!=W_l` for positive `k!=l`, already because their additive
projections satisfy `X_1*X_2=k^2` and `X_1*X_2=l^2`.  Nevertheless every `[k](z,E(z))` lies on
both `W_k` and the graph of `E`.

This counterfeit realizes the full multiplication-image, stabilizer, degree, height, and graph-
intersection package with defect one and no subgroup relation.  The route is therefore closed:
the infinitely many intersections are one tautological point on each of infinitely many targets.
To distinguish the usual exponential one would need a genuinely analytic moving-target theorem
that identifies or couples different `W_k`; neither algebraic dynamics, canonical heights, nor
the current minimality data supplies such a coupling.

### Lattice-box incidence sees at most the single period rank, not transcendence defect

Let `z=(z_1,...,z_n)` be the positive fully transcendental defect-one witness, write
`y_i=exp(z_i)`, and put

`K=Q(z,y)`,  `td_Q K=n-1`.

For `I_N={-N,...,N}`, `L_N=2*N+1`, and `M_N=I_N^n`, consider the two boxes

`A_N={m dot z:m in M_N}`,  `Y_N={y^m:m in M_N}=exp(A_N)`.

Rational linear independence makes `m |-> m dot z` injective, so

`|A_N|=L_N^n`.                                                   `(AC1)`

All collisions on the multiplicative side are computed by the period lattice

`Lambda={k in Z^n:y^k=1}
       ={k in Z^n:k dot z belongs to 2*pi*I*Z}`.                 `(AC2)`

The map `k |-> (k dot z)/(2*pi*I)` embeds `Lambda` in `Z`; hence
`rho=rank_Z Lambda` is zero or one.  If `rho=0`, then `|Y_N|=L_N^n`.  If
`Lambda=Z*lambda` is nonzero, every collision fiber is a segment parallel to `lambda`, and

`|M_N|/(1+floor(2*N/||lambda||_infinity)) <= |Y_N|`,
`|Y_N|=Theta_lambda(N^(n-1))`.                                  `(AC3)`

Thus the exact multiplicative rank is

`rank_Z <y_1,...,y_n>=n-rho>=n-1=td_Q K`.                       `(AC4)`

This is the sharp collision conclusion.  In the period case it merely matches the defect-one
transcendence degree, and with no period it exceeds that degree by one without contradiction:
a field of transcendence degree `n-1` can contain multiplicative subgroups of arbitrarily large
finite rank.

The group energies are also explicit.  For an interval of length `L=L_N`, set

`Q_N(0)=#{a,b,c,d in I_N:a+b=c+d}=(2*L^3+L)/3`.

Then

`E_+(A_N)=Q_N(0)^n`.                                            `(AC5)`

If `Lambda=0`, unique exponent vectors give the identical formula

`E_x(Y_N)=Q_N(0)^n`.                                            `(AC6)`

More generally, if `Lambda=Z*lambda` and

`Q_N(t)=#{a,b,c,d in I_N:a+b-c-d=t}`,

the multiplicative energy of the box counted with its exponent-vector multiplicities is exactly

`sum_(j in Z) product_(i=1)^n Q_N(j*lambda_i)`.                 `(AC7)`

The corresponding three-term incidence count is just as sharp.  In one coordinate,

`#{a,b in I_N:a+b in I_N}=3*N^2+3*N+1`;

hence

`#{(a,b,c) in A_N^3:a+b=c}=(3*N^2+3*N+1)^n`,                  `(AC8)`

and, when `Lambda=0`, the same formula holds for
`#{(a,b,c) in Y_N^3:a*b=c}`.  These are constant-proportion quadratic incidence counts.  They
occur on the algebraic group-law surfaces `X+Y=Z` and `X*Y=Z`, precisely the group-like exceptional
surfaces in the Elekes--Szabo mechanism; they are not forbidden incidences.

Sum-product gives the complementary expansion and is again saturated rather than contradicted.
The set `A_N` has

`|A_N+A_N|=(4*N+1)^n=Theta_n(|A_N|)`,

so complex sum-product estimates only force `A_N*A_N` to be large; all of those products remain
perfectly valid elements of `K`.  Conversely,

`|Y_N*Y_N|=Theta_(z,n)(|Y_N|)`.                                 `(AC9)`

The Evertse--Schlickewei--Schmidt theorem for linear equations in a finite-rank multiplicative
group gives a stronger exact qualitative complement.  After dividing
`u_1+u_2=u_3+u_4` by `u_4`, its nondegenerate solutions are bounded solely in terms of the rank
`n-rho`; degenerate subsums contribute `O(|Y_N|^2)`.  Therefore

`2*|Y_N|^2-|Y_N| <= E_+(Y_N) <= C_n*|Y_N|^2`,
`|Y_N+Y_N|=Theta_n(|Y_N|^2)`.                                  `(AC10)`

Thus `A_N` is maximally additively structured and expands multiplicatively, whereas `Y_N` is
maximally multiplicatively structured and expands additively.  A sum-product theorem concerns
one set under both operations; it cannot combine the small additive doubling of `A_N` with the
small multiplicative doubling of the different set `Y_N`.  The exponential bijection between
them is an additive-to-multiplicative group homomorphism, and every discontinuous character has
the same finite energy identities.

Low transcendence degree supplies no fixed bounded-degree incidence variety.  The joint point
`(z,y)` has a rational locus of dimension `n-1`, but the scalar pair

`(m dot z,y^m)`

is obtained from that locus by a different map for every `m`.  Even in arity two, where each
pair is algebraically dependent, its plane curve varies with `m`; in higher arity a pair need not
be algebraically dependent at all.  Elekes--Szabo requires one fixed bounded-degree polynomial
surface and independent Cartesian choices.  Here the only fixed surfaces visible to the boxes
are the two group laws already responsible for `(AC8)`, while the exponential graph relating
`A_N` and `Y_N` is analytic rather than algebraic.  Interpolation determinants do not repair
this: they are nonzero elements of the positive-dimensional field `K`, and the degrees and
heights of the moving orbit maps enter their constants.

The height growth makes the moving-complexity loss explicit.  On a fixed projective model of
`K`, nonarchimedean pole orders satisfy

`h_geom(m dot z)<=C_z`,  `h_ar(m dot z)<=C_z+O(log N)`,
`h_geom(y^m)<=sum_i |m_i| h_geom(y_i)=O(N)`,
`h_ar(y^m)=O(N)`.                                               `(AC11)`

The first bound is uniform because a pole of a linear combination can occur only at a pole of
one of the fixed `z_i`; the arithmetic coefficient contribution is `O(log N)`.  The
multiplicative divisor grows linearly with the exponents.  Northcott-type counting therefore has
exactly enough coefficient or divisor height to accommodate `N^n` elements and yields no
dimension contradiction.

The fully transcendental mixed stress realizes all the favorable incidence data with the actual
analytic exponential.  Put `ell=log 2` and

`w=(2*ell+1,ell+1)`,  `exp(w)=(4*e,2*e)`.

For `m=(a,b)` define the unimodularly related indices

`p=2*a+b`,  `q=a+b`.

Then

`m dot w=p*ell+q`,  `exp(m dot w)=2^p*e^q`.                    `(AC12)`

The numbers `2` and `e` are multiplicatively independent, so `Lambda=0`.  Both boxes have
exactly `L_N^2` elements, both structured energies are
`((2*L_N^3+L_N)/3)^2`, and both group-law triple counts are
`(3*N^2+3*N+1)^2`.  Under the hypothetical defect relation
`td_Q Q(ell,e)=1`, every one of these collision and incidence formulas remains unchanged.  If
`P(ell,e)=0` is the curve equation, the additive function `p*ell+q` has fixed geometric pole
degree and coefficient height `O(log N)`, while `2^p*e^q` has divisor degree `O(N)` and
coefficient height `O(N)`.  Eliminating through `P` for each `(p,q)` consequently produces moving
curves of degree/height growing with `N`, not one surface to which a uniform incidence theorem
applies.

There is an unconditional fully transcendental discontinuous counterfeit with the same sharp
counts.  Choose a positive real transcendental `T`, set

`z=(T,T^(-1))`,  `E(T)=T`,  `E(T^(-1))=T+1`,

and define

`E(a*T+b*T^(-1))=T^a*(T+1)^b` for `a,b in Q`

using coherent positive roots.  Extend this homomorphism to `(C,+)`; to force discontinuity,
also choose rationally independent `c_j -> 0` over the prescribed span and impose `E(c_j)=2`
before extending.  The inputs and exponential values are individually transcendental and the
inputs are rationally independent, but

`Q(z,E(z))=Q(T)`,  `td_Q Q(T)=1`.                               `(AC13)`

Here `Lambda=0`, so `(AC1)`, `(AC5)`, `(AC6)`, and `(AC8)` hold exactly with `n=2`, while
`(AC9)--(AC10)` hold in the rank-two group generated by `T,T+1`.  On `P^1`, the functions

`a*T+b*T^(-1)=(a*T^2+b)/T`

have geometric degree at most two and logarithmic coefficient height
`log max(1,|a|,|b|)`.  The exact divisor

`div(T^a*(T+1)^b)=a*[0]+b*[-1]-(a+b)*[infinity]`  (`a,b in I_N`)

has positive degree

`(|a|+|b|+|a+b|)/2 <= 2*N`.                                   `(AC14)`

Thus even uniform additive degree, linear multiplicative height, maximal structured energies,
quadratic complementary expansion, and exact additive-to-multiplicative incidence coexist in a
fully transcendental defect-one field.  The finite-box data use only the character law and not
holomorphic continuity.  This closes the route: incidence and sum-product machinery either sees
the rank-zero/one period kernel, lands on its allowed group-like exceptions, or pays the moving
degree/height of the rational locus.  None recovers the missing transcendence unit.

### Continuous exponential characters retain a Beltrami parameter

Continuity eliminates Hamel-basis pathologies, but it still does not characterize the complex
exponential.  There is an exact classification.

**Continuous-character lemma.**  Every continuous homomorphism

`E:(C,+)->(C^*,*)`

has a unique continuous lift `L:C->C` with `L(0)=0`, and there are unique `a,b in C` such that

`E(z)=exp(L(z))`,  `L(z)=a*z+b*conj(z)`.                               `(CC1)`

Indeed, `C` is simply connected, so the covering `exp:C->C^*` lifts `E`.  The function

`L(z+w)-L(z)-L(w) in 2*pi*I*Z`

is continuous and vanishes at `(0,0)`, hence is zero.  Thus `L` is continuous additive and
therefore R-linear; every real-linear endomorphism of `C` has the unique form in `(CC1)`.
Conversely every such formula is a continuous homomorphism.

The standard extra conditions cut out the parameters exactly:

`E(conj z)=conj(E(z))` for all `z`  iff  `a,b in R`;                    `(CC2)`

`|E(z)|=exp(Re z)` for all `z` iff

`Re(a+b)=1` and `Im(a-b)=0`;                                         `(CC3)`

positivity on the real axis and unit modulus on the imaginary axis are together equivalent to
`a,b in R`; exact agreement `E(x)=exp(x)` on the real axis then adds `a+b=1`.  Finally

`partial_z E=a*E`,  `partial_conj(z) E=b*E`,
`Jac_R(E)=|E|^2*(|a|^2-|b|^2)`.                                      `(CC4)`

Thus positive orientation is only `|a|>|b|`.  Under conjugation and real-axis normalization it
becomes

`a=1-b`,  `b in R`,  `b<1/2`,                                        `(CC5)`

an infinite family.  Its Beltrami coefficient is `mu=b/a`; positive Jacobian is exactly
`|mu|<1`, as in the standard
[Beltrami criterion](https://encyclopediaofmath.org/wiki/Quasi-conformal_mapping).

The Cauchy--Riemann condition is the genuinely new datum.  Since `E` never vanishes, CR at even
one point forces `b=0` in `(CC4)`, hence CR everywhere.  Exact modulus `(CC3)` then forces
`a=1`.  Equivalently, CR at one point, conjugation compatibility, and `E(1)=e` force
`E(z)=exp(z)`.  Without a normalization, holomorphicity gives only `E(z)=exp(a*z)`; even
`E(1)=e` alone permits `a=1+2*pi*I*N`.  This proves the precise rigidity lemma, but none of the
defect-one or deletion-algebraicity statements contains the derivative appearing in `(CC4)`.

There is already a continuous nonholomorphic defect-one model satisfying all the nondifferential
normalizations.  Let

`E_(1/2)(z)=exp(Re z)=exp((z+conj z)/2)`

and take

`z_1=1+I*e`,  `z_2=2+I*e^2`,  `E_(1/2)(z_1)=e`,  `E_(1/2)(z_2)=e^2`.  `(CC6)`

If `q*z_1+r*z_2=0`, real parts give `q=-2r`, and imaginary parts then give
`r*(e^2-2e)=0`; hence `q=r=0`.  All four displayed values are transcendental, while

`Q(z_1,z_2,E(z_1),E(z_2))=Q(I,e)`

has transcendence degree one.  Retaining the first pair gives `Q(z_1,e)=Q(I,e)`, while retaining
the second gives `Q(z_2,e^2)=Q(I,e^2)`, over which the full field is algebraic.  Thus `(CC6)`
realizes the positive fully transcendental defect-one package and algebraicity over every
one-coordinate deletion.  It also satisfies continuity, `E(1)=e`, conjugation compatibility,
positivity, and the exact usual modulus.  Its only visible failure is CR (and its real Jacobian
is zero).

Even positive orientation and quasiconformality do not repair this.  Consider the normalized
real-linear family

`E_s(z)=exp((1-s)*z+s*conj(z))`
`      =exp(x+I*(1-2s)*y)`,  `z=x+I*y`.                                `(CC7)`

For real `s<1/2`, the lift is orientation preserving and quasiconformal, with

`mu=s/(1-s)`,  `Jac(L_s)=1-2s`,

while every `E_s` satisfies conjugation, exact modulus, positivity, and `E_s(1)=e`.  Choose

`tau=e^4`,  `c=2*pi/tau`,  `s_0=(1-c)/2 in (0,1/2)`

and

`u_1=1+I*tau`,  `u_2=2+3*I*tau`.                                     `(CC8)`

Then `(1-2s_0)*tau=2*pi`, so

`E_(s_0)(u_1)=e`,  `E_(s_0)(u_2)=e^2`.

The real and imaginary parts show that `u_1,u_2` are Q-linearly independent.  Again all four
values are transcendental and the full field is `Q(I,e)`.  Retaining only the first pair gives
`Q(u_1,e)=Q(I,e)`, while retaining only the second gives `Q(u_2,e^2)=Q(I,e^2)`, because
`u_2-2=3*I*e^4`.  Thus the full field is algebraic over either deletion.  This is an
orientation-preserving, quasiconformal, continuous nonholomorphic defect-one counterfeit
satisfying every normalization in `(CC2)--(CC5)`.

The deformation `(CC7)` also gives an exact specialization obstruction.  Keep instead the fixed
tuple from `(CC6)` and put `c=1-2s`.  Its two exponential values are

`Y_1(c)=e*exp(I*c*e)`,  `Y_2(c)=e^2*exp(I*c*e^2)`.                     `(CC9)`

As entire functions of `c`, `Y_1,Y_2` are algebraically independent over `C`: distinct monomials
have frequencies `r*e+s*e^2`, and those frequencies are distinct because `e` is irrational.
Nevertheless at the collapsing parameter `c=0` one has the algebraic relation

`F(c)=Y_2(c)-Y_1(c)^2=0`.

More precisely,

`F(c)=e^2*(exp(I*c*e^2)-exp(2*I*c*e))`,
`F'(0)=I*e^2*(e^2-2e)!=0`.                                          `(CC10)`

Thus the special relation has intersection multiplicity exactly one and disappears immediately;
for real `c`, its zero set is the discrete lattice

`c*(e^2-2e) in 2*pi*Z`.                                               `(CC11)`

Functional algebraic independence along the parameter therefore gives no algebraic independence
at a selected parameter, and a defect at one parameter does not propagate to the holomorphic
endpoint `s=0`.  Standard upper semicontinuity of fiber dimension, for example
[Stacks Project, Lemma 37.30.5](https://stacks.math.columbia.edu/tag/0D4I), concerns fibers of a
fixed proper algebraic morphism.  The Q-Zariski locus of one numerically selected complex point
is not such a fiber invariant; `(CC10)` is a concrete simple-zero witness to the mismatch.

This route is therefore closed.  Continuity upgrades an abstract character to the two-parameter
real-linear form `(CC1)`, but modulus, conjugation, normalization, positive orientation,
quasiconformality, defect one, and deletion algebraicity still allow explicit countermodels.
Cauchy--Riemann at one point plus normalization does force the actual exponential, but that is
precisely the analytic datum absent from the algebraic package.  Once imposed, it identifies the
map without producing any new transcendence-degree inequality, and quasiconformal specialization
cannot transfer one because arithmetic point loci and their isolated relations are not
semicontinuous.

### The Fischler--Rivoal one-zero theorem is exactly conditional, univariate, and lost under elimination

Let `ell=log 2`, and suppose that a nonzero
`P(U,V) in Qbar[U,V]` satisfies `P(e,ell)=0`.  Consider the proposed system on `C^2`

`F(X,Y)=P(exp(X),Y),   G(X,Y)=exp(Y)-2,   H(X,Y)=X-1`.                `(ZR1)`

All three are multivariate exponential polynomials defined over `Qbar`, and `(1,ell)` is a
common zero.  However, the zero theorems in Section 4 of
[Fischler--Rivoal, *Zeros of E-functions and of exponential polynomials defined over
Qbar*](https://rivoal.perso.math.cnrs.fr/articles/Ezeros.pdf) concern only **one-variable**
functions

`f(T)=sum_i P_i(T)*exp(beta_i*T),   P_i in Qbar[T], beta_i in Qbar`.  `(ZR2)`

Their Theorem 4.1 says, **assuming Schanuel**, that two nonzero functions `(ZR2)` with a common
nonzero zero have a common nonunit exponential-polynomial divisor vanishing there.  Its proof
chooses a `Z`-basis `alpha_1,...,alpha_r` of the frequency module and invokes Schanuel to make the
relation ideal of

`(xi,exp(alpha_1*xi),...,exp(alpha_r*xi))`

a height-one prime, hence principal.  This is precisely the missing transcendence-dimension
estimate, so Theorem 4.1 cannot be used to prove it.  Their simple-zero Corollary 4.2, the
period/logarithm divisibility in Corollary 4.3 and Theorem 1.8, and the resulting one-zero
common-factor conclusions are conditional for the same reason.

The unconditional E-function results in that paper do not propagate the zero in `(ZR1)`.
Theorem 1.2 assumes the global quotient `L(g)/g` is entire; Theorem 1.5 assumes that *every* zero
of one globally bounded E-function has the same multiplicity `m>=2`, together with a differential
order bound.  At the mixed point the relevant zero is simple and transverse.  Indeed

`Jac_(X,Y)(H,G)(1,ell)=[[1,0],[0,2]],   det=2`.                       `(ZR3)`

Consequently `(H,G)` is the maximal ideal in the local analytic ring at `(1,ell)`.  More
explicitly, putting `u=X-1`, `v=Y-ell`, one has

`G=2*(exp(v)-1)=v*U(v),   U(0)=2`,
`F=H*A+(Y-ell)*C=H*A+G*(C/U)`                                      `(ZR4)`

for holomorphic germs `A,C`; the second equality uses `P(e,ell)=0`.  Thus

`(F,G,H)_(1,ell)=(G,H)_(1,ell)`

and the local intersection algebra has length one.  The hypothetical equation adds neither a
common hypersurface factor nor extra multiplicity to the already isolated point.

The global count is equally exact.  With `omega=2*pi*I`,

`Z(F,G,H)={(1,ell+k*omega): k in Z, P(e,ell+k*omega)=0}`.             `(ZR5)`

Writing `P(U,V)=sum_j a_j(U)V^j`, no nonzero `a_j` can vanish at the transcendental number `e`.
Hence `P(e,V)` is a nonzero polynomial of degree `deg_V P`, and `(ZR5)` has at most `deg_V P`
points.  This is strictly below the infinite-common-zero hypothesis in Shapiro's conjecture and
in the proved simple-factor case of
[van der Poorten--Tijdeman, *On common zeros of exponential polynomials*, Sections 1 and
4--5](https://www.e-periodica.ch/digbib/view?lang=en&pid=ens-001%3A1975%3A21%3A%3A31).
The latter proves that a simple one-variable exponential sum and an arbitrary one-variable
exponential polynomial with infinitely many common zeros have a nontrivial common divisor; the
paper identifies this special case with Skolem--Mahler--Lech.  Ritt's classical quotient theorem
for constant-coefficient exponential sums likewise assumes that a quotient is entire, i.e. global
containment of all denominator zeros with multiplicities, not one common zero
([Ritt, 1929](https://doi.org/10.1090/S0002-9947-1929-1501506-6)).

Eliminating `X` does not repair the hypotheses.  Evaluation modulo the analytic equation `H=0`
sends `exp(X)` to `e` and gives the univariate pair

`F(1,T)=P(e,T),   G(1,T)=exp(T)-2`,                                  `(ZR6)`

over `Qbar(e)`, not over `Qbar`.  This coefficient escape is unavoidable: if `P(e,T)` belonged
to `Qbar[T]`, then its root `ell` would be algebraic.  MacColl--Ritt factorization over `C` gives
no common nonunit factor in `(ZR6)`: every nonunit factor of the ordinary polynomial is, up to an
exponential unit, polynomial, whereas `exp(T)-2` has no nonconstant polynomial divisor.  The last
claim can also be checked directly: in an identity

`exp(T)-2=R(T)*sum_beta Q_beta(T)*exp(beta*T)`

with nonconstant `R`, linear independence of distinct exponential frequencies forces
`R*Q_1=1` and `R*Q_0=-2`, impossible in `C[T]`.  Fischler--Rivoal themselves record the sharp
complex-coefficient example

`exp(T)-e,   exp(sqrt(2)*T)-exp(sqrt(2))`,                             `(ZR7)`

which share `T=1` but have gcd one.  Formula `(ZR6)` lands in exactly the coefficient regime
where `(ZR7)` shows that a single zero has no factorization force.  Fixing `Y=ell` instead gives
coefficients in `Qbar(ell)`; a slice `X=T,Y=ell*T` puts the nonalgebraic frequency `ell` into the
exponential.  Every direct univariate reduction loses `(ZR2)` in one of these two ways.

The same obstruction survives the positive fully-transcendental normal form.  Put

`W_0=2*ell+1,   W_1=ell+1,   (exp(W_0),exp(W_1))=(4*e,2*e)`.          `(ZR8)`

The two inputs are `Q`-linearly independent, and all four displayed coordinates are
transcendental.  Moreover their generated field is exactly `Q(e,ell)`, so under the hypothetical
relation it has transcendence degree one: `(ZR8)` is the all-transcendental defect-one mixed
stress, not merely a change of notation.  The invertible rational shear

`X=2*W_1-W_0=1,   Y=W_0-W_1=ell`

turns `(ZR1)` into the `Qbar`-defined multivariate system

`F*=P(exp(2*V-U),U-V),`
`G*=exp(U-V)-2,`
`H*=2*V-U-1`.                                                        `(ZR9)`

At `(U,V)=(W_0,W_1)`, the determinant of the gradients of `(H*,G*)` is `-2`, so this is again a
reduced transverse point and `F*` is locally redundant.  Restricting to `H*=0` and setting
`T=U-V=V-1` reduces `(ZR9)` to exactly `(ZR6)`: the transcendental coefficient `e` reappears.
Thus augmentation and rational shearing do not bring the point into the univariate `Qbar`
theory.

This route is closed sharply.  Classical Ritt--Shapiro results require global divisibility or
infinitely many common zeros; the mixed system has a finite set bounded by `deg_V P` and a simple
local intersection.  The 2025 one-common-zero theorem has the desired arithmetic conclusion only
for univariate `Qbar`-defined functions and only after assuming Schanuel, while every elimination
of the mixed system introduces `e`, `ell`, or a nonalgebraic frequency.  In several variables an
isolated transverse common zero is the generic codimension-two behavior, not evidence for a
common factor.

### An extra local exponential equation vanishes in a length-one algebra

Let `m=n+1`, let `P=(z,exp(z))` be a positive fully transcendental defect-one witness, and let
`W subset Ga^m x Gm^m` be its Q-locus.  Then `dim W=m-1`, so at a smooth point its local ideal
has codimension `m+1`.  Choose rational polynomials `P_0,...,P_m` locally cutting `W` and pull
them back to the exponential graph:

`f_j(t)=P_j(z+t,exp(z+t))=P_j(z+t,exp(z)*exp(t))`.                     `(LR1)`

Writing `K=Q(z,exp(z))`, every Taylor coefficient of every `f_j` lies in `K`, and

`partial_i f_j(0)=P_(j,X_i)(P)+exp(z_i)*P_(j,Y_i)(P) in K`.           `(LR2)`

Suppose the graph intersection is nonsingular and isolated, so some `m` rows, say
`f_1,...,f_m`, have nonzero Jacobian determinant `J in K`.  Then the formal inverse-function
theorem gives the following exact local statement.

**Length-one residue lemma.**  In `K[[t_1,...,t_m]]`,

`(f_1,...,f_m)=(t_1,...,t_m)`,
`A=K[[t]]/(f_1,...,f_m)=K`.                                         `(LR3)`

Consequently every further germ `h` with `h(0)=0`, in particular the remaining pullback `f_0`,
already belongs to `(f_1,...,f_m)`, and

`K[[t]]/(f_0,f_1,...,f_m)=K`,  `length=1`.                           `(LR4)`

Multiplication by `f_0` on `A` is the zero map, so its trace, norm, determinant, characteristic
polynomial, and local resultant are respectively `0,0,0,T`, and `0`.  They are discrete but
tautological: they contain no information beyond `f_0(0)=0`.  This is simply the regular-system-
of-parameters situation; compare the
[Stacks Project definition](https://stacks.math.columbia.edu/tag/00KU).

For any numerator `g in K[[t]]`, the simple-zero Grothendieck residue is

`Res_0 (g(t) dt_1...dt_m/(f_1...f_m))=g(0)/J in K`.                   `(LR5)`

In particular the residue with numerator `f_0` is zero, while the residue of `1` need not even
be algebraic over Q.  Formula `(LR5)` is the standard change-of-coordinates formula for a simple
zero; see the local discussion in
[Residues and Hodge theory](https://www3.nd.edu/~lnicolae/residues.pdf).  Normalizing the
numerator to the Jacobian makes the residue equal to one, but then it is independent of both the
point and the extra equation.

The overdetermined Jacobian supplies only the same tautology.  Its `(m+1) x m` matrix has a
one-dimensional left kernel whose entries are its signed maximal minors.  By `(LR2)` those
coefficients lie in `K`, not in `Qbar`.  Equivalently, if `f_0` is the extra equation, then

`f_0=sum_(i=1)^m A_i(t)*f_i`,  `A_i(t) in K[[t]]`,                    `(LR6)`

and the constants `A_i(0)` are obtained by dividing Jacobian minors by `J`.  Rational ambient
coefficients therefore do not produce a rational conormal relation after evaluation at the
transcendental graph point.

The mixed boundary gives exact numerical formulas.  Put `a=log 2` and consider the point

`p=(x_0,x_1)=(2*a+1,a+1)`

and the three pullbacks

`F_1=x_0-2*x_1+1`,
`F_2=exp(x_0)-2*exp(x_1)`,
`F_3=P(exp(x_1)/2,x_1-1)`,                                           `(LR7)`

where the hypothetical rational polynomial relation is `P(e,a)=0`.  At `p`,

`grad F_1=(1,-2)`,  `grad F_2=(4*e,-4*e)`,
`grad F_3=(0,D)`,                                                     `(LR8)`

with

`D=e*P_U(e,a)+P_V(e,a)`.

Thus

`J_(1,2)=4*e`,  `J_(1,3)=D`,  `J_(2,3)=4*e*D`.                       `(LR9)`

The first pair is always transverse, and its exact residues are

`Res_p dx_0 dx_1/(F_1*F_2)=1/(4*e)`,
`Res_p F_3 dx_0 dx_1/(F_1*F_2)=0`.                                  `(LR10)`

The first value is transcendental by Hermite's theorem, so rational coefficients do not make a
selected local residue algebraic.  If `D!=0`, the other two simple residues are `1/D` and
`1/(4*e*D)`.  If `D=0`, those pairs are degenerate and may be nonisolated, but the transverse
pair `(F_1,F_2)` still generates the maximal ideal and adjoining `F_3` still leaves the length
equal to one.  No case gives a contradiction.

The signed-minor relation among the three rows in `(LR8)` is explicitly

`(4*e*D)*grad F_1-D*grad F_2+(4*e)*grad F_3=0`.                       `(LR11)`

Correspondingly, the first-order part of the exact ideal membership `(LR6)` is

`F_3=-D*F_1+(D/(4*e))*F_2+O((F_1,F_2)^2)`.                           `(LR12)`

All coefficients lie in the defect-one field `K=Q(a,e)`.  In this mixed stress each individual
displayed coordinate/exponential pair already generates `K`, so the deletion fields equal `K`
and trace or norm down to them is literally the identity.  In the general minimal witness,
`K` is finite algebraic over each deletion field, but tracing `(LR5)` only lands in that
transcendental deletion field; there is no finite extension `K/Q` over which an arithmetic trace
could be taken.

There is no hidden finite global resultant.  Set `v=x_1-1`; on `F_1=0`,

`F_2=e*exp(v)*(exp(v)-2)`.

Hence the common zeros of the first two equations are the infinite logarithmic lattice

`v=a+2*pi*I*N`,  `N in Z`,                                           `(LR13)`

and every one has the same local residue `1/(4*e)`.  At these points the third equation becomes

`P(e,a+2*pi*I*N)=0`.

Because `e` is transcendental, the nonzero rational polynomial `P(U,V)` cannot specialize to the
zero polynomial at `U=e`; hence it selects only finitely many lattice branches and includes
`N=0`.  That selection is neither a finite algebraic scheme nor Galois-stable over Q.  A
polynomial Bezoutian applies to the ambient equations,
where the common locus is positive-dimensional; after graph pullback the functions are entire
and the relevant zero set is the infinite lattice `(LR13)`.  Summing the constant residues
diverges rather than producing a rational global trace.

The route is therefore closed by `(LR3)--(LR5)`.  At a nonsingular isolated graph point, `m`
equations already give a length-one local algebra and every extra equation is automatically zero
inside it.  The only discrete residue, multiplicity, norm, or resultant values are normalized
tautologies; the unnormalized values live in `K` and can be transcendental, as `1/(4e)` shows.
A successful argument would require a new arithmetic theorem canonically assembling a finite,
Q-stable set of exponential branches.  The rational local cuts, defect-one deletion package, and
the selected analytic branch do not provide such a set.

### Fully transcendental augmentation has exactly one exceptional rational hyperplane

The augmentation used to remove the all-algebraic-exponential branch has a stronger rational-
subspace description.  It also pinpoints why augmentation preserves all coordinate deletions but
cannot preserve the full rational-hyperplane package.

Let `u=(u_1,...,u_m)` be a globally least counterexample in the uniform algebraic-exponential
branch.  Thus the `u_i` are Q-linearly independent, every `exp(u_i)` is algebraic, and

`K=Q(u_i,exp(u_i):1<=i<=m)`,  `td_Q K=m-1`.                         `(EH1)`

Global leastness says that every rationally independent tuple of length `<m` satisfies its
Schanuel bound.  Choose an algebraic number `a` such that

`E=exp(a)` is transcendental over `K`.                               `(EH2)`

Such an `a` exists unconditionally.  Choose `m` Q-linearly independent algebraic numbers
`a_1,...,a_m`.  Lindemann--Weierstrass makes `exp(a_1),...,exp(a_m)` algebraically independent
over Q.  Since `td_Q K=m-1`, at least one of them is transcendental over `K`.  Moreover `a` is
not in `span_Q(u)`: otherwise, after clearing denominators, `exp(a)` would be algebraic because
all the `exp(u_i)` are algebraic.

Put

`V=Q*a direct_sum U`,  `U=span_Q(u_1,...,u_m)`,
`K_V=Q(a,u_i,E,exp(u_i):i)=K(a,E)`,  `td_Q K_V=m`.                  `(EH3)`

Here `K(a,E)` is algebraic over `K(E)`, rather than necessarily equal to it, because the
algebraic number `a` need not belong to `K`.  This distinction does not affect transcendence
degree.  Likewise, changing a rational basis or exponentiating a rational combination can adjoin
particular roots; throughout this paragraph the resulting fields are mutually algebraic, not
silently identified as equal subfields of `C`.

For a rational subspace `H subset V`, let `K_H` denote the field generated by a rational basis
of `H` and the exponentials of that basis.  This is well defined up to algebraic extension:
clearing denominators between two bases gives mutual Kummer-algebraicity.  Then the following
classification is exact.

**One-exceptional-hyperplane lemma.**  Every proper rational subspace `H subsetneq V` satisfies

`td_Q K_H >= dim_Q H`                                                `(EH4)`

except the single hyperplane `H=U`.  At that hyperplane

`td_Q K_U=m-1<dim_Q U=m`.                                           `(EH5)`

Proof: if `H subset U` and `dim H<m`, `(EH4)` is global leastness; if `H=U`, `(EH5)` is `(EH1)`.
Suppose instead that `H` is not contained in `U`, and write `r=dim H`.  Then

`H_0=H intersection U`,  `dim H_0=r-1`,

and `H` has an element `h=c*a+u_0` with `c in Q^*` and `u_0 in U`.  The value `exp(u_0)` is
algebraic: clear the rational denominators of `u_0` and use that every `exp(u_i)` is algebraic.
Also `E^c` is transcendental over `K`; otherwise a nonzero integral power of `E` would be
algebraic over `K`, and hence so would `E`.  Therefore

`exp(h)=E^c*exp(u_0)` is transcendental over every algebraic
extension of `K` inside `C`,                                        `(EH6)`

and in particular over `K_(H_0)`, which is algebraic over the field generated inside `K` by
the corresponding integral multiples.  Since `dim H_0=r-1<m`, global leastness gives
`td_Q K_(H_0)>=r-1`.  Adjoining the element `(EH6)`, which already belongs to `K_H`, adds one
transcendence unit and proves `(EH4)`.  For every hyperplane `H!=U`, the upper bound
obtained because the compositum `K_H*K_V` is algebraic over `K_V`, together with `(EH3)`,
sharpens `(EH4)` to

`td_Q K_H=m`.                                                       `(EH7)`

Now apply the integral shear used in the fully transcendental reduction:

`w_0=u_1+2*a`,  `w_1=u_1+a`,  `w_j=u_j+a  (2<=j<=m)`.              `(EH8)`

It is an invertible rational change of basis of `V`; indeed `a=w_0-w_1`,
`u_1=2*w_1-w_0`, and `u_j=w_j-a`.  Every `w_j` is transcendental because it is a
transcendental `u_j` plus an algebraic number, and every `exp(w_j)` is a nonzero algebraic
multiple of `E` or `E^2`, hence transcendental.  Thus `(EH8)` is a fully transcendental
defect-one tuple of length `m+1`.

In the coefficient coordinates of the basis `(w_0,...,w_m)`, the unique exceptional
hyperplane is not a coordinate hyperplane.  The coefficient of `a` in
`sum_(j=0)^m c_j*w_j` is

`2*c_0+c_1+...+c_m`,

so the old counterexample hyperplane is exactly

`U={c:2*c_0+c_1+...+c_m=0}`.                                      `(EH9)`

Every coordinate-deletion span contains vectors with nonzero `a` coefficient and is different
from `(EH9)`; hence `(EH7)` explains directly why all coordinate deletions of `(EH8)` have the
full transcendence degree `m`.  Conversely, no invertible rational shear can eliminate the
exception: it merely carries `U` to another rational hyperplane.  This is a genuine invariant,
because restricting to that hyperplane recovers the original length-`m` counterexample.

The lemma strengthens the augmentation normal form: in the difficult algebraic-exponential
source branch, the resulting all-transcendental defect-one witness obeys Schanuel on every
rational subspace other than one explicitly marked hyperplane.  It also blocks a tempting
upgrade of the coordinate-deletion theorem.  Claiming that augmentation makes *every* rational
hyperplane exact is false precisely at `(EH9)`; iterating augmentation only creates a flag whose
newest omitted-input hyperplane contains the preceding counterexample.  Any argument based on
rational projections must therefore either use the analytic exponential to destroy this single
exceptional direction or also handle the original algebraic-exponential branch.

### Six exponentials detects the exceptional hyperplane but is saturated by its one external unit

The exact unconditional input must first be separated into two statements.  The ordinary
[Six Exponentials Theorem (Waldschmidt, Theorem
10)](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/SurveyTrdceEllipt2006.pdf)
says that if `x_1,x_2` and `b_1,b_2,b_3` are respectively Q-linearly independent, then at least
one of

`exp(x_i*b_j),   1<=i<=2, 1<=j<=3`                                  `(SE1)`

is transcendental over `Q`.  The ranks here are over `Q`, not over `Qbar`.  In particular three
Q-linearly independent algebraic multipliers are allowed; they could never be Qbar-linearly
independent.  A verified classical algebraic-independence refinement, recorded as Theorem 2.9 in
[Waldschmidt, *Algebraic Independence in Algebraic Groups, Part II*](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/LN1752-14-2001.pdf),
puts

`L=Q(x_1,x_2,b_1,b_2,b_3,exp(x_i*b_j):i<=2,j<=3)`

and proves

`td_Q L>=2`.                                                        `(SE2)`

This is the `d*l>d+l` case `d=2,l=3` of its small-transcendence-degree theorem.  It is stronger
than `(SE1)`, but it is still an absolute, not a relative-over-`K`, assertion.

For an arbitrary fully transcendental witness let

`V=span_Q(z_1,...,z_n)`, `y_i=exp(z_i)`, `K=Q(z_i,y_i:i<=n)`.

The exact exponential closure supplied by the original graph point is only

`u=sum_i q_i*z_i in V  =>  exp(u) in K^alg`,                         `(SE3)`

because, after clearing a common denominator `N`,

`exp(u)^N=product_i y_i^(N*q_i) in K`.

Algebraicity of `K` over every deletion field also puts `(SE3)` in the algebraic closure of each
deletion field, but supplies no new arguments `u`.  In particular

`a,x in K, exp(x) in K^alg  does not imply  exp(a*x) in K^alg`.      `(SE4)`

This is the precise unavailable closure property in every attempted product grid.

For two Q-independent rows `x=(x_1,x_2)` in `V`, define the guaranteed multiplier space

`M_V(x)={b in C:b*x_1 in V and b*x_2 in V}`.                         `(SE5)`

It is a Q-vector space, and evaluation `b -> b*x_1` embeds it into `V`, so
`dim_Q M_V(x)<=n`.  If `n=2`, the rows span `V` and `(SE5)` is the multiplier field

`A(V)={b:b*V subset V}`.

Indeed `A(V)` is closed under sums and products, and multiplication by a nonzero element is an
injective endomorphism of finite-dimensional `V`, hence surjective; thus it also contains the
inverse.  Therefore

`[A(V):Q]*dim_(A(V)) V=n`,                                          `(SE6)`

so `dim_Q A(V)` divides `n`.  In dimension two it is at most two and cannot provide the three
columns in `(SE1)`.  Notice that this conclusion uses only product-in-`V` closure; deletion
algebraicity does not enlarge `(SE5)`.

The mixed fully transcendental stress is even sharper.  Let

`w_0=2*ell+1`, `w_1=ell+1`, `ell=log 2`, `K=Q(e,ell)`.               `(SE7)`

Then `span_Q(w_0,w_1)=Q+Q*ell`.  If `b` stabilizes this space, write `b=r+s*ell`.  The condition
`b*ell in Q+Q*ell` forces `s=0`, since otherwise `ell` would satisfy a quadratic equation over
`Q`; hence

`A(span_Q(w_0,w_1))=Q`.                                             `(SE8)`

Thus the rational-span data supplies only one multiplier direction.  There is nevertheless an
exact six-exponentials test for what would be needed beyond it.  Put `r=w_1/w_0`.  Since `r` is
transcendental, `1,r,r^(-1)` are Q-linearly independent (in fact Qbar-linearly independent), and
the product grid is

`[[w_0,w_1,w_0^2/w_1],`
` [w_1,w_1^2/w_0,w_0]]`.                                            `(SE9)`

Assume hypothetically that `td_Q K=1`.  All rows and columns of `(SE9)` lie in `K`, and the four
corner values are `exp(w_0)=4*e` and `exp(w_1)=2*e`.  Applying `(SE2)` proves the genuine relative
conclusion

`td_K K(exp(w_0^2/w_1),exp(w_1^2/w_0))>=1`.                         `(SE10)`

In particular the two new cross-exponentials cannot both be algebraic over `K`.  This does not
contradict the defect-one field: neither deletion algebraicity nor `(SE3)` places either one in
`K^alg`.  The ordinary theorem `(SE1)` is completely silent here, because the already displayed
entry `4*e` is transcendental over `Q`.

The exceptional-hyperplane normal form `(EH1)--(EH9)` makes the saturation exact.  Retain its
notation

`V=Q*a direct_sum U`, `E=exp(a)`, `exp(U) subset Qbar^*`,
`K_V=K(E)`, `td_Q K_V=m`.

Suppose a candidate grid has Q-independent rows `x_1,x_2`, Q-independent columns
`b_1,b_2,b_3`, and all six products in `V`.  Write uniquely

`x_i*b_j=c_(ij)*a+u_(ij),   c_(ij) in Q, u_(ij) in U`.               `(SE11)`

After one common denominator `D`, formula `(EH6)` gives

`exp(x_i*b_j)=alpha_(ij)*E^(c_(ij)),   alpha_(ij) in Qbar^*`,
`Q(exp(x_i*b_j):i,j) subset Qbar(E^(1/D))`.                          `(SE12)`

If every `c_(ij)=0`, all six exponentials are algebraic, contradicting `(SE1)`.  Equivalently,
for every Q-independent pair in the old exceptional hyperplane,

`dim_Q {b:b*x_1,b*x_2 in U}<=2`.                                   `(SE13)`

Thus six exponentials proves that a `2 by 3` product grid cannot remain inside the unique bad
hyperplane.  If some `c_(ij)!=0`, however, `(EH6)` says that the corresponding value is
transcendental over `K`; the single unit `E` already supplies it, and `(SE12)` shows that all six
values together have transcendence degree at most one over `Qbar`.  This exactly saturates the
ordinary conclusion.  The stronger total bound `(SE2)` also gives no contradiction: an
algebraic-exponential counterexample has `m>=2` (the case `m=1` is excluded by
Hermite--Lindemann), while the whole crossing grid lies in `K_V`: the rows and products do by
assumption, each column is the quotient `(x_1*b_j)/x_1`, and the exponentials lie there by
`(SE12)`.  This field has transcendence degree `m>=2`.  In the boundary `m=2`, the old field
contributes one unit and `E` contributes the second,
so `(SE2)` holds with equality.  The unique-hyperplane theorem therefore makes six exponentials
locate the crossing, but its conclusion is precisely the already-proved external unit `(EH6)`.

Two partial exponential characters show that `(SE4)` is independent of the deletion package.
Let `T` be transcendental and put

`z_1=T`, `z_2=T^2`, `K_0=Q(T)`.

In a divisible algebraic closure fix coherent rational powers and define on
`span_Q(T,T^2,T^3,T^4)`

`E_0(T^j)=T+j  (1<=j<=4)`.                                         `(SE14)`

The four functions `T+j` are multiplicatively independent, so this defines an injective
Q-additive character.  The original tuple

`(T,T^2;T+1,T+2)`

is Q-linearly independent, fully transcendental, has generated field `K_0` of transcendence
degree one, and either one-coordinate deletion still generates `K_0`.  Thus it realizes the
positive defect-one minimal deletion package.  Rows `T,T^2` and columns `1,T,T^2` are respectively
Q-independent, while

`(E_0(T^(i+j-1)))_(i=1,2;j=1,2,3)`
` =[[T+1,T+2,T+3],[T+2,T+3,T+4]]`                                  `(SE15)`

lies entirely in `K_0`.  Every entry is already transcendental, so `(SE15)` satisfies the
ordinary conclusion `(SE1)`; it violates `(SE2)`, showing exactly where the analytic theorem adds
information beyond an abstract character.  Keeping the same original tuple but instead assigning
`E_1(T^3)=S,E_1(T^4)=R` for independent new transcendentals `S,R` gives another character with
identical deletion data and an external grid.  Hence the original tuple does not determine the
two cross-values even algebraically.

There is also an exact defect-one model which saturates the full classical bound rather than
violating it.  Let `alpha^3=2` and let `T,S` be algebraically independent.  On
`V=T*Q(alpha)` set

`E(T)=S`, `E(alpha*T)=S+1`, `E(alpha^2*T)=S+2`.                      `(SE16)`

Then

`z=(T,alpha*T,alpha^2*T)`, `exp(z)=(S,S+1,S+2)`,
`K_1=Q(alpha,T,S)`, `td_Q K_1=2`.

All six displayed coordinates are transcendental, the inputs are Q-independent, and every
two-coordinate deletion still generates `K_1` (use a ratio of the retained inputs to recover
`alpha`, and any retained output to recover `S`).  With rows `T,alpha*T` and columns
`1,alpha,alpha^2`, the complete grid is

`[[S,S+1,S+2],[S+1,S+2,S^2]] subset K_1`,                           `(SE17)`

because `alpha^3=2`.  Its total transcendence degree is exactly two, equal to `(SE2)`.  Thus even
a fully available `2 by 3` grid is compatible with defect one from arity three onward.  The model
is an abstract character, but it satisfies every Q-rank, field-containment, full-transcendence,
and deletion-algebraicity input used by the proposed argument; what distinguishes the complex
exponential is only the analytic theorem, whose numerical lower bound is already saturated.

The route therefore yields two sharp positive restrictions but no Schanuel contradiction:
`(SE10)` forces one new mixed cross-value outside a hypothetical degree-one field, and `(SE13)`
forbids a six-exponential grid wholly inside the algebraic-exponential exceptional hyperplane.
Deletion algebraicity cannot supply the missing product-exponential closure `(SE4)`; if a grid
crosses the hyperplane, the one external value `E` from `(EH6)` supplies exactly the
transcendence detected by six exponentials, and for arity at least three the total lower bound two
is already below the defect-one field dimension.

### Anchor Four/Six-Exponentials matrices are either rank-deficient or spend their surplus externally

Here is the exhaustive audit at the canonical anchor.  Put

`omega=2*pi*I`, `a=1+omega`, `b=1+2*omega`,
`exp(a)=exp(b)=e`, `A=Q*1 direct_sum Q*omega`.                    `(AF1)`

Let `V` be a canonical anchored, fully transcendental, anchored-minimal defect-one input space,
`n=dim_Q V`, and `K=Q(V,exp(V))`, so `td_Q K=n-1`.  The anchor dichotomy `(CS3)` is essential:

`n=2 => V=A and td_Q Q(e,omega)=1`,
`n>2 => td_Q Q(e,omega)=2`.                                      `(AF2)`

Thus in positive complement arity the two-unit conclusion of every classical matrix theorem is
already present in the anchor field.  Only the arity-two branch can possibly gain a relative
unit, and that branch is exactly the open algebraic independence of `e` and `pi`.

First distinguish the theorem statements.  The ordinary Six Exponentials Theorem says that two
Q-independent row factors `x_1,x_2` and three Q-independent column factors `y_1,y_2,y_3` make at
least one of the six `exp(x_i*y_j)` transcendental.  Gel'fond--Tijdeman's refinement, Theorem 13(3)
in Waldschmidt's
[*Elliptic Functions and Transcendence*](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/SurveyTrdceEllipt2006.pdf),
says in this `2 by 3` case that

`td_Q Q(x_i,y_j,exp(x_i*y_j):i<=2,j<=3)>=2`.                     `(AF3)`

The analogous assertion for a `2 by 2` grid that one of all four exponentials is transcendental
is the **Four Exponentials Conjecture**, not a theorem.  The unconditional `2 by 2` result
available here is the special Theorem 13(4): if the two entries in one row,
`exp(x_1*y_1),exp(x_1*y_2)`, are algebraic, then at least two among

`x_1,x_2,y_1,y_2,exp(x_2*y_1),exp(x_2*y_2)`                      `(AF4)`

are algebraically independent.  Confusing the open four-entry assertion with `(AF4)` produces
several false apparent contradictions below.

All anchors, their conjugates, and all integer period translates stay in the same rational
plane.  Explicitly,

`conj(a)=3*a-2*b`, `conj(b)=4*a-3*b`,
`a+k*omega=(1-k)*a+k*b`,                                         `(AF5)`

and their exponentials are again `e`.  More generally, for `u=p+q*omega` and
`v=r+s*omega` in `A`,

`u*v=p*r+(p*s+q*r)*omega+q*s*omega^2`,
`exp(u*v)=zeta_(u,v)*exp(p*r)*exp(q*s*omega^2)`,
`zeta_(u,v)=exp((p*s+q*r)*omega) in Qbar^*`.                      `(AF6)`

For rational coefficients, `exp(p*r)` is algebraic over `Q(e)`.  Hence every fixed product grid
made from anchors, conjugates, and integer translates has all its exponential entries algebraic
over

`K(Z)`, `Z=exp(omega^2/D)`                                       `(AF7)`

for one common positive denominator `D`.  Such operations can introduce at most one new
transcendence direction, never the missing unit inside `K`.

There is also a precise rank obstruction before applying any theorem.  If `x_1,x_2` are a basis
of `A`, the multipliers whose two products remain in the controlled input plane form

`M_A={c:c*x_1,c*x_2 in A}={c:c*A subset A}=Q`.                   `(AF8)`

Indeed `c*1 in A` gives `c=r+s*omega`, and `c*omega in A` forces `s=0`, since the transcendental
`omega` satisfies no quadratic equation over `Q`.  Thus two nonzero controlled multiplier
columns are already Q-dependent.  In particular neither a qualifying `2 by 2` nor a qualifying
`2 by 3` matrix can have every product in `A`.  Conjugation and period translation do not alter
this because `(AF5)` is an invertible rational change of rows.

The basic `2 by 2` anchor matrix illustrates both boundaries.  Rows and columns `1,omega` give

`[[e,1],[1,exp(omega^2)]].`                                      `(AF9)`

The Four Exponentials Conjecture, even if granted, is already satisfied by the known
transcendental entry `e` and would not force `exp(omega^2)` outside `K`.  The special theorem
`(AF4)` can be used only conditionally: take
`x_1=y_1=omega/2`, `x_2=y_2=1`.  If `exp(omega^2/4)` were algebraic, the two first-row entries
would be `exp(omega^2/4)` and `-1`, so `(AF4)` and a hypothetical
`td_Q Q(e,omega)=1` would contradict one another.  Therefore the defect hypothesis implies only

`exp(omega^2/4) is transcendental over Q`;                       `(AF10)`

it may still be algebraic over the transcendental field `K`.  Sign changes from conjugation and
integer translates reduce by `(AF6)` to the same single value.

Ratios produce the strongest genuine canonical grid.  The number

`r=b/a=(1+2*omega)/(1+omega)`                                    `(AF11)`

is transcendental, and `1,r,r^(-1)` are Q-linearly independent: a rational relation would make
`r` quadratic over `Q`.  With rows `a,b` the complete product and exponential grids are

`[[a,b,a^2/b],[b,b^2/a,a]]`,
`[[e,e,exp(a^2/b)],[e,exp(b^2/a),e]].`                            `(AF12)`

All row and column independence hypotheses in `(AF3)` hold.  The ordinary theorem again sees
the already transcendental corner `e`.  If `n=2`, however, all five row/column factors lie in
the degree-one field `K`, so `(AF3)` gives the exact relative conclusion

`td_K K(exp(a^2/b),exp(b^2/a))>=1`.                              `(AF13)`

This is a real dimension surplus, but it is entirely external: neither cross argument belongs
to `A`, and the graph data gives no reason for either exponential to be algebraic over `K`.  If
`n>2`, `(AF2)` already supplies transcendence degree two before the cross values are adjoined,
so `(AF3)` gives no surplus at all.  Replacing `r^(-1)` by a ratio involving a conjugate or a
different period translate changes the displayed rational functions of `omega`, but not this
field count: every qualifying new column creates uncontrolled product-exponentials.

Ratios of exponential values are even less useful.  For `u,v in V`,

`exp(u)/exp(v)=exp(u-v) in K^alg`,                               `(AF14)`

but using this number as a multiplier would require `exp(x*exp(u-v))`; the exponential
homomorphism supplies no relation between that value and `K`.  At the anchor the most tempting
ratio is `exp(b)/exp(a)=1`, which cannot contribute an independent column.  For a
conjugation-stable witness, `conj(u) in V` and
`exp(conj(u))=conj(exp(u)) in K^alg`, but products `x*conj(u)` have exactly the same missing
closure.  Thus conjugates add available row factors, not controlled product entries.

Algebraic multiplier columns make the external nature still clearer.  Choose algebraic
`alpha,beta` with `1,alpha,beta` Q-linearly independent and use rows `1,omega`.  The grid is

`[[e,exp(alpha),exp(beta)],`
` [1,exp(alpha*omega),exp(beta*omega)]].`                         `(AF15)`

Lindemann--Weierstrass already makes `e,exp(alpha),exp(beta)` algebraically independent, while
Gel'fond--Schneider makes the last two entries transcendental when `alpha,beta` are irrational.
In the arity-two defect branch, `K*Qbar` is algebraic over `Qbar(e)`, so the first row supplies
two transcendence units over `K`.  This is stronger than `(AF3)` but still harmless: the new
values were introduced precisely by leaving the rational multiplier closure of the witness.
With rows `a,b` instead, these entries are replaced by products of `exp(alpha)` with
`exp(alpha*omega)` and the same uncontrolled values remain.

Using complementary canonical inputs cannot improve the conclusion.  For any two independent
rows in `V`, three columns whose six products all lie in `V` do make all six exponentials
algebraic over `K` by `(SE3)`.  The ordinary theorem then selects a transcendental element of
`K^alg`, which costs no additional transcendence degree.  If `n>=3`, the total field `K` has
transcendence degree `n-1>=2`, exactly enough for `(AF3)`.  If `n=2`, `(AF8)` prevents such a
triple.  This exhausts the alternatives: a grid either stays in `V` and its theorem bound is
already paid by `K`, or it leaves `V` and introduces exponential values with no deletion or
minimality control.

An exact-kernel exponential character saturates the strongest remaining case `(AF13)`.  Let
`T=pi`, choose a positive real `S` algebraically independent from `pi`, and retain the actual
`omega=2*pi*I`.  The four source numbers

`omega,1,a^2/b,b^2/a`                                            `(AF16)`

are Q-linearly independent: after multiplying a putative relation by `a*b`, comparison of the
four coefficients of the resulting cubic polynomial in the transcendental `omega` makes every
coefficient zero.  The target numbers

`omega,Log(T),Log(S),Log(S+1)`                                   `(AF17)`

are also Q-linearly independent; exponentiating an integral relation and comparing divisors in
`Qbar(T,S)` proves this.  Extend `(AF16)->(AF17)` to a Q-linear automorphism `B` of `C` fixing
`omega`, and set `E_B=exp o B`.  Then

`ker(E_B)=omega*Z`,
`E_B(a)=E_B(b)=T`,
`E_B(a^2/b)=S`, `E_B(b^2/a)=S+1`.                                `(AF18)`

The canonical tuple `(a,b;T,T)` is Q-linearly independent and fully transcendental, and

`td_Q Q(a,b,T)=td_Q Q(omega,pi)=1`,
`td_Q Q(omega,pi,S)=2`.                                          `(AF19)`

Thus the ratio grid has exactly the two total units required by `(AF3)` and exactly the one
external unit in `(AF13)`.  Any fixed finite collection of conjugate, translate, and ratio
cross-directions can be added to the construction by sending a Q-basis of the new source span
to logarithms of multiplicatively independent rational functions `S+j`; the whole enlarged
family still lies in the same relative-transcendence-one field `Qbar(pi,S)`.  The character is
not the holomorphic exponential and is not a counterexample to the classical theorem.  It is a
sharp model of every Q-rank, exact-kernel, anchor, field-containment, and strongest theorem
dimension conclusion used in this audit.

Therefore Four/Six Exponentials cannot contradict the canonical terminal witness.  The only
unconditional `2 by 2` theorem forces the absolute external value `(AF10)`; the optimal ratio
`2 by 3` grid forces the relative external unit `(AF13)` only in arity two; and all higher-arity
or algebraic-multiplier matrices pay the required rank before returning anything to `K`.

### The full shear algebraic matroid has an exact rank-one canonical model

An algebraic-matroid certificate cannot distinguish the canonical exponential point from an
explicit defect-one character, even after every rational shear and its exact Kummer equations are
adjoined.  For a field extension `L/Qbar` and a finite coordinate set `S subset L`, write

`r(S)=td_Qbar Qbar(S)`.                                            `(AM1)`

This is the algebraic-matroid rank.  Submodularity and monotonicity hold for every algebraic
matroid.  In characteristic zero substantially more is automatic: Ingleton's theorem, recalled
as Theorem 28 in the primary paper Bollen--Draisma--Pendavingh,
[*Algebraic matroids and Frobenius flocks*](https://arxiv.org/abs/1701.06384), says that every
characteristic-zero algebraic matroid has a linear representation.  Concretely, for a finitely
generated field `F/Qbar`,

`r(S)=dim_F span_F{d s:s in S} subset Omega_(F/Qbar)`.             `(AM2)`

Hence every linear rank inequality, including Ingleton,

`r(AB)+r(AC)+r(AD)+r(BC)+r(BD)`
` >=r(A)+r(B)+r(CD)+r(ABC)+r(ABD)`,                               `(AM3)`

already holds.  This is special to characteristic zero; positive-characteristic algebraic
matroids need not be linear because Frobenius can kill differentials.

Information-theoretic tools have a different scope.  Shannon inequalities are merely
polymatroid inequalities and so apply to `(AM1)`.  Matús proves in the primary paper
[*Algebraic matroids are almost entropic*](https://staff.utia.cas.cz/matus/algaent.pdf) that every
finite algebraic-matroid rank vector lies in the closure of the entropic cone.  Consequently all
continuous homogeneous Shannon and non-Shannon information inequalities are valid for algebraic
matroids in every characteristic.  Ingleton has the opposite comparison: it is a linear-rank
inequality, not a universal entropy inequality, and it is available here because of the
characteristic-zero linearisation `(AM2)`.  Copy lemmas are existential extension statements,
not additional equations on the original ground set.  Even when a copy/AK construction is used
to derive a valid inequality, one may not identify its auxiliary entropy variable with a
prescribed exponential shear coordinate or require the copy to satisfy `(AM10)--(AM11)`.  The
model below is itself rank-one linear and entropic, so it satisfies submodularity, Ingleton,
every linear rank inequality, and every universal Shannon or non-Shannon information inequality
simultaneously.

Construct the model over a transcendental `T`.  Work in an algebraic closure of `Qbar(T)` with
one coherent choice of every rational power `T^q`.  On the rational plane `Q+Q*T`, define

`E_*(A+B*T)=exp(2*pi*I*B)*T^A`, `A,B in Q`.                       `(AM4)`

The root-of-unity factor and coherent powers make `(AM4)` an additive-to-multiplicative
character.  Its kernel is exact:

`ker(E_*)=Z*T`.                                                    `(AM5)`

Indeed `E_*(A+B*T)=1` first forces `A=0` because the transcendental `T` has no nonzero rational
power algebraic, and then forces `B in Z`.  Put

`X_0=1+T`, `X_1=1+2*T`, `Y_0=Y_1=T`.                              `(AM6)`

Then `X_0,X_1` are Q-linearly independent, all four coordinates are transcendental, the
canonical anchor and duplicate-value identities hold, and

`r(X_0,X_1,Y_0,Y_1)=1=2-1`.                                      `(AM7)`

Thus `(AM6)` is already an exact fully transcendental canonical defect-one rank model.

Now adjoin the complete rational shear orbit.  For `q=(q_0,q_1) in Q^2`, set

`U_q=q_0*X_0+q_1*X_1`
`   =(q_0+q_1)+(q_0+2*q_1)*T`,
`V_q=E_*(U_q)`
`   =exp(2*pi*I*(q_0+2*q_1))*T^(q_0+q_1)`.                       `(AM8)`

The additive and multiplicative orbit laws are exact:

`U_(q+r)=U_q+U_r`, `V_(q+r)=V_q*V_r`.                            `(AM9)`

For an integer shear matrix `M=(m_(ji))`, `(AM9)` gives the literal binomials

`U_j'=sum_i m_(ji)*X_i`,
`V_j'=product_i Y_i^(m_(ji))`.                                   `(AM10)`

For a rational row `q`, choose a positive `D` with `D*q_i in Z`; then

`V_q^D=Y_0^(D*q_0)*Y_1^(D*q_1)`.                                `(AM11)`

Thus `(AM8)` satisfies not only the algebraic dependence pattern but every polynomial/Kummer
identity furnished by rational basis invariance.  The two distinguished rows recover the
literal anchor data:

`U_((2,-1))=1`, `V_((2,-1))=T`,
`U_((-1,1))=T`, `V_((-1,1))=1`.                                  `(AM12)`

They are the modeled algebraic input `1` and exact period `T`.

The rank function of this infinite orbit is completely explicit.  For every finite collection
`C` of the `U_q,V_q`,

`r(C)=0` if every member of `C` is algebraic over `Qbar`,
`r(C)=1` otherwise.                                               `(AM13)`

Indeed all entries are algebraic over `Qbar(T)`, while any nonconstant linear function of `T`
or nonzero rational power of `T` is transcendental and recovers `T` algebraically.  Equivalently,
all nonloops are parallel in a one-dimensional vector representation.  Every instance of
`(AM3)` is therefore either equality or a tautological `0<=1`; the same is true for every other
valid homogeneous rank inequality.  This disposes of any finite inequality certificate, and in
fact `(AM13)` handles the whole infinite orbit at once.

Tangent-space linearisation supplies no extra coupling.  In `Omega_(Qbar(T)/Qbar)` one has

`dX_0=dT`, `dX_1=2*dT`, `dY_0=dY_1=dT`,                          `(AM14)`

and differentiating `(AM10)` gives only

`dU_j'=sum_i m_(ji)*dX_i`,
`dV_j'/V_j'=sum_i m_(ji)*dY_i/Y_i`.                              `(AM15)`

These are two separate linear representations.  The exponential-graph one-forms in the model
are

`theta_0=dY_0/Y_0-dX_0=(1/T-1)*dT`,
`theta_1=dY_1/Y_1-dX_1=(1/T-2)*dT`,
`theta_1-theta_0=-dT !=0`.                                       `(AM16)`

Nothing in an algebraic matroid asserts `theta_i=0`.  Ordinary derivations of `C/Qbar` do not
commute with analytic exponentiation; differentiating a numerical identity `Y_i=exp(X_i)` is
therefore invalid.  An E-derivation would impose

`D(Y_i)=Y_i*D(X_i)`,                                              `(AM17)`

and the duplicate value in `(AM6)` would then force `D(X_1-X_0)=D(T)=0`.  The ordinary tangent
representation `(AM14)` deliberately permits `D(T)=1`.  Thus `(AM17)`, equivalently constancy
of the true analytic period for exponential-compatible derivations, is the exact analytic datum
lost by the algebraic matroid.

Modular cuts do not restore it.  A modular cut classifies possible single-element matroid
extensions; it does not require an adjoined element to raise rank.  Every shear coordinate in
`(AM8)` lies in the algebraic closure of the original four, so `(AM13)` realises it as a loop or
parallel element through a permitted principal extension.  Copy constructions may adjoin
independent entropy variables, but there is no rule identifying such a copy with a shear
coordinate or enforcing `(AM17)`.  Even retaining the exact circuit polynomials `(AM10)--(AM11)`
does not help, since the model satisfies them literally.

Consequently no finite certificate built from algebraic-matroid ranks, Ingleton or stronger
linear inequalities, entropic/non-Shannon inequalities, copy extensions, modular cuts, and the
entire rational shear-binomial package can force rank two at the canonical boundary.  The exact
rank-one representable model `(AM4)--(AM16)` satisfies every imposed algebraic identity.  What it
omits is not another matroid axiom but analytic compatibility of derivations with the standard
exponential and its fixed period, namely `(AM17)`.

### Deletion cores do not glue finite recovery branches

Let `K=Q(z,exp(z))` be a defect-one field and, first, restrict to primitive integral
hyperplanes so that every deletion field `K_H` is literally a subfield of `K`.  The checked
minimality package gives

`[K:K_H]<infinity`,  `trdeg_Q K_H=trdeg_Q K=m-1`.                     `(DC1)`

Define the deletion core

`C=intersection_H K_H`.                                               `(DC2)`

There is no corresponding bound on `[K:C]` or on `trdeg_Q C`.  Intersections of incomparable
finite-index function subfields can have full transcendence degree or collapse to Q, and neither
outcome gives a finite Q-stable set of recovery branches.

The mixed boundary makes the core completely explicit.  Write `a=log 2`, `eta=e`, and use the
fully transcendental sheared tuple

`w=(2*a+1,a+1)`,  `exp(w)=(4*eta,2*eta)`.

For a primitive integral row `(p,q)`, put

`A=2*p+q`,  `B=p+q`.

The projected pair is

`u=A*a+B`,  `exp(u)=2^A*eta^B`,

so its field is

`K_(p,q)=Q(A*a+B,2^A*eta^B)`
` = Q(a,eta^B)` if `A*B!=0`,
` = Q(eta)` if `A=0`, and `=Q(a)` if `B=0`.                           `(DC3)`

The exceptional rows `(1,-2)` and `(1,-1)` occur in the family.  Therefore

`intersection_(p,q) K_(p,q)=Q(a) intersection Q(eta)`.                `(DC4)`

A hypothetical irreducible relation `P(eta,a)=0` only says that `K` is finite over each of
`Q(a)` and `Q(eta)`; it does not determine their intersection.  All three behaviors occur for
irreducible rational curves:

* if `a=eta=t`, the intersection is `Q(t)`;
* if `a=t^2`, `eta=t^3`, then `K=Q(t)` and the intersection is `Q(t^6)`, still of
  transcendence degree one; and
* if `a=t+t^(-1)`, `eta=t+2*t^(-1)`, then

  `P(U,V)=U^2-3*U*V+2*V^2+1`

  is irreducible, `K=Q(t)`, and `Q(a) intersection Q(eta)=Q`.

For the last assertion, `Q(a)` and `Q(eta)` are the fixed fields of the involutions

`sigma_1(t)=1/t`,  `sigma_2(t)=2/t`.

Their composition scales `t` by `2`.  A rational function invariant under `t |-> 2*t` has no
finite nonzero zero or pole orbit, hence is constant.  Thus even the exact shape of `P` as a
finite correspondence does not decide whether `(DC4)` is algebraic over Q.

There are sharper fully transcendental abstract-exponential countermodels realizing both
extremes.  First take `K=Q(t)`, inputs

`z_1=t`,  `z_2=t+1`,

and define an exponential homomorphism on their rational span by

`E(z_1)=t`,  `E(z_2)=t+1`,                                           `(DC5)`

using coherent rational roots.  Valuations at `0` and `-1` show that the two target values are
multiplicatively independent, so the definition is consistent.  The inputs are Q-linearly
independent, all four displayed values are transcendental, and the full field has transcendence
degree one.  For a primitive `(p,q)`,

`u=(p+q)*t+q`,  `E(u)=t^p*(t+1)^q`.

If `p+q!=0`, the additive coordinate recovers `t`.  If `p+q=0`, primitivity gives
`(p,q)=+/- (1,-1)`, and `t/(t+1)` or its inverse recovers `t`.  Hence

`K_(p,q)=K` for every primitive integral hyperplane, and `C=K`.        `(DC6)`

Thus full transcendence, defect one, and even equality for every deletion do not force the core
to lose any transcendence.

At the opposite extreme, retain the inputs `(t,t^(-1))` and set

`A=t+t^(-1)`,  `B=t+2*t^(-1)`,
`E(t)=A^2/B`,  `E(t^(-1))=B/A`.                                      `(DC7)`

Again all four displayed values are transcendental and the inputs are Q-linearly independent.
Every primitive hyperplane field has finite index in `K=Q(t)`, because its additive coordinate
`p*t+q/t` alone gives the quadratic equation

`p*T^2-u*T+q=0`.                                                      `(DC8)`

For the rows `(1,1)` and `(1,2)`, however,

`E(t)*E(t^(-1))=A`,
`E(t)*E(t^(-1))^2=B`,

so the two deletion fields are exactly

`F_1=Q(t+t^(-1))`,  `F_2=Q(t+2*t^(-1))`.                             `(DC9)`

Their intersection is Q by the involution argument above.  Consequently the core over *all*
primitive integral hyperplanes is exactly Q.  This model satisfies the fully transcendental
defect-one and every-hyperplane finite-recovery package, yet the desired descent still fails.

Indeed, each `K/F_c`, where

`F_c=Q(t+c/t)`,

is a quadratic Galois extension with involution `sigma_c(t)=c/t`.  Its exact trace and norm are

`Tr_(K/F_c)(t)=t+c/t`,  `Nm_(K/F_c)(t)=c`.                            `(DC10)`

Thus the relevant norms can even be rational for every `c`.  But the involutions for `c=1,2`
generate the infinite dihedral group containing every scaling `t |-> 2^N*t`; the orbit of the
actual branch `t` is infinite.  The normal closure of each individual quadratic recovery is just
`K`, yet these normal structures are relative to different fixed fields and do not combine into
a finite Galois extension over their core `Q`.  In fact `K/Q` is transcendental.  Existence of a
normal closure is only an individual finite-extension statement; compare
[Stacks Project, Lemma 9.16.3](https://stacks.math.columbia.edu/tag/09DT).

This also identifies why trace and norm compatibility cannot help.  Their transitivity applies
to nested towers, while the `K_H` are generally incomparable.  Symmetrizing a missing coordinate
over `K/K_H` produces an element of that particular transcendental `K_H`; symmetrizations for
different `H` need not agree or land in `(DC2)`.  The rational norms in `(DC10)` show that even
perfect numerical agreement would not make the recovery orbit finite.

There is a further scope issue for genuinely rational, rather than integral, basis changes.  A
rational input combination introduces chosen roots of exponential values.  The formal
rational-hyperplane theorem therefore says that the *transformed full field* is algebraic over
its deletion field; it does not canonically place every deletion field inside the original `K`.
One must choose a common algebraic overfield and compatible root embeddings before taking an
intersection or compositum.  Such composita depend on the embeddings, as emphasized in the
[Stacks Project warning](https://stacks.math.columbia.edu/tag/09IC).  The integral models
`(DC5)--(DC10)` avoid this ambiguity and already refute the descent.

Finally, algebraic recovery monodromy does not preserve the exponential graph.  In the mixed
case, an embedding of `K/Q(a)` permutes the roots of `P(U,a)` but has no reason to send the
selected root `eta=exp(a+1)/2=e` to another value of that analytic expression--there is no other
such value at the fixed `a`.  Similarly, conjugating `a` over `Q(eta)` does not preserve the
selected logarithm `exp(a)=2`.  Automorphisms of `C/Q` do not commute with `exp`.  A theorem
asserting that all algebraic recovery conjugates remain graph points would be precisely the
missing analytic--arithmetic compatibility, not a consequence of deletion algebraicity.

The route is therefore closed.  The core may retain full transcendence, as `(DC6)`, or equal Q,
as `(DC9)`, while the recovery branches still have infinite combined monodromy.  To obtain a
finite Q-stable set one would need both `C/Q` algebraic and `K/C` finite; together those would make
the positive-transcendence field `K` algebraic, an impossibility.  What is actually needed is a
finite *relative* branch set preserved by the analytic exponential graph, and the deletion,
trace, norm, and normal-closure packages supply no such preservation.

### A defect-one fully transcendental witness may be forced to span the true period

There is another exact strengthening of the normal form which uses the analytic exponential
rather than merely an abstract injective character.  Put

`omega=2*pi*I`,  so `exp(omega)=1`.                                  `(PB1)`

**Period-bearing normal-form lemma.**  Failure of Schanuel's conjecture is equivalent to the
existence of a Q-linearly independent fully transcendental family `w` of length at least two
such that

`td_Q Q(w,exp(w))=length(w)-1`

and

`omega in span_Q(w)`.                                                `(PB2)`

Only the forward implication needs proof.  Start with the positive fully transcendental
restricted-minimal defect-one witness supplied above, write its length as `m>=2`, and put

`z=(z_1,...,z_m)`,  `K=Q(z,exp(z))`,  `td_Q K=m-1`.                 `(PB3)`

The full field `K` is algebraic over every one-coordinate deletion field.  If `omega` already
belongs to `span_Q(z)`, take `w=z`.  Assume from now on that it does not.

Choose two distinct indices `i,j`.  At least one of

`h_1=omega+z_i`,  `h_2=omega+2*z_i`                                 `(PB4)`

is transcendental over Q: if both were algebraic, their difference `z_i` would be algebraic.
Fix `k in {1,2}` for which `h=omega+k*z_i` is transcendental.  Since `exp(omega)=1`,

`exp(h)=exp(z_i)^k`,                                                 `(PB5)`

which is transcendental because `exp(z_i)` is nonzero and transcendental.

There are two field-theoretic cases.

1. Suppose `omega` is algebraic over `K`.  Delete `z_j` and insert `h`, obtaining a new
   length-`m` family

   `w=(z_r:r!=j, h)`.                                                `(PB6)`

   It is rationally independent.  Indeed, a rational relation with nonzero coefficient on `h`
   would express `omega` as an element of `span_Q(z)`, contrary to the case assumption; after
   that coefficient is zero, independence of the retained `z_r` finishes the argument.  Every
   displayed coordinate and exponential is transcendental by the old witness and `(PB4)--(PB5)`.
   Because `i!=j`, the retained family includes `z_i`, and hence

   `omega=h-k*z_i in span_Q(w)`.                                    `(PB7)`

   Let `K_j` be the deletion field.  The new generated field is, up to the exact redundancy in
   `(PB5)`, `K_j(omega)`.  Minimality gives `td_Q K_j=m-1` and `K/K_j` algebraic; the present
   case gives `omega/K` algebraic.  By transitivity `K_j(omega)/K_j` is algebraic, so the field
   in `(PB6)` still has transcendence degree `m-1`.  Thus it is fully transcendental,
   period-bearing, and defect one without increasing arity.

2. Suppose `omega` is transcendental over `K`.  Keep every `z_r` and append `h`:

   `w=(z_1,...,z_m,h)`.                                              `(PB8)`

   The same coefficient argument proves rational independence, and `(PB4)--(PB5)` give full
   transcendence.  The new field is exactly `K(omega)`, because `h=omega+k*z_i` and its
   exponential already belongs to `K`.  Hence

   `td_Q K(omega)=td_Q K+1=m`,                                      `(PB9)`

   one below the new length `m+1`; and `(PB7)` again puts `omega` in the rational span.

These cases prove `(PB2)`, and the converse is immediate from the displayed defect-one equality.
The arity change is controlled sharply: it is zero when the period is algebraic over the witness
field and one when it is transcendental.  The deletion-algebraicity clause is essential in the
first case; without it, replacing `z_j` could lower the transcendence degree below `m-1`.

This normal form makes the period-shift action internal.  Once `(PB2)` holds, one can choose a
rational basis of the same input span in which the period is a rational combination, and all
integer shifts by that combination leave every exponential value unchanged.  It does not yet
give a contradiction: discontinuous exponential characters can be prescribed to have the same
period.  What it does remove is the earlier dichotomy in which `2*pi*I` lay outside both the
input span and the defect field.  Any surviving proof may now assume simultaneously full
transcendence, exact defect one, and the presence of the standard analytic period in the input
span.

### Integer period translations close to an additive cylinder

Let `tau=2*pi*I`, let `z=(z_1,...,z_n)` be a Q-linearly independent, fully transcendental
defect-one witness, and write

`y=exp(z),    K=Q(z,y),    td_Q K=n-1.`

For `k in Z^n`, put `z^(k)=z+k*tau` and `K_k=Q(z^(k),y)`.  The exponentials are unchanged.  The
rational-independence exceptional set is exact.  If `tau` is not in `span_Q(z)`, every `z^(k)`
is independent: a relation `q dot z^(k)=0` has `q dot k!=0` and would express
`tau=-(q dot z)/(q dot k)`.  If instead

`tau=c dot z,    c in Q^n,`                                        `(PT1)`

then uniqueness follows from independence of `z`, and

`z^(k) is dependent  iff  1+c dot k=0.`                            `(PT2)`

Its relation space is then the line `Q*c`; off this affine lattice hyperplane it is zero.  Thus
the exceptional set is either empty or a coset of a rank-`n-1` sublattice, and at every
exceptional `k` the shifted tuple has rank exactly `n-1`.

The field calculation has one additional, unavoidable binary invariant.  Put `L=K(tau)`.  Since
`L=K_k(tau)`, define

`epsilon_k=td_(K_k) L in {0,1}.`

Then

`td_Q K_k=td_Q L-epsilon_k.`                                      `(PT3)`

There is a geometric characterization of the bit.  Let `V` be the Q-locus of `(z,y,tau)` and
change coordinates to `W=X+k*T`.  Then `epsilon_k=1` exactly when the projection
`V -> (W,Y)` has generic one-dimensional fiber.  Since that fiber lies in an affine line, this
is equivalent to `V` being invariant under

`(X,Y,T) |-> (X-s*k,Y,T+s),    s in Ga.`                            `(PT4)`

Equivalently there is a Q-derivation of `L` which kills `K_k` and sends
`D(tau)=1`, `D(z_i)=-k_i`, and `D(y_i)=0`.  Deciding the last unit in `(PT3)` is therefore already
a graph-compatible unipotent-stabilizer assertion.

The requested three cases are now exact.

* If `tau in span_Q(z)`, then `td_Q L=n-1`.  For every nonexceptional `k`,
  `(1+c dot k)*tau=c dot z^(k)`, so `K_k=K` and `td_Q K_k=n-1`.  At an exceptional `k`,
  `td_Q K_k=n-1-epsilon_k`, and both values can occur.
* If `tau` is algebraic over `K` but is outside `span_Q(z)`, every shift remains independent,
  `td_Q L=n-1`, and `td_Q K_k=n-1-epsilon_k` (with `epsilon_0=0`).
* If `tau` is transcendental over `K`, every shift remains independent, `td_Q L=n`, and
  `td_Q K_k=n-epsilon_k` (with `epsilon_0=1`).  A nonzero shift can retain defect one or acquire
  exactly the missing transcendence unit, according to `(PT4)`.

These alternatives are genuine.  They are realized by discontinuous exponential characters
having the actual period `tau`.  Choose all auxiliary parameters below algebraically independent
over `Q(tau)`.  On the Q-span of `tau,z_1,...,z_n`, prescribe a Q-linear map `B` by
`B(tau)=tau` and by choosing logarithms `B(z_i)` of the displayed `y_i`; extend `B`
discontinuously on a Hamel basis of `C`, and set

`E(x)=exp(B(x)).`                                                   `(PT5)`

Then `E(tau)=1` and `E(z_i)=y_i`.  In the span case take `n=3`,

`z=(U+tau,U^2,-U-U^2),    c=(1,1,1),    k=(-1,0,0).`

The shift is exceptional and equals `(U,U^2,-U-U^2)`.  With
`y=(U,U+1,1/(U*(U+1)))`, its field drops from `Q(U,tau)` to `Q(U)`; with
`y=(U,tau,1/(U*tau))`, it stays `Q(U,tau)`.  The product of the three values is one, exactly as
required by `c dot z=tau`, so `(PT5)` is consistent.

For the algebraic-over-`K` case outside the span, its degree-one instance already realizes both
bits.  Take

`z=(U-tau,U^2-tau,U^3-tau),    k=(1,1,1).`

Then `tau in K=Q(U,tau)` but `tau notin span_Q(z)`.  Values `(U,U+1,U+2)` give
`K_k=Q(U)`; replacing one value by `tau` makes `K_k=Q(U,tau)`.  All displayed inputs and values
are transcendental and the inputs are Q-linearly independent.

For the transcendental-over-`K` case choose `T,U` algebraically independent over `Q(tau)` and
set

`z=(U,U+T,2*U+T^2),    y=(T,T+1,T+2),    K=Q(T,U).`             `(PT6)`

For the coherent line `k=t*(1,1,2)`,

`K_k=Q(T,U+t*tau),    td_Q K_k=2=n-1;`                          `(PT7)`

the locus has precisely the stabilizer `(PT4)`.  Off that line, either
`z_2^(k)-z_1^(k)-T` or `z_3^(k)-2*z_1^(k)-T^2` recovers `tau`, so

`K_k=Q(T,U,tau),    td_Q K_k=3=n.`                              `(PT8)`

This one defect-one character realizes both possible field dimensions along one period orbit.

The Q-Zariski closure of the whole shift orbit is even more explicit and forgets all additive
relations.  In the Laurent coordinate ring put

`J_y={g in Q[Y_1^(+-1),...,Y_n^(+-1)]:g(y)=0}.`

Then

`I_Q({(z+k*tau,y):k in Z^n})=J_y*Q[X,Y^(+-1)],`                `(PT9)`

so the closure is `A^n times Loc_Q(y)`.  Indeed, after evaluating `Y=y`, a polynomial on
`z+tau*Z^n` is a polynomial in `k`; the integer grid is Zariski dense, so every coefficient in
the `X` variables vanishes at `y`.  Removing the exceptional hyperplane in `(PT2)` does not
change this closure.  Since every `y_i` is transcendental, this cylinder has dimension at least
`n+1`, even when every independent individual shift in the period-bearing case has Q-locus
dimension only `n-1`.  The dimension jump is the union of moving loci, not extra transcendence
inside any one shifted field.

There is an exact bounded-degree Grassmann stabilization, but it stabilizes to `(PT9)`, not to a
defect relation.  Let `R_D` be the finite-dimensional span of Laurent monomials having additive
degree at most `D` in each `X_i` and toric exponents between `-D` and `D`, and let `I_(D,N)` be
those elements vanishing on the box `|k_i|<=N`.  If `2*N+1>D`, grid interpolation gives

`I_(D,N)=R_D intersection (J_y*Q[X,Y^(+-1)]).`                  `(PT10)`

The reduced finite boxes have length `(2*N+1)^n`, so their Hilbert polynomials are unbounded and
do not lie in one fixed Hilbert component.  A relation through the original point is not
propagated: its translates are moving polynomials `F(X-k*tau,Y)`, generally over `Q(tau)`, and a
single polynomial vanishing on all shifts must lose its `X`-dependence modulo `J_y`.

The marked hyperplane `(EH9)` is transported, never duplicated.  Let
`V_0=span_Q(w_0,...,w_m)`, `U=ker(a dot -)`, with `a=(2,1,...,1)`.  In
`V_0 direct_sum Q*tau`, a shift defines

`S_k(v+t*tau)=v+(t+ell_k(v))*tau,    ell_k(w_i)=k_i.`            `(PT11)`

It sends `V_0` to the shifted span and the one marked exception to `U_k=S_k(U)`.  Within a
shifted Grassmannian there is only this transported candidate, and

`U_k=U_l  iff  (k-l)|_U=0  iff  k-l in Q*a.`                    `(PT12)`

Thus the possibly infinite orbit consists of unipotent copies of the same direction.  If
`tau in V_0`, the same statement holds for every independent shift using the invertible matrix
`I+k*c^t`; its singular determinant condition is exactly `(PT2)`.

The transcendence-degree effect on the marked direction is also exact.  If `ell_k|_U=0`, then
`U_k=U` pointwise.  Otherwise let `H_0=U intersection ker(ell_k)`, of dimension `m-1`.
The one-exceptional-hyperplane lemma gives `td_Q K_(H_0)>=m-1`, whence

`td_Q K_(U_k)=m-1` if `tau` is algebraic over `K_U`,
`td_Q K_(U_k)=m`   if `tau` is transcendental over `K_U`.`       `(PT13)`

In the second line the remaining shifted basis vector imports one nonzero rational multiple of
the new `tau`; in the first everything lies in `K_U(tau)`.  A period shift can therefore heal
the marked defect by exactly one external unit, or merely carry it; it cannot clone it.  This is
fully compatible with `(EH1)--(EH9)` and does not eliminate the source hyperplane.

The mixed boundary makes the field dichotomy numerical.  Conditionally suppose
`K=Q(e,ell)` has transcendence degree one, `ell=log 2`, and shift `(1,ell)`:

`K_k=Q(e,1+k_1*tau,ell+k_2*tau).`

The period is outside the rational span because the inputs are real.  If `tau` is algebraic over
`K`, every `K_k` has transcendence degree one.  If `tau` is transcendental over `K`, then

`td_Q K_0=1,    td_Q K_k=2 for every k!=0.`                     `(PT14)`

For `k_1!=0` one recovers `tau` and `ell`; for `k_1=0`, `k_2!=0`, the element
`ell+k_2*tau` is transcendental over `K`, hence over `Q(e)`.  The fully transcendental shear
`(2*ell+1,ell+1;4*e,2*e)` has the same coherent/off-coherent calculation.  Thus translation
either gives moving defect-one presentations or adds the external period; neither alternative
constrains the original field.

Finally, the new period-bearing normal form `(PB1)--(PB9)` allows one to choose the first case
`tau in span_Q(z)` from the outset.  Then `(PT2)` is the complete exceptional set and every
independent shift has *exactly the same field* `K`.  This strengthens the normal form but gives
no orbit contradiction: the common Q-Zariski closure is still the cylinder `(PT9)`, while the
individual defining ideals move.

Nothing here used primitivity, holomorphicity, or the size of the standard period, only
`tau!=0` and `exp(tau)=1`.  The orbit has no finite accumulation point, so the analytic identity
theorem does not propagate an algebraic relation.  The discontinuous character `(PT5)--(PT8)`
has the same lattice, field jumps, stabilized ideals, and hyperplane transport.  Holomorphicity
would distinguish it only through an infinitesimal graph direction, whereas the period orbit
closes to the horizontal translations `partial_(X_i)` and `(PT9)` discards that direction.
Therefore infinitely many same-value exponential points force an additive cylinder, not an
invariant mixed relation or a transcendence contradiction.

### The period-bearing witness can be based by two coordinates exactly one true period apart

The period-bearing normal form `(PB1)--(PB9)` admits the proposed sharp strengthening.

**Adjacent-period normal-form theorem.**  Schanuel's conjecture fails if and only if there are
`n>=2` and a family `w=(w_0,...,w_(n-1))` such that

`w` is Q-linearly independent,
`td_Q Q(w,exp(w))=n-1`,
`w_j and exp(w_j) are transcendental for every j`,
`w_1-w_0=omega=2*pi*I`.                                             `(AP1)`

In particular `exp(w_1)=exp(w_0)`.  The converse is immediate: the first two clauses in `(AP1)`
are already a length-`n` counterexample.  We prove the forward direction with exact basis and
field bookkeeping.

Start from the period-bearing fully transcendental defect-one witness supplied by `(PB2)`.  Write

`V=span_Q(z_1,...,z_n)`, `L=sum_i Z*z_i`,
`F=Q(z_i,exp(z_i):i<=n)`, `td_Q F=n-1`, `omega in V`.                `(AP2)`

Here `n>=2`.  The intersection of the lattice `L` with the rational period line is free of rank
one.  Let

`L intersection Q*omega=Z*v`, `v=rho*omega`, `rho in Q^*`,           `(AP3)`

with `v` primitive in `L`, and extend it to a Z-basis

`(v,x,b_2,...,b_(n-1))` of `L`.                                    `(AP4)`

At least one complementary basis element has transcendental exponential.  Otherwise
`exp(v)` and all `exp(b_j)` would be algebraic, and the unimodular inverse to `(AP4)` would express
every original `exp(z_i)` as an integral monomial in algebraic numbers, contradicting full
transcendence.  Reorder the complement so that

`t=exp(x)` is transcendental.                                      `(AP5)`

The input `x` itself need not yet be transcendental.  Among the progression
`x+k*omega`, `k in Z`, at most one term is algebraic: two algebraic terms would have nonzero
algebraic difference equal to an integral multiple of the transcendental number `omega`.
Consequently some `k in {0,1,2}` makes both

`p_0=x+k*omega`, `p_1=x+(k+1)*omega`                                `(AP6)`

transcendental.  They are Q-linearly independent, their difference is `omega`, and

`exp(p_0)=exp(p_1)=t`.                                              `(AP7)`

Moreover `(p_0,p_1,b_2,...,b_(n-1))` is a Q-basis of `V`: its inverse formulas begin

`omega=p_1-p_0`, `v=rho*(p_1-p_0)`, `x=(k+1)*p_0-k*p_1`.            `(AP8)`

It remains only to make the other displayed pairs transcendental.  For each `j>=2`, among

`b_j+c*p_0`, `c in {0,1,2}`,                                       `(AP9)`

at most one is algebraic, because the difference of two is a nonzero integral multiple of the
transcendental `p_0`.  Also at most one of

`exp(b_j)*t^c`, `c in {0,1,2}`,                                    `(AP10)`

is algebraic: the ratio of two algebraic choices would make a nonzero integral power of `t`
algebraic, hence make `t` algebraic.  The two exceptional choices in `(AP9)--(AP10)` leave at
least one of the three coefficients.  Choose such a `c_j` and set

`w_0=p_0`, `w_1=p_1`, `w_j=b_j+c_j*p_0  (j>=2)`.                    `(AP11)`

This is an upper-triangular integral shear of the rational basis in `(AP8)`, so it remains a
Q-basis.  Equations `(AP6)--(AP10)` prove every transcendence clause in `(AP1)`.  When `n=2`
there are no remaining `b_j`; `(AP6)` itself is the complete construction, so the arity-two edge
requires no separate assumption.

An arbitrary invertible rational basis change preserves the transcendence degree of the
coordinate-exponential field by Kummer algebraicity, but this construction permits sharper field
bookkeeping.  Put

`zeta=exp(v)=exp(rho*omega)`.                                       `(AP12)`

Writing `rho=a/d` in lowest terms gives `zeta^d=1`, so `zeta` is a root of unity.  Because
`(AP4)` is a Z-basis, the original field is exactly

`F=Q(v,x,b_j,zeta,t,exp(b_j):j>=2)`.                                `(AP13)`

Using `(AP7)--(AP11)` and the inverse formulas `(AP8)`, the new field is exactly

`F_w=Q(v,x,b_j,t,exp(b_j):j>=2)`.                                  `(AP14)`

Indeed the new exponential generators are `t,t,exp(b_j)*t^(c_j)`, and division by the known
powers of `t` recovers every `exp(b_j)`.  Therefore the strongest unconditional relation is

`F_w subset F`, `F=F_w(zeta)`, `[F:F_w]<infinity`,
`td_Q F_w=td_Q F=n-1`.                                              `(AP15)`

This proves the defect-one clause without losing an additional unit.  It also answers the exact
field-equality question: the construction gives

`F_w=F  iff  zeta in F_w`.                                         `(AP16)`

Equality is automatic if the primitive lattice period in `(AP3)` is an integral multiple of
`omega` (then `zeta=1`), and it is automatic after putting `Qbar` in the ground field.  It is not
a consequence of period-bearing defect one over `Q`.  For example, the lattice basis
`(x,x+omega/d)` has primitive period `omega/d` and exponential generators
`t,zeta_d*t`.  Replacing it by a pair one full period apart gives only the repeated generator
`t`; the cyclotomic constant `zeta_d` need not belong to the new field.  One can make this
obstruction literal with a generic `x`: choose `x,exp(x)` algebraically independent over the
countable field `Qbar(omega)`.  Then

`Q(x,omega,exp(x)) intersection Qbar=Q`,

so a nonrational `zeta_d` is genuinely absent, while both the old coordinates and exponential
values are transcendental.  At the abstract defect-one level the same phenomenon is completely
explicit.  Take `d>2`, put `x=omega^2`, and define a partial Q-additive character on
`Q*x direct_sum Q*omega` by

`E(x)=omega`, `E(omega/d)=zeta_d`, hence `E(omega)=1`.                `(AP16a)`

Then

`(x,x+omega/d;omega,zeta_d*omega)`

is Q-linearly independent and fully transcendental, its field is `Q(omega,zeta_d)` of
transcendence degree one, and that field is algebraic over either one-coordinate deletion.  The
adjacent pair `(x,x+omega)` instead has the repeated value `omega` and generated field
`Q(omega)`, which does not contain `zeta_d` because a rational function field over `Q` has no
new algebraic constants.  Thus `(AP15)`, not unconditional literal equality, is the invariant
statement; defect and transcendence degree are intentionally blind to finite cyclotomic
constants.

The structural package is formalized in `Schanuel/AdjacentPeriodDeletion.lean` and
`Schanuel/AdjacentPeriodNormalForm.lean`.  Its definition is

`PeriodPairedDefectOne (w : Fin (n+2) -> C) :=`
`  LinearIndependent Q w ∧ DefectOne w ∧`
`  (forall i, Transcendental Q (w i)) ∧`
`  (forall i, Transcendental Q (exp (w i))) ∧`
`  w 1-w 0=period`.                                                 `(AP17)`

and the checked theorem is

`not Conjecture <-> exists n w, PeriodPairedDefectOne w`.           `(AP18)`

The proof extracts `omega=sum_i c_i*z_i`, permutes a nonzero coefficient to index `1`, and uses
the explicit rows `e_0+k*c`, `e_0+(k+1)*c`, and `e_i` for `i>=2`.  The determinant calculation is
literally `det B=c_1`, by one row replacement and two determinant-preserving row additions.  If
the first period shift is transcendental take `k=0`; otherwise its algebraicity makes the shifts
at `2` and `3` transcendental, so take `k=2`.  Rational-basis invariance then preserves linear
independence and exact defect one, while the explicit row formulas prove the adjacent-period and
pointwise transcendence clauses.

The exact cyclotomic formula `(AP15)` would still require an additional
lattice/Smith-normal-form layer and intermediate-field membership proofs.  It is not needed for
`(AP18)`: the checked rational-basis transcendence-degree invariance avoids the stronger and
false unconditional field-equality claim.

### Quotienting the repeated exponential removes exactly the allowed period normal

The adjacent-period form `(AP1)` makes the proposed kernel quotient completely explicit, but it
does not recover the missing transcendence-degree unit.  Write the length as `m`, put

`y_j=exp(w_j),   omega=w_1-w_0,   y_1=y_0`,                         `(KQ1)`

and let

`A=Q[X_0,...,X_(m-1),Y_0^+-,...,Y_(m-1)^+-]`,
`I=ker(A -> C, (X,Y) |-> (w,y))`.                                  `(KQ2)`

Here `I` is prime, `dim A=2m`, and defect one says

`dim(A/I)=m-1,   ht(I)=m+1`.                                       `(KQ3)`

Use the unimodular additive/toric coordinates

`U_0=X_1-X_0, U_1=X_0, U_j=X_j (j>=2)`,
`V_0=Y_1/Y_0, V_1=Y_0, V_j=Y_j (j>=2)`.                            `(KQ4)`

The binomial `Y_1-Y_0` generates the same ideal as `V_0-1`.  It already belongs to `I`; hence
factoring the *ambient* coordinate ring by it does not factor the locus by any further relation:

`A'=A/(V_0-1) = Q[U_0,...,U_(m-1),V_1^+-,...,V_(m-1)^+-]`,
`I'=I/(V_0-1),   A'/I'=A/I`.                                      `(KQ5)`

Consequently

`dim A'=2m-1,   dim(A'/I')=m-1,   ht(I')=m`.                       `(KQ6)`

Thus the rational binomial lowers the ambient dimension and the codimension by exactly one and
does not lower the locus dimension.  Geometrically this is restriction to the kernel subtorus of
the character `Y |-> Y_1/Y_0`, followed by its identification with `G_m^(m-1)`; it is not a
quotient of the locus by a positive-dimensional group action.  The induced point is

`q=(omega,w_0,w_2,...,w_(m-1); y_0,y_2,...,y_(m-1))`
`  in G_a^m x G_m^(m-1)`,                                          `(KQ7)`

and its field is still exactly `Q(w,y)`.

The conormal calculation records the same cancellation infinitesimally.  Put `B=A/I=A'/I'` and
tensor at the generic point of `Spec B`.  Since the coordinate `V_0-1` is not in `I^2` (apply
`partial/partial V_0` and reduce modulo `I`), the standard conormal sequence is short exact:

`0 -> Frac(B)*dlog(V_0) -> (I/I^2) tensor_B Frac(B)`
`  -> (I'/(I')^2) tensor_B Frac(B) -> 0`.                           `(KQ8)`

Its ranks are `1 -> m+1 -> m`.  On the exponential graph,

`dlog(V_0)=dlog(Y_1)-dlog(Y_0)=dX_1-dX_0=dU_0`.                    `(KQ9)`

The analytic inverse image of `V_0=1` is not one hypersurface but

`union_(r in Z) {U_0=r*omega}`.                                    `(KQ10)`

On the chosen component `U_0=omega`, `(KQ9)` vanishes.  Hence the repeated-value binomial
contributes precisely the normal that freezes the period direction; it supplies no second normal
and no algebraic equation over `Q` for the transcendental value `omega`.

This is also visible in an exact expected-dimension equality.  After `(KQ5)`, forget the
exponential of `U_0` and consider

`Gamma_rel={(u;v):v_j=exp(u_j), j=1,...,m-1}`
`  subset G_a^m x G_m^(m-1)`.                                     `(KQ11)`

It has analytic dimension `m`, while the algebraic locus has dimension `m-1` and the ambient
space dimension `2m-1`.  Thus their expected intersection dimension is exactly zero.  The
apparently overdetermined intersection before quotienting was entirely the allowed equation
`exp(omega)=1`.

Topology gives the same information and no more.  The character in `(KQ4)` transforms the
universal covering lattice unimodularly.  Its diagonal subtorus has inverse image `(KQ10)`; the
integer `r=1` is merely the connected-component label.  On that component the remaining covering
sequence is

`0 -> omega*Z^(m-1) -> C^(m-1) -> (C^*)^(m-1) -> 1`.               `(KQ12)`

Neither its fundamental group nor the component label relates `omega` algebraically to the
remaining values `y_j`.

The precise missing statement can now be isolated.  For every tuple `a=(a_1,...,a_r)` for which
`(omega,a_1,...,a_r)` is Q-linearly independent, one would need

`td_(Q(omega)) Q(omega,a,exp(a)) >= r`.                             `(KQ13)`

Since `omega` is transcendental, `(KQ13)` is exactly Schanuel's inequality for the tuple
`(omega,a)`, because `exp(omega)=1`.  Conversely, the period-bearing normal form `(PB1)--(PB9)`
(or the stronger adjacent form `(AP1)`) turns any failure of Schanuel into a failure of `(KQ13)`
after a rational basis change.  Therefore `(KQ13)` for all `r,a` is equivalent to full Schanuel,
not an available relative period-lattice theorem.  Under the defect-one hypothesis above,

`td_(Q(omega)) Q(w,y)=(m-1)-1=m-2`,                                `(KQ14)`

so `(KQ13)` is missing exactly one unit.

The analytic subgroup theorem cannot provide it: that theorem starts with a logarithm of an
algebraic point of a commutative algebraic group, whereas `(KQ7)` has transcendental additive and
multiplicative coordinates.  The algebraic point `1 in G_m` sees the allowed period lattice only.
Likewise, an algebraic one-motive `[Z -> G_m]` may use an algebraic torus point, but the fully
transcendental `y_j` are not such points.  Changing the ground field to one containing them leaves
the number-field/motivic setting and simply repackages `(KQ13)`.  Known one-motive period theorems
control linear period relations and do not assert this algebraic-independence inequality.

The arity-two stress makes the boundary literal.  For

`(w_0,w_1)=(1+omega,1+2*omega),   (y_0,y_1)=(e,e)`,                 `(KQ15)`

the quotient point is `(omega,1+omega;e) in G_a^2 x G_m`.  A
hypothetical algebraic dependence `P(omega,e)=0` gives the codimension-two curve

`U_1-U_0-1=0,   P(U_0,V_1)=0`;                                    `(KQ16)`

before quotienting there is only the additional normal `V_0-1=0`.  Inequality `(KQ13)` is now
`td_(Q(omega)) Q(omega,e)>=1`, exactly algebraic independence of `e` and `pi`.  Thus the quotient
does not simplify even the first open stress.

Finally, a continuous period character shows that algebraic-group and covering-space data alone
cannot prove the missing unit.  Let `lambda=Log(omega)=log(2*pi)+pi*I/2` (principal branch), and
define the invertible real-linear map

`L(x+t*omega)=x*lambda+t*omega   (x,t in R)`,
`E_L(z)=exp(L(z))`.                                                  `(KQ17)`

Because `Re(lambda)!=0`, `L` is a real-linear homeomorphism; it fixes `omega`, so `E_L` is a
continuous universal covering homomorphism with kernel exactly `omega*Z`.  It is not holomorphic.
Moreover `E_L(1)=omega`, and therefore the same inputs as `(KQ15)` satisfy

`E_L(1+omega)=E_L(1+2*omega)=omega`,
`Q(1+omega,1+2*omega,omega)=Q(omega)`,                              `(KQ18)`

of transcendence degree one.  Both inputs and both displayed values are transcendental, and the
inputs are Q-linearly independent.  Their full rational algebraic locus is already the curve

`X_1-2*X_0+1=0,   Y_0-X_1+X_0=0,   Y_1-Y_0=0`.                    `(KQ19)`

Thus `(KQ17)--(KQ19)` preserve the kernel, universal-cover topology, binomial quotient,
dimensions, and conormal count while saturating defect one.  Holomorphicity distinguishes the
standard exponential, but no existing topological, analytic-subgroup, or one-motive theorem
turns that distinction into `(KQ13)`.  The kernel quotient is exact bookkeeping, not the missing
transcendence mechanism.

### Adjacent-pair deletion has an exact two-step cycle

There is a useful deletion dichotomy after `(AP1)`, but iterating it does not force the terminal
branch.  Let `w=(w_0,...,w_(n-1))` satisfy `(AP1)`, set

`v=(w_0,w_2,...,w_(n-1))`,
`F=Q(v,exp(v))`, `K=Q(w,exp(w))`.                                  `(DT1)`

Since `w_1=w_0+omega` and `exp(w_1)=exp(w_0)`, one has the exact equality

`K=F(omega)`.                                                       `(DT2)`

In particular

`epsilon=td_F F(omega) in {0,1}`,
`td_Q F=td_Q K-epsilon=n-1-epsilon`.                               `(DT3)`

Deletion preserves Q-linear independence and all coordinatewise transcendence clauses.  Thus
there are exactly two branches:

* if `epsilon=0`, then `td_Q F=n-1`, so the length-`n-1` tuple `v` meets Schanuel's lower bound
  with equality, and `omega` is algebraic over `F`;
* if `epsilon=1`, then `td_Q F=n-2`, so `v` is itself a fully transcendental defect-one failure
  of length `n-1`, and `omega` is transcendental over `F`.          `(DT4)`

There is no third possibility and no hidden finite extension in `(DT2)`: the only deleted input
is recovered as `w_0+omega`, and its exponential was already present.

The second branch gives a literal cycle, not merely a possible increase under an inefficient
normalization.  Starting with its smaller failure `v`, apply the period augmentation

`A(v)=(w_0,w_0+omega,w_2,...,w_(n-1))`.                            `(DT5)`

The result is exactly `w`, with no basis change at all.  Original Q-linear independence proves
the augmented family's independence; `epsilon=1` raises transcendence degree from `n-2` to
`n-1`, and the repeated exponential gives the adjacent-period form.  If `D` denotes deletion of
the second coordinate, then

`D(A(v))=v,   A(D(w))=w`.                                          `(DT6)`

Consequently no invariant of these tuple/field states can be strictly well founded under both
the deletion and the period-normalization step: their composite is the identity.  In particular,
lexicographic combinations of arity with the algebraic/transcendental status of `omega` simply
alternate

`(n, adjacent) -> (n-1, omega transcendental over F) -> (n, adjacent)`, `(DT7)`

and algebraic extension degree is unavailable in the middle arrow because `F(omega)/F` is purely
transcendental of degree one.  Heights cannot repair an identity cycle, and there is no canonical
arithmetic height for the transcendental adjunction in any case.

Minimal arity sharpens, but does not remove, this obstruction.  Let `r` be the least arity of an
arbitrary Schanuel failure.  The period-bearing construction gives an adjacent witness of arity
either `r` or `r+1`:

* if an adjacent witness exists already in arity `r`, its deletion cannot be a failure, so it is
  necessarily in the `epsilon=0` branch;
* if a minimal failure field does not algebraize `omega`, adjoining the period produces an
  adjacent witness in arity `r+1`, and its deletion is precisely the arity-`r` failure in the
  `epsilon=1` branch.                                               `(DT8)`

Thus minimality proves a conditional statement about an adjacent witness of minimal *general*
arity; it does not prove that such a witness exists.  Minimizing only among adjacent witnesses
also gives no contradiction, because deletion leaves that class.

The cycle is realized unconditionally for an abstract exponential character with the exact
standard kernel.  For `n>=3`, choose complex numbers

`t_1,...,t_(n-2)` algebraically independent over `Q(omega)`         `(DT9)`

and, by countable avoidance, so that chosen logarithms of
`t_1,t_1+1,t_2,...,t_(n-2)` together with `omega` are Q-linearly independent.  There is then a
Q-linear automorphism `B:C->C` satisfying

`B(omega)=omega, B(t_1)=Log(t_1), B(t_1^2)=Log(t_1+1),`
`B(t_j)=Log(t_j) (2<=j<=n-2)`.                                    `(DT10)`

Indeed the displayed source and target families are Q-linearly independent and may be extended
to Hamel bases.  Put `E=exp o B`.  Since `B` is injective and fixes `omega`,

`ker(E)=omega*Z`.                                                   `(DT11)`

For

`w=(t_1,t_1+omega,t_1^2,t_2,...,t_(n-2))`,                         `(DT12)`

with the evident omission of the final range when `n=3`, one has

`E(w)=(t_1,t_1,t_1+1,t_2,...,t_(n-2))`,
`Q(w,E(w))=Q(omega,t_1,...,t_(n-2))`,
`td_Q Q(w,E(w))=n-1`.                                              `(DT13)`

Every displayed input and output is transcendental, and the inputs are Q-linearly independent.
Deleting `t_1+omega` gives

`F=Q(t_1,...,t_(n-2)),   td_Q F=n-2,`
`omega transcendental over F`;                                    `(DT14)`

adjoining that same coordinate recovers `(DT12)` exactly.  This exact-kernel model rules out any
descent argument using only additivity, the period lattice, transcendence-degree towers, or
coordinatewise transcendence.  Its discontinuity marks the analytic input that such an argument
would still have to exploit.

Arity two is forced into the other branch.  Write an adjacent pair as

`w=(x,x+omega)`, `t=exp(x)`, `F=Q(x,t)`.                            `(DT15)`

Both `x` and `t` are transcendental in `(AP1)`, so `td_Q F>=1`.  Defect one gives
`td_Q F(omega)=1`; hence necessarily

`td_Q F=1,   omega algebraic over F,   epsilon=0`.                  `(DT16)`

For the exact stress `(x,x+omega)=(1+omega,1+2*omega)`, one has

`F=Q(1+omega,e)=Q(omega,e)`                                        `(DT17)`

and `omega` already belongs to `F`.  The defect-one assertion is therefore

`td_Q Q(omega,e)=1`, equivalently `e` algebraic over `Q(omega)`,    `(DT18)`

which is precisely failure of algebraic independence of `e` and `pi`.  Reaching `epsilon=0`
does not prove Schanuel: it terminates the deletion only at the original open boundary.

The deletion part is now checked in `Schanuel/AdjacentPeriodDeletion.lean`.  In particular,
`generatedField_eq_adjacentPeriodAdjoinField` proves the literal equality `(DT2)`,
`relative_trdeg_adjacentDeletion_eq_zero_or_one` proves the `0/1` alternative, and
`adjacentDeletion_defectOne_dichotomy` packages `(DT3)--(DT4)` together with preservation of
rational linear independence and both pointwise transcendence conditions.

The full forward implication of `(AP18)` is now checked in
`Schanuel/AdjacentPeriodNormalForm.lean`, without a basis-extension choice.  If
`omega=sum_i c_i*z_i`, permute a nonzero coefficient to `c_1`.  For `k` equal to `0` or `2`, use
the rational matrix with rows

`r_0=e_0+k*c,   r_1=e_0+(k+1)*c,   r_i=e_i (i>=2)`.                `(DT19)`

Replacing row `1` of the identity by `c` gives determinant `c_1`; the other two row additions
preserve it.  Hence the matrix is invertible.  Its first two values are
`z_0+k*omega` and `z_0+(k+1)*omega`, so they differ by `omega` and have the same exponential.
If the shift at `1` is transcendental, take `k=0`; if it is algebraic, adding one and two
transcendental periods shows that the shifts at `2` and `3` are transcendental, so take `k=2`.
All later coordinates and exponentials are unchanged.  The checked rational-basis invariance
then preserves linear independence and exact defect one.  Thus
`not_conjecture_iff_exists_periodPairedDefectOne` proves the literal two-way equivalence `(AP18)`.

### A canonical `(1+omega,1+2*omega)` anchor follows at the subspace level

The adjacent-period normal form gives a clean canonical-anchor reduction, but its natural proof
is basis-independent.  Put `omega=2*pi*I`, `A=span_Q{1,omega}`, and for a finite-dimensional
rational input space `S` write

`delta(S)=td_Q Q(b,exp(b))-dim_Q S`,                              `(CA1)`

where `b` is any rational basis of `S`.  This is well-defined: after a rational change of basis,
clearing one common denominator makes every new exponential a root of a Laurent monomial in the
old exponentials, and the inverse change gives mutual algebraicity.  The same rectangular
denominator argument gives transcendence-degree monotonicity when `S subset T`.

Start with the checked adjacent-period defect-one witness space `S`, so `omega in S` and
`delta(S)=-1`.  Set `T=S+Q*1`.  If `1 in S`, then `T=S`.  Otherwise `(1,b)` is a basis of `T` and

`Q(1,b,e,exp(b))=Q(b,exp(b))(e)`,                                 `(CA2)`

so both dimension and transcendence degree rise by at most one.  Hence `delta(T)<=-1` in either
case, and `A subset T`.  This avoids an unjustified exact-field assertion: arbitrary rational
basis changes are only mutually algebraic because of Kummer roots, while the literal adjunction
of `1` in `(CA2)` is exact.

Choose a failing `R` of least dimension among the rational subspaces with
`A subset R subset T`.  Then every proper rational subspace `H<R` containing `A` satisfies its
Schanuel bound.  If `d=dim R>2`, extend a basis of `A` by a complement and delete one complement
vector.  The resulting `H` has dimension `d-1`, so minimality and monotonicity give

`d-1 <= td_Q Q(H,exp H) <= td_Q Q(R,exp R) < d`.                  `(CA3)`

Thus the last transcendence degree is exactly `d-1`.  If `d=2`, then `R=A` and its anchor field
is exactly `Q(omega,e)`; transcendence of either `omega` or `e` gives the same lower bound `1`,
while failure gives the upper bound `<2`.  This shows why the canonical theorem must allow the
length-two case: it is precisely the unresolved possibility `td_Q Q(omega,e)=1`.

Take the first two basis vectors of `R` to be

`a_0=1+omega,   a_1=1+2*omega`.                                  `(CA4)`

They are a basis of `A`, both are transcendental, and both exponentials equal the transcendental
number `e`.  For each complementary basis vector `b_j`, among `b_j+c*a_0`,
`c in {0,1,2}`, at most one value can be algebraic: two algebraic values would make a nonzero
integral multiple of `a_0` algebraic.  At most one of their exponentials can be algebraic: two
would have quotient `e^(c-d)`, which is transcendental for `c!=d`.  The union of the two bad sets
has size at most two, so one coefficient makes both values transcendental.  Applying these
choices simultaneously is an integral unipotent shear.  It fixes `(CA4)`, preserves the input
space and generated field exactly, and makes every coordinate and exponential transcendental.

Consequently the exact mathematical normal form is

`not Conjecture  iff  exists n w:Fin(n+2)->C,`                    `(CA5)`
`  LinearIndependent_Q w and DefectOne w and`
`  (forall i, Transcendental_Q(w_i) and Transcendental_Q(exp w_i)) and`
`  w_0=1+omega and w_1=1+2*omega`.                                `(CA6)`

The forward witness can additionally be chosen so that every proper rational input subspace
containing `A` satisfies `Bound`; the reverse implication is immediate from independence and
defect one.

This equivalence is now checked in `Schanuel/CanonicalAnchorNormalForm.lean`.  The rectangular
Kummer lemma clears one common positive denominator and compares the resulting integral family;
the prescribed-basis theorem uses `Basis.sumExtend` and a finite reindexing to `Fin (n+2)`.
Least arity among anchored failures supplies defect one: at positive complement arity one deletes
the final complement, while at complement arity zero the transcendental first anchor supplies the
required lower bound.  Finally, the ordinary coordinate-transcendence shear followed by the
full-transcendence shear uses the first anchor as pivot; both anchor coefficients are zero at both
stages.  No basis-independent field object or weakened statement is needed.

### The terminal alternative is disjoint over the independent anchor field

The canonical terminal form admits an exact relative refinement.  Put

`c=(omega,e)`, `B=Q(c)=Q(canonicalAnchor,exp(canonicalAnchor))`.    `(RT1)`

The checked two-generator presentation gives `td_Q B<=2`, while transcendence of `omega` gives
`td_Q B>=1`.  The fully transcendental period-boundary theorem identifies its upper endpoint:

`td_Q B=1 iff c is algebraically dependent over Q`,
`td_Q B=2 iff c is algebraically independent over Q`.            `(RT2)`

Consequently the terminal equivalence can be made logically disjoint:

`not Conjecture iff`
`  (c is algebraically dependent) or`
`  (c is algebraically independent and there is a positive terminal witness).` `(RT3)`

In the second branch let `w:Fin(n+3)->C`, let `v` delete its final complementary input, and put

`F=Q(v,exp(v))`, `K=Q(w,exp(w))`.                                 `(RT4)`

The anchor inclusion is literal, and the terminal theorem gives

`td_Q B=2`, `td_Q F=n+2`, `[K:F]<infinity`.                       `(RT5)`

The transcendence-degree tower and finite-cardinal cancellation therefore give the exact
relative equality

`td_B F=n`.                                                       `(RT6)`

Both the missing input `b` and `exp(b)` are algebraic over `F`.  Thus the higher-arity branch is
not allowed to hide the unresolved dependence of `e` and `pi` inside its base: it is precisely a
finite algebraic graph extension of a relative equality field over an already independent
two-dimensional anchor.

Equations `(RT2)--(RT6)` are formalized in
`Schanuel/CanonicalAnchorRelativeTerminal.lean`, including generator inclusion, the relative
field tower, and the exact equivalence `(RT3)`.  This isolates rather than proves the missing
assertion.  The field `F/B` need not be rational, finite over a pure transcendental extension in
a controlled way, or self-sufficient against graph extensions.  Excluding a new input outside
the rational input span with both it and its exponential algebraic over such an `F` is exactly
the relative arithmetic statement still needed; ordinary tower additivity alone gives no lower
bound for that last zero-dimensional extension.

### The terminal algebraic graph extension is a simple isolated intersection, not a contradiction

The checked terminal dichotomy sharpens the positive branch as follows.  Write

`F=Q(v,exp(v)),  K=F(b,exp(b)),  td_Q F=td_Q K=len(v)`,            `(CT1)`

where `v` retains the literal anchors and `K/F` is algebraic.  Hence both `b` and `exp(b)` are
algebraic over `F`.  Let `A(T),B(U) in F[T]` be their monic minimal polynomials.  Characteristic
zero makes both separable, so

`A'(b)!=0,   B'(exp(b))!=0`.                                      `(CT2)`

Thus the algebraic point `(b,exp(b))` is already a nonsingular zero of the square algebraic
system

`A(X)=0,  B(Y)=0`,                                                `(CT3)`

whose Jacobian determinant is `A'(b)B'(exp(b))!=0`.  Pulling back to the analytic exponential
graph gives two one-variable germs

`A(b+s),   B(exp(b+s))`,                                         `(CT4)`

with derivatives `A'(b)` and `exp(b)B'(exp(b))`, respectively.  Both derivatives are nonzero.
Consequently either germ alone generates the maximal ideal `(s)` in `C{s}`, and

`C{s}/(A(b+s),B(exp(b+s))) = C`,  `length=1`.                     `(CT5)`

Equivalently, in `C{X-b,Y-exp(b)}` the ideal generated by `(CT3)` is already the maximal ideal.
Adding the analytic graph equation `Y-exp(X)` changes neither the quotient nor its length.  The
Grothendieck residue of the square system is the ordinary simple-point value

`Res dX wedge dY/(A(X)B(Y)) = 1/(A'(b)B'(exp(b)))`;               `(CT6)`

it lies in a finite algebraic extension of `F` but need not lie in `Q`, or even in the fixed
anchor field `Q(e,2*pi*I)`.

This is a nonsingular Khovanskii system *over `F`* in the vacuous strongest sense: the ordinary
polynomial equation `A(X)=0` already isolates `b`, without using exponentiation.  It does not
descend to a rational-coefficient Khovanskii system.  The extension `K/F` is finite, but `F/Q` is
transcendental of positive degree in this branch, so trace and norm only descend coefficients
from `K` to `F`.  The two fixed elements `e` and `2*pi*I` inside `F` provide no finite
`F/Q(e,2*pi*I)` descent and no control of the remaining equality-tuple parameters.

Holomorphicity therefore supplies exactly isolated transversality: the graph meets the selected
finite algebraic fiber with local multiplicity one.  It creates no positive-dimensional graph
germ, repeated zero, residue integrality, or extra transcendence degree.  Any successful use of
`(CT1)` must add an arithmetic theorem descending the `F`-coefficients while preserving the
selected analytic branch; ordinary separability, the implicit-function theorem, Jacobians,
local residues, and intersection multiplicity all certify the counterfeit instead of excluding
it.

### Arithmetic specialization cannot retain the canonical exponential graph

The positive terminal branch does admit an exact finite-type arithmetic model, but its
quantifiers stop before any exponential compatibility.  With

`F=Q(v,exp(v)),  K=F(b,exp(b)),  [K:F]<infinity`,                 `(PS1)`

choose a finitely generated Q-domain `R subset F` with fraction field `F` containing all named
deletion generators and the coefficients needed to express the two missing elements.  After
localizing once, the integral closure `S` of `R` in `K` is finite, contains `b,exp(b)`, and may be
taken finite etale over a nonempty open of `Spec R`.  Thus every closed point of that open and a
point above it specialize all *polynomial* identities into finite extensions of Q.  In
particular they retain

`2*v_0-v_1=1,   y_0=y_1,`                                        `(PS2)`

and the algebraic recovery equations for `b` and `y_b`.  They do not retain
`y_i=exp_C(v_i)`: those identities hold at the generic complex embedding but are not equations
of the finite-type Q-model.

In fact no specialization can impose the standard p-adic exponential simultaneously on the two
anchors.  Normalize `v_p(p)=1` and let

`D_p={x in C_p : v_p(x)>1/(p-1)}`.                               `(PS3)`

On `D_p`, `Exp_p` is injective, with the formal logarithm as inverse on its image.  For every
prime `p` and every homomorphism `phi:S->C_p`, if

`phi(v_0),phi(v_1) in D_p` and
`phi(y_j)=Exp_p(phi(v_j))  (j=0,1)`,                              `(PS4)`

then `(PS2)` gives `Exp_p(phi(v_0))=Exp_p(phi(v_1))`, hence
`phi(v_0)=phi(v_1)`.  The first equation in `(PS2)` then gives `phi(v_0)=1`, contradicting
`1 notin D_p`.  The logarithmic formulation is identical: equal `y_0,y_1` have equal formal
logs, while the log image lies in the maximal ideal and cannot contain `1`.  Unlike the complex
exponential, the local p-adic exponential has no nonzero period available to receive `omega`.

Nor can one force the missing input into a useful p-adic graph separately.  Positive valuation
`v_P(phi(b))>0` is a congruence condition on a chosen arithmetic point and place, not a
consequence of `K/F` being finite.  Even when it is arranged, the condition

`phi(y_b)=Exp_p(phi(b))`                                         `(PS5)`

is the infinite family of congruences

`phi(y_b)-sum_(r<N) phi(b)^r/r! = O(P^(N*c-N/(p-1)))`             `(PS6)`

for all `N`, where `c=v_P(phi(b))>1/(p-1)`.  A finite list of algebraic recovery equations does
not imply this tower.  Conditions `b=0 mod P` and `y_b=1 mod P` already require the relevant two
divisors to meet in the chosen fiber, which is not guaranteed by dominance or by the lying-over
theorem.

The quantitative product-formula balance is unfavorable even if `(PS5)` is inserted by hand.
For `L` containing the specialized values, put

`E_N=sum_(r=0)^(N-1) phi(b)^r/r!`,  `delta_N=phi(y_b)-E_N`.        `(PS7)`

Legendre's estimate gives

`v_P(delta_N)>=N*(c-1/(p-1))`                                   `(PS8)`

under exact p-adic graph compatibility.  But elementary height inequalities give

`h(E_N)<= (N-1)h(phi(b))+log((N-1)!)+log N`,
`h(delta_N)<=h(phi(y_b))+h(E_N)+log 2`.                           `(PS9)`

The product formula therefore pays at least the same linear valuation cost and an additional
factorial denominator cost; `(PS8)` supplies no missing transcendence unit.  Moreover any
infinite sequence of distinct algebraic specializations with both degree and coordinate heights
bounded is excluded by Northcott, so an approximation sequence necessarily loses uniform degree
or height control.

There is a sharp algebraic/exponential-character counterfeit.  For `d>=2`, take

`F_0=Q(T,E,U_2,...,U_(d-1))`,
`v_0=1+T, v_1=1+2*T, y_0=y_1=E`,
`v_i=U_i, y_i=U_i+1`,
`b=T^2, y_b=E+T`.                                                `(PS10)`

The `d+1` inputs are Q-linearly independent, every displayed value is transcendental, the
deletion field and full field are both `F_0` of transcendence degree `d`, and both missing values
are algebraic over the deletion field.  A discontinuous character can be prescribed by
`Echar(1)=E`, `Echar(T)=1`, `Echar(U_i)=U_i+1`, and
`Echar(T^2)=E+T`, then extended along a Q-basis.  Thus `(PS10)` realizes the entire finite-type
terminal package and the finite selected exponential identities.  Yet `(PS3)--(PS4)` excludes
every standard p-adic graph specialization of its anchors.

Consequently arithmetic specialization offers no bridge from the checked terminal field tower
to p-adic analytic subgroup theorems.  A usable theorem would have to produce one *fixed*
number-field specialization satisfying the infinite graph condition `(PS5)`, with a convergence
prime and uniform degree/height bounds.  The terminal algebraic data supply none of these
quantifiers, and the canonical anchor actually forbids imposing them on the whole tuple.

### The full period orbit saturates one special coset and no individual field

The terminal pair has an infinite genuine graph orbit, but its three relevant Zariski closures
are different.  Let `a=(v,exp(v))`, so `F=Q(a)` has transcendence degree `d=len(v)`, let
`K=F(b,y)` be finite with `y=exp(b)`, and put `omega=2*pi*i in F`.  For

`P_k=(a,b+k*omega,y),  k in Z`,                                  `(PO1)`

every point is on the complex exponential graph and

`Q(P_k)=K`,  `td_Q Q(P_k)=d`.                                    `(PO2)`

Nevertheless, if `m_y(Y) in F[Y]` is the minimal polynomial of `y`, then the closure of the
last pair over `F` is

`V_F(m_y(Y)) subset Ga x Gm`,                                    `(PO3)`

a one-dimensional integral `F`-scheme which splits over `C` into the conjugate horizontal
lines; the selected complex closure is simply `Y=y`.  Indeed a polynomial vanishing at
`(b+k*omega,y)` for all integers `k` becomes a one-variable polynomial with infinitely many
roots, hence vanishes identically in the additive coordinate.

Over Q, `y` is transcendental by the fully transcendental terminal package.  The same coefficient
argument therefore gives

`Zcl_Q{P_k}=Loc_Q(a,y) x A1`,
`dim Zcl_Q{P_k}=td_Q Q(a,y)+1=d+1`.                               `(PO4)`

Thus the union reaches the expected Schanuel dimension although every individual member still
has transcendence degree `d`.  The added dimension records infinitely many moving Q-loci under
the rational shears `b mapsto b+k*(v_1-v_0)`; it cannot be specialized back to the original
point.

The group-theoretic reason is exact.  In `G=Ga x Gm`, let

`H=Ga x {1}`,  `Gamma=< (omega,1) >`.                             `(PO5)`

The cyclic subgroup `Gamma` is Zariski dense in `H`, and `(b,y)Gamma` is dense in the coset
`(b,y)H`.  The algebraic quotient `G/H=Gm` maps the entire integer orbit to the single point
`y`.  There is no algebraic quotient of `Ga` by the discrete analytic lattice `omega*Z`: its
algebraic closure is all of `Ga`, so the quotient consumes exactly the apparent infinitude.
Laurent's toric theorem is not directly applicable before quotienting because of the additive
factor; after quotienting, the integer orbit is the single torus point `y`.  More general
Mordell--Lang formulations see the allowed special case of a coset of a subgroup, not an
exceptional intersection requiring finiteness.

Rational division makes the saturation particularly transparent.  Choose
`eta_q=exp(b/q)`, so `eta_q^q=y`.  Dividing the full orbit gives

`P_(q,k)=((b+k*omega)/q, eta_q*zeta_q^k)`,                        `(PO6)`

with `k` taken modulo `q` for the horizontal components and then modulo translations by
`omega`.  For fixed `q`, its complex closure is the union of the `q` lines

`Y^q=y`;                                                           `(PO7)`

over `F` the reduced equation is `m_y(Y^q)=0`.  But the union over all `q` is Zariski dense in
`Ga x Gm` even over `F`: a polynomial of fixed `Y`-degree cannot vanish on all `q` distinct roots
once `q` exceeds that degree.  After quotienting by `H`, the integer orbit is one point while
the division orbit becomes the set of all roots of `y`, which is infinite and hence dense in
`Gm`.

This quotient dimension is entirely Kummer-theoretic.  Every `eta_q` is algebraic over `F(y)`,
with degree at most `q`, so no individual division point adds transcendence degree.  In the
generic saturation model `(PS10)`, `Y^q-(E+T)` is irreducible over
`Q(T,E,U_2,...)` (use the prime divisor `E+T`), so the degrees are exactly `q`; at
number-field specializations
`h(eta_q)=h(y)/q` while the degrees escape.  This is precisely how Northcott compactness is
avoided.

Functional transcendence also certifies, rather than forbids, the picture.  The entire curve

`gamma(t)=(b+omega*t, y*exp(omega*t))`                            `(PO8)`

has full two-dimensional algebraic closure over the constant field, as predicted by Ax's
functional theorem.  Its intersection with the horizontal coset occurs at every integer because

`g(t)=exp(2*pi*i*t)-1`                                            `(PO9)`

has precisely those zeros.  This is the sharp growth regime: `g` has exponential type `2*pi`
(after the standard symmetric normalization, `sin(pi*t)` has the boundary type `pi`), so
Carlson uniqueness hypotheses requiring strictly smaller type fail.  Moreover

`N(r,0,g)=2*r+O(log r)`,  `T(r,exp(2*pi*i*t))=2*r+O(1)`,           `(PO10)`

so Nevanlinna zero counting is saturated with no excess.  Ax--Schanuel applies to the generic
parameter `t`, not to a discrete set of constant specializations; unlikely-intersection bounds
discard exactly the weakly special coset `(b,y)H` responsible for the lattice.

Hence the period orbit contributes one geometric direction and quotienting consumes it exactly.
The rational-division tower leaves a dense multiplicative quotient, but only through unbounded
finite Kummer extensions.  It supplies no second anomalous transcendence unit and no bound for
the original terminal point.

### Continuous Kummer coherence trades approximation for unbounded degree

Let `S` be a conjugation-stable rational input space containing `1,omega`, choose a Q-basis
`w_1,...,w_m`, and put

`F=Q(w_1,...,w_m, exp(w_1),...,exp(w_m))`.                        `(RA1)`

The anchors make the real span of `S` equal to `C`, while its rational span is dense there.  For
`q=(q_i) in Q^m`, let `D` clear all denominators and set

`z_q=sum_i q_i*w_i`,  `u_q=exp(z_q)`.

Then the genuine analytic branch satisfies the exact Kummer equation

`u_q^D=product_i exp(w_i)^(D*q_i) in F`,  `[F(u_q):F]<=D`.         `(RA2)`

Thus continuity does select a coherent root with `u_q->1` whenever `z_q->0`, but it does not
put those roots in one bounded extension.  The coherence is

`u_(q/N)^N=u_q`;                                                  `(RA3)`

it is a point of the inverse Kummer tower, not an algebraic section of that tower over `F`.
For the terminal pair `K=F(b,y_b)`, the nearby genuine graph points are exactly

`(b+z_q, y_b*u_q) in K(u_q)^2`,  `[K(u_q):F]<=D*[K:F]`.           `(RA3a)`

They converge to `(b,y_b)` at the selected embedding, but their algebraic recovery branches
move through this unbounded tower.

There are two quantitatively different approximation regimes.  The first is rational division.
Already the canonical input `a=1+omega` gives

`z_N=a/N`, `u_N=exp(a/N)=exp(1/N)*zeta_N`, `u_N^N=e`,
`u_(MN)^M=u_N`,                                                   `(RA4)`

and

`|z_N|=|1+omega|/N`,
`u_N-1=(1+omega)/N+O(N^-2)`.                                     `(RA5)`

Because `e` is transcendental, it is a nonconstant element of every finitely generated Q-field
containing it.  On a normal projective model of `F`, choose a divisorial valuation `nu` with
`nu(e)!=0`.  If `L=F(u_N)` and `e_nu` is the ramification index of an extension of `nu`, then

`N/gcd(N,nu(e)) divides e_nu`, hence
`[F(u_N):F]>=N/gcd(N,nu(e))`.                                    `(RA6)`

In particular the degrees grow at least linearly along primes not dividing `nu(e)`.  This rules
out a fixed finite extension containing the coherent branch and gives the exact obstruction to
an algebraic continuity/closed-graph argument.

Relative heights exhibit the matching compensation.  On the normalized Kummer cover,

`h(u_N)=h(e)/N`, while `[F(u_N):F]` is of order `N`.               `(RA7)`

At a number-field specialization the same identity is the usual absolute-height equality
`h(alpha^N)=N*h(alpha)`.  Hence the selected roots have shrinking height but unbounded degree,
precisely outside Northcott's hypotheses.  At the chosen complex embedding both `u_N` and
`conj(u_N)=exp(1/N)*zeta_N^(-1)` approach `1`, but they account for only two roots.  When
`X^N-e` is irreducible,

`product_(sigma:F(u_N)->C) (1-sigma(u_N))=1-e`.                  `(RA8)`

The other Kummer branches compensate the two small factors.  Positivity of the radial part,
unit-circle phase, and two-sided conjugate convergence select embeddings, not an algebraic
factor of the norm.

The second regime uses integer cancellation and no field extension.  If `m>2`, the pigeonhole
form of simultaneous Dirichlet approximation gives a constant `C_w` and arbitrarily large `Q`
with `a in Z^m\{0}` such that

`max_i |a_i|<=Q`,
`0<|sum_i a_i*w_i|<=C_w*Q^(1-m/2)`.                              `(RA9)`

For sufficiently large `Q` the nonzero sum is not a period, by the exact kernel.  Its exponential

`U_a=product_i exp(w_i)^a_i in F`                                `(RA10)`

therefore differs from `1`, but

`-log|U_a-1| >= (m/2-1)*log Q-O_w(1)`.                           `(RA11)`

After any number-field specialization for which the same archimedean smallness were separately
imposed, elementary height bounds give

`h(U_a)<=sum_i |a_i|*h(exp(w_i))=O_w(Q)`.                         `(RA12)`

Thus the gain guaranteed by Dirichlet is logarithmic while the product-formula allowance is
linear.  More fundamentally, finite-type specialization preserves `(RA10)` but not `(RA9)`,
which refers to the original transcendental complex embedding.  No specialization theorem
supplies a number-field point retaining it.

Conjugation stability does not alter either balance.  It rewrites

`U_a*conj(U_a)=exp(2*Re(sum a_i*w_i))>0`,
`U_a/conj(U_a)=exp(2*I*Im(sum a_i*w_i))`                          `(RA13)`

at the selected embedding.  These are radial and unit-circle conditions, but neither says that
the elements are algebraic numbers, algebraic integers, or global units.  Exact kernel converts
equality with `1` into a period relation; it gives no lower bound for a nonzero near-period.

There is also a sharp continuous defect-one saturation model, stronger than the discontinuous-
character tests but deliberately not canonically normalized.  Put
Put `c=-omega^2=4*pi^2`, `h=log(c)`, and

`E_T(x+I*y)=exp(h*x+I*y)`.                                       `(RA14)`

As in `(CQ20)--(CQ23)`, this is a continuous conjugation-compatible homomorphism, positive on
the real axis, unitary on the imaginary axis, with exact kernel `omega*Z`.  On the stable anchor
space `Q*1 direct_sum Q*omega` its graph field is `Q(omega)`, of transcendence degree one.  Its
coherent divisions are

`E_T((1+omega)/N)=c^(1/N)*zeta_N`,                               `(RA15)`

and approach `1` from both conjugate sides at rate `1/N`.  In `Q(omega)`, the valuation at
`omega=0` has `nu(c)=2`; the ramification divisibility `(RA6)` gives degree at least `ell` for
every odd prime `ell`, hence exactly `ell`.  All continuity, conjugation, positivity/unit-circle splitting,
kernel, Kummer coherence, and degree/height formulas above coexist with defect one.  This model
has `E_T(1)=c`, not `e`, and fails the Cauchy--Riemann equation (`h!=1`).  The genuinely normalized
complex exponential itself supplies `(RA4)--(RA8)`, so restoring `E(1)=e` and holomorphicity does
not repair the unbounded-degree mechanism; it merely restores the original open anchor field.

Therefore analytic continuity does distinguish the genuine exponential from arbitrary Hamel
characters, but its coherent branch selection is archimedean rather than algebraic.  Rational
division spends the convergence gain on Kummer degree, integer approximation spends it on
exponent height, and conjugation selects only finitely many embeddings.  A successful arithmetic
argument would need a uniform bounded-degree algebraic recovery branch or an exponentially strong
integer approximation; neither follows from the stable terminal package.

### The canonical anchor and exact covering lattice remove the continuous Beltrami counterfeit

The canonical pair `(CA4)` materially strengthens the continuous-character audit `(CC1)--(CC11)`.
Let `E:(C,+)->(C^*,*)` be a continuous homomorphism compatible with conjugation.  Its lifted
real-linear map has the form

`L(x+I*y)=alpha*x+I*beta*y`,  `alpha,beta in R`,
`E=exp o L`.                                                       `(CR1)`

If `E(1+omega)=E(1+2*omega)=e`, division and additivity give

`E(omega)=1`, `E(1)=e`.                                           `(CR2)`

Conjugation compatibility makes `L(1)=alpha` real, so `(CR2)` implies `alpha=1`.  Since
`L(omega)=beta*omega`, the period equation says `beta in Z`.  If one also retains the exact
covering lattice of the complex exponential,

`ker E=omega*Z`,                                                   `(CR3)`

then `|beta|=1`.  Consequently

`E(z)=exp(z)` if `beta=1`, and `E(z)=exp(conj z)` if `beta=-1`.    `(CR4)`

Positive orientation selects the first alternative; the second has the identical Schanuel
inequality after conjugating every input and output.  Thus continuity, reflection, the literal
canonical anchor, and the exact kernel characterize the relevant analytic character up to this
harmless conjugation.  In particular the earlier continuous countermodels `(CC6)--(CC8)` and
`(CE13)--(CE14)` cannot satisfy the combined anchored data: their imaginary scaling changes the
kernel lattice, or their real scaling changes `E(1)`.

Every hypothesis in this rigidity calculation is exact.  If `(CR3)` is weakened merely to
`E(omega)=1`, any nonzero integer `beta` in `(CR1)` survives and the kernel becomes
`(omega/beta)*Z`.  If conjugation is dropped, the lift may shear the real direction by an
integral period while fixing both values in `(CR2)`.  If continuity is dropped, Hamel-basis
characters can fix `1`, `omega`, and any prescribed finite tuple while assigning their
exponentials almost arbitrarily.

This removes a genuine family of adversarial models, but it is not a transcendence proof.
Equation `(CR4)` recovers the original analytic exponential (or its conjugate); it supplies no
lower bound for the Q-Zariski locus of one selected graph point.  Any argument which concludes
`(CA5)` from the rigidity lemma alone has simply used the defining analytic properties to rename
the original map.  The remaining task is still to turn holomorphicity of this now-rigid map into
an arithmetic inequality at an isolated point, precisely the specialization gap already exposed
by the Ax, Khovanskii, and de Rham audits.

### Integer winding deformations fix the anchor but not its isolated relations

The continuous-character classification leaves a useful discrete test family.  For a nonzero
integer `d`, define

`E_d(x+I*y)=exp(x+I*d*y)=exp(A_d(x+I*y))`,
`A_d(z)=((1+d)/2)*z+((1-d)/2)*conj(z)`.                            `(ED1)`

Then `E_d` is a continuous conjugation-compatible universal-cover homomorphism, agrees with the
real exponential, and satisfies

`ker(E_d)=(omega/d)*Z`,
`E_d(1+omega)=E_d(1+2*omega)=e`.                                  `(ED2)`

The path from `1` to `1+omega` winds `d` times.  Thus the canonical anchor sees its endpoints but
does not see primitive winding.  The exact standard kernel holds only for `d=+/-1`, and positive
orientation selects `d=1`; this is an isolated topological condition, not an algebraic identity
among the endpoint graph coordinates.

The dependence on `d` is exact.  For a fixed input `w_i=a_i+I*b_i`, put

`Y_i=E_1(w_i)`, `rho_i=exp(a_i)`, `q_i=exp(I*b_i)`.                `(ED3)`

Then

`rho_i^2=Y_i*conj(Y_i)`, `q_i=Y_i/rho_i`,
`E_d(w_i)=rho_i*q_i^d`, `E_(d+2)(w_i)=(Y_i/conj(Y_i))*E_d(w_i)`,   `(ED4)`

and equivalently

`E_d(w_i)^2=Y_i^(d+1)*conj(Y_i)^(1-d)`.                           `(ED5)`

Writing `d=2s+1` or `d=2s` separates the two geometric subsequences:

`E_(2s+1)(w_i)=Y_i^(s+1)*conj(Y_i)^(-s)`,
`E_(2s)(w_i)=rho_i*(Y_i/conj(Y_i))^s`.                            `(ED6)`

Hence every deformed value lies in the single field

`N=Q(w,Y,conj(Y),rho_1,...,rho_r)`,
`[N:Q(w,Y,conj(Y))]<=2^r`.                                       `(ED7)`

Now suppose `w` is a length-`r` canonical anchored defect-one tuple for `E_1`; thus
`td_Q K_1=r-1`, where `K_1=Q(w,Y)`, and the first two entries and outputs are the canonical pair.
Their conjugate outputs add nothing, so `(ED7)` gives only

`td_Q Q(w,E_d(w))<=td_Q N<=2*r-3`.                                `(ED8)`

For `r>=3` this is at least `r`, exactly the size at which it ceases to contradict Schanuel.
For `r=2` the obstruction is sharper: the tuple consists only of the anchor, and

`Q(w,E_d(w))=Q(omega,e)` for every integer `d`.                    `(ED9)`

Thus a hypothetical relation between `e` and `pi` persists for every winding number simply
because the selected graph point is literally constant.  Infinitely many characters do not give
infinitely many arithmetic points.

The maps `A_d` also explain why rational-basis and conjugation arguments add no unit.  On the
anchor basis `a_0=1+omega`, `a_1=1+2*omega`,

`A_d(a_0)=(2-d)*a_0+(d-1)*a_1`,
`A_d(a_1)=(2-2*d)*a_0+(2*d-1)*a_1`,                               `(ED10)`

and the displayed rational matrix has determinant `d`.  If the whole rational input space `S`
is conjugation-stable, `A_d:S->S` is an invertible rational basis change for `d!=0`.  Kummer
invariance then makes the fields for `exp(A_d w)=E_d(w)` algebraic over one another, so a defect
would persist for every `d`; this persistence is compatible with `(ED9)` and gives no
contradiction.  If `S` is not conjugation-stable, `A_dS` moves in `S+conj(S)`, and canonical
minimality does not make that larger space a failure.  Conjugation itself gives only

`E_(-d)(w)=conj(E_d(w))`;                                         `(ED11)`

conjugating a relation at `d=1` changes `w` to `conj(w)`, rather than producing the same relation
at the fixed tuple and a new parameter.

Nor do transported equations have bounded algebraic complexity.  If a polynomial of output
degree `D` is rewritten using `(ED6)`, every Laurent exponent has absolute value at most
`D*(abs(d)+1)/2`; after clearing denominators the total degree is `O(D*(abs(d)+1))`, and it grows
linearly whenever an active nonanchor phase exponent does not cancel.  The matrices in `(ED10)`
have logarithmic height `Theta(log(abs(d)+1))`, determinant `d`, and inverses with denominator
`d`.  Thus relations moved
by rational transforms occupy an unbounded sequence of Hilbert components or heights; there is
no finite pigeonhole principle that forces one polynomial to recur.

For a fixed polynomial `P`, continuous interpolation of the winding parameter gives the entire
exponential polynomial

`H_P(t)=P(w,(rho_i*exp(I*t*b_i))_i)`.                              `(ED12)`

A relation at the standard exponential says only `H_P(1)=0`.  It makes `H_P` identically zero
only if all coefficients cancel separately after grouping monomials with equal frequencies
`sum alpha_i*b_i`.  Defect one and deletion minimality impose no such real-linear frequency
condition.

There is a canonical-anchor version of the simple-zero obstruction `(CC10)`.  On a simply
connected neighborhood of `I` avoiding `0` and `-1`, choose `zeta` outside the following
countable union of proper analytic sets so that, for fixed logarithm branches,

`u=Log(zeta)`, `v=Log(zeta+1)`,
`{1,omega,u,v} is Q-linearly independent`,                        `(ED13)`

and `zeta,zeta+1,u,v` are all transcendental.  Such choices exist by Baire: a rational relation
among `1,omega,Log(zeta),Log(zeta+1)` cannot hold identically, since differentiating would force
both logarithm coefficients to vanish.  Also avoid the proper real-analytic locus

`Im(v)*(zeta+1)-Im(u)*zeta=0`;                                    `(ED14)`

it is genuinely proper because at `zeta=I` its left side is
`(pi/4)*(1+I)-(pi/2)*I=(pi/4)*(1-I)!=0`.

The fixed tuple

`(1+omega,1+2*omega,u,v)`                                         `(ED15)`

is therefore Q-linearly independent with every input and output transcendental, retains the
canonical values `e,e` for every integer `E_d`, and at `t=1` satisfies the rational polynomial relation

`E_1(v)-E_1(u)-1=(zeta+1)-zeta-1=0`.                              `(ED16)`

But its deformation function

`H(t)=E_t(v)-E_t(u)-1`

has

`H'(1)=I*(Im(v)*(zeta+1)-Im(u)*zeta)!=0`.                          `(ED17)`

Thus the relation has intersection multiplicity exactly one at the genuine exponential, while
both anchor values agree at every integer parameter.  The analytic interpolation used to measure
that multiplicity necessarily leaves the anchor between integers: an analytic function with
values in `Z` is locally constant.  This tuple is not asserted to be a Schanuel counterexample;
it isolates the missing implication.  The canonical anchor,
Q-linear independence, full transcendence of all displayed values, and a rational graph relation
do not turn a selected relation into a functional identity.  Minimal-counterexample hypotheses
are field-dimension statements and supply no derivative condition capable of contradicting
`(ED17)`.

Finally, using the exact kernel cannot amplify the zero.  Among positive integer parameters it
selects the single value `d=1`; among all nonzero integers it leaves only `+/-1`.  At every other
`d` the new primitive period `omega/d` already lies in the rational span of the canonical anchor,
so rational rank does not detect the smaller lattice.  Zero estimates require many zeros or a
high-multiplicity zero, whereas the kernel condition supplies neither.  The family therefore
sharpens the conclusion of `(CR4)`: primitive winding characterizes the standard map, but no
invariant extracted from one anchored endpoint locus propagates its arithmetic relation in `d`.

### Conjugation after the adjacent-period quotient retains the exact two-unit gap

The forced period does enlarge the conjugation intersection, but it does not improve the
reflection argument.  For an adjacent-period witness of length `n`, put

`K=Q(w,exp(w))`, `Kbar=conj(K)`, `L=K*Kbar`, `I=K intersection Kbar`,
`D=td_Q L`, `J=td_Q I`.                                            `(CQ1)`

Because `omega=w_1-w_0` belongs to `K` and `conj(omega)=-omega` belongs to `Kbar`,

`Q(omega) subset I,   J>=1`.                                       `(CQ2)`

Defect one and transcendence-degree submodularity give

`td_Q K=td_Q Kbar=n-1`,
`D+J<=2*n-2`.                                                       `(CQ3)`

Write `w_i=x_i+u_i`, with `x_i` real and `u_i` purely imaginary, and set

`r=rank_Q{x_i}`, `s=rank_Q{u_i}`.                                  `(CQ4)`

The adjacent relation gives `x_1=x_0` and `u_1-u_0=omega`, so `r<=n-1`, `s>=1`; Q-linear
independence of `w` gives `r+s>=n`.  The compositum has the exact algebraic presentation

`L  ~alg  Q(x,u,exp(2*x),exp(2*u))`.                               `(CQ5)`

Indeed `x=(w+conj(w))/2`, `u=(w-conj(w))/2`, while
`exp(2*x)=y*conj(y)` and `exp(2*u)=y/conj(y)`; conversely `y` is algebraic over the displayed
field because `y^2=exp(2*x)*exp(2*u)`.  Schanuel for rational bases of the real and imaginary
spans would therefore give

`D>=r+s`.                                                          `(CQ6)`

On the intersection side let

`A=ker(Q^n -> span_Q(u), q |-> q dot u)`,
`B=ker(Q^n -> span_Q(x), q |-> q dot x)`.                           `(CQ7)`

They have dimensions `n-s` and `n-r` and intersect trivially.  Integral bases give
`2*n-r-s` Q-linearly independent real or purely imaginary combinations whose values and
exponentials lie in `I`.  The vector `e_1-e_0` belongs to `B` and its associated purely imaginary
combination is exactly `omega`.  Thus the already-known unit `(CQ2)` is one member of this kernel
tuple, not an extra member beyond it.  Schanuel for the kernel tuple would give

`J>=2*n-r-s`.                                                      `(CQ8)`

Equations `(CQ6)` and `(CQ8)` would total `D+J>=2*n`, contradicting `(CQ3)` by two units.  Knowing
`J>=1` does not change this gap: Hermite--Lindemann proves precisely the transcendence of the
one displayed kernel member `omega`, while `(CQ8)` asks for the whole kernel tuple.

The quotient calculation makes the cancellation exact.  Put `N=n-1`, delete `w_1`, and write
the resulting tuple `a=(w_0,w_2,...,w_(n-1))` as `a=p+q`, with real `p` and purely imaginary
`q`.  Define the ranks relative to the period by

`R=rank_Q{p_j}=r`,
`S=dim_Q((span_Q(omega,q_j))/Q*omega)=s-1`.                         `(CQ9)`

The family `a` is Q-linearly independent modulo `Q*omega`; hence the map to its real span and
its imaginary span modulo the period is injective and

`R+S>=N`.                                                          `(CQ10)`

Since `Q(omega)` lies in all four fields in `(CQ1)`, set

`D_0=td_(Q(omega))L=D-1`, `J_0=td_(Q(omega))I=J-1`,
`d_0=td_(Q(omega))K=n-2=N-1`.                                     `(CQ11)`

Submodularity becomes

`D_0+J_0<=2*d_0=2*N-2`.                                           `(CQ12)`

The relative versions of `(CQ7)` are

`A_0={c in Q^N:c dot q in Q*omega}`, `dim A_0=N-S`,
`B_0={c in Q^N:c dot p=0}`,       `dim B_0=N-R`.                   `(CQ13)`

Their intersection is zero by independence modulo `Q*omega`.  After clearing denominators, an
integral basis vector of `A_0` gives the real number `c dot a-k*omega` and its exponential in
`I`; an integral basis vector of `B_0` gives the purely imaginary number `c dot a` and its
exponential in `I`.  The resulting

`E_0=2*N-R-S`                                                      `(CQ14)`

numbers are Q-linearly independent modulo `Q*omega`.  Consequently the two desired relative
Schanuel bounds are exactly

`D_0>=R+S`, `J_0>=2*N-R-S`.                                       `(CQ15)`

Their sum is `2*N`, still two larger than the upper bound `2*N-2` in `(CQ12)`.  Quotienting has
subtracted the known period unit once from the compositum count and once from the intersection
count; it has subtracted the same two units from the target.  The earlier shortfall is unchanged.

Neither classical exponential theorem fills it.  Hermite--Lindemann establishes
`td_Q Q(omega)=1`, which is exactly the base removed in `(CQ11)`, and gives no algebraic
independence from a second transcendental.  Six Exponentials cannot be formed using only the
rational multipliers whose exponential values are algebraic over `K`, since three such
multipliers are Q-dependent.  If an algebraic irrational multiplier `alpha` is introduced, then

`exp(alpha*w_1)/exp(alpha*w_0)=exp(alpha*omega)`,                   `(CQ16)`

and `exp(alpha*omega)` is transcendental by Gelfond--Schneider.  But these multiplier values are
new elements with no reason to lie in `L` or `I`.  The algebraic-independence refinement of Six
Exponentials can force a transcendental extension generated by such new values, as in `(E6)`, but
it supplies no increment to either `D_0` or `J_0`.

For the exact arity-two stress

`w=(1+omega,1+2*omega)`, `exp(w)=(e,e)`,                           `(CQ17)`

one has `K=Q(omega,e)=Kbar`, hence, under the hypothetical defect,

`D=J=1`, `r=s=1`.                                                   `(CQ18)`

Both desired absolute bounds are `2`, so each is short by one.  After quotienting, `N=1`,
`R=1`, `S=0`, and

`D_0=J_0=0`, while `(CQ15)` asks for `D_0>=1` and `J_0>=1`.         `(CQ19)`

The compositum projection is the real tuple `(1,e^2)` and the intersection-kernel tuple is
`(1,e)` (the input is `w_0-omega=1`); either relative lower bound says exactly that `e` is
transcendental over `Q(omega)`.  Thus both halves of the reflection argument reproduce algebraic
independence of `e` and `pi` rather than prove it.

A conjugation-compatible continuous counterfeit saturates every algebraic and rank inequality
above.  Put

`c=-omega^2=4*pi^2>0`, `h=log(c)`,
`T(x+I*y)=h*x+I*y`, `E_T(z)=exp(T(z))`.                             `(CQ20)`

The real-linear map `T` is an invertible homeomorphism, fixes `omega`, and commutes with complex
conjugation.  Therefore `E_T` is a continuous universal-cover homomorphism satisfying

`ker(E_T)=omega*Z`, `E_T(conj z)=conj(E_T(z))`;                    `(CQ21)`

it is nonholomorphic because its real and imaginary scaling factors differ.  Moreover

`E_T(1)=c`, `E_T(1+omega)=E_T(1+2*omega)=c`.                       `(CQ22)`

The adjacent pair is Q-linearly independent, all its inputs and values are transcendental, and

`Q(1+omega,1+2*omega,c)=Q(omega)`.                                `(CQ23)`

Thus `K=Kbar=L=I=Q(omega)`, `D=J=1`, and all the absolute and relative ranks and degrees are
exactly those in `(CQ18)--(CQ19)`.  Unlike a merely abstract character, `(CQ20)` preserves the
kernel, universal-cover topology, and reflection identity, including
`E_T(z)E_T(conj z)=E_T(2*Re z)`.  What it omits is precisely complex holomorphicity.  No known
reflection, Hermite--Lindemann, or Six-Exponentials argument converts that local analytic
property into either missing relative unit in `(CQ19)`.

### Canonical conjugation-stable amplification is exact, but leaves a cross-sector unit

The canonical anchored minimality in `(CA1)--(CA6)` yields a stronger reduction than the earlier
factor-of-two audit.  For a finite rational input space `V`, write

`g(V)=td_Q Q(b,exp(b))`                                           `(CS1)`

for any rational basis `b`; Kummer invariance makes this well-defined.  Let `S` be the
anchored-minimal witness, put `n=dim_Q S`,

`A=Q*1 direct_sum Q*omega`, `B=Q(e,omega)`,
`K=Q(S,exp S)`, `g(S)=td_Q K=n-1`,                               `(CS2)`

and recall that every proper `H<S` containing `A` satisfies `g(H)>=dim H`.  There is an exact
anchor dichotomy:

`n=2  => S=A and td_Q B=1`,
`n>2  => A<S and td_Q B=2, hence td_B K=n-3`.                     `(CS3)`

Indeed failure and one-dimensional transcendence give the first line; in the second, anchored
minimality gives `g(A)>=2`, while `B=Q(e,omega)` has at most two generators.

Now put

`H=S intersection conj(S)`, `h=dim H`, `T=S+conj(S)`,
`dim T=2*n-h`.                                                     `(CS4)`

The shared canonical anchor gives `A subset H`, so `h>=2`.  Set
`Kbar=conj(K)`, `D=td_Q(K*Kbar)`, and `J=td_Q(K intersection Kbar)`.  The graph field of `T` is
algebraic over `K*Kbar` and conversely, hence `g(T)=D`.  Moreover

`D+J<=2*n-2`, `J>=g(H)`.                                         `(CS5)`

The second inequality is literal despite rational denominators: for a basis `c` of `H`, choose
a common positive integer `N` so that every `N*c_j` is an integral combination of a basis of
both `S` and `conj(S)`.  Then `N*c_j` and `exp(N*c_j)` lie in `K intersection Kbar`, while their
field is algebraic-equivalent to the graph field of `c`.

If `S` is not conjugation-stable, then `H<S`, so anchored minimality and `(CS5)` give

`J>=h`,
`g(T)=D<=2*n-2-h=dim T-2`.                                       `(CS6)`

Thus adjoining the conjugate does not merely preserve failure: it amplifies defect one to defect
at least two.  In the branch `n>2`, subtracting the exact anchor base makes the bookkeeping

`td_B K=n-3`,
`td_B(K intersection Kbar)>=h-2`,
`td_B(K*Kbar)<=2*n-h-4=dim(T/A)-2`.                               `(CS7)`

The two shared anchor directions are charged on both sides and do not supply either missing
relative unit.

Choose a failing conjugation-stable `R`, with `A subset R subset T`, of least dimension among
such spaces.  If `m=dim R>2`, conjugation is a rational involution and one may delete a
nonanchor vector from one of its eigenspaces while retaining a stable codimension-one space
containing `A`.  Stable minimality and monotonicity then give

`m-1<=g(R)<m`, hence `g(R)=m-1`.                                  `(CS8)`

If `m=2`, then `R=A` and failure similarly gives `g(R)=1`.  The anchored shears from `(CA4)` may
be performed inside `R`, so it still admits a basis beginning with
`1+omega,1+2*omega` in which every coordinate and exponential is transcendental.  We have
therefore proved the exact reduction

`not SC iff there is a conjugation-stable, canonical-anchored,`
`          fully-transcendental defect-one input space R`.        `(CS9)`

The forward implication is `(CS4)--(CS8)` and the reverse is immediate.  This is a genuine
structural strengthening, but its eigenspace endpoint is sharp.  Write

`R=R^+ direct_sum R^-`,
`R^+={x in R:conj(x)=x}`, `R^-={u in R:conj(u)=-u}`,              `(CS10)`

with `r=dim R^+`, `s=dim R^-`, so `m=r+s` and the anchors imply `r,s>=1`.  For bases containing
`1` and `omega`, put

`F_+=Q(R^+,exp R^+)`,
`F_-=Q(R^-,exp R^-)`, `F=F_+*F_-=Q(R,exp R)`.                    `(CS11)`

The field `F_+` is real: its sector consists of real inputs and positive real values; the second
sector consists of purely imaginary inputs and unit-circle values.  If `s>1`, the proper stable space
`R^+ direct_sum Q*omega` has graph field `F_+(omega)`, so minimality gives

`td_Q F_+(omega)>=r+1`, hence `td_Q F_+>=r`.                      `(CS12)`

Similarly, if `r>1`, the proper stable space `Q*1 direct_sum R^-` has graph field `F_-(e)` and

`td_Q F_-(e)>=s+1`, hence `td_Q F_->=s`.                          `(CS13)`

Consequently, when `r,s>1`, both the real-exponential tuple and the unit-circle tuple already
meet their individual Schanuel ranks, while

`td_Q(F_+*F_-)=r+s-1`.                                            `(CS14)`

The missing unit is exactly a cross-sector algebraic-independence statement.  Conjugation does
not make `F_+` and `F_-` algebraically disjoint, and a loss in compositum transcendence need not
appear as a positive-transcendence-degree field intersection.  Real-exponential o-minimality
controls definable and functional dimension, not the ordinary Q-transcendence degree of one
named point; unit-circle geometry likewise supplies no pointwise lower bound for transcendental
arguments and values.  In the boundary `r=s=1`, `(CS14)` is simply
`td_Q Q(e,omega)=1`: either sector separately has rank one, and their joint independence is
exactly the unresolved algebraic independence of `e` and `pi`.  If only one of `r,s` equals one,
the same missing unit may instead remain wholly in the opposite sector, amounting to the
corresponding real or imaginary restriction of Schanuel.

The standard one-sector stresses make this precise.  For `ell=log 2`, the real tuple `(1,ell)`
has graph field `Q(e,ell)` and its rank-two bound is exactly the open algebraic independence of
`e` and `log 2`; definability in the o-minimal real exponential field supplies no arithmetic
increment.  The purely imaginary tuple `(omega,I*ell)` has outputs `(1,2^I)` and asks for
`td_Q Q(omega,ell,2^I)>=2`.  Gelfond--Schneider proves `2^I` transcendental and Baker-type
linear-form results exclude the expected linear relations, but neither yields this ordinary
degree-two bound.  Hence neither eigenspace comes with an unconditional theorem capable of
supplying the unit missing in `(CS14)`.

There is an exact higher-dimensional exponential-character counterfeit even after the anchor
itself satisfies Schanuel.  Work in the `td_Q B=2` branch and choose a positive real `C`
algebraically independent over `Qbar(e,pi)` such that, for

`U=(C-I)/(C+I)=exp(I*theta)`, `theta/(2*pi) notin Q`.              `(CS15)`

Writing `RR` for the real numbers, choose Q-linear automorphisms `a,b:RR->RR` extending

`a(1)=1`, `a(C)=log C`, `b(2*pi)=2*pi`, `b(C)=theta`,             `(CS16)`

and define the conjugation-compatible character

`E_*(x+I*y)=exp(a(x)+I*b(y))`.                                    `(CS17)`

The indicated extensions exist because the two source pairs and two target pairs are each
Q-linearly independent.  The map has positive values on the real axis, unit-circle values on
the imaginary axis, commutes with conjugation, and has the exact global kernel
`omega*Z`: injectivity of `a` first forces `x=0`, and
`b(y) in 2*pi*Z` forces `y in 2*pi*Z`.  On the stable four-space

`R_*=Q*1 direct_sum Q*omega direct_sum Q*C direct_sum Q*(I*C)`    `(CS18)`

it satisfies

`E_*(1)=e`, `E_*(omega)=1`, `E_*(C)=C`, `E_*(I*C)=U`,
`td_Q Q(R_*,E_*(R_*))=td_Q Q(omega,e,C)=3`.                       `(CS19)`

The only proper conjugation-stable spaces between `A` and `R_*` are
`A+Q*C` and `A+Q*(I*C)`; both graph fields have transcendence degree three.  Hence `R_*` is a
stable-minimal defect-one space with exact two-dimensional anchor base.  The basis

`1+omega`, `1+2*omega`, `C+1+omega`, `I*C+1+omega`                `(CS20)`

is rationally independent and all four inputs and values `e,e,C*e,U*e` are transcendental.
Thus `(CS10)--(CS14)`, positivity, the circle decomposition, conjugation, the canonical values,
and even the exact period kernel coexist with defect one.  The automorphisms in `(CS16)` are
necessarily discontinuous (for example `E_*(C)=C`, not `exp(C)`); this is precisely what the
standard holomorphic exponential excludes.  But at the actual isolated graph point neither
o-minimality nor holomorphicity supplies the missing arithmetic disjointness theorem.  Any
argument that did so in the two-dimensional endpoint would already prove the algebraic
independence of `e` and `pi`.

### Sector-terminal algebraicity is order-definable but yields no arithmetic descent

Assume the conjugation-stable anchored-minimal defect-one space `(CS9)` has dimension `m>2`.
Choose a nonanchor eigenvector `b` of conjugation and a stable complement

`R=H direct_sum Q*b`,  `A subset H`,  `dim H=m-1`.               `(ST1)`

Choose an eigenbasis of `H` (so conjugation sends every basis vector to itself or its negative)
and use it to define graph fields.  Then

`F=Q(H,exp H) subset K=Q(R,exp R)=F(b,exp b)`,                   `(ST2)`

stable minimality and monotonicity give

`m-1<=td_Q F<=td_Q K=m-1`.                                      `(ST3)`

Hence `td_Q F=m-1`, `K/F` is finite, and both `b` and `exp b` are algebraic over the sharp
deletion field.  This is the exact sector-terminal lemma.  The question is whether the real or
circle geometry of the selected eigenvector contradicts this finite extension.

Let `RR` denote the real numbers and put `F_0=F intersection RR`.  Since `F` is stable under
conjugation and contains the nonreal
period, conjugation is a nontrivial automorphism and

`[F:F_0]=2`,  `td_Q F_0=m-1`.                                   `(ST4)`

If a real element is algebraic over `F`, it is algebraic over `F_0`: multiply an annihilating
polynomial by its coefficientwise conjugate, or use transitivity through the fixed field.
Consequently the real sector `b in R`, `t=exp b>0` satisfies

`b,t in (F_0)^real-algebraic-closure`.                            `(ST5)`

Both are already in definable closure of `F_0` in the pure real-closed-field structure.  A
squarefree polynomial over `F_0`, an isolating interval, and the signs of its derivatives give a
finite Thom encoding selecting each root.  The exponential equation `t=exp b` adds no
o-minimal dimension to this zero-dimensional ordered fiber.

This explains why model completeness of `R_exp` cannot supply a transcendence increment.  It
allows existential formulas with parameters from `F_0` to be rewritten or transferred between
models containing those parameters; it does not eliminate the parameters or turn an
`F_0`-definable singleton into a Q-algebraic number.  Moreover `F_0` is generally neither real
closed nor closed under exponential, so it is not itself a submodel to which model completeness
can be directly applied.  Passing to its real/exponential closure only enlarges the parameter
field whose ordinary transcendence degree is already `m-1`.

There is a sharp parameter-free actual-exponential warning.  The function

`f(x)=exp(x)-x^2`                                                 `(ST6)`

is strictly increasing on `(-infinity,0)`, tends to `-infinity` at the left endpoint, and has
`f(0)=1`.  It has a unique negative root `beta`, which is parameter-free definable in `R_exp`.
The root is transcendental: if it were nonzero algebraic, Hermite--Lindemann would make
`exp(beta)` transcendental, contradicting `exp(beta)=beta^2`.  Thus

`exp(beta)=beta^2`,  `td_Q Q(beta,exp beta)=1`,                   `(ST7)`

even though `beta` is a definable singleton.  Setting `T=beta^2`, the selected negative root is
quadratic over `Q(T)` and its exponential already lies in `Q(T)`.  Ordered root isolation and
the actual real exponential therefore coexist with exactly the relative algebraicity in
`(ST2)`.

The purely imaginary sector is equally rigid and equally harmless.  Put `b=I*theta` with
`theta in R` and `u=exp b`, so `u*conj(u)=1`.  From algebraicity over `F` and conjugation one gets

`-b^2=theta^2 algebraic over F_0`,
`c=(u+u^(-1))/2=cos(theta) algebraic over F_0`.                   `(ST8)`

Conversely, after these two real quantities are named,

`b^2+theta^2=0`,  `u^2-2*c*u+1=0`.                               `(ST9)`

Thus conjugation reduces the input and output to two real algebraic parameters and two quadratic
branch choices; it creates no relative transcendence.  The reciprocal-conjugate minimal
polynomial of `u` is self-inversive after descent, but its coefficients remain in the
transcendental field `F_0`, not in Q.

Compactness of the circle does not improve this.  The family

`X^2-2*c*X+1,  -1<c<1`,                                         `(ST10)`

has two unit-circle roots for every real parameter `c`; choosing the sign of the imaginary part
selects one root definably without bounding the arithmetic complexity of `c`.  The covering
`theta mapsto exp(I*theta)` has lifts differing by `2*pi*Z`; this periodic covering on all of
`R` cannot be definable in an o-minimal structure.  A principal argument on the circle can be
definable after adding restricted trigonometry, and on a fixed fundamental arc an order condition
selects its branch, but only over the parameters `c` and `pi`; definable choice is not ordinary
algebraic descent.

An actual-exponential saturation realizes `(ST8)--(ST10)` with finite degree.  Choose a generic
`theta in (0,pi)` and set

`T=theta^2`,  `c=cos(theta)`,  `b=I*theta`,  `u=exp(I*theta)`.     `(ST11)`

Over the real parameter field `Q(T,c)`, the input `b` and output `u` satisfy the two quadratics
in `(ST9)`.  Positivity of `theta` and positivity of `Im(u)` select the actual branches.  By
choosing `theta` outside a countable union of analytic zero sets, these parameters and any fixed
finite anchored deletion family can retain all required rational linear independences.  Naming
`T` and `c` as real deletion coordinates embeds this exact recovery pattern into an actual
exponential graph field.  Whether that deletion field has the sharp absolute degree `(ST3)` is
the original Schanuel-type question; order and circle topology add no further constraint.

Local Jacobians make the same point.  In the real case, a separable annihilator `A(X)` already
has `A'(b)!=0`; in the circle case the two quadratic equations in `(ST9)` already isolate the
chosen branches.  Appending `Y-exp(X)` or the argument condition does not increase local
intersection multiplicity.  Traces, resultants, and Thom encodings descend only from `K` to
`F_0`, a field of transcendence degree `m-1`; there is no finite trace from `F_0` to Q.

Therefore the sector-terminal alternative is exact but terminal: the real branch is an
ordered-algebraic singleton over the deletion parameters, and the imaginary branch is a
quadratic circle/argument lift over those parameters.  Model completeness and definable choice
control the geometry of these parameterized finite fibers, not the ordinary Q-transcendence
degree of the parameters.  Any successful sector argument would need an arithmetic theorem
forcing the deletion parameters themselves into a smaller field; neither o-minimality,
conjugation, positivity, nor compactness provides it.

### Mixed Hardy--Toeplitz kernels are positive but do not create a cross-sector unit

Continue with a conjugation-stable input space and choose real-sector inputs `x_i` and
imaginary-sector inputs `u_j`.  Put

`A_i=exp(x_i)>0`,  `B_j=exp(u_j)`,  `abs(B_j)=1`.                 `(HK1)`

The most direct mixed exponential matrix has an exact outer-product factorization:

`M_(i,j)=exp(x_i+u_j)=A_i*B_j`.                                 `(HK2)`

Thus `rank(M)<=1` and every minor of order at least two vanishes.  Rational or integral shears
do not help: `exp(p_i*x+q_j*u)=A^(p_i)*B^(q_j)` has the same factorization.  Holomorphy makes the
corresponding mixed jet matrix even more explicitly degenerate.  For `f(x,theta)=exp(x+I*theta)`,

`partial_x^p partial_theta^q f = I^q*f`.                         `(HK3)`

Every mixed derivative column is proportional to the value column.  The Cauchy--Riemann
equation here lowers the rank; it does not supply a second arithmetic direction.  Wronskians of
distinct functions `exp(k*z)` can be nonzero, but are a Vandermonde constant times a monomial in
the already displayed exponential values.  In particular every finite holomorphic jet belongs
to the field generated by the value.

Positivity gives nonzero determinants only after several sector points are assembled.  For
positive weights `A_l` and distinct phases `B_l`, define

`mu_k=sum_l A_l*B_l^k`,  `T_N=(mu_(j-k))_(0<=j,k<N)`.            `(HK4)`

Writing `V_(j,l)=B_l^j` gives `T_N=V*diag(A_l)*conjTranspose(V)`.  Hence `T_N` is positive
semidefinite, has rank at most the number of atoms, and for exactly `N` atoms

`det(T_N)=(product_l A_l)*abs(product_(l<q) (B_q-B_l))^2`.       `(HK5)`

This is positive when the phases are distinct, but it is already a product of a real-sector
factor and a circle-sector Vandermonde.  For more rows than atoms the determinant vanishes; for
fewer rows Cauchy--Binet gives a sum of the same separated positive factors.  No determinant
forces algebraic independence between a weight and a phase.

The Hardy/Szego kernel has an equally explicit outcome.  Choose the signs of `x_i` so that
`A_i>1` and set

`z_i=A_i^(-1)*B_i=exp(-x_i+u_i)`,  `abs(z_i)<1`.                 `(HK6)`

The Gram matrix `S_(i,j)=1/(1-z_i*conj(z_j))` is positive definite for distinct `z_i`, and the
Cauchy double-alternant identity gives

`det(S) = product_(i<j) abs(z_i-z_j)^2 /
          (product_i (1-abs(z_i)^2) *
           product_(i<j) abs(1-z_i*conj(z_j))^2)`.               `(HK7)`

More generally, for `a_i*b_j!=1`,

`det(1/(1-a_i*b_j)) =
   product_(i<k)(a_i-a_k)*product_(j<l)(b_j-b_l) /
   product_(i,j)(1-a_i*b_j)`.                                   `(HK8)`

All entries and determinants in `(HK4)--(HK8)` lie in the original stable graph field `F`; the
Hermitian determinants lie in its real fixed field `F_0`.  Their positivity detects only
distinctness.  It is not a discrete arithmetic condition: colliding two points makes `(HK7)`
tend continuously to zero, while `F_0/Q` is transcendental and supplies neither a number-field
norm nor a product-formula lower bound.  Rational residues and Bezoutians formed from these
entries remain in the same field and have the same defect.

Kernels with genuinely higher rank leave the permitted field.  A Bargmann--Fock entry
`exp(z_i*conj(z_j))` evaluates the exponential at a product, although a stable rational input
space is closed only under addition, rational scaling, and conjugation.  A Paley--Wiener entry
integrates `exp(I*t*(z-conj(w)))` over a real continuum; stability does not imply closure under
multiplication by `I*t`, and the continuum of new exponential values is not contained in `F`.
Restricting either construction back to additive entries `exp(z_i+conj(z_j))` restores the
rank-one factorization `(HK2)`.  Consequently a positive-rank theorem for these larger kernels
is a statement about an enlarged analytic field, not the terminal graph field.

The canonical anchor makes the obstruction literal.  With `omega=2*pi*I`,

`exp(p_i+q_j*omega)=e^(p_i)`                                    `(HK9)`

for integers `p_i,q_j`; every column is the same.  The Toeplitz measure supported at
`exp(omega)=1` has rank one.  The one-point Hardy matrix also has rank one, while its confluent
jet determinants, when nonzero, are rational functions of `e` and contain no information about
`omega`.  Dividing the period only adds roots of unity and finite cyclotomic/Kummer degrees, not
an ordinary transcendence unit.  Thus these kernels do not even distinguish the endpoint
`td_Q Q(e,omega)=1` whose exclusion would imply the algebraic independence of `e` and `pi`.

Finally the sharp character `(CS15)--(CS20)` passes every value-level test above.  Additivity,
multiplicativity, positivity on the real sector, unit modulus on the imaginary sector, and
conjugation are exactly the hypotheses used in `(HK1)--(HK9)`; its discontinuity never enters
the determinant calculations.  Genuine holomorphic derivatives do distinguish that character
globally, but at one actual exponential point the complete finite jet is given by `(HK3)` and
adjoins no element to the value field.  The Cauchy--Riemann equations have constant algebraic
coefficients and therefore cannot manufacture the missing ordinary-transcendence unit.

This gives a sharp trichotomy.  Mixed exponential jets factor with rank one; Hardy and Toeplitz
positivity produces explicit nonzero elements already in `F_0`, with no discrete lower bound;
and Bargmann or Paley--Wiener rank is purchased by leaving the stable graph field.  Hence the
stable real/unit-circle splitting plus holomorphy does not improve the terminal
transcendence-degree inequality.

### A parameter-free real graph point forces surplus in its canonical deletion

There is a useful canonical-anchor amplification of the actual root `(ST7)`.  Set

`v=(1+omega,1+2*omega,beta^2)`,
`w=(1+omega,1+2*omega,beta^2,beta)`.                              `(ST12)`

Both tuples are Q-linearly independent.  Indeed, the imaginary part of a rational relation on
`w` first gives `q_0+2*q_1=0`; its real part is then a rational polynomial of degree at most two
in the transcendental number `beta`, so every coefficient vanishes.  Put

`F=Q(e,omega,beta^2,exp(beta^2))`,
`K=Q(w,exp(w))=F(beta)`.                                         `(ST13)`

The deletion graph field is exactly `F`, while `beta^2 in F` and `exp(beta)=beta^2` show

`[K:F]<=2`, `td_Q K=td_Q F`.                                    `(ST14)`

Thus this is an unconditional actual-exponential instance of the terminal algebraic-pair
phenomenon over a canonical anchored deletion.  Its Schanuel accounting is exact:

`Bound(w) iff td_Q F=4`
`         iff (e,omega,beta^2,exp(beta^2)) is algebraically independent.` `(ST15)`

The three-input deletion only asks for `td_Q F>=3`.  If it attains equality, appending `beta`
produces a literal defect-one family; avoiding that failure requires the deletion to carry one
full surplus unit, `td_Q F=4`.                                    `(ST16)`

This example rules out a local prohibition on algebraic input--exponential pairs even for the
genuine holomorphic exponential and the fixed canonical anchor: such pairs occur naturally.
What Schanuel must enforce is a global surplus in the preceding graph field.  In the checked
terminal counterexample normal form that preceding field is constrained to equality, which is
why `(ST14)--(ST16)` reproduce the exact obstruction rather than resolve it.

### Lambert W has functional independence but no arithmetic inverse-value specialization

The actual real stress `(ST6)--(ST7)` has an exact inverse-exponential form.  On the principal
branch put `w=W_0(1/2)>0` and

`beta=-2*w=-2*W_0(1/2)`.                                        `(LW1)`

Since `w*exp(w)=1/2`,

`exp(beta)=exp(-2*w)=(2*w)^2=beta^2`.                            `(LW2)`

The sign selects the unique negative root: `exp(x)-x^2` is strictly increasing on the negative
real axis, tends to minus infinity at the left endpoint, and is positive at zero.  Hermite--
Lindemann proves exactly the already known one unit: `beta` is transcendental, since a nonzero
algebraic `beta` would make `exp(beta)` transcendental whereas `beta^2` is algebraic.

The differential equation does not strengthen this value statement.  For

`B(t)=-2*W_0(t)`

one has the exact identities

`t*(2-B)*B'=2*B`,  `exp(B)=B^2/(4*t^2)`.                         `(LW3)`

Induction in the first identity shows that every derivative `B^(r)(1/2)` lies in `Q(beta)`.
Thus the complete finite differential jet at the selected algebraic point generates precisely
the same ordinary field as the value.  The general nonzero solution of the differential equation
satisfies

`B*exp(-B/2)=c*t`                                                `(LW4)`

for an arbitrary differential constant `c`; the Lambert normalization chooses `c=-2`, and the
principal real path chooses a branch.  This is a nonlinear first-order differential-algebraic
extension, not a Picard--Vessiot extension of a linear system.  Its differential equation leaves
both the integration constant and branch selection external.

At the function-field level the standard functional theorem is already sharp.  The function
`B` is transcendental over `C(t)` and `(LW3)` gives

`td_C C(t,B,exp(B))=td_C C(t,B)=2`.                              `(LW5)`

Indeed algebraicity of `B` over `C(t)` would make `exp(-B/2)=-2*t/B` algebraic over `C(B)`,
contrary to the essential exponential singularity over the rational function field.  More
strongly, `B` and `2*t` are Q-linearly independent modulo constants.  Ax's differential theorem
applied to these two functions yields

`td_C C(B,t,exp(B),exp(2*t))>=3`.                                `(LW6)`

Using `(LW3)`, this says that `B`, `t`, and `exp(2*t)` are algebraically independent over `C`;
in particular the functions `B(t)` and `exp(2*t)` are algebraically independent.  Nevertheless
at the algebraic specialization `t=1/2` their values are exactly `beta` and `e`.  Functional
transcendence therefore gives the desired independence before specialization and loses it at the
single point where it is needed.

Siegel--Shidlovskii specialization cannot repair this loss.  Around zero,

`W_0(t)=sum_(n>=1) (-n)^(n-1)*t^n/n!`.                           `(LW7)`

The E-normalized coefficients `(-n)^(n-1)` have superexponential height, and the series has
radius `1/e` with a branch point at `-1/e`; `W_0` is not an entire E-function.  In particular
`1/2>1/e` is reached from its rational Taylor germ only by analytic continuation.  Although
`t*exp(t)` is an E-function, inverse evaluation starts at the transcendental preimage `w`, so
the E-function value theorems have already lost their algebraic-input hypothesis.  Likewise
`exp(beta^2)` is the E-function `exp` evaluated at a transcendental input.

Inverse-function monodromy supplies branches, not number-field conjugates.  If `W_k(1/2)` is any
branch and `beta_k=-2*W_k(1/2)`, then every branch satisfies

`exp(beta_k)=beta_k^2`,                                         `(LW8)`

and hence every `beta_k` is transcendental.  Distinct branch values are pairwise Q-linearly
independent.  For if `beta_l=r*beta_k` with `r=a/b in Q^*`, then `(LW8)` gives

`beta_l^(2*b)=exp(b*beta_l)=exp(a*beta_k)=beta_k^(2*a)`.

Thus `beta_k^(2*(a-b))=(a/b)^(2*b)`.  If `a!=b` this makes `beta_k`
algebraic; if `a=b` then `beta_l=beta_k`.  Both alternatives contradict the hypotheses.  The
branches form an infinite monodromy
orbit, asymptotic to logarithms differing by `2*pi*I*k`; no finite subset is stable enough to
have a trace or norm.  The exact comparison of two branches is

`beta_l-beta_k = -2*Log(beta_k/beta_l) + 2*pi*I*n`               `(LW9)`

for a branch-dependent integer `n`; it introduces another logarithm rather than an algebraic
period relation.  If two distinct `beta_k,beta_l` were algebraically dependent, their
Q-independent input pair and `(LW8)` would have graph field of transcendence degree at most one.
Thus proving branch algebraic independence by monodromy would itself prove the corresponding
two-variable Schanuel instance.  Analytic monodromy is not algebraic Galois conjugacy over Q.

The three proposed relative conclusions are therefore exact open Schanuel boundaries:

* for `(1,beta)`, the graph field is `Q(e,beta)`, so the required bound is precisely algebraic
  independence of `e` and `beta`;
* for `(omega,beta)`, reality versus pure imaginarity gives Q-linear independence and the graph
  field is `Q(omega,beta)`, so the required bound is precisely algebraic independence of
  `omega` and `beta`;
* `beta,beta^2` are Q-linearly independent, and if `exp(beta^2)` were algebraic then
  `Q(beta,beta^2,exp(beta),exp(beta^2))=Q(beta,exp(beta^2))` would have transcendence degree one.
  Even proving mere transcendence of `exp(beta^2)=(beta^2)^beta` is not covered by
  Hermite--Lindemann or Gel'fond--Schneider, because both the base and exponent are
  transcendental.

There is a sharp positive-sector character saturation for the value statements.  Let `C=e+1`.
The triples

`{1,C,C^2}` and `{1,-2*log(C),log(2)}`                            `(LW10)`

are Q-linearly independent.  The first assertion follows from transcendence of `e`; for the
second, clearing a rational relation and exponentiating would give a nonzero Laurent-polynomial
equation in `e` involving only `e`, `e+1`, and `2`.  Choose a Q-linear automorphism `a` of the
real numbers sending the first triple in `(LW10)` to the second, and a Q-linear automorphism `b`
with `b(2*pi)=2*pi`.  Then

`E_*(x+I*y)=exp(a(x)+I*b(y))`                                    `(LW11)`

is a positive, conjugation-compatible exponential character with `E_*(1)=e` and exact kernel
`omega*Z`.  For `beta_*=-C` it satisfies

`E_*(beta_*)=beta_*^2`,  `E_*(beta_*^2)=2`.                      `(LW12)`

Both Q-independent pairs `(1,beta_*)` and `(beta_*,beta_*^2)` have graph field `Q(e)` of
transcendence degree one.  This character is necessarily discontinuous and nonholomorphic; it
does not counterfeit the actual Lambert branch.  It does prove sharply that the inverse value
equation, positivity, conjugation, exact period kernel, coherent rational powers, and even an
algebraic value at the squared input contain no hidden arithmetic determinant.  The genuine
analytic information supplies functional independence `(LW6)`, but the missing ingredient is a
specialization theorem for a nonlinear non-E-function inverse at `t=1/2`.

### Canonical auxiliary-polynomial budgets close strictly below the multiplicity threshold

This is a self-contained Philippon--Brownawell audit of the positive terminal normal form.  Let
the full canonical tuple have length `N>=3`, write

`w=(1+omega,1+2*omega,v_2,...,v_(N-2),b)`, `y=exp(w)`,            `(APC1)`

and let `w^-` delete `b`.  The checked terminal conclusion is

`F=Q(w^-,exp(w^-))`, `td_Q F=N-1`,
`K=F(b,eta)`, `eta=exp(b)`, `[K:F]=Delta<infinity`.               `(APC2)`

Choose any finite-type Q-model generated by the displayed coordinates and filter it by total
degree in a fixed finite generating set.  Noether normalization and `(APC2)` give the exact
Hilbert exponent

`dim_Q K_(<=D)=Theta(D^(N-1))`;                                  `(APC3)`

passing from `F` to `K` changes only the implicit constant, by at most a factor depending on
`Delta`.  This is the first decisive point: algebraicity of the terminal pair removes no Hilbert
exponent because the deletion field already has the sharp transcendence degree `N-1`.

Let `V_D` be the box of Q-polynomials in the `2*N` variables `(X_i,Y_i)` having degree at most
`D` in each variable.  It has exactly

`M_D=(D+1)^(2*N)`                                                `(APC4)`

coefficients.  The graph derivations `Delta_i=partial_(X_i)+Y_i*partial_(Y_i)` preserve `V_D`.
For every rectangular multi-index `0<=alpha_i<T`, the value

`(Delta^alpha P)(w,y)`                                           `(APC5)`

lies in a filtered piece `K_(<=c*D)`; repeated differentiation changes integer coefficients but
does not increase the monomial degrees in `w,y`.  Expressing all `(APC5)` in a Q-basis of that
piece therefore imposes at most

`C*Delta*T^N*D^(N-1)`                                           `(APC6)`

rational linear conditions on the coefficients of `P`.  The raw Hilbert--Siegel dimension count
guarantees a nonzero `P` only while `(APC6)<(APC4)`, namely

`T << D^((N+1)/N)=D^(1+1/N)`.                                   `(APC7)`

This includes every relation already present at the selected point; quotienting first by its
Q-locus merely computes the same Hilbert function `(APC3)`.

The sharp multiplicity threshold is much larger.  Along the full graph flow,

`Phi_P(s)=P(w_1+s_1,...,w_N+s_N,y_1*exp(s_1),...,y_N*exp(s_N))`.  `(APC8)`

In one coordinate its summands are `s^a*exp(c*s)`, `0<=a,c<=D`.  Their confluent Wronskian is a
nonzero product of factorials and powers of the distinct integer differences `c'-c`.  Hence the
first `(D+1)^2` derivatives determine that coordinate, and tensoring shows that the rectangular
jet map for `(APC8)` becomes injective only at

`T=(D+1)^2`.                                                     `(APC9)`

The gap between `(APC7)` and `(APC9)` is the factor `D^(1-1/N)` in every coordinate.  At the
uniqueness threshold the number of scalar conditions is of order `D^(3*N-1)`, versus only
`D^(2*N)` coefficients.  Thus neither a sharper Siegel lemma nor a better choice of a lattice
basis can cross the rank boundary.

There is also an exact height balance.  After fixing the finite-type model, the matrix in
`(APC6)` has logarithmic coefficient size

`O(D+T*log(D+1))`.

Writing `R=C*Delta*T^N*D^(N-1)`, an ordinary Siegel bound has the characteristic factor

`log H(P) << (R/(M_D-R))*(D+T*log(D+1))`.                         `(APC10)`

It blows up as the dimension boundary is approached.  Divided derivatives move the factorial
part from the archimedean norm into denominators and do not change this quotient.  In the usual
Philippon criterion, proving transcendence degree at least `N` from integer polynomials of size
`sigma` and nonzero values of size `exp(-S)` requires the strict growth
`S/sigma^N -> infinity`.  Extrapolation from `(APC7)` and the zero estimate `(APC9)` yields at
best the boundary order `S=O(sigma^N)`, with the height term `(APC10)` still charged.  The
criterion consequently reproduces the conjectural inequality but never reaches its required
strict side.

Terminal algebraicity supplies no free multiplicity.  If `A(X),B(Y) in F[X],F[Y]` are the
minimal polynomials of `b,eta`, separability gives

`A'(b)!=0`, `B'(eta)!=0`.                                       `(APC11)`

Thus their pullbacks `A(b+s)` and `B(eta*exp(s))` have simple zeros.  Taking an `m`-th power
raises vanishing order, degree, and logarithmic height by the same factor `m`.  Moreover their
coefficients lie in the transcendental field `F`, not a number field.  Trace or norm down the
finite extension `K/F` still lands in `F`; eliminating a transcendence basis of `F` costs the
factor `D^(N-1)` already visible in `(APC6)`.  There is no Liouville, product-formula, or
Northcott lower bound for a nonzero element of the selected complex embedding of `F`.

Many integer combinations do not change the balance.  For `q in Z^N`, put

`xi_q=q dot w`, `zeta_q=product_i y_i^(q_i)=exp(xi_q)`.           `(APC12)`

Both entries lie in the same finite extension `K`, and their filtered complexity is `O(|q|)`.
The anchor vector `c=(-1,1,0,...,0)` gives the exact fibers

`xi_(q+k*c)=xi_q+k*omega`, `zeta_(q+k*c)=zeta_q`.                `(APC13)`

In `G_a x G_m` the subgroup generated by `(omega,1)` is Zariski dense in the proper subgroup
`G_a x {1}`.  Philippon's subgroup-sensitive zero lemma therefore records `(APC13)` as its
exceptional subgroup before it can force an auxiliary polynomial to vanish identically.  On the
parameter lattice, quotienting by `Z*c` consumes exactly one direction: a box has only order
`L^(N-1)` fibers after the order-`L` period strings are removed, matching the exponent in
`(APC3)`.  Equations transported by different `q` are different polynomials; taking
their product makes degree and height grow at least linearly with the number of manufactured
zeros.  Even the fictitious favorable case of one common polynomial only reaches the standard
interpolation equality `number of jets = Hilbert dimension`.

Brownawell's absolute exponential consequences likewise give no relative unit.  They can force
one of several values such as `exp(b),exp(b^2),exp(b^3)` to be transcendental over Q, but here
`exp(b)=eta` is already required to be transcendental.  Those theorems do not assert
transcendence over the parameter field `F`; adjoining `b^2` or `b^3` as new inputs merely pays
the corresponding arity cost.

There is a sharp canonical-anchor counterfeit satisfying all algebraic and local multiplicity
data.  Let `O,E` be algebraically independent indeterminates, put `F_*=Q(O,E)`, and in its
algebraic closure choose

`b_*^2=O^2+1`, `eta_*^2=E+O`.                                   `(APC14)`

The three elements `1,O,b_*` are Q-linearly independent.  Define an exponential character on
their rational span by

`E_*(1)=E`, `E_*(O)=1`, `E_*(b_*)=eta_*`,                        `(APC15)`

choose coherent rational roots, and extend it to the additive group using divisibility of the
algebraically closed multiplicative group.  Then

`w_*=(1+O,1+2*O,b_*)`, `E_*(w_*)=(E,E,eta_*)`,                   `(APC16)`

is fully transcendental and rationally independent, its anchor deletion field is exactly
`F_*` of transcendence degree two, and the full graph field `F_*(b_*,eta_*)` has degree four over
it.  Indeed the two radicands in `(APC14)` represent independent square classes: the divisor
`E+O` occurs to odd order in the second and in their product, but not in the first.
Thus it has length three and exact defect one.  Every integer combination `(APC12)`, every Kummer
division, every finite trace/norm, and every algebraic-group incidence remains in an algebraic
extension of `F_*`.

After choosing a complex embedding of this countable field, define for each frequency `xi_q`

`g_q(t)=E_*(xi_q)*exp((t-1)*xi_q)`.                               `(APC17)`

At `t=1` these entire germs have exactly the values, all graph jets, constant-coefficient
recurrences, confluent Wronskians, and multiplicity estimates used in `(APC5)--(APC13)`.  They
fail only the common global normalization at the other endpoint:
`g_q(0)=E_*(xi_q)*exp(-xi_q)`, not `1`.  Hence an auxiliary-polynomial proof based on the selected
point, its terminal algebraicity, integer combinations, and any finite jet package is refuted by
`(APC14)--(APC17)`.  To distinguish the genuine exponential it must couple to a second endpoint
or an arithmetic normalization; the resulting height and support costs are exactly those in
`(APC9)--(APC10)`.  The canonical anchor and the finite terminal pair therefore add structure,
but no surplus in the Philippon--Brownawell degree--height--multiplicity budget.

### A period-strip argument principle exports the selected zero to the noncompact boundary

The adjacent quotient admits a genuine several-variable zero count, but the resulting integer is
a topological degree rather than an arithmetic trace.  Let `W'` be the Q-locus of `(KQ7)` in

`H=G_a^n x G_m^(n-1)`, `dim H=2*n-1`, `dim W'=n-1`, `codim W'=n`.   `(GR1)`

At its generic smooth point choose rational Laurent polynomials `G_1,...,G_n` whose differentials
span the conormal space, and pull them back to the quotient exponential graph:

`f_i(u)=G_i(u_0,...,u_(n-1),exp(u_1),...,exp(u_(n-1)))`.            `(GR2)`

When the graph intersection is transverse, the `f_i` have a simple isolated common zero at
`u=(omega,w_0,w_2,...)`.  This is the most favorable setup for a multidimensional argument
principle.

There is an immediate obstruction to putting `(GR2)` on a period cylinder.  A polynomial in
`u_0` with coefficients holomorphic in the other displayed variables which satisfies

`f(u_0+omega,u')=f(u_0,u')`                                       `(GR3)`

is independent of `u_0`: a nonconstant polynomial cannot have a nonzero period.  Therefore, if
all `n` equations in `(GR2)` descended to `C/(omega*Z)` in the first coordinate, the first column
of their Jacobian would vanish and the common zero could not be transverse.  The multiplicative
coordinate `exp(u_0)` which was periodic has been removed by the adjacent binomial quotient;
the surviving algebraic equations distinguish `omega` through nonperiodic additive dependence.

For a bounded product domain `Omega` with no boundary zero, the several-variable argument
principle nevertheless gives the valid integer

`deg(f,Omega,0)=sum_(a in Omega, f(a)=0) mult_a(f)`.                `(GR4)`

Equivalently, on a Leray cycle surrounding the zero fiber,

`(1/(2*pi*I)^n) integral det(partial f_i/partial u_j)`
`  *du_0...du_(n-1)/(f_1...f_n)=deg(f,Omega,0)`.                   `(GR5)`

The selected transverse zero contributes `+1`.  But `(GR4)` permits the total degree itself to
be `1`; it neither forces a second zero nor makes the selected point part of a Q-stable finite
fiber.  The defining inequalities for a period strip use `Im(u_0)` and the chosen component
label, not algebraic data over Q.

The arity-two `e`--`pi` boundary gives an exact transverse system.  Conditionally let
`P(U,V) in Q[U,V^+-]` generate the relation ideal of `(omega,e)`.  In quotient coordinates put

`f_1(u_0,u_1)=u_1-u_0-1`,
`f_2(u_0,u_1)=P(u_0,exp(u_1))`.                                    `(GR6)`

These vanish at `(omega,1+omega)`.  With

`Delta P=P_U+V*P_V`,
`det J_f(omega,1+omega)=-(Delta P)(omega,e)`.                       `(GR7)`

This determinant cannot vanish.  Otherwise the height-one kernel of evaluation at `(omega,e)`
would give `P | Delta P`.  Comparing the `U`-degree and the extreme Laurent exponents in `V`
forces `Delta P=cP` for a constant `c`; writing `P=sum_j p_j(U)V^j` then gives

`p_j'(U)+(j-c)*p_j(U)=0`.                                         `(GR8)`

A polynomial solution is nonzero only when `j=c` and `p_j` is constant, making `P` a Laurent
monomial, a unit which cannot vanish.  Thus `(GR6)` is transverse independently of the unknown
shape of the hypothetical relation.

After multiplying `P` by a Laurent monomial in `V` if necessary, eliminating `u_1` reduces the
global count to the one-variable exponential polynomial

`g(z)=P(z,exp(z+1))=sum_(j=0)^d p_j(z)*exp(j*(z+1))`,
`g(omega)=0`, `g'(omega)=(Delta P)(omega,e)!=0`.                   `(GR9)`

Take the period-height strip `pi<Im(z)<3*pi` and truncate it by `|Re(z)|<R`, avoiding boundary
zeroes.  The ordinary argument principle is

`N(R)=(1/(2*pi*I))*integral_(boundary S_R) g'(z)/g(z) dz`
`    =1+N_other(R)`.                                               `(GR10)`

It is only a winding number.  Its horizontal sides do not cancel, because

`g(z+omega)-g(z)=sum_j (p_j(z+omega)-p_j(z))*exp(j*(z+1)) !=0`.    `(GR11)`

The last inequality is exact: if the difference vanished, every polynomial `p_j` would be
periodic and hence constant, whereas a relation `P(omega,e)=0` with `P` independent of `U` would
make the transcendental number `e` algebraic.

There is no hidden coefficient estimate on the remaining boundary integral.  If
`A=max_j deg p_j` and `H` bounds their rational coefficients, then on the closed strip box, for
`R>=1`, the elementary termwise estimates give

`|g(z)| <= (d+1)*(A+1)*H*(1+(1+3*pi)*R)^A*exp(d*(R+1))`,
`|g'(z)| <= (d+1)*(A+1)*(A+d)*H`
`             *(1+(1+3*pi)*R)^A*exp(d*(R+1))`.                    `(GR12)`

Argument-principle control would also require a lower bound for `|g|` on the boundary.  Rational
coefficients supply none: a boundary can approach a transcendental zero arbitrarily closely,
and moving `R` across such a zero changes `(GR10)` by its multiplicity.  Thus increasing the
large box transfers the local contribution among the nonperiodic faces rather than stabilizing
an arithmetic count.

Even granting perfect periodicity does not help, as an explicit rational system shows.  Reinsert
the known kernel equation and take

`h_0(z)=exp(z_0)-1`, `h_j(z)=z_j (1<=j<n)`.                        `(GR13)`

On the product of `-R<Re(z_0)<R`, `pi<Im(z_0)<3*pi` with small discs in the other variables,
there is exactly one zero, `(omega,0,...,0)`, with Jacobian one.  Hence its global degree and the
normalized residue in `(GR5)` are exactly `1`.  The horizontal faces cancel because `h_0` is
periodic, but the two vertical faces carry the whole degree: as `R` tends to infinity,

`h_0'(R+I*y)/h_0(R+I*y) -> 1`,
`h_0'(-R+I*y)/h_0(-R+I*y) -> 0` uniformly for `pi<=y<=3*pi`,         `(GR14)`

so their normalized contour contribution tends to `1`.  This is a global, noncompact boundary
calculation, distinct from the length-one local residue `(LR3)--(LR5)`: even a rational periodic
system with a normalized local residue already has topological degree one and needs no companion
zero.

Finally, compactification cannot turn this boundary degree into an algebraic residue at infinity.
After compactifying the additive coordinates to `P^1`, each `exp(u_j)` has an essential
singularity at `u_j=infinity`; it is not a meromorphic function on the compactification.  A toric
compactification controls the algebraic limits `V_j=0,infinity`, but the analytic graph reaches
them through exponential growth and oscillation and does not extend as an algebraic or
meromorphic cycle.  The hypotheses of the projective global residue theorem therefore fail, and
the missing residues at infinity are precisely the face contributions in `(GR10)--(GR14)`.

Thus the global route adds a legitimate integer, but not an arithmetic one: it is the degree of a
domain selected by nonalgebraic inequalities and may equal the single local multiplicity.  To
obtain a contradiction one would need a new theorem making the noncompact boundary degree vanish
or arranging the entire zero fiber into a finite Q-stable cycle.  Periodicity, rational
coefficients, toric compactification, and the hypothetical defect relation provide neither.

### Gel'fond constants force an external unit, not independence inside the AP field

At the arity-two adjacent boundary put

`omega=2*pi*I`, `K=Q(e,omega)`, `td_Q K=1`.                        `(GC1)`

This is equivalent to `td_Q Q(e,pi)=1`: each of `omega` and `pi` is algebraic over the field
generated by the other, and `K(I)=Q(e,pi,I)` is only a finite algebraic extension.  We work
conditionally on a relation `P(e,omega)=0`.  The theorem scopes used below are Theorems 7--8,
10, and 13 in Michel Waldschmidt's survey
[*Elliptic Functions and Transcendence*](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/SurveyTrdceEllipt2006.pdf):
Gel'fond--Schneider, Six Exponentials, and its algebraic-independence refinement.  None of these
theorems is relative to the transcendental field `K`.

First track the branch exactly.  For algebraic `alpha`, set

`G_alpha=exp(alpha*pi)=exp((-I*alpha/2)*omega)`.                    `(GC2)`

The logarithms of `-1` are `(2*k+1)*pi*I`; hence the values of `(-1)^(-I*alpha)` are

`exp((-I*alpha)*(2*k+1)*pi*I)=G_alpha^(2*k+1),   k in Z`.          `(GC3)`

If `-I*alpha` is algebraic irrational, Gel'fond--Schneider says that every value in `(GC3)` is
transcendental.  In particular

`G=G_1=exp(pi)=(-1)^(-I)`                                         `(GC4)`

for the principal branch is transcendental.  If `-I*alpha in Q`, equivalently
`alpha in I*Q`, then `G_alpha` is a root of unity and the theorem does not apply.  For nonzero
rational `q`, `G_q=G^q` is transcendental but algebraic over `Q(G)`, so all rational multiples
add no further transcendence degree.

This is only an absolute conclusion.  From `(GC1)` and `(GC4)` one gets

`td_K K(G) in {0,1}`, `td_Q K(G)>=1`,                              `(GC5)`

and the second inequality was already true for `K`.  Gel'fond--Schneider does not exclude `G`
from being algebraic over, or even belonging to, a transcendence-degree-one field containing
`e` and `pi`.

There is a sharper but still external power consequence.  The `d=l=2` clause of the algebraic-
independence theorem gives

`exp(pi^2) is transcendental  or  e and pi are algebraically independent`. `(GC6)`

Indeed take `x_1=y_1=I*pi` and `x_2=y_2=1`.  If `exp(pi^2)` were algebraic, then the theorem's
two required entries `exp(x_1*y_1)=exp(-pi^2)` and `exp(x_1*y_2)=-1` would be algebraic.  Its
conclusion says that at least two among

`I*pi,1,I*pi,1,-1,e`                                               `(GC7)`

are algebraically independent, which can only mean `e` and `pi`.  Thus the hypothetical defect
forces `exp(pi^2)` to be transcendental.  But, exactly as in `(GC5)`, it does not force

`td_K K(exp(pi^2))=1`;                                             `(GC8)`

a transcendental number may be algebraic over a transcendental field of degree one.  For
`k>=2`, Gel'fond--Schneider itself does not apply to `exp(pi^k)`, because both the evident base
and exponent presentations use transcendental quantities.  The case `k=2` is obtained only
through the separate dichotomy `(GC6)`; the cited theorems give no accumulating independence for
the higher powers.

Six Exponentials displays the same field mismatch.  Use the two Q-independent rows `1,pi` and
the three Q-independent columns `1,I,pi`.  The six values are

`e, exp(I), G;   G, -1, exp(pi^2)`.                                `(GC9)`

The ordinary theorem is already satisfied by `e` or `G`.  The algebraic-independence refinement
does imply, under `(GC1)`,

`td_K K(G,exp(I),exp(pi^2))>=1`.                                   `(GC10)`

This is a genuine second absolute unit, but the theorem does not choose its generator.  Even if
`G` and `exp(pi^2)` both lie in an algebraic extension of `K`, `exp(I)` may supply `(GC10)`.
Replacing the third column by an algebraic number such as `sqrt(2)` only replaces the uncontrolled
entries by `exp(sqrt(2))` and `exp(sqrt(2)*pi)`; the latter is absolutely transcendental by
Gel'fond--Schneider but need not be transcendental over `K`.

Larger fixed-row Gel'fond matrices do not change this conclusion.  The exact Diaz bound `(GM)`
with `d=2` approaches only one transcendence degree over `K`, no matter how many algebraic
multipliers are used.  One common external parameter can therefore satisfy every fixed-row
application.  Growing the row rank requires new inputs outside `span_Q{1,pi}` and their
exponentials are not controlled by the AP field.

Nor does the hypothetical polynomial make a resultant bridge.  The identity in `(GC2)` is an
analytic equation

`T=exp((-I/2)*W)`,                                                  `(GC11)`

not a polynomial over `Q`.  Eliminating `W` between `P(E,W)` and a hypothetical polynomial
`Q(E,W,T)` for `G` over `K` merely produces another dependence between the transcendental
quantities `E,T`; it cannot produce a polynomial in `T` alone.  Conversely, eliminating through
`(GC11)` introduces logarithm branches

`W=2*I*(Log(T)+k*omega)=2*I*Log(T)-4*k*pi`,                         `(GC12)`

so the period and selected branch reappear.  Gel'fond--Schneider says that `T` is transcendental,
not that the height-two ideal `(P,Q)` cannot exist.

The algebraic compatibility is visible in the domain

`Q[E,W,T]/(W^2+4*E^2, T-E-1)`.                                    `(GC13)`

It has transcendence degree one and all three displayed residue classes are transcendental;
`T` is nevertheless already algebraic over `Q(E,W)`.  Thus every absolute conclusion in
`(GC4)--(GC8)` is compatible with a defect relation and a resultant relation.

An exact-kernel abstract character also saturates the exponential-matrix lower bound.  Let `S`
be algebraically independent from the actual number `pi`.  The source family

`omega,1,pi,pi^2,I`                                                `(GC14)`

is Q-linearly independent.  The target family

`omega,Log(pi),Log(pi+1),Log(pi+2),Log(S)`                          `(GC15)`

is Q-linearly independent as well: exponentiating a rational relation would give a
multiplicative relation among the distinct rational functions `pi,pi+1,pi+2,S`, and their
divisors force every exponent to vanish.  Extend the correspondence `(GC14)->(GC15)` to a
Q-linear automorphism `B` of `C`, and put `E_B=exp o B`.  Then

`ker(E_B)=omega*Z`,
`E_B(1)=pi`, `E_B(pi)=pi+1`, `E_B(pi^2)=pi+2`, `E_B(I)=S`.          `(GC16)`

For the adjacent pair `(1+omega,1+2*omega)`, both values are `pi` and

`Q(omega,pi)=Q(I,pi)`, `td_Q=1`,
`omega^2+4*E_B(1)^2=0`.                                           `(GC17)`

The analogues of both `exp(pi)` and `exp(pi^2)` are transcendental but remain inside this same
field.  The six entries for the rows and columns in `(GC9)` lie in `Q(I,pi,S)`: the one value
`E_B(I)=S` supplies exactly the single relative unit in `(GC10)`, while
`E_B(I*pi)=E_B(omega/2)=-1`.  The automorphism can similarly send any prescribed finite family
of powers or algebraic-multiple directions to multiplicatively independent rational functions
of `pi` and `S`, keeping the entire fixed-row matrix in an extension of relative transcendence
degree one.

This character is deliberately discontinuous and is not a counterexample to the analytic
Gel'fond--Schneider or Six-Exponentials theorems.  It is a sharp model of all their resulting
field-rank inequalities together with the exact period kernel and AP defect.  The missing input
would have to assert that one of the forced transcendental values is transcendental *over
`Q(e,pi)`*, or otherwise return that external unit to `K`.  Such a relative theorem already
contains the desired algebraic independence and is not supplied by the classical results.

### Failure is equivalent to a critical equality field algebraizing the period

The terminal branch of adjacent-pair deletion admits an exact converse, and the transcendental-
period branch can be converted to the same form without cycling.  The result is the following
structural equivalence.

**Critical-period equality theorem.**  Schanuel's conjecture fails if and only if there are
`m>=1` and a tuple `v=(v_1,...,v_m)` such that

`v is Q-linearly independent`,
`every v_i and exp(v_i) is transcendental`,
`td_Q F=m, where F=Q(v,exp(v))`,
`omega notin span_Q(v)`,
`omega is algebraic over F`.                                      `(CE1)`

The reverse implication is immediate but important.  The length-`m+1` tuple `(omega,v)` is
Q-linearly independent, and

`Q(omega,v,exp(omega),exp(v))=F(omega)`                            `(CE2)`

has transcendence degree `m`, because `exp(omega)=1` and `omega/F` is algebraic.  It is therefore
a Schanuel failure by one unit.

For the forward implication, choose a globally least fully transcendental defect-one failure
`z=(z_1,...,z_n)`.  Thus

`K=Q(z,exp(z))`, `td_Q K=n-1`,                                    `(CE3)`

and `n>=2` by the proved one-dimensional theorem.  If `D_i` is the field generated after deleting
`z_i` and `exp(z_i)`, minimality applies Schanuel to that independent length-`n-1` tuple.  Hence

`td_Q D_i=n-1`, `K/D_i is algebraic` for every `i`.                `(CE4)`

There are two exhaustive cases.

If `omega` is algebraic over `K`, choose an index `i` for which

`omega notin span_Q{z_j:j!=i}`.                                   `(CE5)`

Such an index always exists: if `omega` is outside `span_Q(z)`, every index works; if it lies in
that span, choose a nonzero coordinate in its unique expansion in the independent basis `z`.
Then the deletion tuple `v=z_hat_i` satisfies `(CE1)`: equality is `(CE4)`, and algebraicity of
`omega/D_i` follows by transitivity from `omega/K` and `K/D_i`.

If instead `omega` is transcendental over `K`, fix any `i` and replace the deleted coordinate by

`h=omega+z_i`,
`v=(z_1,...,z_(i-1),h,z_(i+1),...,z_n)`.                           `(CE6)`

This tuple has length `n`.  It is Q-linearly independent: a relation with nonzero coefficient of
`h` would put `omega` in `K`, while a relation with zero coefficient contradicts independence of
the deletion.  Moreover

`exp(h)=exp(z_i)`,                                                  `(CE7)`

so the new output is transcendental and algebraic over `D_i` by `(CE4)`.  The input `h` is
transcendental over `K`, hence over `D_i`; consequently its generated field `F_v` satisfies

`F_v is algebraic over D_i(h)`,
`td_Q F_v=td_Q D_i+1=n`.                                          `(CE8)`

Because `z_i` is algebraic over `D_i`, the identity `omega=h-z_i` makes `omega` algebraic over
`F_v`.  Finally, if

`omega=q*h+sum_(j!=i) q_j*z_j`,                                   `(CE9)`

then `q!=1` would put `omega` in `K`, while `q=1` would give the forbidden relation
`z_i+sum q_j z_j=0`.  Thus `omega` is outside the new rational span.  Equations
`(CE6)--(CE9)` prove every clause of `(CE1)` in the formerly cycling branch.

This theorem identifies the exact missing analytic statement:

**Critical-period exclusion.**  If a fully transcendental Q-linearly independent tuple `v`
satisfies `td_Q Q(v,exp(v))=len(v)` and does not rationally span `omega`, then `omega` is
transcendental over `Q(v,exp(v))`.                                 `(CE10)`

By `(CE1)--(CE2)`, `(CE10)` for all finite tuples is equivalent to full Schanuel.  It is not a
weaker relative analytic-subgroup lemma.

The arity-one equality stress makes the equivalence concrete.  Put

`v=(1+omega)`, `exp(v)=e`, `F=Q(1+omega,e)=Q(omega,e)`.             `(CE11)`

The input and output are transcendental, `omega` is not a rational multiple of `1+omega`, and
`omega` already belongs to `F`.  Therefore `(CE1)` reduces exactly to

`td_Q Q(omega,e)=1`,                                               `(CE12)`

the failure of algebraic independence of `e` and `pi`.  The equality hypothesis does not provide
extra slack: it is the one-dimensional Schanuel lower bound attained exactly, with the period
algebraicity carrying the missing next unit.

Known analytic-subgroup theorems do not exclude `(CE1)`.  The complex analytic subgroup theorem
starts with a logarithm of a point of a commutative algebraic group over `Qbar`.  Here the torus
point `(exp(v_1),...,exp(v_m))` is coordinatewise transcendental.  Declaring it rational over
`F` changes the ground field to a transcendental field and supplies no number-field height or
product formula; an analytic subgroup theorem relative to this base strong enough to prove
`(CE10)` would already prove Schanuel by the equivalence above.  The known algebraic point
`1 in G_m` sees only the allowed period `omega`.

The same hypothesis mismatch holds for commutative algebraic groups and one-motives.  A
one-motive `[Z^m -> G_m^m]` over `Qbar` requires algebraic image points, whereas the images in
`(CE1)` are transcendental.  Over `F` they are rational but the proposed period comparison is no
longer an arithmetic period theorem over an algebraic base.  Baker's theorem can exclude
algebraic-linear relations among logarithms of algebraic torus points; it says nothing about the
nonlinear assertion that the genuine period is algebraic over the field of transcendental points
and their logarithms.

A continuous exact-kernel model shows that topology and the real Lie-group structure saturate
`(CE1)`.  Reuse `(CQ20)`:

`c=-omega^2=4*pi^2`, `a=log(c)`,
`T(x+I*y)=a*x+I*y`, `E_T=exp o T`.                                 `(CE13)`

This is a conjugation-compatible continuous universal-cover homomorphism with
`ker(E_T)=omega*Z`, but it is nonholomorphic.  For `v=1+omega`,

`E_T(v)=c`, `Q(v,E_T(v))=Q(omega)`, `td_Q=1`;                      `(CE14)`

both `v` and `c` are transcendental, `omega` is outside `Q*v`, and `omega` belongs to the equality
field.  Thus every clause of `(CE1)`, the exact period lattice, covering topology, and reflection
compatibility can coexist.  What distinguishes the standard exponential is holomorphicity; no
unconditional analytic-subgroup theorem currently turns it into `(CE10)`.

The Lean formalization is primarily field and finite-dimensional linear algebra.  Define

`CriticalPeriodEquality (v : Fin m -> C) :=`
`  LinearIndependent Q v /\ FullyTranscendental v /\`
`  trdeg Q (tupleField v)=m /\`
`  period notin span Q (range v) /\ IsAlgebraic (tupleField v) period`. `(CE15)`

The target is `not Conjecture <-> exists m v, CriticalPeriodEquality v`.  The reverse direction
uses `exp(period)=1` and a `cons` independence lemma.  Forward formalization should reuse the
globally least fully transcendental defect-one reduction and deletion algebraicity; the algebraic
period branch needs a basis-coordinate deletion lemma, while the transcendental branch needs a
single-coordinate replacement equivalence, `exp(period+z_i)=exp(z_i)`, and the standard
transcendence-degree tower lemma for adjoining one transcendental element.  No new analytic axiom
is required for the equivalence itself.

### Period-shift fields have bounded geometry but need not stabilize

The critical equality theorem makes every integer period shift live in one finitely generated
field, but not in one finite extension of the shifted base.  Let `v` satisfy `(CE1)`, write

`y=exp(v)`, `F=Q(v,y)`, `L=F(omega)`, `td_Q L=m`,                    `(SF1)`

and, for `k=(k_1,...,k_m) in Z^m`, put

`u^(k)_i=v_i+k_i*omega`, `F_k=Q(u^(k),y)`.                         `(SF2)`

All exponential values are fixed and

`L=F_k(omega)`                                                     `(SF3)`

for every `k`.  Since adjoining one element changes transcendence degree by at most one, `(SF3)`
gives the exact dichotomy

`td_Q F_k in {m-1,m}`;
`td_Q F_k=m     iff L/F_k is finite`,
`td_Q F_k=m-1   iff omega/F_k is transcendental and L=F_k(omega)`. `(SF4)`

Thus `L/F` is finite by `(CE1)`, but `L/F_k` need not be finite.  This distinction blocks a
direct use of norms or finiteness of intermediate fields.

There is nevertheless a useful exact repetition lemma.  If `k!=l` and `F_k=F_l`, choose an
index `i` with `k_i!=l_i`.  Both labelled generators `u^(k)_i` and `u^(l)_i` then belong to the
common field, so

`omega=(u^(k)_i-u^(l)_i)/(k_i-l_i) in F_k`, hence `F_k=F_l=L`.     `(SF5)`

Consequently all proper shift fields are pairwise distinct.  Repetition, if it occurs, proves
only that the repeated field already contains the allowed period; it is not a contradiction.

The one-coordinate case describes all possible geometry.  Fix `i`, put

`x=v_i`, `A=Q(v_j (j!=i),y)`, `F=A(x)`.                            `(SF6)`

Because `td F=m`, either `td A=m` or `td A=m-1`.

If `td A=m`, then `L/A` is finite.  Characteristic zero makes it separable, so it has only
finitely many intermediate fields.  Equations `(SF5)--(SF6)` imply

`A(x+k*omega)=L for all but finitely many k in Z`.                 `(SF7)`

This is the strongest conclusion furnished by intermediate-field finiteness, and it merely says
that almost every shifted generator recovers the period.

If `td A=m-1`, then `x` is transcendental over `A` and `L/A` is a one-variable function field.
There is at most one `k` for which `x+k*omega` is algebraic over `A`: two such integers would make
both `omega` and `x` algebraic over `A`.  Choose the irreducible equation

`R(X,W) in A[X,W]`, `R(x,omega)=0`,                                `(SF8)`

which generates the height-one kernel because `L=A(x,omega)`.  For every nonexceptional `k`,
the substitution automorphism `X=U-kW` preserves irreducibility, and therefore

`[L:A(x+k*omega)]=deg_W R(U-kW,W)<=deg_total R`.                   `(SF9)`

If `D=deg_total R` and `R_D` is the top homogeneous part, equality holds whenever
`R_D(-k,1)!=0`; hence the degree in `(SF9)` is exactly `D` for all but finitely many integers.
The entire infinite family is a pencil of bounded-degree maps from one fixed curve to `P^1`.
Gonality supplies only the common lower bound for these degrees.  De Franchis-type finiteness
does not apply because the target has genus zero, and a fixed curve can have a positive-dimensional
family of maps to `P^1` in one linear system.

The same boundedness persists in several coordinates.  On a normal projective model `X` of `L`,
choose a divisor `D` dominating the pole divisors of `omega`, all `v_i`, and all `y_i`.  The maps
defined by `(u^(k),y)` all use sections of the fixed space `H^0(X,O_X(D))`.  Whenever such a map
is generically finite, the standard intersection formula gives

`[L:F_k]*deg(image_k)<=D^m`,                                      `(SF10)`

after replacing `D` once by a fixed very ample multiple if necessary.  Thus the finite degrees
are uniformly bounded.  The parameter coefficients `k_i` have unbounded arithmetic height, and
bounded geometric degree gives no Northcott statement for these moving transcendental subfields.

An exact-kernel character shows that the curve pencil can contain infinitely many distinct proper
fields of the same degree.  Choose a square root `t` of the genuine period,

`t^2=omega`,                                                       `(SF11)`

and choose a positive real `s` algebraically independent over `Q(omega)`.  The triples
`(omega,t,s)` and `(omega,Log(s),Log(s+1))` are Q-linearly independent; for the second triple,
exponentiating an integer relation gives the impossible rational-function identity
`s^a(s+1)^b=1`.  Extend their correspondence to a Q-linear automorphism `B` of `C` and define

`E_B=exp o B`, `B(omega)=omega`, `B(t)=Log(s)`, `B(s)=Log(s+1)`.   `(SF12)`

Then `ker(E_B)=omega*Z`, `E_B(t)=s`, and `E_B(s)=s+1`.  For

`v=(t,s)`, `F=Q(t,s)`, `td_Q F=2`, `omega=t^2 in F`,              `(SF13)`

all inputs and outputs are transcendental, `v` is Q-linearly independent, and
`omega notin span_Q(v)`.  Thus this is an exact critical-equality model.  Shifting its first
coordinate gives, with `u_k=t+k*t^2`,

`F_0=L=Q(s,t)`,
`F_k=Q(s,u_k)`, `[L:F_k]=2` for every `k!=0`.                      `(SF14)`

Indeed `t` has equation `k*T^2+T-u_k=0`, and the rational map `t |-> t+k*t^2` has degree two.
The fields for distinct nonzero `k` are distinct by `(SF5)`.  Their traces and norms are entirely
compatible with the pencil: if the other root is `t'=-1/k-t`, then

`Tr(t)=-1/k`, `N(t)=-u_k/k`,
`Tr(omega)=1/k^2+2*u_k/k`, `N(omega)=u_k^2/k^2`.                  `(SF15)`

These identities produce elements of the moving base `F_k`; they neither recover a common
arithmetic integer nor force the fields to coincide.  The deck involution `t |-> -1/k-t` itself
moves with `k`.

The distinction between `L/F` and `L/F_k` is also visible when the former is genuinely proper.
For any `d>=2`, put `x=omega^d`.  Extend a Q-linear basis map with

`B(omega)=omega`, `B(x)=Log(x)`,                                  `(SF16)`

and again set `E_B=exp o B`.  For `v=(x)`, one has

`F=Q(x)`, `L=Q(omega)`, `[L:F]=d`, `E_B(x)=x`,                    `(SF17)`

while `omega notin Q*x`.  Nevertheless

`F_0=F`, but `F_k=Q(x,x+k*omega)=L` for every `k!=0`.              `(SF18)`

Thus even a nontrivial finite `L/F` can collapse to degree one after every nonzero shift.

The genuine `e`--period boundary has exactly the same harmless stabilization.  Under the
hypothetical equality `td_Q Q(e,omega)=1`, take the critical tuple `v=1+omega`.  Then

`F=L=Q(e,omega)`,
`F_k=Q(e,1+(k+1)*omega)=L` for `k!=-1`,
`F_(-1)=Q(e)`, `[L:F_(-1)]<infinity`.                              `(SF19)`

The last degree is the unknown degree of the period over `Q(e)`.  Notice that `[L:F]=1`, whereas
`[L:F_(-1)]` can be larger; traces or norms at the exceptional shift are simply the coefficients
of the unknown minimal polynomial of `omega` over the transcendental field `Q(e)`.

The mixed stress displays both sides of `(SF4)`.  Let `ell=log 2` and suppose
`K=Q(e,ell)` has transcendence degree one.  If `omega/K` is algebraic, the length-one tuple

`v=ell+1`, `exp(v)=2e`, `F=K`, `L=K(omega)`                       `(SF20)`

is a critical equality witness.  Here `A=Q(e)` has full transcendence degree one and `L/A` is
finite, so `(SF7)` says that all but finitely many period shifts generate `L`; this is again
consistent with the assumed defect.

If instead `omega/K` is transcendental, put

`v=(omega+ell+1, 2*ell+1)`, `exp(v)=(2e,4e)`.                     `(SF21)`

Then `F=L=K(omega)` has transcendence degree two and satisfies `(CE1)`.  Shifting the first
coordinate by `-omega` gives exactly

`F_(-1)=K`, `L=K(omega)=F_(-1)(omega)`,
`td_Q F_(-1)=1`, `trdeg_(F_(-1)) L=1`;                            `(SF22)`

every other integer shift recovers `omega` and gives `F_k=L`.  Thus a field lying inside the
finite extension `L/F=L/L` can still have a transcendental extension to `L` after shifting.

Finally, fixed-base traces and norms cannot repair the problem.  In a finite extension they give

`Tr(x+k*omega)=Tr(x)+k*Tr(omega)`,
`N(x+k*omega)` is a polynomial in `k` of degree at most `[L:A]`,   `(SF23)`

but their coefficients lie in a finitely generated transcendental field and have no discrete
archimedean lower bound.  Traces over `F_k` instead land in different moving fields.  Hilbert- or
Grassmann-parameter compactness only records the rational pencil `k |-> F_k`; the integers are
Zariski dense in its parameter line, so infinitely many points do not make that map constant.
The exact model `(SF11)--(SF15)` realizes the nonconstant pencil.  Excluding it for the standard
holomorphic exponential would require a compatibility between the algebraic curve
`R(v_i,omega)=0` and the analytic differential equation of `exp`; field degree, birational
rigidity, traces, norms, and the fixed period kernel alone provide no such compatibility.

### Algebraic specialization reaches only the quadratic approximation boundary

Noether normalization makes approximation of a critical equality locus completely explicit, but
it loses the graph identity at exactly the available height exponent.  Let `W` be an irreducible
`Q`-locus of dimension `m`, let `p in W(C)` be the selected exponential point, and choose a finite
Noether normalization

`pi:W -> A^m`, `Delta=deg(pi)`, `t_0=pi(p)`.                       `(NS1)`

After deleting the branch divisor, assume first that `pi` is unramified at `p`.  There is then a
complex ball `U` about `t_0` and a holomorphic inverse branch `phi:U->W(C)` with

`phi(t_0)=p`, `||phi(t)-p||<=C_W*||t-t_0||`.                       `(NS2)`

Simultaneous Dirichlet approximation over `Q(I)` supplies infinitely many
`t_a in Q(I)^m` of projective multiplicative height at most `Q` such that

`||t_a-t_0||<=C(t_0)*Q^(-(1+1/m))`.                               `(NS3)`

For `m=1`, Gaussian continued fractions give the familiar exponent two.  Avoiding the proper
branch and discriminant loci, put `p_a=phi(t_a)`.  Every coordinate of `p_a` is algebraic and

`[Q(p_a):Q]<=2*Delta`.                                             `(NS4)`

Choose integral equations for the coordinates over the normalization ring whose coefficient
degrees are at most `B`.  The standard root-height inequality gives

`h(p_a)<=B*h(t_a)+O_W(1)`, hence `H(p_a)<=C_W*Q^B`.                `(NS5)`

Here `B` is fixed by the chosen finite model; replacing the normalization changes this fixed
height slope but cannot make it zero.

Write the algebraic specialization coordinates as `(v_i^(a),y_i^(a))`.  On the selected branch
the analytic graph discrepancies

`Delta_i(t)=y_i(phi(t))-exp(v_i(phi(t)))`                          `(NS6)`

vanish at `t_0`.  If the restriction has contact order `mu_i`, Taylor's theorem and `(NS3)` give

`0<|Delta_i(t_a)|<=C_i*Q^(-(1+1/m)*mu_i)`                         `(NS7)`

after discarding its other zeros.  Nonvanishing also follows directly from
Lindemann--Weierstrass whenever `v_i^(a)` is a nonzero algebraic number, because `y_i^(a)` is
algebraic.  In terms of the algebraic-point height, `(NS5)` converts `(NS7)` only to

`|Delta_i(t_a)|<=C_i'*H(p_a)^(-(1+1/m)*mu_i/B)`.                  `(NS8)`

Thus an unramified algebraic branch supplies polynomial smallness, with exponent two only on a
curve and only before the finite-model height slope is charged.  A ramification index replaces
the linear local inverse by a Puiseux exponent and is paid back in the algebraic degree/height of
the lifted point; it does not create a free contact order.

This is far outside the stable Hermite scale.  Even in the easier fixed-input audit above, the
uniform endpoint after prime avoidance was only

`log|exp(alpha_0)-beta| >= -O_D(log(H)*log log(3*H))`
`(alpha_0 fixed)`;                                                 `(NS9)`

allowing the algebraic input `alpha` to move adds its degree and height to the auxiliary
normalization rather than improving that scale.  Using `(NS9)` as an optimistic comparison,
`(NS5)` makes its right side `-O_W(log Q*log log Q)`, whereas `(NS7)` has logarithm only
`-O_W(log Q)`.  The inequalities are compatible.  Even if one grants the stronger favorable
polynomial measure `|exp(alpha)-beta|>=H^(-C_D)`, a contradiction would require the strict
numerical inequality

`(1+1/m)*mu_i > B*C_D`.                                           `(NS10)`

Noether normalization provides neither a large `mu_i` nor a small `B*C_D`; increasing the degree
of the locus or imposing higher contact increases the height and Hermite constants on the right.

The genuine period shows that exponent two cannot be improved by remembering the correct branch.
Consider the rational curve

`C: Y=1` through `(omega,1)`.                                     `(NS11)`

If `p_j/q_j` are continued-fraction convergents to `2*pi` and
`omega_j=I*p_j/q_j`, then `[Q(omega_j):Q]<=2`, `H(omega_j)asymp q_j`, and

`0<|exp(omega_j)-1|
 =|exp(I*(p_j/q_j-2*pi))-1|
 asymp|p_j/q_j-2*pi| < q_j^(-2)`.                                 `(NS12)`

The zero of `exp Z-1` at `omega` is simple, so the exponential discrepancy is exactly the
rational approximation error.  Consequently no lower bound based only on bounded algebraic
degree, height, and proximity to the true period can have a universal exponent strictly smaller
than two.  Fixing `omega` itself is not an algebraic specialization at all, while requiring
`exp(omega_a)=1` at a nonzero algebraic `omega_a` contradicts Lindemann--Weierstrass.  Every
closed-point specialization must therefore lose the exact period equation.

The canonical anchor makes the same boundary still more rigid.  Put

`x_0=1+omega`, `w_0=x_0`, `w_1=2*x_0-1=1+2*omega`,
`exp(w_0)=exp(w_1)=e`.                                             `(NS13)`

Under the hypothetical boundary `td_Q Q(omega,e)=1`, let `P(X,Y)` be the irreducible curve
equation of `(x_0,e)`.  Write

`d_X=deg_X P`, `d_Y=deg_Y P`.                                    `(NS14)`

If the projection to `X` is unramified at the selected branch, take

`x_j=1+I*p_j/q_j`, `P(x_j,y_j)=0`, `y_j -> e`.                    `(NS15)`

Then

`[Q(x_j,y_j):Q]<=2*d_Y`,
`h(y_j)<=d_X*log q_j+O_P(1)`,
`H(x_j,y_j)<=C_P*q_j^(d_X+1)`.                                   `(NS16)`

The two algebraic graph errors are

`delta_(0,j)=y_j-exp(x_j)`,
`delta_(1,j)=y_j-exp(2*x_j-1)`.                                  `(NS17)`

Their difference eliminates the algebraic branch coordinate exactly:

`delta_(1,j)-delta_(0,j)
 =exp(x_j)-exp(2*x_j-1)
 =exp(x_j)*(1-exp(x_j-1)).`                                      `(NS18)`

The last function has derivative `-e` at `x_0`.  Hence

`max(|delta_(0,j)|,|delta_(1,j)|)
 >=(1/2)*|exp(x_j)-exp(2*x_j-1)|
 asymp|x_j-x_0|`.                                                 `(NS19)`

On an unramified branch both errors are also `O(|x_j-x_0|)`.  Thus at least one, and generically
both, have exactly first-order size `q_j^(-2)`; in point-height language the available exponent
is at most `2/(d_X+1)`.  The repeated anchor output does not square the gain.  If the projection
ramifies, Puiseux variation makes `y_j-e` larger relative to `x_j-x_0`; the exact difference
`(NS18)` still prevents both errors from acquiring higher order in the period coordinate.

Norms and traces do not change this comparison.  Only the analytically selected branch in a
degree-`Delta` fiber is close to `p`; the other conjugate branches contribute the same height
powers that appear in `(NS5)`.  Taking a norm therefore multiplies one factor from `(NS7)` by
`Delta-1` uncontrolled factors of size `H^O(1)`.  This is precisely the degree/normalizer loss in
`(NS10)`, not an extra small factor.

A simple exact model shows that no property of Noether normalization itself can do better.
On `(NS11)` the normalization has `Delta=B=1`, the selected point is the genuine standard
exponential period point, and the algebraic specializations `(omega_j,1)` attain the quadratic
rate `(NS12)`.  All points are unramified, their degrees are uniformly two, and their heights are
exactly of order `q_j`.  The model already contains the correct local exponential derivative and
the true period, yet it produces no contradiction.  The missing ingredient would have to be a
pointwise transcendence measure beating the rational approximation exponent after all branch
degree and height slopes are charged; for the canonical anchor `(NS18)--(NS19)` proves that the
second coordinate supplies no such surplus.

### The exponential-motive torsor for the canonical anchor has the desired dimension only formally

The irregular-period formalism packages `e` and the ordinary period exactly, but its numerical
injectivity is the target rather than an unconditional theorem.  We use the primary preliminary
manuscript of Fresan--Jossen,
[*Exponential motives*](https://javier.fresan.perso.math.cnrs.fr/expmot.pdf), especially
Sections 8.1--8.2 and Propositions 12.1.3--12.1.5.

For an algebraic number `alpha`, their rank-one exponential motive is

`E(alpha)=H^0(Spec(Q),-alpha)`.                                   `(IM1)`

The potential is the constant `-alpha`, so its comparison scalar is `exp(alpha)`.  In particular,
`E(1)` has period matrix `(e)`.  The ordinary Tate motive `Q(-1)` has comparison scalar
`omega=2*pi*I`.  Therefore the smallest faithful exponential motive containing both values is

`M_min=E(1) direct_sum Q(-1)`,
`P_min=diag(e,omega)`.                                             `(IM2)`

If the unit object is displayed as well, as is convenient for the literal anchor, this becomes

`M_can=Q(0) direct_sum Q(-1) direct_sum E(1)`,
`P_can=diag(1,omega,e)`.                                           `(IM3)`

The canonical graph coordinates are merely the regular functions

`w_0=1+omega`, `w_1=1+2*omega`, `Y_0=Y_1=e`                       `(IM4)`

of the two nontrivial diagonal entries.  Thus duplicating the exponential value and translating
the period do not add a row, a character, or a Galois dimension.

The same object contains the integral presentation

`e-1=integral_0^1 exp(x) dx`.                                     `(IM5)`

Indeed `H^1(A^1,{0,1},-x)` has period structure `Q(0) direct_sum E(1)`.  Starting with
`diag(1,e)` and making rational changes of de Rham and Betti bases gives the exact matrix

`[[1,e-1],[0,e]]
 =[[1,1],[0,1]]*diag(1,e)*[[1,-1],[0,1]].`                         `(IM6)`

Hence replacing `e` by `e-1` changes neither the period algebra nor the tannakian group.

Fresan--Jossen compute unconditionally

`G_(E(1))=G_m`, `G_(Q(-1))=G_m`,
`G_(M_min)=G_m^2`.                                                 `(IM7)`

For the last equality, one can read their proof of Proposition 12.1.4 before its conjectural final
step.  The map `G_(M_min)->G_(Q(-1))` is surjective.  Classical motives have trivial perverse
realisation, whereas `E(1)` has perverse Galois group `G_m`; this places a copy of `G_m` in the
kernel.  Since the action on the two rank-one summands embeds the group in `G_m^2`, its dimension
is exactly two.

After choosing the bases in `(IM2)`, the motivic period torsor is therefore

`T_(M_min)=Spec Q[U,U^(-1),V,V^(-1)]`,
`alpha_(M_min)=(U,V)=(e,omega)`.                                  `(IM8)`

Its evaluation homomorphism is

`per:Q[U^(+/-1),V^(+/-1)] -> C`, `U |-> e`, `V |-> omega`.        `(IM9)`

Since both numbers are nonzero, injectivity of `(IM9)` is exactly

`td_Q Q(e,omega)=2`.                                               `(IM10)`

Thus the predicted Galois dimension is two and the motivic Galois dimension is proved to be two,
but the proved numerical dimension is only

`1<=td_Q Q(e,omega)<=2`.                                          `(IM11)`

Individual normality does not tensor.  Hermite--Lindemann proves that `(e)` is a generic point of
its one-dimensional exponential torsor, and transcendence of `pi` does the same for `(omega)` on
the Tate torsor.  Fresan--Jossen explicitly warn in Example 8.1.9 that a direct sum of two normal
period structures need not be normal.  The elementary model

`U |-> T`, `V |-> T+1`                                            `(IM12)`

has transcendental, individually generic coordinates and a formal ambient torus `G_m^2`, while
its numerical image lies on `V-U-1=0` and has transcendence degree one.  This is not a motivic
counterexample; it is a sharp model of why the two one-dimensional period theorems and the
two-dimensional formal torsor do not imply joint injectivity.

The exact missing theorem is stated in the same manuscript.  Their exponential period conjecture
says that the comparison point is generic in the motivic torsor, equivalently that the period
structure is normal.  Proposition 12.1.4 states conditionally that `exp(alpha)` for nonzero
algebraic `alpha` is transcendental over the field of all usual periods.  Setting `alpha=1` and
using the usual period `omega` gives `(IM10)` immediately.  Therefore that proposition does not
provide an unconditional route to algebraic independence of `e` and `pi`; in this smallest case
its mixed exponential/ordinary content is precisely the desired assertion.

The literal equation `exp(1+omega)=e` does not create an additional morphism in the category.
The zero-dimensional object `E(alpha)` is defined only for algebraic potentials `alpha`; there is
no object `E(1+omega)` over `Q`, because `1+omega` is itself a period rather than an algebraic
parameter.  The anchor identity is an external analytic identity between the two numerical
realisations in `(IM3)`, not a motivic tensor relation that could raise the dimension in `(IM7)`.

The E-function/E-operator theorems stop at the same boundary.  The E-function `exp(z)` satisfies
the rank-one E-operator `partial_z-1`; the Siegel--Shidlovskii--Andre--Beukers theorem proves the
one unit at `z=1`.  Beukers' primary
[*refined Siegel--Shidlovskii theorem*](https://annals.math.princeton.edu/2006/163-1/p08)
characterises relations among values at a nonzero algebraic point of E-functions with algebraic
Taylor coefficients.  The obvious second function `omega*1` is not an E-function over `Qbar`,
because its constant Taylor coefficient is not algebraic.  In differential Galois theory the
constant field is already `C`, so the Tate comparison scalar is invisible; adjoining a trivial
differential equation to `partial_z-1` leaves only the one-dimensional differential Galois group.

Arithmetic E-operator theory does identify connection and Stokes constants, but it supplies no
mixed special-value injectivity.  Fischler--Rivoal,
[*Arithmetic theory of E-operators*](https://jep.centre-mersenne.org/item/JEP_2016__3__31_0/),
show that finite connection constants are E-values and describe Stokes constants using G-values
and gamma derivatives.  This enlarges the list of permitted irregular periods; it does not turn
`2*pi*I` into an algebraic-coefficient E-function in the same Siegel--Shidlovskii system as
`exp(z)`.

A larger example in Fresan--Jossen makes the scope especially transparent.  Their Euler--
Mascheroni construction has period matrix

`[[1,0,gamma],[0,e^(-1),E_1(1)],[0,0,omega]]`                     `(IM13)`

and motivic Galois group

`{[[1,0,b],[0,a,c],[0,0,d]] : a,d in G_m; b,c in G_a}`,           `(IM14)`

of dimension four.  The exponential period conjecture would make

`e^(-1), E_1(1), gamma, omega` algebraically independent.          `(IM15)`

Unconditionally, `(IM14)` is a computation of the formal motivic group, not a four-unit
transcendence theorem; `(IM13)` introduces the new uncontrolled periods `E_1(1)` and `gamma`.
Quotienting those extensions returns the two-dimensional direct sum `(IM2)` and the same missing
injectivity `(IM9)`.

Consequently the exponential-motive formulation is exact but closed.  It proves the desired
formal rank `dim G_(M_min)=2`, while normality of the comparison point is algebraic independence
of `e` and `pi` itself.  The canonical anchor supplies no third motivic coordinate, and the
unconditional E-function, E-operator, and individual period theorems prove only the two separate
one-dimensional projections.

### Half-integer Bessel connection matrices contain `sqrt(pi)` only after a nonarithmetic normalization

The smallest nontrivial special-function package displays the normalization defect exactly.  The
modified Bessel equation of order `1/2` is

`z^2*y''+z*y'-(z^2+1/4)*y=0`.                                    `(BF1)`

It is a rank-two equation over `Q(z)`, ordinary at `z=1`.  Put

`u_+(z)=z^(-1/2)*exp(z)`, `u_-(z)=z^(-1/2)*exp(-z)`.

An arithmetically normalized Frobenius basis at zero is

`Ihat_-(z)=z^(-1/2)*cosh(z)`, `Ihat_+(z)=z^(-1/2)*sinh(z)`,
`[Ihat_-;Ihat_+]=(1/2)*[[1,1],[1,-1]]*[u_+;u_-]`.                 `(BF2)`

All coefficients after the allowed rational power `z^(-1/2)` are rational, and the connection
matrix in `(BF2)` is rational.  At the selected point,

`Ihat_-(1)=cosh(1)`, `Ihat_+(1)=sinh(1)`,
`Ihat_-(1)+Ihat_+(1)=e`.                                         `(BF3)`

Thus the arithmetic system contains the E-value `e`, but no `pi`-coordinate.

The conventional Bessel normalization is different.  From the defining hypergeometric series,

`I_nu(z)=(z/2)^nu/Gamma(nu+1)*{}_0F_1(;nu+1;z^2/4)`,             `(BF4)`

one obtains

`I_(-1/2)(z)=sqrt(2/(pi*z))*cosh(z)`,
`I_(1/2)(z)=sqrt(2/(pi*z))*sinh(z)`.                              `(BF5)`

Consequently its connection matrix is

`C_std=c*[[1,1],[1,-1]]`, `c=1/sqrt(2*pi)`,
`det(C_std)=-1/pi`.                                               `(BF6)`

At `z=1` the exact value formulas are

`I_(-1/2)(1)=c*(e+e^(-1))`,
`I_(1/2)(1)=c*(e-e^(-1))`.                                       `(BF7)`

Hence this single value/connection package really has the target field:

`Qbar(c,I_(-1/2)(1),I_(1/2)(1))=Qbar(e,sqrt(pi))`,
`td_Q(left side)=td_Q Q(e,pi)`.                                  `(BF8)`

But `(BF6)` was obtained from the rational matrix `(BF2)` by multiplying the local basis by
`sqrt(2/pi)`.  Such a basis change is not defined over `Qbar`.  A rank-one equation makes the
same issue unavoidable: the equation `y'=y` may be assigned the analytic basis
`sqrt(pi)*exp(z)`, so a notion of connection matrix allowing arbitrary complex rescaling can
insert `sqrt(pi)` into any system.  With arithmetic bases, the exponential equation has
connection constant one.  Thus rank two is the first familiar Bessel presentation, not an
intrinsic two-dimensional arithmetic object containing `e` and `sqrt(pi)`.

The exact Siegel--Shidlovskii scope confirms this distinction.  Beukers' primary refined theorem
[*A refined version of the Siegel--Shidlovskii theorem*](https://annals.math.princeton.edu/2006/163-1/p08)
assumes E-functions

`f(z)=sum_(n>=0) a_n*z^n/n!`, `a_n in Qbar`,                      `(BF9)`

with exponential height/denominator bounds, satisfying a common system over `Qbar(z)`, and
evaluates them at a nonzero algebraic ordinary point.  The normalized functions `cosh(z)` and
`sinh(z)` meet these hypotheses.  Functionally they have transcendence degree one because
`cosh(z)^2-sinh(z)^2=1`, and the theorem gives exactly

`td_Qbar Qbar(cosh(1),sinh(1))=td_Qbar Qbar(e)=1`.                `(BF10)`

The standard functions in `(BF5)` do not meet `(BF9)`: their first Puiseux coefficients contain
`1/sqrt(pi)`.  Adjoining the constant function `sqrt(pi)` does not repair this, because its
constant Taylor coefficient is not algebraic.  Running differential Galois theory over `C(z)`
also loses it: `(BF1)` has connected Picard--Vessiot group `G_m`, as its two solutions are the
opposite exponential characters, and every element of `C` is already fixed as a differential
constant.  The connection scalar `c` contributes no Galois dimension.

Rational-parameter confluent hypergeometric systems show the same tradeoff.  For Kummer's
E-function

`M(a,b,z)={}_1F_1(a;b;z)=sum_(n>=0) (a)_n/(b)_n*z^n/n!`,          `(BF11)`

the two sectorial coefficients at infinity are, up to the branch phase,

`Gamma(b)/Gamma(a)` and `Gamma(b)/Gamma(b-a)`.                    `(BF12)`

When the value collapses to the desired elementary exponential, the Gamma factor cancels:

`M(a,a,z)=exp(z)`,
`M(1,2,z)=(exp(z)-1)/z`.                                         `(BF13)`

In the first line the coefficients in `(BF12)` are `1` and `1/Gamma(0)=0`; in the second the
nonzero Gamma ratios are algebraic.  Half-parameters do produce `sqrt(pi)` in `(BF12)`, but the
value then generally introduces a new E-value.  The basic example is

`M(1/2,3/2,z)=integral_0^1 exp(z*t^2)dt`
`              =sqrt(pi)/(2*sqrt(z))*erfi(sqrt(z))`.              `(BF14)`

At `z=1`, Siegel--Shidlovskii controls the E-value
`M(1/2,3/2,1)`, not either factor `sqrt(pi)` or `erfi(1)`.  Direct-summing `(BF14)` with
`exp(z)` can prove independence statements involving this new E-value when the corresponding
functions are functionally independent, but supplies no elimination of `erfi(1)` and hence no
statement about `Q(e,pi)`.

Fourier--Laplace/E-operator theory classifies, rather than removes, this extra constant.  In the
primary paper of Fischler--Rivoal,
[*Arithmetic theory of E-operators*](https://jep.centre-mersenne.org/item/JEP_2016__3__31_0/),
Proposition 1 concerns connection at a finite algebraic point and places the constants of an
arithmetically normalized E-solution in the ring of E-values (with a possible logarithm for a
general local solution).  Their Theorem 2 concerns the irregular point at infinity and places
Stokes/asymptotic constants in the `G`-module generated by Gamma derivatives at rational points.
The factors `Gamma(1/2)=sqrt(pi)` in `(BF5)--(BF6)` lie in this latter permitted class.  Neither
result asserts algebraic independence between a finite E-value and a Gamma/Stokes constant.

This also explains why a mixed E/G theorem does not close the package.  One may replace the
determinant in `(BF6)` by the G-value `pi=4*arctan(1)`, but then the pair at the common algebraic
point is exactly the already audited E/G pair `(exp(1),4*arctan(1))`.  Existing complex
Siegel--Shidlovskii lifting applies only to the all-E block; the p-adic mixed criteria are
functional theorems under Frobenius/MOM hypotheses and do not give injectivity of this complex
evaluation map.  The special-function connection matrix adds no compatibility absent from that
pair.

The obstruction has an exact rank-one saturation model.  Let `T` be transcendental and set

`e_*=pi_*=T`, `c_*=(2*T)^(-1/2)`,
`I_-^*=c_*(T+T^(-1))`, `I_+^*=c_*(T-T^(-1))`.                    `(BF15)`

Then the normalized values `(T+T^(-1))/2,(T-T^(-1))/2` satisfy the hyperbola relation and have
transcendence degree one, exactly `(BF10)`.  The matrix `c_*[[1,1],[1,-1]]` has determinant
`-1/T`, all identities `(BF6)--(BF8)` hold, both `e_*` and `pi_*` are individually
transcendental, yet the full field has transcendence degree one.  This is not an analytic Bessel
counterexample; it proves that the exact connection formulas, the differential-Galois rank, the
all-E specialization theorem, and the arithmetic classification of the Gamma constant are all
compatible with failure of algebraic independence.

Therefore the Bessel/Kummer route packages `e` and `sqrt(pi)` in one displayed matrix only by
using two different arithmetic regimes: an E-value block and a Gamma-normalized Stokes block.
In the half-Bessel candidate the scalar disappears with legitimate arithmetic bases; in a
genuinely Gamma-valued Kummer Stokes block the accompanying algebraic-point value is new.
Retaining both entries makes numerical injectivity of `(BF8)` exactly algebraic independence of
`e` and `pi`.

### Nesterenko's CM theorem forces two units outside the AP defect field

The modular route gives a substantially stronger relative conclusion than `(GC5)`, but in the
wrong direction for closing the AP boundary.  We use Yu. V. Nesterenko's primary paper,
[*Modular functions and transcendence questions*](https://www.mathnet.ru/eng/sm158)
(Sbornik Math. 187 (1996), 1319--1348).  With Ramanujan's normalization

`P(q)=E_2(tau)`, `Q(q)=E_4(tau)`, `R(q)=E_6(tau)`,
`q=exp(2*pi*I*tau)`,                                               `(CM1)`

his theorem states, for every `0<|q|<1`,

`td_Q Q(q,P(q),Q(q),R(q))>=3`.                                    `(CM2)`

At the CM point `tau=I`, put `G=exp(pi)` and `gamma=Gamma(1/4)`.  The classical transformation
and theta-value formulas give exactly

`q=exp(-2*pi)=G^(-2)`,
`E_2(I)=3/pi`, `E_6(I)=0`,
`theta_3(I)=gamma/(sqrt(2)*pi^(3/4))`,
`eta(I)=gamma/(2*pi^(3/4))`,
`E_4(I)=3*gamma^8/(64*pi^6)`.                                     `(CM3)`

For completeness, `E_2(I)=3/pi` follows by evaluating
`E_2(-1/tau)=tau^2 E_2(tau)+6*tau/(pi*I)` at `tau=I`; weight six gives
`E_6(I)=I^6E_6(I)=-E_6(I)`.  Also `E_4(I)^3=1728*eta(I)^24`, which yields the last formula.  The
associated complete elliptic period is

`K_ell(1/sqrt(2))=gamma^2/(4*sqrt(pi))`.                            `(CM4)`

Because the fourth entry in `(CM2)` is zero, the other three entries are algebraically
independent.  Equations `(CM3)` therefore give the exact algebraic field comparison

`Q(q,E_2(I),E_4(I)) subset Q(G,pi,gamma)`,
`Q(G,pi,gamma) algebraic over Q(q,E_2(I),E_4(I))`,                 `(CM5)`

where the reverse algebraicity uses `G^2=q^(-1)`, `pi=3/E_2(I)`, and
`gamma^8=(64/3)*pi^6 E_4(I)`.  Hence Nesterenko's celebrated CM corollary is

`td_Q Q(pi,G,gamma)=3`;                                            `(CM6)`

in fact `pi,G,gamma` are algebraically independent.  The theta constant, eta value, and elliptic
period in `(CM3)--(CM4)` add no further direction: after algebraic closure they generate the same
field as `pi,gamma`.

Now impose the AP defect

`K=Q(e,omega)`, `td_Q K=1`, `omega=2*pi*I`.                        `(CM7)`

After adjoining the algebraic number `I`, the field `K(I)=Q(e,pi,I)` is algebraic over `Q(pi)`:
it is finitely generated, contains `Q(pi)`, and has the same transcendence degree one.  Algebraic
independence is preserved under algebraic base extension, so `(CM6)` gives the exact tower

`td_K K(G)=1`,
`td_(K(G)) K(G,gamma)=1`,
`td_K K(G,gamma)=2`,
`td_Q K(G,gamma)=3`.                                               `(CM8)`

Thus neither the modular nome nor the CM period can lie in an algebraic extension of the defect
field.  The modular theorem does not merely fail to force a shared period into `K`; conditionally
on the defect, it forces `G` and `gamma` to be algebraically independent *over* `K`.

Quasimodular refinements do not create a bridge to `e`.  The level-one quasimodular ring with
rational Fourier coefficients is `Q[E_2,E_4,E_6]`, and the Ramanujan derivation remains in it:

`theta E_2=(E_2^2-E_4)/12`,
`theta E_4=(E_2 E_4-E_6)/3`,
`theta E_6=(E_2 E_6-E_4^2)/2`.                                   `(CM9)`

Consequently every value at `I` obtained from these forms and any finite number of their
`q`-derivatives lies in

`Q(1/pi, gamma^8/pi^6)`,                                          `(CM10)`

while adjoining the nome adds exactly `G`.  Theta/elliptic-period formulas only make algebraic
extensions of `(CM10)`.  Stronger value theorems for algebraically independent quasimodular forms
can certify subtuples of the already-known three directions `(pi,G,gamma)`; they do not introduce
the constant `e=exp(1)`.

The E-function side has the complementary hypothesis mismatch.  The function `exp(z)` is an
E-function and its algebraic-point value at `z=1` is `e`; Siegel--Shidlovskii and its refinements
(for example the primary value theorem of
[Nesterenko--Shidlovskii](https://www.mathnet.ru/eng/sm152)) compare such values through a common
linear differential system at algebraic arguments.  Here
`G=exp(pi)` uses the transcendental argument `pi`, while `q=exp(-2*pi)` is a transcendental
argument/value in the exponential presentation.  As functions of `tau`, the modular and
quasimodular forms are not E-functions in a common E-system with `exp(z)`.  Direct-summing the
unrelated differential equations supplies no specialization theorem over the transcendental base
`Q(pi,G,gamma)`.  The exact compatibility left by all known theorems is

`e algebraic over Qbar(pi)`,
`G,gamma algebraically independent over Qbar(pi,e)`.               `(CM11)`

The first line is the hypothetical AP defect; the second is precisely `(CM8)`.  There is no
logical tension between them.

An exact rank model makes the saturation transparent.  Let `T,U,V` be algebraically independent
and put formally

`pi_*=T`, `omega_*=2*I*T`, `e_*=T`, `G_*=U`, `gamma_*=V`,
`q_*=U^(-2)`, `E_(2,*)=3/T`, `E_(6,*)=0`,
`E_(4,*)=3*V^8/(64*T^6)`.                                        `(CM12)`

Then the AP field `Q(e_*,omega_*)` has transcendence degree one, the three nonzero modular entries
`q_*,E_(2,*),E_(4,*)` are algebraically independent, all identities `(CM3)` hold formally, and

`td_(Q(e_*,omega_*)) Q(e_*,omega_*,G_*,gamma_*)=2`.                `(CM13)`

One can also retain the exact period group law.  Choose actual complex `U,V` algebraically
independent over `Qbar(pi)`, extend the Q-linear assignment

`B(omega)=omega`, `B(1)=Log(pi)`, `B(pi)=Log(U)`                   `(CM14)`

to an automorphism of `C`, and set `E_B=exp o B`.  Then
`ker(E_B)=omega*Z`, the adjacent pair `(1+omega,1+2*omega)` has repeated value `pi` and a
transcendence-degree-one field, while its analogue `E_B(pi)=U` and the independent period symbol
`V` provide exactly the two modular directions in `(CM8)`.  This discontinuous character is not
a model of the analytic modular theorem; it shows that its exact field-rank conclusion and the
period homomorphism are fully compatible with AP defect one.

The modular route therefore proves a positive and sharp relative theorem, `(CM8)`, but every new
unit is external.  Closing the AP boundary would require a mixed E/modular special-value theorem
forcing `e` to be transcendental over `Qbar(pi)` (or forcing one modular unit algebraically back
into `K`).  The former is exactly algebraic independence of `e` and `pi`, and the latter is
contradicted by Nesterenko under the defect hypothesis.

### Gaussian normalization at nome `e^(-1)` leaves two external modular units

There is a particularly literal Poisson coupling of `e` and `pi`, but normalizing the Gaussian
to make its nome `e^(-1)` moves the theta parameter away from the CM locus.  Use

`theta_3(tau)=sum_(n in Z) exp(pi*I*n^2*tau)`,
`tau=I/pi`, `r=exp(pi*I*tau)=e^(-1)`.                              `(GP1)`

Poisson summation for `S_0(a)=sum_n exp(-a*n^2)` gives

`S_0(a)=sqrt(pi/a)*S_0(pi^2/a)`,
`theta_3(I/pi)=sqrt(pi)*theta_3(I*pi)`.                            `(GP2)`

The square roots in this section are the positive ones.  In modular notation, `tau'=-1/tau=I*pi`
and `(GP2)` is the usual transformation

`theta_3(tau')=(-I*tau)^(1/2)*theta_3(tau)`.

Thus the theta nome is `r=e^(-1)`, while the level-one modular Fourier parameter is

`q=exp(2*pi*I*tau)=r^2=e^(-2)`;                                  `(GP3)`

at the dual point they are respectively `r'=e^(-pi^2)` and `q'=e^(-2*pi^2)`.  This distinction
prevents a hidden factor-of-two in applying modular value theorems.

Differentiation creates no second Poisson equation.  If
`S_2(a)=sum_n n^2 exp(-a*n^2)`, differentiating `(GP2)` gives exactly

`S_2(1)=sqrt(pi)*(S_0(pi^2)/2-pi^2*S_2(pi^2))`.                  `(GP4)`

Equivalently, logarithmically differentiating the modular transformation gives

`theta_3'(tau)/theta_3(tau)`
` =tau^(-2)*theta_3'(tau')/theta_3(tau')-1/(2*tau)`,              `(GP5)`

so at `tau=I/pi` the coefficients are `-pi^2` and `I*pi/2`.  The heat equation merely rewrites
the same moment identity as a second derivative in the elliptic variable.  Higher differentiated
Poisson identities similarly express dual moments through the original moments and powers of
`pi`; they do not successively eliminate the theta values.

The exact arithmetic content is best seen through modular forms.  Put

`A=E_2(tau)`, `B=E_4(tau)`, `C=E_6(tau)`.                         `(GP6)`

Nesterenko's theorem `(CM2)` applies because `0<|q|<1`; it does not require `tau` or `q` to be
algebraic.  Since `q=e^(-2)` and `e` are algebraic over one another, it yields

`td_Q Q(e,A,B,C)>=3`.                                             `(GP7)`

Consequently, under the arity-two AP defect

`F=Qbar(e,pi)`, `td_Q F=1`,
`td_F F(A,B,C)>=2`.                                                `(GP8)`

This is a genuine relative conclusion, but both guaranteed units are new modular values.

Theta constants and their derivatives do not hide a smaller field to which `(GP8)` could be
projected.  Write `x=theta_2(tau)^4`, `y=theta_3(tau)^4`, and
`z=theta_4(tau)^4`.  Jacobi's identities are

`y=x+z`,
`B=x^2+x*z+z^2`,
`C=(x+2*z)*(2*x+z)*(z-x)/2`.                                     `(GP9)`

Because `B^3-C^2=1728*Delta(tau)!=0`, these equations make all three theta constants algebraic
over `Q(B,C)`, and conversely `B,C` are polynomial in their fourth powers.  Their first
derivatives satisfy

`theta_2'/theta_2=(pi*I/12)*(A+theta_3^4+theta_4^4)`,
`theta_3'/theta_3=(pi*I/12)*(A+theta_2^4-theta_4^4)`,
`theta_4'/theta_4=(pi*I/12)*(A-theta_2^4-theta_3^4)`.             `(GP10)`

Together with the Ramanujan equations `(CM9)`, this proves the exact algebraic-closure equality

`acl F(A,B,C)`
` =acl F(theta_j(tau),theta_j'(tau):j=2,3,4)`.                    `(GP11)`

The same remains true after adjoining any finite set of theta derivatives, heat-equation
derivatives, or Wronskians.  Hence a heat or Wronskian calculation can recover the two external
directions in `(GP8)`, but cannot turn them into a second unit inside `F`.

Modular inversion also preserves rather than eliminates these directions.  Besides `(GP2)`,

`theta_2(tau')=pi^(-1/2)*theta_4(tau)`,
`theta_4(tau')=pi^(-1/2)*theta_2(tau)`,                            `(GP12)`

and

`E_2(tau')=(6-A)/pi^2`,
`E_4(tau')=B/pi^4`,
`E_6(tau')=-C/pi^6`.                                              `(GP13)`

Thus all dual theta and modular values lie in the algebraic closure of `F(A,B,C)`.  Applying
Nesterenko again at `q'=e^(-2*pi^2)` says

`td_Q Q(q',E_2(tau'),E_4(tau'),E_6(tau'))>=3`,                   `(GP14)`

but `(GP8)` already permits `td_Q F(A,B,C)=3`.  Therefore `(GP14)` is compatible even with
`q'` algebraic over `F(A,B,C)` and forces no additional relative unit.  The attractive formula

`pi=(theta_3(tau)/theta_3(tau'))^2`                               `(GP15)`

is simply `(GP2)` solved for its Gaussian normalization, not an elimination of the common
theta scale.

Nor is a Gamma-period evaluation available here.  Both `tau=I/pi` and `tau'=I*pi` are
transcendental, hence are not imaginary-quadratic CM points.  Chowla--Selberg and the special
`Gamma(1/4)` formulas in `(CM3)--(CM4)` apply at `tau=I`, whose nome is `e^(-pi)`, not at either
parameter in `(GP1)`.  Rescaling the Gaussian from `e^(-pi)` to `e^(-1)` is exactly what trades
the CM Gamma evaluation for the unknown theta values in `(GP11)`.

The rank obstruction is sharp at the level of every algebraic identity and theorem inequality
used above.  Let `T,U,V` be algebraically independent, and formally set

`e_*=pi_*=T`, `q_*=T^(-2)`, `A_*=U`, `B_*=V`, `C_*=1`.             `(GP16)`

Then `Q(e_*,pi_*)` has transcendence degree one while
`Q(q_*,A_*,B_*,C_*)` has transcendence degree three, with exactly two units over the defect
field.  In an algebraic closure choose `x_*,z_*` satisfying `(GP9)`, take fourth roots for the
three theta symbols, and define their derivatives by `(GP10)`.  Define the dual symbols by
`(GP12)--(GP13)` and take, for example, `q_*'=T^(-2)`; the dual four-tuple again has
transcendence degree three.  This is not asserted to be a specialization of analytic modular
forms.  It is a sharp algebraic model showing that Poisson inversion, all theta/derivative
identities, and both Nesterenko lower bounds are jointly compatible with defect one.

Therefore the `e^(-1)` Gaussian normalization yields the strong but external inequality `(GP8)`.
To force algebraic independence of `e` and `pi` one would still need a theorem placing one of
`A,B,C` algebraically over `Qbar(e,pi)`, or a mixed value theorem adding a unit already inside
that field.  Poisson summation, modular inversion, the heat equation, and known modular
algebraic-independence theorems provide neither.

### Mixed exponential--modular Ax--Schanuel loses every arithmetic unit at the CM fiber

There is now a primary theorem which treats the two uniformizers in one functional statement:
Blazquez-Sanz--Casale--Freitag--Nagloo,
[*A differential approach to Ax--Schanuel, I*, Theorem E](https://arxiv.org/html/2102.03384v5)
(arXiv:2102.03384v5, 2026).  For `k` exponential germs `p_1,...,p_k` and `ell`
`j_Gamma`-germs `p_(k+1),...,p_(k+ell)`, all in formal variables `s_1,...,s_m`, it says that

`td_C C(p_1,...,p_(k+ell), exp(p_1),...,exp(p_k),`
`        j(p_(k+1)),j'(p_(k+1)),j''(p_(k+1)),...)`
`  < k+3*ell+rank(partial p_j/partial s_i)`                       `(MX1)`

forces either a nonzero integer relation `sum n_i*p_i in C` among the exponential inputs or a
commensurator relation between two modular inputs.  Two features of the exact statement are
decisive here: the base field in `(MX1)` is **all of `C`**, and the rank is a rank of nonconstant
formal germs, not a rank of their specialized values.

Apply `(MX1)` with `k=ell=1`, independent variables `s,t`, and germs

`p_1=I+s`, `p_2=I+t`.                                             `(MX2)`

They are literally centered in the upper half-plane, as required by the theorem.  Over `C`,
replacing `p_1` by `Z=1+s` and rescaling its output from `exp(I+s)` to
`Y=exp(1+s)=exp(1-I)*exp(I+s)` changes neither field nor transcendence degree.  There is no
nonzero integer relation on the nonconstant `p_1`, there is only one modular input, and the
Jacobian rank is two.  Hence `(MX1)` gives the sharp equality

`td_C C(Z,T,Y,J_0,J_1,J_2)=6`,                                   `(MX3)`

where `T=I+t` and `(J_0,J_1,J_2)=(j(T),j'(T),j''(T))`.  Thus the two-dimensional analytic graph is
Zariski dense over `C` in `A^6`.  This is a strong functional theorem, but its specialization at
`s=t=0` is

`(Z,T,Y,J_0,J_1,J_2)=(1,I,e,1728,0,j''(I)).`                     `(MX4)`

The closure from `(MX3)` has fiber `A^4_(Y,J_0,J_1,J_2)` after imposing `Z=1,T=I`; imposing the
two CM output equations `J_0=1728,J_1=0` still leaves
`A^2_(Y,J_2)`.  The analytic graph meets that residual plane in the single point `(e,j''(I))`,
but `(MX1)` supplies no algebraic equation on that point.  Equivalently, evaluation of the
local analytic coordinate algebra at `s=t=0` has a large kernel containing
`s,t,Y-e,J_0-1728,J_1,J_2-j''(I)`.  There is no specialization inequality from the left side of
`(MX3)` to `td_Q Q(e,pi)`.

The nome does not change this conclusion.  Put `omega=2*pi*I` and add a second exponential germ
`p_2=I+omega*t`, whose output differs by a nonzero `C`-constant from

`Q(t)=exp(omega*(I+t))`, `Q(0)=q=exp(-2*pi)`.                     `(MX5)`

Use `p_1=I+s`, `p_2=I+omega*t`, and the modular input `p_3=I+t`.  No nonzero integer combination
of the two exponential inputs is constant, the input Jacobian has rank two, and there is only
one modular input.  Theorem E with `(k,ell)=(2,1)` therefore gives the exact seven-generator
equality

`td_C C(Z,T,Y,Q,J_0,J_1,J_2)=7`.                                 `(MX6)`

After `Z=1,T=I,J_0=1728,J_1=0`, its ambient residual fiber is the full
`A^3_(Y,Q,J_2)`.  In particular the theorem sees `(e,q,j''(I))` as three arbitrary constants:
`e`, `q`, `omega`, and every CM period already belonged to its base field before the count began.
On the one-parameter diagonal `s=t`, the input rank drops from two to one and Theorem E gives the
equally sharp value five for `C(s,exp(s),j(I+s),j'(I+s),j''(I+s))`; specializing `s=0` again
annihilates the whole functional contribution.

Ax--Schanuel with derivatives therefore does not even see the desired fixed pair.  For the
adjacent-period germs

`r_0=I+s`, `r_1=I+omega+s`,
`r_1-r_0=omega in C`, `exp(r_1)=exp(r_0)`,                        `(MX7)`

the first exceptional conclusion of Theorem E already holds with integer vector `(-1,1)`.
Adding any number of modular germs cannot turn this instance of `(MX1)` into a lower bound.  This
is exactly the functional shadow of the canonical pair `(1+omega,e)` (or of the two coordinates
`1+omega,1+2*omega`): the repeated exponential is recorded as a permitted constant additive
relation, not as a bonus dimension.

There is nevertheless a sharp arithmetic conclusion at the actual CM fiber, but it comes from
Nesterenko's value theorem `(CM2)`, not from mixed Ax--Schanuel.  With `G=exp(pi)` and
`gamma=Gamma(1/4)`, Ramanujan's differential identities give

`D j=-E_4^2*E_6/Delta`, `D=(1/omega)*d/dtau`,
`D^2 j(I)=864*E_4(I)`,
`j''(I)=omega^2*864*E_4(I)=-162*gamma^8/pi^4`.                    `(MX8)`

If the canonical anchor field `K=Q(1+omega,e)=Q(omega,e)` has defect one, `(CM6)--(CM8)` say that
`G,gamma` are algebraically independent over `K` (an algebraic extension by `I` is harmless).
Taking nonzero powers in `(CM3)` and `(MX8)` therefore yields the exact relative count

`td_K K(q,j''(I))=2`, `td_Q K(q,j''(I))=3`.                       `(MX9)`

Thus the CM fiber adds **two external units** to the larger anchored field, not the missing unit
inside `K`.  Neither one is algebraic over a deletion field, so minimal-deletion algebraicity
does not pull it back.

Finally, the exact specialized-data counterfeit shows that all these counts saturate.  Let
`T,U,V` be algebraically independent and set

`omega_*=2*I*T`, `e_*=T`, `G_*=U`, `gamma_*=V`, `q_*=U^(-2)`,
`J_(0,*)=1728`, `J_(1,*)=0`, `J_(2,*)=-162*V^8/T^4`.              `(MX10)`

Then `Q(1+omega_*,e_*)=Q(I,T)` has transcendence degree one, while

`td_(Q(I,T)) Q(I,T,q_*,J_(2,*))=2`;                              `(MX11)`

all specialized CM, nome, derivative, and period formulas above hold, and the total field has
transcendence degree three.  This is not asserted to be an analytic `exp`--`j` model; it is an
exact model of every algebraic identity and dimension statement surviving specialization.
The actual functional family `(MX2)--(MX6)` supplies the complementary analytic witness: maximal
generic Ax--Schanuel dimension and arbitrary constant specialization coexist.  A contradiction
would require a mixed **special-value** theorem over `Qbar`, not functional Ax--Schanuel over
`C`; at this anchor that missing assertion is precisely the algebraic independence of `e` and
`pi` one was trying to prove.

### The adjacent-period binomial removes exactly the apparent defect gain in auxiliary counts

Specialize an auxiliary-polynomial construction to `(AP1)`.  Thus

`w_1=w_0+omega`, `y_i=exp(w_i)`, `y_1=y_0`,
`K=Q(w,y)`, `td_Q K=n-1`.                                           `(AJ1)`

The known multiplicative relation lattice is **exactly** rank one.  If `m in Z^n` satisfies
`y^m=1`, then `m dot w=k*omega` for some `k in Z`, because the kernel of the complex exponential
is `Z*omega`.  Since `omega=w_1-w_0` and `w` is Q-linearly independent,

`m=k*(e_1-e_0)`.                                                    `(AJ2)`

Consequently, for toric indices `b,b'`,

`y^b=y^(b') iff b-b' in Z*(e_1-e_0)`.                              `(AJ3)`

This permits exact quotient counts, but only for values at the selected point.

First use coordinatewise boxes

`0<=a_i<=D`, `0<=b_i<=E`, `X^a*Y^b`.                               `(AJ4)`

Before quotienting there are

`N_full=(D+1)^n*(E+1)^n`                                           `(AJ5)`

coefficients.  In a collision class only `s=b_0+b_1` survives, with `0<=s<=2E`, so the image of
the box in `Q[X,Y]/(Y_1-Y_0)` has exact dimension

`N_quot=(D+1)^n*(2E+1)*(E+1)^(n-2)`.                              `(AJ6)`

Thus `N_quot~2*D^n*E^(n-1)`, one full toric power smaller than `(AJ5)`.  The kernel has dimension

`(D+1)^n*E^2*(E+1)^(n-2)`                                         `(AJ7)`

and consists exactly of the box elements divisible by `B=Y_1-Y_0`.  More generally, for
`0<=s<=E+1`, the subspace divisible by `B^s` has dimension

`(D+1)^n*(E-s+1)^2*(E+1)^(n-2)`.                                  `(AJ8)`

Indeed division by `Y_1-Y_0` lowers both individual degrees in `Y_0,Y_1` by one; iteration gives
`(AJ8)`.  Equivalently the `B`-adic graded pieces in the two collision variables have dimensions
`2(E-s)+1`, `0<=s<=E`.  For total additive degree at most `D` and total toric degree at most `E`,
the analogous exact formulas are

`N_full=binom(D+n,n)*binom(E+n,n)`,
`N_quot=binom(D+n,n)*binom(E+n-1,n-1)`,
`dim(B^s)=binom(D+n,n)*binom(E-s+n,n)`.                              `(AJ9)`

The large kernel in `(AJ7)` is not a supply of new arithmetic auxiliaries.  On the scaled leaf

`X_i=t*w_i`, `Y_i=exp(t*w_i)`,

the binomial becomes

`B(t)=exp(t*w_0)*(exp(t*omega)-1)`,
`B(1)=0`, `B'(1)=y_0*omega!=0`.                                    `(AJ10)`

Therefore multiplication by `B` gives exactly one automatic order of vanishing, and

`ord_(t=1)(B^s Q)=s+ord_(t=1)Q`.                                   `(AJ11)`

Every apparently free kernel coefficient has merely selected an auxiliary already containing
the known simple factor.  Reaching order `T` through this kernel still requires `B^T`, spending
toric degree `T`.

It is essential not to identify equal point values with equal analytic frequencies.  Fix all
indices except `b_0,b_1` and fix `s=b_0+b_1`.  The allowed `b_1=j` form a consecutive interval of
length

`m_s=min(E,s)-max(0,s-E)+1`.                                       `(AJ12)`

Their frequencies are

`lambda_j=s*w_0+j*omega+sum_(r>=2)b_r*w_r`.                         `(AJ13)`

They have the same exponential at `t=1`, but are pairwise distinct.  The first `m_s` derivative
columns have the exact Vandermonde determinant

`det((y^b)*lambda_j^r)_(0<=r<m_s,j)`
` =(y^b)^(m_s)*omega^(m_s*(m_s-1)/2)*product_(q=1)^(m_s-1) q! !=0`. `(AJ14)`

Thus `m_s` colliding values support at most multiplicity `m_s-1`, exactly as `m_s` distinct
frequencies do.  Polynomial prefactors of degree at most `A` replace this by the confluent bound
`(A+1)*m_s-1`; the collision supplies no reduction.

The full univariate pullback of `(AJ4)` has polynomial prefactor degree at most `nD` and
`(E+1)^n` distinct frequencies, hence

`ord_(t=1)F < (nD+1)*(E+1)^n`                                     `(AJ15)`

for every nonzero pullback.  A normal representative modulo `B`, with `Y_1` absent and
`deg_(Y_0)<=2E`, has `(2E+1)*(E+1)^(n-2)` distinct frequencies and the corresponding bound

`ord_(t=1)F < (nD+1)*(2E+1)*(E+1)^(n-2)`.                          `(AJ16)`

The discarded frequencies are precisely those in the `B`-multiples; `(AJ14)` shows why they
cannot also be discarded from a jet calculation.

The coordinate-leaf multiplicity threshold is unchanged even numerically.  The sharp tensor
threshold for degrees `(D_i,E_i)` is

`Z=sum_i ((D_i+1)*(E_i+1)-1)`.                                    `(AJ17)`

With `D_i=E_i=R`, the full box gives

`Z_full=n*((R+1)^2-1)=n*R^2+2*n*R`.                               `(AJ18)`

For the quotient normal form take toric degrees `(2R,0,R,...,R)`.  Then

`Z_quot=((R+1)*(2R+1)-1)+R`
`       +(n-2)*((R+1)^2-1)=n*R^2+2*n*R`.                          `(AJ19)`

The coefficient space loses a factor `R`, but the exact zero threshold does not move at all; the
double degree in `Y_0` compensates the omitted `Y_1` direction.

Now insert the arithmetic Hilbert--Siegel count, keeping separate two constructions which must
not be conflated.  If one uses only a normal representative modulo `B`, then at uniform degree
`R` its coefficient rank from `(AJ6)` is

`N_quot=(2R+1)*(R+1)^(2n-2)=Theta(R^(2n-1)).`                      `(AJ20)`

Under the hypothetical defect `d=td_Q K=n-1`, scalarizing all total graph jets below `T` over a
transcendence basis gives the optimistic bound

`U=O(R^d*T^n)=O(R^(n-1)*T^n)`                                     `(AJ21)`

rational rows when `T=O(R)`.  More honestly, differentiating the exponentials introduces powers
of the `w_i` through degree `T`, so the relevant Hilbert numerator has degree `O(R+T)` and

`U=O((R+T)^(n-1)*T^n)`.                                           `(AJ21a)`

Either estimate gives, for the quotient-only construction,

`T=O(R)`.                                                         `(AJ22)`

This is a full factor `R` below `(AJ18)--(AJ19)`.

The extra coefficients in `(AJ5)` cannot, however, simply be declared spurious for jets: the
`B`-adic piece `B^s Q` first appears in derivative order `s`, and `(AJ14)` shows that all pieces
are visible once `T>E`.  Retaining the full space gives `N_full=Theta(R^(2n))`.  The deliberately
overoptimistic frozen-degree version of `(AJ21)` then gives `T=O(R^(1+1/n))`, while the honest
degree growth `(AJ21a)` gives, in the relevant range `T>=R`,

`T=O(R^(2n/(2n-1)))`.                                              `(AJ22a)`

This modest gain is genuine in the dimension count but is still `o(R^2)`.  The automatic kernel
`B^s` itself contributes only `s<=R` orders.  Thus quotienting explains exactly why a
normal-representative construction returns to the equality-case range; allowing all collision
modes improves the exponent slightly, but nowhere near the zero threshold.  The invalid step
would be to retain their coefficient count while continuing to treat them as one frequency in
the higher-jet rows.

The height bookkeeping has no hidden margin.  For an integer linear system with `N` unknowns,
`U<N` rows, entry height `A` and common denominator `Delta`, a standard Siegel bound has the
shape

`log H(P) <= (U/(N-U))*(log A+log Delta+O(log N)).`                 `(AJ23)`

At the terminal dimension range (either `T=cR` for the quotient or `(AJ22a)` for the full space)
the ratio `U/N` is already a nonzero constant; it does not tend to zero.  Divided jets through
order `T` introduce a common factorial denominator dividing `T!`, with

`log(T!)=T*log T-T+O(log T)`.                                      `(AJ24)`

Using ordinary derivatives removes this finite-place denominator but restores the same factorial
in the archimedean entries.  The tautological factor itself is an exact saturation example:

`B(t)^s=sum_(j=0)^s (-1)^(s-j)*binom(s,j)*exp(t*((s-j)*w_0+j*w_1))`,
`ord_1 B^s=s`,
`H(B^s)=binom(s,floor(s/2))=2^(s+o(s))`,
`(B^s)^((s))(1)/s!=(y_0*omega)^s`.                                 `(AJ25)`

Thus each automatic order costs one new frequency and asymptotic coefficient height `log 2`; its
first nonzero normalized jet is not small or discrete in a favorable direction.

For the arity-two stress

`(w_0,w_1)=(1+omega,1+2*omega)`, `(y_0,y_1)=(e,e)`,                 `(AJ26)`

the desired conclusion is algebraic independence of `e` and `pi`.  The exact quotient counts
become

`N_full=(R+1)^4`, `N_quot=(R+1)^2*(2R+1)=Theta(R^3)`,
`U=O((R+T)*T^2)`, `T=O(R)`,
`Z=2*R^2+4*R`.                                                     `(AJ27)`

If all `N_full=Theta(R^4)` coefficients are retained, the honest terminal range is instead
`T=O(R^(4/3))` (or `O(R^(3/2))` under the deliberately frozen, too-favorable numerator).  Both
remain far below `Z`.

Here `(AJ10)` has `B'(1)=e*omega`, and `(AJ25)` gives the first normalized nonzero jet
`(e*omega)^s`.  The missing factor between the constructible order and the zero threshold is
exactly `R`; neither the duplicate value nor its integer binomial creates the missing unit.

Finally compare a Q-linearly independent algebraic-input pair `(alpha_0,alpha_1)`.  Its toric
values in the same box are all distinct: equality would make a nonzero algebraic linear form in
the `alpha_i` an integral multiple of the transcendental period.  Lindemann--Weierstrass makes
the two exponential values algebraically independent, so `d=2`.  The unquotiented count is

`N=Theta(R^4)`, `U=O(R^2*T^2)`, hence again `T=O(R)` against the same
`2R^2+4R` threshold.                                                `(AJ28)`

Thus, after quotienting, the AP1 collision lowers the coefficient exponent from four to three at
exactly the same time that the hypothetical field dimension falls from two to one.  Those changes
cancel.  The full `B`-adic space recovers a small `R^(1/3)` gain in arity two, but the known
binomial still does not free a decisive coefficient.  At the required `T~R^2`, the honest full
row bound is `O(R^(4n-2))` against only `Theta(R^(2n))` unknowns, a missing factor
`R^(2n-2)`; the quotient version is worse by one more power.  Neither the value collision nor the
factorial height in `(AJ23)--(AJ25)` supplies that factor, and treating the frequencies in
`(AJ13)` as equal would be the precise invalid step.

### Integer radial zeros factor through the known period binomial

The adjacent-period form also permits an exact audit of Carlson-, Skolem--Mahler--Lech-, and
integer-interpolation ideas.  Put `omega=2*pi*I`, `q(t)=exp(omega*t)`, and consider a finite
exponential polynomial written after grouping frequencies modulo `Z*omega`:

`F(t)=sum_(j=1)^r exp(mu_j*t)*Q_j(t,q(t))`,                         `(IZ1)`

where `Q_j in C[T,Q,Q^(-1)]` and the nonzero numbers

`a_j=exp(mu_j)`                                                     `(IZ2)`

are pairwise distinct.  Such a presentation exists for every radial pullback
`P(t*w,exp(t*w))` from an adjacent-period family: two frequencies have the same value at
`t=1` exactly when their difference lies in `Z*omega`, by `(AJ2)--(AJ3)`.

At every integer `k`, `q(k)=1`, so

`F(k)=sum_j a_j^k Q_j(k,1)`.                                      `(IZ3)`

The sequences `k^s*a_j^k`, for distinct `a_j` and the finitely many powers occurring in
`Q_j(T,1)`, are linearly independent.  One elementary proof applies the shift operators
`(S-a_j)` successively: `(S-a_j)` lowers the polynomial degree of `p(k)*a_j^k`, while it is
invertible on the generalized eigenspaces belonging to every `a_l!=a_j`.  Equivalently, any
sufficiently long initial block is a confluent Vandermonde system.  Hence

`F(k)=0 for every k>=0  implies  Q_j(T,1)=0 for every j`.            `(IZ4)`

In the Laurent polynomial ring, `Q_j(T,1)=0` is exactly divisibility by `Q-1`.  Substituting
`Q=q(t)` gives the sharp factorization

`F(k)=0 for every k>=0  implies`
`F(t)=(exp(omega*t)-1)*G(t)`                                       `(IZ5)`

inside the same exponential-polynomial ring.  The converse is immediate.  Since

`d/dt (exp(omega*t)-1)|_(t=k)=omega!=0`,                            `(IZ6)`

iteration also proves that zeros of multiplicity at least `s` at every nonnegative integer are
equivalent to divisibility by `(exp(omega*t)-1)^s`, after removing any identically zero grouped
summands.  Thus an infinite integer zero set does not reveal a new common factor: it recovers
exactly the radial form of `Y_1-Y_0` already counted in `(AJ10)--(AJ11)`.

There is a finite version with no asymptotic ambiguity.  If

`deg_T Q_j(T,1)<=A_j`,

then the recurrence in `(IZ3)` has total confluent order

`M=sum_j (A_j+1)`.                                                  `(IZ7)`

Any `M` consecutive zero values force every `Q_j(T,1)` to vanish and hence force the factor in
`(IZ5)`.  With fewer than `M` samples, the confluent Vandermonde system has a nonzero kernel, so
the threshold is sharp.  Increasing the number of forced integer zeros therefore increases the
polynomial-prefactor/frequency budget at the same rate; Carlson rescaling cannot turn the one
selected zero into an infinite set for free.

For the arity-two boundary

`w=(1+omega,1+2*omega)`, `exp(w)=(e,e)`,                            `(IZ8)`

a hypothetical relation `P(omega,e)=0` pulls back simply to

`H(t)=P(t*omega,exp(t))`, `H(1)=0`.                                `(IZ9)`

There is no reason for `H(k)=P(k*omega,e^k)` to vanish at any other integer.  Multiplying by
`exp(omega*t)-1` creates all integer zeros, but is the tautological period factor `(IZ5)`;
multiplying shifted copies `product_(j=1)^N H(t-j+1)` creates `N` selected zeros only by spending
`N` times the degree, frequency count, and logarithmic height.  The same conclusion holds for a
general defect relation: its radial pullback vanishes at `t=1`, whereas the period supplies an
infinite lattice only to the already-known binomial ideal.

This closes the integer-sampling route exactly.  Skolem--Mahler--Lech identifies possible
arithmetic progressions of zeros, Carlson-type uniqueness bounds the same finite exponential
type, and the direct recurrence proof `(IZ3)--(IZ7)` shows in this setting that both mechanisms
return the forced factor `exp(omega*t)-1`.  A new proof would have to propagate the isolated
arithmetic zero `(IZ9)` without multiplying by that factor or increasing complexity; neither
the period relation nor defect-one field dimension supplies such propagation.

### Confluent collision blocks retain a common defect-field mode

The radial Wronskian makes the warning in `(AJ14)` exact.  Fix the indices
`b_2,...,b_(n-1)` and a collision sum `s=b_0+b_1`.  Write

`j_-=max(0,s-E)`, `j_+=min(E,s)`, `m=m_s=j_+-j_-+1`,
`lambda_j=s*w_0+j*omega+sum_(r>=2)b_r*w_r`,
`eta=exp(lambda_j)=y_0^s*product_(r>=2)y_r^(b_r)`.                  `(WK1)`

Thus the class size is the exact triangular sequence

`m_s=s+1` for `0<=s<=E`, and `m_s=2E-s+1` for `E<=s<=2E`.          `(WK2)`

Let `A` be the polynomial-prefactor degree on the radial line, put `q=A+1` and `M=q*m`, and use
the local basis

`f_(j,k)(t)=(t-1)^k*exp(lambda_j*t)`,
`j_-<=j<=j_+`, `0<=k<q`.                                          `(WK3)`

(For the original additive box one may take `A=nD`; the many `X`-monomials with the same total
degree have already collapsed to scalar multiples of the same radial function.)  The ordinary
derivative matrix in rows `0<=r<M` has the exact confluent-Vandermonde determinant

`W_C(1)=det(f_(j,k)^((r))(1))`
` = +/- eta^M*C_q^m*omega^(q^2*binom(m,2))*C_m^(q^2)`,             `(WK4)`

where

`C_v=product_(h=0)^(v-1) h!`.                                     `(WK5)`

Indeed the standard confluent determinant contributes `C_q^m` and raises every pairwise
difference to the power `q^2`, while

`product_(p<r)(lambda_r-lambda_p)`
` =omega^binom(m,2)*product_(h=1)^(m-1)h!`.                        `(WK6)`

In particular `(WK4)` is nonzero, gives the sharp class bound `ord_1<M`, and contains the exact
period exponent

`L_C=q^2*binom(m,2)`.                                              `(WK7)`

If both columns and derivative rows are divided by their natural factorials, the normalized jet
determinant is

`W_C^div(1)=+/- eta^M*omega^L_C*C_m^(q^2)/C_M`.                    `(WK8)`

Thus its rational denominator divides `C_M`; no period power is an arithmetic denominator.  The
factorial sizes are also explicit:

`log C_v=(1/2)*v^2*log v-(3/4)*v^2+O(v*log v)`,                    `(WK9)`

so the ordinary determinant has integer-factor logarithm

`m*log C_q+q^2*log C_m`
` =(1/2)*m*q^2*log q+(1/2)*q^2*m^2*log m+O(m*q^2+q^2*m*log m)`,    `(WK10)`

whereas normalized rows pay `log C_M=Theta(q^2*m^2*log(q*m))`.  When `q,m=Theta(R)`, the period
exponent is `Theta(R^4)` and the factorial height/denominator loss is `Theta(R^4 log R)`.

Dividing `(WK4)` by the displayed integer and by `omega^L_C` does **not** produce an algebraic
nonzero number in general; it produces exactly

`W_C(1)/(+/- C_q^m*C_m^(q^2)*omega^L_C)=eta^M in K`.               `(WK11)`

This is the immovable common-frequency mode.  The same determinant at zero is

`W_C(0)=+/- C_q^m*C_m^(q^2)*omega^L_C`,
`W_C(1)/W_C(0)=eta^M`.                                             `(WK12)`

Hence a stable two-endpoint normalization cancels all relative period modes and leaves precisely
the exponential value whose arithmetic is missing.  Gauging by `exp(-lambda_(j_-)*t)` makes the
remaining frequencies integer multiples of `omega`, but its value at `t=1` is `eta^(-1)`; it
merely moves the defect-field factor from the Wronskian into the endpoint normalization.  Neither
a number-field product formula nor the stable Hermite endpoint applies to `(WK11)` unless one
already controls `eta` over the period field.  Dividing by `eta^M` as well makes the answer a
rational factorial, but uses a transcendental coefficient from `K` and destroys the integral
coefficient lattice.

The aggregate block calculation is equally exact.  In the nonnegative toric box,

`sum_(s=0)^(2E) binom(m_s,2)=E*(E+1)*(2E+1)/6`.                    `(WK13)`

For every choice of the other `n-2` toric indices, the product of all collision-block
determinants therefore contains

`omega^(q^2*(E+1)^(n-2)*E*(E+1)*(2E+1)/6)`                        `(WK14)`

and the value factor

`product_(b in [0,E]^n)(y^b)^q`
` =product_i y_i^(q*E*(E+1)^n/2)`,                                `(WK15)`

with the `i=0,1` exponents combined using `y_1=y_0`.  Centering the indices in a Laurent box makes
the total exponent in `(WK15)` zero, but clearing the negative powers restores the same endpoint
monomial.  Even before that clearing, `(WK14)` is a power of the transcendental period, not a
nonzero algebraic integer.  The apparent product-formula determinant is therefore either a
tautological rational factorial after division by elements of `K`, or an element of the same
defect field as the original tuple.

For the arity-two stress `(w_0,w_1)=(1+omega,1+2*omega)`, one has

`lambda_j=s+(s+j)*omega`, `eta=e^s`,                               `(WK16)`

and hence

`W_s(1)=+/- e^(s*q*m_s)*C_q^(m_s)*omega^(q^2*binom(m_s,2))*C_(m_s)^(q^2)`. `(WK17)`

After removing every integer and period factor, the residue is `e^(s*q*m_s)`.  The only class
with residue `1` is `s=0`, but in the nonnegative box it has `m_0=1` and no collision.  Across all
classes the exact exponents are

`e^(q*E*(E+1)^2)` and `omega^(q^2*E*(E+1)*(2E+1)/6)`.              `(WK18)`

Thus the desired algebraic independence of `e` and `pi` is not reduced to a rational determinant:
it is sitting unchanged in the two monomial factors of `(WK18)`.

The algebraic-input equality case shows the complementary arithmetic advantage.  For
Q-linearly independent algebraic `alpha_i`, all toric frequencies are distinct and every
collision class has `m=1`; the frequency differences are nonzero algebraic numbers.  A centered
full Wronskian can cancel its total exponential factor and leave an algebraic Vandermonde.  In
the adjacent-period case the within-class differences instead supply the transcendental
`omega^L_C`, and removing them leaves `eta^M`.  This is exactly the missing algebraic-input
hypothesis, not a new determinant margin.

Finally, the collision-block data admit an exact discontinuous-character counterfeit.  Let
`tau` be transcendental, set

`omega=tau`, `w_0=tau^2`, `w_1=tau^2+tau`, `u=tau`.                `(WK19)`

Choose a Q-linear map `ell:C->C` with `ell(w_0)=L`, `exp(L)=u`, and `ell(omega)=0`, and put
`E=exp o ell`.  Then `E(w_0)=E(w_1)=u`, the two inputs are Q-linearly independent, every displayed
input and value is transcendental, and

`td_Q Q(w_0,w_1,E(w_0),E(w_1))=1`.                                `(WK20)`

For every integral frequency `lambda=b dot w`, the entire germ

`g_b(t)=E(lambda)*exp((t-1)*lambda)`                               `(WK21)`

is multiplicative in `b` and has exactly the point values, frequencies, collision classes, jets,
and Wronskians `(WK1)--(WK15)` (with `u` in place of the common value).  It is not the global path
`t |-> E(t*lambda)`: at the other
endpoint `g_b(0)=E(lambda)*exp(-lambda)`.  Consequently a genuinely global Hermite argument can
distinguish the analytic exponential only through that second endpoint, but the complementary
factor there restores exactly what `(WK11)--(WK12)` lost.  Any proposed proof using just the
collision Wronskians, period normalization, and multiplicativity is therefore refuted by
`(WK19)--(WK21)`; a successful refinement would need a new arithmetic lower bound coupling both
endpoints over the positive-transcendence-degree field `K`.

### The two-endpoint Hermite identity escapes into `Z[omega]`

There is a concrete two-endpoint version of `(WK11)`, using exactly the canonical Hermite tail
formalized in `CanonicalHermiteApproximation.lean`.  For one collision block let

`f_C(X)=product_(j=j_-)^(j_+) (X-lambda_j) in A[X]`,
`A=Z[lambda_(j_-),omega] subset K`,                                `(HE1)`

and take an integer `p>=1`.  Put

`H_p(X)=X^(p-1)*f_C(X)^p`, `L=p*(m+1)-1`,
`G_p(X)=(1/p!)*sum_(k=p)^L H_p^((k))(X)`,
`N_p=f_C(0)^p+p*G_p(0)`.                                           `(HE2)`

The factorial division in `(HE2)` is coefficientwise integral over `A`: the `k`-th derivative is
divisible by `k!`, hence by `p!` for `k>=p`.  The same boundary calculation as in the formalized
canonical tail gives

`sum_(k=0)^L H_p^((k))(0)=(p-1)!*N_p`,
`sum_(k=0)^L H_p^((k))(lambda_j)=p!*G_p(lambda_j)`.                 `(HE3)`

Integration of the derivative of `exp(-z)*sum_k H_p^((k))(z)` gives the exact endpoint error

`epsilon_(p,j)=N_p*exp(lambda_j)-p*G_p(lambda_j)`,
`(p-1)!*epsilon_(p,j)`
` =exp(lambda_j)*lambda_j*integral_0^1 exp(-x*lambda_j)*H_p(x*lambda_j) dx`. `(HE4)`

Thus all factorials are the same as in the canonical theorem, but its arithmetic conclusion is
not: here `N_p,G_p` lie in `A`, not in `Z`.  The formal congruence

`N_p = f_C(0)^p (mod p*A)`                                        `(HE5)`

does not make `N_p` a nonzero integer after evaluation.

Since every endpoint value in the block is `eta`, eliminating the common endpoint gives the
literal two-row Hermite determinant

`det [[N_p,p*G_p(lambda_j)],[N_p,p*G_p(lambda_k)]]`
` =N_p*p*(G_p(lambda_k)-G_p(lambda_j))`
` =N_p*(epsilon_(p,j)-epsilon_(p,k))`.                             `(HE6)`

The polynomial difference is divisible by
`lambda_k-lambda_j=(k-j)*omega`.  After removing that known period factor, `(HE6)` remains an
element of `A`; it is not rational or algebraic over `Q`.  Conversely, retaining the common
endpoint instead of taking `(HE6)` retains the factor `eta`.  The two choices are exhaustive:
the determinant either forgets the target exponential value and lands in the period/frequency
ring, or keeps it and stays in the defect field.

The relative-period form gives an exact saturation, not just a lack of a lower-bound theorem.
Translate the class so that its relative nodes are `1,...,m` and set

`F_m(Z)=product_(r=1)^m (Z-r) in Z[Z]`,
`H_(p,m)(Z)=Z^(p-1)*F_m(Z)^p`, `L=p*(m+1)-1`.                      `(HE7)`

For the differential equation with parameter `omega`, define

`S_omega H(Z)=sum_(k=0)^L omega^(L-k)*H^((k))(Z)`.                 `(HE8)`

It satisfies the exact integral identity

`(exp(-omega*Z)*S_omega H(Z))'=-omega^(L+1)*exp(-omega*Z)*H(Z)`.   `(HE9)`

At `0` and a root `r in {1,...,m}`, write

`S_omega H_(p,m)(0)=(p-1)!*N_(p,m)(omega)`,
`S_omega H_(p,m)(r)=p!*G_(p,m,r)(omega)`,                          `(HE10)`

where `G_(p,m,r) in Z[omega]` and

`N_(p,m)(W)=W^(p*m)*((-1)^m*m!)^p+p*G_(p,m,0)(W) in Z[W]`.         `(HE11)`

Here the power `W^(pm)` is exact because the boundary derivative has order `p-1` and
`L-(p-1)=pm`.  Integrating `(HE9)` from `0` to `r` gives

`(p-1)!*(N_(p,m)(omega)*exp(omega*r)-p*G_(p,m,r)(omega))`
` =omega^(p*(m+1))*exp(omega*r)*r`
`   *integral_0^1 exp(-omega*r*x)*H_(p,m)(r*x) dx`.                `(HE12)`

For the true period `exp(omega)=1`, define

`Q_(p,m,r)(W)=N_(p,m)(W)-p*G_(p,m,r)(W) in Z[W]`.                 `(HE13)`

If `p` is prime and `p>m`, then

`Q_(p,m,r)(W) = W^(pm)*((-1)^m*m!)^p (mod p*Z[W])`,               `(HE14)`

so it is a nonzero polynomial of degree at most `pm`; since `omega` is transcendental,
`Q_(p,m,r)(omega)!=0`.  Nevertheless `(HE12)` supplies the explicit small-value bound (using
`|exp(-omega*r*x)|=1` for `omega=2*pi*i`)

`0<|Q_(p,m,r)(omega)|`
` <= |omega|^(p*(m+1))*r^p*C_m^p/(p-1)!`,
`C_m=max_(0<=u<=m)|F_m(u)|`.                                      `(HE15)`

For every fixed `m,r` the right side tends to zero factorially.  Thus the actual Hermite endpoint
manufactures nonzero, arbitrarily small elements of `Z[omega]`; replacing `Z` by `Z[omega]` has
destroyed precisely the discreteness used in Hermite--Lindemann.

The coefficient loss is equally explicit.  Since
`||F_m||_1<=product_(r=1)^m(1+r)=(m+1)!`, a crude derivative bound gives

`H(Q_(p,m,r))`
` <=2*(L+1)*L!*max(1,m)^L*((m+1)!)^p`,                             `(HE16)`

and hence

`log H(Q_(p,m,r))=O(p*m*log(p*m)+p*m*log m)`.                      `(HE17)`

The factorial upper bound `(HE15)` and this growing degree/height are therefore an exact
Hermite-type transcendence approximation to the already-transcendental period, not an
algebraic-independence estimate involving `eta`.  Multiplying the relative identity by `eta`
only multiplies **both** endpoints by `eta`; it supplies no integral approximation to that common
mode.

In the stress `(w_0,w_1)=(1+omega,1+2*omega)`, the direct block has

`lambda_j=s+(s+j)*omega`, `eta=e^s`,
`f_C(0)=(-1)^m*product_j (s+(s+j)*omega) in Z[omega]`.              `(HE18)`

Consequently `(HE4)` is exactly

`N_p(omega)*e^s-p*G_p(s+(s+j)*omega)=epsilon_(p,j)`,               `(HE19)`

with `(p-1)!*epsilon_(p,j)` equal to the displayed integral.  Subtraction as in `(HE6)` removes
`e^s` and produces a small element divisible by `(j-k)*omega` in `Z[omega]`; keeping one equation
leaves `e^s` over `Q(omega)`.  This is the dichotomy `period approximation versus the original
AI(e,pi) target` in an exact formula.

Galois symmetrization does not close it.  Suppose hypothetically that a primitive
`P(E,W) in Z[E,W]`, of degree `delta` in `E` and leading coefficient `a_delta(W)`, satisfies
`P(e,omega)=0`.  For `A_p(W)=N_p(W)` and
`B_(p,j)(W)=p*G_p(s+(s+j)*W)`, the only available finite norm is over `Q(omega)`:

`Res_E(P(E,W),A_p(W)*E^s-B_(p,j)(W)) at W=omega`
` =a_delta(omega)^s*product_(sigma=1)^delta`
`   (A_p(omega)*e_sigma^s-B_(p,j)(omega))`.                        `(HE20)`

If this resultant is nonzero, clearing its rational denominators gives a nonzero element of
`Z[omega]`, not of `Z`; `(HE15)` shows exactly why such an element can be factorially small.  If
it is zero, the proposed discrete nonzero quantity has disappeared because the two polynomials
share a root.  Moreover only the distinguished factor `e_1=e` in `(HE20)` obeys the analytic
remainder estimate; the other algebraic conjugates over `Q(omega)` are not selected exponential
values.

The same obstruction is visible directly in the Wronskian residue:

`product_sigma (e_sigma^s)^M`
` =((-1)^delta*P(0,omega)/a_delta(omega))^(s*M)`.                   `(HE21)`

It is a rational function of the transcendental period.  There is no further finite norm from
`Q(omega)` to `Q`, and absolute `Aut(C/Q)` moves `omega` through an infinite orbit while not
preserving the analytic endpoint estimate.  A resultant in `E` can eliminate `e`; eliminating
`W` would require a polynomial equation for the transcendental period.

For algebraic inputs the base polynomial `f` lies in `Z[X]`, so the canonical construction has
`N_p in Z`, `G_p in Z[X]`, and `N_p=f(0)^p (mod p)`; after the finite algebraic conjugates are
included, denominator clearing and the field norm produce an actual nonzero integer.  The
factorial remainder can then contradict `1<=|D|`.  In `(HE20)` the identical operation terminates
one level earlier at `Z[omega]`, where `(HE13)--(HE15)` exhibit exact saturation.  Therefore the
two-endpoint Hermite determinant, period powers, Galois products, and resultants do not produce
the missing discrete quantity; a new lower bound over the transcendental base `Q(omega)` would
have to be strong enough to rule out the explicit canonical sequence `(HE13)` itself, and hence
cannot follow from the existing stable endpoint.

### Quantitative measures are one full degree factor too weak for the Hermite escape

The height estimate `(HE16)` can be sharpened enough to make a direct comparison with known
transcendence measures.  Retain `(HE7)--(HE13)`, put

`L=p*(m+1)-1`, `D=p*m`, `r_+=max(1,r)`,
`B_m=||F_m||_1<=product_(k=1)^m(1+k)=(m+1)!`.                     `(QM1)`

Writing `H_(p,m)=sum_(ell=0)^L a_ell Z^ell`, one has

`|H_(p,m)^((k))(r)|`
` <= k!*binom(L,k)*r_+^L*||H_(p,m)||_1`
` <= L!*r_+^L*B_m^p`.                                             `(QM2)`

Since each coefficient of `G_(p,m,r)(W)` is one such derivative divided by `p!`, `(HE11)` and
`(HE13)` give the explicit naive-height bound

`H(Q_(p,m,r))`
` <=(m!)^p+2*p*(L!/p!)*r_+^L*((m+1)!)^p`.                          `(QM3)`

In particular, uniformly for `1<=r<=m`,

`h_Q=log H(Q_(p,m,r))`
` <=log(3p)+log(L!/p!)+L*log m+p*log((m+1)!)`
` =p*m*log p+O(p*m*log(m+1))`.                                    `(QM4)`

The analytic constant in `(HE15)` satisfies the elementary two-sided bound

`m!<=C_m=max_(0<=u<=m)|product_(k=1)^m(u-k)|<=m^m`:               `(QM5)`

the lower bound is the value at `u=0`, and every factor is at most `m` on the interval.  Hence

`log|Q_(p,m,r)(omega)|<=-A_(p,m,r)`,
`A_(p,m,r)=log((p-1)!)-p*((m+1)*log|omega|+log r+log C_m)`.         `(QM6)`

The upper bound is useful only if `log p` exceeds `m*log m+O(m)`; in every case

`A_(p,m,r)<=p*log p<=D*log D`.                                    `(QM7)`

Thus allowing `m` to grow cannot improve the available exponent.  It increases `D` and the
height while `(QM5)` consumes `p*m*log m` of the factorial saving.  The asymptotically best regime
for this comparison is bounded `m`, not a growing collision block.

The applicable uniform primary-source measure is Corollary 3.2 of M. Waldschmidt,
[*Transcendence measures for exponentials and logarithms*, J. Austral. Math. Soc. A 25 (1978),
445--465](https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/JAustralMS25-1978-445-465.pdf):
for a nonzero `P in Z[X]` of degree at most `N>2` and height at most `H>16`,

`log|P(pi)|>-240*N*(log H+N*log N)*(1+log N)`.                     `(QM8)`

This is the strongest verified form used here that is uniform while both degree and height grow;
fixed-degree constants are not uniform enough for `D=pm -> infinity`.

To apply `(QM8)` to `Q(omega)` with `omega=2*pi*i`, write

`Q(2*i*X)=Q_even(X)+i*Q_odd(X)`,                                  `(QM9)`

where `Q_even,Q_odd in Z[X]`, at least one is nonzero, both have degree at most `D`, and height at
most

`H_pi=2^D*H(Q)`.                                                   `(QM10)`

Since `|Q(omega)|` is at least the modulus of either component, `(QM8)` yields

`log|Q(omega)|`
` >-Phi_pi(D,H_pi)`,
`Phi_pi=240*D*(log H_pi+D*log D)*(1+log D)`.                       `(QM11)`

For a contradiction, `(QM6)` would require `A_(p,m,r)>Phi_pi`.  But independently of `(QM3)`,

`Phi_pi>=240*D^2*log D*(1+log D)`,
`A_(p,m,r)/Phi_pi<=1/(240*D*(1+log D)) ->0`.                       `(QM12)`

This rules out every optimization in `p,m,r`; the known lower bound is one full factor `D log D`
smaller than what the endpoint would need.  Constants and the actual height `(QM3)` only worsen
the comparison.

The smallest cases show that this is not an artifact of a large collision block.  For `m=r=1`,

`C_1=1`, `D=p`,
`|Q_(p,1,1)(omega)|<=|omega|^(2p)/(p-1)!`,
`H(Q_(p,1,1))<=1+2*p*((2p-1)!/p!)*2^p`,                           `(QM13)`

and the ratio in `(QM12)` is at most `1/(240*p*(1+log p))`.  For the first nontrivial class
`m=2`, one has `C_2=2`, `D=2p`, and, for `r=1`,

`|Q_(p,2,1)(omega)|<=(2*|omega|^3)^p/(p-1)!`,                     `(QM14)`

while the ratio is at most `1/(480*p*(1+log(2p)))`.  Degree-one irrationality measures for `pi`
do not apply: the Hermite sequence has degree `p` even in `(QM13)`.

Adding the hypothetical relation `P(e,omega)=0` compounds rather than repairs the loss.  Let the
fixed primitive polynomial `P(E,W) in Z[E,W]` have bidegrees

`deg_E P=a`, `deg_W P=b`, and height `H_P`,                        `(QM15)`

and form the other resultant, now eliminating the period,

`R_p(E)=Res_W(P(E,W),Q_(p,m,r)(W)) in Z[E]`.                       `(QM16)`

If it is nonzero, the Sylvester determinant gives the concrete bounds

`deg R_p<=a*D`,
`log H(R_p)<=log((b+D)!)+D*log((a+1)*H_P)+b*h_Q`.                  `(QM17)`

Indeed every determinant term contains `D` coefficient polynomials of `P`, each of `ell^1`
norm at most `(a+1)H_P`, and `b` coefficients of `Q`.  At `E=e`, if
`P(e,W)=c(e)*product_(nu=1)^b(W-omega_nu)` with `omega_1=omega`, then

`R_p(e)=c(e)^D*product_(nu=1)^b Q_(p,m,r)(omega_nu)`.              `(QM18)`

Only the `nu=1` factor has `(QM6)`.  For every other fixed conjugate,

`log|Q(omega_nu)|<=h_Q+log(D+1)+D*log max(1,|omega_nu|)`,          `(QM19)`

so the resultant is not even forced to be small when `b>=2`: the possible gain `A<=D log D` is
offset by `(b-1)h_Q+O_P(D)`, already of order `D log D`.  If `(QM16)` vanishes, there is no
nonzero quantity to estimate.

Even granting the most favorable case `b=1` and discarding every conjugate-growth loss does not
help.  The strongest recent height exponent for `e` comes from Theorem 1 and the explicit
Proposition 1 of S. Fischler and T. Rivoal,
[*A new transcendence measure for the values of the exponential function at algebraic
arguments* (2025)](https://rivoal.perso.math.cnrs.fr/articles/mesureexp.pdf).  For `alpha=1`
and a **fixed** polynomial degree `delta`, their exponent is the optimal Dirichlet exponent
`mu(1,delta)=delta`:

`|S(e)|>c(epsilon,delta)*H(S)^(-delta-epsilon)`.                    `(QM20)`

Their Proposition 1 makes the constant explicit when `delta` grows, but does not remove its
degree dependence.  In our resultant `delta<=aD` and `(QM17)` gives
`log H(R_p)=O_P(D log D)`.  Even the unrealistically favorable uniform version with constant one
would cost

`delta*log H(R_p)=O_P(D^2*log D)`,                                `(QM21)`

against at most `A=O(D log D)` from the distinguished endpoint.  The limiting favorable ratio is
`O_P(1/D)`.  The actual explicit constant in Proposition 1 is additional loss: with its accessory
parameter chosen minimally (`p_FR=delta` when `d=1`), its definitions include

`q=lcm(1,...,delta)`,
`a_FR=(delta+1)!*exp(delta*(delta+1)/2)*(2q)^(delta^2)`,
`b_FR=(2q)^(delta*(delta+1))`,                                    `(QM22)`

inside the lower-bound constant.  Hence it is emphatically not uniform in the growing degree
needed by `(QM16)`.

Eliminating `e` first, as in `(HE20)`, ends at `Z[omega]` and is blocked by `(QM12)`; eliminating
`omega` first ends at `Z[e]` and loses the extra resultant degree in `(QM21)`.  Applying both
measures successively therefore multiplies the bad degree/height factors rather than canceling
them.  In the algebraic-input equality case no transcendence measure of growing degree is needed:
the canonical conjugate product is a nonzero integer and uses `1<=|D|`.  Here the replacement of
that integer by either a degree-`D` polynomial in `pi` or a degree-`O(D)` polynomial in `e` is
exactly the missing unit.  Existing quantitative measures cannot restore it.

### Rational scalar descent has a maximal Hopf envelope but no generic point

Let `z=(z_1,...,z_n)` be Q-linearly independent, put `y=exp(z)`,
`K=Q(z,y)`, and consider the genuine rational scalar orbit in
`G=Ga^n times Gm^n`:

`S={p_q=(q*z,exp(q*z)):q in Q}`.                                  `(SD1)`

Every point has coordinates algebraic over the original field.  If `q=a/m` with `m>0`, then

`(exp(q*z_i))^m=y_i^a`,                                           `(SD2)`

so `K(p_q)/K` is finite of degree at most `m^n`.  Consequently the field

`L=K(p_q:q in Q)`                                                  `(SD3)`

is algebraic over `K` and `td_Q L=td_Q K`.

The ordinary Q-Zariski closure must first be distinguished from a group closure.  Let

`C_z=Closure_Q({q*z:q in Q}) subset Ga^n`.                         `(SD4)`

This is the affine cone cut out by all rational homogeneous polynomials `R` with `R(z)=0`.  If

`rho=td_Q Q(z_2/z_1,...,z_n/z_1)`                                 `(SD5)`

(after choosing any nonzero coordinate as denominator), then `dim C_z=rho+1`.  A direct
exponential-polynomial calculation gives the exact mixed closure

`Closure_Q(S)=C_z times Gm^n`,
`dim Closure_Q(S)=n+rho+1`.                                       `(SD6)`

Indeed, for a Laurent polynomial `P=sum_b P_b(X)Y^b in Q[X,Y^(+-1)]` vanishing on `S`,

`F(t)=sum_b P_b(t*z)*exp(t*(b dot z))`                             `(SD7)`

vanishes for all rational `t`, hence identically by holomorphy.  The frequencies `b dot z` are
pairwise distinct by Q-linear independence, so confluent-Vandermonde independence gives
`P_b(t*z)=0` for every `b` and every `t`.  This is exactly the extended ideal of `C_z`.

In particular the Q-vanishing ideal need **not** be a Hopf ideal, even though `S` is a subgroup
of `G(C)`.  Rational Zariski closure does not commute with products of dense subsets when the
points are not Q-rational.  For example, with `z=(T,sqrt(2)*T)` and transcendental `T`, the
additive cone is

`C_z: X_2^2-2*X_1^2=0`,                                           `(SD8)`

the union over `C` of two conjugate lines; adding a point from each line leaves this cone.  Over
`C` the closure of the original subgroup is only

`Closure_C(S)=(C*z) times Gm^n`, of dimension `n+1`.               `(SD9)`

What is maximal is the **Hopf envelope**, namely the smallest Q-algebraic subgroup containing
`S`.  Its additive projection is all `Ga^n`, since a proper Q-linear subspace would give a
rational linear relation on `z`.  Its toric projection is all `Gm^n`: a character
`a in Z^n` trivial on every rational division point would satisfy

`exp(q*(a dot z))=1 for every q in Q`;                             `(SD10)`

taking `q=1/m` for every `m` gives `a dot z in intersection_m m*omega*Z={0}` and hence `a=0`.
Finally, connected subgroups of a vector group times a torus split, because algebraic Goursat
would otherwise give a nontrivial group both unipotent and of multiplicative type.  Therefore

`HopfEnvelope_Q(S)=Ga^n times Gm^n`.                              `(SD11)`

If `a dot z=omega`, the integer orbit has `Y^a=1`, but rational divisions have
`Y^a=exp(omega/m)` of unbounded torsion order; even this character disappears from the Hopf
envelope.  Passing from `(SD6)` to `(SD11)` amounts to adding and multiplying independent
Q-conjugate components.  Those new points are not analytic graph points.

Neither `(SD6)` nor `(SD11)` is bounded by `td_Q L`: Zariski dimension is the transcendence
degree of a **generic point** of the closure, and `(SD3)` contains no such generic point.  It
contains only an infinite collection of nongeneric points whose individual Q-loci move.

The false descent principle has an unconditional exact counterfeit at the target defect.  Let
`T_1,...,T_(n-1)` be algebraically independent complex numbers and set, for `n>=2`,

`z_i=T_1^i  (1<=i<=n)`,
`y_i=T_i  (1<=i<n)`,
`y_n=1+product_(i=1)^(n-1)T_i`.                                  `(SD12)`

The `z_i` are Q-linearly independent.  The `y_i` are multiplicatively independent: valuations
at the distinct prime divisors `T_i` and `1+product T_i` kill every integral relation.  Choose
coherent rational powers of each `y_i` and define on `span_Q(z)`

`E(sum_i q_i*z_i)=product_i y_i^(q_i)`;                           `(SD13)`

extend this homomorphism to `(C,+)` using divisibility of `C^*`.  It is necessarily discontinuous.
Then

`Q(z,E(z))=Q(T_1,...,T_(n-1))`, `td_Q=n-1`,                       `(SD14)`

every input and value displayed in `(SD12)` is transcendental and every rational scalar point is
algebraic over this same field.  Here `rho=1`, so the ordinary scalar closure `(SD6)` has dimension
`n+2`, while its Hopf envelope `(SD11)` has dimension `2n`.  For `n=2` this is simply

`z=(T,T^2)`, `E(z)=(T,1+T)`, `td_Q Q(z,E(z))=1`,                  `(SD15)`

while the scalar orbit is Q-Zariski dense in `Ga^2 times Gm^2`.  Thus even the exact positive
fully-transcendental defect-one field data do not imply the proposed closure-dimension bound.

Adding conjugates does not restore a graph-generic point.  Kummer conjugates over `K` replace a
selected `m`-th root in `(SD2)` by root-of-unity twists.  Except for the distinguished twist,

`sigma(exp(z_i/m))!=exp(sigma(z_i/m))=exp(z_i/m)`,                `(SD16)`

so these are toric conjugates, not further analytic graph points.  They can only accelerate the
toric density already present in `(SD6)`.  Absolute conjugates over `Q` do make the union of pure
field loci dense in the Q-locus, but in general

`sigma(exp(q*z_i))!=exp(q*sigma(z_i))`;                           `(SD17)`

moreover the compositum of the fields `sigma(K)` is not algebraic over one fixed defect field and
can have unbounded transcendence degree.  Independent conjugates therefore force either the
wrong points or the loss of the field bound.

Function-field heights reproduce the same escape exactly.  In the counterfeit `(SD12)`, over
`K(mu_m)` choose `u_i^m=y_i`.  The prime-divisor independence gives the full Kummer degree

`[K(mu_m,u_1,...,u_n):K(mu_m)]=m^n`.                              `(SD18)`

Normalized heights and norms are

`h(u_i)=h(y_i)/m`,
`Norm_(K(mu_m,u)/K(mu_m))(u_i-1)=+/-(y_i-1)^(m^(n-1))`.           `(SD19)`

Equivalently, at every unramified complex place,

`sum_(zeta_1,...,zeta_n in mu_m) log|zeta_i*u_i-1|`
` =m^(n-1)*log|y_i-1|`.                                           `(SD20)`

The selected division branch has small height, but its algebraic degree grows as `m^n` and all
other branches restore the original norm.  Northcott cannot be applied with unbounded degree.
For additive coordinates, an arithmetic height also pays the denominator of `q=a/m`; a purely
geometric function-field height treats `q` as a constant but then has no archimedean place capable
of selecting the analytic branch.

This is not peculiar to the counterfeit.  For any actual tuple, `(SD2)` gives the same Kummer
upper-degree and normalized-height identities, while a full norm sums all root-of-unity sheets.
Moriwaki product formulas see the divisorial places of the finitely generated field and average
over those sheets; the distinguished complex identity `exp(qz)` is one embedding of an algebraic
division point and contributes no separate positive place.  A bound strong enough to single it
out would be exactly the pointwise transcendence measure missing in the earlier adelic audit.

Thus the substantive positive statements are the exact closure formula `(SD6)` and the maximal
Hopf envelope `(SD11)`.  They give no Schanuel contradiction because `L`-rational density never
forces an `L`-generic point, even when `L/K` is algebraic.  The counterfeit `(SD12)--(SD20)`
closes the proposed descent, conjugate, and product-formula repairs simultaneously.

### One-sided logarithmic extensions absorb every finite external-value gain

There is a general amplification operation which explains why repeatedly forcing one new
exponential value outside a defect field cannot by itself close the conjecture.  Let

`K=Q(z_1,...,z_n,exp(z_1),...,exp(z_n))`,
`d=td_Q K<n`, and `U=span_Q(z_1,...,z_n)`.                         `(OA1)`

If `b notin U` and `exp(b) in K`, then the augmented tuple `(z_1,...,z_n,b)` is rationally
independent and its generated field is exactly

`K'=K(b)`,  so  `td_Q K'<=d+1<n+1`.                               `(OA2)`

Thus it is another counterexample, with at least the same defect.  There is a symmetric version:
if `b in K \ U`, then the augmented generated field is

`K'=K(exp(b))`,  so again  `td_Q K'<=d+1<n+1`.                     `(OA3)`

In `(OA2)` the input is the one possibly new transcendence unit and its exponential is old; in
`(OA3)` the input is old and its exponential is the one possibly new unit.  No algebraic-
independence theorem which supplies only one side of one new graph pair can beat this exact
one-unit-per-new-direction accounting.

The first construction can be iterated unconditionally using actual analytic logarithms.  The
positive real numbers `log p`, for primes `p`, are Q-linearly independent: after clearing a
rational relation and exponentiating, unique factorization gives a product of distinct prime
powers equal to one, hence all exponents vanish.  Their Q-span is infinite dimensional, whereas
`U` is finite dimensional.  Therefore for every `r` one may choose distinct primes
`p_1,...,p_r` so that

`z_1,...,z_n,log p_1,...,log p_r`                                  `(OA4)`

is Q-linearly independent.  Since `exp(log p_j)=p_j in Q`, its generated field is

`K_r=K(log p_1,...,log p_r)`,
`td_Q K_r<=d+r<n+r`.                                                `(OA5)`

Every added logarithm is transcendental by Hermite--Lindemann, but the original deficit survives
in every finite arity.  In particular a hypothetical defect-one tuple has arbitrarily long
extensions with transcendence degree at most one below their length.  This is an amplification,
not a contradiction: each logarithm consumes exactly the one transcendence unit allowed by its
new input.

The second construction gives the matching absorption rule for named external values.  A defect
field `K` has positive transcendence degree (each nonzero rational direction of the original
independent tuple already satisfies the one-dimensional theorem), hence it is infinite
dimensional as a Q-vector space.  After any finite number of augmentations one can choose
`b in K` outside the current rational input span and append it.  If a theorem proves
`exp(b)` transcendental over `K`, adjoining that forced value raises transcendence degree by
exactly one while arity also rises by one; if it is algebraic over `K`, the defect only becomes
larger.  Repeating produces a finite tower

`K=K_0 subset K_1 subset ... subset K_s`,
`K_(j+1)=K_j(exp(b_j))`,  `td_(K_j) K_(j+1)<=1`,                   `(OA6)`

and a countertuple at every stage.  Consequently the external units forced by Six Exponentials,
Gel'fond's two-by-two theorem, a fixed modular-value theorem, or any other finite collection of
one-value statements can always be absorbed at exactly their arity cost.  A successful route must
instead obtain at least two algebraically independent new quantities from one new rational input,
force a named external quantity back into the *unchanged* field `(OA1)`, or impose a global
compatibility across the entire tower.  The last alternative is not automatic: the union is a
countable infinite-transcendence-degree subfield of `C`, so no finite-arity contradiction or
compactness argument follows merely from `(OA6)`.

### Logarithmic forms see transversality, not the selected graph point

Let `W` be the irreducible Q-locus of a positive fully-transcendental AP witness of length `N`,
let `K=Q(W)=Q(w,y)` be its function field, and normalize `W`.  Thus

`dim W=td_Q K=N-1`, `X_1-X_0=tau=2*pi*i` at the selected embedding,
`Y_1=Y_0` identically on `W`.                                     `(DR1)`

In the Kahler differential space `Omega_(K/Q)`, consider the restrictions of the graph forms

`theta_i=dY_i/Y_i-dX_i`.                                          `(DR2)`

Differentiating the known binomial gives `dY_1/Y_1=dY_0/Y_0`, but therefore

`theta_1-theta_0=-d(X_1-X_0)=-d tau !=0`.                         `(DR3)`

The last inequality is rigorous: for a finitely generated characteristic-zero field, the kernel
of `d:K->Omega_(K/Q)` is the relative algebraic closure of `Q` in `K`, whereas the actual period
`tau` is transcendental.  Thus equal exponential values do **not** give equal graph forms.  They
give a nonzero exact difference.

The residue calculation has the same outcome.  On any normal projective model of `K`, at every
prime divisor `D`,

`res_D(theta_i)=ord_D(Y_i)`, `res_D(dX_i)=0`.                      `(DR4)`

Hence the residue columns for `i=0,1` coincide, and `theta_1-theta_0` has zero residues because it
is exact.  Each individual `theta_i` is nonexact when `Y_i` is transcendental: a nonconstant
rational function has a nonzero divisor on a projective normal model, so `dlog Y_i` has a nonzero
residue somewhere, while an exact rational differential has zero residues.  In rational de Rham
cohomology one therefore has exactly

`[theta_1]=[theta_0]`,                                             `(DR5)`

not a new independent class.

Topological monodromy adds no second period.  For a closed loop `gamma` in the locus where `Y_i`
is invertible,

`integral_gamma theta_i=2*pi*i*wind(Y_i o gamma)`,                 `(DR6)`

because the exact `dX_i` integrates to zero.  The two AP integrals in `(DR6)` are equal.  By
contrast, `tau=(X_1-X_0)(p)` is the value of a rational function at the selected complex point;
it is not the integral of `(DR3)` around a closed algebraic cycle.  Integrating `(DR3)` along an
open path merely returns the difference of its endpoint values and has no Q-de Rham period or
product-formula discreteness.

The arity-two stress makes the tangent gap explicit.  Under a hypothetical irreducible relation
`P(e,tau)=0`, write the curve function field as `Q(E,T)/(P)` and

`X_0=1+T`, `X_1=1+2*T`, `Y_0=Y_1=E`.                              `(DR7)`

At a generic smooth point with `P_E!=0`,

`dE=-(P_T/P_E)*dT`,
`theta_0=(-P_T/(E*P_E)-1)*dT`,
`theta_1=(-P_T/(E*P_E)-2)*dT`,
`theta_1-theta_0=-dT`.                                            `(DR8)`

Since `T=tau` is transcendental, `dT!=0`.  As `dim_K Omega_(K/Q)=1`, the two forms have exact
rank one, the maximum allowed by the defect curve.  Their common annihilator in
`Der_Q(K,K)` is zero.  Thus the de Rham calculation neither supplies a second differential nor a
nonzero tangent vector satisfying the exponential differential equations; proving either would
already prove algebraic independence of `e` and `pi`.

There is an exact AP exponential-character countermodel in every arity which saturates this rank.
Take algebraically independent `T_1,...,T_(N-1)`, with the selected complex value
`T_1=2*pi*i`, and parametrize a rational variety by

`X_0=T_1^2`, `X_1=T_1^2+T_1`, `Y_0=Y_1=T_1`,
`X_i=T_i`, `Y_i=T_i+1` for `2<=i<N`.                              `(DR9)`

The inputs are Q-linearly independent, every displayed coordinate is transcendental, and the
generated field is `Q(T_1,...,T_(N-1))` of transcendence degree `N-1`.  Prescribe a discontinuous
exponential character by

`E(X_0)=E(X_1)=T_1`, `E(T_i)=T_i+1`;                              `(DR10)`

this is consistent because `X_1-X_0=T_1` and hence `E(T_1)=1`, and it extends to `C` as before.
On the normalization,

`theta_0=(1/T_1-2*T_1)*dT_1`,
`theta_1=(1/T_1-2*T_1-1)*dT_1`,
`theta_i=(1/(T_i+1)-1)*dT_i  (i>=2)`.                             `(DR11)`

These forms span all of `Omega_(K/Q)`: their rank is exactly `N-1`, while
`theta_1-theta_0=-dT_1`.  Their residues, exact difference, true numerical period, AP binomial,
field defect, and maximal tangent rank are identical to the proposed de Rham inputs.  Only the
global analytic normalization of the character is missing.

This identifies the precise point at which Ax's differential mechanism is unavailable.  For an
exponential differential field, an integral graph locus satisfies

`D(Y_i)/Y_i=D(X_i)` for every relevant derivation `D`, equivalently `theta_i=0` on its tangent
distribution.                                                       `(DR12)`

Ax then compares the rank of those tangent directions with Q-linear relations modulo constants.
A single complex graph point imposes no instance of `(DR12)` on `Der_Q(K,K)`.  Indeed `(DR3)`
shows that imposing it for both AP coordinates would force `D(tau)=0` for every derivation, hence
`tau` algebraic over `Q`, a contradiction.  The algebraic locus is necessarily transverse to the
graph distribution in at least that direction.

The algebraic-input equality case gives the same warning at full dimension.  For Q-linearly
independent algebraic inputs, `dX_i=0`, and Lindemann--Weierstrass makes the exponential values
algebraically independent; hence the forms `theta_i=dlog Y_i` have rank `N=dim W`.  A principle
forcing a common graph-tangent direction from a point would falsely rule out this sharp equality
case as well.

Therefore the AP binomial accounts for exactly one repeated logarithmic cohomology class, matching
the one-dimensional defect, while its graph-form difference is the nonzero exact differential of
the period coordinate.  Residues, exactness, monodromy, and de Rham periods do not produce the
missing unit.  Any successful Ax-style refinement would have to manufacture an actual formal or
analytic graph arc through the selected point; the point and its Q-algebraic locus do not contain
one.

### Conjugation-stable holomorphic intersections have no parity surplus

This is a self-contained global-intersection audit of the conjugation-stable defect-one normal
form.  Let

`G=G_a^m x G_m^m`, `gamma(z)=(z,exp(z))`,                         `(HI1)`

and let `W subset G` be the irreducible Q-locus of a stable defect-one point
`p=gamma(w)`.  Thus `dim_C W=m-1`, while the exponential graph has dimension `m` in the
`2*m`-dimensional ambient group.  The intersection is overdetermined by one equation.  If `p` is
isolated in the analytic pullback of `W`, generic linear combinations of local generators give
`m` holomorphic germs `f_1,...,f_m` and the positive local number

`mu_p=length_C C{z-w}/(f_1,...,f_m)`.                             `(HI2)`

At a nonsingular graph intersection their Jacobian is invertible, `mu_p=1`, and every remaining
pulled-back equation lies in the maximal ideal generated by the `f_i`.  Restricted minimality is
a statement about dimensions of rational input subspaces; it imposes no condition on this
Jacobian and therefore does not force `mu_p>1`.

The stable real/imaginary splitting makes ordinary conjugate pairing weaker, not stronger.
Choose an eigenbasis

`S=S_+ direct_sum S_-`, `conj=+1 on S_+`, `conj=-1 on S_-`.       `(HI3)`

In the corresponding ambient coordinates the rational holomorphic involution

`sigma(X_+,X_-,Y_+,Y_-)=(X_+,-X_-,Y_+,Y_-^(-1))`                `(HI4)`

preserves the exponential graph.  It also preserves `W`: `sigma(p)=conj(p)`, and a rational
Laurent polynomial vanishes at `p` if and only if it vanishes at `conj(p)`.  Consequently the
anti-holomorphic involution

`rho=sigma o conj`                                               `(HI5)`

preserves both `W` and the graph and fixes the selected point itself.  Its fixed graph is exactly
the sector real form

`z_+ in R`, `z_- in I*R`, `exp(z_+)>0`, `abs(exp(z_-))=1`.        `(HI6)`

Thus a mixed real/unit-circle witness is a *fixed* point of the relevant real structure; it is
not forced to occur in a two-point orbit and fixed-point theory does not split it into a pure
real or pure imaginary witness.

For any invariant bounded domain with no boundary zero, conjugation gives only

`N(Omega)=sum_(q in Omega) mu_q`
`        =2*sum_(nonfixed orbit representatives q) mu_q`
`         +sum_(q in Fix(rho)) mu_q`.                             `(HI7)`

Local complex degrees are positive, and conjugate local multiplicities are equal, so there is no
signed cancellation.  Modulo two, `(HI7)` merely counts fixed zeros.  The selected sector point
is already fixed and may contribute the single unit `mu_p=1`.  If one instead uses ordinary
conjugation, `p` and `conj(p)` may be distinct, but their sum and difference are not graph
intersections: exponentiation does not commute with additive averaging.  Pairing those two
points therefore supplies no failing eigenspace projection.

The exact scalar stress is

`f(z)=exp(z)-z^2`, `beta=-2*W_0(1/2)`.                            `(HI8)`

It has one real zero, the negative `beta`, and

`f'(beta)=beta*(beta-2)!=0`.                                     `(HI9)`

Every other zero is paired with its complex conjugate.  Hence for every centered disk of radius
`R>abs(beta)` whose boundary contains no zero,

`(1/(2*pi*I))*integral_(abs z=R) f'(z)/f(z) dz=1+2*M(R)`.         `(HI10)`

This is a genuine odd global winding number, caused by a simple fixed real graph intersection.
It proves no algebraic independence: the same point satisfies the rational algebraic relation
`Y=X^2`.  Conjugation-symmetric products make the lack of parity rigidity exhaustive:

`F_(r,s,t)(z)=(exp(z)-z^2)^r*(exp(z)+1)^s*(exp(z)-1)^t`.          `(HI11)`

The zero `beta` has multiplicity `r`; the zeros of `exp(z)+1` occur in nonreal conjugate pairs,
and `exp(z)-1` has the fixed zero `0` plus the pairs `+/-k*omega`.  On centered domains the parity
can therefore be either value, and arbitrary local multiplicity is obtained without changing
the rational exponential-polynomial format.

The canonical period itself supplies an odd unit rather than a contradiction.  On a product
neighborhood of `(omega,0,...,0)`, the rational holomorphic system

`H(z_0,...,z_(m-1))=(exp(z_0)-1,z_1,...,z_(m-1))`                `(HI12)`

has Jacobian determinant `1`, local multiplicity `1`, and topological degree `1`.  If `z_0` is
an imaginary-sector coordinate then `rho(z_0)=-conj(z_0)`, so `omega` is a fixed point of the
twisted real structure.  On larger vertical boxes the degree simply counts further period
zeros; changing the height of the box changes the count.  There is no canonical evenness or
nonzero parity left to extract from the anchor.

Intersection currents retain exactly the same information.  For a proper complete intersection,

`[div(f_1)] wedge ... wedge [div(f_m)]`
`  =sum_q mu_q*delta_q`                                          `(HI13)`

locally on the zero-dimensional fiber.  It is a positive conjugation-invariant current, so
`(HI13)` reproduces `(HI7)` and has no signs.  Multiplying an equation by a nonzero rational
constant leaves the current and complex multiplicities unchanged; on the fixed real form it can
reverse a real Brouwer-degree sign.  Thus even the sign is not intrinsic to the Q-variety.
Poincare--Lelong or a multidimensional argument principle moves the total mass to a boundary
integral, but supplies no arithmetic normalization of that boundary value.

There is no compact Bezout number behind `(HI13)`.  The coordinate functions `exp(z_i)` have
essential singularities at the additive hyperplanes at infinity, so the graph does not extend to
a meromorphic cycle in a projective compactification.  Degrees of the algebraic equations of `W`
therefore do not bound the global graph intersection.  The fixed degree-two curve `Y=X^2`
already has the infinitely many intersections `-2*W_k(1/2)` with the exponential graph.  On
large polydiscs, zeroes crossing the boundary change the degree and the Bezout-current mass by
their multiplicities; conjugation only makes nonfixed crossings occur in pairs.

There is a sharp all-dimensional Q-algebraic model with the same overdetermined dimensions.  For
`m>=2`, set

`W_m={Y_i=X_i^2 (1<=i<=m), X_m=X_1} subset G_a^m x G_m^m`.       `(HI14)`

It is irreducible, defined over Q, conjugation-stable, and has dimension `m-1`.  Its graph
pullback is

`exp(z_i)-z_i^2=0 (1<=i<=m)`, `z_m-z_1=0`.                       `(HI15)`

Choose arbitrary Lambert branches `alpha_i=-2*W_(k_i)(1/2)` with `alpha_m=alpha_1`.  Every scalar
root is simple: simultaneous vanishing of `exp(z)-z^2` and its derivative would force `z=0` or
`z=2`, neither of which is a root.  The first `m` equations in `(HI15)` therefore already have
invertible diagonal Jacobian, while the extra equation is locally redundant.  Each intersection
has multiplicity one.  A nonreal choice of `alpha_1` gives two distinct generic conjugate
intersections; the choice `alpha_i=beta` gives a fixed simple real intersection.  Thus

`dim W_m=m-1`, `dim gamma(C^m)=m`, `dim G=2*m`, `mu=1`             `(HI16)`

coexist exactly, despite the negative expected dimension.

The repeated coordinates in `(HI14)` deliberately violate rational input independence.  This is
the sharp logical boundary: requiring `(HI14)` simultaneously to be the exact Q-locus of a
Q-linearly independent graph point of dimension `m-1` would already be a Schanuel counterexample.
Holomorphic intersection theory sees the dimensions, involution, local multiplicities, currents,
and boundary degree displayed above, but it does not see the missing rational-linear hypothesis
in a way that can raise dimension.  Conjugation-stable minimality cannot repair that gap because
`rho` fixes the mixed sector point and averaging conjugate intersections does not preserve the
graph.  Hence no real/imaginary-sector witness, parity contradiction, or canonical winding
surplus follows from the global intersection package.

### Terminal field norms and Moriwaki slopes contain no selected exponential place

The terminal algebraic-extension branch has exactly the form needed for an arithmetic-height
audit.  Write

`F=Q(v,exp(v))`, `td_Q F=d=N-1`,
`K=F(b,y)`, `y=exp_C(b)`, `[K:F]<infinity`.                       `(AH1)`

The singleton theorem excludes the only relevant case `d=0`, so take `d>=1`.  Choose a normal,
flat, projective arithmetic model `B` of relative dimension `d` with function field `F`, and nef
smooth hermitian line bundles `Hbar_1,...,Hbar_d`.  Let `pi:B_K->B` be the normalization in `K`
and put `Hbar'_i=pi^*Hbar_i`.  For every **nonzero** `gamma in K^*`, the polarized product
formula is

`0=-sum_(D in B_K^(1)) ord_D(gamma)*h_(Hbar'_1,...,Hbar'_d)(D)`
`  +integral_(B_K(C)) log|gamma(q)| product_i c_1(Hbar'_i)(q)`.    `(AH2)`

This is the principal arithmetic-intersection identity.  It is Moriwaki's construction of
heights over finitely generated fields; see [Moriwaki, *Arithmetic height functions over
finitely generated fields*](https://arxiv.org/abs/math/9809016).  In the equivalent measured-place
form, the nonarchimedean absolute value attached to `D` has weight
`h_(Hbar'_1,...,Hbar'_d)(D)`, and the archimedean places are the generic complex points equipped
with the wedge measure.  The product formula in precisely this form is Proposition 1.2 of
[Burgos Gil--Philippon--Sombra, *Height of varieties over finitely generated
fields*](https://www.maia.ub.edu/~sombra/publications/FG_Fields/FG_Fields.pdf).

The chosen inclusion `K subset C` is one generic point `q_0 in B_K(C)`.  Since `d>=1`, every
smooth wedge measure in `(AH2)` gives the singleton `{q_0}` measure zero.  More decisively, the
suggested norm of the exponential discrepancy does not exist as a nonzero arithmetic quantity.
There are exactly two interpretations:

`exp_C(b)-y=0 in C`, so, as a field element, it is `0` and its norm is `0`.           `(AH3)`

`exp(b(-))-y(-)` is an analytic function on the complement of the poles of `b` and `y` on `B_K(C)`,
but it is generally not rational and has essential singularities at those poles.              `(AH4)`

The logarithm and divisor in `(AH2)` are undefined for `(AH3)`, while the field norm
`N_(K/F)` is undefined for `(AH4)`.  Replacing the discrepancy by a nonzero algebraic auxiliary
`gamma` restores `(AH2)` but discards the exponential equation.

Norm descent adds no inequality.  For `gamma in K^*`, one has exactly

`div_B(N_(K/F)(gamma))=pi_*div_(B_K)(gamma)`,                     `(AH5)`

and, off the branch locus,

`log|N_(K/F)(gamma)(q)|`
`  =sum_(q' in pi^(-1)(q)) m_(q')*log|gamma(q')|`.                `(AH6)`

The projection formula identifies `(AH2)` with the product formula for its norm in `F`; it
sums all algebraic sheets and produces no positive remainder.  Finiteness of `K/F` likewise
gives no nonarchimedean exponential law.  At a vertical divisor over `p`, the usual `p`-adic
exponential is available only under a convergence inequality such as
`v_p(b)>1/(p-1)`, and neither that inequality nor `Exp_p(b)=y` follows from `(AH1)`.  At the
remaining divisors there is no distinguished exponential branch at all.  Thus the minimal
polynomials of `b` and `y` constrain their valuations separately but impose no relation between
them.

A finite-cover calculation shows that this loss is exact.  Take

`F=Q(T)`, `K=F(S)` with `S^m=T`,                                  `(AH7)`

and select the embedding `S |-> s`, `T |-> s^m`, where `s` is a real ultra-Liouville
transcendental.  For coprime integers `p,q`, put `gamma_(p,q)=q*S-p`.  Then

`N_(K/F)(gamma_(p,q))=(-1)^m*(p^m-q^m*T)`,                       `(AH8)`

and on the selected complex fiber

`log|p^m-q^m*s^m|=sum_(zeta^m=1) log|q*zeta*s-p|`.               `(AH9)`

If `p/q -> s`, the selected `zeta=1` summand is `log|q*s-p|`, while the other summands total
`(m-1)*log q+O_(s,m)(1)`.  Ultra-Liouville approximants make the first summand smaller than
`-A*log q` for arbitrarily large `A`, whereas the coefficient height of the norm in `(AH8)` is
only `m*log q+O(1)`.  The complete product formula remains an equality: the other sheets, the
horizontal divisor of `p^m-q^m*T`, and its archimedean average absorb the selected small value.
This is a finite-extension countermodel to any lower bound derived solely from degree, model,
and polarization data.

Metric and model changes do not create the missing place.  If the first metric is changed by a
smooth conjugation-invariant potential `phi`, then, with one fixed `dd^c` normalization,

`c_1(Hbar'_1(phi))=c_1(Hbar'_1)+dd^c(phi)`,                       `(AH10)`

and the archimedean variation in `(AH2)` is

`integral log|gamma|*dd^c(phi)*product_(i>=2)c_1(Hbar'_i)`
` =sum_D ord_D(gamma)*integral_(D(C)) phi*product_(i>=2)c_1(Hbar'_i)`. `(AH11)`

Poincare--Lelong and integration by parts give `(AH11)`; the variation of the divisor heights
is the same expression with the opposite sign.  Hence every smooth redistribution is absorbed
exactly.  A birational change of model behaves identically by pushforward, with exceptional
divisors supplying the compensating terms.  A smooth potential supported near `q_0` and away
from `div(gamma)` changes neither side, because `log|gamma|` is pluriharmonic there.  To give
`q_0` positive mass one must instead use a singular Green potential.  On a curve, replacing a
probability measure `mu` formally by

`mu_epsilon=mu+epsilon*(delta_(q_0)-mu)`                           `(AH12)`

adds `epsilon*(log|gamma(q_0)|-integral log|gamma|dmu)`; the Green correction needed to restore
the product formula is exactly the negative of this uncontrolled local term.  Thus an atom does
not prove a pointwise lower bound: it inserts that bound as new data.

Arithmetic slope inequalities have the same normalization defect.  If all archimedean norms on
a rank-`r` hermitian lattice are rescaled by `exp(-c)`, then

`widehat_deg(Ebar(c))=widehat_deg(Ebar)+c*r`,
`widehat_mu(Ebar(c))=widehat_mu(Ebar)+c`                           `(AH13)`

up to the fixed normalization of archimedean degree.  Every valid slope inequality shifts its
section-norm term oppositely.  The exponential graph selects neither an integral lattice nor a
hermitian metric at the finite places, so there is no canonical normalization from which a
positive slope gap could follow.  This dependence is substantive: Moriwaki's own [note on
polarizations](https://arxiv.org/abs/math/0006025) explicitly records that even Northcott
finiteness over a finitely generated field depends on the polarization.

The two mandatory stresses expose the pointwise mismatch without a cover.  Under a hypothetical
dependence, the mixed field `Q(e,log 2)` and the period field `Q(log 2,omega)` are function fields
of curves.  Their selected generic complex points satisfy respectively

`exp(1)=e`, `exp(log 2)=2`; and `exp(log 2)=2`, `exp(omega)=1`.     `(AH14)`

But `exp(X)-2` and `exp(U)-1` are not rational functions on those arithmetic surfaces, while
reading `(AH14)` inside the selected subfield makes each discrepancy literally zero.  Every
divisorial valuation and every smooth archimedean measure is therefore unchanged if the standard
exponential is replaced by an abstract character having the same selected values.

**Audited conclusion.**  For every model and polarization attached to `(AH1)`, norm
compatibility gives only the equality `(AH2)`, the actual exponential discrepancy is either zero
or nonalgebraic as in `(AH3)--(AH4)`, and no nonarchimedean place inherits the complex graph
identity.  Consequently arithmetic intersection, norm, Northcott, and slope formalism alone
cannot supply an invariant positive lower bound.  The extra assertion required is a pointwise
lower bound at `q_0`, uniform against the divisorial height of an algebraic auxiliary.  That is
precisely a transcendence measure for the selected exponential comparison, not a consequence of
the finite extension or its arithmetic model.

### The full Lambert divisor has rational Newton sums but no finite-branch arithmetic trace

There is an important sign correction at the outset.  The values
`-2*W_k(1/2)` are only half of the zero divisor of `exp(z)-z^2`.  For
`epsilon in {+1,-1}` put

`r_(epsilon,k)=-2*W_k(-epsilon/2)`, `k in Z`.                    `(HZ1)`

Then

`exp(r_(epsilon,k)/2)=epsilon*r_(epsilon,k)`,
`exp(r_(epsilon,k))=r_(epsilon,k)^2`,                            `(HZ2)`

and the complete, disjoint zero set is

`Z(exp(z)-z^2)={r_(+,k):k in Z} disjoint_union {r_(-,k):k in Z}`. `(HZ3)`

Thus the negative real stress `beta=-2*W_0(1/2)` lies in the `epsilon=-1`
family, while `-2*W_k(-1/2)` supplies the other square-root sign.  This follows simply from

`exp(z)-z^2=(exp(z/2)-z)*(exp(z/2)+z)`.                          `(HZ4)`

All these zeros are simple: at a zero `r`,
`(exp(z)-z^2)'|_r=r*(r-2)`, and neither `0` nor `2` is a zero.  The standard
Lambert asymptotic, in the branch convention of [DLMF
4.13](https://dlmf.nist.gov/4.13), gives for fixed nonzero `x`

`W_k(x)=2*pi*I*k-log(2*pi*I*k)+log(x)+O(log(abs k)/abs k)`.       `(HZ5)`

Consequently `r_(epsilon,k)=-4*pi*I*k+O(log(abs k))`, with the expected
half-index shift when `x=-1/2`.  Each family has exponent of convergence one, the union has

`#{r: abs(r)<=R}=R/pi+O(log R)`,                                 `(HZ6)`

and `sum_r abs(r)^(-n)` converges exactly for `n>=2`.

The branch-index regularization can be computed without an unspecified Hadamard constant.
Cohen's [Lambert branch product
identity](https://arxiv.org/abs/2012.11698), with every product interpreted as the limit over
`-K<=k<=K`, is

`product_(k in Z) (1-t/W_k(x))=exp(-t/2)-(t/x)*exp(t/2)`.        `(HZ7)`

Substituting `x=-epsilon/2` and `t=-z/2` gives the two exact half-divisor products

`P_epsilon(z):=product_k (1-z/r_(epsilon,k))`
` =exp(z/4)-epsilon*z*exp(-z/4)`
` =exp(-z/4)*(exp(z/2)-epsilon*z)`.                              `(HZ8)`

Multiplication gives both the branch-index product and the usual genus-one canonical product
for the full divisor:

`P_+(z)*P_-(z)=exp(-z/2)*(exp(z)-z^2)`,
`exp(z)-z^2=exp(z)*product_(epsilon,k) E_1(z/r_(epsilon,k))`,
`E_1(u)=(1-u)*exp(u)`.                                          `(HZ9)`

The last exponential factor is forced by `f(0)=f'(0)=1`; it is not an arithmetic remainder.

All reciprocal Newton sums are now explicit.  Define

`S_(epsilon,n)=sum_(k in Z) r_(epsilon,k)^(-n)`,                 `(HZ10)`

using Cohen's symmetric branch ordering for `n=1`; for `n>=2` the sum is absolute and needs no
regularization.  Expanding the logarithm of `(HZ8)` gives

`S_(epsilon,n)`
` =n*sum_(m=1)^n epsilon^m*(-1)^(n-m)*m^(n-m-1)`
`       /(2^(n-m)*(n-m)!)-1_(n=1)/4`.                           `(HZ11)`

In particular `S_(+,1)=3/4` and `S_(-,1)=-5/4`.  For the complete zero set put
`S_n=S_(+,n)+S_(-,n)`.  Then

`S_1=-1/2`,
`S_n=(-1)^n*n*sum_(m=1)^(floor(n/2)) m^(n-2*m-1)/(n-2*m)!`
`    (n>=2)`.                                                    `(HZ12)`

Thus, for example,

`S_2=2`, `S_3=-3`, `S_4=4`, `S_5=-35/6`, `S_6=33/4`.           `(HZ13)`

The first equality in `(HZ12)` is genuinely convention-dependent: `sum abs(r)^(-1)` diverges,
and a different non-symmetric ordering changes the exponential prefactor.  All identities for
`n>=2` are invariant absolute sums.

There is an equally explicit regularized elementary-symmetric form.  Write

`P_+(z)*P_-(z)=sum_(n>=0) (-1)^n*E_n*z^n`.                      `(HZ14)`

Since the left side is `exp(z/2)-z^2*exp(-z/2)`,

`E_n=(-1)^n*(1/(2^n*n!)-1_(n>=2)*(-1/2)^(n-2)/(n-2)!)`.        `(HZ15)`

The formal Newton identities

`n*E_n=sum_(j=1)^n (-1)^(j-1)*E_(n-j)*S_j`                     `(HZ16)`

hold exactly.  These are regularized symmetric functions of the *whole infinite divisor*, not
elementary symmetric polynomials in any finite list of roots.

The unconditional arithmetic consequences stop much earlier than the analytic identities:

* Every root `r` is transcendental.  Otherwise `r/2` is a nonzero algebraic number and
  Hermite--Lindemann contradicts `exp(r/2)=+/-r`.
* Every two distinct roots `r,s` in the full two-family divisor are Q-linearly independent.  If
  `s=(a/b)*r` with nonzero integers `a,b`, then `b*s=a*r` and `(HZ2)` give
  `s^(2*b)=r^(2*a)`.  Hence
  `r^(2*(a-b))=(a/b)^(2*b)`; transcendence of `r` forces `a=b`, hence `s=r`.
  In particular no two distinct roots have rational ratio.
* Each root is Q-linearly independent from `omega=2*pi*I`.  Indeed `r=q*omega` with
  `q in Q^*` would make `exp(r)` algebraic while `r^2=q^2*omega^2` is transcendental.
* A singleton root is multiplicatively independent even modulo algebraic constants: if
  `r^m in Qbar^*` for a nonzero integer `m`, then `r` is algebraic.  For a finite root set, an
  integral additive relation `sum_j m_j*r_j=0` implies
  `product_j r_j^(2*m_j)=1`; conversely a multiplicative relation
  `product_j r_j^(m_j)=1` implies `sum_j m_j*r_j in omega*Z`.    `(HZ17)`

The last line explains why pairwise Q-linear independence does not prove multiplicative
independence: a nonzero period can absorb the additive relation.  No unconditional argument here
proves Q-linear independence for arbitrary finite sets of three or more branches, multiplicative
independence of two arbitrary branches, or algebraic independence of two branches.

Indeed the two-branch boundary is exact.  For distinct roots `r,s`, the preceding bullet proves
Q-linear independence, while `(HZ2)` gives

`Q(r,s,exp(r),exp(s))=Q(r,s)`.                                  `(HZ18)`

Therefore Schanuel's bound for this pair is *equivalent* to algebraic independence of `r,s`.
Any global-zero argument producing that conclusion would already prove this concrete
two-variable Schanuel instance.  More generally, whenever a finite branch set is Q-linearly
independent, its Schanuel bound is precisely algebraic independence of the branch values.

This remains unchanged after adjoining the canonical anchor.  For finite roots
`r_1,...,r_M`, the anchored graph field is exactly

`Q(1+omega,1+2*omega,r_j,e,e,r_j^2)=Q(e,omega,r_1,...,r_M)`.     `(HZ19)`

Neither zero density nor the rational numbers in `(HZ12)--(HZ16)` force this field to gain one
transcendence unit per branch.  For a chosen finite subset `A` and `n>=2`, the exact identity is

`sum_(r in A) r^(-n)=S_n-sum_(r notin A) r^(-n)`.               `(HZ20)`

The analytic tail is convergent but has no algebraicity, height, or finite-degree control over
the selected field.  The Lambert branches are an infinite analytic monodromy orbit, not a
finite Galois orbit over Q, so `(HZ20)` is neither a trace nor a norm.  Symmetric regularization
has retained every omitted branch rather than eliminated it.

The metric information is equally non-arithmetic.  The asymptotic separation `(HZ5)` and the
count `(HZ6)` control the exponent of convergence and the order of the canonical product.  They
assign no Weil height to the transcendental roots and give no Liouville lower bound for a
polynomial evaluated at finitely many of them.  Three comparison models make the decoupling
sharp:

`sin(pi*z)/(pi*z)=product_(n>=1) (1-z^2/n^2)`                    `(HZ21)`

has an infinite simple, linearly separated zero orbit contained in `Q`; `exp(z)-1`, whose Taylor
coefficients are rational, has all zeros `k*omega` in the one-dimensional field `Q(omega)`; and
for any transcendental `T`, the zeros of `sin(pi*(z-T))` are all `T+Z`, so every finite branch
set lies in `Q(T)` despite order one, exact spacing, a canonical product, and arbitrarily many
zeros.  Thus even rational Taylor coefficients plus a full order-one divisor do not imply
transcendence-degree growth of individual zeros.

**Audited conclusion.**  Hadamard factorization gives the exact products `(HZ8)--(HZ9)`, the
rational reciprocal sums `(HZ11)--(HZ13)`, and the regularized Newton system
`(HZ14)--(HZ16)`.  Its strongest finite arithmetic output is individual transcendence,
pairwise Q-linear independence, and root--period Q-linear independence.  It gives no new finite
algebraic- or multiplicative-independence theorem.  The missing statement would have to turn an
infinite analytic tail such as `(HZ20)` into a finite arithmetic trace with degree/height
control.  Such a statement is absent from Hadamard and value-distribution theory and, already
for two roots, would prove the exact Schanuel instance `(HZ18)`.  The sine and period examples
show that no theorem based only on order, zero density, separation, canonical products, or global
Newton sums can have that consequence.

### Tate degeneration turns graph pairs into periods or external modular data

Let `omega=2*pi*I`.  For `0<|q|<1`, choose a logarithm of `q` and put

`Lambda_q=omega*Z+log(q)*Z`,
`C/Lambda_q --exp--> C^*/q^Z`.                                  `(TE1)`

This is the additive form of Tate uniformization.  To keep the arithmetic coordinates explicit,
write

`s_k(q)=sum_(n>=1) n^k*q^n/(1-q^n)`,
`a_4(q)=-5*s_3(q)`, `a_6(q)=-(5*s_3(q)+7*s_5(q))/12`,            `(TE2)`

and

`E_q: Y^2+X*Y=X^3+a_4(q)*X+a_6(q)`.                              `(TE3)`

For `u notin q^Z`, the analytic quotient map is

`P_q(u)=(X(u,q),Y(u,q))`,                                        `(TE4)`

where

`X(u,q)=sum_(n in Z) q^n*u/(1-q^n*u)^2-2*s_1(q)`,
`Y(u,q)=sum_(n in Z) (q^n*u)^2/(1-q^n*u)^3`
`       +sum_(n>=1) q^n/(1-q^n)^2`.                              `(TE5)`

The invariant differential pulls back to `du/u`, the discriminant is

`Delta(q)=q*product_(n>=1)(1-q^n)^24`,
`J(q)=q^(-1)+744+196884*q+...`.                                  `(TE6)`

These are the standard exact Tate formulas; an authoritative statement with the quotient and
normalized differential is [Tate curve over `C`, Proposition
21.3.5.7](https://math.mit.edu/~hao_peng/skyscraper.pdf).  They already show that passing from
`(b,y=exp b)` to an elliptic point does not stay in `Q(b,y)`: it generally adjoins the two
coefficient values in `(TE2)` and the two infinite-orbit values in `(TE5)`.

There is one way to avoid the new point coordinates, and it loses the graph pair completely.  If
`|y|!=1`, choose `epsilon in {+1,-1}` so that

`q=y^epsilon=exp(epsilon*b)` satisfies `0<|q|<1`.                 `(TE7)`

Then `log q=epsilon*b mod omega*Z`, so `b in Lambda_q`, and

`P_q(y)=P_q(q^epsilon)=O`.                                       `(TE8)`

Thus the input becomes a Tate period and the output becomes the identity.  The Neron--Tate
height is exactly zero, and every elliptic analytic-subgroup theorem treats `(TE8)` as an allowed
kernel relation.  The literal canonical model is especially sharp:

`q=e^(-1)`, `Lambda_q=omega*Z-Z`, `P_q(e)=O`.                     `(TE9)`

Both canonical additive anchors `1,omega` lie in the lattice and the value `e=q^(-1)` is killed.
This is an actual holomorphic quotient, not an abstract-character counterfeit.  It proves that
the Tate group law itself retains none of the desired independence of `e` and `omega`.  If
`|y|=1`, no nonzero integral power of `y` is a Tate nome; producing a curve then necessarily
introduces an unrelated modulus.

The mixed and period stresses behave identically.  Taking `q=1/2` gives

`Lambda_(1/2)=omega*Z-(log 2)*Z`, `P_(1/2)(2)=O`;                 `(TE10)`

both entries of `(log 2,omega)` are periods.  Taking the nome directly from `omega` instead gives
`exp(omega)=1`, the cusp rather than an elliptic curve.  Moreover `q=1/2` is algebraic, so
Mahler's theorem (also a consequence of Nesterenko's theorem `(CM2)`) gives

`J(1/2) is transcendental`.                                      `(TE11)`

In fact `(CM2)` makes `E_2(1/2),E_4(1/2),E_6(1/2)` algebraically independent.  Since `a_4`
determines `E_4` and `(a_4,a_6)` determines `(E_4,E_6)`, the displayed Tate equation at `q=1/2`
is not a curve over `Qbar`.  More generally an algebraic nome is the wrong arithmetic
specialization: for every algebraic `0<|q|<1`, `J(q)` is transcendental.

For an unconditional elliptic-logarithm theorem one needs a curve `E_0/Qbar` and a point
`P in E_0(Qbar)`.  In Tate language these are two separate special-value requirements:

`J(q) in Qbar`, and `P_q(u)` becomes algebraic after an isomorphism `E_q ~= E_0`. `(TE12)`

Neither follows from `u=exp(b)`.  When `J(q)` is algebraic, the raw coefficients `(TE2)` can
still be transcendental; changing to an algebraic Weierstrass model rescales the invariant
differential by a new elliptic period.  If `Omega_1,Omega_2` are periods of an algebraically
normalized differential and `c*Lambda_q=<Omega_1,Omega_2>`, then the logarithm to which the
analytic subgroup theorem applies is

`ell_P=c*b`, not `b`.                                             `(TE13)`

Wustholz's theorem indeed applies to `(E_0,P)` under `(TE12)` and gives the expected algebraic-
linear restrictions on `ell_P` and the elliptic periods; see the primary
[analytic-subgroup preprint](https://archive.mpim-bonn.mpg.de/id/eprint/3829/).  It gives no
algebraic independence of their products or ratios.  There is also no algebraic homomorphism
`G_m -> E_0` carrying `u` to `P_q(u)`: the Tate quotient is analytic, while every algebraic map
of connected algebraic groups from the affine torus to the proper elliptic curve is constant.
Consequently applying the theorem to `G_m times E_0` does not encode `(TE4)`.

The most favorable arithmetic nome makes the new period visible.  Take

`q=exp(-2*pi)`, so `tau=I`, `J(q)=1728`,
`Lambda_q=omega*(Z+I*Z)`.                                        `(TE14)`

Let `E_0/Qbar` be a CM model whose algebraic differential has period lattice
`Omega*(Z+I*Z)`.  The required scale and a terminal logarithm are exactly

`c=Omega/omega`, `ell_(P_q(exp b))=(Omega/omega)*b`.              `(TE15)`

Up to a nonzero algebraic factor, `Omega=Gamma(1/4)^2/sqrt(pi)`; thus `(TE15)` introduces the CM
period already isolated in `(CM3)--(CM6)`.  For the canonical point `u=e`, the logarithm on the
algebraic model is `Omega/omega`.  The point is nontorsion, since torsion would give
`e^n=exp(-2*pi*m)` and hence `n=-2*pi*m` for integers `m,n`.  But its algebraicity is not known
from the Tate formula: it is the new assertion that the scaled values in `(TE5)` are algebraic.
Even if it is imposed, Wustholz sees the relation

`omega*ell_P=Omega`                                               `(TE16)`

with the transcendental coefficient `omega`; it is not an algebraic-linear relation and violates
none of the theorem's hypotheses or conclusions.  Under a hypothetical AP defect
`td_Q Q(e,omega)=1`, Nesterenko instead forces `exp(pi)` and the CM period outside that field as
in `(CM8)`.  The algebraic CM curve therefore imports external units; it does not return one to
the original graph field.

Neron--Tate heights do not repair either branch.  In Tate normalization, for a representative
`|q|<|u|<=1`, put

`g_0(u)=(1-u)*product_(n>=1)(1-q^n*u)*(1-q^n/u)`,
`r=log|u|/log|q| in [0,1)`.                                      `(TE17)`

Up to the standard fixed normalization, the local canonical height is the exact theta/Bernoulli
expression

`lambda_q(P_q(u))=-log|g_0(u)|-(1/2)*B_2(r)*log|q|`,
`B_2(r)=r^2-r+1/6`.                                               `(TE18)`

At `(TE8)` the global height is zero.  In the algebraic-point branch the positive height of a
nontorsion `P` is a height of the new coordinates `(TE5)` and sums all number-field places; the
single complex identity `u=exp(b)` controls none of the other local terms.  Formula `(TE18)`
therefore measures the imported theta product rather than the transcendence degree of
`Q(b,u)`.

Silverman's specialization theorem has an exact but incompatible quantifier.  For an abelian
scheme over a curve `C/Qbar` and an algebraic section `P`, it gives, after fixing the base height,

`lim_(h_C(t)->infinity) widehat_h_(E_t)(P_t)/h_C(t)`
`  =widehat_h_(E_eta)(P)`, `t in C(Qbar)`.                        `(TE19)`

See [Silverman, *Heights and the specialization map for families of abelian
varieties*](https://doi.org/10.1515/crll.1983.342.197).  It neither specializes algebraicity to a
prescribed transcendental nome nor transports an analytic exponential identity.  Approximating
`e^(-1)` by algebraic nomes produces curves with transcendental `J` by `(TE11)`.  Parametrizing
instead by algebraic `j`-values gives algebraic curves but transcendental inverse nomes and no
algebraic section whose Tate parameter is the fixed number `e` or a terminal `y`.  At the CM
fiber `j=1728`, `(TE19)` is not a large-height limit, and the required point algebraicity remains
exactly `(TE12)`.  Degeneration `q->0` only makes the `-log|q|` and theta terms in `(TE18)` grow;
it supplies no specialization back to `q=e^(-1)`.

**Audited conclusion.**  Tate uniformization has an exhaustive dichotomy.  Choosing `q` from a
graph pair gives the exact period/identity saturation `(TE7)--(TE10)`.  Choosing an algebraic
elliptic curve and a nontrivial point requires the new modular condition, elliptic period scale,
and point coordinates `(TE12)--(TE15)`.  Analytic-subgroup theorems then give only linear period
information, while Neron--Tate and specialization heights are defined only after those external
arithmetic data have been supplied.  No unconditional unit is returned to `Q(e,omega)` or to the
terminal field `Q(v,exp(v))`; excluding terminal algebraicity would require an algebraic-
independence theorem for the mixed exponential/elliptic special values, not Tate degeneration.

### Parameter-free exponential closure has rank zero and infinite ordinary transcendence

Three closure operators must be kept separate.  In an exponential field `(F,E)`, define
`ecl_F(A)` to consist of coordinates of solutions of square exponential-polynomial systems over
`A` with nonzero exponential Jacobian.  Kirby's [exponential-algebraicity
theorem](https://arxiv.org/abs/0810.4285) proves, for every exponential field, that `ecl` is a
finite-character pregeometry and agrees with closure under `E`-derivations.  Model-theoretic
`acl` means membership in a finite definable set, while `dcl` means unique definability.  Neither
of the latter notions is part of the definition of `ecl`.                         `(CLX1)`

The actual real exponential field is the exceptional setting where the three notions agree.
Wilkie's model-completeness/o-minimality theorem and the implicit-definition theorem of
[Jones--Wilkie](https://eprints.maths.manchester.ac.uk/944/1/Locally_Polynomially.pdf) give, for
every `A subset R`,

`acl_(R_exp)(A)=dcl_(R_exp)(A)=ecl_R(A)`.                        `(CLX2)`

The last equality is also recorded explicitly as Proposition 3.5 of
[Krapp](https://londmathsoc.onlinelibrary.wiley.com/doi/full/10.1112/blms.12972).  Here
`acl=dcl` follows from definable Skolem functions/order, and this closure has exchange.  A fixed
real Khovanskii system has a definable discrete set of nonsingular solutions, hence only finitely
many by o-minimality; order then defines each one by its position in that finite set.

The Lambert stress is already a parameter-free rank-zero transcendental.  Let `beta<0` be the
unique negative solution of

`exp(beta)-beta^2=0`.                                            `(CLX3)`

It is a simple zero because

`(exp(X)-X^2)'|_beta=beta*(beta-2)!=0`.                          `(CLX4)`

Thus `beta in ecl_R(emptyset)`, and its uniqueness on the negative half-line puts it in
`dcl_(R_exp)(emptyset)` directly.  Hermite--Lindemann proves

`etd(beta/emptyset)=dim_dcl(beta/emptyset)=0`,
`trdeg_Q Q(beta,exp(beta))=trdeg_Q Q(beta)=1`.                   `(CLX5)`

The same phenomenon occurs at the mixed boundary.  With `ell=log 2`,

`ell in dcl(emptyset)` via `exp(X)-2=0`, `e=exp(1) in dcl(emptyset)`,
`dim_dcl(1,ell/emptyset)=0`,
`Q(1,ell,exp(1),exp(ell))=Q(e,ell)`.                             `(CLX6)`

Both `e` and `ell` are transcendental, so the last field has transcendence degree either one or
two.  Closure theory gives exactly the same rank-zero data in both alternatives.  Saying that
the degree is two is the original mixed Schanuel instance, not a consequence of `(CLX2)`.
Likewise `(1,beta)` is Q-linearly independent, has closure rank zero, and has graph field
`Q(e,beta)`; its degree-one/degree-two alternative is invisible to `dcl` and `ecl`.

In fact the parameter-free real closure has the largest ordinary transcendence degree compatible
with countability.  Let `p_1,p_2,...` be distinct primes and put

`a_j=sqrt(p_j)>0`, `t_j=exp(a_j)`.                               `(CLX7)`

Every `a_j,t_j` lies in `dcl_(R_exp)(emptyset)`.  The `a_j` are Q-linearly independent, and a
polynomial relation among finitely many `t_j` would be a Qbar-linear relation among exponentials
of the distinct algebraic sums `sum m_j*a_j`; Lindemann--Weierstrass excludes it.  Hence

`{t_j:j>=1} is algebraically independent over Q`,
`trdeg_Q dcl_(R_exp)(emptyset)=aleph_0`.                         `(CLX8)`

The reverse inequality follows because the language is countable, so there are only countably
many parameter-free definable elements.  Thus a pregeometry can have exchange, finite character,
countable closure, and *countably infinite pure-field transcendence degree entirely in its
rank-zero closed set*.

For every finite initial tuple `a=(a_1,...,a_n)` from `(CLX7)`, Lindemann--Weierstrass gives the
proved algebraic-input equality case

`dim_dcl(a/emptyset)=0`,
`trdeg_Q Q(a,exp(a))=n`, `delta(a)=0`.                            `(CLX8a)`

Thus closure rank zero occurs both in a theorem-level Schanuel equality case and in the unresolved
mixed alternative `(CLX6)`; the pregeometry data do not distinguish them.

There is a concrete all-deletion matroid inside this actual rank-zero core.  For `m>=3`, take
algebraically independent `t_1,...,t_(m-1)` from `(CLX7)` and set

`u=(t_1,...,t_(m-1),product_(j<m)t_j)`.                          `(CLX9)`

The `m` entries are Q-linearly independent, every entry is parameter-free definable, and

`trdeg_Q Q(u)=m-1`,
`Q(u) is generated by every one-coordinate deletion of u`,
`dim_dcl(u/emptyset)=0`.                                        `(CLX10)`

For `m=2`, use `u=(t_1,t_1^2)`; the full field is algebraic over either deletion and again has
degree one.  This is an exact pure-field defect-one/all-deletion configuration living at closure
rank zero.  All values `exp(u_i)` are also parameter-free definable, but their ordinary
transcendence contribution is not controlled by closure.  Requiring the graph field in `(CLX10)`
also to have degree `m-1` would be an actual Schanuel counterexample; the point of the model is
that exchange and definability provide no step toward excluding it.

The complex situation is different at the model-theoretic level but identical at the `ecl`
level.  Put

`C_E=ecl_C(emptyset)`.                                          `(CLX11)`

For a countable parameter set there are countably many rational exponential-polynomial systems,
and the nonsingular zeros of each holomorphic square system form a discrete, hence countable,
subset of `C^n`.  Therefore `C_E` is countable.  The same family
`exp(sqrt(p_j))` used in `(CLX7)` lies in `C_E` and is algebraically independent, so

`trdeg_Q C_E=aleph_0`, `etd(C_E/emptyset)=0`.                    `(CLX12)`

Every Lambert branch solving `exp(X)-X^2=0`, every logarithm of `2`, and every period is in
`C_E`: each is a nonsingular Khovanskii zero.  Unlike over the reals, these equations have
infinitely many complex solutions.  Hence Khovanskii isolation is only local and does not by
itself give a finite definable set.  The characterization of `acl` or `dcl` in the pure complex
exponential field remains open; the equality `(CLX2)` must not be imported into `C_exp`.
There are isolated positive facts: the ring `Z` is definable as the multiplicative stabilizer of
`ker(exp)`, so the two generators `{omega,-omega}` of the cyclic kernel form a finite definable
set and `omega in acl_(C_exp)(emptyset)`.  This again puts an ordinarily transcendental constant
at model-theoretic algebraic rank zero without identifying `acl` with `ecl`.
Adding conjugation, a real predicate, and order can select `beta` or the principal `ell`, but that
is a stronger language and still does not change their pure-field transcendence.

The canonical stable least-failure package lands exactly in this blind core.  The earlier
minimality/derivation reduction shows that a globally least Schanuel failure can be chosen with
all inputs in `C_E`; conjugation, rational basis changes, canonical anchors, and the stable shear
preserve `C_E`.  Thus a hypothetical canonical conjugation-stable fully transcendental
defect-one witness `w` can satisfy simultaneously

`w subset C_E`, `etd(w/emptyset)=0`,
`ldim_Q(w)=N`, `trdeg_Q Q(w,exp(w))=N-1`.                        `(CLX13)`

At its terminal deletion, if

`F=Q(v,exp(v))`, `K=F(b,exp(b))`, `[K:F]<infinity`,              `(CLX14)`

then pure-field algebraicity already gives `b,exp(b) in ecl_C(v)`: `ecl_C(v)` is an
exponential subfield and contains the pure-field algebraic closure of `F`.  Exchange merely
records that the terminal element is closure-dependent.  Since all of `(CLX13)` lies in the base
`C_E`, Kirby's unconditional weak predimension inequality over the ecl-closed base reads only

`trdeg_(C_E) C_E(w,exp(w))-ldim_Q(w/C_E)=0-0>=etd(w/C_E)=0`.     `(CLX15)`

It places no restriction on the absolute defect
`trdeg_Q Q(w,exp(w))-ldim_Q(w)=-1`.  Countability is equally silent: a finite countertuple fits
inside a countable closed set, and `(CLX12)` shows that this closed set has ample ordinary
transcendence.

Quasianalyticity does not add an arithmetic unit.  By finite character, a finite tuple in `C_E`
can be enlarged to a nonsingular zero of a finite square Khovanskii system over `Q`.  The inverse
function theorem makes that germ a reduced isolated point, and holomorphic/real-analytic
quasianalyticity prevents a function with a zero of infinite order from being nonzero.  But
`beta` already has the strongest possible local situation: a parameter-free simple zero with
Jacobian `(CLX4)`.  Its relative questions with `e`, and the mixed question `(CLX6)`, remain
open.  Local multiplicity one is therefore saturated before any ordinary algebraic-independence
surplus appears.

There is a sharp countable exponential-field counterconfiguration showing that the abstract
closure axioms alone cannot do better.  Let

`F=Qbar(T)^alg`                                                   `(CLX16)`

with `T` transcendental.  Choose a Q-basis of the additive group containing `T,T^2`, prescribe
coherent rational roots so that a total homomorphism `E:F^+->F^*` satisfies

`E(T)=T`, `E(T^2)=T^2`,                                         `(CLX17)`

and extend it using divisibility of `F^*`.  Both `T` and `T^2` are nonsingular zeros of the same
parameter-free equation

`E(X)-X=0`, with exponential derivative `E(X)-1!=0`.             `(CLX18)`

Since `T in ecl_F(emptyset)` and `F` is algebraic over `Qbar(T)`, one has

`ecl_F(emptyset)=F`, `F is countable`,
`etd_F(F/emptyset)=0`.                                          `(CLX19)`

Thus `ecl_F` has exchange, finite character, and the countable-closure property, while the
Q-linearly independent tuple `(T,T^2)` has

`trdeg_Q Q(T,T^2,E(T),E(T^2))=1<2`.                             `(CLX20)`

This field is deliberately not ordered, analytic, or the actual complex exponential field.  It
is an exact countermodel to any *formal* implication from Khovanskii nonsingularity, exchange, or
countable closure to nonnegative ordinary predimension.

Finally, the pseudo-exponential distinction is decisive.  Zilber's
[pseudo-exponential fields](https://ora.ox.ac.uk/objects/uuid%3Ab9ffda07-1690-4bc1-b9f7-e6a3f91f7783)
axiomatize an algebraically closed exponential field with standard kernel, the Schanuel
predimension inequality, strong exponential-algebraic closedness, and countable closure.  In
those fields `(CLX20)` is impossible because

`delta(x)=trdeg_Q Q(x,E(x))-ldim_Q(x)>=0`                        `(CLX21)`

is an axiom.  Exchange and countable closure are unconditional for actual `C_exp`; `(CLX21)` is
precisely Schanuel's conjecture there, and strong exponential-algebraic closedness is also not an
available theorem for the standard complex exponential field.  Quasiminimal excellence controls
generic types over closed sets only after these pseudo-exponential axioms are assumed; it cannot
be used to prove the axiom `(CLX21)` for rank-zero constants.

**Audited conclusion.**  In `R_exp`, `acl=dcl=ecl` is a countable exchange pregeometry whose
parameter-free closed set already has ordinary transcendence degree `aleph_0`; `beta`, `ell`, and
`e` are explicit rank-zero transcendental points.  In `C_exp`, `ecl` still has exchange and
countable closure, while `acl/dcl` are not characterized, and a least stable defect-one failure
would lie wholly in `C_E`, where the relative weak predimension theorem becomes `0>=0`.
The actual configurations `(CLX3)--(CLX10)` and the exact exponential counterfeit
`(CLX16)--(CLX20)` show that isolation, quasianalyticity, exchange, finite character, and
countability cannot force an ordinary transcendence surplus.  The principle that does so in
pseudo-exponential fields is the Schanuel predimension axiom itself.

### Dense terminal unit groups have infinite-rank additive complements

Consider the real sector of the stable terminal alternative.  Thus

`K=F(b,y)`, `[K:F]<infinity`, `e in F`,
`b,y algebraic over F`, `b in R`, `y=exp(b)>0`,                  `(SU1)`

where full transcendence makes `b` irrational.  The multiplicative group

`Gamma=<e,y> subset K^*`                                        `(SU2)`

has rank exactly two.  Indeed `e^p*y^q=1` gives `p+q*b=0`, because the exponent
is real; irrationality of `b` then gives `p=q=0`.  This finite rank is a genuine consequence,
but it controls exact additive equations, not archimedean proximity.

Let `p_n/q_n` be the continued-fraction convergents to `b`, with `q_n>0`, and put

`delta_n=q_n*b-p_n`, `U_n=e^(-p_n)*y^(q_n)=exp(delta_n) in Gamma`. `(SU3)`

The standard exact convergent inequalities are

`1/(q_n+q_(n+1))<|delta_n|<1/q_(n+1)`.                           `(SU4)`

Since `q_(n+1)>=q_n`, for all large `n`

`(1/2)*|delta_n|<=|U_n-1|<=2*|delta_n|`,
`-log|U_n-1|=log q_(n+1)+O(1)`.                                  `(SU5)`

Writing `q_(n+1)=a_(n+1)q_n+q_(n-1)` makes the gain
`log q_n+log a_(n+1)+O(1)`.  Stable minimality imposes no known restriction on these partial
quotients.

The global algebraic complexity grows much faster.  For every fixed Moriwaki polarization of
the finitely generated field `K`, height and divisor functoriality give

`h(U_n)<=|p_n|*h(e)+q_n*h(y)=O_b(q_n)`,
`div(U_n)=-p_n*div(e)+q_n*div(y)`.                                `(SU6)`

Also `h(1-U_n)<=h(U_n)+O(1)`.  Thus ordinary continued fractions give logarithmic smallness
against linear height.  Exceptionally large `a_(n+1)` can improve the selected complex value,
but the distinguished embedding of a positive-transcendence-degree field is not a positive-mass
place in the product formula, as `(AH2)--(AH12)` showed.

The exact scope of the unit-equation theorem is decisive.  The
[Evertse--Schlickewei--Schmidt theorem](https://annals.math.princeton.edu/2002/155-3/p04)
works over **every** characteristic-zero field: for a finite-rank subgroup
`Delta subset (K^*)^m`, the nondegenerate solutions of

`a_1*x_1+...+a_m*x_m=1`                                         `(SU7)`

are bounded in number solely in terms of `m` and `rank(Delta)`.  Hence it would apply here if
both coordinates of

`U_n+(1-U_n)=1`                                                   `(SU8)`

belonged to one fixed finite-rank multiplicative group.  The first coordinates do; the second
do not.  In fact the theorem proves the sharp positive statement

`rank <1-U_n:n>=1> = infinity`.                                  `(SU9)`

For otherwise the pairs `(U_n,1-U_n)` would lie in a fixed finite-rank subgroup of `(K^*)^2`
and give infinitely many distinct nondegenerate solutions of `(SU8)`.  Thus algebraicity of all
`1-U_n` over `F`—automatic because they lie in the one fixed finite extension `K/F`—does not
approximate the missing finite-rank hypothesis.  Finite extension degree and multiplicative rank
are unrelated.

Stable minimality supplies only ordinary algebraic recurrences.  If

`Y^d+c_(d-1)Y^(d-1)+...+c_0 in F[Y]`                             `(SU10)`

annihilates `y`, then multiplying `(SU10)` by `e^p*y^q` gives a fixed projective relation among
consecutive powers.  As `(p,q)` varies, all ratios of its terms are unchanged powers of `y`; it
does not produce distinct solutions of a fixed inhomogeneous equation such as `(SU7)`.  Norms
make the same compensation explicit:

`N_(K/F)(1-U_n)`
` =product_(sigma:K/F) (1-e^(-p_n)*sigma(y)^(q_n)) in F^*`.       `(SU11)`

The selected factor is small, while the other conjugate factors have height and logarithmic
size `O(q_n)`.  The norm lands in the transcendental field `F`, not in a discrete ring of
integers.

The function-field `S`-unit theorem fails at exactly the same coordinate.  On a normal
projective model, let `S` contain the supports of `div(e)` and `div(y)`.  Every `U_n` is an
`S`-unit, but the zero divisor of `1-U_n` generally leaves `S`.  If infinitely many complements
were also `S`-units, the exact equation `(SU8)` and the function-field unit theorem would already
give a contradiction.  Instead their new zeros account for the linear height in `(SU6)`.  The
model example is

`A=Z[T,T^(-1)]`, `U_m=T^m`,
`1-U_m=product_(d|m) Phi_d(T)`.                                  `(SU12)`

As `m` ranges through primes, a new irreducible cyclotomic divisor appears each time.  To make
the first `M` complements units one must pass to

`A_M=A[(1-U_1)^(-1),...,(1-U_M)^(-1)]`;                          `(SU13)`

the unit rank and divisor set then grow with `M`, and the union is not a finitely generated
domain.  This is precisely why the effective unit-equation theorem over finitely generated
domains—see [Evertse--Gyory, *Effective results for unit equations over finitely generated
domains*](https://arxiv.org/abs/1107.5756)—cannot be applied uniformly to `(SU8)`.

Quantitative Subspace-Theorem and logarithmic-form bounds require additional arithmetic data.
For fixed multiplicatively independent algebraic numbers `alpha,beta`, Baker theory gives, for
`B=max(3,|p|,|q|)`, a bound of the shape

`0<|alpha^p*beta^q-1| ==> -log|alpha^p*beta^q-1|<=C_(alpha,beta)*log B`. `(SU14)`

This would control the next partial quotient.  It is unavailable for `(SU3)`, because the
generator `e` and, in the terminal branch, normally `y`, are transcendental over `Q` even though
they are algebraic over `F`.  A raw number-field product formula would give only
`-log|1-U_n|=O(h(U_n))=O(q_n)`, while the usual Subspace-Theorem threshold is
`H(U_n)^(-epsilon)=exp(-Omega(q_n))`.  The generic continued-fraction value
`q_(n+1)^(-1)` is only inverse-polynomial in `q_n`, far above that threshold; no strict exponent
is present.

Specialization cannot insert the missing hypotheses.  After choosing a finitely generated
`Z`-domain `R subset F` and its integral closure in `K`, a closed point sends `e,y,b` to algebraic
numbers and preserves `(SU10)--(SU11)`.  It does not preserve

`e=exp_C(1)`, `y=exp_C(b)`, or
`|e^(-p_n)y^(q_n)-1|=exp(-log q_(n+1)+O(1))`.                     `(SU15)`

The integers `(p_n,q_n)` were chosen from the continued fraction of the original selected real
number `b`; after specialization they have no relation to the logarithm ratio of the algebraic
images.  Applying effective unit equations to each closed point therefore proves a theorem about
different generators, while choosing a new point for each `n` loses the fixed number field and
fixed height constants.  Conditions `(SU15)` are archimedean inequalities, not identities in the
finite-type model.

The mixed stress is literal.  Under a hypothetical dependence in `K=Q(e,log 2)`, take

`b=log 2`, `y=2`, `U_n=e^(-p_n)*2^(q_n)`.                         `(SU16)`

Equations `(SU4)--(SU6)` hold and every `U_n` already lies in the hypothetical
transcendence-degree-one field.
Yet `(SU9)` says that the complements generate infinite multiplicative rank.  The algebraicity
of the second generator `2` does not help because the first generator is `e`; Baker's algebraic-
generator hypothesis still fails.

For a purely imaginary stable terminal direction, write `b=I*theta` and
`y=exp(I*theta)`.  Since the terminal complement is Q-linearly independent from the anchored
period, `alpha=theta/(2*pi)` is irrational.  If `k_n/q_n` are its convergents, then

`epsilon_n=q_n*theta-2*pi*k_n`, `V_n=y^(q_n)=exp(I*epsilon_n)`,
`-log|V_n-1|=log q_(n+1)+O(1)`, `h(V_n)=q_n*h(y)`.                `(SU17)`

The radial generator `e` cannot aid approximation because `|e^p*y^q|=e^p`, so convergence to one
forces `p=0`.  The same ESS argument makes `<1-V_n>` infinite rank.  The condition `|y|=1` holds
only at the selected embedding and is not preserved by algebraic specialization; Kronecker's
root-of-unity theorem would require integrality and modulus one at every conjugate.  The exact
period boundary `b=omega`, `y=1` is different: it is the allowed kernel direction and produces
no dense nontorsion unit-circle subgroup.

There is a sharp one-variable specialization counterfeit.  Choose a transcendental
`t in C` with `|t|=1` and irrational argument, embed `Q(T)` by `T |-> t`, and use convergent
denominators `q_n` of `arg(t)/(2*pi)`.  Then

`T^(q_n) in Q(T)^*`, `|t^(q_n)-1| -> 0`,
`1-T^(q_n)=product_(d|q_n)Phi_d(T)`.                              `(SU18)`

It has exactly the unit-circle proximity, linear function-field height, moving complement
divisors, and specialization loss above, in transcendence degree one.  It is not an exponential
counterexample; it proves that finite rank, one complex dense orbit, function-field heights, and
all exact unit-equation theorems are jointly compatible with the terminal approximation package.

**Audited conclusion.**  The route yields the substantive theorem `(SU9)`: the additive
complements of the continued-fraction orbit necessarily have infinite multiplicative rank.  That
is the opposite of the hypothesis needed by `S`-unit and Subspace theorems.  Stable minimality
puts those complements in one finite algebraic extension but supplies no fixed unit group, fixed
divisor set, exact inhomogeneous equation, or specialization preserving the selected exponential
smallness.  No transcendence unit is forced back into the deletion field.

### K-theory regulators either recover the logarithm or add a higher period

Retain the conjugation-stable terminal extension

`K=F(b,y)`, `[K:F]<infinity`, `y=exp(b)`,                        `(KT1)`

with the canonical elements `e,omega` already in `F`.  Algebraic `K`-theory first requires a
choice of coefficient field.  Over `K` every symbol below is defined, but this has already
adjoined the terminal numbers `b,y`; over a number field the Borel and unit-lattice theorems
apply, but neither `F` nor `K` is a number field in the positive terminal branch.

At weight one there is no hidden operation.  For a field, `K_1(K)=K^*`, and at the selected
complex embedding the Deligne regulator is simply

`r_D:K_1(C)=C^* -> C/(omega*Z)`, `r_D(u)=Log(u) mod omega*Z`.     `(KT2)`

Thus in the real sector

`b in R`, `y>0`: `r_D(y)=b`;                                    `(KT3)`

in the imaginary sector

`b=I*t`, `|y|=1`: `r_D(y)=I*t mod omega*Z`.                      `(KT4)`

The regulator has recovered the input, not a new algebraic coordinate.  Complex conjugation
does not double it: in the real sector `conj(y)=y`, while in the imaginary sector
`conj(y)=y^(-1)` and the two classes sum to zero.  The canonical period is exactly the ambiguity
in `(KT2)`; `exp(omega)=1` maps to the zero `K_1` class rather than to a second regulator vector.
Dirichlet's logarithmic regulator becomes a lattice only for the units of a number field and uses
all its archimedean embeddings.  The one selected embedding of the finitely generated field in
`(KT1)` supplies no such discreteness.

At weight two, Matsumoto's presentation is

`K_2^M(K)=(K^* tensor K^*)/<a tensor (1-a)>`,
`{a,1-a}=0`.                                                     `(KT5)`

Consequently the exact objects from the dense-unit route collapse:

`U_n=e^(-p_n)*y^(q_n)`, `0!=U_n!=1`,
`{U_n,1-U_n}=0 in K_2(K)`.                                      `(KT6)`

Corestriction to `F` sends `(KT6)` to zero.  Its `dlog` image is also tautologically zero,
because `dlog(U_n)` and `dlog(1-U_n)` are proportional to `dU_n`.  The infinite multiplicative
rank of the complements proved in `(SU9)` is therefore killed, not exploited, by the Steinberg
relation.

Other symbols do not measure ordinary transcendence degree.  In `Q(T)`, the tame symbol at
`T=0` of

`{T,2} in K_2^M(Q(T))` is `2^(-1) in Q^*`;                      `(KT7)`

hence `{T,2}` is nonzero although the coefficient field has transcendence degree one.  Conversely
`{T,1-T}=0` with both entries nonconstant.  The symbol `{e,y}` in `(KT1)` may similarly be
nonzero, but nonvanishing detects a multiplicative/tame-symbol obstruction, not a second
algebraically independent field generator.  In the unit-circle sector

`{y,conj(y)}={y,y^(-1)}=-{y,y}`                                 `(KT8)`

is zero after tensoring with `Q`, since `{y,y}=-{y,-1}` is two-torsion.  Conjugation again supplies
no second rational class.

Bloch symbols live one weight higher and must not be confused with `(KT5)`.  The pre-Bloch group
is generated by `[z]`, while the Bloch group is the kernel, modulo five-term relations, of

`delta([z])=z wedge (1-z)`.                                     `(KT9)`

Although `{z,1-z}=0` in `K_2`, a single `[z]` generally does **not** lie in the Bloch group,
because the wedge in `(KT9)` need not vanish.  The five-term relation in one standard convention
is

`[x]-[z]+[z/x]-[(1-x^(-1))/(1-z^(-1))]+[(1-x)/(1-z)]=0`.        `(KT10)`

Putting `x=U_n,z=U_m` leaves `U_m/U_n` in the rank-two group, but the last two arguments contain

`(1-U_n)/(1-U_m)`.                                               `(KT11)`

By `(SU9)` these complement ratios cannot be confined to a fixed finite-rank group.  Thus the
five-term relation repackages exactly the objects that escaped the `S`-unit theorem; it does not
send them back to `F`.

The regulator is equally explicit.  For an embedding in `C`, the Bloch--Wigner function is

`D(z)=Im(Li_2(z))+log|z|*arg(1-z)`,                              `(KT12)`

and it annihilates `(KT10)`.  In the real terminal sector every `U_n` and `1-U_n` is real, so

`D(U_n)=D(1-U_n)=0`.                                             `(KT13)`

On the infinite subsequence with `0<U_n<1`, Euler's identity reads

`Li_2(U_n)+Li_2(1-U_n)`
` =pi^2/6-Log(U_n)*Log(1-U_n)`,                                  `(KT14)`

where `(SU4)--(SU5)` give

`Log(U_n)=O(1/q_(n+1))`, `Log(1-U_n)=-log q_(n+1)+O(1)`,
`Log(U_n)*Log(1-U_n)=O(log(q_(n+1))/q_(n+1))`.                   `(KT15)`

The two dilogarithms and `Log(1-U_n)` are new analytic values; none is an element of `K` merely
because its argument is.  For `U_n>1`, branch continuation adds multiples of `omega` and the same
external logarithm.  Hence `(KT14)` gives a small regulator identity, not an arithmetic element
of the terminal field.

In the imaginary sector, with `V_n=exp(I*epsilon_n)` from `(SU17)`, the regulator is the Clausen
function.  Its derivative and small-angle asymptotic are

`d/dtheta D(exp(I*theta))=-log|2*sin(theta/2)|`,
`D(V_n)=epsilon_n*(1-log|epsilon_n|)+O(epsilon_n^3)`
`      =O(log(q_(n+1))/q_(n+1))`.                               `(KT16)`

This value can be nonzero, but it is a new weight-two period.  Conjugation gives
`D(conj(V_n))=-D(V_n)`: the invariant combination cancels and the anti-invariant combination
doubles the external period.  No functional equation makes it algebraic over `F` or `K`.

The actual Borel theorem has a different base.  For a number field `L` with `r_2` complex pairs,
the Bloch/Borel regulator on `K_3(L)_ind` has rank `r_2` and its covolume is related to
`zeta_L(2)`.  Suslin's precise bridge between `K_3^ind` and the Bloch group is recorded in
[*K_3 of a field and the Bloch group*](https://www.maths.dur.ac.uk/users/herbert.gangl/Suslin_K3_Bloch_group.pdf),
and a standard regulator reference is [Bloch, *Higher Regulators, Algebraic K-Theory, and Zeta
Functions of Elliptic Curves*](https://bookstore.ams.org/CRMM/11).  Regulator nonvanishing is
compatible even with transcendence degree zero.  If `zeta_6=exp(pi*I/3)`, then

`1-zeta_6=zeta_6^(-1)`, so `delta([zeta_6])=0`,
`[zeta_6] in B(Q(sqrt(-3)))`, `D(zeta_6)>0`.                     `(KT17)`

This is a genuine nonzero Bloch regulator over an algebraic number field.  It proves that a
nonzero higher regulator creates a real period value outside the coefficient field; it does not
force positive ordinary transcendence degree of that field.

Regulators on an algebraic curve require still more global data.  If `C/Qbar` is smooth and
`f,g in Qbar(C)^*`, the symbol belongs to tame `K_2(C)` only when every tame symbol

`partial_x{f,g}=(-1)^(ord_x(f)*ord_x(g))*`
`  (f^(ord_x(g))/g^(ord_x(f)))(x)`                               `(KT18)`

is one.  On that kernel, the real regulator pairs with a cycle `gamma` through

`integral_gamma eta(f,g)`,
`eta(f,g)=log|f|*d arg(g)-log|g|*d arg(f)`.                       `(KT19)`

For the terminal locus the rational functions representing `b,y` generally have nontrivial tame
symbols.  More fundamentally, `y=exp(b)` holds at one selected complex generic point, not as an
identity of rational functions on `C`; hence `(KT19)` does not simplify to an exponential
differential.  Correcting the tame symbols introduces additional functions and divisor points,
and specializing a model over the transcendental base `F` to `Qbar` destroys the selected graph
identity.

Mahler measure gives the same one-variable saturation by Jensen's formula:

`m(Z-y)=log max(1,|y|)`.                                        `(KT20)`

For `y=exp(b)>0`, this is `max(0,b)`; for `|y|=1`, it is zero.  The polynomial has already used
the terminal value `y` as a coefficient.  If instead one starts with an integral polynomial,
regulator formulas can produce genuinely new `L`-values—for example

`m(1+X+Y)=(3*sqrt(3)/(4*pi))*L(chi_(-3),2)`—                     `(KT21)`

but `(KT21)` is an external period attached to a rational curve polynomial, not a field element
forced into `K`.  A hypothetical rational relation `P(e,log 2)=0` likewise defines a curve, yet
its Mahler measure averages `P` on the full unit torus; the selected point `(e,log 2)` lies off
that torus.  In the general terminal branch the minimal equations have coefficients in `F`, so
forming their Mahler measure has already imported the entire deletion field.

The two low-dimensional stresses now close exactly.  For `(1,log 2)`, the output units are
`(e,2)` and

`r_D(e)=1`, `r_D(2)=log 2`;                                     `(KT22)`

the regulator simply returns the two inputs.  Possible nonvanishing of `{e,2}` is compatible
with a transcendence-degree-one field by the symbolic model `{T,2}` in `(KT7)`.  For
`(log 2,omega)`, the output units are `(2,1)`: their regulators are `(log 2,0)`, the period is the
kernel ambiguity, and `{2,1}=0`.  For the adjacent-period pair with repeated value `(e,e)`, there
is only one `K_1` class and `{e,e}` is rationally zero.  None of these ranks contains the missing
algebraic-independence unit.

Finally, transfer cannot select the desired embedding.  Regulator compatibility with
`K/F`-corestriction sums over every extension embedding, just as `(SU11)` does for the norm.  In
particular the transfer of `(KT6)` is zero, while transferring a genuine `K_3` or curve class
sums its dilogarithmic/regulator values over all conjugates.  A lower bound at the one embedding
where `y=exp(b)` is not recovered from that sum.

**Audited conclusion.**  `K_1` gives exactly `(b mod omega)`, Steinberg symbols annihilate the
new complement pairs, Bloch five-term identities import their infinite-rank ratios, and nonzero
Bloch/Borel or curve regulators live in external logarithmic, dilogarithmic, or `L`-value period
spaces.  The sharp models `(KT7)`, `(KT17)`, and `(KT20)--(KT21)` show that regulator
nonvanishing and exact functional equations coexist with coefficient fields of transcendence
degree zero or one.  An injectivity theorem converting these regulator values into ordinary
algebraic independence over the transcendental base `F` would be a new period conjecture, not an
unconditional consequence of algebraic `K`-theory.

### Exponential dynamics propagates ecl but not terminal field algebraicity

Let `f(z)=exp(z)` and start with the positive canonical terminal alternative

`F=Q(v,exp(v))`, `K=F(b,y)`, `y=exp(b)`, `[K:F]<infinity`,
`omega=2*pi*I in F`.                                             `(DY1)`

Write `x_0=b`, `x_1=y`, and `x_(n+1)=f(x_n)`.  The exact orbit-field tower is

`L_1=K`, `L_(n+1)=L_n(exp(x_n))` for `n>=1`.                    `(DY2)`

Terminal algebraicity controls only the first arrow: `L_1/F` is finite.  At the next step

`x_2=exp(y)=exp(exp(b))`                                        `(DY3)`

is not in `K` by any consequence of `(DY1)`.  Each later adjunction has relative transcendence
degree zero or one, but there is no unconditional lower bound selecting one of these alternatives.
If `x_2` happens to be algebraic over `K`, transitivity merely makes it algebraic over `F`; it
does not contradict Hermite--Lindemann because the fully transcendental terminal value `y` is
not algebraic over `Q`.

There is one propagation statement, but it is purely closure-theoretic.  Pure-field algebraicity
puts `b in ecl_C(F)`, and `ecl_C(F)` is an exponential subfield.  Consequently

`x_n in ecl_C(F)` for every `n>=0`.                              `(DY4)`

Thus the whole forward orbit has exponential-closure rank zero over `F`, even if its ordinary
transcendence degree over `F` grows without bound.  This is exactly the closure/ordinary-degree
separation of `(CLX11)--(CLX20)`, not new arithmetic information.

The backward orbit loses even less at its first level.  Since the complex exponential has kernel
`omega*Z`,

`f^(-1)(y)={b+k*omega:k in Z} subset K`.                        `(DY5)`

The canonical period anchor makes an infinite inverse fiber live in the same finite extension.
For the next inverse level one must solve `exp(z)=b+k*omega`; its branches
`Log(b+k*omega)+j*omega`, `j in Z`, are not forced into `K`.  Hence backward iteration has the
same sharp boundary as forward iteration: the given graph arrow and its period translates are
retained, while the next genuinely new logarithm or exponential leaves the terminal field.

The Lambert stress makes `(DY2)--(DY3)` completely explicit.  Let

`beta=-2*W_0(1/2)`, `exp(beta)=beta^2`.                           `(DY6)`

Since `-1<beta<0`, its real forward orbit satisfies

`x_0=beta`, `x_1=beta^2 in (0,1)`,
`x_2=exp(beta^2) in (1,e)`, `x_(n+1)=exp(x_n)`.                  `(DY7)`

For `n>=2`, `x_(n+1)>x_n+1`, so the orbit escapes to positive infinity.  The first unknown value
is already

`x_2=exp(beta^2)`.                                               `(DY8)`

No standard transcendence theorem proves even that `(DY8)` is transcendental.  Schanuel applied
to the Q-linearly independent pair `(beta,beta^2)` would prove the stronger statement that
`beta` and `x_2` are algebraically independent, because

`Q(beta,beta^2,exp(beta),exp(beta^2))=Q(beta,x_2)`.              `(DY9)`

Hermite--Lindemann cannot be iterated here: its input at the second step, `beta^2`, is
transcendental.  The first inverse fiber is equally saturated:

`f^(-1)(beta^2)=beta+omega*Z subset Q(beta,omega)`.              `(DY10)`

The analytic multiplier records escape but no arithmetic.  For every starting point,

`(f^n)'(x_0)=product_(j=1)^n x_j
             =exp(sum_(j=0)^(n-1)x_j)`.                         `(DY11)`

At `beta` this multiplier eventually grows extremely rapidly.  It belongs to the field generated
by the orbit segment and introduces no discrete norm, height, or new algebraic relation.

Periodic dynamics gives a sharp actual-exponential obstruction to any general orbit-growth
claim.  The fixed points are

`alpha_k=-W_k(-1)`, `exp(alpha_k)=alpha_k`.                      `(DY12)`

Every `alpha_k` is transcendental by Hermite--Lindemann, and it is a nonsingular
parameter-free Khovanskii point because

`(exp(X)-X)'|_(alpha_k)=alpha_k-1!=0`.                           `(DY13)`

Nevertheless its complete forward orbit is the singleton `{alpha_k}` and its graph field is
`Q(alpha_k)`, of transcendence degree one.  Distinct fixed points are pairwise Q-linearly
independent: if `alpha_l=(a/b)*alpha_k`, equality of
`exp(b*alpha_l)=alpha_l^b` and `exp(a*alpha_k)=alpha_k^a` forces
`alpha_k^(a-b)=(a/b)^b`, hence either algebraicity or equality.  Algebraic independence of two
fixed points is again exactly their two-variable Schanuel instance.

More generally, put

`G_(m,n)(z)=f^(m+n)(z)-f^m(z)`.                                 `(DY14)`

If `z` becomes periodic after `m` steps and the multiplier `mu` of the resulting `n`-cycle is
not one, then

`G_(m,n)'(z)=(f^m)'(z)*(mu-1)!=0`.                              `(DY15)`

Such a preperiodic point is another parameter-free nonsingular exponential-algebraic point.
The equation gives local isolation and a finite orbit, not ordinary algebraicity.  At a parabolic
cycle `mu=1`, this particular equation is multiple; complex dynamics still supplies no
arithmetic replacement for the missing Jacobian.

Nevanlinna growth sees the opposite, global side of the same map.  With the standard
characteristic,

`T(r,exp)=r/pi`,
`log T(r,exp o exp)=r+O(log r)`.                                 `(DY16)`

The second estimate follows directly by integrating
`max(Re(exp(r*exp(I*theta))),0)`: it is at most `exp(r)` and on an arc of width comparable to
`1/r` around zero it is at least a constant times `exp(r)`.  Higher iterates have tower-like
growth, and value distribution counts increasingly many global inverse branches.  But
Nevanlinna characteristic has no coefficient field and does not attach an arithmetic trace to a
chosen branch.  The fixed points `(DY12)` and the one-field inverse fiber `(DY10)` show that
global abundance and local field growth are independent.

Arithmetic dynamical heights are unavailable for exactly structural reasons.  The
Call--Silverman construction applies to polarized algebraic self-maps, for example a rational map
of degree `d>=2`, and uses

`hat h_phi(P)=lim_(n->infinity) d^(-n)*h(phi^n(P))`,
`hat h_phi(phi(P))=d*hat h_phi(P)`.                              `(DY17)`

See the standard [arithmetic-dynamics
notes](https://swc-math.github.io/aws/2010/2010SilvermanNotes.pdf).  The exponential map has an
essential singularity at infinity and is not a rational self-map of `P^1`; there is no algebraic
degree, polarized line bundle, or Weil-height functional equation behind `(DY11)`.  Moreover the
selected terminal point is over a finitely generated transcendental field and the analytic map
`exp_C` is not a rational map of an arithmetic model of that field.  Dynamical Mordell--Lang,
Northcott, and canonical-height specialization therefore have no object to which they apply.

Polynomial dynamics gives two exact comparison models.  First, `P(z)=z^2` agrees with `f` at the
first Lambert step,

`P(beta)=beta^2=f(beta)`,                                       `(DY18)`

but then `P^2(beta)=beta^4` remains in `Q(beta)`, whereas
`f^2(beta)=exp(beta^2)` is the open value `(DY8)`.  The isolated algebraic correspondence
`Y=X^2` controls one step only.  Second, over the function field `Q(T)`,

`P^n(T)=T^(2^n) in Q(T)`, `hat h_P(T)=1`.                       `(DY19)`

The canonical height is positive and degrees grow like `2^n`, yet the field generated by the
entire orbit has ordinary transcendence degree one.  Thus even when an algebraic dynamical height
exists and is positive, it measures divisor/height growth rather than acquisition of new
transcendence-basis elements.

Holomorphic specialization fails at precisely the terminal intersection.  The universal beta
family is

`b(s)=s`, `y(s)=s^2`, `H(s)=exp(s)-s^2`.                        `(DY20)`

At `s=beta`, `H(beta)=0` and `H'(beta)=beta*(beta-2)!=0`, so the graph and algebraic
correspondence meet transversely at one parameter.  Generically, Ax's differential theorem
applied to the Q-linearly independent functions `s,s^2` gives the exact functional statement

`trdeg_C C(s,exp(s),exp(s^2))=3`.                               `(DY21)`

At the selected point, `exp(s)` specializes to `beta^2` and the remaining field is just
`Q(beta,exp(beta^2))`, whose degree is the open alternative `(DY9)`.  Functional independence
therefore does not specialize through a single transverse zero.

The same mechanism holds for `(DY1)`.  After spreading `F`, `b`, and `y` over a finite-type
parameter space, algebraic recovery gives local algebraic branches `b(s),y(s)`.  The function

`H(s)=exp_C(b(s))-y(s)`                                         `(DY22)`

vanishes at the selected complex parameter but need not vanish on any germ.  If it did vanish
identically along a positive-dimensional germ, functional Ax--Schanuel could constrain that
family.  A terminal point supplies only one zero, exactly as `(DY20)`.  Specializing the
finite-type model at algebraic parameters preserves the algebraic recovery equations but not
`H=0`, and there is no algebraic branch representing `exp(y(s))` for the next iterate.

**Audited conclusion.**  Finite terminal algebraicity propagates to all period translates of
the first inverse fiber and to the entire orbit only inside `ecl`, as `(DY4)--(DY5)`; it does not
propagate as ordinary algebraicity past `x_1`.  At `beta`, the first new iterate is the open
number `exp(beta^2)`, while the orbit is analytically escaping and has rapidly growing
multipliers.  Actual fixed points show that exponential-algebraic periodic orbits can remain in
one transcendence-degree-one field, and polynomial models show that even positive canonical
height and exponential degree growth do not force field growth.  Nevanlinna theory counts the
global divisor, and holomorphic families give generic functional independence, but neither
supplies an arithmetic specialization theorem at the isolated terminal parameter.  Any theorem
forcing `x_2` to leave `K` would already contain a new relative exponential-value statement; in
the Lambert stress it would address the exact Schanuel boundary `(DY9)`.

### The cross-sector deficit is a common differential, not necessarily a common subfield

The checked sector endpoint admits one further exact interpretation.  Retain the notation of
`(CS10)--(CS14)` and write

`K_+=F_+`, `K_-=F_-`, `K=K_+*K_-`, `m=r+s`.                     `(KD1)`

For finitely generated characteristic-zero fields, the natural maps

`K tensor_(K_+) Omega_(K_+/Q) -> Omega_(K/Q)`,
`K tensor_(K_-) Omega_(K_-/Q) -> Omega_(K/Q)`                    `(KD2)`

are injective.  One way to see this is to choose a transcendence basis of the smaller field over
`Q`; it remains algebraically independent in the larger field, and its differentials remain
linearly independent because all the extensions are separably generated in characteristic zero.
Let `U_+` and `U_-` be their images.  Since `K` is the compositum, its Kähler differentials are
generated by the two images, so

`U_+ + U_- = Omega_(K/Q)`,
`dim_K U_+ = td_Q K_+`, `dim_K U_- = td_Q K_-`.                  `(KD3)`

The newly checked CS12--CS14 theorem gives, when both sector complements are nonzero,

`dim_K U_+ >= r`, `dim_K U_- >= s`, `dim_K Omega_(K/Q)=r+s-1`.

Consequently

`dim_K(U_+ intersection U_-)
 =td_Q K_+ + td_Q K_- - td_Q K >= 1`.                            `(KD4)`

Thus the missing cross-sector unit can be represented by a nonzero rational differential that is
simultaneously a `K`-linear combination of real-sector differentials and a `K`-linear combination
of anti-fixed-sector differentials.  This is stronger than merely saying that some polynomial
mixes the two sets of generators, but it is weaker than a common transcendental element.

Conjugation does make the overlap real, but only after allowing coefficients from `K`.  The
involution preserves both `U_+` and `U_-`.  If `0!=alpha` lies in their intersection, then either
`alpha+conj(alpha)` is a nonzero fixed form, or `conj(alpha)=-alpha`; in the latter case
`omega*alpha` is nonzero and fixed because `conj(omega)=-omega`.  Hence

`(U_+ intersection U_-)^(conj=1) != 0`.                          `(KD5)`

There is no valid inference from `(KD5)` to
`td_Q(K_+ intersection K_-)>0`.  The sharp finite-cover example is

`E=Q(t)`, `A=Q(t^2)`, `B=Q(t^2+t)`.                              `(KD6)`

Both `A` and `B` have transcendence degree one, their compositum is `E` because
`t=(t^2+t)-t^2`, and the two differential images are the whole one-dimensional space:

`E*d(t^2)=E*dt=E*d(t^2+t)=Omega_(E/Q)`.                          `(KD7)`

Nevertheless `A intersection B=Q`.  Indeed an element of the intersection is invariant under
both involutions `sigma(t)=-t` and `tau(t)=-1-t`.  Their generated group contains the translation
`t -> t+1`.  A rational function over a characteristic-zero field invariant under a nonzero
translation is constant: any finite pole would acquire infinitely many translates, and a
pole-free rational function is a polynomial whose finite difference can vanish only when it is
constant.  Thus even maximal differential overlap can come from two finite covers with no common
nonconstant quotient.

The coefficient field is the precise loss.  In `(KD7)`, for example,

`dt=(1/(2*t))*d(t^2)=(1/(2*t+1))*d(t^2+t)`,                      `(KD8)`

and neither coefficient belongs to the corresponding smaller field.  The stable exponential
setting has the same issue.  If `x` is fixed and `u,y=exp(u)` are anti-fixed/reciprocal, then the
basic graph forms

`d(exp x)/(exp x)-dx`, `dy/y-du`

are respectively fixed and anti-fixed under conjugation, but a relation over `K` may mix them
using coefficients of the opposite parity.  Symmetrization produces `(KD5)` without making the
coefficients rational, constant, or internal to either sector.  Residue arguments rule out a
constant integral relation—this is the already checked proper-rotundity information—but not a
relation with rational-function coefficients such as `(KD8)`.

**Audited conclusion.**  The exact sector deficit always yields a nonzero conjugation-fixed
common Kähler direction.  Algebraic geometry alone cannot turn it into a common transcendence
parameter or an algebraic-disjointness contradiction: finite covers already realize full
differential overlap with trivial field intersection.  A successful continuation must therefore
force coefficient descent for this particular exponential/logarithmic common form, using an
arithmetic property absent from general function fields.  Merely invoking separability,
conjugation, closedness of logarithmic forms, or common-field intersection repeats `(KD6)--(KD8)`.

### The imaginary sector has an explicit real quadratic quotient

The cross-sector problem can be made entirely real without losing a transcendence unit.  Choose
the anti-fixed basis in `(CS11)` as

`u_0=omega, u_1,...,u_q`,  `v_j=exp(u_j)`,                        `(RQ1)`

so `conj(u_j)=-u_j`, `conj(v_j)=v_j^(-1)`, and `v_0=1`.  Put

`B=Q(u_0,...,u_q,v_0,...,v_q)`, `B_0=B intersection R`.          `(RQ2)`

For `j>=1` define the fixed real quantities

`a_j=u_j/omega`,
`c_j=v_j+v_j^(-1)`,
`d_j=(v_j-v_j^(-1))/omega`.                                      `(RQ3)`

Then there is an exact fixed-field presentation

`B_0=Q(omega^2,a_j,c_j,d_j : 1<=j<=q)`,
`B=B_0(omega)`, `[B:B_0]=2`.                                    `(RQ4)`

Indeed the field on the right of the first line is real and

`u_j=a_j*omega`, `v_j=(c_j+omega*d_j)/2`.                         `(RQ5)`

It therefore generates `B` after adjoining `omega`.  Conversely all its displayed generators
belong to `B` and are fixed by conjugation.  Since it is a subfield of `R`, it cannot contain the
nonreal number `omega`; but `omega^2` is already present.  Thus adjoining `omega` has degree two,
and the unique decomposition `r+s*omega` shows that its conjugation-fixed field is precisely the
field in `(RQ4)`.  Notice also the intrinsic relations

`c_j^2-omega^2*d_j^2=4`.                                         `(RQ6)`

Writing `u_j=I*theta_j` gives the more transparent real description

`a_j=theta_j/(2*pi)`, `c_j=2*cos(theta_j)`, `d_j=sin(theta_j)/pi`,
`B_0=Q(pi^2,theta_j/pi,cos(theta_j),sin(theta_j)/pi : j>=1)`.     `(RQ7)`

Let `A=F_+`, which is already pointwise real, and let `E=A*B`.  Equations `(RQ4)--(RQ5)` give

`E=(A*B_0)(omega)`, `E intersection R=A*B_0`,
`td_Q E=td_Q(A*B_0)`, `td_Q B=td_Q B_0`.                         `(RQ8)`

The fixed-field identity follows because `A*B_0` is real, contains `omega^2`, and adjoining the
nonreal square root `omega` again has degree two.  Hence `(CS12)--(CS14)` become the wholly real
boundary

`td_Q A>=r`, `td_Q B_0>=s`, `td_Q(A*B_0)=r+s-1`.                 `(RQ9)`

For `r=s=1`, this is exactly the dependence boundary between `A=Q(e)` and
`B_0=Q(omega^2)=Q(pi^2)`.  For larger imaginary sectors, `(RQ7)` shows what additional structure
is actually available: normalized angles and their sine/cosine values, with the conic identities
`(RQ6)`.  Passing to the real fixed field is therefore lossless, but does not by itself produce
the missing unit.  Any proposed real-analytic or ordered-field argument must prove a genuine
arithmetic disjointness theorem between the two explicit fields in `(RQ9)`; definability alone
still permits dependence at a named point.

The field-generation and transcendence-degree parts of this reduction are now checked in Lean.
`antiFixedRealCore` is generated by the four classes in `(RQ3)--(RQ4)` (including the squared
period); each generator is proved fixed by conjugation, and the whole core is contained in the
pointwise-fixed intermediate field.  The reconstruction formula proves

`generatedField(u)=antiFixedRealCore(u)*Q(omega)`,
`td_Q generatedField(u)=td_Q antiFixedRealCore(u)`.               `(RQ10)`

The second equality remains true after compositing with an arbitrary intermediate field.  Its
specialization to the distinguished sector bases combines with the checked CS12--CS14 theorem to
give exactly `(RQ9)` with `B_0` replaced by the definitionally explicit `antiFixedRealCore`.
Thus the passage to two real fields is not merely prose bookkeeping: the generator identities,
algebraic period adjunction, and exact one-unit real-compositum deficit are kernel-checked.

There is a further lossless simplification.  From `(RQ6)`, every normalized skew trace satisfies

`d_j^2=(c_j^2-4)/omega^2`.                                       `(RQ11)`

Define the even core

`B_ev=Q(omega^2,a_j,c_j : 1<=j<=q)`
`    =Q(pi^2,theta_j/pi,cos(theta_j) : 1<=j<=q)`.                 `(RQ12)`

The first equality with `pi^2` is literal, not just transcendence-degree notation:

`omega^2=-4*pi^2`, `Q(omega^2)=Q(pi^2)`.                         `(RQ12a)`

Both the numerical identity and the equality of the two generated intermediate fields are now
checked in Lean.  In the singleton imaginary sector `u=(omega)`, the normalized-input and trace
generators are `1` and `2`, so the stronger field identity

`antiFixedEvenCore(omega)=Q(omega^2)=Q(pi^2)`                    `(RQ12b)`

is checked directly as well.

Combining `(RQ12b)` with the already checked singleton positive field gives an exact real anchor
field

`F_anchor,real=Q(exp(1))*Q(pi^2)=Q(e,pi^2)`,
`td_Q generatedField(canonicalAnchor)=td_Q F_anchor,real`.        `(RQ12c)`

This compositum identity and transcendence-degree equality are now checked in Lean.  Consequently
the zero-complement sector case is literally the `Q(e,pi^2)` degree question, with no remaining
complex period, phase, trace, or auxiliary generator.  The same formal package proves the sharp
upper bound and equivalence

`td_Q F_anchor,real<=2`,
`Bound(canonicalAnchor) iff td_Q Q(e,pi^2)=2`.                    `(RQ12d)`

Writing the two generators as the literal ordered tuple `(pi^2,e)`, the field-generation proof
now also identifies the transcendence-degree assertion with algebraic independence:

`td_Q Q(e,pi^2)=2 iff AlgebraicIndependent_Q(pi^2,e)`,
`Bound(canonicalAnchor) iff AlgebraicIndependent_Q(pi^2,e)`.      `(RQ12e)`

Moreover the real anchor degree is always exactly one or two, so its complementary endpoint is

`td_Q Q(e,pi^2)=1 iff not AlgebraicIndependent_Q(pi^2,e)`.        `(RQ12f)`

Then `B_0/B_ev` is algebraic (indeed generated by finitely many quadratic elements), so

`td_Q B_0=td_Q B_ev`,
`td_Q(A*B_0)=td_Q(A*B_ev)`.                                      `(RQ13)`

Both equalities, including the arbitrary-compositum version of the second, are now checked in
Lean.  Combining them with CS12--CS14 yields the minimal-generator real endpoint

`td_Q A>=r`, `td_Q B_ev>=s`, `td_Q(A*B_ev)=r+s-1`.               `(RQ14)`

The normalized imaginary inputs retain the full rational independence of the anti-fixed basis:

`1,a_1,...,a_q are Q-linearly independent, and all lie in B_ev`. `(RQ15)`

Indeed multiplication by the nonzero scalar `omega^(-1)` is an injective `Q`-linear map on
`C`, and it carries `(u_0,...,u_q)` to `(1,a_1,...,a_q)`.  This statement, including membership
in the even core, is now checked in Lean.  Thus `(RQ14)` does not discard the input-side
independence needed by any prospective cosine-field theorem.

Finally, the real anchor identity propagates through the checked global terminal equivalence.
If `PositiveStableTerminal` denotes the existing positive-complement branch, then Lean now proves

`not Schanuel`
` iff td_Q Q(e,pi^2)=1 or PositiveStableTerminal`.               `(RQ16)`

Using `(RQ12f)`, the same kernel-checked equivalence has the fully explicit form

`not Schanuel`
` iff not AlgebraicIndependent_Q(pi^2,e) or PositiveStableTerminal`. `(RQ16a)`

The second disjunct is unchanged and carries all of the stable deletion and algebraic-extension
data proved earlier.  Equation `(RQ16)` replaces only the zero-complement branch, but does so
literally: a global failure terminates either at the exact real `e`--`pi^2` boundary or at the
positive stable witness to which `(RQ14)--(RQ15)` apply.

For the positive branch, the global equivalence now retains the least-arity hypothesis rather
than discarding it:

`not Schanuel`
` iff not AlgebraicIndependent_Q(pi^2,e) or PositiveLeastStableFailure`. `(RQ17)`

Here `PositiveLeastStableFailure` includes positive complementary arity, linear independence,
the literal canonical anchor, conjugation stability, failure of the bound, and nonexistence of
any smaller stable anchored failure.  Lean then constructs distinguished sector bases from every
such witness, proves their two dimensions sum to the full input arity, and—whenever both have a
non-anchor direction—derives `(RQ14)` directly for their plus field and even imaginary core.
Thus the terminal equivalence no longer loses the minimality hypothesis needed by CS12--CS14;
the unresolved alternatives are the explicit pair boundary, a one-sided sector boundary, or the
two-real-field one-unit deficit already displayed in `(RQ14)`.

The sector classification and both one-sided endpoints are now literal as well.  Positivity of
the complementary arity makes exactly one of the following hold: only the fixed complement is
zero, only the anti-fixed complement is zero, or both are positive.  Reindexing the singleton
bases gives the field identities

`p=0 => F_+=Q(e), td_Q F_+=1`,
`q=0 => B_ev=Q(pi^2), td_Q B_ev=1`.                              `(RQ18)`

Here the second degree equality is backed by the newly exported checked theorem that `pi^2` is
transcendental (deduced from the checked transcendence of the standard period and
`omega^2=-4*pi^2`).  The even-core compositum deficit is now exported without any positivity
assumption.  Cardinal cancellation therefore gives the exact one-sided degrees

`p=0 => td_Q(Q(e)*B_ev)=q+1`,
`q=0 => td_Q(F_+*Q(pi^2))=p+1`.                                 `(RQ19)`

Thus all three positive-sector shapes have a kernel-checked real description.  What remains in
the one-sided cases is not bookkeeping loss: it is respectively the possibility that the large
even core is dependent with `e`, or that the large fixed graph field is dependent with `pi^2`.

The terminal algebraic extension now acts on every sector direction, not merely the selected
omitted original coordinate.  If `K_del` is the checked sharp scaled deletion field and
`x` belongs to the rational span of the full witness, Lean proves

`x is algebraic over K_del`,
`exp(x) is algebraic over K_del`.                                 `(RQ20)`

The first assertion uses literal membership of rational input combinations in the full graph
field and transitivity through the algebraic terminal extension.  For the second, one common
positive integral denominator puts the singleton scaled graph field inside the full field;
rational-scaling integrality then makes `exp(x)` algebraic, and restriction of scalars returns it
to `K_del`.  Specializing `(RQ20)` to every distinguished plus- and minus-sector basis vector is
exported explicitly.  The further specialization to the even core is also checked: `omega^2`,
every normalized imaginary input `u_i/omega`, and every trace
`exp(u_i)+exp(u_i)^(-1)` are algebraic over `K_del`.  Hence the positive terminal obstruction can
be stated entirely as a sharp
deletion field over which every real or purely imaginary basis direction and its exponential is
algebraic.  Also, the real pair `(pi^2,e)` is now checked algebraically independent exactly when
the earlier complex pair `(2*pi*I,e)` is, so the real reduction loses no information.

The scaled deletion field also absorbs the anchor more strongly than mere elementwise terminal
algebraicity suggests.  If its positive scale is `d`, its first two input generators are
`d*(1+omega)` and `d*(1+2*omega)`.  Their difference and division by the rational scalar give

`omega in K_del`, hence `pi^2 in K_del`.                          `(RQ21)`

The rational-scaling integrality theorem applied to the first unscaled anchor coordinate gives

`e is integral over K_del`.                                      `(RQ22)`

Thus the full explicit real anchor tuple `(pi^2,e)` is algebraic over every positive sharp
deletion field, with `pi^2` actually already inside that field.  This makes the remaining
positive branch a relative algebraicity configuration over a field that literally contains the
period square and differs from containing the entire real anchor only by a finite algebraic
adjunction of `e`.

The corresponding field tower is now exact in Lean.  Put

`K_anchor=Q(e,pi^2)`, `M=K_del*K_anchor`, `L=Q(w,exp(w))`.        `(RQ23)`

Adjoining the explicit pair `(pi^2,e)` to `K_del` is algebraic, so restriction of scalars and
the transcendence-degree tower give

`td_Q M=td_Q K_del=complementCount+2`.                            `(RQ23a)`

If `(pi^2,e)` is algebraically independent, then

`td_(K_anchor) M=complementCount`.                               `(RQ23b)`

For the original canonically anchored full witness, `K_anchor` is literally a subfield of `L`:
the period is the difference of the first two inputs, `pi^2` is a rational multiple of its
square, and `e` is their common exponential.  The same tower cancellation proves

`td_(K_anchor) L=complementCount`.                               `(RQ23c)`

Moreover `M<=L`, and terminal algebraicity of `L/K_del` implies that `L/M` is algebraic, hence

`td_M L=0`.                                                      `(RQ23d)`

This separates the only Kummer subtlety cleanly: `e` need not lie in the scaled deletion field,
but it is integral there; after adjoining it, the resulting field is literally intermediate in
the full anchored graph field.  Thus the positive endpoint is now an exact algebraic top
extension of relative degree `complementCount` over the entirely real anchor, not merely an
absolute-degree comparison.

The finite anchor step is quantitative as well.  Since `pi^2` is already in `K_del`, Lean proves
the literal restriction-of-scalars identity

`K_del*K_anchor = K_del(e)`.                                    `(RQ24)`

If `d>0` is the integer scale in the terminal deletion data, the first scaled anchored
exponential places `e^d` in `K_del`.  Hence the minimal polynomial of `e` divides
`X^d-e^d`, and the checked simple-extension bound is

`[K_del(e):K_del] <= d`.                                        `(RQ24a)`

Thus no unspecified finite extension is hidden in `(RQ23)`: the only missing anchor element is
one explicit Kummer root, with degree bounded by the actual denominator-clearing scale.

There is a stronger tuple-level normalization.  If `u` is the unscaled anchored deletion and
`d>0` is its common scale, define

`v_0=u_0`, `v_1=u_1`, and `v_i=d*u_i` for `i>=2`.                `(RQ25)`

Coordinatewise multiplication by nonzero rational units proves in Lean that `v` is linearly
independent and has exactly the same rational span as `u`; hence it remains conjugation-stable,
proper in the full span, and retains the omitted direction outside.  It also remains literally
canonically anchored.  On graph fields the checked identity is

`Q(v,exp(v))=K_del*Q(e,pi^2)=K_del(e)`.                          `(RQ25a)`

For the non-anchor coordinates this is tautological.  At the two anchor coordinates, the scaled
field contains the inputs and the powers `e^d`, while the unscaled anchored graph contributes
exactly `e`; conversely positive integer scaling turns each anchored exponential into the
corresponding power.  Consequently

`Q(v,exp(v)) <= Q(w,exp(w))`,
`td_Q Q(v,exp(v))=complementCount+2`,
`Q(w,exp(w)) / Q(v,exp(v)) is algebraic`.                        `(RQ25b)`

These facts are packaged in the new kernel-checked
`AnchorPreservingStableTerminalDeletionData`, and every positive least stable failure carries
such data.  Thus the terminal theorem can now be used with an honest smaller stable anchored
equality tuple whose graph field is literally included in the full field: neither a uniformly
scaled anchor nor a subsequent Kummer adjunction remains in the final normal form.

The new package is self-contained: without referring back to its construction, Lean derives

`td_Q Q(w,exp(w))=complementCount+2`, hence `DefectOne(w)`,
`td_(Q(e,pi^2)) Q(v,exp(v))=complementCount` if `(pi^2,e)` is independent, `(RQ26)`

and, for every `x` in the full rational input span, both `x` and `exp(x)` are algebraic over
`Q(v,exp(v))`.  Thus all later sector and terminal algebraicity arguments can start directly
from the honest anchored equality graph field rather than reconstructing it from scaled data.

Finally the global endpoint is exported in disjoint form:

`not Schanuel iff not AI_Q(pi^2,e)`
`  or (AI_Q(pi^2,e) and exists a positive least stable failure carrying`
`      AnchorPreservingStableTerminalDeletionData)`.             `(RQ27)`

The positive branch therefore simultaneously retains least arity, the real/imaginary sector
decomposition, a proper honest anchored equality tuple, literal graph-field inclusion, exact
relative degree over `Q(e,pi^2)`, and algebraicity of the full graph extension.

The missing one-dimensional input direction can now be selected directly over this honest base.
Applying the checked invariant-hyperplane eigenvector theorem to the full stable span and the
deletion span gives a complex number `b` such that

`b in span_Q(w) \ span_Q(v)`,
`conj(b)=b or conj(b)=-b`,
`b and exp(b) are algebraic over Q(v,exp(v))`.                    `(RQ28)`

The finrank calculation uses `complementCount+1=n`, so the deletion span is genuinely a
codimension-one invariant hyperplane.  Thus the denominator-free positive endpoint has an actual
real or purely imaginary algebraic graph complement, not merely an unspecified omitted original
coordinate.

The complement can now be reinserted as a literal final coordinate.  For an arbitrary family
`v` and complex number `b`, Lean first proves the reusable two-generator adjunction principle

`b and exp(b) algebraic over Q(v,exp(v))`
`  => Q(snoc(v,b),exp(snoc(v,b))) / Q(v,exp(v)) algebraic`,         `(RQ29)`

and hence equality of the two absolute transcendence degrees.  Unlike the earlier one-generator
snoc lemma, this requires no membership hypothesis on `exp(b)`: the enlarged graph field is
proved to be generated over the predecessor by the two lifted elements `b` and `exp(b)`, and the
algebraicity of their two-element algebra is then composed with that generated-field identity.

Applying `(RQ29)` to `(RQ28)`, define `u=snoc(v,b)`.  The checked completion satisfies

`u is Q-linearly independent, canonically anchored, and conjugation-stable`,
`span_Q(u)=span_Q(w)`,
`Fin.init(u)=v` and `u_last=b`,
`Q(u,exp(u)) / Q(v,exp(v)) is algebraic`,
`td_Q Q(u,exp(u))=complementCount+2`, hence `DefectOne(u)`,         `(RQ30)`
`conj(u_last)=u_last or conj(u_last)=-u_last`.

The completion remains a **positive least** conjugation-stable failure, not merely some new
defect-one witness: its complementary arity equals that of the original least failure, and the
same minimality statement transfers verbatim.  Thus the eigenvector normalization is stable
under re-running every proper-subspace and sector argument already proved for a least failure.

Finally all auxiliary packaging has been eliminated from the exported global endpoint.  Define a
positive eigenvector terminal witness to be a tuple `u` of length `n+3` such that

* `u` is a positive least stable anchored failure;
* its literal initial segment `Fin.init(u)` is independent, anchored, stable, and has graph-field
  degree exactly `n+2`;
* its last coordinate lies outside the initial rational span, is fixed or anti-fixed by
  conjugation, and both it and its exponential are algebraic over the literal initial graph
  field.

Lean proves the package-free equivalence

`not Schanuel iff not AI_Q(pi^2,e)`
`  or (AI_Q(pi^2,e) and exists a positive eigenvector terminal witness)`. `(RQ31)`

This is now a tuple-level terminal normal form in the strictest sense: the sharp equality field
is the graph field of the actual prefix, the entire algebraic defect is the actual final
input-output pair, and that final input is genuinely real or purely imaginary.  No reindexing,
uniform scale, Kummer adjunction, unspecified hyperplane basis, or reference to an earlier
witness remains in `(RQ31)`.

All field-tower consequences are now exported directly from this package-free predicate.  If
`K=Q(Fin.init(u),exp(Fin.init(u)))` and `L=Q(u,exp(u))`, Lean proves

`K<=L`, `Bound(Fin.init(u))` with equality,
`L/K is algebraic`, and `td_K L=0`.                              `(RQ32)`

Conditional on algebraic independence of `(pi^2,e)`, the real anchor lies literally in both
fields and

`td_(Q(e,pi^2)) K = td_(Q(e,pi^2)) L = n`.                      `(RQ32a)`

Thus `(RQ31)` can be consumed without reconstructing any instance or referring to the older
terminal structures: it is exactly a sharp bounded prefix followed by a zero-relative-degree
last graph pair.

The conjugation sign also yields a wholly real pair of final invariants.  The last input lies
outside the rational span of the canonical anchor and is therefore nonzero.  In both the fixed
and anti-fixed cases Lean proves that

`b^2` and `exp(b)+exp(b)^(-1)` are fixed by conjugation,
`b^2` and `exp(b)+exp(b)^(-1)` are algebraic over K.              `(RQ33)`

For a real `b` the first assertion is immediate; for a purely imaginary `b`, conjugation swaps
`exp(b)` with its inverse.  Hence even the literal final graph defect has a pointwise-real
quadratic/trace shadow over the sharp prefix field.  This is a consequence, not a replacement:
recovering `b` and `exp(b)` from these two real invariants is at most quadratic, exactly matching
the lossless even-core mechanism used on the anti-fixed sector.

That last claim is now quantitative in Lean.  Define the terminal real core

`C_b=Q(b^2, exp(b)+exp(b)^(-1))`,
`M=K*C_b`.                                                       `(RQ34)`

The core `C_b` is pointwise fixed by conjugation and is contained in `Q(b,exp(b))`.  The generic
snoc identity is checked exactly:

`Q(snoc(v,b),exp(snoc(v,b)))`
`  = Q(v,exp(v))*Q(b,exp(b))`.                                  `(RQ34a)`

Consequently the full terminal field is precisely the restriction to `Q` of

`M(b,exp(b))`,                                                   `(RQ34b)`

with no merely algebraic comparison or unspecified finite cover.  Two explicit monic equations
give the quantitative reconstruction:

`b` is a root of `X^2-b^2`,
`exp(b)` is a root of `X^2-(exp(b)+exp(b)^(-1))*X+1`.

Mathlib's minimal-polynomial degree formula and the compositum finrank inequality then yield

`[M(b,exp(b)):M] <= 4`.                                         `(RQ34c)`

The proof exports reusable degree-two lemmas for a square root and for a nonzero element with
known reciprocal trace, plus their degree-four pair combination.  Thus the final complex defect
over its entirely real shadow is not only algebraic but uniformly quartic at worst.

The real-shadow compositum is itself now integrated into the exact terminal tower.  Since both
generators of `C_b` are algebraic over `K`, Lean proves

`td_Q M = n+2`, `M <= L`, and `L/M is algebraic`.                `(RQ35)`

Conditional on algebraic independence of `(pi^2,e)`, the same cancellation through the real
anchor gives

`td_(Q(e,pi^2)) M = n`.                                         `(RQ35a)`

Thus the quartic cover does not alter either the absolute sharp degree or the exact relative
degree over the canonical real anchor.  Moreover, the restriction-of-scalars identity `(RQ34b)`
has been upgraded to an explicit linear equivalence over `M`; consequently the quantitative
bound applies to the actual full terminal graph field:

`[L:M] <= 4`.                                                    `(RQ36)`

This removes the last presentational ambiguity in `(RQ34c)`: the finite extension being bounded
is literally the terminal graph field appearing in the package-free global equivalence, with its
natural inclusion algebra structure over the pointwise-real shadow.

The finiteness is now exported as an actual `FiniteDimensional M L` instance, not inferred from a
numerical finrank convention.  Factoring the reconstruction through the tower

`M <= M(b) <= M(b,exp(b))`

shows that each successive degree is one or two.  Degree multiplication therefore gives the
sharper exhaustive alternative

`[L:M] = 1, 2, or 4`; in particular `[L:M] != 3`.                `(RQ37)`

The degree-one branch is characterized without an auxiliary carrier:

`[L:M]=1 iff M=L`.                                               `(RQ37a)`

Lean packages these facts back into the global endpoint.  Define a positive quartic real
eigenvector terminal witness to be the literal tuple witness from `(RQ31)` together with the
finite-dimensional extension and the degree alternative `(RQ37)`.  Then

`not Schanuel iff not AI_Q(pi^2,e)`
`  or (AI_Q(pi^2,e) and exists a positive quartic real eigenvector terminal witness)`. `(RQ38)`

Thus the remaining positive branch is an exact finite biquadratic-shaped cover of a sharp field
generated over the prefix by two pointwise-real algebraic invariants.  This is still a reduction,
not a contradiction: neither least arity nor conjugation stability presently forces the cover to
be trivial, and even triviality would leave the arithmetic real-shadow field to control.

The word "biquadratic-shaped" can now be made structural.  A simple extension of degree at most
two is normal in both possible cases: degree one is the trivial extension and degree two is a
quadratic extension.  Lean applies this separately to `M(b)` and `M(exp(b))`, proves their
compositum normal, and uses characteristic zero for separability.  The exact carrier comparison
has also been strengthened from a linear equivalence to an `M`-algebra equivalence.  Transporting
the resulting structure gives

`L/M is finite Galois, with [L:M] in {1,2,4}`.                   `(RQ39)`

The quantitative global witness in `(RQ38)` now includes this Galois assertion.  This makes all
finite-cover symmetries and fixed-field tools available on the literal terminal graph field; it
does not assume that complex conjugation fixes the base `M` pointwise, so it does not conflate the
analytic conjugation action with the newly obtained relative Galois group.

The relative group is now determined one step further.  For every `M`-automorphism `sigma`, the
quadratic equations force

`sigma(b) in {b,-b}` and
`sigma(exp(b)) in {exp(b),exp(b)^(-1)}`.                          `(RQ40)`

Lean proves these alternatives directly, then uses induction on the two-generator adjoin field
to show

`sigma^2=1` for every `sigma in Gal(L/M)`.                       `(RQ40a)`

An abstract group lemma makes the group commutative, and the finite Galois cardinality theorem
identifies its order with the extension degree.  Hence

`|Gal(L/M)| in {1,2,4}`, every element has order at most two, and `Gal(L/M)` is abelian. `(RQ40b)`

In particular the degree-four case is Klein-four-shaped rather than cyclic quartic.  The global
quantitative witness `(RQ38)` now records the Galois, finite-dimensional, commutative, and
exponent-two assertions together with the exact degree trichotomy.

The quartic branch also exposes its analytic failure internally, without appealing to the
separate model `(RT1)--(RT5)`.  If every relative automorphism intertwined the selected terminal
graph pair, so that

`sigma(exp(b)) = exp(sigma(b))`,

then `sigma(b) in {b,-b}` would determine `sigma(exp(b))` as well.  Two-generator extensionality
would therefore make the sign of `sigma(b)` an injection

`Gal(L/M) -> {false,true}`.

This contradicts `|Gal(L/M)|=[L:M]=4`.  Lean consequently proves the sharp implication

`[L:M]=4 => exists sigma in Gal(L/M),`
`  sigma(exp(b)) != exp(sigma(b))`.                              `(RQ41)`

Here both sides are compared after the literal full graph field is embedded in `C`; no formal
exponential operation is placed on an abstract extension.  The implication is included in the
quantitative global witness `(RQ38)`.  Thus the nontrivial quartic alternative cannot be removed
by silently treating all algebraic deck transformations as analytic symmetries: at least one
deck transformation is formally forced not to preserve the genuine exponential graph.

The complete quartic action is now explicit.  Encode an automorphism by the two Booleans saying
whether it fixes `b` and whether it fixes `exp(b)`.  The quadratic root alternatives and
two-generator extensionality make this map injective in every degree; in degree four the Galois
cardinality calculation makes it bijective:

`Gal(L/M) ~= {fix/switch b} x {fix/switch exp(b)}`.             `(RQ42)`

Consequently all three nonidentity patterns are realized separately:

`sigma: b |-> -b, exp(b) |-> exp(b)`,
`tau:   b |->  b, exp(b) |-> exp(b)^(-1)`,
`rho:   b |-> -b, exp(b) |-> exp(b)^(-1)`.                      `(RQ42a)`

The quartic hypothesis also forces `exp(b) != exp(b)^(-1)`, so these labels do not collapse.
Using `exp(-b)=exp(b)^(-1)`, Lean verifies that the first two automorphisms in `(RQ42a)` fail
analytic compatibility while the simultaneous switch preserves it.  Together with the identity,
the four algebraic sheets therefore split exactly into the two diagonal analytic sign patterns
and the two off-diagonal non-analytic patterns.  The strengthened global witness records both
the sign-map bijection and this explicit two-bad/one-good nonidentity classification.

The quartic group identification is now literal rather than descriptive.  Lean proves that the
degree-four relative Galois group is a Klein four group and constructs a multiplicative
equivalence

`Gal(L/M) ~= Multiplicative (ZMod 2 x ZMod 2)`.                 `(RQ43)`

It also proves the converse half of the analytic classification: a relative automorphism
intertwines the genuine complex exponential on the terminal pair if and only if its two signs
are diagonal.  Consequently the compatible automorphisms form a subtype of cardinality exactly
two.  Thus the algebraic four-sheet cover contains exactly two analytic sheets; compatibility is
neither automatic nor merely known to fail somewhere.

The diagonal subgroup exposes a previously omitted pointwise-real invariant.  Put

`c = b*(exp(b)-exp(b)^(-1))`.                                   `(RQ44)`

Whether conjugation fixes `b` or negates it, it applies the same sign to the odd exponential
difference, so `c` is fixed by conjugation.  Direct calculation gives

`c^2 = b^2*((exp(b)+exp(b)^(-1))^2-4) in C_b`.                 `(RQ44a)`

Hence `c` is a quadratic algebraic element over the original shadow `M=K*C_b`.  In the quartic
branch the input-only deck switch fixes `M` but sends the nonzero `c` to `-c`, proving

`c notin M` and `[M(c):M]=2`.                                  `(RQ44b)`

This mixed term is precisely the algebraic coordinate that distinguishes the two diagonal
analytic sheets from the two off-diagonal sheets.

Define the analytic terminal real core and its prefix compositum by

`D_b=C_b*Q(c)`, `A=K*D_b=M(c)`.                                `(RQ45)`

Lean proves that `D_b` is pointwise fixed by conjugation, `A` is literally the restriction of
the displayed simple extension `M(c)`, and adjoining it changes no transcendence degree:

`td_Q A=n+2`, and, if `AI_Q(pi^2,e)`, `td_(Q(e,pi^2)) A=n`.     `(RQ45a)`

The full graph field is finite-dimensional and algebraic over `A` in every branch.  Combining
the exact old degree trichotomy with the tower formula gives the unconditional sharpening

`[L:A]=1 or [L:A]=2`.                                          `(RQ45b)`

In the genuine old quartic branch both stages are exactly quadratic:

`[A:M]=2` and `[L:A]=2`.                                       `(RQ45c)`

The remaining top sheet has an exact one-generator presentation.  With
`t=exp(b)+exp(b)^(-1)` and `c` as in `(RQ44)`, nonvanishing of `b` gives the literal identity

`exp(b)=(t+c/b)/2`.                                             `(RQ47)`

Lean proves membership from this formula and then upgrades the carrier comparison to

`L=A(b)` and `A(b) ~=_A L`.                                    `(RQ47a)`

Thus the exponential is not an independent algebraic generator over the analytic shadow.  In
the quartic branch the simple extension has degree exactly two and `b notin A`; the final
obstruction is one explicit square-root sheet generated by the last input.  These facts are also
stored in the strongest quadratic analytic terminal package.

The analytic/algebraic interface is now expressed as a subgroup identity rather than only a
count.  Inside `Gal(L/M)`, Lean defines the stabilizer `H` of the mixed invariant `c` and proves,
for every quartic deck transformation `sigma`,

`sigma(exp(b))=exp(sigma(b)) iff sigma(c)=c iff sigma in H`.     `(RQ48)`

The earlier two-sheet count transports to the actual subgroup: `|H|=2`.  Hence the analytic
sign patterns are precisely a subgroup of the algebraic Klein-four cover, selected by the
invariant adjoined in `(RQ45)`.

The top extension is itself finite Galois over the analytic shadow.  Galois descent through the
tower `M<=A<=L`, together with `(RQ45b)`, gives

`L/A is Galois` and `|Gal(L/A)| in {1,2}`.                      `(RQ49)`

In the old quartic branch this group has order two.  The strongest endpoint package now records
both this quadratic Galois top and the order-two compatible stabilizer in the original group.

Moreover every `A`-automorphism of `L` is analytically compatible on the literal terminal pair.
Indeed restriction of scalars embeds it into `Gal(L/M)`; because it fixes `A`, it fixes `c`, and
`(RQ48)` applies.  Lean therefore proves

`forall sigma in Gal(L/A), sigma(exp(b))=exp(sigma(b))`          `(RQ50)`

in the quartic branch.  Thus adjoining `c` removes exactly the non-analytic deck transformations:
the remaining quadratic Galois sheet is the simultaneous sign switch and respects the displayed
exponential equation.  This still does not force the sheet to be trivial, because compatibility
on one algebraic graph pair is weaker than analytic continuity or order preservation of the
field automorphism.

The residual sheet is now classified exactly, rather than only through compatibility.  Lean
proves in the old quartic branch that

`|Gal(L/A)|=2`,                                                   `(RQ51)`

that every member of this group either fixes both `b,exp(b)` or sends them to
`-b,exp(b)^(-1)`, and that there is a unique nonidentity automorphism realizing the latter
action.  Thus the sole remaining terminal obstruction is a literal quadratic simultaneous
switch.  Eliminating it requires information that distinguishes the actual complex exponential
from this algebraically valid involution; no further ambiguity remains in the finite cover.

This compatibility extends from the terminal pair to the entire completed witness.  Every
`A`-automorphism fixes the prefix graph field pointwise, while `(RQ50)` handles the last
coordinate, so Lean proves

`forall sigma in Gal(L/A), forall i, sigma(exp(u_i))=exp(sigma(u_i))`. `(RQ52)`

Consequently the residual involution is a genuine symmetry of every displayed graph pair in the
finite witness.  The missing ingredient must therefore control the ambient analytic exponential
beyond those finitely many algebraic coordinates; tuple-level compatibility alone cannot rule
out the switch.

The same conclusion propagates multiplicatively to the whole integral input lattice.  For
`m in Z^(n+3)`, the formalization defines inside `L`

`x_m=sum_i m_i*u_i`, `y_m=prod_i exp(u_i)^(m_i)=exp(x_m)`,

and proves

`sigma(y_m)=exp(sigma(x_m))` for every `sigma in Gal(L/A)`.       `(RQ53)`

Thus even closure under all integral additive and multiplicative consequences of the displayed
graph equations does not eliminate the quadratic switch.  Any successful final argument must
reach beyond the discrete lattice—for example through a rigorously justified analytic,
order-theoretic, or approximation mechanism that is unavailable to arbitrary exponential-group
homomorphisms.

The topological boundary is now explicit.  Rational combinations of `1` and the standard period
form a dense subset of `C`; since both elements lie in the analytic base `A`, the image of `A` is
dense in `L`.  A continuous `A`-automorphism of `L` fixes that dense subset pointwise, hence is
the identity.  Lean therefore proves

`sigma != 1 in Gal(L/A) implies sigma is discontinuous`.         `(RQ54)`

In particular the unique simultaneous switch from `(RQ51)` is forced to be a wild discontinuous
field automorphism in the inherited complex topology.  This cleanly isolates the remaining gap:
the finite graph and integral-lattice compatibility results do not supply continuity, and a
field automorphism of a complex subfield need not be continuous merely because it respects those
discrete exponential values.

The discontinuity is witnessed by an explicit limiting configuration.  Density supplies
`a_k in A` with `a_k -> b`; for the nonidentity switch `sigma(b)=-b`, set `x_k=a_k-b`.  Then Lean
checks

`x_k -> 0`, while `sigma(x_k)=a_k+b -> 2*b != 0`.               `(RQ55)`

Thus the obstruction is not a subtle failure of a bundled continuity proof: its jump at zero is
forced directly by the dense fixed base and the terminal sign action.

This incompatible pair of limits is also promoted to the pointwise topological statement

`sigma != 1 in Gal(L/A) implies not ContinuousAt sigma 0`.       `(RQ56)`

Thus continuity does not merely fail somewhere globally: it already fails at the additive
identity, exactly where compatibility with an analytic exponential homomorphism would normally
be propagated from local control.

Additivity then propagates this negative result in the opposite direction.  Continuity at any
`z in L` would, after translating by `z` and subtracting `sigma(z)`, imply continuity at zero.
Consequently Lean proves the pointwise classification

`sigma != 1 in Gal(L/A) implies forall z in L, not ContinuousAt sigma z`. `(RQ57)`

The residual sheet is therefore nowhere continuous on the full graph field.

In fact the quartic hypothesis can be removed from the exact local classification.  Density of
the anchored analytic base, translation to zero, and additivity apply to every relative deck
transformation.  At every point `z`, Lean proves

`ContinuousAt sigma z iff sigma=1` for `sigma in Gal(L/A)`.      `(RQ58)`

Thus any analytic-shadow sheets are separated perfectly by a single continuity test, whether the
cover has degree one or two.

Finite Galois cardinality turns this into an exact collapse criterion:

`[L:A]=1 iff every sigma in Gal(L/A) is ContinuousAt zero`.     `(RQ59)`

The remaining quadratic obstruction is therefore equivalent to failure of automatic continuity
for the relative deck group, not merely implied by such a failure.

The complementary degree is classified just as sharply:

`[L:A]=2 iff some sigma in Gal(L/A) is nowhere continuous`.     `(RQ60)`

Together `(RQ59)--(RQ60)` identify the entire one-or-two cover dichotomy with its topological
behavior.

Relative finrank removes the last notational distinction between degree and literal field
collapse:

`A=L iff [L:A]=1`.                                               `(RQ61)`

Combining this with `(RQ59)` yields the field-theoretic endpoint

`A=L iff every sigma in Gal(L/A) is ContinuousAt zero`.         `(RQ62)`

Thus automatic continuity would not merely reduce the obstruction: it would identify the full
graph field with its pointwise-real analytic shadow exactly.

The simple-generator presentation `L=A(b)` makes the same dichotomy visible on the terminal input:

`b in A iff [L:A]=1`,                                           `(RQ63)`
`A=L iff b in A`,                                               `(RQ64)`
`b in A iff every sigma in Gal(L/A) is ContinuousAt zero`.     `(RQ65)`

Accordingly, the residual branch is now concentrated in one literal membership question for the
last input.

The complementary statements are exact as well:

`b notin A iff [L:A]=2`,                                        `(RQ66)`
`b notin A iff some sigma in Gal(L/A) is nowhere continuous`.  `(RQ67)`

Hence absence of the sole generator, quadratic degree, and topological wildness are three
equivalent descriptions of the same remaining obstruction.

The terminal action itself no longer needs the old quartic hypothesis.  Since `L=A(b)`, any
relative automorphism fixing `b` is the identity.  A nonidentity automorphism therefore sends
`b` to `-b`; fixing the mixed invariant then forces the output action as well:

`sigma != 1 implies sigma(b)=-b and sigma(exp(b))=exp(b)^(-1)`. `(RQ68)`

Thus the simultaneous switch classification applies to every nontrivial analytic-shadow cover,
including a quadratic cover arising from a lower-degree square/trace branch.

In degree two the group-cardinality calculation gives a unique such nonidentity switch, now with
the hypothesis stated directly as `[L:A]=2`.                            `(RQ69)`

The identity/switch dichotomy removes the quartic assumptions from the compatibility results as
well.  Every `sigma in Gal(L/A)` preserves the genuine exponential equation on the terminal pair
`(RQ70)`, on every coordinate of the completed tuple `(RQ71)`, and on its entire integral graph
lattice `(RQ72)`.  These are properties of the analytic shadow itself, not artifacts of the
larger Klein-four presentation.

The explicit topological witness also becomes quartic-free.  Every nonidentity analytic deck
transformation admits `x_k -> 0` with `sigma(x_k) -> 2*b != 0`.  `(RQ73)`  Translating that
sequence by an arbitrary `z in L` gives `x_k -> z` while
`sigma(x_k) -> sigma(z)+2*b != sigma(z)`.                         `(RQ74)`

Thus nowhere-continuity is witnessed by a concrete incompatible sequence at every point, in
every nontrivial analytic-shadow branch.

Finally, the degree-two analytic deck group is identified abstractly, not only counted:

`[L:A]=2 implies Gal(L/A) is multiplicatively equivalent to ZMod 2`. `(RQ75)`

This matches the concrete unique simultaneous switch from `(RQ69)` with the canonical cyclic
group of order two.

All of these statements are assembled into one exhaustive branch theorem.  Every analytic top
satisfies exactly the following structural alternative:

* `A=L`, and every relative automorphism is the identity; or
* `b notin A`, `[L:A]=2`, and there is a unique nonidentity simultaneous switch, which is nowhere
  continuous on `L`.                                               `(RQ76)`

This is the sharpest current terminal normal form: the second branch is the sole remaining
obstruction after the mixed analytic invariant has been adjoined.

The branch proposition is now named independently of the large quantitative witness package,
and the global reduction exposes it without any packaging loss:

`not Schanuel iff not AI_Q(pi^2,e)`
`  or (AI_Q(pi^2,e) and exists a positive terminal witness satisfying the explicit branch)`.
                                                                    `(RQ77)`

Thus a putative global counterexample yields literally either the collapsed analytic cover or
the unique quadratic wild switch above; recovering the underlying terminal witness from this
endpoint is immediate.

The quadratic branch now has exact Galois averages.  Writing `y=exp(b)`, Lean proves after
embedding the trace and norm back into `L`:

`Tr_(L/A)(b)=0`, `N_(L/A)(b)=-b^2`,
`Tr_(L/A)(y)=y+y^(-1)`, `N_(L/A)(y)=1`.                 `(RQ78)`

Moreover the unique switch has no accidental fixed elements: `sigma(z)=z` holds exactly when
`z` lies in the embedded analytic base `A`.                          `(RQ79)`

The last-input presentation is now literal at the polynomial level as well.  If `[L:A]=2`, the
minimal polynomial of `b` over `A` is exactly

`X^2-b^2`,                                                        `(RQ80)`

where the coefficient `b^2` is represented by its actual element of `A`.  Thus the simultaneous
switch is precisely the conjugation of this displayed quadratic Kummer presentation.

The terminal exponential nondegeneracy does not in fact require the old quartic branch.  For
every positive terminal witness,

`exp(b) != exp(b)^(-1)`.                                         `(RQ81)`

Indeed equality would give `exp(2b)=1`; the exact kernel of complex exponentiation would then
put `b` in the rational span of the standard period, contradicting its exclusion from the
canonical-anchor span.  This replaces the earlier sign-count proof of the quartic special case.

Consequently, in the quadratic analytic branch the exponential generator is absent from `A` as
well `(RQ82)`: otherwise the relative switch would fix it and invert it simultaneously.  Its
minimal polynomial is therefore exactly

`X^2-(y+y^(-1))*X+1`, where `y=exp(b)`.                           `(RQ83)`

Thus either member of the terminal graph pair separately generates the same quadratic top, with
literal square and reciprocal-trace presentations respectively.

The symmetric reconstruction is now explicit over the analytic shadow.  Writing
`c=b*(y-y^(-1))`, terminal nondegeneracy permits division and gives

`b=c/(y-y^(-1)) in A(y)`.                                      `(RQ84)`

Consequently adjoining the last exponential alone and then restricting scalars to `Q` recovers
the literal full graph field `(RQ85)`.  The corresponding simple extension is exposed as an
`A`-algebra equivalence

`A(y) ~=_A generatedField(u)`.                                 `(RQ86)`

These reconstruction statements require no relative-degree or quartic hypothesis: either member
of the terminal graph pair generates the full field over the analytic shadow in every branch.
In fact the two simple extensions are literally the same intermediate field inside `C`:

`A(b)=A(y)`.                                                   `(RQ87)`

The exponential generator therefore supplies a fully symmetric branch detector.  Membership
`y in A` is equivalent to relative degree one `(RQ88)`, and hence also to literal collapse
`A=generatedField(u)` `(RQ89)` and continuity at zero of every analytic-shadow deck
transformation `(RQ90)`.  Complementarily, `y notin A` is equivalent to relative degree two
`(RQ91)` and to the existence of a nowhere-continuous deck transformation `(RQ92)`.

The connector between the two quadratic presentations is itself nondegenerate:

`c=b*(y-y^(-1)) != 0`.                                         `(RQ93)`

The reciprocal-trace discriminant has the exact ambient identity

`(y+y^(-1))^2-4=(y-y^(-1))^2`,                                `(RQ94)`

and is therefore nonzero for every positive terminal witness `(RQ95)`.  More intrinsically, the
three actual coefficients `b2=b^2`, `t=y+y^(-1)`, and `c` belong to `A`, with `c != 0`, and obey

`c^2=b2*(t^2-4)` in A.                                        `(RQ96)`

Thus the additive and reciprocal quadratic presentations determine the same nondegenerate
quadratic square class over the analytic shadow.

The residual quadratic field now has an exact coordinate normal form.  In the degree-two branch,
for every `z in L` there is a unique pair `(a,d) in A x A` such that

`z=a+d*b`.                                                      `(RQ97)`

For every nonidentity analytic-shadow deck transformation, these coordinates diagonalize its
action:

`sigma(a+d*b)=a-d*b`.                                          `(RQ98)`

Thus the wild sheet is literally the sign involution on the second summand of `L=A directSum A*b`;
the fixed and anti-fixed coordinates are unique, not merely existential trace expressions.
Moreover the coordinates are recovered by the involution itself:

`a=(z+sigma(z))/2`,  `d=(z-sigma(z))/(2*b)`.                   `(RQ99)`

The full anti-fixed eigenspace is consequently exact:

`sigma(z)=-z iff exists d in A, z=d*b`.                        `(RQ100)`

This complements the earlier fixed-field theorem: the two eigensummands of the residual quadratic
extension are now identified pointwise and with explicit projectors.

Thus both the additive/multiplicative Galois averages and the complete fixed subfield of the
residual sheet are explicit.  These identities sharpen the descent target but do not supply the
missing automatic continuity.

Thus the terminal complex defect over a pointwise-real shadow is now at most quadratic, not
quartic.  The old Klein-four cover remains useful because it records the two independent
algebraic sign switches; the analytic mixed invariant quotients out their off-diagonal
difference.

Finally this sharper field is incorporated into a new package-free global endpoint.  A positive
quadratic analytic real eigenvector terminal witness retains the complete quartic Galois and
sign-pattern data over `M`, while recording the pointwise-real analytic core, its exact absolute
degree, finite algebraic top extension, degree-one-or-two alternative, and the exact quadratic
tower in the quartic case.  Lean proves

`not Schanuel iff not AI_Q(pi^2,e)`
`  or (AI_Q(pi^2,e) and exists a positive quadratic analytic terminal witness)`. `(RQ46)`

This is a strict reduction of the finite-cover obstruction, not its elimination: a nontrivial
quadratic analytic sheet can still remain, and the real-anchor branch `Q(e,pi^2)` is unchanged.

Thus neither the unit-circle phases nor their normalized sine coordinates need remain in the
final target.  The entire unresolved imaginary contribution is carried by the true squared
period, normalized angles, and ordinary cosine values.  This sharpens the arithmetic question,
but its `r=s=1` boundary is still exactly `Q(e)` versus `Q(pi^2)`.

### Trace descent already fails inside a genuine exponential graph field

The finite-cover warning `(KD6)` is not merely an abstract function-field pathology.  Let `beta`
be the unique negative real zero of

`exp(X)-X^2`.                                                     `(RT1)`

Existence and uniqueness follow because `exp(x)-x^2` is strictly increasing on the negative
axis, tends to `-infinity` at `-infinity`, and equals one at zero.  The number `beta` is
transcendental: if it were nonzero algebraic, Hermite--Lindemann would make `exp(beta)`
transcendental, contrary to `exp(beta)=beta^2`.  Therefore evaluation at `beta` identifies
`Q(T)` with `Q(beta)`.  Inside the genuine graph field

`E=Q(beta,exp(beta))=Q(beta)`                                    `(RT2)`

consider

`A=Q(exp(beta))=Q(beta^2)`,
`B=Q(beta+exp(beta))=Q(beta^2+beta)`.                             `(RT3)`

Exactly as in `(KD6)`, one has

`A intersection B=Q`, `A*B=E`,
`E*d(beta^2)=Omega_(E/Q)=E*d(beta^2+beta)`.                      `(RT4)`

The two quadratic deck involutions are

`sigma(beta)=-beta`, `tau(beta)=-1-beta`;                        `(RT5)`

they fix `A` and `B` respectively, and generate the translation `beta -> beta+1`, so their
common invariant rational functions are constant.  Yet neither deck involution preserves the
selected exponential graph equation.  Under `sigma`, the actual exponential of the conjugate
input is `exp(-beta)=beta^(-2)`, whereas the field conjugate of the selected output `beta^2` is
still `beta^2`.  Under `tau`, the actual exponential is
`exp(-1-beta)=e^(-1)*beta^(-2)`, whereas the field conjugate of the output is
`(-1-beta)^2`.  Thus traces and norms average algebraic sheets on which the analytic graph
identity has disappeared.

This is the exact obstruction to using terminal finiteness to descend the coefficients in
`(KD5)`: even an authentic real exponential point, a simple exponential-polynomial equation,
two finite covers, and complete trace data coexist with `(RT4)`.  Complex conjugation is special
because its second sheet does preserve `exp`, but averaging over that one involution yields only
the real quotient `(RQ8)`; it supplies no further sheets capable of descending from
`A*B_0` to either `A` or `B_0`.

### Abelian-period exponentials force a second unit, but it can remain external

A recent auxiliary-function theorem gives a strong test of the period/exponential boundary, but
its exact hypotheses reveal another external-unit loss.  In
[Tosi, *On the algebraic independence of periods of abelian varieties and their exponentials*,
Theorem 1](https://arxiv.org/abs/2309.02800), let `X` be a `g`-dimensional abelian variety over a
number field, let `Omega` be a `2g` by `2g` period/quasiperiod matrix, and form the `g` by `2g`
matrix whose `i`-th row is

`(exp(xi_i*omega_(i,1)),...,exp(xi_i*omega_(i,2g)))`.             `(AV1)`

Choose `m` rows of `Omega` and `n` rows of `(AV1)`, adjoining the corresponding `xi_i`, and call
the resulting set `S`.  The theorem says that if `td_Q Q(S)=1` and

`2*m+n>2*g`,                                                      `(AV2)`

then every transcendental `a in Q(S)` has transcendence type at least

`2+(2*m+n-2*g)/(2*g+n)`.                                         `(AV3)`

Since `pi` has transcendence type at most `2+epsilon` for every `epsilon>0`, `(AV3)` implies the
useful corollary

`pi in Q(S)` and `(AV2)`  =>  `td_Q Q(S)>=2`.                    `(AV4)`

This is unconditional and genuinely mixes periods with their ordinary exponentials.  It does not,
however, isolate the canonical pair `(e,pi)`.  The smallest case already shows the issue.  Take a
CM elliptic curve with holomorphic period row `(Omega,tau*Omega)`, where `tau` is a nonreal
imaginary-quadratic number, and choose

`xi=(1+omega)/Omega`, `omega=2*pi*I`.                             `(AV5)`

With `g=m=n=1`, condition `(AV2)` holds and the selected field contains

`Omega`, `xi`, `omega=xi*Omega-1`,
`exp(xi*Omega)=e`, `exp(xi*tau*Omega)=exp(tau*(1+omega))`.         `(AV6)`

Thus `(AV4)` forces two transcendence units among the quantities in `(AV6)`, but besides `e` and
`omega` it has introduced both the elliptic period `Omega` and the new exponential
`exp(tau*(1+omega))`.  The latter cannot be reduced by the character law to a rational power of
`e` times a root of unity.  Indeed an identity

`tau*(1+omega)=a+b*omega`, `a,b in Q`,                            `(AV7)`

would give `(tau-a)+(tau-b)*omega=0`; the transcendence of `omega` over `Qbar` forces
`tau=a=b`, contradicting that `tau` is nonreal.  Algebraic dependence of `(e,omega)` alone gives
no control over either external quantity in `(AV6)`.

The other natural normalizations have the same shape.  Taking `xi=1/Omega` makes the first
exponential equal to `e`, but then the field need not contain `pi` and the second value is
`exp(tau)`.  Taking `xi=omega/Omega` puts `pi` in the field and makes the first exponential one,
but the second is `exp(tau*omega)`; for `tau=I` it is `exp(-2*pi)`.  Selecting both rows of the
elliptic period matrix imports the quasiperiods, whose Legendre determinant contains `2*pi*I` but
whose known algebraic-independence surplus may again lie in the elliptic period data.

This exactly matches the anchor Four/Six-Exponentials audit: a rectangular period theorem can
force a second unit only after completing an abelian period row, and that completion adds values
outside the terminal graph field.  Tosi's proof itself assumes the degree-one alternative and
derives the stronger transcendence-type lower bound `(AV3)`; it explicitly notes that the desired
degree-two conclusion is expected rather than proved in that generality.  Applying `(AV4)` to the
stable endpoint would therefore require an additional algebraic containment of the elliptic
period and every companion exponential in `Q(e,omega)`.  No such containment follows from the
sector reduction, and asserting it is stronger than the missing cross-sector unit.

### Period-lattice monodromy has exactly the permitted zero density

The smallest endpoint also defeats the most direct attempt to turn logarithmic monodromy into
infinitely many algebraic relations.  Suppose for this audit that

`td_Q Q(e,omega)=1`, where `e=exp(1)` and `omega=2*pi*I`,            `(PL1)`

and let `P(X,Y) in Q[X,Y]` generate the height-one prime kernel of evaluation at `(e,omega)`.
Complex conjugation gives `P(e,-omega)=0`; hence irreducibility and equality of the two kernel
ideals imply

`P(X,-Y)=c*P(X,Y)`, `c^2=1`.                                    `(PL2)`

The odd case would make the irreducible polynomial `P` divisible by `Y`, impossible because
`omega` is transcendental.  After rescaling, `P` is therefore even in `Y`, which recovers the
real quotient `Q(e,omega^2)` rather than a contradiction.

Now form the honest exponential polynomial

`F(z)=P(exp(z),omega)`.                                          `(PL3)`

It has rational-polynomial dependence on the fixed coefficient `omega`, and periodicity gives

`F(1+k*omega)=P(e,omega)=0` for every `k in Z`.                  `(PL4)`

These infinitely many zeros do not force `F=0`: after specializing `Y=omega`, the factor
`X-e` divides `P(X,omega)` over `C`, so `(PL4)` is simply the ordinary period lattice of
`exp(z)-e`.  Moreover the root is simple.  Indeed `P` depends on `X`, is separable over
`Q(Y)`, and its nonzero discriminant cannot vanish at the transcendental number `omega`; hence
`P_X(e,omega)!=0`, and

`F'(1+k*omega)=e*P_X(e,omega)!=0`.                               `(PL5)`

Thus the selected branch contributes only the natural linear zero density of an exponential
polynomial of exponential degree `deg_X P`.

Trying to make the coefficient move does not improve the count.  For every positive integer
`m`, the rational-coefficient exponential polynomial

`H_m(z)=P(exp(z),(z-1)/m)`                                      `(PL6)`

has the two forced zeros `1+/-m*omega`.  The product through `m<=M` has only `2M` forced zeros,
while both its polynomial and exponential degrees grow linearly in `M`; on a disk large enough
to contain those zeros its exponential indicator budget is quadratic in `M`.  Taking powers
raises multiplicity and degree in the same proportion.  In particular neither the periodic
family `(PL3)` nor the moving-coefficient family `(PL6)` creates a zero surplus.

**Audited conclusion.**  Analytic continuation does preserve the equation `exp(z)=e` around its
period lattice, but it holds the algebraic coefficient `omega` fixed.  It does not manufacture
`P(e,m*omega)=0`.  When the coefficient is moved by `(PL6)`, the number and multiplicity of known
zeros are paid for by exactly the same degree/type growth.  Any successful monodromy argument
must therefore add an arithmetic lower bound or a new compatibility between distinct branches;
plain periodicity plus a one-variable zero estimate is at the sharp boundary.

### E-function/Gevrey separation does not yet give cross-field disjointness

The canonical positive generator is an E-value: `e=exp(1)`.  The effective E-function theorem of
[Fischler--Rivoal](https://arxiv.org/abs/1906.05589) computes all algebraic relations among values
of specified E-functions at algebraic arguments from the functional relations of those
E-functions.  In particular it is an exact and unconditional specialization theorem inside the
E-value class.  It does not admit a period such as `pi` as an additional coefficient or input;
using it on `exp(z)` alone recovers the known transcendence of `e`, not independence from `pi`.

At the exact squared-period endpoint, the other generator is a G-value:

`pi=4*arctan(1)`, `pi^2=16*arctan(1)^2`,                         `(EG0)`

where `arctan(z)=sum_(n>=0)(-1)^n*z^(2*n+1)/(2*n+1)` is a G-function and `z=1` is
an ordinary point of its rational differential equation `(1+z^2)A'=1`.

Thus `(RQ12a)` places the smallest stable boundary directly at the E-versus-G interface.  The
natural conjecture `E intersection G=Qbar` is itself stated in the cited arithmetic-Gevrey work
as out of reach.

The arithmetic-Gevrey interface makes the obstruction explicit.  In
[Fischler--Rivoal, *Relations between values of arithmetic Gevrey series*](https://arxiv.org/abs/2301.13518),
Gamma values are connected to E-values and order-`1` Gevrey sums by identities of the form

`e*Gamma(a) + (explicit E-value) = (explicit D-value)`.           `(EG1)`

For `a=1/2`, `Gamma(1/2)^2=pi`, so this is the relevant arithmetic interface.  But the paper's
separation conclusions for Gamma values use conjectures such as

`D intersection E = Qbar`                                       `(EG2)`

and a lifting conjecture for the mixed/Gevrey class; the paper states that even the analogous
`E intersection G=Qbar` is out of reach.  Therefore `(EG1)` supplies no unconditional descent
of a polynomial relation between `e` and `pi`.

There is a second, structural gap: even a proof of `(EG2)` would not by itself prove the needed
algebraic independence.  From `td_Q Q(e,pi)=1`, the one-variable fields generated separately by
`e` and `pi` can have trivial intersection while their compositum has degree one, just as in the
finite-cover examples `(KD6)` and `(RT3)--(RT4)`.  Ring intersection is weaker still.  The
required input is algebraic disjointness (or an equivalent two-unit transcendence statement),
not merely the absence of a common named E/Gevrey value.

**Audited conclusion.**  Beukers--Siegel--Shidlovskii lifting solves specialization within one
E-function system.  The stable endpoint mixes an E-value with a period/Gamma value, precisely
where current lifting becomes conjectural; its proposed intersection conclusion would remain
strictly below the cross-field degree statement `(RQ14)`.  This route can reopen only with an
unconditional mixed-class lifting theorem plus a mechanism upgrading it to algebraic
disjointness.

## Active next steps

1. Continue searching for a higher-dimensional mechanism that genuinely overcomes either the
   Hilbert-count deficit or the specialization defect. Merely restating the missing estimate as a
   relative period, small-value, or exponential-algebraic-closedness assertion is not progress.
2. Test whether the conjugation-fixed common differential in `(KD5)` has an arithmetic residue,
   height, or connection constraint forcing its coefficients to descend; the abstract
   finite-cover overlap `(KD6)--(KD8)` and its genuine-exponential realization `(RT1)--(RT5)`
   are mandatory adversarial models.
3. Work in the minimal lossless real quotient `(RQ14)` and isolate a property of the normalized
   cosine field `(RQ12)` that is arithmetic rather than merely definable or
   differential-algebraic.  Any candidate must already handle the `Q(e)` versus `Q(pi^2)`
   endpoint.
4. Audit every proposed general proof against the independence hypothesis, analytic use of `exp`,
   constants obstruction, equality cases, exact quantitative inequalities, and circularity list
   in `PROMPT.md`.

## Verification

The project is pinned to Lean 4.29.1 and Mathlib 4.29.1. The complete command is

```sh
nix develop -c lake build
```

The registered root list contains forty-seven modules. The full build succeeds with 2927 jobs.
Current output contains only harmless linter advice (principally unused generic Galois section
hypotheses and minor simplification suggestions); there are no errors or proof placeholders.
The new restriction, rational-hyperplane, algebraicity, least-failure, defect-one equivalence, and
uniform-boundary theorems, including the positive fully transcendental normal form and its
deletion theorems, the period-bearing equivalence, and both fully transcendental mixed/period
boundary theorems, together with the adjacent-period exact field identity, deletion dichotomy,
explicit matrix construction, full adjacent-period equivalence, and the critical-period equality
equivalence and its exported helper theorems, as well as the rectangular Kummer comparison,
prescribed canonical-anchor basis, anchored least-failure, full-transcendence shear, and exact
canonical-anchor equivalence, together with the sharp terminal deletion, algebraic-extension,
missing-pair algebraicity, and exact terminal-dichotomy theorems, have also been audited with
`#print axioms`; the disjoint anchor/positive-terminal equivalence, the exact degree-one and
degree-two anchor boundary, and the relative deletion transcendence-degree theorems have the same
audit result.  The conjugation-stable amplification module's intersection/compositum
submodularity, conjugate and joined graph-field identities, canonical stable-closure basis, and
intersection-gap failure theorems have likewise been audited.  The completed
minimal-stable-failure module
has separately been audited through its literal field-intersection descent, stable amplification,
invariant-hyperplane deletion, least stable defect-one theorem, stable shear, and terminal exact
equivalence.  The stable terminal deletion, algebraic-extension, omitted-pair, exact dichotomy,
and genuine eigenvector-complement exports have the same audit result.  The fixed/anti-fixed
sector decomposition, distinguished sector bases, appended-span and compositum identities,
common-scale Kummer comparison, least-failure proper-subspace bound, sector dimension identity,
and exact defect-one compositum degree have now been audited as well.  Each checked export uses
only `propext`, `Classical.choice`, and `Quot.sound`.  The later basis-invariant proper-subspace
theorem and both explicit sector-anchor bounds have the same audit result.
The singleton anchor-field identities, compositum upper bound, and direct CS12/CS13 sector-field
degree estimates have likewise been audited with only those three axioms.
The exact degree-one cross-sector deficit and its combined CS12--CS14 endpoint have the same
audit result.
The explicit conjugation-fixed anti-sector generators, real-core containment, exact graph-field
reconstruction after adjoining the period, algebraicity of that adjunction, and equality of the
anti-sector and real-core transcendence degrees have likewise been checked with only those three
axioms.  The arbitrary-compositum invariance and combined wholly real CS12--CS14 endpoint have
the same audit result.
The quadratic skew-trace collapse, equality with the smaller even-core degree, its
arbitrary-compositum form, and the resulting minimal-generator real endpoint `(RQ14)` have the
same audit result.  The rational linear independence of the normalized imaginary basis, its
zeroth-coordinate identity, and membership of all normalized inputs in the even core have also
been audited with only those three axioms.  The identity `omega^2=-4*pi^2` and equality of the
fields generated by `omega^2` and `pi^2`, including the full singleton even-core collapse
`(RQ12b)`, have the same audit result.  The explicit real anchor field `Q(e,pi^2)` and equality
of its transcendence degree with the canonical anchor graph field `(RQ12c)` have likewise been
audited with only those three axioms.  The two-generator upper bound and exact canonical-bound
equivalence `(RQ12d)` have the same audit result.  The global real terminal equivalence `(RQ16)`
has also been audited with only those three axioms.  The explicit pair-generation theorem,
the degree-two and degree-one algebraic-(in)dependence equivalences `(RQ12e)--(RQ12f)`, and the
pair-level global terminal equivalence `(RQ16a)` have the same audit result.
The positive least-stable refinement `(RQ17)` and its automatic extraction of distinguished
sector data and the conditional even-sector endpoint have also been audited with only those
three axioms.  The singleton reindexing and field collapses, exact degree-one results for
`Q(e)` and `Q(pi^2)`, unconditional even-core compositum deficit, and the two exact one-sided
boundaries `(RQ18)--(RQ19)` have the same audit result.
The span-to-graph membership lemma, terminal algebraicity of every span direction and its
exponential `(RQ20)`, its specialization to all sector-basis pairs, and the equivalence of the
real and complex anchor pairs have also been audited with only those three axioms.  The explicit
algebraicity of all minimal even-core generators over the same deletion field has the same audit
result.
Literal containment of the standard period and `pi^2` in the scaled deletion field `(RQ21)`,
integrality of `e` `(RQ22)`, and algebraicity of the full real-anchor tuple over that field have
also been audited with only those three axioms.
The exact real-anchor tower `(RQ23)`, its explicit simple Kummer presentation and degree bound
`(RQ24)`, and the anchor-preserving coordinate scaling, graph-field identity, and denominator-free
terminal package `(RQ25)` have likewise been audited with only those three axioms.
The package's intrinsic full-degree, defect-one, real-relative-degree, and all-span-pair
algebraicity consequences `(RQ26)` have the same audit result.
The disjoint global equivalence using the denominator-free deletion package `(RQ27)` has also
been audited with only those three axioms.
The actual fixed/anti-fixed algebraic complement over that honest equality graph field `(RQ28)`
has the same audit result.
The two-generator snoc algebraicity theorem, eigenvector completion, preservation of least stable
failure, and the package-free literal-prefix/literal-last-coordinate equivalence
`(RQ29)--(RQ31)` have likewise been audited with only those three axioms.
The direct literal field tower and real-anchor relative degrees `(RQ32)`, together with the
nonzero final direction and its conjugation-fixed algebraic square/trace shadow `(RQ33)`, have the
same audit result.
The exact snoc compositum identity, pointwise-real terminal core, restriction-of-scalars
reconstruction, and uniform quartic degree bound `(RQ34)` have likewise been audited with only
those three axioms.
The real-shadow compositum's exact absolute and conditional real-anchor relative degrees, its
algebraic inclusion into the full field `(RQ35)`, and the literal full-field quartic bound
`(RQ36)` have the same audit result.
Actual finite-dimensionality, exclusion of the cubic degree, the degree-one equality criterion,
and the fully quantitative global terminal equivalence `(RQ37)--(RQ38)` have likewise been
audited with only those three axioms.
The normality of both quadratic stages, their finite Galois compositum, the exact terminal
algebra equivalence, and the transported literal full-field Galois assertion `(RQ39)` have the
same audit result.
The reciprocal-trace root dichotomy, explicit action on both terminal generators, exponent-two
and commutativity theorems, Galois-group cardinal trichotomy, and their inclusion in the global
endpoint `(RQ40)` have likewise been audited with only those three axioms.  Two-generator
automorphism extensionality and the forced failure of exponential compatibility in the quartic
branch `(RQ41)`, including its strengthened global endpoint, have the same audit result.  The
quartic sign-map bijection, realization of every independent sign pattern, nondegeneracy of the
exponential switch, and exact analytic/non-analytic sheet classification `(RQ42)` have likewise
been audited with only those three axioms.  The literal Klein-four equivalence and exact count of
analytic sheets `(RQ43)`, the mixed conjugation-fixed invariant and its quadratic adjunction
`(RQ44)`, the analytic real-core transcendence and degree-one-or-two cover `(RQ45)`, and the
resulting strongest global equivalence `(RQ46)` have the same audit result.  The rational
reconstruction of the last exponential, exact simple-extension carrier and algebra equivalence,
and quadratic last-input presentation `(RQ47)` have likewise been audited with only those three
axioms.  The mixed-invariant stabilizer and exact compatible-subgroup order `(RQ48)`, finite
Galois analytic top `(RQ49)`, and compatibility of every analytic-top deck transformation
`(RQ50)` have the same audit result.  The exact order-two analytic group, diagonal action, and
unique nonidentity simultaneous switch `(RQ51)` have likewise been audited with only those three
axioms.  Full-tuple exponential compatibility over the analytic shadow `(RQ52)` has the same
audit result.  The explicit integral graph lattice and compatibility of the analytic deck group
on all its points `(RQ53)` have likewise been audited with only those three axioms.  Density of
the rational period lattice, rigidity of continuous relative automorphisms, and forced
discontinuity of the residual sheet `(RQ54)` have the same audit result.  The explicit sequence
converging to zero whose switched image converges to `2*b != 0` `(RQ55)` has likewise been audited
with only those three axioms.  The resulting failure of continuity at zero `(RQ56)` has the same
audit result.  Its additive propagation to nowhere-continuity `(RQ57)` has likewise been audited
with only those three axioms.  The quartic-free exact pointwise continuity classification
`(RQ58)` has the same audit result.
The exact automatic-continuity/degree-one collapse criterion `(RQ59)` has likewise been audited
with only those three axioms.
The complementary degree-two/nowhere-continuous classification `(RQ60)` has the same audit
result.
Literal equality of the analytic shadow with the full graph field at relative degree one
`(RQ61)`, and its exact automatic-continuity reformulation `(RQ62)`, have likewise been audited
with only those three axioms.
The last-input membership criterion `(RQ63)`, literal field-collapse criterion `(RQ64)`, and
their automatic-continuity formulation `(RQ65)` have the same audit result.
The complementary last-input exclusion/degree-two criterion `(RQ66)` and its nowhere-continuous
deck-transformation form `(RQ67)` have likewise been audited with only those three axioms.
The degree-independent simultaneous-switch theorem `(RQ68)` has the same audit result.
The degree-two unique-switch theorem `(RQ69)` and quartic-free terminal, full-tuple, and
integral-lattice compatibility theorems `(RQ70)--(RQ72)` have likewise been audited with only
those three axioms.
The quartic-free discontinuity sequence at zero `(RQ73)` and its translated witness at every
point `(RQ74)` have the same audit result.
The cyclic order-two identification of the degree-two analytic Galois group `(RQ75)` has likewise
been audited with only those three axioms.
The exhaustive collapse-versus-unique-wild-switch dichotomy `(RQ76)` has the same audit result.
Its named branch proposition and package-free global equivalence `(RQ77)` have likewise been
audited with only those three axioms.
The exact terminal trace/norm identities `(RQ78)` and exact fixed-field characterization of the
unique switch `(RQ79)` have the same audit result.
The exact quadratic minimal polynomial of the last input `(RQ80)` has likewise been audited with
only those three axioms.
The quartic-free terminal exponential nondegeneracy `(RQ81)`, exclusion of the exponential from
the degree-two analytic base `(RQ82)`, and its exact reciprocal minimal polynomial `(RQ83)` have
the same audit result.
The rational reconstruction of the last input from the last exponential `(RQ84)`, literal
restriction-of-scalars recovery of the full graph field `(RQ85)`, and the resulting symmetric
simple-extension algebra equivalence `(RQ86)` have likewise been audited with only those three
axioms.
Literal equality of the last-input and last-exponential simple extensions `(RQ87)`, together
with the exponential membership/collapse/continuity criteria `(RQ88)--(RQ90)` and complementary
degree-two/nowhere-continuous criteria `(RQ91)--(RQ92)`, has the same audit result.
Nonvanishing of the mixed connector `(RQ93)`, the exact reciprocal discriminant identity
`(RQ94)`, its witness-level nonvanishing `(RQ95)`, and the coefficient relation internal to the
analytic shadow `(RQ96)` have likewise been audited with only those three axioms.
The unique two-coordinate quadratic normal form `(RQ97)` and diagonal sign action of every
nonidentity residual sheet `(RQ98)` have the same audit result.
The explicit even/odd projector formulas `(RQ99)` and exact anti-fixed eigenspace
characterization `(RQ100)` have likewise been audited with only those three axioms.
