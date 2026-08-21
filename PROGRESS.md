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

The special mixed pair `(e, log 2)` exposes a second exact specialization failure.  The functions
`exp x` and `log(1+x)` are algebraically independent over `Qbar(x)` and solve one rational
differential system that is ordinary at `x=1`.  Siegel--Shidlovskii cannot specialize this
independence because `exp x` is an E-function but not a G-function, while `log(1+x)` is a
G-function but not an E-function.  A monomial system
`(exp(i*x) * log(1+x)^j)_(i+j<=D)` is functionally linearly independent, but preserving its rank
at `x=1` for every `D` is already exactly algebraic independence of `(e, log 2)`.  Mixed
E/G-function and Borel--Laplace representations provide no uniform specialization theorem for
these growing systems; evaluation at `x=1` is again not a differential homomorphism.

The full differential module makes the boundary especially transparent.  Over `Qbar(x)`, the
system for `E=exp x` and `L=log(1+x)` has Picard--Vessiot ring
`Qbar(x)[E,E^-1,L]` and exact Galois group `Gm x Ga`, acting by `E -> cE` and `L -> L+a`.
The exponential line is irregular of slope one at infinity; the logarithmic block is regular
unipotent at `-1`; Fourier--Laplace merely converts these into a punctual/exponential extension
and creates no arithmetic specialization.  The fiber map
`Qbar[E^±1,L] -> C`, `(E,L) -> (e,log 2)`, is injective exactly when those two values are
algebraically independent.  Vertical `Gm x Ga` differential determinants remain full rank at the
point even if a polynomial relation holds, while the horizontal derivation does not descend
because `d(x-1)=1`.

Numerical E/G-value theory is weaker than this missing fiber injectivity.  Although `e` is an
E-value and `log 2` a G-value, even the ring intersection statement
`E-values intersect G-values = Qbar` is conjectural.  More importantly, it would still not imply
their algebraic independence: the value rings are not algebraically closed fields (the E-value
ring is not even known to be a field).  What suffices is algebraic disjointness of their fraction
fields, or an intersection with an algebraic closure, a strictly stronger assertion.  Writing all
monomials as exponential-period cube integrals repackages the same issue: genericity of the actual
comparison point is precisely the restricted exponential-period injectivity statement, not a
consequence of differential Galois, monodromy, or Stokes data.

Local analytic intersection theory cannot manufacture the missing germ.  If a hypothetical
relation made `Q(log 2,e)` one-dimensional, its locus would be an algebraic curve, smooth at the
chosen point, cut out by
`Z_1=1`, `Y_2=2`, `P(Z_2,Y_1)=0`.  Pulling this ideal back to the exponential graph at
`(1,log 2)` gives the maximal ideal `(u,v)`: the intersection is isolated, reduced, and has local
length one.  This is sharp—`log 2` is itself generic over `Q` on the affine line and is a simple
zero of `exp T-2`.  Excess codimension gives only the vacuous lower bound `d-n`, and monodromy or
analytic continuation requires a germ identity that a single generic zero does not provide.

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

### Algebraic groups and motives

The smallest connected subgroup of `Ga^n x Gm^n` containing the point can have dimension at least
`n` while the point itself has much smaller transcendence degree, so the analytic subgroup theorem
does not supply the pointwise bound. The relevant 1-motive period-dimension equality would imply
the desired statement but is a conjectural replacement of the target, not a proof mechanism used
here.

For the Zariski locus `V` of `(z, exp z)`, demanding rotundity
`dim [M]V >= rank M` for every integer matrix `M` is already the family of Schanuel inequalities;
the case `M = I` is the target itself. Analytic intersection theory gives no lower bound when the
intersection with the exponential graph is isolated. Functional Ax--Schanuel is also vacuous
there because all coordinate germs are constants, so their rank modulo the constant field is
zero. Group-law and freeness arguments alone cannot repair this: discontinuous exponential
homomorphisms can send a rationally independent tuple to algebraic, multiplicatively independent
values.

Integer-linear orbit density does not repair this.  For the stress tuple
`(a,1,exp a,e)` with `a=log 2`, the explicit `SL_2(Z)` matrices
`[[1+k*l,k],[l,1]]` produce a Zariski-dense orbit in `Ga^2 x Gm^2`, by two successive
exponential-polynomial independence arguments.  Thus a hypothetical transcendence-degree-one
field `Q(log 2,e)` would already contain a dense orbit of low-degree points.  Rational scalings
also accumulate at the identity, but a relation of bidegree `(r,s)` transports to
`F(N*X_1,Y_2^N)`, whose degree grows like `N*s` while the distance shrinks like `1/N`.  The
relation therefore changes at exactly the scale needed to evade the identity theorem, finite
pigeonhole arguments, and Noetherianity.

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

Complex conjugation gives only a joint real/pure-imaginary reformulation.  If `K` is the original
field, `D=td(K*Kbar)`, and `e=td(K intersect Kbar)`, then `D+e<=2*td(K)`.  Writing `z=x+v` with
real `x` and purely imaginary `v`, rational independence gives
`rank_Q(x)+rank_Q(v)>=n`, and the joint conjugate field is algebraically equivalent to the
generated field of rational bases of those two spans.  Even a bound
`D>=rank_Q(x)+rank_Q(v)` yields only half the desired inequality unless one also controls the
intersection.  For `(1,log 2)` conjugation is trivial; for `(log 2,2*pi*I)` it merely separates
the two exact missing coordinates.  Norms `a*conj(a)>0` land in a real function field containing
arbitrarily small positive elements, not in a discrete ordered ring.

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

## Active next steps

1. Continue searching for a higher-dimensional mechanism that genuinely overcomes either the
   Hilbert-count deficit or the specialization defect. Merely restating the missing estimate as a
   relative period, small-value, or exponential-algebraic-closedness assertion is not progress.
2. Audit every proposed general proof against the independence hypothesis, analytic use of `exp`,
   constants obstruction, equality cases, exact quantitative inequalities, and circularity list
   in `PROMPT.md`.

## Verification

The project is pinned to Lean 4.29.1 and Mathlib 4.29.1. The complete command is

```sh
nix develop -c lake build
```

The registered root list contains twenty-nine modules. The full build succeeds with 2907 jobs.
Current warnings are limited to unused section hypotheses in generic Galois declarations; there
are no errors or proof placeholders.
