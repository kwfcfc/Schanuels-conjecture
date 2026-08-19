# Progress report: a Lean 4 attempt around Schanuel's conjecture

## Executive summary

Schanuel's conjecture has **not** been proved here. It is a major open problem, and the Lean
development does not postulate it or hide any gaps with `sorry`, `admit`, or a custom axiom.

What has been achieved is a checked formal boundary around the problem:

1. the standard finite-family statement is represented faithfully in Lean;
2. its elementary field-theoretic consequences and upper bounds are proved;
3. its transcendence-degree bound is converted into an exact finite-selection problem;
4. the one-dimensional case is proved equivalent to Hermite--Lindemann;
5. the one-dimensional proof is pushed through Mathlib's existing analytic Lindemann estimate;
6. the modular/analytic endpoint is completed for every nonzero rational exponent;
7. the remaining Galois argument for arbitrary algebraic exponents is isolated explicitly.

The last item is still substantial. Lean proves that the unrestricted
`LindemannArithmeticStep` is **equivalent** to Hermite--Lindemann, so it packages the remaining
nonvanishing theorem for arbitrary algebraic exponents; it is not a minor cleanup lemma. The
rational case is now discharged without this hypothesis.

## 1. The statement being formalized

For complex numbers `z₁, ..., zₙ` that are linearly independent over `ℚ`, Schanuel's
conjecture predicts

\[
  \operatorname{trdeg}_{\mathbb Q}
  \mathbb Q(z_1,\ldots,z_n,e^{z_1},\ldots,e^{z_n}) \ge n.
\]

The core definitions in [`Schanuel.lean`](./Schanuel.lean) are, schematically,

```lean
def generatedField (z : Fin n → ℂ) : IntermediateField ℚ ℂ :=
  IntermediateField.adjoin ℚ
    (Set.range z ∪ Set.range (fun i ↦ Complex.exp (z i)))

def Bound (z : Fin n → ℂ) : Prop :=
  Cardinal.mk (Fin n) ≤ Algebra.trdeg ℚ (generatedField z)

def Conjecture : Prop :=
  ∀ (n : ℕ) (z : Fin n → ℂ), LinearIndependent ℚ z → Bound z
```

Several choices here are deliberate:

- `Fin n → ℂ` makes the finite family and its cardinality explicit.
- `IntermediateField.adjoin`, rather than ring or algebra adjoin, represents the field
  `ℚ(zᵢ, exp zᵢ)`.
- Mathlib's transcendence degree is cardinal-valued, so the lower bound remains a cardinal
  inequality instead of being prematurely converted to a natural number.
- `Conjecture` is only a definition of a proposition. Nothing creates an inhabitant of it.

The usual informal dimension hypothesis is also checked: a linearly independent `Fin n` family
has a rational span of `finrank n`.

## 2. How I analyzed the problem

The analysis proceeded by separating four layers that are easy to conflate on paper.

### Layer A: representation

First, make sure Lean is talking about the right field, family, linear-independence hypothesis,
and transcendence degree. This catches foundational mistakes before attempting transcendence
arguments.

### Layer B: field-theoretic structure

Ignore the conjectural lower bound temporarily and ask what follows merely because the field has
`2n` displayed generators. This gives the unconditional upper bound, finiteness, monotonicity,
and a transcendence-basis formulation.

### Layer C: the smallest nontrivial dimension

Specialize to `n = 1`. A one-element family is linearly independent exactly when its element is
nonzero, and transcendence degree at least one is equivalent to at least one of `z` and `exp z`
being transcendental. This identifies Hermite--Lindemann as the precise theorem needed in one
dimension.

### Layer D: the available analytic proof infrastructure

Mathlib 4.29.1 does not contain a completed Hermite--Lindemann or Lindemann--Weierstrass theorem,
but it contains `LindemannWeierstrass.exp_polynomial_approx`. The attempt therefore starts from a
hypothetical algebraic relation for `exp z`, constructs the finite set of algebraic exponents to
which that estimate applies, and determines exactly where the existing library stops.

This layered approach is useful even though it cannot solve the open conjecture: every reduction
is independently checkable, and conditional reasoning is never confused with an unconditional
proof.

## 3. Results that are fully proved

| Result | Status | Location |
| --- | --- | --- |
| Standard finite-family formulation | Definition, not assumed | `Schanuel.lean` |
| Rational span of a linearly independent `Fin n` family has `finrank n` | Proved | `Schanuel.lean` |
| Empty-family bound | Proved unconditionally | `Schanuel.lean` |
| `trdeg ≤ 2n` for the generated field | Proved unconditionally | `Schanuel.lean` |
| Generated-field and transcendence-degree monotonicity under subfamilies | Proved unconditionally | `Schanuel.lean` |
| Bound from algebraic independence of all `zᵢ` or all `exp zᵢ` | Proved conditionally on those explicit hypotheses | `Schanuel.lean` |
| Bound iff `n` displayed generators can be selected algebraically independently | Proved equivalence | `Schanuel/Structural.lean` |
| One-variable bound iff `z` or `exp z` is transcendental | Proved equivalence | `Schanuel.lean` |
| One-dimensional Schanuel iff Hermite--Lindemann | Proved equivalence | `Schanuel.lean` |
| Integral normalization and simultaneous analytic approximants | Proved | `Schanuel/LindemannAttempt.lean` |
| `exp x` is transcendental for every nonzero integer or rational `x` | Proved unconditionally | `Schanuel/LindemannAttempt.lean` |
| One-variable Schanuel for every nonzero rational input | Proved unconditionally | `Schanuel/LindemannAttempt.lean` |
| Named arithmetic step iff Hermite--Lindemann | Proved equivalence; neither side is proved | `Schanuel/LindemannAttempt.lean` |
| Missing arithmetic step implies the one-variable bound | Proved implication | `Schanuel/LindemannAttempt.lean` |

### 3.1 The unconditional upper bound

The family

\[
  (z_1,\ldots,z_n,e^{z_1},\ldots,e^{z_n})
\]

is represented by `expPair : Fin n ⊕ Fin n → ℂ` and lifted into `generatedField z`.
The proof shows that adjoining this lifted family gives the top intermediate field. Therefore the
generated field is algebraic over the corresponding algebra adjoin, and Mathlib's general
transcendence-degree bound yields

\[
  \operatorname{trdeg}_{\mathbb Q}\mathbb Q(z_i,e^{z_i}) \le 2n.
\]

This is not part of Schanuel's difficult direction, but it verifies that the field representation
behaves correctly.

### 3.2 The finite-selection characterization

[`Schanuel/Structural.lean`](./Schanuel/Structural.lean) proves

```lean
Bound z ↔
  ∃ f : Fin n → Fin n ⊕ Fin n,
    AlgebraicIndependent ℚ (expPair z ∘ f)
```

and an equivalent version in which `f` is explicitly injective.

The forward proof chooses a transcendence basis contained in the range of the displayed
generators. The bound says that this basis has at least `n` elements, so a `Fin n` family can be
embedded into it. Choosing preimages in `expPair` produces the desired subfamily. Conversely, an
algebraically independent `Fin n` subfamily inside the generated field immediately gives the
transcendence-degree lower bound.

Thus the full conjecture can be restated as follows:

> Every rationally linearly independent `n`-tuple permits the selection of `n` algebraically
> independent elements among its coordinates and their exponentials.

This is an exact reformulation, not a proof of the hard transcendence assertion.

### 3.3 The exact one-dimensional boundary

For a single complex number `z`, Lean proves

\[
  \mathrm{Bound}(z)
  \quad\Longleftrightarrow\quad
  z\text{ is transcendental }\lor e^z\text{ is transcendental}.
\]

The nontrivial direction is short but informative. If both `z` and `exp z` were algebraic, then
the field they generate would be algebraic over `ℚ`, hence would have transcendence degree zero,
contradicting `Bound`.

Since the one-element family `[z]` is linearly independent over `ℚ` precisely when `z ≠ 0`, this
gives

\[
  \text{one-dimensional Schanuel}
  \quad\Longleftrightarrow\quad
  \text{Hermite--Lindemann}.
\]

Here Hermite--Lindemann is the statement that a nonzero algebraic `z` has transcendental `exp z`.
This theorem is known in ordinary mathematics, but the required completed formal proof is absent
from the pinned Mathlib version.

## 4. The attempted Hermite--Lindemann proof

The detailed attempt lives in
[`Schanuel/LindemannAttempt.lean`](./Schanuel/LindemannAttempt.lean).

Assume, toward a contradiction, that

1. `z` is algebraic over `ℚ`;
2. `z ≠ 0`;
3. `exp z` is also algebraic over `ℚ`.

The checked formal chain is the following.

### Step 1: clear denominators in minimal polynomials

`integerMinpoly z` is obtained by applying `IsLocalization.integerNormalization` to
`minpoly ℚ z`. Lean proves that, when `z` is algebraic and nonzero,

- this integer polynomial is nonzero;
- it vanishes at `z`;
- its constant coefficient is nonzero.

The last fact is essential because Mathlib's analytic approximation theorem assumes it.

### Step 2: extract an integral exponential relation

Apply the same normalization to the minimal polynomial of `exp z`. Since `exp z ≠ 0`, its
constant coefficient is nonzero. Expanding the resulting equation gives a relation

\[
  a_0 + \sum_{k\in\operatorname{supp}(q)\setminus\{0\}}
    a_k e^{kz} = 0,
\]

where `q ∈ ℤ[X]` and `a₀ = q(0) ≠ 0`. This is the theorem
`normalized_integral_exp_relation_of_isAlgebraic`.

### Step 3: collect all nonzero algebraic exponents

Define

\[
  S = \{kz : k\in\operatorname{supp}(q),\ k\ne 0\}.
\]

Every member of `S` is algebraic because `z` is algebraic, and every member is nonzero because
`z ≠ 0`.

The development forms a common integer polynomial by multiplying the normalized minimal
polynomials of the elements of `S`. This polynomial is nonzero, has nonzero constant
coefficient, and contains all elements of `S` among its complex roots.

### Step 4: invoke Mathlib's analytic Lindemann estimate

For all sufficiently large primes `p`, `exp_polynomial_approx` supplies

- an integer `nₚ` with `p ∤ nₚ`;
- an integer polynomial `gₚ` with a degree bound;
- for every complex root `r` of the common polynomial, an estimate

\[
  \left\|n_p e^r-p\,g_p(r)\right\|
  \le \frac{c^p}{(p-1)!}.
\]

The definition `HasLindemannApproximants` records this data. Importantly, the estimate is retained
for **every** root of the common polynomial, not only the originally selected `kz`; this is what a
future conjugate or norm argument needs.

### Step 5: verify the analytic endpoint

The development also proves that any fixed multiple of `c^p/(p-1)!` is eventually less than one,
and that an eventual condition on natural numbers can be met by a prime. Thus the factorial-decay
and arbitrarily-large-prime endpoints are already available.

### Step 6: close the integer and rational cases

When `z = m` is a nonzero integer, the exponents `k m` in the integral exponential relation are
integers. Consequently every `gₚ(k m)` is an integer, so no number field, scaling factor, trace,
or Galois descent is needed. The checked proof defines

\[
  D_p = n_p q(0) + p\sum_k q_k g_p(km) \in \mathbb Z.
\]

For a prime larger than `|q(0)|`, the facts `p ∤ nₚ` and `q(0) ≠ 0` show that `Dₚ` is
nonzero modulo `p`. Rewriting it with the assumed exponential relation expresses `Dₚ` as a
weighted sum of approximation errors. Factorial decay then gives `|Dₚ| < 1`, contradicting
that `Dₚ` is a nonzero integer. This proves `exp_intCast_transcendental`.

For a nonzero rational `x = a / b`, algebraicity of `exp x` would imply algebraicity of
`(exp x)^b = exp a`, contradicting the integer result. This proves
`exp_ratCast_transcendental` and, through the existing singleton criterion,
`bound_singleton_ratCast`.

## 5. What remains unproved

### 5.1 The Galois half of Hermite--Lindemann beyond rational inputs

The explicit gap is `LindemannArithmeticStep`. Given the relation above and the simultaneous
approximants, it asserts that the left-hand side of the relation cannot be zero.

This definition is intentionally exposed as a hypothesis, but it should be assessed honestly:

- no number field or Galois closure containing all relevant roots has yet been constructed;
- no Galois-symmetric auxiliary relation or quantity has yet been constructed;
- no common multiplier has yet made all required evaluations algebraic integers;
- no trace, norm, or product over embeddings has yet been formed;
- rationality plus integrality has not yet been converted into an ordinary integer;
- nonvanishing modulo `p` has not yet been proved;
- the conjugate-wise analytic bounds have not yet been assembled into an absolute-value bound.

The rational case now demonstrates that the modular and analytic endpoint closes once the
polynomial-evaluation sum is an ordinary integer. For a general algebraic exponent, constructing
such an integral Galois-symmetric quantity (or a norm with controlled conjugates) remains the
essential missing task.

Consequently, `LindemannArithmeticStep` packages essentially the whole remaining arithmetic half
of Hermite--Lindemann. In fact, the file proves the exact equivalence

```text
LindemannArithmeticStep
  ⇔ Hermite--Lindemann
  ⇒ one-dimensional Schanuel,
```

but it proves neither equivalent proposition. In the reverse direction the approximants
hypothesis is not needed: Hermite--Lindemann directly says that the nonzero integer polynomial
`q` cannot vanish at `exp z`. This confirms formally that the named step is a repackaging of the
full missing nonvanishing theorem, not a smaller result already close to completion.

### 5.2 Schanuel in dimensions at least two

Even a completed Hermite--Lindemann proof settles only `n = 1`. The general conjecture asks for
algebraic independence of sufficiently many elements, not merely the transcendence of one
exponential. The structural selection theorem makes this requirement transparent but does not
provide the needed algebraic independence.

A completed Lindemann--Weierstrass development would prove useful special cases, notably families
of algebraic, rationally linearly independent exponents: a polynomial relation among their
exponentials expands into a linear relation among exponentials of distinct algebraic linear
combinations. It would still not settle Schanuel for arbitrary complex inputs.

The remaining general case is therefore not a missing Mathlib lemma; it is the open mathematical
problem itself.

## 6. How I would continue

### Near-term goal: replace the monolithic arithmetic step by checked lemmas

1. **Specify the correct symmetric auxiliary quantity.** One cannot apply an embedding `σ` to
   `q(exp z) = 0` and conclude `q(exp (σ z)) = 0`: field embeddings do not commute with the
   analytic exponential map. Reproduce the symmetrization used in the classical proof, using all
   relevant algebraic roots, and state precisely which sum or product will later be rational and
   integral.
2. **Choose a finite ambient number field.** Construct a splitting field or normal closure that
   contains the roots of the common integer polynomial and the polynomial evaluations used in the
   approximation.
3. **Control integrality.** The normalized integer polynomials need not be monic, so their roots
   need not already be algebraic integers. Choose and track an explicit common scaling factor that
   makes the relevant roots and evaluations integral.
4. **Prove Galois stability.** Use a field norm, trace, or an explicitly symmetric polynomial over
   the root set. The proof must establish invariance directly; it must not assume that embeddings
   pass through `Complex.exp`.
5. **Descend to an integer.** Prove that this quantity is both rational and integral, hence comes
   from `ℤ`.
6. **Prove modular nonvanishing.** Select a sufficiently large prime avoiding the finite collection
   of bad coefficients, leading coefficients, discriminants, and denominators. Use `p ∤ nₚ` to
   show that the constructed integer is nonzero modulo `p`.
7. **Propagate the analytic bounds.** Use the original exponential relation only where it is
   valid, and use the root-wise estimates to bound the remaining conjugate factors or terms.
   Combine the finite bounds and factorial decay to make the resulting integer's absolute value
   less than one.
8. **Derive the contradiction.** A nonzero integer cannot have absolute value less than one. This
   would prove `LindemannArithmeticStep`, then Hermite--Lindemann, then the unconditional
   one-dimensional Schanuel theorem.

Each item should first appear as a small theorem with an explicit statement. Only after the pieces
are independently checked should `LindemannArithmeticStep` be discharged.

### Concrete Mathlib route for that decomposition

The following route is based on a source-level audit of Mathlib 4.29.1. These APIs exist, but this
part of the proposed argument has **not** yet been assembled or typechecked as a proof.

1. Let `L` be the intermediate field generated by the complex roots of `minpoly ℚ z`. The APIs
   `IntermediateField.adjoin_rootSet_isSplittingField`,
   `IsSplittingField.finiteDimensional`, and `IsGalois.of_separable_splitting_field` provide a
   finite Galois setting for the conjugates.
2. Represent a finite exponential relation as an element of the additive monoid algebra
   `AddMonoidAlgebra ℚ L`. Evaluation in `ℂ` can be built from
   `AddMonoidAlgebra.liftNCRingHom` and `Complex.expMonoidHom`; conjugating the exponents uses the
   `mapDomain` APIs.
3. Multiply all Galois conjugates of that monoid-algebra relation. The identity factor ensures
   that evaluation is still zero, while the no-zero-divisors instances for additive monoid
   algebras over rational vector spaces are intended to preserve nonzeroness.
4. Shift by a suitable orbit sum so the Galois-invariant relation has a provably nonzero constant
   coefficient. This is the important symmetrization step that a direct norm of `q(exp z) = 0`
   would miss.
5. Clear the finitely many rational coefficient denominators. For exponent denominators,
   `Algebra.IsAlgebraic.exists_integral_multiples ℤ` supplies a common scale making the finite
   exponent set integral.
6. Prove a reusable lemma `scaled_aeval_isIntegral`: if `k * u` is integral and `g` has bounded
   degree, then a sufficiently large power of `k` times `g(u)` is integral. The intended proof
   expands the polynomial and uses the closure lemmas for `IsIntegral` under finite sums,
   products, powers, and integer scalar multiplication.
7. Show the scaled approximation sum is fixed by every Galois automorphism. The fixed-field API
   `IsGalois.mem_range_algebraMap_iff_fixed` then makes it rational; rationality together with
   integrality descends it to an integer.
8. Arrange the resulting integer in the form

   \[
     A_p = k^{pT} n_p v_0 + pB_p.
   \]

   Choose `p` avoiding `k v₀`. Since `p ∤ nₚ`, reduction modulo `p` proves `Aₚ ≠ 0`. The
   symmetric exponential relation rewrites `Aₚ` as a sum of approximation errors, producing a
   bound of the form

   \[
     |A_p| \le A\,C^p/(p-1)! < 1,
   \]

   which contradicts the fact that `Aₚ` is a nonzero integer.

Candidate theorem boundaries are:

```text
galoisOrbitRelation_of_expRelation
orbitShift_constantCoeff_ne_zero
exists_integral_coeff_galoisRelation
scaled_aeval_isIntegral
fixed_scaled_approximation_sum_isInteger
galoisRelation_ne_zero
```

Keeping these as separate lemmas would make it clear which parts are algebraic, modular, or
analytic, and would prevent the current all-in-one proposition from concealing the true workload.
The orbit-relation route should reapply `exp_polynomial_approx` to its new Galois-stable support.
This is preferable to taking a direct norm of the original approximation combination: the latter
would require growth control on `nₚ`, while `HasLindemannApproximants` intentionally records no such
bound.

### Medium-term goal: formalize the algebraic-input special case

After completing the full Lindemann--Weierstrass theorem, prove that if the `zᵢ` are algebraic and
rationally linearly independent, then their exponentials are algebraically independent. The
existing theorem `bound_of_algebraicIndependent_exponential` would then immediately give
Schanuel's bound for that special class.

### Long-term goal: keep the true open frontier explicit

For arbitrary complex inputs there is currently no known proof strategy that resolves Schanuel's
conjecture. Useful formal work can still include equivalent formulations, verified consequences,
and additional known special cases, but none should be presented as closing the general gap.

## 7. Lean-specific lessons from the attempt

- Intermediate-field subtypes can carry competing `Algebra ℚ` instances. The working proofs use
  canonical rational algebra homomorphisms via `toRingHom.toRatAlgHom` where necessary.
- `IntermediateField.adjoin` describes the generated field, while transcendence-basis APIs often
  work through `Algebra.adjoin`; an explicit algebraicity bridge is required.
- Cardinal-valued transcendence degree avoids lossy `Cardinal.toNat` conversions.
- The transcendence-basis selection proof requires transporting algebraic independence through
  subtype inclusions and choosing preimages from a range.
- Isolated probes are useful for discovering APIs, but every result must be rebuilt under the
  project's actual Lake options. The final verification uses the default project target.

## 8. Verification status

The project is pinned to Lean 4.29.1 and Mathlib 4.29.1. The complete check is

```sh
nix develop --command lake build
```

and currently reports:

```text
Built Schanuel
Built Schanuel.Structural
Built Schanuel.LindemannAttempt
Build completed successfully (2747 jobs).
```

The Lean sources contain no `sorry`, `admit`, or custom axiom declarations.
