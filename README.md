# Schanuel's conjecture: a Lean 4 boundary formalization

For a detailed account of the proof strategy, checked progress, precise missing mathematics, and
next formalization steps, see [`PROGRESS.md`](./PROGRESS.md).

[`Schanuel.lean`](./Schanuel.lean) states the standard finite-family form of Schanuel's
conjecture using Mathlib's complex exponential, intermediate fields, linear independence, and
cardinal-valued transcendence degree.

Schanuel's conjecture is open. Accordingly, `Schanuel.Conjecture` is only a definition of a
proposition: this project does not add it as an axiom and contains no unproved placeholders.

The checked results prove:

- the empty-family (`n = 0`) case;
- the predicted bound when the coordinates or their exponentials are algebraically independent;
- the unconditional upper bound
  `Algebra.trdeg ℚ (generatedField z) ≤ 2 * n`;
- monotonicity of the generated field and its transcendence degree under taking subfamilies;
- that a linearly independent `Fin n` family has rational span of `finrank n`;
- the exact one-variable characterization
  `Bound [z] ↔ Transcendental ℚ z ∨ Transcendental ℚ (exp z)`;
- that the one-dimensional Schanuel statement is equivalent to Hermite--Lindemann.

[`Schanuel/Structural.lean`](./Schanuel/Structural.lean) sharpens the numerical bound to a finite
selection problem: `Bound z` holds exactly when `n` algebraically independent elements can be
selected from the `2n` numbers `zᵢ, exp zᵢ`. It also proves the equivalent formulation with an
injective selection map.

[`Schanuel/LindemannAttempt.lean`](./Schanuel/LindemannAttempt.lean) pushes the one-dimensional
proof into Mathlib's existing `LindemannWeierstrass.exp_polynomial_approx`. It formally:

- clears denominators in minimal polynomials;
- obtains simultaneous prime-indexed approximations for the relevant algebraic exponents;
- extracts the integral exponential relation that would follow if `exp z` were algebraic;
- proves the needed factorial decay and prime-selection endpoint lemmas.

The remaining arithmetic argument is packaged as `LindemannArithmeticStep`. Its intended proof is
the classical Galois/integrality argument: first construct the correct Galois-symmetric auxiliary
relation, descend a scaled approximation sum to an integer, prove it nonzero modulo a large prime,
then use the analytic estimate to force its absolute value below one. This is defined only as a
proposition and used through explicit hypotheses; it is not added as an axiom. The file proves
that it is exactly equivalent to Hermite--Lindemann, confirming that it packages the full missing
nonvanishing argument rather than a small final lemma.

Mathlib is pinned to `v4.29.1`, matching the Lean version supplied by the Nix shell.

```sh
nix develop -c lake exe cache get
nix develop -c lake build
```

The project has no `sorry`, `admit`, or custom axioms.
