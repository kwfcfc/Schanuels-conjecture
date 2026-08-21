# Survey: ordinary mathematical background for the Hermite--Lindemann/Lindemann--Weierstrass argument

`PROMPT.md` permits public search only "for ordinary mathematical background or standard named
theorems," explicitly not "to search for a solution to this exact conjecture or benchmark," and
explicitly not to determine or report whether Schanuel's conjecture is open. This file is scoped
accordingly: it surveys (1) how the classical, already-proved Hermite--Lindemann/
Lindemann--Weierstrass theorem has been formalized elsewhere, as background for finishing
`Schanuel/GaloisStableArithmetic.lean` (`PROGRESS.md` §4 Step 8), and (2) named theorems adjacent
to Schanuel's conjecture (Six/Four Exponentials, Baker, Ax's precise statement, Nesterenko,
Zilber's program, the period-conjecture equivalence), stated as mathematics, not as evidence for
or against the numerical conjecture's difficulty or status.

An earlier version of this file included a table of benchmark-leaderboard submissions for a
Lean-eval problem statement matching this project's target lemma, and a concluding assessment of
how open the conjecture is for `n ≥ 2`. Both were out of scope under `PROMPT.md` and have been
removed; see the notes at the end of §1.3 and §4.8.

This is a research survey based on web sources consulted on 2026-08-19. Treat anything
time-sensitive here (repository states, "recent" papers) as a snapshot, not a permanent fact --
re-check before relying on it.

## 1. Prior formalizations of Hermite--Lindemann/Lindemann--Weierstrass

### 1.1 Mathlib4 itself

Mathlib (pinned `v4.29.1`) has the analytic scaffolding this project already builds on
(`LindemannWeierstrass.exp_polynomial_approx` in
`Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart`, confirmed present in the pinned
checkout at `.lake/packages/mathlib/Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`)
but no finished Hermite--Lindemann or Lindemann--Weierstrass theorem. I found no evidence of an
active, close-to-merging PR. Worth checking directly and periodically:
<https://github.com/leanprover-community/mathlib4/pulls> and the `#mathlib4` Zulip stream. If this
theorem lands upstream, the cleanest possible resolution of `LindemannArithmeticStep` is to bump
the pin and delete the local gap entirely, rather than maintain a from-scratch proof here.

### 1.2 Complete, public, mature formalizations in other systems

Two full formalizations of the general theorem already exist and are worth reading closely:

- **Isabelle/HOL, Archive of Formal Proofs.** Manuel Eberl, *The Hermite--Lindemann--Weierstraß
  Transcendence Theorem*. <https://www.isa-afp.org/entries/Hermite_Lindemann.html> (outline PDF at
  `browser_info/current/AFP/Hermite_Lindemann/outline.pdf`, dated 2026-06-18 in the copy consulted
  here). Proves exactly the target statement, plus corollaries: transcendence of `e`, `π`, and of
  `sin`, `cos`, `tan`, `sinh`, `cosh`, `tanh`, `arcsin`, `arccos`, `arctan` at nonzero algebraic
  arguments. Builds on Eberl's separate AFP entries for `e` and `π` individually
  (`E_Transcendental`, `Pi_Transcendental`).
- **Coq.** Sophie Bernard (Inria Marelle team), *Formalization of the Lindemann-Weierstrass
  Theorem*, ITP 2017 (<https://inria.hal.science/hal-01647563/document>); repository
  <https://github.com/Sobernard/Lindemann>; project page
  <http://www-sop.inria.fr/marelle/lindemann/>. Also proves the full theorem plus Baker's
  reformulation and the transcendence of `e`, `π`. Built on Coquelicot and Mathematical Components.

Both predate this project and both are complete -- no missing steps, no analogue of
`LindemannArithmeticStep` left open. That is the strongest evidence available that the remaining
mathematics is entirely tractable by "ordinary" formalization effort; what's missing here is
Lean/Mathlib-specific engineering time, not undiscovered mathematics.

A 2023 paper gives a from-scratch elementary rewrite of the classical proof, aimed explicitly at
undergraduate readability rather than a new formalization: Sever Angel Popescu, *A simple and
self-contained proof for the Lindemann-Weierstrass theorem*, arXiv:2306.14352. It is useful here
because it makes the symmetrization trick (§2 below) unusually explicit and elementary.

### 1.3 [section removed: out of scope under `PROMPT.md`]

An earlier version of this file surveyed a public Lean formalization benchmark leaderboard for
submissions solving a problem statement matching this project's target lemma. `PROMPT.md`'s last
line forbids using public search "to search for a solution to this exact conjecture or benchmark";
a leaderboard of solved-submission commit hashes for this exact statement is precisely that, so it
has been removed rather than repeated here.

## 2. The symmetrization technique used by the checked proof

Eberl's formalization and Popescu's independent elementary presentation both emphasize the same
underlying symmetrization mechanism. The checked Lean proof in this repository implements it as a
finite Galois orbit product followed by exponent-reversal; the latter makes the constant
coefficient a positive sum of squares. The classical alternative presentation is:

1. Prove the statement first only for sums that are *already* symmetric: one integer coefficient
   per full root-set of an irreducible integer polynomial. This is exactly this project's existing
   shape -- `commonIntegerPolynomial` / `aroots` at `Schanuel/LindemannAttempt.lean:94-121` already
   builds a single integer polynomial whose root set contains everything needed; Eberl's
   `Hermite-Lindemann-aux1` and Popescu's Hermite-integral argument both prove non-vanishing at
   exactly this stage, by the same factorial-decay-plus-mod-`p` contradiction this project's
   `exp_intCast_transcendental` (`Schanuel/LindemannAttempt.lean:326`) already carries out for the
   integer/rational special case.
2. Given an arbitrary (not necessarily symmetric) relation, force it into that shape by
   **multiplying together the images of the relation under every permutation of the relevant
   root-multiset** (Eberl's `Hermite-Lindemann-aux2`/`aux4`; Popescu's Lemma 2.1 together with
   expanding `∏(e^{αᵢ} + 1)` into all subset-sums of the conjugates). The key fact, stated
   plainly: *a finite set of algebraic numbers is stable under every embedding of the field it
   generates if and only if it is exactly the root set of some polynomial over* `ℚ` (Popescu,
   Lemma 2.1). Permutation-symmetric combinations of a root-multiset are visibly stable under
   every embedding, so this construction always lands back in the shape step 1 handles.
3. That the resulting symmetrized coefficients land in `ℚ` (then, after clearing denominators, in
   `ℤ`) is exactly the fundamental theorem of symmetric polynomials / Vieta's formulas applied to
   the polynomial whose roots are the now-stable multiset -- not an appeal to
   `IsGalois.mem_range_algebraMap_iff_fixed`.

Mathlib already has both toolkits on disk in the pinned version -- this is not a gap that needs
new library code, just new lemmas built from existing pieces:

- `Mathlib/RingTheory/MvPolynomial/Symmetric/FundamentalTheorem.lean` and
  `.../NewtonIdentities.lean` -- literally "the fundamental theorem of symmetric polynomials."
- `Mathlib/RingTheory/Polynomial/Vieta.lean`, `.../SmallDegreeVieta.lean`.
- `Mathlib/FieldTheory/Galois/Basic.lean` (has `fixedField` and related lemmas) for the
  alternative route `PROGRESS.md` §6 already sketches.

**Recommendation:** before investing further in the `IsGalois`/splitting-field route, prototype
the permutation-plus-elementary-symmetric-polynomial route on a small test case (e.g. two
conjugate roots of an irreducible quadratic) and compare which produces less Mathlib friction. Two
independent complete formalizations, in two different proof assistants, converging on the same
trick -- one that Mathlib already has both halves of on the shelf -- is a real signal, not a
coincidence.

## 3. Completed local Hermite--Lindemann route

The Galois-stable route proposed in the earlier version of this survey is now complete in the
repository. `GaloisStableRelation.lean` constructs the symmetrized relation,
`GaloisStableArithmetic.lean` descends its weighted auxiliary sum to an integer,
`LindemannStableEndpoint.lean` proves modular nonvanishing and the factorial-decay contradiction,
and `GaloisStableAnalytic2.lean` proves Hermite--Lindemann and one-dimensional Schanuel.

The prioritized work therefore moves to genuinely higher-dimensional mechanisms. In particular,
repairing or repackaging the one-variable descent can no longer address the arbitrary complex
tuples required by `PROMPT.md`; the exact audited higher-dimensional deficits are recorded in
`PROGRESS.md`.

## 4. Named theorems adjacent to the numerical conjecture

The repository now checks both `n = 1` and the all-algebraic-input case of arbitrary `n`; the
latter concludes through `bound_of_algebraicIndependent_exponential`. `PROMPT.md` lists both as
insufficient on their own. This section states, as ordinary
mathematical background, the named theorems most often discussed alongside Schanuel's conjecture:
the Six and Four Exponentials statements (§4.1), Baker's theorem (§4.2), Ax's precise
differential-Schanuel statement and why its proof mechanism does not carry over to fixed complex
numbers (§4.3), the geometric/o-minimality reformulation and its applications to other problems
(§4.4), Zilber's program (§4.5), and the period-conjecture equivalence (§4.6). It draws no
conclusion about whether the numerical conjecture is open or how tractable `n ≥ 2` is; per
`PROMPT.md`, that determination is out of scope for this file (§4.8).

### 4.1 Unconditional results at small `n`

- **The Six Exponentials Theorem** (Siegel/Schneider; made explicit and proved independently by
  Lang and by Ramachandra, 1960s). If `x₁, x₂ ∈ ℂ` are `ℚ`-linearly independent and
  `y₁, y₂, y₃ ∈ ℂ` are `ℚ`-linearly independent, then at least one of the six numbers `e^{yᵢxⱼ}` is
  transcendental. This is real, unconditional, proved multi-number content for the ordinary complex
  exponential -- genuine `n ≥ 2`-flavored progress, not a special or adjacent setting.
- **The Four Exponentials Conjecture**: the natural sharpening obtained by shrinking the `2×3` grid
  above to `2×2` (two `x`'s, two `y`'s). It **remains open**, and Lang himself remarked that the
  six-exponentials proof technique "just misses" applying to four. It is elementary to show the
  Four Exponentials Conjecture *follows from* Schanuel's conjecture -- so here is a small, fully
  explicit, standalone corollary of Schanuel that has stood unproved on its own since Lang stated
  it.
- **Nesterenko's theorem** (1996; Ostrowski Prize 1997): `π`, `e^π`, and `Γ(1/4)` are algebraically
  independent over `ℚ` -- a genuine, proved transcendence-degree-3 simultaneous independence
  result, achieved by bounding linear forms in values of modular/Eisenstein series at a CM point.
  It is **not** an instance of the ordinary exponential Schanuel conjecture -- `Γ(1/4)` is a
  period-theoretic object tied to a CM elliptic curve, not a value of `exp` at an algebraic
  argument -- but it shows simultaneous algebraic independence of several numbers *is* achievable
  when enough extra (here, modular-function) structure is available to exploit. That structure has
  no counterpart for a generic pair like `(e, π)`.

### 4.2 Baker's theorem on linear forms in logarithms

(1966; Fields Medal 1970.) Unconditionally, nonzero *linear* combinations, with algebraic
coefficients, of logarithms of algebraic numbers, together with `1`, are linearly independent over
the algebraic numbers -- effectively, with explicit bounds. Subsumes the Gelfond--Schneider
theorem. It is restricted to *linear* relations among logarithms, so it gives no traction on
general polynomial (algebraic) independence questions such as whether `e` and `π` are algebraically
independent.

### 4.3 Ax–Schanuel: the precise statement, and precisely why it doesn't transfer

Ax's theorem (1971, *On Schanuel's Conjectures*, Ann. of Math.) is not evidence-by-analogy for the
numerical conjecture; it is a different, precisely stated theorem in a different category, and the
difference is exactly what makes it provable. Following Bakker--Tsimerman's lecture notes (*Lectures
on the Ax--Schanuel Conjecture*, the clearest available exposition, Theorem 1.2.5):

> **Theorem (Ax--Schanuel).** Let `f₁, …, fₙ ∈ ℂ[[t₁, …, tₘ]]` be `ℚ`-linearly independent modulo
> constants. Then
> `trdeg_ℂ ℂ(f₁,…,fₙ,e^{f₁},…,e^{fₙ}) ≥ n + rk J(f₁,…,fₙ)`,
> where `J(f₁,…,fₙ) = (∂fᵢ/∂tⱼ)` is the Jacobian matrix.

Compare this to the numerical conjecture, which only ever claims `≥ n`. The extra summand
`rk J(f₁,…,fₙ)` is the load-bearing term: it is literally the rank of a matrix of *partial
derivatives*, a quantity that exists only because the `fᵢ` are functions of variables `t₁,…,tₘ`,
not fixed numbers. Ax's proof uses the derivation essentially: differentiating a hypothetical
relation among the `fᵢ`, `e^{fᵢ}` produces a *new, lower-complexity* relation that feeds an
induction. A fixed complex number cannot be differentiated, so this entire proof strategy has no
numerical counterpart to even attempt, let alone carry out. This is why "Ax proved the differential
Schanuel conjecture" is not partial progress on the numerical one in any technical sense -- it
settles a formally parallel but structurally different statement, in a setting with an extra tool
(the derivative) that manufactures exactly the extra transcendence the theorem needs. Even the
functional analogue of Lindemann--Weierstrass in the same notes (Corollary 1.2.7) needs a further
hypothesis beyond linear independence -- that `trdeg_ℂ ℂ(f₁,…,fₙ) = rk J(f₁,…,fₙ)`, i.e. the `fᵢ`
have no formal relations beyond what their derivatives already detect -- underscoring that even the
functional theory needs strictly more input than the numerical conjecture ever gets to assume.

### 4.4 Where Ax–Schanuel-style methods do win: a family of sibling problems, not this one

The geometric reformulation of Ax–Schanuel (atypical intersections between an algebraic subvariety
and the graph of a uniformizing map, controlled by "bialgebraic" subvarieties) generalizes far
beyond the exponential map, to Shimura varieties, mixed Shimura varieties, and general variations of
Hodge structure. Combined with o-minimality and the Pila--Wilkie counting theorem, plus an
independent arithmetic input (a lower bound on Galois-orbit size, from separate machinery such as
isogeny estimates or class field theory), this has resolved real, previously-open problems:

- **André–Oort conjecture** (special/CM points on Shimura varieties are Zariski-dense only in
  special subvarieties): proved unconditionally for `𝒜_g` by Tsimerman (2018), building on the
  Ax–Lindemann–Weierstrass theorem for `𝒜_g` (Pila--Tsimerman, 2014); proved conditionally on GRH
  for general Shimura varieties (Klingler--Yafaev, 2014).
- **Manin–Mumford conjecture** (torsion points on abelian varieties): originally proved by Raynaud
  (1983) via entirely different Galois/`p`-adic methods; *re-proved* via the
  Ax-Lindemann-Weierstrass/o-minimality method by Pila--Zannier, illustrating the new method's power
  even on an already-settled target.
- **Instances of the Shafarevich conjecture** (finiteness of certain integral points):
  Lawrence--Venkatesh (2018) used a `p`-adic functional-transcendence input (in the spirit of
  Ax–Schanuel for period maps) to prove finiteness of integral points on certain moduli of
  hypersurfaces.

The common shape: a moduli-type variety with a distinguished, arithmetically meaningful set of
"special points" (torsion, CM), where a *separate* arithmetic ingredient supplies a Galois-orbit
lower bound, which o-minimal point-counting then turns into a contradiction with naive functional
transcendence. Schanuel's conjecture has no such structure to lean on: it is a statement about an
arbitrary handed-you tuple of complex numbers, with no ambient family of varieties to count points
on and no moduli-theoretic Galois orbit to bound. That is the concrete reason this powerful, active
methodology has not produced -- and has no obvious route to producing -- unconditional progress on
Schanuel's conjecture itself, at any `n`, including `n = 2`.

### 4.5 Zilber's program: pseudo-exponentiation, existential closedness, Zilber–Pink/CIT

Boris Zilber's program (2004--) approaches the same territory from model theory rather than
o-minimality/point-counting, and is closer in spirit to the numerical conjecture, but still has not
resolved it:

- Zilber constructed "pseudo-exponential fields" satisfying a Schanuel-like axiom by fiat (a
  Hrushovski construction) and conjectured `ℂ_exp` is isomorphic to the canonical one. **Zilber's
  conjecture is equivalent to Schanuel's conjecture over `ℂ` together with a further "Strong
  Exponential-Algebraic Closedness" property** -- if anything strictly stronger than what this
  project needs, not a shortcut to it.
- The **Existential Closedness** conjecture asks whether "generic" systems of exponential-polynomial
  equations have solutions with the expected transcendence properties. Unconditional special cases
  are proved -- e.g. Aslanyan, Kirby, and Mantova for varieties with dominant projection to the
  domain of the exponential map of abelian varieties and tori, and separately for the modular
  `j`-function. Note the shape: it asks whether *some* solution with generic properties exists for
  a system, not whether a *specific handed-you tuple* (like `(e, π)`) has a specific property -- a
  different, if adjacent, question from Schanuel's conjecture.
- Zilber's **Conjecture on Intersections with Tori (CIT)**, part of the wider Zilber–Pink family
  (which also generalizes André–Oort and Manin–Mumford): roughly, a subvariety of the algebraic
  torus `(ℂ*)ⁿ` with "too many" points of bounded multiplicative rank must be special. This has
  seen substantial genuine progress in the toric case (Bombieri--Masser--Zannier; Maurin;
  Habegger), but it concerns purely *multiplicative* relations among algebraic points of the torus
  (roots of unity, torsion), and matters to Zilber's program because it underwrites whether the
  pseudo-exponential field construction is even the right model-theoretic object -- it is not
  itself progress on transcendence of exponential values.

### 4.6 Grothendieck's period conjecture connection

Yves André showed Schanuel's conjecture is equivalent to Grothendieck's period conjecture applied to
the simplest possible case (a "1-motive without abelian part"). This reframes Schanuel's conjecture
not as an isolated fact about `exp`, but as the smallest instance of the conjecture believed to
govern *all* periods in arithmetic geometry -- a conjecture no more solved in general than
Schanuel's own special case of it. Recent work (2025, arXiv:2509.08700) extends Schanuel-style
statements to semi-elliptic/Weierstrass-℘ settings via the same period-theoretic framework.

### 4.7 Algorithmic/logical consequences

Macintyre and Wilkie (1996) proved that Tarski's decidability question for the first-order theory of
`(ℝ, +, ×, exp)` has a positive answer *conditional on* the real form of Schanuel's conjecture.
ICALP 2024 has further work on algorithmic applications of the conjecture.

### 4.8 Scope note

This section is a catalog of named theorems and their precise statements, kept as "ordinary
mathematical background" under `PROMPT.md`. It intentionally stops short of a summary verdict on
whether the numerical conjecture is open, how tractable `n ≥ 2` is, or whether these methods could
ever be combined into a proof: rendering that verdict is out of scope for a literature survey and
is explicitly excluded by `PROMPT.md`'s rules for this task. Readers wanting the technical content
of any one theorem above should consult the cited primary references directly.

## References

- Mathlib4: <https://github.com/leanprover-community/mathlib4>
- Eberl, *Hermite--Lindemann--Weierstraß*: <https://www.isa-afp.org/entries/Hermite_Lindemann.html>
- Bernard, Coq Lindemann: <https://github.com/Sobernard/Lindemann>, <http://www-sop.inria.fr/marelle/lindemann/>
- Popescu, *A simple and self-contained proof for the Lindemann-Weierstrass theorem*: arXiv:2306.14352
- Waldschmidt, *Variations autour de la conjecture de Schanuel*: <https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/VariationsSchanuel.pdf>
- Macintyre--Wilkie, *Schanuel's Conjecture and the Decidability of the Real Exponential Field*
- On Zilber's pseudo-exponential fields: arXiv:1310.3777, arXiv:2403.09304
- Ax, *On Schanuel's Conjectures*, Ann. of Math. 93 (1971) -- the original differential-Schanuel paper
- Bakker--Tsimerman, *Lectures on the Ax--Schanuel Conjecture*: <https://benjamin-bakker.github.io/montreal.pdf> (precise Ax statement, Ax--Lindemann--Weierstrass, André--Oort/Manin--Mumford/Shafarevich applications, §1)
- Tsimerman's sketch of Ax-Schanuel and o-minimality: <https://www.math.toronto.edu/~jacobt/ASsketch.pdf>
- Six/Four Exponentials: <https://en.wikipedia.org/wiki/Six_exponentials_theorem>, <https://en.wikipedia.org/wiki/Four_exponentials_conjecture> (Lang, *Introduction to Transcendental Numbers*, is the standard reference)
- Nesterenko, *Modular functions and transcendence questions*, 1996 (algebraic independence of `π`, `e^π`, `Γ(1/4)`)
- Toric Zilber--Pink / CIT progress: Bombieri--Masser--Zannier (1999, 2008); Maurin (2008); Habegger (2009)
