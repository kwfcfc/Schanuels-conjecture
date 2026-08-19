# Survey: prior art, techniques, and directions beyond this project's boundary

This note surveys two separate questions raised by `PROGRESS.md`'s account of what remains:

1. Is anyone else further along on the concrete, immediate gap (`LindemannArithmeticStep`,
   equivalently the Galois half of Hermite--Lindemann)? If a complete argument already exists
   somewhere, the honest move is to read and (if warranted) port it rather than reinvent it.
2. What is actually known, active, or hopeless for Schanuel's conjecture beyond that -- i.e. for
   `n ≥ 2`, which no amount of finishing Hermite--Lindemann settles?

This is a research survey based on web sources consulted on 2026-08-19. Treat anything
time-sensitive here (repository states, benchmark leaderboards, "recent" papers) as a snapshot,
not a permanent fact -- re-check before relying on it.

## 1. Is anyone further along on the immediate gap?

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

### 1.3 A very recent, harder-to-verify lead: the Lean-eval benchmark

`leanprover/lean-eval` is a public, submission-based Lean formalization benchmark (launched June
2026, <https://lean-lang.org/eval/>) that includes a problem named `lindemann_weierstrass`, stated
as:

```lean
theorem lindemann_weierstrass {n : ℕ} (x : Fin n → ℂ)
    (h_alg : ∀ i, IsAlgebraic ℚ (x i))
    (h_lin : LinearIndependent ℚ x) :
    AlgebraicIndependent ℚ (fun i => Complex.exp (x i))
```

This is *exactly* the general Lindemann--Weierstrass statement, in exactly the vocabulary this
project already uses. Specialized to `n = 1` it is verbatim `HermiteLindemannStatement`
(`Schanuel.lean:317`); used as-is it would also directly discharge the "algebraic-input special
case" that `PROGRESS.md` §6 calls a medium-term goal, via the already-proved
`bound_of_algebraicIndependent_exponential` (`Schanuel.lean:257`). Finishing this one statement
would therefore close two of this project's open items at once.

As of 2026-08-19, **seven independent submitters/AI systems are recorded as having solved this
problem** between 2026-06-14 and 2026-08-17: GanjinZero (Seed Prover, ByteDance), LorenzoLuccioli
(Aristotle, Harmonic), lukerj00 (Tau), rishistyping (Stealth Model), Morgan-Griffiths (GPT-5.6),
ZhengyangZhang06 (Humanifa + GPT-5.6), Vilin97 (24-hour GPT-5.6 speedrun). Grading is by an
automated comparator plus an independently implemented second kernel (`nanoda`), with no human
review -- the same *kind* of check (pinned statement, kernel-verified, no `sorry`/extra axioms)
this project itself already passes (see the "how it was verified" note in the audit trail of this
project's own history). That is grounds for cautious optimism that these are genuine, complete
proofs, not benchmark artifacts.

**Caveat: I have not read any of this code myself.** One submission (LorenzoLuccioli's) is
explicitly marked non-public. Of the rest, the leaderboard's result metadata names these public
repositories:

| Submitter | Repo | Commit | Issue | Solved |
| --- | --- | --- | --- | --- |
| rishistyping | `rishistyping/autoformalization-machine-intelligence` | `004459c3b692db3e3c992ee5653a1d5cd30a009a` | #711 | 2026-07-11 |
| Morgan-Griffiths | `Morgan-Griffiths/447c39cc95090748126d411f53f69439` | `ad0f468f7d4049b36924960709295cd804268645` | #744 | 2026-07-12 |
| Humanifa + GPT-5.6 | `humanfia/lean-eval` | `c8f70aae07b59f4d605e5683f69ab1d833ba3b2d` | #891 | 2026-07-28 |
| Vilin97 | `Vilin97/lean-eval-speedrun` | `59777319f23faa740a621e4a0e62e91a79d7f1c9` | #1081 | 2026-08-17 (batch of 79) |

When I tried to browse two of these at their recorded commit, GitHub returned 404 -- most likely
because the branch has since moved or been deleted, not evidence of anything improper. **Before
relying on any of this:** check these directly (this required authenticated/interactive GitHub
browsing I did not have in this session), read the actual proof, and re-verify it locally with
this project's own standard -- `lake build`, then `#print axioms` on the ported theorem -- exactly
as this repo already does for its own results. Don't take "solved" on trust any more than
`PROGRESS.md` asks a reader to take its own claims on trust.

## 2. The technique that makes the missing step tractable

Both complete formalizations (Eberl; and, independently, Popescu's elementary rewrite) close the
"Galois half" the same way, and it is *not* the route currently sketched in `PROGRESS.md` §6
(build a splitting field, use `IsGalois`, take fixed points of the Galois group). Instead:

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

## 3. Prioritized next steps for `LindemannArithmeticStep`

1. Check `leanprover-community/mathlib4` PRs and Zulip directly for active human work; if the
   theorem lands upstream, retire this gap by bumping the pin instead of maintaining a local proof.
2. Read (don't blindly port) the public Lean-eval submissions in §1.3; if genuine and legible, they
   are a ready-made map of exactly which Mathlib lemmas a working proof needs.
3. Read Eberl's outline side by side with `PROGRESS.md` §6's own candidate lemma list
   (`galoisOrbitRelation_of_expRelation`, `orbitShift_constantCoeff_ne_zero`, etc.) and rewrite that
   list around the permutation/symmetric-polynomial route from §2 wherever it removes work.
4. Only then attempt `LindemannArithmeticStep` directly, keeping it broken into small,
   independently-checkable lemmas -- matching this project's existing practice and its own stated
   preference (`PROGRESS.md` §6, closing paragraph) for exactly this kind of decomposition.

## 4. The broader landscape: what's known and active for `n ≥ 2`

Even a complete Hermite--Lindemann/Lindemann--Weierstrass theorem only finishes `n = 1` and the
all-algebraic-input special case of `n ≥ 2` (via `bound_of_algebraicIndependent_exponential`). This
section was expanded on 2026-08-19 after a direct follow-up question: given that even `n = 2` looks
hard (nobody knows whether `e` and `π` are algebraically independent), what does the celebrated
Ax--Schanuel program actually contribute? Short answer: essentially nothing *directly* to the
numerical conjecture, for a precise structural reason (§4.3); its real wins are on a family of
related-but-different problems (§4.4). Separately, a handful of genuine unconditional results
already sit right at the numerical conjecture's small-`n` boundary (§4.1), and they show just how
narrow the frontier is.

### 4.1 Genuine unconditional partial results at small `n` -- and how narrow the frontier is

- **The Six Exponentials Theorem** (Siegel/Schneider; made explicit and proved independently by
  Lang and by Ramachandra, 1960s). If `x₁, x₂ ∈ ℂ` are `ℚ`-linearly independent and
  `y₁, y₂, y₃ ∈ ℂ` are `ℚ`-linearly independent, then at least one of the six numbers `e^{yᵢxⱼ}` is
  transcendental. This is real, unconditional, proved multi-number content for the ordinary complex
  exponential -- genuine `n ≥ 2`-flavored progress, not a special or adjacent setting.
- **The Four Exponentials Conjecture**: the natural sharpening obtained by shrinking the `2×3` grid
  above to `2×2` (two `x`'s, two `y`'s). It **remains open**, and Lang himself remarked that the
  six-exponentials proof technique "just misses" applying to four. It is elementary to show the
  Four Exponentials Conjecture *follows from* Schanuel's conjecture -- so here is a small, fully
  explicit, standalone corollary of Schanuel that nobody has proved on its own in sixty years. This
  is arguably the sharpest available illustration of exactly how hard `n ≈ 2` already is.
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

### 4.8 Bottom line

No induction from `n = 1` exists, and none is expected, for a reason sharper than "nobody has found
one": the `n = 1` statement is about a single number's transcendence, while `n ≥ 2` asks for *joint*
algebraic independence, a strictly stronger and different kind of fact that individual transcendence
results do not constrain. `e` and `π` have each been known transcendental since the 1800s; whether
they are *jointly* algebraically independent -- equivalently, whether `e + π`, `e·π`, etc. are even
irrational -- remains completely open, and the Four Exponentials Conjecture (§4.1) shows the gap
persists even after weakening "algebraically independent" all the way down to one explicit
multiplicative statement. Every methodology surveyed above that *has* produced unconditional wins
for several numbers or points at once (Ax–Schanuel/o-minimality, Zilber's existential closedness,
Zilber–Pink/CIT, Nesterenko's modular-function method) does so by exploiting extra structure -- a
derivative, a moduli interpretation, a modular form -- that a generic, arbitrarily-given tuple of
complex numbers, which is what Schanuel's conjecture demands, simply does not have. What progress
exists for `n ≥ 2` on the actual conjecture is a patchwork of theorems for specific input shapes
(Lindemann--Weierstrass: all-algebraic inputs; Gelfond--Schneider/Baker: specific
multiplicative/logarithmic combinations; Six Exponentials: a specific `2×3` grid shape), not a
general method, and none of the active research programs surveyed here currently offers one.

## References

- Mathlib4: <https://github.com/leanprover-community/mathlib4>
- Eberl, *Hermite--Lindemann--Weierstraß*: <https://www.isa-afp.org/entries/Hermite_Lindemann.html>
- Bernard, Coq Lindemann: <https://github.com/Sobernard/Lindemann>, <http://www-sop.inria.fr/marelle/lindemann/>
- Popescu, *A simple and self-contained proof for the Lindemann-Weierstrass theorem*: arXiv:2306.14352
- Lean-eval benchmark: <https://lean-lang.org/eval/>, <https://github.com/leanprover/lean-eval>, <https://github.com/leanprover/lean-eval-submissions>
- Waldschmidt, *Variations autour de la conjecture de Schanuel*: <https://webusers.imj-prg.fr/~michel.waldschmidt/articles/pdf/VariationsSchanuel.pdf>
- Macintyre--Wilkie, *Schanuel's Conjecture and the Decidability of the Real Exponential Field*
- On Zilber's pseudo-exponential fields: arXiv:1310.3777, arXiv:2403.09304
- Ax, *On Schanuel's Conjectures*, Ann. of Math. 93 (1971) -- the original differential-Schanuel paper
- Bakker--Tsimerman, *Lectures on the Ax--Schanuel Conjecture*: <https://benjamin-bakker.github.io/montreal.pdf> (precise Ax statement, Ax--Lindemann--Weierstrass, André--Oort/Manin--Mumford/Shafarevich applications, §1)
- Tsimerman's sketch of Ax-Schanuel and o-minimality: <https://www.math.toronto.edu/~jacobt/ASsketch.pdf>
- Six/Four Exponentials: <https://en.wikipedia.org/wiki/Six_exponentials_theorem>, <https://en.wikipedia.org/wiki/Four_exponentials_conjecture> (Lang, *Introduction to Transcendental Numbers*, is the standard reference)
- Nesterenko, *Modular functions and transcendence questions*, 1996 (algebraic independence of `π`, `e^π`, `Γ(1/4)`)
- Toric Zilber--Pink / CIT progress: Bombieri--Masser--Zannier (1999, 2008); Maurin (2008); Habegger (2009)
