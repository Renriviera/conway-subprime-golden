# Presentation proposal for the Conway subprime proof

11 September 2026. Based on the original manuscript, the revised manuscript in
`proof-variants/lean-friendly`, and the current active Lean sources. The existing
manuscripts and formalization have not been edited. The new simplifications below
are mathematical proposals, not changes already checked in Lean.

**Recommendation.** Use the revised ratio proof as the basis of the presentation.
It already eliminates the Coppola–Laporta almost-equal-primes theorem. Present the
number theory as one standard circle-method lemma, and concentrate the main text
on why a prime frontier and an almost-filled integer region force Fibonacci
growth. Replace explicit parameter formulas by continuity where possible, and
simplify the geometry of the prime-extension step as below.

There is a second reasonable route if the stronger amplitude theorem
`M_n ~ c φ^n`, with `c > 0`, is a priority: retain the original dynamics and
replace its filling lemma by a version of the circle-method lemma with
logarithmically small overlap. That extension is described below. It needs a
written analytic proof; it is not an instance of the current fixed-parameter
Lean theorem.

**1. Put the explanation of the golden ratio first.**

Move the elementary structure/parity lemma from the revised manuscript's
bounded-step-comparison section to immediately after the definition of the
generations. A proposed introductory passage is:

> The operation has two very different effects. When the sum is composite,
> division by its least prime factor keeps the output below the current maximum.
> When the sum is prime, the output can advance the maximum. Thus the new frontier
> consists entirely of primes. An advancing odd prime must be formed from an odd
> input and an even input, and the even input is limited by the maximum one
> generation earlier. This is the source of the Fibonacci upper bound. The main
> work is to show that the supply of generated integers and primes eventually
> makes this bound asymptotically sharp.

Then display the proof's destination:

\[
M_{n+1}\le M_n+M_{n-1},\qquad
M_{n+1}=M_n+M_{n-1}+o(M_n),\qquad
|C_n|\sim M_{n-1}.
\]

The first statement is elementary; the latter two are what the proof establishes.
The positive fixed point of `r ↦ 1 + 1/r` is the golden ratio. Give the rigorous
ratio-contraction argument later; an approximate recurrence alone should not be
presented as already proving convergence.

Explain the geometry with a figure: shade an almost-filled integer region below
`M_{n-1}`, draw sparse prime points from there to `M_n`, and mark the complete
prime prefix reaching `(1-o(1))M_n`. Label the first region **almost filled**:
the argument permits integer holes and does not establish a solid interval all
the way to `M_{n-1}`. This one picture motivates both the growth ratio `φ` and
the density `1/φ`.

Explain the golden weight through the Fibonacci matrix:

\[
\begin{pmatrix}M_{n+2}\\M_{n+1}\end{pmatrix}
\le
\begin{pmatrix}1&1\\1&0\end{pmatrix}
\begin{pmatrix}M_{n+1}\\M_n\end{pmatrix},\qquad
(1,\varphi^{-1})
\begin{pmatrix}1&1\\1&0\end{pmatrix}
=\varphi(1,\varphi^{-1}).
\]

Consequently `W_n=M_{n+1}+M_n/φ` grows by at most `φ` per generation. It is a
natural measurement of Fibonacci growth, rather than an unexplained trick.

**2. Use one binary representation lemma for both generation mechanisms.**

For fixed proportional intervals `I_X,J_X`, fixed `η,B>0`, and `ν∈{1,2}`, put

\[
\mathcal J_{\nu,X}(N)
=\operatorname{meas}\{v\in I_X:N-\nu v\in J_X\}.
\]

Among targets `1≤N≤BX` with `N≡ν+1 (mod 2)` and
`𝒥_{ν,X}(N)≥ηX`, all but `o(X/log X)` have a representation
`N=νp+q`, with prime `p∈I_X,q∈J_X`.

State this as a lemma in the main text and prove the two cases together in the
analytic appendix. The current Lean sources derive exactly this interface from
Siegel–Walfisz and a Vaughan-form prime exponential-sum bound.

| Equation | Role in the Conway argument |
| --- | --- |
| `2m=p+q` | Averaging available odd primes generates almost every integer in a buffered range. |
| `2u-t=2p+q` | An available prime `t` beyond the prefix generates extra primes `u` in two steps. |

The coefficient `2` introduces no new obstruction at odd primes, since it is
invertible there. On their respective admissible parities, the two equations
have the same singular series:

\[
\mathfrak S_\nu(N)
=2C_2\prod_{\substack{\ell\mid N\\\ell>2}}
          \frac{\ell-1}{\ell-2}\ge2C_2>0,
\qquad
C_2=\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right).
\]

Here `ℓ` runs over primes. Explain the real overlap as the length of the allowed
segment on the line `νp+q=N` inside a rectangle. This gives the reader a geometric
reason for the hypothesis.

Retain the distinction between `o(X/log X)` and mere density zero. The candidate
primes in a proportional interval number about `X/log X`; an exceptional set
that is only `o(X)` could contain every candidate. The paper needs this
quantitative comparison, rather than an informal assertion that almost all
targets are represented.

**3. Modern references: use Helfgott for the method, and cite the actual inputs precisely.**

The best combination is:

- Harald Andrés Helfgott, [*The ternary Goldbach problem*](https://arxiv.org/abs/1501.05438)
  (2015), as the modern broad reference for the circle method in this setting.
  His [author's book page](https://webusers.imj-prg.fr/~harald.helfgott/anglais/book.html)
  provides later material. It identifies its posted chapters as a December 2019
  version and gives a July 2024 update. Cite the version actually consulted.
- Helfgott, [*Minor arcs for Goldbach's problem*](https://arxiv.org/abs/1205.5252)
  (2012; version 4, 2013), for modern prime exponential-sum analysis. Its main
  theorem uses smoothing and explicit parameter ranges. Importing that theorem
  literally would require matching those features to the sharp interval sums.
- Terence Tao, [*254A, Notes 8*](https://terrytao.wordpress.com/2015/03/30/254a-notes-8-the-hardy-littlewood-circle-method-and-vinogradovs-theorem/)
  (2015), especially Proposition 24 for the interval major-arc estimate and
  Exercise 34 for the unrestricted almost-all binary argument. The restricted
  intervals and coefficient `2` still need the appendix's own derivation.
- R. C. Vaughan, [*The Hardy–Littlewood Method*, second edition](https://www.cambridge.org/core/books/the-hardy-littlewood-method/5B45E102D5AFAD6FADDD66E4B510E7FA)
  (1997), Chapter 3, as the standard textbook foundation. The local Lean input
  file specifically cites Theorem 3.1; verify the equation and numbering in the
  consulted edition before using that pinpoint citation in the final manuscript.

Helfgott's [three-primes theorem](https://arxiv.org/abs/1312.7748) concerns
`N=p+q+r`. It does not itself supply `N=2p+q` or summands in the required
intervals. It should therefore not simply replace the Coppola–Laporta citation
in the old filling proof. The useful change is to consolidate the analytic
dependency, rather than to exchange theorem names. His optimized explicit
constants are not needed for a purely asymptotic conclusion.

State Siegel–Walfisz with separate exponents for clarity:

\[
\psi(x;q,a)=\frac{x}{\phi_E(q)}
+O_{A,B}\left(\frac{x}{\log^A x}\right),
\qquad q\le\log^B x,\quad(a,q)=1.
\]

The other input is

\[
\left|\sum_{n\le x}\Lambda(n)e(n\alpha)\right|
\ll(\log x)^4
\left(\frac{x}{\sqrt q}+x^{4/5}+\sqrt{xq}\right),
\qquad \left|\alpha-\frac aq\right|\le q^{-2},\quad(a,q)=1.
\]

Introduce `φ_E` only in the analytic appendix, or choose a visually distinct
notation for Euler's totient there. Keep it separate from the golden ratio.

**4. Replace the explicit choice of λ by continuity.**

In the revised manuscript, the displayed choice of `λ` and its subsequent power
estimates can be replaced by the following LaTeX passage. Keep the existing
definitions `b=δ/8`, `ε=1-λ²/(λ+1)`, and `κ=(1-ε)b/λ⁴`.

```latex
Fix $0<\delta\le1/10$. As $\lambda\uparrow\varphi$, we have
\[
 \frac{\varphi}{\lambda}\longrightarrow1,\qquad
 \epsilon\longrightarrow0,\qquad
 \kappa\longrightarrow\frac{\delta}{8\varphi^4}>0.
\]
By continuity, we may fix $8/5\le\lambda<\varphi$ sufficiently
close to $\varphi$ that
\[
 \left(\frac{\varphi}{\lambda}\right)^5<1+\delta,
 \qquad
 \rho:=\frac{(\varphi/\lambda)^4}{1+\kappa}<1.
\]
All interval parameters are now fixed before the scale tends to infinity.
```

This establishes exactly the inequalities the comparison uses. An explicit
formula can remain in the formalization notes if desired.

Similarly, at the end of the comparison, write `M_n/L_n≤1+O(δ)`, with a uniform
absolute constant over `8/5≤λ≤φ`. The subsequent choice of `δ` small in terms
of `ζ` is then immediate. The intermediate constants such as `12` and `24` do
not contribute to the mathematical mechanism.

**5. Simplify the prime-extension geometry and remove the T-grid.**

This replaces the interval construction and complementary-input estimates in
the revised profile-increase lemma. First record a small consequence of the
existing prime lower bound:

For fixed `0<c<C` and `w>0`, uniformly for `a∈[c,C]`,

\[
\#\bigl(\mathbb P\cap[aL,(a+w)L]\bigr)\gg_{c,C,w}\frac L{\log L}.
\]

To prove this using only the stated fixed-interval hypothesis, choose finitely
many grid intervals of width `w/2` so that every interval `[a,a+w]` contains
one of them. Take the minimum of their positive constants and the maximum of
their thresholds. This uniformity is over the location of an interval of fixed
width; its width does not shrink with `L`.

Now retain the original selection of an available odd prime `t` with
`1+δ<t/L≤2+2δ`. Set

\[
\tau=t/L,\qquad w=\delta/20,\qquad b=\delta/8,
\]
\[
I=[\lambda-w,\lambda]L,\qquad J=[1-4w,1]L,
\]
\[
U=\left[\lambda+\frac{\tau+1}{2}-2w,
        \lambda+\frac{\tau+1}{2}-w\right]L.
\]

The first two intervals contain available primes at generations `j+1` and `j`.
For every real `p∈I` and `u∈U`, direct endpoint subtraction gives

\[
2u-t-2p\in[(1-4w)L,L]=J.
\]

Thus the overlap has length `wL`. In fact all the targets lie in the fixed range

\[
2u-t\in[(2\lambda+1-4w)L,(2\lambda+1-2w)L]\subset[1,6L].
\]

The source intervals `I,J` are independent of `t`, so one global binary
exceptional set applies to every chosen `t` through the injective map
`u↦2u-t`. The uniform prime lower bound just proved supplies `≫L/log L`
prime candidates in the moving interval `U`. This removes the finite set of
centers `T` from the boost proof.

For a prime `r∈[λ³,λ³+b]L` and any `u∈U`, the complementary integer `v=r-u`
satisfies

\[
\begin{aligned}
v/L&\le\lambda^3-\lambda+b-(\tau+1)/2+2w\\
&\le\lambda+b-\delta/2+2w
=\lambda-11\delta/40<\lambda-\delta/4,\\
v/L&\ge\lambda^3-\lambda-(\tau+1)/2+w\ge4/5.
\end{aligned}
\]

Here `λ³−2λ−1≤0`, `λ³−λ≥12/5`, and `(τ+1)/2≤8/5` throughout the
allowed ranges. Use exactly the existing buffered filling lemma at cutoff
`λL` with buffer `δ/(4λ)`.

The same two exclusions now leave a candidate: missing `u` account for
`o(L/log L)` possibilities, and missing `r-u` account for another
`o(L/log L)`. The available prime `u` and integer `r-u` generate `r`.
The final rebalancing step at generation `j+4` is unchanged.

Show these generation indices in a small diagram or table:

| Generation | Available inputs and new output |
| --- | --- |
| `j` | The outlying prime `t` and primes `q∈J`. |
| `j+1` | Their average `(t+q)/2`, and primes `p∈I`. |
| `j+2` | Almost every prime `u=p+(t+q)/2` in `U`, and almost all needed complementary integers. |
| `j+3` | Every prime in the enlarged prefix, using `r=u+(r-u)`. |
| `j+4` | Propagation rebalances the two consecutive prime cutoffs. |

**6. An optional shorter estimate for the analytic appendix.**

The original appendix bounds `(n/φ_E(n))²` by a four-divisor function. A direct
mean-value argument gives stronger bounds with less logarithmic bookkeeping.
Put `f(n)=(n/φ_E(n))²` and define a nonnegative multiplicative function `g`
supported on squarefree integers by

\[
g(\ell)=\left(\frac{\ell}{\ell-1}\right)^2-1
=\frac{2\ell-1}{(\ell-1)^2}.
\]

Then `f(n)=Σ_{d|n}g(d)` and

\[
\sum_{d\ge1}\frac{g(d)}d
=\prod_\ell\left(1+\frac{g(\ell)}\ell\right)<\infty.
\]

The product converges because `g(ℓ)/ℓ=O(ℓ⁻²)`. Divisor interchange gives

\[
\sum_{n\le x}f(n)\ll x,\qquad
\sum_{n\le x}\frac{f(n)}n\ll\log(2x).
\]

Consequently, by dyadic summation and divisor interchange respectively,

\[
\sum_{k>z}\frac1{\phi_E(k)^2}\ll z^{-1}\quad(z\ge1),\qquad
\sum_{N\le BX}\sum_{h\mid N}f(h)\ll_B X\log X.
\]

The original Ramanujan-sum argument then gives a singular-series tail
`≪F(N)/P`, where `F(N)=Σ_{h|N}f(h)`, and at most `O(X log X/P)` targets
with a fixed-size tail. This can replace much of the divisor-function and
log-power bookkeeping in the original appendix. It is an elementary derivation,
so it need not introduce another specialized reference.

Keep the proof of the almost-all theorem visibly in three parts: the major arcs
give a positive main term, the minor arcs are small in mean square, and a
counting inequality bounds the exceptions. Choose a sufficiently large fixed
logarithmic cutoff exponent, followed by a sufficiently large Siegel–Walfisz
saving. Give the actual error estimates in a compact appendix table.

**7. Alternative if retaining the positive amplitude is important.**

The existing appendix can be adapted to the following stronger statement:
for fixed `A,D,B>0`, intervals `I_X,J_X⊂[1,BX]`, and `ν∈{1,2}`, all but
`O_{A,D,B}(X/log^A X)` admissible targets `N≤BX` with overlap at least
`X/log^D X` have a restricted representation.

The intervals may vary with `X`, but for each `X` they must be fixed across
the targets being counted. This is a proposed extension of the written
circle-method argument, not something obtained by substituting a varying
parameter into the current proportional-interval theorem.

To see the required changes, use `P=(log X)^K` with `K>A+2D+20`. The
minor-arc mean-square estimate in the original appendix is

\[
\sum_N|R_{\mathfrak m}(N)|^2
\ll X^3P^{-1}(\log X)^9+X^{13/5}(\log X)^9.
\]

Test this against a threshold comparable to `X/log^D X`, rather than to `X`.
The resulting exceptional set has size

\[
\ll X P^{-1}(\log X)^{9+2D}
   +X^{3/5}(\log X)^{9+2D}
\ll_{A,D}X/\log^A X.
\]

Choose the major-arc approximation error smaller than `X/log^D X`; arbitrary
logarithmic savings in Siegel–Walfisz allow this. The singular-series estimate
above supplies positivity outside an acceptable exceptional set. For interval
endpoints below the rational denominator `q`, bound the initial prime sum
trivially by `O(q)` using the prime-counting upper bound; otherwise apply the
Vaughan estimate. This supplies endpoint uniformity that the original fixed
positive proportional endpoints did not need.

For filling, use `ν=1`, `B=2`, and `I_X=J_X=[1,X]`. Let
`h=X/log^D X` with `D>A`. For
`h+1≤m≤X-h`, the target `2m` has overlap

\[
\operatorname{meas}([1,X]\cap[2m-X,2m-1])
=\min(2m-2,2X-2m)\ge2h.
\]

Hence all but `O_A(X/log^A X)` such midpoints are generated from primes at
most `X`; the omitted endpoints contain `O(h+1)` integers. This recovers
the original full filling bound `H_{j+1}(X)≪_A X/log^A X` without an
almost-equal-primes theorem. It would preserve the original summable-loss
argument and its positive amplitude conclusion once the extended analytic
lemma is written and checked.

For the present exposition, the revised proof remains the lower-risk choice:
its analytic interface and subsequent dynamics already match the active Lean
development. The stronger route is worthwhile if a single asymptotic constant
is intended as a headline result.

**8. Make the paper's status and its logical dependencies precise.**

The current formal theorem in `lean/ConwayGolden/Subprime/StandardMain.lean`
has an explicit hypothesis `h : CircleMethod.StandardInputs`. It verifies the
deduction from Siegel–Walfisz and the Vaughan-form bound to the golden-ratio
limit. The proofs of those two analytic theorems remain external. The active
development does derive the restricted binary lemmas, the prime interval
lower bound, and the subsequent generation dynamics; exhaustion is proved
using Bertrand's postulate.

A suitable description is:

> The deduction from the two stated standard analytic estimates to the
> golden-ratio limit has been formalized in Lean. The analytic estimates
> themselves are supplied by the classical results cited below.

This is more informative than relying on a `no sorry` claim. It also updates
the revised manuscript's stale statement that the restricted binary results
have not been formalized. This proposal used source inspection, not a fresh
build or an independent audit of the entire development.

For the finished paper, use the following order: definition and main theorem;
parity and the two-layer picture; one restricted binary lemma; filling and
propagation; the prime-extension mechanism; the abstract bounded-step
comparison; cardinality limits. Put the circle-method proof and the precise
formalization boundary in appendices. Treat the positive-amplitude theorem
as a separate stronger result if it is retained.
