# Conway closure: maximum growth, solid cores, and the remaining ratio problem

Initial research notes, 7 September 2026. These record the first, partial stage of the argument. A subsequent [proof draft on approximate prime completeness](prime-completeness.md) supplies an argument for the remaining cardinality-ratio limit, including the additional analytic lemma. That draft has not been independently reviewed. The deductions below are supplied with proofs; they are not claimed to be results stated in the cited Conway paper. The cardinality-ratio conjecture is **not proved in this initial note**.

Let

\[
 s(t)=\begin{cases}t,&t\text{ prime},\\t/\operatorname{lpf}(t),&t\text{ composite},\end{cases}
 \qquad C_0=\{1\},\quad C_{n+1}=C_n\cup s(C_n+C_n).
\]

Repeated inputs are allowed. Put

\[
 M_n=\max C_n,\qquad K_n=\max\{k:[1,k]\subseteq C_n\},\qquad a_n=|C_n|,
 \qquad \varphi=(1+\sqrt5)/2.
\]

The exact cardinality-ratio question appears as Conjecture 3 in [Caragiu–Vicol–Zaki, *Fibonacci Quarterly* 55 (2017), 327–331](https://www.fq.math.ca/Papers1/55-4/CaragiuVicolZaki03162017.pdf). Their Theorem 1 proves that the union of the sets is all positive integers. We use that exhaustion result to start an asymptotic argument with an arbitrarily large finite interval already present.

## Results established in these notes

Using the classical prime number theorem with its error term and the almost-all Goldbach theorem with almost equal summands stated below, one obtains

\[
 M_n\sim c\varphi^n\quad(c>0),\qquad a_n=\Theta(\varphi^n),\qquad K_n=\Theta(\varphi^n).
\]

In particular, the ratio of successive **maxima** tends to the golden ratio, and the nth-root growth rates of both cardinality and solid core are the golden ratio. This does not establish \(a_{n+1}/a_n\to\varphi\). It does imply that if the latter ratio has a limit, that limit must be \(\varphi\).

A sufficient additional statement is

\[
 K_n/M_{n-1}\longrightarrow1.
\]

It would imply \(a_n\sim M_{n-1}\), the desired cardinality ratio, and the global density \(a_n/M_n\to1/\varphi\). A weaker sufficient statement is that only \(o(M_{n-1})\) integers below \(M_{n-1}\) are missing.

## 1. The exact upper bound

A composite input sum made at time \(n+1\) produces an output at most \(M_n\). Thus every composite in \(C_{n+1}\) is at most \(M_n\). For \(n\ge2\), every even element of \(C_n\) is therefore at most \(M_{n-1}\); the exceptional prime 2 also satisfies this bound.

If the maximum increases, it increases to an odd prime. Its two summands have opposite parity. Consequently, for \(n\ge2\),

\[
 M_{n+1}\le M_n+M_{n-1}.
\]

The same inequality holds directly at \(n=1\). With \(M_0=1,M_1=2\), this gives \(M_n\le F_{n+2}\).

We also have the useful inclusion

\[
 C_n\subseteq[1,M_{n-1}]\cup\{p\le M_n:p\text{ prime}\}\qquad(n\ge1).
\]

The region beyond the previous maximum contains only primes, so it contributes \(O(M_n/\log M_n)\) elements.

## 2. The analytic input and its precise consequence

We use the corollary to Theorem 1 of [Coppola–Laporta (1995), *On the representation of even integers as sum of two almost equal primes*](https://www.giovannicoppola.name/files/articoli/8_giovanni_coppola_number_theory_seminar_politecnico_torino_245.pdf): for every fixed \(A>0\), all but \(O_A(X/(\log X)^A)\) midpoints \(m\in[X,2X]\) admit

\[
 2m=p+q,\qquad |p-m|,|q-m|\le m^{3/4},
\]

with both summands prime. The exponent \(3/4\) is a deliberately non-optimal admissible choice.

It follows that, whenever all primes at most \(X\) belong to \(C_j\),

\[
 H_{j+1}(X):=|[1,\lfloor X\rfloor]\setminus C_{j+1}|
 \ll_A X/(\log X)^A. \tag{1}
\]

To check the upper cutoff, first restrict to \(m\le X-X^{3/4}\); then \(m+m^{3/4}\le X\). The omitted upper boundary has \(O(X^{3/4})\) elements. Sum the exceptional-set estimate over dyadic intervals between \(\sqrt X\) and \(X\), and discard the \(O(\sqrt X)\) smaller midpoints. Both discarded terms are smaller than \(X/(\log X)^A\) for every fixed \(A\), for sufficiently large \(X\). Finally, \(s(p+q)=s(2m)=m\). This proves (1).

We also use

\[
 \#\{p\text{ prime}:X-X/(\log X)^2\le p\le X\}
 \sim X/(\log X)^3. \tag{2}
\]

This follows from the classical PNT error \(\pi(x)=\operatorname{Li}(x)+O(xe^{-c\sqrt{\log x}})\); see [Evertse's analytic number theory notes, Chapter 1, p. 53](https://pub.math.leidenuniv.nl/~evertsejh/ant18-1.pdf). Mere \(\pi(x)\sim x/\log x\), without a quantitative error, is not the justification for (2).

## 3. A prime-prefix bootstrap with summable losses

Suppose all primes up to \(X\) lie in \(C_n\), and all primes up to \(Y\) lie in \(C_{n-1}\), where \(Y\le X\le2Y\). By (1), \(C_n\) misses at most

\[
 H\ll Y/(\log Y)^4
\]

integers up to \(Y\). Set \(\delta=X/(\log X)^2\).

Consider any prime \(r\) with

\[
 X<r\le X+Y-\delta.
\]

For every prime \(p\in[X-\delta,X]\), the difference \(r-p\) is a positive even integer at most \(Y\). Distinct primes give distinct differences. By (2), the number of choices for \(p\) is asymptotic to \(X/(\log X)^3\), and eventually exceeds \(H\). Therefore at least one difference belongs to \(C_n\). For that choice,

\[
 r=s\bigl(p+(r-p)\bigr)\in C_{n+1}.
\]

All primes at most \(X\) were already present. Hence all primes through \(X+Y-\delta\) belong to \(C_{n+1}\).

Choose a sufficiently large \(L\). By exhaustion, \([1,\lceil L\rceil]\subseteq C_N\) for some \(N\). Define real cutoffs

\[
 L_0=L_1=L,\qquad
 L_{k+1}=L_k+L_{k-1}-\frac{L_k}{(\log L_k)^2}\quad(k\ge1).
\]

Induction using the preceding argument gives

\[
 \{p\le L_k:p\text{ prime}\}\subseteq C_{N+k}.
\]

For large enough starting \(L\), the ratios remain between 1 and 2, and

\[
 L_{k+1}\ge L_k+\tfrac12L_{k-1}\ge\tfrac54L_k.
\]

Thus \(\log L_k\gg k+1\), so \(\sum_k(\log L_k)^{-2}<\infty\).

To obtain the sharp exponential lower bound, put \(u_k=L_k/\varphi^k\) and \(\epsilon_k=(\log L_k)^{-2}\). Since \(\varphi^{-1}+\varphi^{-2}=1\),

\[
 u_{k+1}\ge(1-\epsilon_k)
 \left(\frac{u_k}{\varphi}+\frac{u_{k-1}}{\varphi^2}\right).
\]

Writing \(v_k=\min(u_k,u_{k-1})\) gives \(v_{k+1}\ge(1-\epsilon_k)v_k\). The infinite product \(\prod_k(1-\epsilon_k)\) is positive. Consequently

\[
 L_k\gg\varphi^k.
\]

The Fibonacci upper bound gives the reverse estimate. By (1), the next generation contains \(L_k-O(L_k/\log^4 L_k)\) integers below \(L_k\). Accounting for the fixed starting time \(N\),

\[
 M_n\asymp\varphi^n,\qquad a_n\asymp\varphi^n. \tag{3}
\]

## 4. Why the maximum has a ratio limit

The one-sided Fibonacci inequality is stronger than a mere upper exponential bound. Define

\[
 T_n=\frac{M_n+M_{n-1}/\varphi}{\varphi^n},\qquad
 d_n=M_n+M_{n-1}-M_{n+1}\ge0.
\]

Then

\[
 T_{n+1}=T_n-d_n/\varphi^{n+1}.
\]

Thus \(T_n\) decreases to a limit \(t\ge0\). By (3), \(t>0\). Setting \(x_n=M_n/\varphi^n\), we have

\[
 x_n=T_n-\varphi^{-2}x_{n-1}.
\]

This stable linear recurrence gives \(x_n\to t/(1+\varphi^{-2})=:c>0\). Hence

\[
 \boxed{M_n\sim c\varphi^n,\qquad M_{n+1}/M_n\to\varphi.}
\]

This is an unconditional deduction from the stated analytic inputs and the known exhaustion theorem.

## 5. What can be proved for an actual solid core

Here is an elementary additive-combinatorial smoothing lemma. If \(A\subseteq[1,\lfloor X\rfloor]\) misses \(o(X)\) integers, then for all large \(X\), every integer

\[
 X/4\le m\le3X/4
\]

has a representation \(2m=a+b\) with \(a,b\in A\). Indeed the candidate values \(a\) with both \(a\) and \(2m-a\) in the ambient interval number at least \(X/2-O(1)\). Each hole rules out at most two candidates. Thus some candidate survives. This generates \(m\) by the division-by-2 branch.

Apply this to the almost-full interval up to \(L_k\) in \(C_{N+k+1}\). Then \(C_{N+k+2}\) contains the interval \([\lceil L_k/4\rceil,\lfloor3L_k/4\rfloor]\). These intervals overlap for successive \(k\), because \(L_k\le2L_{k-1}\); the initially present interval \([1,\lceil L\rceil]\) anchors their union at 1. Consequently

\[
 K_{N+k+2}\ge\lfloor3L_k/4\rfloor,
\]

and therefore \(K_n=\Theta(\varphi^n)\). This proves the core's exponential rate but not the sharp saturation \(K_n\sim M_{n-1}\).

## 6. Precise sufficient conditions for the cardinality ratio

If

\[
 |[1,M_{n-1}]\setminus C_n|=o(M_{n-1}), \tag{4}
\]

the inclusion in Section 1 and PNT give

\[
 a_n=M_{n-1}+o(M_{n-1}).
\]

Together with Section 4, this proves

\[
 \frac{a_{n+1}}{a_n}\to\varphi,
 \qquad\frac{a_n}{M_n}\to\frac1\varphi.
\]

The solid-core statement \(K_n/M_{n-1}\to1\) implies (4), but is stronger than necessary.

There is another sufficient condition adapted to the analytic input. Let \(Q_n\) be the prime immediately before the first prime missing from \(C_n\). Then

\[
 Q_n/M_n\to1 \tag{5}
\]

would imply (4) through (1). This only requires a complete prefix of primes, not a complete prefix of integers.

In fact the same bootstrap shows that \(Q_n\sim d\varphi^n\) for some \(0<d\le c\). Here are the details. The constructed cutoffs and (3) imply \(Q_n\asymp\varphi^n\). Thus successive \(Q_n\)'s are comparable. The counting argument of Section 3, followed by (2) to pass from a real cutoff to its preceding prime, gives

\[
 Q_{n+1}\ge Q_n+Q_{n-1}-O(Q_n/(\log Q_n)^2).
\]

For \(V_n=(Q_n+Q_{n-1}/\varphi)/\varphi^n\), it follows that
\(V_{n+1}-V_n\ge-O(n^{-2})\). The sequence is bounded above and bounded away from zero. Adding the partial sums of a suitable convergent positive multiple of \(\sum n^{-2}\) makes it bounded and nondecreasing, hence convergent. The stable recurrence used in Section 4 then gives \(Q_n/\varphi^n\to d>0\).

Thus (5) asks whether the two positive leading constants agree: \(d=c\). No proof of that equality is supplied here. It is a sufficient route, not an asserted equivalence to the original conjecture.

## 7. Why solid-core saturation encounters a Goldbach barrier

Fix \(n\ge2\) and a **composite** integer \(m\) such that

\[
 \frac{M_n+M_{n-1}}2<m\le M_n.
\]

It is not already in \(C_n\), because \(m>M_{n-1}\). Any representation producing it must have input sum \(\ell m\), with \(\ell\) prime. Since \(M_n\le2M_{n-1}\), the displayed lower bound implies \(m>2M_n/3\). Hence \(\ell\ge3\) is impossible: the input sum would exceed \(2M_n\).

Therefore \(\ell=2\). Both summands of \(2m\) must exceed \(M_{n-1}\): if one were at most that bound, the sum would be at most \(M_n+M_{n-1}\). Every generated integer above \(M_{n-1}\) is prime. We obtain the exact equivalence

\[
 \boxed{m\in C_{n+1}\iff 2m=p+q\text{ for primes }p,q\in C_n}
\]

throughout this upper band, for composite \(m\).

Since \(M_{n-1}/M_n\to1/\varphi\), the band's lower endpoint is asymptotically \(0.80901699\ldots M_n\). Thus full solid-core saturation includes a pointwise Goldbach problem on a substantial moving interval. The almost-all theorem does not eliminate every hole there.

## 8. Small divisors, adics, and covering systems

For a prime \(\ell\) and integer \(m\ge2\), the composite input \(\ell m\) has least prime factor \(\ell\) exactly when

\[
 \gcd\left(m,\prod_{q<\ell,\ q\text{ prime}}q\right)=1.
\]

The corresponding inverse branch generates \(m\) whenever \(\ell m\in C_n+C_n\).

* \(\ell=2\): no restriction on \(m\). In particular an even target can only be generated through this composite branch, because every \(\ell m\) with odd \(\ell\) is even and has least prime factor 2.
* \(\ell=3\): \(m\) must be odd, and \(3m\in C_n+C_n\).
* \(\ell=5\): \(m\) must be coprime to 6, and \(5m\in C_n+C_n\).

All \(\ell\ge3\) branches land at most at \(2M_n/3\). They can help fill the interior but cannot directly fill the upper band in Section 7.

Modulo \(2^k\), one should track the two parity classes before averaging, since division by 2 is not an invertible operation on \(\mathbb Z_2\). An even target \(m\) requires a sum divisible by 4; an odd target requires an even sum congruent to 2 modulo 4. These are exact local constraints, not independence assumptions.

Finite covering systems of residue classes could organize which small-divisor branch is locally admissible. To turn this into a proof one still needs an additive representation in the finite sets at the correct generation. Congruence coverage alone gives neither that representation nor the prime pairs needed at the boundary. This is why exceptional-set estimates, prime counts in intervals, and the elementary dense-sumset intersection argument are particularly relevant tools here.

## 9. Reproducible computation

`conway.cpp` computes each sumset by exact modular convolution (NTT), then applies the least-prime-factor map. The modulus is 2013265921 and transform lengths divide \(2^{27}\). Every representation count is smaller than the modulus, so a zero coefficient is an exact test for absence. Direct convolution checks every coefficient for the smaller stages. No floating-point rounding is used to decide membership.

Run from this directory:

```sh
clang++ -O3 -std=c++17 conway.cpp -o /tmp/conway-exact
/tmp/conway-exact 32 > experiment.txt
```

The cardinalities reproduce the 2017 table through generation 32. Selected independent outputs:

| n | size | maximum | solid core | core / previous maximum |
|---:|---:|---:|---:|---:|
| 20 | 5,961 | 9,049 | 5,542 | 0.991235915 |
| 24 | 40,442 | 61,949 | 38,043 | 0.993315752 |
| 28 | 274,963 | 424,429 | 261,858 | 0.998196934 |
| 32 | 1,873,356 | 2,908,723 | 1,796,920 | 0.999581125 |

At generation 32 only 119 integers at most the previous maximum 1,797,673 are missing. The remaining 75,802 elements lie above that previous maximum and are prime.

It is false that all primes below the maximum are always generated: at generation 27 the maximum is 262,331, but the prime 262,321 is absent. At generation 29 four primes below the maximum are absent. These finite observations support approximate prime completeness but prevent assuming exact completeness in a proof.

The remaining task is (4), or a sufficient sharper statement such as solid-core saturation or (5). None is inferred from the finite computation or from the nth-root growth result.
