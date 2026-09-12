# Approximate prime completeness and the Conway cardinality ratio

7 September 2026 — proof draft developed in this workspace, not independently reviewed. This extends the preliminary arguments in [research.md](research.md). It is not a claim that the cited sources state the Conway result.

## Statement

Let \(s(m)=m\) for prime \(m\), and \(s(m)=m/\operatorname{lpf}(m)\) for composite \(m\). Define

\[
C_0=\{1\},\qquad C_{n+1}=C_n\cup\{s(a+b):a,b\in C_n\}.
\]

Repeated inputs are allowed. Write \(M_n=\max C_n\), and let \(Q_n\) be the prime immediately before the first prime absent from \(C_n\), for \(n\ge1\). Thus every prime at most \(Q_n\) is present, and \(Q_n\le M_n\). Put \(\varphi=(1+\sqrt5)/2\).

The argument below gives

\[
\boxed{Q_n/M_n\longrightarrow1.}
\]

Consequently, for some \(c>0\),

\[
M_n\sim c\varphi^n,\qquad
|C_n|\sim c\varphi^{n-1},\qquad
\boxed{\frac{|C_{n+1}|}{|C_n|}\longrightarrow\varphi},\qquad
\frac{|C_n|}{M_n}\longrightarrow\frac1\varphi.
\]

The proof does not assert that the solid core reaches \((1-o(1))M_{n-1}\). It permits an exceptional set of missing composite integers.

## 1. Analytic inputs

We use the known exhaustion \(\bigcup_n C_n=\mathbb N\), proved in Theorem 1 of [Caragiu–Vicol–Zaki (2017)](https://www.fq.math.ca/Papers1/55-4/CaragiuVicolZaki03162017.pdf). The same paper poses the cardinality limit as Conjecture 3.

The first analytic fact is the following consequence of the almost-all theorem for Goldbach representations with nearly equal summands:

**Goldbach filling lemma.** For every fixed \(A>0\), if all primes at most \(X\) belong to \(C_j\), then

\[
|[1,\lfloor X\rfloor]\setminus C_{j+1}|
\ll_A X(\log X)^{-A}. \tag{1}
\]

Indeed, the corollary to Theorem 1 of [Coppola–Laporta (1995)](https://www.giovannicoppola.name/files/articoli/8_giovanni_coppola_number_theory_seminar_politecnico_torino_245.pdf), taking exponent \(3/4>5/8\), supplies \(2m=p+q\) with \(|p-m|,|q-m|\le m^{3/4}\), except for \(O_A(X/\log^A X)\) midpoints. Restrict first to \(m\le X-X^{3/4}\) so both primes are at most \(X\), sum over dyadic scales, and discard \(m\le\sqrt X\). The discarded terms \(O(X^{3/4})\) are smaller than the stated error. Then \(s(2m)=m\).

We use the classical prime number theorem with error term to count primes in intervals of length \(X/(\log X)^2\):

\[
\pi(X)-\pi\left(X-\frac{X}{\log^2X}\right)
\sim\frac{X}{\log^3X}. \tag{2}
\]

For the underlying PNT, see [Evertse, Chapter 1, p. 53](https://pub.math.leidenuniv.nl/~evertsejh/ant18-1.pdf).

The new input is an almost-all statement with **specified intervals** for the two prime variables. Its proof from standard circle-method estimates is provided in the appendix.

**Fixed-interval binary lemma.** Fix \(0<\alpha<\beta\), \(0<\gamma<\delta\), \(\eta>0\), \(B>0\), and \(A>0\). Set

\[
I_X=[\alpha X,\beta X],\qquad J_X=[\gamma X,\delta X],
\]

and

\[
\mathcal J_X(N)=\operatorname{length}\{u\in I_X:N-2u\in J_X\}.
\]

Among odd integers \(1\le N\le BX\) satisfying \(\mathcal J_X(N)\ge\eta X\), at most

\[
O(X/\log^A X)
\]

fail to admit \(N=2p+q\) with primes \(p\in I_X\), \(q\in J_X\). All constants may depend on the fixed interval data and on \(A\). No assertion is made for every individual odd \(N\).

## 2. The two asymptotic constants

We recall and justify the preliminary fact

\[
M_n\sim c\varphi^n,\qquad Q_n\sim d\varphi^n,
\qquad 0<d\le c. \tag{3}
\]

Any composite output formed from \(C_n\) is at most \(M_n\). Hence

\[
C_n\subseteq[1,M_{n-1}]\cup\{p\le M_n:p\text{ prime}\}. \tag{4}
\]

A new maximum is prime. Apart from the directly checked initial step, it is an odd-plus-even sum, whose even summand is at most \(M_{n-1}\). Thus

\[
M_{n+1}\le M_n+M_{n-1},\qquad M_n\le F_{n+2}. \tag{5}
\]

For a lower bound, suppose that all primes up to \(X\) are in \(C_n\), and all primes up to \(Y\) are in \(C_{n-1}\), with \(Y\le X\le2Y\). Equation (1) bounds the missing integers up to \(Y\) in \(C_n\) by \(O(Y/\log^4Y)\). Put \(h=X/\log^2X\). For a prime

\[
X<r\le X+Y-h,
\]

each prime \(p\in[X-h,X]\) gives a distinct positive even difference \(r-p\le Y\). By (2), there are more such primes than missing differences, for large \(X\). Some difference lies in \(C_n\), so \(r\in C_{n+1}\).

Starting from a sufficiently large interval present in some \(C_N\), we can therefore construct prime cutoffs

\[
L_0=L_1=L,\qquad
L_{k+1}=L_k+L_{k-1}-\frac{L_k}{\log^2L_k},
\]

with all primes at most \(L_k\) in \(C_{N+k}\). The cutoffs grow at least geometrically, and their relative losses have finite sum. More explicitly, \(u_k=L_k/\varphi^k\) satisfies

\[
u_{k+1}\ge(1-\epsilon_k)
\left(\frac{u_k}{\varphi}+\frac{u_{k-1}}{\varphi^2}\right),
\qquad \epsilon_k=\frac1{\log^2L_k},\qquad\sum_k\epsilon_k<\infty.
\]

The minimum of two successive \(u_k\)'s stays bounded away from zero, by the positive infinite product \(\prod_k(1-\epsilon_k)\). Thus \(M_n\asymp Q_n\asymp\varphi^n\).

Define

\[
T_n=\frac{M_n+M_{n-1}/\varphi}{\varphi^n}.
\]

By (5), \(T_n\) is non-increasing, and it is bounded away from zero. If \(T_n\to t>0\), the identity

\[
M_n/\varphi^n=T_n-\varphi^{-2}(M_{n-1}/\varphi^{n-1})
\]

implies \(M_n/\varphi^n\to c=t/(1+\varphi^{-2})>0\).

For \(Q_n\), repeat the cutoff extension with \(X=Q_n,Y=Q_{n-1}\). Their ratio is bounded, which suffices in place of the bound 2 once \(n\) is large. Using (2) once more to pass to the prime preceding the new real cutoff gives

\[
Q_{n+1}\ge Q_n+Q_{n-1}-O(Q_n/\log^2Q_n).
\]

Therefore

\[
V_n=\frac{Q_n+Q_{n-1}/\varphi}{\varphi^n}
\quad\text{satisfies}\quad
V_{n+1}-V_n\ge-O(n^{-2}).
\]

It is bounded and bounded away from zero. Adding suitable partial sums of \(\sum n^{-2}\) makes it bounded and non-decreasing, so it converges. The same contracting identity as for \(M_n\) gives \(Q_n/\varphi^n\to d>0\). This proves (3).

## 3. An outlying prime creates an almost-complete interval of primes

Suppose, for a contradiction, that \(d<c\). Choose a fixed integer \(k\ge0\) such that

\[
d<T:=c\varphi^{-k}\le\varphi d.
\]

Such a \(k\) exists by scaling \(c/d>1\) down by successive powers of \(\varphi\), stopping before reaching 1. Set

\[
X=\varphi^{n-1},\qquad t_n=M_{n-1-k}.
\]

Every maximum after the initial stage is prime. By retention, \(t_n\in C_{n-1}\), and

\[
t_n=TX+o(X),\quad Q_{n-1}=dX+o(X),\quad Q_n=\varphi dX+o(X).
\]

Write \(\Delta=T-d>0\) and \(\varepsilon=\Delta/16\). Consider three fixed intervals scaled by \(X\):

\[
\begin{aligned}
I_X&=[(\varphi d-2\varepsilon)X,(\varphi d-\varepsilon)X],\\
J_X&=[(2d-T+3\varepsilon)X,(2d-T+9\varepsilon)X],\\
U_X&=[(\varphi^2d+\varepsilon)X,(\varphi^2d+2\varepsilon)X].
\end{aligned} \tag{6}
\]

For sufficiently large \(n\), every prime in \(I_X\) lies in \(C_n\), and every prime in \(J_X\) lies in \(C_{n-1}\). To check the latter assertion, its upper endpoint is

\[
(2d-T+9\varepsilon)X=(d-7\varepsilon)X< Q_{n-1},
\]

while the lower endpoint is positive because \(T\le\varphi d<2d\).

For every integer \(u\in U_X\), consider

\[
2p+q=2u-t_n. \tag{7}
\]

The right-hand side is odd. For any real \(p\in I_X\), the corresponding real value \(q=2u-t_n-2p\) lies between

\[
(2d-T+4\varepsilon)X+o(X)
\quad\text{and}\quad
(2d-T+8\varepsilon)X+o(X).
\]

It therefore lies in \(J_X\), with positive margin, for large \(n\). The real solution interval for \(p\) has length \(\varepsilon X\). The fixed-interval binary lemma applies to (7).

The map \(u\mapsto2u-t_n\) is injective. Thus all but \(O_A(X/\log^A X)\) integers \(u\in U_X\) admit (7) with the required prime inputs. If such a \(u\) is itself prime, then

\[
b=\frac{t_n+q}{2}\in C_n,
\qquad
u=p+b\in C_{n+1}. \tag{8}
\]

Here \(t_n,q\in C_{n-1}\) are odd primes, so their even sum is divided by 2. The final sum is kept because \(u\) is prime. In fact \(b=u-p\) is even, as required by that final odd prime sum.

We have proved that \(C_{n+1}\) contains all but \(O_A(X/\log^A X)\) primes in the interval \(U_X\), which lies a fixed positive distance beyond the asymptotic complete prime prefix \(\varphi^2dX\).

## 4. The next generation cannot have its proposed first missing prime

Let \(r_n\) be the first prime missing from \(C_{n+2}\). It is the prime immediately after \(Q_{n+2}\), so the PNT and (3) give

\[
r_n=\varphi^3dX+o(X).
\]

For any prime \(u\in U_X\), the difference \(a=r_n-u\) is an even integer in the range

\[
(\varphi d-2\varepsilon)X+o(X)
\le a\le
(\varphi d-\varepsilon)X+o(X),
\]

because \(\varphi^3-\varphi^2=\varphi\). Thus \(1\le a\le Q_n\) for all large \(n\).

There are asymptotically \(\varepsilon X/\log X\) primes \(u\in U_X\). Two exclusions can prevent using one:

1. The prime \(u\) is absent from \(C_{n+1}\). Section 3 bounds this by \(O_A(X/\log^A X)\).
2. The difference \(r_n-u\) is absent from \(C_{n+1}\). Equation (1), applied to the complete prime prefix \(Q_n\) in \(C_n\), bounds this by \(O_A(X/\log^A X)\). Distinct \(u\)'s give distinct differences.

Take \(A=4\). The exclusions together are \(o(X/\log X)\), so at least one candidate survives. Then

\[
u\in C_{n+1},\quad r_n-u\in C_{n+1},\quad
s\bigl(u+(r_n-u)\bigr)=r_n\in C_{n+2},
\]

contradicting the definition of \(r_n\). Therefore \(d=c\), and

\[
\boxed{Q_n\sim M_n\sim c\varphi^n.}
\]

Notice that no pointwise binary Goldbach or Lemoine conjecture was used. The variable candidate \(u\) is selected after discarding two small exceptional sets.

## 5. Cardinalities

Apply (1) with \(X=Q_{n-1}\). Since \(Q_{n-1}\sim M_{n-1}\),

\[
\begin{aligned}
|[1,M_{n-1}]\setminus C_n|
&\le M_{n-1}-Q_{n-1}
 +O(Q_{n-1}/\log^4Q_{n-1})\\
&=o(M_{n-1}).
\end{aligned}
\]

Equation (4) bounds the elements above \(M_{n-1}\) by \(\pi(M_n)=o(M_{n-1})\). Hence

\[
|C_n|\sim M_{n-1}\sim c\varphi^{n-1},
\]

which yields the claimed ratio and density limits.

## Appendix: proof of the fixed-interval binary lemma

This appendix supplies the interval restriction explicitly. The standard analytic ingredients are Siegel–Walfisz and Vaughan's bound for exponential sums over primes. The latter is stated, in a slightly stronger form, as Lemma 1 of [Kumchev, *On sums of primes from Beatty sequences* (2008)](https://tigerweb.towson.edu/akumchev/a23.pdf). A presentation of the circle-method inputs and the ordinary almost-all binary argument is in [Tao's 254A Notes 8, especially Exercise 34](https://terrytao.wordpress.com/2015/03/30/254a-notes-8-the-hardy-littlewood-circle-method-and-vinogradovs-theorem/). The coefficient-2 and interval details below are derived here.

Write \(e(z)=e^{2\pi iz}\), and use \(\phi_{\!E}\) for Euler's totient to distinguish it from the golden ratio. Put

\[
S_I(\theta)=\sum_{p\in I_X}(\log p)e(p\theta),\qquad
S_J(\theta)=\sum_{p\in J_X}(\log p)e(p\theta).
\]

The weighted representation count is

\[
R_X(N)=\int_0^1 S_I(2\theta)S_J(\theta)e(-N\theta)\,d\theta.
\]

Choose \(P=(\log X)^K\), where \(K\) is a sufficiently large fixed constant in terms of the desired saving \(A\). Use major arcs

\[
\mathfrak M=\bigcup_{q\le P}\ \bigcup_{(a,q)=1}
\{\theta\in\mathbb R/\mathbb Z:|\theta-a/q|\le P/X\}.
\]

They are disjoint for large \(X\). Let \(\mathfrak m\) be the complement.

### Minor arcs

Dirichlet approximation gives, for \(\theta\in\mathfrak m\), a reduced \(a/q\) with

\[
P<q\le X/P,\qquad |\theta-a/q|\le P/(qX)\le q^{-2}.
\]

If \(q\le P\), that approximation would lie in one of our major arcs, which explains the strict lower bound. Applying Vaughan's estimate to the two initial segments whose difference defines \(S_J\), we get

\[
\sup_{\mathfrak m}|S_J(\theta)|
\ll X P^{-1/2}(\log X)^4+X^{4/5}(\log X)^4.
\]

Also, by Parseval and the PNT,

\[
\int_0^1|S_I(2\theta)|^2\,d\theta
=\sum_{p\in I_X}(\log p)^2\ll X\log X.
\]

If \(R_{\mathfrak m}(N)\) denotes the minor-arc integral, Bessel's inequality therefore gives, for any prescribed \(D>0\) after choosing \(K\) sufficiently large,

\[
\sum_{N\in\mathbb Z}|R_{\mathfrak m}(N)|^2
\ll_D X^3(\log X)^{-D}. \tag{9}
\]

Thus \(|R_{\mathfrak m}(N)|\) exceeds a fixed positive multiple of \(X\) for at most \(O_D(X/\log^D X)\) integers.

### Major arcs and the local factor

Let

\[
V_I(\beta)=\int_{I_X}e(u\beta)\,du,\qquad
V_J(\beta)=\int_{J_X}e(u\beta)\,du.
\]

Siegel–Walfisz and partial summation give, uniformly for \(q\le P\), \(|\beta|\le P/X\), and any prescribed fixed \(E>0\),

\[
\begin{aligned}
S_J(a/q+\beta)&=\frac{\mu(q)}{\phi_{\!E}(q)}V_J(\beta)
+O_E(X\log^{-E}X),\\
S_I(2a/q+2\beta)&=\frac{\mu(q')}{\phi_{\!E}(q')}V_I(2\beta)
+O_E(X\log^{-E}X),\qquad q'=q/(q,2).
\end{aligned}
\]

Here \(K\) has already been fixed, and the implicit constants can depend on \(K,E\). The arbitrary logarithmic saving in Siegel–Walfisz absorbs the factors from summing residue classes and partial summation.

The measure of the major arcs is \(O(P^3/X)\). Choosing \(E\) sufficiently large makes the integrated approximation error smaller than any prescribed \(X/\log^A X\). Since \(|V_I(2\beta)V_J(\beta)|\ll\min(X^2,|\beta|^{-2})\), the main-term integrals can be extended to \(\mathbb R\), at cost

\[
O\left(\frac XP\sum_{q\le P}\frac1{\phi_{\!E}(q')}\right)
=O\left(\frac{X(\log(2P))^2}{P}\right).
\]

Fourier inversion gives

\[
\int_{\mathbb R}V_I(2\beta)V_J(\beta)e(-N\beta)\,d\beta
=\mathcal J_X(N).
\]

Thus the major-arc integral is, up to the stated small error,

\[
\mathfrak S_P(N)\mathcal J_X(N),\qquad
\mathfrak S_P(N)=\sum_{q\le P}
\frac{\mu(q)\mu(q')}{\phi_{\!E}(q)\phi_{\!E}(q')}c_q(N),
\]

where \(c_q(N)\) is the Ramanujan sum.

For odd \(N\), the full singular series is

\[
\mathfrak S(N)=
2\prod_{\ell>2}\left(1-\frac1{(\ell-1)^2}\right)
\prod_{\substack{\ell\mid N\\\ell>2}}\frac{\ell-1}{\ell-2}.
\tag{10}
\]

In particular \(\mathfrak S(N)\ge s_0>0\), uniformly over odd \(N\). To verify the coefficient 2, odd squarefree \(q\) contribute \(\mu(q)^2c_q(N)/\phi_{\!E}(q)^2\); even squarefree \(q=2r\) contribute the same odd-\(r\) term because \(c_2(N)=-1\). Terms with \(4\mid q\) vanish. The Euler product then gives (10).

### Controlling the singular-series tail for almost all targets

For completeness, an elementary first-moment estimate suffices here. For every integer \(N\ge1\),

\[
\sum_{q>Y}\frac{|c_q(N)|}{\phi_{\!E}(q)^2}
\ll\frac{\log^3(2Y)}Y
\sum_{h\mid N}\left(\frac{h}{\phi_{\!E}(h)}\right)^2.
\tag{11}
\]

To see this, use \(|c_q(N)|\le\sum_{h\mid(q,N)}h\) and
\(\phi_{\!E}(hk)\ge\phi_{\!E}(h)\phi_{\!E}(k)\). Then bound the tail of \(\sum_k\phi_{\!E}(k)^{-2}\) by \(O(\log^3(2z)/z)\) for \(z\ge1\), and by a constant for smaller \(z\). This tail bound follows from
\((k/\phi_{\!E}(k))^2\le\tau(k)^2\le\tau_4(k)\) and \(\sum_{k\le z}\tau_4(k)\ll z\log^3(2z)\), by partial summation.

Moreover,

\[
\begin{aligned}
\sum_{N\le BX}\sum_{h\mid N}\left(\frac h{\phi_{\!E}(h)}\right)^2
&\le BX\sum_{h\le BX}\frac{\tau_4(h)}h\\
&\ll_B X\log^4X.
\end{aligned}
\]

For odd \(N\), the discrepancy between \(\mathfrak S_P(N)\) and \(\mathfrak S(N)\) is bounded by twice the left side of (11) with \(Y=P/2\). Markov's inequality shows that

\[
|\mathfrak S_P(N)-\mathfrak S(N)|>s_0/2
\]

for at most

\[
O\left(\frac{X\log^4X\,\log^3(2P)}P\right)
=O_A(X/\log^A X)
\]

targets, on choosing \(K\) large enough.

For every other odd target with \(\mathcal J_X(N)\ge\eta X\), the major-arc contribution is at least a fixed positive multiple of \(X\). Equation (9) shows that the minor arcs can cancel this for only \(O_A(X/\log^A X)\) further targets. Hence \(R_X(N)>0\) outside the asserted exceptional set, proving the fixed-interval binary lemma.

## Scope and checks

The conclusion is asymptotic; no effective numerical convergence rate is asserted. The contradiction uses fixed positive margins after assuming \(c>d\), so no uniformity as the gap tends to zero is required. The moving integer \(t_n\) only shifts the target through an injective map; it does not alter the two fixed prime intervals or their exceptional-set estimate. Every input's generation is explicitly tracked in (8) and Section 4. No full Goldbach conjecture, prime-pair conjecture, random-independence hypothesis, or exact completeness of primes below a finite maximum is assumed.

The remaining distinction is between this proof draft and independent mathematical verification. The original solid-core saturation question also remains separate: the argument proves density sufficient for the cardinality ratio, not the disappearance of every composite hole.
