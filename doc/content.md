# Improving $R(3,k)$ in just two bites

A guided tour of the proofs, from the beginning

Companion notes for a talk on the paper of Zion Hefty, Paul Horn, Dylan King and Florian Pfender (arXiv:2510.19718, v3 of 20 February 2026). Written for someone who is not a specialist: every step is spelled out, and nothing is assumed beyond what a graph is.

::: note How to read this
Sections 1–6 are elementary and completely self-contained; if you follow them you can follow everything else. Section 7 sets up an exchange rate that converts "I built a graph" into "here is a Ramsey bound", and Section 8 puts every result of the last sixty-five years on a single axis. Sections 9–14 are the paper itself. Section 15 is the takeaway — if you read only two pages, read those.

Statements marked **Theorem** or **Lemma** are proved here in full unless the proof explicitly says otherwise. Where I give a heuristic instead of a proof, it says so in the margin note. Section 16 lists exactly what is and is not proved.
:::

---

## 1. The question

A **graph** $G$ is a set $V(G)$ of vertices together with a set of edges, each edge joining two vertices. Two vertices joined by an edge are **adjacent**, or **neighbours**. We write $n = |V(G)|$.

Two definitions carry the whole subject.

::: def
A **triangle** is a set of three vertices, every two of which are adjacent. A graph is **triangle-free** if it contains none.

An **independent set** is a set of vertices, no two of which are adjacent. The **independence number** $\alpha(G)$ is the size of the largest independent set in $G$.
:::

Now colour every pair of $n$ points either red or blue.

::: def
$R(\ell,k)$ is the least $N$ such that every red/blue colouring of the pairs of an $N$-element set contains $\ell$ points with all pairs red, or $k$ points with all pairs blue.
:::

Ramsey proved in 1930 that this number is finite. The classical illustration is $R(3,3)=6$: among any six people, three are mutual acquaintances or three are mutual strangers.

::: prop
$R(3,3) = 6$.
:::

::: proof
*Six suffices.* Fix a point $v$ among the six. It is joined to the other five, so by the pigeonhole principle at least three of those five pairs get the same colour; say $v$ is joined in red to $x,y,z$. If any pair among $x,y,z$ is red, that pair together with $v$ is a red triangle. If not, $x,y,z$ are pairwise blue, a blue triangle.

*Five does not.* Place five points in a circle and colour a pair red exactly when the points are adjacent on the circle. The red graph is a $5$-cycle, which has no triangle; and any three of the five points contain two circle-neighbours, so no three are pairwise blue.
:::

Exact values are hopeless in general — $R(3,9) = 36$ is known, $R(3,10)$ is only known to be $40$ or $41$ — so the subject is asymptotic. We fix $3$ and let $k \to \infty$.

## 2. The dictionary

This is the translation that turns a question about colourings into a question about one graph. Everything afterwards is on the graph side.

::: theorem The dictionary
$R(3,k) > n$ if and only if there exists a graph $G$ on $n$ vertices such that
$$G \text{ is triangle-free} \qquad\text{and}\qquad \alpha(G) < k .$$
:::

::: proof
A red/blue colouring of all pairs of an $n$-set is the same thing as a graph $G$ on those $n$ vertices: let the red pairs be the edges of $G$, so the blue pairs are exactly the non-edges. Under this correspondence, a set of $\ell$ points with all pairs red is a set of $\ell$ pairwise adjacent vertices, and a set of $k$ points with all pairs blue is an independent set of size $k$.

So a colouring of the $n$-set with no red triangle and no blue $K_k$ is precisely a graph $G$ on $n$ vertices that is triangle-free and has $\alpha(G) < k$. Such a colouring exists if and only if $n$ is too small to force the pattern, i.e. if and only if $R(3,k) > n$.
:::

We call a graph as in the theorem a **witness** for $n$: a certificate that $n$ vertices are not yet enough.

::: idea The shape of the whole subject
The dictionary splits the problem into two opposite activities.

- To prove a **lower bound** on $R(3,k)$ — "$R(3,k)$ is large" — you must **build a witness**: one triangle-free graph on many vertices whose independent sets are all small. This is where today's paper lives.
- To prove an **upper bound** — "$R(3,k)$ is small" — you must prove a theorem about **every** triangle-free graph, namely that it has a large independent set. A theorem about all graphs kills all witnesses, and killing witnesses bounds $R(3,k)$ from above.

Constructions build witnesses; theorems destroy them.
:::

---

## 3. Two ways to find an independent set

Write $\Delta(G)$ for the largest degree in $G$ and $d$ for the **average** degree, so that $d = 2|E(G)|/n$. Both of the following are two-line arguments, and together they are the entire tension of the problem.

::: lemma Neighbourhoods are independent
If $G$ is triangle-free, then $\alpha(G) \ge \Delta(G) \ge d$.
:::

::: proof
Let $v$ be a vertex of maximum degree and let $N(v)$ be its set of neighbours. If two vertices $u,w \in N(v)$ were adjacent, then $u,v,w$ would be a triangle. Since $G$ has none, $N(v)$ is an independent set, and it has $\Delta(G)$ elements. As $\alpha(G)$ is the size of the largest independent set and we have just exhibited one of size $\Delta(G)$, we get $\alpha(G) \ge \Delta(G)$. Finally $\Delta(G) \ge d$ because a maximum is at least an average.
:::

So making the graph dense hands the enemy a large independent set for free. The opposite pressure is just as simple.

Both proofs share a shape worth naming, because every lower bound on $\alpha$ in these notes has it: **exhibit an independent set, then measure it.** Since $\alpha(G)$ is the size of the largest one, producing any independent set at all bounds $\alpha(G)$ from below — and if the set was produced at random, its *expected* size will do, because a fixed number that beats a random quantity always beats that quantity's average.

::: lemma Greedy, or Caro–Wei
For every graph $G$,
$$\alpha(G) \;\ge\; \sum_{v \in V(G)} \frac{1}{d(v)+1} \;\ge\; \frac{n}{d+1},$$
where $d(v)$ is the degree of $v$ and $d$ is the average degree.
:::

::: proof
Take a uniformly random ordering of the vertices — think of them arriving one at a time — and let
$$I \;=\; \{\,v : v \text{ arrives before \emph{every} neighbour of } v\,\}.$$

**First, why is $I$ independent?** This needs an argument, because the definition of $I$ tests **one vertex at a time**: it never mentions pairs, so nothing in it obviously prevents two adjacent vertices from both passing their own test. Suppose they did — that $u$ and $v$ are adjacent and both lie in $I$. Then:

- $u \in I$ says $u$ arrives before all of $u$'s neighbours, and $v$ is one of them, so $u$ arrives before $v$;
- $v \in I$ says $v$ arrives before all of $v$'s neighbours, and $u$ is one of them, so $v$ arrives before $u$.

Both cannot hold in one ordering, so no such pair exists and $I$ is independent. (In words: $I$ is everyone who arrives before all of their own friends. Two friends can never both qualify — one of them arrives first, and then the other has a friend who arrived earlier.)

**Now the step that brings in $\alpha$.** By definition $\alpha(G)$ is the size of the *largest* independent set, so any independent set we can exhibit is a lower bound for it:
$$\alpha(G) \;\ge\; |I| \qquad\text{for every ordering.}$$
The left-hand side is a fixed number, the right-hand side is random; taking expectations of both sides therefore gives $\alpha(G) \ge \mathbb{E}|I|$. (Equivalently: some ordering must do at least as well as the average, and for that ordering $\alpha(G) \ge |I| \ge \mathbb{E}|I|$.)

**It remains to compute $\mathbb{E}|I|$.** A vertex $v$ lies in $I$ exactly when $v$ comes first among the $d(v)+1$ vertices of $\{v\}\cup N(v)$, and in a uniformly random ordering each of those $d(v)+1$ vertices is equally likely to be first, so $\mathbb{P}(v \in I) = 1/(d(v)+1)$. By linearity of expectation,
$$\mathbb{E}|I| \;=\; \sum_{v} \mathbb{P}(v\in I) \;=\; \sum_v \frac{1}{d(v)+1},$$
which gives the first inequality. For the second, the function $x \mapsto 1/(x+1)$ is convex on $x \ge 0$, so by Jensen's inequality $\frac1n\sum_v \frac{1}{d(v)+1} \ge \frac{1}{d+1}$, where $d$ is the average of the $d(v)$.
:::

## 4. The first real bound, and the shape of everything to come

::: theorem
Every triangle-free graph on $n = k^2$ vertices satisfies $\alpha(G) \ge k$. Consequently
$$R(3,k) \;\le\; k^2 .$$
:::

::: proof
Let $G$ be triangle-free on $k^2$ vertices and put $t = \Delta(G)$.

If $t \ge k$, then $\alpha(G) \ge t \ge k$ by the neighbourhood lemma.

If $t \le k-1$, then every degree is at most $k-1$, so by the greedy lemma
$$\alpha(G) \;\ge\; \frac{n}{t+1} \;\ge\; \frac{k^2}{k} \;=\; k .$$

Either way $\alpha(G) \ge k$, so no witness on $k^2$ vertices exists, and the dictionary gives $R(3,k) \le k^2$.
:::

::: idea The one tension, in its simplest form
Look at what just happened. You are trying to build a graph with no large independent set, and you have exactly **one number to choose**: how dense to make it.

- Too dense, and some neighbourhood is a large independent set ($\alpha \ge \Delta$).
- Too sparse, and greedy finds a large independent set ($\alpha \ge n/(d+1)$).

The two pressures cross at $d \approx \sqrt{n}$, and that crossing gives $\alpha \approx \sqrt n$. Every refinement in the next sixty-five years is this same balance with logarithms inserted in the right places.
:::

## 5. Random graphs and the first moment

::: def
$G(n,p)$ is the random graph on $n$ vertices in which each of the $\binom n2$ pairs is an edge independently with probability $p$.
:::

::: note Notation: counting with indicators
Both moment methods below rest on one device. For a fixed set $S$ of $a$ vertices, define a number that depends on how the random graph came out:
$$\mathbb{1}_S \;=\; \begin{cases} 1 & \text{if } S \text{ happens to be independent},\\ 0 & \text{otherwise.}\end{cases}$$
This is called an **indicator random variable**: it turns a yes/no question into a number one can add and average. Three facts are all we need.

1. **Its average is a probability.** $\mathbb{E}[\mathbb{1}_S] = 1\cdot\mathbb{P}(S\text{ independent}) + 0\cdot\mathbb{P}(\text{not}) = \mathbb{P}(S \text{ independent})$.
2. **Counting is adding indicators.** If $X$ is the number of independent $a$-sets, then $X = \sum_S \mathbb{1}_S$, summed over all $\binom na$ sets $S$ of size $a$: each set contributes $1$ if it qualifies and $0$ if not. Hence, by linearity of expectation, $\mathbb{E}X = \sum_S \mathbb{P}(S\text{ independent})$.
3. **A product of indicators means "both".** Since $0\cdot0 = 0\cdot1 = 0$ and $1\cdot 1 = 1$, the product $\mathbb{1}_S\mathbb{1}_T$ is itself the indicator of the event that $S$ *and* $T$ are both independent, so $\mathbb{E}[\mathbb{1}_S\mathbb{1}_T] = \mathbb{P}(S \text{ and } T \text{ both independent})$. Squaring $X$ therefore gives $X^2 = \sum_{S,T}\mathbb{1}_S\mathbb{1}_T$, a sum over *pairs* of sets.

Point 2 deserves emphasis, because it is why the first moment is always the easy one: **linearity of expectation needs no independence.** The events "$S$ is independent" for different $S$ overlap and influence one another badly, and it does not matter at all — the average of a sum is the sum of the averages regardless. The second moment is where that entanglement finally has to be faced, and it enters exactly through how much $S$ and $T$ overlap.
:::

::: lemma Independence number of a random graph
Let $p = p(n) \to 0$ with $np \to \infty$. If
$$a \;\ge\; (1+o(1))\,\frac{2}{p}\log(np),$$
then with high probability $\alpha(G(n,p)) < a$.
:::

::: proof
Let $X$ be the number of independent sets of size $a$. A fixed set of $a$ vertices is independent exactly when all $\binom a2$ pairs inside it are non-edges, which has probability $(1-p)^{\binom a2}$, so
$$\mathbb{E}X \;=\; \binom na (1-p)^{\binom a2} \;\le\; \left(\frac{en}{a}\right)^{a} e^{-p a(a-1)/2} \;=\; \exp\!\Big(a\Big[\log \tfrac{en}{a} - \tfrac{p(a-1)}{2}\Big]\Big),$$
using $\binom na \le (en/a)^a$ and $1-p \le e^{-p}$. The bracket is negative as soon as
$$\log\frac{en}{a} \;<\; \frac{p(a-1)}{2}. \tag{$\dagger$}$$

So take $a = (1+\varepsilon)\frac{2}{p}\log(np)$ for a fixed $\varepsilon>0$ and compare the two sides.

*Right-hand side.* Immediately, $\dfrac{p(a-1)}{2} = (1+\varepsilon)\log(np) - \dfrac p2 = (1+\varepsilon+o(1))\log(np)$.

*Left-hand side.* Substituting the same $a$,
$$\frac na \;=\; \frac{np}{2(1+\varepsilon)\log(np)}, \qquad\text{so}\qquad \log\frac{en}{a} \;=\; \log(np) \;-\; \log\log(np) \;+\; O(1).$$
Since $np \to \infty$ and $\log\log x = o(\log x)$, this is $(1+o(1))\log(np)$.

The left side is therefore $(1+o(1))\log(np)$ and the right side is $(1+\varepsilon+o(1))\log(np)$, so $(\dagger)$ holds for all large $n$ — the fixed $\varepsilon$ is exactly the slack absorbed by the $(1+o(1))$ in the statement. Then $\mathbb{E}X \to 0$, and since $X$ is a non-negative integer, Markov's inequality gives $\mathbb{P}(X \ge 1) \le \mathbb{E}X \to 0$. So with high probability $X = 0$: there is no independent set of size $a$ at all, which is to say $\alpha(G(n,p)) < a$.
:::

This is the single formula we use most. But notice exactly what was proved, because the reverse direction is a different statement.

::: warn What the lemma does and does not give
The first moment bounds $\alpha$ from **above**: with high probability there is *no* independent set of size $a$. It says nothing about whether $\alpha$ might be far *smaller* than $a$.

That reverse bound is true — with high probability $\alpha(G(n,p)) \ge (1-\varepsilon)\frac2p\log(np)$ as well, so $\alpha$ is concentrated around $\frac2p\log(np)$ — but it is a genuinely different argument, the **second moment method**: for $a$ slightly below the threshold one shows $\mathbb{E}X \to \infty$ *and* $\mathrm{Var}(X) = o\big((\mathbb{E}X)^2\big)$, so Chebyshev's inequality forces $X > 0$. We do not prove it here.

It is also worth saying that neither direction is a guarantee. $G(n,p)$ can come out empty, with $\alpha = n$; "with high probability" means the exceptional outcomes have probability tending to $0$, not that they are absent.

**Where each direction is used.** Every *construction* in these notes needs only the upper bound — a witness must have $\alpha$ **small**, and that is all we ever verify (Section 6, and Section 14 for the paper itself). The lower bound is used in exactly one place, and not inside a proof: the second pressure of Section 8, where we claim that a pseudorandom graph *cannot* have independent sets smaller than a random graph of the same density. That is precisely why the barrier of Section 8 is a heuristic about pseudorandom graphs rather than a theorem about all triangle-free graphs.
:::

It is worth seeing it once at the density that will matter. For $p = c\sqrt{\log n/n}$ we have $np = c\sqrt{n\log n}$, hence $\log(np) = (\tfrac12+o(1))\log n$, and so
$$\alpha(G(n,p)) \;\approx\; \frac2p\cdot\frac{\log n}{2} \;=\; \frac{\log n}{p} \;=\; \frac1c\sqrt{n\log n}.$$
The halving of $\log n$ into $\tfrac12\log n$ — because $np$ is roughly $\sqrt n$ rather than $n$ — is what makes the formula come out as $\log n / p$ rather than $2\log n / p$, and it is used again in Sections 8 and 14.

::: note Greedy versus optimal, and a factor of $2$
Running the greedy algorithm of Lemma 3.2 on $G(n,p)$ produces about $(1/p)\log(np)$ vertices — exactly **half** of the truth. I verified this numerically: at $n = 80{,}000$ and average degree $d = np = 50$, greedy returns $6{,}282$ vertices and $n\log d/d$ predicts $6{,}259$.

Remember this factor of $2$. At the very end of these notes it turns out to be the entire remaining gap in the problem.
:::

### 5.1 The two moment methods

The word *moment* just means an average of a power: the **first moment** of a random variable $X$ is $\mathbb{E}X$, the **second moment** is $\mathbb{E}[X^2]$. They name the two standard tools, and the pair is worth holding in mind, because the whole subject alternates between them.

- **First moment method.** Compute $\mathbb{E}X$. If $X$ counts objects, so $X \ge 0$ and integer-valued, Markov's inequality gives $\mathbb{P}(X\ge1)\le\mathbb{E}X$. So if $\mathbb{E}X \to 0$ then whp $X = 0$: **the objects do not exist.** That is Lemma 5.2.
- **Second moment method.** Knowing $\mathbb{E}X$ is *large* does **not** show $X>0$ — a lottery ticket has a large expected payout and almost always pays nothing. You also need $X$ to be concentrated, and that is what the variance measures. Chebyshev's inequality gives
$$\mathbb{P}(X=0) \;\le\; \frac{\mathrm{Var}(X)}{(\mathbb{E}X)^2} \;=\; \frac{\mathbb{E}[X^2]}{(\mathbb{E}X)^2}-1 .$$
So if the ratio $\mathbb{E}[X^2]/(\mathbb{E}X)^2$ tends to $1$, then whp $X>0$: **the objects do exist.**

Both inequalities invoked above are one-liners once indicators are available, so we prove them.

::: lemma Markov's inequality
If $X \ge 0$ and $t > 0$, then $\mathbb{P}(X \ge t) \le \dfrac{\mathbb{E}X}{t}$.
:::

::: proof
Split $X$ according to whether the event $\{X \ge t\}$ occurs — that is, write $1 = \mathbb{1}_{X\ge t} + \mathbb{1}_{X<t}$ and multiply by $X$:
$$\mathbb{E}X \;=\; \mathbb{E}\big[X\,\mathbb{1}_{X \ge t}\big] \;+\; \mathbb{E}\big[X\,\mathbb{1}_{X<t}\big] \;\ge\; \mathbb{E}\big[X\,\mathbb{1}_{X\ge t}\big],$$
where the last step drops a term that is $\ge 0$ — and this is the *only* place the hypothesis $X\ge0$ is used. Now compare $X\,\mathbb{1}_{X\ge t}$ with $t\,\mathbb{1}_{X \ge t}$ outcome by outcome: when the indicator is $1$ we have $X \ge t$, and when it is $0$ both sides are $0$. So $X\,\mathbb{1}_{X\ge t} \ge t\,\mathbb{1}_{X\ge t}$ always, and taking expectations,
$$\mathbb{E}X \;\ge\; t\,\mathbb{E}\big[\mathbb{1}_{X\ge t}\big] \;=\; t\,\mathbb{P}(X \ge t). \qquad$$
:::

Taking $t=1$ gives the form used in Lemma 5.2: for an integer-valued $X \ge 0$, $\mathbb{P}(X\ge1)\le\mathbb{E}X$.

::: lemma Chebyshev's inequality
For any $X$ with finite variance, writing $\mu = \mathbb{E}X$, and any $t>0$,
$$\mathbb{P}\big(|X - \mu| \ge t\big) \;\le\; \frac{\mathrm{Var}(X)}{t^2}.$$
:::

::: proof
The random variable $Y = (X-\mu)^2$ is non-negative, so Markov applies to it. The events $\{|X-\mu| \ge t\}$ and $\{Y \ge t^2\}$ are the *same* event — squaring is monotone on non-negative numbers — so
$$\mathbb{P}\big(|X-\mu|\ge t\big) \;=\; \mathbb{P}\big(Y \ge t^2\big) \;\le\; \frac{\mathbb{E}Y}{t^2} \;=\; \frac{\mathrm{Var}(X)}{t^2},$$
the last equality being the definition $\mathrm{Var}(X) = \mathbb{E}[(X-\mu)^2]$.
:::

::: cor The form we use
If $\mathbb{E}X = \mu > 0$ then
$$\mathbb{P}(X = 0) \;\le\; \frac{\mathrm{Var}(X)}{\mu^2} \;=\; \frac{\mathbb{E}[X^2]}{\mu^2} - 1 .$$
:::

::: proof
If $X = 0$ then $|X - \mu| = \mu$, so the event $\{X=0\}$ is contained in the event $\{|X-\mu| \ge \mu\}$, and a smaller event has no larger probability. Chebyshev with $t = \mu$ gives $\mathbb{P}(X=0) \le \mathrm{Var}(X)/\mu^2$. For the second form, expand $\mathrm{Var}(X) = \mathbb{E}[X^2] - \mu^2$ and divide by $\mu^2$.
:::

::: idea Why the second moment is the harder one
Markov needs nothing but $X\ge0$; Chebyshev needs nothing but a variance. The difficulty is never in the inequalities — it is in *computing* the two sides. $\mathbb{E}X$ comes free from linearity, whatever the dependencies. $\mathbb{E}[X^2]$ is a sum over **pairs**, and pairs of overlapping sets are exactly where the dependence between "$S$ is independent" and "$T$ is independent" lives. That is the whole asymmetry between the two methods.
:::

### 5.2 The reverse bound, and what it would take

So: can we prove that $\alpha(G(n,p))$ is also not much *smaller* than $\frac2p\log(np)$? Yes — and here is the machine, set up exactly.

::: prop
With $X$ the number of independent sets of size $a$, and $I$ the size of the intersection of two independently chosen uniform $a$-subsets of the $n$ vertices,
$$\frac{\mathbb{E}[X^2]}{(\mathbb{E}X)^2} \;=\; \mathbb{E}\Big[(1-p)^{-\binom I2}\Big] \;=\; \sum_{i=0}^{a} \frac{\binom ai\binom{n-a}{a-i}}{\binom na}\,(1-p)^{-\binom i2}.$$
:::

::: proof
Write $X = \sum_S \mathbb{1}_S$ as in the notation box above, so that $X^2 = \sum_{S,T}\mathbb{1}_S\mathbb{1}_T$ and $\mathbb{E}[X^2] = \sum_{S,T}\mathbb{P}(S,T\text{ both independent})$. For two sets $S,T$, the event that both are independent says that every pair inside $S$ and every pair inside $T$ is a non-edge; the pairs lying inside $S\cap T$ are common to both lists and so are counted once, not twice. Hence
$$\mathbb{E}[\mathbb{1}_S\mathbb{1}_T] \;=\; (1-p)^{\,2\binom a2 - \binom{|S\cap T|}{2}}.$$
Summing over all ordered pairs $(S,T)$ and dividing by $(\mathbb{E}X)^2 = \binom na^2 (1-p)^{2\binom a2}$ leaves
$$\frac{\mathbb{E}[X^2]}{(\mathbb{E}X)^2} \;=\; \frac{1}{\binom na^2}\sum_{S,T}(1-p)^{-\binom{|S\cap T|}{2}},$$
which is the average of $(1-p)^{-\binom I2}$ over a uniformly random pair $(S,T)$. The intersection size $I$ of two independent uniform $a$-sets is hypergeometric, with the displayed probabilities.
:::

Now one can see both why it works and where the difficulty is. First, how big is the overlap?

::: lemma The typical overlap
Let $S$ be any fixed $a$-set and $T$ a uniformly random $a$-set. Then
$$\mathbb{E}\,|S\cap T| \;=\; \frac{a^2}{n} \;=:\; \mu,$$
and $\mathrm{Var}(|S\cap T|) \le \mu$, so if $\mu \to \infty$ then $|S\cap T| = (1+o(1))\mu$ with high probability.
:::

::: proof
Count with indicators, exactly as in the notation box: $|S \cap T| = \sum_{v \in S}\mathbb{1}_{v\in T}$. By symmetry, $T$ is equally likely to be any of the $\binom na$ sets of size $a$, so a fixed vertex $v$ lies in $T$ with probability $a/n$ — that is the fraction of vertices $T$ occupies. Linearity of expectation over the $a$ vertices of $S$ then gives
$$\mathbb{E}|S\cap T| \;=\; \sum_{v\in S}\mathbb{P}(v\in T) \;=\; a\cdot\frac an \;=\; \frac{a^2}{n}.$$
Note this holds for *every* $S$, so it is also the answer when $S$ is random.

For the variance we cannot just add up the variances of the $\mathbb{1}_{v\in T}$, because they are **not independent**: $T$ has a fixed size $a$, so a vertex being in $T$ makes it slightly harder for the next one to be. The correct identity for a sum is
$$\mathrm{Var}\Big(\sum_{v\in S}\mathbb{1}_{v\in T}\Big) \;=\; \sum_{v\in S}\mathrm{Var}\big(\mathbb{1}_{v\in T}\big) \;+\; \sum_{u\ne v}\mathrm{Cov}\big(\mathbb{1}_{u\in T},\mathbb{1}_{v\in T}\big),$$
where $\mathrm{Cov}(X,Y) = \mathbb{E}[XY]-\mathbb{E}X\,\mathbb{E}Y$ measures how two quantities move together. Write $q = a/n$. Each single term is an indicator, so $\mathrm{Var}(\mathbb{1}_{v\in T}) = q(1-q)$. For a pair $u \ne v$, the chance that *both* land in $T$ is $\frac{a}{n}\cdot\frac{a-1}{n-1}$ — after $u$ takes one of the $a$ places, $v$ competes for the remaining $a-1$ among $n-1$ vertices — so
$$\mathrm{Cov} \;=\; \frac an\cdot\frac{a-1}{n-1} - q^2 \;=\; q\left[\frac{a-1}{n-1}-\frac an\right] \;=\; q\cdot\frac{n(a-1)-a(n-1)}{n(n-1)} \;=\; -\,\frac{q(n-a)}{n(n-1)} \;<\; 0 .$$
The covariance is **negative**, which is the fixed size of $T$ making itself felt. Summing over the $a$ diagonal terms and the $a(a-1)$ ordered pairs, and using $1-q = (n-a)/n$,
$$\mathrm{Var} \;=\; a\,q(1-q) \;-\; a(a-1)\frac{q(n-a)}{n(n-1)} \;=\; a\,q\,\frac{n-a}{n}\left[1-\frac{a-1}{n-1}\right] \;=\; a\cdot\frac an\Big(1-\frac an\Big)\frac{n-a}{n-1},$$
which is at most $a^2/n = \mu$ because the last two factors are each at most $1$.

Chebyshev's inequality (Lemma 5.5) then gives, for any fixed $\varepsilon>0$,
$$\mathbb{P}\big(\,\big||S\cap T|-\mu\big| \ge \varepsilon\mu\,\big) \;\le\; \frac{\mathrm{Var}}{\varepsilon^2\mu^2} \;\le\; \frac{1}{\varepsilon^2\mu} \;\longrightarrow\; 0 .$$
:::

::: note What a covariance is, and why this one is negative
**The definition.** $\mathrm{Cov}(X,Y) = \mathbb{E}\big[(X-\mathbb{E}X)(Y-\mathbb{E}Y)\big] = \mathbb{E}[XY]-\mathbb{E}X\,\mathbb{E}Y$: the average product of the two deviations. It asks *when $X$ is above its mean, is $Y$ too?* — positive if they tend to move together, negative if one being high pushes the other low, and zero if they are unrelated. Independent variables have covariance $0$ (the converse is false).

**Why it appears in a variance.** Purely from squaring a sum, exactly as $(x+y)^2 = x^2+y^2+2xy$. Writing $\bar X_i = X_i - \mathbb{E}X_i$,
$$\mathrm{Var}\Big(\sum_i X_i\Big) = \mathbb{E}\Big[\Big(\sum_i \bar X_i\Big)^{2}\Big] = \sum_i\sum_j \mathbb{E}\big[\bar X_i \bar X_j\big] ,$$
and the diagonal terms $i=j$ are the variances while every off-diagonal term is a covariance. For *independent* variables the off-diagonal terms vanish and variances simply add — the rule one is used to. Here they do not vanish.

**For indicators it reads plainly.** $\mathrm{Cov}(\mathbb{1}_A,\mathbb{1}_B) = \mathbb{P}(A\cap B) - \mathbb{P}(A)\mathbb{P}(B)$: *do these two events co-occur more, or less, often than they would by chance?* Above we compared $\frac an\cdot\frac{a-1}{n-1}$ with $\big(\frac an\big)^2$, and $\frac{a-1}{n-1} < \frac an$ whenever $a<n$ — less often than chance, hence negative.

**The reason is seats.** $T$ has exactly $a$ places. If $u$ takes one, only $a-1$ remain for $v$ among $n-1$ candidates: the two vertices are *competing*. With independent coin flips, where $|T|$ is free to vary, there is no competition and the covariance is zero.

**Two checks.** At $a=n$ the formula gives $\mathrm{Var}=0$ — right, since then $T$ is everything and $|S\cap T| = a$ with certainty. At $a=1$ the correction factor is exactly $1$ and we recover the binomial value — right, since with a single draw there is nobody to compete with.
:::

::: note What "hypergeometric" means, and why the extra factor
The count $|S\cap T|$ is a textbook **hypergeometric** random variable: an urn holds $n$ balls of which $a$ are marked (the members of $S$), you draw $a$ of them **without replacement** (the set $T$), and you count the marked ones. Its distribution is the $f(i)$ of the Proposition — choose which $i$ of the $a$ marked balls and which $a-i$ of the $n-a$ unmarked ones, out of $\binom na$ equally likely draws.

Had the draws been independent — each vertex tossed into $T$ with probability $q$, so that $|T|$ merely *averaged* $a$ — the count would be **binomial**, with variance $aq(1-q)$. Sampling without replacement instead multiplies this by
$$\frac{n-a}{n-1} \;<\; 1,$$
the *finite population correction*, and it is exactly the negative covariance computed above. Fixing the size of $T$ makes the sample **self-balancing**: an unusually full draw early leaves fewer places later. So sampling without replacement is always at least as concentrated as independent coin flips — which is why we may be generous and simply use $\mathrm{Var} \le \mu$.
:::


At our density $a \approx \sqrt{n\log n}$, so $\mu = a^2/n \approx \log n$, which does tend to infinity — the overlap is concentrated, and two random $a$-sets really do meet in about $\log n$ vertices. Now
$$(1-p)^{-\binom \mu2} \;\approx\; e^{\,p\mu^2/2} \;=\; \exp\Big(\tfrac12\sqrt{\tfrac{\log n}{n}}\,\log^2 n\Big) \;\longrightarrow\; 1 ,$$
so the typical term contributes $1$, as it must. At the other extreme $i = a$ the two sets coincide, and that single term is $\binom na^{-1}(1-p)^{-\binom a2} = 1/\mathbb{E}X$, which tends to $0$ precisely because we are below the threshold. **The content of the proof is that every intermediate $i$ is also negligible**, and that is a genuinely delicate estimate — the terms first fall, then rise again — which is why we do not reproduce it here. It is classical (Bollobás and Erdős; see also Frieze for the sharp form, which pins $\alpha$ to within an additive $o(1/p)$).

::: note The machine, run numerically
Since the identity above is exact, we can simply evaluate it. Writing $a^*$ for the true threshold — the largest $a$ with $\mathbb{E}X \ge 1$ — and taking $a = 0.95\,a^*$, at $p = \sqrt{\log n/n}$:

| $n$ | $a$ | $\log \mathbb{E}X$ | $\mathbb{E}[X^2]/(\mathbb{E}X)^2 - 1$ |
|---|---|---|---|
| $10^5$ | $980$ | $329$ | $0.75$ |
| $10^6$ | $3384$ | $1308$ | $0.29$ |
| $10^7$ | $11535$ | $5048$ | $0.12$ |

The first moment blows up and the variance ratio falls towards $1$, so by Chebyshev $\mathbb{P}(X=0)$ is already at most $0.12$ at $n=10^7$ and shrinking. The second moment method really does deliver the matching bound.
:::

::: warn How slowly these asymptotics converge
The same computation contains a warning worth heeding whenever you use these formulas at a finite $n$. The asymptotic threshold $\frac2p\log(np)$ *overshoots* the true $a^*$ badly:

| $n$ | $a^*$ | $\frac2p\log(np)$ | ratio |
|---|---|---|---|
| $10^5$ | $1032$ | $1301$ | $0.79$ |
| $10^6$ | $3563$ | $4423$ | $0.81$ |
| $10^7$ | $12143$ | $14885$ | $0.82$ |
| $10^8$ | $40995$ | $49708$ | $0.82$ |

The ratio does tend to $1$ — the gap is the $\log\log(np)$ term we discarded in the proof of Lemma 5.2 — but even at $n = 10^8$ it is still $18\%$ out. This is the same phenomenon as Shearer's $f(d)$ approaching $\log d/d$ from below (Section 9), and as the slow drift in simulations of the triangle-free process. **These are statements about the limit, and the limit arrives late.**
:::

## 6. The deletion method, and the barrier it creates

A random graph is not triangle-free, and lowering $p$ until it is destroys everything: $G(n,p)$ has no triangles at all only when $p = O(1/n)$, where the graph is a scattering of isolated vertices and small trees, $\alpha$ is a constant fraction of $n$, and the dictionary yields only $R(3,k) \gtrsim k$.

So one builds *above* the triangle threshold and repairs afterwards. Count the repair bill: the expected number of triangles is $\binom n3 p^3 \approx n^3p^3/6$ and the expected number of edges is $\binom n2 p \approx n^2 p/2$, so
$$\frac{\#\text{triangles}}{\#\text{edges}} \;\approx\; \frac{n^3p^3/6}{n^2p/2} \;=\; \frac{np^2}{3}.$$
Deleting one edge from every triangle is affordable exactly when this ratio is small, that is when $np^2 = O(1)$, that is when
$$p \;\lesssim\; \frac{1}{\sqrt n}.$$
This value is called the **edge deletion threshold** for triangles, written $p_{K_3} = n^{-1/2}$. It is Erdős's ceiling, and it is the number the rest of this story is about.

::: theorem Erdős, 1961
$R(3,k) \;=\; \Omega\!\left(\dfrac{k^2}{(\log k)^2}\right).$
:::

::: proof
Take $p = c/\sqrt n$ for a small constant $c$ and sample $G \sim G(n,p)$. By the count above, the expected number of triangles is a $c^2/3$ fraction of the expected number of edges, so deleting one edge from each triangle leaves a triangle-free graph retaining most of its edges. Its independence number is, up to the technical point noted below, that of $G(n,p)$:
$$\alpha \;\approx\; \frac2p \log (np) \;=\; \frac{2\sqrt n}{c}\cdot \log\big(c\sqrt n\big) \;=\; (1+o(1))\,\frac{\sqrt n \log n}{c}.$$
Setting $k$ equal to this and solving, $n \approx c^2k^2/(\log n)^2$; since $n = k^{2+o(1)}$ we have $\log n = (2+o(1))\log k$, so $n = \Omega(k^2/(\log k)^2)$, and the dictionary finishes the proof.
:::

::: warn The one gap in the argument above
Deleting edges can only *increase* $\alpha$, so "its independence number is that of $G(n,p)$" needs an argument. The honest version proves a robust statement — that with high probability *every* set of the critical size spans many more edges than could possibly have been deleted inside it — so that removing the triangle edges cannot create a new independent set. The paper we are studying describes this step as "some further effort"; it is standard, and we will meet exactly the same issue again in Section 13.
:::

\pagebreak

## 7. The exchange rate

We now fix a normalisation and convert graph-building into Ramsey constants once and for all. Recall from Section 4 that the interesting degree scale is around $\sqrt n$; with logarithms it becomes $\sqrt{n\log n}$.

::: def The density parameter
Every construction below produces a graph whose density we write as
$$p \;=\; c\cdot\sqrt{\frac{\log n}{n}}, \qquad\text{so that the average degree is}\qquad d \;=\; pn \;=\; c\sqrt{n\log n}.$$
The number $c$ is the **one quantity you get to choose**. Turn it up and the graph is denser; turn it down and it is sparser.
:::

::: lemma The conversion lemma
Suppose that for every large $n$ there is a triangle-free graph on $n$ vertices with
$$\alpha(G) \;\le\; A\sqrt{n\log n}\,(1+o(1)).$$
Then
$$R(3,k) \;\ge\; \left(\frac{1}{2A^2} - o(1)\right)\frac{k^2}{\log k}.$$
:::

::: proof
Given $k$, set $n = \frac{1}{2A^2}\cdot\frac{k^2}{\log k}$. Then $n = k^{2+o(1)}$, so
$$\log n = 2\log k - \log\big(2A^2\log k\big) = (2+o(1))\log k,$$
and therefore
$$n \log n \;=\; \frac{1}{2A^2}\cdot\frac{k^2}{\log k}\cdot (2+o(1))\log k \;=\; (1+o(1))\,\frac{k^2}{A^2}.$$
Hence $A\sqrt{n\log n} = (1+o(1))k$. Shrinking the constant by an arbitrarily small amount makes the graph's independence number strictly less than $k$, so it is a witness for $n$, and the dictionary gives $R(3,k) > n$.
:::

::: idea The exchange rate
$$\boxed{\;\alpha = A\sqrt{n\log n} \quad\Longleftrightarrow\quad R(3,k) \;=\; \frac{1}{2A^2}\cdot\frac{k^2}{\log k}\;}$$
A **smaller** $A$ is a **better** construction. All the history is a race to push $A$ down, and $A$ is measured in units of $\sqrt{n\log n}$.
:::

## 8. Both pressures at once: the shape of the answer

Fix the density parameter $c$ and suppose the graph we build is *pseudorandom* — it looks locally like $G(n,p)$. Then both pressures of Section 4 apply, now with logarithms.

**Pressure 1 (neighbourhoods).** By Lemma 3.1, $\alpha \ge d = c\sqrt{n\log n}$, so $A \ge c$. *Denser is worse.*

**Pressure 2 (the first moment).** This is the direction that needs the *lower* bound on $\alpha(G(n,p))$ flagged in Section 5, so it is a heuristic, not a theorem: we assume the graph we build is random-like enough that its independent sets are no smaller than a random graph's. Since $np = c\sqrt{n\log n} = n^{1/2+o(1)}$ we have $\log(np) = (\tfrac12+o(1))\log n$, so
$$\alpha \;\approx\; \frac{2}{p}\log(np) \;=\; \frac{\log n}{p} \;=\; \frac1c\sqrt{n\log n},$$
so $A \ge 1/c$. *Sparser is worse.*

::: theorem The barrier
For a pseudorandom triangle-free graph of density parameter $c$,
$$A(c) \;=\; \max\left(c,\ \frac1c\right) \;\ge\; 1,$$
with equality if and only if $c=1$. Via the exchange rate, no construction of this kind can prove more than
$$R(3,k) \;\ge\; \left(\tfrac12+o(1)\right)\frac{k^2}{\log k}.$$
:::

::: proof
$\max(c,1/c) \ge \sqrt{c\cdot 1/c} = 1$ by the arithmetic–geometric mean inequality, with equality exactly when $c = 1/c$, i.e. $c=1$. Substituting $A = 1$ into the exchange rate gives $1/(2A^2) = 1/2$.
:::

At $c=1$ something striking happens: the maximum degree and the independence number coincide, both equal to $\sqrt{n\log n}$. The graph is exactly as dense as it can be before its own neighbourhoods become the largest independent sets.

Now the entire history of the problem is one number climbing towards $1$:

::: note The table
| $c$ | $A = \max(c,1/c)$ | constant $1/(2A^2)$ | who |
|---|---|---|---|
| $1/\sqrt{\log n} \to 0$ | $\to\infty$ | $k^2/(\log k)^2$ | Erdős 1961 |
| small | large | $\approx 1/160$ | Kim 1995 |
| $1/\sqrt2 \approx 0.707$ | $\sqrt2$ | $1/4$ | Bohman–Keevash; Fiz Pontiveros–Griffiths–Morris |
| $\sqrt{2/3} \approx 0.816$ | $\sqrt{3/2}$ | $1/3$ | Campos–Jenssen–Michelen–Sahasrabudhe, May 2025 |
| $1$ | $1$ | $1/2$ | **this paper**, October 2025 |
:::

## 9. The other side: Shearer's theorem, with proof

Everything so far has been about building witnesses. Now the opposite activity, so that we know what we are aiming at — and because the gap that remains today is entirely on this side.

### 9.1 The statement

Shearer's function is defined by a recursion. Set
$$f(0) = 1, \qquad f(d) \;=\; \frac{1 + (d^2-d)f(d-1)}{d^2+1} \quad (d \ge 1),$$
so $f(1) = 1/2$, $f(2) = 3/7$, and so on. The continuous version of the same recursion is the differential equation
$$(d+1)f(d) \;+\; (d^2-d)\,f'(d) \;=\; 1, \qquad f(0)=1,$$
whose solution is available in closed form:
$$f(d) \;=\; \frac{d\log d - d + 1}{(d-1)^2} \;=\; (1+o(1))\,\frac{\log d}{d}.$$

::: note A remark on the two versions and their dates
Shearer proved $\alpha(G) \ge n f(d)$ for the closed-form $f$ above, with $d$ the *average* degree, in 1983 (*Discrete Math.* 46, 83–87). In 1991 (*JCTB* 53, 300–307) he strengthened it to the per-vertex sum $\alpha(G) \ge \sum_i f(d_i)$ with the difference-equation $f$ — an improvement of exactly the kind by which Caro and Wei strengthened Turán's theorem, and which we already met in Lemma 3.2. The proof below is the 1991 one; it contains the 1983 statement, since $f$ is convex and Jensen's inequality gives $\sum_i f(d_i) \ge n f(d)$.

The approach to $\log d/d$ is slow and from below: at $d = 1000$ the ratio $f(d)\big/(\log d/d)$ is still only $0.86$. That is where the $(1+o(1))$ lives.
:::

::: theorem Shearer 1983, 1991
Let $G$ be triangle-free with degree sequence $d_1,\dots,d_n$. Then
$$\alpha(G) \;\ge\; \sum_{i=1}^{n} f(d_i) \;\ge\; n\,f(d) \;=\; (1+o(1))\,\frac{n\log d}{d}.$$
:::

### 9.2 The proof

We need one property of $f$, which is a calculation we take on trust: both $f(d)$ and the successive difference $f(d) - f(d+1)$ are decreasing in $d$. The second of these is the only structural fact used below, and it gives the inequality
$$f(d-n)-f(d) \;\ge\; n\big[f(d-1)-f(d)\big] \qquad (0 \le n \le d), \tag{$\ast$}$$
since the left side is a sum of $n$ successive differences, each at least the last one.

::: proof
By induction on $n$; the case $n=0$ is trivial. Write $S = \sum_i f(d_i)$.

**Setting up.** Fix a vertex $i$. Let $S_i = N(i)$ be its neighbours and let $S_i'$ be the vertices at distance exactly $2$ from $i$. For $k \in S_i'$ put $n_k = |N(k)\cap S_i| \ge 1$. Let $H_i = G - N[i]$ be the graph obtained by deleting $i$ together with all of its neighbours.

Which degrees change in $H_i$? A vertex at distance $\ge 3$ from $i$ loses nothing. A vertex $k \in S_i'$ loses exactly its $n_k$ neighbours in $S_i$. So the corresponding sum for $H_i$ is
$$T_i \;=\; S \;-\; f(d_i) \;-\; \sum_{j\in S_i} f(d_j) \;+\; \sum_{k \in S_i'}\Big[f(d_k - n_k) - f(d_k)\Big].$$

$H_i$ is again triangle-free, so by induction $\alpha(H_i) \ge T_i$. Moreover $\alpha(G) \ge 1 + \alpha(H_i)$: take a maximum independent set of $H_i$ and add $i$ to it, which is legal because $H_i$ contains no neighbour of $i$. So the theorem follows if we can find a single vertex $i$ with
$$1 - f(d_i) - \sum_{j\in S_i} f(d_j) + \sum_{k\in S_i'}\big[f(d_k-n_k)-f(d_k)\big] \;\ge\; 0. \tag{$\dagger$}$$

**It holds on average.** Let $A$ be the sum of the left-hand side of $(\dagger)$ over all $i$; we show $A \ge 0$, which forces some $i$ to satisfy $(\dagger)$.

Interchange the order of summation in the two sums. Each vertex $j$ appears in $\sum_{j \in S_i} f(d_j)$ once for each of its $d_j$ neighbours $i$, contributing $d_j f(d_j)$ in total. And $k \in S_i'$ if and only if $i \in S_k'$, with the same count $n$ of common neighbours either way. Hence
$$A \;=\; \sum_{i=1}^n \Big[\,1 - (d_i+1)f(d_i) + B_i\,\Big], \qquad\text{where}\qquad B_i \;=\; \sum_{k\in S_i'}\big[f(d_i - n_k) - f(d_i)\big].$$

**Where triangle-freeness enters.** Apply $(\ast)$ to each term of $B_i$:
$$B_i \;\ge\; \Big(\sum_{k \in S_i'} n_k\Big)\big[f(d_i-1)-f(d_i)\big].$$
Now $\sum_{k\in S_i'} n_k$ counts the edges between $S_i$ and $S_i'$. Because $G$ is triangle-free, **$S_i$ spans no edges at all**, so every edge leaving a vertex $j \in S_i$, other than the edge $ji$ itself, must land in $S_i'$. Therefore the count is exactly $\sum_{j\in S_i}(d_j-1)$, with nothing double-counted, and
$$B_i \;\ge\; \Big(\sum_{j \sim i}(d_j-1)\Big)\big[f(d_i-1)-f(d_i)\big].$$

This is the only place the hypothesis is used, and it is the whole gain: in a graph with triangles, edges inside $S_i$ would be counted twice and the bound would be weaker.

**Summing.** Write $\delta_i = f(d_i-1)-f(d_i)$, which by our property of $f$ is *decreasing* in $d_i$. Summing the last display over $i$ groups the terms by edges:
$$\sum_i B_i \;\ge\; \sum_{ij \in E}\Big[(d_j-1)\delta_i + (d_i-1)\delta_j\Big] \;\ge\; \sum_{ij\in E}\Big[(d_i-1)\delta_i + (d_j-1)\delta_j\Big] \;=\; \sum_i (d_i^2-d_i)\,\delta_i .$$
The middle inequality is a rearrangement: $\delta$ is decreasing in the degree, so $(d_i-d_j)(\delta_j-\delta_i) \ge 0$, which expands to exactly the swap performed. The final equality holds because each vertex $i$ lies in $d_i$ edges and contributes $(d_i-1)\delta_i$ to each.

**The recursion does the rest.** Substituting,
$$A \;\ge\; \sum_{i=1}^n \Big[\,1 - (d_i+1)f(d_i) + (d_i^2-d_i)\big(f(d_i-1)-f(d_i)\big)\Big],$$
and every bracket is *zero*, because
$$(d+1)f(d) = 1 + (d^2-d)\big(f(d-1)-f(d)\big) \iff (d^2+1)f(d) = 1 + (d^2-d)f(d-1),$$
which is the definition of $f$. Hence $A \ge 0$, some $i$ satisfies $(\dagger)$, and the induction closes.
:::

::: idea What the proof is really doing
Strip away the algebra and one move remains: **delete a vertex and its whole neighbourhood, and recurse.** Deleting $N[i]$ buys you one vertex of the independent set and costs you $1 + d_i$ vertices of the graph.

Triangle-freeness is used exactly once, to say that $N(i)$ spans no edges — so removing it destroys *every* edge that touches it, with nothing counted twice. Each step is therefore maximally destructive: the graph that remains is sparser than it has any right to be, and $f$ is precisely the bookkeeping that converts that surplus, iterated, into the extra factor of $\log d$ over the greedy bound $n/(d+1)$.

Shearer's Remark 1 makes the connection to Section 5 exact: the bound $\sum_i f(d_i)$ is achieved *on average* by the random greedy algorithm — pick a random vertex, take it, delete its neighbourhood, repeat. So his theorem says, in a precise sense: **no triangle-free graph is worse for greedy than a random graph of the same density.** That is the same statement we checked numerically in Section 5.
:::

### 9.3 The resulting upper bound, and the factor of $2$

Combine Shearer with the neighbourhood bound $\alpha \ge d$ and minimise over $d$: the crossing is at $d^2 = n\log d$, and since $\log d = (\tfrac12+o(1))\log n$ there, $d = \sqrt{n\log n/2}$. Hence every triangle-free graph has
$$\alpha(G) \;\ge\; \Big(\tfrac{1}{\sqrt2}+o(1)\Big)\sqrt{n\log n}, \qquad\text{i.e.}\qquad A \ge \tfrac{1}{\sqrt2},$$
and the exchange rate of Section 7 turns this into
$$R(3,k) \;\le\; (1+o(1))\,\frac{k^2}{\log k}.$$
This has been the best known upper bound since 1983.

So the lower bound of this paper is $\tfrac12$ and the upper bound is $1$: a factor of $2$. That factor is not mysterious. Shearer's theorem delivers the *greedy* value $n\log d/d$; a random graph of the same density actually contains an independent set of size $2n\log d/d$ (Section 5). The conjecture is that every triangle-free graph does as well as the random one.

Davies, Jenssen, Perkins and Roberts made this precise, and their formulation is the cleanest way to state what is missing. For a graph $G$ let $\alpha_G(1)$ denote the **average** size of an independent set, averaged uniformly over all independent sets of $G$ (including the empty one).

::: theorem Davies–Jenssen–Perkins–Roberts 2018
Let $G$ be triangle-free on $n$ vertices with maximum degree $d$. Then
$$\alpha_G(1) \;\ge\; (1+o_d(1))\,\frac{\log d}{d}\,n .$$
:::

That is Shearer's bound for the *average* independent set, which is strictly stronger than Shearer's bound for the largest one. What remains is to show that the largest is substantially bigger than the average.

::: note The conjectures, and exactly what they would give
- **Conjecture 1.** For every triangle-free $G$: $\ \alpha(G)/\alpha_G(1) \ge 4/3$. This implies $R(3,k) \le (3/4+o(1))k^2/\log k$.
- **Conjecture 2.** For every triangle-free $G$ of minimum degree $d$: $\ \alpha(G)/\alpha_G(1) \ge 2 - o_d(1)$. This implies $R(3,k) \le (\tfrac12+o(1))k^2/\log k$ — and hence, with this paper, would settle the problem.

For a random graph the ratio $\alpha/\alpha_G(1)$ is $2$, which is the factor we have been tracking all along. The smallest ratio the authors could find in any triangle-free graph is $1.43283\ldots$, attained by the cyclic graph witnessing $R(3,9) \ge 36$; they picked $4/3$ for Conjecture 1 as a round number below it, and note it is the ratio of maximum to average in a triangle.

So the state of the problem is: **the construction side is finished, and the remaining factor of $2$ is the assertion that in a triangle-free graph the biggest independent set is at least twice the average one.**
:::

\pagebreak

## 10. Blow-ups: how to walk past the deletion threshold

Everything so far says density is capped at $p_{K_3} = n^{-1/2}$. The first idea of the paper's ancestry is that this cap is an illusion.

::: def Blow-up
Let $H$ be a graph on $m$ vertices, thought of as **clusters**, and let $s \ge 1$. The **blow-up** of $H$ by $s$ is the graph on $n = ms$ vertices obtained by replacing each cluster with $s$ vertices, joining two vertices if and only if their clusters are adjacent in $H$, and putting no edges inside a cluster.
:::

::: lemma Blow-ups preserve triangle-freeness exactly
If $H$ is triangle-free, so is its blow-up. Moreover the blow-up has the same edge density as $H$, and each vertex has degree $s\cdot d_H(\text{its cluster})$.
:::

::: proof
Suppose $u,v,w$ formed a triangle in the blow-up. No two of them lie in a common cluster, since a cluster is an independent set. So they lie in three distinct clusters, which are then pairwise adjacent in $H$ — a triangle in $H$. The density and degree statements are immediate from the definition.
:::

This is an exact statement, with no probability and no error term, and it is what makes the whole construction work:

::: theorem Blow-ups beat the deletion threshold
Let $s \gg \log n$, put $m = n/s$, and let $p = \Theta\big(\sqrt{\log n / n}\big)$. Then $p = o\big(m^{-1/2}\big)$: the base graph $G(m,p)$ is far *below* its own deletion threshold, so it can be made triangle-free by deleting a $o(1)$ fraction of its edges. Blowing it up by $s$ then yields a triangle-free graph on $n$ vertices of density $p$, which is $\Theta(\sqrt{\log n})$ times denser than $p_{K_3}$.
:::

::: proof
The deletion threshold for a graph on $m$ vertices is $m^{-1/2} = \sqrt{s/n}$. Comparing,
$$\frac{p}{m^{-1/2}} \;=\; \Theta\!\left(\sqrt{\frac{\log n}{n}}\cdot\sqrt{\frac ns}\right) \;=\; \Theta\!\left(\sqrt{\frac{\log n}{s}}\right) \;\longrightarrow\; 0 \quad\text{when } s \gg \log n .$$
Equivalently, the number of triangles per edge in the base graph is $\Theta(mp^2) = \Theta(\log n/s) = o(1)$. So a $o(1)$ fraction of the base edges lie in triangles; delete one edge from each. Lemma 10.2 transports triangle-freeness and the density to the blow-up.
:::

::: idea Why this is the crucial move
The density that is impossible on $n$ vertices is easy on $n/s$ vertices, and blowing up carries it back **for free**. Everything the classical method could not reach is reachable this way. The only question is what price you pay — and you do pay one.
:::

## 11. Why one blow-up is not enough

::: lemma
The blow-up of $H$ by $s$ has independence number exactly $s\cdot\alpha(H)$.
:::

::: proof
If $S$ is independent in $H$, then all $s|S|$ vertices lying in the clusters of $S$ are pairwise non-adjacent — two in the same cluster because clusters carry no edges, two in different clusters because those clusters are non-adjacent in $H$. This gives $\alpha \ge s\,\alpha(H)$.

Conversely let $I$ be independent in the blow-up and let $S$ be the set of clusters it meets. No two clusters of $S$ are adjacent in $H$, since that would put an edge inside $I$; so $S$ is independent in $H$ and $|I| \le s|S| \le s\,\alpha(H)$.
:::

With the parameters of the next section this is about $2s\sqrt{n\log n}$, larger than the target $\sqrt{n\log n}$ by a factor of $2s$. A single blow-up is far too structured: it wears its large independent sets on the outside.

This is exactly the position Campos, Jenssen, Michelen and Sahasrabudhe were in. Their solution (May 2025) was to use the blow-up as a **seed** for the density and then run a *nibble* — a long sequence of small random edge additions — on top of it, to destroy the structure. In numbers: their seed is a blow-up of $G(m,p)$ with $m = n/\log^2 n$ and $p = \sqrt{\log n/6n}$, giving $c = 1/\sqrt6 \approx 0.408$; the nibble then roughly **doubles** the density, reaching $c = \sqrt{2/3} \approx 0.816$ and the constant $1/3$.

Look at what the nibble is being paid to do: multiply the density by two. The question the new paper asks is whether something cheaper can do that.

## 12. The construction

The answer is: do the blow-up again. Here is the construction, exactly as in Section 2 of the paper.

::: def The construction
Fix $\varepsilon > 0$ and set
$$s = \log^2 n, \qquad m = \frac ns, \qquad p = \beta\sqrt{\frac{\log n}{n}} \ \ \text{with } \beta = \tfrac12, \qquad k = \kappa\sqrt{n\log n} \ \ \text{with } \kappa = 1+\varepsilon.$$

1. Sample two independent random graphs $G_R \sim G(m,p)$ and $G_B \sim G(m,p)$, on disjoint vertex sets $V_R = \{r_1,\dots,r_m\}$ and $V_B = \{b_1,\dots,b_m\}$. Call them the **red** and the **blue** graph.
2. Let $V(G) = \{v_1,\dots,v_n\}$ and choose an **injective map**
$$\pi : V(G) \longrightarrow V_R\times V_B$$
uniformly at random. Write $\pi(v) = (\pi_R(v), \pi_B(v))$; these are the **red** and **blue coordinates** of $v$.
3. Join $v$ and $w$ by a **red** edge if $\pi_R(v)\pi_R(w) \in E(G_R)$, and by a **blue** edge if $\pi_B(v)\pi_B(w) \in E(G_B)$. If both, keep both: we work with the multigraph, which has the same independence number.
4. Delete edges to destroy every triangle, by four explicit rules — one for red-red-red triangles, one for blue-blue-blue, one for red-red-blue (delete the blue edge) and one for blue-blue-red (delete the red edge), with ties broken by a fixed lexicographic order on the pairs of $V_R$ and of $V_B$.
:::

::: warn A notational trap
The words *red* and *blue* here have nothing to do with the red/blue colouring of Section 1. That colouring is long gone: we are building a single graph $G$. Red and blue simply name the two halves of the construction.
:::

::: idea The picture
A vertex is a **cell of an $m\times m$ grid**: its row is its red coordinate, its column its blue coordinate. The $n$ vertices are $n$ cells chosen at random, and the grid is very sparsely occupied ($m^2 \approx n^2/\log^4 n$ cells for $n$ vertices). Two vertices are adjacent if their **rows** are adjacent in the red graph, **or** their **columns** are adjacent in the blue graph.

All vertices sharing a row form a red **fibre** — a red-independent set of size about $s$ — and likewise for columns. So the two blow-ups of Section 10 are both present: rows are the red clusters, columns the blue clusters. And because $\pi$ is random, *the rows are unrelated to the columns*. That independence is the entire source of the pseudorandomness.
:::

The density of the union is $(2+o(1))p = \sqrt{\log n/n}$, so in the language of Section 7 this construction sits at $c = 1$ — exactly the bottom of the barrier of Theorem 8.1. Two things must now be checked: that the triangles can be removed cheaply, and that the independent sets really are as small as a random graph of this density.

## 13. Triangles come in bunches

At density $2p$ a typical edge lies in about $n(2p)^2 = \log n$ triangles. If those triangles were spread out, one would have to delete a $\log n$ fraction of the edges — everything — and we would be back at Erdős's ceiling. They are not spread out.

::: lemma The bunching lemma
Every triangle of the construction has an **apex**: a vertex $w$ whose two triangle edges have the same colour. If $w$ is an apex with same-coloured edges to $u$ and $v$, then **every** vertex in $w$'s fibre of that colour also forms a triangle with the edge $uv$. Hence triangles occur in bunches of size $\approx s$, all sharing a single edge, and deleting that one edge destroys the whole bunch.
:::

::: proof
A triangle has three edges, each red or blue, so by pigeonhole two of them share a colour; those two edges meet at a vertex, which we call $w$. Say both are blue, so $\pi_B(w)$ is adjacent in $G_B$ to $\pi_B(u)$ and to $\pi_B(v)$.

Blue adjacency depends only on the blue coordinate. So if $w'$ is any vertex with $\pi_B(w') = \pi_B(w)$ — that is, any vertex in the same blue fibre — then $w'$ is also blue-adjacent to both $u$ and $v$, and $u,v,w'$ is again a triangle. By Lemma 3.1 of the paper the fibres have size $(1+o(1))s$ with high probability, which gives the count. Deleting the edge $uv$ destroys every triangle in the bunch at once.
:::

::: theorem The deletion is cheap
With $s = \log^2 n$, the construction loses only a $O(1/\log n) = o(1)$ fraction of its edges.
:::

::: proof
Fix an edge $uv$. A bunch of triangles on $uv$ is determined not by an apex vertex but by an apex *cluster*: a vertex of $V_R$ adjacent in $G_R$ to both red coordinates, or a vertex of $V_B$ adjacent in $G_B$ to both blue coordinates. The expected number of such common neighbours is
$$2mp^2 \;=\; 2\cdot\frac ns\cdot \frac14\cdot\frac{\log n}{n} \;=\; \frac{\log n}{2s} \;=\; \frac{1}{2\log n}.$$
So the expected number of bunches per edge is $O(1/\log n)$, and one deletion kills each bunch. Equivalently: there are $\approx\log n$ triangles per edge but they come in bunches of $s = \log^2 n$, so the number of deletions per edge is $\approx \log n / s = 1/\log n \to 0$.
:::

::: idea This is the heart of the paper
The classical deletion method fails above $p_{K_3}$ because each edge carries too many triangles. The blow-up structure does not reduce the *number* of triangles at all — it **stacks them on top of one another**, so that one deletion handles $s$ of them. The gain is exactly the factor $s$. In the authors' words: *"every edge removal destroys at least $(1+o(1))s$ triangles in this process. This factor $s$ represents exactly the gain in efficiency of this construction when compared with the typical edge deletion method."*

There is a trade-off in $s$, and it is the design decision of the whole construction: a larger $s$ makes deletions cheaper, but longer rows and columns mean more structure for independent sets to exploit. The choice $s = \log^2 n$ is the sweet spot.
:::

## 14. The independent sets

::: lemma The projection criterion
Ignoring deleted edges, a set $I \subseteq V(G)$ is independent if and only if $\pi_R(I)$ is independent in $G_R$ **and** $\pi_B(I)$ is independent in $G_B$.
:::

::: proof
Immediate from the definition of the edges: a red edge inside $I$ is exactly a $G_R$-edge between two red coordinates of vertices of $I$, and similarly in blue. $I$ has no edge inside it precisely when neither colour contributes one.
:::

So a candidate independent set must survive **two independent random graphs at once**. This is where the two blow-ups rescue each other: a set that is structured for the red graph — a union of rows, say — is a *random* set as far as the blue graph is concerned, because $\pi$ was chosen at random, and blue kills it.

Now the counting. There is a genuine tension:

- if $I$ crowds into few rows and columns, it has few pairs to avoid and is *more* likely to be independent — but there are *few* such sets;
- if $I$ spreads over $k$ rows and $k$ columns, it must avoid $\approx k^2/2$ pairs in each colour and is very unlikely to be independent — but *most* sets look like this.

The balance comes out exactly, and it is worth doing.

::: theorem The threshold is at $\kappa = 1$
Write $|\pi_R(I)| = x_R k$ and $|\pi_B(I)| = x_B k$. Then, in units of $k\log n$, the exponent of the expected number of independent $k$-sets with these projection sizes is
$$g(x_R,x_B) \;=\; \underbrace{\frac{x_R+x_B-1}{2}}_{\text{how many such sets}} \;-\; \underbrace{\frac{\kappa}{4}\big(x_R^2+x_B^2\big)}_{\text{probability each is independent}},$$
whose maximum over $x_R,x_B$ equals $\dfrac{1-\kappa}{2\kappa}$, attained at $x_R = x_B = 1/\kappa$. This is zero at $\kappa = 1$ and strictly negative for $\kappa = 1+\varepsilon$.
:::

::: proof
*The count.* Since $\pi$ is uniform, $\pi(I)$ is a uniform $k$-subset of $V_R\times V_B$, and the paper's Lemma 4.2 gives
$$\mathbb{P}\big(|\pi_R(I)| = x_Rk,\ |\pi_B(I)| = x_Bk\big) \;\le\; \exp\!\left(-\frac{2-x_R-x_B}{2}(1+o(1))\,k\log n\right).$$
Also $\binom nk = n^{k/2+o(k)} = \exp\big(\tfrac12 k\log n(1+o(1))\big)$, because $\log(n/k) = (\tfrac12+o(1))\log n$ for $k = \kappa\sqrt{n\log n}$. Multiplying, the number of $k$-sets with projections of these sizes is $\exp\big(\frac{x_R+x_B-1}{2}k\log n(1+o(1))\big)$.

*The probability.* By the projection criterion the two colours are independent conditions, so
$$\mathbb{P}(I \text{ independent}) \;\approx\; (1-p)^{\binom{x_Rk}{2}}\,(1-p)^{\binom{x_Bk}{2}} \;\approx\; \exp\!\left(-\frac{p k^2}{2}\big(x_R^2+x_B^2\big)\right).$$
Now evaluate $pk^2/2$ with $\beta = \tfrac12$ and $k = \kappa\sqrt{n\log n}$:
$$\frac{pk^2}{2} = \frac12\cdot\frac12\sqrt{\frac{\log n}{n}}\cdot \kappa^2 n\log n = \frac{\kappa^2}{4}\sqrt{n\log n}\,\log n = \frac{\kappa}{4}\,k\log n .$$
So the probability exponent is $-\frac{\kappa}{4}(x_R^2+x_B^2)$ in units of $k\log n$, as claimed.

*The optimisation.* $\partial g/\partial x_R = \tfrac12 - \tfrac{\kappa}{2}x_R = 0$ gives $x_R = 1/\kappa$, and likewise $x_B = 1/\kappa$; the function is concave, so this is the maximum. Its value is
$$g\!\left(\tfrac1\kappa,\tfrac1\kappa\right) = \frac{2/\kappa - 1}{2} - \frac{\kappa}{4}\cdot\frac{2}{\kappa^2} = \frac1\kappa - \frac12 - \frac{1}{2\kappa} = \frac{1-\kappa}{2\kappa}.$$
:::

Two features of this computation deserve to be pointed out. First, the optimum sits at $x_R = x_B \approx 1$: the dangerous sets are the *generic* ones, whose projections are essentially injective. Second, sets with $x_R + x_B < 1$ need no argument at all — the counting exponent is already negative, so **no $k$-sets with projections that small exist**.

::: warn What the real proof has to do that this computation does not
The calculation above is the skeleton. Two things make the paper's Sections 3 and 4 longer than one page.

1. **The deleted edges.** Every deleted edge joins the two endpoints of a monochromatic path of length two, hence lies inside some neighbourhood $N_v$. A devious $k$-set could hide behind exactly those. The paper therefore classifies every vertex $v \in V_R\cup V_B$ by how much of $I$ sits in its neighbourhood — into *huge*, *large*, *medium* and *small*, with cutoffs $t_1 = \sqrt{n\log n}/\log\log n$, $t_2 = n^{1/4+\varepsilon}$, $t_3 = n^{2\varepsilon}$ — and shows that all but the huge class contribute only $o(k^2)$ unusable pairs. The huge class is tiny: at most $2\log\log n$ vertices. Those few neighbourhoods are the correction terms in the paper's function $f(\ell_R,\ell_B)$. Chernoff and McDiarmid bounds do the work.
2. **The middle window.** For $x_R+x_B \approx 1$ neither the counting nor the probability wins on its own, and the neighbourhood bound must be brought in as well. That is the third case of the paper's Lemma 4.2.

The vocabulary is borrowed from the triangle-free process: pairs lying inside a common neighbourhood are called *closed*, the rest *open*.
:::

## 15. Cashing it in

::: theorem Theorem 1.3 of the paper
For every $\varepsilon>0$ there is $n_0$ such that for all $n \ge n_0$ there exists a triangle-free graph $G$ on $n$ vertices with
$$\alpha(G) \;<\; (1+\varepsilon)\sqrt{n\log n}.$$
:::

The construction of Section 12 is such a graph: Section 13 makes it triangle-free at a cost of a $o(1)$ fraction of its edges, and Section 14 shows that no $k$-set with $k = (1+\varepsilon)\sqrt{n\log n}$ is independent.

::: theorem Theorem 1.2 of the paper
$$R(3,k) \;\ge\; \left(\frac12 + o(1)\right)\frac{k^2}{\log k}.$$
:::

::: proof
Apply the conversion lemma of Section 7 with $A = 1+\varepsilon$, which is legitimate by Theorem 15.1:
$$R(3,k) \;\ge\; \left(\frac{1}{2(1+\varepsilon)^2} - o(1)\right)\frac{k^2}{\log k}.$$
Letting $\varepsilon \to 0$ gives the claim.
:::

And by Theorem 8.1 this is the end of the road for constructions of this type: the average degree and the independence number now agree, both equal to $\sqrt{n\log n}$, which is the minimum of $\max(c,1/c)$. In the authors' own words:

> *"In our construction, independence number and average vertex degree asymptotically agree, and they are the same as a random graph of the same density. Any construction improving on the constant $\tfrac12$ would have to have lower density, and at the same time independence number smaller than the random graph of that density."*

As a check on the framework: they also note that the Campos–Jenssen–Michelen–Sahasrabudhe construction has independent sets exactly $3/2$ times its average degree — which is what $c = \sqrt{2/3}$ predicts, since $(1/c)/c = 3/2$.

\pagebreak

## 16. The intuition, in one page

If the audience remembers nothing else, it should be this.

**The problem is a balancing act with one knob.** You want a triangle-free graph with no large independent set. Make it too dense and a single vertex's neighbourhood is already a large independent set, because in a triangle-free graph neighbours are never adjacent. Make it too sparse and a greedy sweep finds a large independent set. The optimum is where the two coincide, and at that point the degree and the independence number are both $\sqrt{n\log n}$.

**Randomness alone cannot reach the optimum.** A random graph of that density is riddled with triangles — about $\log n$ per edge — and repairing it by deleting an edge from each triangle would delete everything. That caps the classical method at density $n^{-1/2}$, a factor $\sqrt{\log n}$ short. Every advance in sixty-five years has been an attempt to build denser than that while still looking random.

**A blow-up walks straight past the cap — and pays for it in structure.** Take a random graph on only $n/s$ vertices. On so few vertices the density you want is *far below* the local triangle threshold, so the graph is essentially triangle-free already; make it exactly triangle-free by deleting a few edges, then blow each vertex up into $s$ copies. Blowing up preserves triangle-freeness *exactly* and preserves the density, so you now have a triangle-free graph of a density that was unreachable. The price is that a blow-up is transparently structured: any independent set of the small graph, blown up, is an enormous independent set of the big one.

**Two blow-ups laid on top of each other cancel each other's structure.** Give every vertex a random pair of coordinates — a row and a column of a large grid — and join two vertices when their rows are adjacent in one random graph, *or* their columns are adjacent in another, independent one. Each half is a blow-up, so each half is dense and triangle-free. But the large independent sets of the row-structure are, with respect to the columns, completely random sets, and the column graph destroys them; and vice versa. What survives is a set that must dodge two independent random graphs at once — which is exactly the first-moment behaviour of a *single* random graph at the combined density. The construction is highly structured, yet the counting cannot tell it apart from a random graph.

**The union has triangles, but they come in bunches, and that is the whole trick.** Mixing two graphs creates triangles — about $\log n$ per edge, just as before. But in a blow-up, adjacency depends only on which row (or column) you are in. So if some vertex $w$ closes a triangle on the edge $uv$, then *every one of the $s$ vertices in $w$'s row* closes a triangle on that same edge. The triangles are not spread out; they are **stacked**, $s$ of them on a single edge. Deleting that one edge destroys all $s$. With $s = \log^2 n$ and only $\log n$ triangles per edge, the number of deletions per edge is $1/\log n$ — the repair is essentially free.

That is the paper. The classical method failed because triangles were spread thin; the blow-up does not remove the triangles, it **piles them up so that one deletion handles many**.

::: idea The one-sentence version
*Randomness gives triangle-free graphs that are too sparse; blow-ups give graphs that are dense but too structured; overlay two blow-ups and the structures cancel while the density survives — and the triangles you create pile up so neatly that they can be swept away almost for free.*
:::

**Why this is the end of the road.** At the optimum the construction's independence number equals its average degree, and both equal what a random graph of the same density would give. To beat the constant $\tfrac12$ you would need a triangle-free graph that is *sparser* and yet has independent sets *smaller than a random graph of that density* — an object nobody knows how to build for any problem of this type. The remaining gap to the known upper bound is a factor of $2$, and it now has a precise name: by Davies–Jenssen–Perkins–Roberts it is the assertion that in a triangle-free graph the *largest* independent set is at least twice the *average* one, as it is in a random graph.

**A footnote on style, which is part of the story.** The two previous constructions of this quality were a $125$-page AMS Memoir and a $52$-page paper, both analysing a random *process* through differential equations. This is a construction: five lines to write down, two estimates to check, fifteen pages. Joel Spencer wrote in 2011 that the constant "seems beyond our reach", and in the same chapter: *"My dream is a ten-page paper which gives $R(3,k) = \Theta(k^2/\log k)$."* The authors point out that a weakened version of their construction, combined with Shearer's one-page upper bound, would hand him exactly that.

The method has already left the building: within five months it had been used for cycle-complete Ramsey numbers $r(C_\ell,K_k)$, for star hypergraph Ramsey numbers, and by Kühn, Sauermann, Steiner and Wigderson to **disprove the odd Hadwiger conjecture**.

---

## 17. What is proved here, and what is not

::: note Provenance
**Proved in full above,** from first principles: the dictionary (§2); $\alpha \ge \Delta$ and Caro–Wei (§3); $R(3,k)\le k^2$ (§4); the first-moment bound for $G(n,p)$ (§5); the conversion lemma and the barrier $A(c) = \max(c,1/c)$ (§7–8); that blow-ups beat the deletion threshold and that a single blow-up has independence number $s\,\alpha(H)$ (§10–11); the bunching lemma and the deletion cost (§13); the projection criterion and the exponent computation locating $\kappa = 1$ (§14); and Theorem 1.2 from Theorem 1.3 (§15).

**Stated without proof:** the second-moment lower bound on $\alpha(G(n,p))$ discussed in §5 — used only for the heuristic barrier of §8, never inside a proof; the monotonicity of $f$ and of its successive differences, used in §9.2 (a calculus exercise in Shearer's Lemma 1); the Davies–Jenssen–Perkins–Roberts theorem quoted in §9.3, which is proved by the occupancy method; and the paper's Lemma 4.2 tail estimate quoted inside the proof in §14.

**Heuristic, not proof:** the independence computation of §14 is the paper's Section 4 with its correction terms dropped. It reproduces the sharp threshold $\kappa=1$ exactly, which is why it is worth seeing, but the corrections are what the paper's Section 3 exists to control; §14's caveat box says precisely what they are.

**Mine, not the paper's:** the normalisation $p = c\sqrt{\log n/n}$, the function $A(c) = \max(c,1/c)$ and the exchange rate $A \mapsto 1/(2A^2)$ are an organising device for these notes. They are faithful — the authors state the same conclusion in prose, quoted in §15 — but the framing should not be attributed to them.
:::

### References

- Z. Hefty, P. Horn, D. King, F. Pfender, *Improving $R(3,k)$ in just two bites*, arXiv:2510.19718 (v3, February 2026).
- M. Campos, M. Jenssen, M. Michelen, J. Sahasrabudhe, *A new lower bound for the Ramsey numbers $R(3,k)$*, arXiv:2505.13371 (2025).
- G. Fiz Pontiveros, S. Griffiths, R. Morris, *The triangle-free process and the Ramsey number $R(3,k)$*, Memoirs AMS 263 (2020).
- T. Bohman, P. Keevash, *Dynamic concentration of the triangle-free process*, Random Structures & Algorithms (2021).
- J. H. Kim, *The Ramsey number $R(3,t)$ has order of magnitude $t^2/\log t$* (1995).
- J. B. Shearer, *A note on the independence number of triangle-free graphs*, Discrete Math. 46 (1983) 83–87; and *…, II*, J. Combin. Theory Ser. B 53 (1991) 300–307.
- P. Erdős, *Graph theory and probability II*, Canad. J. Math. 13 (1961).
- E. Davies, M. Jenssen, W. Perkins, B. Roberts, *On the average size of independent sets in triangle-free graphs*, Proc. AMS 146 (2018).
