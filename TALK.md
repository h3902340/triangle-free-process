# Talk transcript — *Improving R(3,k) in just two bites*

**Paper:** Zion Hefty, Paul Horn, Dylan King, Florian Pfender, *Improving R(3,k) in just two bites*, arXiv:2510.19718 (October 2025).
**Slot:** 2026‑09‑01, 14:00–16:00 (with a 10‑minute break at ~15:08).
**Audience:** no prior knowledge assumed. Whiteboard available.

---

## ⚠️ Read this first (author's note)

I could **not** open the arXiv PDF while writing this (network egress to arxiv.org was blocked in my environment). Everything here was reconstructed from:

* the abstract and seminar announcements (verified by search),
* Robert Morris's survey *Some recent results in Ramsey theory* (arXiv:2601.05221), which describes the construction as **"the union of two blow‑ups of a random graph, placed randomly on top of one another"**, and
* my own re‑derivation of every calculation from scratch (all the arithmetic in this transcript I did and checked myself; one factual claim — the density at which the triangle‑free process stops — I verified by writing and running a simulation, see Appendix C).

The **history, the statements of results, and the "master calculation" that organises the whole talk are solid.** The parts you should double‑check against the actual PDF before you speak are flagged in the text with **[CHECK]**. They are mostly: the exact choice of parameters (cluster size *s*, base density *q*), how the authors phrase the deletion lemma, and whether they state their result for general *H*‑free settings beyond triangles.

Everything else you can deliver as written.

---

## Practical notes

**Timing map** (the numbers in the transcript are wall‑clock times):

| Time | Part | Content |
|---|---|---|
| 14:00 | 0 | The party problem; R(3,3)=6 |
| 14:10 | 1 | Ramsey numbers, and the translation into graph language |
| 14:25 | 2 | The easy bounds: √n, and Erdős's random graph |
| 14:45 | 3 | The upper bound side: Ajtai–Komlós–Szemerédi and Shearer |
| 14:55 | 4 | **The master picture** — one dial, one formula, all the results |
| 15:08 | — | **Break (10 min)** |
| 15:18 | 5 | The triangle‑free process, and why it stops too early |
| 15:33 | 6 | **The paper: two bites** |
| 15:55 | 7 | Where things stand, open problems, questions |

**If you are running late**, cut in this order: (1) the Petersen graph digression in Part 1, (2) the derivation of α(G(n,p)) in Part 2 — just state it, (3) Part 5's differential‑equation discussion — say "it takes 200 pages" and move on. **Never** cut Part 4; it is the spine of the talk.

**Board plan.** You will want four board areas. Reserve them at the start and *do not erase them*:

* **Board A (top left, keep all talk):** the dictionary
  `R(3,k) > n  ⟺  ∃ G on n vertices, triangle-free, α(G) < k`
* **Board B (top right, keep all talk):** the two forces
  `α ≥ Δ ≈ d` and `α ≈ 2n·log d / d`
* **Board C (main, centre):** the master calculation of Part 4 — the dial *c*, the function `A(c) = max(c, 1/c)`, and the results table. Keep this from 14:55 to the end.
* **Board D (scratch):** everything else; erase freely.

**Notation you will use all talk** (write it once, at 14:25, and leave it up):
`n` = number of vertices, `p` = edge probability/density, `d` = pn = average degree, `α(G)` = size of the largest independent set, `Δ` = max degree, `log` = natural log.

---

# Part 0 — 14:00 — The party problem

> Good afternoon. I want to tell you about a paper that came out last October, by Zion Hefty, Paul Horn, Dylan King and Florian Pfender. It's called *"Improving R(3,k) in just two bites."* It's about a number that people have been trying to pin down for sixty‑five years, and this paper moves it to what a lot of people believe is the final answer.
>
> I should say up front: I am not a specialist in this area. So I'm going to do this the way I'd want it done for me — from the beginning, with nothing assumed. By the end of the afternoon you will understand, honestly and in detail, what the new construction is and why it works. It is genuinely simple. That's the punchline of the paper: the previous proofs were 200‑page monographs, and this one is a few pages.
>
> Let's start with a puzzle you may have heard.
>
> **Six people are at a party.** Any two of them either know each other, or they don't. Claim: among any six people, there are always **three who all know each other**, or **three who are all mutual strangers**.

**[WB — Board D]** Draw six dots. Draw a couple of solid lines (= "know each other") and a couple of dashed lines (= "strangers").

> Let me prove it, because the proof is thirty seconds long and it is the seed of everything today.
>
> Pick any person — call her *v*. She has five relationships with the other five people. Each is either "knows" or "stranger". Five things, two categories, so one category contains at least three of them. Say **v knows three people**, *x*, *y*, *z*. Now look at those three. If any two of them know each other — say *x* and *y* — then *v*, *x*, *y* are three mutual acquaintances and we're done. Otherwise none of them know each other, and *x*, *y*, *z* are three mutual strangers. Done either way.

**[WB]** Draw exactly this: *v* with three solid edges to *x*, *y*, *z*, then the triangle on *x*,*y*,*z* dashed.

> Two remarks. First: notice the shape of the argument — **pigeonhole, then a case split**. That's essentially the only tool anyone had for forty years on the *upper* bound side.
>
> Second, and more important: **five people are not enough.** Here's the counterexample.

**[WB]** Draw a pentagon *C₅* — five dots in a circle, five solid edges around the rim.

> Seat five people in a circle; each knows their two neighbours and nobody else. Do you see three mutual acquaintances? No — the acquaintance graph is a 5‑cycle, and a 5‑cycle has no triangle. Do you see three mutual strangers? Take any three of the five people; among five in a circle, any three of them include two who are neighbours. So no.
>
> Please remember this pentagon. It is the very first example of the object that this entire talk is about: **a graph with no triangle, in which you also cannot find many mutually non‑adjacent vertices.** Everything after this is that same pentagon, on a million vertices, done as well as it can possibly be done.

*(If asked "why 5 and 6?" — say: that's exactly the content of the number R(3,3) = 6, which we define next.)*

---

# Part 1 — 14:10 — Ramsey numbers, and the translation

> Let me set up the language properly.
>
> A **graph** is a set of vertices, some pairs joined by edges. In the party, vertices = people, edges = "they know each other".
>
> Now, the general statement. Colour every edge of a big complete graph — every pair joined — with red or blue.

**[WB — Board A, top]**

```
R(s,t) = the smallest n such that:
   every red/blue colouring of all pairs of an n-element set
   contains a red K_s  (s points, all pairs red)
   or a blue K_t       (t points, all pairs blue)
```

> **Ramsey's theorem (1930)** says this number is finite for every *s* and *t*. That's already not obvious — it says you cannot colour arbitrarily large structures without creating order somewhere. Complete disorder is impossible. That slogan is the whole field.
>
> The party problem says **R(3,3) = 6**: six is enough, five is not, and the pentagon was our proof that five is not.
>
> Now, how much do we know about these numbers? Here's the embarrassing truth.

**[WB — Board D]**

```
R(3,3)=6   R(3,4)=9   R(3,5)=14   R(3,6)=18
R(3,7)=23  R(3,8)=28  R(3,9)=36   R(3,10)=40 or 41  ← unknown!
```

> That's it. We do not know R(3,10). We know it's 40 or 41 and nobody can close the gap. For the *diagonal* numbers it's worse: R(5,5) is unknown — somewhere between 43 and 46. Erdős's famous line: if aliens threatened to destroy Earth unless we computed R(5,5), we should marshal all our computers and mathematicians and try; but if they asked for R(6,6), we should attempt to destroy the aliens first.
>
> So exact values are hopeless. The mathematics is about **asymptotics**: how does R(3,k) grow as k → ∞? Today, *s* = 3 is fixed and *k* → ∞. This is called the **off‑diagonal** case, and it is the case where we actually know the growth rate.

## The translation into graph language

> Here is the single most important move of the talk. It takes a statement about colourings and turns it into a statement about a single graph.
>
> A red/blue colouring of all pairs is the same thing as **a graph**: let *G* be the graph of red edges. Then blue edges are exactly the non‑edges of *G*.
>
> * A red triangle = a triangle in *G*.
> * A blue *K_k* = *k* vertices with **no** edges of *G* between them. That's called an **independent set** of size *k*.
>
> We write **α(G)** for the size of the largest independent set in *G*. So:

**[WB — Board A, big, and leave it up all afternoon]**

```
      R(3,k) > n
         ⟺
∃ a graph G on n vertices with:
     (i)  G has no triangle
     (ii) α(G) < k     (no k vertices are pairwise non-adjacent)
```

> Read it out loud, because we will use it fifty times: **to prove a lower bound on R(3,k), you must build a triangle‑free graph on many vertices whose independent sets are all small.**
>
> That's it. That is the whole problem. The rest of this talk is: *how do you build such a graph?* The pentagon was the case n = 5, k = 3.
>
> One more example so it's concrete. *(Cut this if behind.)*

**[WB]** Draw the Petersen graph — outer pentagon, inner pentagram, five spokes.

> The Petersen graph: 10 vertices, no triangles, and its largest independent set has 4 vertices. So there's no red triangle and no blue *K₅*, which proves R(3,5) > 10. The true value is 14, so even here the best construction is cleverer than the most famous graph in combinatorics. These small cases are done by computer search and they tell you nothing about the asymptotics. We need constructions that scale.

## Which way is which

> Let me nail down the logic, because sign errors here are fatal.
>
> * **Lower bound on R(3,k)** = "R(3,k) is big" = **a construction**: I hand you a triangle‑free graph with small α. This is where all the excitement is, and where today's paper lives.
> * **Upper bound on R(3,k)** = "R(3,k) is small" = **a theorem about all graphs**: *every* triangle‑free graph on n vertices has a large independent set.

**[WB — Board B, and leave it up]**

```
LOWER BOUND  = build one good graph      (this paper)
UPPER BOUND  = a theorem about all graphs
```

---

# Part 2 — 14:25 — The easy bounds, and Erdős's random graph

> Let's get our hands dirty. First question: **how small can α(G) be, if G is triangle‑free on n vertices?**
>
> Two observations. Both are two lines. Together they are, I promise you, the entire subject.

**[WB — Board B, under the previous]** Write the standing notation first:
`n = #vertices, d = average degree, Δ = max degree, α = largest independent set`

> **Observation 1 (the neighbourhood bound).** Take any vertex *v*, and look at its neighbours *N(v)*. Can two neighbours be adjacent to each other? No! — that would make a triangle with *v*. So **the neighbourhood of every vertex is an independent set**. Therefore

```
α(G) ≥ Δ(G) ≥ d      (★ "you can't be too dense")
```

> This is the first force in the problem: **making the graph dense creates a big independent set for free**, namely a neighbourhood.
>
> **Observation 2 (greedy).** Repeatedly pick any vertex, put it in your independent set, delete it and all its neighbours. Each step costs you at most Δ+1 vertices, so you get an independent set of size at least n/(Δ+1). Therefore

```
α(G) ≥ n/(d+1)   roughly    (★★ "you can't be too sparse")
```

> This is the second force: **making the graph sparse leaves lots of room** for an independent set.
>
> Now put them together. You are trying to make α small, and you have one dial to turn — the density.

**[WB]** Draw two crossing curves against *d* on the x-axis: the increasing line `d`, the decreasing curve `n/d`. Mark the crossing.

> If you make the graph dense, (★) kills you. If you make it sparse, (★★) kills you. The best you can do is balance them: *d* = n/d, i.e. **d = √n**, and then α ≥ √n.
>
> So **every** triangle‑free graph on n vertices has α ≥ √n. Translate through our dictionary: if α < k then √n < k, so n < k². Hence

```
R(3,k) ≤ k² + 1        (two lines of work!)
```

> And in the other direction? Can we build a triangle‑free graph with α as small as √n? If we could, we'd have R(3,k) ≈ k² and we'd be done. **This balance — dense enough that there's no room, sparse enough that no neighbourhood is huge — is the whole game.** Everything from now on is putting logarithms in the right places on both sides of this.
>
> Now let's try to actually build the graph.

## Attempt 1: pure randomness

> The natural thing to try, and historically the first thing anyone tried: **flip coins**.
>
> **G(n,p)**: take n vertices, and include each of the C(n,2) pairs as an edge independently with probability *p*.

**[WB — Board D]** `G(n,p): n vertices, each pair an edge independently w.p. p`

> Two things we need to know about it.
>
> **(a) How big are its independent sets?** Fix a set *S* of *a* vertices. It is independent exactly when all C(a,2) ≈ a²/2 pairs inside it are non‑edges, which happens with probability (1−p)^(a²/2) ≈ e^(−p·a²/2). Now count how many sets we have to worry about — this is called the *first moment method* or *union bound*:

**[WB]** (do this calculation carefully, it recurs three more times today)

```
E[# independent sets of size a] = C(n,a) · (1-p)^{C(a,2)}
                                ≈ exp( a·log(n/a) − p·a²/2 )

  → this is < 1  as soon as   p·a/2 > log(n/a),  i.e.  a ≳ (2/p)·log(np)
```

> So with high probability **α(G(n,p)) ≈ (2/p)·log(np)**. Write that down; it is the most‑used formula of the afternoon.
>
> Notice, in passing, the meaning of the factor 2: if you build an independent set greedily in a random graph you get about (1/p)·log(np), and the truth is exactly twice that. Greedy is off by a factor of 2. **Hold on to that 2** — the entire remaining gap in this problem is that factor of 2.
>
> **(b) How many triangles does it have?** Expected number = C(n,3)·p³ ≈ n³p³/6. And the number of edges is ≈ n²p/2. So

```
(#triangles)/(#edges) ≈ n p²  = (average degree) × p
```

> **Attempt 1 fails**, obviously: G(n,p) has triangles. But there's a classic repair, due to Erdős.

## The alteration trick, and the first real theorem

> **Alteration**: take G(n,p), then **delete one edge from every triangle**. What's left is triangle‑free. And deleting edges can only *increase* α, but if we delete only a small fraction of edges, α shouldn't change much.
>
> For this to work we need the triangles to be fewer than the edges: from the ratio above, we need **np² ≲ 1**, i.e.

```
p ≈ 1/√n
```

> That's the ceiling on the density of this method. Now plug into the independence formula: with p = n^(−1/2), np = √n, so

```
α ≈ (2/p)·log(np) = 2√n · (1/2)log n = √n · log n
```

> Compare that with the ideal √n from our balance calculation: we are off by a factor of **log n**. And through the dictionary (α < k, so k ≈ √n log n, so n ≈ k²/log²n ≈ k²/(4 log²k)):

```
Erdős 1961:   R(3,k) ≥ c · k² / (log k)²
```

> Versus the upper bound k². So by 1961 we knew: R(3,k) is between k²/log²k and k². **A gap of a squared logarithm**, and closing it took thirty‑four years.
>
> And here's the thing I want you to take from this part: the failure is *precisely* the ceiling p ≤ 1/√n. Random graphs cannot be denser than that without drowning in triangles. Every advance in the next sixty years is an answer to the question: **how do I build a triangle‑free graph that is denser than 1/√n but still behaves like a random graph?**

**[WB — Board B]** Write the standing goal, boxed:

```
GOAL:  triangle-free, but as random-like and as dense as possible.
       The ceiling p ~ 1/√n is what we must beat.
```

---

# Part 3 — 14:45 — The upper bound side (so we know what we're aiming at)

> Before we go hunting for constructions, let me tell you the target — how good could a construction possibly be? That's the upper bound side: theorems that say *every* triangle‑free graph has a biggish independent set.
>
> We proved one already: α ≥ √n. It came from balancing `α ≥ d` against `α ≥ n/d`. The improvement is to replace the crude greedy bound `n/d` by something with a logarithm in it.
>
> **Theorem (Ajtai–Komlós–Szemerédi 1980; sharpened by Shearer 1983).** Every triangle‑free graph on n vertices with average degree d has

```
α(G) ≥ (1 + o(1)) · n·log d / d
```

**[WB — Board B, right under the greedy bound]**

> Do you see what that is? It's the greedy bound `n/d` multiplied by **log d**. Why should a logarithm appear? Intuition: run the greedy algorithm, but *cleverly*. In a triangle‑free graph, when you pick a vertex *v* you learn a lot — all of *N(v)* is independent, so you should sometimes prefer to descend into a neighbourhood rather than take *v* itself. Shearer's proof is a beautiful induction with a carefully chosen weighting; it's about a page and I'm happy to sketch it in questions.
>
> Now redo the balancing act with the improved bound. We need

```
α ≥ max( d ,  n log d / d )
```

**[WB]** Same two crossing curves as before, but the decreasing one now has a log on it.

> The crossing is at d² = n log d. Since d will turn out to be around √n, we have log d ≈ ½ log n, so

```
d² ≈ ½ n log n     ⟹     d ≈ √(n log n / 2)
     ⟹  every triangle-free graph has  α ≥ (1/√2 + o(1))·√(n log n)
```

> Now convert to a Ramsey bound. Let me do the conversion once, carefully, and then we'll reuse it all afternoon. Suppose we have a triangle‑free graph with

```
α = A·√(n log n)        (A is the number we care about)
```

> Setting k = α, we get k² = A²·n·log n. And n is about k² up to logs, so **log n = (2 + o(1))·log k**. Substituting:

```
k² = A²·n·(2 log k)      ⟹      n = (1/(2A²)) · k²/log k
```

**[WB — Board C, top. This is the most important formula of the talk. Box it.]**

```
   α = A·√(n log n)      ⟷      R(3,k)  =  (1/(2A²)) · k²/log k

        smaller A  =  better construction  =  bigger Ramsey bound
```

> Check it against what we just proved: Shearer forces A ≥ 1/√2, so A² ≥ 1/2, so the constant 1/(2A²) ≤ 1:

```
Shearer 1983:   R(3,k) ≤ (1 + o(1))·k²/log k
```

> And that is **still the best known upper bound today**, forty‑three years later.
>
> So here is the state of the world as of 1983, and it's where the real story begins:

**[WB — Board C]**

```
    c·k²/(log k)²   ≤   R(3,k)   ≤   (1+o(1))·k²/log k
       (Erdős '61)                     (Shearer '83)
```

> There's a whole logarithm between them, and the question — *which end is the truth?* — was open. Erdős offered money for it. In 1995 Jeong Han Kim answered it: **the upper bound is the truth, up to the constant.**

```
Kim 1995:   R(3,k) ≥ c·k²/log k     (with c = 1/162, a small explicit constant)
```

> So the *order of magnitude* is k²/log k, settled thirty years ago. Since then, the entire game — and this paper — has been about **the constant in front**. And by our boxed formula, the constant in front is nothing but the number **A**: how small can you make the independent sets, measured in units of √(n log n)?

*(Timing check: it should be about 14:55. Take a sip of water. The next 13 minutes are the heart of the talk.)*

---

# Part 4 — 14:55 — The master picture

> Everything from 1995 to 2025 fits on this one board. I'm going to build it now and then never erase it.
>
> **The one dial.** Every construction we will discuss produces a graph that is *pseudorandom* — it looks locally like a random graph — of some density. Parametrise the density like this:

**[WB — Board C, centre, big]**

```
        p = c · √(log n / n)          ← c is THE DIAL
        d = pn = c·√(n log n)         ← average degree
```

> Why this scaling? Because it's the scale at which the problem lives: recall the balance point was d ≈ √(n log n). The dial *c* is a pure number, and every result in this area is a statement about **how large a c you can achieve**. Erdős's construction, in these units, had p = 1/√n — that's c = 1/√(log n), which tends to 0. Everybody since has been pushing *c* up.
>
> Now, the two forces. Both give lower bounds on α, and I'll express both in units of √(n log n).
>
> **Force 1 — neighbourhoods (★).** α ≥ d = c·√(n log n). So **A ≥ c**. *Denser is worse.*
>
> **Force 2 — first moment.** If the graph behaves like a random graph of the same density, its independent sets have size (2/p)·log(np). Let's evaluate: np = c√(n log n) = n^(1/2 + o(1)), so log(np) = (½ + o(1))·log n, and

```
α ≈ (2/p)·(½ log n) = log n / p = (1/c)·√(n log n)
```

> So **A ≥ 1/c**. *Sparser is worse.* — and note this matches Shearer's `n log d/d` **times two**, exactly the greedy‑versus‑optimal factor 2 I flagged earlier.

**[WB — Board C, centre. This is the punchline of the entire talk.]**

```
        A(c)  =  max( c , 1/c )

              ↑ neighbourhood bound        ↑ random-graph bound
                (dense is bad)               (sparse is bad)

        minimised at   c = 1 ,  where  A = 1
```

**[WB]** Draw it: the V‑shaped graph of max(c, 1/c) against c, with its minimum at (1, 1). Mark the points c = 1/√2, c = √(2/3), c = 1 on the axis.

> Look at what this says. **The best you could possibly hope for from a pseudorandom triangle‑free graph is A = 1**, achieved at exactly one density, c = 1. At that density two completely different things coincide: the maximum degree, and the size of a random‑like independent set. Both equal √(n log n).
>
> Now feed A = 1 into the boxed dictionary: 1/(2A²) = **1/2**.

**[WB — Board C, right side. Build this table live, filling in rows as you go through history.]**

```
      c            A = max(c,1/c)     constant 1/(2A²)     who
   ------------------------------------------------------------------
   1/√log n  →0        →∞              →0  (log² loss)     Erdős 1961
     ~small           large            1/162               Kim 1995
     1/√2 = .707       √2               1/4                Bohman–Keevash;
                                                           Fiz Pontiveros–
                                                           Griffiths–Morris
     √(2/3)= .816     √(3/2)            1/3                Campos–Jenssen–
                                                           Michelen–
                                                           Sahasrabudhe 2025
      1                 1               1/2                THIS PAPER 2025
   ------------------------------------------------------------------
   (any c > 1 is worse again — the V goes back up)
```

> This is the whole story of the last thirty years, and it is one number climbing from 0 to 1.
>
> And note the last line of the table. **You cannot do better than 1/2 this way.** The V‑shape has a minimum. So this paper doesn't just improve the constant — it reaches the end of the road for this entire family of arguments. That's why the authors, and several other groups, conjecture that

```
CONJECTURE:  R(3,k) = (1/2 + o(1))·k²/log k
```

> and equivalently, on the upper bound side:

```
CONJECTURE:  every triangle-free graph has α ≥ (1 − o(1))·√(n log n)
             — i.e. Shearer's bound can be improved by a factor of 2.
```

> That's the factor of 2 I asked you to remember: greedy versus optimal in a random graph. Shearer's theorem proves the *greedy* value for all triangle‑free graphs; the conjecture is that the *true* random‑graph value holds for all of them. And after this paper, we know that if that conjecture is true, it is **sharp** — because there's now a construction sitting exactly on it.
>
> So: the remaining gap in this sixty‑five‑year‑old problem is now precisely a factor of 2, and the ball is entirely in the upper bound's court.

*(This is the natural high point. It's about 15:08.)*

> **Let's take ten minutes. When we come back I'll tell you how people actually build these graphs — and then the new idea, which I think you'll find genuinely charming.**

---

## ☕ Break — 15:08–15:18

*(Leave Boards A, B, C up. Erase D.)*

---

# Part 5 — 15:18 — The triangle‑free process, and why it stalls

> Welcome back. Recap in one line: **we want a triangle‑free graph of density p = c·√(log n/n) that behaves like a random graph, and we want c as close to 1 as possible.** Erdős's coin‑flipping got c → 0. How do you do better?

## The idea: be greedy, but randomly

> Here's the natural algorithm, and it's beautiful.

**[WB — Board D]**

```
THE TRIANGLE-FREE PROCESS
  Start with n vertices, no edges.
  Repeat:  pick a uniformly random pair {u,v} such that adding uv
           creates no triangle;  add it.
  Stop when no such pair exists.
```

> Call a pair **open** if adding it wouldn't create a triangle — equivalently, *u* and *v* have no common neighbour. The process adds a random open pair, over and over, until none remain. The result is a **maximal** triangle‑free graph, built as randomly as possible.
>
> This is the right idea, and it beat everything for twenty years. Why should it be better than Erdős's alteration? Because alteration commits to all its coin flips at once and then pays for its mistakes; the process **never makes a mistake** — it only ever adds edges that are legal *given everything so far*. It's the difference between throwing a handful of coins on the floor and placing them one at a time.
>
> Analysing it is another matter. The graph you're building is used to decide the next step, so nothing is independent; there's no formula. The technique — which is a whole industry now — is:
>
> * write down **differential equations** for the quantities you care about (how many open pairs remain, degrees, codegrees, counts of small structures);
> * prove that the actual random quantities **track the solutions** of those equations, with error bars, for as long as possible;
> * the magic word is **self‑correction**: if a quantity drifts above its predicted value, the dynamics of the process push it back down. That's what lets you follow the process for its entire life instead of a short while.
>
> The history:
>
> * **Kim 1995** analysed a semi‑random cousin of this process and got the right order of magnitude, R(3,k) ≥ (1/162)k²/log k. Fields Medal‑adjacent work; it won the Fulkerson Prize.
> * **Bohman 2009** gave a second, cleaner proof by analysing the honest triangle‑free process.
> * **Bohman–Keevash** and, independently, **Fiz Pontiveros–Griffiths–Morris** (announced 2013, published in the following years — the latter is a 125‑page AMS Memoir) pinned it down completely: the process ends with

```
α ≈ √2 · √(n log n)      i.e.  A = √2      ⟹      R(3,k) ≥ (1/4 − o(1))·k²/log k
```

> **Where does that √2 come from?** Look at our V‑diagram. The process ends at density **c = 1/√2 ≈ 0.707**, and there A = 1/c = √2. In other words:

**[WB — Board C, point at the V]** Mark c = 1/√2 on the *left* branch of the V.

> **The triangle‑free process stops on the wrong side of the minimum, and too early.** It is not dense enough. Its independent sets are governed by the random‑graph force, not the neighbourhood force — it's leaving density on the table by a factor of √2.
>
> That's a slightly shocking statement, because the process runs until *no legal edge remains*. How can a maximal triangle‑free graph be "not dense enough"? The naive heuristic actually predicts it should get all the way to c = √2: a random pair has about np² = c² log n common neighbours, so the fraction of open pairs should be about e^(−c²log n) = n^(−c²), which only hits zero around c = √2. But the process does much better than that at closing pairs off — it preferentially eats the open pairs, so they vanish far earlier than a Poisson guess suggests. It suffocates at c = 1/√2.
>
> **I checked this myself** — I wrote a simulation and ran the process to completion:

**[WB — Board D. This is worth putting up; people like seeing a real number.]**

```
   n       final avg degree d      d / √(n log n)
  1000            70.0                 0.843
  2000           103.0                 0.835
  4000           150.8                 0.828
  8000           220.5                 0.822        →  1/√2 = 0.707
```

> Slowly drifting down towards 1/√2, exactly as the theorems say (the convergence is slow — the error terms are of order log log n / log n, which is still 0.25 at n = 8000). And a greedy independent set in those graphs comes out at about 0.78·√(n log n), consistent with the true α being twice that, √2·√(n log n). So the theory is real, and it's on my laptop.
>
> **Fiz Pontiveros, Griffiths and Morris conjectured that 1/4 was the truth** — that the process is optimal. That conjecture stood for a decade.

## 2025: the first crack

> In May 2025, **Campos, Jenssen, Michelen and Sahasrabudhe** disproved it. Their idea, in our language: don't start the process from the empty graph. **Start it from a cleverly chosen "seed" graph**, then run the process (or a nibble) to fill in the rest. The seed was a **blow‑up of a random graph** — I'll define that in two minutes, because it's exactly the object the new paper uses.
>
> Result: c = √(2/3) ≈ 0.816, so A = √(3/2), so

```
Campos–Jenssen–Michelen–Sahasrabudhe 2025:  R(3,k) ≥ (1/3 + o(1))·k²/log k
```

> Still 52 pages, still a nibble argument, still a hard analysis. But it broke the psychological barrier: the process is *not* optimal, and the seed is where the gain comes from.
>
> Five months later, the paper we're here for asked: **what if the seed is the whole story? What if we throw away the nibble entirely?**

---

# Part 6 — 15:33 — The paper: two bites

> Here is the plan for the last twenty minutes. I'll define **blow‑ups**; show you why one blow‑up is a brilliant idea that fails catastrophically; show you why **two** of them fix each other; and then do the two calculations that make the whole thing work. There's no 200‑page analysis coming. It's a construction and two estimates.

## 6.1 Blow‑ups

**[WB — Board D, drawing]** Draw a small graph *H* with 4–5 vertices; then draw each vertex as a blob containing 3 dots; join two blobs by *all* edges when the base vertices are adjacent.

> **Definition.** Take a graph *H* on *m* vertices — call them **clusters**. Replace each cluster by *s* vertices. Join two vertices of the big graph if and only if their clusters are **adjacent in H**. Inside a cluster: no edges. That's the **blow‑up** of *H* by *s*. It has n = m·s vertices.
>
> Two immediate facts. First:
>
> **A blow‑up of a triangle‑free graph is triangle‑free.**
>
> Why? A triangle in the blow‑up uses three vertices; two in the same cluster are never adjacent, so the three lie in three distinct clusters, which then form a triangle in *H*. Contradiction. Note it's an *exact* statement — no "with high probability", no error terms. That's why this object is so useful.
>
> Second: **densities are preserved.** If *H* has density *q*, the blow‑up has density ≈ q as well, and every vertex has degree (degree in H)·s.
>
> Now here's the point that I think is the real idea of the paper. Remember our obstruction: in G(n,p) at the density we want, every edge lies in about log n triangles, so alteration is hopeless. Look at what a blow‑up does to that problem.

**[WB — Board D]**

```
Base graph H = G(m,q),  clusters of size s,  n = ms.
Triangles per edge in the BASE:   ≈ m·q²

We will want the blow-up to have density p = √(log n / n) and m = n/s, q ≈ p/2:

     m·q²  ≈  (n/s)·(log n / n)/4  =  log n / (4s)   →  0   if  s ≫ log n
```

> **That's the trick.** By using a base graph on only m = n/s vertices, the density that's hard to achieve on *n* vertices becomes easy on *m* vertices: the base is so far below *its* triangle threshold that it's essentially triangle‑free already — you delete a o(1) fraction of its edges and you're done. Then you blow it up, and blowing up is *free*: it multiplies the number of vertices by *s* and keeps the density, and triangle‑freeness is exact.
>
> So: **blow‑ups give you a triangle‑free graph of any density you like.** The ceiling p ≤ 1/√n that killed Erdős is gone.
>
> There has to be a catch, and there is.

## 6.2 Why one blow‑up fails

**[WB]** On your blow‑up drawing, shade one blob, then shade a second non‑adjacent blob, then a third.

> A blow‑up is full of enormous independent sets. Take *any* independent set in the base *H* and blow it up: every vertex of it, in every cluster, all pairwise non‑adjacent. So

```
α(blow-up)  =  s · α(H)
```

> With our parameters that's about **2s·√(n log n)** — we wanted √(n log n). We are off by a factor of 2s, and s is large. Catastrophe.
>
> And you can't fix it by choosing *H* more cleverly, because the problem is *structural*: the blow‑up has a rigid geometry, and independent sets exploit geometry. Any single blow‑up is transparent in this way.
>
> **[Pause here. Ask the room:] So what would you do?**
>
> The answer in the previous paper (Campos–Jenssen–Michelen–Sahasrabudhe) was: use the blow‑up as a *seed*, giving you the density, and then run a nibble/process on top to destroy the structure. That works, painfully, and gives 1/3.
>
> The answer in this paper is: **use a second blow‑up.**

## 6.3 The construction

**[WB — Board D, clean space. Write this out in full; it is the paper.]**

```
THE CONSTRUCTION  (Hefty–Horn–King–Pfender)

Parameters:  n vertices.   Cluster size s with   log n ≪ s ≪ √(n/log n).
             m = n/s clusters.   q = ½·√(log n / n).

BITE 1:  • take a random partition π₁ of the n vertices into m clusters of size s
         • take a random base graph H₁ = G(m, q); delete an edge from each of its
           (few) triangles
         • B₁ := the blow-up:  u ~ v  iff  π₁(u) π₁(v) ∈ H₁

BITE 2:  • do it again, completely independently: π₂, H₂, B₂

OVERLAY: G₀ := B₁ ∪ B₂        (take all the edges of both)

CLEAN-UP: delete one edge from each triangle of G₀  ⟶  G,  which is triangle-free.
```

> Say it in words: **two random blow‑ups, laid randomly on top of one another.** Each one is dense and triangle‑free but structurally transparent; and the point is that

> **each blow‑up destroys the large independent sets of the other.**

**[WB]** Draw two overlapping cluster partitions of the same vertex set — e.g. a set of dots grouped into rows (partition 1) and separately into columns (partition 2). This picture sells the whole idea.

> Why? Take one of those catastrophic independent sets of B₁ — a union of B₁‑clusters. With respect to B₂'s partition it is a **completely random** set of vertices, because π₂ was chosen independently. Random sets of that size are certainly *not* independent in B₂; B₂ has an edge inside it, easily. So it dies.
>
> The two structures are, so to speak, incompatible geometries on the same vertex set. Neither one's symmetries help you inside the other.
>
> Now there are exactly two things to check, and they are the two things that could go wrong.
>
> 1. **The union has triangles.** We must remove them without wrecking the graph.
> 2. **The union must have small independent sets.** We need α ≈ √(n log n).

## 6.4 The triangles come in bunches — this is the key lemma

> Let's count the damage. In G₀, density p = 2q = √(log n/n), a typical edge lies in about n·p² = **log n** triangles. Same as the random graph. If those triangles were spread out, we'd have to delete a log n fraction of the edges — everything — and we'd be right back where Erdős was in 1961.
>
> **They are not spread out.** Here's the structure.

**[WB — Board D. Draw this carefully; it's the heart of the proof.]**

> Take any triangle *u, v, w* in G₀ = B₁ ∪ B₂. Each of its three edges comes from B₁ or from B₂. Neither B₁ nor B₂ contains a triangle on its own, so the three edges are not all from the same one. So two of them come from the same graph — say the edges *wu* and *wv* are both in B₂ — and they meet at a vertex; call *w* the **apex**.

```
        w   ← apex;  both edges wu, wv come from the SAME blow-up (say B₂)
       / \
      u---v   ← the "base" edge, from the other blow-up
```

> Now the observation. In B₂, adjacency depends **only on which cluster you are in**. So if *w* is adjacent to both *u* and *v*, then **every one of the s vertices in w's cluster is adjacent to both u and v.**

**[WB]** Shade *w*'s whole cluster and draw the fan of triangles onto the same edge *uv*.

> So triangles do not come one at a time. **They come in bunches of s, all sharing the same base edge uv.** And therefore:

```
   delete the single edge uv   ⟹   kill all s triangles at once.
```

> Count the cost. Per edge *uv*, how many *bunches* are there? One for each cluster that is adjacent (in the appropriate base graph) to both of *u*'s and *v*'s clusters — that's the number of common neighbours in **cluster space**, which is about log n / s. So:

**[WB — box this]**

```
  fraction of edges we must delete  ≈  log n / s   =   o(1)     since s ≫ log n
```

> **That's the paper.** Everything else is bookkeeping. The blow‑up structure concentrates the triangles into bunches of size *s*, so the alteration method — the 1961 idea that could only reach p = 1/√n — suddenly works at p = √(log n / n), which is √(log n) times denser. The whole gain comes from the fact that the same log n triangles per edge are *sitting on top of each other* instead of being spread out.
>
> And notice: **this is where the "two bites" beats the nibble.** The nibble adds edges in many tiny rounds precisely because it must avoid making triangles it can't afford. Here we make a huge number of triangles on purpose, and then delete them almost for free, because they're stacked.

## 6.5 The independent sets

> Second thing to check. We need α(G) ≈ √(n log n). Let's do the first moment, exactly as we did for G(n,p) an hour ago.
>
> Take a set *I* of *a* vertices, with a ≈ √(n log n). Since s ≪ √(n/log n), we have a ≪ m, so *I* lands in *a* distinct clusters in each partition, with room to spare.
>
> For *I* to be independent it must be independent **in B₁ and in B₂** — two independent conditions:

**[WB — Board D]**

```
P(I independent)  ≈  (1-q)^{a²/2} · (1-q)^{a²/2}  =  (1-q)^{a²}  ≈ (1-p)^{a²/2}

  ← exactly the probability for the random graph G(n,p) with p = 2q !
```

> That's the beautiful part: the two independent constraints multiply, and the product is *precisely* the random‑graph answer at the union's density. The construction is structured, but the first‑moment calculation cannot tell it apart from G(n,p). So we get the same threshold as before:

```
   union bound:  C(n,a)·(1-p)^{a²/2} < 1   ⟺   a ≳ log n / p  =  (1/c)·√(n log n)
```

> — and with c = 1, **α ≈ √(n log n)**, which is what we wanted.
>
> Two honest caveats, which is where the real (still short) work in the paper goes:
>
> * Sets *I* that are lopsided — that concentrate in a few clusters of one partition — need to be handled separately. That's exactly the "each blow‑up kills the other's structure" argument, done as a union bound over the possible shapes. **[CHECK against the paper for how they organise this.]**
> * We deleted edges in the clean‑up, and deleting edges can only *create* independent sets. So you don't prove "every a‑set contains an edge", you prove "every a‑set contains **many** edges" — far more than the number of edges you deleted inside it. That's a routine strengthening of the same first‑moment computation. **[CHECK.]**

## 6.6 Cashing it in

> Set the dial to **c = 1**: p = √(log n/n). Then

**[WB — Board C, complete the master picture]**

```
   degree                d = √(n log n)
   independence number   α = √(n log n)     ← they are EQUAL. Both forces balance.
   so  A = 1,   and    R(3,k) ≥ (1/(2·1²) + o(1))·k²/log k

                 R(3,k) ≥ (1/2 + o(1))·k²/log k
```

> And we're done. Up from 1/3, up from 1/4, and — by the V‑shaped diagram — at the exact bottom of what any pseudorandom construction can give.
>
> Let me flag the three sentences worth remembering:
>
> 1. **Blow‑ups make triangle‑freeness free**, because triangle‑freeness of a blow‑up is exactly triangle‑freeness of a much smaller, much sparser base graph.
> 2. **Blow‑ups make triangles collapse into bunches**, so the 1961 deletion method suddenly works at a density it could never reach before.
> 3. **Two independent blow‑ups are pseudorandom**, because each one's structure is invisible to the other's, and their first moments multiply to exactly the random‑graph answer.

## 6.7 Two questions you should be asking

> **"Why exactly two? Why not three, or ten?"** The first‑moment calculation only sees the *total* density, so extra blow‑ups buy you nothing there. One blow‑up is structurally broken; two is already enough to break the structure. Two is the answer because two is the first number bigger than one.
>
> **"Why not push c above 1 and get an even better constant?"** Because past c = 1 the *other* force takes over: the graph's own neighbourhoods are independent sets of size c√(n log n), and they get worse as you densify. The V goes back up. c = 1 is where a triangle‑free graph is as dense as it can be before it starts building large independent sets by hand. **This is a limit of the universe, not of the method.**
>
> **[If asked about general H:]** The authors state the construction as a general tool: for suitable graphs *H* it produces *H*‑free graphs denser than the *H*‑free process, with the pseudorandomness preserved. Triangles are the headline application. **[CHECK how far they push the general statement.]**

---

# Part 7 — 15:55 — Where we stand, and what I'd like you to take away

**[WB — Board C, final state. Point at it while you say this.]**

```
      (1/2 + o(1))·k²/log k   ≤   R(3,k)   ≤   (1 + o(1))·k²/log k
        Hefty–Horn–King–               Shearer 1983
        Pfender 2025
```

> Sixty‑five years of work on this problem, and the gap is now **a factor of two.** And we know exactly what that factor of two *is*: it is greedy versus optimal in a random graph. Shearer's theorem gives every triangle‑free graph the greedy value n·log d/d; the conjecture is that the truth is the random value, twice that. If someone proves it, this problem is closed, and this paper's construction is the reason we'd know the answer is sharp.
>
> Three closing thoughts.
>
> **First, on the shape of progress.** For thirty years the best constructions were *processes* — algorithms you run and then spend a hundred pages proving they behave. This paper is a *construction*: you write it down in five lines, and the analysis is two estimates a graduate student can check. The authors say it explicitly — no nibble, significantly less technical. When a field's best result gets simpler, something has been understood.
>
> **Second, on where the idea came from.** It came from noticing what was doing the work in someone else's proof. Campos–Jenssen–Michelen–Sahasrabudhe used a blow‑up as a seed and then a nibble; the natural question was "how much of the gain is the seed?" The answer was "all of it — do it twice and drop the nibble."
>
> **Third, the one‑sentence version**, if you remember nothing else: *randomness gives you triangle‑free graphs that are too sparse; blow‑ups give you graphs that are dense but too structured; overlay two blow‑ups and the structures cancel while the density survives.*
>
> Thank you. Questions.

---
---

# Appendix A — Cheat sheet (numbers you must not fumble)

```
DICTIONARY
   R(3,k) > n   ⟺   ∃ triangle-free G on n vertices with α(G) < k

TWO FORCES  (G triangle-free, n vertices, avg degree d)
   α ≥ Δ ≥ d                       neighbourhoods are independent
   α ≥ n/(d+1)                     greedy
   α ≥ (1+o(1))·n log d / d        Shearer 1983 (all triangle-free graphs)
   α ≈ 2·n log d / d               random-like graphs (= (2/p)log(np))
                                   ← the missing factor 2

THE DIAL
   p = c·√(log n/n),  d = c·√(n log n)
   A(c) = max(c, 1/c)  where  α = A·√(n log n)
   conversion:  α = A√(n log n)  ⟺  R(3,k) ≈ (1/(2A²))·k²/log k

TABLE
   c = 1/√log n → 0      A → ∞        k²/log²k     Erdős 1961
   c small               —            (1/162)      Kim 1995
   c = 1/√2 ≈ 0.707      A = √2       1/4          Bohman–Keevash / FGM (~2013–20)
   c = √(2/3) ≈ 0.816    A = √(3/2)   1/3          CJMS, May 2025
   c = 1                 A = 1        1/2          Hefty–Horn–King–Pfender, Oct 2025
   upper bound                        1            Shearer 1983

CONSTRUCTION PARAMETERS
   clusters: m = n/s,   cluster size  log n ≪ s ≪ √(n/log n)
   base density q = ½√(log n/n);   union density p = 2q = √(log n/n)
   base triangles per edge  ≈ mq² = log n/(4s) = o(1)
   triangles per edge in the union ≈ log n, in bunches of size s
   ⟹ delete a  (log n)/s = o(1)  fraction of edges

SMALL VALUES
   R(3,3)=6, R(3,4)=9, R(3,5)=14, R(3,6)=18, R(3,7)=23, R(3,8)=28,
   R(3,9)=36, R(3,10) ∈ {40,41} (open)
```

# Appendix B — Questions you should expect

**"Is the o(1) in the lower bound doing something dodgy?"**
No — it's the usual "as k → ∞". The construction has parameters (cluster size *s*) chosen as slowly growing functions of *n*, and every estimate has an error of order log log n/log n or so. Nothing is hidden there.

**"Why √(n log n) and not something else? Where does that scale come from?"**
From balancing the two forces: `d` versus `n log d/d`. Set them equal: d² = n log d ≈ ½ n log n. Any triangle‑free graph optimised for small α lives at that degree.

**"Why does log n become 2 log k?"**
Because n ≈ k²/log k, so log n = 2 log k − log log k = (2+o(1)) log k. Do it on the board if pushed; it's the only place the "2" in 1/(2A²) comes from.

**"Isn't the union of two triangle‑free graphs usually full of triangles?"**
Yes! About log n per edge here. The whole point is that they arrive in bunches of s sharing a common edge, so one deletion kills s of them, and the total deletion is a o(1) fraction. (Draw the fan again.)

**"Could you use three, or a random graph plus a blow‑up?"**
First moment only sees total density, so more blow‑ups don't help. A blow‑up plus a nibble is exactly the previous paper (constant 1/3); it's *worse*, because the nibble limits your density.

**"Does the deletion hurt the independence number?"**
Only if a large set were held together by a few edges. It isn't — the first moment shows every set of size ≈ √(n log n) spans many edges, far more than could be deleted inside it. This is why one proves a robust version of the counting.

**"Is 1/2 conjectured to be the truth, and by whom?"**
Yes — it's stated in this paper's abstract that multiple groups have conjectured 1/2 is asymptotically tight, and the construction now matches it. Equivalently: Shearer's bound should be improvable by a factor of 2 for triangle‑free graphs. **[CHECK who exactly, if you want to name names.]**

**"What about R(4,k), R(5,k)?"**
Much worse understood — the order of magnitude of R(4,k) was only pinned down recently (k³/log⁴k‑ish, Mattheus–Verstraëte 2023 for the lower bound, using an algebraic rather than random construction). The methods here are stated to be flexible for other *H*; how far they reach is a natural question. **[CHECK the paper's own remarks.]**

**"How hard is the paper?"**
Short. That's its selling point: previous constructions of this quality were 50–125 pages of differential‑equation tracking; this is a construction plus two first‑moment estimates.

**"Can I see the triangle‑free process?"**
Yes — `sim/triangle_free_process.c` in the repo, ~60 lines. Compile with `gcc -O2`, run `./tfp 4000`. It runs the process to maximality and prints the final density and a greedy independent set.

# Appendix C — What I verified, and how

* **The master calculation** (`A(c) = max(c,1/c)`, the conversion `1/(2A²)`, the table of constants 1/4, 1/3, 1/2, and Shearer ⇒ 1) — derived from scratch, and every row of the table is consistent with the published constants. This is the part you can lean on hardest.
* **The density of the triangle‑free process.** I simulated it to maximality (exact, not approximate) for n = 500…8000. Final average degree over √(n log n): 0.847, 0.843, 0.835, 0.828, 0.822 — decreasing towards 1/√2 = 0.707, and the corresponding edge‑count constant decreasing towards 1/(2√2) = 0.354, matching the Fiz Pontiveros–Griffiths–Morris / Bohman–Keevash constants. Greedy independent sets came out at ≈ 0.78·√(n log n), consistent with the true α = √2·√(n log n) (greedy finds about half of α in random‑like graphs). This confirms that the new construction (c = 1) really is **strictly denser** than the process, which is what the paper's abstract claims.
* **Not verified against the source** (arXiv was unreachable from my sandbox): the authors' exact parameter choices, the precise statement of their deletion lemma, how they organise the union bound over "shapes" of candidate independent sets, and how general their *H*‑free statement is. These are the **[CHECK]** marks in the text. The *mechanism* is not in doubt — Morris's survey describes the construction as "the union of two blow‑ups of the random graph, placed randomly on top of one another", and every number above is forced by that description — but the presentation details may differ.

# Appendix D — References to have on the last slide / board

* Hefty, Horn, King, Pfender, *Improving R(3,k) in just two bites*, arXiv:2510.19718 (2025).
* Campos, Jenssen, Michelen, Sahasrabudhe, *A new lower bound for the Ramsey numbers R(3,k)*, arXiv:2505.13371 (2025).
* Fiz Pontiveros, Griffiths, Morris, *The triangle‑free process and the Ramsey number R(3,k)*, Memoirs AMS 263 (2020); arXiv:1302.6279.
* Bohman, Keevash, *Dynamic concentration of the triangle‑free process*, Random Structures & Algorithms (2021).
* Bohman, *The triangle‑free process*, Adv. Math. (2009); arXiv:0806.4375.
* Kim, *The Ramsey number R(3,t) has order of magnitude t²/log t* (1995).
* Shearer, *A note on the independence number of triangle‑free graphs* (1983); Ajtai, Komlós, Szemerédi (1980).
* Erdős, *Graph theory and probability II* (1961).
* Morris, *Some recent results in Ramsey theory*, arXiv:2601.05221 — the survey; good for context.
* Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin., Dynamic Survey DS1 — the table of exact values.
