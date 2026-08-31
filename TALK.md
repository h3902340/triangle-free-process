# Talk transcript — *Improving R(3,k) in just two bites*

**Paper:** Zion Hefty, Paul Horn, Dylan King, Florian Pfender, *Improving R(3,k) in just two bites*, arXiv:2510.19718 (v1 October 2025; v3 of 20 February 2026 is the version this transcript follows).
**Slot:** 2026‑09‑01, 14:00–16:00 (with a 10‑minute break at ~15:08).
**Audience:** no prior knowledge assumed. Whiteboard available.

---

## ⚠️ Read this first (author's note)

This transcript has been **checked line by line against the paper** (v3, 20 Feb 2026). The construction in Part 6, the parameters, the deletion rules, the quotes and the history are all as the authors state them.

Three places where I deliberately simplify for a two‑hour general audience, so you know what you're standing on:

* **The "master picture" of Part 4** (the dial *c*, `A(c) = max(c, 1/c)`, the table of constants) is my organising device, not the paper's notation. It is faithful — the authors state its punchline themselves, and I quote them doing so in §6.6 — but don't attribute the diagram to them.
* **The exponent calculation in §6.5** is the honest skeleton of the paper's Section 4 with the correction terms dropped. The paper's function *f* carries those corrections; I say so out loud in the talk.
* **Sections 3 and 4 are 8 pages of careful work** and I compress them into one slide's worth. §6.5's last block says what's actually hard. If someone in the room is a combinatorialist, that's the block they'll ask about.

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

**If you are running late**, cut in this order: (1) the Petersen graph digression in Part 1, (2) the derivation of α(G(n,p)) in Part 2 — just state it, (3) Part 5's differential‑equation discussion — say "it takes 200 pages" and move on, (4) the "what's actually hard" block at the end of §6.5. **Never** cut Part 4 (the spine of the talk) or §6.4 (the one‑lemma heart of the paper).

**Board plan.** You will want four board areas. Reserve them at the start and *do not erase them*:

* **Board A (top left, keep all talk):** the dictionary
  `R(3,k) > n  ⟺  ∃ G on n vertices, triangle-free, α(G) < k`
* **Board B (top right, keep all talk):** the two forces
  `α ≥ Δ ≈ d` and `α ≈ 2n·log d / d`
* **Board C (main, centre):** the master calculation of Part 4 — the dial *c*, the function `A(c) = max(c, 1/c)`, and the results table. Keep this from 14:55 to the end.
* **Board D (scratch):** everything else; erase freely. You will need it clear twice in Part 6 — once for the construction, once for the m × m grid picture.

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
> Now put them together. You are trying to make α small, and there is really only **one number you get to choose** — the density. Think of it as the single knob on the machine: turn it up, the graph gets denser; turn it down, it gets sparser. Everything else follows from where you set it.

**[WB]** Draw two crossing curves against *d* on the x-axis: the increasing line `d`, the decreasing curve `n/d`. Mark the crossing.

> If you make the graph dense, (★) kills you. If you make it sparse, (★★) kills you. The best you can do is balance them: *d* = n/d, i.e. **d = √n**, and then α ≥ √n.
>
> So **every** triangle‑free graph on n vertices has α ≥ √n.
>
> Now let's cash that in. I'm going to do this translation slowly, because we make exactly this move four more times this afternoon, and it's the only place where the Ramsey number talks to the graph theory.

**[WB — point back at Board A]**

> Look at the dictionary. It says R(3,k) > n means: **there exists** a triangle‑free graph on n vertices with α < k. Call such a graph a **witness** — it's a certificate that n vertices still aren't enough to force the pattern.
>
> And what we just proved is a statement about **every** triangle‑free graph: α ≥ √n.
>
> Put the two together. If a witness exists, then √n ≤ α < k, and so n < k². Now read that backwards: **once n reaches k², a witness cannot exist.** No witness means R(3,k) > n is false, which means R(3,k) ≤ n. Take n = k²:

```
      every triangle-free G on n vertices has  α ≥ √n
                          ⇓
        no witness survives once  √n ≥ k
                          ⇓
              R(3,k) ≤ k² + 1        (two lines of work!)
```

> That's the shape of every upper bound in this subject: **a theorem about all graphs kills the witnesses, and killing witnesses bounds R from above.** Constructions build witnesses; theorems destroy them.

*(The +1 is slack, in case you're asked: α ≥ √n is a hair off — the exact balance gives α ≥ √(n+¼) − ½ — so the honest crude bound is k², and I keep the +1 to avoid a rounding digression. Don't put this on the board.)*

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

> **Attempt 1 fails** — but let's be precise about why, because the reason is not that there are *many* triangles. It's that there are *any*. Our witness has to be triangle‑free, full stop; a single triangle disqualifies it.
>
> Now, the obvious response from the floor: *"then just take p small enough that there are no triangles at all."* Let me kill that right now, because it's exactly why this subject is hard.

**[WB]**

```
G(n,p) is honestly triangle-free only when   p = O(1/n)   (average degree O(1))
  → the graph is mostly isolated vertices and little trees
  → α is a CONSTANT FRACTION of n
  → k ≈ cn, so n ≈ k/c, so this proves only  R(3,k) ≳ k     ✗ worthless
```

> Avoiding triangles honestly costs you everything. The graph you get is so thin that it's almost all independent set.
>
> So you have no choice: **build denser than the triangle threshold, and repair the damage afterwards.** And now the ratio we just computed earns its place — it isn't an obituary for Attempt 1, it's the **repair bill**: np² is the number of triangles sitting on each edge. Here's the repair, due to Erdős.

## The alteration trick, and the first real theorem

> **Alteration**: take G(n,p), then **delete one edge from every triangle**. What's left is triangle‑free. And deleting edges can only *increase* α, but if we delete only a small fraction of edges, α shouldn't change much.
>
> So the repair is affordable exactly when the bill is small — when there are fewer triangles than edges, so that deleting one edge per triangle doesn't consume the graph. From the ratio, that means **np² ≲ 1**, i.e.

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

> Do you see what that is? It's the greedy bound `n/d` multiplied by **log d**. Why should a logarithm appear? Here is the honest one‑sentence reason. Pick a random vertex *v*, take it, and throw away *v* together with all its neighbours. Because the graph is triangle‑free, *N(v)* is an independent set — there are no edges inside it — and that means throwing it away destroys **every edge it touches, with nothing counted twice**. In a graph with triangles you'd be double‑counting and destroying fewer. So triangle‑freeness makes each greedy step maximally destructive, the leftover graph gets sparser faster than you'd expect, and iterating that gain is exactly where the logarithm comes from. Shearer's proof is a short induction with a carefully chosen weighting — it's a two‑page paper from 1983, and Appendix D has as much of it as you'd want at a whiteboard.
>
> But here's the meaning of the number, which is better than the proof for our purposes. Take a random graph of average degree d and run the plain greedy algorithm on it — process the vertices in random order, take each one if none of its neighbours is already taken. That returns about **n·log d / d** vertices. I checked this on a computer: at n = 80,000 and d = 50, greedy returns 6,282 and n·log d/d predicts 6,259.
>
> So Shearer's theorem says exactly this:

**[WB — Board B, boxed]**

```
   No triangle-free graph is worse — as far as greedy can see —
   than a random graph of the same density.
```

> Random graphs are the *worst case*. Hold on to that, because in an hour it's going to be the thing standing between us and the end of this problem.
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
Kim 1995:   R(3,k) ≥ c·k²/log k     (with c ≈ 1/160, a small explicit constant)
```

> So the *order of magnitude* is k²/log k, settled thirty years ago. Since then, the entire game — and this paper — has been about **the constant in front**. Here is Joel Spencer, writing a survey chapter in 2011:

**[WB — or just read it, slowly]**

> *"The value of a constant c so that R(3,k) ∼ c·k²/log k remains open to this day, but this problem seems beyond our reach."*

> Hold that thought for an hour. And by our boxed formula, the constant in front is nothing but the number **A**: how small can you make the independent sets, measured in units of √(n log n)?

*(Timing check: it should be about 14:55. Take a sip of water. The next 13 minutes are the heart of the talk.)*

---

# Part 4 — 14:55 — The master picture

> Everything from 1995 to 2025 fits on this one board. I'm going to build it now and then never erase it.
>
> **The one number you choose.** Every construction we will discuss produces a graph that is *pseudorandom* — it looks locally like a random graph — of some density. So let me write the density in the units that matter:

**[WB — Board C, centre, big]**

```
        p = c · √(log n / n)     ← c is the knob:  the ONE number we choose
        d = pn = c·√(n log n)         ← average degree
```

> Why this scaling? Because it's the scale at which the problem lives: recall the balance point was d ≈ √(n log n). So *c* is a pure number — how many times denser than that reference scale your graph is — and here is the claim I want you to hold on to: **every result in this area, for sixty‑five years, is a statement about how large a c you can achieve.** One knob, and everyone has been turning it. Erdős's construction, in these units, had p = 1/√n — that's c = 1/√(log n), which tends to 0. Everybody since has been pushing *c* up.
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

> This is **Conjecture 1.1 of Campos, Jenssen, Michelen and Sahasrabudhe**, quoted as such in today's paper. Equivalently, on the upper bound side:

```
CONJECTURE:  every triangle-free graph has α ≥ (1 − o(1))·√(n log n)
             — i.e. Shearer's bound can be improved by a factor of 2.
```

> And that upper bound is not orphaned either: a conjecture of **Davies, Jenssen, Perkins and Roberts**, relating the maximum and the average size of an independent set in a triangle‑free graph, would imply it. So both halves of the conjecture have a named route; today we're doing the half that got done.

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

> In May 2025, **Campos, Jenssen, Michelen and Sahasrabudhe** disproved it. Their idea, in our language: don't start from the empty graph. **Start from a cleverly chosen "seed" graph**, then run a tailored nibble to fill in the rest. The seed was a **blow‑up of a random graph** — I'll define that in two minutes, because it's exactly the object the new paper uses. The seed supplies density c ≈ 0.408; the nibble then roughly *doubles* it and destroys the structure the blow‑up introduced.
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

## 6.1 Blow‑ups, and why they beat the deletion threshold

**[WB — Board D, drawing]** Draw a small graph *H* with 4–5 vertices; then draw each vertex as a blob containing 3 dots; join two blobs by *all* edges when the base vertices are adjacent.

> **Definition.** Take a graph *H* on *m* vertices — call them **clusters**. Replace each cluster by *s* vertices. Join two vertices of the big graph if and only if their clusters are **adjacent in H**. Inside a cluster: no edges. That's the **blow‑up** of *H* by *s*. It has n = m·s vertices.
>
> Two immediate facts. First:
>
> **A blow‑up of a triangle‑free graph is triangle‑free.**
>
> Why? A triangle in the blow‑up uses three vertices; two in the same cluster are never adjacent, so the three lie in three distinct clusters, which then form a triangle in *H*. Contradiction. Note it's an *exact* statement — no "with high probability", no error terms. That's why this object is so useful.
>
> Second: **densities are preserved.** If *H* has density *p*, the blow‑up has density ≈ p as well.
>
> Now here's the point that I think is the real idea of the paper. The paper says it in one sentence in the introduction, so let me put it the way they do. For any forbidden graph *H* there's an **edge deletion threshold** p_H: the density at which the random graph G(n,p) has about as many copies of *H* as it has edges. Below that threshold, "sample and delete" works — you lose only a o(1) fraction of your edges. Above it, you drown. For triangles:

**[WB — Board D]**

```
edge deletion threshold for triangles:   p_K3 = √(1/n)     ← Erdős's ceiling, 1961
```

> That ceiling is what has capped the random method for sixty‑five years. **A blow‑up walks straight past it.** Watch:

```
Base graph on only  m = n/s  vertices, with density p.
Its own deletion threshold is √(1/m) = √(s/n)  —  a factor √s HIGHER.

So pick  p  well below √(1/m)  but well ABOVE √(1/n),
delete the few triangles in the base, blow up by s:
  ⟹ a triangle-free graph on n vertices with density p ≫ p_K3.
```

> That's the whole trick, and it is worth saying slowly: **the density that is impossible on n vertices is easy on n/s vertices, and blowing up carries it back for free.** The base is far below *its* threshold, so it costs almost nothing to make it triangle‑free, and then blow‑up preserves triangle‑freeness exactly.
>
> There has to be a catch, and there is.

## 6.2 Why one blow‑up fails

**[WB]** On your blow‑up drawing, shade one blob, then a second non‑adjacent blob, then a third.

> A blow‑up is full of enormous independent sets. Take *any* independent set in the base *H* and blow it up: every vertex of it, in every cluster, all pairwise non‑adjacent. So

```
α(blow-up)  =  s · α(H)
```

> The blow‑up operation inflates independent sets by exactly the factor it gains you in density. Catastrophe — and you can't fix it by choosing *H* more cleverly, because the problem is *structural*. Any single blow‑up is transparent in this way.
>
> **[Pause. Ask the room:] So what would you do?**
>
> This is exactly where Campos, Jenssen, Michelen and Sahasrabudhe were last May. Their answer: use the blow‑up as a **seed** for the density, then run a tailored nibble on top to destroy the structure. In numbers:

**[WB — Board D]**

```
CJMS 2025:  m = n/log²n,  p = √(log n / 6n),  blow up by log²n
            → a triangle-free graph of density (1/√6)·√(log n/n)  = 0.408 · c-units
            then the nibble roughly DOUBLES the density and kills the
            structured independent sets
            → density (1+o(1))√(2 log n/3n) = 0.816 = √(2/3)     ⟹  1/3
```

> Look at what the nibble is being paid to do there. **Its job is to double the density.** Fifty pages of differential equations, to multiply by two.
>
> And the new paper's question is: *is there something cheaper that doubles the density?*

## 6.3 The construction

> Yes. **Do the blow‑up again.**

**[WB — Board D, clean space. Write this out in full; it is the paper.]**

```
THE CONSTRUCTION  (Hefty–Horn–King–Pfender, Section 2)

Parameters:   s = log²n,   m = n/s,   p = β·√(log n / n)  with β = ½,
              and we aim for  k = κ·√(n log n)  with κ = 1+ε.

1.  Sample TWO independent random graphs  G_R, G_B ~ G(m,p),
    on vertex sets  V_R = {r₁,…,r_m}  and  V_B = {b₁,…,b_m}.
    Call them the RED graph and the BLUE graph.

2.  Take n vertices v₁,…,v_n and choose an INJECTIVE map
        π : V(G) → V_R × V_B
    uniformly at random.  So each vertex gets a red coordinate π_R(v)
    and a blue coordinate π_B(v).

3.  Join v and w   if  π_R(v)π_R(w) ∈ G_R   (a RED edge)
                    or  π_B(v)π_B(w) ∈ G_B   (a BLUE edge).
    (If both, keep both — we work with the multigraph; α is the same.)

4.  Delete edges to kill every triangle (four explicit rules, below).
```

> **Warning, and I want to be emphatic about this:** these reds and blues have *nothing* to do with the red/blue Ramsey colouring from the first hour. That colouring is long gone; we are building one graph *G*. Red and blue here just name the two bites.

**[WB — the picture that makes it click. Draw an m × m grid of cells; scatter n dots, at most one per cell.]**

> Here's the geometry. A vertex is a **cell in an m × m grid**: its row is its red coordinate, its column is its blue coordinate. The n vertices are n cells chosen at random — and note the grid has m² ≈ n²/log⁴n cells, so it's *very* sparsely occupied. Two vertices are adjacent if their **rows** are adjacent in the red graph, **or** their **columns** are adjacent in the blue graph.
>
> Combinatorialists have a name for this: *G* is a random induced subgraph of the **co‑normal product** of G_R and G_B. And the two blow‑ups are hiding in the picture: all the vertices in one row form a **fiber** — an independent set in red of size about s = log²n — and likewise for columns. Rows are the red clusters; columns are the blue clusters; and because π is random, **the rows and columns are completely unrelated to each other.** That is the entire source of the pseudorandomness.

> **[If asked:]** the paper notes that the precise choice in step 2 barely matters — you can allow repetitions, or condition on exactly s vertices per row and column (which is literally two random balanced blow‑ups), or even use an algebraic incidence structure like a projective plane. Three different follow‑up papers make three different choices.

## 6.4 The triangles come in bunches — this is the key lemma

> Now the two things that could go wrong. First: **the union has triangles.**
>
> At density 2p = √(log n/n), a typical edge lies in about n·(2p)² = **log n** triangles. If they were spread out we'd have to delete a log n fraction of the edges — everything — and we'd be back in 1961.
>
> **They are not spread out.** Here is the structure. Take any triangle. Each edge is red or blue. Neither the red graph nor the blue graph has a triangle *by accident of density* — and in any case, count colours: two of the three edges share a colour, and they meet at a vertex. Call it the **apex**.

**[WB — Board D. Draw this carefully; it is the heart of the proof.]**

```
        w   ← apex; the two edges wu, wv have the SAME colour (say blue)
       / \
      u---v   ← the third edge
```

> Adjacency in blue depends **only on the column**. So if *w* is blue‑adjacent to both *u* and *v*, then **every vertex in w's column is blue‑adjacent to both u and v.** There are about s of them.

**[WB]** Shade *w*'s whole column and draw the fan of triangles onto the same edge *uv*.

> Triangles do not come one at a time. **They come in bunches of ≈ s, all sharing the edge uv.** So:

```
   delete the single edge uv   ⟹   kill all s triangles at once.
```

> The paper's own sentence: *"every edge removal destroys at least (1+o(1))s triangles in this process. This factor s represents exactly the gain in efficiency of this construction when compared with the typical edge deletion method."*
>
> Count the cost: about log n triangles per edge, in bunches of s = log²n, so

**[WB — box this]**

```
  fraction of edges deleted  ≈  (log n)/s  =  1/log n  =  o(1)      ✓
```

> **That's the paper.** The blow‑up structure stacks the triangles, so the 1961 deletion method works at a density it could never reach before.
>
> And there's a trade‑off in *s* that's worth stating, because it's the design decision of the whole construction: *"A larger value of s yields a larger gain, but the resulting graph is also further from a random graph."* Bigger s = cheaper deletions, but longer rows and columns, i.e. more structure for independent sets to exploit. **s = log²n** is the sweet spot.
>
> For completeness, the deletion is done by four explicit deterministic rules — you order the pairs of V_R and of V_B lexicographically, and from each triangle you delete a designated edge:

```
   (a) red–red–red     (c) red–red + blue    ← delete the blue edge
   (b) blue–blue–blue  (d) blue–blue + red   ← delete the red edge
```

> The tie‑breaking looks fussy; it's there so that the deleted set is a *deterministic function* of G_R, G_B and π, which is what lets you control it in the analysis. Note also that the paper does **not** pre‑clean the base graphs — red‑red‑red triangles do occur (rarely, since p = o(1/√m)) and are handled by rule (a) in the same sweep.

## 6.5 The independent sets

> Second thing. We need α(G) < k = (1+ε)√(n log n). Here is the one observation everything rests on:

**[WB]**

```
   I is independent in G   ⟺   π_R(I) is independent in G_R
                           AND  π_B(I) is independent in G_B
                                            (ignoring the deleted edges)
```

> — because a red edge inside *I* is exactly a red edge between two rows that *I* meets. So a k‑set has to survive **two independent random graphs at once.** And now there's a genuine tension, which is the crux of Section 4:

**[WB — Board D, side by side]**

```
   projections SMALL (I crowds into few rows/columns)
        → few pairs to avoid → MORE likely independent
        → but such sets are RARE

   projections LARGE (I spreads out over k rows and k columns)
        → k²/2 pairs to avoid in each colour → very unlikely independent
        → but such sets are COMMON
```

> Let me do the balance, because it comes out exactly. Write |π_R(I)| = x_R·k and |π_B(I)| = x_B·k. Two exponents, both in units of k·log n:

```
  how many k-sets have projections this small?
        exp( (x_R + x_B − 1)/2 · k log n )

  probability such a set is independent?
        exp( −p·(x_R² + x_B²)k²/2 )  =  exp( −(κ/4)(x_R² + x_B²)·k log n )   [β=½]
```

**[WB — put the sum up and maximise it]**

```
  g(x_R,x_B) = (x_R + x_B − 1)/2  −  (κ/4)(x_R² + x_B²)

  ∂/∂x_R = ½ − (κ/2)x_R = 0   ⟹   x_R = x_B = 1/κ
  and then      g  =  (2/κ − 1)/2 − (κ/4)(2/κ²)  =  1/κ − 1/2 − 1/(2κ)
                   =  (1 − κ) / (2κ)     ⟹  ZERO exactly at κ = 1,
                                             NEGATIVE for κ = 1+ε.  ✓
```

> Read that off: at **κ = 1** the two exponents cancel *identically*. That is why the answer is √(n log n) and not anything else, and why κ = 1+ε works and κ = 1−ε would not. The construction is sitting precisely on the first‑moment threshold of the random graph of the same density — which is exactly what the master picture demanded of it.
>
> Notice also the first case falls out for free: if x_R + x_B < 1, the *count* exponent is already negative — **there simply are no k‑sets whose projections are that small.** You don't even need them to be non‑independent.
>
> **What's actually hard?** Two things, and this is the honest content of Sections 3 and 4. *(Cut this subsection if you are past 15:50.)*
>
> * **The deleted edges.** We deleted a o(1) fraction of edges — but they're not deleted at random, they sit exactly where triangles were, and a devious independent set might hide behind them. Every deleted edge joins the two endpoints of a monochromatic path of length 2, i.e. lies **inside some neighbourhood N_v**. So the paper classifies every vertex *v* of V_R ∪ V_B by how much of *I* sits in its neighbourhood, into **huge / large / medium / small**, and shows that all but the "huge" class contribute only o(k²) unusable pairs. And the huge class is tiny: at most **2 log log n** vertices. Those few neighbourhoods are the only real correction — they're the `min(…)` terms in the paper's function f. Chernoff and McDiarmid do the work.
> * **The middle window** x_R + x_B ≈ 1, where neither the counting nor the probability wins on its own and you have to use the neighbourhood bound as well. That's the third case of Lemma 4.2, and it's where the ε's are earned.
>
> The vocabulary is borrowed, charmingly, from the process: pairs inside a common neighbourhood are called **closed**, the rest **open** — the paper has a footnote saying so.

## 6.6 Cashing it in

> Put it together. Density 2p = √(log n/n) — that's the knob at **c = 1**:

**[WB — Board C, complete the master picture]**

```
   average degree        d ≈ 2pn = √(n log n)
   independence number   α  <  (1+ε)√(n log n)     ← Theorem 1.3
                              they are EQUAL. Both forces balance.

   so A = 1  and  R(3,k) ≥ (1/2 + o(1))·k²/log k         ← Theorem 1.2
```

> Up from 1/3, up from 1/4, and — by the V‑shaped diagram — at the exact bottom of what any pseudorandom construction can give. In the authors' own words:

**[WB, or just read it out]**

> *"In our construction, independence number and average vertex degree asymptotically agree, and they are the same as a random graph of the same density. Any construction improving on the constant 1/2 would have to have lower density, and at the same time independence number smaller than the random graph of that density."*

> That's our V, stated by the people who built it. (And as a check on the picture: they note the CJMS construction has independent sets exactly **3/2 times** its average degree — which is what c = √(2/3) predicts, since 1/c ÷ c = 3/2.)
>
> Three sentences worth remembering:
>
> 1. **Blow‑ups beat the edge deletion threshold**, because the density that's impossible on n vertices is easy on n/s vertices, and blowing up carries it back exactly.
> 2. **Blow‑ups make triangles come in bunches of s**, so deletion costs a factor s less — that factor is precisely the gain over the classical method.
> 3. **Two independent blow‑ups are pseudorandom**, because each one's rows are invisible to the other's columns, and a k‑set must now survive two random graphs at once — which is exactly the first moment of a single random graph at the doubled density.

## 6.7 Two questions you should be asking

> **"Why exactly two? Why not three, or ten?"** The first moment only sees the *total* density, so extra bites buy nothing there. One blow‑up is structurally broken; two already break each other's structure. Two is the answer because two is the first number bigger than one.
>
> **"Why not push c above 1 and get a better constant?"** Because past c = 1 the *other* force takes over: neighbourhoods are independent sets of size c√(n log n) and they grow. The V goes back up. **This is a limit of the universe, not of the method** — as the authors say, to beat 1/2 you would need a construction that is *sparser* and has independent sets *smaller than a random graph of that density*. Nobody knows such an object for any problem of this type.

---

# Part 7 — 15:55 — Where we stand, and what I'd like you to take away

**[WB — Board C, final state. Point at it while you say this.]**

```
      (1/2 + o(1))·k²/log k   ≤   R(3,k)   ≤   (1 + o(1))·k²/log k
        Hefty–Horn–King–               Shearer 1983
        Pfender 2025
```

> Sixty‑five years of work on this problem, and the gap is now **a factor of two.** And we know exactly what that factor of two *is*: it is greedy versus optimal in a random graph. Shearer's theorem gives every triangle‑free graph the greedy value n·log d/d; the conjecture is that the truth is the random value, twice that. If someone proves it — the Davies–Jenssen–Perkins–Roberts conjecture is the identified route — this problem is closed, and this paper's construction is the reason we'd know the answer is sharp.
>
> **And the method has already left the building.** In the five months after it was posted, three groups used this construction for other things:
>
> * the same authors, in Section 5, get the star hypergraph Ramsey number R(S₄⁽³⁾, S_k⁽³⁾) ≥ (1/2 − o(1))k²/log k — a suggestion of Mubayi's, improving a nibble argument of Mubayi and Spanier;
> * Campos, Jenssen, Michelen and Sahasrabudhe together with Pfender got the first **polynomial** improvements over the edge deletion threshold for the cycle‑complete Ramsey numbers r(C_ℓ, K_k), for every odd ℓ ≥ 9;
> * Kühn, Sauermann, Steiner and Wigderson used it to **disprove the odd Hadwiger conjecture** — a completely different corner of graph theory, where what they need from the construction is not "no large independent set" but another pseudorandom property entirely.
>
> When a construction gets picked up three times in five months, the object was the point, not the theorem.
>
> Three closing thoughts.
>
> **First, on the shape of progress.** For thirty years the best constructions were *processes* — algorithms you run and then spend a hundred pages proving they behave. This paper is a *construction*: you write it down in five lines, and the analysis is two estimates a graduate student can check. The authors say it explicitly — no nibble, significantly less technical.
>
> And here is the payoff of that Spencer quote I left hanging. In the same 2011 chapter where he called the constant beyond our reach, he wrote:

**[WB — read it out]**

> *"Is the story of R(3,k) over? I think not. I think there is plenty of room for a consolidation of the results. My dream is a ten‑page paper which gives R(3,k) = Θ(k²/log k)."*

> This paper answers him directly. It's fifteen pages, and it does more than the dream asked for — and the authors point out that if you only wanted the *order of magnitude*, you could combine a weakened version of their construction with Shearer's one‑page upper bound and hand Spencer his ten pages exactly. When a field's best result gets simpler, something has been understood.
>
> **Second, on where the idea came from.** It came from noticing what was doing the work in someone else's proof. Campos–Jenssen–Michelen–Sahasrabudhe used a blow‑up as a seed and a nibble to double its density; the natural question was "what else could double it?" The answer was "another blow‑up — and it's free." The authors also credit an older precedent: **Alon and Rödl** stacked triangle‑free graphs on top of one another to shrink independence numbers, for multicolour Ramsey numbers R(3,…,3,k). What's new here is having to cope with the triangles that the stacking creates — and the discovery that they're cheap to remove.
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
   c small               —            (≈1/160)     Kim 1995
   c = 1/√2 ≈ 0.707      A = √2       1/4          Bohman–Keevash / FGM (~2013–20)
   c = √(2/3) ≈ 0.816    A = √(3/2)   1/3          CJMS, May 2025
   c = 1                 A = 1        1/2          Hefty–Horn–King–Pfender, Oct 2025
   upper bound                        1            Shearer 1983

CONSTRUCTION PARAMETERS  (the paper's own notation)
   s = log²n,   m = n/s,   p = β√(log n/n) with β = ½,   k = κ√(n log n) with κ = 1+ε
   G_R, G_B ~ G(m,p) independent;  π : V(G) → V_R × V_B injective, uniform
   v~w  iff  π_R(v)π_R(w) ∈ G_R  or  π_B(v)π_B(w) ∈ G_B      (co-normal product)
   final density (2+o(1))p = √(log n/n)  ⟹  c = 1;  avg degree ≈ √(n log n)
   fibers (rows/columns) have size ≈ s = log²n
   p = o(1/√m), so the base graphs are below THEIR deletion threshold
   triangles per edge ≈ log n, in bunches of ≈ s  ⟹  delete ≈ 1/log n of the edges
   CJMS for comparison: m = n/log²n, p = √(log n/6n), blow up by log²n
        → c = 1/√6 ≈ 0.408, nibble doubles it to √(2/3) ≈ 0.816

THE EXPONENT BALANCE  (skeleton of §4;  ℓ_R = x_R k, ℓ_B = x_B k)
   # k-sets with those projections ≈ exp( (x_R+x_B−1)/2 · k log n )
   P(independent)                  ≈ exp( −(κ/4)(x_R²+x_B²) · k log n )
   max of the sum = (1−κ)/(2κ)  at  x_R = x_B = 1/κ   ⟹  0 at κ=1, <0 at κ=1+ε

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
Yes. It is Conjecture 1.1 in this paper, attributed to Campos, Jenssen, Michelen and Sahasrabudhe. The missing half is the upper bound — equivalently, Shearer's bound improved by a factor of 2 — and a conjecture of Davies, Jenssen, Perkins and Roberts on the maximum versus average size of independent sets in triangle‑free graphs would imply it.

**"What about other Ramsey numbers?"**
The construction is explicitly a general tool, and it has already travelled: star hypergraph Ramsey numbers (Section 5 of the paper), cycle‑complete numbers r(C_ℓ,K_k) for odd ℓ ≥ 9 (CJMS + Pfender), and the disproof of the odd Hadwiger conjecture (Kühn–Sauermann–Steiner–Wigderson). For R(4,k) the order of magnitude was pinned down separately and recently by Mattheus and Verstraëte, with an algebraic rather than random construction.

**"Why is π injective into V_R × V_B rather than two random partitions?"**
Convenience. The paper says the variants — allow repeats, or condition on exactly s vertices per fiber (which is literally two random balanced blow‑ups) — have only marginal effects and are interchangeable; the three follow‑up papers each pick a different one. What matters is that π has expansion: the rows must be unrelated to the columns.

**"Does the red/blue here mean the Ramsey colouring?"**
No, and it's the one genuine notation trap in the talk. Say it twice.

**"How hard is the paper?"**
Fifteen pages. That's its selling point: previous constructions of this quality were 50–125 pages of differential‑equation tracking. Section 2 is the construction (2 pages), Section 3 controls the deleted edges (5 pages of Chernoff/McDiarmid bookkeeping), Section 4 is the first‑moment argument (3 pages), Section 5 is the hypergraph application.

**"Can I see the triangle‑free process?"**
Yes — `sim/triangle_free_process.c` in the repo, ~60 lines. Compile with `gcc -O2`, run `./tfp 4000`. It runs the process to maximality and prints the final density and a greedy independent set.

# Appendix C — Provenance, and the simulation

**Checked against the paper (v3, 20 Feb 2026):** the construction and all its parameters, the four deletion rules, the "bunches of s" gain, the statement of Theorems 1.2 and 1.3, Conjecture 1.1 and its attribution, the CJMS parameters and their 3/2 ratio, Kim's constant, both Spencer quotes, and the three follow‑up applications. Everything in Part 6 is the paper's.

**Mine, not the paper's** (faithful, but don't attribute):

* the "master picture" of Part 4 — the dial *c* and `A(c) = max(c, 1/c)`. The authors state its conclusion in prose (quoted in §6.6); the diagram is my packaging.
* the exponent balance in §6.5 — the paper's Lemma 4.2 with the correction terms dropped. It reproduces the sharp threshold κ = 1 exactly, which is why it's worth showing, but the corrections are what Section 3 exists to control.

**The simulation.** I ran the triangle‑free process to maximality (exact, not approximate) for n = 500…8000. Final average degree over √(n log n): 0.847, 0.843, 0.835, 0.828, 0.822 — decreasing towards 1/√2 = 0.707, with the edge‑count constant heading for 1/(2√2) = 0.354, matching Bohman–Keevash and Fiz Pontiveros–Griffiths–Morris. Greedy independent sets came out at ≈ 0.78·√(n log n), consistent with the true α = √2·√(n log n) (greedy finds about half of α in random‑like graphs). Convergence is slow — the error terms are of order log log n/log n, still ≈ 0.25 at n = 8000. Worth putting on the board in Part 5: it makes concrete that the process really does stop *below* c = 1, which is the whole reason there was room left to improve.

Code: `sim/triangle_free_process.c`; numbers: `sim/RESULTS.md`.

# Appendix D — If someone asks about Shearer's proof

You promised a sketch in Part 3. Here is what to say, and where to stop.

**The exact statement.** Shearer proves α(G) ≥ n·f(d) for triangle‑free G of average degree d, where

```
f(d) = (d·log d − d + 1) / (d − 1)²        f(0)=1, f(1)=1/2
```

and f(d) ~ log d / d. (It approaches it slowly from below — at d = 1000 the ratio is still only 0.86 — which is where the (1+o(1)) in the talk comes from.)

**Why that number — the answer to give first.** It is exactly what plain greedy achieves on a random graph of the same average degree: process vertices in a random order, take one if no neighbour is taken already. That yields ≈ n·log d/d. So the theorem reads: *no triangle-free graph is worse than a random graph of that density, as far as greedy can see.* This is the honest, illuminating answer, and it is the one that connects to the rest of the talk.

**The mechanism, if they push.** It is an induction on the number of vertices, and it is a single move, not a clever choice between moves:

1. Pick a vertex **v uniformly at random**. Put v in the independent set and delete its closed neighbourhood N[v] — that is 1 + d(v) vertices. Let G' be what's left.
2. Then α(G) ≥ 1 + α(G'), and by induction α(G') ≥ |V(G')|·f(d(G')), where d(G') is the average degree of G'.
3. Take the expectation over the random v. What has to be shown is E[1 + |V(G')|·f(d(G'))] ≥ n·f(d).
4. **This is the only place triangle‑freeness is used, and it is the whole ballgame.** N(v) is an independent set — no edges inside it — so deleting N[v] destroys every edge touching N(v) with *nothing counted twice*. In a graph with triangles, edges inside N(v) get double‑counted and you destroy strictly fewer. So triangle‑freeness makes each step maximally destructive: the leftover graph is sparser than it has any right to be, and iterating that surplus is where the log d comes from.
5. f is then chosen as the solution of the differential equation that falls out of step 3, which Shearer solves in closed form as the f above. Convexity plus Jensen handles the passage from the individual degrees to the single average degree.

**Where to stop.** That is the idea. If they want it line by line, say it is two pages (Shearer, *A note on the independence number of triangle-free graphs*, Discrete Math. 46 (1983) 83–87) and offer to send it. **Do not attempt the induction at the board** — the differential equation is not what your audience came for. There is also a modern proof, via the "occupancy method", by Davies, Jenssen, Perkins and Roberts — the same four people whose conjecture would close this problem.

**The follow-up worth being ready for:** *"if greedy gets n·log d/d, and the true independence number of a random graph is twice that, why can't we prove the factor 2?"* That is precisely the open problem — Conjecture 1.1's upper half, and the Davies–Jenssen–Perkins–Roberts route. Say so; it is a good question and the honest answer is "nobody knows."

# Appendix E — References to have on the last slide / board

* Hefty, Horn, King, Pfender, *Improving R(3,k) in just two bites*, arXiv:2510.19718 (v3, Feb 2026).
* Campos, Jenssen, Michelen, Sahasrabudhe, *A new lower bound for the Ramsey numbers R(3,k)*, arXiv:2505.13371 (2025) — the 1/3 bound and Conjecture 1.1.
* Fiz Pontiveros, Griffiths, Morris, *The triangle‑free process and the Ramsey number R(3,k)*, Memoirs AMS 263 (2020); arXiv:1302.6279.
* Bohman, Keevash, *Dynamic concentration of the triangle‑free process*, Random Structures & Algorithms (2021); Bohman, *The triangle‑free process*, Adv. Math. (2009).
* Kim, *The Ramsey number R(3,t) has order of magnitude t²/log t* (1995).
* Shearer, *A note on the independence number of triangle‑free graphs* (1983); Ajtai, Komlós, Szemerédi (1980–81).
* Erdős, *Graph theory and probability II* (1961).
* Davies, Jenssen, Perkins, Roberts — the conjecture on maximum vs average independent set size that would give the matching upper bound.
* Alon, Rödl — stacking Ramsey graphs for multicolour R(3,…,3,k); the precedent the authors credit.
* Spencer, chapter in *Ramsey Theory* (2011) — the source of both quotes.
* Kühn, Sauermann, Steiner, Wigderson — disproof of the odd Hadwiger conjecture using this construction.
* Mubayi, Spanier — the star hypergraph Ramsey bound that Section 5 improves.
* Radziszowski, *Small Ramsey Numbers*, Electron. J. Combin., Dynamic Survey DS1 — the table of exact values.
* Morris, *Some recent results in Ramsey theory*, arXiv:2601.05221 — survey, good for context.
