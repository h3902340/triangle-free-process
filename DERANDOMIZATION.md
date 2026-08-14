# Derandomizing the SOTA lower bound

Target: Hefty–Horn–King–Pfender (arXiv:2510.19718)
\[
R(3,k)\ge\Bigl(\tfrac12+o(1)\Bigr)\frac{k^2}{\log k}.
\]

---

## Did we get a concrete family?

**Yes, two of them.** Only one has a complete SOTA proof.

| Family | Graph | SOTA $\alpha$ bound | Efficient? |
|--------|--------|----------------------|------------|
| **L** (lex-first good config) | $L_n=\mathrm{Clean}(\omega_n^\star)$ | **Theorem** | No ($\exp(\Theta(n^2/\log^4 n))$ search) |
| **A** (algebraic two bites) | $A_q$ on $n=q^2\lceil(2\log q)^2\rceil$ vertices | **Conjecture** | Yes, $\mathrm{poly}(n)$ |

Best *proven + polynomial-time* explicit bound is still Alon's $\Omega(k^{3/2})$.

---

## Family L — named graphs, SOTA proved

Order every HHKP configuration lexicographically. Let $\omega_n^\star$ be the first one whose cleaned graph has $\alpha<(1+\varepsilon)\sqrt{n\log n}$. Set $L_n=\mathrm{Clean}(\omega_n^\star)$.

The counting proof shows a good configuration exists, so $L_n$ is well-defined and meets SOTA. This is a concrete family, not a poly-time construction.

---

## Family A — explicit algebraic graphs

For each odd prime $q$:

1. **Seeds.** Cayley graphs on $\mathbb{F}_q^2$ with Sidon connection sets
   - red: truncated parabola $\{(t,t^2):1\le t\le d\}\cup\text{negatives}$
   - blue: transpose $\{(t^2,t):1\le t\le d\}\cup\text{negatives}$
   - $d=\lfloor q/(2\sqrt{\log q})\rfloor$
2. **Sample.** Vertex set = $\ell$ horizontal shears $A_i(x,y)=(x,y+ix)$, $\ell=\lceil(2\log q)^2\rceil$.
3. **Cleanup.** Same deterministic rule as HHKP.

**Proved:** triangle-free, degree $O(\sqrt{n\log n})$, poly-time; $G_2$-independent sets are lifts of seed-independent sets; heavy/vertical seed independent sets have size $O(q\sqrt{\log q})$; open edges survive cleanup. See `family-a-independence.tex`.

**Not proved:** $\alpha(G_R)=O(q\sqrt{\log q})$ in full generality, and that every set of size $C\sqrt{n\log n}$ spans an *open* $G_2$-edge.

Implementation: `explicit_family.py`

```bash
python3 explicit_family.py 7 --diagnose
```

On $q=7$ the second bite already cuts the $x$-axis lift (527 blue edges) and the greedy independent set ($63$) sits below the SOTA target $\sqrt{n\log n}\approx 72$. Small $q$ is not a proof; the trend is the expected one.

```bash
python3 explicit_family.py 3
python3 explicit_family.py 5
```

Small $q$ is too sparse ($d=1$) and greedy independent sets are larger than the SOTA target — as expected. The scaling is asymptotic.

---

## Files

| File | Role |
|------|------|
| `explicit-family.tex` | Definitions, proofs, conjecture |
| `explicit_family.py` | Constructor for $A_q$ |
| `sota-combinatorial.tex` | Counting existence proof used by Family L |
