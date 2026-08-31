# Triangle-free process: measured final density

Built and run to **maximality** (exact, no approximation) with `sim/triangle_free_process.c`:

```
gcc -O2 -o tfp sim/triangle_free_process.c -lm
./tfp 4000
```

| n | edges m | avg degree d | max degree | d / √(n ln n) | m / (n^1.5 √(ln n)) | greedy α / √(n ln n) |
|---|---|---|---|---|---|---|
| 500  | 11 804  | 47.2  | 55  | 0.847 | 0.4235 | 0.825 |
| 1000 | 35 022  | 70.0  | 79  | 0.843 | 0.4214 | 0.830 |
| 2000 | 102 977 | 103.0 | 114 | 0.835 | 0.4176 | 0.803 |
| 4000 | 301 668 | 150.8 | 165 | 0.828 | 0.4141 | 0.796 |
| 8000 | 881 871 | 220.5 | 240 | 0.822 | 0.4111 | 0.780 |

Predicted limits (Bohman–Keevash; Fiz Pontiveros–Griffiths–Morris):

* `d / √(n ln n) → 1/√2 = 0.7071`, i.e. the process stops at density `p = (1/√2)·√(log n/n)` — **strictly less dense than the c = 1 of the new construction**;
* `m / (n^1.5 √(ln n)) → 1/(2√2) = 0.3536`;
* `α → √2·√(n log n)`, so a greedy independent set (which finds about half of α in a random-like graph) should tend to `1/√2 = 0.707` — measured 0.78 and falling.

Convergence is slow: the error terms are of order `log log n / log n`, still ≈ 0.25 at n = 8000.
