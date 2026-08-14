"""
Family A: algebraic two-bites graphs A_q.

Vertex set: shears of F_q^2, n = q^2 * ell with ell = ceil((2 log q)^2).
Red / blue seeds: Sidon--Cayley graphs on the parabola and its transpose.
Cleanup: greedy monochromatic, then bichromatic minority-colour deletion.

This constructs the graphs. The SOTA independence-number bound is conjectural;
see explicit-family.tex.
"""

from __future__ import annotations

import argparse
import math
from collections import defaultdict


def is_prime(q: int) -> bool:
    if q < 2:
        return False
    if q % 2 == 0:
        return q == 2
    d = 3
    while d * d <= q:
        if q % d == 0:
            return False
        d += 2
    return True


def next_odd_prime(q: int) -> int:
    if q <= 3:
        return 3
    if q % 2 == 0:
        q += 1
    while not is_prime(q):
        q += 2
    return q


class FamilyA:
    """Explicit two-bites graph A_q on n = q^2 * ell vertices."""

    def __init__(self, q: int):
        if q < 3 or not is_prime(q) or q == 2:
            raise ValueError("q must be an odd prime")
        self.q = q
        self.N = q * q
        self.ell = max(1, math.ceil((2.0 * math.log(q)) ** 2))
        self.n = self.N * self.ell
        self.d = max(1, int(q / (2.0 * math.sqrt(math.log(q)))))
        self.d = min(self.d, q - 1)

        self._S_R = self._connection_parabola(transpose=False)
        self._S_B = self._connection_parabola(transpose=True)
        self._vertices = [
            (r, i) for r in range(self.N) for i in range(self.ell)
        ]
        self._index = {v: idx for idx, v in enumerate(self._vertices)}
        self.edges = self._clean(self._product_edges())

    def _xy(self, r: int) -> tuple[int, int]:
        return divmod(r, self.q)

    def _pack(self, x: int, y: int) -> int:
        return (x % self.q) * self.q + (y % self.q)

    def _add(self, r: int, s: int) -> int:
        x1, y1 = self._xy(r)
        x2, y2 = self._xy(s)
        return self._pack(x1 + x2, y1 + y2)

    def _shear(self, r: int, i: int) -> int:
        x, y = self._xy(r)
        return self._pack(x, y + i * x)

    def _connection_parabola(self, transpose: bool) -> set[int]:
        S: set[int] = set()
        for t in range(1, self.d + 1):
            if transpose:
                s = self._pack(t * t, t)
            else:
                s = self._pack(t, t * t)
            S.add(s)
            x, y = self._xy(s)
            S.add(self._pack(-x, -y))
        S.discard(0)
        return S

    def _neighbours_seed(self, r: int, S: set[int]) -> list[int]:
        return [self._add(r, s) for s in S]

    def _product_edges(self) -> tuple[set[tuple[int, int]], set[tuple[int, int]]]:
        red: set[tuple[int, int]] = set()
        blue: set[tuple[int, int]] = set()
        lifts = [[] for _ in range(self.N)]
        for r in range(self.N):
            for i in range(self.ell):
                lifts[r].append((r, i))

        blue_lifts: dict[int, list[tuple[int, int]]] = defaultdict(list)
        for r in range(self.N):
            for i in range(self.ell):
                blue_lifts[self._shear(r, i)].append((r, i))

        for r in range(self.N):
            for rp in self._neighbours_seed(r, self._S_R):
                if r >= rp:
                    continue
                for u in lifts[r]:
                    for v in lifts[rp]:
                        a, b = self._index[u], self._index[v]
                        red.add((a, b) if a < b else (b, a))

        for b in range(self.N):
            for bp in self._neighbours_seed(b, self._S_B):
                if b >= bp:
                    continue
                for u in blue_lifts[b]:
                    for v in blue_lifts[bp]:
                        a, c = self._index[u], self._index[v]
                        blue.add((a, c) if a < c else (c, a))

        return red, blue

    def _clean(
        self, coloured: tuple[set[tuple[int, int]], set[tuple[int, int]]]
    ) -> set[tuple[int, int]]:
        red, blue = coloured
        kept_red = self._greedy_triangle_free(red)
        kept_blue = self._greedy_triangle_free(blue)
        kept = set(kept_red) | set(kept_blue)

        adj: dict[int, set[int]] = defaultdict(set)
        colour = {}
        for e in kept_red:
            u, v = e
            adj[u].add(v)
            adj[v].add(u)
            colour[e] = "red"
        for e in kept_blue:
            u, v = e
            adj[u].add(v)
            adj[v].add(u)
            colour[e] = "blue"

        def edge(u: int, v: int) -> tuple[int, int]:
            return (u, v) if u < v else (v, u)

        # Bichromatic triangles: delete the minority colour.
        to_delete: set[tuple[int, int]] = set()
        for u, v in list(kept):
            common = adj[u] & adj[v]
            for w in common:
                e1, e2, e3 = edge(u, v), edge(v, w), edge(u, w)
                cols = [colour[e1], colour[e2], colour[e3]]
                if cols.count("red") == 1:
                    for e in (e1, e2, e3):
                        if colour[e] == "red":
                            to_delete.add(e)
                elif cols.count("blue") == 1:
                    for e in (e1, e2, e3):
                        if colour[e] == "blue":
                            to_delete.add(e)
        kept -= to_delete
        return kept

    def _greedy_triangle_free(
        self, edges: set[tuple[int, int]]
    ) -> list[tuple[int, int]]:
        adj: dict[int, set[int]] = defaultdict(set)
        kept: list[tuple[int, int]] = []
        for u, v in sorted(edges):
            if adj[u].isdisjoint(adj[v]):
                kept.append((u, v))
                adj[u].add(v)
                adj[v].add(u)
        return kept

    def is_triangle_free(self) -> bool:
        adj: dict[int, set[int]] = defaultdict(set)
        for u, v in self.edges:
            adj[u].add(v)
            adj[v].add(u)
        for u, v in self.edges:
            if adj[u] & adj[v]:
                return False
        return True

    def greedy_independent_set(self) -> list[int]:
        adj: dict[int, set[int]] = defaultdict(set)
        for u, v in self.edges:
            adj[u].add(v)
            adj[v].add(u)
        order = sorted(range(self.n), key=lambda x: len(adj[x]))
        chosen: list[int] = []
        blocked: set[int] = set()
        for v in order:
            if v not in blocked:
                chosen.append(v)
                blocked.add(v)
                blocked.update(adj[v])
        return chosen

    def summary(self) -> dict[str, float]:
        deg = [0] * self.n
        for u, v in self.edges:
            deg[u] += 1
            deg[v] += 1
        alpha_lb = len(self.greedy_independent_set())
        target = math.sqrt(self.n * math.log(self.n))
        return {
            "q": self.q,
            "n": self.n,
            "ell": self.ell,
            "d": self.d,
            "edges": len(self.edges),
            "avg_degree": (2.0 * len(self.edges) / self.n) if self.n else 0.0,
            "max_degree": max(deg) if deg else 0,
            "alpha_greedy_lb": alpha_lb,
            "sota_target_sqrt_n_log_n": target,
            "triangle_free": float(self.is_triangle_free()),
        }


def main() -> None:
    parser = argparse.ArgumentParser(description="Build algebraic two-bites graph A_q")
    parser.add_argument("q", type=int, help="odd prime (or next odd prime is used)")
    parser.add_argument(
        "--exact-prime",
        action="store_true",
        help="fail if q is not an odd prime instead of rounding up",
    )
    args = parser.parse_args()
    q = args.q if args.exact_prime else next_odd_prime(args.q)
    if args.exact_prime and (q < 3 or not is_prime(q) or q == 2):
        raise SystemExit("q must be an odd prime")
    G = FamilyA(q)
    for key, val in G.summary().items():
        print(f"{key}: {val}")


if __name__ == "__main__":
    main()
