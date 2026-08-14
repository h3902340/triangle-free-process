"""
Family A: algebraic two-bites graphs A_q.

Vertex set: shears of F_q^2, n = q^2 * ell with ell = ceil((2 log q)^2).
Red / blue seeds: Sidon--Cayley graphs on the parabola and its transpose.
Cleanup: greedy monochromatic, then bichromatic minority-colour deletion.

This constructs the graphs with mixed shears A_i(x,y)=(x+s y, y+s x),
s=i+2, so vertical lines are not G_2-independent.
See explicit-family.tex and structured-cases.tex.
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

    def __init__(self, q: int, seed_only: bool = False):
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
        self._gl2 = self._gl2_list()
        self._vertices = [
            (r, i) for r in range(self.N) for i in range(self.ell)
        ]
        self._index = {v: idx for idx, v in enumerate(self._vertices)}
        self.edges: set[tuple[int, int]] = set()
        if not seed_only:
            self.edges = self._clean(self._product_edges())

    def _xy(self, r: int) -> tuple[int, int]:
        return divmod(r, self.q)

    def _pack(self, x: int, y: int) -> int:
        return (x % self.q) * self.q + (y % self.q)

    def _add(self, r: int, s: int) -> int:
        x1, y1 = self._xy(r)
        x2, y2 = self._xy(s)
        return self._pack(x1 + x2, y1 + y2)

    def _sub(self, r: int, s: int) -> int:
        x1, y1 = self._xy(r)
        x2, y2 = self._xy(s)
        return self._pack(x1 - x2, y1 - y2)

    def _gl2_list(self) -> list[tuple[int, int, int, int]]:
        """ell mixed invertible maps: prefer all entries nonzero (no axis preserved)."""
        q = self.q
        mixed: list[tuple[int, int, int, int]] = []
        rest: list[tuple[int, int, int, int]] = []
        for a in range(q):
            for b in range(q):
                for c in range(q):
                    for d in range(q):
                        if (a * d - b * c) % q == 0:
                            continue
                        mat = (a, b, c, d)
                        if min(a, b, c, d) > 0:
                            mixed.append(mat)
                        else:
                            rest.append(mat)
        mats = mixed + rest
        if len(mats) < self.ell:
            raise RuntimeError("F_q too small for ell invertible shears")
        return mats[: self.ell]

    def _shear(self, r: int, i: int) -> int:
        x, y = self._xy(r)
        a, b, c, d = self._gl2[i]
        return self._pack(a * x + b * y, c * x + d * y)

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

    def _seed_neighbours(self, r: int, transpose: bool = False) -> list[int]:
        S = self._S_B if transpose else self._S_R
        return self._neighbours_seed(r, S)

    def seed_greedy_independent_set(self, transpose: bool = False) -> list[int]:
        """Greedy independent set in G_R (or G_B if transpose)."""
        adj: dict[int, set[int]] = defaultdict(set)
        for r in range(self.N):
            for rp in self._seed_neighbours(r, transpose=transpose):
                if r < rp:
                    adj[r].add(rp)
                    adj[rp].add(r)
        order = sorted(range(self.N), key=lambda x: len(adj[x]))
        chosen: list[int] = []
        blocked: set[int] = set()
        for v in order:
            if v not in blocked:
                chosen.append(v)
                blocked.add(v)
                blocked.update(adj[v])
        return chosen

    def fibre_weights(self, points: list[int]) -> list[int]:
        weights = [0] * self.q
        for r in points:
            x, _y = self._xy(r)
            weights[x] += 1
        return weights

    def tight_4_intervals(self, points: list[int]) -> int:
        """Count x where four consecutive fibres are pairwise tight (should be 0 for q>3)."""
        B: list[set[int]] = [set() for _ in range(self.q)]
        for r in points:
            x, y = self._xy(r)
            B[x].add(y)
        count = 0
        if self.d < 3:
            return 0
        for x in range(self.q):
            sizes = [len(B[(x + i) % self.q]) for i in range(4)]
            if min(sizes) == 0:
                continue
            tight = (
                sizes[0] + sizes[1] == self.q
                and sizes[1] + sizes[2] == self.q
                and sizes[2] + sizes[3] == self.q
                and sizes[0] + sizes[3] == self.q
            )
            if tight:
                count += 1
        return count

    def vertical_line_lift_blue_edges(self, w: int = 0) -> int:
        """Blue G_2-edges inside the lift of the vertical line x=w."""
        count = 0
        points = [
            (self._pack(w, y), i)
            for y in range(self.q)
            for i in range(self.ell)
        ]
        for a in range(len(points)):
            r, i = points[a]
            br = self._shear(r, i)
            for b in range(a + 1, len(points)):
                rp, j = points[b]
                bb = self._shear(rp, j)
                if self._sub(br, bb) in self._S_B:
                    count += 1
        return count

    def xaxis_lift_blue_edges(self) -> int:
        """Blue G_2-edges inside the lift of the x-axis (should be positive)."""
        count = 0
        points = [
            (self._pack(t, 0), i)
            for t in range(self.q)
            for i in range(self.ell)
        ]
        for a in range(len(points)):
            r, i = points[a]
            br = self._shear(r, i)
            for b in range(a + 1, len(points)):
                rp, j = points[b]
                bb = self._shear(rp, j)
                if self._sub(br, bb) in self._S_B:
                    count += 1
        return count

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
    parser.add_argument(
        "--diagnose",
        action="store_true",
        help="also count blue edges on the x-axis and a vertical-line lift",
    )
    parser.add_argument(
        "--seed",
        action="store_true",
        help="only build the seeds; report greedy alpha(G_R) and fibre profile",
    )
    args = parser.parse_args()
    q = args.q if args.exact_prime else next_odd_prime(args.q)
    if args.exact_prime and (q < 3 or not is_prime(q) or q == 2):
        raise SystemExit("q must be an odd prime")
    G = FamilyA(q, seed_only=args.seed)
    if args.seed:
        ind = G.seed_greedy_independent_set()
        weights = G.fibre_weights(ind)
        print(f"q: {G.q}")
        print(f"N: {G.N}")
        print(f"d: {G.d}")
        print(f"seed_alpha_greedy: {len(ind)}")
        print(f"seed_target_q_sqrt_log_q: {G.q * math.sqrt(math.log(G.q))}")
        print(f"seed_max_fibre: {max(weights) if weights else 0}")
        print(f"seed_nonzero_fibres: {sum(1 for w in weights if w)}")
        print(f"seed_tight_4_intervals: {G.tight_4_intervals(ind)}")
        return
    for key, val in G.summary().items():
        print(f"{key}: {val}")
    if args.diagnose:
        print(f"xaxis_lift_size: {G.q * G.ell}")
        print(f"xaxis_lift_blue_edges: {G.xaxis_lift_blue_edges()}")
        print(f"vertical_line_lift_blue_edges: {G.vertical_line_lift_blue_edges()}")


if __name__ == "__main__":
    main()
