#!/usr/bin/env python3
"""Leftover degree as a function of fugacity λ, and circulant ratio scan.

If leftover degree dropped to O(1) for some λ with E|I| already (1+δ) times
the λ=1 mean, that would be a leading-constant route. This script checks
whether that happens on triangle-free-process graphs and lists every
triangle-free inverse-closed circulant on n≤31 with its α/avg ratio.
"""
import random
import time
from itertools import combinations


def triangle_free_process(n, seed=0):
    rng = random.Random(seed)
    pairs = [(i, j) for i in range(n) for j in range(i + 1, n)]
    rng.shuffle(pairs)
    adj_set = [set() for _ in range(n)]
    for u, v in pairs:
        if adj_set[u] & adj_set[v]:
            continue
        adj_set[u].add(v)
        adj_set[v].add(u)
    return [sorted(s) for s in adj_set]


def glauber_lambda(adj, lam, steps, burn, seed=0, record_every=40):
    """λ-Glauber: add with lam/(1+lam) when free, remove with 1/(1+lam) when occupied."""
    rng = random.Random(seed)
    n = len(adj)
    nbr = [set(a) for a in adj]
    occupied = [False] * n
    occ_count = [0] * n
    size = 0
    p_add = lam / (1.0 + lam)
    p_rem = 1.0 / (1.0 + lam)
    samples = 0
    sum_size = 0.0
    sum_f = 0.0
    sum_e_f = 0.0
    sum_caro = 0.0
    # greedy start then strip
    order = list(range(n))
    rng.shuffle(order)
    for v in order:
        if occ_count[v] == 0:
            occupied[v] = True
            size += 1
            for u in nbr[v]:
                occ_count[u] += 1
    for _ in range(n):
        v = rng.randrange(n)
        if occupied[v]:
            occupied[v] = False
            size -= 1
            for u in nbr[v]:
                occ_count[u] -= 1

    for t in range(steps):
        v = rng.randrange(n)
        if occupied[v]:
            if rng.random() < p_rem:
                occupied[v] = False
                size -= 1
                for u in nbr[v]:
                    occ_count[u] -= 1
        elif occ_count[v] == 0:
            if rng.random() < p_add:
                occupied[v] = True
                size += 1
                for u in nbr[v]:
                    occ_count[u] += 1
        if t >= burn and (t - burn) % record_every == 0:
            f = [x for x in range(n) if (not occupied[x]) and occ_count[x] == 0]
            fset = set(f)
            e_f = 0
            caro = 0.0
            for x in f:
                df = sum(1 for y in nbr[x] if y in fset)
                e_f += df
                caro += 1.0 / (df + 1)
            samples += 1
            sum_size += size
            sum_f += len(f)
            sum_e_f += e_f // 2
            sum_caro += caro
    avg_i = sum_size / samples
    avg_f = sum_f / samples
    d_f = (2 * sum_e_f / samples) / avg_f if avg_f else 0
    return {
        "lam": lam,
        "E|I|": avg_i,
        "E|F|": avg_f,
        "d_F": d_f,
        "Caro": sum_caro / samples,
        "E|I|+Caro": avg_i + sum_caro / samples,
    }


def is_triangle_free_circulant(n, dists):
    S = set()
    for d in dists:
        S.add(d % n)
        S.add((-d) % n)
    S.discard(0)
    for a in S:
        for b in S:
            if (a + b) % n in S:
                return False
    return True


def circulant_mitm_stats(n, distances):
    """Independence stats via MITM; copied from circulant_mitm.py."""
    adj = [0] * n
    S = set()
    for d in distances:
        S.add(d % n)
        S.add((-d) % n)
    S.discard(0)
    for i in range(n):
        for d in S:
            adj[i] |= 1 << ((i + d) % n)

    def isets_on(verts):
        m = len(verts)
        out = []
        for local in range(1 << m):
            gmask = 0
            ok = True
            sz = 0
            for i in range(m):
                if local & (1 << i):
                    v = verts[i]
                    if adj[v] & gmask:
                        ok = False
                        break
                    gmask |= 1 << v
                    sz += 1
            if ok:
                out.append((local, sz, gmask))
        return out

    mid = n // 2
    left = list(range(mid))
    right = list(range(mid, n))
    LIS = isets_on(left)
    RIS = isets_on(right)
    r_index = {v: j for j, v in enumerate(right)}
    mR = len(right)
    count = [0] * (1 << mR)
    ssum = [0] * (1 << mR)
    maxsz = [0] * (1 << mR)
    for local, sz, _ in RIS:
        count[local] += 1
        ssum[local] += sz
        if sz > maxsz[local]:
            maxsz[local] = sz
    for i in range(mR):
        bit = 1 << i
        for u in range(1 << mR):
            if u & bit:
                count[u] += count[u ^ bit]
                ssum[u] += ssum[u ^ bit]
                if maxsz[u ^ bit] > maxsz[u]:
                    maxsz[u] = maxsz[u ^ bit]
    z = 0
    size_sum = 0
    alpha = 0
    for local, szL, gL in LIS:
        forbidden = 0
        m = gL
        while m:
            v = (m & -m).bit_length() - 1
            rbits = 0
            nb = adj[v]
            while nb:
                w = (nb & -nb).bit_length() - 1
                if w in r_index:
                    rbits |= 1 << r_index[w]
                nb &= nb - 1
            forbidden |= rbits
            m &= m - 1
        allowed = ((1 << mR) - 1) ^ forbidden
        z += count[allowed]
        size_sum += szL * count[allowed] + ssum[allowed]
        alpha = max(alpha, szL + maxsz[allowed])
    avg = size_sum / z
    return alpha, avg, alpha / avg, z, 2 * len(S)


def scan_circulants(n_max=29):
    """All inverse-closed triangle-free circulants, n≤n_max (odd n: no 2-torsion)."""
    rows = []
    worst = (10.0, None)
    for n in range(5, n_max + 1):
        half = n // 2
        dists = list(range(1, half + (n % 2 == 0)))  # include n/2 if even
        if n % 2 == 0:
            # n/2 is its own inverse; include as a 0-1 choice separately
            core = list(range(1, half))
        else:
            core = list(range(1, half + 1))
        found = 0
        local_worst = (10.0, None)
        max_k = min(6, len(core))
        for k in range(0, max_k + 1):
            for subset in combinations(core, k):
                s = list(subset)
                if n % 2 == 0:
                    # try without and with the diametral chord
                    variants = [s, s + [half]]
                else:
                    variants = [s]
                for dists_choice in variants:
                    if not is_triangle_free_circulant(n, dists_choice):
                        continue
                    if not dists_choice:
                        continue
                    alpha, avg, ratio, z, deg = circulant_mitm_stats(n, dists_choice)
                    found += 1
                    rec = (n, deg, alpha, avg, ratio, tuple(sorted(dists_choice)), z)
                    rows.append(rec)
                    if ratio < local_worst[0]:
                        local_worst = (ratio, rec)
                    if ratio < worst[0]:
                        worst = (ratio, rec)
        print(
            f"n={n:2d} triangle-free circulants={found:4d} "
            f"worst ratio={local_worst[0] if found else None} {local_worst[1]}",
            flush=True,
        )
    return worst, rows


def main():
    print("=== leftover vs λ on a triangle-free-process graph n=200 ===", flush=True)
    adj = triangle_free_process(200, seed=6)
    d = sum(len(a) for a in adj) / 200
    print(f"mean degree {d:.2f}")
    for lam in [0.25, 0.5, 1.0, 2.0, 4.0, 8.0, 16.0, 32.0]:
        t0 = time.time()
        st = glauber_lambda(adj, lam, steps=250_000, burn=40_000, seed=3)
        print(
            f"  λ={lam:5.2f} E|I|={st['E|I|']:7.2f} E|F|={st['E|F|']:7.2f} "
            f"d_F={st['d_F']:6.3f} E|I|+Caro={st['E|I|+Caro']:7.2f} "
            f"({time.time()-t0:.1f}s)",
            flush=True,
        )

    print("\n=== triangle-free circulant ratio scan ===", flush=True)
    t0 = time.time()
    worst, rows = scan_circulants(29)
    print(f"global worst: {worst} ({time.time()-t0:.1f}s)")
    rows.sort(key=lambda r: r[4])
    print("ten smallest ratios:")
    for rec in rows[:10]:
        print(f"  n={rec[0]} d={rec[1]} α={rec[2]} avg={rec[3]:.4f} ratio={rec[4]:.6f} S={rec[5]} z={rec[6]}")


if __name__ == "__main__":
    main()
