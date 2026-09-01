#!/usr/bin/env python3
"""Verify α/avg ≥ 4/3 for every triangle-free graph on n ≤ 7."""


def stats(n, adj):
    z = 0
    ssum = 0
    alpha = 0
    for mask in range(1 << n):
        ok = True
        m = mask
        while m:
            v = (m & -m).bit_length() - 1
            if adj[v] & mask:
                ok = False
                break
            m &= m - 1
        if ok:
            sz = mask.bit_count()
            z += 1
            ssum += sz
            if sz > alpha:
                alpha = sz
    return alpha, ssum / z, alpha * z / ssum, z


def triangle_free(n, adj):
    for u in range(n):
        nb = adj[u]
        vbits = nb
        while vbits:
            v = (vbits & -vbits).bit_length() - 1
            if v > u and (adj[v] & nb):
                return False
            vbits &= vbits - 1
    return True


def main():
    worst = 10.0
    worst_ex = None
    count_tf = 0
    for n in range(1, 8):
        m = n * (n - 1) // 2
        edges = [(i, j) for i in range(n) for j in range(i + 1, n)]
        seen = 0
        for bits in range(1 << m):
            adj = [0] * n
            for e, (i, j) in enumerate(edges):
                if bits & (1 << e):
                    adj[i] |= 1 << j
                    adj[j] |= 1 << i
            if not triangle_free(n, adj):
                continue
            count_tf += 1
            a, avg, r, z = stats(n, adj)
            if r < worst:
                worst = r
                worst_ex = (n, bits, a, avg, r, z)
        print(f"n={n} done, triangle-free so far {count_tf}, worst {worst:.6f}")
    print("WORST", worst_ex)
    print("4/3", 4 / 3)
    print("holds for n<=7:", worst >= 4 / 3 - 1e-12)


if __name__ == "__main__":
    main()
