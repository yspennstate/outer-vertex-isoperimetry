#!/usr/bin/env python3
"""Exact finite checks for the vertex-isoperimetry manuscript.

Python 3.10+, NetworkX. No floating-point comparison and no randomness.
These checks do not prove an infinite-graph theorem, check publication priority,
or constitute a formal verification of the proofs.
"""
from __future__ import annotations

import argparse
from fractions import Fraction as F
import json
from pathlib import Path
import sys


def arrays(adj: list[int]) -> tuple[list[int], list[int], list[int]]:
    n = len(adj)
    lim = 1 << n
    size, edges, vertex = [0]*lim, [0]*lim, [0]*lim
    for s in range(1, lim):
        size[s] = s.bit_count()
        neighborhood, boundary = 0, 0
        for v, mask in enumerate(adj):
            if s >> v & 1:
                neighborhood |= mask
                boundary += (mask & ~s).bit_count()
        edges[s] = boundary
        vertex[s] = (neighborhood & ~s).bit_count()
    return size, edges, vertex


def closure(adj: list[int], s: int, reverse: bool = False) -> int:
    order = range(len(adj)-1, -1, -1) if reverse else range(len(adj))
    while True:
        for v in order:
            if not s >> v & 1 and (adj[v] & s).bit_count() >= 2:
                s |= 1 << v
                break
        else:
            return s


def run(max_order: int) -> dict:
    try:
        import networkx as nx
    except ImportError as exc:
        raise RuntimeError('Install NetworkX: python -m pip install networkx') from exc
    count = dict(graphs=0, local_additions=0, closure_order_checks=0,
                 terminal_checks=0, weighted_transfer_cases=0,
                 regular_tree_completion_cases=0, finite_scale_cases=0,
                 degree_face_pairs=0, sharpness_parameter_checks=0)
    for graph in nx.graph_atlas_g():
        n = graph.number_of_nodes()
        if not 1 <= n <= max_order:
            continue
        assert set(graph) == set(range(n))
        adj = [sum(1 << u for u in graph[v]) for v in range(n)]
        deg = [mask.bit_count() for mask in adj]
        delta = max(deg, default=0)
        size, edge, vertex = arrays(adj)
        full = (1 << n)-1
        closed = [0]*(1 << n)
        count['graphs'] += 1
        for s in range(1, 1 << n):
            c = closure(adj, s)
            assert c == closure(adj, s, reverse=True)
            closed[s] = c
            count['closure_order_checks'] += 1
            assert edge[c] == vertex[c]
            count['terminal_checks'] += 1
            for v in range(n):
                if s >> v & 1:
                    continue
                r = (adj[v] & s).bit_count()
                if r < 2:
                    continue
                t = s | (1 << v)
                assert edge[t]-edge[s] == deg[v]-2*r
                assert vertex[t]-vertex[s] <= deg[v]-r-1
                count['local_additions'] += 1

        # Three vertex-dependent weights. beta is the exact all-set edge floor.
        # All computations are doubled to make the half-integer weights integral.
        for pattern in range(3):
            gamma2 = [0 if pattern == 0 else ((v+pattern) % 3) for v in range(n)]
            a2 = [2*(deg[v]-3)+gamma2[v] for v in range(n)]
            sums = [0]*(1 << n)
            for s in range(1, 1 << n):
                bit = s & -s
                sums[s] = sums[s ^ bit] + a2[bit.bit_length()-1]
            beta2 = min(2*edge[s]-sums[s] for s in range(1, 1 << n))
            for s in range(1, 1 << n):
                c = closed[s]
                additions = size[c]-size[s]
                edef2 = 2*edge[s]-sums[s]-beta2
                vdef2 = 2*vertex[s]-sums[s]-beta2
                assert edef2 >= 2*additions
                assert vdef2 >= 0
                added = c & ~s
                gamma_added2 = sum(gamma2[v] for v in range(n) if added >> v & 1)
                terminal2 = 2*edge[c]-sums[c]-beta2
                assert vdef2 >= terminal2 + gamma_added2 >= gamma_added2
                count['weighted_transfer_cases'] += 1

        # Complete every core vertex to degree D using disjoint infinite trees.
        # Its exact edge constant is min(D-2, D-max_average_degree(core)).
        # No tree vertices enter the two-neighbor closure of a core-only seed.
        internal2 = [sum(deg[v] for v in range(n) if s >> v & 1)-edge[s]
                     for s in range(1 << n)]
        mad = max(F(internal2[s], size[s]) for s in range(1, 1 << n))
        for D in range(max(3, delta), max(3, delta)+3):
            h = F(D)-max(F(2), mad)
            if h < D-3:
                continue
            num, den = h.numerator, h.denominator
            gamma_num = num-(D-3)*den
            for s in range(1, 1 << n):
                c = closed[s]
                m = size[c]-size[s]
                # Distinct attached tree roots count once each in both boundaries.
                stubs_s = sum(D-deg[v] for v in range(n) if s >> v & 1)
                stubs_c = sum(D-deg[v] for v in range(n) if c >> v & 1)
                e = edge[s]+stubs_s
                b = vertex[s]+stubs_s
                ec = edge[c]+stubs_c
                bc = vertex[c]+stubs_c
                DE, DV = den*e-num*size[s], den*b-num*size[s]
                DEC = den*ec-num*size[c]
                assert ec == bc and DEC >= 0
                assert 0 <= DV <= DE
                assert m*(gamma_num+den) <= DE
                assert DV >= DEC+gamma_num*m
                bad = sum(not (s >> v & 1) and (adj[v] & s).bit_count() >= 2 for v in range(n))
                assert bad <= m and e-b <= (D-1)*m
                if gamma_num > 0:
                    assert gamma_num*m <= DV
                    assert DE*gamma_num <= (num+2*den)*DV
                count['regular_tree_completion_cases'] += 1

        # Exact finite-scale edge floor for every possible size cutoff.
        for M in range(1, n+1):
            h = min(F(edge[s], size[s]) for s in range(1, 1 << n) if size[s] <= M)
            if h < delta-3:
                continue
            num, den = h.numerator, h.denominator
            cnum = num-(delta-4)*den
            assert cnum > 0
            for s in range(1, 1 << n):
                if size[s] > M:
                    continue
                DE = den*edge[s]-num*size[s]
                lhs = size[s]*cnum+DE
                if lhs >= M*cnum:
                    continue
                c = closed[s]
                assert size[c]*cnum <= lhs
                assert den*vertex[s] >= num*size[s]
                count['finite_scale_cases'] += 1

    # Exact rational threshold and neighboring obstruction.
    for d in range(3, 501):
        for f in range(5, 501):
            if (d-2)*(f-2) < 4:
                continue
            squared_num = (d-2)*((d-2)*(f-2)-4)
            squared_den = f-2
            gap_num = squared_num-(d-3)**2*squared_den
            assert gap_num >= 0
            assert (gap_num == 0) == ((d, f) == (3, 6))
            count['degree_face_pairs'] += 1
        assert (d-2)*(d-4)-(d-3)**2 == -1
    assert F(8,15) > F(64,121)
    assert F(5,1) == F((5-2)*((5-2)*(5-2)-4), 5-2)
    for k in (1,2,3,5,10,100,1000,10000):
        C, d = F(3)+F(1,k), k+4
        assert (d-2)*(d-4) > (F(d)-C)**2
        count['sharpness_parameter_checks'] += 1
    return {
        'status': 'ALL_EXACT_CHECKS_PASS',
        'max_atlas_order': max_order,
        'counts': count,
        'arithmetic': 'integer and fractions.Fraction; no floating point',
        'scope': 'Finite checks of identities and consequences; not a proof of infinite theorems, not a novelty check, not formal proof-assistant verification.'
    }


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--max-order', type=int, default=7, choices=range(1,8))
    parser.add_argument('--output', type=Path)
    args = parser.parse_args()
    try:
        result = run(args.max_order)
        text = json.dumps(result, indent=2)+'\n'
        if args.output:
            args.output.write_text(text, encoding='utf-8')
        print(text, end='')
    except (AssertionError, OSError, RuntimeError) as exc:
        print(f'CHECK FAILED: {exc}', file=sys.stderr)
        raise

if __name__ == '__main__':
    main()
