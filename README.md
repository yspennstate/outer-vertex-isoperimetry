# Outer vertex-isoperimetry of regular plane tessellations

Yitzchak Shmalo
Einstein Institute of Mathematics, The Hebrew University of Jerusalem

Manuscript, exact-arithmetic checks and a Lean 4 development for the outer
vertex-isoperimetric constant of regular plane tessellations.

The paper is [`paper/main.pdf`](paper/main.pdf); its LaTeX source is beside it
and is self-contained, with the bibliography inline.

## The result

For an infinite plane tessellation in which every vertex has degree `d`, every
face has degree `f`, and `1/d + 1/f <= 1/2`, the edge-isoperimetric constant is

    Φ(d,f) = (d-2) sqrt(1 - 4/((d-2)(f-2))),

a value due to Häggström–Jonasson–Lyons and to Higuchi–Shirai. Lyons and Peres
ask in Question 6.20 of *Probability on Trees and Networks* for the
corresponding outer vertex constant. Haslegrave and Panagiotis settled the
triangular and quadrangular cases, where it is strictly smaller. The paper
settles the rest: for `f >= 5` the two constants coincide, so

    h_V = h_E = Φ(d,f),    and in particular    h_V(H(5,5)) = sqrt(5).

The proof does not use the embedding. An infinite locally finite simple graph of
maximum degree `Δ` has `h_V = h_E` whenever `h_E >= Δ - 3`, and the additive
constant 3 is optimal uniformly in the degree. The mechanism is a two-neighbour
bootstrap: absorb any outside vertex with two neighbours inside. The edge defect
falls by at least one at every absorption, so the process stops; at the terminal
set every outer boundary vertex has exactly one neighbour inside, so the two
boundaries have equal size; and the vertex defect never rose along the way.

The paper also gives a weighted form of the transfer, quantitative bounds on the
closure of nearly minimising sets, sharp comparisons when face degrees vary, a
degree-volume version for varying vertex degrees, and finite-scale and anchored
variants.

## What is proved where

| | |
|---|---|
| Paper | the theorems, including the infinite-graph arguments |
| `formal/` | the finite statements the proofs rest on, in Lean 4 |
| `checks/` | exhaustive finite verification of the same statements |

The Lean development and the Python checker cover the same ground by different
means. Neither proves the infinite-graph theorems, and the paper does not use
either as a substitute for a proof.

## The Lean development

`formal/OuterIsoperimetry.lean` formalises the local boundary updates
(`s - 2r` for edges, at most `s - r - 1` for outer vertices), the descent that
terminates the bootstrap, the transfer inequality at a terminal set, the
threshold algebra deciding when `Φ(d,f) >= d - 3`, and the quadrangular algebra
behind the optimality of the constant 3.

Everything is stated over the integers. No square root appears: a statement
about `Φ` is a statement about the integer `(f-2)·Φ²`, and a statement about the
quadrangular constant is a statement about any `x` with `x² = (d-2)(d-4)`. That
keeps the file free of dependencies — it builds against core Lean 4 with no
Mathlib.

```sh
cd formal
lake build
lake env lean AxiomCheck.lean    # prints the axioms each theorem uses
```

Every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`;
two depend on no axioms at all. There is no `sorry` and no added axiom.

One thing the formalisation made explicit: the vertex-defect descent needs only
the bootstrap rule `r >= 2`, not the weight hypothesis `a(v) >= deg(v) - 3`. It
is the edge descent, which drives termination, that needs the weight.

## The exact checks

```sh
python -m pip install -r checks/requirements.txt
python checks/check.py
```

The run tests all 1,252 nonempty Graph Atlas graphs of order at most seven,
covering 228,422 local additions, 143,670 closure comparisons, 431,010 weighted
transfer cases, 33,474 finite-scale cases and 247,007 admissible degree/face
pairs. All arithmetic is integer or `fractions.Fraction`; there is no floating
point. `checks/check_output.json` records a run under NetworkX 3.6.1.

## Scope

The `f = 3` and `f = 4` vertex constants are Haslegrave–Panagiotis; the edge
formula is Häggström–Jonasson–Lyons and Higuchi–Shirai; the comparisons under
degree bounds are Oh's. Only the `f >= 5` vertex statement and the transfer
principle behind it are proved here. The general transitive-plane-graph clause of
Question 6.20 is not settled, and where the threshold fails, as it does for
hyperbolic quadrangulations, a different argument is needed.

The manuscript has not had independent human peer review.

## License

MIT, see [LICENSE](LICENSE).
