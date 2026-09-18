/-
Machine-checked arithmetic backbone of

    Outer vertex-isoperimetry of regular plane tessellations
    Yitzchak Shmalo

The paper proves h_V = h_E for an infinite locally finite simple graph whose
edge-isoperimetric constant satisfies h_E >= Δ - 3, and derives the value
Φ(d,f) = (d-2) sqrt(1 - 4/((d-2)(f-2))) for every (d,f)-regular plane
tessellation with f >= 5.

Two ingredients carry that proof, and both are finite statements that a proof
assistant can check.  The first is the pair of local boundary updates driving
the two-neighbour bootstrap, together with the descent that makes it terminate.
The second is the algebra deciding when the threshold h_E >= Δ - 3 holds, and
the algebra behind the optimality of the constant 3.

Everything below is stated over the integers.  The square root never appears:
each statement about Φ is a statement about (f-2)·Φ², which is an integer, and
each statement about the quadrangular constant e_d is a statement about any x
with x² = (d-2)(d-4).  This keeps the file free of any dependency: it compiles
against core Lean 4 alone, with no Mathlib.

What is NOT formalised here: the passage from these finite facts to the
infinite-graph theorems.  The bootstrap's termination is proved as a descent on
integers; that a terminal set exists, is the two-neighbour closure, and has
equal edge and outer vertex boundaries is graph-theoretic content that lives in
the paper.
-/

namespace OuterIsoperimetry

/-! ## 1. The local boundary updates

At an addition the bootstrap takes a vertex `v` outside the current set with
`s = deg v` and `r = |N(v) ∩ K| ≥ 2` neighbours inside.  Exactly `r` boundary
edges become internal and `s - r` new ones appear, so the edge boundary changes
by `s - 2r`.  The vertex `v` leaves the outer boundary and at most `s - r` new
vertices enter it, so the outer vertex boundary changes by at most `s - r - 1`.
-/

/-- Change in the edge boundary when a vertex of degree `s` with `r` neighbours
inside is absorbed.  Equation (2.5) of the paper. -/
def edgeDelta (s r : Int) : Int := s - 2 * r

/-- Upper bound on the change in the outer vertex boundary at the same step.
Equation (2.6) of the paper. -/
def vertexDeltaBound (s r : Int) : Int := s - r - 1

/-- The local surplus `γ(v) = a(v) - deg(v) + 3`, nonnegative exactly when the
weight hypothesis (2.4) holds at `v`. -/
def surplus (a s : Int) : Int := a - s + 3

/-- **Edge defect descent.**  Under the weight hypothesis `a ≥ s - 3` and the
bootstrap rule `r ≥ 2`, absorbing a vertex drops the edge defect by at least
one.  This is the estimate that makes the process terminate. -/
theorem edge_defect_drop {a s r : Int} (hw : s - 3 ≤ a) (hr : 2 ≤ r) :
    edgeDelta s r - a ≤ -1 := by
  unfold edgeDelta
  omega

/-- The same descent in the form used in the paper: the drop is
`-γ(v) - (2r - 3)`. -/
theorem edge_defect_drop_eq {a s r : Int} :
    edgeDelta s r - a = -surplus a s - (2 * r - 3) := by
  unfold edgeDelta surplus
  omega

/-- **Vertex defect descent.**  The outer vertex defect drops by at least the
local surplus.  Note the weight hypothesis `a ≥ s - 3` is not needed here: the
bootstrap rule `r ≥ 2` alone gives this, which is why the surplus appears on the
right.  The weight hypothesis is what the *edge* descent needs. -/
theorem vertex_defect_drop {a s r : Int} (hr : 2 ≤ r) :
    vertexDeltaBound s r - a ≤ -surplus a s := by
  unfold vertexDeltaBound surplus
  omega

/-- The same, in the paper's form `-γ(v) - (r - 2)`. -/
theorem vertex_defect_drop_eq {a s r : Int} :
    vertexDeltaBound s r - a = -surplus a s - (r - 2) := by
  unfold vertexDeltaBound surplus
  omega

/-- With a maximum degree `Δ` and the uniform weight `a = h`, the edge defect
drops by at least `γ + 1` where `γ = h - Δ + 3`.  This is the constant in the
closure-size bound (3.2). -/
theorem edge_defect_drop_uniform {h Δ s r : Int}
    (hs : s ≤ Δ) (hr : 2 ≤ r) :
    edgeDelta s r - h ≤ -((h - Δ + 3) + 1) := by
  unfold edgeDelta
  omega

/-- And the vertex defect drops by at least `γ`, the constant in (3.3). -/
theorem vertex_defect_drop_uniform {h Δ s r : Int}
    (hs : s ≤ Δ) (hr : 2 ≤ r) :
    vertexDeltaBound s r - h ≤ -(h - Δ + 3) := by
  unfold vertexDeltaBound
  omega

/-! ## 2. Termination of the bootstrap

The edge defect is nonnegative on every finite nonempty set and drops by at
least one per addition, so the number of additions is bounded by its initial
value.  That is the whole termination argument, and it is a descent on `Int`.
-/

/-- A sequence dropping by at least one each step falls at least linearly. -/
theorem descent_linear (E : Nat → Int) (hstep : ∀ n, E (n + 1) ≤ E n - 1) :
    ∀ n, E n ≤ E 0 - n := by
  intro n
  induction n with
  | zero => simp
  | succ k ih =>
      have h := hstep k
      omega

/-- **Termination.**  If the edge defect stays nonnegative and drops by at least
one per addition, the bootstrap performs at most `E 0` additions.  Theorem 2.1
runs the process for at most `⌊E(K)⌋` steps for exactly this reason. -/
theorem bootstrap_terminates (E : Nat → Int) (N : Nat)
    (hstep : ∀ n, E (n + 1) ≤ E n - 1) (hnonneg : 0 ≤ E N) :
    (N : Int) ≤ E 0 := by
  have h := descent_linear E hstep N
  omega

/-! ## 3. The transfer at the terminal set

At the terminal set every outer boundary vertex has exactly one neighbour
inside, so the two boundaries have the same size and the two defects agree.
Since the vertex defect only fell along the way, its initial value is at least
its terminal value, which is the nonnegative edge defect.  That is the
inequality `|∂_V K| ≥ a(K) + β` of (2.3).
-/

/-- **Boundary transfer.**  If the vertex defect at the start is at least its
value at the terminal set plus the accumulated surplus, and the terminal vertex
defect equals the terminal edge defect, which is nonnegative, then the starting
vertex defect is at least the accumulated surplus.  With surplus zero this is
`|∂_V K| ≥ a(K) + β`. -/
theorem transfer (dV dVterm dEterm surplusSum : Int)
    (hdrop : dVterm + surplusSum ≤ dV)
    (hterm : dVterm = dEterm)
    (hEnonneg : 0 ≤ dEterm) :
    surplusSum ≤ dV := by
  omega

/-- The unweighted corollary: the starting vertex defect is nonnegative, which
is Theorem 1.2's conclusion `h_V ≥ h_E`. -/
theorem transfer_unweighted (dV dVterm dEterm : Int)
    (hdrop : dVterm ≤ dV) (hterm : dVterm = dEterm) (hEnonneg : 0 ≤ dEterm) :
    0 ≤ dV := by
  omega

/-! ## 4. The threshold algebra

`Φ(d,f)² = (d-2)² - 4(d-2)/(f-2)`.  Multiplying by `f-2` clears the
denominator, so `phiSqNum d f = (f-2)·Φ(d,f)²` is an integer and every
comparison of `Φ` with `d-3` becomes an integer comparison.
-/

/-- `(f-2)·Φ(d,f)²`, an integer for integer `d, f`. -/
def phiSqNum (d f : Int) : Int := (d - 2) * (d - 2) * (f - 2) - 4 * (d - 2)

/-- The difference of squares behind (4.2): `(d-2)² - (d-3)² = 2d - 5`. -/
theorem sq_diff (d : Int) : (d - 2) * (d - 2) - (d - 3) * (d - 3) = 2 * d - 5 := by
  simp [Int.sub_mul, Int.mul_sub]
  omega

/-- The threshold comparison, cleared of denominators:
`(f-2)·(Φ² - (d-3)²) = (f-2)(2d-5) - 4(d-2)`. -/
theorem threshold_identity (d f : Int) :
    phiSqNum d f - (d - 3) * (d - 3) * (f - 2)
      = (2 * d - 5) * (f - 2) - 4 * (d - 2) := by
  unfold phiSqNum
  have h : (d - 2) * (d - 2) * (f - 2) - (d - 3) * (d - 3) * (f - 2)
      = ((d - 2) * (d - 2) - (d - 3) * (d - 3)) * (f - 2) := by
    simp [Int.sub_mul]
  rw [sq_diff] at h
  omega

/-- **The threshold holds for `f ≥ 5` and `d ≥ 4`.**  This is the inequality
`h > d - 3` of (4.2), which is what lets Theorem 1.2 apply to a `(d,f)`-regular
tessellation.  Stated as `Φ² > (d-3)²` after clearing `f-2 > 0`. -/
theorem threshold_holds {d f : Int} (hd : 4 ≤ d) (hf : 5 ≤ f) :
    (d - 3) * (d - 3) * (f - 2) < phiSqNum d f := by
  have key : 4 * (d - 2) < (2 * d - 5) * (f - 2) := by
    have h3 : (3 : Int) ≤ f - 2 := by omega
    have hpos : (0 : Int) ≤ 2 * d - 5 := by omega
    have hmono : (2 * d - 5) * 3 ≤ (2 * d - 5) * (f - 2) :=
      Int.mul_le_mul_of_nonneg_left h3 hpos
    omega
  have hid := threshold_identity d f
  omega

/-- The degree-three case: admissibility forces `f ≥ 6`, and then `Φ ≥ 0 = d-3`,
so the threshold holds with equality allowed. -/
theorem threshold_holds_cubic {f : Int} (hf : 6 ≤ f) :
    (3 - 3) * (3 - 3) * (f - 2) ≤ phiSqNum 3 f := by
  unfold phiSqNum
  omega

/-- **The pentagonal value.**  `Φ(5,5)² = 5`, so `h_V(H_{5,5}) = √5`. -/
theorem phi_five_five : phiSqNum 5 5 = 5 * (5 - 2) := by decide

/-- `Φ(3,6) = 0`: the Euclidean hexagonal tessellation is amenable. -/
theorem phi_three_six : phiSqNum 3 6 = 0 := by decide

/-! ## 5. Optimality of the additive constant 3

For the quadrangular tessellation `Q_d = H_{d,4}` the edge constant is
`e_d = sqrt((d-2)(d-4))` and the vertex constant is the positive root of
`P_d(x) = x² - (d-4)x - (d-4)`.  Proposition 6.1 shows `v_d < e_d` from
`P_d(e_d) > 0`, which rests on two identities that hold for any `x` with
`x² = (d-2)(d-4)`; no square root is needed to state or check them.
-/

/-- `e_d² = (d-3)² - 1`, the identity behind `d - 3 - e_d = 1/(d-3+e_d) → 0`. -/
theorem quad_edge_sq (d : Int) :
    (d - 2) * (d - 4) = (d - 3) * (d - 3) - 1 := by
  simp [Int.sub_mul, Int.mul_sub]
  omega

/-- **`P_d(e_d) = (d-4)(d-3-e_d)`.**  Stated for any `x` with `x² = (d-2)(d-4)`,
which is what `e_d` satisfies.  Since `d ≥ 5` gives `d - 4 > 0`, and the paper
shows `d - 3 - e_d > 0`, this forces `P_d(e_d) > 0` and hence `v_d < e_d`. -/
theorem quad_poly_at_edge (d x : Int) (hx : x * x = (d - 2) * (d - 4)) :
    x * x - (d - 4) * x - (d - 4) = (d - 4) * (d - 3 - x) := by
  rw [hx]
  simp [Int.mul_sub, Int.sub_mul]
  omega

/-- The vertex constant `v_d` is a root of `P_d`, and `P_d` has a negative root,
so a point where `P_d` is positive and which is itself positive lies above the
positive root.  Recorded as the sign fact the argument uses. -/
theorem quad_poly_sign {d x : Int} (hd : 5 ≤ d) (hgap : x < d - 3) :
    0 < (d - 4) * (d - 3 - x) := by
  have h1 : (0 : Int) < d - 4 := by omega
  have h2 : (0 : Int) < d - 3 - x := by omega
  exact Int.mul_pos h1 h2

/-! ## 6. The volume-weighted threshold

Corollary 2.4 replaces the flat weight by `a(v) = h·deg(v)`.  The hypothesis
`a(v) ≥ deg(v) - 3` then reads `(1-h)·deg(v) ≤ 3`, which is condition (2.9).
-/

/-- The volume-weighted hypothesis is exactly condition (2.9). -/
theorem volume_weight_iff (h s : Int) :
    (s - 3 ≤ h * s) ↔ (s - h * s ≤ 3) := by
  omega

end OuterIsoperimetry
