/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.
-/
/-
Selected prefix from facebookresearch/algebraic-combinatorics commit
b6022318e986a0c20764569208ba8ebbe1c04dbf. The selection ends immediately after
`lgv_nonpermutable`; all later applications, including native-evaluated examples
and the admitted Catalan exercise, are omitted. See THIRD_PARTY.md.
-/
import Mathlib

/-!
# The Lindström-Gessel-Viennot Lemma: Weighted and Generalized Versions

This file formalizes the weighted version of the LGV lemma and related results,
following Section "The weighted version ... The nonpermutable case" (sec.det.comb.lgv)
of the Algebraic Combinatorics notes.

## Main definitions

* `LGV.SimpleDigraph`: A digraph structure with no self-loops (irreflexive adjacency)
* `LGV.SimpleDigraph.toDigraph`: Conversion to Mathlib's `Digraph` type
* `LGV.ArcWeight`: A weight function on arcs of a digraph
* `LGV.pathWeight`: The weight of a path (product of arc weights)
* `LGV.pathTupleWeight`: The weight of a path tuple (product of path weights)
* `LGV.pathWeightMatrix`: The matrix of sums of path weights between source/target vertices
* `LGV.catalanHankelMatrix`: The Hankel matrix of Catalan numbers

## Main results

* `LGV.lgv_weighted_lattice`: LGV lemma, lattice weight version (Theorem thm.lgv.kpaths.wt)
* `LGV.lgv_weighted_digraph`: LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
* `LGV.lgv_nonpermutable`: LGV lemma, nonpermutable lattice weight version
    (Corollary cor.lgv.kpaths.wt-np)
* `LGV.binom_det_nonneg`: Determinant of binomial coefficient matrix is nonnegative
    (Corollary cor.lgv.binom-det-nonneg)
* `LGV.catalan_hankel_det`: Hankel determinant of Catalan numbers equals 1
    (Corollary cor.lgv.catalan-hankel-det-0)
* `LGV.catalan_hankel_det_zero` through `LGV.catalan_hankel_det_seven`: Base cases proved
    by computation

## References

* Source: AlgebraicCombinatorics/tex/Determinants/LGV2.tex
* [Lindström, *On the vector representations of induced matroids*][Lindstrom73]
* [Gessel-Viennot, *Binomial determinants, paths, and hook length formulae*][GesVie85]

## Implementation notes

We formalize the LGV lemma for general path-finite acyclic digraphs, with the integer
lattice ℤ² as a special case. The key construction is a sign-reversing involution
on intersecting path tuples that exchanges tails at the first intersection point.

The nonpermutable case applies when the source and target vertices are "sorted" in
a way that prevents non-identity permutations from having non-intersecting path tuples.

For the Catalan Hankel determinant, we use Mathlib's `catalan` function and prove
the base cases (k = 0, 1, ..., 7) by direct computation using `native_decide`.
The general theorem uses the LGV lemma with Dyck paths.

### Relationship with LGV1.lean

This file (LGV2.lean) and LGV1.lean both work with the integer lattice digraph, but
use different representations:

- **LGV1.lean**: Uses Mathlib's `Digraph` type and `LatticePath` (list of steps: east/north)
- **LGV2.lean**: Uses `LGV.SimpleDigraph` (custom structure with irreflexivity) and
  `SimpleDigraph.Path` (list of vertices)

The integer lattice definitions have equivalent adjacency relations, proven by
`integerLattice_arc_iff` and `integerLattice_toDigraph_adj_iff`. The conversion
`SimpleDigraph.toDigraph` allows transferring results between the two representations.

This file contains the complete weighted LGV lemma proof. LGV1.lean contains the
counting case infrastructure with lattice-specific path counting results.
-/

open Finset BigOperators Matrix

namespace LGV

/-!
## Digraph Definitions

We work with simple digraphs that are path-finite and acyclic.
-/

/-- A simple digraph with vertex set V.
    Convention conv.lgv.digraph(d): A simple digraph has arcs as pairs of distinct vertices. -/
structure SimpleDigraph (V : Type*) where
  /-- The arc relation: `arc u v` means there is an arc from `u` to `v` -/
  arc : V → V → Prop
  /-- No self-loops -/
  arc_irrefl : ∀ v, ¬arc v v

namespace SimpleDigraph

variable {V : Type*} [DecidableEq V]

/-- A path in a digraph is a list of vertices where consecutive vertices are connected by arcs.
    A path may contain 0 arcs (in which case start and end are identical). -/
structure Path (D : SimpleDigraph V) where
  /-- The vertices of the path, in order -/
  vertices : List V
  /-- The path is nonempty -/
  nonempty : vertices ≠ []
  /-- Consecutive vertices are connected by arcs -/
  arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length, D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩)
      (vertices.get ⟨i + 1, hi⟩)

/-- The starting vertex of a path -/
def Path.start {D : SimpleDigraph V} (p : Path D) : V :=
  p.vertices.head p.nonempty

/-- The ending vertex of a path -/
def Path.finish {D : SimpleDigraph V} (p : Path D) : V :=
  p.vertices.getLast p.nonempty

omit [DecidableEq V] in
/-- Simp lemma for `Path.start` on a constructed path -/
@[simp] lemma Path.start_mk {D : SimpleDigraph V} (vs : List V) (hne : vs ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, D.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vs.get ⟨i + 1, hi⟩)) :
    (Path.mk vs hne harcs).start = vs.head hne := rfl

omit [DecidableEq V] in
/-- Simp lemma for `Path.finish` on a constructed path -/
@[simp] lemma Path.finish_mk {D : SimpleDigraph V} (vs : List V) (hne : vs ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < vs.length, D.arc (vs.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (vs.get ⟨i + 1, hi⟩)) :
    (Path.mk vs hne harcs).finish = vs.getLast hne := rfl

/-- A digraph is path-finite if there are only finitely many paths between any two vertices.
    Convention conv.lgv.digraph(b) -/
def IsPathFinite (D : SimpleDigraph V) : Prop :=
  ∀ u v : V, Set.Finite {p : Path D | p.start = u ∧ p.finish = v}

/-- A digraph is acyclic if it has no directed cycles.
    Convention conv.lgv.digraph(c) -/
def IsAcyclic (D : SimpleDigraph V) : Prop :=
  ∀ p : Path D, p.start = p.finish → p.vertices.length = 1

/-- Extract a subpath from index `i` to index `j` (inclusive).
    The resulting path has `j - i + 1` vertices. -/
def Path.subpath {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) : Path D where
  vertices := (p.vertices.drop i).take (j - i + 1)
  nonempty := by
    simp only [ne_eq, List.take_eq_nil_iff, List.drop_eq_nil_iff]
    push_neg
    constructor <;> omega
  arcs_valid := by
    intro k hk
    simp only [List.length_take, List.length_drop] at hk
    have hk' : k + 1 < min (j - i + 1) (p.vertices.length - i) := hk
    have hk'' : k < j - i := by omega
    simp only [List.getElem_take, List.getElem_drop, List.get_eq_getElem]
    have hi' : i + k < p.vertices.length := by omega
    have hi'' : i + k + 1 < p.vertices.length := by omega
    simpa only [List.get_eq_getElem, Nat.add_assoc] using p.arcs_valid (i + k) hi''

omit [DecidableEq V] in
/-- The start of a subpath is the vertex at index `i`. -/
lemma Path.subpath_start {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) :
    (p.subpath i j hij hj).start = p.vertices.get ⟨i, Nat.lt_of_le_of_lt hij hj⟩ := by
  simp only [subpath, start, List.head_eq_getElem, List.getElem_take, List.getElem_drop, 
             List.get_eq_getElem, add_zero]

omit [DecidableEq V] in
/-- The finish of a subpath is the vertex at index `j`. -/
lemma Path.subpath_finish {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) :
    (p.subpath i j hij hj).finish = p.vertices.get ⟨j, hj⟩ := by
  simp only [subpath, finish]
  rw [List.getLast_eq_getElem]
  simp only [List.length_take, List.length_drop, List.getElem_take, List.getElem_drop]
  congr 1
  omega

omit [DecidableEq V] in
/-- The length of a subpath from `i` to `j` is `j - i + 1`. -/
lemma Path.subpath_length {D : SimpleDigraph V} (p : Path D) (i j : ℕ) (hij : i ≤ j) 
    (hj : j < p.vertices.length) :
    (p.subpath i j hij hj).vertices.length = j - i + 1 := by
  simp only [subpath, List.length_take, List.length_drop]
  omega

omit [DecidableEq V] in
/-- In an acyclic digraph, all vertices on a path are distinct.
    This follows from the fact that if a vertex appears twice, we could extract
    a cycle (a path from that vertex back to itself). -/
lemma Path.vertices_nodup_of_acyclic {D : SimpleDigraph V} (hac : D.IsAcyclic) 
    (p : Path D) : p.vertices.Nodup := by
  rw [List.nodup_iff_injective_getElem]
  intro ⟨i, hi⟩ ⟨j, hj⟩ hget
  simp only [Fin.mk.injEq]
  -- hget : p.vertices[i] = p.vertices[j]
  -- WLOG i ≤ j
  by_cases hij : i ≤ j
  · -- Case i ≤ j: Extract subpath from i to j
    let sp := p.subpath i j hij hj
    -- This subpath starts and ends at the same vertex
    have hcycle : sp.start = sp.finish := by
      simp only [sp, subpath_start, subpath_finish, List.get_eq_getElem]
      exact hget
    -- By acyclicity, the subpath has length 1
    have hlen1 := hac sp hcycle
    -- The subpath length is j - i + 1
    have hlen2 : sp.vertices.length = j - i + 1 := subpath_length p i j hij hj
    -- So j - i + 1 = 1, i.e., j = i
    omega
  · -- Case j < i: symmetric
    push_neg at hij
    have hij' : j ≤ i := le_of_lt hij
    let sp := p.subpath j i hij' hi
    have hcycle : sp.start = sp.finish := by
      simp only [sp, subpath_start, subpath_finish, List.get_eq_getElem]
      exact hget.symm
    have hlen1 := hac sp hcycle
    have hlen2 : sp.vertices.length = i - j + 1 := subpath_length p j i hij' hi
    omega

/-!
### Conversion to Mathlib's Digraph

`LGV.SimpleDigraph` is a specialized digraph structure that enforces irreflexivity
(no self-loops). Mathlib's `Digraph` is more general and allows self-loops.

We provide a conversion that forgets the irreflexivity proof, allowing use of
Mathlib's digraph infrastructure when needed.
-/

variable {V : Type*}

/-- Convert a `SimpleDigraph` to Mathlib's `Digraph`.
    This forgets the irreflexivity proof but preserves the adjacency relation.
    
    Note: LGV1.lean uses Mathlib's `Digraph` directly, while LGV2.lean uses this
    `SimpleDigraph` structure. This conversion enables interoperability. -/
def toDigraph (D : SimpleDigraph V) : Digraph V where
  Adj := D.arc

/-- The adjacency relation is preserved by `toDigraph`. -/
@[simp]
theorem toDigraph_adj (D : SimpleDigraph V) (u v : V) :
    D.toDigraph.Adj u v ↔ D.arc u v := Iff.rfl

end SimpleDigraph

/-!
## The Integer Lattice ℤ²

Definition def.lgv.lattice: The integer lattice has vertex set ℤ² with arcs
(i,j) → (i+1,j) (east-steps) and (i,j) → (i,j+1) (north-steps).

### Relationship with LGV1.lean

LGV1.lean defines `LGV.integerLattice : Digraph LatticePoint` using Mathlib's `Digraph`.
This file defines `LGV.integerLattice : SimpleDigraph (ℤ × ℤ)` using our custom structure.

The two definitions have semantically identical adjacency relations:
- LGV1: `IntegerLatticeAdj p q ↔ q = (p.1 + 1, p.2) ∨ q = (p.1, p.2 + 1)`
- LGV2: `integerLattice.arc u v ↔ (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)`

The lemma `integerLattice_arc_iff` proves these are equivalent, enabling
results from either file to be transferred to the other.
-/

/-- The integer lattice digraph ℤ².
    
    This is the same lattice as in LGV1.lean, but using `SimpleDigraph` instead of
    Mathlib's `Digraph`. See `integerLattice_arc_iff` for the characterization
    and `integerLattice_toDigraph_adj_iff` for the equivalence with LGV1's definition. -/
def integerLattice : SimpleDigraph (ℤ × ℤ) where
  arc u v := (v.1 = u.1 + 1 ∧ v.2 = u.2) ∨ (v.1 = u.1 ∧ v.2 = u.2 + 1)
  arc_irrefl := by
    intro ⟨x, y⟩
    simp only [not_or, not_and]
    constructor <;> omega

/-- Characterization of adjacency in the integer lattice.
    An arc exists from u to v iff v is one step east or north of u.
    
    This matches the form of `integerLattice_adj_iff` in LGV1.lean. -/
theorem integerLattice_arc_iff (u v : ℤ × ℤ) :
    integerLattice.arc u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) := by
  simp only [integerLattice, Prod.ext_iff]

/-- The integer lattice adjacency relation in LGV2 matches the one in LGV1.
    
    This bridges the two definitions:
    - LGV1.lean: `integerLattice.Adj p q` where `integerLattice : Digraph LatticePoint`
    - LGV2.lean: `integerLattice.arc u v` where `integerLattice : SimpleDigraph (ℤ × ℤ)`
    
    Both are equivalent to: `v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1)` -/
theorem integerLattice_toDigraph_adj_iff (u v : ℤ × ℤ) :
    integerLattice.toDigraph.Adj u v ↔ v = (u.1 + 1, u.2) ∨ v = (u.1, u.2 + 1) :=
  integerLattice_arc_iff u v

/-- Each arc in the integer lattice increases coordinates (or keeps them equal) -/
private lemma integerLattice_arc_nondecreasing (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    u.1 ≤ v.1 ∧ u.2 ≤ v.2 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Each arc in the integer lattice increases the sum x + y by exactly 1 -/
private lemma integerLattice_arc_sum (u v : ℤ × ℤ) (h : integerLattice.arc u v) :
    v.1 + v.2 = u.1 + u.2 + 1 := by
  rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega

/-- Coordinates are monotone along a path in the integer lattice -/
private lemma integerLattice_path_monotone (p : SimpleDigraph.Path integerLattice) (i j : ℕ)
    (hi : i < p.vertices.length) (hj : j < p.vertices.length) (hij : i ≤ j) :
    (p.vertices.get ⟨i, hi⟩).1 ≤ (p.vertices.get ⟨j, hj⟩).1 ∧
    (p.vertices.get ⟨i, hi⟩).2 ≤ (p.vertices.get ⟨j, hj⟩).2 := by
  induction j with
  | zero =>
    simp only [Nat.le_zero] at hij
    subst hij
    constructor <;> rfl
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hij with rfl | hik
    · constructor <;> rfl
    · have hk : k < p.vertices.length := Nat.lt_of_succ_lt hj
      have hik' : i ≤ k := Nat.lt_succ_iff.mp hik
      obtain ⟨h1, h2⟩ := ih hk hik'
      have harc : integerLattice.arc (p.vertices.get ⟨k, hk⟩) (p.vertices.get ⟨k + 1, hj⟩) :=
        p.arcs_valid k hj
      obtain ⟨h3, h4⟩ := integerLattice_arc_nondecreasing _ _ harc
      exact ⟨le_trans h1 h3, le_trans h2 h4⟩

/-- Start coordinates ≤ finish coordinates for any path in the integer lattice -/
private lemma integerLattice_path_start_le_finish (p : SimpleDigraph.Path integerLattice) :
    p.start.1 ≤ p.finish.1 ∧ p.start.2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h := integerLattice_path_monotone p 0 (p.vertices.length - 1) hlen hlast (Nat.zero_le _)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  convert h using 2 <;> simp [List.head_eq_getElem, List.getLast_eq_getElem]

/-- Helper for path_sum_eq: proves the sum formula by induction on the list -/
private lemma integerLattice_path_sum_eq_aux (l : List (ℤ × ℤ)) (hne : l ≠ [])
    (harcs : ∀ i : ℕ, ∀ hi : i + 1 < l.length, integerLattice.arc (l.get ⟨i, Nat.lt_of_succ_lt hi⟩)
        (l.get ⟨i + 1, hi⟩)) :
    (l.getLast hne).1 + (l.getLast hne).2 = (l.head hne).1 + (l.head hne).2 + (l.length - 1) := by
  induction l with
  | nil => exact absurd rfl hne
  | cons x xs ih =>
    cases xs with
    | nil => simp
    | cons y ys =>
      have hne' : y :: ys ≠ [] := List.cons_ne_nil y ys
      have harcs' : ∀ i : ℕ, ∀ hi : i + 1 < (y :: ys).length,
          integerLattice.arc ((y :: ys).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((y :: ys).get ⟨i + 1, hi⟩) := by
        intro i hi
        have hi' : (i + 1) + 1 < (x :: y :: ys).length := by simp at hi ⊢; omega
        have := harcs (i + 1) hi'
        simp only [List.length_cons, List.get_cons_succ] at this ⊢
        exact this
      have harc_xy : integerLattice.arc x y := by
        have := harcs 0 (by simp : 0 + 1 < (x :: y :: ys).length)
        simp at this
        exact this
      have hsum_xy := integerLattice_arc_sum x y harc_xy
      specialize ih hne' harcs'
      simp only [List.getLast_cons hne', List.head_cons, List.length_cons] at ih ⊢
      omega

/-- The sum of coordinates increases by exactly (length - 1) along a path -/
private lemma integerLattice_path_sum_eq (p : SimpleDigraph.Path integerLattice) :
    p.finish.1 + p.finish.2 = p.start.1 + p.start.2 + (p.vertices.length - 1) :=
  integerLattice_path_sum_eq_aux p.vertices p.nonempty p.arcs_valid

/-- Path length is determined by start and finish coordinates -/
lemma integerLattice_path_length_eq (p : SimpleDigraph.Path integerLattice) :
    (p.vertices.length : ℤ) = p.finish.1 + p.finish.2 - p.start.1 - p.start.2 + 1 := by
  have h := integerLattice_path_sum_eq p
  have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  omega

/-- Sum at vertex i equals start sum + i -/
lemma integerLattice_path_vertex_sum (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    (p.vertices.get ⟨i, hi⟩).1 + (p.vertices.get ⟨i, hi⟩).2 = p.start.1 + p.start.2 + i := by
  induction i with
  | zero =>
    simp only [SimpleDigraph.Path.start, CharP.cast_eq_zero, add_zero]
    have : p.vertices.get ⟨0, hi⟩ = p.vertices.head p.nonempty := by
      simp [List.head_eq_getElem, List.get_eq_getElem]
    rw [this]
  | succ k ih =>
    have hk : k < p.vertices.length := Nat.lt_of_succ_lt hi
    have ihk := ih hk
    have harc := p.arcs_valid k hi
    have hsum := integerLattice_arc_sum _ _ harc
    omega

/-- x-coordinate change at each step is 0 or 1 -/
lemma integerLattice_path_x_step (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i + 1 < p.vertices.length) :
    (p.vertices.get ⟨i + 1, hi⟩).1 - (p.vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩).1 = 0 ∨
    (p.vertices.get ⟨i + 1, hi⟩).1 - (p.vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩).1 = 1 := by
  have harc := p.arcs_valid i hi
  rcases harc with ⟨hx, _⟩ | ⟨hx, _⟩ <;> [right; left] <;> omega

/-- Vertices of a lattice path are bounded by start and finish coordinates -/
lemma integerLattice_path_vertices_bounded (p : SimpleDigraph.Path integerLattice) (i : ℕ)
    (hi : i < p.vertices.length) :
    p.start.1 ≤ (p.vertices.get ⟨i, hi⟩).1 ∧ (p.vertices.get ⟨i, hi⟩).1 ≤ p.finish.1 ∧
    p.start.2 ≤ (p.vertices.get ⟨i, hi⟩).2 ∧ (p.vertices.get ⟨i, hi⟩).2 ≤ p.finish.2 := by
  have hne := p.nonempty
  have hlen : 0 < p.vertices.length := List.length_pos_of_ne_nil hne
  have hlast : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hlen Nat.one_pos
  have h1 := integerLattice_path_monotone p 0 i hlen hi (Nat.zero_le _)
  have h2 := integerLattice_path_monotone p i (p.vertices.length - 1) hi hlast (Nat.le_sub_one_of_lt hi)
  simp only [SimpleDigraph.Path.start, SimpleDigraph.Path.finish]
  constructor
  · convert h1.1 using 1; simp [List.head_eq_getElem]
  constructor
  · convert h2.1 using 1; simp [List.getLast_eq_getElem]
  constructor
  · convert h1.2 using 1; simp [List.head_eq_getElem]
  · convert h2.2 using 1; simp [List.getLast_eq_getElem]

/-- Paths in the integer lattice are determined by their vertex list -/
private lemma integerLattice_path_ext (p q : SimpleDigraph.Path integerLattice)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

/-- The integer lattice is acyclic -/
theorem integerLattice_acyclic : integerLattice.IsAcyclic := by
  intro p hp
  -- We'll show that any path in the integer lattice that returns to its start must be trivial
  -- Key observation: each arc increases x+y by exactly 1
  by_contra h
  -- If the path has length > 1, it has at least one arc
  have hpos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  have hlen : 1 < p.vertices.length := by
    rcases Nat.eq_or_lt_of_le (Nat.one_le_of_lt hpos) with heq | hlt
    · exact (h heq.symm).elim
    · exact hlt
  -- We'll prove by induction that for all i, the sum x+y at position i is at least x+y at position 0 plus i
  have hmono : ∀ i : ℕ, ∀ hi : i < p.vertices.length,
      (p.vertices.get ⟨i, hi⟩).1 + (p.vertices.get ⟨i, hi⟩).2 ≥
      (p.vertices.get ⟨0, hpos⟩).1 + (p.vertices.get ⟨0, hpos⟩).2 + i := by
    intro i
    induction i with
    | zero => intro hi; simp
    | succ n ih =>
      intro hi
      have hn : n < p.vertices.length := Nat.lt_of_succ_lt hi
      have harci : n + 1 < p.vertices.length := hi
      have harc_n := p.arcs_valid n harci
      simp only [integerLattice] at harc_n
      have ih_n := ih hn
      rcases harc_n with ⟨hx, hy⟩ | ⟨hx, hy⟩ <;> omega
  -- Apply to the last vertex
  have hlast_idx : p.vertices.length - 1 < p.vertices.length := Nat.sub_lt hpos Nat.one_pos
  have hlast := hmono (p.vertices.length - 1) hlast_idx
  -- The last vertex is getLast
  have hlast_eq : p.vertices.get ⟨p.vertices.length - 1, hlast_idx⟩ = p.vertices.getLast p.nonempty := by
    simp [List.getLast_eq_getElem]
  rw [hlast_eq] at hlast
  -- start = head = get 0
  have hstart : p.start = p.vertices.get ⟨0, hpos⟩ := by
    simp [SimpleDigraph.Path.start, List.head_eq_getElem]
  -- finish = getLast
  have hfinish : p.finish = p.vertices.getLast p.nonempty := rfl
  -- Since start = finish
  rw [← hfinish, ← hp, hstart] at hlast
  -- We get a contradiction since length - 1 ≥ 1
  have hlen' : p.vertices.length - 1 ≥ 1 := Nat.le_sub_one_of_lt hlen
  omega

/-- The integer lattice is path-finite -/
theorem integerLattice_pathFinite : integerLattice.IsPathFinite := by
  intro u v
  by_cases h : v.1 < u.1 ∨ v.2 < u.2
  · -- Case 1: No paths exist (would need to go backwards)
    convert Set.finite_empty
    ext p
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro hstart hfinish
    have hle := integerLattice_path_start_le_finish p
    rw [hstart, hfinish] at hle
    omega
  · -- Case 2: Paths exist but are finite
    push_neg at h
    -- Define the path length and bounding box
    let n := (v.1 - u.1 + v.2 - u.2 + 1).toNat
    let box : Finset (ℤ × ℤ) := (Finset.Icc u.1 v.1) ×ˢ (Finset.Icc u.2 v.2)
    -- Define the subtype of paths from u to v
    let S := {p : SimpleDigraph.Path integerLattice | p.start = u ∧ p.finish = v}
    -- Show S is finite by injecting into Fin n → box
    suffices Finite S by exact Set.finite_coe_iff.mpr this
    -- Define the injection: map each path to its vertex list as a function
    let f : S → (Fin n → box) := fun ⟨p, hp⟩ i =>
      let hi : i.val < p.vertices.length := by
        have hlen := integerLattice_path_length_eq p
        rw [hp.1, hp.2] at hlen
        simp only [n] at hlen ⊢
        have := i.isLt
        omega
      ⟨p.vertices.get ⟨i.val, hi⟩, by
        have hbd := integerLattice_path_vertices_bounded p i.val hi
        rw [hp.1, hp.2] at hbd
        simp only [box, Finset.mem_product, Finset.mem_Icc]
        exact ⟨⟨hbd.1, hbd.2.1⟩, ⟨hbd.2.2.1, hbd.2.2.2⟩⟩⟩
    have hinj : Function.Injective f := by
      intro ⟨p, hp⟩ ⟨q, hq⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      apply integerLattice_path_ext
      apply List.ext_get
      · -- Lengths are equal (both determined by u and v)
        have hlenp := integerLattice_path_length_eq p
        have hlenq := integerLattice_path_length_eq q
        rw [hp.1, hp.2] at hlenp
        rw [hq.1, hq.2] at hlenq
        omega
      · -- Elements are equal at each position
        intro i hip hiq
        have heqi := congr_fun heq ⟨i, by
          have hlenp := integerLattice_path_length_eq p
          rw [hp.1, hp.2] at hlenp
          simp only [n]
          omega⟩
        simp only [Subtype.mk.injEq] at heqi
        exact heqi
    exact Finite.of_injective f hinj

/-!
## Path Weights

For each arc, we assign a weight from a commutative ring K.
The weight of a path is the product of its arc weights.
-/

variable {V : Type*} [DecidableEq V] {K : Type*} [CommRing K]

/-- An arc weight function assigns a ring element to each arc.
    Definition in Theorem thm.lgv.kpaths.wt -/
def ArcWeight (D : SimpleDigraph V) (K : Type*) := (u v : V) → D.arc u v → K

/-- Helper function to compute the product of arc weights along a vertex list.
    Uses recursion on the structure of the list.
    - For an empty list or single vertex, the weight is 1 (no arcs).
    - For a list [v₀, v₁, ...], the weight is w(v₀, v₁) * (weight of [v₁, ...]). -/
noncomputable def pathWeightAux {D : SimpleDigraph V} (w : ArcWeight D K)
    (vertices : List V) (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩)) : K :=
  match vertices with
  | [] => 1
  | [_] => 1
  | v₀ :: v₁ :: rest =>
    have h : 0 + 1 < (v₀ :: v₁ :: rest).length := by simp
    have arc_proof : D.arc v₀ v₁ := by
      have := arcs_valid 0 h
      simp at this
      exact this
    have rest_arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < (v₁ :: rest).length,
        D.arc ((v₁ :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v₁ :: rest).get ⟨i + 1, hi⟩) := by
      intro i hi
      have hi' : (i + 1) + 1 < (v₀ :: v₁ :: rest).length := by simp at hi ⊢; omega
      have := arcs_valid (i + 1) hi'
      simp only [List.length_cons, List.get_cons_succ] at this ⊢
      exact this
    w v₀ v₁ arc_proof * pathWeightAux w (v₁ :: rest) rest_arcs_valid

/-- The weight of a path is the product of weights of its arcs.
    w(p) := ∏_{a is an arc of p} w(a) -/
noncomputable def pathWeight {D : SimpleDigraph V} (w : ArcWeight D K) (p : SimpleDigraph.Path D) : K :=
  pathWeightAux w p.vertices p.arcs_valid

omit [DecidableEq V] in
/-- pathWeightAux is independent of the proof of arcs_valid (proof irrelevance). -/
lemma pathWeightAux_proof_irrel {D : SimpleDigraph V} (w : ArcWeight D K)
    (l : List V) (arcs1 arcs2 : ∀ i : ℕ, ∀ hi : i + 1 < l.length,
      D.arc (l.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l.get ⟨i + 1, hi⟩)) :
    pathWeightAux w l arcs1 = pathWeightAux w l arcs2 := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    cases vs with
    | nil => rfl
    | cons v' vs' =>
      unfold pathWeightAux
      show (w v v' _ * pathWeightAux w (v' :: vs') _) = (w v v' _ * pathWeightAux w (v' :: vs') _)
      rfl

omit [DecidableEq V] in
/-- pathWeightAux equality when lists are equal (combines substitution with proof irrelevance). -/
lemma pathWeightAux_eq_of_eq {D : SimpleDigraph V} (w : ArcWeight D K) {l1 l2 : List V} (h : l1 = l2)
    (arcs1 : ∀ i : ℕ, ∀ hi : i + 1 < l1.length,
      D.arc (l1.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l1.get ⟨i + 1, hi⟩))
    (arcs2 : ∀ i : ℕ, ∀ hi : i + 1 < l2.length,
      D.arc (l2.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l2.get ⟨i + 1, hi⟩)) :
    pathWeightAux w l1 arcs1 = pathWeightAux w l2 arcs2 := by
  subst h
  exact pathWeightAux_proof_irrel w l1 arcs1 arcs2

omit [DecidableEq V] in
/-- pathWeightAux of a singleton list is 1. -/
@[simp]
lemma pathWeightAux_singleton {D : SimpleDigraph V} (w : ArcWeight D K) (v : V)
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < [v].length,
      D.arc ([v].get ⟨i, Nat.lt_of_succ_lt hi⟩) ([v].get ⟨i + 1, hi⟩)) :
    pathWeightAux w [v] arcs_valid = 1 := rfl

omit [DecidableEq V] in
/-- pathWeightAux of a two-element list is just the arc weight. -/
lemma pathWeightAux_pair {D : SimpleDigraph V} (w : ArcWeight D K) (u v : V)
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < [u, v].length,
      D.arc ([u, v].get ⟨i, Nat.lt_of_succ_lt hi⟩) ([u, v].get ⟨i + 1, hi⟩)) :
    pathWeightAux w [u, v] arcs_valid = w u v (arcs_valid 0 (by simp)) := by
  unfold pathWeightAux
  simp

omit [DecidableEq V] in
/-- pathWeightAux of a cons-cons list factors into an arc weight times the tail. -/
lemma pathWeightAux_cons_cons {D : SimpleDigraph V} (w : ArcWeight D K) (u v : V) (rest : List V)
    (arcs_valid : ∀ i : ℕ, ∀ hi : i + 1 < (u :: v :: rest).length,
      D.arc ((u :: v :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((u :: v :: rest).get ⟨i + 1, hi⟩))
    (rest_arcs : ∀ i : ℕ, ∀ hi : i + 1 < (v :: rest).length,
      D.arc ((v :: rest).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v :: rest).get ⟨i + 1, hi⟩))
    (arc_uv : D.arc u v) :
    pathWeightAux w (u :: v :: rest) arcs_valid = 
      w u v arc_uv * pathWeightAux w (v :: rest) rest_arcs := by
  simp only [pathWeightAux]

omit [DecidableEq V] in
/-- pathWeightAux is multiplicative over list append when the lists share a common vertex.
    If l1 = [..., v] and l2 = [v, ...], then pathWeightAux (l1 ++ l2.tail) = pathWeightAux l1 * pathWeightAux l2. -/
lemma pathWeightAux_append {D : SimpleDigraph V} (w : ArcWeight D K)
    (l1 l2 : List V) (h1_ne : l1 ≠ []) (h2_ne : l2 ≠ [])
    (h_join : l1.getLast h1_ne = l2.head h2_ne)
    (arcs1 : ∀ i : ℕ, ∀ hi : i + 1 < l1.length,
      D.arc (l1.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l1.get ⟨i + 1, hi⟩))
    (arcs2 : ∀ i : ℕ, ∀ hi : i + 1 < l2.length,
      D.arc (l2.get ⟨i, Nat.lt_of_succ_lt hi⟩) (l2.get ⟨i + 1, hi⟩))
    (arcs_concat : ∀ i : ℕ, ∀ hi : i + 1 < (l1 ++ l2.tail).length,
      D.arc ((l1 ++ l2.tail).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((l1 ++ l2.tail).get ⟨i + 1, hi⟩)) :
    pathWeightAux w (l1 ++ l2.tail) arcs_concat = pathWeightAux w l1 arcs1 * pathWeightAux w l2 arcs2 := by
  induction l1 generalizing l2 with
  | nil => simp at h1_ne
  | cons v1 vs1 ih =>
    cases vs1 with
    | nil => 
      -- l1 = [v1], so l1 ++ l2.tail = v1 :: l2.tail
      simp only [List.singleton_append, List.getLast_singleton] at h_join ⊢
      rw [pathWeightAux_singleton]
      simp only [one_mul]
      -- Need to show pathWeightAux (v1 :: l2.tail) = pathWeightAux l2
      -- Since l2 = v1 :: l2.tail (by h_join), this follows from proof irrelevance
      cases l2 with
      | nil => simp at h2_ne
      | cons v2 vs2 =>
        simp only [List.head_cons] at h_join
        subst h_join
        simp only [List.tail_cons]
    | cons v2 vs2 =>
      -- l1 = v1 :: v2 :: vs2
      simp only [List.cons_append]
      have h1_tail_ne : v2 :: vs2 ≠ [] := List.cons_ne_nil _ _
      have h_join_tail : (v2 :: vs2).getLast h1_tail_ne = l2.head h2_ne := by
        simp only [List.getLast_cons h1_tail_ne] at h_join
        exact h_join
      have arcs1_tail : ∀ i : ℕ, ∀ hi : i + 1 < (v2 :: vs2).length,
          D.arc ((v2 :: vs2).get ⟨i, Nat.lt_of_succ_lt hi⟩) ((v2 :: vs2).get ⟨i + 1, hi⟩) := fun i hi =>
        arcs1 (i + 1) (by simp at hi ⊢; omega)
      have arcs_concat_tail : ∀ i : ℕ, ∀ hi : i + 1 < ((v2 :: vs2) ++ l2.tail).length,
          D.arc (((v2 :: vs2) ++ l2.tail).get ⟨i, Nat.lt_of_succ_lt hi⟩) 
                (((v2 :: vs2) ++ l2.tail).get ⟨i + 1, hi⟩) := fun i hi => by
        have := arcs_concat (i + 1) (by simp at hi ⊢; omega)
        simp only [List.get_eq_getElem, List.cons_append, List.getElem_cons_succ] at this ⊢
        exact this
      have ih_applied := ih l2 h1_tail_ne h2_ne h_join_tail arcs1_tail arcs2 arcs_concat_tail
      have h_eq : pathWeightAux w (v2 :: (vs2 ++ l2.tail)) arcs_concat_tail = 
                  pathWeightAux w (v2 :: vs2) arcs1_tail * pathWeightAux w l2 arcs2 := by
        simpa only [List.cons_append] using ih_applied
      simp only [pathWeightAux, h_eq]
      ring

/-- The weight of a path tuple is the product of weights of its component paths.
    w(𝐩) := w(p₁) w(p₂) ⋯ w(pₖ) -/
noncomputable def pathTupleWeight {D : SimpleDigraph V} {k : ℕ} (w : ArcWeight D K)
    (ps : Fin k → SimpleDigraph.Path D) : K :=
  ∏ i, pathWeight w (ps i)

/-!
## k-Vertices and Path Tuples

Definition def.lgv.path-tups: A k-vertex is a k-tuple of vertices.
A path tuple from 𝐀 to 𝐁 is a k-tuple of paths where pᵢ goes from Aᵢ to Bᵢ.
-/

/-- A k-vertex is a k-tuple of vertices of D.
    Definition def.lgv.path-tups(a) -/
abbrev kVertex (V : Type*) (k : ℕ) := Fin k → V

/-- Permute a k-vertex by a permutation σ: σ(𝐀) = (A_{σ(1)}, A_{σ(2)}, ..., A_{σ(k)}).
    Definition def.lgv.path-tups(b) -/
def permuteKVertex {V : Type*} {k : ℕ} (σ : Equiv.Perm (Fin k)) (A : kVertex V k) : kVertex V k :=
  fun i => A (σ i)

/-- A path tuple from 𝐀 to 𝐁 is a k-tuple (p₁, ..., pₖ) where pᵢ is a path from Aᵢ to Bᵢ.
    Definition def.lgv.path-tups(c) -/
structure PathTuple {V : Type*} [DecidableEq V] (D : SimpleDigraph V) (k : ℕ)
    (A B : kVertex V k) where
  /-- The paths in the tuple -/
  paths : Fin k → SimpleDigraph.Path D
  /-- Each path starts at the corresponding source vertex -/
  starts : ∀ i, (paths i).start = A i
  /-- Each path ends at the corresponding target vertex -/
  finishes : ∀ i, (paths i).finish = B i

@[ext]
lemma PathTuple.ext {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt1 pt2 : PathTuple D k A B)
    (h : ∀ i, pt1.paths i = pt2.paths i) : pt1 = pt2 := by
  cases pt1; cases pt2
  simp only [PathTuple.mk.injEq]
  ext i
  exact h i

/-- Two paths have a vertex in common -/
def pathsIntersect {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) : Prop :=
  ∃ v, v ∈ p.vertices ∧ v ∈ q.vertices

/-- A path tuple is non-intersecting (nipat) if no two paths share a vertex.
    Definition def.lgv.path-tups(d) -/
def PathTuple.isNonIntersecting {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Prop :=
  ∀ i j, i ≠ j → ¬pathsIntersect (pt.paths i) (pt.paths j)

/-- A path tuple is intersecting (ipat) if some two paths share a vertex.
    Definition def.lgv.path-tups(e) -/
def PathTuple.isIntersecting {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Prop :=
  ¬pt.isNonIntersecting

/-!
## The Path Weight Matrix

The matrix M where M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p).
-/

/-- The set of paths from u to v in a path-finite digraph -/
noncomputable def pathsFromTo {V : Type*} [DecidableEq V] (D : SimpleDigraph V)
    (hpf : D.IsPathFinite) (u v : V) : Finset (SimpleDigraph.Path D) :=
  (hpf u v).toFinset

/-- The sum of weights of all paths from u to v.
    ∑_{p : u → v} w(p) -/
noncomputable def pathWeightSum {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) (u v : V) : K :=
  ∑ p ∈ pathsFromTo D hpf u v, pathWeight w p

/-- The path weight matrix M_{i,j} = ∑_{p : Aᵢ → Bⱼ} w(p) -/
noncomputable def pathWeightMatrix {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) {k : ℕ}
    (A B : kVertex V k) : Matrix (Fin k) (Fin k) K :=
  Matrix.of fun i j => pathWeightSum hpf w (A i) (B j)

/-!
## LGV Lemma: Weighted Lattice Version

Theorem thm.lgv.kpaths.wt: For the integer lattice with arc weights w,
det(M) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)
-/

/-- The set of non-intersecting path tuples from 𝐀 to 𝐁 -/
noncomputable def nipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isNonIntersecting}

/-- The set of nipats is finite (follows from path-finiteness) -/
noncomputable def nipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (nipatSet (D := D) A B) := by
  -- The set of all path tuples from A to B is finite
  have h_all_finite : Set.Finite {pt : PathTuple D k A B | True} := by
    let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i => 
      {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
    have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
    have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) := 
      Set.Finite.pi (fun i => h_each_finite i)
    -- Define the map from PathTuple to the pi type
    let f : {pt : PathTuple D k A B | True} → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
      ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
    have hf_inj : Function.Injective f := by
      intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
      simp only [Subtype.mk.injEq, f] at heq ⊢
      cases pt1; cases pt2
      simp only [PathTuple.mk.injEq] at heq ⊢
      exact congrArg Subtype.val heq
    -- The pi type is finite
    have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
    -- Since f is injective and the codomain is finite, the domain is finite
    have h_finite : Finite {pt : PathTuple D k A B | True} := Finite.of_injective f hf_inj
    exact Set.finite_coe_iff.mp h_finite
  exact h_all_finite.subset (fun _ _ => trivial)

/-- Convert nipatSet to Finset using the finiteness proof -/
noncomputable def nipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (nipatSetFinite hpf A B).toFinset

/-- When nipatSet is empty, nipatFinset is empty -/
theorem nipatFinset_of_empty {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k)
    (h : nipatSet (D := D) A B = ∅) :
    nipatFinset hpf A B = ∅ := by
  unfold nipatFinset
  rw [Set.Finite.toFinset_eq_empty]
  exact h

/-- Sum of weights over all nipats from 𝐀 to 𝐁
    Note: σ is not used in this definition since the permutation is already
    encoded in B (which should be permuteKVertex σ B' for some B') -/
noncomputable def nipatWeightSum {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (w : ArcWeight D K) {k : ℕ}
    (A B : kVertex V k) (_σ : Equiv.Perm (Fin k)) : K :=
  ∑ pt ∈ nipatFinset hpf A B, pathTupleWeight w pt.paths

/-!
## Path Tuple Infrastructure for LGV

The key step in the LGV proof is to express the product of sums as a sum over path tuples:
  ∏_j (∑_{p : A_j → B_j} w(p)) = ∑_{pt : PathTuple} pathTupleWeight w pt.paths

This uses `Finset.prod_univ_sum` and a bijection between PathTuple and the piFinset.
-/

/-- Bijection between PathTuple and the piFinset of pathsFromTo.
    This is the key to converting the product of sums to a sum over path tuples. -/
noncomputable def pathTupleEquivPiFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    PathTuple D k A B ≃ (Fintype.piFinset (fun j => pathsFromTo D hpf (A j) (B j))) := by
  refine ⟨?toFun, ?invFun, ?left_inv, ?right_inv⟩
  case toFun =>
    intro pt
    refine ⟨pt.paths, ?_⟩
    simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    intro j
    exact ⟨pt.starts j, pt.finishes j⟩
  case invFun =>
    intro ⟨f, hf⟩
    simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hf
    exact ⟨f, fun j => (hf j).1, fun j => (hf j).2⟩
  case left_inv =>
    intro pt
    rfl
  case right_inv =>
    intro ⟨f, hf⟩
    rfl

/-!
## LGV Lemma: General Digraph Version

Theorem thm.lgv.kpaths.wt-dg: The same result holds for any path-finite acyclic digraph.

The proof uses a sign-reversing involution on intersecting path tuples. The key steps are:

1. Express det(M) using the Leibniz formula as ∑_σ (-1)^σ ∏_i M_{i,σ(i)}
2. Expand each product as a sum over path tuples from 𝐀 to σ(𝐁)
3. Define a sign-reversing involution f on intersecting path tuples:
   - Find the first crowded point (vertex in multiple paths)
   - Pick the smallest index i whose path contains a crowded point
   - Pick the first crowded point v on path p_i
   - Pick the largest index j such that v is on path p_j
   - Exchange the tails of p_i and p_j at v
   - This maps (σ, 𝐩) to (σ ∘ t_{i,j}, 𝐩'), where t_{i,j} is the transposition
4. The involution preserves weight but flips sign, so intersecting tuples cancel
5. Only non-intersecting path tuples (nipats) contribute to the sum
-/

variable {V : Type*} [DecidableEq V]

/-- A crowded point in a path tuple is a vertex that appears in at least two paths -/
def PathTuple.isCrowded {D : SimpleDigraph V} {k : ℕ} {A B : kVertex V k}
    (pt : PathTuple D k A B) (v : V) : Prop :=
  ∃ i j : Fin k, i ≠ j ∧ v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices

/-- An intersecting path tuple has at least one crowded point -/
theorem PathTuple.isIntersecting_iff_exists_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt.isIntersecting ↔ ∃ v, pt.isCrowded v := by
  unfold isIntersecting isNonIntersecting isCrowded pathsIntersect
  push_neg
  constructor
  · intro ⟨i, j, hij, v, hvi, hvj⟩
    exact ⟨v, i, j, hij, hvi, hvj⟩
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    exact ⟨i, j, hij, v, hvi, hvj⟩

/-- The set of path tuples from 𝐀 to σ(𝐁) paired with the permutation σ -/
abbrev pathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Type _ :=
  (σ : Equiv.Perm (Fin k)) × PathTuple D k A (permuteKVertex σ B)

/-- The sign of a path tuple with permutation is (-1)^σ -/
def signOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (sp : pathTupleWithPerm (D := D) A B) : ℤˣ :=
  Equiv.Perm.sign sp.1

/-- The weight of a path tuple with permutation -/
noncomputable def weightOfPathTupleWithPerm {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K) (sp : pathTupleWithPerm (D := D) A B) : K :=
  pathTupleWeight w sp.2.paths

/-- The index of the first occurrence of a vertex in a path's vertex list -/
def firstIndexIn {D : SimpleDigraph V} (p : SimpleDigraph.Path D) (v : V) : ℕ :=
  p.vertices.findIdx (· = v)

-- Helper: findIdx returns the index of the first element satisfying the predicate
/-- Helper lemma: findIdx returns n if element at n satisfies predicate and all before don't.
    This is useful for showing that firstCrowdedIndexOnPath is preserved under signReversing. -/
private lemma findIdx_eq_of_first_satisfies {α : Type*} (l : List α) (p : α → Bool) (n : ℕ) (hn : n < l.length)
    (h_at_n : p l[n] = true)
    (h_before : ∀ m : ℕ, (hm : m < n) → p l[m] = false) :
    l.findIdx p = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero =>
      simp only [List.findIdx_cons, List.getElem_cons_zero] at *
      simp only [h_at_n, Bool.true_eq, ↓reduceIte]
    | succ m =>
      simp only [List.findIdx_cons]
      have h_not_px : p x = false := by
        have := h_before 0 (Nat.zero_lt_succ m)
        simp only [List.getElem_cons_zero] at this
        exact this
      simp only [h_not_px, Bool.false_eq_true, ↓reduceIte]
      apply congrArg (· + 1)
      have hm_lt : m < xs.length := by
        simp only [List.length_cons] at hn; omega
      apply ih m hm_lt
      · simp only [List.getElem_cons_succ] at h_at_n; exact h_at_n
      · intro k hk
        have := h_before (k + 1) (by omega)
        simp only [List.getElem_cons_succ] at this
        exact this

private lemma findIdx_get_eq (l : List V) (v : V) (hv : v ∈ l) :
    l[l.findIdx (· = v)]'(List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩) = v := by
  have h := @List.findIdx_getElem (α := V) (p := (· = v)) (xs := l) 
    (w := List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩)
  simp at h
  exact h

-- Helper: findIdx is bounded by the index of any element satisfying the predicate
omit [DecidableEq V] in
private lemma findIdx_le_of_mem (l : List V) (i : ℕ) (hi : i < l.length)
    (pred : V → Bool) (hp : pred l[i] = true) : l.findIdx pred ≤ i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => 
      simp only [List.getElem_cons_zero] at hp
      simp only [List.findIdx_cons, hp, Bool.true_eq, ↓reduceIte, le_refl]
    | succ j =>
      simp only [List.findIdx_cons]
      simp only [List.getElem_cons_succ] at hp
      cases hx : pred x with
      | true => simp
      | false => 
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp at hi
        have := ih j (by omega : j < xs.length) hp
        omega

-- Helper: if two elements have the same findIdx, they are equal
private lemma findIdx_inj (l : List V) (v w : V) (hv : v ∈ l) (hw : w ∈ l)
    (heq : l.findIdx (· = v) = l.findIdx (· = w)) : v = w := by
  have hv_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hv, by simp⟩
  have hw_lt := List.findIdx_lt_length_of_exists (p := (· = w)) ⟨w, hw, by simp⟩
  have hv_get := findIdx_get_eq l v hv
  have hw_get := findIdx_get_eq l w hw
  have hv_lt' : l.findIdx (· = w) < l.length := by rw [← heq]; exact hv_lt
  have key : l[l.findIdx (· = v)]'hv_lt = l[l.findIdx (· = w)]'hv_lt' := by
    simp only [heq]
  rw [hv_get] at key
  have key2 : l[l.findIdx (· = w)]'hv_lt' = l[l.findIdx (· = w)]'hw_lt := by
    congr 1
  rw [key2, hw_get] at key
  exact key

/-- In an acyclic digraph, the first intersection of two paths (if they intersect)
    is well-defined: it's the same whether we look from path p or path q.
    This is because if they were different, we could form a cycle. -/
theorem first_intersection_unique {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (hp : pathsIntersect p q) :
    ∃! v, v ∈ p.vertices ∧ v ∈ q.vertices ∧
      (∀ v' ∈ p.vertices, v' ∈ q.vertices →
        firstIndexIn p v ≤ firstIndexIn p v') := by
  -- Get a common vertex from the intersection hypothesis
  obtain ⟨v₀, hv₀_p, hv₀_q⟩ := hp
  -- Define the predicate: index i has a common vertex at that position
  let P : ℕ → Prop := fun i => ∃ (hi : i < p.vertices.length), 
    p.vertices[i] ∈ q.vertices
  -- P is decidable
  have hP_dec : DecidablePred P := by
    intro i
    by_cases hi : i < p.vertices.length
    · exact decidable_of_iff (p.vertices[i] ∈ q.vertices) (by
        simp only [P]
        constructor
        · intro h
          exact ⟨hi, h⟩
        · intro ⟨_, h⟩
          convert h)
    · exact isFalse (by simp only [P, not_exists]; intro h; exact absurd h hi)
  -- There exists an index with a common vertex
  have hP_exists : ∃ i, P i := by
    have hfind_lt := List.findIdx_lt_length_of_exists (p := (· = v₀)) ⟨v₀, hv₀_p, by simp⟩
    use p.vertices.findIdx (· = v₀)
    simp only [P]
    refine ⟨hfind_lt, ?_⟩
    have : p.vertices[p.vertices.findIdx (· = v₀)] = v₀ := 
      findIdx_get_eq p.vertices v₀ hv₀_p
    rw [this]
    exact hv₀_q
  -- Find the minimum such index
  let min_idx := Nat.find hP_exists
  -- Get the vertex at this index
  have hmin_P : P min_idx := Nat.find_spec hP_exists
  simp only [P] at hmin_P
  obtain ⟨hmin_lt, hv_q⟩ := hmin_P
  -- Define v as the vertex at min_idx
  let v := p.vertices[min_idx]
  -- v is in p.vertices
  have hv_p : v ∈ p.vertices := List.getElem_mem hmin_lt
  -- Claim: v is the unique first intersection
  use v
  constructor
  · -- v satisfies the properties
    refine ⟨hv_p, hv_q, ?_⟩
    intro v' hv'_p hv'_q
    -- Show firstIndexIn p v ≤ firstIndexIn p v'
    unfold firstIndexIn
    -- The index of v in p is at most min_idx
    have hv_findIdx : p.vertices.findIdx (· = v) ≤ min_idx := by
      apply findIdx_le_of_mem p.vertices min_idx hmin_lt (· = v)
      simp [v]
    -- Also, min_idx ≤ findIdx (· = v') by minimality
    have hmin_le_v' : min_idx ≤ p.vertices.findIdx (· = v') := by
      apply Nat.find_le
      simp only [P]
      have hfind'_lt := List.findIdx_lt_length_of_exists (p := (· = v')) ⟨v', hv'_p, by simp⟩
      refine ⟨hfind'_lt, ?_⟩
      have : p.vertices[p.vertices.findIdx (· = v')] = v' := 
        findIdx_get_eq p.vertices v' hv'_p
      rw [this]
      exact hv'_q
    -- We need findIdx v ≤ findIdx v'
    -- We have findIdx v ≤ min_idx ≤ findIdx v'
    exact le_trans hv_findIdx hmin_le_v'
  · -- Uniqueness
    intro w ⟨hw_p, hw_q, hw_min⟩
    -- w also achieves the minimum
    have hw_findIdx_le : firstIndexIn p w ≤ firstIndexIn p v := hw_min v hv_p hv_q
    have hv_findIdx_le : firstIndexIn p v ≤ firstIndexIn p w := by
      unfold firstIndexIn
      have hv_findIdx : p.vertices.findIdx (· = v) ≤ min_idx := by
        apply findIdx_le_of_mem p.vertices min_idx hmin_lt (· = v)
        simp [v]
      have hmin_le_w : min_idx ≤ p.vertices.findIdx (· = w) := by
        apply Nat.find_le
        simp only [P]
        have hfind'_lt := List.findIdx_lt_length_of_exists (p := (· = w)) ⟨w, hw_p, by simp⟩
        refine ⟨hfind'_lt, ?_⟩
        have : p.vertices[p.vertices.findIdx (· = w)] = w := 
          findIdx_get_eq p.vertices w hw_p
        rw [this]
        exact hw_q
      exact le_trans hv_findIdx hmin_le_w
    have heq_idx : firstIndexIn p v = firstIndexIn p w := le_antisymm hv_findIdx_le hw_findIdx_le
    exact (findIdx_inj p.vertices v w hv_p hw_p heq_idx).symm

/-- Split a path at a vertex v, returning (head ending at v, tail starting at v).
    The head includes v, the tail starts at v. -/
noncomputable def SimpleDigraph.Path.splitAt {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let idx := p.vertices.findIdx (· = v)
  let head := p.vertices.take (idx + 1)
  let tail := p.vertices.drop idx
  have h_idx_lt : idx < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : head ≠ [] := by
    intro h
    have hlen : head.length = 0 := by simp [h]
    simp only [head, List.length_take] at hlen
    omega
  have h_tail_ne : tail ≠ [] := by
    intro h
    have hlen : tail.length = 0 := by rw [h]; rfl
    simp only [tail, List.length_drop] at hlen
    omega
  have h_head_arcs : ∀ i : ℕ, ∀ hi : i + 1 < head.length,
      D.arc (head.get ⟨i, Nat.lt_of_succ_lt hi⟩) (head.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [head, List.length_take, lt_min_iff] at hi
    have hi2 : i + 1 < p.vertices.length := by omega
    have := p.arcs_valid i hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [head]
    rw [List.getElem_take, List.getElem_take]
    exact this
  have h_tail_arcs : ∀ i : ℕ, ∀ hi : i + 1 < tail.length,
      D.arc (tail.get ⟨i, Nat.lt_of_succ_lt hi⟩) (tail.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [tail, List.length_drop] at hi
    have hi2 : idx + i + 1 < p.vertices.length := by omega
    have := p.arcs_valid (idx + i) hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [tail]
    rw [List.getElem_drop, List.getElem_drop]
    simpa only [Nat.add_assoc] using this
  (⟨head, h_head_ne, h_head_arcs⟩, ⟨tail, h_tail_ne, h_tail_arcs⟩)

/-- The head of splitAt ends at v -/
lemma SimpleDigraph.Path.splitAt_head_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.finish = v := by
  unfold splitAt SimpleDigraph.Path.finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_len : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 
               p.vertices.findIdx (· = v) + 1 := by
    rw [List.length_take]
    omega
  have h_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h
    have : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    omega
  rw [List.getLast_eq_getElem]
  have h_idx : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length - 1 = 
               p.vertices.findIdx (· = v) := by
    rw [h_len]; omega
  simp only [h_idx, List.getElem_take]
  have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
  simp at this
  exact this

/-- The tail of splitAt starts at v -/
lemma SimpleDigraph.Path.splitAt_tail_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.start = v := by
  unfold splitAt SimpleDigraph.Path.start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h
    have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen
    omega
  rw [List.head_eq_getElem]
  simp only [List.getElem_drop, Nat.add_zero]
  have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
  simp at this
  exact this

/-- Concatenate two paths where the first path ends at v and the second starts at v.
    The resulting path goes from the start of the first to the end of the second.
    The vertex v appears once in the result (not duplicated). -/
noncomputable def SimpleDigraph.Path.concat {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : SimpleDigraph.Path D :=
  let vertices := p.vertices ++ q.vertices.tail
  have h_ne : vertices ≠ [] := by
    simp only [vertices]
    intro h
    have hlen : (p.vertices ++ q.vertices.tail).length = 0 := by rw [h]; rfl
    simp only [List.length_append, List.length_tail] at hlen
    have hp_ne := p.nonempty
    have hp_len : p.vertices.length ≠ 0 := by
      intro h
      exact hp_ne (List.eq_nil_of_length_eq_zero h)
    omega
  have h_arcs : ∀ i : ℕ, ∀ hi : i + 1 < vertices.length,
      D.arc (vertices.get ⟨i, Nat.lt_of_succ_lt hi⟩) (vertices.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [vertices, List.length_append, List.length_tail] at hi
    simp only [List.get_eq_getElem, vertices]
    by_cases h : i + 1 < p.vertices.length
    · rw [List.getElem_append_left (by omega), List.getElem_append_left h]
      exact p.arcs_valid i h
    · push_neg at h
      by_cases h' : i < p.vertices.length
      · have hi_eq : i = p.vertices.length - 1 := by omega
        have hq_len : 1 < q.vertices.length := by
          have hq_ne := q.nonempty
          by_contra hq_short
          push_neg at hq_short
          have htail_len : q.vertices.tail.length = 0 := by simp only [List.length_tail]; omega
          omega
        rw [List.getElem_append_left h', List.getElem_append_right (by omega)]
        have h1 : p.vertices[i]'h' = p.finish := by 
          simp only [SimpleDigraph.Path.finish, hi_eq, List.getLast_eq_getElem]
        have h_idx : i + 1 - p.vertices.length = 0 := by omega
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'(by simp; omega) = q.vertices[1]'hq_len := by
          simp only [h_idx, List.getElem_tail]
        rw [h1, h2, hpq]
        have hq_arc := q.arcs_valid 0 hq_len
        simp only [List.get_eq_getElem, SimpleDigraph.Path.start, List.head_eq_getElem] at hq_arc ⊢
        exact hq_arc
      · push_neg at h'
        have hi1 : i - p.vertices.length < q.vertices.tail.length := by simp; omega
        have hi2 : i + 1 - p.vertices.length < q.vertices.tail.length := by simp; omega
        rw [List.getElem_append_right (by omega), List.getElem_append_right (by omega)]
        have h1 : q.vertices.tail[i - p.vertices.length]'hi1 = 
                  q.vertices[i - p.vertices.length + 1]'(by simp at hi1; omega) := by 
          simp only [List.getElem_tail]
        have h2 : q.vertices.tail[i + 1 - p.vertices.length]'hi2 = 
                  q.vertices[i + 1 - p.vertices.length + 1]'(by simp at hi2; omega) := by 
          simp only [List.getElem_tail]
        rw [h1, h2]
        have hq_arc := q.arcs_valid (i - p.vertices.length + 1) (by simp at hi2; omega)
        simp only [List.get_eq_getElem] at hq_arc
        convert hq_arc using 2; omega
  ⟨vertices, h_ne, h_arcs⟩

omit [DecidableEq V] in
/-- The concatenation of two paths starts at the first path's start -/
lemma SimpleDigraph.Path.concat_start {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).start = p.start := by
  unfold concat start
  simp only
  exact List.head_append_of_ne_nil (l' := q.vertices.tail) p.nonempty

omit [DecidableEq V] in
/-- The concatenation of two paths ends at the second path's finish -/
lemma SimpleDigraph.Path.concat_finish {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).finish = q.finish := by
  unfold concat finish
  simp only
  have hq_ne := q.nonempty
  by_cases h : q.vertices.tail = []
  · have hq_len : q.vertices.length = 1 := by
      have : q.vertices.tail.length = 0 := by simp [h]
      simp only [List.length_tail] at this
      have hq_pos : 0 < q.vertices.length := List.length_pos_of_ne_nil hq_ne
      omega
    have hq_finish_eq_start : q.vertices.getLast hq_ne = q.vertices.head hq_ne := by
      rw [List.getLast_eq_getElem, List.head_eq_getElem]; congr; omega
    simp only [h, List.append_nil]
    rw [hq_finish_eq_start]
    unfold start at hpq
    rw [← hpq]; unfold finish; rfl
  · rw [List.getLast_append_of_ne_nil _ h, List.getLast_tail h]

omit [DecidableEq V] in
/-- pathWeight is multiplicative over path concatenation. -/
lemma pathWeight_concat {D : SimpleDigraph V} (w : ArcWeight D K) 
    (p q : SimpleDigraph.Path D) (hpq : p.finish = q.start) :
    pathWeight w (p.concat q hpq) = pathWeight w p * pathWeight w q := by
  unfold pathWeight SimpleDigraph.Path.concat
  simp only
  have h_join : p.vertices.getLast p.nonempty = q.vertices.head q.nonempty := by
    unfold SimpleDigraph.Path.finish SimpleDigraph.Path.start at hpq
    exact hpq
  exact pathWeightAux_append w p.vertices q.vertices p.nonempty q.nonempty h_join p.arcs_valid q.arcs_valid _

/-- pathWeight factors over splitAt: the weight of a path is the product of the weights
    of its head and tail after splitting at any vertex. -/
lemma pathWeight_splitAt {D : SimpleDigraph V} (w : ArcWeight D K) 
    (p : SimpleDigraph.Path D) (v : V) (hv : v ∈ p.vertices) :
    pathWeight w p = pathWeight w (p.splitAt v hv).1 * pathWeight w (p.splitAt v hv).2 := by
  unfold pathWeight SimpleDigraph.Path.splitAt
  simp only
  set idx := p.vertices.findIdx (· = v) with h_idx_def
  set head := p.vertices.take (idx + 1) with h_head_def
  set tail := p.vertices.drop idx with h_tail_def
  have h_idx_lt : idx < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : head ≠ [] := by
    intro h
    have hlen : head.length = 0 := by simp [h]
    simp only [h_head_def, List.length_take] at hlen
    omega
  have h_tail_ne : tail ≠ [] := by
    intro h
    have hlen : tail.length = 0 := by rw [h]; rfl
    simp only [h_tail_def, List.length_drop] at hlen
    omega
  -- The key: head ++ tail.tail = p.vertices
  have h_concat : head ++ tail.tail = p.vertices := by
    simp only [h_head_def, h_tail_def]
    have htail : (p.vertices.drop idx).tail = p.vertices.drop (idx + 1) := List.tail_drop
    rw [htail, List.take_append_drop]
  -- The join condition
  have h_head_last : head.getLast h_head_ne = v := by
    simp only [h_head_def]
    rw [List.getLast_eq_getElem]
    have h_len : (p.vertices.take (idx + 1)).length = idx + 1 := by
      rw [List.length_take]; omega
    simp only [h_len]
    rw [List.getElem_take]
    have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
    simp at this
    exact this
  have h_tail_head : tail.head h_tail_ne = v := by
    simp only [h_tail_def]
    rw [List.head_eq_getElem]
    simp only [List.getElem_drop, Nat.add_zero]
    have := @List.findIdx_getElem V (· = v) p.vertices h_idx_lt
    simp at this
    exact this
  have h_join : head.getLast h_head_ne = tail.head h_tail_ne := by
    rw [h_head_last, h_tail_head]
  -- Arc proofs
  have h_arcs_head : ∀ i : ℕ, ∀ hi : i + 1 < head.length,
      D.arc (head.get ⟨i, Nat.lt_of_succ_lt hi⟩) (head.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [h_head_def, List.length_take, lt_min_iff] at hi
    have hi2 : i + 1 < p.vertices.length := by omega
    have := p.arcs_valid i hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [h_head_def]
    rw [List.getElem_take, List.getElem_take]
    exact this
  have h_arcs_tail : ∀ i : ℕ, ∀ hi : i + 1 < tail.length,
      D.arc (tail.get ⟨i, Nat.lt_of_succ_lt hi⟩) (tail.get ⟨i + 1, hi⟩) := by
    intro i hi
    simp only [h_tail_def, List.length_drop] at hi
    have hi2 : idx + i + 1 < p.vertices.length := by omega
    have := p.arcs_valid (idx + i) hi2
    simp only [List.get_eq_getElem] at this ⊢
    simp only [h_tail_def]
    rw [List.getElem_drop, List.getElem_drop]
    simpa only [Nat.add_assoc] using this
  -- Construct arcs_concat from p.arcs_valid using h_concat
  have h_len_eq : (head ++ tail.tail).length = p.vertices.length := by
    rw [h_concat]
  have h_arcs_concat : ∀ i : ℕ, ∀ hi : i + 1 < (head ++ tail.tail).length,
      D.arc ((head ++ tail.tail).get ⟨i, Nat.lt_of_succ_lt hi⟩) 
            ((head ++ tail.tail).get ⟨i + 1, hi⟩) := by
    intro i hi
    have hi' : i + 1 < p.vertices.length := h_len_eq ▸ hi
    have := p.arcs_valid i hi'
    simp only [List.get_eq_getElem] at this ⊢
    convert this using 2
  -- Apply pathWeightAux_append
  have h_main := pathWeightAux_append w head tail h_head_ne h_tail_ne h_join h_arcs_head h_arcs_tail h_arcs_concat
  -- Connect LHS to RHS using h_concat
  calc pathWeightAux w p.vertices p.arcs_valid 
      = pathWeightAux w (head ++ tail.tail) h_arcs_concat := 
          pathWeightAux_eq_of_eq w h_concat.symm _ _
    _ = pathWeightAux w head h_arcs_head * pathWeightAux w tail h_arcs_tail := h_main
    _ = pathWeightAux w head _ * pathWeightAux w tail _ := rfl

/-- The head of splitAt starts at the original path's start -/
lemma SimpleDigraph.Path.splitAt_head_start {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).1.start = p.start := by
  unfold splitAt start
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_head_ne : p.vertices.take (p.vertices.findIdx (· = v) + 1) ≠ [] := by
    intro h; have hlen : (p.vertices.take (p.vertices.findIdx (· = v) + 1)).length = 0 := by simp [h]
    simp only [List.length_take] at hlen; omega
  exact List.head_take h_head_ne

/-- The tail of splitAt ends at the original path's finish -/
lemma SimpleDigraph.Path.splitAt_tail_finish {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : (p.splitAt v hv).2.finish = p.finish := by
  unfold splitAt finish
  simp only
  have h_idx_lt : p.vertices.findIdx (· = v) < p.vertices.length := 
    List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_drop_ne : p.vertices.drop (p.vertices.findIdx (· = v)) ≠ [] := by
    intro h; have hlen : (p.vertices.drop (p.vertices.findIdx (· = v))).length = 0 := by rw [h]; rfl
    simp only [List.length_drop] at hlen; omega
  rw [List.getLast_drop h_drop_ne]

/-- Exchange the tails of two paths at a common vertex.
    If p goes A → v → B and q goes A' → v → B', then after exchange:
    p' goes A → v → B' and q' goes A' → v → B -/
noncomputable def exchangeTails {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    SimpleDigraph.Path D × SimpleDigraph.Path D :=
  let sp_p := p.splitAt v hv_p
  let sp_q := q.splitAt v hv_q
  let head_p := sp_p.1
  let tail_p := sp_p.2
  let head_q := sp_q.1
  let tail_q := sp_q.2
  have h1 : head_p.finish = tail_q.start := by
    have hp := SimpleDigraph.Path.splitAt_head_finish p v hv_p
    have hq := SimpleDigraph.Path.splitAt_tail_start q v hv_q
    simp only [head_p, sp_p, tail_q, sp_q] at *
    rw [hp, hq]
  have h2 : head_q.finish = tail_p.start := by
    have hp := SimpleDigraph.Path.splitAt_tail_start p v hv_p
    have hq := SimpleDigraph.Path.splitAt_head_finish q v hv_q
    simp only [tail_p, sp_p, head_q, sp_q] at *
    rw [hq, hp]
  (SimpleDigraph.Path.concat head_p tail_q h1, SimpleDigraph.Path.concat head_q tail_p h2)

/-- The first path from exchangeTails starts at the original first path's start -/
lemma exchangeTails_fst_start {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.start = p.start := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_start]
  exact SimpleDigraph.Path.splitAt_head_start p v hv_p

/-- The first path from exchangeTails ends at the original second path's finish -/
lemma exchangeTails_fst_finish {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.finish = q.finish := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_finish]
  exact SimpleDigraph.Path.splitAt_tail_finish q v hv_q

/-- The second path from exchangeTails starts at the original second path's start -/
lemma exchangeTails_snd_start {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.start = q.start := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_start]
  exact SimpleDigraph.Path.splitAt_head_start q v hv_q

/-- The second path from exchangeTails ends at the original first path's finish -/
lemma exchangeTails_snd_finish {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.finish = p.finish := by
  unfold exchangeTails
  simp only
  rw [SimpleDigraph.Path.concat_finish]
  exact SimpleDigraph.Path.splitAt_tail_finish p v hv_p

omit [DecidableEq V] in
/-- If p.finish = v, then v is in (concat p q).vertices -/
lemma SimpleDigraph.Path.concat_mem_of_finish {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : p.finish ∈ (p.concat q hpq).vertices := by
  unfold concat
  simp only
  apply List.mem_append_left
  exact List.getLast_mem p.nonempty

/-- The crowded point v is in the first exchanged path's vertices.
    Since head_p ends at v, and concat uses head_p.vertices ++ tail_q.vertices.tail,
    v is in the first path. -/
lemma exchangeTails_fst_mem_v {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    v ∈ (exchangeTails p q v hv_p hv_q).1.vertices := by
  unfold exchangeTails
  simp only
  apply List.mem_append_left
  have h := SimpleDigraph.Path.splitAt_head_finish p v hv_p
  unfold SimpleDigraph.Path.finish at h
  have hmem := List.getLast_mem (p.splitAt v hv_p).1.nonempty
  rw [h] at hmem
  exact hmem

/-- The crowded point v is in the second exchanged path's vertices.
    Since head_q ends at v, and concat uses head_q.vertices ++ tail_p.vertices.tail,
    v is in the second path. -/
lemma exchangeTails_snd_mem_v {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    v ∈ (exchangeTails p q v hv_p hv_q).2.vertices := by
  unfold exchangeTails
  simp only
  apply List.mem_append_left
  have h := SimpleDigraph.Path.splitAt_head_finish q v hv_q
  unfold SimpleDigraph.Path.finish at h
  have hmem := List.getLast_mem (q.splitAt v hv_q).1.nonempty
  rw [h] at hmem
  exact hmem

/-- Exchanging tails twice at the same vertex returns the original paths.
    This is the key involutivity property needed for the sign-reversing involution.
    
    **Proof idea:** When we exchange tails at v:
    - p becomes head_p ++ tail_q
    - q becomes head_q ++ tail_p
    
    When we exchange again at v:
    - head_p ++ tail_q splits at v into (head_p, tail_q) 
    - head_q ++ tail_p splits at v into (head_q, tail_p)
    - Exchanging gives (head_p ++ tail_p, head_q ++ tail_q) = (p, q)
    
    The key lemma is that splitAt(concat(head, tail), v) = (head, tail) when head ends at v
    and tail starts at v, and v appears only once in head (which holds for acyclic paths). -/
-- Helper: findIdx on head after splitAt equals head.length - 1
private lemma splitAt_head_findIdx_eq (l : List V) (v : V) (hv : v ∈ l) :
    let idx := l.findIdx (· = v)
    let head := l.take (idx + 1)
    head.findIdx (· = v) = head.length - 1 := by
  simp only
  have h_idx_lt : l.findIdx (· = v) < l.length := List.findIdx_lt_length_of_exists ⟨v, hv, by simp⟩
  have h_len : (l.take (l.findIdx (· = v) + 1)).length = l.findIdx (· = v) + 1 := by
    rw [List.length_take]; omega
  have h_getElem : l[l.findIdx (· = v)]'h_idx_lt = v := by
    have := @List.findIdx_getElem V (· = v) l h_idx_lt
    simp at this; exact this
  have h_head_getElem : (l.take (l.findIdx (· = v) + 1))[l.findIdx (· = v)]'(by rw [h_len]; omega) = v := by
    rw [List.getElem_take]; exact h_getElem
  have hv_mem_head : v ∈ l.take (l.findIdx (· = v) + 1) := by
    rw [List.mem_iff_getElem]
    exact ⟨l.findIdx (· = v), by rw [h_len]; omega, h_head_getElem⟩
  have h_head_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hv_mem_head, by simp⟩
  have h_le : (l.take (l.findIdx (· = v) + 1)).findIdx (· = v) ≤ l.findIdx (· = v) := by
    by_contra h_neg; push_neg at h_neg; omega
  have h_ge : l.findIdx (· = v) ≤ (l.take (l.findIdx (· = v) + 1)).findIdx (· = v) := by
    by_contra h_neg; push_neg at h_neg
    have h_found : (l.take (l.findIdx (· = v) + 1))[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'h_head_lt = v := by
      have := @List.findIdx_getElem V (· = v) (l.take (l.findIdx (· = v) + 1)) h_head_lt
      simp only [decide_eq_true_eq] at this; exact this
    have h_in_l : l[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'(by omega) = v := by
      have : (l.take (l.findIdx (· = v) + 1))[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'h_head_lt = 
             l[(l.take (l.findIdx (· = v) + 1)).findIdx (· = v)]'(by omega) := by
        rw [List.getElem_take]
      rw [← this]; exact h_found
    have h_not_before : ∀ j, (hj : j < l.findIdx (· = v)) → ¬(l[j]'(Nat.lt_trans hj h_idx_lt) = v) := by
      intro j hj
      have := List.not_of_lt_findIdx hj
      simp at this; exact this
    exact h_not_before _ h_neg h_in_l
  have h_eq := le_antisymm h_le h_ge
  rw [h_eq, h_len]; omega

-- Key lemma: splitAt on concatenated path gives back original components
private lemma splitAt_concat_vertices_eq (head_verts tail_verts : List V) (v : V)
    (hhead_ne : head_verts ≠ [])
    (htail_ne : tail_verts ≠ [])
    (hhead_last : head_verts.getLast hhead_ne = v)
    (htail_first : tail_verts.head htail_ne = v)
    (hhead_findIdx : head_verts.findIdx (· = v) = head_verts.length - 1) :
    let combined := head_verts ++ tail_verts.tail
    let idx := combined.findIdx (· = v)
    (combined.take (idx + 1), combined.drop idx) = (head_verts, tail_verts) := by
  simp only
  have hv_mem : v ∈ head_verts := by rw [← hhead_last]; exact List.getLast_mem hhead_ne
  have h_findIdx : (head_verts ++ tail_verts.tail).findIdx (· = v) = head_verts.length - 1 := by
    rw [List.findIdx_append]
    have h_lt : head_verts.findIdx (· = v) < head_verts.length := by
      exact List.findIdx_lt_length_of_exists ⟨v, hv_mem, by simp⟩
    simp only [h_lt, ↓reduceIte]
    exact hhead_findIdx
  rw [h_findIdx]
  have h_len : head_verts.length - 1 + 1 = head_verts.length := by
    have := List.length_pos_of_ne_nil hhead_ne; omega
  have h_take : (head_verts ++ tail_verts.tail).take head_verts.length = head_verts := List.take_left
  have hhead_len : 0 < head_verts.length := List.length_pos_of_ne_nil hhead_ne
  have h_drop : (head_verts ++ tail_verts.tail).drop (head_verts.length - 1) = tail_verts := by
    rw [List.drop_append]
    have h_drop_head : head_verts.drop (head_verts.length - 1) = [head_verts.getLast hhead_ne] := by
      rw [List.drop_eq_getElem_cons (by omega)]
      simp only [List.getLast_eq_getElem]
      congr 1
      rw [List.drop_eq_nil_of_le (by omega)]
    rw [h_drop_head]
    have h_sub : head_verts.length - 1 - head_verts.length = 0 := by omega
    simp only [h_sub, List.drop_zero, List.singleton_append]
    rw [hhead_last, ← htail_first]
    exact List.cons_head_tail htail_ne
  rw [h_len, h_take, h_drop]

-- Helper lemma: splitAt vertices for the head
private lemma splitAt_fst_vertices {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : 
    (p.splitAt v hv).1.vertices = p.vertices.take (p.vertices.findIdx (· = v) + 1) := by
  unfold SimpleDigraph.Path.splitAt
  simp only

-- Helper lemma: splitAt vertices for the tail
private lemma splitAt_snd_vertices {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) : 
    (p.splitAt v hv).2.vertices = p.vertices.drop (p.vertices.findIdx (· = v)) := by
  unfold SimpleDigraph.Path.splitAt
  simp only

-- Helper lemma: concat vertices
omit [DecidableEq V] in
private lemma concat_vertices {D : SimpleDigraph V} (p q : SimpleDigraph.Path D) 
    (hpq : p.finish = q.start) : (p.concat q hpq).vertices = p.vertices ++ q.vertices.tail := by
  unfold SimpleDigraph.Path.concat
  simp only

-- Helper lemma: paths are determined by their vertices
omit [DecidableEq V] in
private lemma path_ext {D : SimpleDigraph V} (p q : SimpleDigraph.Path D)
    (h : p.vertices = q.vertices) : p = q := by
  cases p; cases q
  simp only [SimpleDigraph.Path.mk.injEq] at h ⊢
  exact h

-- Helper lemma: exchangeTails first component vertices
private lemma exchangeTails_fst_vertices {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).1.vertices = 
    (p.splitAt v hv_p).1.vertices ++ (q.splitAt v hv_q).2.vertices.tail := by
  unfold exchangeTails
  simp only [concat_vertices]

-- Helper lemma: exchangeTails second component vertices  
private lemma exchangeTails_snd_vertices {D : SimpleDigraph V}
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    (exchangeTails p q v hv_p hv_q).2.vertices = 
    (q.splitAt v hv_q).1.vertices ++ (p.splitAt v hv_p).2.vertices.tail := by
  unfold exchangeTails
  simp only [concat_vertices]

-- concat of splitAt components gives back original
private lemma concat_splitAt_vertices_eq {D : SimpleDigraph V} (p : SimpleDigraph.Path D) 
    (v : V) (hv : v ∈ p.vertices) :
    (p.splitAt v hv).1.vertices ++ (p.splitAt v hv).2.vertices.tail = p.vertices := by
  rw [splitAt_fst_vertices, splitAt_snd_vertices]
  have h1 : (p.vertices.drop (p.vertices.findIdx (· = v))).tail = 
            p.vertices.drop (p.vertices.findIdx (· = v) + 1) := List.tail_drop
  simp only [h1]
  exact List.take_append_drop _ _

lemma exchangeTails_involutive {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let q' := (exchangeTails p q v hv_p hv_q).2
    let hv_p' : v ∈ p'.vertices := exchangeTails_fst_mem_v p q v hv_p hv_q
    let hv_q' : v ∈ q'.vertices := exchangeTails_snd_mem_v p q v hv_p hv_q
    exchangeTails p' q' v hv_p' hv_q' = (p, q) := by
  simp only
  -- Define the components
  set head_p := (p.splitAt v hv_p).1 with h_head_p_def
  set tail_p := (p.splitAt v hv_p).2 with h_tail_p_def
  set head_q := (q.splitAt v hv_q).1 with h_head_q_def
  set tail_q := (q.splitAt v hv_q).2 with h_tail_q_def
  -- Key facts about the splitAt components
  have h_head_p_last : head_p.vertices.getLast head_p.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish p v hv_p
  have h_tail_p_first : tail_p.vertices.head tail_p.nonempty = v := 
    SimpleDigraph.Path.splitAt_tail_start p v hv_p
  have h_head_q_last : head_q.vertices.getLast head_q.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish q v hv_q
  have h_tail_q_first : tail_q.vertices.head tail_q.nonempty = v := 
    SimpleDigraph.Path.splitAt_tail_start q v hv_q
  -- The head findIdx properties
  have h_head_p_findIdx : head_p.vertices.findIdx (· = v) = head_p.vertices.length - 1 := by
    rw [splitAt_fst_vertices]
    exact splitAt_head_findIdx_eq p.vertices v hv_p
  have h_head_q_findIdx : head_q.vertices.findIdx (· = v) = head_q.vertices.length - 1 := by
    rw [splitAt_fst_vertices]
    exact splitAt_head_findIdx_eq q.vertices v hv_q
  -- p' = head_p ++ tail_q.tail, q' = head_q ++ tail_p.tail
  have h_p'_verts : (exchangeTails p q v hv_p hv_q).1.vertices = 
                    head_p.vertices ++ tail_q.vertices.tail := exchangeTails_fst_vertices p q v hv_p hv_q
  have h_q'_verts : (exchangeTails p q v hv_p hv_q).2.vertices = 
                    head_q.vertices ++ tail_p.vertices.tail := exchangeTails_snd_vertices p q v hv_p hv_q
  -- Use splitAt_concat_vertices_eq to show splitAt on p' gives (head_p, tail_q)
  have h_split_p' := splitAt_concat_vertices_eq 
    head_p.vertices tail_q.vertices v 
    head_p.nonempty tail_q.nonempty 
    h_head_p_last h_tail_q_first h_head_p_findIdx
  have h_split_q' := splitAt_concat_vertices_eq 
    head_q.vertices tail_p.vertices v 
    head_q.nonempty tail_p.nonempty 
    h_head_q_last h_tail_p_first h_head_q_findIdx
  -- Extract the components from the split
  have h_p'_split_fst : ((exchangeTails p q v hv_p hv_q).1.splitAt v 
      (exchangeTails_fst_mem_v p q v hv_p hv_q)).1.vertices = head_p.vertices := by
    rw [splitAt_fst_vertices, h_p'_verts]
    have := h_split_p'
    simp only at this
    exact congr_arg Prod.fst this
  have h_p'_split_snd : ((exchangeTails p q v hv_p hv_q).1.splitAt v 
      (exchangeTails_fst_mem_v p q v hv_p hv_q)).2.vertices = tail_q.vertices := by
    rw [splitAt_snd_vertices, h_p'_verts]
    have := h_split_p'
    simp only at this
    exact congr_arg Prod.snd this
  have h_q'_split_fst : ((exchangeTails p q v hv_p hv_q).2.splitAt v 
      (exchangeTails_snd_mem_v p q v hv_p hv_q)).1.vertices = head_q.vertices := by
    rw [splitAt_fst_vertices, h_q'_verts]
    have := h_split_q'
    simp only at this
    exact congr_arg Prod.fst this
  have h_q'_split_snd : ((exchangeTails p q v hv_p hv_q).2.splitAt v 
      (exchangeTails_snd_mem_v p q v hv_p hv_q)).2.vertices = tail_p.vertices := by
    rw [splitAt_snd_vertices, h_q'_verts]
    have := h_split_q'
    simp only at this
    exact congr_arg Prod.snd this
  -- Now show the result equals (p, q)
  apply Prod.ext
  · -- First component
    apply path_ext
    rw [exchangeTails_fst_vertices, h_p'_split_fst, h_q'_split_snd]
    exact concat_splitAt_vertices_eq p v hv_p
  · -- Second component
    apply path_ext
    rw [exchangeTails_snd_vertices, h_q'_split_fst, h_p'_split_snd]
    exact concat_splitAt_vertices_eq q v hv_q

/-- The head of path p (vertices before v) is preserved after exchangeTails.
    This is the key lemma for proving that the canonical selection is invariant. -/
lemma exchangeTails_head_eq {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let hv_p' := exchangeTails_fst_mem_v p q v hv_p hv_q
    (p'.splitAt v hv_p').1.vertices = (p.splitAt v hv_p).1.vertices := by
  simp only
  rw [splitAt_fst_vertices, splitAt_fst_vertices]
  rw [exchangeTails_fst_vertices]
  -- The head of p' = head_p ++ tail_q.tail is just head_p (up to v)
  -- We need: (head_p ++ tail_q.tail).take (findIdx (· = v) + 1) = head_p.take (findIdx (· = v) + 1)
  have h_head_p := splitAt_fst_vertices p v hv_p
  have h_tail_q := splitAt_snd_vertices q v hv_q
  -- head_p.vertices ends with v, so findIdx in the concatenation finds v at the same position
  have h_head_p_last : (p.splitAt v hv_p).1.vertices.getLast (p.splitAt v hv_p).1.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish p v hv_p
  have h_findIdx_head : (p.splitAt v hv_p).1.vertices.findIdx (· = v) = 
      (p.splitAt v hv_p).1.vertices.length - 1 := splitAt_head_findIdx_eq p.vertices v hv_p
  -- In the concatenation, findIdx finds v at the same position (end of head_p)
  have h_concat := splitAt_concat_vertices_eq 
    (p.splitAt v hv_p).1.vertices (q.splitAt v hv_q).2.vertices v
    (p.splitAt v hv_p).1.nonempty (q.splitAt v hv_q).2.nonempty
    h_head_p_last (SimpleDigraph.Path.splitAt_tail_start q v hv_q)
    h_findIdx_head
  simp only at h_concat
  exact congr_arg Prod.fst h_concat

/-- Exchanging tails preserves the total weight.


    **Proof outline:** The key insight is that `pathWeight` is multiplicative over path
    concatenation: if p = p₁ ++ p₂ (concatenation at a shared vertex), then
    w(p) = w(p₁) * w(p₂).

    When we exchange tails at vertex v:
    - p has weight w(p_head) * w(p_tail) where p_head ends at v and p_tail starts at v
    - q has weight w(q_head) * w(q_tail) where q_head ends at v and q_tail starts at v
    - p' = p_head ++ q_tail has weight w(p_head) * w(q_tail)
    - q' = q_head ++ p_tail has weight w(q_head) * w(p_tail)

    Thus: w(p) * w(q) = w(p_head) * w(p_tail) * w(q_head) * w(q_tail)
                      = w(p_head) * w(q_tail) * w(q_head) * w(p_tail)  (by commutativity)
                      = w(p') * w(q')

    The proof uses multiplicativity of `pathWeight` over path concatenation
    and commutativity of multiplication in K. -/
theorem exchangeTails_weight {D : SimpleDigraph V}
    (w : ArcWeight D K) (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    pathWeight w p * pathWeight w q =
      pathWeight w (exchangeTails p q v hv_p hv_q).1 *
      pathWeight w (exchangeTails p q v hv_p hv_q).2 := by
  -- Split both paths at v
  let sp_p := p.splitAt v hv_p
  let sp_q := q.splitAt v hv_q
  let head_p := sp_p.1
  let tail_p := sp_p.2
  let head_q := sp_q.1
  let tail_q := sp_q.2
  -- By pathWeight_splitAt:
  -- pathWeight p = pathWeight head_p * pathWeight tail_p
  -- pathWeight q = pathWeight head_q * pathWeight tail_q
  have hp : pathWeight w p = pathWeight w head_p * pathWeight w tail_p := pathWeight_splitAt w p v hv_p
  have hq : pathWeight w q = pathWeight w head_q * pathWeight w tail_q := pathWeight_splitAt w q v hv_q
  -- exchangeTails gives us (head_p ++ tail_q, head_q ++ tail_p)
  -- By pathWeight_concat:
  -- pathWeight (head_p ++ tail_q) = pathWeight head_p * pathWeight tail_q
  -- pathWeight (head_q ++ tail_p) = pathWeight head_q * pathWeight tail_p
  unfold exchangeTails
  simp only
  have h1 : head_p.finish = tail_q.start := by
    rw [SimpleDigraph.Path.splitAt_head_finish, SimpleDigraph.Path.splitAt_tail_start]
  have h2 : head_q.finish = tail_p.start := by
    rw [SimpleDigraph.Path.splitAt_head_finish, SimpleDigraph.Path.splitAt_tail_start]
  rw [pathWeight_concat w head_p tail_q h1, pathWeight_concat w head_q tail_p h2]
  rw [hp, hq]
  ring

/-!
### Deterministic Intersection Data Selection

The sign-reversing involution requires selecting intersection data (i, j, v) deterministically
so that applying the involution twice returns the original path tuple. The algorithm from
the LaTeX source is:
1. Pick the smallest i such that path i contains a crowded point
2. Pick the first crowded point v on path i (by position in the path)
3. Pick the largest j such that v is on path j

This selection is preserved under the involution because:
- The heads of paths i and j (before v) are unchanged
- So v is still the first crowded point on path i
- And j is still the largest index containing v
-/

/-- The set of path indices that have a crowded vertex (shared with another path) -/
def PathTuple.crowdedPathIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) : Finset (Fin k) :=
  Finset.univ.filter fun i =>
    ∃ j : Fin k, i ≠ j ∧ ((pt.paths i).vertices.toFinset ∩ (pt.paths j).vertices.toFinset).Nonempty

/-- The set of crowded vertices on a specific path -/
def PathTuple.crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (i : Fin k) : Finset V :=
  (pt.paths i).vertices.toFinset.filter fun v =>
    ∃ j : Fin k, i ≠ j ∧ v ∈ (pt.paths j).vertices

/-- The set of path indices that contain a given vertex -/
def PathTuple.pathIndicesContaining {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (v : V) : Finset (Fin k) :=
  Finset.univ.filter fun i => v ∈ (pt.paths i).vertices

/-- The index of the first crowded vertex on a path (by position) -/
def PathTuple.firstCrowdedIndexOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (i : Fin k) : ℕ :=
  (pt.paths i).vertices.findIdx fun v => v ∈ pt.crowdedVerticesOnPath i

/-- An intersecting path tuple has nonempty crowdedPathIndices -/
lemma PathTuple.isIntersecting_iff_crowdedPathIndices_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt.isIntersecting ↔ pt.crowdedPathIndices.Nonempty := by
  rw [PathTuple.isIntersecting_iff_exists_crowded]
  constructor
  · intro ⟨v, i, j, hij, hvi, hvj⟩
    use i
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij, v
    simp only [Finset.mem_inter, List.mem_toFinset]
    exact ⟨hvi, hvj⟩
  · intro ⟨i, hi⟩
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    obtain ⟨j, hij, v, hv⟩ := hi
    simp only [Finset.mem_inter, List.mem_toFinset] at hv
    exact ⟨v, i, j, hij, hv.1, hv.2⟩

/-- Key lemma: if i is the smallest crowded path index and v is a crowded vertex on path i,
    then all other paths containing v have index > i -/
lemma PathTuple.crowded_vertex_other_paths_gt {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi_min : ∀ i' ∈ pt.crowdedPathIndices, i ≤ i')
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i)
    (j : Fin k) (hj : j ∈ pt.pathIndicesContaining v) (hjne : j ≠ i) :
    i < j := by
  simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  obtain ⟨hvi, j', hij', hvj'⟩ := hv
  by_contra h
  push_neg at h
  have hj_lt : j < i := lt_of_le_of_ne h hjne
  have hj_crowded : j ∈ pt.crowdedPathIndices := by
    simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use i
    constructor
    · exact hjne
    · use v
      simp only [Finset.mem_inter, List.mem_toFinset]
      exact ⟨hj, hvi⟩
  have hi_le_j := hi_min j hj_crowded
  omega

/-!
### Canonical Intersection Data Selection

The sign-reversing involution requires selecting intersection data (i, j, v) canonically
so that applying the involution twice returns the original path tuple. The algorithm is:
1. i = the smallest path index that contains a crowded point
2. v = the first crowded point on path i (by position in the vertex list)
3. j = the largest path index that contains v

This selection is preserved under the involution because:
- The heads of paths i and j (before v) are unchanged by exchangeTails
- So v is still the first crowded point on path i
- And j is still the largest index containing v
-/

/-- Get the smallest crowded path index. -/
def PathTuple.minCrowdedPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  pt.crowdedPathIndices.min' (pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)

/-- The minimum crowded path index is in crowdedPathIndices -/
lemma PathTuple.minCrowdedPathIndex_mem {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.minCrowdedPathIndex hip ∈ pt.crowdedPathIndices :=
  Finset.min'_mem _ _

/-- The minimum crowded path index is minimal -/
lemma PathTuple.minCrowdedPathIndex_le {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.minCrowdedPathIndex hip ≤ i :=
  Finset.min'_le _ _ hi

/-- The crowded vertices on the minimum path are nonempty -/
lemma PathTuple.crowdedVerticesOnPath_minCrowded_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    (pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip)).Nonempty := by
  have hi_mem := pt.minCrowdedPathIndex_mem hip
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi_mem
  obtain ⟨j, hij, v, hv⟩ := hi_mem
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩

/-- Get the first crowded vertex on the minimum crowded path.
    This uses List.find? to get the first vertex in the path that is crowded. -/
noncomputable def PathTuple.firstCrowdedVertex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : V :=
  let i := pt.minCrowdedPathIndex hip
  let crowded := pt.crowdedVerticesOnPath i
  -- Find the first vertex in the path that is crowded
  ((pt.paths i).vertices.find? (fun v => v ∈ crowded)).get (by
    -- Prove that find? returns some
    have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
    obtain ⟨v, hv⟩ := hne
    apply List.find?_isSome.mpr
    use v
    constructor
    · -- v is in the path
      simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
      exact hv.1
    · -- v ∈ crowded
      simp only [decide_eq_true_eq]
      exact hv)

/-- The first crowded vertex is in the minimum crowded path -/
lemma PathTuple.firstCrowdedVertex_mem_path {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ (pt.paths (pt.minCrowdedPathIndex hip)).vertices := by
  unfold firstCrowdedVertex
  have h := Option.get_mem (by
    have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
    obtain ⟨v, hv⟩ := hne
    simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
    apply List.find?_isSome.mpr
    use v, hv.1
    simp only [decide_eq_true_eq, crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    exact hv : ((pt.paths (pt.minCrowdedPathIndex hip)).vertices.find? 
      (fun v => v ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip))).isSome)
  exact List.mem_of_find?_eq_some h

/-- The first crowded vertex is in the crowdedVerticesOnPath set -/
lemma PathTuple.firstCrowdedVertex_mem_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip) := by
  unfold firstCrowdedVertex
  have hne := pt.crowdedVerticesOnPath_minCrowded_nonempty hip
  obtain ⟨v, hv⟩ := hne
  have h_isSome : ((pt.paths (pt.minCrowdedPathIndex hip)).vertices.find? 
      (fun v => v ∈ pt.crowdedVerticesOnPath (pt.minCrowdedPathIndex hip))).isSome := by
    apply List.find?_isSome.mpr
    use v
    constructor
    · simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
      exact hv.1
    · simp only [decide_eq_true_eq]
      exact hv
  have h := Option.get_mem h_isSome
  have hprop := List.find?_some h
  simp only [decide_eq_true_eq] at hprop
  exact hprop

/-- The first crowded vertex is crowded (shared with another path) -/
lemma PathTuple.firstCrowdedVertex_is_crowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    ∃ j : Fin k, pt.minCrowdedPathIndex hip ≠ j ∧ 
      pt.firstCrowdedVertex hip ∈ (pt.paths j).vertices := by
  have hcrowded := pt.firstCrowdedVertex_mem_crowded hip
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hcrowded
  exact hcrowded.2

/-- The set of path indices containing the first crowded vertex (excluding the minimum) -/
noncomputable def PathTuple.otherPathsContainingFirstCrowded {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Finset (Fin k) :=
  (pt.pathIndicesContaining (pt.firstCrowdedVertex hip)).filter 
    (fun j => j ≠ pt.minCrowdedPathIndex hip)

/-- The set of other paths containing the first crowded vertex is nonempty -/
lemma PathTuple.otherPathsContainingFirstCrowded_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    (pt.otherPathsContainingFirstCrowded hip).Nonempty := by
  obtain ⟨j, hij, hvj⟩ := pt.firstCrowdedVertex_is_crowded hip
  use j
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter, pathIndicesContaining,
    Finset.mem_univ, true_and]
  exact ⟨hvj, hij.symm⟩

/-- Get the largest path index containing the first crowded vertex (other than the minimum) -/
noncomputable def PathTuple.maxOtherPathIndex {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) : Fin k :=
  (pt.otherPathsContainingFirstCrowded hip).max' (pt.otherPathsContainingFirstCrowded_nonempty hip)

/-- The max other path index is different from the min crowded path index -/
lemma PathTuple.maxOtherPathIndex_ne_min {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.maxOtherPathIndex hip ≠ pt.minCrowdedPathIndex hip := by
  have hmem := Finset.max'_mem _ (pt.otherPathsContainingFirstCrowded_nonempty hip)
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter] at hmem
  exact hmem.2

/-- The first crowded vertex is in the max other path -/
lemma PathTuple.firstCrowdedVertex_mem_maxOtherPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    pt.firstCrowdedVertex hip ∈ (pt.paths (pt.maxOtherPathIndex hip)).vertices := by
  have hmem := Finset.max'_mem _ (pt.otherPathsContainingFirstCrowded_nonempty hip)
  simp only [otherPathsContainingFirstCrowded, Finset.mem_filter, pathIndicesContaining,
    Finset.mem_univ, true_and] at hmem
  exact hmem.1

/-- Helper function to extract intersection indices from an intersecting path tuple.
    Returns a pair (i, j) with i ≠ j such that paths i and j intersect. -/
noncomputable def getIntersectionIndices {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { p : Fin k × Fin k // p.1 ≠ p.2 } :=
  Classical.choice (by
    -- Convert isIntersecting to existential form using isIntersecting_iff_exists_crowded
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, _, _⟩ := hip
    exact ⟨⟨(i, j), hij⟩⟩)

/-- Helper function to extract full intersection data from an intersecting path tuple.
    Returns (i, j, v, hvi, hvj) where i ≠ j and v is on both paths i and j. -/
noncomputable def getIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  Classical.choice (by
    rw [PathTuple.isIntersecting_iff_exists_crowded] at hip
    obtain ⟨v, i, j, hij, hvi, hvj⟩ := hip
    exact ⟨⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩⟩)

/-!
### Canonical (Deterministic) Intersection Data Selection

To prove that signReversing is an involution, we need to select intersection data
(i, j, v) deterministically so that the same selection is made before and after
applying the involution.

The canonical selection algorithm:
1. i = smallest index in crowdedPathIndices (using Finset.min')
2. v = first crowded vertex on path i (by position in the path)
3. j = largest index in pathIndicesContaining v, excluding i (using Finset.max')

This selection is preserved under exchangeTails because:
- The head of path i (vertices before v) is unchanged
- So v is still the first crowded vertex on path i
- And j is still the largest index containing v
-/

/-- A crowded path index has at least 2 paths containing some crowded vertex -/
lemma PathTuple.crowdedPathIndex_pathIndicesContaining_card {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    1 < (pt.pathIndicesContaining v).card := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  obtain ⟨hvi, j, hij, hvj⟩ := hv
  have hi_mem : i ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvi
  have hj_mem : j ∈ pt.pathIndicesContaining v := by
    simp only [pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hvj
  have hne : i ≠ j := hij
  calc (pt.pathIndicesContaining v).card 
      ≥ ({i, j} : Finset (Fin k)).card := Finset.card_le_card (by
        intro x hx
        simp only [Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hi_mem
        · exact hj_mem)
    _ = 2 := by simp [hne]
    _ > 1 := by omega

/-- If i is a crowded path index, the set of other path indices containing a crowded vertex on i
    is nonempty -/
lemma PathTuple.pathIndicesContaining_sdiff_singleton_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices)
    (v : V) (hv : v ∈ pt.crowdedVerticesOnPath i) :
    (pt.pathIndicesContaining v \ {i}).Nonempty := by
  have hcard := pt.crowdedPathIndex_pathIndicesContaining_card i hi v hv
  rw [Finset.sdiff_nonempty]
  intro h
  have hsub : pt.pathIndicesContaining v ⊆ {i} := h
  have : (pt.pathIndicesContaining v).card ≤ ({i} : Finset (Fin k)).card := Finset.card_le_card hsub
  simp only [Finset.card_singleton] at this
  omega

/-- A crowded path index has nonempty crowdedVerticesOnPath -/
lemma PathTuple.crowdedPathIndex_crowdedVerticesOnPath_nonempty {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    (pt.crowdedVerticesOnPath i).Nonempty := by
  simp only [crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hi
  obtain ⟨j, hij, v, hv⟩ := hi
  simp only [Finset.mem_inter, List.mem_toFinset] at hv
  use v
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
  exact ⟨hv.1, j, hij, hv.2⟩

/-- The first crowded vertex on path i (when i is a crowded path index) exists in the path -/
lemma PathTuple.firstCrowdedIndexOnPath_lt_length {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    pt.firstCrowdedIndexOnPath i < (pt.paths i).vertices.length := by
  have hne := pt.crowdedPathIndex_crowdedVerticesOnPath_nonempty i hi
  obtain ⟨v, hv⟩ := hne
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv
  unfold firstCrowdedIndexOnPath
  apply List.findIdx_lt_length_of_exists
  use v, hv.1
  simp only [crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
  exact hv

/-- The vertex at firstCrowdedIndexOnPath is in crowdedVerticesOnPath -/
lemma PathTuple.firstCrowdedVertex_mem_crowdedVerticesOnPath {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B)
    (i : Fin k) (hi : i ∈ pt.crowdedPathIndices) :
    let idx := pt.firstCrowdedIndexOnPath i
    let h := pt.firstCrowdedIndexOnPath_lt_length i hi
    (pt.paths i).vertices.get ⟨idx, h⟩ ∈ pt.crowdedVerticesOnPath i := by
  simp only
  unfold firstCrowdedIndexOnPath
  have h_lt := pt.firstCrowdedIndexOnPath_lt_length i hi
  unfold firstCrowdedIndexOnPath at h_lt
  have h_findIdx := @List.findIdx_getElem _ (fun v => v ∈ pt.crowdedVerticesOnPath i) 
    (pt.paths i).vertices h_lt
  simp only [List.get_eq_getElem]
  simp at h_findIdx
  exact h_findIdx

/-- Canonical intersection data: deterministically selects (i, j, v) for an intersecting path tuple.
    - i = smallest crowded path index
    - v = first crowded vertex on path i
    - j = largest path index containing v (other than i) -/
noncomputable def getCanonicalIntersectionData {D : SimpleDigraph V} {k : ℕ}
    {A B : kVertex V k} (pt : PathTuple D k A B) (hip : pt.isIntersecting) :
    { data : (i : Fin k) × (j : Fin k) × { v : V // v ∈ (pt.paths i).vertices ∧ v ∈ (pt.paths j).vertices } // 
      data.1 ≠ data.2.1 } :=
  let hne := pt.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip
  let i := pt.crowdedPathIndices.min' hne
  let hi : i ∈ pt.crowdedPathIndices := Finset.min'_mem _ hne
  let idx := pt.firstCrowdedIndexOnPath i
  let h_idx := pt.firstCrowdedIndexOnPath_lt_length i hi
  let v := (pt.paths i).vertices.get ⟨idx, h_idx⟩
  let hv_crowded := pt.firstCrowdedVertex_mem_crowdedVerticesOnPath i hi
    let hv_i : v ∈ (pt.paths i).vertices := by
      simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset] at hv_crowded
      exact hv_crowded.1
    let h_sdiff_ne := pt.pathIndicesContaining_sdiff_singleton_nonempty i hi v hv_crowded
    let j := (pt.pathIndicesContaining v \ {i}).max' h_sdiff_ne
    let hj_mem : j ∈ pt.pathIndicesContaining v \ {i} := Finset.max'_mem _ h_sdiff_ne
    let hj_ne_i : j ≠ i := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton] at hj_mem
      exact hj_mem.2
    let hv_j : v ∈ (pt.paths j).vertices := by
      simp only [Finset.mem_sdiff, Finset.mem_singleton, PathTuple.pathIndicesContaining, 
                 Finset.mem_filter, Finset.mem_univ, true_and] at hj_mem
      exact hj_mem.1
  ⟨⟨i, j, ⟨v, hv_i, hv_j⟩⟩, hj_ne_i.symm⟩


/-- The sign-reversing involution on intersecting path tuples.
    For an ipat (σ, 𝐩), we:
    1. Find the smallest i such that p_i contains a crowded point
    2. Find the first crowded point v on p_i
    3. Find the largest j such that v is on p_j
    4. Exchange tails of p_i and p_j at v
    5. Compose σ with the transposition t_{i,j}
    This gives (σ ∘ t_{i,j}, 𝐩') which is still an ipat.

    **Implementation note:** The permutation component is `sp.1 * Equiv.swap i j` where
    i and j are the intersection indices. The path tuple component uses `exchangeTails`
    to swap the tails of paths i and j at the crowded vertex v. -/
noncomputable def signReversing {D : SimpleDigraph V} (_hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) : pathTupleWithPerm (D := D) A B :=
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  let newPaths : Fin k → SimpleDigraph.Path D := fun l =>
    if h : l = i then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1
    else if h' : l = j then (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2
    else sp.2.paths l
  have h_starts : ∀ l, (newPaths l).start = A l := by
    intro l
    simp only [newPaths]
    split_ifs with h h'
    · rw [h, exchangeTails_fst_start, sp.2.starts]
    · rw [h', exchangeTails_snd_start, sp.2.starts]
    · exact sp.2.starts l
  have h_finishes : ∀ l, (newPaths l).finish = (permuteKVertex (sp.1 * Equiv.swap i j) B) l := by
    intro l
    simp only [newPaths, permuteKVertex, Equiv.Perm.coe_mul, Function.comp_apply]
    split_ifs with h h'
    · -- l = i case
      rw [h, exchangeTails_fst_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_left]
    · -- l = j case  
      rw [h', exchangeTails_snd_finish, sp.2.finishes]
      simp only [permuteKVertex, Equiv.swap_apply_right]
    · -- l ≠ i, l ≠ j case
      rw [sp.2.finishes]
      simp only [permuteKVertex]
      congr 1
      rw [Equiv.swap_apply_of_ne_of_ne h h']
    ⟨sp.1 * Equiv.swap i j, ⟨newPaths, h_starts, h_finishes⟩⟩

/-- The signReversing map preserves the intersecting property.
    The crowded point v at indices i and j is preserved in the exchanged paths. -/
lemma signReversing_isIntersecting {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    (signReversing hac sp hip).2.isIntersecting := by
  -- Extract the intersection data used by signReversing
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  -- Show v is a crowded point in the new paths at indices i and j
  rw [PathTuple.isIntersecting_iff_exists_crowded]
  use v
  unfold PathTuple.isCrowded
  use i, j, hij
  constructor
  · -- v is in path i of sp'
    show v ∈ ((signReversing hac sp hip).2.paths i).vertices
    conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]
    exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  · -- v is in path j of sp'
    show v ∈ ((signReversing hac sp hip).2.paths j).vertices
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]
    exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj

/-- Helper: The paths of sp' at index i is the first component of exchangeTails -/
private lemma signReversing_path_i {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]

/-- Helper: The paths of sp' at index j is the second component of exchangeTails -/
private lemma signReversing_path_j {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]

/-- Helper: The paths of sp' at index l ≠ i, j are unchanged -/
private lemma signReversing_path_other {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (l : Fin k) (hl_ne_i : l ≠ i) (hl_ne_j : l ≠ j) :
    (signReversing hac sp hip).2.paths l = sp.2.paths l := by
  conv_lhs => unfold signReversing; rw [h_data]; simp only [hl_ne_i, dite_false, hl_ne_j]

/-- Helper: The permutation of sp' is sp.1 * swap i j -/
private lemma signReversing_perm_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).1 = sp.1 * Equiv.swap i j := by
  conv_lhs => unfold signReversing; rw [h_data]

/-- Helper: A vertex w is in the head of path p (before v) iff it's in the head of the exchanged path -/
private lemma mem_head_iff_mem_exchangeTails_head {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v w : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let p' := (exchangeTails p q v hv_p hv_q).1
    let hv_p' := exchangeTails_fst_mem_v p q v hv_p hv_q
    w ∈ (p.splitAt v hv_p).1.vertices ↔ w ∈ (p'.splitAt v hv_p').1.vertices := by
  simp only
  rw [exchangeTails_head_eq _hac p q v hv_p hv_q]

/-- Helper: exchangeTails preserves head vertices (snd version) -/
private lemma exchangeTails_head_eq_snd {D : SimpleDigraph V} (_hac : D.IsAcyclic)
    (p q : SimpleDigraph.Path D) (v : V)
    (hv_p : v ∈ p.vertices) (hv_q : v ∈ q.vertices) :
    let q' := (exchangeTails p q v hv_p hv_q).2
    let hv_q' := exchangeTails_snd_mem_v p q v hv_p hv_q
    (q'.splitAt v hv_q').1.vertices = (q.splitAt v hv_q).1.vertices := by
  simp only
  rw [splitAt_fst_vertices, splitAt_fst_vertices]
  rw [exchangeTails_snd_vertices]
  -- The head of q' = head_q ++ tail_p.tail is just head_q (up to v)
  have h_head_q := splitAt_fst_vertices q v hv_q
  have h_tail_p := splitAt_snd_vertices p v hv_p
  have h_head_q_last : (q.splitAt v hv_q).1.vertices.getLast (q.splitAt v hv_q).1.nonempty = v := 
    SimpleDigraph.Path.splitAt_head_finish q v hv_q
  have h_findIdx_head : (q.splitAt v hv_q).1.vertices.findIdx (· = v) = 
      (q.splitAt v hv_q).1.vertices.length - 1 := splitAt_head_findIdx_eq q.vertices v hv_q
  have h_concat := splitAt_concat_vertices_eq 
    (q.splitAt v hv_q).1.vertices (p.splitAt v hv_p).2.vertices v
    (q.splitAt v hv_q).1.nonempty (p.splitAt v hv_p).2.nonempty
    h_head_q_last (SimpleDigraph.Path.splitAt_tail_start p v hv_p)
    h_findIdx_head
  simp only at h_concat
  exact congr_arg Prod.fst h_concat

/-- Key invariance lemma: pathIndicesContaining v is preserved after signReversing.
    This holds because v is in the HEAD of paths i and j (since v is the first crowded vertex
    on path i, and v is shared with j). After exchangeTails at v, the heads are preserved,
    so v is still on exactly the same paths. -/
private lemma signReversing_pathIndicesContaining_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩) :
    (signReversing hac sp hip).2.pathIndicesContaining v = sp.2.pathIndicesContaining v := by
  ext l
  simp only [PathTuple.pathIndicesContaining, Finset.mem_filter, Finset.mem_univ, true_and]
  -- We need to show: v ∈ sp'.paths l ↔ v ∈ sp.paths l
  by_cases hl_i : l = i
  · -- l = i case
    constructor
    · intro hv_sp'
      rw [hl_i]
      exact hvi
    · intro _
      rw [hl_i, signReversing_path_i hac sp hip i j hij v hvi hvj h_data]
      exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  · by_cases hl_j : l = j
    · -- l = j case
      constructor
      · intro hv_sp'
        rw [hl_j]
        exact hvj
      · intro _
        rw [hl_j, signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
        exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
    · -- l ≠ i, l ≠ j case: path l is unchanged
      rw [signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl_i hl_j]

/-- Helper lemma: findIdx returns n if the element at position n satisfies the predicate
    and all elements before it do not. -/
private lemma findIdx_eq_of_first {α : Type*} (l : List α) (p : α → Bool)
    (n : ℕ) (hn : n < l.length)
    (h_first : ∀ m : ℕ, ∀ hm : m < n, ¬p (l[m]'(Nat.lt_trans hm hn)))
    (h_p_n : p (l[n]'hn)) :
    l.findIdx p = n := by
  induction l generalizing n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => 
      simp only [List.findIdx_cons, List.getElem_cons_zero] at h_p_n ⊢
      simp [h_p_n]
    | succ n' =>
      simp only [List.findIdx_cons]
      have h_not_x : p x = false := by
        have := h_first 0 (Nat.zero_lt_succ n')
        simp at this
        exact this
      simp only [h_not_x, Bool.false_eq_true, ↓reduceIte]
      have hn' : n' < xs.length := by simp at hn; omega
      have h_first' : ∀ m : ℕ, ∀ hm : m < n', ¬p (xs[m]'(Nat.lt_trans hm hn')) := by
        intro m hm
        have hm1 : m + 1 < n' + 1 := by omega
        have := h_first (m + 1) hm1
        simp only [List.getElem_cons_succ] at this
        exact this
      have h_p_n' : p (xs[n']'hn') := by
        have := h_p_n
        simp only [List.getElem_cons_succ] at this
        exact this
      have h_ih := ih n' hn' h_first' h_p_n'
      omega

/-- Helper lemma: vertices before v on path i are not crowded in sp'.
    This is the key insight for proving that firstCrowdedIndexOnPath is preserved.
    
    For any vertex w at index m < idx on path i (where idx is the index of v):
    - w is not crowded in sp (since v at idx is the FIRST crowded vertex)
    - w is only on path i in sp (not on any other path)
    - After exchangeTails, w is still only on path i:
      * w is in the head of path i (preserved by exchangeTails_head_eq)
      * w is not in path j' = head_j ++ tail_i.tail (w not in head_j since not in path j,
        and w not in tail_i.tail since w is before v which starts tail_i)
      * w is not in any other path l (paths l are unchanged for l ≠ i, j)
    - So w is not crowded in sp' -/
private lemma vertices_before_v_not_crowded_in_sp' {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (w : V) (m : ℕ) (hm_lt_idx : m < (sp.2.paths i).vertices.findIdx (· = v))
    (hm_lt_len : m < (sp.2.paths i).vertices.length)
    (hw_eq : (sp.2.paths i).vertices[m] = w) :
    w ∉ (signReversing hac sp hip).2.crowdedVerticesOnPath i := by
  -- Step 1: Show w is NOT crowded in sp (since v is the first crowded vertex)
  -- This means w is only on path i in sp, not shared with any other path
  
  -- Extract key facts from h_data
  have hi_crowded : i ∈ sp.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi, hvj⟩
  
  -- From h_data, i is the min of crowdedPathIndices
  have hi_min_sp : i = sp.2.crowdedPathIndices.min' 
      (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) := by
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    exact (congrArg (fun x => x.val.1) h).symm
  
  -- v is at position firstCrowdedIndexOnPath i
  have h_v_at_idx : (sp.2.paths i).vertices[sp.2.firstCrowdedIndexOnPath i]'
      (sp.2.firstCrowdedIndexOnPath_lt_length i hi_crowded) = v := by
    -- Extract from getCanonicalIntersectionData definition
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    -- The equality gives us that v is the vertex at firstCrowdedIndexOnPath i
    have h_eq := congrArg (fun x => x.val.2.2.val) h
    simp only [List.get_eq_getElem] at h_eq
    -- h_eq says v = (paths i').vertices[firstCrowdedIndexOnPath i']
    -- where i' = crowdedPathIndices.min'
    -- Since i = i' (from hi_min_sp), we can use simp with hi_min_sp
    simp only [← hi_min_sp] at h_eq
    exact h_eq
  
  -- Since paths have nodup vertices (acyclic), findIdx (· = v) = firstCrowdedIndexOnPath i
  have hnd := SimpleDigraph.Path.vertices_nodup_of_acyclic hac (sp.2.paths i)
  have h_findIdx_eq : (sp.2.paths i).vertices.findIdx (· = v) = sp.2.firstCrowdedIndexOnPath i := by
    have h_idx : (sp.2.paths i).vertices.idxOf v = sp.2.firstCrowdedIndexOnPath i := by
      rw [← h_v_at_idx]
      exact hnd.idxOf_getElem _ _
    simp only [List.idxOf] at h_idx
    exact h_idx
  
  -- Therefore m < firstCrowdedIndexOnPath i
  have hm_lt_first : m < sp.2.firstCrowdedIndexOnPath i := by
    rw [← h_findIdx_eq]
    exact hm_lt_idx
  
  -- So w = (paths i).vertices[m] is NOT in crowdedVerticesOnPath i
  -- (because firstCrowdedIndexOnPath is the FIRST index where the crowded predicate holds)
  have hw_not_crowded_sp : w ∉ sp.2.crowdedVerticesOnPath i := by
    rw [← hw_eq]
    -- The predicate for crowdedVerticesOnPath is decidable
    have h_pred : ¬ ((sp.2.paths i).vertices[m] ∈ sp.2.crowdedVerticesOnPath i) := by
      intro h_in
      -- firstCrowdedIndexOnPath i = findIdx (fun v => v ∈ crowdedVerticesOnPath i)
      unfold PathTuple.firstCrowdedIndexOnPath at hm_lt_first
      -- If (paths i).vertices[m] ∈ crowdedVerticesOnPath i, then findIdx should be ≤ m
      have h_findIdx_le : (sp.2.paths i).vertices.findIdx 
          (fun v => v ∈ sp.2.crowdedVerticesOnPath i) ≤ m := by
        -- If the element at position m satisfies the predicate, then findIdx ≤ m
        have hp : (sp.2.paths i).vertices[m] ∈ sp.2.crowdedVerticesOnPath i := h_in
        -- Use the fact that findIdx returns the first index satisfying the predicate
        -- If element at m satisfies it, findIdx must be ≤ m
        by_contra h_gt
        push_neg at h_gt
        -- All elements before findIdx don't satisfy the predicate
        -- In particular, element at m doesn't satisfy it (since m < findIdx)
        have h_not_p : ¬ (fun v => v ∈ sp.2.crowdedVerticesOnPath i) (sp.2.paths i).vertices[m] := by
          have h_lt : m < (sp.2.paths i).vertices.findIdx (fun v => v ∈ sp.2.crowdedVerticesOnPath i) := h_gt
          -- For all n < findIdx, the element at n doesn't satisfy the predicate
          have := List.not_of_lt_findIdx h_lt
          simp only [decide_eq_false_iff_not] at this
          exact this
        exact h_not_p hp
      omega
    exact h_pred
  
  -- This means w is only on path i in sp (not shared with any other path)
  have hw_only_on_i : ∀ l : Fin k, l ≠ i → w ∉ (sp.2.paths l).vertices := by
    intro l hl
    by_contra hw_l
    apply hw_not_crowded_sp
    simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rw [← hw_eq]; exact List.getElem_mem hm_lt_len
    · exact ⟨l, hl.symm, hw_l⟩
  
  -- Step 2: Show w is not crowded in sp'
  -- w ∉ sp'.crowdedVerticesOnPath i means:
  -- either w ∉ sp'.paths i, or ∀ l ≠ i, w ∉ sp'.paths l
  -- We'll show the second
  
  simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset, not_and]
  intro hw_in_sp'_i
  push_neg
  intro l hl
  
  -- Case analysis on l
  by_cases hl_j : l = j
  · -- l = j: w is not on path j in sp', which is head_j ++ tail_i.tail
    rw [hl_j, signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
    rw [exchangeTails_snd_vertices]
    simp only [List.mem_append, not_or]
    constructor
    · -- w not in head_j (= take part of path j up to v)
      -- Since w is only on path i in sp, w ∉ path j in sp
      have hw_not_j := hw_only_on_i j hij.symm
      intro hw_head_j
      apply hw_not_j
      have := splitAt_fst_vertices (sp.2.paths j) v hvj
      rw [this] at hw_head_j
      exact List.mem_of_mem_take hw_head_j
    · -- w not in tail_i.tail (= drop part of path i after v)
      -- Since w is at position m < findIdx(v), w is before v on path i
      -- So w cannot be in tail_i.tail (which starts after v)
      intro hw_tail_i
      -- w is at position m < findIdx(v), so w is in take (findIdx(v)+1)
      -- But tail starts at findIdx(v), so tail.tail starts at findIdx(v)+1
      -- By nodup, w cannot be in both take(findIdx(v)+1) and drop(findIdx(v)+1)
      have h_w_in_take : w ∈ (sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1) := by
        have h_take_len : m < ((sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1)).length := by
          simp only [List.length_take]
          omega
        have := List.getElem_mem h_take_len
        simp only [List.getElem_take] at this
        rw [hw_eq] at this
        exact this
      have h_tail_drop : ((sp.2.paths i).splitAt v hvi).2.vertices.tail = 
          (sp.2.paths i).vertices.drop ((sp.2.paths i).vertices.findIdx (· = v) + 1) := by
        rw [splitAt_snd_vertices]
        exact List.tail_drop
      rw [h_tail_drop] at hw_tail_i
      have h_disjoint : ((sp.2.paths i).vertices.take ((sp.2.paths i).vertices.findIdx (· = v) + 1)).Disjoint 
          ((sp.2.paths i).vertices.drop ((sp.2.paths i).vertices.findIdx (· = v) + 1)) := 
        List.disjoint_take_drop hnd (Nat.le_refl _)
      exact List.disjoint_left.mp h_disjoint h_w_in_take hw_tail_i
  · -- l ≠ j (and l ≠ i by hl)
    -- Path l is unchanged in sp'
    have h_path_l_eq : (signReversing hac sp hip).2.paths l = sp.2.paths l := 
      signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl.symm hl_j
    rw [h_path_l_eq]
    exact hw_only_on_i l hl.symm

/-- Key invariance lemma: The canonical selection returns the same (i, j, v) for sp' as for sp.
    This is the heart of the involutive proof. -/
lemma signReversing_canonical_eq {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting)
    (i j : Fin k) (hij : i ≠ j) (v : V) (hvi : v ∈ (sp.2.paths i).vertices) (hvj : v ∈ (sp.2.paths j).vertices)
    (h_data : getCanonicalIntersectionData sp.2 hip = ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩)
    (hip' : (signReversing hac sp hip).2.isIntersecting) :
    ∃ hvi' : v ∈ ((signReversing hac sp hip).2.paths i).vertices,
    ∃ hvj' : v ∈ ((signReversing hac sp hip).2.paths j).vertices,
    getCanonicalIntersectionData (signReversing hac sp hip).2 hip' = ⟨⟨i, j, ⟨v, hvi', hvj'⟩⟩, hij⟩ := by
  -- The membership facts for v in sp'
  have hvi' : v ∈ ((signReversing hac sp hip).2.paths i).vertices := by
    rw [signReversing_path_i hac sp hip i j hij v hvi hvj h_data]
    exact exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  have hvj' : v ∈ ((signReversing hac sp hip).2.paths j).vertices := by
    rw [signReversing_path_j hac sp hip i j hij v hvi hvj h_data]
    exact exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  use hvi', hvj'
  
  -- We need to show that getCanonicalIntersectionData returns the same (i, j, v)
  -- This requires showing:
  -- 1. i = sp'.2.crowdedPathIndices.min'
  -- 2. v = sp'.2.paths i at firstCrowdedIndexOnPath
  -- 3. j = (sp'.2.pathIndicesContaining v \ {i}).max'
  
  -- The key insight is that v is the FIRST crowded vertex on path i.
  -- After exchangeTails, the head of path i (vertices up to and including v) is preserved.
  -- Therefore:
  -- - v is still crowded on path i (shared with j, whose head also contains v)
  -- - All vertices before v on path i are still not crowded
  -- - So v is still the first crowded vertex on path i
  -- - i is still the smallest crowded index (any smaller index has unchanged path)
  -- - pathIndicesContaining v is preserved (shown above)
  -- - So j is still the largest in pathIndicesContaining v \ {i}
  
  -- Set up sp' for convenience
  set sp' := signReversing hac sp hip with h_sp'
  
  -- First, establish that i is in sp'.2.crowdedPathIndices
  have hi'_crowded : i ∈ sp'.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi', hvj'⟩
  
  -- Extract that i was the min for sp
  have hi_min_sp : i = sp.2.crowdedPathIndices.min' 
      (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) := by
    have h := h_data
    simp only [getCanonicalIntersectionData] at h
    exact (congrArg (fun x => x.val.1) h).symm
  
  -- Show that no index < i is crowded in sp'
  -- This is the key case analysis: for any l < i, l was not crowded in sp,
  -- and after signReversing, l is still not crowded because:
  -- - If l ∉ {i, j}, path l is unchanged
  -- - If l = j, then j < i, but j is crowded (shares v with i), so j ≥ i, contradiction
  have h_no_smaller_crowded : ∀ l : Fin k, l < i → l ∉ sp'.2.crowdedPathIndices := by
    intro l hl_lt
    have hl_not_crowded_sp : l ∉ sp.2.crowdedPathIndices := by
      intro hl_in
      have h_le := Finset.min'_le sp.2.crowdedPathIndices l hl_in
      rw [← hi_min_sp] at h_le
      omega
    -- Case analysis: is l = j?
    by_cases hlj : l = j
    · -- Case l = j: This is a contradiction
      -- j is crowded in sp (shares v with i), so j ∈ crowdedPathIndices
      -- Since i is the minimum, i ≤ j. But l = j < i, contradiction.
      have hj_crowded : j ∈ sp.2.crowdedPathIndices := by
        simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
        use i, hij.symm
        simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
        exact ⟨v, hvj, hvi⟩
      have hi_le_j := Finset.min'_le sp.2.crowdedPathIndices j hj_crowded
      rw [← hi_min_sp] at hi_le_j
      omega
    · -- Case l ≠ j (and l ≠ i since l < i)
      have hli : l ≠ i := by omega
      -- Path l is unchanged in sp'
      have h_path_l_eq : sp'.2.paths l = sp.2.paths l := 
        signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hli hlj
      -- Suppose l is crowded in sp'. Then there exists m ≠ l with shared vertex w.
      intro hl_crowded'
      simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and] at hl_crowded'
      obtain ⟨m, hlm, w, hw_inter⟩ := hl_crowded'
      simp only [Finset.mem_inter, List.mem_toFinset] at hw_inter
      obtain ⟨hw_l', hw_m'⟩ := hw_inter
      -- w is on path l in sp' = path l in sp
      rw [h_path_l_eq] at hw_l'
      -- Case analysis on m
      by_cases hmi : m = i
      · -- m = i: w is on path l (unchanged) and path i' = head_i ++ tail_j.tail
        rw [hmi, signReversing_path_i hac sp hip i j hij v hvi hvj h_data] at hw_m'
        rw [exchangeTails_fst_vertices] at hw_m'
        simp only [List.mem_append] at hw_m'
        rcases hw_m' with hw_head_i | hw_tail_j
        · -- w is in head_i: w was on path l and path i in sp
          have hw_i : w ∈ (sp.2.paths i).vertices := by
            have := splitAt_fst_vertices (sp.2.paths i) v hvi
            rw [this] at hw_head_i
            exact List.mem_of_mem_take hw_head_i
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hli, w, by simp [hw_l', hw_i]⟩
        · -- w is in tail_j.tail: w was on path l and path j in sp
          have hw_j : w ∈ (sp.2.paths j).vertices := by
            have := splitAt_snd_vertices (sp.2.paths j) v hvj
            rw [this] at hw_tail_j
            exact List.mem_of_mem_drop (List.mem_of_mem_tail hw_tail_j)
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨j, hlj, w, by simp [hw_l', hw_j]⟩
      · by_cases hmj : m = j
        · -- m = j: w is on path l (unchanged) and path j' = head_j ++ tail_i.tail
          rw [hmj, signReversing_path_j hac sp hip i j hij v hvi hvj h_data] at hw_m'
          rw [exchangeTails_snd_vertices] at hw_m'
          simp only [List.mem_append] at hw_m'
          rcases hw_m' with hw_head_j | hw_tail_i
          · -- w is in head_j: w was on path l and path j in sp
            have hw_j : w ∈ (sp.2.paths j).vertices := by
              have := splitAt_fst_vertices (sp.2.paths j) v hvj
              rw [this] at hw_head_j
              exact List.mem_of_mem_take hw_head_j
            apply hl_not_crowded_sp
            simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨j, hlj, w, by simp [hw_l', hw_j]⟩
          · -- w is in tail_i.tail: w was on path l and path i in sp
            have hw_i : w ∈ (sp.2.paths i).vertices := by
              have := splitAt_snd_vertices (sp.2.paths i) v hvi
              rw [this] at hw_tail_i
              exact List.mem_of_mem_drop (List.mem_of_mem_tail hw_tail_i)
            apply hl_not_crowded_sp
            simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨i, hli, w, by simp [hw_l', hw_i]⟩
        · -- m ∉ {i, j}: path m is unchanged
          have h_path_m_eq : sp'.2.paths m = sp.2.paths m := 
            signReversing_path_other hac sp hip i j hij v hvi hvj h_data m hmi hmj
          rw [h_path_m_eq] at hw_m'
          -- w was shared between l and m in sp, so l was crowded
          apply hl_not_crowded_sp
          simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨m, hlm, w, by simp [hw_l', hw_m']⟩
  
  -- Now we can show i is the min of sp'.2.crowdedPathIndices
  have hi'_min : i = sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') := by
    apply le_antisymm
    · apply Finset.le_min'
      intro l hl
      by_contra h
      push_neg at h
      exact h_no_smaller_crowded l h hl
    · exact Finset.min'_le sp'.2.crowdedPathIndices i hi'_crowded
  
  -- v is crowded in sp' (on both paths i and j)
  have hv_crowded' : v ∈ sp'.2.crowdedVerticesOnPath i := by
    simp only [PathTuple.crowdedVerticesOnPath, Finset.mem_filter, List.mem_toFinset]
    exact ⟨hvi', j, hij, hvj'⟩
  
  -- pathIndicesContaining v is preserved
  have h_pathIndices_eq := signReversing_pathIndicesContaining_eq hac sp hip i j hij v hvi hvj h_data
  
  -- The final equality requires showing that all components of getCanonicalIntersectionData match:
  -- 1. i is the min of crowdedPathIndices (shown in hi'_min)
  -- 2. The firstCrowdedIndexOnPath gives the same index (v is still first crowded vertex)
  -- 3. The vertex at that index is v (since heads are preserved)
  -- 4. j is the max of (pathIndicesContaining v \ {i}) (by h_pathIndices_eq)
  
  -- For (2) and (3): The head of path i is preserved by exchangeTails_head_eq,
  -- and the crowded status of vertices before v is preserved (shown in h_no_smaller_crowded analysis).
  -- Since v was the first crowded vertex in sp, it remains the first in sp'.
  
  -- Extract key facts from h_data
  have hi_crowded : i ∈ sp.2.crowdedPathIndices := by
    simp only [PathTuple.crowdedPathIndices, Finset.mem_filter, Finset.mem_univ, true_and]
    use j, hij
    simp only [Finset.Nonempty, Finset.mem_inter, List.mem_toFinset]
    exact ⟨v, hvi, hvj⟩
  
  -- The index of v on path i
  let idx := sp.2.firstCrowdedIndexOnPath i
  have h_idx : idx < (sp.2.paths i).vertices.length := sp.2.firstCrowdedIndexOnPath_lt_length i hi_crowded
  
  -- Key fact: v is at index idx on path i
  have h_v_at_idx : (sp.2.paths i).vertices[idx]'h_idx = v := by
    -- By definition of getCanonicalIntersectionData, v is defined as the vertex at firstCrowdedIndexOnPath i
    -- We extract this from h_data
    have h_v_eq : v = (getCanonicalIntersectionData sp.2 hip).val.2.2.val := by
      rw [h_data]
    -- Unfold getCanonicalIntersectionData to see that the result is (paths i').get ⟨idx', h_idx'⟩
    -- where i' = crowdedPathIndices.min' and idx' = firstCrowdedIndexOnPath i'
    simp only [getCanonicalIntersectionData] at h_v_eq
    -- h_v_eq now shows v = (sp.2.paths (min' ...)).vertices.get ⟨firstCrowdedIndexOnPath (min' ...), _⟩
    -- Since i = min' (by hi_min_sp), this gives us what we need
    rw [h_v_eq]
    -- Now need to show (sp.2.paths i).vertices[idx] = (sp.2.paths (min' ...)).vertices.get ...
    -- Use hi_min_sp: i = min' ...
    -- First, rewrite i to min' in the goal
    have h_idx_eq : idx = sp.2.firstCrowdedIndexOnPath (sp.2.crowdedPathIndices.min' 
        (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)) := by
      exact congrArg sp.2.firstCrowdedIndexOnPath hi_min_sp
    simp only [hi_min_sp, h_idx_eq, List.get_eq_getElem]
  
  -- Key fact: idx equals the findIdx of v on path i
  have h_idx_eq_findIdx : idx = (sp.2.paths i).vertices.findIdx (· = v) := by
    -- Since v is at position idx on path i (by h_v_at_idx), and vertices are distinct
    -- (by acyclicity), findIdx (· = v) = idx
    have hnodup := SimpleDigraph.Path.vertices_nodup_of_acyclic hac (sp.2.paths i)
    have h_mem : v ∈ (sp.2.paths i).vertices := hvi
    have h_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, h_mem, by simp⟩
    have h_get := @List.findIdx_getElem _ (· = v) (sp.2.paths i).vertices h_lt
    simp only [decide_eq_true_eq] at h_get
    -- h_get : (sp.2.paths i).vertices[findIdx] = v
    -- h_v_at_idx : (sp.2.paths i).vertices[idx] = v
    -- Since vertices are distinct, findIdx = idx
    have h_eq : (sp.2.paths i).vertices[(sp.2.paths i).vertices.findIdx (· = v)]'h_lt = 
                (sp.2.paths i).vertices[idx]'h_idx := by
      rw [h_get, h_v_at_idx]
    exact (hnodup.getElem_inj_iff.mp h_eq).symm

  -- Key fact: firstCrowdedIndexOnPath gives the same index in sp' as in sp
  have h_firstCrowded_eq : sp'.2.firstCrowdedIndexOnPath i = idx := by
      -- This follows from:
      -- 1. Vertices before v on path i are not crowded in sp' (by vertices_before_v_not_crowded_in_sp')
      -- 2. v is crowded in sp' (by hv_crowded')
      -- 3. The head of path i is preserved (by exchangeTails_head_eq)
      
      -- First, show that the head of path i is preserved
      have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
        signReversing_path_i hac sp hip i j hij v hvi hvj h_data
      
      simp only [PathTuple.firstCrowdedIndexOnPath]
      
      -- sp'.paths i has vertices = head_p ++ tail_q.tail
      have h_sp'_verts : (sp'.2.paths i).vertices = 
          ((sp.2.paths i).splitAt v hvi).1.vertices ++ 
          ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
        rw [h_path_i_eq, exchangeTails_fst_vertices]
      
      -- head_p has length idx + 1
      have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
        rw [splitAt_fst_vertices]
        rw [List.length_take]
        have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
        rw [h_idx_eq_findIdx]
        omega
      
      -- idx < length of sp'.paths i
      have h_idx_lt' : idx < (sp'.2.paths i).vertices.length := by
        rw [h_sp'_verts, List.length_append]
        have : 0 < ((sp.2.paths j).splitAt v hvj).2.vertices.tail.length ∨ 
               ((sp.2.paths j).splitAt v hvj).2.vertices.tail.length = 0 := by omega
        rcases this with hpos | hzero
        · omega
        · rw [h_head_len]; omega
      
      -- The key insight: sp'.paths i has the same first (idx+1) vertices as sp.paths i
      have h_prefix : ∀ m : ℕ, (hm : m ≤ idx) → 
          (sp'.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx_lt') = 
          (sp.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx) := by
        intro m hm
        have h_m_lt_head : m < ((sp.2.paths i).splitAt v hvi).1.vertices.length := by
          rw [h_head_len]; omega
        have h1 : (sp'.2.paths i).vertices[m]'(Nat.lt_of_le_of_lt hm h_idx_lt') = 
            (((sp.2.paths i).splitAt v hvi).1.vertices ++ 
             ((sp.2.paths j).splitAt v hvj).2.vertices.tail)[m]'(by
               rw [List.length_append]; omega) := by
          simp only [h_sp'_verts]
        rw [h1, List.getElem_append_left h_m_lt_head]
        simp only [splitAt_fst_vertices, List.getElem_take]

      -- The vertex at position idx in sp'.paths i is v
      have h_v_at_idx' : (sp'.2.paths i).vertices[idx]'h_idx_lt' = v := 
        (h_prefix idx (Nat.le_refl idx)).trans h_v_at_idx
      
      -- v is crowded in sp' (already have hv_crowded')
      have h_v_crowded_bool : (fun w => w ∈ sp'.2.crowdedVerticesOnPath i) v := hv_crowded'
      
      -- For m < idx, the vertex at position m is not crowded in sp'
      have h_before_not_crowded : ∀ m : ℕ, (hm : m < idx) → 
          ¬((sp'.2.paths i).vertices[m]'(Nat.lt_trans hm h_idx_lt') ∈ sp'.2.crowdedVerticesOnPath i) := by
        intro m hm
        have h_m_lt_sp : m < (sp.2.paths i).vertices.length := Nat.lt_trans hm h_idx
        have h_getElem_eq : (sp'.2.paths i).vertices[m]'(Nat.lt_trans hm h_idx_lt') = 
            (sp.2.paths i).vertices[m]'h_m_lt_sp := h_prefix m (Nat.le_of_lt hm)
        rw [h_getElem_eq]
        have h_m_lt_findIdx : m < (sp.2.paths i).vertices.findIdx (· = v) := by
          rw [← h_idx_eq_findIdx]; exact hm
        exact vertices_before_v_not_crowded_in_sp' hac sp hip i j hij v hvi hvj h_data 
          ((sp.2.paths i).vertices[m]'h_m_lt_sp) m h_m_lt_findIdx h_m_lt_sp rfl
      
      -- Apply findIdx_eq_of_first
      exact findIdx_eq_of_first (sp'.2.paths i).vertices 
        (fun w => decide (w ∈ sp'.2.crowdedVerticesOnPath i)) idx h_idx_lt'
        (fun m hm => by
          have := h_before_not_crowded m hm
          simp only [Bool.not_eq_true, decide_eq_false_iff_not]
          exact this)
        (by simp only [decide_eq_true_eq]; rw [h_v_at_idx']; exact h_v_crowded_bool)
  
  -- Now we can show getCanonicalIntersectionData returns the same (i, j, v)
  -- The component equalities are established (hi'_min, h_firstCrowded_eq, h_pathIndices_eq)
  -- The final equality follows from these.
  
  -- First, establish that the min equals i
  have h_min_eq : sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') = i := hi'_min.symm
  
  -- The vertex at the first crowded index on path i in sp' is v
  -- We need to re-derive h_v_at_idx' here since it was local to h_firstCrowded_eq
  have h_idx_lt' : idx < (sp'.2.paths i).vertices.length := by
    have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
      signReversing_path_i hac sp hip i j hij v hvi hvj h_data
    have h_sp'_verts : (sp'.2.paths i).vertices = 
        ((sp.2.paths i).splitAt v hvi).1.vertices ++ 
        ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
      rw [h_path_i_eq, exchangeTails_fst_vertices]
    have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
      rw [splitAt_fst_vertices, List.length_take]
      have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
      rw [h_idx_eq_findIdx]; omega
    rw [h_sp'_verts, List.length_append, h_head_len]; omega
  
  have h_v_at_idx'_new : (sp'.2.paths i).vertices[idx]'h_idx_lt' = v := by
    have h_path_i_eq : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
      signReversing_path_i hac sp hip i j hij v hvi hvj h_data
    have h_sp'_verts : (sp'.2.paths i).vertices = 
        ((sp.2.paths i).splitAt v hvi).1.vertices ++ 
        ((sp.2.paths j).splitAt v hvj).2.vertices.tail := by
      rw [h_path_i_eq, exchangeTails_fst_vertices]
    have h_head_len : ((sp.2.paths i).splitAt v hvi).1.vertices.length = idx + 1 := by
      rw [splitAt_fst_vertices, List.length_take]
      have h_findIdx_lt := List.findIdx_lt_length_of_exists (p := (· = v)) ⟨v, hvi, by simp⟩
      rw [h_idx_eq_findIdx]; omega
    have h_idx_lt_head : idx < ((sp.2.paths i).splitAt v hvi).1.vertices.length := by
      rw [h_head_len]; omega
    calc (sp'.2.paths i).vertices[idx]'h_idx_lt' 
        = (((sp.2.paths i).splitAt v hvi).1.vertices ++ 
           ((sp.2.paths j).splitAt v hvj).2.vertices.tail)[idx]'(by rw [List.length_append]; omega) := by
          simp only [h_sp'_verts]
      _ = ((sp.2.paths i).splitAt v hvi).1.vertices[idx]'h_idx_lt_head := by
          rw [List.getElem_append_left h_idx_lt_head]
      _ = (sp.2.paths i).vertices[idx]'h_idx := by
          simp only [splitAt_fst_vertices, List.getElem_take]
      _ = v := h_v_at_idx
  
  -- Now show the vertex computed by getCanonicalIntersectionData equals v
  have h_v_eq' : (sp'.2.paths (sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip'))).vertices.get 
      ⟨sp'.2.firstCrowdedIndexOnPath (sp'.2.crowdedPathIndices.min' 
        (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip')), 
       sp'.2.firstCrowdedIndexOnPath_lt_length _ (Finset.min'_mem _ _)⟩ = v := by
    simp only [h_min_eq, h_firstCrowded_eq, List.get_eq_getElem]
    exact h_v_at_idx'_new
  
  -- The max of (pathIndicesContaining v \ {i}) in sp' equals j
  have h_max_eq : ∀ h_sdiff_ne : (sp'.2.pathIndicesContaining v \ {i}).Nonempty,
      (sp'.2.pathIndicesContaining v \ {i}).max' h_sdiff_ne = j := by
    intro h_sdiff_ne
    have h_eq : sp'.2.pathIndicesContaining v \ {i} = sp.2.pathIndicesContaining v \ {i} := by
      rw [h_pathIndices_eq]
    -- j is in the set
    have hj_mem_sp' : j ∈ sp'.2.pathIndicesContaining v \ {i} := by
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                 Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨hvj', hij.symm⟩
    -- j is maximal: for all k in the set, k ≤ j
    have hj_max : ∀ k ∈ sp'.2.pathIndicesContaining v \ {i}, k ≤ j := by
      intro k hk
      rw [h_eq] at hk
      -- k is in sp.2.pathIndicesContaining v \ {i}
      -- j is the max' of this set (from h_data)
      -- We use the fact that h_data tells us j = max' of pathIndicesContaining v \ {i}
      have hj_mem_sp : j ∈ sp.2.pathIndicesContaining v \ {i} := by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hvj, hij.symm⟩
      -- From h_data, j is the max' of sp.2.pathIndicesContaining v \ {i}
      -- We need to show k ≤ j
      -- Since both k and j are in the same finite set, and j is the max from h_data
      have h_sdiff_ne_sp : (sp.2.pathIndicesContaining v \ {i}).Nonempty := ⟨j, hj_mem_sp⟩
      -- Extract from h_data that j equals the max'
      -- getCanonicalIntersectionData returns j = max' (pathIndicesContaining (vertex at idx) \ {i})
      -- where vertex at idx = v (by h_v_at_idx) and i = min' (by hi_min_sp)
      -- So j = max' (pathIndicesContaining v \ {i})
      have h_j_is_max : j = (sp.2.pathIndicesContaining v \ {i}).max' h_sdiff_ne_sp := by
        -- From the definition of getCanonicalIntersectionData and h_data
        -- The j component equals max' (pathIndicesContaining v \ {i})
        -- This is a consequence of h_data which specifies the exact form
        simp only [getCanonicalIntersectionData] at h_data
        have h := congrArg (fun x => x.val.2.1) h_data
        simp only at h
        rw [← h]
        -- Now we need to show the sets are equal
        -- The vertex in the definition equals v, and min' = i
        have h_vert : (sp.2.paths (sp.2.crowdedPathIndices.min' 
            (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip))).vertices.get 
            ⟨sp.2.firstCrowdedIndexOnPath (sp.2.crowdedPathIndices.min' 
              (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip)), 
             sp.2.firstCrowdedIndexOnPath_lt_length _ (Finset.min'_mem _ _)⟩ = v := by
          -- Use hi_min_sp : i = min' ... to rewrite
          have h_eq : sp.2.crowdedPathIndices.min' 
              (sp.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip) = i := hi_min_sp.symm
          simp only [h_eq, List.get_eq_getElem]
          exact h_v_at_idx
        simp only [h_vert, hi_min_sp]
      rw [h_j_is_max]
      exact Finset.le_max' _ _ hk
    exact le_antisymm (Finset.max'_le _ h_sdiff_ne j hj_max) (Finset.le_max' _ j hj_mem_sp')
  
  -- Now construct the equality using Subtype.ext
  -- The goal is to show:
  -- getCanonicalIntersectionData sp'.2 hip' = ⟨⟨i, j, ⟨v, hvi', hvj'⟩⟩, hij⟩
  -- 
  -- We have established:
  -- - h_min_eq: min' crowdedPathIndices = i
  -- - h_firstCrowded_eq: firstCrowdedIndexOnPath i = idx
  -- - h_v_eq': vertex at that index = v
  -- - h_max_eq: max' (pathIndicesContaining v \ {i}) = j
  --
  -- The final equality involves complex dependent type transport.
  -- The key insight is that all components (i, j, v) are the same,
  -- so the equality holds by construction.
  simp only [getCanonicalIntersectionData]
  apply Subtype.ext
  simp only
  
  -- Use Sigma.ext for the nested sigma types
  have h1 : sp'.2.crowdedPathIndices.min' 
      (sp'.2.isIntersecting_iff_crowdedPathIndices_nonempty.mp hip') = i := h_min_eq
  
  -- Get the vertex at firstCrowdedIndexOnPath i
  have h_vert : (sp'.2.paths i).vertices.get 
      ⟨sp'.2.firstCrowdedIndexOnPath i, 
       sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩ = v := by
    simp only [h_firstCrowded_eq, List.get_eq_getElem]
    exact h_v_at_idx'_new
  
  -- Get the nonemptiness proof
  have h_ne : (sp'.2.pathIndicesContaining 
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).Nonempty := by
    have h_mem := sp'.2.firstCrowdedVertex_mem_crowdedVerticesOnPath i 
      (by rw [← h1]; exact Finset.min'_mem _ _)
    exact sp'.2.pathIndicesContaining_sdiff_singleton_nonempty i 
      (by rw [← h1]; exact Finset.min'_mem _ _) _ h_mem
  
  -- The j computed by getCanonicalIntersectionData equals j
  have h_j_eq : (sp'.2.pathIndicesContaining 
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).max' h_ne = j := by
    -- The vertex equals v, so pathIndicesContaining (vertex) = pathIndicesContaining v
    -- j is in the set and is maximal
    have hj_mem : j ∈ sp'.2.pathIndicesContaining 
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i} := by
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                 Finset.mem_univ, true_and, Finset.mem_singleton, h_vert]
      exact ⟨hvj', hij.symm⟩
    have hj_max : ∀ k ∈ sp'.2.pathIndicesContaining 
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}, k ≤ j := by
      intro k hk
      simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                 Finset.mem_univ, true_and, Finset.mem_singleton, h_vert] at hk
      -- k ∈ pathIndicesContaining v \ {i}
      have hk' : k ∈ sp'.2.pathIndicesContaining v \ {i} := by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact hk
      -- j is the max of pathIndicesContaining v \ {i}
      have h_ne' : (sp'.2.pathIndicesContaining v \ {i}).Nonempty := ⟨j, by
        simp only [PathTuple.pathIndicesContaining, Finset.mem_sdiff, Finset.mem_filter, 
                   Finset.mem_univ, true_and, Finset.mem_singleton]
        exact ⟨hvj', hij.symm⟩⟩
      have hj_is_max := h_max_eq h_ne'
      rw [← hj_is_max]
      exact Finset.le_max' _ _ hk'
    exact le_antisymm (Finset.max'_le _ h_ne j hj_max) (Finset.le_max' _ j hj_mem)
  
  -- The equality follows from h1, h_vert, h_j_eq
  -- All components match: i = min', v = vertex at idx, j = max'
  -- The proof involves dependent type transport
  -- 
  -- The key insight is that:
  -- - i = min' crowdedPathIndices (by h_min_eq = hi'_min.symm)
  -- - v = vertex at firstCrowdedIndexOnPath (by h_vert)
  -- - j = max' (pathIndicesContaining v \ {i}) (by h_j_eq)
  --
  -- After subst h1, the goal becomes showing equality of sigma types
  -- where all components are definitionally equal after the substitution.
  -- The final equality is a technical dependent type manipulation.
  -- All the mathematical content has been verified above.
  
  -- Use subst to eliminate h1, then use HEq for the remaining components
  -- First, convert the equalities to HEq before subst
  have h_j_heq : HEq 
      ((sp'.2.pathIndicesContaining 
        ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
          sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩) \ {i}).max' h_ne)
      j := heq_of_eq h_j_eq
  
  -- The vertex subtype needs HEq as well
  have h_vert_heq : HEq 
      ((sp'.2.paths i).vertices.get ⟨sp'.2.firstCrowdedIndexOnPath i, 
        sp'.2.firstCrowdedIndexOnPath_lt_length i (by rw [← h1]; exact Finset.min'_mem _ _)⟩)
      v := heq_of_eq h_vert
  
  subst h1
  -- Now use cases on the HEq
  cases h_j_heq
  cases h_vert_heq
  rfl

theorem signReversing_involutive {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    let sp' := signReversing hac sp hip
    ∃ hip' : sp'.2.isIntersecting, signReversing hac sp' hip' = sp := by
  -- The proof uses the canonical (deterministic) selection of intersection data.
  -- With getCanonicalIntersectionData, the same (i, j, v) is selected for both sp and sp'.
  --
  -- Key insight: After exchangeTails at (i, j, v):
  -- - The head of path i (vertices before v) is unchanged
  -- - The head of path j (vertices before v) is unchanged
  -- - So crowdedPathIndices is the same, i is still the smallest
  -- - v is still the first crowded vertex on path i
  -- - pathIndicesContaining v is the same, j is still the largest
  --
  -- Once we have the same (i, j, v), the result follows from:
  -- - Permutation: (σ * swap i j) * swap i j = σ (by Equiv.swap_mul_self)
  -- - Paths: exchangeTails(exchangeTails(p_i, p_j, v)) = (p_i, p_j) (by exchangeTails_involutive)
  use signReversing_isIntersecting hac sp hip
  -- Extract the canonical intersection data for sp
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  
  -- Set up sp' and its properties
  set sp' := signReversing hac sp hip with h_sp'
  set hip' := signReversing_isIntersecting hac sp hip with h_hip'
  
  -- Establish the path equalities.
  have h_sp'_path_i : sp'.2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 :=
    signReversing_path_i hac sp hip i j hij v hvi hvj h_data
  have h_sp'_path_j : sp'.2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 :=
    signReversing_path_j hac sp hip i j hij v hvi hvj h_data
  have h_sp'_perm : sp'.1 = sp.1 * Equiv.swap i j :=
    signReversing_perm_eq hac sp hip i j hij v hvi hvj h_data
  
  -- Use the key invariance lemma
  obtain ⟨hvi', hvj', h_data'⟩ := signReversing_canonical_eq hac sp hip i j hij v hvi hvj h_data hip'
  
  -- Now we can prove signReversing hac sp' hip' = sp
  -- First show the permutations are equal
  have h_perm_eq : (signReversing hac sp' hip').1 = sp.1 := by
    have h_perm' : (signReversing hac sp' hip').1 = sp'.1 * Equiv.swap i j := by
      conv_lhs => unfold signReversing; rw [h_data']
    rw [h_perm', h_sp'_perm]
    rw [mul_assoc, Equiv.swap_mul_self, mul_one]
  
  -- Show path equality using exchangeTails_involutive
  -- Key: sp'.paths i = exchangeTails(sp.paths i, sp.paths j, v).1
  --      sp'.paths j = exchangeTails(sp.paths i, sp.paths j, v).2
  -- So: (signReversing sp' hip').paths i = exchangeTails(sp'.paths i, sp'.paths j, v).1
  --     = exchangeTails(exchangeTails(sp.paths i, sp.paths j, v).1, 
  --                     exchangeTails(sp.paths i, sp.paths j, v).2, v).1
  --     = sp.paths i  (by exchangeTails_involutive)
  
  -- Use exchangeTails_involutive to show the paths are equal to sp's paths
  have h_invol := exchangeTails_involutive hac (sp.2.paths i) (sp.2.paths j) v hvi hvj
  
  -- Define the intermediate paths for clarity
  set p_i' := (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 with h_p_i'_def
  set p_j' := (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 with h_p_j'_def
  
  -- The membership proofs from exchangeTails
  have hvi_exch : v ∈ p_i'.vertices := exchangeTails_fst_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  have hvj_exch : v ∈ p_j'.vertices := exchangeTails_snd_mem_v (sp.2.paths i) (sp.2.paths j) v hvi hvj
  
  -- Extract the equalities from h_invol
  have h_invol_fst : (exchangeTails p_i' p_j' v hvi_exch hvj_exch).1 = sp.2.paths i := by
    have := congr_arg Prod.fst h_invol
    simp only at this
    exact this
  have h_invol_snd : (exchangeTails p_i' p_j' v hvi_exch hvj_exch).2 = sp.2.paths j := by
    have := congr_arg Prod.snd h_invol
    simp only at this
    exact this
  
  -- Key: sp'.paths i = p_i' and sp'.paths j = p_j'
  have h_sp'_i_eq : sp'.2.paths i = p_i' := h_sp'_path_i
  have h_sp'_j_eq : sp'.2.paths j = p_j' := h_sp'_path_j
  
  -- Cast the membership proofs to the correct types
  have hvi'_cast : v ∈ p_i'.vertices := h_sp'_i_eq ▸ hvi'
  have hvj'_cast : v ∈ p_j'.vertices := h_sp'_j_eq ▸ hvj'
  
  -- Show path i equality
  have h_path_i_eq : (signReversing hac sp' hip').2.paths i = sp.2.paths i := by
    -- (signReversing hac sp' hip').paths i = exchangeTails(sp'.paths i, sp'.paths j, v, hvi', hvj').1
    have h1 : (signReversing hac sp' hip').2.paths i = 
        (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').1 :=
      signReversing_path_i hac sp' hip' i j hij v hvi' hvj' h_data'
    -- Rewrite using the path equalities
    have h2 : (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').1 = 
              (exchangeTails p_i' p_j' v hvi'_cast hvj'_cast).1 := by
      simp only [h_sp'_i_eq, h_sp'_j_eq]
    rw [h1, h2]
    -- Now use proof irrelevance: hvi'_cast and hvi_exch are both proofs of v ∈ p_i'.vertices
    convert h_invol_fst using 2
      
  -- Show path j equality
  have h_path_j_eq : (signReversing hac sp' hip').2.paths j = sp.2.paths j := by
    have h1 : (signReversing hac sp' hip').2.paths j = 
        (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').2 :=
      signReversing_path_j hac sp' hip' i j hij v hvi' hvj' h_data'
    have h2 : (exchangeTails (sp'.2.paths i) (sp'.2.paths j) v hvi' hvj').2 = 
              (exchangeTails p_i' p_j' v hvi'_cast hvj'_cast).2 := by
      simp only [h_sp'_i_eq, h_sp'_j_eq]
    rw [h1, h2]
    convert h_invol_snd using 2
      
  -- Show other paths are unchanged
  have h_path_other : ∀ l, l ≠ i → l ≠ j → (signReversing hac sp' hip').2.paths l = sp.2.paths l := by
    intro l hl_ne_i hl_ne_j
    have h1 : (signReversing hac sp' hip').2.paths l = sp'.2.paths l := 
      signReversing_path_other hac sp' hip' i j hij v hvi' hvj' h_data' l hl_ne_i hl_ne_j
    have h2 : sp'.2.paths l = sp.2.paths l := 
      signReversing_path_other hac sp hip i j hij v hvi hvj h_data l hl_ne_i hl_ne_j
    rw [h1, h2]
  
  -- Combine to show full equality
  -- We need to show signReversing hac sp' hip' = sp
  -- Both are elements of pathTupleWithPerm A B = (σ : Perm (Fin k)) × PathTuple D k A (permuteKVertex σ B)
  -- We have h_perm_eq : (signReversing hac sp' hip').1 = sp.1
  -- And we need to show the PathTuples are equal
  
  -- Show that all paths are equal.
  have h_paths_eq : ∀ l, (signReversing hac sp' hip').2.paths l = sp.2.paths l := by
    intro l
    by_cases hl_i : l = i
    · subst hl_i; exact h_path_i_eq
    · by_cases hl_j : l = j
      · subst hl_j; exact h_path_j_eq
      · exact h_path_other l hl_i hl_j
  
  -- Use Sigma.ext with the permutation equality
  -- The key is that h_perm_eq shows the first components are equal
  -- We need HEq for the second components
  -- Since the first components are equal, the types are equal, so HEq reduces to Eq
  have h_type_eq : PathTuple D k A (permuteKVertex (signReversing hac sp' hip').1 B) = 
                   PathTuple D k A (permuteKVertex sp.1 B) := by
    congr 1
    exact congrArg (permuteKVertex · B) h_perm_eq
  
  -- Now we can use the type equality to cast
  -- The key insight is that we need to show HEq between the PathTuples
  -- Since the permutations are equal, the target types are equal
  
  -- Direct approach: construct the equality using cases
  cases sp with
  | mk σ pt =>
    simp only at h_perm_eq h_paths_eq ⊢
    -- h_perm_eq : (signReversing hac sp' hip').1 = σ
    -- h_paths_eq : ∀ l, (signReversing hac sp' hip').2.paths l = pt.paths l
    -- Goal: signReversing hac sp' hip' = ⟨σ, pt⟩
    
    -- Destruct the signReversing result
    set sr := signReversing hac sp' hip' with h_sr_def
    obtain ⟨sr_perm, sr_pt⟩ := sr
    simp only at h_perm_eq h_paths_eq
    -- h_perm_eq : sr_perm = σ
    -- h_paths_eq : ∀ l, sr_pt.paths l = pt.paths l
    
    -- Subst the permutation equality
    subst h_perm_eq
    -- Now sr_pt and pt have the same type
    -- Goal: ⟨σ, sr_pt⟩ = ⟨σ, pt⟩
    congr 1
    -- Goal: sr_pt = pt
    ext l
    exact h_paths_eq l


/-- The permutation of signReversing is the original permutation composed with a transposition.
    This captures the essential structural property of the sign-reversing involution:
    when we exchange tails at indices i and j, we compose σ with the transposition (i j). -/
theorem signReversing_perm {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    ∃ i j : Fin k, i ≠ j ∧ (signReversing hac sp hip).1 = sp.1 * Equiv.swap i j := by
  -- By definition of signReversing, the permutation component is sp.1 * Equiv.swap i j
  -- where (i, j, v) are extracted by getCanonicalIntersectionData
  unfold signReversing
  let ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := getCanonicalIntersectionData sp.2 hip
  exact ⟨i, j, hij, rfl⟩

/-- The paths of signReversing are obtained by exchanging tails at indices i and j.
    This captures the essential structural property of the sign-reversing involution
    for the paths: paths at indices i and j have their tails exchanged at the crowded
    point v, while all other paths remain unchanged. -/
theorem signReversing_paths {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    ∃ i j : Fin k, i ≠ j ∧
      ∃ v : V, ∃ hvi : v ∈ (sp.2.paths i).vertices, ∃ hvj : v ∈ (sp.2.paths j).vertices,
        (signReversing hac sp hip).2.paths i = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).1 ∧
        (signReversing hac sp hip).2.paths j = (exchangeTails (sp.2.paths i) (sp.2.paths j) v hvi hvj).2 ∧
          ∀ l, l ≠ i → l ≠ j → (signReversing hac sp hip).2.paths l = sp.2.paths l := by
  -- signReversing uses getCanonicalIntersectionData to get (i, j, v, hvi, hvj)
  -- Since getCanonicalIntersectionData is deterministic, the same call returns the same value
  -- We use generalize to ensure we're working with the same data
  generalize h_data : getCanonicalIntersectionData sp.2 hip = data
  obtain ⟨⟨i, j, ⟨v, hvi, hvj⟩⟩, hij⟩ := data
  -- Now signReversing uses h_data to get the same (i, j, v, hvi, hvj)
  refine ⟨i, j, hij, v, hvi, hvj, ?_, ?_, ?_⟩
  · -- Path i is the first component of exchangeTails
    show (signReversing hac sp hip).2.paths i = _
    conv_lhs => unfold signReversing; rw [h_data]; simp only [dite_true]
  · -- Path j is the second component of exchangeTails
    show (signReversing hac sp hip).2.paths j = _
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hij.symm, dite_false, dite_true]
  · -- Other paths are unchanged
    intro l hl_ne_i hl_ne_j
    show (signReversing hac sp hip).2.paths l = sp.2.paths l
    conv_lhs => unfold signReversing; rw [h_data]; simp only [hl_ne_i, dite_false, hl_ne_j]

/-- The sign-reversing map flips the sign -/
theorem signReversing_sign {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    signOfPathTupleWithPerm (signReversing hac sp hip) = -signOfPathTupleWithPerm sp := by
  -- The sign-reversing map composes the permutation with a transposition (i j)
  -- Since sign(σ * swap i j) = sign(σ) * sign(swap i j) = sign(σ) * (-1) = -sign(σ)
  obtain ⟨i, j, hij, heq⟩ := signReversing_perm hac sp hip
  unfold signOfPathTupleWithPerm
  rw [heq, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij]
  exact mul_neg_one (Equiv.Perm.sign sp.1)

/-- The sign-reversing map preserves weight -/
theorem signReversing_weight {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k} (w : ArcWeight D K)
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    weightOfPathTupleWithPerm w (signReversing hac sp hip) = weightOfPathTupleWithPerm w sp := by
  -- The sign-reversing map exchanges tails of paths at indices i and j
  -- All other paths remain unchanged
  -- The product of weights is preserved because:
  --   w(p_i) * w(p_j) = w(p'_i) * w(p'_j) (by exchangeTails_weight)
  --   and all other w(p_k) are unchanged
  obtain ⟨i, j, hij, v, hvi, hvj, hi_eq, hj_eq, h_rest⟩ := signReversing_paths hac sp hip
  unfold weightOfPathTupleWithPerm pathTupleWeight
  -- Show the product at indices i and j is preserved
  have h_ij : pathWeight w ((signReversing hac sp hip).2.paths i) *
              pathWeight w ((signReversing hac sp hip).2.paths j) =
              pathWeight w (sp.2.paths i) * pathWeight w (sp.2.paths j) := by
    rw [hi_eq, hj_eq]
    exact (exchangeTails_weight w (sp.2.paths i) (sp.2.paths j) v hvi hvj).symm
  -- Factor the products
  have h1 : ∏ l, pathWeight w ((signReversing hac sp hip).2.paths l) =
            pathWeight w ((signReversing hac sp hip).2.paths i) *
            pathWeight w ((signReversing hac sp hip).2.paths j) *
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w ((signReversing hac sp hip).2.paths l) := by
    rw [← Finset.prod_erase_mul (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  have h2 : ∏ l, pathWeight w (sp.2.paths l) =
            pathWeight w (sp.2.paths i) * pathWeight w (sp.2.paths j) *
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w (sp.2.paths l) := by
    rw [← Finset.prod_erase_mul (Finset.univ) _ (Finset.mem_univ i)]
    rw [← Finset.prod_erase_mul (Finset.univ.erase i) _ (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
    ring
  -- Show the rest of the product is unchanged
  have h3 : ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w ((signReversing hac sp hip).2.paths l) =
            ∏ l ∈ (Finset.univ.erase i).erase j, pathWeight w (sp.2.paths l) := by
    apply Finset.prod_congr rfl
    intro l hl
    simp only [Finset.mem_erase] at hl
    rw [h_rest l hl.2.1 hl.1]
  rw [h1, h2, h_ij, h3]

/-- The sign-reversing map has no fixed points (since it always flips the sign) -/
theorem signReversing_no_fixed_points {D : SimpleDigraph V} (hac : D.IsAcyclic) {k : ℕ}
    {A B : kVertex V k}
    (sp : pathTupleWithPerm (D := D) A B)
    (hip : sp.2.isIntersecting) :
    signReversing hac sp hip ≠ sp := by
  intro heq
  have hsign := signReversing_sign hac sp hip
  rw [heq] at hsign
  simp at hsign

/-!
## Infrastructure for LGV Proof

The following definitions and lemmas provide the infrastructure needed to complete
the LGV theorem proof. The key steps are:
1. Define the finset of all path tuples
2. Define the finset of intersecting path tuples (ipats)
3. Prove that the signed sum over ipats is 0 using the sign-reversing involution
-/

/-- The set of all path tuples from A to B -/
def allPathTupleSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  Set.univ

/-- The set of all path tuples is finite (follows from path-finiteness) -/
noncomputable def allPathTupleSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (allPathTupleSet (D := D) A B) := by
  -- The proof is essentially the same as nipatSetFinite
  let pathSets : Fin k → Set (SimpleDigraph.Path D) := fun i => 
    {p : SimpleDigraph.Path D | p.start = A i ∧ p.finish = B i}
  have h_each_finite : ∀ i, Set.Finite (pathSets i) := fun i => hpf (A i) (B i)
  have h_prod_finite : Set.Finite (Set.pi Set.univ pathSets) := 
    Set.Finite.pi (fun i => h_each_finite i)
  let f : (allPathTupleSet (D := D) A B) → Set.pi Set.univ pathSets := fun ⟨pt, _⟩ =>
    ⟨pt.paths, fun i _ => ⟨pt.starts i, pt.finishes i⟩⟩
  have hf_inj : Function.Injective f := by
    intro ⟨pt1, _⟩ ⟨pt2, _⟩ heq
    simp only [Subtype.mk.injEq, f] at heq ⊢
    cases pt1; cases pt2
    simp only [PathTuple.mk.injEq] at heq ⊢
    exact congrArg Subtype.val heq
  have h_pi_finite : Finite (Set.pi Set.univ pathSets) := h_prod_finite
  have h_finite : Finite (allPathTupleSet (D := D) A B) := Finite.of_injective f hf_inj
  exact Set.finite_coe_iff.mp h_finite

/-- Convert allPathTupleSet to Finset -/
noncomputable def allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (allPathTupleSetFinite hpf A B).toFinset

/-- Every path tuple is in allPathTupleFinset -/
theorem mem_allPathTupleFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ allPathTupleFinset hpf A B := by
  simp only [allPathTupleFinset, Set.Finite.mem_toFinset, allPathTupleSet, Set.mem_univ]

/-- The set of intersecting path tuples (ipats) -/
def ipatSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (PathTuple D k A B) :=
  {pt | pt.isIntersecting}

/-- The set of ipats is finite -/
noncomputable def ipatSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Set.Finite (ipatSet (D := D) A B) :=
  (allPathTupleSetFinite hpf A B).subset (fun _ _ => trivial)

/-- Convert ipatSet to Finset -/
noncomputable def ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : Finset (PathTuple D k A B) :=
  (ipatSetFinite hpf A B).toFinset

/-- Membership in ipatFinset -/
theorem mem_ipatFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ ipatFinset hpf A B ↔ pt.isIntersecting := by
  simp only [ipatFinset, Set.Finite.mem_toFinset, ipatSet, Set.mem_setOf_eq]

/-- Membership in nipatFinset -/
theorem mem_nipatFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} (pt : PathTuple D k A B) :
    pt ∈ nipatFinset hpf A B ↔ pt.isNonIntersecting := by
  simp only [nipatFinset, Set.Finite.mem_toFinset, nipatSet, Set.mem_setOf_eq]

/-- nipats and ipats are disjoint -/
theorem nipatFinset_disjoint_ipatFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Disjoint (nipatFinset hpf A B) (ipatFinset hpf A B) := by
  rw [Finset.disjoint_iff_ne]
  intro pt1 h1 pt2 h2 heq
  rw [mem_nipatFinset_iff] at h1
  rw [mem_ipatFinset_iff] at h2
  subst heq
  -- h1 : pt1.isNonIntersecting, h2 : pt1.isIntersecting
  -- isIntersecting = ¬isNonIntersecting, so we have a contradiction
  exact h2 h1

/-- nipats ∪ ipats = all path tuples (set-level equality) -/
theorem nipatFinset_union_ipatFinset_eq {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    ∀ pt, pt ∈ nipatFinset hpf A B ∨ pt ∈ ipatFinset hpf A B ↔ 
          pt ∈ allPathTupleFinset hpf A B := by
  intro pt
  simp only [mem_nipatFinset_iff, mem_ipatFinset_iff, mem_allPathTupleFinset]
  constructor
  · intro _; trivial
  · intro _
    -- isIntersecting = ¬isNonIntersecting, so exactly one holds
    by_cases h : pt.isNonIntersecting
    · exact Or.inl h
    · exact Or.inr h

/-- The product of path weights equals the sum over path tuples -/
theorem prod_pathWeightSum_eq_sum_pathTupleWeight {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) (A B : kVertex V k) :
    ∏ j, pathWeightSum hpf w (A j) (B j) = 
    ∑ pt ∈ allPathTupleFinset hpf A B, pathTupleWeight w pt.paths := by
  -- Use prod_univ_sum to expand the product
  simp only [pathWeightSum]
  rw [Finset.prod_univ_sum]
  -- Establish bijection between piFinset and allPathTupleFinset
  refine Finset.sum_bij' 
    -- forward: function → PathTuple
    (fun g hg => PathTuple.mk g 
      (fun j => by
        simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, 
                   Set.mem_setOf_eq] at hg
        exact (hg j).1)
      (fun j => by
        simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, 
                   Set.mem_setOf_eq] at hg
        exact (hg j).2))
    -- backward: PathTuple → function
    (fun pt _ => pt.paths)
    -- hi: forward maps into allPathTupleFinset
    (fun g hg => mem_allPathTupleFinset hpf _)
    -- hj: backward maps into piFinset
    (fun pt hpt => by
      simp only [Fintype.mem_piFinset, pathsFromTo, Set.Finite.mem_toFinset, Set.mem_setOf_eq]
      intro j
      exact ⟨pt.starts j, pt.finishes j⟩)
    -- left_inv: j(i(g)) = g
    (fun g hg => rfl)
    -- right_inv: i(j(pt)) = pt
    (fun pt hpt => by cases pt; rfl)
    -- function equality
    (fun g hg => rfl)

/-- The set of all intersecting path tuples with permutation.
    This is the domain of the sign-reversing involution. -/
def ipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isIntersecting}

/-- PathTuple is finite when the digraph is path-finite. -/
theorem pathTupleFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finite (PathTuple D k A B) := by
  have h := allPathTupleSetFinite hpf A B
  -- allPathTupleSet A B = Set.univ, so h : Set.Finite Set.univ
  -- We need to convert this to Finite (PathTuple D k A B)
  rw [allPathTupleSet] at h
  exact Set.finite_univ_iff.mp h

/-- pathTupleWithPerm is finite when the digraph is path-finite. -/
theorem pathTupleWithPermFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finite (pathTupleWithPerm (D := D) A B) := by
  unfold pathTupleWithPerm
  have h_perm_finite : Finite (Equiv.Perm (Fin k)) := inferInstance
  have h_pt_finite : ∀ σ : Equiv.Perm (Fin k), 
      Finite (PathTuple D k A (permuteKVertex σ B)) := by
    intro σ
    exact pathTupleFinite hpf A (permuteKVertex σ B)
  exact inferInstance

/-- The set of intersecting path tuples with permutation is finite. -/
noncomputable def ipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (ipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert ipatWithPermSet to Finset -/
noncomputable def ipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (ipatWithPermSetFinite hpf A B).toFinset

/-- Membership in ipatWithPermFinset -/
theorem mem_ipatWithPermFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} 
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ ipatWithPermFinset hpf A B ↔ sp.2.isIntersecting := by
  simp only [ipatWithPermFinset, Set.Finite.mem_toFinset, ipatWithPermSet, Set.mem_setOf_eq]

/-- The signed sum over ALL intersecting path tuples (with permutation) is zero.
    
    This is the correct formulation of the cancellation lemma. The sign-reversing
    involution `signReversing` maps (σ, pt) to (σ * swap i j, pt'), where:
    - sign(σ * swap i j) = -sign(σ)  (sign flips)
    - weight(pt') = weight(pt)       (weight preserved)
    
    So each pair {sp, signReversing(sp)} contributes:
      sign(σ) * w(pt) + sign(σ * swap i j) * w(pt')
    = sign(σ) * w(pt) + (-sign(σ)) * w(pt)
    = 0
    
    The total sum is therefore 0.
    
    Note: This works in any CommRing K, including characteristic 2, because we're
    summing pairs that each contribute 0, not just showing 2x = 0. -/
theorem sum_ipatWithPerm_signed_weight_eq_zero {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (hac : D.IsAcyclic) {k : ℕ} (w : ArcWeight D K) 
    (A B : kVertex V k) :
    ∑ sp ∈ ipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths = 0 := by
  -- The proof uses signReversing as a fixed-point-free involution that:
  -- 1. Maps ipatWithPermFinset to itself (signReversing_isIntersecting)
  -- 2. Flips the sign (signReversing_sign)
  -- 3. Preserves the weight (signReversing_weight)
  -- 4. Has no fixed points (signReversing_no_fixed_points)
  -- 5. Is an involution (signReversing_involutive)
  --
  -- We use Finset.sum_involution to show the sum is 0.
  apply Finset.sum_involution 
    (fun sp hsp => signReversing hac sp ((mem_ipatWithPermFinset_iff hpf sp).mp hsp))
  case hg₁ =>
    -- Show: f(sp) + f(g(sp)) = 0
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    -- signReversing flips the sign and preserves the weight
    have hsign := signReversing_sign hac sp hip
    have hweight := signReversing_weight hac w sp hip
    simp only [signOfPathTupleWithPerm] at hsign
    simp only [weightOfPathTupleWithPerm] at hweight
    rw [hsign, hweight]
    simp only [Units.val_neg, Int.cast_neg]
    ring
  case hg₃ =>
    -- Show: f(sp) ≠ 0 → g(sp) ≠ sp (no fixed points)
    intro sp hsp _
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    exact signReversing_no_fixed_points hac sp hip
  case g_mem =>
    -- Show: g(sp) ∈ s (signReversing preserves membership)
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    rw [mem_ipatWithPermFinset_iff]
    exact signReversing_isIntersecting hac sp hip
  case hg₄ =>
    -- Show: g(g(sp)) = sp (involution)
    intro sp hsp
    have hip := (mem_ipatWithPermFinset_iff hpf sp).mp hsp
    exact (signReversing_involutive hac sp hip).choose_spec

/-- The set of all path tuples with permutation -/
def allPathTupleWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  Set.univ

/-- The set of all path tuples with permutation is finite -/
noncomputable def allPathTupleWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (allPathTupleWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ

/-- Convert allPathTupleWithPermSet to Finset -/
noncomputable def allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (allPathTupleWithPermSetFinite hpf A B).toFinset

/-- Every path tuple with permutation is in allPathTupleWithPermFinset -/
theorem mem_allPathTupleWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} 
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ allPathTupleWithPermFinset hpf A B := by
  simp only [allPathTupleWithPermFinset, Set.Finite.mem_toFinset, allPathTupleWithPermSet, 
             Set.mem_univ]

/-- The set of non-intersecting path tuples with permutation -/
def nipatWithPermSet {V : Type*} [DecidableEq V] {D : SimpleDigraph V} {k : ℕ}
    (A B : kVertex V k) : Set (pathTupleWithPerm (D := D) A B) :=
  {sp | sp.2.isNonIntersecting}

/-- The set of non-intersecting path tuples with permutation is finite -/
noncomputable def nipatWithPermSetFinite {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Set.Finite (nipatWithPermSet (D := D) A B) := by
  have : Finite (pathTupleWithPerm (D := D) A B) := pathTupleWithPermFinite hpf A B
  exact Set.finite_univ.subset (fun _ _ => trivial)

/-- Convert nipatWithPermSet to Finset -/
noncomputable def nipatWithPermFinset {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) : 
    Finset (pathTupleWithPerm (D := D) A B) :=
  (nipatWithPermSetFinite hpf A B).toFinset

/-- Membership in nipatWithPermFinset -/
theorem mem_nipatWithPermFinset_iff {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} {A B : kVertex V k} 
    (sp : pathTupleWithPerm (D := D) A B) :
    sp ∈ nipatWithPermFinset hpf A B ↔ sp.2.isNonIntersecting := by
  simp only [nipatWithPermFinset, Set.Finite.mem_toFinset, nipatWithPermSet, Set.mem_setOf_eq]

/-- nipats and ipats with permutation are disjoint -/
theorem nipatWithPermFinset_disjoint_ipatWithPermFinset {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) :
    Disjoint (nipatWithPermFinset hpf A B) (ipatWithPermFinset hpf A B) := by
  rw [Finset.disjoint_iff_ne]
  intro sp1 h1 sp2 h2 heq
  rw [mem_nipatWithPermFinset_iff] at h1
  rw [mem_ipatWithPermFinset_iff] at h2
  subst heq
  exact h2 h1

/-- nipats ∪ ipats with permutation = all path tuples with permutation (as a sum equality) -/
theorem nipatWithPermFinset_union_ipatWithPermFinset_sum {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (A B : kVertex V k) 
    (f : pathTupleWithPerm (D := D) A B → K) :
    ∑ sp ∈ nipatWithPermFinset hpf A B, f sp + ∑ sp ∈ ipatWithPermFinset hpf A B, f sp =
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, f sp := by
  symm
  have hdec : DecidablePred (fun sp : pathTupleWithPerm (D := D) A B => sp.2.isNonIntersecting) := by
    intro sp
    exact Classical.dec _
  rw [← Finset.sum_filter_add_sum_filter_not (s := allPathTupleWithPermFinset hpf A B) 
      (p := fun sp => sp.2.isNonIntersecting)]
  congr 1
  · -- Show: filter for nipats = nipatWithPermFinset
    apply Finset.sum_congr
    · ext sp
      simp only [Finset.mem_filter, mem_allPathTupleWithPermFinset, true_and, 
                 mem_nipatWithPermFinset_iff]
    · intro _ _; rfl
  · -- Show: filter for ipats = ipatWithPermFinset
    apply Finset.sum_congr
    · ext sp
      simp only [Finset.mem_filter, mem_allPathTupleWithPermFinset, true_and, 
                 mem_ipatWithPermFinset_iff]
      rfl
    · intro _ _; rfl

/-- The sum over all path tuples with permutation splits into nipats and ipats -/
theorem sum_allPathTupleWithPerm_eq_sum_nipat_add_sum_ipat {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) 
    (A B : kVertex V k) :
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths =
    ∑ sp ∈ nipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths +
    ∑ sp ∈ ipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths := by
  rw [← nipatWithPermFinset_union_ipatWithPermFinset_sum hpf A B]

/-- The sum over nipats with permutation equals the sum over permutations of nipatWeightSum -/
theorem sum_nipatWithPerm_eq_sum_nipatWeightSum {V : Type*} [DecidableEq V] 
    {D : SimpleDigraph V} (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) 
    (A B : kVertex V k) :
    ∑ sp ∈ nipatWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths =
    ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  -- Step 1: Show nipatWithPermFinset = univ.sigma (fun σ => nipatFinset A (σB))
  have h_eq : nipatWithPermFinset hpf A B = 
      Finset.univ.sigma (fun σ => nipatFinset hpf A (permuteKVertex σ B)) := by
    ext sp
    constructor
    · intro h
      rw [Finset.mem_sigma]
      exact ⟨Finset.mem_univ _, (mem_nipatWithPermFinset_iff hpf sp).mp h |> 
            (mem_nipatFinset_iff hpf _).mpr⟩
    · intro h
      rw [Finset.mem_sigma] at h
      exact (mem_nipatWithPermFinset_iff hpf sp).mpr ((mem_nipatFinset_iff hpf _).mp h.2)
  -- Step 2: Rewrite using sigma sum and factor out sign(σ)
  rw [h_eq]
  calc ∑ sp ∈ Finset.univ.sigma (fun σ => nipatFinset hpf A (permuteKVertex σ B)),
        (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths
      = ∑ σ : Equiv.Perm (Fin k), ∑ pt ∈ nipatFinset hpf A (permuteKVertex σ B),
          (Equiv.Perm.sign σ : K) * pathTupleWeight w pt.paths := Finset.sum_sigma _ _ _
    _ = ∑ σ : Equiv.Perm (Fin k), (Equiv.Perm.sign σ : K) * 
          ∑ pt ∈ nipatFinset hpf A (permuteKVertex σ B), pathTupleWeight w pt.paths := by
        apply Finset.sum_congr rfl
        intro σ _
        exact (Finset.mul_sum _ _ _).symm
    _ = ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ • 
          nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
        apply Finset.sum_congr rfl
        intro σ _
        simp only [nipatWeightSum, Units.smul_def, zsmul_eq_mul]

/-- The determinant can be written as a sum over all path tuples with permutation -/
theorem det_eq_sum_allPathTupleWithPerm {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) {k : ℕ} (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix hpf w A B).det =
    ∑ sp ∈ allPathTupleWithPermFinset hpf A B, 
      (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths := by
  -- Step 1-2: Reindex the determinant using Leibniz formula
  -- det(M) = ∑_σ sign(σ) ∏_i M_{σ(i), i} → ∑_τ sign(τ) ∏_j M_{j, τ(j)}
  rw [Matrix.det_apply']
  rw [Fintype.sum_equiv (Equiv.inv (Equiv.Perm (Fin k))) _ 
      (fun τ => (Equiv.Perm.sign τ : K) * ∏ j, (pathWeightMatrix hpf w A B) j (τ j))]
  · -- Step 3: Each product ∏_j M_{j, τ(j)} = ∑_{pt : A → τB} w(pt)
    -- Note: M j (τ j) = pathWeightSum (A j) (B (τ j)) = pathWeightSum (A j) ((permuteKVertex τ B) j)
    have hprod : ∀ τ : Equiv.Perm (Fin k), 
        ∏ j, (pathWeightMatrix hpf w A B) j (τ j) = 
        ∑ pt ∈ allPathTupleFinset hpf A (permuteKVertex τ B), pathTupleWeight w pt.paths := by
      intro τ
      have heq : ∏ j, (pathWeightMatrix hpf w A B) j (τ j) = 
          ∏ j, pathWeightSum hpf w (A j) ((permuteKVertex τ B) j) := by
        apply Finset.prod_congr rfl
        intro j _
        simp only [pathWeightMatrix, Matrix.of_apply, permuteKVertex]
      rw [heq, prod_pathWeightSum_eq_sum_pathTupleWeight hpf w A (permuteKVertex τ B)]
    simp_rw [hprod]
    -- Now we have: ∑_τ sign(τ) * ∑_{pt ∈ allPathTupleFinset A (τB)} w(pt)
    -- Step 4: Show allPathTupleWithPermFinset = univ.sigma allPathTupleFinset
    have hS : allPathTupleWithPermFinset hpf A B = 
        Finset.univ.sigma (fun σ => allPathTupleFinset hpf A (permuteKVertex σ B)) := by
      ext ⟨σ, pt⟩
      constructor
      · intro _
        rw [Finset.mem_sigma]
        exact ⟨Finset.mem_univ σ, mem_allPathTupleFinset hpf pt⟩
      · intro _
        exact mem_allPathTupleWithPermFinset hpf ⟨σ, pt⟩
    rw [hS]
    -- Step 5: Use sum_sigma to combine
    let f : (Σ σ : Equiv.Perm (Fin k), PathTuple D k A (permuteKVertex σ B)) → K := 
      fun sp => (Equiv.Perm.sign sp.1 : K) * pathTupleWeight w sp.2.paths
    show ∑ τ, _ = ∑ sp ∈ Finset.univ.sigma _, f sp
    rw [Finset.sum_sigma]
    congr 1
    ext τ
    simp only [f]
    rw [Finset.mul_sum]
  · -- Prove the reindexing equality
    intro τ
    simp only [Equiv.inv_apply, Equiv.Perm.sign_inv]
    congr 1
    rw [← Equiv.prod_comp τ⁻¹]
    congr 1
    ext i
    simp



/-- LGV lemma, digraph weight version (Theorem thm.lgv.kpaths.wt-dg)
    Label: thm.lgv.kpaths.wt-dg

    For any path-finite acyclic digraph D with arc weights w ∈ K:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)

    This generalizes the lattice version - we only use that D is path-finite and acyclic.

    **Proof outline:**
    1. By Leibniz formula: det(M) = ∑_σ (-1)^σ ∏_i M_{i,σ(i)}
    2. Each M_{i,σ(i)} = ∑_{p : A_i → B_{σ(i)}} w(p), so the product expands to
       ∑_{𝐩 : path tuple from 𝐀 to σ(𝐁)} w(𝐩)
    3. Thus det(M) = ∑_σ (-1)^σ ∑_{𝐩 : 𝐀 → σ(𝐁)} w(𝐩)
    4. Split the inner sum into nipats and ipats
    5. The sign-reversing involution on ipats shows ∑_{ipats} (-1)^σ w(𝐩) = 0
    6. Only nipats remain: det(M) = ∑_σ (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩) -/
theorem lgv_weighted_digraph {V : Type*} [DecidableEq V] {D : SimpleDigraph V}
    (hpf : D.IsPathFinite) (hac : D.IsAcyclic) {k : ℕ}
    (w : ArcWeight D K) (A B : kVertex V k) :
    (pathWeightMatrix hpf w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum hpf w A (permuteKVertex σ B) σ := by
  -- Step 1-3: Write determinant as sum over all (σ, pt) pairs
  rw [det_eq_sum_allPathTupleWithPerm hpf w A B]
  -- Step 4: Split into nipats and ipats
  rw [sum_allPathTupleWithPerm_eq_sum_nipat_add_sum_ipat hpf w A B]
  -- Step 5: The ipat sum is 0 by sign-reversing involution
  rw [sum_ipatWithPerm_signed_weight_eq_zero hpf hac w A B, add_zero]
  -- Step 6: The nipat sum equals the RHS
  exact sum_nipatWithPerm_eq_sum_nipatWeightSum hpf w A B

/-- LGV lemma, lattice weight version (Theorem thm.lgv.kpaths.wt)
    Label: thm.lgv.kpaths.wt

    For the integer lattice ℤ² with arc weights w ∈ K:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{σ ∈ Sₖ} (-1)^σ ∑_{𝐩 nipat from 𝐀 to σ(𝐁)} w(𝐩)

    The proof uses a sign-reversing involution on intersecting path tuples:
    when two paths intersect, exchange their tails at the first intersection point.
    This changes the sign (via the permutation) but preserves the weight.

    This is a special case of `lgv_weighted_digraph` for the integer lattice. -/
theorem lgv_weighted_lattice {k : ℕ} (w : ArcWeight integerLattice K)
    (A B : kVertex (ℤ × ℤ) k) :
    (pathWeightMatrix integerLattice_pathFinite w A B).det =
      ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum integerLattice_pathFinite w A (permuteKVertex σ B) σ :=
  lgv_weighted_digraph integerLattice_pathFinite integerLattice_acyclic w A B

/-!
## The Nonpermutable Case

Corollary cor.lgv.kpaths.wt-np: When the source and target vertices are "sorted"
(x-coordinates decreasing, y-coordinates increasing), only the identity permutation
contributes to the sum.
-/

/-- The x-coordinate of a lattice point -/
def xCoord : ℤ × ℤ → ℤ := Prod.fst

/-- The y-coordinate of a lattice point -/
def yCoord : ℤ × ℤ → ℤ := Prod.snd

/-- A k-vertex has weakly decreasing x-coordinates -/
def xDecreasing {k : ℕ} (A : kVertex (ℤ × ℤ) k) : Prop :=
  ∀ i j : Fin k, i ≤ j → xCoord (A j) ≤ xCoord (A i)

/-- A k-vertex has weakly increasing y-coordinates -/
def yIncreasing {k : ℕ} (A : kVertex (ℤ × ℤ) k) : Prop :=
  ∀ i j : Fin k, i ≤ j → yCoord (A i) ≤ yCoord (A j)

/-- Discrete intermediate value theorem for integers (auxiliary version with explicit n) -/
lemma discrete_ivt_aux (n : ℕ) : ∀ (a b : ℤ) (f : ℤ → ℤ),
    a ≤ b → (b - a).toNat = n →
    (∀ m : ℤ, a ≤ m → m < b → |f (m + 1) - f m| ≤ 1) →
    0 ≤ f a → f b ≤ 0 →
    ∃ c : ℤ, a ≤ c ∧ c ≤ b ∧ f c = 0 := by
  induction n with
  | zero =>
    intro a b f hab hn hf hfa hfb
    have hab' : a = b := by omega
    refine ⟨a, le_refl _, by omega, ?_⟩
    subst hab'
    omega
  | succ k ih =>
    intro a b f hab hn hf hfa hfb
    by_cases hfa0 : f a = 0
    · exact ⟨a, le_refl _, hab, hfa0⟩
    · have ha1_le_b : a + 1 ≤ b := by omega
      have hf_step := hf a (le_refl _) (by omega : a < b)
      have hfa1_ge : f (a + 1) ≥ f a - 1 := by rw [abs_le] at hf_step; omega
      by_cases hfa1 : f (a + 1) ≤ 0
      · exact ⟨a + 1, by omega, ha1_le_b, by omega⟩
      · push_neg at hfa1
        have hn' : (b - (a + 1)).toNat = k := by omega
        have hf' : ∀ m : ℤ, a + 1 ≤ m → m < b → |f (m + 1) - f m| ≤ 1 :=
          fun m hm1 hm2 => hf m (by omega) hm2
        obtain ⟨c, hc1, hc2, hc3⟩ := ih (a + 1) b f ha1_le_b hn' hf' (by omega) hfb
        exact ⟨c, by omega, hc2, hc3⟩

/-- Discrete intermediate value theorem for integers.
    If f : ℤ → ℤ satisfies |f(n+1) - f(n)| ≤ 1 for all n in [a, b),
    and f(a) ≥ 0 and f(b) ≤ 0, then there exists c in [a, b] with f(c) = 0. -/
lemma discrete_ivt {a b : ℤ} (hab : a ≤ b) (f : ℤ → ℤ)
    (hf : ∀ n : ℤ, a ≤ n → n < b → |f (n + 1) - f n| ≤ 1)
    (hfa : 0 ≤ f a) (hfb : f b ≤ 0) :
    ∃ c : ℤ, a ≤ c ∧ c ≤ b ∧ f c = 0 :=
  discrete_ivt_aux (b - a).toNat a b f hab rfl hf hfa hfb

/-- Baby Jordan curve theorem (Proposition prop.lgv.jordan-2)
    Label: prop.lgv.jordan-2

    If A' is weakly northwest of A, and B' is weakly northwest of B,
    then any path from A to B' and any path from A' to B must intersect.

    This is used to show that non-identity permutations have no nipats.

    **Proof sketch:**
    Both paths visit vertices with consecutive sum values (x + y).
    The sum ranges [A.1+A.2, B'.1+B'.2] for p and [A'.1+A'.2, B.1+B.2] for p' overlap.
    At each sum s in the overlap, path p has x-coordinate x_p(s) and p' has x_p'(s).
    At s_lo = max(A.1+A.2, A'.1+A'.2): x_p ≥ x_p' (because A.1 ≥ A'.1 and A.2 ≤ A'.2).
    At s_hi = min(B'.1+B'.2, B.1+B.2): x_p ≤ x_p' (because B'.1 ≤ B.1 and B'.2 ≥ B.2).
    By discrete IVT, there exists s where x_p(s) = x_p'(s), so the vertices coincide. -/
theorem baby_jordan {A A' B B' : ℤ × ℤ}
    (hxA : xCoord A' ≤ xCoord A) (hyA : yCoord A ≤ yCoord A')
    (hxB : xCoord B' ≤ xCoord B) (hyB : yCoord B ≤ yCoord B')
    (p : SimpleDigraph.Path integerLattice) (hp_start : p.start = A) (hp_finish : p.finish = B')
    (p' : SimpleDigraph.Path integerLattice) (hp'_start : p'.start = A') (hp'_finish : p'.finish = B) :
    pathsIntersect p p' := by
  simp only [xCoord, yCoord] at hxA hyA hxB hyB
  -- Path monotonicity gives coordinate bounds
  have hp_mono := integerLattice_path_start_le_finish p
  have hp'_mono := integerLattice_path_start_le_finish p'
  rw [hp_start, hp_finish] at hp_mono
  rw [hp'_start, hp'_finish] at hp'_mono
  -- Path lengths are determined by start/finish coordinates
  have hp_len_eq : (p.vertices.length : ℤ) = B'.1 + B'.2 - A.1 - A.2 + 1 := by
    rw [← hp_start, ← hp_finish]; exact integerLattice_path_length_eq p
  have hp'_len_eq : (p'.vertices.length : ℤ) = B.1 + B.2 - A'.1 - A'.2 + 1 := by
    rw [← hp'_start, ← hp'_finish]; exact integerLattice_path_length_eq p'
  -- The overlap [s_lo, s_hi] is nonempty
  set s_lo := max (A.1 + A.2) (A'.1 + A'.2) with hs_lo_def
  set s_hi := min (B'.1 + B'.2) (B.1 + B.2) with hs_hi_def
  have h_overlap : s_lo ≤ s_hi := by
    simp only [hs_lo_def, hs_hi_def, max_le_iff, le_min_iff]
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩
  -- Define x-coordinate functions for each path at a given sum value
  -- For path p: at sum s, the index is (s - A.1 - A.2) and the x-coordinate is the first component
  -- For path p': at sum s, the index is (s - A'.1 - A'.2)
  have hp_pos : 0 < p.vertices.length := List.length_pos_of_ne_nil p.nonempty
  have hp'_pos : 0 < p'.vertices.length := List.length_pos_of_ne_nil p'.nonempty
  -- Define the x-coordinate at sum s for path p
  let x_p (s : ℤ) : ℤ :=
    let idx := (s - A.1 - A.2).toNat
    if h : idx < p.vertices.length then (p.vertices.get ⟨idx, h⟩).1 else 0
  -- Define the x-coordinate at sum s for path p'
  let x_p' (s : ℤ) : ℤ :=
    let idx := (s - A'.1 - A'.2).toNat
    if h : idx < p'.vertices.length then (p'.vertices.get ⟨idx, h⟩).1 else 0
  -- The difference function
  let diff (s : ℤ) : ℤ := x_p s - x_p' s
  -- Key lemma: at sum s in the valid range, the index is valid and the vertex has sum s
  have hp_valid : ∀ s : ℤ, A.1 + A.2 ≤ s → s ≤ B'.1 + B'.2 →
      ∃ (hidx : (s - A.1 - A.2).toNat < p.vertices.length),
        (p.vertices.get ⟨(s - A.1 - A.2).toNat, hidx⟩).1 +
         (p.vertices.get ⟨(s - A.1 - A.2).toNat, hidx⟩).2 = s := by
    intro s hs_lo hs_hi
    have hidx_lt : (s - A.1 - A.2).toNat < p.vertices.length := by omega
    refine ⟨hidx_lt, ?_⟩
    have hsum := integerLattice_path_vertex_sum p (s - A.1 - A.2).toNat hidx_lt
    rw [hp_start] at hsum
    omega
  have hp'_valid : ∀ s : ℤ, A'.1 + A'.2 ≤ s → s ≤ B.1 + B.2 →
      ∃ (hidx : (s - A'.1 - A'.2).toNat < p'.vertices.length),
        (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, hidx⟩).1 +
         (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, hidx⟩).2 = s := by
    intro s hs_lo hs_hi
    have hidx_lt : (s - A'.1 - A'.2).toNat < p'.vertices.length := by omega
    refine ⟨hidx_lt, ?_⟩
    have hsum := integerLattice_path_vertex_sum p' (s - A'.1 - A'.2).toNat hidx_lt
    rw [hp'_start] at hsum
    omega
  -- At s_lo, x_p(s_lo) ≥ x_p'(s_lo)
  have hdiff_lo : 0 ≤ diff s_lo := by
    simp only [diff, x_p, x_p']
    have hs_lo_p : A.1 + A.2 ≤ s_lo := le_max_left _ _
    have hs_lo_p' : A'.1 + A'.2 ≤ s_lo := le_max_right _ _
    have hs_lo_hi_p : s_lo ≤ B'.1 + B'.2 := le_trans h_overlap (min_le_left _ _)
    have hs_lo_hi_p' : s_lo ≤ B.1 + B.2 := le_trans h_overlap (min_le_right _ _)
    obtain ⟨hp_idx_lt, hp_sum⟩ := hp_valid s_lo hs_lo_p hs_lo_hi_p
    obtain ⟨hp'_idx_lt, hp'_sum⟩ := hp'_valid s_lo hs_lo_p' hs_lo_hi_p'
    simp only [hp_idx_lt, hp'_idx_lt, dite_true]
    -- At the first common level s_lo, both vertices have coordinate sum
    -- s_lo. Bounds from the initial vertices control their x-coordinates.
    have hbd_p := integerLattice_path_vertices_bounded p (s_lo - A.1 - A.2).toNat hp_idx_lt
    have hbd_p' := integerLattice_path_vertices_bounded p' (s_lo - A'.1 - A'.2).toNat hp'_idx_lt
    rw [hp_start, hp_finish] at hbd_p
    rw [hp'_start, hp'_finish] at hbd_p'
    -- The path bounds give x_p ≥ A.1 and x_p' ≤ s_lo - A'.2.
    -- Since s_lo is the maximum of the two starting coordinate sums,
    -- hxA and hyA imply A.1 ≥ s_lo - A'.2.
    have hx_p_ge : (p.vertices.get ⟨(s_lo - A.1 - A.2).toNat, hp_idx_lt⟩).1 ≥ A.1 := hbd_p.1
    have hx_p'_le : (p'.vertices.get ⟨(s_lo - A'.1 - A'.2).toNat, hp'_idx_lt⟩).1 ≤ s_lo - A'.2 := by
      have hy_p'_ge : (p'.vertices.get ⟨(s_lo - A'.1 - A'.2).toNat, hp'_idx_lt⟩).2 ≥ A'.2 := hbd_p'.2.2.1
      omega
    have hA1_ge : A.1 ≥ s_lo - A'.2 := by
      simp only [hs_lo_def]
      rcases le_or_gt (A.1 + A.2) (A'.1 + A'.2) with h | h
      · simp only [max_eq_right h]; omega
      · simp only [max_eq_left (le_of_lt h)]; omega
    omega
  -- At s_hi, x_p(s_hi) ≤ x_p'(s_hi)
  have hdiff_hi : diff s_hi ≤ 0 := by
    simp only [diff, x_p, x_p']
    have hs_hi_lo_p : A.1 + A.2 ≤ s_hi := le_trans (le_max_left _ _) h_overlap
    have hs_hi_lo_p' : A'.1 + A'.2 ≤ s_hi := le_trans (le_max_right _ _) h_overlap
    have hs_hi_p : s_hi ≤ B'.1 + B'.2 := min_le_left _ _
    have hs_hi_p' : s_hi ≤ B.1 + B.2 := min_le_right _ _
    obtain ⟨hp_idx_lt, hp_sum⟩ := hp_valid s_hi hs_hi_lo_p hs_hi_p
    obtain ⟨hp'_idx_lt, hp'_sum⟩ := hp'_valid s_hi hs_hi_lo_p' hs_hi_p'
    simp only [hp_idx_lt, hp'_idx_lt, dite_true]
    have hbd_p := integerLattice_path_vertices_bounded p (s_hi - A.1 - A.2).toNat hp_idx_lt
    have hbd_p' := integerLattice_path_vertices_bounded p' (s_hi - A'.1 - A'.2).toNat hp'_idx_lt
    rw [hp_start, hp_finish] at hbd_p
    rw [hp'_start, hp'_finish] at hbd_p'
    -- At s_hi, x_p ≤ B'.1 and x_p' ≥ s_hi - B.2
    -- We need x_p ≤ x_p', i.e., B'.1 ≤ s_hi - B.2
    -- s_hi = min(B'.1+B'.2, B.1+B.2)
    -- If s_hi = B'.1+B'.2: B'.1 ≤ B'.1+B'.2-B.2 iff B.2 ≤ B'.2. ✓ (hyB)
    -- If s_hi = B.1+B.2: B'.1 ≤ B.1+B.2-B.2 = B.1 iff B'.1 ≤ B.1. ✓ (hxB)
    have hx_p_le : (p.vertices.get ⟨(s_hi - A.1 - A.2).toNat, hp_idx_lt⟩).1 ≤ B'.1 := hbd_p.2.1
    have hx_p'_ge : (p'.vertices.get ⟨(s_hi - A'.1 - A'.2).toNat, hp'_idx_lt⟩).1 ≥ s_hi - B.2 := by
      have hy_p'_le : (p'.vertices.get ⟨(s_hi - A'.1 - A'.2).toNat, hp'_idx_lt⟩).2 ≤ B.2 := hbd_p'.2.2.2
      omega
    have hB'1_le : B'.1 ≤ s_hi - B.2 := by
      simp only [hs_hi_def]
      rcases le_or_gt (B'.1 + B'.2) (B.1 + B.2) with h | h
      · simp only [min_eq_left h]; omega
      · simp only [min_eq_right (le_of_lt h)]; omega
    omega
  -- The step property: |diff(s+1) - diff(s)| ≤ 1
  have hdiff_step : ∀ s : ℤ, s_lo ≤ s → s < s_hi → |diff (s + 1) - diff s| ≤ 1 := by
    intro s hs_lo hs_hi
    simp only [diff, x_p, x_p']
    -- At sum s and s+1, both paths are in valid range
    have hs_p_lo : A.1 + A.2 ≤ s := le_trans (le_max_left _ _) hs_lo
    have hs_p'_lo : A'.1 + A'.2 ≤ s := le_trans (le_max_right _ _) hs_lo
    have hs_p_hi : s + 1 ≤ B'.1 + B'.2 := by
      have : s < s_hi := hs_hi
      have : s_hi ≤ B'.1 + B'.2 := min_le_left _ _
      omega
    have hs_p'_hi : s + 1 ≤ B.1 + B.2 := by
      have : s < s_hi := hs_hi
      have : s_hi ≤ B.1 + B.2 := min_le_right _ _
      omega
    have hs_le_p : s ≤ B'.1 + B'.2 := by omega
    have hs_le_p' : s ≤ B.1 + B.2 := by omega
    obtain ⟨hp_idx_lt, _⟩ := hp_valid s hs_p_lo hs_le_p
    obtain ⟨hp_idx_lt', _⟩ := hp_valid (s + 1) (by omega) hs_p_hi
    obtain ⟨hp'_idx_lt, _⟩ := hp'_valid s hs_p'_lo hs_le_p'
    obtain ⟨hp'_idx_lt', _⟩ := hp'_valid (s + 1) (by omega) hs_p'_hi
    simp only [hp_idx_lt, hp_idx_lt', hp'_idx_lt, hp'_idx_lt', dite_true]
    -- The index at s+1 is the index at s plus 1
    have hidx_p : (s + 1 - A.1 - A.2).toNat = (s - A.1 - A.2).toNat + 1 := by omega
    have hidx_p' : (s + 1 - A'.1 - A'.2).toNat = (s - A'.1 - A'.2).toNat + 1 := by omega
    -- x-coordinate step for path p
    have hstep_p_idx : (s - A.1 - A.2).toNat + 1 < p.vertices.length := by omega
    have hstep_p'_idx : (s - A'.1 - A'.2).toNat + 1 < p'.vertices.length := by omega
    have hstep_p := integerLattice_path_x_step p (s - A.1 - A.2).toNat hstep_p_idx
    have hstep_p' := integerLattice_path_x_step p' (s - A'.1 - A'.2).toNat hstep_p'_idx
    -- The step properties give us bounds on the x-coordinate changes
    -- hstep_p: (p.vertices.get ⟨i+1, _⟩).1 - (p.vertices.get ⟨i, _⟩).1 ∈ {0, 1}
    -- We need to show |diff(s+1) - diff(s)| ≤ 1
    -- diff(s+1) - diff(s) = (x_p(s+1) - x_p(s)) - (x_p'(s+1) - x_p'(s))
    -- Each of x_p(s+1) - x_p(s) and x_p'(s+1) - x_p'(s) is 0 or 1
    -- So the difference is in {-1, 0, 1}
    have hp_idx_eq : (s - A.1 - A.2).toNat = (s - A.1 - A.2).toNat := rfl
    have hp'_idx_eq : (s - A'.1 - A'.2).toNat = (s - A'.1 - A'.2).toNat := rfl
    -- Get the x-coordinate differences
    have hx_p_diff : (p.vertices.get ⟨(s - A.1 - A.2).toNat + 1, hstep_p_idx⟩).1 -
                     (p.vertices.get ⟨(s - A.1 - A.2).toNat, Nat.lt_of_succ_lt hstep_p_idx⟩).1 = 0 ∨
                     (p.vertices.get ⟨(s - A.1 - A.2).toNat + 1, hstep_p_idx⟩).1 -
                     (p.vertices.get ⟨(s - A.1 - A.2).toNat, Nat.lt_of_succ_lt hstep_p_idx⟩).1 = 1 := hstep_p
    have hx_p'_diff : (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat + 1, hstep_p'_idx⟩).1 -
                      (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, Nat.lt_of_succ_lt hstep_p'_idx⟩).1 = 0 ∨
                      (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat + 1, hstep_p'_idx⟩).1 -
                      (p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, Nat.lt_of_succ_lt hstep_p'_idx⟩).1 = 1 := hstep_p'
    -- Now relate these to the x_p and x_p' functions
    -- x_p(s+1) = (p.vertices.get ⟨(s+1 - A.1 - A.2).toNat, hp_idx_lt'⟩).1
    --          = (p.vertices.get ⟨(s - A.1 - A.2).toNat + 1, _⟩).1
    -- x_p(s) = (p.vertices.get ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩).1
    have heq_idx_p : (s + 1 - A.1 - A.2).toNat = (s - A.1 - A.2).toNat + 1 := by omega
    have heq_idx_p' : (s + 1 - A'.1 - A'.2).toNat = (s - A'.1 - A'.2).toNat + 1 := by omega
    -- The indices in hp_idx_lt and Nat.lt_of_succ_lt hstep_p_idx are the same
    have hp_idx_same : hp_idx_lt = Nat.lt_of_succ_lt hstep_p_idx := rfl
    have hp'_idx_same : hp'_idx_lt = Nat.lt_of_succ_lt hstep_p'_idx := rfl
    -- Now we can compute
    rcases hx_p_diff with hx_p_0 | hx_p_1 <;> rcases hx_p'_diff with hx_p'_0 | hx_p'_1 <;>
    · simp only [heq_idx_p, heq_idx_p']
      simp only [abs_le]
      constructor <;> omega
  -- Apply discrete IVT
  obtain ⟨s, hs_lo, hs_hi, hdiff_zero⟩ := discrete_ivt h_overlap diff hdiff_step hdiff_lo hdiff_hi
  -- At sum s, both paths have the same x-coordinate
  simp only [diff, x_p, x_p'] at hdiff_zero
  have hs_p_lo : A.1 + A.2 ≤ s := le_trans (le_max_left _ _) hs_lo
  have hs_p'_lo : A'.1 + A'.2 ≤ s := le_trans (le_max_right _ _) hs_lo
  have hs_p_hi : s ≤ B'.1 + B'.2 := le_trans hs_hi (min_le_left _ _)
  have hs_p'_hi : s ≤ B.1 + B.2 := le_trans hs_hi (min_le_right _ _)
  obtain ⟨hp_idx_lt, hp_sum⟩ := hp_valid s hs_p_lo hs_p_hi
  obtain ⟨hp'_idx_lt, hp'_sum⟩ := hp'_valid s hs_p'_lo hs_p'_hi
  simp only [hp_idx_lt, hp'_idx_lt, dite_true, sub_eq_zero] at hdiff_zero
  -- The vertices have the same x-coordinate and the same sum, so they're equal
  have hv_eq : p.vertices.get ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩ =
               p'.vertices.get ⟨(s - A'.1 - A'.2).toNat, hp'_idx_lt⟩ := by
    ext
    · exact hdiff_zero
    · omega
  -- The vertex is in both paths
  use p.vertices.get ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩
  constructor
  · exact List.get_mem p.vertices ⟨(s - A.1 - A.2).toNat, hp_idx_lt⟩
  · rw [hv_eq]
    exact List.get_mem p'.vertices ⟨(s - A'.1 - A'.2).toNat, hp'_idx_lt⟩

/-- A monotone bijection on Fin k is the identity.
    This is used to show that if σ ≠ id, then σ is not monotone. -/
lemma monotone_perm_eq_id {k : ℕ} (σ : Equiv.Perm (Fin k))
    (h : ∀ i j : Fin k, i < j → σ i ≤ σ j) : σ = Equiv.refl (Fin k) := by
  cases k with
  | zero =>
    ext i
    exact i.elim0
  | succ k =>
    have main : ∀ n : ℕ, ∀ i : Fin (k + 1), i.val = n → σ i = i := by
      intro n
      induction' n using Nat.strong_induction_on with n ih
      intro i hi
      have hih : ∀ j : Fin (k + 1), j.val < n → σ j = j := fun j hj => ih j.val hj j rfl
      have hge : i ≤ σ i := by
        by_contra hlt
        push_neg at hlt
        have hlt' : σ i < i := hlt
        have hval : (σ i).val < n := by rw [← hi]; exact Fin.val_fin_lt.mpr hlt'
        have heq : σ (σ i) = σ i := hih (σ i) hval
        exact (ne_of_lt hlt') (σ.injective heq)
      have hle : σ i ≤ i := by
        by_contra hgt
        push_neg at hgt
        have hgt' : i < σ i := hgt
        have hpre : σ.symm i < i := by
          by_contra hge'
          push_neg at hge'
          rcases hge'.eq_or_lt with heq | hgt''
          · have := congrArg σ heq.symm
            simp at this
            exact (ne_of_gt hgt') this.symm
          · have hmono := h i (σ.symm i) hgt''
            simp at hmono
            exact not_lt.mpr hmono hgt'
        have hval : (σ.symm i).val < n := by rw [← hi]; exact Fin.val_fin_lt.mpr hpre
        have heq := hih (σ.symm i) hval
        simp at heq
        exact (ne_of_gt hpre) heq
      exact le_antisymm hle hge
    ext i
    simp only [Equiv.refl_apply]
    exact congrArg Fin.val (main i.val i rfl)

/-- When σ ≠ id, there are no nipats from 𝐀 to σ(𝐁) under the sorting conditions -/
theorem no_nipats_nonidentity {k : ℕ} (A B : kVertex (ℤ × ℤ) k)
    (hxA : xDecreasing A) (hyA : yIncreasing A)
    (hxB : xDecreasing B) (hyB : yIncreasing B)
    (σ : Equiv.Perm (Fin k)) (hσ : σ ≠ Equiv.refl (Fin k)) :
    nipatSet (D := integerLattice) A (permuteKVertex σ B) = ∅ := by
  ext pt
  simp only [nipatSet, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
  intro hpt
  -- σ ≠ id means σ is not monotone, so there exist i < j with σ(i) > σ(j)
  have : ∃ i j : Fin k, i < j ∧ σ j < σ i := by
    by_contra h
    push_neg at h
    exact hσ (monotone_perm_eq_id σ h)
  obtain ⟨i, j, hij, hσij⟩ := this
  -- Apply baby_jordan to paths i and j
  have h_intersect : pathsIntersect (pt.paths i) (pt.paths j) := by
    apply baby_jordan
    · exact hxA i j (le_of_lt hij)
    · exact hyA i j (le_of_lt hij)
    · exact hxB (σ j) (σ i) (le_of_lt hσij)
    · exact hyB (σ j) (σ i) (le_of_lt hσij)
    · exact pt.starts i
    · exact pt.finishes i
    · exact pt.starts j
    · exact pt.finishes j
  exact hpt i j (ne_of_lt hij) h_intersect

/-- When the nipatSet is empty, the nipatWeightSum is zero -/
theorem nipatWeightSum_of_empty {k : ℕ} (w : ArcWeight integerLattice K)
    (A B : kVertex (ℤ × ℤ) k) (σ : Equiv.Perm (Fin k))
    (h : nipatSet (D := integerLattice) A B = ∅) :
    nipatWeightSum integerLattice_pathFinite w A B σ = 0 := by
  unfold nipatWeightSum
  rw [nipatFinset_of_empty _ _ _ h]
  simp

/-- Permuting a k-vertex by the identity permutation gives the same k-vertex -/
theorem permuteKVertex_refl {V : Type*} {k : ℕ} (B : kVertex V k) :
    permuteKVertex (Equiv.refl (Fin k)) B = B := by
  unfold permuteKVertex
  simp

/-- LGV lemma, nonpermutable lattice weight version (Corollary cor.lgv.kpaths.wt-np)
    Label: cor.lgv.kpaths.wt-np

    Under the sorting conditions:
    - x(A₁) ≥ x(A₂) ≥ ⋯ ≥ x(Aₖ)
    - y(A₁) ≤ y(A₂) ≤ ⋯ ≤ y(Aₖ)
    - x(B₁) ≥ x(B₂) ≥ ⋯ ≥ x(Bₖ)
    - y(B₁) ≤ y(B₂) ≤ ⋯ ≤ y(Bₖ)

    The LGV formula simplifies to:
    det((∑_{p : Aᵢ → Bⱼ} w(p))_{i,j}) = ∑_{𝐩 nipat from 𝐀 to 𝐁} w(𝐩) -/
theorem lgv_nonpermutable {k : ℕ} (w : ArcWeight integerLattice K)
    (A B : kVertex (ℤ × ℤ) k)
    (hxA : xDecreasing A) (hyA : yIncreasing A)
    (hxB : xDecreasing B) (hyB : yIncreasing B) :
    (pathWeightMatrix integerLattice_pathFinite w A B).det =
      nipatWeightSum integerLattice_pathFinite w A B (Equiv.refl (Fin k)) := by
  -- Apply the weighted LGV lemma
  rw [lgv_weighted_lattice]
  -- Split the sum: only the identity term survives
  have h_sum : ∑ σ : Equiv.Perm (Fin k), Equiv.Perm.sign σ •
        nipatWeightSum integerLattice_pathFinite w A (permuteKVertex σ B) σ =
      Equiv.Perm.sign (Equiv.refl (Fin k)) •
        nipatWeightSum integerLattice_pathFinite w A (permuteKVertex (Equiv.refl (Fin k)) B)
          (Equiv.refl (Fin k)) := by
    apply Fintype.sum_eq_single
    intro σ hσ
    have h := no_nipats_nonidentity A B hxA hyA hxB hyB σ hσ
    rw [nipatWeightSum_of_empty _ _ _ _ h]
    simp
  rw [h_sum]
  simp only [Equiv.Perm.sign_refl, one_smul]
  rw [permuteKVertex_refl]


end LGV
