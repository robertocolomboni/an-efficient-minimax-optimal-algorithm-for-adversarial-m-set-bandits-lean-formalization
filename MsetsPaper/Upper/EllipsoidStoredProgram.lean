import MsetsPaper.Upper.StoredResourceOperations
import MsetsPaper.Upper.ProjectionSearchProgram
import MsetsPaper.Upper.RealArithmeticPrimitives

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper.ResourcePrograms

open SchurSolver (StoredVector StoredMatrix storedVector storedMatrix
  resourceVectorRead resourceVectorRead_values resourceVectorRead_bounds
  resourceMatrixRead resourceMatrixRead_values resourceMatrixRead_bounds)

variable {d : ℕ}

structure StoredEllipsoid (d : ℕ) where
  center : StoredVector d
  shape : StoredMatrix d

def StoredEllipsoid.decode (s : StoredEllipsoid d) : EllipsoidState d :=
  ⟨storedVector s.center, storedMatrix s.shape⟩

def centerCellResource (c u : StoredVector d) (k : ℝ) (i : Fin d) : ResourceRun ℝ :=
  let a := resourceVectorRead c i
  let b := resourceVectorRead u i
  ⟨a.value - k * b.value, a.work + b.work + 2, a.allocated + b.allocated + 2⟩

theorem centerCellResource_values (c u : StoredVector d) (k : ℝ) (i : Fin d) :
    (centerCellResource c u k i).value = storedVector c i - k * storedVector u i := by
  simp only [centerCellResource, resourceVectorRead_values]

theorem centerCellResource_bounds (c u : StoredVector d) (k : ℝ) (i : Fin d) :
    (centerCellResource c u k i).work ≤ 2 * d + 6 ∧
      (centerCellResource c u k i).allocated ≤ 4 * d + 8 := by
  have hc := resourceVectorRead_bounds c i
  have hu := resourceVectorRead_bounds u i
  dsimp only [centerCellResource]
  constructor <;> omega

def shapeCellResource (Q : StoredMatrix d) (u : StoredVector d) (a b : ℝ)
    (i j : Fin d) : ResourceRun ℝ :=
  let q := resourceMatrixRead Q i j
  let x := resourceVectorRead u i
  let y := resourceVectorRead u j
  ⟨a * (q.value - b * (x.value * y.value)), q.work + x.work + y.work + 4,
    q.allocated + x.allocated + y.allocated + 4⟩

theorem shapeCellResource_values (Q : StoredMatrix d) (u : StoredVector d) (a b : ℝ)
    (i j : Fin d) :
    (shapeCellResource Q u a b i j).value =
      a * (storedMatrix Q i j - b * (storedVector u i * storedVector u j)) := by
  simp only [shapeCellResource, resourceMatrixRead_values, resourceVectorRead_values]

theorem shapeCellResource_bounds (Q : StoredMatrix d) (u : StoredVector d) (a b : ℝ)
    (i j : Fin d) :
    (shapeCellResource Q u a b i j).work ≤ 4 * d + 12 ∧
      (shapeCellResource Q u a b i j).allocated ≤ 8 * d + 16 := by
  have hq := resourceMatrixRead_bounds Q i j
  have hx := resourceVectorRead_bounds u i
  have hy := resourceVectorRead_bounds u j
  dsimp only [shapeCellResource]
  constructor <;> omega

def ellipsoidUpdateResource (s : StoredEllipsoid d) (g : StoredVector d) :
    ResourceRun (StoredEllipsoid d) :=
  let product := matVecProgram s.shape g
  let quad := dotProgram g product.value
  let nplus := (d : ℝ) + 1
  let nsq := (d : ℝ) * d
  let a := nsq / (nsq - 1)
  let b := (2 / nplus) / quad.value
  let root := sqrtResource quad.value
  let k := 1 / (nplus * root.value)
  let center := vectorProgram (centerCellResource s.center product.value k)
  let shape := matrixProgram (shapeCellResource s.shape product.value a b)
  ⟨⟨center.value, shape.value⟩,
    product.work + quad.work + center.work + shape.work + root.work + 13,
    product.allocated + quad.allocated + center.allocated + shape.allocated + root.allocated + 19⟩

theorem ellipsoidUpdateResource_values (s : StoredEllipsoid d) (g : StoredVector d) :
    (ellipsoidUpdateResource s g).value.decode =
      ⟨ellipsoidNextCenter (storedVector s.center) (storedVector g) (storedMatrix s.shape),
        ellipsoidNextShape (storedMatrix s.shape) (storedVector g)⟩ := by
  simp only [ellipsoidUpdateResource, StoredEllipsoid.decode, vectorProgram_values,
    centerCellResource_values, matrixProgram_values, shapeCellResource_values,
    matVecProgram_values, dotProgram_values, sqrtResource_values]
  congr 1
  ext i j
  simp only [ellipsoidNextShape, ellipsoidRankOneDowndate, Matrix.smul_apply,
    Matrix.sub_apply, Matrix.vecMulVec_apply, smul_eq_mul, ellipsoidQuadratic, pow_two]

theorem ellipsoidUpdateResource_bounds (s : StoredEllipsoid d) (g : StoredVector d) :
    (ellipsoidUpdateResource s g).work ≤ 100 * (d + 1) ^ 3 ∧
      (ellipsoidUpdateResource s g).allocated ≤ 100 * (d + 1) ^ 3 := by
  let u := (matVecProgram s.shape g).value
  let q := (dotProgram g u).value
  let k := 1 / (((d : ℝ) + 1) * (sqrtResource q).value)
  let a := ((d : ℝ) * d) / ((d : ℝ) * d - 1)
  let b := (2 / ((d : ℝ) + 1)) / q
  have hp := matVecProgram_bounds s.shape g
  have hq := dotProgram_bounds g u
  have hc := vectorProgram_bounds (centerCellResource s.center u k)
    (2 * d + 6) (4 * d + 8) (centerCellResource_bounds s.center u k)
  have hs := matrixProgram_bounds (shapeCellResource s.shape u a b)
    (4 * d + 12) (8 * d + 16) (shapeCellResource_bounds s.shape u a b)
  have hr := sqrtResource_bounds q
  dsimp only [ellipsoidUpdateResource]
  dsimp only [u, q, k, a, b] at hq hc hs hr
  constructor <;> nlinarith [hp.1, hp.2, hq.1, hq.2, hc.1, hc.2, hs.1, hs.2, hr.1, hr.2]

def allZeroResource : List ℝ → ResourceRun Bool
  | [] => ⟨true, 1, 1⟩
  | x :: xs =>
    let tail := allZeroResource xs
    ⟨decide (x = 0) && tail.value, tail.work + 3, tail.allocated + 3⟩

theorem allZeroResource_values (xs : List ℝ) :
    (allZeroResource xs).value = true ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [allZeroResource]
  | cons x xs ih => simp [allZeroResource, ih]

theorem allZeroResource_counts (xs : List ℝ) :
    (allZeroResource xs).work = 3 * xs.length + 1 ∧
      (allZeroResource xs).allocated = 3 * xs.length + 1 := by
  induction xs with
  | nil => simp [allZeroResource]
  | cons x xs ih => simp only [allZeroResource, List.length_cons]; constructor <;> omega

theorem allZeroResource_vector (g : StoredVector d) :
    (allZeroResource g.val).value = true ↔ storedVector g = 0 := by
  rw [allZeroResource_values]
  constructor
  · intro h
    funext i
    exact h _ (List.getElem_mem (by rw [g.property]; exact i.isLt))
  · intro h x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hx
    have hval := congrFun h (⟨k, by rw [← g.property]; exact hk⟩ : Fin d)
    simpa only [storedVector, cachedRealVector, Pi.zero_apply] using hval

def ellipsoidStepResource (s : StoredEllipsoid d) (g : StoredVector d) :
    ResourceRun (StoredEllipsoid d) :=
  let test := allZeroResource g.val
  if test.value then ⟨s, test.work + 1, test.allocated + 1⟩ else
    let next := ellipsoidUpdateResource s g
    ⟨next.value, test.work + next.work + 1, test.allocated + next.allocated + 2⟩

theorem ellipsoidStepResource_values (s : StoredEllipsoid d) (g : StoredVector d) :
    (ellipsoidStepResource s g).value.decode =
      if storedVector g = 0 then s.decode else
        ⟨ellipsoidNextCenter (storedVector s.center) (storedVector g) (storedMatrix s.shape),
          ellipsoidNextShape (storedMatrix s.shape) (storedVector g)⟩ := by
  simp only [ellipsoidStepResource, allZeroResource_vector, apply_ite,
    ellipsoidUpdateResource_values]
  split_ifs <;> rfl

theorem ellipsoidStepResource_bounds (s : StoredEllipsoid d) (g : StoredVector d) :
    (ellipsoidStepResource s g).work ≤ 104 * (d + 1) ^ 3 ∧
      (ellipsoidStepResource s g).allocated ≤ 104 * (d + 1) ^ 3 := by
  have ht := allZeroResource_counts g.val
  rw [g.property] at ht
  have hn := ellipsoidUpdateResource_bounds s g
  have hpoly : 3 * d + 3 ≤ 4 * (d + 1) ^ 3 := by
    nlinarith only [Nat.zero_le (d ^ 2), Nat.zero_le (d ^ 3)]
  dsimp only [ellipsoidStepResource]
  split_ifs <;> dsimp only <;> constructor <;> omega

end MsetsPaper.Upper.ResourcePrograms
