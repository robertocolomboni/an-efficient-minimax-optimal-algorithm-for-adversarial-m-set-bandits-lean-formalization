import MsetsPaper.Upper.ProjectionOracleProgram
import MsetsPaper.Upper.EllipsoidUpdateProgram
import MsetsPaper.Upper.ProjectionEllipsoidCapstone

/-! A non-enumerative counted implementation of the complete search.
This file proves refinement and real-operation bounds. List traversal,
allocation, and peak live storage are not silently treated as constant-time. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

def countedAllZero : List ℝ → Bool × ℕ
  | [] => (true, 0)
  | x :: xs =>
    let tail := countedAllZero xs
    (decide (x = 0) && tail.1, tail.2 + 1)

theorem countedAllZero_values (xs : List ℝ) :
    (countedAllZero xs).1 = true ↔ ∀ x ∈ xs, x = 0 := by
  induction xs with
  | nil => simp [countedAllZero]
  | cons x xs ih => simp [countedAllZero, ih]

theorem countedAllZero_cost (xs : List ℝ) : (countedAllZero xs).2 = xs.length := by
  induction xs <;> simp_all [countedAllZero]

variable {d m : ℕ}

theorem countedAllZero_vector (g : Fin d → ℝ) :
    (countedAllZero (List.ofFn g)).1 = true ↔ g = 0 := by
  rw [countedAllZero_values]
  simp [List.mem_ofFn, funext_iff]

def ellipsoidStepProgram (st : EllipsoidState d) (g : Fin d → ℝ) : EllipsoidState d × ℕ :=
  let zeroTest := countedAllZero (List.ofFn g)
  if zeroTest.1 then (st, zeroTest.2 + 1)
  else
    let next := ellipsoidUpdateProgram st.center st.shape g
    (next.1, zeroTest.2 + 1 + next.2)

theorem ellipsoidStepProgram_values (st : EllipsoidState d) (g : Fin d → ℝ) :
    (ellipsoidStepProgram st g).1 =
      if g = 0 then st else ⟨ellipsoidNextCenter st.center g st.shape, ellipsoidNextShape st.shape g⟩ := by
  dsimp only [ellipsoidStepProgram]
  simp only [countedAllZero_vector, apply_ite, ellipsoidUpdateProgram_values]
  split_ifs <;> rfl

theorem ellipsoidStepProgram_cost (st : EllipsoidState d) (g : Fin d → ℝ) :
    (ellipsoidStepProgram st g).2 ≤ 6 * d * d + 5 * d + 10 := by
  dsimp only [ellipsoidStepProgram]
  split_ifs <;> dsimp only <;>
    simp only [countedAllZero_cost, List.length_ofFn, ellipsoidUpdateProgram_cost] <;> omega

def projectionSearchProgramStep (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m)
    (st : ProjectionSearchState d) : ProjectionSearchState d × ℕ :=
  let cut := projectionCutProgram theta a b st.ellipsoid.center R m
  let g := cachedRealVector cut.1 (projectionCutProgram_length theta a b st.ellipsoid.center R hm)
  let next := ellipsoidStepProgram st.ellipsoid g
  let best := projectionRetainBestProgram theta a b st.ellipsoid.center st.best R m
  (⟨next.1, best.1, st.queries + 1⟩, cut.2 + next.2 + best.2)

theorem projectionSearchProgramStep_values (theta a b : Fin d → ℝ) (R : ℝ)
    (hm : 1 ≤ m) (st : ProjectionSearchState d) :
    (projectionSearchProgramStep theta a b R hm st).1 =
      projectionSearchStep (m := m) theta a b R st := by
  have hg := projectionCutVector_eq theta a b st.ellipsoid.center R hm
  simp only [projectionCutVector] at hg
  simp only [projectionSearchProgramStep, hg, ellipsoidStepProgram_values,
    projectionRetainBestProgram_values, projectionSearchStep, ellipsoidStep]

def projectionStepCost (d m : ℕ) : ℕ :=
  (2 * m + 6) * d * d + 6 * m * d + 38 * d + 17

theorem projectionSearchProgramStep_cost (theta a b : Fin d → ℝ) (R : ℝ)
    (hm : 1 ≤ m) (st : ProjectionSearchState d) :
    (projectionSearchProgramStep theta a b R hm st).2 ≤ projectionStepCost d m := by
  have hcut := projectionCutProgram_cost theta a b st.ellipsoid.center R m
  have hnext := ellipsoidStepProgram_cost st.ellipsoid
    (cachedRealVector (projectionCutProgram theta a b st.ellipsoid.center R m).1
      (projectionCutProgram_length theta a b st.ellipsoid.center R hm))
  have hbest := projectionRetainBestProgram_cost theta a b st.ellipsoid.center st.best R m
  dsimp only [projectionSearchProgramStep]
  unfold projectionStepCost
  nlinarith

/-- Tail-recursive execution: only the current state and accumulated counter
are passed to the next iteration. A separate heap semantics is still needed
to conclude a peak-allocation bound for the underlying list primitives. -/
def projectionSearchLoop (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) :
    ℕ → ProjectionSearchState d → ℕ → ProjectionSearchState d × ℕ
  | 0, st, cost => (st, cost)
  | n + 1, st, cost =>
    let next := projectionSearchProgramStep theta a b R hm st
    projectionSearchLoop theta a b R hm n next.1 (cost + next.2)

theorem projectionSearchLoop_values (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m)
    (n k cost : ℕ) :
    (projectionSearchLoop theta a b R hm n
      (projectionSearchRun (m := m) theta a b R k) cost).1 =
      projectionSearchRun (m := m) theta a b R (k + n) := by
  induction n generalizing k cost with
  | zero => simp [projectionSearchLoop]
  | succ n ih =>
    simp only [projectionSearchLoop, projectionSearchProgramStep_values]
    change (projectionSearchLoop theta a b R hm n
      (projectionSearchRun (m := m) theta a b R (k + 1)) _).1 = _
    rw [ih]
    congr 1
    omega

theorem projectionSearchLoop_cost (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m)
    (n : ℕ) (st : ProjectionSearchState d) (cost : ℕ) :
    (projectionSearchLoop theta a b R hm n st cost).2 ≤ cost + n * projectionStepCost d m := by
  induction n generalizing st cost with
  | zero => simp [projectionSearchLoop]
  | succ n ih =>
    dsimp only [projectionSearchLoop]
    have h := ih (projectionSearchProgramStep theta a b R hm st).1
      (cost + (projectionSearchProgramStep theta a b R hm st).2)
    have hs := projectionSearchProgramStep_cost theta a b R hm st
    nlinarith

/-- R^2 is one real multiplication; initial matrix cells are copies of it or
zero. The returned matrix is explicitly materialized, not an oracle. -/
def ellipsoidInitialProgram (R : ℝ) : EllipsoidState d × ℕ :=
  let radiusSq := R * R
  let cell := fun i j : Fin d => (if i = j then radiusSq else 0, 0)
  let shape := countedMatrix cell
  (⟨0, cachedRealMatrix shape.1 (countedMatrix_length cell) (countedMatrix_row_length cell)⟩,
    1 + shape.2)

theorem ellipsoidInitialProgram_values (R : ℝ) :
    (ellipsoidInitialProgram (d := d) R).1 = ellipsoidInitial R := by
  simp only [ellipsoidInitialProgram, countedMatrix_cached, ellipsoidInitial]
  congr 1
  ext i j
  simp [Matrix.smul_apply, Matrix.one_apply, pow_two]

theorem ellipsoidInitialProgram_cost (R : ℝ) : (ellipsoidInitialProgram (d := d) R).2 = 1 := by
  simp only [ellipsoidInitialProgram]
  rw [countedMatrix_cost (fun i j : Fin d => (if i = j then R * R else 0, 0)) 0 (fun _ _ => rfl)]
  simp

def projectionSearchProgram (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) (N : ℕ) :
    ProjectionSearchState d × ℕ :=
  let initial := ellipsoidInitialProgram (d := d) R
  projectionSearchLoop theta a b R hm N ⟨initial.1, 0, 0⟩ initial.2

theorem projectionSearchProgram_values (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) (N : ℕ) :
    (projectionSearchProgram theta a b R hm N).1 = projectionSearchRun (m := m) theta a b R N := by
  simp only [projectionSearchProgram, ellipsoidInitialProgram_values, ellipsoidInitialProgram_cost]
  simpa only [projectionSearchRun, Nat.zero_add] using projectionSearchLoop_values theta a b R hm N 0 1

theorem projectionSearchProgram_cost (theta a b : Fin d → ℝ) (R : ℝ) (hm : 1 ≤ m) (N : ℕ) :
    (projectionSearchProgram theta a b R hm N).2 ≤ 1 + N * projectionStepCost d m := by
  dsimp only [projectionSearchProgram]
  rw [ellipsoidInitialProgram_cost]
  exact projectionSearchLoop_cost theta a b R hm N _ 1

end MsetsPaper.Upper
