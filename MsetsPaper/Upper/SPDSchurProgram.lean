import MsetsPaper.Upper.SPDSchurAlgebra
import MsetsPaper.Upper.EllipsoidUpdateProgram
import MsetsPaper.Upper.SecondMoment

/-! # Materialized scalar-pivot SPD solve with an exact arithmetic counter

Each Schur matrix, reduced right-hand side and recursive solution is cached
as finite data before use. The counter charges real +,-,*,/ operations. List
access, allocation and integer/control work are separate resource obligations;
the cubic theorem below is not a claim that list indexing is constant-time.
-/

namespace MsetsPaper.Upper.SchurSolver

open Matrix
open scoped BigOperators

noncomputable section

variable {n : ℕ}

def schurRows (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) : List (List ℝ) × ℕ :=
  countedMatrix (fun i j ↦ (schur A i j, 3))

theorem schurRows_length (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (schurRows A).1.length = n := countedMatrix_length _

theorem schurRows_row_length (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (row : List ℝ) (hrow : row ∈ (schurRows A).1) : row.length = n :=
  countedMatrix_row_length _ row hrow

theorem schurRows_cached (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    cachedRealMatrix (schurRows A).1 (schurRows_length A) (schurRows_row_length A) =
      schur A := countedMatrix_cached _

theorem schurRows_cost (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    (schurRows A).2 = 3 * n * n := countedMatrix_cost _ 3 (fun _ _ ↦ rfl)

def rhsCells (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) : List ℝ × ℕ :=
  countedMap (fun i ↦ (reducedRhs A b i, 3)) (List.finRange n)

theorem rhsCells_values (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) : (rhsCells A b).1 = List.ofFn (reducedRhs A b) := by
  simp only [rhsCells, countedMap_values, List.ofFn_eq_map]

theorem rhsCells_length (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) : (rhsCells A b).1.length = n := by
  rw [rhsCells_values, List.length_ofFn]

theorem rhsCells_cached (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) :
    cachedRealVector (rhsCells A b).1 (rhsCells_length A b) = reducedRhs A b := by
  ext i
  simp [cachedRealVector, rhsCells_values]

theorem rhsCells_cost (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ)
    (b : Fin (n + 1) → ℝ) : (rhsCells A b).2 = 3 * n := by
  simp [rhsCells, countedMap_cost, List.map_const', Nat.mul_comm]

structure SolveRun (n : ℕ) where
  values : List ℝ
  length_eq : values.length = n
  realOps : ℕ

def SolveRun.vector (r : SolveRun n) : Fin n → ℝ :=
  cachedRealVector r.values r.length_eq

/-- No recursion on an unevaluated matrix expression: both smaller inputs
are materialized and then read through their verified cache interfaces. -/
def solveRun : (n : ℕ) → Matrix (Fin n) (Fin n) ℝ → (Fin n → ℝ) → SolveRun n
  | 0, _, _ => ⟨[], rfl, 0⟩
  | n + 1, A, b =>
    let rows := schurRows A
    let B := cachedRealMatrix rows.1 (schurRows_length A) (schurRows_row_length A)
    let rhs := rhsCells A b
    let c := cachedRealVector rhs.1 (rhsCells_length A b)
    let tail := solveRun n B c
    let dot := countedDot (fun j ↦ A 0 j.succ) tail.vector
    ⟨((b 0 - dot.1) / A 0 0) :: tail.values,
      by simp only [List.length_cons, tail.length_eq],
      rows.2 + rhs.2 + tail.realOps + dot.2 + 2⟩

theorem solveRun_values : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
    (solveRun n A b).values = List.ofFn (solveSpec n A b) := by
  intro n
  induction n with
  | zero => intro A b; simp [solveRun]
  | succ n ih =>
    intro A b
    have ht := ih (schur A) (reducedRhs A b)
    have hv : (solveRun n (schur A) (reducedRhs A b)).vector =
        solveSpec n (schur A) (reducedRhs A b) := by
      ext i
      simp [SolveRun.vector, cachedRealVector, ht]
    simp only [solveRun, schurRows_cached, rhsCells_cached, countedDot_values,
      hv, ht, solveSpec, reconstruct, List.ofFn_cons, dotProduct]

theorem solveRun_vector (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (solveRun n A b).vector = solveSpec n A b := by
  ext i
  simp [SolveRun.vector, cachedRealVector, solveRun_values]

/-- The arithmetic recurrence is 3*n^2+5*n+2 per pivot, not a determinant call. -/
theorem solveRun_realOps : ∀ (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ),
    (solveRun n A b).realOps = n ^ 2 * (n + 1) := by
  intro n
  induction n with
  | zero => intro A b; simp [solveRun]
  | succ n ih =>
    intro A b
    simp only [solveRun, schurRows_cost, rhsCells_cost, countedDot_cost, ih]
    ring

theorem solveRun_realOps_cubic (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) :
    (solveRun n A b).realOps ≤ 2 * n ^ 3 := by
  rw [solveRun_realOps]
  by_cases hn : n = 0
  · simp [hn]
  · have hn1 : 1 ≤ n := by omega
    nlinarith [sq_nonneg (n : ℤ)]

theorem solveRun_solves (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (b : Fin n → ℝ) : A *ᵥ (solveRun n A b).vector = b := by
  rw [solveRun_vector]
  exact solveSpec_solves n A hA b

theorem solveRun_eq_inverse (n : ℕ) (A : Matrix (Fin n) (Fin n) ℝ)
    (hA : A.PosDef) (b : Fin n → ℝ) : (solveRun n A b).vector = A⁻¹ *ᵥ b := by
  rw [solveRun_vector]
  exact solveSpec_eq_inverse n A hA b

/-- Application to the actual second moment; positivity is derived from
full support, not supplied as an algorithm-specific invertibility premise. -/
theorem solveRun_secondMoment {d m : ℕ} (p : Action d m → ℝ)
    (hp : ∀ a, 0 < p a) (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (b : Fin d → ℝ) :
    (solveRun d (secondMoment p) b).vector = (secondMoment p)⁻¹ *ᵥ b ∧
      (solveRun d (secondMoment p) b).realOps = d ^ 2 * (d + 1) :=
  ⟨solveRun_eq_inverse d _ (secondMoment_posDef p hp hm hmtop) b,
    solveRun_realOps d _ b⟩

end

end MsetsPaper.Upper.SchurSolver
