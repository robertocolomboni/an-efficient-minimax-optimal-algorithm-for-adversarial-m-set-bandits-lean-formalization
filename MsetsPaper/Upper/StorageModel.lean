import MsetsPaper.Upper.ListAccess

/-! A conservative explicit word-allocation model.

`ResourceRun` records a value, constructor/access work, and allocated temporary
words. A word stores a real, index, reference or control-frame slot; this is
not the bit length of an arbitrary real. Allocations are counted even if an
implementation could reuse them. `arenaLoop` implements the stated memory
discipline: retain the returned finite data, discard other iteration-local
allocations before the next iteration. Its peak theorem is proved from that
recurrence, not inserted as a claimed bound in a program definition.
-/

noncomputable section

namespace MsetsPaper.Upper

structure ResourceRun (α : Type*) where
  value : α
  work : ℕ
  allocated : ℕ

def resourceListGet {α : Type*} : List α → ℕ → ResourceRun (Option α)
  | [], _ => ⟨none, 1, 1⟩
  | x :: _, 0 => ⟨some x, 1, 2⟩
  | _ :: xs, k + 1 =>
    let tail := resourceListGet xs k
    ⟨tail.value, tail.work + 1, tail.allocated + 2⟩

theorem resourceListGet_values {α : Type*} (xs : List α) (k : ℕ) :
    (resourceListGet xs k).value = xs[k]? := by
  induction xs generalizing k with
  | nil => simp [resourceListGet]
  | cons x xs ih => cases k <;> simp [resourceListGet, ih]

theorem resourceListGet_work {α : Type*} (xs : List α) (k : ℕ) :
    (resourceListGet xs k).work = (countedListGet xs k).2 := by
  induction xs generalizing k with
  | nil => simp [resourceListGet, countedListGet]
  | cons x xs ih => cases k <;> simp [resourceListGet, countedListGet, ih]

theorem resourceListGet_allocated_le {α : Type*} (xs : List α) (k : ℕ) :
    (resourceListGet xs k).allocated ≤ 2 * (resourceListGet xs k).work := by
  induction xs generalizing k with
  | nil => simp [resourceListGet]
  | cons x xs ih =>
    cases k with
    | zero => simp [resourceListGet]
    | succ k => have := ih k; simp only [resourceListGet]; omega

def resourceListRead {α : Type*} (fallback : α) (xs : List α) (k : ℕ) : ResourceRun α :=
  let lookup := resourceListGet xs k
  ⟨lookup.value.getD fallback, lookup.work + 1, lookup.allocated + 1⟩

theorem resourceListRead_values {α : Type*} (fallback : α) (xs : List α) (k : ℕ) :
    (resourceListRead fallback xs k).value = xs[k]?.getD fallback := by
  simp only [resourceListRead, resourceListGet_values]

theorem resourceListRead_bounds {α : Type*} (fallback : α) (xs : List α) (k : ℕ) :
    (resourceListRead fallback xs k).work ≤ xs.length + 2 ∧
      (resourceListRead fallback xs k).allocated ≤ 2 * xs.length + 3 := by
  have hwork := countedListGet_cost_le_length xs k
  have halloc := resourceListGet_allocated_le xs k
  rw [resourceListGet_work] at halloc
  simp only [resourceListRead, resourceListGet_work]
  constructor <;> omega

/-- Explicit reset between iterations. `footprint` counts the materialized
data retained by an iteration; `allocated` includes all its new temporary
words. Old input words may remain live during the step and are charged too. -/
def arenaLoop {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ) :
    ℕ → σ → ℕ → σ × ℕ
  | 0, state, peak => (state, max peak (footprint state))
  | n + 1, state, peak =>
    let next := step state
    let peak' := max peak (footprint state + next.allocated)
    arenaLoop step footprint n next.value peak'

theorem arenaLoop_values {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ)
    (n : ℕ) (state : σ) (peak : ℕ) :
    (arenaLoop step footprint n state peak).1 = (fun s => (step s).value)^[n] state := by
  induction n generalizing state peak with
  | zero => rfl
  | succ n ih => simpa only [arenaLoop, ih, Function.iterate_succ_apply]

/-- The iteration count does not multiply space: this follows from explicit
retention/reset, provided the local allocation and retained-data bounds hold.
These two local bounds must be proved for each concrete program separately. -/
theorem arenaLoop_peak_le {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ)
    (Inv : σ → Prop) (P A : ℕ)
    (hfoot : ∀ s, Inv s → footprint s ≤ P)
    (hstep : ∀ s, Inv s → Inv (step s).value ∧ (step s).allocated ≤ A)
    (n : ℕ) (state : σ) (hstate : Inv state) (peak : ℕ) (hpeak : peak ≤ P + A) :
    (arenaLoop step footprint n state peak).2 ≤ P + A := by
  induction n generalizing state peak with
  | zero =>
    simp only [arenaLoop]
    exact max_le hpeak ((hfoot state hstate).trans (Nat.le_add_right P A))
  | succ n ih =>
    have hs := hstep state hstate
    apply ih _ hs.1 _
    exact max_le hpeak (Nat.add_le_add (hfoot state hstate) hs.2)

end MsetsPaper.Upper
