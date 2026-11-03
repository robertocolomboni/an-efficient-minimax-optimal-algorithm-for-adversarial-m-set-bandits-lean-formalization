import MsetsPaper.Upper.RoundProgram

/-! # Nested arenas and streaming rounds

The step has its own already-accounted local peak, because the projection
reclaims its temporaries internally. Summing its total allocations would
incorrectly reintroduce the iteration budget into the space bound.
Between rounds only the returned finite state, the time index, and eight
driver/counter words survive. This is a word-RAM tail-transition model,
not a statement about Lean's generated code or arbitrary-precision bits.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver

noncomputable section

def copyStoredVectorResource {d : ℕ} (x : StoredVector d) : ResourceRun (StoredVector d) :=
  let copied := resourceMap (fun z => (⟨z, 1, 1⟩ : ResourceRun ℝ)) x.1
  ⟨⟨copied.value, by simp [copied, resourceMap_values, x.2]⟩,
    copied.work + 1, copied.allocated + 1⟩

theorem copyStoredVectorResource_values {d : ℕ} (x : StoredVector d) :
    (copyStoredVectorResource x).value = x := by
  apply Subtype.ext
  simp [copyStoredVectorResource, resourceMap_values]

theorem copyStoredVectorResource_bounds {d : ℕ} (x : StoredVector d) :
    (copyStoredVectorResource x).work ≤ 3 * d + 2 ∧
    (copyStoredVectorResource x).allocated ≤ 4 * d + 2 := by
  have h := resourceMap_bounds (fun z => (⟨z, 1, 1⟩ : ResourceRun ℝ)) x.1 1 1
    (fun _ _ => ⟨le_rfl, le_rfl⟩)
  rw [x.2] at h
  dsimp only [copyStoredVectorResource]
  constructor <;> omega

/-- Time-dependent semantic iteration. Random draws and feedback are supplied
online by `step`, not stored as a horizon-length list in the persistent state. -/
def streamIterate {σ : Type*} (step : ℕ → σ → σ) : ℕ → ℕ → σ → σ
  | 0, _, state => state
  | n + 1, t, state => streamIterate step n (t + 1) (step t state)

/-- A tail-transition driver whose steps have their own nested local arenas.
The local peak is extra live space above the supplied input state. -/
def nestedArenaProgram {σ : Type*} (step : ℕ → σ → ResourceRun σ × ℕ)
    (footprint : σ → ℕ) : ℕ → ℕ → σ → ℕ → ℕ → ℕ → ResourceRun σ × ℕ
  | 0, _, state, work, allocated, peak =>
    (⟨state, work + 1, allocated + 1⟩, max peak (footprint state + 8))
  | n + 1, t, state, work, allocated, peak =>
    let next := step t state
    nestedArenaProgram step footprint n (t + 1) next.1.value
      (work + next.1.work + 3) (allocated + next.1.allocated + 8)
      (max peak (footprint state + next.2 + 8))

theorem nestedArenaProgram_values {σ : Type*} (step : ℕ → σ → ResourceRun σ × ℕ)
    (footprint : σ → ℕ) (n t : ℕ) (state : σ) (work allocated peak : ℕ) :
    (nestedArenaProgram step footprint n t state work allocated peak).1.value =
      streamIterate (fun t s => (step t s).1.value) n t state := by
  induction n generalizing t state work allocated peak with
  | zero => rfl
  | succ n ih => simp only [nestedArenaProgram, ih, streamIterate]

theorem nestedArenaProgram_work {σ : Type*} (step : ℕ → σ → ResourceRun σ × ℕ)
    (footprint : σ → ℕ) (W : ℕ) (hW : ∀ t s, (step t s).1.work ≤ W)
    (n t : ℕ) (state : σ) (work allocated peak : ℕ) :
    (nestedArenaProgram step footprint n t state work allocated peak).1.work ≤
      work + n * (W + 3) + 1 := by
  induction n generalizing t state work allocated peak with
  | zero => simp [nestedArenaProgram]
  | succ n ih =>
    dsimp only [nestedArenaProgram]
    have h := ih (t + 1) (step t state).1.value (work + (step t state).1.work + 3)
      (allocated + (step t state).1.allocated + 8)
      (max peak (footprint state + (step t state).2 + 8))
    have hs := hW t state
    nlinarith

theorem nestedArenaProgram_peak {σ : Type*} (step : ℕ → σ → ResourceRun σ × ℕ)
    (footprint : σ → ℕ) (P A : ℕ)
    (hP : ∀ s, footprint s ≤ P) (hA : ∀ t s, (step t s).2 ≤ A)
    (n t : ℕ) (state : σ) (work allocated peak : ℕ) (hpeak : peak ≤ P + A + 8) :
    (nestedArenaProgram step footprint n t state work allocated peak).2 ≤ P + A + 8 := by
  induction n generalizing t state work allocated peak with
  | zero => simp only [nestedArenaProgram]; exact max_le hpeak (by have := hP state; omega)
  | succ n ih =>
    apply ih
    apply max_le hpeak
    have hp := hP state
    have ha := hA t state
    omega

end

end MsetsPaper.Upper.RoundProgram
