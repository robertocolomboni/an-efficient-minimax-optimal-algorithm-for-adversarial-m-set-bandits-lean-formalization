import MsetsPaper.Upper.StorageModel

/-! Explicit bounded-live-data tail transitions. The word-RAM arena retains
only the returned finite state between transitions. Reachable words in that
state are counted by footprint; every step-local allocation is charged before
the reset. Eight additional control/counter words cover the loop driver.
This is a stated abstract execution model, not a claim about Lean's compiler.
-/

noncomputable section

namespace MsetsPaper.Upper

def arenaProgram {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ) :
    ℕ → σ → ℕ → ℕ → ℕ → ResourceRun σ × ℕ
  | 0, state, work, allocated, peak =>
    (⟨state, work + 1, allocated + 1⟩, max peak (footprint state + 8))
  | n + 1, state, work, allocated, peak =>
    let next := step state
    arenaProgram step footprint n next.value (work + next.work + 3)
      (allocated + next.allocated + 8) (max peak (footprint state + next.allocated + 8))

theorem arenaProgram_values {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ)
    (n : ℕ) (state : σ) (work allocated peak : ℕ) :
    (arenaProgram step footprint n state work allocated peak).1.value =
      (fun s => (step s).value)^[n] state := by
  induction n generalizing state work allocated peak with
  | zero => rfl
  | succ n ih => simpa only [arenaProgram, ih, Function.iterate_succ_apply]

theorem arenaProgram_work {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ)
    (W : ℕ) (hW : ∀ s, (step s).work ≤ W)
    (n : ℕ) (state : σ) (work allocated peak : ℕ) :
    (arenaProgram step footprint n state work allocated peak).1.work ≤ work + n * (W + 3) + 1 := by
  induction n generalizing state work allocated peak with
  | zero => simp [arenaProgram]
  | succ n ih =>
    dsimp only [arenaProgram]
    have h := ih (step state).value (work + (step state).work + 3)
      (allocated + (step state).allocated + 8) (max peak (footprint state + (step state).allocated + 8))
    have hs := hW state
    nlinarith

theorem arenaProgram_allocated {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ)
    (A : ℕ) (hA : ∀ s, (step s).allocated ≤ A)
    (n : ℕ) (state : σ) (work allocated peak : ℕ) :
    (arenaProgram step footprint n state work allocated peak).1.allocated ≤
      allocated + n * (A + 8) + 1 := by
  induction n generalizing state work allocated peak with
  | zero => simp [arenaProgram]
  | succ n ih =>
    dsimp only [arenaProgram]
    have h := ih (step state).value (work + (step state).work + 3)
      (allocated + (step state).allocated + 8) (max peak (footprint state + (step state).allocated + 8))
    have hs := hA state
    nlinarith

theorem arenaProgram_peak {σ : Type*} (step : σ → ResourceRun σ) (footprint : σ → ℕ)
    (P A : ℕ) (hP : ∀ s, footprint s ≤ P) (hA : ∀ s, (step s).allocated ≤ A)
    (n : ℕ) (state : σ) (work allocated peak : ℕ) (hpeak : peak ≤ P + A + 8) :
    (arenaProgram step footprint n state work allocated peak).2 ≤ P + A + 8 := by
  induction n generalizing state work allocated peak with
  | zero => simp only [arenaProgram]; exact max_le hpeak (by have := hP state; omega)
  | succ n ih =>
    apply ih
    apply max_le hpeak
    have hp := hP state
    have ha := hA state
    omega

end MsetsPaper.Upper
