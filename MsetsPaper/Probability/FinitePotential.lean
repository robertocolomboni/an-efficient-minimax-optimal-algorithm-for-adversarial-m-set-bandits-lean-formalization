import MsetsPaper.Probability.FiniteExponential

/-! # Pathwise telescoping on an adaptive action tree -/

namespace MsetsPaper.Probability

variable {α : Type}

theorem pathSum_le_potential_drop
    (g b : (t : ℕ) → ActionTree α t → α → ℝ)
    (V : (t : ℕ) → ActionTree α t → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ h a, g t h a ≤ V t h - V (t + 1) (h, a) + b t h a) :
    ∀ h, pathSum g T h ≤ V 0 () - V T h + pathSum b T h := by
  induction T with
  | zero => intro h; cases h; simp [pathSum]
  | succ T ih =>
    rintro ⟨h, a⟩
    have hp := ih (fun t ht h a ↦ hstep t (Nat.lt_trans ht (Nat.lt_succ_self T)) h a) h
    have hs := hstep T (Nat.lt_succ_self T) h a
    simp only [pathSum_succ]
    linarith

theorem pathSum_mono_upto (g b : (t : ℕ) → ActionTree α t → α → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ h a, g t h a ≤ b t h a) :
    ∀ h, pathSum g T h ≤ pathSum b T h := by
  induction T with
  | zero => intro h; simp
  | succ T ih =>
    rintro ⟨h, a⟩
    exact add_le_add
      (ih (fun t ht h a ↦ hstep t (Nat.lt_trans ht (Nat.lt_succ_self T)) h a) h)
      (hstep T (Nat.lt_succ_self T) h a)

theorem pathSum_congr_upto (g b : (t : ℕ) → ActionTree α t → α → ℝ) (T : ℕ)
    (hstep : ∀ t < T, ∀ h a, g t h a = b t h a) :
    ∀ h, pathSum g T h = pathSum b T h := by
  intro h
  exact le_antisymm (pathSum_mono_upto g b T (fun t ht h a ↦ (hstep t ht h a).le) h)
    (pathSum_mono_upto b g T (fun t ht h a ↦ (hstep t ht h a).ge) h)

theorem pathSum_mul (g : (t : ℕ) → ActionTree α t → α → ℝ) (c : ℝ) :
    ∀ t h, pathSum (fun t h a ↦ c * g t h a) t h = c * pathSum g t h := by
  intro t h
  simpa using pathSum_linear g (fun _ _ _ ↦ 0) c 0 t h

theorem pathSum_add (g b : (t : ℕ) → ActionTree α t → α → ℝ) :
    ∀ t h, pathSum (fun t h a ↦ g t h a + b t h a) t h =
      pathSum g t h + pathSum b t h := by
  intro t h
  simpa using pathSum_linear g b 1 1 t h

theorem pathSum_sub (g b : (t : ℕ) → ActionTree α t → α → ℝ) :
    ∀ t h, pathSum (fun t h a ↦ g t h a - b t h a) t h =
      pathSum g t h - pathSum b t h := by
  intro t h
  simpa [sub_eq_add_neg] using pathSum_linear g b 1 (-1) t h

end MsetsPaper.Probability
