import MsetsPaper.Probability.CanonicalSupermartingale
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exponential supermartingales on a finite adaptive action tree

Each nodewise moment bound is propagated with the proved tower property.
The final Markov step and logarithmic threshold are also proved here.
This is the conditional-moment -> supermartingale -> Markov route of L5/L6.
-/

namespace MsetsPaper.Probability

open scoped BigOperators

variable {α : Type}

noncomputable def pathSum (g : (t : ℕ) → ActionTree α t → α → ℝ) :
    (t : ℕ) → ActionTree α t → ℝ
  | 0, _ => 0
  | t + 1, (h, a) => pathSum g t h + g t h a

@[simp] theorem pathSum_zero (g : (t : ℕ) → ActionTree α t → α → ℝ)
    (h : ActionTree α 0) : pathSum g 0 h = 0 := rfl

@[simp] theorem pathSum_succ (g : (t : ℕ) → ActionTree α t → α → ℝ)
    (t : ℕ) (h : ActionTree α t) (a : α) :
    pathSum g (t + 1) (h, a) = pathSum g t h + g t h a := rfl

theorem pathSum_const (c : ℝ) : ∀ t (h : ActionTree α t),
    pathSum (fun _ _ _ ↦ c) t h = t * c := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
    rintro ⟨h, a⟩
    rw [pathSum_succ, ih]
    push_cast
    ring

theorem pathSum_linear (g v : (t : ℕ) → ActionTree α t → α → ℝ) (a b : ℝ) :
    ∀ t h, pathSum (fun s p x ↦ a * g s p x + b * v s p x) t h =
      a * pathSum g t h + b * pathSum v t h := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
    rintro ⟨h, x⟩
    simp only [pathSum_succ, ih]
    ring

variable [Fintype α]

theorem exponential_step (P : BranchingLaw α)
    (g : (t : ℕ) → ActionTree α t → α → ℝ)
    (hmgf : ∀ t h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1)
    (t : ℕ) (h : ActionTree α t) :
    (∑ a, P.next t h a * Real.exp (pathSum g (t + 1) (h, a))) ≤
      Real.exp (pathSum g t h) := by
  simp only [pathSum_succ, Real.exp_add]
  calc
    (∑ a, P.next t h a * (Real.exp (pathSum g t h) * Real.exp (g t h a))) =
        Real.exp (pathSum g t h) * ∑ a, P.next t h a * Real.exp (g t h a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ Real.exp (pathSum g t h) * 1 :=
      mul_le_mul_of_nonneg_left (hmgf t h) (Real.exp_pos _).le
    _ = _ := mul_one _

theorem exponential_expectation_le_one (P : BranchingLaw α)
    (g : (t : ℕ) → ActionTree α t → α → ℝ)
    (hmgf : ∀ t h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1) (T : ℕ) :
    P.expectation T (fun h ↦ Real.exp (pathSum g T h)) ≤ 1 := by
  have h := CanonicalFiniteTree.expectation_le_initial P
    (fun t h ↦ Real.exp (pathSum g t h)) T
    (fun t _ h ↦ exponential_step P g hmgf t h)
  simpa only [pathSum, Real.exp_zero] using h

/-- The logarithmic tail is a consequence of the finite Markov inequality. -/
theorem exponential_log_tail (P : BranchingLaw α)
    (g : (t : ℕ) → ActionTree α t → α → ℝ)
    (hmgf : ∀ t h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1)
    (T : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    P.probability T {h | Real.log (1 / rho) ≤ pathSum g T h} ≤ rho := by
  have hr : 0 < 1 / rho := by positivity
  have hM := P.probability_ge_le_expectation_div T
    (fun h ↦ Real.exp (pathSum g T h)) (fun h ↦ (Real.exp_pos _).le) hr
  have hE : {h | Real.log (1 / rho) ≤ pathSum g T h} =
      {h | 1 / rho ≤ Real.exp (pathSum g T h)} := by
    ext h
    exact (Real.log_le_iff_le_exp hr)
  rw [hE]
  calc
    _ ≤ P.expectation T (fun h ↦ Real.exp (pathSum g T h)) / (1 / rho) := hM
    _ ≤ 1 / (1 / rho) := div_le_div_of_nonneg_right
      (exponential_expectation_le_one P g hmgf T) hr.le
    _ = rho := by simp

theorem exp_le_chord_zero_one {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1) :
    Real.exp u ≤ 1 + (Real.exp 1 - 1) * u := by
  have h : Real.exp ((1-u) * 0 + u * 1) ≤ (1-u) * Real.exp 0 + u * Real.exp 1 :=
    convexOn_exp.2 (Set.mem_univ _) (Set.mem_univ _) (by linarith) hu (by ring)
  simp only [mul_zero, zero_add, mul_one, Real.exp_zero] at h
  nlinarith

/-- The exact conditional exponential estimate in L6, including compensation. -/
theorem nonnegative_bounded_mgf {β : Type} [Fintype β]
    (p x : β → ℝ) (hp : ∀ a, 0 ≤ p a) (hsum : ∑ a, p a = 1)
    {B mean : ℝ} (hB : 0 < B) (hx : ∀ a, 0 ≤ x a ∧ x a ≤ B)
    (hmean : ∑ a, p a * x a = mean) :
    (∑ a, p a * Real.exp (x a / B - (Real.exp 1 - 1) * mean / B)) ≤ 1 := by
  have hraw : (∑ a, p a * Real.exp (x a / B)) ≤
      1 + (Real.exp 1 - 1) * mean / B := by
    calc
      _ ≤ ∑ a, p a * (1 + (Real.exp 1 - 1) * (x a / B)) := by
        apply Finset.sum_le_sum
        intro a _
        exact mul_le_mul_of_nonneg_left (exp_le_chord_zero_one
          (div_nonneg (hx a).1 hB.le) ((div_le_one hB).mpr (hx a).2)) (hp a)
      _ = _ := by
        simp only [mul_add, mul_one, Finset.sum_add_distrib, hsum]
        congr 1
        rw [← hmean]
        simp only [Finset.mul_sum, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro a _
        ring
  have hraw' : (∑ a, p a * Real.exp (x a / B)) ≤
      Real.exp ((Real.exp 1 - 1) * mean / B) := by
    exact hraw.trans (by simpa [add_comm] using
      Real.add_one_le_exp ((Real.exp 1 - 1) * mean / B))
  calc
    _ = (∑ a, p a * Real.exp (x a / B)) /
        Real.exp ((Real.exp 1 - 1) * mean / B) := by
      simp only [Real.exp_sub, ← mul_div_assoc, ← Finset.sum_div]
    _ ≤ 1 := (div_le_one (Real.exp_pos _)).mpr hraw'

omit [Fintype α] in
theorem pathSum_scaled_centered
    (x : (t : ℕ) → ActionTree α t → α → ℝ) (B c : ℝ) :
    ∀ t h, pathSum (fun s p a ↦ x s p a / B - c / B) t h =
      (pathSum x t h - c * t) / B := by
  intro t
  induction t with
  | zero => intro h; simp
  | succ t ih =>
    rintro ⟨h, a⟩
    simp only [pathSum_succ, ih, Nat.cast_add, Nat.cast_one]
    ring

/-- L6's sharp exponential-tail conclusion for an actual adaptive finite law. -/
theorem nonnegative_bounded_sum_tail (P : BranchingLaw α)
    (x : (t : ℕ) → ActionTree α t → α → ℝ)
    {B mean : ℝ} (hB : 0 < B)
    (hx : ∀ t h a, 0 ≤ x t h a ∧ x t h a ≤ B)
    (hmean : ∀ t h, ∑ a, P.next t h a * x t h a = mean)
    (T : ℕ) {rho : ℝ} (hrho : 0 < rho) :
    P.probability T {h | (Real.exp 1 - 1) * mean * T + B * Real.log (1 / rho) ≤
      pathSum x T h} ≤ rho := by
  let g := fun t h a ↦ x t h a / B - (Real.exp 1 - 1) * mean / B
  have hmgf : ∀ t h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1 := by
    intro t h
    exact nonnegative_bounded_mgf (P.next t h) (x t h) (P.nonneg t h)
      (P.sum_one t h) hB (hx t h) (hmean t h)
  refine (P.probability_mono T _ _ ?_).trans (exponential_log_tail P g hmgf T hrho)
  intro h hh
  change Real.log (1 / rho) ≤ pathSum g T h
  rw [show pathSum g T h =
      (pathSum x T h - (Real.exp 1 - 1) * mean * T) / B from
        pathSum_scaled_centered x B ((Real.exp 1 - 1) * mean) T h]
  apply (le_div_iff₀ hB).mpr
  change (Real.exp 1 - 1) * mean * T + B * Real.log (1 / rho) ≤ pathSum x T h at hh
  nlinarith

/-- The manuscript's (slightly looser) L6 bound, with the success probability
spelled out rather than left as a tail-event convention. -/
theorem nonnegative_bounded_sum_high_probability (P : BranchingLaw α)
    (x : (t : ℕ) → ActionTree α t → α → ℝ)
    {B mean : ℝ} (hB : 0 < B) (hmean0 : 0 ≤ mean)
    (hx : ∀ t h a, 0 ≤ x t h a ∧ x t h a ≤ B)
    (hmean : ∀ t h, ∑ a, P.next t h a * x t h a = mean)
    (T : ℕ) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 - rho ≤ P.probability T {h | pathSum x T h ≤
      2 * mean * T + 2 * B * Real.log (1 / rho)} := by
  apply P.probability_le_of_compl_bound
  refine (P.probability_mono T _ _ ?_).trans
    (nonnegative_bounded_sum_tail P x hB hx hmean T hrho)
  intro h hh
  have hnot : ¬ pathSum x T h ≤ 2 * mean * T + 2 * B * Real.log (1 / rho) := hh
  have hlog : 0 ≤ Real.log (1 / rho) := Real.log_nonneg ((one_le_div hrho).mpr hrho1)
  have hmuT : 0 ≤ mean * (T : ℝ) := mul_nonneg hmean0 (Nat.cast_nonneg T)
  have hc : (Real.exp 1 - 1) * (mean * T) ≤ 2 * (mean * T) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_three]) hmuT
  have hBlog : 0 ≤ B * Real.log (1 / rho) := mul_nonneg hB.le hlog
  change (Real.exp 1 - 1) * mean * T + B * Real.log (1 / rho) ≤ pathSum x T h
  nlinarith

theorem exponential_step_at (P : BranchingLaw α)
    (g : (t : ℕ) → ActionTree α t → α → ℝ) (t : ℕ) (h : ActionTree α t)
    (hmgf : ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1) :
    (∑ a, P.next t h a * Real.exp (pathSum g (t + 1) (h, a))) ≤
      Real.exp (pathSum g t h) := by
  simp only [pathSum_succ, Real.exp_add]
  calc
    _ = Real.exp (pathSum g t h) * ∑ a, P.next t h a * Real.exp (g t h a) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ ≤ Real.exp (pathSum g t h) * 1 :=
      mul_le_mul_of_nonneg_left hmgf (Real.exp_pos _).le
    _ = _ := mul_one _

theorem exponential_log_tail_upto (P : BranchingLaw α)
    (g : (t : ℕ) → ActionTree α t → α → ℝ) (T : ℕ)
    (hmgf : ∀ t < T, ∀ h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1)
    {rho : ℝ} (hrho : 0 < rho) :
    P.probability T {h | Real.log (1 / rho) ≤ pathSum g T h} ≤ rho := by
  have hexp : P.expectation T (fun h ↦ Real.exp (pathSum g T h)) ≤ 1 := by
    have h := CanonicalFiniteTree.expectation_le_initial P
      (fun t h ↦ Real.exp (pathSum g t h)) T
      (fun t ht h ↦ exponential_step_at P g t h (hmgf t ht h))
    simpa only [pathSum, Real.exp_zero] using h
  have hr : 0 < 1 / rho := by positivity
  have hM := P.probability_ge_le_expectation_div T
    (fun h ↦ Real.exp (pathSum g T h)) (fun h ↦ (Real.exp_pos _).le) hr
  have hE : {h | Real.log (1 / rho) ≤ pathSum g T h} =
      {h | 1 / rho ≤ Real.exp (pathSum g T h)} := by
    ext h
    exact Real.log_le_iff_le_exp hr
  rw [hE]
  exact hM.trans ((div_le_div_of_nonneg_right hexp hr.le).trans_eq (by simp))

/-- The sharper intermediate bound explicitly displayed in L6, before
replacing e-1 by 2 and enlarging the logarithmic coefficient. -/
theorem nonnegative_bounded_sum_sharp_high_probability_upto (P : BranchingLaw α)
    (x : (t : ℕ) → ActionTree α t → α → ℝ) (T : ℕ)
    {B mean : ℝ} (hB : 0 < B)
    (hx : ∀ t < T, ∀ h a, 0 ≤ x t h a ∧ x t h a ≤ B)
    (hmean : ∀ t < T, ∀ h, ∑ a, P.next t h a * x t h a = mean)
    {rho : ℝ} (hrho : 0 < rho) :
    1 - rho ≤ P.probability T {h | pathSum x T h ≤
      (Real.exp 1 - 1) * mean * T + B * Real.log (1 / rho)} := by
  let g := fun t h a ↦ x t h a / B - (Real.exp 1 - 1) * mean / B
  have hmgf : ∀ t < T, ∀ h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1 := by
    intro t ht h
    exact nonnegative_bounded_mgf (P.next t h) (x t h) (P.nonneg t h)
      (P.sum_one t h) hB (hx t ht h) (hmean t ht h)
  apply P.probability_le_of_compl_bound
  refine (P.probability_mono T _ _ ?_).trans (exponential_log_tail_upto P g T hmgf hrho)
  intro h hh
  have hnot : ¬ pathSum x T h ≤
      (Real.exp 1 - 1) * mean * T + B * Real.log (1 / rho) := hh
  change Real.log (1 / rho) ≤ pathSum g T h
  rw [show pathSum g T h =
      (pathSum x T h - (Real.exp 1 - 1) * mean * T) / B from
        pathSum_scaled_centered x B ((Real.exp 1 - 1) * mean) T h]
  apply (le_div_iff₀ hB).mpr
  linarith

theorem nonnegative_bounded_sum_high_probability_upto (P : BranchingLaw α)
    (x : (t : ℕ) → ActionTree α t → α → ℝ) (T : ℕ)
    {B mean : ℝ} (hB : 0 < B) (hmean0 : 0 ≤ mean)
    (hx : ∀ t < T, ∀ h a, 0 ≤ x t h a ∧ x t h a ≤ B)
    (hmean : ∀ t < T, ∀ h, ∑ a, P.next t h a * x t h a = mean)
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho ≤ 1) :
    1 - rho ≤ P.probability T {h | pathSum x T h ≤
      2 * mean * T + 2 * B * Real.log (1 / rho)} := by
  let g := fun t h a ↦ x t h a / B - (Real.exp 1 - 1) * mean / B
  have hmgf : ∀ t < T, ∀ h, ∑ a, P.next t h a * Real.exp (g t h a) ≤ 1 := by
    intro t ht h
    exact nonnegative_bounded_mgf (P.next t h) (x t h) (P.nonneg t h)
      (P.sum_one t h) hB (hx t ht h) (hmean t ht h)
  apply P.probability_le_of_compl_bound
  refine (P.probability_mono T _ _ ?_).trans (exponential_log_tail_upto P g T hmgf hrho)
  intro h hh
  have hnot : ¬ pathSum x T h ≤ 2 * mean * T + 2 * B * Real.log (1 / rho) := hh
  have hlog : 0 ≤ Real.log (1 / rho) := Real.log_nonneg ((one_le_div hrho).mpr hrho1)
  have hmuT : 0 ≤ mean * (T : ℝ) := mul_nonneg hmean0 (Nat.cast_nonneg T)
  have hc : (Real.exp 1 - 1) * (mean * T) ≤ 2 * (mean * T) :=
    mul_le_mul_of_nonneg_right (by linarith [Real.exp_one_lt_three]) hmuT
  have hBlog : 0 ≤ B * Real.log (1 / rho) := mul_nonneg hB.le hlog
  change Real.log (1 / rho) ≤ pathSum g T h
  rw [show pathSum g T h =
      (pathSum x T h - (Real.exp 1 - 1) * mean * T) / B from
        pathSum_scaled_centered x B ((Real.exp 1 - 1) * mean) T h]
  apply (le_div_iff₀ hB).mpr
  nlinarith

end MsetsPaper.Probability
