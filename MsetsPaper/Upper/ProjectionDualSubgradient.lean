import MsetsPaper.Upper.ProjectionDual

/-! # Convexity and the manuscript's explicit projection-dual subgradient -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

def scalarProjectionPenalty (a b x : ℝ) : ℝ := -a * max x 0 + b * max (-x) 0

def scalarProjectionSlope (a b x : ℝ) : ℝ :=
  if 0 < x then -a else if x < 0 then -b else -(a + b) / 2

theorem scalarProjectionPenalty_pos (a b x : ℝ) (hx : 0 ≤ x) :
    scalarProjectionPenalty a b x = -a * x := by
  simp [scalarProjectionPenalty, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]

theorem scalarProjectionPenalty_neg (a b x : ℝ) (hx : x ≤ 0) :
    scalarProjectionPenalty a b x = -b * x := by
  rw [scalarProjectionPenalty, max_eq_right hx, max_eq_left (neg_nonneg.mpr hx)]
  ring

theorem scalarProjectionPenalty_eq_max (a b x : ℝ) (hab : a ≤ b) :
    scalarProjectionPenalty a b x = max (-a * x) (-b * x) := by
  by_cases hx : 0 ≤ x
  · rw [scalarProjectionPenalty_pos _ _ _ hx, max_eq_left]
    nlinarith [mul_le_mul_of_nonneg_right hab hx]
  · have hx' : x ≤ 0 := by linarith
    rw [scalarProjectionPenalty_neg _ _ _ hx', max_eq_right]
    nlinarith [mul_le_mul_of_nonpos_right hab hx']

theorem scalarProjectionPenalty_support (a b x y : ℝ) (hab : a ≤ b) :
    scalarProjectionPenalty a b x + scalarProjectionSlope a b x * (y - x) ≤
      scalarProjectionPenalty a b y := by
  have hyA : -a * y ≤ scalarProjectionPenalty a b y := by
    rw [scalarProjectionPenalty_eq_max _ _ _ hab]
    exact le_max_left _ _
  have hyB : -b * y ≤ scalarProjectionPenalty a b y := by
    rw [scalarProjectionPenalty_eq_max _ _ _ hab]
    exact le_max_right _ _
  by_cases hx : 0 < x
  · rw [scalarProjectionSlope, if_pos hx, scalarProjectionPenalty_pos _ _ _ hx.le]
    nlinarith
  · by_cases hx' : x < 0
    · rw [scalarProjectionSlope, if_neg hx, if_pos hx', scalarProjectionPenalty_neg _ _ _ hx'.le]
      nlinarith
    · have hx0 : x = 0 := by linarith
      subst x
      rw [scalarProjectionPenalty_pos _ _ _ le_rfl]
      simp only [scalarProjectionSlope, lt_self_iff_false, ↓reduceIte, sub_zero,
        mul_zero, zero_add]
      nlinarith

variable {d m : ℕ}

/-- An arbitrary allowable subgradient at the kink; the other branches are
the derivatives of the corresponding affine pieces. -/
def scalarProjectionSlopeWithZero (a b x s : ℝ) : ℝ :=
  if 0 < x then -a else if x < 0 then -b else s

theorem scalarProjectionPenalty_support_with_zero (a b x y s : ℝ) (hab : a ≤ b)
    (hs : x = 0 → -b ≤ s ∧ s ≤ -a) :
    scalarProjectionPenalty a b x + scalarProjectionSlopeWithZero a b x s * (y - x) ≤
      scalarProjectionPenalty a b y := by
  have hyA : -a * y ≤ scalarProjectionPenalty a b y := by
    rw [scalarProjectionPenalty_eq_max _ _ _ hab]; exact le_max_left _ _
  have hyB : -b * y ≤ scalarProjectionPenalty a b y := by
    rw [scalarProjectionPenalty_eq_max _ _ _ hab]; exact le_max_right _ _
  by_cases hx : 0 < x
  · rw [scalarProjectionSlopeWithZero, if_pos hx, scalarProjectionPenalty_pos _ _ _ hx.le]
    nlinarith
  · by_cases hx' : x < 0
    · rw [scalarProjectionSlopeWithZero, if_neg hx, if_pos hx',
        scalarProjectionPenalty_neg _ _ _ hx'.le]
      nlinarith
    · have hx0 : x = 0 := by linarith
      subst x
      simp only [scalarProjectionSlopeWithZero, lt_self_iff_false, ↓reduceIte,
        scalarProjectionPenalty_pos _ _ _ le_rfl, mul_zero, sub_zero, zero_add]
      by_cases hy : 0 ≤ y
      · nlinarith [mul_le_mul_of_nonneg_right (hs rfl).2 hy]
      · nlinarith [mul_le_mul_of_nonpos_right (hs rfl).1 (le_of_not_ge hy)]

def projectionSubgradientWithZero (theta a b v s : Fin d → ℝ) : Fin d → ℝ :=
  fun i ↦ weightedMarginal (m := m) (theta + v) i +
    scalarProjectionSlopeWithZero (a i) (b i) (v i) (s i)

theorem projectionDual_subgradient_with_zero (theta a b u v s : Fin d → ℝ)
    (hmd : m ≤ d) (hab : ∀ i, a i ≤ b i)
    (hs : ∀ i, v i = 0 → -b i ≤ s i ∧ s i ≤ -a i) :
    projectionDual (m := m) theta a b v +
      projectionSubgradientWithZero (m := m) theta a b v s ⬝ᵥ (u - v) ≤
        projectionDual (m := m) theta a b u := by
  have hF := logPartition_support (m := m) (theta + v) (theta + u) hmd
  have hv : (theta + u) - (theta + v) = u - v := by abel
  rw [hv] at hF
  have hP := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin d))) ↦
    scalarProjectionPenalty_support_with_zero (a i) (b i) (v i) (u i) (s i) (hab i) (hs i)
  simp only [Finset.sum_add_distrib, scalarProjectionPenalty] at hP
  have hg : projectionSubgradientWithZero (m := m) theta a b v s ⬝ᵥ (u - v) =
      weightedMarginal (m := m) (theta + v) ⬝ᵥ (u - v) +
        ∑ i, scalarProjectionSlopeWithZero (a i) (b i) (v i) (s i) * (u i - v i) := by
    simp only [dotProduct, projectionSubgradientWithZero, Pi.sub_apply, add_mul,
      Finset.sum_add_distrib]
  rw [hg]
  simp only [projectionDual, projectionPenalty, Finset.sum_add_distrib]
  linarith

/-- Exactly the three coordinate branches displayed in the manuscript. -/
def projectionSubgradient (theta a b v : Fin d → ℝ) : Fin d → ℝ :=
  fun i => if 0 < v i then weightedMarginal (m := m) (theta + v) i - a i
    else if v i < 0 then weightedMarginal (m := m) (theta + v) i - b i
    else weightedMarginal (m := m) (theta + v) i - (a i + b i) / 2

theorem projectionSubgradient_eq (theta a b v : Fin d → ℝ) (i : Fin d) :
    projectionSubgradient (m := m) theta a b v i =
      weightedMarginal (m := m) (theta + v) i + scalarProjectionSlope (a i) (b i) (v i) := by
  unfold projectionSubgradient scalarProjectionSlope
  split_ifs <;> ring

/-- The global subgradient inequality, with no smoothness or subgradient premise. -/
theorem projectionDual_subgradient (theta a b u v : Fin d → ℝ) (hmd : m ≤ d)
    (hab : ∀ i, a i ≤ b i) :
    projectionDual (m := m) theta a b v +
      projectionSubgradient (m := m) theta a b v ⬝ᵥ (u - v) ≤
        projectionDual (m := m) theta a b u := by
  have heq : projectionSubgradient (m := m) theta a b v =
      projectionSubgradientWithZero (m := m) theta a b v (fun i ↦ -(a i + b i) / 2) := by
    ext i
    simp only [projectionSubgradient, projectionSubgradientWithZero, scalarProjectionSlopeWithZero]
    split_ifs <;> ring
  rw [heq]
  exact projectionDual_subgradient_with_zero theta a b u v _ hmd hab
    (fun i _ ↦ by constructor <;> linarith [hab i])

theorem projectionDual_convex (theta a b : Fin d → ℝ) (hmd : m ≤ d)
    (hab : ∀ i, a i ≤ b i) : ConvexOn ℝ Set.univ (projectionDual (m := m) theta a b) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  have hF := (logPartition_convex (m := m) hmd).2 (Set.mem_univ (theta + x))
    (Set.mem_univ (theta + y)) hs ht hst
  have hz : s • (theta + x) + t • (theta + y) = theta + (s • x + t • y) := by
    ext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    nlinarith [congrArg (fun r : ℝ ↦ r * theta i) hst]
  rw [hz] at hF
  have hP : projectionPenalty a b (s • x + t • y) ≤
      s * projectionPenalty a b x + t * projectionPenalty a b y := by
    unfold projectionPenalty
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    change scalarProjectionPenalty (a i) (b i) (s * x i + t * y i) ≤
      s * scalarProjectionPenalty (a i) (b i) (x i) +
        t * scalarProjectionPenalty (a i) (b i) (y i)
    simp_rw [scalarProjectionPenalty_eq_max _ _ _ (hab i)]
    apply max_le
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_left (-a i * x i) (-b i * x i)) hs,
        mul_le_mul_of_nonneg_left (le_max_left (-a i * y i) (-b i * y i)) ht]
    · nlinarith [mul_le_mul_of_nonneg_left (le_max_right (-a i * x i) (-b i * x i)) hs,
        mul_le_mul_of_nonneg_left (le_max_right (-a i * y i) (-b i * y i)) ht]
  change logPartition (m := m) (theta + (s • x + t • y)) +
    projectionPenalty a b (s • x + t • y) ≤ _
  dsimp [projectionDual]
  simpa only [smul_eq_mul, mul_add, add_assoc, add_left_comm, add_comm] using add_le_add hF hP

theorem projectionSubgradient_abs_le_one (theta a b v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) (i : Fin d) :
    |projectionSubgradient (m := m) theta a b v i| ≤ 1 := by
  have hmu0 := (weightedMarginal_pos (theta + v) hmpos hmtop i).le
  have hmu1 := (weightedMarginal_lt_one (theta + v) hmtop i).le
  rw [abs_le]
  unfold projectionSubgradient
  split_ifs <;> constructor <;> linarith [(ha i).1, (ha i).2, (hb i).1, (hb i).2]

theorem projectionSubgradient_norm_le_one (theta a b v : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    ‖projectionSubgradient (m := m) theta a b v‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro i
  exact projectionSubgradient_abs_le_one theta a b v hmpos hmtop ha hb i

end MsetsPaper.Upper
