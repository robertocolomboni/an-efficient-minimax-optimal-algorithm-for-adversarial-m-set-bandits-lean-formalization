import MsetsPaper.Upper.EllipsoidIteration
import MsetsPaper.Upper.ProjectionApproximationCapstone

/-! The specific projection separation/subgradient oracle and its finite
central-cut search. No successful-optimization premise is supplied. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d m : ℕ}

def projectionEllipsoidOracle (theta a b : Fin d → ℝ) (R : ℝ)
    (v : Fin d → ℝ) : Fin d → ℝ :=
  if coordinateL1 v ≤ R then projectionSubgradient (m := m) theta a b v
  else l1Separator v

def projectionEllipsoidGood (theta a b vstar : Fin d → ℝ) (R tau : ℝ)
    (v : Fin d → ℝ) : Prop :=
  coordinateL1 v ≤ R ∧
    projectionDual (m := m) theta a b v ≤ projectionDual (m := m) theta a b vstar + tau

theorem projectionEllipsoidOracle_cuts (theta a b vstar : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) (R tau : ℝ)
    (hstar : coordinateL1 vstar ≤ R / 2) (htau : 0 < tau) (htauR : tau ≤ R)
    (c : Fin d → ℝ) (hbad : ¬ projectionEllipsoidGood (m := m) theta a b vstar R tau c) :
    projectionEllipsoidOracle (m := m) theta a b R c ≠ 0 ∧
      ∀ x, euclideanNorm (x - vstar) ≤ tau / (2 * Real.sqrt (d : ℝ)) →
        (x - c) ⬝ᵥ projectionEllipsoidOracle (m := m) theta a b R c ≤ 0 := by
  have hmd : m ≤ d := by omega
  have hball := fun x hx => projection_near_minimum_ball theta a b vstar x
    hmpos hmtop ha hb hab R tau hstar htauR hx
  by_cases hc : coordinateL1 c ≤ R
  · have hlarge : projectionDual (m := m) theta a b vstar + tau <
        projectionDual (m := m) theta a b c := by
      exact lt_of_not_ge (fun h => hbad ⟨hc, h⟩)
    have hstrict : ∀ x, euclideanNorm (x - vstar) ≤ tau / (2 * Real.sqrt (d : ℝ)) →
        (x - c) ⬝ᵥ projectionSubgradient (m := m) theta a b c < 0 := by
      intro x hx
      have hsub := projectionDual_subgradient theta a b x c hmd hab
      rw [dotProduct_comm (projectionSubgradient (m := m) theta a b c) (x - c)] at hsub
      have hxG := (hball x hx).2
      linarith
    have hstarBall : euclideanNorm (vstar - vstar) ≤ tau / (2 * Real.sqrt (d : ℝ)) := by
      simp only [sub_self, euclideanNorm, WithLp.toLp_zero, norm_zero]
      positivity
    refine ⟨?_, ?_⟩
    · simp only [projectionEllipsoidOracle, hc, ↓reduceIte]
      intro hzero
      have h := hstrict vstar hstarBall
      rw [hzero, dotProduct_zero] at h
      exact lt_irrefl 0 h
    · intro x hx
      simpa only [projectionEllipsoidOracle, hc, ↓reduceIte] using (hstrict x hx).le
  · have hsep : ∀ x, euclideanNorm (x - vstar) ≤ tau / (2 * Real.sqrt (d : ℝ)) →
        (x - c) ⬝ᵥ l1Separator c < 0 := by
      intro x hx
      have h := l1Separator_separates x c R (hball x hx).1 (lt_of_not_ge hc)
      rw [dotProduct_comm, dotProduct_sub]
      linarith [h.1, h.2]
    have hstarBall : euclideanNorm (vstar - vstar) ≤ tau / (2 * Real.sqrt (d : ℝ)) := by
      simp only [sub_self, euclideanNorm, WithLp.toLp_zero, norm_zero]
      positivity
    refine ⟨?_, ?_⟩
    · simp only [projectionEllipsoidOracle, hc, ↓reduceIte]
      intro hzero
      have h := hsep vstar hstarBall
      rw [hzero, dotProduct_zero] at h
      exact lt_irrefl 0 h
    · intro x hx
      simpa only [projectionEllipsoidOracle, hc, ↓reduceIte] using (hsep x hx).le

def ellipsoidIterationBudget (d : ℕ) (R rho : ℝ) : ℕ :=
  ⌈4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / rho)⌉₊ + 1

theorem ellipsoidIterationBudget_sufficient (d : ℕ) (R rho : ℝ) :
    4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / rho) <
      (ellipsoidIterationBudget d R rho : ℝ) := by
  have h := Nat.le_ceil (4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / rho))
  unfold ellipsoidIterationBudget
  push_cast
  linarith

theorem ellipsoidIterationBudget_bound (hd : 1 ≤ d) (R rho : ℝ)
    (hrho : 0 < rho) (hR : rho ≤ R) :
    (ellipsoidIterationBudget d R rho : ℝ) ≤
      8 * (d : ℝ) ^ 2 * Real.log (R / rho) + 2 := by
  have hdR : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hlog : 0 ≤ Real.log (R / rho) := Real.log_nonneg ((one_le_div hrho).mpr hR)
  have hnonneg : 0 ≤ 4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / rho) := by positivity
  have hceil := Nat.ceil_lt_add_one hnonneg
  unfold ellipsoidIterationBudget
  push_cast
  have hcoef : 4 * (d : ℝ) * ((d : ℝ) + 1) ≤ 8 * (d : ℝ) ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hcoef hlog]

theorem projectionEllipsoid_finds_good (theta a b vstar : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) (R tau : ℝ)
    (hstar : coordinateL1 vstar ≤ R / 2) (htau : 0 < tau) (htauR : tau ≤ R) :
    ∃ k < ellipsoidIterationBudget d R (tau / (2 * Real.sqrt (d : ℝ))),
      projectionEllipsoidGood (m := m) theta a b vstar R tau
        (ellipsoidRun (projectionEllipsoidOracle (m := m) theta a b R) R k).center := by
  have hd : 2 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hR : 0 < R := htau.trans_le htauR
  have hrho : 0 < tau / (2 * Real.sqrt (d : ℝ)) := by positivity
  apply ellipsoidRun_finds_good hd _ _ R _ hR hrho vstar
  · intro x hx
    exact (euclideanNorm_le_coordinateL1 x).trans
      (projection_near_minimum_ball theta a b vstar x hmpos hmtop ha hb hab
        R tau hstar htauR hx).1
  · exact projectionEllipsoidOracle_cuts theta a b vstar hmpos hmtop ha hb hab
      R tau hstar htau htauR
  · exact ellipsoidIterationBudget_sufficient d R _

end MsetsPaper.Upper
