import MsetsPaper.Upper.ProjectionEllipsoid

/-! Streaming best-feasible-center retention for the concrete ellipsoid
recursion. The search never tests the unknown optimal value. -/

noncomputable section
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

def projectionRetainBest (theta a b : Fin d → ℝ) (R : ℝ)
    (candidate best : Fin d → ℝ) : Fin d → ℝ :=
  if coordinateL1 candidate ≤ R ∧
      projectionDual (m := m) theta a b candidate ≤ projectionDual (m := m) theta a b best
    then candidate else best

structure ProjectionSearchState (d : ℕ) where
  ellipsoid : EllipsoidState d
  best : Fin d → ℝ
  queries : ℕ

def projectionSearchStep (theta a b : Fin d → ℝ) (R : ℝ)
    (st : ProjectionSearchState d) : ProjectionSearchState d :=
  ⟨ellipsoidStep (projectionEllipsoidOracle (m := m) theta a b R) st.ellipsoid,
    projectionRetainBest (m := m) theta a b R st.ellipsoid.center st.best,
    st.queries + 1⟩

def projectionSearchRun (theta a b : Fin d → ℝ) (R : ℝ) : ℕ → ProjectionSearchState d
  | 0 => ⟨ellipsoidInitial R, 0, 0⟩
  | n + 1 => projectionSearchStep (m := m) theta a b R (projectionSearchRun theta a b R n)

theorem projectionSearchRun_ellipsoid (theta a b : Fin d → ℝ) (R : ℝ) (n : ℕ) :
    (projectionSearchRun (m := m) theta a b R n).ellipsoid =
      ellipsoidRun (projectionEllipsoidOracle (m := m) theta a b R) R n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [projectionSearchRun, projectionSearchStep, ellipsoidRun] using
      (congrArg (ellipsoidStep (projectionEllipsoidOracle (m := m) theta a b R)) ih)

theorem projectionSearchRun_queries (theta a b : Fin d → ℝ) (R : ℝ) (n : ℕ) :
    (projectionSearchRun (m := m) theta a b R n).queries = n := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [projectionSearchRun, projectionSearchStep] using congrArg (· + 1) ih

theorem projectionRetainBest_feasible (theta a b : Fin d → ℝ) (R : ℝ)
    (candidate best : Fin d → ℝ) (hbest : coordinateL1 best ≤ R) :
    coordinateL1 (projectionRetainBest (m := m) theta a b R candidate best) ≤ R := by
  unfold projectionRetainBest
  split_ifs with h
  · exact h.1
  · exact hbest

theorem projectionRetainBest_le_old (theta a b : Fin d → ℝ) (R : ℝ)
    (candidate best : Fin d → ℝ) :
    projectionDual (m := m) theta a b (projectionRetainBest (m := m) theta a b R candidate best) ≤
      projectionDual (m := m) theta a b best := by
  unfold projectionRetainBest
  split_ifs with h
  · exact h.2
  · exact le_rfl

theorem projectionRetainBest_le_candidate (theta a b : Fin d → ℝ) (R : ℝ)
    (candidate best : Fin d → ℝ) (hfeas : coordinateL1 candidate ≤ R) :
    projectionDual (m := m) theta a b (projectionRetainBest (m := m) theta a b R candidate best) ≤
      projectionDual (m := m) theta a b candidate := by
  unfold projectionRetainBest
  split_ifs with h
  · exact le_rfl
  · exact le_of_not_ge (fun hle => h ⟨hfeas, hle⟩)

theorem projectionSearchRun_feasible (theta a b : Fin d → ℝ) (R : ℝ) (hR : 0 ≤ R) (n : ℕ) :
    coordinateL1 (projectionSearchRun (m := m) theta a b R n).best ≤ R := by
  induction n with
  | zero => simpa only [projectionSearchRun, coordinateL1, Pi.zero_apply, abs_zero,
      Finset.sum_const_zero] using hR
  | succ n ih => exact projectionRetainBest_feasible theta a b R _ _ ih

theorem projectionSearchRun_best_le_queried (theta a b : Fin d → ℝ) (R : ℝ) (n k : ℕ)
    (hk : k < n)
    (hfeas : coordinateL1
      (ellipsoidRun (projectionEllipsoidOracle (m := m) theta a b R) R k).center ≤ R) :
    projectionDual (m := m) theta a b (projectionSearchRun (m := m) theta a b R n).best ≤
      projectionDual (m := m) theta a b
        (ellipsoidRun (projectionEllipsoidOracle (m := m) theta a b R) R k).center := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hkn : k < n
    · exact (projectionRetainBest_le_old theta a b R _ _).trans (ih hkn)
    · have hkeq : k = n := by omega
      subst k
      have h := projectionRetainBest_le_candidate (m := m) theta a b R
        (projectionSearchRun (m := m) theta a b R n).ellipsoid.center
        (projectionSearchRun (m := m) theta a b R n).best
      rw [projectionSearchRun_ellipsoid] at h
      simpa only [projectionSearchRun, projectionSearchStep, projectionSearchRun_ellipsoid]
        using h hfeas

/-- The returned, retained center is accurate. Its program depends only on
the objective, its explicit subgradient and the search parameters, not on
the minimizer used in the proof. -/
theorem projectionSearchRun_accuracy (theta a b vstar : Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1) (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1)
    (hab : ∀ i, a i ≤ b i) (R tau : ℝ)
    (hstar : coordinateL1 vstar ≤ R / 2) (htau : 0 < tau) (htauR : tau ≤ R) :
    let N := ellipsoidIterationBudget d R (tau / (2 * Real.sqrt (d : ℝ)))
    let result := projectionSearchRun (m := m) theta a b R N
    coordinateL1 result.best ≤ R ∧
      projectionDual (m := m) theta a b result.best ≤
        projectionDual (m := m) theta a b vstar + tau ∧
      result.queries = N := by
  dsimp only
  obtain ⟨k, hk, hfeas, hgood⟩ := projectionEllipsoid_finds_good theta a b vstar
    hmpos hmtop ha hb hab R tau hstar htau htauR
  refine ⟨projectionSearchRun_feasible theta a b R (htau.le.trans htauR) _, ?_,
    projectionSearchRun_queries theta a b R _⟩
  exact (projectionSearchRun_best_le_queried theta a b R _ k hk hfeas).trans hgood

end MsetsPaper.Upper
