import MsetsPaper.Upper.ProjectionEllipsoidCapstone
import MsetsPaper.Upper.AlgorithmUpdate

/-! Borel measurability of the actual fixed-budget projection. Branches at
zero gradients and ties are included; no regularity of the returned optimizer
is assumed. The iteration budget depends on eta,T,d, not on the input theta. -/

noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace MsetsPaper.Upper

variable {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem measurable_coordinateL1 (v : Ω → Fin d → ℝ) (hv : Measurable v) :
    Measurable (fun w => coordinateL1 (v w)) :=
  Finset.measurable_sum Finset.univ
    (fun i _ => continuous_abs.measurable.comp ((measurable_pi_apply i).comp hv))

theorem measurable_projectionDual (theta v : Ω → Fin d → ℝ)
    (htheta : Measurable theta) (hv : Measurable v) (a b : Fin d → ℝ) :
    Measurable (fun w => projectionDual (m := m) (theta w) a b (v w)) := by
  apply (measurable_partition (m := m) (fun w => theta w + v w) (htheta.add hv)).log.add
  apply Finset.measurable_sum
  intro i _
  have hi := (measurable_pi_apply i).comp hv
  exact ((hi.max measurable_const).const_mul (-a i)).add
    ((hi.neg.max measurable_const).const_mul (b i))

theorem measurable_projectionSubgradient (theta v : Ω → Fin d → ℝ)
    (htheta : Measurable theta) (hv : Measurable v) (a b : Fin d → ℝ) :
    Measurable (fun w => projectionSubgradient (m := m) (theta w) a b (v w)) := by
  apply measurable_pi_lambda
  intro i
  have hi := (measurable_pi_apply i).comp hv
  have hmu := (measurable_pi_apply i).comp
    (measurable_actual_marginal (m := m) (fun w => theta w + v w) (htheta.add hv))
  exact Measurable.ite (measurableSet_lt measurable_const hi) (hmu.sub_const (a i))
    (Measurable.ite (measurableSet_lt hi measurable_const) (hmu.sub_const (b i))
      (hmu.sub_const ((a i + b i) / 2)))

theorem measurable_l1Separator (v : Ω → Fin d → ℝ) (hv : Measurable v) :
    Measurable (fun w => l1Separator (v w)) := by
  apply measurable_pi_lambda
  intro i
  exact Measurable.ite (measurableSet_le measurable_const ((measurable_pi_apply i).comp hv))
    measurable_const measurable_const

theorem measurable_projectionEllipsoidOracle (theta v : Ω → Fin d → ℝ)
    (htheta : Measurable theta) (hv : Measurable v) (a b : Fin d → ℝ) (R : ℝ) :
    Measurable (fun w => projectionEllipsoidOracle (m := m) (theta w) a b R (v w)) :=
  Measurable.ite (measurableSet_le (measurable_coordinateL1 v hv) measurable_const)
    (measurable_projectionSubgradient theta v htheta hv a b) (measurable_l1Separator v hv)

theorem measurable_ellipsoidMatVec (Q : Ω → Matrix (Fin d) (Fin d) ℝ)
    (v : Ω → Fin d → ℝ) (hQ : Measurable Q) (hv : Measurable v) :
    Measurable (fun w => Q w *ᵥ v w) := by
  apply measurable_pi_lambda
  intro i
  change Measurable (fun w => ∑ j, Q w i j * v w j)
  apply Finset.measurable_sum
  intro j _
  exact ((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hQ)).mul
    ((measurable_pi_apply j).comp hv)

theorem measurable_ellipsoidQuadratic (Q : Ω → Matrix (Fin d) (Fin d) ℝ)
    (v : Ω → Fin d → ℝ) (hQ : Measurable Q) (hv : Measurable v) :
    Measurable (fun w => ellipsoidQuadratic (Q w) (v w)) := by
  have hQv := measurable_ellipsoidMatVec Q v hQ hv
  change Measurable (fun w => ∑ i, v w i * (Q w *ᵥ v w) i)
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    ((measurable_pi_apply i).comp hv).mul ((measurable_pi_apply i).comp hQv))

theorem measurable_ellipsoidNextCenter (c g : Ω → Fin d → ℝ)
    (Q : Ω → Matrix (Fin d) (Fin d) ℝ)
    (hc : Measurable c) (hg : Measurable g) (hQ : Measurable Q) :
    Measurable (fun w => ellipsoidNextCenter (c w) (g w) (Q w)) := by
  have hq := measurable_ellipsoidQuadratic Q g hQ hg
  exact hc.sub ((measurable_const.div (hq.sqrt.const_mul ((d : ℝ) + 1))).smul
    (measurable_ellipsoidMatVec Q g hQ hg))

theorem measurable_ellipsoidNextShape (Q : Ω → Matrix (Fin d) (Fin d) ℝ)
    (g : Ω → Fin d → ℝ) (hQ : Measurable Q) (hg : Measurable g) :
    Measurable (fun w => ellipsoidNextShape (Q w) (g w)) := by
  have hq := measurable_ellipsoidQuadratic Q g hQ hg
  have hQg := measurable_ellipsoidMatVec Q g hQ hg
  apply measurable_pi_lambda
  intro i
  apply measurable_pi_lambda
  intro j
  change Measurable (fun w => ((d : ℝ) ^ 2 / ((d : ℝ) ^ 2 - 1)) *
    (Q w i j - ((2 / ((d : ℝ) + 1)) / ellipsoidQuadratic (Q w) (g w)) *
      ((Q w *ᵥ g w) i * (Q w *ᵥ g w) j)))
  exact (((measurable_pi_apply j).comp ((measurable_pi_apply i).comp hQ)).sub
    ((measurable_const.div hq).mul (((measurable_pi_apply i).comp hQg).mul
      ((measurable_pi_apply j).comp hQg)))).const_mul _

theorem measurable_projectionRetainBest (theta candidate best : Ω → Fin d → ℝ)
    (htheta : Measurable theta) (hc : Measurable candidate) (hb : Measurable best)
    (a b : Fin d → ℝ) (R : ℝ) :
    Measurable (fun w => projectionRetainBest (m := m) (theta w) a b R (candidate w) (best w)) :=
  Measurable.ite
    ((measurableSet_le (measurable_coordinateL1 candidate hc) measurable_const).inter
      (measurableSet_le (measurable_projectionDual theta candidate htheta hc a b)
        (measurable_projectionDual theta best htheta hb a b))) hc hb

theorem measurable_projectionSearchRun (theta : Ω → Fin d → ℝ)
    (htheta : Measurable theta) (a b : Fin d → ℝ) (R : ℝ) (n : ℕ) :
    Measurable (fun w => (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center) ∧
    Measurable (fun w => (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.shape) ∧
    Measurable (fun w => (projectionSearchRun (m := m) (theta w) a b R n).best) := by
  classical
  induction n with
  | zero => exact ⟨measurable_const, measurable_const, measurable_const⟩
  | succ n ih =>
    have hg := measurable_projectionEllipsoidOracle (m := m) theta _ htheta ih.1 a b R
    have hzero := measurableSet_eq_fun hg (measurable_const : Measurable (fun _ : Ω => (0 : Fin d → ℝ)))
    have hc : Measurable (fun w =>
        if projectionEllipsoidOracle (m := m) (theta w) a b R
            (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center = 0
        then (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center
        else ellipsoidNextCenter
          (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center
          (projectionEllipsoidOracle (m := m) (theta w) a b R
            (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center)
          (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.shape) :=
      Measurable.ite hzero ih.1 (measurable_ellipsoidNextCenter _ _ _ ih.1 hg ih.2.1)
    have hQ : Measurable (fun w =>
        if projectionEllipsoidOracle (m := m) (theta w) a b R
            (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center = 0
        then (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.shape
        else ellipsoidNextShape
          (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.shape
          (projectionEllipsoidOracle (m := m) (theta w) a b R
            (projectionSearchRun (m := m) (theta w) a b R n).ellipsoid.center)) :=
      Measurable.ite hzero ih.2.1 (measurable_ellipsoidNextShape _ _ ih.2.1 hg)
    have hb := measurable_projectionRetainBest (m := m) theta _ _ htheta ih.1 ih.2.2 a b R
    exact ⟨by simpa only [projectionSearchRun, projectionSearchStep, ellipsoidStep, apply_ite] using hc,
      by simpa only [projectionSearchRun, projectionSearchStep, ellipsoidStep, apply_ite] using hQ,
      hb⟩

theorem measurable_ellipsoidProjectionShift (eta T : ℝ) :
    Measurable (fun theta : Fin d → ℝ => ellipsoidProjectionShift (m := m) theta eta T) :=
  (measurable_projectionSearchRun (m := m) id measurable_id _ _ _ _).2.2

theorem measurable_ellipsoidProjection (eta T : ℝ) :
    Measurable (fun theta : Fin d → ℝ => ellipsoidProjection (m := m) theta eta T) :=
  measurable_id.add (measurable_ellipsoidProjectionShift (m := m) eta T)

end MsetsPaper.Upper
