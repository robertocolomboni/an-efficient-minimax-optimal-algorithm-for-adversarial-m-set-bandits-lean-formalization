import MsetsPaper.Probability.FiniteKLDivergence
import MsetsPaper.Alignment.Definitions
import MsetsPaper.Alignment.UpperObservable
import MsetsPaper.Alignment.ImplementationAlgorithm

/-! Paper interfaces using Mathlib's actual extended-valued KL. The finite
sum remains the internal algebraic representation, with an explicit proved
identification at each positive reference law. No infinity is silently
converted to zero: finiteness is proved in `paperKL_ne_top`.
-/

noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory MsetsLower MsetsLower.History
open MsetsPaper.Probability MsetsPaper.Upper

namespace MsetsPaper.Alignment

section Finite
variable {α : Type*} [Fintype α] [MeasurableSpace α] [MeasurableSingletonClass α]

def paperKL (q p : α → ℝ) : ℝ≥0∞ :=
  InformationTheory.klDiv (finiteAtomicMeasure q id) (finiteAtomicMeasure p id)

theorem paperKL_eq_ofReal (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    paperKL q p = ENNReal.ofReal (finiteKL q p) :=
  klDiv_finiteAtomicMeasure_eq_ofReal_finiteKL q p hq hqsum hp hpsum

theorem paperKL_ne_top (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) : paperKL q p ≠ ∞ := by
  rw [paperKL_eq_ofReal q p hq hqsum hp hpsum]
  exact ENNReal.ofReal_ne_top

theorem paperKL_toReal (q p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    (paperKL q p).toReal = finiteKL q p :=
  klDiv_finiteAtomicMeasure_toReal q p hq hqsum hp hpsum

theorem paperKL_le_iff (q r p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hr : ∀ x, 0 ≤ r x) (hrsum : ∑ x, r x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    paperKL q p ≤ paperKL r p ↔ finiteKL q p ≤ finiteKL r p := by
  rw [← ENNReal.toReal_le_toReal (paperKL_ne_top q p hq hqsum hp hpsum)
    (paperKL_ne_top r p hr hrsum hp hpsum),
    paperKL_toReal q p hq hqsum hp hpsum, paperKL_toReal r p hr hrsum hp hpsum]

theorem paperKL_add_le_of_finite (q next p : α → ℝ)
    (hq : ∀ x, 0 ≤ q x) (hqsum : ∑ x, q x = 1)
    (hn : ∀ x, 0 < next x) (hnsum : ∑ x, next x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    {eps : ℝ} (heps : 0 ≤ eps)
    (h : finiteKL q next + finiteKL next p ≤ finiteKL q p + eps) :
    paperKL q next + paperKL next p ≤ paperKL q p + ENNReal.ofReal eps := by
  rw [paperKL_eq_ofReal q next hq hqsum hn hnsum,
    paperKL_eq_ofReal next p (fun x => (hn x).le) hnsum hp hpsum,
    paperKL_eq_ofReal q p hq hqsum hp hpsum,
    ← ENNReal.ofReal_add (finiteKL_nonneg q next hq hqsum hn hnsum)
      (finiteKL_nonneg next p (fun x => (hn x).le) hnsum hp hpsum),
    ← ENNReal.ofReal_add (finiteKL_nonneg q p hq hqsum hp hpsum) heps]
  exact ENNReal.ofReal_le_ofReal h

theorem exact_omd_iff_extended_kl_projection (p q z : α → ℝ) (eta : ℝ)
    (C : Set (α → ℝ)) (hC : ∀ r ∈ C, (∀ x, 0 ≤ r x) ∧ ∑ x, r x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    (q ∈ C ∧ ∀ r ∈ C, eta * finiteExpectation q z + (paperKL q p).toReal ≤
      eta * finiteExpectation r z + (paperKL r p).toReal) ↔
    (q ∈ C ∧ ∀ r ∈ C, paperKL q (mwUpdate p z eta) ≤ paperKL r (mwUpdate p z eta)) := by
  have hn := mwUpdate_pos p z eta hp hpsum
  have hnsum := sum_mwUpdate p z eta hp hpsum
  constructor
  · rintro ⟨hq, hmin⟩
    refine ⟨hq, fun r hr => ?_⟩
    rw [paperKL_le_iff q r _ (hC q hq).1 (hC q hq).2 (hC r hr).1 (hC r hr).2 hn hnsum]
    apply (omd_objective_comparison p q r z eta hp hpsum (hC q hq).2 (hC r hr).2).mp
    simpa only [paperKL_toReal q p (hC q hq).1 (hC q hq).2 hp hpsum,
      paperKL_toReal r p (hC r hr).1 (hC r hr).2 hp hpsum] using hmin r hr
  · rintro ⟨hq, hmin⟩
    refine ⟨hq, fun r hr => ?_⟩
    rw [paperKL_toReal q p (hC q hq).1 (hC q hq).2 hp hpsum,
      paperKL_toReal r p (hC r hr).1 (hC r hr).2 hp hpsum]
    apply (omd_objective_comparison p q r z eta hp hpsum (hC q hq).2 (hC r hr).2).mpr
    exact (paperKL_le_iff q r _ (hC q hq).1 (hC q hq).2
      (hC r hr).1 (hC r hr).2 hn hnsum).mp (hmin r hr)

end Finite

variable {d m : ℕ}

/-- L7's primal optimizer, expressed with extended-valued relative entropy. -/
theorem projection_minimizes_extendedKL (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (lam : ℝ)
    (hlam : 0 < lam) (hlamhalf : lam ≤ 1 / 2)
    (v : Fin d → ℝ)
    (hmin : ∀ u, projectionDual (m := m) theta (projectionLower d m lam)
      (projectionUpper d m lam) v ≤ projectionDual (m := m) theta
        (projectionLower d m lam) (projectionUpper d m lam) u) :
    Implementation.SmoothingPolytope lam (weightedLaw (m := m) (theta + v)) ∧
    ∀ q : Action d m → ℝ, Implementation.SmoothingPolytope lam q →
      paperKL (weightedLaw (m := m) (theta + v)) (weightedLaw theta) ≤
        paperKL q (weightedLaw theta) := by
  obtain ⟨hbox, hopt⟩ := (Implementation.projection_dual theta hm hmtop lam hlam hlamhalf).2.2.1 v hmin
  refine ⟨hbox, fun q hq => ?_⟩
  exact (paperKL_le_iff _ q _
    (fun x => (weightedLaw_pos (theta + v) (by omega) x).le)
    (sum_weightedLaw (theta + v) (by omega)) hq.1.1 hq.1.2
    (weightedLaw_pos theta (by omega)) (sum_weightedLaw theta (by omega))).mpr (hopt q hq)

/-- L8 with its genuine measure KL in both input and output; the computed
vector, global dual accuracy and resource bounds are the same as before. -/
theorem approximate_projection_extendedKL (theta : Fin d → ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (eta T : ℝ)
    (heta : 0 < eta) (hcap : eta ≤ 1 / (256 * (d : ℝ))) (hT : 1 ≤ T)
    (hKL : paperKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤
      ENNReal.ofReal T) :
    let run := ResourcePrograms.projectionArena (Implementation.storeParameter theta) m eta T
    let v := ellipsoidProjectionShift (m := m) theta eta T
    SchurSolver.storedVector run.1.value = theta + v ∧
    coordinateL1 v ≤ projectionRadius d T ∧
    (∀ u, projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
      (projectionUpper d m (128 * eta * d)) v ≤
      projectionDual (m := m) theta (projectionLower d m (128 * eta * d))
        (projectionUpper d m (128 * eta * d)) u + projectionTolerance d eta T) ∧
    Implementation.SmoothingPolytope ((128 * eta * d) / 2)
      (weightedLaw (m := m) (SchurSolver.storedVector run.1.value)) ∧
    (∀ q : Action d m → ℝ, Implementation.SmoothingPolytope (128 * eta * d) q →
      paperKL q (weightedLaw (m := m) (SchurSolver.storedVector run.1.value)) +
        paperKL (weightedLaw (m := m) (SchurSolver.storedVector run.1.value)) (weightedLaw theta) ≤
          paperKL q (weightedLaw theta) + ENNReal.ofReal (eta / T)) ∧
    (run.1.work : ℝ) ≤ Implementation.projectionTimeBound d m eta T ∧
    run.2 ≤ ResourcePrograms.projectionArenaSpace d m := by
  have hmd : m ≤ d := by omega
  have hinput : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw theta) ≤ T := by
    rw [← paperKL_toReal _ _ (fun x => (weightedLaw_pos _ hmd x).le)
      (sum_weightedLaw _ hmd) (weightedLaw_pos theta hmd) (sum_weightedLaw theta hmd)]
    exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hKL).trans_eq
      (ENNReal.toReal_ofReal (by linarith))
  obtain ⟨hout, hradius, haccuracy, hbox, hpyth, hwork, hspace⟩ :=
    Implementation.approximate_projection theta hm hmtop eta T heta hcap hT hinput
  refine ⟨hout, hradius, haccuracy, hbox, ?_, hwork, hspace⟩
  intro q hq
  exact paperKL_add_le_of_finite _ _ _ hq.1.1 hq.1.2
    (weightedLaw_pos _ hmd) (sum_weightedLaw _ hmd)
    (weightedLaw_pos _ hmd) (sum_weightedLaw _ hmd)
    (div_nonneg heta.le (by linarith)) (hpyth q hq)

/-- L4 on the actual observable run law, with the measure-theoretic KL in
the initial entropy term. Its reference law is proved strictly positive. -/
theorem upper_omd_stability_extendedKL
    (L : SignedLossProcess d m) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (q : Action d m → ℝ) (hq : ∀ a, 0 ≤ q a) (hqsum : ∑ a, q a = 1)
    (hqbox : ∀ i,
      128 * mainLearningRate d T (Nat.choose d m) delta * d * ((m : ℝ) / d) ≤ marginal q i ∧
      marginal q i ≤ 1 - 128 * mainLearningRate d T (Nat.choose d m) delta * d *
        (1 - (m : ℝ) / d)) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
    ∀ᵐ h ∂signedRunLaw (mainAlgorithm T delta (by omega)) L T,
      observablePathSum (observableSurrogateDifference theta L eta q) T h ≤
        (paperKL q (weightedLaw (m := m) (0 : Fin d → ℝ))).toReal / eta + 1 +
          2 * eta * observablePathSum (observableSurrogateSecondMoment theta L eta) T h := by
  simpa only [paperKL_toReal q _ hq hqsum (weightedLaw_pos _ (by omega))
    (sum_weightedLaw _ (by omega))] using
    upper_omd_stability_observable L hmpos hmtop T hT hdelta0 hdelta1 q hq hqsum hqbox

/-- P1's invariant in extended KL, including t=0 and the final update. -/
theorem algorithm_uniform_extendedKL (L : SignedLossProcess d m)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 1 ≤ T)
    (delta : ℝ) (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (t : ℕ) (ht : t ≤ T) (h : ActionTree (Action d m) t) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    paperKL (weightedLaw (m := m) (0 : Fin d → ℝ))
      (weightedLaw (parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h)) ≤
        ENNReal.ofReal t := by
  have hi := (Implementation.efficient_implementation L hm hmtop T hT
    delta hdelta0 hdelta1).2.1 t ht h
  dsimp only
  rw [paperKL_eq_ofReal _ _ (fun x => (weightedLaw_pos _ (by omega) x).le)
    (sum_weightedLaw _ (by omega)) (weightedLaw_pos _ (by omega))
    (sum_weightedLaw _ (by omega))]
  exact ENNReal.ofReal_le_ofReal hi.2

/-- P1's actual update has the paper's extended-KL Pythagorean contract. -/
theorem algorithm_projection_transition_extendedKL (L : SignedLossProcess d m)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {eta : ℝ} (heta : 0 < eta) (hcap : eta ≤ 1 / (256 * (d : ℝ)))
    (t : ℕ) (ht : t < T) (h : ActionTree (Action d m) t) (a : Action d m) :
    let theta := parametersOnActions (ellipsoidAlgorithmParameters eta T) L t h
    let next := parametersOnActions (ellipsoidAlgorithmParameters eta T) L (t + 1) (h, a)
    let tilde := theta - eta • surrogateVector theta (lossesOnActions L t h) eta a
    Implementation.SmoothingPolytope ((128 * eta * d) / 2) (weightedLaw (m := m) next) ∧
    ∀ q : Action d m → ℝ, Implementation.SmoothingPolytope (128 * eta * d) q →
      paperKL q (weightedLaw (m := m) next) +
        paperKL (weightedLaw (m := m) next) (weightedLaw tilde) ≤
          paperKL q (weightedLaw tilde) + ENNReal.ofReal (eta / T) := by
  obtain ⟨hbox, hpyth⟩ :=
    Implementation.algorithm_projection_transition L hm hmtop T hT heta hcap t ht h a
  refine ⟨hbox, fun q hq => ?_⟩
  exact paperKL_add_le_of_finite _ _ _ hq.1.1 hq.1.2
    (weightedLaw_pos _ (by omega)) (sum_weightedLaw _ (by omega))
    (weightedLaw_pos _ (by omega)) (sum_weightedLaw _ (by omega))
    (div_nonneg heta.le (Nat.cast_nonneg _)) (hpyth q hq)

end MsetsPaper.Alignment
