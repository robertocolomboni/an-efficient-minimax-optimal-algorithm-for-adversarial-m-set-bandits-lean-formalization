import MsetsPaper.Alignment.UpperAmbient
import MsetsPaper.Probability.PolicyActionTree

/-! L5 for arbitrary predictable random comparator distributions on the
ambient space. Doob--Dynkin factorization and null-set normalization are
proved before transferring the canonical event. -/

namespace MsetsPaper.Alignment

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open MsetsPaper.Probability MsetsPaper.Probability.AmbientHistory
open scoped BigOperators

noncomputable section
variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

theorem exists_normalized_comparator_upto (μ : Measure Ω) (hmd : m ≤ d)
    (H : (t : ℕ) → Ω → History d m t) (q : ℕ → Ω → Action d m → ℝ) (T : ℕ)
    (hq : ∀ t < T,
      Measurable[(inferInstance : MeasurableSpace (History d m t)).comap (H t)] (q t))
    (hvalid : ∀ t < T, ∀ᵐ ω ∂μ, IsDistribution (q t ω)) :
    ∃ q' : (t : ℕ) → History d m t → Action d m → ℝ,
      (∀ t, Measurable (q' t)) ∧
      (∀ t h, IsDistribution (q' t h)) ∧
      ∀ t < T, ∀ᵐ ω ∂μ, q' t (H t ω) = q t ω := by
  classical
  obtain ⟨Q, hQ⟩ := exists_normalized_policy_upto μ hmd H q T hq hvalid
  let q' (t : ℕ) (h : History d m t) (a : Action d m) := (Q.kernel t h).real {a}
  refine ⟨q', ?_, ?_, ?_⟩
  · intro t
    apply measurable_pi_lambda
    intro a
    exact ((Q.kernel t).measurable_coe (measurableSet_singleton a)).ennreal_toReal
  · intro t h
    exact ⟨fun _ ↦ measureReal_nonneg, PolicyActionTree.sum_action_probability Q t h⟩
  · intro t ht
    filter_upwards [hQ t ht, hvalid t ht] with ω hQω hvω
    funext a
    change (Q.kernel t (H t ω)).real {a} = q t ω a
    rw [hQω, finiteAtomicMeasure_real_apply _ hvω.1 id _ (measurableSet_singleton a)]
    simp

theorem measurable_comparatorDelta
    (theta ell : Ω → Fin d → ℝ) (q : Ω → Action d m → ℝ)
    (htheta : Measurable theta) (hell : Measurable ell) (hq : Measurable q)
    (a : Action d m) : Measurable (fun ω ↦ comparatorDelta (theta ω) (q ω) (ell ω) a) := by
  have he := measurable_estimateFromFeedback theta (fun _ ↦ a)
    (fun ω ↦ actionLoss a (ell ω)) htheta measurable_const (measurable_actionLoss a hell)
  have hes (b : Action d m) : Measurable (fun ω ↦ estimateScalar (theta ω) a (ell ω) b) := by
    simp only [estimateScalar, dotProduct_comm (fun i ↦ History.selectedIndicator i b),
      dot_indicator_eq_actionLoss]
    simpa only [estimateFromFeedback_eq_estimateVector] using measurable_actionLoss b he
  unfold comparatorDelta comparatorEstimate comparatorTrue finiteExpectation
  exact (Finset.measurable_sum _ (fun b _ ↦ ((hq.eval (a := b)).mul (hes b)))).sub
    (Finset.measurable_sum _ (fun b _ ↦ (hq.eval (a := b)).mul (measurable_actionLoss b hell)))

theorem measurable_comparatorV
    (theta : Ω → Fin d → ℝ) (q : Ω → Action d m → ℝ)
    (htheta : Measurable theta) (hq : Measurable q) :
    Measurable (fun ω ↦ comparatorV (theta ω) (q ω)) := by
  unfold comparatorV finiteExpectation
  exact Finset.measurable_sum _ (fun b _ ↦ (hq.eval (a := b)).mul
    (measurable_actionLoss b (measurable_actual_correction theta htheta)))

def ambientComparatorDelta
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (q : ℕ → Ω → Action d m → ℝ) (eta : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T,
    comparatorDelta (ellipsoidAlgorithmParameters eta T t (history X ell t ω))
      (q t ω) (ell t ω) (X t ω)

def ambientComparatorV
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (q : ℕ → Ω → Action d m → ℝ) (eta : ℝ) (T : ℕ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T,
    comparatorV (ellipsoidAlgorithmParameters eta T t (history X ell t ω)) (q t ω)

/-- L5 for any history-predictable comparator sequence; its validity and
normalization, like the stochastic protocol premises, need hold only a.s.
and only before the finite horizon. -/
theorem upper_kw_concentration_ambient
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hX : ∀ t < T, Measurable (X t))
    (hell : ∀ t < T, Measurable[historySigma X ell t] (ell t))
    (hp : ∀ t < T, Measurable[historySigma X ell t] (p t))
    (hnorm : ∀ t < T, ∀ᵐ ω ∂μ, ∀ a : Action d m, |actionLoss a (ell t ω)| ≤ 1)
    (halgorithm : ∀ t < T, ∀ᵐ ω ∂μ,
      p t ω = weightedLaw (m := m) (ellipsoidAlgorithmParameters
        (mainLearningRate d T (Nat.choose d m) delta) T t (history X ell t ω)))
    (hsample : letI : Nonempty (Action d m) := nonempty_MSetAction (show m ≤ d by omega)
      ∀ t < T, ∀ᵐ ω ∂μ,
        condDistrib (X t) (history X ell t) μ (history X ell t ω) =
          finiteAtomicMeasure (p t ω) id)
    (q : ℕ → Ω → Action d m → ℝ)
    (hqmeas : ∀ t < T, Measurable[historySigma X ell t] (q t))
    (hq : ∀ t < T, ∀ᵐ ω ∂μ, IsDistribution (q t ω))
    {rho : ℝ} (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    1 - rho ≤ μ.real {ω | |ambientComparatorDelta X ell q eta T ω| ≤
      eta / 4 * ambientComparatorV X ell q eta T ω + Real.log (2 / rho) / eta} := by
  classical
  have hmd : m ≤ d := by omega
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  let eta := mainLearningRate d T (Nat.choose d m) delta
  let theta := ellipsoidAlgorithmParameters (d := d) (m := m) eta T
  obtain ⟨L, hL, hlaw⟩ := exists_mainAlgorithm_ambient_law μ X ell p hmd T delta
    hX hell hp hnorm halgorithm hsample
  obtain ⟨q', hqm, hqv, hqeq⟩ := exists_normalized_comparator_upto μ hmd
    (history X ell) q T hqmeas hq
  have hb := upper_kw_concentration L hmpos hmtop T hT hdelta0 hdelta1 q' hqm
    (fun t _ h a ↦ (hqv t h).1 a) (fun t _ h ↦ (hqv t h).2) hrho0 hrho1
  have hLa : ∀ᵐ ω ∂μ, ∀ t < T, L.itemLoss t (history X ell t ω) = ell t ω := by
    simpa only [ae_all_iff] using hL
  have hqa : ∀ᵐ ω ∂μ, ∀ t < T, q' t (history X ell t ω) = q t ω := by
    simpa only [ae_all_iff] using hqeq
  have hd : (fun ω ↦ observablePathSum (observableComparatorDelta theta q' L) T
      (history X ell T ω)) =ᵐ[μ] ambientComparatorDelta X ell q eta T := by
    filter_upwards [hLa, hqa] with ω hLω hqω
    rw [observablePathSum_history]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [observableComparatorDelta, ambientComparatorDelta,
      hLω t (Finset.mem_range.mp ht), hqω t (Finset.mem_range.mp ht)]
    rfl
  have hv : (fun ω ↦ observablePathSum (observableComparatorV theta q') T
      (history X ell T ω)) =ᵐ[μ] ambientComparatorV X ell q eta T := by
    filter_upwards [hqa] with ω hqω
    rw [observablePathSum_history]
    apply Finset.sum_congr rfl
    intro t ht
    simp only [observableComparatorV, ambientComparatorV, hqω t (Finset.mem_range.mp ht)]
    rfl
  let E : Set (History d m T) := {h |
    |observablePathSum (observableComparatorDelta theta q' L) T h| ≤
      eta / 4 * observablePathSum (observableComparatorV theta q') T h + Real.log (2 / rho) / eta}
  have hE : MeasurableSet E := by
    apply measurableSet_le
    · exact (measurable_observablePathSum _ (fun t a ↦
        measurable_comparatorDelta (theta t) (L.itemLoss t) (q' t)
          (measurable_ellipsoidAlgorithmParameters eta T t) (L.measurable_itemLoss t) (hqm t) a) T).abs
    · exact ((measurable_observablePathSum _ (fun t _ ↦
        measurable_comparatorV (theta t) (q' t)
          (measurable_ellipsoidAlgorithmParameters eta T t) (hqm t)) T).const_mul _).add_const _
  have heq : μ {ω | |ambientComparatorDelta X ell q eta T ω| ≤
      eta / 4 * ambientComparatorV X ell q eta T ω + Real.log (2 / rho) / eta} =
      μ ((history X ell T) ⁻¹' E) := by
    apply measure_congr
    filter_upwards [hd, hv] with ω hdω hvω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, E, hdω, hvω]
  change 1 - rho ≤ (μ {ω | |ambientComparatorDelta X ell q eta T ω| ≤
    eta / 4 * ambientComparatorV X ell q eta T ω + Real.log (2 / rho) / eta}).toReal
  rw [heq, ← Measure.map_apply
    (measurable_history_upto X ell T hX hell T le_rfl) hE, hlaw T le_rfl]
  exact hb

end
end MsetsPaper.Alignment
