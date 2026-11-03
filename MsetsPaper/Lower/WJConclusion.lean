import MsetsPaper.Lower.WJRegret
import MsetsPaper.Lower.WJTesting
import MsetsPaper.Lower.WJParameters
import MsetsPaper.Lower.SparseCappedSeedJensen
import MsetsPaper.Probability.PrivateSeedRunLaw
import MsetsPaper.Probability.ProductFixingBridge

/-!
The noise-table and regret steps of the introductory fixed-cardinality proof.
After the finite average bounds the exhaustion probability, a favorable set
can be fixed first. This merely reassociates the averaging; the noise and
the learner still follow their original, independent input laws.
-/

namespace MsetsPaper.Lower.WJ

open MsetsLower MsetsLower.Lower MsetsLower.Feedback
open MsetsPaper.Probability MsetsPaper.Probability.PrivateSeed
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def fixedSetJointLaw {d : ℕ} (P : Policy d 1) (S : Finset (Fin d))
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    Measure ((Fin T → SparseCapped.Noise) × History d 1 T) :=
  DenseCommonNoise.noiseTableMeasure T ⊗ₘ
    SparseCapped.fixedBitsRunKernel P (by omega) c epsilon he hs (bitsOfSet S) T

instance fixedSetJointLaw_isProbabilityMeasure {d : ℕ} (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    IsProbabilityMeasure (fixedSetJointLaw P S c T epsilon he hs) := by
  unfold fixedSetJointLaw
  infer_instance

theorem fixedSetJointLaw_map_noise {d : ℕ} (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    (fixedSetJointLaw P S c T epsilon he hs).map Prod.fst =
      DenseCommonNoise.noiseTableMeasure T := by
  exact Measure.fst_compProd _ _

theorem fixedSetJointLaw_map_history {d : ℕ} (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    (fixedSetJointLaw P S c T epsilon he hs).map Prod.snd =
      historyLaw P S c T epsilon he hs := by
  change (DenseCommonNoise.noiseTableMeasure T ⊗ₘ
    SparseCapped.fixedBitsRunKernel P (by omega) c epsilon he hs (bitsOfSet S) T).snd = _
  rw [Measure.snd_compProd]
  exact SparseCapped.noiseMixture_eq_observableProcess P (by omega) c epsilon he hs
    (bitsOfSet S) T

theorem fixedSetJointLaw_eq_parametric {d : ℕ} (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    fixedSetJointLaw P S c T epsilon he hs =
      parametricRunWithParameterKernel P
        (SparseCapped.fixedBitsLossProcess (by omega) c epsilon he hs (bitsOfSet S) T) T ∘ₘ
          DenseCommonNoise.noiseTableMeasure T := by
  ext E hE
  rw [fixedSetJointLaw, Measure.compProd_apply hE,
    Measure.bind_apply hE (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro Z
  rw [parametricRunWithParameterKernel_apply,
    Measure.map_apply measurable_prodMk_left hE, SparseCapped.fixedBitsRunKernel_apply]
  rfl

theorem measurable_fixedSet_deficit {d T : ℕ} (S : Finset (Fin d)) (c : ℕ) :
    Measurable (fun x : (Fin T → SparseCapped.Noise) × History d 1 T =>
      SparseCapped.deficit c (fixedTable S x.1) T x.2) := by
  have hf : Measurable (fun x : (Fin T → SparseCapped.Noise) × History d 1 T =>
      ((bitsOfSet S, x.1), x.2)) := by fun_prop
  simpa only [Function.comp_def, fixedTable] using
    (SparseCapped.measurable_deficit (d := d) (m := 1) (T := T) c T).comp hf

theorem integrable_fixedSet_deficit {d T : ℕ} (hd : 1 ≤ d)
    (S : Finset (Fin d)) (c : ℕ)
    (μ : Measure ((Fin T → SparseCapped.Noise) × History d 1 T)) [IsFiniteMeasure μ] :
    Integrable (fun x => SparseCapped.deficit c (fixedTable S x.1) T x.2) μ := by
  refine Integrable.of_mem_Icc (-((c : ℝ) * d)) T
    (measurable_fixedSet_deficit S c).aemeasurable (ae_of_all _ fun x => ?_)
  have htop := (SparseCapped.topScore_mem_Icc hd c (fixedTable S x.1) T x.2).1
  have hlearner := (SparseCapped.learnerScore_mem_Icc hd c (fixedTable S x.1) T x.2).2
  have hupper := SparseCapped.deficit_le hd c (fixedTable S x.1) T x.2
  constructor
  · unfold SparseCapped.deficit
    linarith
  · simpa using hupper

theorem fixedSet_shape_mean {d : ℕ} (P : Policy d 1) (S : Finset (Fin d))
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    (∫ x, SparseCapped.shapeSum (fixedTable S x.1) T
      ∂fixedSetJointLaw P S c T epsilon he hs) = (2 / 3 : ℝ) * T := by
  have hf : Measurable (fun Z : Fin T → SparseCapped.Noise =>
      SparseCapped.shapeSum (fixedTable S Z) T) :=
    (SparseCapped.measurable_shapeSum T).comp (measurable_const.prodMk measurable_id)
  rw [← integral_map measurable_fst.aemeasurable hf.aestronglyMeasurable,
    fixedSetJointLaw_map_noise]
  exact DenseCommonNoise.integral_shapeSum (m := 0) (fun _ => false)

/-- The indicator is integrated under its genuine history marginal. -/
theorem fixedSet_indicator_mean {d : ℕ} (P : Policy d 1) (S : Finset (Fin d))
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    (∫ x, (allInactive S c T).indicator (fun _ => (1 : ℝ)) x.2
      ∂fixedSetJointLaw P S c T epsilon he hs) =
        (historyLaw P S c T epsilon he hs).real (allInactive S c T) := by
  have hf : Measurable ((allInactive S c T).indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator (measurableSet_allInactive S c T)
  rw [← integral_map measurable_snd.aemeasurable hf.aestronglyMeasurable,
    fixedSetJointLaw_map_history]
  exact integral_indicator_one (measurableSet_allInactive S c T)

/-- No independence between the exhaustion event and the noise is required. -/
theorem fixedSet_deficit_mean {d : ℕ} (hd : 1 ≤ d) (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    (2 / 3 : ℝ) * T - (T : ℝ) *
        (historyLaw P S c T epsilon he hs).real (allInactive S c T) -
        (c : ℝ) * S.card ≤
      ∫ x, SparseCapped.deficit c (fixedTable S x.1) T x.2
        ∂fixedSetJointLaw P S c T epsilon he hs := by
  let μ := fixedSetJointLaw P S c T epsilon he hs
  let X := fun x : (Fin T → SparseCapped.Noise) × History d 1 T =>
    SparseCapped.shapeSum (fixedTable S x.1) T
  let B := fun x : (Fin T → SparseCapped.Noise) × History d 1 T =>
    (allInactive S c T).indicator (fun _ => (1 : ℝ)) x.2
  have hXi : Integrable X μ :=
    Integrable.of_mem_Icc 0 T
      ((SparseCapped.measurable_shapeSum T).comp
        (measurable_const.prodMk measurable_fst)).aemeasurable
      (ae_of_all _ fun x => SparseCapped.shapeSum_mem_Icc (fixedTable S x.1) T)
  have hBi : Integrable B μ := by
    refine Integrable.of_mem_Icc 0 1
      ((measurable_const.indicator (measurableSet_allInactive S c T)).comp
        measurable_snd).aemeasurable (ae_of_all _ fun x => ?_)
    dsimp [B, Set.indicator]
    split_ifs <;> norm_num
  calc
    _ = ∫ x, X x - (T : ℝ) * B x - (c : ℝ) * S.card ∂μ := by
      have hsub : Integrable (fun x => X x - (T : ℝ) * B x) μ :=
        hXi.sub (hBi.const_mul (T : ℝ))
      rw [integral_sub hsub (integrable_const ((c : ℝ) * S.card)),
        integral_sub hXi (hBi.const_mul (T : ℝ)), integral_const_mul]
      simp only [X, B, μ, fixedSet_shape_mean, fixedSet_indicator_mean,
        integral_const, probReal_univ, smul_eq_mul, one_mul]
    _ ≤ _ := integral_mono ((hXi.sub (hBi.const_mul _)).sub (integrable_const _))
      (integrable_fixedSet_deficit hd S c μ)
      (fun x => deficit_ge_shape_sub_allInactive hd c S x.1 x.2)

/-- Once finite averaging selects S, the actual noise/history experiment
has the required deficit tail; the event can depend on every noise draw. -/
theorem fixedSet_deficit_tail {d : ℕ} (hd : 1 ≤ d) (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (hT : 0 < T) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16)
    (hbudget : (c : ℝ) * S.card ≤ (T : ℝ) / 8)
    (hA : (historyLaw P S c T epsilon he hs).real (allInactive S c T) ≤ 1 / 4) :
    (1 : ℝ) / 8 ≤ (fixedSetJointLaw P S c T epsilon he hs).real
      {x | (T : ℝ) / 8 ≤ SparseCapped.deficit c (fixedTable S x.1) T x.2} := by
  apply MsetsPaper.Lower.deficit_tail_one_eighth _ _ (measurable_fixedSet_deficit S c)
    (integrable_fixedSet_deficit hd S c _) (by positivity)
  · have hm := fixedSet_deficit_mean hd P S c T epsilon he hs
    have hp := mul_le_mul_of_nonneg_left hA (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
    nlinarith
  · exact ae_of_all _ fun x => by
      simpa using SparseCapped.deficit_le hd c (fixedTable S x.1) T x.2

theorem exists_fixedSet_loss_process {d : ℕ} (hd : 1 ≤ d) (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (hT : 0 < T) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16)
    (hbudget : (c : ℝ) * S.card ≤ (T : ℝ) / 8)
    (hA : (historyLaw P S c T epsilon he hs).real (allInactive S c T) ≤ 1 / 4) :
    ∃ L : LossProcess d 1,
      (∀ t (h : History d 1 t) (a : MSetAction d 1),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L T).real {h | epsilon * T / 8 ≤ pathRegret L T h} := by
  let L := SparseCapped.fixedBitsLossProcess (d := d) (m := 1)
    (by omega) c epsilon he hs (bitsOfSet S) T
  let : Nonempty (MSetAction d 1) := nonempty_MSetAction hd
  have htail := fixedSet_deficit_tail hd P S c T hT epsilon he hs hbudget hA
  have hsubset : {x : (Fin T → SparseCapped.Noise) × History d 1 T |
      (T : ℝ) / 8 ≤ SparseCapped.deficit c (fixedTable S x.1) T x.2} ⊆
      parametricRegretEvent L T (epsilon * T / 8) := by
    intro x hx
    change _ ≤ parametricPathRegret L T x
    rw [show x = (x.1, x.2) from rfl, parametricPathRegret_eq_at]
    change _ ≤ pathRegret ((SparseCapped.tableLossProcess (d := d) (m := 1)
      (by omega) c epsilon he hs T).at (fixedTable S x.1)) T x.2
    rw [SparseCapped.pathRegret_eq_scaled_deficit (by omega) hd]
    simpa only [Nat.cast_one, div_one, mul_div_assoc] using
      mul_le_mul_of_nonneg_left hx he
  have hregret := htail.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono hsubset))
  rw [fixedSetJointLaw_eq_parametric] at hregret
  obtain ⟨Z, hZ⟩ := MsetsPaper.Probability.exists_fixed_parametric_regret_via_product
    hd (DenseCommonNoise.noiseTableMeasure T) P L T (epsilon * T / 8) ((1 : ℝ) / 8) hregret
  exact ⟨L.at Z, (L.at Z).action_mem_Icc, hZ⟩

/-- Finite averaging can fix the favorable set before fixing the noise. -/
theorem exists_le_of_uniformAverage_le {α : Type*} [Fintype α] [Nonempty α]
    (f : α → ℝ) {b : ℝ} (h : uniformAverage f ≤ b) : ∃ x, f x ≤ b := by
  by_contra! hnone
  have hsum : (∑ _x : α, b) < ∑ x : α, f x :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun x _ => hnone x)
  have hn : (0 : ℝ) < Fintype.card α := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  have hle := (div_le_iff₀ hn).mp h
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
  linarith

/-- The W,J construction with explicit numerical budgets. Every event bound
is derived from the finite experiment and its capped history laws. -/
theorem lower_bound_of_budgets {d k c T : ℕ} (P : Policy d 1)
    (hk0 : 1 ≤ k) (hk : k < d) (hc : 0 < c) (hT : 0 < T)
    (hcap : 4 * T ≤ c * d) (hbonus : (c : ℝ) * k ≤ (T : ℝ) / 8)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16)
    (hinfo : 128 * epsilon ^ 2 * c + Real.log 2 ≤ (3 : ℝ) / 16 * Real.log (k + 1 : ℕ)) :
    ∃ L : LossProcess d 1,
      (∀ t (h : History d 1 t) (a : MSetAction d 1),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L T).real {h | epsilon * T / 8 ≤ pathRegret L T h} := by
  let := subset_nonempty hk.le
  have hA := aProbability_le_quarter P hk0 hk hc hcap epsilon he hs hinfo
  obtain ⟨S, hS⟩ := exists_le_of_uniformAverage_le
    (fun S : WJ.Subset d k =>
      (historyLaw P S.val c T epsilon he hs).real (allInactive S.val c T)) hA
  apply exists_fixedSet_loss_process (by omega) P S.val c T hT epsilon he hs _ hS
  simpa only [S.property] using hbonus

/-- An explicit version of the sketch's asymptotic lower bound. The equalities
encode its stated simplifying assumptions that K/32 and 4T/K are integers. -/
theorem introductory_lower_bound {d k c T : ℕ} (P : Policy d 1)
    (hk : 255 ≤ k) (hd : d = 32 * k) (hc : 0 < c) (hcap : c * d = 4 * T)
    (hT : (d : ℝ) * Real.log d ≤ T) :
    ∃ L : LossProcess d 1,
      (∀ t (h : History d 1 t) (a : MSetAction d 1),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 8 ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-14 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log d) ≤ pathRegret L T h} := by
  obtain ⟨L, hL, htail⟩ := lower_bound_of_budgets P (by omega) (by omega) hc
    (horizon_pos (by omega) hd hc hcap) hcap.ge
    (cap_card_eq_time_eighth hd hcap).le (epsilonDimension d c) (epsilonDimension_nonneg d c)
    (epsilonDimension_small_of_horizon hk hd hc hcap hT)
    (epsilonDimension_information_budget hk hd hc)
  refine ⟨L, hL, htail.trans (ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_))⟩
  intro h hh
  exact (epsilonDimension_regret_threshold hk hd hc hcap).trans hh

/-- A single adaptive non-anticipating adversary is chosen before the
learner's persistent private seed is realized. -/
theorem introductory_lower_bound_private_seed
    {Ω : Type*} [MeasurableSpace Ω] {d k c T : ℕ}
    (hk : 255 ≤ k) (hd : d = 32 * k) (hc : 0 < c) (hcap : c * d = 4 * T)
    (hT : (d : ℝ) * Real.log d ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d 1 t → MSetAction d 1)
    (hchoose : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d 1,
      (∀ t (h : History d 1 t) (a : MSetAction d 1),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      (1 : ℝ) / 8 ≤ ν.real {r |
        (2 : ℝ) ^ (-14 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log d) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show 1 ≤ d by omega))
  let : Nonempty (MSetAction d 1) := ⟨a⟩
  let P := MsetsPaper.Probability.PrivateSeed.behavioralPolicy ν choose hchoose a
  obtain ⟨L, hL, htail⟩ := introductory_lower_bound P hk hd hc hcap hT
  refine ⟨L, hL, ?_⟩
  have heq : ν.real {r |
      (2 : ℝ) ^ (-14 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log d) ≤
        pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} =
      (runLaw P L T).real {h |
        (2 : ℝ) ^ (-14 : ℤ) * Real.sqrt ((d : ℝ) * T * Real.log d) ≤ pathRegret L T h} := by
    exact congrArg ENNReal.toReal (privateRun_event_probability ν choose hchoose a L T _
      (measurableSet_le measurable_const (measurable_pathRegret L T)))
  exact htail.trans_eq heq.symm

end

end MsetsPaper.Lower.WJ
