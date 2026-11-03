import MsetsPaper.Lower.WJCombinatorics
import MsetsPaper.Lower.WJRegret

/-! # Finite W,J averaging of the actual history test

P is averaged over a uniform k-set S and a uniform point outside S. The
erase/insert equivalence identifies this law with the paper's uniform
marked (k+1)-set experiment. Q uses all of W as the favorable set.
-/

namespace MsetsPaper.Lower.WJ

open MsetsLower MsetsLower.History MsetsPaper.Probability
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def aProbability {d : ℕ} (P : Policy d 1) (k c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) : ℝ :=
  uniformAverage fun S : WJ.Subset d k =>
    (historyLaw P S.val c T epsilon he hs).real (allInactive S.val c T)

def pProbability {d : ℕ} (P : Policy d 1) (k c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) : ℝ :=
  uniformAverage fun x : Exterior d k => pSection P x.1.val x.2.val c T epsilon he hs

def qProbability {d : ℕ} (P : Policy d 1) (k c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) : ℝ :=
  uniformAverage fun x : Exterior d k => qSection P x.1.val x.2.val c T epsilon he hs

/-- The P event average is literally the paper's uniform marked-set experiment. -/
theorem pProbability_eq_marked {d : ℕ} (P : Policy d 1) (k c T : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    pProbability P k c T epsilon he hs =
      uniformAverage (fun x : Marked d k =>
        pSection P (x.1.val.erase x.2.val) x.2.val c T epsilon he hs) := by
  rw [marked_average_eq_exterior]
  unfold pProbability
  apply congrArg uniformAverage
  funext x
  change pSection P x.1.val x.2.val c T epsilon he hs =
    pSection P ((insert x.2.val x.1.val).erase x.2.val) x.2.val c T epsilon he hs
  rw [Finset.erase_insert x.2.property]

/-- Erasing the mark also gives the uniform favorable-set law for A. -/
theorem aProbability_eq_marked {d k : ℕ} (P : Policy d 1) (hk : k < d) (c T : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    aProbability P k c T epsilon he hs =
      uniformAverage (fun x : Marked d k =>
        (historyLaw P (x.1.val.erase x.2.val) c T epsilon he hs).real
          (allInactive (x.1.val.erase x.2.val) c T)) := by
  rw [marked_average_eq_exterior, exterior_average_fibers]
  unfold aProbability
  apply congrArg uniformAverage
  funext S
  have hn : ((d - k : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.sub_pos_of_lt hk).ne'
  change (historyLaw P S.val c T epsilon he hs).real (allInactive S.val c T) =
    (∑ j : {j : Fin d // j ∉ S.val},
      (historyLaw P ((insert j.val S.val).erase j.val) c T epsilon he hs).real
        (allInactive ((insert j.val S.val).erase j.val) c T)) / (d - k : ℕ)
  have hj (j : {j : Fin d // j ∉ S.val}) : (insert j.val S.val).erase j.val = S.val :=
    Finset.erase_insert j.property
  simp_rw [hj]
  simp [card_exterior_fiber, hn]

theorem binaryKL_uniformAverage {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) (hc : ∀ i, BinaryCompatible (p i) (q i)) :
    binaryKL (uniformAverage p) (uniformAverage q) ≤
      uniformAverage (fun i => binaryKL (p i) (q i)) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hw : (∑ _i : ι, (1 : ℝ) / Fintype.card ι) = 1 := by simp [hn]
  have h := binaryKL_finite_mixture (fun _ : ι => (1 : ℝ) / Fintype.card ι)
    p q (fun _ => by positivity) hw hp hq hc
  have hwf (f : ι → ℝ) : (∑ i, (1 : ℝ) / Fintype.card ι * f i) = uniformAverage f := by
    unfold uniformAverage
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hwf] using h

theorem compatible_uniformAverage {ι : Type*} [Fintype ι] [Nonempty ι]
    (p q : ι → ℝ) (hp : ∀ i, p i ∈ Icc (0 : ℝ) 1)
    (hq : ∀ i, q i ∈ Icc (0 : ℝ) 1) (hc : ∀ i, BinaryCompatible (p i) (q i)) :
    BinaryCompatible (uniformAverage p) (uniformAverage q) := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance).ne'
  have hw : (∑ _i : ι, (1 : ℝ) / Fintype.card ι) = 1 := by simp [hn]
  have h := BinaryCompatible_finite_mixture (fun _ : ι => (1 : ℝ) / Fintype.card ι)
    p q (fun _ => by positivity) hw hp hq hc
  have hwf (f : ι → ℝ) : (∑ i, (1 : ℝ) / Fintype.card ι * f i) = uniformAverage f := by
    unfold uniformAverage
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simpa only [hwf] using h

theorem probabilities_mem_Icc {d : ℕ} (P : Policy d 1) {k : ℕ} (hk : k < d)
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    aProbability P k c T epsilon he hs ∈ Icc (0 : ℝ) 1 ∧
    pProbability P k c T epsilon he hs ∈ Icc (0 : ℝ) 1 ∧
    qProbability P k c T epsilon he hs ∈ Icc (0 : ℝ) 1 := by
  letI := nonempty_MSetAction hk.le
  letI := exterior_nonempty hk
  refine ⟨?_, ?_, ?_⟩
  · apply uniformAverage_mem_Icc
    intro S
    exact ⟨measureReal_nonneg, measureReal_le_one⟩
  · exact uniformAverage_mem_Icc fun x => pSection_mem_Icc P x.1.val x.2.val c T epsilon he hs
  · exact uniformAverage_mem_Icc fun x => qSection_mem_Icc P x.1.val x.2.val c T epsilon he hs

theorem probabilities_compatible {d : ℕ} (P : Policy d 1) {k : ℕ} (hk : k < d)
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    BinaryCompatible (pProbability P k c T epsilon he hs)
      (qProbability P k c T epsilon he hs) := by
  letI := exterior_nonempty hk
  exact compatible_uniformAverage _ _
    (fun x => pSection_mem_Icc P x.1.val x.2.val c T epsilon he hs)
    (fun x => qSection_mem_Icc P x.1.val x.2.val c T epsilon he hs)
    (fun x => section_compatible (by omega) P x.1.val x.2.val x.2.property c T epsilon he hs)

/-- The finite averaging has the same capped information budget as each section. -/
theorem probabilities_binaryKL_le {d : ℕ} (P : Policy d 1) {k : ℕ} (hk : k < d)
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    binaryKL (pProbability P k c T epsilon he hs)
      (qProbability P k c T epsilon he hs) ≤ 128 * epsilon ^ 2 * c := by
  letI := exterior_nonempty hk
  apply (binaryKL_uniformAverage (ι := Exterior d k)
    (fun x => pSection P x.1.val x.2.val c T epsilon he hs)
    (fun x => qSection P x.1.val x.2.val c T epsilon he hs)
    (fun x => pSection_mem_Icc P x.1.val x.2.val c T epsilon he hs)
    (fun x => qSection_mem_Icc P x.1.val x.2.val c T epsilon he hs)
    (fun x => section_compatible (by omega) P x.1.val x.2.val x.2.property c T epsilon he hs)).trans
  calc
    _ ≤ uniformAverage (fun _ : Exterior d k => 128 * epsilon ^ 2 * c) :=
      uniformAverage_mono fun x =>
        section_binaryKL_le (by omega) P x.1.val x.2.val x.2.property c T epsilon he hs
    _ = _ := uniformAverage_const _

theorem allInactive_iff_disjoint {d : ℕ} (S : Finset (Fin d)) (c T : ℕ)
    (h : History d 1 T) :
    h ∈ allInactive S c T ↔ Disjoint S (SparseCapped.historyActiveItems c T h) := by
  simp only [allInactive, Set.mem_ofPred_eq, Finset.disjoint_left]
  constructor
  · intro hS i hi ha
    have hl : SparseCapped.historyNatCount i T h < c := by
      simpa [SparseCapped.historyActiveItems] using ha
    have hlR : selectedCount i T h < (c : ℝ) := by
      rw [← SparseCapped.cast_historyNatCount]
      exact_mod_cast hl
    exact (not_lt_of_ge (hS i hi)) hlR
  · intro hS i hi
    by_contra hn
    have hlR : selectedCount i T h < (c : ℝ) := lt_of_not_ge hn
    have hl : SparseCapped.historyNatCount i T h < c := by
      rw [← SparseCapped.cast_historyNatCount] at hlR
      exact_mod_cast hlR
    exact hS hi (by simp [SparseCapped.historyActiveItems, hl])

theorem testEvent_iff_count {d : ℕ} (S : Finset (Fin d)) (j : Fin d) (c T : ℕ)
    (h : History d 1 T) : h ∈ testEvent S j c T ↔
      Disjoint S (SparseCapped.historyActiveItems c T h) ∧
        j ∈ SparseCapped.historyActiveItems c T h := by
  simp only [testEvent, mem_inter_iff, allInactive_iff_disjoint, Set.mem_ofPred_eq]
  congr 1
  simp [SparseCapped.historyActiveItems, ← SparseCapped.cast_historyNatCount]

theorem integrable_uniformAverage {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    Integrable (fun x => uniformAverage (fun i => f i x)) μ := by
  exact (integrable_finsetSum _ (fun i _ => hf i)).div_const _

theorem uniformAverage_integral {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : Measure Ω) (f : ι → Ω → ℝ) (hf : ∀ i, Integrable (f i) μ) :
    uniformAverage (fun i => ∫ x, f i x ∂μ) =
      ∫ x, uniformAverage (fun i => f i x) ∂μ := by
  unfold uniformAverage
  rw [integral_div, integral_finsetSum _ (fun i _ => hf i)]

/-- The conditional P inequality follows from counting active arms in each
history before integrating that history. -/
theorem pSection_average_ge {d k c T : ℕ} (P : Policy d 1)
    (hk : k < d) (hc : 0 < c) (hbudget : 4 * T ≤ c * d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) (S : WJ.Subset d k) :
    (3 : ℝ) / 4 * (historyLaw P S.val c T epsilon he hs).real (allInactive S.val c T) ≤
      uniformAverage (fun j : {j : Fin d // j ∉ S.val} =>
        pSection P S.val j.val c T epsilon he hs) := by
  classical
  let μ := historyLaw P S.val c T epsilon he hs
  let f := fun (j : {j : Fin d // j ∉ S.val}) =>
    (testEvent S.val j.val c T).indicator (fun _ => (1 : ℝ))
  have hf (j : {j : Fin d // j ∉ S.val}) : Integrable (f j) μ :=
    (integrable_const _).indicator (measurableSet_testEvent S.val j.val c T)
  have hpoint (h : History d 1 T) :
      (3 : ℝ) / 4 * (allInactive S.val c T).indicator (fun _ => (1 : ℝ)) h ≤
        uniformAverage (fun j => f j h) := by
    have hactive := historyActive_card_three_quarters (by omega) hc hbudget h
    have hn : 3 * d ≤ 4 * (SparseCapped.historyActiveItems c T h).card := by
      have hr : (3 : ℝ) * d ≤ 4 * (SparseCapped.historyActiveItems c T h).card := by linarith
      exact_mod_cast hr
    have hcount := exterior_joint_event_average_ge hk S
      (SparseCapped.historyActiveItems c T h) hn
    simpa only [f, Set.indicator, allInactive_iff_disjoint, testEvent_iff_count] using hcount
  calc
    _ = ∫ h, (3 : ℝ) / 4 * (allInactive S.val c T).indicator (fun _ => (1 : ℝ)) h ∂μ := by
      rw [integral_const_mul]
      congr 1
      exact (integral_indicator_one (measurableSet_allInactive S.val c T)).symm
    _ ≤ ∫ h, uniformAverage (fun j => f j h) ∂μ :=
      integral_mono (((integrable_const _).indicator
        (measurableSet_allInactive S.val c T)).const_mul _) (integrable_uniformAverage μ f hf) hpoint
    _ = _ := by
      rw [← uniformAverage_integral μ f hf]
      congr 1
      funext j
      exact integral_indicator_one (measurableSet_testEvent S.val j.val c T)

theorem pProbability_ge {d k c T : ℕ} (P : Policy d 1)
    (hk : k < d) (hc : 0 < c) (hbudget : 4 * T ≤ c * d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    (3 : ℝ) / 4 * aProbability P k c T epsilon he hs ≤
      pProbability P k c T epsilon he hs := by
  unfold pProbability
  rw [exterior_average_fibers]
  unfold aProbability
  rw [← uniformAverage_const_mul]
  apply uniformAverage_mono
  intro S
  simpa only [uniformAverage, card_exterior_fiber] using
    pSection_average_ge P hk hc hbudget epsilon he hs S

theorem qSection_average_le {d k c T : ℕ} (P : Policy d 1)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16)
    (W : WJ.Subset d (k + 1)) :
    uniformAverage (fun j : {j : Fin d // j ∈ W.val} =>
      (historyLaw P W.val c T epsilon he hs).real (testEvent (W.val.erase j.val) j.val c T)) ≤
        1 / (k + 1 : ℕ) := by
  classical
  let μ := historyLaw P W.val c T epsilon he hs
  let f := fun (j : {j : Fin d // j ∈ W.val}) =>
    (testEvent (W.val.erase j.val) j.val c T).indicator (fun _ => (1 : ℝ))
  have hf (j : {j : Fin d // j ∈ W.val}) : Integrable (f j) μ :=
    (integrable_const _).indicator (measurableSet_testEvent (W.val.erase j.val) j.val c T)
  have hpoint (h : History d 1 T) : uniformAverage (fun j => f j h) ≤ 1 / (k + 1 : ℕ) := by
    simpa only [f, Set.indicator, testEvent_iff_count] using
      marked_event_average_le W (SparseCapped.historyActiveItems c T h)
  calc
    _ = uniformAverage (fun j => ∫ h, f j h ∂μ) := by
      congr 1
      funext j
      exact (integral_indicator_one (measurableSet_testEvent (W.val.erase j.val) j.val c T)).symm
    _ = ∫ h, uniformAverage (fun j => f j h) ∂μ := uniformAverage_integral μ f hf
    _ ≤ ∫ _h, (1 : ℝ) / (k + 1 : ℕ) ∂μ :=
      integral_mono (integrable_uniformAverage μ f hf) (integrable_const _) hpoint
    _ = _ := by simp [μ]

/-- Erase/insert reindexing makes Q's history law independent of the mark J. -/
theorem qProbability_le {d k c T : ℕ} (P : Policy d 1) (hk : k < d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    qProbability P k c T epsilon he hs ≤ 1 / (k + 1 : ℕ) := by
  letI := nonempty_MSetAction (Nat.succ_le_iff.mpr hk)
  let f : Marked d k → ℝ := fun x =>
    (historyLaw P x.1.val c T epsilon he hs).real
      (testEvent (x.1.val.erase x.2.val) x.2.val c T)
  have heq : uniformAverage f = qProbability P k c T epsilon he hs := by
    rw [marked_average_eq_exterior]
    unfold qProbability
    congr 1
    funext x
    simp [f, Function.comp_def, exteriorToMarked, qSection, Finset.erase_insert x.2.property]
  rw [← heq, marked_average_fibers]
  calc
    _ ≤ uniformAverage (fun _ : WJ.Subset d (k + 1) => (1 : ℝ) / (k + 1 : ℕ)) := by
      apply uniformAverage_mono
      intro W
      simpa only [uniformAverage, card_marked_fiber, f] using
        qSection_average_le P epsilon he hs W
    _ = _ := uniformAverage_const _

/-- A fully explicit version of the introductory binary-KL calculation. -/
theorem aProbability_le_quarter {d k c T : ℕ} (P : Policy d 1)
    (hk0 : 1 ≤ k) (hk : k < d) (hc : 0 < c) (hbudget : 4 * T ≤ c * d)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16)
    (hinfo : 128 * epsilon ^ 2 * c + Real.log 2 ≤ (3 : ℝ) / 16 * Real.log (k + 1 : ℕ)) :
    aProbability P k c T epsilon he hs ≤ 1 / 4 := by
  have hmem := probabilities_mem_Icc P hk c T epsilon he hs
  have hcompat := probabilities_compatible P hk c T epsilon he hs
  have hp := pProbability_ge P hk hc hbudget epsilon he hs
  have hq := qProbability_le (c := c) (T := T) P hk epsilon he hs
  have hkl := probabilities_binaryKL_le P hk c T epsilon he hs
  have hn : (1 : ℝ) < (k + 1 : ℕ) := by exact_mod_cast (by omega : 1 < k + 1)
  have hlog : 0 < Real.log (k + 1 : ℕ) := Real.log_pos hn
  by_cases hz : qProbability P k c T epsilon he hs = 0
  · rw [hcompat.1 hz] at hp
    linarith
  have hq0 : 0 < qProbability P k c T epsilon he hs :=
    lt_of_le_of_ne hmem.2.2.1 (Ne.symm hz)
  have hq1 : qProbability P k c T epsilon he hs < 1 := by
    exact hq.trans_lt ((div_lt_one (by linarith)).mpr hn)
  have hlower := binaryKL_lower_bound hmem.2.1.1 hmem.2.1.2 hq0 hq1
  have hinv : (k + 1 : ℕ) ≤ 1 / qProbability P k c T epsilon he hs := by
    apply (le_div_iff₀ hq0).mpr
    simpa only [mul_comm] using
      (le_div_iff₀ (by linarith : (0 : ℝ) < (k + 1 : ℕ))).mp hq
  have hlog' := Real.log_le_log (by linarith : (0 : ℝ) < (k + 1 : ℕ)) hinv
  have hscale := mul_le_mul_of_nonneg_left hlog' hmem.2.1.1
  have hscale' := mul_le_mul_of_nonneg_right hp hlog.le
  nlinarith

end

end MsetsPaper.Lower.WJ
