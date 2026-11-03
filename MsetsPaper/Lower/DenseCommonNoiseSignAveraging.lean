import MsetsPaper.Lower.DenseCommonNoiseMoments
import MsetsPaper.Lower.DenseCommonNoiseTesting
import MsetsPaper.Lower.DenseCommonNoiseTableBridge

/-! # Averaging the genuine independent sign prior

The conditional two-sign comparison is integrated against the fair product
measure explicitly; no conditional-bias certificate is an input to the final
specialization below.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

def flipSigns {m : ℕ} (i : Fin (2 * m)) (U : Signs m) : Signs m :=
  fun j => if j = i then !(U j) else U j

@[simp] theorem flipSigns_twice {m : ℕ} (i : Fin (2 * m)) (U : Signs m) :
    flipSigns i (flipSigns i U) = U := by
  funext j
  by_cases hj : j = i <;> simp [flipSigns, hj]

def flipSignsEquiv {m : ℕ} (i : Fin (2 * m)) : Signs m ≃ᵐ Signs m where
  toEquiv :=
    { toFun := flipSigns i
      invFun := flipSigns i
      left_inv := flipSigns_twice i
      right_inv := flipSigns_twice i }
  measurable_toFun := measurable_of_finite _
  measurable_invFun := measurable_of_finite _

theorem bitMeasure_map_not : bitMeasure.map Bool.not = bitMeasure := by
  apply Measure.ext_of_singleton
  intro b
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton _)]
  have hpre : Bool.not ⁻¹' {b} = {(!b)} := by
    ext a
    cases a <;> cases b <;> simp
  rw [hpre]
  unfold bitMeasure
  simp

theorem flipSigns_measurePreserving {m : ℕ} (i : Fin (2 * m)) :
    MeasurePreserving (flipSignsEquiv i) (signsMeasure m) (signsMeasure m) := by
  change MeasurePreserving (fun U : Signs m => fun j => if j = i then !(U j) else U j)
    (Measure.pi fun _ => bitMeasure) (Measure.pi fun _ => bitMeasure)
  apply measurePreserving_pi (fun _ => bitMeasure) (fun _ => bitMeasure)
    (f := fun j b => if j = i then !b else b)
  intro j
  by_cases hj : j = i
  · simpa only [hj, if_true] using
      (show MeasurePreserving Bool.not bitMeasure bitMeasure from
        ⟨measurable_of_finite _, bitMeasure_map_not⟩)
  · simp only [hj, if_false]
    exact ⟨measurable_id, Measure.map_id⟩

theorem sign_mixture_pairing {m : ℕ} (i : Fin (2 * m)) (f : Signs m → ℝ) :
    (∫ U, signValue (U i) * f U ∂signsMeasure m) =
      ∫ U, (f (Function.update U i true) - f (Function.update U i false)) / 2
        ∂signsMeasure m := by
  have hinv := (flipSigns_measurePreserving i).integral_comp'
    (fun U => signValue (U i) * f U)
  have hpoint (U : Signs m) :
      (signValue (U i) * f U + signValue (flipSigns i U i) * f (flipSigns i U)) / 2 =
        (f (Function.update U i true) - f (Function.update U i false)) / 2 := by
    have heq : Function.update U i (U i) = U := Function.update_eq_self i U
    have hflip : Function.update U i (!(U i)) = flipSigns i U := by
      funext j
      by_cases hj : j = i <;> simp [flipSigns, Function.update, hj]
    cases hb : U i
    · have hfalse : Function.update U i false = U := by simpa only [hb] using heq
      have htrue : Function.update U i true = flipSigns i U := by simpa only [hb, Bool.not_false] using hflip
      simp [hfalse, htrue, flipSigns, hb, signValue]
      ring
    · have htrue : Function.update U i true = U := by simpa only [hb] using heq
      have hfalse : Function.update U i false = flipSigns i U := by simpa only [hb, Bool.not_true] using hflip
      simp [hfalse, htrue, flipSigns, hb, signValue]
      ring
  calc
    _ = (∫ U, (signValue (U i) * f U +
        signValue (flipSigns i U i) * f (flipSigns i U)) / 2 ∂signsMeasure m) := by
      rw [integral_div, integral_add Integrable.of_finite Integrable.of_finite]
      change _ = (_ + (∫ U, (fun V => signValue (V i) * f V) (flipSignsEquiv i U)
        ∂signsMeasure m)) / 2
      rw [hinv]
      ring
    _ = _ := integral_congr_ae (ae_of_all _ hpoint)

theorem sign_mixture_le_of_pair_bound {m : ℕ} (i : Fin (2 * m)) (f : Signs m → ℝ)
    {B : ℝ} (hpair : ∀ U, (f (Function.update U i true) - f (Function.update U i false)) / 2 ≤ B) :
    (∫ U, signValue (U i) * f U ∂signsMeasure m) ≤ B := by
  rw [sign_mixture_pairing]
  calc
    _ ≤ ∫ _U : Signs m, B ∂signsMeasure m :=
      integral_mono Integrable.of_finite Integrable.of_finite hpair
    _ = B := by simp

theorem signVector_update {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Signs m) (i : Fin (2 * m)) (b : Bool) :
    signVector (d := d) (Function.update U i b) =
      Function.update (signVector U) (Fin.castLE h2m i) (signValue b) := by
  funext j
  by_cases hji : j = Fin.castLE h2m i
  · subst j
    simp [signVector, i.isLt]
  · have hval : j.val ≠ i.val := by
      intro heq
      exact hji (Fin.ext heq)
    by_cases hj : j.val < 2 * m
    · have hne : (⟨j.val, hj⟩ : Fin (2 * m)) ≠ i := by
        intro heq
        exact hval (congrArg Fin.val heq)
      simp [signVector, hj, Function.update, hji, hne]
    · simp [signVector, hj, Function.update, hji]

/-- Expected number of selections under the original finite-table experiment
with signs fixed. This definition uses the actual randomized-policy run law. -/
def expectedSelections {d m : ℕ} (P : Policy d m) (hm : 0 < m)
    (eta : ℝ) (heta : 0 ≤ eta) (hs : eta ≤ 1 / 16)
    (U : Signs m) (T : ℕ) (i : Fin d) : ℝ :=
  ∫ h, History.selectedCount i T h ∂noiseMixture P hm eta heta hs U T

/-- The actual sign prior, including all the other signs, preserves the
`T/16` bias bound. Learner randomization is already integrated in the policy
kernels; no sign or seed has been fixed after observing the learner's run. -/
theorem integral_sign_expectedSelections_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T)
    (i : Fin (2 * m)) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (∫ U : Signs m, signValue (U i) *
      expectedSelections P hm (eta m T) he hs U T (Fin.castLE h2m i) ∂signsMeasure m) ≤
      (T : ℝ) / 16 := by
  dsimp only
  apply sign_mixture_le_of_pair_bound
  intro U
  have h := observable_flip_count_bias_le P hm h2m hT
    (signVector U) (abs_signVector_le U) (Fin.castLE h2m i)
  dsimp only at h
  have hle := (le_abs_self _).trans h
  unfold expectedSelections
  rw [noiseMixture_eq_observableProcess, noiseMixture_eq_observableProcess]
  simpa [signVector_update h2m, signValue] using hle

theorem actionLoss_signVector_eq_sum_signs {d m : ℕ} (h2m : 2 * m ≤ d)
    (U : Signs m) (a : MSetAction d m) :
    actionLoss a (signVector U) =
      ∑ i : Fin (2 * m), signValue (U i) * History.selectedIndicator (Fin.castLE h2m i) a := by
  classical
  unfold actionLoss
  symm
  apply Fintype.sum_of_injective (Fin.castLE h2m)
    (fun i j hij => Fin.ext (congrArg (fun k : Fin d => k.val) hij))
  · intro j hj
    have hnot : ¬ j.val < 2 * m := by
      intro hlt
      exact hj ⟨⟨j.val, hlt⟩, Fin.ext rfl⟩
    simp [signVector, hnot]
  · intro i
    simp only [signVector, Fin.val_castLE, dif_pos i.isLt]
    by_cases hi : Fin.castLE h2m i ∈ a.val <;> simp [History.selectedIndicator, hi]

/-- The observable action-sign sum is exactly the signed sum of selection
counts. Coordinates beyond `2m` contribute zero, as stated in the paper. -/
theorem actionSum_eq_signedCounts {d m : ℕ} (h2m : 2 * m ≤ d) (U : Signs m) :
    ∀ T : ℕ, ∀ h : History d m T,
      History.actionSum (fun a => actionLoss a (signVector U)) T h =
        ∑ i : Fin (2 * m), signValue (U i) * History.selectedCount (Fin.castLE h2m i) T h := by
  intro T
  induction T with
  | zero => intro h; simp [History.actionSum, History.selectedCount]
  | succ T ih =>
      intro h
      rw [History.actionSum_succ, ih h.1, actionLoss_signVector_eq_sum_signs h2m U h.2.1]
      simp only [History.selectedCount, History.actionSum_succ, mul_add, Finset.sum_add_distrib]

theorem two_thirds_integral_signedCount_le {d m T : ℕ}
    (P : Policy d m) (hm : 0 < m) (h2m : 2 * m ≤ d) (hT : d ^ 2 ≤ T) :
    let ht : 0 < T := lt_of_lt_of_le (pow_pos (by omega : 0 < d) 2) hT
    let he := (eta_pos hm ht).le
    let hs := (eta_le_one_div_256 hm h2m hT).trans (by norm_num : (1:ℝ)/256 ≤ 1/16)
    (2 / 3 : ℝ) * (∫ U : Signs m, ∑ i : Fin (2 * m), signValue (U i) *
      expectedSelections P hm (eta m T) he hs U T (Fin.castLE h2m i) ∂signsMeasure m) ≤
      (m : ℝ) * T / 12 := by
  dsimp only
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  calc
    _ ≤ (2 / 3 : ℝ) * ∑ _i : Fin (2 * m), ((T : ℝ) / 16) :=
      mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i _ => integral_sign_expectedSelections_le P hm h2m hT i)
        (by norm_num)
    _ = _ := by simp; ring

end

end MsetsPaper.Lower.DenseCommonNoise
