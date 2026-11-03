import CoefficientOne.Sampling.ExactSampler
import CoefficientOne.Sampling.IndexedDummyLift
import CoefficientOne.Sampling.CardinalityCorrection

/-!
# The concrete at-most sampler

The only theorem input for the transfer is interior stretch in dimension n+k.
The construction itself includes the Borel correction, and its cardinality
guarantee holds for every seed. No maximum-entropy claim is made for this output.
-/

open scoped BigOperators
open MeasureTheory EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ} [NeZero n]

local instance : NeZero (n + k) := ⟨by have h := NeZero.ne n; omega⟩

def atMostRawSampler (n k : ℕ) [NeZero n] (x : atMostHypersimplex (Fin n) k)
    (ω : Seed (n + k)) : Finset (Fin n) :=
  realOutput (exactSampler (n + k) k (liftedExactInput x) ω)

def atMostSampler (n k : ℕ) [NeZero n] (x : atMostHypersimplex (Fin n) k)
    (ω : Seed (n + k)) : Finset (Fin n) :=
  cardinalityCorrect n (coordinateSum x.val) (atMostRawSampler n k x ω)

theorem measurable_atMostRawSampler :
    Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) => atMostRawSampler n k z.1 z.2) := by
  have hx : Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) => liftedExactInput z.1) :=
    fun s hs => measurable_fst (continuous_liftedExactInput.measurable hs)
  have hp : Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) =>
      (liftedExactInput z.1, z.2)) := hx.prodMk measurable_snd
  have hfull : Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) =>
      exactSampler (n + k) k (liftedExactInput z.1) z.2) :=
    fun s hs => hp (measurable_exactSampler (by omega : k ≤ n + k) hs)
  exact fun s hs => hfull ((measurable_of_finite (realOutput (n := n) (k := k))) hs)

theorem measurable_atMostRawSampler_fixed (x : atMostHypersimplex (Fin n) k) :
    Measurable (atMostRawSampler n k x) := by
  have hp : Measurable (fun ω : Seed (n + k) => (x, ω)) := measurable_const.prodMk measurable_id
  exact fun s hs => hp (measurable_atMostRawSampler hs)

theorem continuous_coordinateSum {ι : Type*} [Fintype ι] :
    Continuous (coordinateSum : (ι → ℝ) → ℝ) := by
  unfold coordinateSum
  fun_prop

theorem measurable_atMostSampler :
    Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) => atMostSampler n k z.1 z.2) := by
  have hs : Measurable (fun z : atMostHypersimplex (Fin n) k × Seed (n + k) => coordinateSum z.1.val) :=
    continuous_coordinateSum.measurable.comp (measurable_subtype_coe.comp measurable_fst)
  exact measurable_cardinalityCorrect hs measurable_atMostRawSampler

theorem measurable_atMostSampler_fixed (x : atMostHypersimplex (Fin n) k) :
    Measurable (atMostSampler n k x) := by
  have hp : Measurable (fun ω : Seed (n + k) => (x, ω)) := measurable_const.prodMk measurable_id
  exact fun s hs => hp (measurable_atMostSampler hs)

theorem coordinateSum_le_card (x : atMostHypersimplex (Fin n) k) : coordinateSum x.val ≤ n := by
  have h : ∑ i, x.val i ≤ ∑ _ : Fin n, (1 : ℝ) := Finset.sum_le_sum fun i _ => (x.property.1 i).2
  simpa [coordinateSum] using h

theorem atMostSampler_card (x : atMostHypersimplex (Fin n) k) (ω : Seed (n + k)) :
    (atMostSampler n k x ω).card = ⌊coordinateSum x.val⌋₊ ∨
      (atMostSampler n k x ω).card = ⌈coordinateSum x.val⌉₊ :=
  cardinalityCorrect_card (coordinateSum_nonneg x.property) (coordinateSum_le_card x) _

theorem atMostSampler_card_le (x : atMostHypersimplex (Fin n) k) (ω : Seed (n + k)) :
    (atMostSampler n k x ω).card ≤ k := by
  have hfloor : ⌊coordinateSum x.val⌋₊ ≤ k := (Nat.cast_le (α := ℝ)).mp
    ((Nat.floor_le (coordinateSum_nonneg x.property)).trans x.property.2)
  have hceil : ⌈coordinateSum x.val⌉₊ ≤ k := Nat.ceil_le.mpr x.property.2
  rcases atMostSampler_card x ω with h | h <;> omega

@[simp] theorem atMostSampler_zero (x : atMostHypersimplex (Fin n) 0) (ω : Seed (n + 0)) :
    atMostSampler n 0 x ω = ∅ :=
  Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero (atMostSampler_card_le x ω))

theorem atMostRawSampler_marginal_of_interior_stretch
    (hinterior : 1 ≤ k → k < n + k → InteriorStretchSix (n + k) k)
    (x : atMostHypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (atMostRawSampler n k x ω) ∂seedMeasure (n + k)) = x.val i := by
  simp only [atMostRawSampler, indicator_realOutput]
  rw [exactSampler_marginal_of_interior_stretch (by omega : k ≤ n + k) hinterior]
  exact indexedDummyLift_real x.val i

theorem atMostRawSampler_card_ae_of_interior_stretch
    (hinterior : 1 ≤ k → k < n + k → InteriorStretchSix (n + k) k)
    (x : atMostHypersimplex (Fin n) k) :
    ∀ᵐ ω ∂seedMeasure (n + k), (atMostRawSampler n k x ω).card = ⌊coordinateSum x.val⌋₊ ∨
      (atMostRawSampler n k x ω).card = ⌈coordinateSum x.val⌉₊ := by
  let F : Seed (n + k) → Finset (Fin n ⊕ Fin k) :=
    fun ω => splitLiftedOutput (exactSampler (n + k) k (liftedExactInput x) ω)
  have hF : Measurable F := (measurable_of_finite splitLiftedOutput).comp
    (measurable_exactSampler_fixed (by omega : k ≤ n + k) (liftedExactInput x))
  apply liftedSampler_cardinality_ae (seedMeasure (n + k)) (coordinateSum_nonneg x.property) x.property.2 F hF
  · intro ω
    change (splitLiftedOutput (exactSampler (n + k) k (liftedExactInput x) ω)).card = k
    rw [splitLiftedOutput_card, exactSampler_card (by omega : k ≤ n + k)]
  · intro j
    simp only [F, indicator_splitLiftedOutput]
    rw [exactSampler_marginal_of_interior_stretch (by omega : k ≤ n + k) hinterior]
    exact indexedDummyLift_dummy x.val j

theorem atMostSampler_marginal_of_interior_stretch
    (hinterior : 1 ≤ k → k < n + k → InteriorStretchSix (n + k) k)
    (x : atMostHypersimplex (Fin n) k) (i : Fin n) :
    (∫ ω, indicator i (atMostSampler n k x ω) ∂seedMeasure (n + k)) = x.val i := by
  rw [show (∫ ω, indicator i (atMostSampler n k x ω) ∂seedMeasure (n + k)) =
      ∫ ω, indicator i (atMostRawSampler n k x ω) ∂seedMeasure (n + k) from
    cardinalityCorrect_integral (seedMeasure (n + k)) (fun _ => coordinateSum x.val)
      (atMostRawSampler n k x) (atMostRawSampler_card_ae_of_interior_stretch hinterior x) (indicator i)]
  exact atMostRawSampler_marginal_of_interior_stretch hinterior x i

theorem atMostSampler_probability_of_interior_stretch
    (hinterior : 1 ≤ k → k < n + k → InteriorStretchSix (n + k) k)
    (x : atMostHypersimplex (Fin n) k) (i : Fin n) :
    (seedMeasure (n + k)) {ω | i ∈ atMostSampler n k x ω} = ENNReal.ofReal (x.val i) :=
  probability_member_eq_of_integral (seedMeasure (n + k)) (measurable_atMostSampler_fixed x) i
    (atMostSampler_marginal_of_interior_stretch hinterior x i)

theorem atMostRawSampler_stretch_of_interior_stretch
    (hinterior : 1 ≤ k → k < n + k → InteriorStretchSix (n + k) k)
    (x y : atMostHypersimplex (Fin n) k) :
    expectedOutputDistance (seedMeasure (n + k)) (atMostRawSampler n k x) (atMostRawSampler n k y) ≤
      12 * vectorL1 (fun i => x.val i - y.val i) := by
  have hx := measurable_exactSampler_fixed (by omega : k ≤ n + k) (liftedExactInput x)
  have hy := measurable_exactSampler_fixed (by omega : k ≤ n + k) (liftedExactInput y)
  calc
    _ ≤ expectedOutputDistance (seedMeasure (n + k))
        (exactSampler (n + k) k (liftedExactInput x)) (exactSampler (n + k) k (liftedExactInput y)) := by
      exact integral_mono
        (integrable_outputDistance _ (measurable_atMostRawSampler_fixed x) (measurable_atMostRawSampler_fixed y))
        (integrable_outputDistance _ hx hy) (fun ω => realOutput_distance_le _ _)
    _ ≤ 6 * vectorL1 (fun i => (liftedExactInput x).val i - (liftedExactInput y).val i) :=
      exactSampler_stretch_of_interior_stretch (by omega) hinterior _ _
    _ ≤ 6 * (2 * vectorL1 (fun i => x.val i - y.val i)) :=
      mul_le_mul_of_nonneg_left (indexedDummyLift_l1 x.property y.property) (by norm_num)
    _ = _ := by ring

theorem atMostSampler_stretch_of_interior_stretch
    (hinterior : 1 ≤ k → k < n + k → InteriorStretchSix (n + k) k)
    (x y : atMostHypersimplex (Fin n) k) :
    expectedOutputDistance (seedMeasure (n + k)) (atMostSampler n k x) (atMostSampler n k y) ≤
      12 * vectorL1 (fun i => x.val i - y.val i) := by
  have he := cardinalityCorrect_expectedDistance (seedMeasure (n + k))
    (fun _ => coordinateSum x.val) (fun _ => coordinateSum y.val)
    (atMostRawSampler n k x) (atMostRawSampler n k y)
    (atMostRawSampler_card_ae_of_interior_stretch hinterior x)
    (atMostRawSampler_card_ae_of_interior_stretch hinterior y)
  change expectedOutputDistance (seedMeasure (n + k)) (atMostSampler n k x) (atMostSampler n k y) = _ at he
  rw [he]
  exact atMostRawSampler_stretch_of_interior_stretch hinterior x y

end
end CoefficientOne.Sampling
