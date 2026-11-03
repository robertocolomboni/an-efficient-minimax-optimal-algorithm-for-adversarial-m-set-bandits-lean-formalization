import MsetsPaper.Lower.PrivateSeedEndpoints
import MsetsPaper.Lower.FeedbackSmooth
import MsetsPaper.Lower.FeedbackManuscriptDerivative
import MsetsPaper.Lower.ConfidenceObliviousFineSteps

/-!
# Lower statements and assembly of the definitive manuscript

Source: `paper/main.tex`, matching lower-bound statements and proof.

The P2/P3/P4 interfaces expose action-loss bounds while preserving the stronger
itemwise construction results. The assembly below follows the paper's proof order:
first prove the entire half-range case, then complement at the end. This is
distinct from the preserved `NewRoute.lower_bound_semantic`, which reduces
to the minimum action size before splitting the logarithmic terms.

`LossProcess` is a measurable deterministic function of the previous public
history, with all action losses in [0,1]. The private-seed endpoint explicitly
selects one adversary before quantifying the learner's seed realization.
-/

namespace MsetsPaper.Alignment.LowerDefinitive

open MsetsLower MsetsLower.Lower MsetsLower.Feedback
open MsetsPaper.Lower MsetsPaper.Probability
open MsetsPaper.Probability.PrivateSeed MeasureTheory Set
open scoped ENNReal

noncomputable section

/-- L10: fix only the independent adversary seed, after averaging the
learner's seed. The restrictions on b and p are precisely the paper's. -/
theorem lemma_lower_fixing_table
    {Ξ R : Type*} [MeasurableSpace Ξ] [MeasurableSpace R]
    (μ : Measure Ξ) (ν : Measure R)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (regret : Ξ × R → ℝ) (hregret : Measurable regret)
    {b p : ℝ} (_hb : 0 ≤ b) (_hp : p ∈ Icc (0 : ℝ) 1)
    (htail : p ≤ (μ.prod ν).real {ω | b ≤ regret ω}) :
    ∃ ξ, p ≤ ν.real {r | b ≤ regret (ξ, r)} :=
  exists_fixed_adversary_seed μ ν regret hregret htail

/-- L11 in its definitive direction m -> d-m, with the action-loss
normalization exposed in both premise and conclusion. -/
theorem lemma_lower_complement {d m T : ℕ}
    (_hd : 2 ≤ d) (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (_hT : 1 ≤ T)
    {c₀ δ₀ : ℝ} (_hc : 0 ≤ c₀) (_hδ : δ₀ ∈ Icc (0 : ℝ) 1)
    (h : ∀ P : Policy d m, ∃ L : LossProcess d m,
      (∀ t (history : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t history) ∈ Icc (0 : ℝ) 1) ∧
      δ₀ ≤ (runLaw P L T).real {history | c₀ ≤ pathRegret L T history}) :
    ∀ P : Policy d (d - m), ∃ L : LossProcess d (d - m),
      (∀ t (history : History d (d - m) t) (a : MSetAction d (d - m)),
        actionLoss a (L.itemLoss t history) ∈ Icc (0 : ℝ) 1) ∧
      δ₀ ≤ (runLaw P L T).real {history | c₀ ≤ pathRegret L T history} := by
  intro P
  have hmd : m ≤ d := by omega
  exact NewRoute.real_tail_of_semantic (Nat.sub_le d m) P
    (lower_tail_for_complementary_size (Nat.sub_le d m) hmd (by omega) rfl
      (fun Q ↦ by
        obtain ⟨G, _hG, htail⟩ := h Q
        exact NewRoute.tail_of_real hmd Q G htail) P)

/-- L12: the increasing smooth interval bijection, the actual push-forward
density, and the definitive coefficient 80 are one combined interface. -/
theorem lemma_lower_feedback_density {u : ℝ} (hu : |u| ≤ 1 / 16) :
    StrictMonoOn (feedbackMap u) (Icc (-1 : ℝ) 1) ∧
    BijOn (feedbackMap u) (Icc (-1 : ℝ) 1) (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
    ContDiffOn ℝ ⊤ (feedbackMap u) (Icc (-1 : ℝ) 1) ∧
    ContDiffOn ℝ ⊤ (feedbackInverse u) (Icc (-1 / 2 : ℝ) (1 / 2 : ℝ)) ∧
    feedbackPushforwardMeasure u = feedbackDensityMeasure u ∧
    (∀ y ∈ Icc (-1 / 2 : ℝ) (1 / 2 : ℝ),
      feedbackDensity u y = 1 / Real.sqrt (1 - 16 * u * y + 16 * u ^ 2)) ∧
    ∀ v : ℝ, |v| ≤ 1 / 16 →
      InformationTheory.klDiv (feedbackDensityMeasure u) (feedbackDensityMeasure v) ≤
        ENNReal.ofReal (80 * (u - v) ^ 2) := by
  exact ⟨feedbackMap_strictMonoOn hu, feedbackMap_bijOn hu,
    FeedbackSmooth.contDiffOn_feedbackMap u, FeedbackSmooth.contDiffOn_feedbackInverse hu,
    feedbackPushforwardMeasure_eq_densityMeasure hu,
    fun _ hy => FeedbackSharp.feedbackDensity_eq_inv_sqrt hu hy,
    fun _ hv => FeedbackSharp.klDiv_feedbackDensityMeasure_le_eighty hu hv⟩

/-- L13 has neither a nonnegative-X hypothesis nor an extra integrability
hypothesis. Its actual proof now uses the displayed event partition. -/
theorem lemma_lower_mean_to_probability
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Measurable X)
    {μ M : ℝ} (hμ : 0 < μ) (hμM : μ ≤ M)
    (hupper : ∀ᵐ ω ∂P, X ω ≤ M) (hmean : μ ≤ ∫ ω, X ω ∂P) :
    μ / (2 * M) ≤ P.real {ω | μ / 2 ≤ X ω} :=
  MsetsLower.Probability.probability_ge_half_mean_paper P X hX hμ hμM hupper hmean

/-- The newly explicit horizon after T2 is invariant under complementation. -/
theorem horizon_complement {d m : ℕ} (hmd : m ≤ d) (δ : ℝ) :
    NewRoute.horizon d (d - m) δ = NewRoute.horizon d m δ := by
  unfold NewRoute.horizon
  rw [Nat.sub_sub_self hmd, min_comm]

/-- The sharper polynomial majorant printed in the definitive appendix,
using min(m,d-m) ≤ m rather than replacing m by d. -/
theorem horizon_polynomial_bound {d m : ℕ} {δ : ℝ}
    (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ)) :
    (NewRoute.horizon d m δ : ℝ) ≤
      1 + 64 * (d : ℝ) ^ 2 + 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / δ) := by
  have hlog := (ConfidenceOblivious.log_inverse_positive hδ hsmall).le
  have hs : ((min m (d - m) : ℕ) : ℝ) ≤ m := by exact_mod_cast min_le_left m (d - m)
  have hs0 : (0 : ℝ) ≤ min m (d - m) := Nat.cast_nonneg _
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg _
  have hsq : ((min m (d - m) : ℕ) : ℝ) ^ 2 ≤ (m : ℝ) ^ 2 := by nlinarith
  have hprod := mul_le_mul_of_nonneg_left hsq
    (show (0 : ℝ) ≤ 4 * (d : ℝ) * Real.log (1 / δ) by positivity)
  have hnonneg : (0 : ℝ) ≤ 64 * (d : ℝ) ^ 2 +
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / δ) := by positivity
  have hceil := (Nat.ceil_lt_add_one hnonneg).le
  change (NewRoute.horizon d m δ : ℝ) ≤ _ at hceil
  nlinarith

/-- T3, first finish the entire m ≤ d/2 case, including max -> sum. -/
theorem lower_bound_half {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : NewRoute.horizon d m δ ≤ T) (P : Policy d m) :
    HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / δ)))) δ := by
  have hmin : min m (d - m) = m := min_eq_left (by omega)
  have hreq := NewRoute.horizon_requirements hδ hsmall hT
  rw [hmin] at hreq
  have ht := NewRoute.lower_bound_half_max hm h2m hreq.1 hδ hsmall hreq.2 P
  exact ht.mono (NewRoute.final_threshold_le_max (by positivity)
    (NewRoute.log_choose_nonneg (by omega))
    (ConfidenceOblivious.log_inverse_positive hδ hsmall).le) le_rfl

/-- T3, complement only in the last branch, as in the definitive text.
No earlier final lower-bound endpoint is used in this proof. -/
theorem lower_bound_semantic {d m T : ℕ}
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : NewRoute.horizon d m δ ≤ T) :
    ∀ P : Policy d m, HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / δ)))) δ := by
  by_cases hhalf : 2 * m ≤ d
  · exact lower_bound_half hm hhalf hδ hsmall hT
  · have hmd : m ≤ d := by omega
    have hs : 1 ≤ d - m := by omega
    have h2s : 2 * (d - m) ≤ d := by omega
    have hTs : NewRoute.horizon d (d - m) δ ≤ T := by
      rw [horizon_complement hmd]
      exact hT
    apply lower_tail_for_complementary_size hmd (Nat.sub_le d m) (by omega)
      (Nat.sub_sub_self hmd).symm
    intro P
    have ht := lower_bound_half hs h2s hδ hsmall hTs P
    rwa [Nat.choose_symm hmd] at ht

/-- T3: exact explicit statement with an actual deterministic adaptive
non-anticipating adversary and the symmetric ceiling threshold. -/
theorem theorem_lower_bound_explicit {d m T : ℕ}
    (_hd : 2 ≤ d) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (d : ℝ) ^ 2 +
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / δ)) ≤ T) :
    ∀ P : Policy d m, ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m), actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      δ ≤ (runLaw P L T).real {h | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / δ))) ≤ pathRegret L T h} := by
  intro P
  exact NewRoute.real_tail_of_semantic (by omega) P
    (lower_bound_semantic hm hmtop hδ hsmall hT P)

/-- T2 with its newly displayed choice of horizon and the paper's polynomial
majorant. A policy is selected before its adversary witness. -/
theorem theorem_lower_bound_chosen_horizon :
    ∃ c δ₀ : ℝ, 0 < c ∧ δ₀ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ d m δ, 0 < δ → δ ≤ δ₀ →
        (NewRoute.horizon d m δ : ℝ) ≤
          1 + 64 * (d : ℝ) ^ 2 + 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / δ)) ∧
      (∀ d m T δ, 2 ≤ d → 1 ≤ m → m ≤ d - 1 → 0 < δ → δ ≤ δ₀ →
        NewRoute.horizon d m δ ≤ T → ∀ P : Policy d m, ∃ L : LossProcess d m,
          (∀ t (h : History d m t) (a : MSetAction d m), actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
          δ ≤ (runLaw P L T).real {h | c * Real.sqrt ((d : ℝ) * T *
            (Real.log (d.choose m : ℝ) + Real.log (1 / δ))) ≤ pathRegret L T h}) := by
  refine ⟨(2 : ℝ) ^ (-43 : ℤ), (2 : ℝ) ^ (-36 : ℤ), by positivity,
    by constructor <;> norm_num, ?_, ?_⟩
  · intro d m δ hδ hsmall
    exact horizon_polynomial_bound hδ hsmall
  · intro d m T δ hd hm hmtop hδ hsmall hT
    exact theorem_lower_bound_explicit hd hm hmtop hδ hsmall hT

/-- T2 with the literal existential horizon quantifier. Its chosen witness
is the symmetric ceiling displayed immediately after the statement. -/
theorem theorem_lower_bound :
    ∃ (c δ₀ : ℝ) (τ : ℕ → ℕ → ℝ → ℕ),
      0 < c ∧ δ₀ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ d m δ, τ d m δ = NewRoute.horizon d m δ) ∧
      (∀ d m δ, 0 < δ → δ ≤ δ₀ →
        (τ d m δ : ℝ) ≤
          1 + 64 * (d : ℝ) ^ 2 + 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / δ)) ∧
      (∀ d m T δ, 2 ≤ d → 1 ≤ m → m ≤ d - 1 → 0 < δ → δ ≤ δ₀ →
        τ d m δ ≤ T → ∀ P : Policy d m, ∃ L : LossProcess d m,
          (∀ t (h : History d m t) (a : MSetAction d m),
            actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
          δ ≤ (runLaw P L T).real {h | c * Real.sqrt ((d : ℝ) * T *
            (Real.log (d.choose m : ℝ) + Real.log (1 / δ))) ≤ pathRegret L T h}) := by
  obtain ⟨c, δ₀, hc, hδ₀, hpoly, hmain⟩ := theorem_lower_bound_chosen_horizon
  exact ⟨c, δ₀, NewRoute.horizon, hc, hδ₀, fun _ _ _ => rfl, hpoly, hmain⟩

/-- The same definitive assembly for an arbitrary persistent private seed.
The common behavioral policy is constructed before selecting L. -/
theorem theorem_lower_bound_explicit_private_seed
    {Ω : Type*} [MeasurableSpace Ω] {d m T : ℕ}
    (hd : 2 ≤ d) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : NewRoute.horizon d m δ ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m), actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      δ ≤ ν.real {r | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / δ))) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := behavioralPolicy ν choose hc a
  obtain ⟨L, hL, ht⟩ := theorem_lower_bound_explicit hd hm hmtop hδ hsmall hT P
  refine ⟨L, hL, ?_⟩
  rw [PrivateSeedEndpoints.private_regret_probability_eq ν choose hc a L]
  exact ht

/-- C1: specialize this assembly to m=1. Singleton actions are in proved
bijection with the K ordinary arms and action loss equals item loss. -/
theorem corollary_ordinary_bandits_explicit {K T : ℕ} (hK : 2 ≤ K)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ≤ T) :
    ∀ P : Policy K 1, ∃ L : LossProcess K 1,
      (∀ t (h : History K 1 t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) 1) ∧
      δ ≤ (runLaw P L T).real {h | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((K : ℝ) * T *
        (Real.log (K : ℝ) + Real.log (1 / δ))) ≤ pathRegret L T h} := by
  intro P
  have ht : NewRoute.horizon K 1 δ ≤ T := by
    simpa only [NewRoute.horizon_one hK] using hT
  obtain ⟨L, _hL, htail⟩ := theorem_lower_bound_explicit hK (by omega) (by omega) hδ hsmall ht P
  exact ⟨L, NewRoute.ordinary_item_range L, by simpa only [Nat.choose_one_right] using htail⟩

/-- C1 in its literal qualitative form, deduced from T2 by m=1. The chosen
threshold is exactly tau(K,1,δ), and its polynomial majorant is explicit. -/
theorem corollary_ordinary_bandits :
    ∃ (c δ₀ : ℝ) (τ : ℕ → ℝ → ℕ),
      0 < c ∧ δ₀ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ K δ, τ K δ = NewRoute.horizon K 1 δ) ∧
      (∀ K δ, 2 ≤ K → 0 < δ → δ ≤ δ₀ →
        (τ K δ : ℝ) ≤ 1 + 64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ∧
      (∀ K T δ, 2 ≤ K → 0 < δ → δ ≤ δ₀ → τ K δ ≤ T →
        ∀ P : Policy K 1, ∃ L : LossProcess K 1,
          (∀ t (h : History K 1 t) i, L.itemLoss t h i ∈ Icc (0 : ℝ) 1) ∧
          δ ≤ (runLaw P L T).real {h | c * Real.sqrt ((K : ℝ) * T *
            (Real.log (K : ℝ) + Real.log (1 / δ))) ≤ pathRegret L T h}) := by
  obtain ⟨c, δ₀, τ, hc, hδ₀, hτ, hpoly, hmain⟩ := theorem_lower_bound
  refine ⟨c, δ₀, fun K δ => τ K 1 δ, hc, hδ₀, fun K δ => hτ K 1 δ, ?_, ?_⟩
  · intro K δ _hK hδ hsmall
    simpa only [Nat.cast_one, one_pow, mul_one] using hpoly K 1 δ hδ hsmall
  · intro K T δ hK hδ hsmall hT P
    obtain ⟨L, _hL, htail⟩ := hmain K 1 T δ hK (by omega) (by omega) hδ hsmall hT P
    exact ⟨L, NewRoute.ordinary_item_range L, by simpa only [Nat.choose_one_right] using htail⟩

end
end MsetsPaper.Alignment.LowerDefinitive
