import MsetsPaper.Alignment.LowerSketchRouteSparse
import MsetsPaper.Alignment.LowerSketchRouteDense
import MsetsPaper.Alignment.LowerSketchRouteConfidence

/-! Independent completion of the definitive main-text T2 sketch.
The three branches use coefficient 80; the dense branch retains Top_m to
its tail. Only generic arithmetic, complementation, and representation
transport are shared with the appendix assembly. -/

namespace MsetsPaper.Alignment.LowerSketchRoute

open MsetsLower MsetsLower.Lower MeasureTheory Set
open MsetsPaper.Lower MsetsPaper.Lower.NewRoute MsetsPaper.Probability
open scoped ENNReal

noncomputable section

theorem tail_of_real {d m T : ℕ} (hmd : m ≤ d)
    (P : Policy d m) (L : LossProcess d m) {b p : ℝ}
    (h : p ≤ (runLaw P L T).real {h | b ≤ pathRegret L T h}) :
    HasRegretLowerTail hmd P T b p := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  refine ⟨L, ?_⟩
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2 h

theorem real_tail_of_semantic {d m T : ℕ} (hmd : m ≤ d)
    (P : Policy d m) {b p : ℝ} (h : HasRegretLowerTail hmd P T b p) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      p ≤ (runLaw P L T).real {h | b ≤ pathRegret L T h} := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  obtain ⟨L, hL⟩ := h
  exact ⟨L, L.action_mem_Icc,
    (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hL⟩

/-- The main-text sparse/dense split, using only the new sketch branches. -/
theorem action_count_tail {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    (P : Policy d m) :
    HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-42 : ℤ) *
        Real.sqrt ((d : ℝ) * T * Real.log (d.choose m : ℝ)))
      ((2 : ℝ) ^ (-14 : ℤ)) := by
  by_cases hr : (m : ℝ) / d ≤ (2 : ℝ) ^ (-32 : ℤ)
  · obtain ⟨L, _hitem, htail⟩ :=
      Sparse.lower_action_count_sparse hm h2m hT hr P
    exact (tail_of_real (by omega : m ≤ d) P L htail).mono
      (mul_le_mul_of_nonneg_right (by norm_num :
        (2 : ℝ) ^ (-42 : ℤ) ≤ (2 : ℝ) ^ (-24 : ℤ)) (Real.sqrt_nonneg _))
      (by norm_num)
  · obtain ⟨L, _hobl, _hitem, htail⟩ :=
      Dense.lower_action_count_dense hm h2m hT (lt_of_not_ge hr) P
    exact tail_of_real (by omega : m ≤ d) P L htail

/-- The H >= L branch with exactly the manuscript's maximum B. -/
theorem max_tail_action_dominant {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hT : 64 * d ^ 2 ≤ T)
    {delta : ℝ} (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hdom : Real.log (1 / delta) ≤ Real.log (d.choose m : ℝ))
    (P : Policy d m) :
    HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-42 : ℤ) * Real.sqrt ((d : ℝ) * T *
        max (Real.log (d.choose m : ℝ)) (Real.log (1 / delta)))) delta := by
  rw [max_eq_left hdom]
  exact (action_count_tail hm h2m hT P).mono le_rfl
    (hsmall.trans (by norm_num))

theorem log_choose_nonneg {d m : ℕ} (hmd : m ≤ d) :
    0 ≤ Real.log (d.choose m : ℝ) := by
  apply Real.log_nonneg
  exact_mod_cast (show 1 ≤ d.choose m from Nat.choose_pos hmd)

/-- The confidence-dominant case of the coefficient-80 sketch. -/
theorem max_tail_confidence_dominant {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (hdom : Real.log (d.choose m : ℝ) < Real.log (1 / delta))
    (P : Policy d m) :
    HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-42 : ℤ) * Real.sqrt ((d : ℝ) * T *
        max (Real.log (d.choose m : ℝ)) (Real.log (1 / delta)))) delta := by
  rw [max_eq_right hdom.le]
  obtain ⟨L, _hobl, _hitem, htail⟩ :=
    Confidence.lower_confidence_oblivious hm h2m hdelta hsmall hT P
  exact (tail_of_real (by omega : m ≤ d) P L htail).mono
    (mul_le_mul_of_nonneg_right (by norm_num :
      (2 : ℝ) ^ (-42 : ℤ) ≤ (2 : ℝ) ^ (-16 : ℤ)) (Real.sqrt_nonneg _)) le_rfl

/-- A common explicit threshold for the two sketch terms. -/
theorem lower_bound_half_max {d m T : ℕ}
    (hm : 1 ≤ m) (h2m : 2 * m ≤ d) (hTaction : 64 * d ^ 2 ≤ T)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hTconfidence : 4 * (d : ℝ) * (m : ℝ) ^ 2 * Real.log (1 / delta) ≤ T)
    (P : Policy d m) :
    HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-42 : ℤ) * Real.sqrt ((d : ℝ) * T *
        max (Real.log (d.choose m : ℝ)) (Real.log (1 / delta)))) delta := by
  by_cases hdom : Real.log (1 / delta) ≤ Real.log (d.choose m : ℝ)
  · exact max_tail_action_dominant hm h2m hTaction hsmall hdom P
  · exact max_tail_confidence_dominant hm h2m hdelta hsmall hTconfidence
      (lt_of_not_ge hdom) P

/-- Complete semantic sketch: reduce to s, apply the two-term case split, replace
max by half the sum, and transport the exact tail through complementation. -/
theorem lower_bound_semantic {d m T : ℕ}
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : horizon d m delta ≤ T) :
    ∀ P : Policy d m, HasRegretLowerTail (by omega : m ≤ d) P T
      ((2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / delta)))) delta := by
  have hmd : m ≤ d := by omega
  have hs := min_size_bounds hm hmtop
  have hreq := horizon_requirements hdelta hsmall hT
  apply lower_tail_of_min_size (by omega : 0 < m) hmd
  intro P
  have ht := lower_bound_half_max hs.1 hs.2 hreq.1 hdelta hsmall hreq.2 P
  rw [choose_min_size hmd] at ht
  exact ht.mono (final_threshold_le_max (by positivity)
    (log_choose_nonneg hmd) (ConfidenceOblivious.log_inverse_positive hdelta hsmall).le) le_rfl

/-- Quantitative completion of the sketch, exposing the deterministic adaptive loss
process, action normalization, run law, ceiling, and numerical constant. -/
theorem lower_bound_explicit {d m T : ℕ}
    (_hd : 2 ≤ d) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (d : ℝ) ^ 2 +
      4 * (d : ℝ) * (min m (d - m) : ℕ) ^ 2 * Real.log (1 / delta)) ≤ T) :
    ∀ P : Policy d m, ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ (runLaw P L T).real
        {h | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
          (Real.log (d.choose m : ℝ) + Real.log (1 / delta))) ≤ pathRegret L T h} := by
  intro P
  exact real_tail_of_semantic (by omega : m ≤ d) P
    (lower_bound_semantic hm hmtop hdelta hsmall hT P)

/-- Literal quantified T2 with an explicit polynomial upper bound. -/
def QualitativeLowerBound : Prop :=
  ∃ (c delta0 : ℝ) (tau : ℕ → ℕ → ℝ → ℕ),
    0 < c ∧ delta0 ∈ Ioo (0 : ℝ) 1 ∧
    (∀ d m delta, m ≤ d → 0 < delta → delta ≤ delta0 →
      (tau d m delta : ℝ) ≤ thresholdPolynomial d delta) ∧
    (∀ d m delta T, 2 ≤ d → 1 ≤ m → m ≤ d - 1 →
      0 < delta → delta ≤ delta0 → tau d m delta ≤ T →
      ∀ P : Policy d m, ∃ L : LossProcess d m,
        (∀ t (h : History d m t) (a : MSetAction d m),
          actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
        delta ≤ (runLaw P L T).real
          {h | c * Real.sqrt ((d : ℝ) * T *
            (Real.log (d.choose m : ℝ) + Real.log (1 / delta))) ≤ pathRegret L T h})

/-- T2, with exactly c=2^-43, delta0=2^-36 and the new ceiling as witnesses. -/
theorem lower_bound : QualitativeLowerBound := by
  refine ⟨(2 : ℝ) ^ (-43 : ℤ), (2 : ℝ) ^ (-36 : ℤ), horizon, ?_, ?_, ?_, ?_⟩
  · positivity
  · constructor <;> norm_num
  · intro d m delta hmd hdelta hsmall
    exact horizon_polynomial_bound hmd hdelta hsmall
  · intro d m delta T hd hm hmtop hdelta hsmall hT
    exact lower_bound_explicit hd hm hmtop hdelta hsmall hT

/-- Persistent private randomness is quantified before the deterministic
adversary is selected; this wrapper uses the new sketch endpoint. -/
theorem lower_bound_explicit_private_seed
    {Ω : Type*} [MeasurableSpace Ω] {d m T : ℕ}
    (hd : 2 ≤ d) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    {delta : ℝ} (hdelta : 0 < delta) (hsmall : delta ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : horizon d m delta ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → History d m t → MSetAction d m)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : LossProcess d m,
      (∀ t (h : History d m t) (a : MSetAction d m),
        actionLoss a (L.itemLoss t h) ∈ Icc (0 : ℝ) 1) ∧
      delta ≤ ν.real {r | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((d : ℝ) * T *
        (Real.log (d.choose m : ℝ) + Real.log (1 / delta))) ≤
          pathRegret L T (deterministicRun (fun t h => choose t r h) L T)} := by
  let a := Classical.choice (nonempty_MSetAction (show m ≤ d by omega))
  let P := MsetsPaper.Probability.PrivateSeed.behavioralPolicy ν choose hc a
  obtain ⟨L, hL, ht⟩ := lower_bound_explicit hd hm hmtop hdelta hsmall hT P
  refine ⟨L, hL, ?_⟩
  rw [PrivateSeedEndpoints.private_regret_probability_eq ν choose hc a L]
  exact ht

end

end MsetsPaper.Alignment.LowerSketchRoute
