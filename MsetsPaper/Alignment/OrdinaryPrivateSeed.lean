import MsetsPaper.Alignment.OrdinaryDefinitive

/-! # C1 with native arms and the learner's original persistent private seed

The seed is arbitrary, rather than a fresh draw at each round. The learner is
translated before the adversary is selected. The history and regret identities
hold pointwise for every original seed realization.
-/

noncomputable section

universe u

namespace MsetsPaper.Lower.Ordinary

open MeasureTheory

def deterministicRun {K : ℕ}
    (choose : (t : ℕ) → History K t → Fin K) (L : LossProcess K) :
    (t : ℕ) → History K t
  | 0 => ()
  | t + 1 =>
      let h := deterministicRun choose L t
      let i := choose t h
      h.snoc i (L.loss t h i)

def toMsetChoose {Ω : Type*} {K : ℕ}
    (choose : (t : ℕ) → Ω → History K t → Fin K)
    (t : ℕ) (r : Ω) (h : MsetsLower.History K 1 t) : MsetsLower.MSetAction K 1 :=
  armEquiv K (choose t r ((historyEquiv K t).symm h))

theorem measurable_toMsetChoose {Ω : Type*} [MeasurableSpace Ω] {K : ℕ}
    (choose : (t : ℕ) → Ω → History K t → Fin K)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) (t : ℕ) :
    Measurable (Function.uncurry (toMsetChoose choose t)) := by
  exact (armEquiv K).measurable.comp ((hc t).comp
    (measurable_fst.prodMk ((historyEquiv K t).symm.measurable.comp measurable_snd)))

theorem deterministicRun_transport {Ω : Type*} {K : ℕ}
    (choose : (t : ℕ) → Ω → History K t → Fin K)
    (G : MsetsLower.LossProcess K 1) (r : Ω) : ∀ t,
    historyEquiv K t (deterministicRun (fun t h => choose t r h) (fromMsetLoss G) t) =
      MsetsPaper.Probability.deterministicRun (fun t h => toMsetChoose choose t r h) G t := by
  intro t
  induction t with
  | zero => rfl
  | succ t ih =>
      change historyEquiv K (t + 1)
        (extendRun (fromMsetLoss G) t
          (deterministicRun (fun t h => choose t r h) (fromMsetLoss G) t,
           choose t r (deterministicRun (fun t h => choose t r h) (fromMsetLoss G) t))) =
        MsetsLower.extendRun G t
          (MsetsPaper.Probability.deterministicRun (fun t h => toMsetChoose choose t r h) G t,
           toMsetChoose choose t r
             (MsetsPaper.Probability.deterministicRun (fun t h => toMsetChoose choose t r h) G t))
      rw [extendRun_transport, ← ih]
      simp only [toMsetChoose, MeasurableEquiv.symm_apply_apply]

theorem private_pathRegret_transport {Ω : Type*} {K : ℕ}
    (choose : (t : ℕ) → Ω → History K t → Fin K)
    (G : MsetsLower.LossProcess K 1) (r : Ω) (T : ℕ) :
    pathRegret (fromMsetLoss G) T
      (deterministicRun (fun t h => choose t r h) (fromMsetLoss G) T) =
    MsetsLower.Lower.pathRegret G T
      (MsetsPaper.Probability.deterministicRun (fun t h => toMsetChoose choose t r h) G T) := by
  rw [pathRegret_transport, deterministicRun_transport]

end MsetsPaper.Lower.Ordinary

namespace MsetsPaper.Alignment.OrdinaryDefinitive

open MeasureTheory Set MsetsPaper.Lower

theorem corollary_ordinary_bandits_explicit_private_seed
    {Ω : Type*} [MeasurableSpace Ω] {K T : ℕ} (hK : 2 ≤ K)
    {δ : ℝ} (hδ : 0 < δ) (hsmall : δ ≤ (2 : ℝ) ^ (-36 : ℤ))
    (hT : Nat.ceil (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ≤ T)
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    (choose : (t : ℕ) → Ω → Ordinary.History K t → Fin K)
    (hc : ∀ t, Measurable (Function.uncurry (choose t))) :
    ∃ L : Ordinary.LossProcess K,
      (∀ t (h : Ordinary.History K t) i, L.loss t h i ∈ Icc (0 : ℝ) 1) ∧
      δ ≤ ν.real {r | (2 : ℝ) ^ (-43 : ℤ) * Real.sqrt ((K : ℝ) * T *
        (Real.log (K : ℝ) + Real.log (1 / δ))) ≤ Ordinary.pathRegret L T
        (Ordinary.deterministicRun (fun t h => choose t r h) L T)} := by
  have ht : NewRoute.horizon K 1 δ ≤ T := by
    simpa only [NewRoute.horizon_one hK] using hT
  obtain ⟨G, _hG, htail⟩ := LowerDefinitive.theorem_lower_bound_explicit_private_seed
    hK (by omega) (by omega) hδ hsmall ht ν (Ordinary.toMsetChoose choose)
      (Ordinary.measurable_toMsetChoose choose hc)
  refine ⟨Ordinary.fromMsetLoss G, (Ordinary.fromMsetLoss G).loss_mem_Icc, ?_⟩
  simpa only [Ordinary.private_pathRegret_transport, Nat.choose_one_right] using htail

/-- The qualitative C1 quantifiers, native arms, and arbitrary original seed
in a single interface. The adversary is chosen before the seed realization. -/
theorem corollary_ordinary_bandits_private_seed :
    ∃ (c δ₀ : ℝ) (τ : ℕ → ℝ → ℕ),
      0 < c ∧ δ₀ ∈ Ioo (0 : ℝ) 1 ∧
      (∀ K δ, τ K δ = NewRoute.horizon K 1 δ) ∧
      (∀ K δ, 2 ≤ K → 0 < δ → δ ≤ δ₀ →
        (τ K δ : ℝ) ≤ 1 + 64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ∧
      (∀ (Ω : Type u) [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν],
        ∀ K T δ, 2 ≤ K → 0 < δ → δ ≤ δ₀ → τ K δ ≤ T →
        ∀ (choose : (t : ℕ) → Ω → Ordinary.History K t → Fin K),
          (∀ t, Measurable (Function.uncurry (choose t))) →
          ∃ L : Ordinary.LossProcess K,
            (∀ t (h : Ordinary.History K t) i, L.loss t h i ∈ Icc (0 : ℝ) 1) ∧
            δ ≤ ν.real {r | c * Real.sqrt ((K : ℝ) * T *
              (Real.log (K : ℝ) + Real.log (1 / δ))) ≤ Ordinary.pathRegret L T
              (Ordinary.deterministicRun (fun t h => choose t r h) L T)}) := by
  refine ⟨(2 : ℝ) ^ (-43 : ℤ), (2 : ℝ) ^ (-36 : ℤ),
    fun K δ => NewRoute.horizon K 1 δ, by positivity,
    by constructor <;> norm_num, fun _ _ => rfl, ?_, ?_⟩
  · intro K δ _hK hδ hsmall
    simpa only [Nat.cast_one, one_pow, mul_one] using
      (LowerDefinitive.horizon_polynomial_bound (d := K) (m := 1) hδ hsmall)
  · intro Ω _ ν _ K T δ hK hδ hsmall hT choose hc
    have ht : Nat.ceil (64 * (K : ℝ) ^ 2 + 4 * (K : ℝ) * Real.log (1 / δ)) ≤ T := by
      simpa only [NewRoute.horizon_one hK] using hT
    exact corollary_ordinary_bandits_explicit_private_seed hK hδ hsmall ht ν choose hc

end MsetsPaper.Alignment.OrdinaryDefinitive
