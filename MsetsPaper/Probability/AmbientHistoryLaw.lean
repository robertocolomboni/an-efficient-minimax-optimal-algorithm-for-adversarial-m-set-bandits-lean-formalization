import MsetsPaper.Probability.AmbientHistoryFinite
import Mathlib.Probability.Kernel.CondDistrib

/-! # The ambient interaction law follows from conditional sampling

The hypothesis identifies only each next action's conditional distribution
given its past observable history. The complete run law is a conclusion,
proved by induction. No independence between history, losses and learner seed
is assumed.
-/

namespace MsetsPaper.Probability.AmbientHistory

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open scoped ENNReal ProbabilityTheory

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

theorem ae_kernel_eq_of_comp_ae_eq {A B : Type*} [MeasurableSpace A]
    [MeasurableSpace B] [Countable B] [MeasurableSingletonClass B]
    (μ : Measure Ω) (H : Ω → A) (hH : Measurable H)
    (κ η : Kernel A B) (heq : ∀ᵐ ω ∂μ, κ (H ω) = η (H ω)) :
    κ =ᵐ[μ.map H] η := by
  have ha (a : B) : ∀ᵐ h ∂μ.map H, κ h {a} = η h {a} := by
    apply (ae_map_iff hH.aemeasurable
      (measurableSet_eq_fun (κ.measurable_coe (measurableSet_singleton a))
        (η.measurable_coe (measurableSet_singleton a)))).2
    filter_upwards [heq] with ω hω
    rw [hω]
  filter_upwards [ae_all_iff.mpr ha] with h hh
  exact Measure.ext_of_singleton hh

theorem actionHistoryKernel_comp_eq_compProd (P : Policy d m) (t : ℕ)
    (ν : Measure (History d m t)) [IsProbabilityMeasure ν] :
    actionHistoryKernel P t ∘ₘ ν = ν ⊗ₘ P.kernel t := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _), Measure.compProd_apply hS]
  apply lintegral_congr
  intro h
  rw [actionHistoryKernel_apply, Measure.map_apply measurable_prodMk_left hS]

theorem history_law_of_conditional_sampling
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Nonempty (Action d m)]
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (T : ℕ) (hX : ∀ t < T, Measurable (X t))
    (hH : ∀ t ≤ T, Measurable (history X ell t))
    (P : Policy d m) (L : SignedLossProcess d m)
    (hL : ∀ t < T, ∀ᵐ ω ∂μ, L.itemLoss t (history X ell t ω) = ell t ω)
    (hsample : ∀ t < T, ∀ᵐ ω ∂μ,
      condDistrib (X t) (history X ell t) μ (history X ell t ω) =
        P.kernel t (history X ell t ω)) :
    ∀ t ≤ T, μ.map (history X ell t) = signedRunLaw P L t := by
  intro t
  induction t with
  | zero =>
      intro ht
      simp only [history, signedRunLaw, Measure.map_const, measure_univ, one_smul]
  | succ t ih =>
      intro ht
      have htT : t < T := by omega
      have htm : t ≤ T := by omega
      have hkernel := ae_kernel_eq_of_comp_ae_eq μ (history X ell t) (hH t htm)
        (condDistrib (X t) (history X ell t) μ) (P.kernel t) (hsample t htT)
      have hjoint : μ.map (fun ω ↦ (history X ell t ω, X t ω)) =
          μ.map (history X ell t) ⊗ₘ P.kernel t :=
        (compProd_map_condDistrib (hH t htm).aemeasurable (hX t htT).aemeasurable).symm.trans
          (Measure.compProd_congr hkernel)
      have hnext : history X ell (t + 1) =ᵐ[μ]
          signedExtendRun L t ∘ (fun ω ↦ (history X ell t ω, X t ω)) := by
        filter_upwards [hL t htT] with ω hω
        change (history X ell t ω).snoc (X t ω) (actionLoss (X t ω) (ell t ω)) =
          (history X ell t ω).snoc (X t ω)
            (actionLoss (X t ω) (L.itemLoss t (history X ell t ω)))
        rw [hω]
      rw [Measure.map_congr hnext, ← Measure.map_map (measurable_signedExtendRun L t)
        ((hH t htm).prodMk (hX t htT)), hjoint,
        ← actionHistoryKernel_comp_eq_compProd,
        Measure.map_comp _ _ (measurable_signedExtendRun L t), ih htm]
      rfl

/-- Once an ambient experiment has been identified, a policy agreeing on
its actual histories gives the same law. This is used to identify the
factored predictable policy with the manuscript's concrete algorithm. -/
theorem history_law_change_policy
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ) (T : ℕ)
    (hH : ∀ t ≤ T, Measurable (history X ell t))
    (P Q : Policy d m) (L : SignedLossProcess d m)
    (hlaw : ∀ t ≤ T, μ.map (history X ell t) = signedRunLaw P L t)
    (hPQ : ∀ t < T, ∀ᵐ ω ∂μ,
      P.kernel t (history X ell t ω) = Q.kernel t (history X ell t ω)) :
    ∀ t ≤ T, μ.map (history X ell t) = signedRunLaw Q L t := by
  intro t
  induction t with
  | zero => intro ht; rw [hlaw 0 ht]
  | succ t ih =>
      intro ht
      have htm : t ≤ T := by omega
      have hk := ae_kernel_eq_of_comp_ae_eq μ (history X ell t) (hH t htm)
        (P.kernel t) (Q.kernel t) (hPQ t (by omega))
      have hr : ∀ᵐ h ∂μ.map (history X ell t), signedRoundKernel P L t h =
          signedRoundKernel Q L t h := by
        filter_upwards [hk] with h hh
        ext S hS
        rw [signedRoundKernel_apply _ _ _ _ hS, signedRoundKernel_apply _ _ _ _ hS, hh]
      rw [hlaw (t + 1) ht]
      change signedRoundKernel P L t ∘ₘ signedRunLaw P L t =
        signedRoundKernel Q L t ∘ₘ signedRunLaw Q L t
      rw [← hlaw t htm, ← ih htm]
      exact Measure.comp_congr hr

/-- Full canonical representation, derived from predictable losses and
probability vectors and the next-action conditional sampling rule. -/
theorem exists_canonical_protocol
    (μ : Measure Ω) [IsProbabilityMeasure μ] [Nonempty (Action d m)]
    (hmd : m ≤ d) (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (T : ℕ)
    (hX : ∀ t < T, Measurable (X t))
    (hell : ∀ t < T, Measurable[historySigma X ell t] (ell t))
    (hp : ∀ t < T, Measurable[historySigma X ell t] (p t))
    (hnorm : ∀ t < T, ∀ᵐ ω ∂μ, ∀ a : Action d m, |actionLoss a (ell t ω)| ≤ 1)
    (hvalid : ∀ t < T, ∀ᵐ ω ∂μ, IsDistribution (p t ω))
    (hsample : ∀ t < T, ∀ᵐ ω ∂μ,
      condDistrib (X t) (history X ell t) μ (history X ell t ω) =
        finiteAtomicMeasure (p t ω) id) :
    ∃ (P : Policy d m) (L : SignedLossProcess d m),
      (∀ t < T, ∀ᵐ ω ∂μ, P.kernel t (history X ell t ω) = finiteAtomicMeasure (p t ω) id) ∧
      (∀ t < T, ∀ᵐ ω ∂μ, L.itemLoss t (history X ell t ω) = ell t ω) ∧
      ∀ t ≤ T, μ.map (history X ell t) = signedRunLaw P L t := by
  obtain ⟨L, hL⟩ := exists_normalized_loss_upto μ (history X ell) ell T hell hnorm
  obtain ⟨P, hP⟩ := exists_normalized_policy_upto μ hmd (history X ell) p T hp hvalid
  refine ⟨P, L, hP, hL, ?_⟩
  apply history_law_of_conditional_sampling μ X ell T hX
    (measurable_history_upto X ell T hX hell) P L hL
  intro t ht
  filter_upwards [hsample t ht, hP t ht] with ω hs hq
  exact hs.trans hq.symm

end
end MsetsPaper.Probability.AmbientHistory
