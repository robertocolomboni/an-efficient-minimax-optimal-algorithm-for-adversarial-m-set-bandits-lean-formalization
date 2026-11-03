import MsetsPaper.Probability.AmbientHistoryLaw
import MsetsPaper.Upper.MainObservableBound

/-! # Ambient external regret and its canonical observable event

The ambient statistic is the sum of actual played losses minus the minimum
over fixed actions along the same random loss sequence. Its equality with
canonical regret is proved from predictability, not assumed.
-/

namespace MsetsPaper.Probability.AmbientHistory

open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open scoped BigOperators ENNReal

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {d m : ℕ}

def regret (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (T : ℕ) (ω : Ω) : ℝ :=
  (∑ t ∈ Finset.range T, actionLoss (X t ω) (ell t ω)) -
    sInf (Set.range (fun a : Action d m ↦ ∑ t ∈ Finset.range T, actionLoss a (ell t ω)))

theorem measurable_regret (X : ℕ → Ω → Action d m)
    (ell : ℕ → Ω → Fin d → ℝ) (T : ℕ)
    (hX : ∀ t < T, Measurable (X t))
    (hell : ∀ t < T, Measurable[historySigma X ell t] (ell t)) :
    Measurable (regret X ell T) := by
  have hH := measurable_history_upto X ell T hX hell
  have hl (t : ℕ) (ht : t < T) : Measurable (ell t) :=
    (hell t ht).mono (hH t (by omega)).comap_le le_rfl
  have hp : Measurable (fun ω ↦ ∑ t ∈ Finset.range T, actionLoss (X t ω) (ell t ω)) := by
    apply Finset.measurable_sum
    intro t ht
    exact (measurable_actionLoss_joint (hl t (Finset.mem_range.mp ht))).comp
      (measurable_id.prodMk (hX t (Finset.mem_range.mp ht)))
  have hc (a : Action d m) :
      Measurable (fun ω ↦ ∑ t ∈ Finset.range T, actionLoss a (ell t ω)) := by
    apply Finset.measurable_sum
    intro t ht
    exact measurable_actionLoss a (hl t (Finset.mem_range.mp ht))
  exact hp.sub (Measurable.iInf hc)

theorem measurable_observablePathSum
    (g : (t : ℕ) → History d m t → Action d m → ℝ)
    (hg : ∀ t a, Measurable (fun h ↦ g t h a)) :
    ∀ t, Measurable (observablePathSum g t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hgj : Measurable (fun p : History d m t × Action d m ↦ g t p.1 p.2) :=
        measurable_from_prod_countable_left (hg t)
      exact (ih.comp measurable_fst).add
        (hgj.comp (measurable_fst.prodMk measurable_snd.fst))

theorem measurable_observableSignedRegret (L : SignedLossProcess d m) (T : ℕ) :
    Measurable (observableSignedRegret L T) := by
  have hp := measurable_observablePathSum
    (fun t h a ↦ actionLoss a (L.itemLoss t h))
    (fun t a ↦ measurable_actionLoss a (L.measurable_itemLoss t)) T
  have hc (a : Action d m) := measurable_observablePathSum
    (fun t h (_ : Action d m) ↦ actionLoss a (L.itemLoss t h))
    (fun t _ ↦ measurable_actionLoss a (L.measurable_itemLoss t)) T
  exact hp.sub (Measurable.iInf hc)

theorem observablePathSum_history (X : ℕ → Ω → Action d m)
    (ell : ℕ → Ω → Fin d → ℝ)
    (g : (t : ℕ) → History d m t → Action d m → ℝ) (ω : Ω) :
    ∀ T, observablePathSum g T (history X ell T ω) =
      ∑ t ∈ Finset.range T, g t (history X ell t ω) (X t ω) := by
  intro T
  induction T with
  | zero => simp [history, observablePathSum]
  | succ T ih =>
      rw [Finset.sum_range_succ]
      change observablePathSum g T (history X ell T ω) + g T (history X ell T ω) (X T ω) = _
      rw [ih]

theorem regret_eq_of_loss_factor (X : ℕ → Ω → Action d m)
    (ell : ℕ → Ω → Fin d → ℝ) (L : SignedLossProcess d m) (T : ℕ) (ω : Ω)
    (hL : ∀ t < T, L.itemLoss t (history X ell t ω) = ell t ω) :
    observableSignedRegret L T (history X ell T ω) = regret X ell T ω := by
  unfold observableSignedRegret regret
  simp only [observablePathSum_history]
  congr 1
  · apply Finset.sum_congr rfl
    intro t ht
    rw [hL t (Finset.mem_range.mp ht)]
  · congr 2
    funext a
    apply Finset.sum_congr rfl
    intro t ht
    rw [hL t (Finset.mem_range.mp ht)]

theorem regret_ae_eq_of_loss_factor (μ : Measure Ω)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (L : SignedLossProcess d m) (T : ℕ)
    (hL : ∀ t < T, ∀ᵐ ω ∂μ, L.itemLoss t (history X ell t ω) = ell t ω) :
    (fun ω ↦ observableSignedRegret L T (history X ell T ω)) =ᵐ[μ] regret X ell T := by
  have hall : ∀ᵐ ω ∂μ, ∀ t < T, L.itemLoss t (history X ell t ω) = ell t ω := by
    simpa only [ae_all_iff] using hL
  filter_upwards [hall] with ω hω
  exact regret_eq_of_loss_factor X ell L T ω hω

theorem regret_event_transport (μ : Measure Ω)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (P : Policy d m) (L : SignedLossProcess d m) (T : ℕ)
    (hH : Measurable (history X ell T))
    (hL : ∀ t < T, ∀ᵐ ω ∂μ, L.itemLoss t (history X ell t ω) = ell t ω)
    (hlaw : μ.map (history X ell T) = signedRunLaw P L T) (b : ℝ) :
    μ.real {ω | regret X ell T ω ≤ b} =
      (signedRunLaw P L T).real {h | observableSignedRegret L T h ≤ b} := by
  have hregret := regret_ae_eq_of_loss_factor μ X ell L T hL
  have hE := measurableSet_le (measurable_observableSignedRegret L T) (measurable_const (a := b))
  have heq : μ {ω | regret X ell T ω ≤ b} =
      μ ((history X ell T) ⁻¹' {h | observableSignedRegret L T h ≤ b}) := by
    apply measure_congr
    filter_upwards [hregret] with ω hω
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hω]
  change (μ {ω | regret X ell T ω ≤ b}).toReal = _
  rw [heq, ← Measure.map_apply hH hE, hlaw]
  rfl

end
end MsetsPaper.Probability.AmbientHistory
