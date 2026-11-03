import MsetsPaper.Probability.PolicySeedFixed

/-! # Independent master seeds in a jointly measurable random environment -/

noncomputable section
open MeasureTheory ProbabilityTheory MsetsLower MsetsLower.History
open scoped ENNReal

namespace MsetsPaper.Probability.PolicySeed

variable {d m T : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem measurable_seedRun_parametric
    (P : Policy d m) (hmd : m ≤ d) (L : Ξ → LossProcess d m)
    (hL : ∀ t, Measurable (fun x : Ξ × History d m t ↦ (L x.1).itemLoss t x.2)) :
    Measurable (fun x : Ξ × Seeds T ↦ seedRun P hmd (L x.1) T x.2) := by
  have hc (t : ℕ) : Measurable (fun x : (Ξ × Seeds T) × History d m t ↦
      fixedChoose P hmd x.1.2 t x.2) :=
    (measurable_fixedChoose_joint P hmd t).comp
      ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
  have hl (t : ℕ) : Measurable (fun x : (Ξ × Seeds T) × History d m t ↦
      (L x.1.1).itemLoss t x.2) :=
    (hL t).comp ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
  have h := measurable_deterministicRun
    (fun t (x : Ξ × Seeds T) h ↦ fixedChoose P hmd x.2 t h) hc
    (fun x : Ξ × Seeds T ↦ L x.1) hl T
  convert h using 1
  funext x
  exact (deterministicRun_fixedChoose_eq_seedRun P hmd x.2 (L x.1) T le_rfl).symm

/-- Joint event probabilities retain the independent environment coordinate.
This is the literal product experiment used when fixing the private seed in
the manuscript and then averaging it back. -/
theorem seedRun_joint_event_probability
    (P : Policy d m) (hmd : m ≤ d) (L : Ξ → LossProcess d m)
    (hL : ∀ t, Measurable (fun x : Ξ × History d m t ↦ (L x.1).itemLoss t x.2))
    (mu : Measure Ξ) [IsProbabilityMeasure mu]
    (E : Set (Ξ × History d m T)) (hE : MeasurableSet E) :
    (mu.prod (seedMeasure T)) {x | (x.1, seedRun P hmd (L x.1) T x.2) ∈ E} =
      ∫⁻ xi, runLaw P (L xi) T (Prod.mk xi ⁻¹' E) ∂mu := by
  have hmap : Measurable (fun x : Ξ × Seeds T ↦ (x.1, seedRun P hmd (L x.1) T x.2)) :=
    measurable_fst.prodMk (measurable_seedRun_parametric P hmd L hL)
  have hset : MeasurableSet {x : Ξ × Seeds T | (x.1, seedRun P hmd (L x.1) T x.2) ∈ E} :=
    hmap hE
  rw [Measure.prod_apply hset]
  apply lintegral_congr
  intro xi
  exact seedRun_event_probability P hmd (L xi) T (Prod.mk xi ⁻¹' E) (measurable_prodMk_left hE)

end MsetsPaper.Probability.PolicySeed
