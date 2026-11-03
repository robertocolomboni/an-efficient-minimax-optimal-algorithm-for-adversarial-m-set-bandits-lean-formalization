import MsetsLower.Core.Protocol
import Mathlib.Probability.Kernel.Representation
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Explicit independent private seeds for arbitrary observable policies

Each round uses a measurable realization of its actual action kernel. The
same realization is used in every loss environment. A finite master seed
is a product of independent uniforms, fixed before the interaction.
-/

noncomputable section
open MeasureTheory ProbabilityTheory MsetsLower MsetsLower.History
open scoped ENNReal

namespace MsetsPaper.Probability.PolicySeed

abbrev UniformSeed : Type := unitInterval
abbrev Seeds (T : ℕ) := Fin T → UniformSeed

def seedMeasure (T : ℕ) : Measure (Seeds T) :=
  Measure.pi (fun _ ↦ (volume : Measure UniformSeed))

instance seedMeasure_probability (T : ℕ) : IsProbabilityMeasure (seedMeasure T) := by
  unfold seedMeasure
  infer_instance

variable {d m : ℕ}

theorem exists_selector (P : Policy d m) (hmd : m ≤ d) (t : ℕ) :
    ∃ f : History d m t → UniformSeed → MSetAction d m,
      Measurable (Function.uncurry f) ∧ ∀ h, (volume : Measure UniformSeed).map (f h) = P.kernel t h := by
  letI := nonempty_MSetAction hmd
  exact (P.kernel t).exists_measurable_map_eq_unitInterval

def selector (P : Policy d m) (hmd : m ≤ d) (t : ℕ) :
    History d m t → UniformSeed → MSetAction d m :=
  Classical.choose (exists_selector P hmd t)

theorem measurable_selector (P : Policy d m) (hmd : m ≤ d) (t : ℕ) :
    Measurable (Function.uncurry (selector P hmd t)) :=
  (Classical.choose_spec (exists_selector P hmd t)).1

theorem selector_law (P : Policy d m) (hmd : m ≤ d) (t : ℕ) (h : History d m t) :
    (volume : Measure UniformSeed).map (selector P hmd t h) = P.kernel t h :=
  (Classical.choose_spec (exists_selector P hmd t)).2 h

def seedSplit (T : ℕ) : Seeds (T + 1) ≃ᵐ (UniformSeed × Seeds T) :=
  MeasurableEquiv.piFinSuccAbove (fun _ ↦ UniformSeed) (Fin.last T)

def seedSnoc {T : ℕ} (r : Seeds T) (u : UniformSeed) : Seeds (T + 1) :=
  (seedSplit T).symm (u, r)

@[simp] theorem seedSnoc_last {T : ℕ} (r : Seeds T) (u : UniformSeed) :
    seedSnoc r u (Fin.last T) = u :=
  Fin.insertNth_apply_same (α := fun _ : Fin (T + 1) ↦ UniformSeed) (Fin.last T) u r

@[simp] theorem seedSnoc_castSucc {T : ℕ} (r : Seeds T) (u : UniformSeed) (i : Fin T) :
    seedSnoc r u i.castSucc = r i := by
  change Fin.insertNth (α := fun _ : Fin (T + 1) ↦ UniformSeed)
    (Fin.last T) u r i.castSucc = r i
  have h := Fin.insertNth_apply_succAbove (α := fun _ : Fin (T + 1) ↦ UniformSeed)
    (Fin.last T) u r i
  simpa only [Fin.succAbove_last] using h

theorem measurable_seedSnoc (T : ℕ) :
    Measurable (fun x : Seeds T × UniformSeed ↦ seedSnoc x.1 x.2) :=
  (seedSplit T).symm.measurable.comp measurable_swap

theorem seedSnoc_measurePreserving (T : ℕ) :
    MeasurePreserving (fun x : Seeds T × UniformSeed ↦ seedSnoc x.1 x.2)
      ((seedMeasure T).prod volume) (seedMeasure (T + 1)) := by
  have h := measurePreserving_piFinSuccAbove
    (fun _ : Fin (T + 1) ↦ (volume : Measure UniformSeed)) (Fin.last T)
  exact h.symm.comp Measure.measurePreserving_swap

theorem lintegral_seedMeasure_snoc {T : ℕ} {f : Seeds (T + 1) → ℝ≥0∞}
    (hf : Measurable f) :
    (∫⁻ r, f r ∂seedMeasure (T + 1)) =
      ∫⁻ r, ∫⁻ u, f (seedSnoc r u) ∂volume ∂seedMeasure T := by
  rw [← (seedSnoc_measurePreserving T).lintegral_comp hf]
  exact lintegral_prod _ (hf.comp (measurable_seedSnoc T)).aemeasurable

def seedRun (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m) :
    (T : ℕ) → Seeds T → History d m T
  | 0, _ => ()
  | T + 1, r =>
      let h := seedRun P hmd L T (fun i ↦ r i.castSucc)
      let a := selector P hmd T h (r (Fin.last T))
      h.snoc a (actionLoss a (L.itemLoss T h))

theorem measurable_seedRun (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m) :
    ∀ T, Measurable (seedRun P hmd L T) := by
  intro T
  induction T with
  | zero => exact measurable_const
  | succ T ih =>
    have hprefix : Measurable (fun r : Seeds (T + 1) ↦ seedRun P hmd L T (fun i ↦ r i.castSucc)) :=
      ih.comp (Measurable.of_eval (fun i ↦ measurable_pi_apply i.castSucc))
    have haction := (measurable_selector P hmd T).comp
      (hprefix.prodMk (measurable_pi_apply (Fin.last T)))
    exact (measurable_extendRun L T).comp (hprefix.prodMk haction)

theorem seedRun_snoc (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m)
    (T : ℕ) (r : Seeds T) (u : UniformSeed) :
    seedRun P hmd L (T + 1) (seedSnoc r u) =
      let h := seedRun P hmd L T r
      let a := selector P hmd T h u
      h.snoc a (actionLoss a (L.itemLoss T h)) := by
  simp only [seedRun, seedSnoc_castSucc, seedSnoc_last]

def seedRound (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m)
    (t : ℕ) (h : History d m t) (u : UniformSeed) : History d m (t + 1) :=
  let a := selector P hmd t h u
  h.snoc a (actionLoss a (L.itemLoss t h))

theorem measurable_seedRound (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m)
    (t : ℕ) (h : History d m t) : Measurable (seedRound P hmd L t h) :=
  (measurable_extendRun L t).comp
    (measurable_const.prodMk (measurable_selector P hmd t).of_uncurry_left)

theorem seedRound_law (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m)
    (t : ℕ) (h : History d m t) :
    (volume : Measure UniformSeed).map (seedRound P hmd L t h) = roundKernel P L t h := by
  have hu : Measurable (fun a : MSetAction d m ↦ h.snoc a (actionLoss a (L.itemLoss t h))) :=
    (measurable_extendRun L t).comp (measurable_const.prodMk measurable_id)
  calc
    _ = ((volume : Measure UniformSeed).map (selector P hmd t h)).map
        (fun a ↦ h.snoc a (actionLoss a (L.itemLoss t h))) := by
      rw [Measure.map_map hu (measurable_selector P hmd t).of_uncurry_left]
      rfl
    _ = _ := by
      rw [selector_law]
      ext s hs
      rw [Measure.map_apply hu hs, roundKernel_apply P L t h hs]
      rfl

/-- The full run law, not just a one-step sampler law. The same fixed seed
realization works for every deterministic non-anticipating loss process. -/
theorem seedRun_map (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m) :
    ∀ T, (seedMeasure T).map (seedRun P hmd L T) = runLaw P L T := by
  intro T
  induction T with
  | zero =>
    change (seedMeasure 0).map (fun _ ↦ ()) = Measure.dirac ()
    simp
  | succ T ih =>
    ext s hs
    have hI : Measurable (s.indicator (1 : History d m (T + 1) → ℝ≥0∞)) :=
      measurable_const.indicator hs
    have hinner (r : Seeds T) :
        (∫⁻ u, s.indicator (1 : History d m (T + 1) → ℝ≥0∞)
          (seedRun P hmd L (T + 1) (seedSnoc r u)) ∂volume) =
        roundKernel P L T (seedRun P hmd L T r) s := by
      simp_rw [seedRun_snoc]
      change (∫⁻ u, s.indicator 1 (seedRound P hmd L T (seedRun P hmd L T r) u) ∂volume) = _
      rw [← lintegral_map hI (measurable_seedRound P hmd L T _), seedRound_law,
        lintegral_indicator_one hs]
    calc
      _ = ∫⁻ r, s.indicator 1 (seedRun P hmd L (T + 1) r) ∂seedMeasure (T + 1) := by
        rw [← lintegral_map hI (measurable_seedRun P hmd L (T + 1)), lintegral_indicator_one hs]
      _ = ∫⁻ r, ∫⁻ u, s.indicator 1
          (seedRun P hmd L (T + 1) (seedSnoc r u)) ∂volume ∂seedMeasure T :=
        lintegral_seedMeasure_snoc (hI.comp (measurable_seedRun P hmd L (T + 1)))
      _ = ∫⁻ r, roundKernel P L T (seedRun P hmd L T r) s ∂seedMeasure T := by
        apply lintegral_congr
        exact hinner
      _ = ∫⁻ h, roundKernel P L T h s ∂runLaw P L T := by
        rw [← ih, lintegral_map ((roundKernel P L T).measurable_coe hs)
          (measurable_seedRun P hmd L T)]
      _ = _ := (runLaw_succ_apply P L T hs).symm

theorem seedRun_event_probability (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m)
    (T : ℕ) (E : Set (History d m T)) (hE : MeasurableSet E) :
    seedMeasure T {r | seedRun P hmd L T r ∈ E} = runLaw P L T E := by
  rw [← seedRun_map P hmd L T, Measure.map_apply (measurable_seedRun P hmd L T) hE]
  rfl

end MsetsPaper.Probability.PolicySeed
