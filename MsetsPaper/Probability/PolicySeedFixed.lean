import MsetsPaper.Probability.PolicySeed
import MsetsPaper.Probability.DeterministicRun

/-! # A fixed master seed really gives a deterministic policy -/

noncomputable section
open MeasureTheory ProbabilityTheory MsetsLower MsetsLower.History
open scoped ENNReal

namespace MsetsPaper.Probability.PolicySeed

variable {d m T : ℕ}

def seedAt (r : Seeds T) (t : ℕ) : UniformSeed :=
  if ht : t < T then r ⟨t, ht⟩ else 0

theorem measurable_seedAt (t : ℕ) : Measurable (fun r : Seeds T ↦ seedAt r t) := by
  unfold seedAt
  split_ifs with ht
  · exact measurable_pi_apply (⟨t, ht⟩ : Fin T)
  · exact measurable_const

def fixedChoose (P : Policy d m) (hmd : m ≤ d) (r : Seeds T)
    (t : ℕ) (h : History d m t) : MSetAction d m :=
  selector P hmd t h (seedAt r t)

theorem measurable_fixedChoose (P : Policy d m) (hmd : m ≤ d) (r : Seeds T) (t : ℕ) :
    Measurable (fixedChoose P hmd r t) :=
  (measurable_selector P hmd t).of_uncurry_right

theorem measurable_fixedChoose_joint (P : Policy d m) (hmd : m ≤ d) (t : ℕ) :
    Measurable (fun x : Seeds T × History d m t ↦ fixedChoose P hmd x.1 t x.2) :=
  (measurable_selector P hmd t).comp
    (measurable_snd.prodMk ((measurable_seedAt t).comp measurable_fst))

def fixedPolicy (P : Policy d m) (hmd : m ≤ d) (r : Seeds T) : Policy d m :=
  Policy.deterministic (fixedChoose P hmd r) (measurable_fixedChoose P hmd r)

def seedPrefix (r : Seeds T) (t : ℕ) (ht : t ≤ T) : Seeds t :=
  fun i ↦ r ⟨i.val, lt_of_lt_of_le i.isLt ht⟩

theorem deterministicRun_fixedChoose_eq_seedRun
    (P : Policy d m) (hmd : m ≤ d) (r : Seeds T) (L : LossProcess d m) :
    ∀ t (ht : t ≤ T), deterministicRun (fixedChoose P hmd r) L t =
      seedRun P hmd L t (seedPrefix r t ht) := by
  intro t
  induction t with
  | zero => intro ht; rfl
  | succ t ih =>
    intro ht
    have htt : t < T := by omega
    have hp : t ≤ T := by omega
    simp only [deterministicRun, ih hp, fixedChoose, seedAt, dif_pos htt, seedRun]
    rfl

theorem fixedPolicy_runLaw (P : Policy d m) (hmd : m ≤ d) (r : Seeds T) (L : LossProcess d m) :
    runLaw (fixedPolicy P hmd r) L T = Measure.dirac (seedRun P hmd L T r) := by
  rw [fixedPolicy, runLaw_deterministic_eq_dirac,
    deterministicRun_fixedChoose_eq_seedRun P hmd r L T le_rfl]
  rfl

/-- Integrating deterministic private-seed policies reconstructs the exact
original policy law for every measurable event and every loss environment. -/
theorem fixedPolicy_event_average (P : Policy d m) (hmd : m ≤ d) (L : LossProcess d m)
    (E : Set (History d m T)) (hE : MeasurableSet E) :
    (∫⁻ r, runLaw (fixedPolicy P hmd r) L T E ∂seedMeasure T) = runLaw P L T E := by
  simp_rw [fixedPolicy_runLaw, Measure.dirac_apply' _ hE]
  have hI : Measurable (E.indicator (1 : History d m T → ℝ≥0∞)) :=
    measurable_const.indicator hE
  rw [← lintegral_map hI (measurable_seedRun P hmd L T),
    seedRun_map, lintegral_indicator_one hE]

end MsetsPaper.Probability.PolicySeed
