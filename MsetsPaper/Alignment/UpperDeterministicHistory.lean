import MsetsPaper.Alignment.UpperAmbient

/-! Deterministic full interaction histories and the observed-history model.

The paper explicitly returns to deterministic adversaries at lines 1127--1133.
Such an adversary may use all previous probability vectors, full loss vectors,
and sampled actions: these are reconstructed from the observed action history
by recursion. This does not identify an enlarged filtration containing fresh
private signals with observed history. -/

noncomputable section
namespace MsetsPaper.Alignment.DeterministicHistory
open MeasureTheory ProbabilityTheory MsetsLower MsetsPaper.Upper
open MsetsPaper.Probability.AmbientHistory
open scoped ProbabilityTheory

variable {d m : ℕ} {Ω : Type*} [MeasurableSpace Ω]

@[reducible] def FullHistory (d m : ℕ) : ℕ → Type
  | 0 => Unit
  | t + 1 => FullHistory d m t × ((Action d m → ℝ) × ((Fin d → ℝ) × Action d m))

@[reducible] private def fullMeasurableSpace (d m : ℕ) :
    (t : ℕ) → MeasurableSpace (FullHistory d m t)
  | 0 => inferInstanceAs (MeasurableSpace Unit)
  | t + 1 => by
      letI := fullMeasurableSpace d m t
      change MeasurableSpace
        (FullHistory d m t × ((Action d m → ℝ) × ((Fin d → ℝ) × Action d m)))
      infer_instance

@[reducible] instance (d m t : ℕ) : MeasurableSpace (FullHistory d m t) :=
  fullMeasurableSpace d m t

/-- Arbitrary measurable deterministic choices based on the entire past. -/
structure Rules (d m : ℕ) where
  law : (t : ℕ) → FullHistory d m t → Action d m → ℝ
  loss : (t : ℕ) → FullHistory d m t → Fin d → ℝ
  measurable_law : ∀ t, Measurable (law t)
  measurable_loss : ∀ t, Measurable (loss t)

def fullHistory (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) : (t : ℕ) → Ω → FullHistory d m t
  | 0, _ => ()
  | t + 1, ω => (fullHistory X ell p t ω, (p t ω, (ell t ω, X t ω)))

def fullSigma (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (t : ℕ) : MeasurableSpace Ω :=
  (inferInstance : MeasurableSpace (FullHistory d m t)).comap (fullHistory X ell p t)

/-- The feedback component is not needed to reconstruct a deterministic past. -/
def reconstruct (rules : Rules d m) : (t : ℕ) → History d m t → FullHistory d m t
  | 0, _ => ()
  | t + 1, h =>
      let prev := reconstruct rules t h.1
      (prev, (rules.law t prev, (rules.loss t prev, h.2.1)))

theorem measurable_reconstruct (rules : Rules d m) :
    ∀ t, Measurable (reconstruct rules t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      exact (ih.comp measurable_fst).prodMk
        (((rules.measurable_law t).comp (ih.comp measurable_fst)).prodMk
          (((rules.measurable_loss t).comp (ih.comp measurable_fst)).prodMk
            measurable_snd.fst))

/-- Forget the unobserved loss coordinates, but retain the actual feedback. -/
def observe : (t : ℕ) → FullHistory d m t → History d m t
  | 0, _ => ()
  | t + 1, h =>
      (observe t h.1, (h.2.2.2, actionLoss h.2.2.2 h.2.2.1))

theorem measurable_observe : ∀ t, Measurable (observe (d := d) (m := m) t) := by
  intro t
  induction t with
  | zero => exact measurable_const
  | succ t ih =>
      have hx : Measurable (fun h : FullHistory d m (t + 1) ↦ h.2.2.2) :=
        measurable_snd.snd.snd
      have hl : Measurable (fun h : FullHistory d m (t + 1) ↦ h.2.2.1) :=
        measurable_snd.snd.fst
      have hy : Measurable (fun h : FullHistory d m (t + 1) ↦
          actionLoss h.2.2.2 h.2.2.1) := by
        classical
        unfold actionLoss
        apply Finset.measurable_sum
        intro i _
        have hmemb : MeasurableSet {h : FullHistory d m (t + 1) | i ∈ h.2.2.2.1} :=
          hx (show MeasurableSet {a : Action d m | i ∈ a.1} from
            MeasurableSet.of_discrete)
        exact Measurable.ite hmemb (hl.eval (a := i)) measurable_const
      exact (ih.comp measurable_fst).prodMk
        (hx.prodMk hy)

theorem observe_fullHistory (X : ℕ → Ω → Action d m)
    (ell : ℕ → Ω → Fin d → ℝ) (p : ℕ → Ω → Action d m → ℝ) :
    ∀ t ω, observe t (fullHistory X ell p t ω) = history X ell t ω := by
  intro t
  induction t with
  | zero => intro ω; rfl
  | succ t ih =>
      intro ω
      change (observe t (fullHistory X ell p t ω), _) = (history X ell t ω, _)
      rw [ih ω]
      rfl

theorem reconstruct_history (rules : Rules d m)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (T : ℕ)
    (hp : ∀ t < T, ∀ ω, p t ω = rules.law t (fullHistory X ell p t ω))
    (hell : ∀ t < T, ∀ ω, ell t ω = rules.loss t (fullHistory X ell p t ω)) :
    ∀ t ≤ T, ∀ ω, reconstruct rules t (history X ell t ω) = fullHistory X ell p t ω := by
  intro t
  induction t with
  | zero => intros; rfl
  | succ t ih =>
      intro ht ω
      change (reconstruct rules t (history X ell t ω),
        (rules.law t (reconstruct rules t (history X ell t ω)),
          (rules.loss t (reconstruct rules t (history X ell t ω)), X t ω))) =
        (fullHistory X ell p t ω, (p t ω, (ell t ω, X t ω)))
      rw [ih (by omega) ω, hp t (by omega) ω, hell t (by omega) ω]

/-- The two generated sigma-algebras are equal, not merely nested. -/
theorem fullSigma_eq_historySigma (rules : Rules d m)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (T : ℕ)
    (hp : ∀ t < T, ∀ ω, p t ω = rules.law t (fullHistory X ell p t ω))
    (hell : ∀ t < T, ∀ ω, ell t ω = rules.loss t (fullHistory X ell p t ω))
    (t : ℕ) (ht : t ≤ T) : fullSigma X ell p t = historySigma X ell t := by
  apply le_antisymm
  · have he : fullHistory X ell p t = reconstruct rules t ∘ history X ell t :=
      funext (fun ω ↦ (reconstruct_history rules X ell p T hp hell t ht ω).symm)
    unfold fullSigma
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_reconstruct rules t).comap_le
  · have he : history X ell t = observe t ∘ fullHistory X ell p t :=
      funext (fun ω ↦ (observe_fullHistory X ell p t ω).symm)
    unfold historySigma
    rw [he, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_observe t).comap_le

/-- These are precisely the two predictability premises of the upper interface. -/
theorem observed_predictability (rules : Rules d m)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (T : ℕ)
    (hp : ∀ t < T, ∀ ω, p t ω = rules.law t (fullHistory X ell p t ω))
    (hell : ∀ t < T, ∀ ω, ell t ω = rules.loss t (fullHistory X ell p t ω)) :
    (∀ t < T, Measurable[historySigma X ell t] (ell t)) ∧
    (∀ t < T, Measurable[historySigma X ell t] (p t)) := by
  constructor
  · intro t ht
    have he : ell t = rules.loss t ∘ reconstruct rules t ∘ history X ell t := by
      funext ω
      simpa only [Function.comp_apply, reconstruct_history rules X ell p T hp hell t ht.le ω]
        using hell t ht ω
    rw [he]
    exact ((rules.measurable_loss t).comp (measurable_reconstruct rules t)).comp
      (comap_measurable (history X ell t))
  · intro t ht
    have he : p t = rules.law t ∘ reconstruct rules t ∘ history X ell t := by
      funext ω
      simpa only [Function.comp_apply, reconstruct_history rules X ell p T hp hell t ht.le ω]
        using hp t ht ω
    rw [he]
    exact ((rules.measurable_law t).comp (measurable_reconstruct rules t)).comp
      (comap_measurable (history X ell t))

/-- Predictability in generated full history already yields measurable
deterministic rules, by Doob--Dynkin; no factorization premise is assumed. -/
theorem exists_rules_of_full_predictability
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ) (T : ℕ)
    (hp : ∀ t < T, Measurable[fullSigma X ell p t] (p t))
    (hell : ∀ t < T, Measurable[fullSigma X ell p t] (ell t)) :
    ∃ rules : Rules d m,
      (∀ t < T, ∀ ω, p t ω = rules.law t (fullHistory X ell p t ω)) ∧
      (∀ t < T, ∀ ω, ell t ω = rules.loss t (fullHistory X ell p t ω)) := by
  classical
  have hpl (t : ℕ) : ∃ g : FullHistory d m t → Action d m → ℝ,
      Measurable g ∧ (t < T → p t = g ∘ fullHistory X ell p t) := by
    by_cases ht : t < T
    · obtain ⟨g, hg, he⟩ := (hp t ht).exists_eq_measurable_comp
      exact ⟨g, hg, fun _ ↦ he⟩
    · exact ⟨fun _ ↦ 0, measurable_const, fun h ↦ (ht h).elim⟩
  have hll (t : ℕ) : ∃ g : FullHistory d m t → Fin d → ℝ,
      Measurable g ∧ (t < T → ell t = g ∘ fullHistory X ell p t) := by
    by_cases ht : t < T
    · obtain ⟨g, hg, he⟩ := (hell t ht).exists_eq_measurable_comp
      exact ⟨g, hg, fun _ ↦ he⟩
    · exact ⟨fun _ ↦ 0, measurable_const, fun h ↦ (ht h).elim⟩
  choose gp hgp hep using hpl
  choose gl hgl hel using hll
  exact ⟨⟨gp, gl, hgp, hgl⟩,
    fun t ht ω ↦ congrFun (hep t ht) ω,
    fun t ht ω ↦ congrFun (hel t ht) ω⟩

/-- T1 also takes deterministic rules on the full interaction history; sampling
is conditioned on that full history. No observed-history predictability is
assumed: it is derived by the reconstruction theorem above. -/
theorem upper_main_regret_full_history
    (μ : Measure Ω) [IsProbabilityMeasure μ] (rules : Rules d m)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hX : ∀ t < T, Measurable (X t))
    (hp : ∀ t < T, ∀ ω, p t ω = rules.law t (fullHistory X ell p t ω))
    (hell : ∀ t < T, ∀ ω, ell t ω = rules.loss t (fullHistory X ell p t ω))
    (hnorm : ∀ t < T, ∀ᵐ ω ∂μ, ∀ a : Action d m, |actionLoss a (ell t ω)| ≤ 1)
    (halgorithm : ∀ t < T, ∀ᵐ ω ∂μ,
      p t ω = weightedLaw (m := m)
        (ellipsoidAlgorithmParameters
          (mainLearningRate d T (Nat.choose d m) delta) T t (history X ell t ω)))
    (hsample : ∀ t < T, ∀ a : Action d m,
      μ⟦(X t) ⁻¹' {a} | fullSigma X ell p t⟧ =ᵐ[μ] fun ω ↦ p t ω a) :
    1 - delta ≤ μ.real {ω | regret X ell T ω ≤
      160 * Real.sqrt ((d : ℝ) * T *
        (Real.log (Nat.choose d m) + Real.log (1 / delta)))} := by
  obtain ⟨hell_obs, hp_obs⟩ := observed_predictability rules X ell p T hp hell
  apply MsetsPaper.Alignment.upper_main_regret_ambient_of_conditional_expectations
    μ X ell p hmpos hmtop T hT hdelta0 hdelta1 hX hell_obs hp_obs hnorm halgorithm
  intro t ht a
  simpa only [fullSigma_eq_historySigma rules X ell p T hp hell t ht.le] using hsample t ht a

/-- A direct input-model interface using predictability in the generated full
interaction history. The measurable rules and observed-history premises are
both consequences of these hypotheses. -/
theorem upper_main_regret_full_predictability
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ)
    (p : ℕ → Ω → Action d m → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {delta : ℝ} (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hX : ∀ t < T, Measurable (X t))
    (hp : ∀ t < T, Measurable[fullSigma X ell p t] (p t))
    (hell : ∀ t < T, Measurable[fullSigma X ell p t] (ell t))
    (hnorm : ∀ t < T, ∀ᵐ ω ∂μ, ∀ a : Action d m, |actionLoss a (ell t ω)| ≤ 1)
    (halgorithm : ∀ t < T, ∀ᵐ ω ∂μ,
      p t ω = weightedLaw (m := m)
        (ellipsoidAlgorithmParameters
          (mainLearningRate d T (Nat.choose d m) delta) T t (history X ell t ω)))
    (hsample : ∀ t < T, ∀ a : Action d m,
      μ⟦(X t) ⁻¹' {a} | fullSigma X ell p t⟧ =ᵐ[μ] fun ω ↦ p t ω a) :
    1 - delta ≤ μ.real {ω | regret X ell T ω ≤
      160 * Real.sqrt ((d : ℝ) * T *
        (Real.log (Nat.choose d m) + Real.log (1 / delta)))} := by
  obtain ⟨rules, hpr, hlr⟩ := exists_rules_of_full_predictability X ell p T hp hell
  exact upper_main_regret_full_history μ rules X ell p hmpos hmtop T hT
    hdelta0 hdelta1 hX hpr hlr hnorm halgorithm hsample

end MsetsPaper.Alignment.DeterministicHistory
