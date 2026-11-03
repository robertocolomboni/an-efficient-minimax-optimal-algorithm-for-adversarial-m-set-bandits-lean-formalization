import MsetsPaper.Upper.RoundArena
import MsetsPaper.Upper.RoundSamplingLaw

/-! # The fully initialized streaming algorithm and its verified resource bounds

The program stores a current d-coordinate parameter vector. Its uniforms
and observed scalar losses are online inputs; no horizon-length list is
allocated by the algorithm. The semantic history below is a proof object,
not a retained component of the executable state.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver ResourcePrograms MsetsLower MsetsLower.History
open scoped unitInterval

noncomputable section

variable {d m : ℕ}

def initialThetaResource (d : ℕ) : ResourceRun (StoredVector d) :=
  let zeros := resourceZeros d
  ⟨⟨zeros.value, by simp [zeros, resourceZeros_values]⟩, zeros.work + 1, zeros.allocated + 1⟩

theorem initialThetaResource_values (d : ℕ) :
    storedVector (initialThetaResource d).value = (0 : Fin d → ℝ) := by
  ext i
  simp [initialThetaResource, resourceZeros_values, storedVector, cachedRealVector]

theorem initialThetaResource_counts (d : ℕ) :
    (initialThetaResource d).work = 2 * d + 2 ∧
    (initialThetaResource d).allocated = 2 * d + 2 := by
  have h := resourceZeros_counts d
  dsimp only [initialThetaResource]
  constructor <;> omega

def algorithmArena (d m T : ℕ) (delta : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) : ResourceRun (StoredVector d) × ℕ :=
  let setup := learningRateResource d m T delta
  let initial := initialThetaResource d
  let run := roundsArena initial.value setup.value.2 T hmd u Y T
  (⟨run.1.value, setup.work + initial.work + run.1.work + 3,
      setup.allocated + initial.allocated + run.1.allocated + 3⟩,
    max (setup.allocated + initial.allocated + 10) (run.2 + 10))

def algorithmSpace (d m : ℕ) : ℕ := 9 * m + 5 * d + roundArenaSpace d m + 60

theorem algorithmArena_peak (d m T : ℕ) (delta : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) :
    (algorithmArena d m T delta hmd u Y).2 ≤ algorithmSpace d m := by
  have hs := (learningRateResource_bounds d m T delta).2
  have hi := (initialThetaResource_counts d).2
  have hr := roundsArena_peak (initialThetaResource d).value
    (learningRateResource d m T delta).value.2 T hmd u Y T
  dsimp only [algorithmArena, algorithmSpace]
  apply max_le <;> omega

theorem algorithmArena_work (d m T : ℕ) (delta : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) :
    (algorithmArena d m T delta hmd u Y).1.work ≤ 7 * m + 2 * d + 26 +
      T * (roundWorkBase d m +
        projectionOracleBudget d (mainLearningRate d T (Nat.choose d m) delta) T *
          (searchStepBudget d m + 6) + 3) := by
  have hs := (learningRateResource_bounds d m T delta).1
  have hi := (initialThetaResource_counts d).1
  have hr := roundsArena_work (initialThetaResource d).value
    (learningRateResource d m T delta).value.2 T hmd u Y T
  rw [learningRateResource_values] at hr
  dsimp only [algorithmArena]
  rw [learningRateResource_values]
  dsimp only [Prod.snd] at hr ⊢
  omega

/-- Literal P1 total running-time bound, including the binomial and learning-
rate setup. The displayed factor is a polynomial in d,m,log T. -/
theorem algorithmArena_polynomial_work (d m T : ℕ) (delta : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) (hT : 1 ≤ T)
    (hdelta0 : 0 < delta) (hdelta1 : delta ≤ 1)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) :
    ((algorithmArena d m T delta (by omega) u Y).1.work : ℝ) ≤
      (T : ℝ) * (roundTimePolynomial d m T + 7 * (m : ℝ) + 2 * d + 29) := by
  have hd : 1 ≤ d := by omega
  have hTR : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hK : (2 : ℝ) ≤ Nat.choose d m := by exact_mod_cast action_count_ge_two hm hmtop
  have hw : ((algorithmArena d m T delta (by omega) u Y).1.work : ℝ) ≤
      7 * (m : ℝ) + 2 * d + 26 + (T : ℝ) * ((roundWorkBase d m : ℝ) +
        (projectionOracleBudget d (mainLearningRate d T (Nat.choose d m) delta) T : ℝ) *
          ((searchStepBudget d m : ℝ) + 6) + 3) := by
    exact_mod_cast algorithmArena_work d m T delta (by omega) u Y
  have hb := projectionOracleBudget_polynomial_bound d hd T (Nat.choose d m) delta
    hTR hK hdelta0 hdelta1
  have hb' := mul_le_mul_of_nonneg_right hb
    (by positivity : (0 : ℝ) ≤ (searchStepBudget d m : ℝ) + 6)
  have ht := mul_le_mul_of_nonneg_left hb' (Nat.cast_nonneg T : (0 : ℝ) ≤ T)
  have hi := mul_le_mul_of_nonneg_right hTR
    (by positivity : (0 : ℝ) ≤ 7 * (m : ℝ) + 2 * d + 26)
  unfold roundTimePolynomial
  nlinarith

theorem streamIterate_succ_right {State : Type*} (step : ℕ → State → State)
    (n t : ℕ) (state : State) :
    streamIterate step (n + 1) t state = step (t + n) (streamIterate step n t state) := by
  induction n generalizing t state with
  | zero => simp [streamIterate]
  | succ n ih =>
    change streamIterate step (n + 1) (t + 1) (step t state) =
      step (t + (n + 1)) (streamIterate step n (t + 1) (step t state))
    rw [ih]
    congr 1 <;> omega

def roundParameter (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) : ℕ → StoredVector d
  | 0 => (initialThetaResource d).value
  | t + 1 => (roundArena (roundParameter eta T hmd u Y t) eta T hmd (u t) (Y t)).1.value

def roundHistory (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) : (t : ℕ) → History d m t
  | 0 => ()
  | t + 1 => (roundHistory eta T hmd u Y t).snoc
    (sampleResource (roundParameter eta T hmd u Y t) hmd (u t)).value.action (Y t)

theorem roundParameter_eq_algorithmParameters (eta T : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) (t : ℕ) :
    storedVector (roundParameter eta T (by omega : m ≤ d) u Y t) =
      algorithmParameters (fun theta => ellipsoidProjection (m := m) theta eta T) eta t
        (roundHistory eta T (by omega : m ≤ d) u Y t) := by
  induction t with
  | zero => exact initialThetaResource_values d
  | succ t ih =>
    change storedVector (roundArena _ eta T _ (u t) (Y t)).1.value = _
    rw [roundArena_values _ eta T (Y t) hm hmtop (u t)]
    change ellipsoidProjection (unprojectedFromFeedback _ eta _ _) eta T =
      ellipsoidProjection (unprojectedFromFeedback _ eta _ _) eta T
    rw [ih]

theorem roundsArena_initial_values (eta T : ℝ) (hmd : m ≤ d)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) (n : ℕ) :
    (roundsArena (initialThetaResource d).value eta T hmd u Y n).1.value =
      roundParameter eta T hmd u Y n := by
  rw [roundsArena_values]
  induction n with
  | zero => rfl
  | succ n ih => rw [streamIterate_succ_right, Nat.zero_add, ih]; rfl

/-- The actual initialized resource program is the parameter algorithm from
the probability/regret proof, on its own generated observable history. -/
theorem algorithmArena_parameters (d m T : ℕ) (delta : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    (u : ℕ → Fin d → unitInterval) (Y : ℕ → ℝ) :
    let eta := mainLearningRate d T (Nat.choose d m) delta
    storedVector (algorithmArena d m T delta (by omega) u Y).1.value =
      algorithmParameters (fun theta => ellipsoidProjection (m := m) theta eta T) eta T
        (roundHistory eta T (by omega : m ≤ d) u Y T) := by
  dsimp only
  simp only [algorithmArena, learningRateResource_values]
  rw [roundsArena_initial_values]
  exact roundParameter_eq_algorithmParameters _ T hm hmtop u Y T

end

end MsetsPaper.Upper.RoundProgram
