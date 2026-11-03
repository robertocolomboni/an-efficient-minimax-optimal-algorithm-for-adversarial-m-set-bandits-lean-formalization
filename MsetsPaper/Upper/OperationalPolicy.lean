import MsetsPaper.Upper.AlgorithmResource
import MsetsPaper.Upper.Algorithm

/-! # Exact policy/run-law identity for the operational implementation

The kernels below are defined by the actual sampler's uniform-input
pushforward. Their equality with the mathematical weighted kernels is proved.
The history-indexed stored vectors are semantic descriptions of the current
state, not a runtime reconstruction: AlgorithmResource proves that the
streaming parameter program maintains exactly these values.
-/

namespace MsetsPaper.Upper.RoundProgram

open SchurSolver ESPSampling MsetsLower MsetsLower.History
open MeasureTheory ProbabilityTheory MsetsPaper.Probability

noncomputable section

variable {d m : ℕ}

def operationalKernel {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → StoredVector d) (htheta : Measurable (fun w => storedVector (theta w)))
    (hmd : m ≤ d) : Kernel Ω (Action d m) where
  toFun w := (uniformCube (Fin d)).map (fun u => (sampleResource (theta w) hmd u).value.action)
  measurable' := by
    simp_rw [sampleResource_map]
    exact measurable_finiteAtomicMeasure (fun w => weightedLaw (storedVector (theta w)))
      (measurable_weightedLaw _ htheta) id

theorem operationalKernel_eq {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → StoredVector d) (htheta : Measurable (fun w => storedVector (theta w)))
    (hmd : m ≤ d) :
    operationalKernel theta htheta hmd =
      weightedActionKernel (m := m) (fun w => storedVector (theta w)) htheta := by
  apply Kernel.ext
  intro w
  exact sampleResource_map_weightedActionKernel theta htheta hmd w

theorem operationalKernel_isMarkov {Ω : Type*} [MeasurableSpace Ω]
    (theta : Ω → StoredVector d) (htheta : Measurable (fun w => storedVector (theta w)))
    (hmd : m ≤ d) : IsMarkovKernel (operationalKernel theta htheta hmd) := by
  rw [operationalKernel_eq]
  exact weightedActionKernel_isMarkov _ htheta hmd

def storedMainParameters (T : ℕ) (delta : ℝ) (t : ℕ) (h : History d m t) : StoredVector d :=
  ⟨List.ofFn (ellipsoidAlgorithmParameters
    (mainLearningRate d T (Nat.choose d m) delta) T t h), List.length_ofFn⟩

theorem storedMainParameters_values (T : ℕ) (delta : ℝ) (t : ℕ) (h : History d m t) :
    storedVector (storedMainParameters T delta t h) =
      ellipsoidAlgorithmParameters (mainLearningRate d T (Nat.choose d m) delta) T t h := by
  exact cachedRealVector_ofFn _

theorem measurable_storedMainParameters (T : ℕ) (delta : ℝ) (t : ℕ) :
    Measurable (fun h : History d m t => storedVector (storedMainParameters T delta t h)) := by
  simp only [storedMainParameters_values]
  exact measurable_ellipsoidAlgorithmParameters _ T t

def operationalMainPolicy (T : ℕ) (delta : ℝ) (hmd : m ≤ d) : Policy d m where
  kernel t := operationalKernel (storedMainParameters T delta t)
    (measurable_storedMainParameters T delta t) hmd
  isMarkov t := operationalKernel_isMarkov _ _ hmd

theorem policy_eq_of_kernel_eq (P Q : Policy d m) (h : P.kernel = Q.kernel) : P = Q := by
  cases P
  cases Q
  cases h
  rfl

theorem operationalMainPolicy_eq_main (T : ℕ) (delta : ℝ) (hmd : m ≤ d) :
    operationalMainPolicy T delta hmd = mainAlgorithm T delta hmd := by
  apply policy_eq_of_kernel_eq
  funext t
  apply Kernel.ext
  intro h
  change (uniformCube (Fin d)).map
    (fun u => (sampleResource (storedMainParameters T delta t h) hmd u).value.action) = _
  rw [sampleResource_map, storedMainParameters_values]
  rfl

/-- This applies to every signed, nonanticipating adversary in the upper
theorem, not just to oblivious or item-wise nonnegative losses. -/
theorem operationalMain_runLaw (T : ℕ) (delta : ℝ) (hmd : m ≤ d)
    (L : SignedLossProcess d m) (t : ℕ) :
    signedRunLaw (operationalMainPolicy T delta hmd) L t =
      signedRunLaw (mainAlgorithm T delta hmd) L t := by
  rw [operationalMainPolicy_eq_main]

end

end MsetsPaper.Upper.RoundProgram
