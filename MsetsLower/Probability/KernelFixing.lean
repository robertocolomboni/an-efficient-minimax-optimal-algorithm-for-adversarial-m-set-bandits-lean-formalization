import MsetsLower.Probability.FixingTable
import Mathlib.Probability.Kernel.Composition.MeasureComp

set_option linter.style.header false

/-!
# Fixing a parameter in a measurable family of experiments

The learner's conditional law generally depends on the auxiliary loss table.
Consequently the joint experiment is a composition of the table measure with
a Markov kernel, rather than an independent product.  This is the exact
Tonelli step needed to fix a deterministic table in that setting.
-/

namespace MsetsLower.Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal ProbabilityTheory

noncomputable section

/-- If a measurable family of probability experiments has average event
probability at least `p`, one deterministic parameter has event probability
at least `p`. -/
theorem exists_fixed_kernel
    {Xi Omega : Type*} [MeasurableSpace Xi] [MeasurableSpace Omega]
    (mu : Measure Xi) [IsProbabilityMeasure mu]
    (K : Kernel Xi Omega) [IsMarkovKernel K]
    {E : Set Omega} (hE : MeasurableSet E) {p : ℝ≥0∞}
    (hp : p ≤ (K ∘ₘ mu) E) :
    ∃ xi : Xi, p ≤ K xi E := by
  have hfinite : (∫⁻ xi, K xi E ∂mu) ≠ ∞ := by
    rw [← Measure.bind_apply hE (Kernel.aemeasurable K)]
    exact ne_of_lt (measure_lt_top (K ∘ₘ mu) E)
  obtain ⟨xi, hxi⟩ := exists_lintegral_le hfinite
  exact ⟨xi, hp.trans ((Measure.bind_apply hE (Kernel.aemeasurable K)).le.trans hxi)⟩

/-- Real-probability version of `exists_fixed_kernel`. -/
theorem exists_fixed_kernel_real
    {Xi Omega : Type*} [MeasurableSpace Xi] [MeasurableSpace Omega]
    (mu : Measure Xi) [IsProbabilityMeasure mu]
    (K : Kernel Xi Omega) [IsMarkovKernel K]
    {E : Set Omega} (hE : MeasurableSet E) {p : Real}
    (hp : p ≤ (K ∘ₘ mu).real E) :
    ∃ xi : Xi, p ≤ (K xi).real E := by
  have hpENN : ENNReal.ofReal p ≤ (K ∘ₘ mu) E := by
    apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
    simpa [measureReal_def] using hp
  obtain ⟨xi, hxi⟩ := exists_fixed_kernel mu K hE hpENN
  refine ⟨xi, ?_⟩
  change p ≤ ENNReal.toReal ((K xi) E)
  exact (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).1 hxi

end

end MsetsLower.Probability

#print axioms MsetsLower.Probability.exists_fixed_kernel
#print axioms MsetsLower.Probability.exists_fixed_kernel_real
