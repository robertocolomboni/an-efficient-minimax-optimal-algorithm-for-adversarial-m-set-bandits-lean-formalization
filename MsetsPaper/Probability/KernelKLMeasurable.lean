import MsetsPaper.Probability.BinaryKL
import Mathlib.Probability.Kernel.RadonNikodym

namespace MsetsPaper.Probability
open MeasureTheory ProbabilityTheory InformationTheory
open scoped ENNReal

/-- Native KL is measurable for dominated finite kernels with countably
generated target. The joint kernel Radon--Nikodym version is essential. -/
theorem measurable_klDiv_kernel_of_ac {Ω X : Type*} [MeasurableSpace Ω]
    [MeasurableSpace X] [MeasurableSpace.CountableOrCountablyGenerated Ω X]
    (κ η : Kernel Ω X) [IsFiniteKernel κ] [IsFiniteKernel η]
    (hac : ∀ r, κ r ≪ η r) : Measurable (fun r => klDiv (κ r) (η r)) := by
  have hm : Measurable (fun x : Ω × X =>
      ENNReal.ofReal (klFun ((Kernel.rnDeriv κ η x.1 x.2).toReal))) :=
    (measurable_klFun.comp (Kernel.measurable_rnDeriv κ η).ennreal_toReal).ennreal_ofReal
  have heq (r : Ω) : klDiv (κ r) (η r) =
      ∫⁻ x, ENNReal.ofReal (klFun ((Kernel.rnDeriv κ η r x).toReal)) ∂η r := by
    rw [klDiv_eq_lintegral_klFun_of_ac (hac r)]
    apply lintegral_congr_ae
    filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := r)] with x hx
    rw [hx]
  simp_rw [heq]
  exact hm.lintegral_kernel_prod_right

end MsetsPaper.Probability
