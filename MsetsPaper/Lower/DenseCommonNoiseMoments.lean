import MsetsPaper.Lower.DenseCommonNoiseLaw
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Comparator mean under the actual independent sign/noise table

This develops the manuscript's calculation `E comparatorScore = m*T/3`
from the concrete product law, rather than postulating that expectation.
-/

namespace MsetsPaper.Lower.DenseCommonNoise

open MsetsLower MsetsLower.Feedback MsetsLower.Lower MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

@[simp] theorem bitMeasure_real_singleton (b : Bool) :
    bitMeasure.real {b} = (1 : ℝ) / 2 := by
  rw [measureReal_def, bitMeasure, Measure.uniformOfFinset_apply_singleton]
  norm_num

theorem integral_bitMeasure (f : Bool → ℝ) :
    ∫ b, f b ∂bitMeasure = (f false + f true) / 2 := by
  rw [integral_fintype Integrable.of_finite]
  simp only [bitMeasure_real_singleton, smul_eq_mul, Fintype.sum_bool]
  ring

theorem integral_max_two_signs :
    ∫ b : Bool × Bool, max (signValue b.1) (signValue b.2) ∂bitMeasure.prod bitMeasure =
      (1 : ℝ) / 2 := by
  rw [integral_prod _ Integrable.of_finite]
  simp_rw [integral_bitMeasure]
  norm_num [signValue]

/-- Any two distinct actual sign coordinates have the independent fair-bit law. -/
theorem map_two_signs {m : ℕ} (i j : Fin (2 * m)) (hij : i ≠ j) :
    (signsMeasure m).map (fun U => (U i, U j)) = bitMeasure.prod bitMeasure := by
  have h := ((signs_coordinates_independent m).indepFun hij).map_prod_eq_prod_map_map
    (measurable_pi_apply i).aemeasurable (measurable_pi_apply j).aemeasurable
  simpa only [map_signs_coordinate] using h

theorem integral_max_sign_coordinates {m : ℕ} (i j : Fin (2 * m)) (hij : i ≠ j) :
    ∫ U : Signs m, max (signValue (U i)) (signValue (U j)) ∂signsMeasure m = (1 : ℝ) / 2 := by
  have hmeas : Measurable (fun U : Signs m => (U i, U j)) :=
    (measurable_pi_apply i).prodMk (measurable_pi_apply j)
  calc
    _ = ∫ b : Bool × Bool, max (signValue b.1) (signValue b.2)
        ∂(signsMeasure m).map (fun U => (U i, U j)) := by
      rw [integral_map hmeas.aemeasurable (measurable_of_finite _).aestronglyMeasurable]
    _ = (1 : ℝ) / 2 := by rw [map_two_signs i j hij]; exact integral_max_two_signs

theorem signVector_pairIndex {d m : ℕ} (h2m : 2 * m ≤ d) (U : Signs m)
    (j : Fin m) (b : Bool) :
    signVector U (pairIndex h2m j b) = signValue (U (pairIndex (le_refl (2 * m)) j b)) := by
  have hidx : (pairIndex h2m j b).val < 2 * m := by
    cases b <;> simp [pairIndex] <;> omega
  simp only [signVector, dif_pos hidx]
  rfl

theorem integral_pairedSignScore {d m : ℕ} (h2m : 2 * m ≤ d) :
    ∫ U : Signs m, pairedSignScore h2m (signVector U) ∂signsMeasure m = (m : ℝ) / 2 := by
  unfold pairedSignScore
  rw [integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
  have hterm : ∀ j : Fin m,
      (∫ U : Signs m,
        max (signVector U (pairIndex h2m j false)) (signVector U (pairIndex h2m j true))
          ∂signsMeasure m) = (1 : ℝ) / 2 := by
    intro j
    simp only [signVector_pairIndex]
    apply integral_max_sign_coordinates
    intro heq
    have hv : 2 * j.val = 2 * j.val + 1 := by
      simpa [pairIndex] using congrArg Fin.val heq
    omega
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem integral_shape_noise_coordinate {T : ℕ} (t : Fin T) :
    ∫ Z : Fin T → Noise, shape (Z t).val ∂noiseTableMeasure T = (2 / 3 : ℝ) := by
  calc
    _ = ∫ z : Noise, shape z.val ∂(noiseTableMeasure T).map (fun Z => Z t) := by
      rw [integral_map (measurable_pi_apply t).aemeasurable
        (measurable_shape.comp measurable_subtype_coe).aestronglyMeasurable]
    _ = (2 / 3 : ℝ) := by rw [map_noise_coordinate]; exact integral_shape_noiseMeasure

/-- The complete fresh-noise shape sum at horizon `T` has mean `2T/3`. -/
theorem integral_shapeSum {m T : ℕ} (U : Signs m) :
    ∫ Z : Fin T → Noise, shapeSum (U, Z) T ∂noiseTableMeasure T = (2 / 3 : ℝ) * T := by
  unfold shapeSum
  rw [integral_finsetSum]
  · have hterm : ∀ r ∈ Finset.range T,
        (∫ Z : Fin T → Noise, shape (tableNoise (U, Z) r) ∂noiseTableMeasure T) =
          (2 / 3 : ℝ) := by
      intro r hr
      have hrT := Finset.mem_range.mp hr
      simp only [tableNoise, dif_pos hrT]
      exact integral_shape_noise_coordinate ⟨r, hrT⟩
    rw [Finset.sum_congr rfl hterm]
    simp
    ring
  · intro r hr
    apply Integrable.of_mem_Icc (0 : ℝ) 1
    · exact (measurable_shape.comp
        ((measurable_tableNoise r).comp (measurable_const.prodMk measurable_id))).aemeasurable
    · exact ae_of_all _ fun Z => shape_mem_Icc (tableNoise_mem_Icc (U, Z) r)

/-- The expected comparator score on the very table law used in the construction. -/
theorem integral_comparatorScore {d m T : ℕ} (h2m : 2 * m ≤ d) :
    ∫ xi : Table m T, pairedSignScore h2m (signVector xi.1) * shapeSum xi T
      ∂tableMeasure m T = (m : ℝ) * T / 3 := by
  let U₀ : Signs m := fun _ => false
  change (∫ xi : Signs m × (Fin T → Noise),
      pairedSignScore h2m (signVector xi.1) * (fun Z => shapeSum (U₀, Z) T) xi.2
        ∂(signsMeasure m).prod (noiseTableMeasure T)) = _
  calc
    _ = (∫ U : Signs m, pairedSignScore h2m (signVector U) ∂signsMeasure m) *
        (∫ Z : Fin T → Noise, shapeSum (U₀, Z) T ∂noiseTableMeasure T) :=
      integral_prod_mul (μ := signsMeasure m) (ν := noiseTableMeasure T)
        (fun U : Signs m => pairedSignScore h2m (signVector U))
        (fun Z : Fin T → Noise => shapeSum (U₀, Z) T)
    _ = _ := by rw [integral_pairedSignScore, integral_shapeSum]; ring

end

end MsetsPaper.Lower.DenseCommonNoise
