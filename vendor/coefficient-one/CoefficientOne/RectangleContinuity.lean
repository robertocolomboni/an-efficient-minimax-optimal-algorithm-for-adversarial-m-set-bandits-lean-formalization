import CoefficientOne.RectangleDeterminants
import CoefficientOne.RectangleComplement

/-!
# Rectangular dual Jacobi–Trudi at nonnegative letters

Add t>0 to every letter, apply the proved positive-alphabet identity, and
let t tend to zero from above. Both sides are polynomial evaluations and hence
continuous. This also covers letters set to zero during deletion identities.
-/

noncomputable section

namespace CoefficientOne.RectangleContinuity

open Finset Filter Topology RectangleDeterminants

variable {N : ℕ}

theorem elementaryInt_continuous (d : ℤ) :
    Continuous (fun a : Fin N → ℝ => elementaryInt a d) := by
  by_cases hd : 0 ≤ d
  · simp only [elementaryInt, if_pos hd]
    simpa only [eval_esymm_eq_elementarySum] using
      MvPolynomial.continuous_eval (MvPolynomial.esymm (Fin N) ℝ d.toNat)
  · simp only [elementaryInt, if_neg hd]
    exact continuous_const

theorem elementaryDet_continuous (q k : ℕ) :
    Continuous (fun a : Fin N → ℝ => elementaryDet a q k) := by
  apply Continuous.matrix_det
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  exact elementaryInt_continuous ((k : ℤ) - (i.val : ℤ) + (j.val : ℤ))

theorem rectangleSchur_continuous (q k : ℕ) :
    Continuous (fun a : Fin N → ℝ => rectangleSchur a q k) :=
  RectangleComplement.schurValue_continuous (rectangleShape N q k)

def positiveApproximation (a : Fin N → ℝ) (t : ℝ) : Fin N → ℝ :=
  fun i => a i + t

theorem positiveApproximation_pos (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (t : ℝ) (ht : 0 < t) : ∀ i, 0 < positiveApproximation a t i := by
  intro i
  exact add_pos_of_nonneg_of_pos (ha i) ht

theorem positiveApproximation_tendsto (a : Fin N → ℝ) :
    Tendsto (positiveApproximation a) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have hc : Continuous (positiveApproximation a) := by
    unfold positiveApproximation
    fun_prop
  have hzero : positiveApproximation a 0 = a := by
    funext i
    simp [positiveApproximation]
  have ht : Tendsto (positiveApproximation a) (𝓝[>] (0 : ℝ))
      (𝓝 (positiveApproximation a 0)) :=
    (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  rw [hzero] at ht
  exact ht

/-- Rectangular dual Jacobi–Trudi with zero letters allowed. -/
theorem rectangleSchur_eq_elementaryDet_of_nonneg (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (q k : ℕ) (hk : k ≤ N) :
    rectangleSchur a q k = elementaryDet a q k := by
  have hf := (rectangleSchur_continuous (N := N) q k).continuousAt.tendsto.comp
    (positiveApproximation_tendsto a)
  have hg := (elementaryDet_continuous (N := N) q k).continuousAt.tendsto.comp
    (positiveApproximation_tendsto a)
  have heq : (fun t => rectangleSchur (positiveApproximation a t) q k) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => elementaryDet (positiveApproximation a t) q k) := by
    have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    filter_upwards [htpos] with t ht
    exact rectangleSchur_eq_elementaryDet _ (positiveApproximation_pos a ha t ht) q k hk
  exact tendsto_nhds_unique (Filter.Tendsto.congr' heq hf) hg

theorem elementaryDet_nonneg (a : Fin N → ℝ) (ha : ∀ i, 0 ≤ a i)
    (q k : ℕ) (hk : k ≤ N) : 0 ≤ elementaryDet a q k := by
  rw [← rectangleSchur_eq_elementaryDet_of_nonneg a ha q k hk]
  exact schurValue_nonneg _ a ha

theorem rectangleSchur_update_zero_eq_elementaryDet (a : Fin N → ℝ)
    (ha : ∀ i, 0 ≤ a i) (i : Fin N) (q k : ℕ) (hk : k ≤ N) :
    rectangleSchur (Function.update a i 0) q k =
      elementaryDet (Function.update a i 0) q k := by
  apply rectangleSchur_eq_elementaryDet_of_nonneg _ _ q k hk
  intro j
  by_cases hji : j = i
  · subst j
    simp
  · simpa [Function.update, hji] using ha j

end CoefficientOne.RectangleContinuity
