import CoefficientOne.Sampling.UnitCurrentPotential

/-! # The ordered edge variation estimate for Gram potentials -/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def orderedVariation (N : ConductanceNetwork ι) (u : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, normalizedConductance N i j * |u i - u j|

theorem orderedVariation_add_le [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (u v : ι → ℝ) :
    orderedVariation N (u + v) ≤ orderedVariation N u + orderedVariation N v := by
  unfold orderedVariation
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  have h := mul_le_mul_of_nonneg_left (abs_add_le (u i - u j) (v i - v j))
    (normalizedConductance_nonneg N hd i j)
  calc
    _ = normalizedConductance N i j * |(u i - u j) + (v i - v j)| := by
      congr 2
      simp only [Pi.add_apply]
      ring
    _ ≤ normalizedConductance N i j * (|u i - u j| + |v i - v j|) := h
    _ = _ := by ring

theorem orderedVariation_le_weighted_abs [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) :
    orderedVariation N u ≤ 2 * ∑ i, stationaryMass N i * |u i| := by
  have hleft : (∑ i, ∑ j, normalizedConductance N i j * |u i|) =
      ∑ i, stationaryMass N i * |u i| := by
    simp only [← Finset.sum_mul, normalizedConductance_rowSum]
  have hright : (∑ i, ∑ j, normalizedConductance N i j * |u j|) =
      ∑ i, stationaryMass N i * |u i| := by
    rw [Finset.sum_comm]
    simp_rw [normalizedConductance_comm N]
    exact hleft
  calc
    orderedVariation N u ≤ ∑ i, ∑ j,
        normalizedConductance N i j * (|u i| + |u j|) := by
      exact Finset.sum_le_sum (fun i _ => Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (by simpa using abs_sub_le (u i) 0 (u j))
          (normalizedConductance_nonneg N hd i j)))
    _ = 2 * ∑ i, stationaryMass N i * |u i| := by
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hleft, hright]
      ring

theorem weighted_square_differences (p f : ι → ℝ)
    (hp : ∑ i, p i = 1) (hf : ∑ i, p i * f i = 0) :
    (∑ i, ∑ j, p i * p j * (f i - f j) ^ 2) = 2 * ∑ i, p i * (f i) ^ 2 := by
  have hinner (i : ι) : (∑ j, p j * (f i - f j) ^ 2) =
      (f i) ^ 2 + ∑ j, p j * (f j) ^ 2 := by
    calc
      _ = (f i) ^ 2 * (∑ j, p j) - 2 * f i * (∑ j, p j * f j) +
          ∑ j, p j * (f j) ^ 2 := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _ := by rw [hp, hf]; ring
  calc
    _ = ∑ i, p i * ((f i) ^ 2 + ∑ j, p j * (f j) ^ 2) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← hinner, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by simp_rw [mul_add, Finset.sum_add_distrib]; rw [← Finset.sum_mul, hp]; ring

theorem orderedVariation_sq_le_energy [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) :
    (orderedVariation N u) ^ 2 ≤
      ∑ i, ∑ j, normalizedConductance N i j * (u i - u j) ^ 2 := by
  have h := finiteExpectation_mul_cauchy
    (p := fun ij : ι × ι => normalizedConductance N ij.1 ij.2)
    (fun ij => normalizedConductance_nonneg N hd ij.1 ij.2)
    (fun ij => |u ij.1 - u ij.2|) (fun _ => 1)
  simpa only [finiteExpectation, Fintype.sum_prod_type, mul_one, one_pow, sq_abs,
    normalizedConductance_sum N hd, orderedVariation] using h

theorem orderedVariation_centeredScaled [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) :
    orderedVariation N (centeredScaledPotential N u) = 2 * N.edgeVariation u := by
  have hpoint (i j : ι) : normalizedConductance N i j *
      |centeredScaledPotential N u i - centeredScaledPotential N u j| =
      N.conductance i j * |u i - u j| := by
    have heq : centeredScaledPotential N u i - centeredScaledPotential N u j =
        degreeMass N * (u i - u j) := by unfold centeredScaledPotential; ring
    rw [heq, abs_mul, abs_of_pos (degreeMass_pos N hd)]
    simp only [normalizedConductance]
    field_simp [(degreeMass_pos N hd).ne']
  simp only [orderedVariation, hpoint, ConductanceNetwork.edgeVariation]
  ring

namespace NormalizedGram
variable {N : ConductanceNetwork ι} (G : NormalizedGram N)

def remainder (l : ι → ℝ) : ι → ℝ := fun i => -(G.vectors i ⬝ᵥ l)

theorem inner_mean_zero (l : ι → ℝ) :
    ∑ i, stationaryMass N i * (G.vectors i ⬝ᵥ l) = 0 := by
  have h := congrArg (fun z => z ⬝ᵥ l) G.mean_zero
  simpa only [sum_dotProduct, smul_dotProduct, smul_eq_mul, zero_dotProduct] using h

theorem remainder_energy_le [Nonempty ι] (hd : ∀ i, 0 < N.degree i) (l : ι → ℝ) :
    (∑ i, ∑ j, normalizedConductance N i j *
      (G.remainder l i - G.remainder l j) ^ 2) ≤ 4 * quadraticForm G.operator l := by
  have heq : ∀ i j, (G.remainder l i - G.remainder l j) ^ 2 =
      ((G.vectors i ⬝ᵥ l) - (G.vectors j ⬝ᵥ l)) ^ 2 := by
    intro i j
    simp only [remainder]
    ring
  simp_rw [heq]
  calc
    _ ≤ ∑ i, ∑ j, 2 * (stationaryMass N i * stationaryMass N j) *
        ((G.vectors i ⬝ᵥ l) - (G.vectors j ⬝ᵥ l)) ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_right (G.conductance_le_two hd i j) (sq_nonneg _)
    _ = 2 * (∑ i, ∑ j, stationaryMass N i * stationaryMass N j *
        ((G.vectors i ⬝ᵥ l) - (G.vectors j ⬝ᵥ l)) ^ 2) := by
      simp only [mul_assoc, Finset.mul_sum]
    _ = 4 * quadraticForm G.operator l := by
      rw [weighted_square_differences _ _ (sum_stationaryMass N hd) (G.inner_mean_zero l),
        G.operator_quadratic]
      ring

theorem remainder_variation_le_two [Nonempty ι] (hd : ∀ i, 0 < N.degree i)
    (l : ι → ℝ) (hl : quadraticForm G.operator l ≤ 1) :
    orderedVariation N (G.remainder l) ≤ 2 := by
  have h1 := orderedVariation_sq_le_energy N hd (G.remainder l)
  have h2 := G.remainder_energy_le hd l
  nlinarith

end NormalizedGram
end
end CoefficientOne.Sampling
