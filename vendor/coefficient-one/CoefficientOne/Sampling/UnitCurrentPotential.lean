import CoefficientOne.Sampling.UnitCurrentResolvent

/-! # A centered unit-current potential and its Gram moment -/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedLaplacian (N : ConductanceNetwork ι) : Matrix ι ι ℝ :=
  Matrix.diagonal (stationaryMass N) - normalizedConductance N

theorem normalizedLaplacian_eq (N : ConductanceNetwork ι) :
    normalizedLaplacian N = (degreeMass N)⁻¹ • N.laplacian := by
  ext i j
  by_cases hij : i = j
  · subst j
    simp [normalizedLaplacian, stationaryMass, N.laplacian_diagonal, div_eq_mul_inv,
      mul_comm]
  · simp [normalizedLaplacian, stationaryMass, normalizedConductance,
      Matrix.diagonal, hij, N.laplacian_offDiagonal hij, div_eq_mul_inv, mul_comm]

def centeredScaledPotential (N : ConductanceNetwork ι) (u : ι → ℝ) : ι → ℝ :=
  fun i => degreeMass N * u i - ∑ j, stationaryMass N j * (degreeMass N * u j)

theorem centeredScaledPotential_mean_zero [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) :
    ∑ i, stationaryMass N i * centeredScaledPotential N u i = 0 := by
  simp only [centeredScaledPotential, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
  rw [sum_stationaryMass N hd]
  ring

theorem centeredScaledPotential_solves [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) :
    normalizedLaplacian N *ᵥ centeredScaledPotential N u = N.laplacian *ᵥ u := by
  have heq : centeredScaledPotential N u = degreeMass N • u -
      (∑ j, stationaryMass N j * (degreeMass N * u j)) • (fun _ => 1) := by
    ext i
    simp [centeredScaledPotential]
  rw [heq, normalizedLaplacian_eq, Matrix.smul_mulVec, Matrix.mulVec_sub,
    Matrix.mulVec_smul, Matrix.mulVec_smul, N.laplacian_mulVec_one]
  simp [smul_smul, (degreeMass_pos N hd).ne']

namespace NormalizedGram
variable {N : ConductanceNetwork ι} (G : NormalizedGram N)

theorem conductance_mulVec_of_mean_zero (u : ι → ℝ)
    (hu : ∑ i, stationaryMass N i * u i = 0) (i : ι) :
    (normalizedConductance N *ᵥ u) i =
      -stationaryMass N i * (G.vectors i ⬝ᵥ G.moment u) := by
  change (∑ j, normalizedConductance N i j * u j) =
    -stationaryMass N i * (G.vectors i ⬝ᵥ G.moment u)
  simp_rw [G.conductance]
  have hmoment : G.vectors i ⬝ᵥ G.moment u =
      ∑ j, stationaryMass N j * u j * (G.vectors i ⬝ᵥ G.vectors j) := by
    simp [moment, dotProduct_sum, dotProduct_smul]
  rw [hmoment]
  have heq : (∑ j, stationaryMass N i * stationaryMass N j *
      (1 - G.vectors i ⬝ᵥ G.vectors j) * u j) =
      stationaryMass N i * (∑ j, stationaryMass N j * u j) -
      stationaryMass N i * (∑ j, stationaryMass N j * u j *
        (G.vectors i ⬝ᵥ G.vectors j)) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq, hu]
  ring

theorem centered_unit_current_decomposition [Nonempty ι]
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) (a b : ι)
    (hu : ∑ i, stationaryMass N i * u i = 0)
    (hsolve : normalizedLaplacian N *ᵥ u = pairDemand a b) (i : ι) :
    u i = pairDemand a b i / stationaryMass N i - G.vectors i ⬝ᵥ G.moment u := by
  have hi := congrFun hsolve i
  simp only [normalizedLaplacian, Matrix.sub_mulVec, Matrix.mulVec_diagonal,
    Pi.sub_apply] at hi
  rw [G.conductance_mulVec_of_mean_zero u hu i] at hi
  have hp := (stationaryMass_pos N hd i).ne'
  field_simp [hp] at ⊢
  nlinarith [hi]

theorem moment_resolvent_equation [Nonempty ι]
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) (a b : ι)
    (hu : ∑ i, stationaryMass N i * u i = 0)
    (hsolve : normalizedLaplacian N *ᵥ u = pairDemand a b) :
    G.moment u + G.operator *ᵥ G.moment u = G.vectors a - G.vectors b := by
  have hcoeff (i : ι) : stationaryMass N i * u i +
      stationaryMass N i * (G.vectors i ⬝ᵥ G.moment u) = pairDemand a b i := by
    rw [G.centered_unit_current_decomposition hd u a b hu hsolve i]
    field_simp [(stationaryMass_pos N hd i).ne']
    <;> ring
  rw [G.operator_mulVec]
  change (∑ i, (stationaryMass N i * u i) • G.vectors i) +
    (∑ i, (stationaryMass N i * (G.vectors i ⬝ᵥ G.moment u)) • G.vectors i) = _
  rw [← Finset.sum_add_distrib]
  simp only [← add_smul, hcoeff]
  ext j
  simp [pairDemand, sub_smul, Finset.sum_sub_distrib, ite_apply]

theorem moment_eq_resolvent [Nonempty ι]
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) (a b : ι)
    (hu : ∑ i, stationaryMass N i * u i = 0)
    (hsolve : normalizedLaplacian N *ᵥ u = pairDemand a b) :
    G.moment u = (1 + G.operator)⁻¹ *ᵥ (G.vectors a - G.vectors b) := by
  have h := G.moment_resolvent_equation hd u a b hu hsolve
  have h' : (1 + G.operator) *ᵥ G.moment u = G.vectors a - G.vectors b := by
    simpa [Matrix.add_mulVec] using h
  rw [← h', Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _
    (isUnit_iff_ne_zero.mpr (resolvent_det_ne_zero _ (G.operator_posSemidef hd))),
    Matrix.one_mulVec]

theorem moment_energy_le_one [Nonempty ι]
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) (a b : ι)
    (hu : ∑ i, stationaryMass N i * u i = 0)
    (hsolve : normalizedLaplacian N *ᵥ u = pairDemand a b) :
    quadraticForm G.operator (G.moment u) ≤ 1 := by
  rw [G.moment_eq_resolvent hd u a b hu hsolve]
  have h := resolvent_quadratic_bound G.operator (G.operator_posSemidef hd)
    (G.vectors a - G.vectors b)
  have hdif := G.difference_norm_sq_le_four a b
  linarith

end NormalizedGram
end
end CoefficientOne.Sampling
