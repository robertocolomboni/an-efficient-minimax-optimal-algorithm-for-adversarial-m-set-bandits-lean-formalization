import CoefficientOne.Sampling.UnitCurrentVariation

/-!
# Unit currents and arbitrary currents

The complete general-network endpoint of `lem:sampling-unit-current`.
The constant three follows from the actual Gram construction and resolvent
estimate, not from the older constant-four resistance argument.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_abs_pairDemand (a b : ι) (hab : a ≠ b) :
    ∑ i, |pairDemand a b i| = 2 := by
  have hpoint (i : ι) : |pairDemand a b i| =
      (if i = a then (1 : ℝ) else 0) + (if i = b then 1 else 0) := by
    by_cases hia : i = a
    · subst i
      simp [pairDemand, hab]
    · by_cases hib : i = b
      · subst i
        simp [pairDemand, hab, Ne.symm hab]
      · simp [pairDemand, hia, hib]
  norm_num [hpoint, Finset.sum_add_distrib]

theorem source_weighted_abs [Nonempty ι] (N : ConductanceNetwork ι)
    (hd : ∀ i, 0 < N.degree i) (a b : ι) (hab : a ≠ b) :
    (∑ i, stationaryMass N i * |pairDemand a b i / stationaryMass N i|) = 2 := by
  have hpoint (i : ι) : stationaryMass N i *
      |pairDemand a b i / stationaryMass N i| = |pairDemand a b i| := by
    rw [abs_div, abs_of_pos (stationaryMass_pos N hd i)]
    field_simp [(stationaryMass_pos N hd i).ne']
  simp only [hpoint]
  exact sum_abs_pairDemand a b hab

namespace NormalizedGram
variable {N : ConductanceNetwork ι} (G : NormalizedGram N)

include G in
theorem centered_unit_orderedVariation_le_six [Nonempty ι]
    (hd : ∀ i, 0 < N.degree i) (u : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (hu : ∑ i, stationaryMass N i * u i = 0)
    (hsolve : normalizedLaplacian N *ᵥ u = pairDemand a b) :
    orderedVariation N u ≤ 6 := by
  let eta : ι → ℝ := fun i => pairDemand a b i / stationaryMass N i
  have hdecomp : u = eta + G.remainder (G.moment u) := by
    ext i
    simpa only [eta, remainder, Pi.add_apply, sub_eq_add_neg] using
      G.centered_unit_current_decomposition hd u a b hu hsolve i
  have heta : orderedVariation N eta ≤ 4 := by
    have h := orderedVariation_le_weighted_abs N hd eta
    have he := source_weighted_abs N hd a b hab
    change (∑ i, stationaryMass N i * |eta i|) = 2 at he
    rw [he] at h
    norm_num at h ⊢
    exact h
  have hv : orderedVariation N (G.remainder (G.moment u)) ≤ 2 :=
    G.remainder_variation_le_two hd _ (G.moment_energy_le_one hd u a b hu hsolve)
  rw [hdecomp]
  exact (orderedVariation_add_le N hd eta _).trans (by linarith)

end NormalizedGram

/-- Every unit-current solution in a connected network with normalized gap one
has total edge variation at most three. All intermediate Gram data are constructed. -/
theorem unit_current_edgeVariation_le_three [Nonempty ι]
    (N : ConductanceNetwork ι) (hd : ∀ i, 0 < N.degree i)
    (hk : HasConstantKernel N) (hg : HasNormalizedGapOne N)
    (u : ι → ℝ) (a b : ι) (hab : a ≠ b)
    (hsolve : N.laplacian *ᵥ u = pairDemand a b) : N.edgeVariation u ≤ 3 := by
  obtain ⟨G⟩ := exists_normalizedGram N hd hk hg
  have h := G.centered_unit_orderedVariation_le_six hd (centeredScaledPotential N u)
    a b hab (centeredScaledPotential_mean_zero N hd u)
    ((centeredScaledPotential_solves N hd u).trans hsolve)
  rw [orderedVariation_centeredScaled N hd u] at h
  linarith

/-- Transporting the positive part of Ch to its negative part yields the factor
three halves. This is the second conclusion of the same manuscript lemma. -/
theorem edgeVariation_le_three_halves_l1_laplacian [Nonempty ι]
    (N : ConductanceNetwork ι) (hd : ∀ i, 0 < N.degree i)
    (hk : HasConstantKernel N) (hg : HasNormalizedGapOne N)
    (h : ι → ℝ) : N.edgeVariation h ≤ (3 / 2 : ℝ) * l1Norm (N.laplacian *ᵥ h) := by
  let G : GreenKernel N := regularizedGreenKernel N (fun x hx => (hk x).mp hx)
  let g : ι → ℝ := N.laplacian *ᵥ h
  have hz : IsZeroSum g := N.laplacian_mulVec_zeroSum h
  have hunit (a b : ι) : N.edgeVariation (G.potential (pairDemand a b)) ≤ 3 := by
    by_cases hab : a = b
    · subst b
      have hp : pairDemand a a = (0 : ι → ℝ) := by ext i; simp [pairDemand]
      rw [hp]
      simp [GreenKernel.potential]
    · exact unit_current_edgeVariation_le_three N hd hk hg _ a b hab
        (G.solves_pairDemand hab)
  by_cases hm : positiveMass g = 0
  · have hl : l1Norm g = 0 := by
      have he := two_mul_positiveMass_eq_l1Norm hz
      rw [hm] at he
      linarith
    have hgzero : g = 0 := by
      ext i
      have hi := (Finset.sum_eq_zero_iff_of_nonneg
        (fun j _ => abs_nonneg (g j))).mp hl i (Finset.mem_univ i)
      exact abs_eq_zero.mp hi
    have he : N.edgeVariation h = 0 := by
      rw [← G.edgeVariation_potential_laplacian h]
      change N.edgeVariation (G.potential g) = 0
      rw [hgzero]
      simp [GreenKernel.potential]
    change N.edgeVariation h ≤ (3 / 2 : ℝ) * l1Norm g
    rw [he, hl]
    norm_num
  · have hpot := G.potential_eq_transport_sum hz hm
    have hbound : N.edgeVariation (G.potential g) ≤
        ∑ a, ∑ b, transportCoefficient g a b * 3 := by
      rw [hpot]
      apply (N.edgeVariation_finset_sum_le Finset.univ _).trans
      apply Finset.sum_le_sum
      intro a _
      apply (N.edgeVariation_finset_sum_le Finset.univ _).trans
      apply Finset.sum_le_sum
      intro b _
      rw [N.edgeVariation_smul_of_nonnegative (transportCoefficient_nonnegative g a b)]
      exact mul_le_mul_of_nonneg_left (hunit a b) (transportCoefficient_nonnegative g a b)
    have hsum : (∑ a, ∑ b, transportCoefficient g a b * 3) =
        (3 / 2 : ℝ) * l1Norm g := by
      simp only [← Finset.sum_mul]
      rw [sum_transportCoefficient hz hm]
      ring
    rw [hsum] at hbound
    rwa [G.edgeVariation_potential_laplacian h] at hbound

end
end CoefficientOne.Sampling
