import EffectiveResistance.PairTransport
import EffectiveResistance.GreenKernelExistence

/-!
# Weighted edge-variation consequences

This file formalizes the static estimate used by the correlated-sampling
application.  We use one half of the ordered edge sum, which is the
order-independent version of the paper's sum over `i < j`.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {N : ConductanceNetwork ι} (G : GreenKernel N)

namespace ConductanceNetwork

/-- Weighted total variation across unoriented edges. -/
def edgeVariation (N : ConductanceNetwork ι) (h : ι → ℝ) : ℝ :=
  (2 : ℝ)⁻¹ * ∑ i, ∑ j, N.conductance i j * |h i - h j|

theorem edgeVariation_nonnegative (N : ConductanceNetwork ι) (h : ι → ℝ) :
    0 ≤ N.edgeVariation h := by
  exact mul_nonneg (inv_nonneg.mpr (by norm_num))
    (Finset.sum_nonneg fun i _ =>
      Finset.sum_nonneg fun j _ =>
        mul_nonneg (N.nonnegative i j) (abs_nonneg _))

@[simp] theorem edgeVariation_zero (N : ConductanceNetwork ι) :
    N.edgeVariation (0 : ι → ℝ) = 0 := by
  simp [edgeVariation]

theorem edgeVariation_add_le (N : ConductanceNetwork ι) (h k : ι → ℝ) :
    N.edgeVariation (h + k) ≤ N.edgeVariation h + N.edgeVariation k := by
  have hpoint (i j : ι) :
      N.conductance i j * |(h + k) i - (h + k) j| ≤
        N.conductance i j * |h i - h j| +
          N.conductance i j * |k i - k j| := by
    calc
      N.conductance i j * |(h + k) i - (h + k) j| =
          N.conductance i j * |(h i - h j) + (k i - k j)| := by
            congr 2
            simp only [Pi.add_apply]
            ring
      _ ≤ N.conductance i j * (|h i - h j| + |k i - k j|) :=
        mul_le_mul_of_nonneg_left (abs_add_le _ _) (N.nonnegative i j)
      _ = N.conductance i j * |h i - h j| +
          N.conductance i j * |k i - k j| := by ring
  unfold edgeVariation
  calc
    (2 : ℝ)⁻¹ * ∑ i, ∑ j,
        N.conductance i j * |(h + k) i - (h + k) j| ≤
      (2 : ℝ)⁻¹ * ∑ i, ∑ j,
        (N.conductance i j * |h i - h j| +
          N.conductance i j * |k i - k j|) := by
            exact mul_le_mul_of_nonneg_left
              (Finset.sum_le_sum fun i _ =>
                Finset.sum_le_sum fun j _ => hpoint i j)
              (inv_nonneg.mpr (by norm_num))
    _ = (2 : ℝ)⁻¹ * ∑ i, ∑ j,
          N.conductance i j * |h i - h j| +
        (2 : ℝ)⁻¹ * ∑ i, ∑ j,
          N.conductance i j * |k i - k j| := by
            simp_rw [Finset.sum_add_distrib]
            ring

theorem edgeVariation_smul_of_nonnegative (N : ConductanceNetwork ι)
    {c : ℝ} (hc : 0 ≤ c) (h : ι → ℝ) :
    N.edgeVariation (c • h) = c * N.edgeVariation h := by
  unfold edgeVariation
  simp only [Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg hc]
  calc
    (2 : ℝ)⁻¹ * ∑ i, ∑ j,
        N.conductance i j * (c * |h i - h j|) =
      (2 : ℝ)⁻¹ * (c * ∑ i, ∑ j,
        N.conductance i j * |h i - h j|) := by
          congr 1
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring
    _ = c * ((2 : ℝ)⁻¹ * ∑ i, ∑ j,
        N.conductance i j * |h i - h j|) := by ring

theorem edgeVariation_finset_sum_le
    {α : Type*} (N : ConductanceNetwork ι) (s : Finset α)
    (u : α → ι → ℝ) :
    N.edgeVariation (∑ x ∈ s, u x) ≤
      ∑ x ∈ s, N.edgeVariation (u x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha]
      exact (N.edgeVariation_add_le (u a) (∑ x ∈ s, u x)).trans
        (add_le_add (le_refl _) ih)

end ConductanceNetwork

namespace GreenKernel

/-- Symmetry of the Green matrix as a bilinear identity. -/
theorem dotProduct_potential_comm (x y : ι → ℝ) :
    x ⬝ᵥ G.potential y = y ⬝ᵥ G.potential x := by
  simp only [potential, Matrix.mulVec, dotProduct, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [G.symmetric.apply]
  ring

/-- Applying the Green matrix to `Lh` recovers all pairwise differences of
`h`; the undetermined additive constant is irrelevant. -/
theorem potential_laplacian_pair_difference (h : ι → ℝ) (i j : ι) :
    G.potential (N.laplacian *ᵥ h) i -
      G.potential (N.laplacian *ᵥ h) j = h i - h j := by
  by_cases hij : i = j
  · subst j
    ring
  · rw [← pairDemand_dotProduct hij,
      ← pairDemand_dotProduct hij]
    calc
      pairDemand i j ⬝ᵥ G.potential (N.laplacian *ᵥ h) =
          (N.laplacian *ᵥ h) ⬝ᵥ G.potential (pairDemand i j) :=
            G.dotProduct_potential_comm _ _
      _ = G.potential (pairDemand i j) ⬝ᵥ
          (N.laplacian *ᵥ h) := dotProduct_comm _ _
      _ = N.energyPairing (G.potential (pairDemand i j)) h := rfl
      _ = N.energyPairing h (G.potential (pairDemand i j)) :=
        N.energyPairing_comm _ _
      _ = h ⬝ᵥ (N.laplacian *ᵥ G.potential (pairDemand i j)) := rfl
      _ = h ⬝ᵥ pairDemand i j := by rw [G.solves_pairDemand hij]
      _ = pairDemand i j ⬝ᵥ h := dotProduct_comm _ _

theorem edgeVariation_potential_laplacian (h : ι → ℝ) :
    N.edgeVariation (G.potential (N.laplacian *ᵥ h)) =
      N.edgeVariation h := by
  unfold ConductanceNetwork.edgeVariation
  apply congrArg ((2 : ℝ)⁻¹ * ·)
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [G.potential_laplacian_pair_difference h i j]

theorem energy_potential_laplacian (h : ι → ℝ) :
    N.energy (G.potential (N.laplacian *ᵥ h)) = N.energy h := by
  rw [N.energy_eq_half_edgePairingSum, N.energy_eq_half_edgePairingSum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  rw [G.potential_laplacian_pair_difference h p.1 p.2]

/-- The Green potential of a zero-sum vector is the corresponding positive
combination of elementary pair-demand potentials. -/
theorem potential_eq_transport_sum
    {g : ι → ℝ} (hg : IsZeroSum g) (hmass : positiveMass g ≠ 0) :
    G.potential g =
      ∑ a, ∑ b, transportCoefficient g a b •
        G.potential (pairDemand a b) := by
  have hdecomp := sum_transportCoefficient_smul_pairDemand hg hmass
  have hdecomp' :
      g = ∑ a, ∑ b, transportCoefficient g a b • pairDemand a b := by
    exact hdecomp.symm.trans (by
      funext k
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul])
  calc
    G.potential g = G.potential
        (∑ a, ∑ b, transportCoefficient g a b • pairDemand a b) :=
      congrArg G.potential hdecomp'
    _ = ∑ a, ∑ b, transportCoefficient g a b •
        G.potential (pairDemand a b) := by
      unfold potential
      simp_rw [Matrix.mulVec_sum, Matrix.mulVec_smul]

theorem potential_pairDemand_apply (a b i : ι) :
  G.potential (pairDemand a b) i = G.kernel i a - G.kernel i b := by
  rw [GreenKernel.potential, pairDemand_eq_basis_sub,
    Matrix.mulVec_sub]
  change (G.kernel i ⬝ᵥ basisVector a) -
    (G.kernel i ⬝ᵥ basisVector b) = G.kernel i a - G.kernel i b
  rw [dotProduct_basisVector (G.kernel i) a,
    dotProduct_basisVector (G.kernel i) b]

/-- Polarization of two-point potentials by effective resistances. -/
theorem two_mul_potential_difference_eq_resistance_polarization
    (a b i j : ι) :
    2 * (G.potential (pairDemand a b) i -
      G.potential (pairDemand a b) j) =
      G.effectiveResistance i b + G.effectiveResistance j a -
        G.effectiveResistance i a - G.effectiveResistance j b := by
  simp_rw [G.potential_pairDemand_apply,
    G.effectiveResistance_expansion]
  ring

theorem effectiveResistance_eq_reciprocalDegrees_sub_defect (i j : ι) :
    G.effectiveResistance i j =
      (N.degree i)⁻¹ + (N.degree j)⁻¹ - G.resistanceDefect i j := by
  rw [resistanceDefect]
  ring

/-- Polarization rewritten entirely in terms of resistance defects. -/
theorem two_mul_potential_difference_eq_defect_polarization
    (a b i j : ι) :
    2 * (G.potential (pairDemand a b) i -
      G.potential (pairDemand a b) j) =
      G.resistanceDefect i a - G.resistanceDefect i b -
        G.resistanceDefect j a + G.resistanceDefect j b := by
  rw [G.two_mul_potential_difference_eq_resistance_polarization]
  simp_rw [G.effectiveResistance_eq_reciprocalDegrees_sub_defect]
  ring

theorem abs_potential_difference_le_defects
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound)
    (a b i j : ι) :
    |G.potential (pairDemand a b) i -
        G.potential (pairDemand a b) j| ≤
      (2 : ℝ)⁻¹ *
        (G.resistanceDefect i a + G.resistanceDefect i b +
          G.resistanceDefect j a + G.resistanceDefect j b) := by
  have hia := G.resistanceDefect_nonnegative hdeg hER i a
  have hib := G.resistanceDefect_nonnegative hdeg hER i b
  have hja := G.resistanceDefect_nonnegative hdeg hER j a
  have hjb := G.resistanceDefect_nonnegative hdeg hER j b
  have hpol :=
    G.two_mul_potential_difference_eq_defect_polarization a b i j
  rw [abs_le]
  constructor <;> nlinarith [inv_pos.mpr (by norm_num : (0 : ℝ) < 2)]

/-- Each defect column has degree-weighted mass at most four. -/
theorem degreeWeighted_resistanceDefect_sum_le_four
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound) (a : ι) :
    (∑ i, N.degree i * G.resistanceDefect i a) ≤ 4 := by
  have hpoint (i : ι) :
      N.degree i * G.resistanceDefect i a ≤
        N.degree i * defectMajorant (N := N) i a :=
    mul_le_mul_of_nonneg_left
      (G.resistanceDefect_le_majorant hdeg hER i a) (hdeg i).le
  calc
    (∑ i, N.degree i * G.resistanceDefect i a) ≤
        ∑ i, N.degree i * defectMajorant (N := N) i a := by
          exact Finset.sum_le_sum fun i _ => hpoint i
    _ = 4 := by
      have hcolumn : ∑ i, N.conductance i a = N.degree a := by
        calc
          (∑ i, N.conductance i a) = ∑ i, N.conductance a i := by
            apply Finset.sum_congr rfl
            intro i _
            exact N.conductance_comm i a
          _ = N.degree a := rfl
      simp only [defectMajorant]
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hdiag :
          (∑ i, N.degree i *
            (2 * (if i = a then (N.degree i)⁻¹ else 0))) = 2 := by
        simp <;> field_simp [ne_of_gt (hdeg a)]
      have hedge :
          (∑ i, N.degree i *
            (2 * (N.conductance i a *
              ((N.degree i)⁻¹ * (N.degree a)⁻¹)))) = 2 := by
        calc
          (∑ i, N.degree i *
            (2 * (N.conductance i a *
              ((N.degree i)⁻¹ * (N.degree a)⁻¹)))) =
              2 * (N.degree a)⁻¹ * ∑ i, N.conductance i a := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro i _
                field_simp [ne_of_gt (hdeg i)]
          _ = 2 := by
            rw [hcolumn]
            field_simp [ne_of_gt (hdeg a)]
      rw [hdiag, hedge]
      ring

/-- Endpoint resistance bounds imply the constant-four edge-variation
estimate for every unit pair demand. -/
theorem edgeVariation_potential_pairDemand_le_four
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound)
    (a b : ι) :
    N.edgeVariation (G.potential (pairDemand a b)) ≤ 4 := by
  let u := G.potential (pairDemand a b)
  let Δ : ι → ι → ℝ := G.resistanceDefect
  have hpoint (i j : ι) :
      N.conductance i j * |u i - u j| ≤
        N.conductance i j * ((2 : ℝ)⁻¹ *
          (Δ i a + Δ i b + Δ j a + Δ j b)) := by
    exact mul_le_mul_of_nonneg_left
      (G.abs_potential_difference_le_defects hdeg hER a b i j)
      (N.nonnegative i j)
  have hordered :
      (∑ i, ∑ j, N.conductance i j * |u i - u j|) ≤
        ∑ i, ∑ j, N.conductance i j * ((2 : ℝ)⁻¹ *
          (Δ i a + Δ i b + Δ j a + Δ j b)) := by
    exact Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ => hpoint i j
  have hleft (t : ι → ℝ) :
      (∑ i, ∑ j, N.conductance i j * t i) =
        ∑ i, N.degree i * t i := by
    apply Finset.sum_congr rfl
    intro i _
    calc
      (∑ j, N.conductance i j * t i) =
          (∑ j, N.conductance i j) * t i := by
            rw [Finset.sum_mul]
      _ = N.degree i * t i := rfl
  have hright (t : ι → ℝ) :
      (∑ i, ∑ j, N.conductance i j * t j) =
        ∑ j, N.degree j * t j := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    calc
      (∑ i, N.conductance i j * t j) =
          (∑ i, N.conductance i j) * t j := by
            rw [Finset.sum_mul]
      _ = (∑ i, N.conductance j i) * t j := by
            congr 1
            apply Finset.sum_congr rfl
            intro i _
            exact N.conductance_comm i j
      _ = N.degree j * t j := rfl
  have hscale (f : ι → ι → ℝ) :
      (∑ i, ∑ j, (2 : ℝ)⁻¹ * f i j) =
        (2 : ℝ)⁻¹ * ∑ i, ∑ j, f i j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  have hinnercollapse :
      (∑ i, ∑ j, N.conductance i j * ((2 : ℝ)⁻¹ *
        (Δ i a + Δ i b + Δ j a + Δ j b))) =
      (∑ i, N.degree i * Δ i a) +
        ∑ i, N.degree i * Δ i b := by
    calc
      (∑ i, ∑ j, N.conductance i j * ((2 : ℝ)⁻¹ *
        (Δ i a + Δ i b + Δ j a + Δ j b))) =
          ∑ i, ∑ j, (2 : ℝ)⁻¹ *
            (N.conductance i j * Δ i a +
             N.conductance i j * Δ i b +
             N.conductance i j * Δ j a +
             N.conductance i j * Δ j b) := by
              apply Finset.sum_congr rfl
              intro i _
              apply Finset.sum_congr rfl
              intro j _
              ring
      _ = (2 : ℝ)⁻¹ *
          ((∑ i, ∑ j, N.conductance i j * Δ i a) +
           (∑ i, ∑ j, N.conductance i j * Δ i b) +
           (∑ i, ∑ j, N.conductance i j * Δ j a) +
           (∑ i, ∑ j, N.conductance i j * Δ j b)) := by
              simp_rw [mul_add, Finset.sum_add_distrib]
              rw [hscale (fun i j => N.conductance i j * Δ i a),
                hscale (fun i j => N.conductance i j * Δ i b),
                hscale (fun i j => N.conductance i j * Δ j a),
                hscale (fun i j => N.conductance i j * Δ j b)]
      _ = (∑ i, N.degree i * Δ i a) +
          ∑ i, N.degree i * Δ i b := by
            rw [hleft (fun i => Δ i a), hleft (fun i => Δ i b),
              hright (fun i => Δ i a), hright (fun i => Δ i b)]
            ring
  have hcollapse :
      (2 : ℝ)⁻¹ *
          (∑ i, ∑ j, N.conductance i j * ((2 : ℝ)⁻¹ *
            (Δ i a + Δ i b + Δ j a + Δ j b))) =
        (2 : ℝ)⁻¹ *
          ((∑ i, N.degree i * Δ i a) +
            ∑ i, N.degree i * Δ i b) := by
    rw [hinnercollapse]
  have ha := G.degreeWeighted_resistanceDefect_sum_le_four hdeg hER a
  have hb := G.degreeWeighted_resistanceDefect_sum_le_four hdeg hER b
  rw [ConductanceNetwork.edgeVariation]
  calc
    (2 : ℝ)⁻¹ *
        (∑ i, ∑ j, N.conductance i j * |u i - u j|) ≤
      (2 : ℝ)⁻¹ *
        (∑ i, ∑ j, N.conductance i j * ((2 : ℝ)⁻¹ *
          (Δ i a + Δ i b + Δ j a + Δ j b))) :=
        mul_le_mul_of_nonneg_left hordered
          (inv_nonneg.mpr (by norm_num))
    _ = (2 : ℝ)⁻¹ *
          ((∑ i, N.degree i * Δ i a) +
            ∑ i, N.degree i * Δ i b) := hcollapse
    _ ≤ (2 : ℝ)⁻¹ * (4 + 4) :=
      mul_le_mul_of_nonneg_left (add_le_add ha hb)
        (inv_nonneg.mpr (by norm_num))
    _ = 4 := by norm_num

/-- General weighted edge-variation consequence.  This is the paper's
inequality `Φ_C(h) ≤ 2 ‖C h‖₁`, with the `ℓ¹` norm written as `l1Norm`. -/
theorem edgeVariation_le_two_l1_laplacian
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound)
    (h : ι → ℝ) :
    N.edgeVariation h ≤ 2 * l1Norm (N.laplacian *ᵥ h) := by
  let g : ι → ℝ := N.laplacian *ᵥ h
  have hg : IsZeroSum g := N.laplacian_mulVec_zeroSum h
  by_cases hmass : positiveMass g = 0
  · have hl1 : l1Norm g = 0 := by
      have htwo := two_mul_positiveMass_eq_l1Norm hg
      rw [hmass] at htwo
      norm_num at htwo
      exact htwo.symm
    have hgzero : g = 0 := by
      funext i
      have hsumabs : (∑ k, |g k|) = 0 := by
        simpa only [l1Norm] using hl1
      have hiabs : |g i| = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg
          (fun k _ => abs_nonneg (g k))).mp hsumabs i (Finset.mem_univ i)
      exact abs_eq_zero.mp hiabs
    calc
      N.edgeVariation h = N.edgeVariation (G.potential g) :=
        (G.edgeVariation_potential_laplacian h).symm
      _ = 0 := by rw [hgzero]; simp [potential]
      _ ≤ 2 * l1Norm g := by rw [hl1]; norm_num
  · have hpot := G.potential_eq_transport_sum hg hmass
    have houter :
        N.edgeVariation
            (∑ a, ∑ b, transportCoefficient g a b •
              G.potential (pairDemand a b)) ≤
          ∑ a, N.edgeVariation
            (∑ b, transportCoefficient g a b •
              G.potential (pairDemand a b)) := by
      simpa using N.edgeVariation_finset_sum_le Finset.univ
        (fun a => ∑ b, transportCoefficient g a b •
          G.potential (pairDemand a b))
    have hinner :
        (∑ a, N.edgeVariation
            (∑ b, transportCoefficient g a b •
              G.potential (pairDemand a b))) ≤
          ∑ a, ∑ b, N.edgeVariation
            (transportCoefficient g a b •
              G.potential (pairDemand a b)) := by
      apply Finset.sum_le_sum
      intro a _
      simpa using N.edgeVariation_finset_sum_le Finset.univ
        (fun b => transportCoefficient g a b •
          G.potential (pairDemand a b))
    have hsmul :
        (∑ a, ∑ b, N.edgeVariation
            (transportCoefficient g a b •
              G.potential (pairDemand a b))) =
          ∑ a, ∑ b, transportCoefficient g a b *
            N.edgeVariation (G.potential (pairDemand a b)) := by
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      exact N.edgeVariation_smul_of_nonnegative
        (transportCoefficient_nonnegative g a b)
        (G.potential (pairDemand a b))
    have hunit :
        (∑ a, ∑ b, transportCoefficient g a b *
            N.edgeVariation (G.potential (pairDemand a b))) ≤
          ∑ a, ∑ b, transportCoefficient g a b * 4 := by
      exact Finset.sum_le_sum fun a _ =>
        Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left
            (G.edgeVariation_potential_pairDemand_le_four hdeg hER a b)
            (transportCoefficient_nonnegative g a b)
    have hfactor :
        (∑ a, ∑ b, transportCoefficient g a b * 4) =
          4 * ∑ a, ∑ b, transportCoefficient g a b := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b _
      ring
    have htotal := sum_transportCoefficient hg hmass
    calc
      N.edgeVariation h = N.edgeVariation (G.potential g) :=
        (G.edgeVariation_potential_laplacian h).symm
      _ = N.edgeVariation
          (∑ a, ∑ b, transportCoefficient g a b •
            G.potential (pairDemand a b)) := congrArg N.edgeVariation hpot
      _ ≤ ∑ a, N.edgeVariation
          (∑ b, transportCoefficient g a b •
            G.potential (pairDemand a b)) := houter
      _ ≤ ∑ a, ∑ b, N.edgeVariation
          (transportCoefficient g a b •
            G.potential (pairDemand a b)) := hinner
      _ = ∑ a, ∑ b, transportCoefficient g a b *
          N.edgeVariation (G.potential (pairDemand a b)) := hsmul
      _ ≤ ∑ a, ∑ b, transportCoefficient g a b * 4 := hunit
      _ = 4 * ∑ a, ∑ b, transportCoefficient g a b := hfactor
      _ = 4 * ((2 : ℝ)⁻¹ * l1Norm g) := by rw [htotal]
      _ = 2 * l1Norm g := by ring

/-- Operator form of the half-normalized spectral gap.  The right side is
the quadratic form of `L D⁻¹ L`, written without introducing an auxiliary
matrix for `D⁻¹`. -/
theorem half_operator_laplacian
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound)
    (h : ι → ℝ) :
    (2 : ℝ)⁻¹ * N.energy h ≤
      reciprocalDegreeNorm (N := N) (N.laplacian *ᵥ h) := by
  let y : ι → ℝ := N.laplacian *ᵥ h
  have hy : IsZeroSum y := N.laplacian_mulVec_zeroSum h
  have hinverse := G.inverseQuadraticForm_le hdeg hER hy
  have henergy : quadraticForm G.kernel y = N.energy h := by
    rw [← G.energy_potential_eq_quadraticForm_kernel hy]
    exact G.energy_potential_laplacian h
  rw [henergy] at hinverse
  linarith

end GreenKernel

end

end EffectiveResistance
