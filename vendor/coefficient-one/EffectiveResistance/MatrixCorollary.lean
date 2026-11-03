import EffectiveResistance.Resistance
import EffectiveResistance.EnergyCauchy
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The generic matrix corollary

This file formalizes the implication from the endpoint effective-resistance
bound to the factor-two normalized Laplacian comparison.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
variable {N : ConductanceNetwork ι} (G : GreenKernel N)

namespace GreenKernel

/-- Coordinate basis vector, kept explicit to make all finite sums reducible. -/
def basisVector (i : ι) : ι → ℝ :=
  fun k => if k = i then 1 else 0

theorem pairDemand_eq_basis_sub (i j : ι) :
    pairDemand i j = basisVector i - basisVector j := by
  funext k
  simp [pairDemand, basisVector]

theorem basisVector_dotProduct (i : ι) (x : ι → ℝ) :
    basisVector i ⬝ᵥ x = x i := by
  classical
  simp [basisVector, dotProduct]

theorem dotProduct_basisVector (x : ι → ℝ) (i : ι) :
    x ⬝ᵥ basisVector i = x i := by
  rw [dotProduct_comm]
  exact basisVector_dotProduct i x

theorem pairDemand_dotProduct {i j : ι} (hij : i ≠ j) (x : ι → ℝ) :
    pairDemand i j ⬝ᵥ x = x i - x j := by
  rw [pairDemand_eq_basis_sub, sub_dotProduct,
    basisVector_dotProduct, basisVector_dotProduct]

theorem effectiveResistance_expansion (i j : ι) :
    G.effectiveResistance i j =
      G.kernel i i + G.kernel j j - 2 * G.kernel i j := by
  rw [GreenKernel.effectiveResistance, GreenKernel.potential,
    pairDemand_eq_basis_sub, sub_dotProduct, Matrix.mulVec_sub]
  simp only [basisVector_dotProduct, Pi.sub_apply]
  simp only [Matrix.mulVec, dotProduct]
  have hi : ∑ x, G.kernel i x * basisVector i x = G.kernel i i := by
    exact dotProduct_basisVector (G.kernel i) i
  have hij' : ∑ x, G.kernel i x * basisVector j x = G.kernel i j := by
    exact dotProduct_basisVector (G.kernel i) j
  have hji : ∑ x, G.kernel j x * basisVector i x = G.kernel j i := by
    exact dotProduct_basisVector (G.kernel j) i
  have hj : ∑ x, G.kernel j x * basisVector j x = G.kernel j j := by
    exact dotProduct_basisVector (G.kernel j) j
  have hsym : G.kernel j i = G.kernel i j := G.symmetric.apply i j
  rw [hi, hij', hji, hj, hsym]
  ring

theorem effectiveResistance_self (i : ι) :
    G.effectiveResistance i i = 0 := by
  rw [G.effectiveResistance_expansion]
  ring

theorem effectiveResistance_comm (i j : ι) :
    G.effectiveResistance i j = G.effectiveResistance j i := by
  rw [G.effectiveResistance_expansion, G.effectiveResistance_expansion]
  have hsym : G.kernel j i = G.kernel i j := G.symmetric.apply i j
  rw [hsym]
  ring

/-- The local probe `e_i / v_i - e_j / v_j`. -/
def endpointProbe (i j : ι) : ι → ℝ :=
  (N.degree i)⁻¹ • basisVector i - (N.degree j)⁻¹ • basisVector j

theorem pairDemand_dot_endpointProbe {i j : ι} (hij : i ≠ j) :
    pairDemand i j ⬝ᵥ endpointProbe (N := N) i j =
      (N.degree i)⁻¹ + (N.degree j)⁻¹ := by
  rw [pairDemand_dotProduct hij]
  simp [endpointProbe, basisVector, hij, Ne.symm hij]

theorem energyPairing_basis (i j : ι) :
    N.energyPairing (basisVector i) (basisVector j) = N.laplacian i j := by
  rw [ConductanceNetwork.energyPairing, basisVector_dotProduct]
  change N.laplacian i ⬝ᵥ basisVector j = N.laplacian i j
  exact dotProduct_basisVector (N.laplacian i) j

theorem basis_dot_laplacian_mulVec (i j : ι) :
    basisVector i ⬝ᵥ (N.laplacian *ᵥ basisVector j) = N.laplacian i j := by
  exact energyPairing_basis (N := N) i j

theorem endpointProbe_energy
    (hdeg : ∀ k, 0 < N.degree k) {i j : ι} (hij : i ≠ j) :
    N.energy (endpointProbe (N := N) i j) =
      (N.degree i)⁻¹ + (N.degree j)⁻¹ +
        2 * N.conductance i j * ((N.degree i)⁻¹ * (N.degree j)⁻¹) := by
  rw [ConductanceNetwork.energy, endpointProbe]
  simp only [ConductanceNetwork.energyPairing, Matrix.mulVec_sub,
    Matrix.mulVec_smul, sub_dotProduct, smul_dotProduct, dotProduct_sub,
    dotProduct_smul, smul_eq_mul]
  rw [basis_dot_laplacian_mulVec, basis_dot_laplacian_mulVec,
    basis_dot_laplacian_mulVec, basis_dot_laplacian_mulVec,
    N.laplacian_diagonal, N.laplacian_diagonal,
    N.laplacian_offDiagonal hij, N.laplacian_offDiagonal (Ne.symm hij),
    N.conductance_comm]
  field_simp [ne_of_gt (hdeg i), ne_of_gt (hdeg j)]
  ring

/-- Gap between the reciprocal endpoint degrees and effective resistance. -/
def resistanceDefect (i j : ι) : ℝ :=
  (N.degree i)⁻¹ + (N.degree j)⁻¹ - G.effectiveResistance i j

theorem resistanceDefect_nonnegative
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound) (i j : ι) :
    0 ≤ G.resistanceDefect i j := by
  by_cases hij : i = j
  · subst j
    rw [resistanceDefect, G.effectiveResistance_self]
    simpa using
      add_nonneg (inv_nonneg.mpr (hdeg i).le) (inv_nonneg.mpr (hdeg i).le)
  · exact sub_nonneg.mpr (hER i j hij)

theorem potential_probe_pairing {i j : ι} (hij : i ≠ j) :
    N.energyPairing (G.potential (pairDemand i j))
        (endpointProbe (N := N) i j) =
      (N.degree i)⁻¹ + (N.degree j)⁻¹ := by
  rw [N.energyPairing_comm, ConductanceNetwork.energyPairing,
    G.solves_pairDemand hij]
  rw [dotProduct_comm]
  exact pairDemand_dot_endpointProbe hij

/-- The defect estimate used in the paper's generic matrix argument. -/
theorem resistanceDefect_le
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound) {i j : ι} (hij : i ≠ j) :
    G.resistanceDefect i j ≤
      2 * N.conductance i j * ((N.degree i)⁻¹ * (N.degree j)⁻¹) := by
  let S : ℝ := (N.degree i)⁻¹ + (N.degree j)⁻¹
  let R : ℝ := G.effectiveResistance i j
  let T : ℝ := 2 * N.conductance i j *
    ((N.degree i)⁻¹ * (N.degree j)⁻¹)
  have hS : 0 < S := by
    dsimp [S]
    exact add_pos (inv_pos.mpr (hdeg i)) (inv_pos.mpr (hdeg j))
  have hT : 0 ≤ T := by
    dsimp [T]
    exact mul_nonneg
      (mul_nonneg (by norm_num) (N.nonnegative i j))
      (mul_nonneg (inv_nonneg.mpr (hdeg i).le) (inv_nonneg.mpr (hdeg j).le))
  have hRS : R ≤ S := hER i j hij
  have hcs := N.energyPairing_sq_le
    (G.potential (pairDemand i j)) (endpointProbe (N := N) i j)
  rw [G.potential_probe_pairing hij, ← G.effectiveResistance_eq_energy hij,
    endpointProbe_energy (N := N) hdeg hij] at hcs
  change S ^ 2 ≤ R * (S + T) at hcs
  have hfirst : S * (S - R) ≤ R * T := by
    nlinarith
  have hsecond : R * T ≤ S * T :=
    mul_le_mul_of_nonneg_right hRS hT
  have hcancel : S * (S - R) ≤ S * T := hfirst.trans hsecond
  have hcancel' : (S - R) * S ≤ T * S := by
    simpa [mul_comm] using hcancel
  have hdelta : S - R ≤ T := (mul_le_mul_iff_left₀ hS).mp hcancel'
  simpa [resistanceDefect, S, R, T] using hdelta

theorem quadraticForm_kernel_eq_neg_half_resistanceSum
    {y : ι → ℝ} (hy : IsZeroSum y) :
    quadraticForm G.kernel y =
      -(2 : ℝ)⁻¹ *
        ∑ i, ∑ j, y i * y j * G.effectiveResistance i j := by
  have hfirst :
      (∑ i, ∑ j, y i * y j * G.kernel i i) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    calc
      (∑ j, y i * y j * G.kernel i i) =
          (y i * G.kernel i i) * ∑ j, y j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := by rw [hy]; ring
  have hsecond :
      (∑ i, ∑ j, y i * y j * G.kernel j j) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      (∑ i, y i * y j * G.kernel j j) =
          (y j * G.kernel j j) * ∑ i, y i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by rw [hy]; ring
  have hcross :
      quadraticForm G.kernel y =
        ∑ i, ∑ j, y i * y j * G.kernel i j := by
    simp only [quadraticForm, Matrix.mulVec, dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hcross]
  simp_rw [G.effectiveResistance_expansion]
  have hexpand :
      (∑ i, ∑ j,
        y i * y j * (G.kernel i i + G.kernel j j - 2 * G.kernel i j)) =
        (∑ i, ∑ j, y i * y j * G.kernel i i) +
        (∑ i, ∑ j, y i * y j * G.kernel j j) -
        2 * (∑ i, ∑ j, y i * y j * G.kernel i j) := by
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.mul_sum]
    ring
  rw [hexpand, hfirst, hsecond]
  ring

theorem quadraticForm_kernel_eq_half_defectSum
    {y : ι → ℝ} (hy : IsZeroSum y) :
    quadraticForm G.kernel y =
      (2 : ℝ)⁻¹ * ∑ i, ∑ j, y i * y j * G.resistanceDefect i j := by
  rw [G.quadraticForm_kernel_eq_neg_half_resistanceSum hy]
  have hdegreeLeft :
      (∑ i, ∑ j, y i * y j * (N.degree i)⁻¹) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    calc
      (∑ j, y i * y j * (N.degree i)⁻¹) =
          (y i * (N.degree i)⁻¹) * ∑ j, y j := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro j _
            ring
      _ = 0 := by rw [hy]; ring
  have hdegreeRight :
      (∑ i, ∑ j, y i * y j * (N.degree j)⁻¹) = 0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    calc
      (∑ i, y i * y j * (N.degree j)⁻¹) =
          (y j * (N.degree j)⁻¹) * ∑ i, y i := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro i _
            ring
      _ = 0 := by rw [hy]; ring
  have hrewrite (i j : ι) :
      G.effectiveResistance i j =
        (N.degree i)⁻¹ + (N.degree j)⁻¹ - G.resistanceDefect i j := by
    rw [resistanceDefect]
    ring
  simp_rw [hrewrite]
  have hexpand :
      (∑ i, ∑ j, y i * y j *
        ((N.degree i)⁻¹ + (N.degree j)⁻¹ - G.resistanceDefect i j)) =
        (∑ i, ∑ j, y i * y j * (N.degree i)⁻¹) +
        (∑ i, ∑ j, y i * y j * (N.degree j)⁻¹) -
        (∑ i, ∑ j, y i * y j * G.resistanceDefect i j) := by
    simp_rw [mul_sub, mul_add, Finset.sum_sub_distrib,
      Finset.sum_add_distrib]
  rw [hexpand, hdegreeLeft, hdegreeRight]
  ring

/-- A pointwise upper majorant for the resistance defect, including the diagonal. -/
def defectMajorant (i j : ι) : ℝ :=
  2 * ((if i = j then (N.degree i)⁻¹ else 0) +
    N.conductance i j * ((N.degree i)⁻¹ * (N.degree j)⁻¹))

theorem resistanceDefect_le_majorant
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound) (i j : ι) :
    G.resistanceDefect i j ≤ defectMajorant (N := N) i j := by
  by_cases hij : i = j
  · subst j
    rw [resistanceDefect, G.effectiveResistance_self]
    simp [defectMajorant, N.diagonal_zero]
    ring_nf
    exact le_refl _
  · rw [defectMajorant, if_neg hij, zero_add]
    simpa [mul_assoc] using G.resistanceDefect_le hdeg hER hij

/-- Weighted squared norm associated with reciprocal degrees. -/
def reciprocalDegreeNorm (y : ι → ℝ) : ℝ :=
  ∑ i, y i ^ 2 * (N.degree i)⁻¹

theorem two_mul_abs_mul_le_sq_add_sq (a b : ℝ) :
    2 * |a * b| ≤ a ^ 2 + b ^ 2 := by
  calc
    2 * |a * b| = 2 * |a| * |b| := by rw [abs_mul]; ring
    _ ≤ |a| ^ 2 + |b| ^ 2 := two_mul_le_add_sq _ _
    _ = a ^ 2 + b ^ 2 := by simp

theorem edgeAbsoluteSum_le_reciprocalDegreeNorm
    (hdeg : ∀ k, 0 < N.degree k) (y : ι → ℝ) :
    (∑ i, ∑ j,
      N.conductance i j * |y i * y j| *
        ((N.degree i)⁻¹ * (N.degree j)⁻¹)) ≤
      reciprocalDegreeNorm (N := N) y := by
  have hterm (i j : ι) :
      N.conductance i j * |y i * y j| *
          ((N.degree i)⁻¹ * (N.degree j)⁻¹) ≤
        (2 : ℝ)⁻¹ * N.conductance i j *
          (y i ^ 2 * (N.degree i)⁻¹ ^ 2 +
           y j ^ 2 * (N.degree j)⁻¹ ^ 2) := by
    have hab := two_mul_abs_mul_le_sq_add_sq
      (y i * (N.degree i)⁻¹) (y j * (N.degree j)⁻¹)
    have hc : 0 ≤ (2 : ℝ)⁻¹ * N.conductance i j :=
      mul_nonneg (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))
        (N.nonnegative i j)
    have hmul := mul_le_mul_of_nonneg_left hab hc
    have hi : |(N.degree i)⁻¹| = (N.degree i)⁻¹ :=
      abs_of_pos (inv_pos.mpr (hdeg i))
    have hj : |(N.degree j)⁻¹| = (N.degree j)⁻¹ :=
      abs_of_pos (inv_pos.mpr (hdeg j))
    calc
      N.conductance i j * |y i * y j| *
          ((N.degree i)⁻¹ * (N.degree j)⁻¹) =
          (2 : ℝ)⁻¹ * N.conductance i j *
            (2 * |(y i * (N.degree i)⁻¹) *
              (y j * (N.degree j)⁻¹)|) := by
                simp only [abs_mul, hi, hj]
                ring
      _ ≤ (2 : ℝ)⁻¹ * N.conductance i j *
          ((y i * (N.degree i)⁻¹) ^ 2 +
           (y j * (N.degree j)⁻¹) ^ 2) := hmul
      _ = (2 : ℝ)⁻¹ * N.conductance i j *
          (y i ^ 2 * (N.degree i)⁻¹ ^ 2 +
           y j ^ 2 * (N.degree j)⁻¹ ^ 2) := by ring
  calc
    (∑ i, ∑ j,
      N.conductance i j * |y i * y j| *
        ((N.degree i)⁻¹ * (N.degree j)⁻¹)) ≤
        ∑ i, ∑ j, (2 : ℝ)⁻¹ * N.conductance i j *
          (y i ^ 2 * (N.degree i)⁻¹ ^ 2 +
           y j ^ 2 * (N.degree j)⁻¹ ^ 2) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hterm i j
    _ = reciprocalDegreeNorm (N := N) y := by
      have hleft :
          (∑ i, ∑ j, (2 : ℝ)⁻¹ * N.conductance i j *
            (y i ^ 2 * (N.degree i)⁻¹ ^ 2)) =
            (2 : ℝ)⁻¹ * reciprocalDegreeNorm (N := N) y := by
        rw [reciprocalDegreeNorm, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        calc
          (∑ j, (2 : ℝ)⁻¹ * N.conductance i j *
            (y i ^ 2 * (N.degree i)⁻¹ ^ 2)) =
              (2 : ℝ)⁻¹ * (y i ^ 2 * (N.degree i)⁻¹ ^ 2) *
                ∑ j, N.conductance i j := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro j _
                  ring
          _ = (2 : ℝ)⁻¹ * (y i ^ 2 * (N.degree i)⁻¹) := by
            rw [← ConductanceNetwork.degree]
            field_simp [ne_of_gt (hdeg i)]
      have hright :
          (∑ i, ∑ j, (2 : ℝ)⁻¹ * N.conductance i j *
            (y j ^ 2 * (N.degree j)⁻¹ ^ 2)) =
            (2 : ℝ)⁻¹ * reciprocalDegreeNorm (N := N) y := by
        rw [Finset.sum_comm]
        calc
          (∑ j, ∑ i, (2 : ℝ)⁻¹ * N.conductance i j *
              (y j ^ 2 * (N.degree j)⁻¹ ^ 2)) =
              ∑ j, ∑ i, (2 : ℝ)⁻¹ * N.conductance j i *
                (y j ^ 2 * (N.degree j)⁻¹ ^ 2) := by
            apply Finset.sum_congr rfl
            intro j _
            apply Finset.sum_congr rfl
            intro i _
            rw [N.conductance_comm]
          _ = (2 : ℝ)⁻¹ * reciprocalDegreeNorm (N := N) y := hleft
      simp_rw [mul_add, Finset.sum_add_distrib]
      rw [hleft, hright]
      ring

/-- Inverse quadratic-form bound deduced from endpoint resistances. -/
theorem inverseQuadraticForm_le
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound)
    {y : ι → ℝ} (hy : IsZeroSum y) :
    quadraticForm G.kernel y ≤
      2 * reciprocalDegreeNorm (N := N) y := by
  have hpoint (i j : ι) :
      y i * y j * G.resistanceDefect i j ≤
        |y i * y j| * defectMajorant (N := N) i j := by
    calc
      y i * y j * G.resistanceDefect i j ≤
          |y i * y j| * G.resistanceDefect i j :=
        mul_le_mul_of_nonneg_right (le_abs_self (y i * y j))
          (G.resistanceDefect_nonnegative hdeg hER i j)
      _ ≤ |y i * y j| * defectMajorant (N := N) i j :=
        mul_le_mul_of_nonneg_left (G.resistanceDefect_le_majorant hdeg hER i j)
          (abs_nonneg _)
  have hsum :
      (∑ i, ∑ j, y i * y j * G.resistanceDefect i j) ≤
        ∑ i, ∑ j, |y i * y j| * defectMajorant (N := N) i j := by
    apply Finset.sum_le_sum
    intro i _
    apply Finset.sum_le_sum
    intro j _
    exact hpoint i j
  have hhalf :
      (2 : ℝ)⁻¹ * (∑ i, ∑ j, y i * y j * G.resistanceDefect i j) ≤
        (2 : ℝ)⁻¹ *
          (∑ i, ∑ j, |y i * y j| * defectMajorant (N := N) i j) :=
    mul_le_mul_of_nonneg_left hsum
      (inv_nonneg.mpr (by norm_num : (0 : ℝ) ≤ 2))
  have hdiag :
      (∑ i, ∑ j, |y i * y j| *
        (if i = j then (N.degree i)⁻¹ else 0)) =
        reciprocalDegreeNorm (N := N) y := by
    rw [reciprocalDegreeNorm]
    apply Finset.sum_congr rfl
    intro i _
    simp [abs_mul_self, pow_two]
  have hmajorant :
      (2 : ℝ)⁻¹ *
          (∑ i, ∑ j, |y i * y j| * defectMajorant (N := N) i j) =
        reciprocalDegreeNorm (N := N) y +
          ∑ i, ∑ j, N.conductance i j * |y i * y j| *
            ((N.degree i)⁻¹ * (N.degree j)⁻¹) := by
    calc
      (2 : ℝ)⁻¹ *
          (∑ i, ∑ j, |y i * y j| * defectMajorant (N := N) i j) =
          ∑ i, ∑ j, |y i * y j| *
            ((if i = j then (N.degree i)⁻¹ else 0) +
              N.conductance i j *
                ((N.degree i)⁻¹ * (N.degree j)⁻¹)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [defectMajorant]
        ring
      _ = (∑ i, ∑ j, |y i * y j| *
            (if i = j then (N.degree i)⁻¹ else 0)) +
          (∑ i, ∑ j, |y i * y j| *
            (N.conductance i j *
              ((N.degree i)⁻¹ * (N.degree j)⁻¹))) := by
        simp_rw [mul_add, Finset.sum_add_distrib]
      _ = reciprocalDegreeNorm (N := N) y +
          ∑ i, ∑ j, N.conductance i j * |y i * y j| *
            ((N.degree i)⁻¹ * (N.degree j)⁻¹) := by
        rw [hdiag]
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
  calc
    quadraticForm G.kernel y =
        (2 : ℝ)⁻¹ *
          (∑ i, ∑ j, y i * y j * G.resistanceDefect i j) :=
      G.quadraticForm_kernel_eq_half_defectSum hy
    _ ≤ (2 : ℝ)⁻¹ *
          (∑ i, ∑ j, |y i * y j| * defectMajorant (N := N) i j) := hhalf
    _ = reciprocalDegreeNorm (N := N) y +
          ∑ i, ∑ j, N.conductance i j * |y i * y j| *
            ((N.degree i)⁻¹ * (N.degree j)⁻¹) := hmajorant
    _ ≤ reciprocalDegreeNorm (N := N) y +
          reciprocalDegreeNorm (N := N) y :=
      add_le_add_right (edgeAbsoluteSum_le_reciprocalDegreeNorm
        (N := N) hdeg y) _
    _ = 2 * reciprocalDegreeNorm (N := N) y := by ring

/-- Degree-weighted mean of a vector. -/
def degreeWeightedMean (x : ι → ℝ) : ℝ :=
  (∑ i, N.degree i * x i) / totalWeight N.degree

/-- Vector centered with respect to the degree weights. -/
def degreeCentered (x : ι → ℝ) : ι → ℝ :=
  fun i => x i - degreeWeightedMean (N := N) x

theorem totalDegree_pos [Nonempty ι] (hdeg : ∀ k, 0 < N.degree k) :
    0 < totalWeight N.degree := by
  rw [totalWeight]
  exact Finset.sum_pos (fun i _ => hdeg i) Finset.univ_nonempty

theorem degreeCentered_weightedSum_zero [Nonempty ι]
    (hdeg : ∀ k, 0 < N.degree k) (x : ι → ℝ) :
    ∑ i, N.degree i * degreeCentered (N := N) x i = 0 := by
  have hV : totalWeight N.degree ≠ 0 := ne_of_gt (totalDegree_pos (N := N) hdeg)
  simp only [degreeCentered]
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [← Finset.sum_mul]
  change (∑ i, N.degree i * x i) -
    totalWeight N.degree *
      ((∑ i, N.degree i * x i) / totalWeight N.degree) = 0
  field_simp [hV]
  ring

theorem quadraticForm_comparison_eq_centered [Nonempty ι]
    (hdeg : ∀ k, 0 < N.degree k) (x : ι → ℝ) :
    quadraticForm (comparisonMatrix N.degree) x =
      ∑ i, N.degree i * (degreeCentered (N := N) x i) ^ 2 := by
  have hV : totalWeight N.degree ≠ 0 := ne_of_gt (totalDegree_pos (N := N) hdeg)
  rw [quadraticForm_comparisonMatrix]
  change
    (∑ i, N.degree i * x i ^ 2) -
        (∑ i, N.degree i * x i) ^ 2 / totalWeight N.degree =
      ∑ i, N.degree i *
        (x i - (∑ j, N.degree j * x j) / totalWeight N.degree) ^ 2
  have hexpand :
      (∑ i, N.degree i *
        (x i - (∑ j, N.degree j * x j) / totalWeight N.degree) ^ 2) =
        (∑ i, N.degree i * x i ^ 2) -
          2 * ((∑ j, N.degree j * x j) / totalWeight N.degree) *
            (∑ i, N.degree i * x i) +
          ((∑ j, N.degree j * x j) / totalWeight N.degree) ^ 2 *
            totalWeight N.degree := by
    calc
      (∑ i, N.degree i *
        (x i - (∑ j, N.degree j * x j) / totalWeight N.degree) ^ 2) =
          ∑ i, (N.degree i * x i ^ 2 -
            2 * ((∑ j, N.degree j * x j) / totalWeight N.degree) *
              (N.degree i * x i) +
            ((∑ j, N.degree j * x j) / totalWeight N.degree) ^ 2 *
              N.degree i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum]
        rw [totalWeight]
  rw [hexpand]
  change
    (∑ i, N.degree i * x i ^ 2) -
        (∑ i, N.degree i * x i) ^ 2 / totalWeight N.degree =
      (∑ i, N.degree i * x i ^ 2) -
        2 * ((∑ i, N.degree i * x i) / totalWeight N.degree) *
          (∑ i, N.degree i * x i) +
        ((∑ i, N.degree i * x i) / totalWeight N.degree) ^ 2 *
          totalWeight N.degree
  field_simp [hV]
  ring

theorem energy_degreeCentered (x : ι → ℝ) :
    N.energy (degreeCentered (N := N) x) = N.energy x := by
  rw [N.energy_eq_half_edgePairingSum, N.energy_eq_half_edgePairingSum]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  simp [ConductanceNetwork.edgePairingSum, degreeCentered]

theorem energy_potential_eq_quadraticForm_kernel
    {y : ι → ℝ} (hy : IsZeroSum y) :
    N.energy (G.potential y) = quadraticForm G.kernel y := by
  rw [ConductanceNetwork.energy, ConductanceNetwork.energyPairing,
    GreenKernel.potential, G.solves_zeroSum y hy, quadraticForm]
  exact dotProduct_comm _ _

theorem reciprocalDegreeNorm_degreeTimes
    (hdeg : ∀ k, 0 < N.degree k) (z : ι → ℝ) :
    reciprocalDegreeNorm (N := N) (fun i => N.degree i * z i) =
      ∑ i, N.degree i * z i ^ 2 := by
  rw [reciprocalDegreeNorm]
  apply Finset.sum_congr rfl
  intro i _
  field_simp [ne_of_gt (hdeg i)]

/-- The factor-two normalized matrix comparison. -/
theorem half_normalized_laplacian [Nonempty ι]
    (hdeg : ∀ k, 0 < N.degree k)
    (hER : G.SatisfiesEndpointBound) :
    LoewnerLE ((2 : ℝ)⁻¹ • comparisonMatrix N.degree) N.laplacian := by
  intro x
  let z : ι → ℝ := degreeCentered (N := N) x
  let y : ι → ℝ := fun i => N.degree i * z i
  let W : ℝ := ∑ i, N.degree i * z i ^ 2
  have hy : IsZeroSum y := by
    exact degreeCentered_weightedSum_zero (N := N) hdeg x
  have hW : 0 ≤ W := by
    exact Finset.sum_nonneg fun i _ => mul_nonneg (hdeg i).le (sq_nonneg _)
  have hpair : N.energyPairing z (G.potential y) = W := by
    rw [ConductanceNetwork.energyPairing, GreenKernel.potential,
      G.solves_zeroSum y hy]
    change z ⬝ᵥ y = W
    simp only [dotProduct, y, W]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcs := N.energyPairing_sq_le z (G.potential y)
  rw [hpair, G.energy_potential_eq_quadraticForm_kernel hy] at hcs
  have hK : quadraticForm G.kernel y ≤ 2 * W := by
    calc
      quadraticForm G.kernel y ≤
          2 * reciprocalDegreeNorm (N := N) y :=
        G.inverseQuadraticForm_le hdeg hER hy
      _ = 2 * W := by
        rw [reciprocalDegreeNorm_degreeTimes (N := N) hdeg z]
  have hE : 0 ≤ N.energy z := N.energy_nonnegative z
  have hWE : W ^ 2 ≤ N.energy z * (2 * W) :=
    hcs.trans (mul_le_mul_of_nonneg_left hK hE)
  have hhalf : (2 : ℝ)⁻¹ * W ≤ N.energy z := by
    by_cases hWzero : W = 0
    · rw [hWzero]
      simpa using hE
    · have hWpos : 0 < W := lt_of_le_of_ne hW (Ne.symm hWzero)
      have hcancel : W * W ≤ (2 * N.energy z) * W := by
        simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hWE
      have hlinear : W ≤ 2 * N.energy z :=
        (mul_le_mul_iff_left₀ hWpos).mp hcancel
      nlinarith
  calc
    quadraticForm ((2 : ℝ)⁻¹ • comparisonMatrix N.degree) x =
        (2 : ℝ)⁻¹ * W := by
      rw [quadraticForm_smul,
        quadraticForm_comparison_eq_centered (N := N) hdeg]
    _ ≤ N.energy z := hhalf
    _ = quadraticForm N.laplacian x := by
      rw [energy_degreeCentered (N := N) x]
      exact N.energy_eq_quadraticForm x

end GreenKernel

end

end EffectiveResistance
