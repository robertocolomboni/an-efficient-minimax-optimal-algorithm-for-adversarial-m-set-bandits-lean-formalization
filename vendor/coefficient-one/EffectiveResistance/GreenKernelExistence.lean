import EffectiveResistance.MatrixCorollary
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Existence of the canonical Green kernel

For a complete conductance network with strictly positive off-diagonal
conductances, the Laplacian is invertible on the zero-sum subspace.  This file
constructs that inverse and packages it as a `GreenKernel`.
-/

open scoped BigOperators
open Matrix

namespace EffectiveResistance

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The four Penrose equations for a real square matrix and a candidate
pseudoinverse. -/
def IsMoorePenroseInverse (A K : Matrix ι ι ℝ) : Prop :=
  A * K * A = A ∧
  K * A * K = K ∧
  (A * K).IsSymm ∧
  (K * A).IsSymm

namespace ConductanceNetwork

variable (N : ConductanceNetwork ι)

/-- Every edge between distinct vertices has positive conductance. -/
def IsStrictlyComplete : Prop :=
  ∀ i j, i ≠ j → 0 < N.conductance i j

/-- Zero energy on a strictly complete network forces all coordinates to be
equal. -/
theorem eq_of_energy_eq_zero
    (hcomplete : N.IsStrictlyComplete) (x : ι → ℝ)
    (henergy : N.energy x = 0) (i j : ι) :
    x i = x j := by
  by_cases hij : i = j
  · exact congrArg x hij
  have hsum : N.edgePairingSum x x = 0 := by
    rw [N.energy_eq_half_edgePairingSum] at henergy
    exact (mul_eq_zero.mp henergy).resolve_left
      (inv_ne_zero (by norm_num : (2 : ℝ) ≠ 0))
  have hterm_nonnegative :
      ∀ p ∈ (Finset.univ : Finset (ι × ι)),
        0 ≤ N.conductance p.1 p.2 *
          (x p.1 - x p.2) * (x p.1 - x p.2) := by
    intro p _
    nlinarith [N.nonnegative p.1 p.2, sq_nonneg (x p.1 - x p.2)]
  have hle :
      N.conductance i j * (x i - x j) * (x i - x j) ≤
        N.edgePairingSum x x := by
    exact Finset.single_le_sum hterm_nonnegative
      (Finset.mem_univ (i, j))
  have hterm :
      N.conductance i j * (x i - x j) ^ 2 = 0 := by
    have hnonneg := mul_nonneg (N.nonnegative i j)
      (sq_nonneg (x i - x j))
    have hnonpos :
        N.conductance i j * (x i - x j) ^ 2 ≤ 0 := by
      rw [← hsum]
      nlinarith [hle]
    exact le_antisymm hnonpos hnonneg
  have hsquare : (x i - x j) ^ 2 = 0 :=
    (mul_eq_zero.mp hterm).resolve_left
      (ne_of_gt (hcomplete i j hij))
  nlinarith

/-- A Laplacian always maps into the zero-sum subspace. -/
theorem laplacian_mulVec_zeroSum (x : ι → ℝ) :
    IsZeroSum (N.laplacian *ᵥ x) := by
  unfold IsZeroSum
  simp only [Matrix.mulVec, dotProduct]
  calc
    (∑ i, ∑ j, N.laplacian i j * x j) =
        ∑ j, (∑ i, N.laplacian i j) * x j := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro j _
          rw [Finset.sum_mul]
    _ = ∑ j, (∑ i, N.laplacian j i) * x j := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          exact (N.laplacian_isSymm.apply i j).symm
    _ = ∑ j, (N.laplacian *ᵥ (fun _ : ι => (1 : ℝ))) j * x j := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          simp [Matrix.mulVec, dotProduct]
    _ = 0 := by rw [N.laplacian_mulVec_one]; simp

end ConductanceNetwork

/-- The linear subspace of vectors whose coordinates sum to zero. -/
def zeroSumSubmodule : Submodule ℝ (ι → ℝ) where
  carrier := {x | IsZeroSum x}
  zero_mem' := by
    change IsZeroSum (0 : ι → ℝ)
    simp [IsZeroSum]
  add_mem' {x y} hx hy := by
    change IsZeroSum (x + y)
    change IsZeroSum x at hx
    change IsZeroSum y at hy
    simp only [IsZeroSum, Pi.add_apply] at hx hy ⊢
    rw [Finset.sum_add_distrib, hx, hy, add_zero]
  smul_mem' a {x} hx := by
    change IsZeroSum (a • x)
    change IsZeroSum x at hx
    simp only [IsZeroSum, Pi.smul_apply, smul_eq_mul] at hx ⊢
    rw [← Finset.mul_sum, hx, mul_zero]

namespace ConductanceNetwork

/-- The Laplacian restricted to the zero-sum subspace. -/
def laplacianOnZeroSum (N : ConductanceNetwork ι) :
    zeroSumSubmodule (ι := ι) →ₗ[ℝ] zeroSumSubmodule (ι := ι) where
  toFun x := ⟨N.laplacian *ᵥ (x : ι → ℝ), by
    change IsZeroSum (N.laplacian *ᵥ (x : ι → ℝ))
    exact N.laplacian_mulVec_zeroSum (x : ι → ℝ)⟩
  map_add' x y := by
    apply Subtype.ext
    change N.laplacian *ᵥ ((x : ι → ℝ) + (y : ι → ℝ)) =
      N.laplacian *ᵥ (x : ι → ℝ) + N.laplacian *ᵥ (y : ι → ℝ)
    exact Matrix.mulVec_add _ _ _
  map_smul' a x := by
    apply Subtype.ext
    change N.laplacian *ᵥ (a • (x : ι → ℝ)) =
      a • (N.laplacian *ᵥ (x : ι → ℝ))
    exact Matrix.mulVec_smul _ _ _

theorem laplacianOnZeroSum_injective [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    Function.Injective N.laplacianOnZeroSum := by
  intro x y hxy
  apply Subtype.ext
  let z : ι → ℝ := fun k => (x : ι → ℝ) k - (y : ι → ℝ) k
  have hzsum : IsZeroSum z := by
    dsimp [z, IsZeroSum]
    rw [Finset.sum_sub_distrib, x.property, y.property, sub_zero]
  have hLz : N.laplacian *ᵥ z = 0 := by
    have hxy' := congrArg Subtype.val hxy
    change N.laplacian *ᵥ (x : ι → ℝ) =
      N.laplacian *ᵥ (y : ι → ℝ) at hxy'
    rw [show z = (x : ι → ℝ) - (y : ι → ℝ) by rfl,
      Matrix.mulVec_sub, hxy', sub_self]
  have hEz : N.energy z = 0 := by
    rw [ConductanceNetwork.energy, ConductanceNetwork.energyPairing, hLz]
    simp
  let i₀ : ι := Classical.choice inferInstance
  have hzconstant : ∀ k, z k = z i₀ := fun k =>
    N.eq_of_energy_eq_zero hcomplete z hEz k i₀
  have hzbase : z i₀ = 0 := by
    have hsum : (Fintype.card ι : ℝ) * z i₀ = 0 := by
      calc
        (Fintype.card ι : ℝ) * z i₀ = ∑ _k : ι, z i₀ := by simp
        _ = ∑ k, z k := by
          apply Finset.sum_congr rfl
          intro k _
          exact (hzconstant k).symm
        _ = 0 := hzsum
    have hcard : 0 < (Fintype.card ι : ℝ) := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι))
    nlinarith
  funext k
  have hzk : z k = 0 := (hzconstant k).trans hzbase
  change (x : ι → ℝ) k - (y : ι → ℝ) k = 0 at hzk
  exact sub_eq_zero.mp hzk

end ConductanceNetwork

/-- Orthogonal projection onto the zero-sum subspace. -/
def zeroSumProjection [Nonempty ι] :
    (ι → ℝ) →ₗ[ℝ] zeroSumSubmodule (ι := ι) where
  toFun y := ⟨fun i => y i - (∑ k, y k) / Fintype.card ι, by
    change IsZeroSum (fun i => y i - (∑ k, y k) / Fintype.card ι)
    unfold IsZeroSum
    rw [Finset.sum_sub_distrib]
    have hcard : (Fintype.card ι : ℝ) ≠ 0 := by
      exact_mod_cast (Fintype.card_pos_iff.mpr (inferInstance : Nonempty ι)).ne'
    calc
      (∑ i, y i) - ∑ _i : ι, (∑ k, y k) / Fintype.card ι =
          (∑ i, y i) - (Fintype.card ι : ℝ) *
            ((∑ k, y k) / Fintype.card ι) := by simp
      _ = 0 := by field_simp <;> ring⟩
  map_add' x y := by
    apply Subtype.ext
    funext i
    change (x i + y i) -
        (Finset.univ.sum fun k : ι => x k + y k) / Fintype.card ι =
      (x i - (Finset.univ.sum fun k : ι => x k) / Fintype.card ι) +
        (y i - (Finset.univ.sum fun k : ι => y k) / Fintype.card ι)
    rw [Finset.sum_add_distrib]
    ring
  map_smul' a x := by
    apply Subtype.ext
    funext i
    change a * x i -
        (Finset.univ.sum fun k : ι => a * x k) / Fintype.card ι =
      a * (x i -
        (Finset.univ.sum fun k : ι => x k) / Fintype.card ι)
    rw [← Finset.mul_sum]
    ring

theorem zeroSumProjection_apply [Nonempty ι] (y : ι → ℝ) (i : ι) :
    (zeroSumProjection y : ι → ℝ) i =
      y i - (∑ k, y k) / Fintype.card ι :=
  rfl

theorem zeroSumProjection_eq_self [Nonempty ι]
    (y : ι → ℝ) (hy : IsZeroSum y) :
    zeroSumProjection y = ⟨y, hy⟩ := by
  apply Subtype.ext
  funext i
  rw [zeroSumProjection_apply]
  rw [show ∑ k, y k = 0 from hy]
  simp

theorem zeroSumProjection_dot_zeroSum [Nonempty ι]
    (x z : ι → ℝ) (hz : IsZeroSum z) :
    (zeroSumProjection x : ι → ℝ) ⬝ᵥ z = x ⬝ᵥ z := by
  simp only [dotProduct, zeroSumProjection_apply, sub_mul]
  rw [Finset.sum_sub_distrib]
  have hfactor :
      (∑ i, (∑ k, x k) / Fintype.card ι * z i) =
        ((∑ k, x k) / Fintype.card ι) * ∑ i, z i := by
    rw [Finset.mul_sum]
  rw [hfactor, show ∑ i, z i = 0 from hz]
  ring

namespace ConductanceNetwork

/-- The restricted Laplacian as a linear equivalence of the zero-sum
subspace. -/
def laplacianZeroSumEquiv [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    zeroSumSubmodule (ι := ι) ≃ₗ[ℝ] zeroSumSubmodule (ι := ι) :=
  LinearEquiv.ofInjectiveEndo N.laplacianOnZeroSum
    (N.laplacianOnZeroSum_injective hcomplete)

/-- The canonical zero-mean inverse of the Laplacian, extended to all vectors
by first removing their constant component. -/
def greenOperator [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    (ι → ℝ) →ₗ[ℝ] (ι → ℝ) :=
  (zeroSumSubmodule (ι := ι)).subtype.comp
    ((N.laplacianZeroSumEquiv hcomplete).symm.toLinearMap.comp
      zeroSumProjection)

theorem greenOperator_zeroSum [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete)
    (y : ι → ℝ) :
    IsZeroSum (N.greenOperator hcomplete y) := by
  exact ((N.laplacianZeroSumEquiv hcomplete).symm
    (zeroSumProjection y)).property

theorem greenOperator_solve_projection [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete)
    (y : ι → ℝ) :
    N.laplacian *ᵥ (N.greenOperator hcomplete y) =
      (zeroSumProjection y : ι → ℝ) := by
  have h := (N.laplacianZeroSumEquiv hcomplete).apply_symm_apply
    (zeroSumProjection y)
  exact congrArg Subtype.val h

theorem greenOperator_solves_zeroSum [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete)
    (y : ι → ℝ) (hy : IsZeroSum y) :
    N.laplacian *ᵥ (N.greenOperator hcomplete y) = y := by
  rw [N.greenOperator_solve_projection hcomplete y,
    zeroSumProjection_eq_self y hy]

theorem laplacian_mulVec_zeroSumProjection [Nonempty ι]
    (N : ConductanceNetwork ι) (y : ι → ℝ) :
    N.laplacian *ᵥ (zeroSumProjection y : ι → ℝ) =
      N.laplacian *ᵥ y := by
  let a : ℝ := (∑ k, y k) / Fintype.card ι
  have hprojection : (zeroSumProjection y : ι → ℝ) =
      y - a • (fun _ : ι => (1 : ℝ)) := by
    funext i
    simp [a, zeroSumProjection_apply]
  rw [hprojection, Matrix.mulVec_sub, Matrix.mulVec_smul,
    N.laplacian_mulVec_one]
  simp

/-- The same canonical inverse also acts as a left inverse modulo the
constant direction. -/
theorem greenOperator_laplacian_mulVec [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete)
    (y : ι → ℝ) :
    N.greenOperator hcomplete (N.laplacian *ᵥ y) =
      (zeroSumProjection y : ι → ℝ) := by
  let x : zeroSumSubmodule (ι := ι) :=
    ⟨N.greenOperator hcomplete (N.laplacian *ᵥ y),
      N.greenOperator_zeroSum hcomplete (N.laplacian *ᵥ y)⟩
  let z : zeroSumSubmodule (ι := ι) := zeroSumProjection y
  have hrestricted : N.laplacianOnZeroSum x = N.laplacianOnZeroSum z := by
    apply Subtype.ext
    change N.laplacian *ᵥ
        (N.greenOperator hcomplete (N.laplacian *ᵥ y)) =
      N.laplacian *ᵥ (zeroSumProjection y : ι → ℝ)
    rw [N.greenOperator_solves_zeroSum hcomplete
        (N.laplacian *ᵥ y) (N.laplacian_mulVec_zeroSum y),
      N.laplacian_mulVec_zeroSumProjection y]
  have hxz : x = z :=
    N.laplacianOnZeroSum_injective hcomplete hrestricted
  exact congrArg Subtype.val hxz

/-- Self-adjointness of the canonical zero-mean inverse, written coordinatewise. -/
theorem greenOperator_coordinate_comm [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete)
    (i j : ι) :
    N.greenOperator hcomplete (GreenKernel.basisVector j) i =
      N.greenOperator hcomplete (GreenKernel.basisVector i) j := by
  let xi := N.greenOperator hcomplete (GreenKernel.basisVector i)
  let xj := N.greenOperator hcomplete (GreenKernel.basisVector j)
  have hxi0 : IsZeroSum xi :=
    N.greenOperator_zeroSum hcomplete (GreenKernel.basisVector i)
  have hxj0 : IsZeroSum xj :=
    N.greenOperator_zeroSum hcomplete (GreenKernel.basisVector j)
  have hxi : N.laplacian *ᵥ xi =
      (zeroSumProjection (GreenKernel.basisVector i) : ι → ℝ) :=
    N.greenOperator_solve_projection hcomplete (GreenKernel.basisVector i)
  have hxj : N.laplacian *ᵥ xj =
      (zeroSumProjection (GreenKernel.basisVector j) : ι → ℝ) :=
    N.greenOperator_solve_projection hcomplete (GreenKernel.basisVector j)
  calc
    xj i = GreenKernel.basisVector i ⬝ᵥ xj := by
      symm
      exact GreenKernel.basisVector_dotProduct i xj
    _ = (zeroSumProjection (GreenKernel.basisVector i) : ι → ℝ) ⬝ᵥ xj :=
      (zeroSumProjection_dot_zeroSum (GreenKernel.basisVector i) xj hxj0).symm
    _ = (N.laplacian *ᵥ xi) ⬝ᵥ xj := by rw [hxi]
    _ = xj ⬝ᵥ (N.laplacian *ᵥ xi) := dotProduct_comm _ _
    _ = N.energyPairing xj xi := rfl
    _ = N.energyPairing xi xj := N.energyPairing_comm xj xi
    _ = xi ⬝ᵥ (N.laplacian *ᵥ xj) := rfl
    _ = xi ⬝ᵥ (zeroSumProjection (GreenKernel.basisVector j) : ι → ℝ) := by
      rw [hxj]
    _ = (zeroSumProjection (GreenKernel.basisVector j) : ι → ℝ) ⬝ᵥ xi :=
      dotProduct_comm _ _
    _ = GreenKernel.basisVector j ⬝ᵥ xi :=
      zeroSumProjection_dot_zeroSum (GreenKernel.basisVector j) xi hxi0
    _ = xi j := GreenKernel.basisVector_dotProduct j xi

/-- The canonical Green kernel of a strictly complete conductance network. -/
def canonicalGreenKernel [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    GreenKernel N where
  kernel := LinearMap.toMatrix' (N.greenOperator hcomplete)
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    simp only [LinearMap.toMatrix'_apply]
    have hbasis : ∀ k : ι,
        GreenKernel.basisVector k = Pi.single k 1 := by
      intro k
      funext l
      by_cases hlk : l = k
      · subst l
        simp [GreenKernel.basisVector, Pi.single_apply]
      · simp [GreenKernel.basisVector, Pi.single_apply, hlk, Ne.symm hlk]
    rw [← hbasis i, ← hbasis j]
    exact (N.greenOperator_coordinate_comm hcomplete i j).symm
  solves_zeroSum y hy := by
    rw [LinearMap.toMatrix'_mulVec]
    exact N.greenOperator_solves_zeroSum hcomplete y hy

/-- Matrix of the canonical zero-sum inverse. -/
def canonicalGreenMatrix [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    Matrix ι ι ℝ :=
  (N.canonicalGreenKernel hcomplete).kernel

theorem canonicalGreenMatrix_mulVec [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete)
    (y : ι → ℝ) :
    N.canonicalGreenMatrix hcomplete *ᵥ y =
      N.greenOperator hcomplete y := by
  exact LinearMap.toMatrix'_mulVec (N.greenOperator hcomplete) y

theorem laplacian_mul_canonicalGreenMatrix_comm [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    N.laplacian * N.canonicalGreenMatrix hcomplete =
      N.canonicalGreenMatrix hcomplete * N.laplacian := by
  apply Matrix.ext_iff_mulVec.mpr
  intro y
  calc
    (N.laplacian * N.canonicalGreenMatrix hcomplete) *ᵥ y =
        N.laplacian *ᵥ (N.canonicalGreenMatrix hcomplete *ᵥ y) := by
          rw [Matrix.mulVec_mulVec]
    _ = N.laplacian *ᵥ (N.greenOperator hcomplete y) := by
          rw [N.canonicalGreenMatrix_mulVec hcomplete y]
    _ = (zeroSumProjection y : ι → ℝ) :=
          N.greenOperator_solve_projection hcomplete y
    _ = N.greenOperator hcomplete (N.laplacian *ᵥ y) :=
          (N.greenOperator_laplacian_mulVec hcomplete y).symm
    _ = N.canonicalGreenMatrix hcomplete *ᵥ (N.laplacian *ᵥ y) := by
          rw [N.canonicalGreenMatrix_mulVec hcomplete]
    _ = (N.canonicalGreenMatrix hcomplete * N.laplacian) *ᵥ y := by
          rw [Matrix.mulVec_mulVec]

/-- The canonical Green matrix satisfies all four Moore--Penrose equations. -/
theorem canonicalGreenMatrix_isMoorePenroseInverse [Nonempty ι]
    (N : ConductanceNetwork ι) (hcomplete : N.IsStrictlyComplete) :
    IsMoorePenroseInverse N.laplacian
      (N.canonicalGreenMatrix hcomplete) := by
  let K := N.canonicalGreenMatrix hcomplete
  have hcomm : N.laplacian * K = K * N.laplacian :=
    N.laplacian_mul_canonicalGreenMatrix_comm hcomplete
  have hAKA : N.laplacian * K * N.laplacian = N.laplacian := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    calc
      (N.laplacian * K * N.laplacian) *ᵥ y =
          N.laplacian *ᵥ (K *ᵥ (N.laplacian *ᵥ y)) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = N.laplacian *ᵥ
          (N.greenOperator hcomplete (N.laplacian *ᵥ y)) := by
            rw [N.canonicalGreenMatrix_mulVec hcomplete]
      _ = N.laplacian *ᵥ (zeroSumProjection y : ι → ℝ) := by
            rw [N.greenOperator_laplacian_mulVec hcomplete y]
      _ = N.laplacian *ᵥ y := N.laplacian_mulVec_zeroSumProjection y
  have hKAK : K * N.laplacian * K = K := by
    apply Matrix.ext_iff_mulVec.mpr
    intro y
    calc
      (K * N.laplacian * K) *ᵥ y =
          K *ᵥ (N.laplacian *ᵥ (K *ᵥ y)) := by
            rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
      _ = N.greenOperator hcomplete
          (N.laplacian *ᵥ (N.greenOperator hcomplete y)) := by
            rw [N.canonicalGreenMatrix_mulVec hcomplete,
              N.canonicalGreenMatrix_mulVec hcomplete]
      _ = (zeroSumProjection (N.greenOperator hcomplete y) : ι → ℝ) :=
            N.greenOperator_laplacian_mulVec hcomplete
              (N.greenOperator hcomplete y)
      _ = N.greenOperator hcomplete y := by
            rw [zeroSumProjection_eq_self _
              (N.greenOperator_zeroSum hcomplete y)]
      _ = K *ᵥ y := by rw [N.canonicalGreenMatrix_mulVec hcomplete]
  have hKsymm : K.IsSymm := by
    exact (N.canonicalGreenKernel hcomplete).symmetric
  have hAKsymm : (N.laplacian * K).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, hKsymm.eq, N.laplacian_isSymm.eq]
    exact hcomm.symm
  have hKAsymm : (K * N.laplacian).IsSymm := by
    unfold Matrix.IsSymm
    rw [Matrix.transpose_mul, N.laplacian_isSymm.eq, hKsymm.eq]
    exact hcomm
  exact ⟨hAKA, hKAK, hAKsymm, hKAsymm⟩

end ConductanceNetwork

end


end EffectiveResistance
