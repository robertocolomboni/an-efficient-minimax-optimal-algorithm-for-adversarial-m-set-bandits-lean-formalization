import MsetsPaper.Upper.InverseCovariance

/-!
# A Moore--Penrose inverse of the actual fixed-cardinality covariance

The matrix is constructed explicitly as `P M⁻¹ P`, where `P` is the orthogonal
projection onto zero-sum vectors.  All four Penrose equations are proved from
full support and normalization of the actual action law.  In particular, the
word pseudoinverse is not shorthand for an arbitrary covariance solution.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- The four defining Moore--Penrose equations for real square matrices. -/
def IsMoorePenroseInverse (A B : Matrix (Fin d) (Fin d) ℝ) : Prop :=
  A * B * A = A ∧ B * A * B = B ∧ (A * B).IsSymm ∧ (B * A).IsSymm

/-- The four Penrose equations uniquely determine the inverse. -/
theorem IsMoorePenroseInverse.unique
    {A B C : Matrix (Fin d) (Fin d) ℝ}
    (hB : IsMoorePenroseInverse A B) (hC : IsMoorePenroseInverse A C) : B = C := by
  have habac : (A * B) * (A * C) = A * C := by
    calc
      (A * B) * (A * C) = (A * B * A) * C := by simp only [Matrix.mul_assoc]
      _ = A * C := by rw [hB.1]
  have hacab : (A * C) * (A * B) = A * B := by
    calc
      (A * C) * (A * B) = (A * C * A) * B := by simp only [Matrix.mul_assoc]
      _ = A * B := by rw [hC.1]
  have habacT := congrArg Matrix.transpose habac
  rw [Matrix.transpose_mul, hC.2.2.1.eq, hB.2.2.1.eq] at habacT
  have hab : A * B = A * C := hacab.symm.trans habacT
  have hbaca : (B * A) * (C * A) = B * A := by
    calc
      (B * A) * (C * A) = B * (A * C * A) := by simp only [Matrix.mul_assoc]
      _ = B * A := by rw [hC.1]
  have hcaba : (C * A) * (B * A) = C * A := by
    calc
      (C * A) * (B * A) = C * (A * B * A) := by simp only [Matrix.mul_assoc]
      _ = C * A := by rw [hB.1]
  have hbacaT := congrArg Matrix.transpose hbaca
  rw [Matrix.transpose_mul, hB.2.2.2.eq, hC.2.2.2.eq] at hbacaT
  have hba : B * A = C * A := hbacaT.symm.trans hcaba
  calc
    B = B * A * B := hB.2.1.symm
    _ = B * (A * B) := Matrix.mul_assoc _ _ _
    _ = B * (A * C) := by rw [hab]
    _ = (B * A) * C := (Matrix.mul_assoc _ _ _).symm
    _ = (C * A) * C := by rw [hba]
    _ = C := hC.2.1

/-- Orthogonal projection onto the hyperplane of vectors with coordinate sum zero. -/
def zeroSumProjection : Matrix (Fin d) (Fin d) ℝ :=
  1 - (d : ℝ)⁻¹ • Matrix.vecMulVec (fun _ => 1) (fun _ => 1)

theorem zeroSumProjection_mulVec (x : Fin d → ℝ) :
    zeroSumProjection *ᵥ x = centerVector x := by
  rw [zeroSumProjection, Matrix.sub_mulVec, Matrix.one_mulVec,
    Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  ext i
  simp [centerVector, dotProduct, div_eq_mul_inv, mul_comm]

theorem zeroSumProjection_isSymm : (zeroSumProjection (d := d)).IsSymm := by
  change (zeroSumProjection (d := d))ᵀ = zeroSumProjection
  simp only [zeroSumProjection, Matrix.transpose_sub, Matrix.transpose_one,
    Matrix.transpose_smul, Matrix.transpose_vecMulVec]

theorem zeroSumProjection_idempotent (hd : d ≠ 0) :
    zeroSumProjection (d := d) * zeroSumProjection = zeroSumProjection := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, zeroSumProjection_mulVec, zeroSumProjection_mulVec]
  exact centerVector_eq_self_of_sum_eq_zero _ (sum_centerVector hd x)

/-- The image of a normalized fixed-cardinality covariance has coordinate sum zero. -/
theorem sum_covariance_mulVec (p : Action d m → ℝ) (hsum : ∑ a, p a = 1)
    (x : Fin d → ℝ) : ∑ i, (covariance p *ᵥ x) i = 0 := by
  have h := Matrix.dotProduct_transpose_mulVec (covariance p) (fun _ => 1) x
  rw [(covariance_isSymm p).eq, covariance_mulVec_one p hsum, dotProduct_zero] at h
  simpa only [dotProduct, one_mul] using h

theorem zeroSumProjection_mul_covariance
    (p : Action d m → ℝ) (hsum : ∑ a, p a = 1) :
    zeroSumProjection * covariance p = covariance p := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, zeroSumProjection_mulVec]
  exact centerVector_eq_self_of_sum_eq_zero _ (sum_covariance_mulVec p hsum x)

theorem covariance_mul_zeroSumProjection
    (p : Action d m → ℝ) (hsum : ∑ a, p a = 1) :
    covariance p * zeroSumProjection = covariance p := by
  have h := congrArg Matrix.transpose (zeroSumProjection_mul_covariance p hsum)
  simpa only [Matrix.transpose_mul, (covariance_isSymm p).eq,
    zeroSumProjection_isSymm.eq] using h

/-- Explicit candidate, subsequently verified against all four Penrose equations. -/
def covariancePseudoInverse (p : Action d m → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  zeroSumProjection * (secondMoment p)⁻¹ * zeroSumProjection

theorem covariancePseudoInverse_isSymm (p : Action d m → ℝ) :
    (covariancePseudoInverse p).IsSymm := by
  change (covariancePseudoInverse p)ᵀ = covariancePseudoInverse p
  simp only [covariancePseudoInverse, Matrix.transpose_mul,
    zeroSumProjection_isSymm.eq, (secondMoment_isSymm p).inv.eq, Matrix.mul_assoc]

theorem covariancePseudoInverse_mulVec (p : Action d m → ℝ) (y : Fin d → ℝ) :
    covariancePseudoInverse p *ᵥ y = centeredInverseSolution p (centerVector y) := by
  rw [covariancePseudoInverse, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    zeroSumProjection_mulVec, zeroSumProjection_mulVec]
  rfl

theorem covariance_mul_covariancePseudoInverse
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    covariance p * covariancePseudoInverse p = zeroSumProjection := by
  apply Matrix.ext_iff_mulVec.mpr
  intro x
  rw [← Matrix.mulVec_mulVec, covariancePseudoInverse_mulVec, zeroSumProjection_mulVec]
  exact covariance_mulVec_centeredInverseSolution p hp hsum hmpos hmtop _
    (sum_centerVector (by omega) x)

theorem covariancePseudoInverse_mul_covariance
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    covariancePseudoInverse p * covariance p = zeroSumProjection := by
  have h := congrArg Matrix.transpose
    (covariance_mul_covariancePseudoInverse p hp hsum hmpos hmtop)
  simpa only [Matrix.transpose_mul, (covariance_isSymm p).eq,
    (covariancePseudoInverse_isSymm p).eq, zeroSumProjection_isSymm.eq] using h

theorem zeroSumProjection_mul_covariancePseudoInverse
    (p : Action d m → ℝ) (hd : d ≠ 0) :
    zeroSumProjection * covariancePseudoInverse p = covariancePseudoInverse p := by
  simp only [covariancePseudoInverse, ← Matrix.mul_assoc, zeroSumProjection_idempotent hd]

/-- All four Moore--Penrose equations, with no assumed inverse or kernel facts. -/
theorem covariancePseudoInverse_isMoorePenroseInverse
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    IsMoorePenroseInverse (covariance p) (covariancePseudoInverse p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [covariance_mul_covariancePseudoInverse p hp hsum hmpos hmtop,
      zeroSumProjection_mul_covariance p hsum]
  · rw [covariancePseudoInverse_mul_covariance p hp hsum hmpos hmtop,
      zeroSumProjection_mul_covariancePseudoInverse p (by omega)]
  · rw [covariance_mul_covariancePseudoInverse p hp hsum hmpos hmtop]
    exact zeroSumProjection_isSymm
  · rw [covariancePseudoInverse_mul_covariance p hp hsum hmpos hmtop]
    exact zeroSumProjection_isSymm

/-- The exact zero-sum inverse/pseudoinverse quadratic identity. -/
theorem quadratic_eq_covariancePseudoInverse
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    y ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) = y ⬝ᵥ (covariancePseudoInverse p *ᵥ y) := by
  rw [covariancePseudoInverse_mulVec, centerVector_eq_self_of_sum_eq_zero y hy]
  apply quadratic_eq_of_covariance_mulVec_eq p hp hmpos hmtop y _ hy
  exact covariance_mulVec_centeredInverseSolution p hp hsum hmpos hmtop y hy

theorem leverage_eq_one_add_covariancePseudoInverse_quadratic
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x : Fin d → ℝ) (hx : ∑ i, x i = (m : ℝ)) :
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) =
      1 + (x - marginal p) ⬝ᵥ (covariancePseudoInverse p *ᵥ (x - marginal p)) := by
  rw [leverage_eq_one_add_centered_inverse_quadratic p hp hsum hmpos hmtop x hx,
    quadratic_eq_covariancePseudoInverse p hp hsum hmpos hmtop _
      (sum_sub_marginal_eq_zero p hsum x hx)]

/-- Any matrix satisfying the standard Penrose equations is the constructed one. -/
theorem covariancePseudoInverse_unique
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : IsMoorePenroseInverse (covariance p) C) :
    C = covariancePseudoInverse p :=
  hC.unique (covariancePseudoInverse_isMoorePenroseInverse p hp hsum hmpos hmtop)

/-- The inverse/pseudoinverse identity for any verified Moore--Penrose inverse. -/
theorem quadratic_eq_pseudoinverse
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : IsMoorePenroseInverse (covariance p) C)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    y ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) = y ⬝ᵥ (C *ᵥ y) := by
  rw [covariancePseudoInverse_unique p hp hsum hmpos hmtop C hC]
  exact quadratic_eq_covariancePseudoInverse p hp hsum hmpos hmtop y hy

theorem leverage_eq_one_add_pseudoinverse_quadratic
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (C : Matrix (Fin d) (Fin d) ℝ) (hC : IsMoorePenroseInverse (covariance p) C)
    (x : Fin d → ℝ) (hx : ∑ i, x i = (m : ℝ)) :
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) =
      1 + (x - marginal p) ⬝ᵥ (C *ᵥ (x - marginal p)) := by
  rw [covariancePseudoInverse_unique p hp hsum hmpos hmtop C hC]
  exact leverage_eq_one_add_covariancePseudoInverse_quadratic p hp hsum hmpos hmtop x hx

end MsetsPaper.Upper
