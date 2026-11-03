import MsetsPaper.Upper.SecondMoment

/-!
# The actual covariance and the inverse second moment

This module proves the covariance identities underlying manuscript Lemma 2 for
the actual full-support fixed-cardinality law.  In particular, on zero-sum
vectors the inverse second moment supplies a solution of the covariance equation,
and every such solution gives the same quadratic form.  No identification with a
Moore--Penrose inverse is assumed or asserted here.
-/

noncomputable section

open scoped BigOperators
open Matrix MsetsLower MsetsLower.History

namespace MsetsPaper.Upper

variable {d m : ℕ}

/-- The covariance matrix of the action indicators for a normalized law. -/
def covariance (p : Action d m → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  secondMoment p - Matrix.vecMulVec (marginal p) (marginal p)

/-- The matrix definition is the actual finite expectation of centered products. -/
theorem covariance_eq_centered_secondMoment (p : Action d m → ℝ)
    (hsum : ∑ a, p a = 1) (i j : Fin d) :
    covariance p i j = ∑ a, p a *
      (selectedIndicator i a - marginal p i) *
      (selectedIndicator j a - marginal p j) := by
  classical
  have hexpand : (∑ a, p a *
      (selectedIndicator i a - marginal p i) *
      (selectedIndicator j a - marginal p j)) =
      (∑ a, p a * selectedIndicator i a * selectedIndicator j a) -
      (∑ a, p a * selectedIndicator i a) * marginal p j -
      (∑ a, p a * selectedIndicator j a) * marginal p i +
      (∑ a, p a) * marginal p i * marginal p j := by
    simp only [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [hexpand, hsum]
  change secondMoment p i j - marginal p i * marginal p j =
    secondMoment p i j - marginal p i * marginal p j -
      marginal p j * marginal p i + 1 * marginal p i * marginal p j
  ring

theorem covariance_isSymm (p : Action d m → ℝ) : (covariance p).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  change secondMoment p j i - marginal p j * marginal p i =
    secondMoment p i j - marginal p i * marginal p j
  rw [(secondMoment_isSymm p).apply]
  ring

/-- Multiplication by the covariance is multiplication by the second moment
minus the rank-one mean correction. -/
theorem covariance_mulVec (p : Action d m → ℝ) (x : Fin d → ℝ) :
    covariance p *ᵥ x = secondMoment p *ᵥ x -
      (marginal p ⬝ᵥ x) • marginal p := by
  rw [covariance, Matrix.sub_mulVec, Matrix.vecMulVec_mulVec]
  congr 1
  ext i
  simp [mul_comm]

theorem covariance_mulVec_one (p : Action d m → ℝ) (hsum : ∑ a, p a = 1) :
    covariance p *ᵥ (fun _ => 1) = 0 := by
  rw [covariance_mulVec, secondMoment_mulVec_one]
  have hdot : marginal p ⬝ᵥ (fun _ => 1) = (m : ℝ) := by
    simpa [dotProduct] using sum_marginal p hsum
  rw [hdot, sub_self]

/-- Symmetry lets us move an inverse second moment across a dot product. -/
theorem dot_secondMoment_inv_mulVec (p : Action d m → ℝ) (x y : Fin d → ℝ) :
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) =
      y ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) := by
  simpa only [(secondMoment_isSymm p).inv.eq] using
    Matrix.dotProduct_transpose_mulVec (secondMoment p)⁻¹ x y

/-- The inverse-image of a zero-sum vector is orthogonal to the marginal. -/
theorem marginal_dot_secondMoment_inv_mulVec_eq_zero
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    marginal p ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) = 0 := by
  rw [dot_secondMoment_inv_mulVec,
    secondMoment_inv_mulVec_marginal p hp hmpos hmtop]
  simp only [dotProduct, ← Finset.sum_mul, hy, zero_mul]

/-- On the zero-sum subspace, the inverse second moment solves the covariance
equation.  Its invertibility comes from the actual full-support action law. -/
theorem covariance_mulVec_secondMoment_inv_mulVec
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    covariance p *ᵥ ((secondMoment p)⁻¹ *ᵥ y) = y := by
  letI := (secondMoment_posDef p hp hmpos hmtop).isUnit.invertible
  rw [covariance_mulVec,
    marginal_dot_secondMoment_inv_mulVec_eq_zero p hp hmpos hmtop y hy,
    zero_smul, sub_zero, Matrix.mulVec_mulVec,
    Matrix.mul_inv_of_invertible, Matrix.one_mulVec]

/-- Any solution of the covariance equation gives the same quadratic value as
the inverse second moment.  This is independent of a pseudoinverse convention. -/
theorem quadratic_eq_of_covariance_mulVec_eq
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y v : Fin d → ℝ) (hy : ∑ i, y i = 0)
    (hv : covariance p *ᵥ v = y) :
    y ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ y) = y ⬝ᵥ v := by
  have hsymm : v ⬝ᵥ (covariance p *ᵥ ((secondMoment p)⁻¹ *ᵥ y)) =
      ((secondMoment p)⁻¹ *ᵥ y) ⬝ᵥ (covariance p *ᵥ v) := by
    simpa only [(covariance_isSymm p).eq] using
      Matrix.dotProduct_transpose_mulVec (covariance p) v ((secondMoment p)⁻¹ *ᵥ y)
  rw [covariance_mulVec_secondMoment_inv_mulVec p hp hmpos hmtop y hy, hv] at hsymm
  simpa only [dotProduct_comm] using hsymm.symm

/-- Centering a vector of cardinality `m` produces a zero-sum vector. -/
theorem sum_sub_marginal_eq_zero (p : Action d m → ℝ) (hsum : ∑ a, p a = 1)
    (x : Fin d → ℝ) (hx : ∑ i, x i = (m : ℝ)) :
    ∑ i, (x - marginal p) i = 0 := by
  simp only [Pi.sub_apply, Finset.sum_sub_distrib, hx, sum_marginal p hsum, sub_self]

theorem marginal_inverse_quadratic_eq_one
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) :
    marginal p ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ marginal p) = 1 := by
  rw [secondMoment_inv_mulVec_marginal p hp hmpos hmtop]
  simp only [dotProduct, ← Finset.sum_mul, sum_marginal p hsum]
  exact mul_inv_cancel₀ (by exact_mod_cast (show m ≠ 0 by omega))

/-- Exact leverage decomposition on the affine fixed-cardinality hyperplane. -/
theorem leverage_eq_one_add_centered_inverse_quadratic
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x : Fin d → ℝ) (hx : ∑ i, x i = (m : ℝ)) :
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) =
      1 + (x - marginal p) ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ (x - marginal p)) := by
  have hy := sum_sub_marginal_eq_zero p hsum x hx
  have hcross := marginal_dot_secondMoment_inv_mulVec_eq_zero
    p hp hmpos hmtop (x - marginal p) hy
  have hcross' : (x - marginal p) ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ marginal p) = 0 := by
    rw [dot_secondMoment_inv_mulVec, hcross]
  calc
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) =
        ((x - marginal p) + marginal p) ⬝ᵥ
          ((secondMoment p)⁻¹ *ᵥ ((x - marginal p) + marginal p)) := by
      rw [sub_add_cancel]
    _ = _ := by
      simp only [Matrix.mulVec_add, add_dotProduct, dotProduct_add,
        hcross, hcross', marginal_inverse_quadratic_eq_one p hp hsum hmpos hmtop]
      ring

/-- The leverage decomposition with any solution of the centered covariance
equation, ready for a separately verified pseudoinverse bridge. -/
theorem leverage_eq_one_add_covariance_solution_quadratic
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x v : Fin d → ℝ) (hx : ∑ i, x i = (m : ℝ))
    (hv : covariance p *ᵥ v = x - marginal p) :
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) = 1 + (x - marginal p) ⬝ᵥ v := by
  rw [leverage_eq_one_add_centered_inverse_quadratic p hp hsum hmpos hmtop x hx,
    quadratic_eq_of_covariance_mulVec_eq p hp hmpos hmtop (x - marginal p) v
      (sum_sub_marginal_eq_zero p hsum x hx) hv]

/-- Subtract the coordinate average; this is the orthogonal projection onto the
zero-sum subspace in Euclidean coordinates. -/
def centerVector (x : Fin d → ℝ) : Fin d → ℝ :=
  x - ((∑ i, x i) / (d : ℝ)) • (fun _ => 1)

theorem sum_centerVector (hd : d ≠ 0) (x : Fin d → ℝ) :
    ∑ i, centerVector x i = 0 := by
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
  simp only [centerVector, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_one,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

theorem centerVector_eq_self_of_sum_eq_zero (x : Fin d → ℝ)
    (hx : ∑ i, x i = 0) : centerVector x = x := by
  simp [centerVector, hx]

/-- The canonical zero-sum solution is obtained by centering `M⁻¹ y`.  Naming
it a solution does not assert unproved Moore--Penrose properties. -/
def centeredInverseSolution (p : Action d m → ℝ) (y : Fin d → ℝ) : Fin d → ℝ :=
  centerVector ((secondMoment p)⁻¹ *ᵥ y)

theorem sum_centeredInverseSolution
    (p : Action d m → ℝ) (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) : ∑ i, centeredInverseSolution p y i = 0 :=
  sum_centerVector (by omega) _

theorem covariance_mulVec_centeredInverseSolution
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y : Fin d → ℝ) (hy : ∑ i, y i = 0) :
    covariance p *ᵥ centeredInverseSolution p y = y := by
  rw [centeredInverseSolution, centerVector, Matrix.mulVec_sub, Matrix.mulVec_smul,
    covariance_mulVec_one p hsum, smul_zero, sub_zero,
    covariance_mulVec_secondMoment_inv_mulVec p hp hmpos hmtop y hy]

/-- A zero covariance vector must be constant; full support proves this rather
than requiring it as a separate spectral hypothesis. -/
theorem eq_const_of_covariance_mulVec_eq_zero
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x : Fin d → ℝ) (hx : covariance p *ᵥ x = 0) :
    x = fun _ => (marginal p ⬝ᵥ x) * (m : ℝ)⁻¹ := by
  letI := (secondMoment_posDef p hp hmpos hmtop).isUnit.invertible
  rw [covariance_mulVec, sub_eq_zero] at hx
  have h := congrArg (fun z => (secondMoment p)⁻¹ *ᵥ z) hx
  rw [Matrix.mulVec_mulVec, Matrix.inv_mul_of_invertible, Matrix.one_mulVec,
    Matrix.mulVec_smul, secondMoment_inv_mulVec_marginal p hp hmpos hmtop] at h
  ext i
  exact congrFun h i

theorem eq_zero_of_covariance_mulVec_eq_zero_of_sum_eq_zero
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x : Fin d → ℝ) (hx : covariance p *ᵥ x = 0) (hs : ∑ i, x i = 0) : x = 0 := by
  have hc := eq_const_of_covariance_mulVec_eq_zero p hp hmpos hmtop x hx
  have hd : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  rw [hc] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  have hz := (mul_eq_zero.mp hs).resolve_left hd
  rw [hc, hz]
  rfl

/-- The centered solution is uniquely characterized by its covariance equation
and its zero coordinate sum. -/
theorem centeredInverseSolution_unique
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (y v : Fin d → ℝ) (hy : ∑ i, y i = 0)
    (hv : covariance p *ᵥ v = y) (hs : ∑ i, v i = 0) :
    v = centeredInverseSolution p y := by
  apply sub_eq_zero.mp
  apply eq_zero_of_covariance_mulVec_eq_zero_of_sum_eq_zero p hp hmpos hmtop
  · rw [Matrix.mulVec_sub, hv,
      covariance_mulVec_centeredInverseSolution p hp hsum hmpos hmtop y hy, sub_self]
  · simp only [Pi.sub_apply, Finset.sum_sub_distrib, hs,
      sum_centeredInverseSolution p hmpos hmtop y, sub_self]

theorem leverage_eq_one_add_centeredInverseSolution_quadratic
    (p : Action d m → ℝ) (hp : ∀ a, 0 < p a) (hsum : ∑ a, p a = 1)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    (x : Fin d → ℝ) (hx : ∑ i, x i = (m : ℝ)) :
    x ⬝ᵥ ((secondMoment p)⁻¹ *ᵥ x) =
      1 + (x - marginal p) ⬝ᵥ centeredInverseSolution p (x - marginal p) := by
  exact leverage_eq_one_add_covariance_solution_quadratic p hp hsum hmpos hmtop x _ hx
    (covariance_mulVec_centeredInverseSolution p hp hsum hmpos hmtop _
      (sum_sub_marginal_eq_zero p hsum x hx))

end MsetsPaper.Upper
