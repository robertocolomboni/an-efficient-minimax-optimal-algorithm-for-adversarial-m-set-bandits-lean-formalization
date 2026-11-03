import MsetsLower.Lower.Sparse.MixtureTV
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Numerical chi-square budget for the sparse mixtures

This file formalizes the constant spending immediately before
`eq:lower-mixture-tv`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower.Lower

noncomputable section

theorem sparse_diagonal_exponent_le :
    10 * sparseA ^ 2 <= (1 : Real) / 32 := by
  norm_num [sparseA]

theorem sparse_cross_prefactor_eq :
    16 * sparseA ^ 2 * sparseRho = (2 : Real) ^ (-44 : Int) := by
  norm_num [sparseA, sparseRho, zpow_neg]

theorem sparse_cross_exponent_eq :
    128 * sparseA ^ 2 * sparseRho = (2 : Real) ^ (-41 : Int) := by
  norm_num [sparseA, sparseRho, zpow_neg]

/-- The diagonal contribution in the manuscript is at most `2^-31`. -/
theorem sparse_mixture_diagonal_term_le
    {r B : Nat} (hr : 2 ^ 32 <= r)
    (hB : (B : Real) <= Real.log (r : Real)) :
    (Real.exp (10 * sparseA ^ 2 * (B : Real)) - 1) / (r : Real) <=
      (2 : Real) ^ (-31 : Int) := by
  have hrposNat : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hrpos : 0 < (r : Real) := by exact_mod_cast hrposNat
  have hrone : 1 <= (r : Real) := by exact_mod_cast hrposNat
  have hlog0 : 0 <= Real.log (r : Real) := Real.log_nonneg hrone
  have harg :
      10 * sparseA ^ 2 * (B : Real) <=
        Real.log (r : Real) * ((1 : Real) / 32) := by
    calc
      10 * sparseA ^ 2 * (B : Real) <=
          ((1 : Real) / 32) * (B : Real) := by
        exact mul_le_mul_of_nonneg_right sparse_diagonal_exponent_le
          (Nat.cast_nonneg B)
      _ <= ((1 : Real) / 32) * Real.log (r : Real) := by
        exact mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = Real.log (r : Real) * ((1 : Real) / 32) := by ring
  have hexp :
      Real.exp (10 * sparseA ^ 2 * (B : Real)) <=
        (r : Real) ^ ((1 : Real) / 32) := by
    rw [Real.rpow_def_of_pos hrpos]
    exact Real.exp_le_exp.mpr harg
  have hnum :
      Real.exp (10 * sparseA ^ 2 * (B : Real)) - 1 <=
        (r : Real) ^ ((1 : Real) / 32) := by
    linarith [Real.exp_pos (10 * sparseA ^ 2 * (B : Real))]
  have hdiv :
      (Real.exp (10 * sparseA ^ 2 * (B : Real)) - 1) / (r : Real) <=
        (r : Real) ^ ((1 : Real) / 32) / (r : Real) :=
    div_le_div_of_nonneg_right hnum hrpos.le
  have hrpowRewrite :
      (r : Real) ^ ((1 : Real) / 32) / (r : Real) =
        (r : Real) ^ (-(31 : Real) / 32) := by
    rw [← Real.rpow_sub_one hrpos.ne' ((1 : Real) / 32)]
    congr 1
    ring
  have hrbase : (2 : Real) ^ 32 <= (r : Real) := by exact_mod_cast hr
  have hdecrease :
      (r : Real) ^ (-(31 : Real) / 32) <=
        ((2 : Real) ^ 32) ^ (-(31 : Real) / 32) :=
    Real.rpow_le_rpow_of_nonpos (by norm_num) hrbase (by norm_num)
  have hpower :
      ((2 : Real) ^ 32) ^ (-(31 : Real) / 32) =
        (2 : Real) ^ (-31 : Int) := by
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : Real) <= 2)]
    norm_num [Real.rpow_intCast]
  calc
    (Real.exp (10 * sparseA ^ 2 * (B : Real)) - 1) / (r : Real) <=
        (r : Real) ^ ((1 : Real) / 32) / (r : Real) := hdiv
    _ = (r : Real) ^ (-(31 : Real) / 32) := hrpowRewrite
    _ <= ((2 : Real) ^ 32) ^ (-(31 : Real) / 32) := hdecrease
    _ = (2 : Real) ^ (-31 : Int) := hpower

/-- A slightly stronger-than-needed bound for the off-diagonal contribution.
The manuscript records `2^-67`; the elementary `log r <= 4 r^(1/4)` bound
already gives `2^-58`, which is still far below the final budget. -/
theorem sparse_mixture_cross_term_le
    {r B : Nat} (hr : 2 ^ 32 <= r)
    (hB : (B : Real) <= Real.log (r : Real)) :
    (16 * sparseA ^ 2 * sparseRho * (B : Real) / (r : Real)) *
        Real.exp (128 * sparseA ^ 2 * sparseRho * (B : Real)) <=
      (2 : Real) ^ (-58 : Int) := by
  let R : Real := r
  let q : Real := R ^ ((1 : Real) / 4)
  have hrposNat : 0 < r := lt_of_lt_of_le (by norm_num) hr
  have hRpos : 0 < R := by
    dsimp [R]
    exact_mod_cast hrposNat
  have hR0 : 0 <= R := hRpos.le
  have hRone : 1 <= R := by
    dsimp [R]
    exact_mod_cast hrposNat
  have hlog0 : 0 <= Real.log R := Real.log_nonneg hRone
  have hlogq0 := Real.log_le_rpow_div hR0
    (by norm_num : (0 : Real) < (1 : Real) / 4)
  have hlogq : Real.log R <= 4 * q := by
    dsimp [q] at hlogq0 ⊢
    nlinarith
  have hcoef :
      128 * sparseA ^ 2 * sparseRho <= (1 : Real) / 4 := by
    rw [sparse_cross_exponent_eq]
    norm_num [zpow_neg]
  have harg :
      128 * sparseA ^ 2 * sparseRho * (B : Real) <=
        Real.log R * ((1 : Real) / 4) := by
    calc
      128 * sparseA ^ 2 * sparseRho * (B : Real) <=
          ((1 : Real) / 4) * (B : Real) :=
        mul_le_mul_of_nonneg_right hcoef (Nat.cast_nonneg B)
      _ <= ((1 : Real) / 4) * Real.log R :=
        mul_le_mul_of_nonneg_left hB (by norm_num)
      _ = Real.log R * ((1 : Real) / 4) := by ring
  have hexp :
      Real.exp (128 * sparseA ^ 2 * sparseRho * (B : Real)) <= q := by
    dsimp [q]
    rw [Real.rpow_def_of_pos hRpos]
    exact Real.exp_le_exp.mpr harg
  have hBq : (B : Real) <= 4 * q := hB.trans hlogq
  have hq0 : 0 <= q := Real.rpow_nonneg hR0 _
  have hsqrtRpos : 0 < Real.sqrt R := Real.sqrt_pos.2 hRpos
  have hqq : q * q = Real.sqrt R := by
    dsimp [q]
    rw [← Real.rpow_add hRpos]
    rw [Real.sqrt_eq_rpow]
    congr 1
    norm_num
  have hratio : q * q / R = 1 / Real.sqrt R := by
    rw [hqq]
    field_simp [hRpos.ne', hsqrtRpos.ne']
    simpa [pow_two] using Real.sq_sqrt hR0
  have hrbase : (2 : Real) ^ 32 <= R := by
    dsimp [R]
    exact_mod_cast hr
  have hsqrtBase : Real.sqrt ((2 : Real) ^ 32) = (2 : Real) ^ 16 := by
    rw [show (2 : Real) ^ 32 = ((2 : Real) ^ 16) ^ 2 by ring]
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg]
    positivity
  have hsqrtLower : (2 : Real) ^ 16 <= Real.sqrt R := by
    rw [← hsqrtBase]
    exact Real.sqrt_le_sqrt hrbase
  have hinv : 1 / Real.sqrt R <= 1 / (2 : Real) ^ 16 :=
    one_div_le_one_div_of_le (by positivity) hsqrtLower
  have hpref0 : 0 <= 16 * sparseA ^ 2 * sparseRho := by
    exact mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg sparseA))
      sparseRho_pos.le
  calc
    (16 * sparseA ^ 2 * sparseRho * (B : Real) / R) *
        Real.exp (128 * sparseA ^ 2 * sparseRho * (B : Real)) <=
      (16 * sparseA ^ 2 * sparseRho * (4 * q) / R) * q := by
        gcongr
    _ = (16 * sparseA ^ 2 * sparseRho) * 4 * (q * q / R) := by ring
    _ = (16 * sparseA ^ 2 * sparseRho) * 4 *
        (1 / Real.sqrt R) := by rw [hratio]
    _ <= (16 * sparseA ^ 2 * sparseRho) * 4 *
        (1 / (2 : Real) ^ 16) := by
      exact mul_le_mul_of_nonneg_left hinv
        (mul_nonneg hpref0 (by norm_num))
    _ = (2 : Real) ^ (-58 : Int) := by
      rw [sparse_cross_prefactor_eq]
      norm_num [zpow_neg]

/-- The exact average chi-square right-hand side in the manuscript is below
`2^-30`. -/
theorem sparse_mixture_chiSquare_budget
    {r B : Nat} (hr : 2 ^ 32 <= r)
    (hB : (B : Real) <= Real.log (r : Real)) :
    (Real.exp (10 * sparseA ^ 2 * (B : Real)) - 1) / (r : Real) +
      (16 * sparseA ^ 2 * sparseRho * (B : Real) / (r : Real)) *
        Real.exp (128 * sparseA ^ 2 * sparseRho * (B : Real)) <=
      (2 : Real) ^ (-30 : Int) := by
  have hd := sparse_mixture_diagonal_term_le hr hB
  have hc := sparse_mixture_cross_term_le hr hB
  calc
    (Real.exp (10 * sparseA ^ 2 * (B : Real)) - 1) / (r : Real) +
        (16 * sparseA ^ 2 * sparseRho * (B : Real) / (r : Real)) *
          Real.exp (128 * sparseA ^ 2 * sparseRho * (B : Real)) <=
      (2 : Real) ^ (-31 : Int) + (2 : Real) ^ (-58 : Int) :=
        add_le_add hd hc
    _ <= (2 : Real) ^ (-30 : Int) := by norm_num [zpow_neg]

/-- The numerical chi-square budget with `r` and `B` instantiated by the
manuscript's integer parameters. -/
theorem sparse_mixture_chiSquare_budget_parameters
    {n k : Nat} (hr : 2 ^ 32 <= sparseRatio n k) :
    (Real.exp
          (10 * sparseA ^ 2 * (sparseBlockCount n k : Real)) - 1) /
        (sparseRatio n k : Real) +
      (16 * sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) /
          (sparseRatio n k : Real)) *
        Real.exp (128 * sparseA ^ 2 * sparseRho *
          (sparseBlockCount n k : Real)) <=
      (2 : Real) ^ (-30 : Int) := by
  apply sparse_mixture_chiSquare_budget hr
  apply Nat.floor_le
  apply Real.log_nonneg
  exact_mod_cast ((by norm_num : 1 <= 2 ^ 32).trans hr)

#print axioms sparse_mixture_diagonal_term_le
#print axioms sparse_mixture_cross_term_le
#print axioms sparse_mixture_chiSquare_budget
#print axioms sparse_mixture_chiSquare_budget_parameters

end

end MsetsLower.Lower.Sparse
