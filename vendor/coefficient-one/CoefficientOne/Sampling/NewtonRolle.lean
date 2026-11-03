import CoefficientOne.Sampling.RestrictedElementary
import Mathlib.Analysis.Calculus.LocalExtr.Polynomial
import Mathlib.Algebra.Order.Chebyshev

/-!
# Rolle and the logarithmic-derivative step in Newton's inequality

The proof counts roots with multiplicity, applies Rolle to each derivative,
and uses the two logarithmic-derivative identities followed by Cauchy–Schwarz.
-/

open scoped BigOperators Topology
open Polynomial Filter

namespace CoefficientOne.Sampling

noncomputable section

/-- Rolle, with multiplicity, preserves real splitting under differentiation. -/
theorem splits_derivative_by_rolle (p : ℝ[X]) (hp : p.Splits) : p.derivative.Splits := by
  apply Polynomial.splits_iff_card_roots.mpr
  apply Nat.le_antisymm (Polynomial.card_roots' _)
  have h := Polynomial.card_roots_le_derivative p
  rw [(Polynomial.splits_iff_card_roots.mp hp)] at h
  rw [Polynomial.natDegree_derivative]
  omega

theorem splits_iterated_derivative_by_rolle (p : ℝ[X]) (hp : p.Splits) (j : ℕ) :
    (Polynomial.derivative^[j] p).Splits := by
  induction j with
  | zero => simpa using hp
  | succ j ih =>
    simpa only [Function.iterate_succ_apply'] using
      splits_derivative_by_rolle (Polynomial.derivative^[j] p) ih

def rootReciprocalSum (roots : List ℝ) (x : ℝ) : ℝ :=
  (roots.map fun r => (x - r)⁻¹).sum

def rootReciprocalSquareSum (roots : List ℝ) (x : ℝ) : ℝ :=
  (roots.map fun r => ((x - r)⁻¹) ^ 2).sum

theorem rootReciprocalSum_hasDerivAt (roots : List ℝ) (x : ℝ)
    (hx : ∀ r ∈ roots, x - r ≠ 0) :
    HasDerivAt (rootReciprocalSum roots) (-rootReciprocalSquareSum roots x) x := by
  induction roots with
  | nil =>
    have hf : rootReciprocalSum [] = fun _ : ℝ => (0 : ℝ) := by
      funext y
      simp [rootReciprocalSum]
    rw [hf]
    simp only [rootReciprocalSquareSum, List.map_nil, List.sum_nil, neg_zero]
    exact hasDerivAt_const x (0 : ℝ)
  | cons r roots ih =>
    have hr := hx r (by simp)
    have ht := ih (fun a ha => hx a (by simp [ha]))
    have hi := ((hasDerivAt_id x).sub_const r).inv hr
    have hf : rootReciprocalSum (r :: roots) =
        fun y => (y - r)⁻¹ + rootReciprocalSum roots y := by
      funext y
      simp [rootReciprocalSum]
    rw [hf]
    convert! hi.add ht using 1 <;>
      first | rfl | simp [rootReciprocalSquareSum, inv_pow, div_eq_mul_inv, add_comm]

theorem rootReciprocalSum_cauchy (roots : List ℝ) (x : ℝ) :
    rootReciprocalSum roots x ^ 2 ≤
      (roots.length : ℝ) * rootReciprocalSquareSum roots x := by
  let f : Fin roots.length → ℝ := fun i => (x - roots.get i)⁻¹
  have hs : rootReciprocalSum roots x = ∑ i, f i := by
    rw [← List.sum_ofFn]
    change (roots.map fun r => (x - r)⁻¹).sum =
      (List.ofFn fun i : Fin roots.length => (x - roots[i.val])⁻¹).sum
    rw [List.ofFn_getElem_eq_map roots (fun r : ℝ => (x - r)⁻¹)]
  have hsq : rootReciprocalSquareSum roots x = ∑ i, (f i) ^ 2 := by
    rw [← List.sum_ofFn]
    change (roots.map fun r => ((x - r)⁻¹) ^ 2).sum =
      (List.ofFn fun i : Fin roots.length => ((x - roots[i.val])⁻¹) ^ 2).sum
    rw [List.ofFn_getElem_eq_map roots (fun r : ℝ => ((x - r)⁻¹) ^ 2)]
  rw [hs, hsq]
  simpa only [Finset.card_univ, Fintype.card_fin] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.univ) (f := f))

theorem eval_derivative_eq_rootReciprocalSum (p : ℝ[X]) (hp : p.Splits)
    (x : ℝ) (hx : p.eval x ≠ 0) :
    p.derivative.eval x = p.eval x * rootReciprocalSum p.roots.toList x := by
  simpa [rootReciprocalSum, one_div] using hp.eval_derivative_eq_eval_mul_sum hx

/-- The second logarithmic-derivative identity, at a point away from roots. -/
theorem eval_second_derivative_eq_root_sums (p : ℝ[X]) (hp : p.Splits)
    (x : ℝ) (hx : p.eval x ≠ 0) :
    p.derivative.derivative.eval x = p.eval x *
      (rootReciprocalSum p.roots.toList x ^ 2 - rootReciprocalSquareSum p.roots.toList x) := by
  have hp0 : p ≠ 0 := by
    intro h
    apply hx
    simp [h]
  have hroots : ∀ r ∈ p.roots.toList, x - r ≠ 0 := by
    intro r hr heq
    have hr' : r ∈ p.roots := by simpa using hr
    have hroot := (Polynomial.mem_roots hp0).mp hr'
    apply hx
    simpa only [sub_eq_zero.mp heq] using hroot.eq_zero
  have hs := rootReciprocalSum_hasDerivAt p.roots.toList x hroots
  have hprod := (p.hasDerivAt x).mul hs
  have heq : (fun y => p.derivative.eval y) =ᶠ[𝓝 x]
      (fun y => p.eval y * rootReciprocalSum p.roots.toList y) := by
    filter_upwards [p.continuous.continuousAt.eventually_ne hx] with y hy
    exact eval_derivative_eq_rootReciprocalSum p hp y hy
  have hsecond := (hprod.congr_of_eventuallyEq heq).unique (p.derivative.hasDerivAt x)
  rw [eval_derivative_eq_rootReciprocalSum p hp x hx] at hsecond
  nlinarith [hsecond]

/-- The normalized Newton estimate for a real-split polynomial, before
substituting factorials and the elementary-symmetric coefficients. -/
theorem realSplit_newton_at (p : ℝ[X]) (hp : p.Splits) (x : ℝ) (hx : p.eval x ≠ 0) :
    (p.natDegree : ℝ) * p.eval x * p.derivative.derivative.eval x ≤
      ((p.natDegree : ℝ) - 1) * (p.derivative.eval x) ^ 2 := by
  have hc := mul_le_mul_of_nonneg_left (rootReciprocalSum_cauchy p.roots.toList x)
    (sq_nonneg (p.eval x))
  have hlength : p.roots.toList.length = p.natDegree := by
    simpa using (Polynomial.splits_iff_card_roots.mp hp)
  rw [hlength] at hc
  rw [eval_derivative_eq_rootReciprocalSum p hp x hx,
    eval_second_derivative_eq_root_sums p hp x hx]
  nlinarith [hc]

end
end CoefficientOne.Sampling
