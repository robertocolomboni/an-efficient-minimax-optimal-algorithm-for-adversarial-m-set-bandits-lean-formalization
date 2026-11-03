import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.GCongr

/-!
# Algebraic and expectation clauses of Lemma 1

The coordinates below are the actual binary action coordinates. No leverage
inequality is assumed or proved here: the matrix/pseudoinverse connection is
a separate obligation. The affine formula, mean, and range are independent
of that connection and hold for any finite binary-action distribution.
-/

namespace MsetsPaper.Upper

open scoped BigOperators

noncomputable section

def phi {d : ℕ} (μ x : Fin d → ℝ) : ℝ :=
  1 + ∑ i, (x i - μ i) ^ 2 / (μ i * (1 - μ i))

def correction {d : ℕ} (m : ℝ) (μ : Fin d → ℝ) (i : Fin d) : ℝ :=
  4 * ((1 + ∑ j, μ j / (1 - μ j)) / m +
    (1 - 2 * μ i) / (μ i * (1 - μ i)))

theorem binary_variance_affine (μ x : ℝ) (hμ : 0 < μ) (hμ1 : μ < 1)
    (hx : x = 0 ∨ x = 1) :
    (x - μ) ^ 2 / (μ * (1 - μ)) =
      μ / (1 - μ) + x * ((1 - 2 * μ) / (μ * (1 - μ))) := by
  rcases hx with rfl | rfl <;>
    field_simp [ne_of_gt hμ, ne_of_gt (sub_pos.mpr hμ1)] <;> ring

theorem phi_affine {d : ℕ} (μ x : Fin d → ℝ)
    (hμ : ∀ i, 0 < μ i) (hμ1 : ∀ i, μ i < 1)
    (hx : ∀ i, x i = 0 ∨ x i = 1) :
    phi μ x = 1 + ∑ i, μ i / (1 - μ i) +
      ∑ i, x i * ((1 - 2 * μ i) / (μ i * (1 - μ i))) := by
  simp only [phi, binary_variance_affine _ _ (hμ _) (hμ1 _) (hx _),
    Finset.sum_add_distrib, add_assoc]

theorem correction_dot {d : ℕ} (m : ℝ) (hm : m ≠ 0) (μ x : Fin d → ℝ)
    (hμ : ∀ i, 0 < μ i) (hμ1 : ∀ i, μ i < 1)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hcard : ∑ i, x i = m) :
    ∑ i, correction m μ i * x i = 4 * phi μ x := by
  rw [phi_affine μ x hμ hμ1 hx]
  simp only [correction, mul_add, add_mul, Finset.sum_add_distrib]
  rw [← Finset.mul_sum, hcard]
  have hc : (4 * ((1 + ∑ j, μ j / (1 - μ j)) / m)) * m =
      4 * (1 + ∑ j, μ j / (1 - μ j)) := by field_simp
  rw [hc]
  rw [mul_add, Finset.mul_sum]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem phi_nonneg {d : ℕ} (μ x : Fin d → ℝ)
    (hμ : ∀ i, 0 < μ i) (hμ1 : ∀ i, μ i < 1) :
    0 ≤ phi μ x := by
  unfold phi
  apply add_nonneg (by norm_num)
  exact Finset.sum_nonneg (fun i _ ↦ div_nonneg (sq_nonneg _)
    (mul_pos (hμ i) (sub_pos.mpr (hμ1 i))).le)

/-- The elementary binary variance identity under a normalized finite law. -/
theorem binary_variance_mean {α : Type*} [Fintype α] (p x : α → ℝ)
    (hp : ∑ a, p a = 1) (hx : ∀ a, x a = 0 ∨ x a = 1) :
    ∑ a, p a * (x a - ∑ b, p b * x b) ^ 2 =
      (∑ b, p b * x b) * (1 - ∑ b, p b * x b) := by
  classical
  let μ := ∑ b, p b * x b
  calc
    _ = ∑ a, (p a * x a - 2 * μ * (p a * x a) + p a * μ ^ 2) := by
      apply Finset.sum_congr rfl
      intro a _
      change p a * (x a - μ) ^ 2 = _
      rcases hx a with h | h <;> rw [h] <;> ring
    _ = μ - 2 * μ * μ + μ ^ 2 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hp, one_mul]
      rfl
    _ = _ := by change μ - 2 * μ * μ + μ ^ 2 = μ * (1 - μ); ring

/-- This is the expectation under the actual finite law, not a hypothesis
asserting the desired mean. Nonnegativity of `p` is unnecessary for this identity. -/
theorem phi_mean {α : Type*} [Fintype α] {d : ℕ}
    (p : α → ℝ) (x : α → Fin d → ℝ)
    (hp : ∑ a, p a = 1) (hx : ∀ a i, x a i = 0 ∨ x a i = 1)
    (hμ : ∀ i, 0 < ∑ a, p a * x a i)
    (hμ1 : ∀ i, (∑ a, p a * x a i) < 1) :
    ∑ a, p a * phi (fun i ↦ ∑ b, p b * x b i) (x a) = (d : ℝ) + 1 := by
  classical
  let μ : Fin d → ℝ := fun i ↦ ∑ a, p a * x a i
  change ∑ a, p a * phi μ (x a) = _
  simp only [phi, mul_add, mul_one, Finset.mul_sum, Finset.sum_add_distrib]
  rw [hp, Finset.sum_comm]
  have hi : ∀ i, (∑ a, p a * ((x a i - μ i) ^ 2 / (μ i * (1 - μ i)))) = 1 := by
    intro i
    simp only [← mul_div_assoc, ← Finset.sum_div]
    rw [binary_variance_mean p (fun a ↦ x a i) hp (fun a ↦ hx a i)]
    exact div_self (mul_ne_zero (ne_of_gt (hμ i)) (ne_of_gt (sub_pos.mpr (hμ1 i))))
  simp only [hi, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    mul_one]
  ring

theorem binary_variance_bound (μ x a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hlo : a ≤ μ) (hhi : b ≤ 1 - μ) (hx : x = 0 ∨ x = 1) :
    (x - μ) ^ 2 / (μ * (1 - μ)) ≤ x / a + (1 - x) / b := by
  have hμ : 0 < μ := ha.trans_le hlo
  have hμ1 : 0 < 1 - μ := hb.trans_le hhi
  rcases hx with rfl | rfl
  · have hid : (0 - μ) ^ 2 / (μ * (1 - μ)) = μ / (1 - μ) := by
      field_simp
      ring
    rw [hid]
    simp only [zero_div, sub_zero, zero_add]
    calc
      μ / (1 - μ) ≤ 1 / (1 - μ) := by gcongr; linarith
      _ ≤ 1 / b := one_div_le_one_div_of_le hb hhi
  · have hid : (1 - μ) ^ 2 / (μ * (1 - μ)) = (1 - μ) / μ := by
      field_simp
    rw [hid]
    simp only [sub_self, zero_div, add_zero]
    calc
      (1 - μ) / μ ≤ 1 / μ := by gcongr; linarith
      _ ≤ 1 / a := one_div_le_one_div_of_le ha hlo

theorem phi_range_general {d : ℕ} (μ x : Fin d → ℝ) (m a b : ℝ)
    (ha : 0 < a) (hb : 0 < b)
    (hlo : ∀ i, a ≤ μ i) (hhi : ∀ i, b ≤ 1 - μ i)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hcard : ∑ i, x i = m) :
    phi μ x ≤ 1 + m / a + ((d : ℝ) - m) / b := by
  calc
    phi μ x ≤ 1 + ∑ i, (x i / a + (1 - x i) / b) := by
      exact add_le_add le_rfl (Finset.sum_le_sum (fun i _ ↦
        binary_variance_bound (μ i) (x i) a b ha hb (hlo i) (hhi i) (hx i)))
    _ = _ := by
      simp only [Finset.sum_add_distrib, ← Finset.sum_div, Finset.sum_sub_distrib,
        hcard, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_one]
      ring

/-- The precise range in Lemma 1, using the two marginal constraints defining
`P_λ`, rather than an unjustified uniform per-coordinate bound. -/
theorem phi_range {d m : ℕ} (hm : 0 < m) (hmd : m < d)
    (μ x : Fin d → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hlo : ∀ i, lam * ((m : ℝ) / d) ≤ μ i)
    (hhi : ∀ i, lam * (1 - (m : ℝ) / d) ≤ 1 - μ i)
    (hx : ∀ i, x i = 0 ∨ x i = 1) (hcard : ∑ i, x i = (m : ℝ)) :
    0 ≤ phi μ x ∧ phi μ x ≤ 1 + 2 * d / lam := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hdR : 0 < (d : ℝ) := by exact_mod_cast (lt_trans hm hmd)
  have hmdR : (m : ℝ) < d := by exact_mod_cast hmd
  have hr : (m : ℝ) / d < 1 := (div_lt_one hdR).mpr hmdR
  have ha : 0 < lam * ((m : ℝ) / d) := mul_pos hlam (div_pos hmR hdR)
  have hb : 0 < lam * (1 - (m : ℝ) / d) := mul_pos hlam (sub_pos.mpr hr)
  refine ⟨phi_nonneg μ x (fun i ↦ ha.trans_le (hlo i))
    (fun i ↦ by linarith [hb.trans_le (hhi i)]), ?_⟩
  refine (phi_range_general μ x (m : ℝ) _ _ ha hb hlo hhi hx hcard).trans_eq ?_
  have hdm : (d : ℝ) - m ≠ 0 := ne_of_gt (sub_pos.mpr hmdR)
  field_simp
  ring

end

end MsetsPaper.Upper
