import MsetsPaper.Upper.AlgorithmInvariantMW
import MsetsPaper.Probability.FiniteTree

/-! # P1: non-circular induction from the projection procedure's local contract

The procedure contract is an explicit premise still to be instantiated by
the certified ellipsoid program. In particular, this theorem does not
postulate its own global marginal or uniform-KL invariant.
-/

noncomputable section
open MsetsLower MsetsPaper.Probability
open scoped BigOperators

namespace MsetsPaper.Upper

variable {d m : ℕ}

theorem uniform_marginal_box (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1)
    {lam : ℝ} (hlam : lam ≤ 1) (i : Fin d) :
    lam * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (0 : Fin d → ℝ) i ∧
      weightedMarginal (m := m) (0 : Fin d → ℝ) i ≤ 1 - lam * (1 - (m : ℝ) / d) := by
  rw [weightedMarginal_zero_eq hmpos hmtop]
  have hd : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hr : 0 ≤ (m : ℝ) / d := by positivity
  have hr1 : (m : ℝ) / d ≤ 1 := (div_le_one hd).mpr (by exact_mod_cast (show m ≤ d by omega))
  constructor <;> nlinarith

theorem finiteKL_weightedLaw_self (theta : Fin d → ℝ) (hmd : m ≤ d) :
    finiteKL (weightedLaw (m := m) theta) (weightedLaw theta) = 0 := by
  unfold finiteKL
  simp only [div_self (weightedLaw_pos theta hmd _).ne', Real.log_one, mul_zero, Finset.sum_const_zero]

theorem algorithm_invariant_of_projection_contract
    (theta ell : (t : ℕ) → ActionTree (Action d m) t → Fin d → ℝ)
    (hmpos : 1 ≤ m) (hmtop : m ≤ d - 1) (T : ℕ) (hT : 0 < T)
    {eta : ℝ} (heta : 0 < eta) (hsmall : eta ≤ 1 / 64)
    (hlam : 128 * eta * d ≤ 1 / 2) (hzero : theta 0 () = 0)
    (hloss : ∀ t < T, ∀ h (a : Action d m), |actionLoss a (ell t h)| ≤ 1)
    (hproject : ∀ t < T, ∀ h a,
      let z := theta t h - eta • surrogateVector (theta t h) (ell t h) eta a
      let next := theta (t + 1) (h, a)
      finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw z) ≤ T →
      (∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) next i ∧
        weightedMarginal (m := m) next i ≤ 1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) ∧
      (∀ q : Action d m → ℝ, (∀ b, 0 ≤ q b) → (∑ b, q b) = 1 →
        (∀ i, 128 * eta * d * ((m : ℝ) / d) ≤ marginal q i ∧
          marginal q i ≤ 1 - 128 * eta * d * (1 - (m : ℝ) / d)) →
        finiteKL q (weightedLaw (m := m) next) ≤ finiteKL q (weightedLaw z) -
          finiteKL (weightedLaw (m := m) next) (weightedLaw z) + eta / T)) :
    ∀ t ≤ T, ∀ h,
      (∀ i, (128 * eta * d / 2) * ((m : ℝ) / d) ≤ weightedMarginal (m := m) (theta t h) i ∧
        weightedMarginal (m := m) (theta t h) i ≤
          1 - (128 * eta * d / 2) * (1 - (m : ℝ) / d)) ∧
      finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw (theta t h)) ≤ t := by
  have hmd : m ≤ d := by omega
  have hTr : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hTpos : (0 : ℝ) < T := by positivity
  have heps : eta / T ≤ 1 / 64 := by
    have hh : eta / T ≤ eta := (div_le_iff₀ hTpos).mpr (by nlinarith)
    exact hh.trans hsmall
  have hUbox := uniform_marginal_box hmpos hmtop (show 128 * eta * d ≤ 1 by linarith)
  intro t
  induction t with
  | zero =>
    intro ht h
    cases h
    rw [hzero]
    refine ⟨uniform_marginal_box hmpos hmtop (by linarith), ?_⟩
    rw [finiteKL_weightedLaw_self _ hmd]
    norm_num
  | succ t ih =>
    intro ht
    rintro ⟨h, a⟩
    have htT : t < T := by omega
    obtain ⟨hbox, hKL⟩ := ih (by omega) h
    let z := theta t h - eta • surrogateVector (theta t h) (ell t h) eta a
    let next := theta (t + 1) (h, a)
    have hstep := unprojected_uniform_KL_le (theta t h) (ell t h) hmpos hmtop heta hsmall
      (fun i ↦ (hbox i).1) (fun i ↦ (hbox i).2) a (hloss t htT h)
    have htcast : (t : ℝ) + 1 ≤ T := by exact_mod_cast ht
    have hinput : finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw z) ≤ T := by
      dsimp [z]
      linarith
    obtain ⟨hnext, hproj⟩ := hproject t htT h a hinput
    refine ⟨hnext, ?_⟩
    have hu := hproj (weightedLaw (m := m) (0 : Fin d → ℝ))
      (fun b ↦ (weightedLaw_pos _ hmd b).le) (sum_weightedLaw _ hmd) hUbox
    have hnonneg := finiteKL_nonneg (weightedLaw (m := m) next) (weightedLaw z)
      (fun b ↦ (weightedLaw_pos next hmd b).le) (sum_weightedLaw next hmd)
      (weightedLaw_pos z hmd) (sum_weightedLaw z hmd)
    change finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw next) ≤ _
    change finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw next) ≤
      finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw z) -
        finiteKL (weightedLaw (m := m) next) (weightedLaw z) + eta / T at hu
    change finiteKL (weightedLaw (m := m) (0 : Fin d → ℝ)) (weightedLaw z) ≤ _ at hstep
    push_cast
    linarith

end MsetsPaper.Upper
