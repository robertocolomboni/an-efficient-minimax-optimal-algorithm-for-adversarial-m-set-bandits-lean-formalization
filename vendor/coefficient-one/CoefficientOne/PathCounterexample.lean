import CoefficientOne.GraphExamples
import EffectiveResistance.GreenKernelExistence

/-!
# A path completed with small positive conductances

There are `k + 1` vertices. Path edges have conductance one; all other
off-diagonal conductances are ε when ε ≥ 0. Using `max ε 0` defines the
same networks on the relevant half-line and provides a continuous extension.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

def perturbedPathNetwork (k : ℕ) (ε : ℝ) : ConductanceNetwork (Fin (k + 1)) where
  conductance i j := if i = j then 0 else
    if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else max ε 0
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    by_cases hij : i = j
    · subst j; simp
    · simp [hij, Ne.symm hij, or_comm]
  nonnegative := by
    intro i j
    split_ifs <;> positivity
  diagonal_zero i := by simp

/-- On the relevant half-line these are exactly the conductances stated
in the manuscript, with no truncation of the parameter. -/
theorem perturbedPathNetwork_conductance_of_nonnegative
    (k : ℕ) (ε : ℝ) (hε : 0 ≤ ε) (i j : Fin (k + 1)) :
    (perturbedPathNetwork k ε).conductance i j =
      if i = j then 0 else
        if i.val + 1 = j.val ∨ j.val + 1 = i.val then 1 else ε := by
  simp only [perturbedPathNetwork, max_eq_left hε]

theorem perturbedPathNetwork_adjacent (k : ℕ) (ε : ℝ) (i : Fin k) :
    (perturbedPathNetwork k ε).conductance i.castSucc i.succ = 1 := by
  simp [perturbedPathNetwork, Fin.ext_iff]

theorem perturbedPathNetwork_strictlyComplete (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    (perturbedPathNetwork k ε).IsStrictlyComplete := by
  intro i j hij
  simp only [perturbedPathNetwork, if_neg hij]
  split_ifs
  · norm_num
  · exact lt_max_of_lt_left hε

/-- Zero Dirichlet energy forces equality across each positive-conductance edge. -/
theorem equal_on_positive_edge_of_energy_zero
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ConductanceNetwork ι) (x : ι → ℝ) (hx : N.energy x = 0)
    (i j : ι) (hij : 0 < N.conductance i j) : x i = x j := by
  have hsum : N.edgePairingSum x x = 0 := by
    rw [N.energy_eq_half_edgePairingSum] at hx
    exact (mul_eq_zero.mp hx).resolve_left (inv_ne_zero (by norm_num : (2 : ℝ) ≠ 0))
  have hterm : ∀ p ∈ (Finset.univ : Finset (ι × ι)),
      0 ≤ N.conductance p.1 p.2 * (x p.1 - x p.2) * (x p.1 - x p.2) := by
    intro p hp
    nlinarith [N.nonnegative p.1 p.2, sq_nonneg (x p.1 - x p.2)]
  have hle : N.conductance i j * (x i - x j) * (x i - x j) ≤ N.edgePairingSum x x :=
    Finset.single_le_sum hterm (Finset.mem_univ (i, j))
  rw [hsum] at hle
  have hs : (x i - x j) ^ 2 = 0 := by
    have hz : N.conductance i j * (x i - x j) ^ 2 = 0 := by
      nlinarith [mul_nonneg hij.le (sq_nonneg (x i - x j))]
    exact (mul_eq_zero.mp hz).resolve_left hij.ne'
  nlinarith

/-- The path edges alone force every zero-energy potential to be constant. -/
theorem perturbedPathNetwork_energy_zero_constant
    (k : ℕ) (ε : ℝ) (x : Fin (k + 1) → ℝ)
    (hx : (perturbedPathNetwork k ε).energy x = 0) : ∀ i j, x i = x j := by
  have hadj (i : Fin k) : x i.castSucc = x i.succ := by
    apply equal_on_positive_edge_of_energy_zero (perturbedPathNetwork k ε) x hx
    rw [perturbedPathNetwork_adjacent]
    norm_num
  have hzero (i : Fin (k + 1)) : x i = x 0 := by
    induction i using Fin.induction with
    | zero => rfl
    | succ i hi => exact (hadj i).symm.trans hi
  intro i j
  exact (hzero i).trans (hzero j).symm

theorem perturbedPathNetwork_kernel_constant
    (k : ℕ) (ε : ℝ) (x : Fin (k + 1) → ℝ) :
    (perturbedPathNetwork k ε).laplacian *ᵥ x = 0 ↔ ∀ i j, x i = x j := by
  constructor
  · intro hx
    apply perturbedPathNetwork_energy_zero_constant k ε x
    simp [ConductanceNetwork.energy, ConductanceNetwork.energyPairing, hx]
  · intro hx
    have heq : x = x 0 • (fun _ => (1 : ℝ)) := by
      ext i
      simpa using hx i 0
    rw [heq, Matrix.mulVec_smul, ConductanceNetwork.laplacian_mulVec_one, smul_zero]

theorem perturbedPathNetwork_continuous_conductance (k : ℕ)
    (i j : Fin (k + 1)) : Continuous (fun ε => (perturbedPathNetwork k ε).conductance i j) := by
  simp only [perturbedPathNetwork]
  split_ifs <;> fun_prop

theorem perturbedPathNetwork_continuous_laplacian (k : ℕ) :
    Continuous (fun ε => (perturbedPathNetwork k ε).laplacian) := by
  apply continuous_pi
  intro i
  apply continuous_pi
  intro j
  simp only [ConductanceNetwork.laplacian_apply]
  split_ifs
  · exact continuous_finsetSum _ (fun l hl => perturbedPathNetwork_continuous_conductance k i l)
  · exact (perturbedPathNetwork_continuous_conductance k i j).neg

/-- The linear potential has unit current on each path edge and no other edges at ε=0. -/
theorem path_linear_current_term (k : ℕ) (i j : Fin (k + 1)) :
    (perturbedPathNetwork k 0).conductance i j *
      (-(i.val : ℝ) - -(j.val : ℝ)) =
        (if j.val = i.val + 1 then (1 : ℝ) else 0) -
        (if j.val + 1 = i.val then (1 : ℝ) else 0) := by
  by_cases hij : i = j
  · subst j
    simp [perturbedPathNetwork]
  · by_cases hnext : j.val = i.val + 1
    · have hprev : ¬ j.val + 1 = i.val := by omega
      have hcast : (j.val : ℝ) = (i.val : ℝ) + 1 := by exact_mod_cast hnext
      have hc : (perturbedPathNetwork k 0).conductance i j = 1 := by
        simp only [perturbedPathNetwork, if_neg hij, if_pos (Or.inl hnext.symm)]
      rw [hc, if_pos hnext, if_neg hprev]
      linarith
    · by_cases hprev : j.val + 1 = i.val
      · have hcast : (j.val : ℝ) + 1 = (i.val : ℝ) := by exact_mod_cast hprev
        have hc : (perturbedPathNetwork k 0).conductance i j = 1 := by
          simp only [perturbedPathNetwork, if_neg hij, if_pos (Or.inr hprev)]
        rw [hc, if_neg hnext, if_pos hprev]
        linarith
      · simp [perturbedPathNetwork, hij, hnext, Ne.symm hnext, hprev]

theorem path_forward_sum (k : ℕ) (i : Fin (k + 1)) :
    (∑ j : Fin (k + 1), if j.val = i.val + 1 then (1 : ℝ) else 0) =
      if i = Fin.last k then 0 else 1 := by
  by_cases hi : i = Fin.last k
  · subst i
    have hfalse (j : Fin (k + 1)) : ¬ j.val = k + 1 := by omega
    simp [hfalse]
  · have hlt : i.val + 1 < k + 1 := by
      have hne : i.val ≠ k := by intro heq; apply hi; exact Fin.ext heq
      omega
    let j₀ : Fin (k + 1) := ⟨i.val + 1, hlt⟩
    have hcond (j : Fin (k + 1)) : j.val = i.val + 1 ↔ j = j₀ := by
      change j.val = j₀.val ↔ j = j₀
      exact Fin.ext_iff.symm
    simp only [hcond, if_neg hi]
    simp

theorem path_backward_sum (k : ℕ) (i : Fin (k + 1)) :
    (∑ j : Fin (k + 1), if j.val + 1 = i.val then (1 : ℝ) else 0) =
      if i = 0 then 0 else 1 := by
  by_cases hi : i = 0
  · subst i
    simp
  · have hpos : 0 < i.val := by
      have hne : i.val ≠ 0 := by intro heq; apply hi; exact Fin.ext heq
      omega
    let j₀ : Fin (k + 1) := ⟨i.val - 1, by omega⟩
    have hcond (j : Fin (k + 1)) : j.val + 1 = i.val ↔ j = j₀ := by
      rw [Fin.ext_iff]
      dsimp [j₀]
      omega
    simp only [hcond, if_neg hi]
    simp

theorem path_linear_potential_solves (k : ℕ) :
    (perturbedPathNetwork k 0).laplacian *ᵥ (fun i : Fin (k + 1) => -(i.val : ℝ)) =
      pairDemand 0 (Fin.last k) := by
  ext i
  rw [ConductanceNetwork.laplacian_mulVec]
  simp_rw [path_linear_current_term]
  rw [Finset.sum_sub_distrib, path_forward_sum, path_backward_sum]
  simp only [pairDemand]
  split_ifs <;> norm_num

/-- Every Green kernel of the uncompleted path has endpoint resistance k. -/
theorem path_effectiveResistance (k : ℕ) (hk : 1 ≤ k)
    (G : GreenKernel (perturbedPathNetwork k 0)) :
    G.effectiveResistance 0 (Fin.last k) = k := by
  have hij : (0 : Fin (k + 1)) ≠ Fin.last k := by
    intro h
    have := congrArg Fin.val h
    simp at this
    omega
  rw [G.effectiveResistance_eq_solution_drop hij
    (fun i : Fin (k + 1) => -(i.val : ℝ)) (path_linear_potential_solves k)]
  simp

theorem perturbedPathNetwork_degree_zero (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) :
    (perturbedPathNetwork k ε).degree 0 = 1 + ((k - 1 : ℕ) : ℝ) * max ε 0 := by
  letI : NeZero k := ⟨by omega⟩
  have hterm (j : Fin k) : (perturbedPathNetwork k ε).conductance 0 j.succ =
      max ε 0 + (if j = 0 then 1 - max ε 0 else 0) := by
    by_cases hj : j = 0
    · subst j
      simp [perturbedPathNetwork, Fin.ext_iff, Nat.mod_eq_of_lt (by omega : 1 < k + 1)]
    · have hjval : j.val ≠ 0 := by intro h; exact hj (Fin.ext h)
      simp [perturbedPathNetwork, Fin.ext_iff, hjval]
  rw [ConductanceNetwork.degree, Fin.sum_univ_succ]
  simp only [ConductanceNetwork.diagonal_zero, zero_add]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Nat.cast_sub hk]
  push_cast
  ring

theorem perturbedPathNetwork_degree_last (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) :
    (perturbedPathNetwork k ε).degree (Fin.last k) =
      1 + ((k - 1 : ℕ) : ℝ) * max ε 0 := by
  let j₀ : Fin k := ⟨k - 1, by omega⟩
  have hterm (j : Fin k) :
      (perturbedPathNetwork k ε).conductance (Fin.last k) j.castSucc =
        max ε 0 + (if j = j₀ then 1 - max ε 0 else 0) := by
    have hne : (Fin.last k : Fin (k + 1)) ≠ j.castSucc := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hnext : ¬ k + 1 = j.val := by omega
    have hprev : j.val + 1 = k ↔ j = j₀ := by
      rw [Fin.ext_iff]
      dsimp [j₀]
      omega
    simp only [perturbedPathNetwork, if_neg hne, Fin.val_last,
      Fin.val_castSucc, hnext, false_or, hprev]
    split_ifs <;> ring
  rw [ConductanceNetwork.degree, Fin.sum_univ_castSucc]
  simp only [ConductanceNetwork.diagonal_zero, add_zero]
  simp_rw [hterm]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Nat.cast_sub hk]
  push_cast
  ring

/-- Both terminal degrees in the family from the manuscript. -/
theorem perturbedPathNetwork_endpoint_degrees
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 ≤ ε) :
    (perturbedPathNetwork k ε).degree 0 = 1 + ((k - 1 : ℕ) : ℝ) * ε ∧
    (perturbedPathNetwork k ε).degree (Fin.last k) = 1 + ((k - 1 : ℕ) : ℝ) * ε := by
  rw [perturbedPathNetwork_degree_zero k hk, perturbedPathNetwork_degree_last k hk,
    max_eq_left hε]
  exact ⟨rfl, rfl⟩

end

end CoefficientOne
