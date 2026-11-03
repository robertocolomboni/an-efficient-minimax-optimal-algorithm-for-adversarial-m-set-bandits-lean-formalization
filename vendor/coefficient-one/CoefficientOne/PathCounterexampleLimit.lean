import CoefficientOne.PathCounterexample
import CoefficientOne.RegularizedGreenKernel

/-!
# The complete-network counterexample in every dimension at least four

The resistance of the path completed with ε-conductances converges to its
path value as ε tends to zero. We justify the limit by the continuous inverse
of `L + J/d`; the kernel computation in `PathCounterexample` ensures this
matrix is invertible even at ε = 0. The endpoint inverse-degree sum tends
to two. Their strict limiting separation gives complete positive networks
violating the endpoint upper bound in every dimension at least four.
-/

open scoped BigOperators Topology
open Matrix EffectiveResistance Filter

namespace CoefficientOne

noncomputable section

def perturbedPathGreenKernel (k : ℕ) (ε : ℝ) : GreenKernel (perturbedPathNetwork k ε) :=
  regularizedGreenKernel (perturbedPathNetwork k ε)
    (fun x hx => (perturbedPathNetwork_kernel_constant k ε x).mp hx)

def perturbedPathResistance (k : ℕ) (ε : ℝ) : ℝ :=
  (perturbedPathGreenKernel k ε).effectiveResistance 0 (Fin.last k)

theorem perturbedPathResistance_formula (k : ℕ) (ε : ℝ) :
    perturbedPathResistance k ε =
      quadraticForm (regularizedLaplacian (perturbedPathNetwork k ε))⁻¹
        (pairDemand 0 (Fin.last k)) := rfl

theorem perturbedPathResistance_zero (k : ℕ) (hk : 1 ≤ k) :
    perturbedPathResistance k 0 = k :=
  path_effectiveResistance k hk (perturbedPathGreenKernel k 0)

/-- The limiting resistance is justified by continuity of an invertible
regularized Laplacian, including at the sparse limiting path. -/
theorem perturbedPathResistance_continuousAt_zero (k : ℕ) :
    ContinuousAt (perturbedPathResistance k) 0 := by
  let A : ℝ → Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ :=
    fun ε => regularizedLaplacian (perturbedPathNetwork k ε)
  have hA : Continuous A :=
    (perturbedPathNetwork_continuous_laplacian k).add continuous_const
  have hdet : (A 0).det ≠ 0 := regularizedLaplacian_det_ne_zero
    (perturbedPathNetwork k 0)
    (fun x hx => (perturbedPathNetwork_kernel_constant k 0 x).mp hx)
  have hinv : ContinuousAt (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ => M⁻¹) (A 0) := by
    apply continuousAt_matrix_inv
    simpa only [Ring.inverse_eq_inv'] using (continuousAt_inv₀ hdet)
  have hq : Continuous (fun M : Matrix (Fin (k + 1)) (Fin (k + 1)) ℝ =>
      quadraticForm M (pairDemand 0 (Fin.last k))) :=
    continuous_const.dotProduct (continuous_id.matrix_mulVec continuous_const)
  exact hq.continuousAt.comp (hinv.comp hA.continuousAt)

theorem perturbedPathResistance_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (perturbedPathResistance k) (𝓝 (0 : ℝ)) (𝓝 (k : ℝ)) := by
  simpa only [perturbedPathResistance_zero k hk] using
    (perturbedPathResistance_continuousAt_zero k).tendsto

theorem perturbedPathResistance_tendsto_right (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (perturbedPathResistance k) (𝓝[>] (0 : ℝ)) (𝓝 (k : ℝ)) :=
  (perturbedPathResistance_tendsto k hk).mono_left nhdsWithin_le_nhds

def perturbedPathInverseDegreeSum (k : ℕ) (ε : ℝ) : ℝ :=
  1 / (perturbedPathNetwork k ε).degree 0 +
    1 / (perturbedPathNetwork k ε).degree (Fin.last k)

theorem perturbedPathInverseDegreeSum_tendsto (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (perturbedPathInverseDegreeSum k) (𝓝 (0 : ℝ)) (𝓝 (2 : ℝ)) := by
  have hden : Continuous (fun ε : ℝ => 1 + ((k - 1 : ℕ) : ℝ) * max ε 0) := by fun_prop
  have hterm : ContinuousAt (fun ε : ℝ => 1 / (1 + ((k - 1 : ℕ) : ℝ) * max ε 0)) 0 :=
    continuousAt_const.div hden.continuousAt (by simp)
  have heq : perturbedPathInverseDegreeSum k = fun ε : ℝ =>
      1 / (1 + ((k - 1 : ℕ) : ℝ) * max ε 0) +
      1 / (1 + ((k - 1 : ℕ) : ℝ) * max ε 0) := by
    funext ε
    rw [perturbedPathInverseDegreeSum, perturbedPathNetwork_degree_zero k hk,
      perturbedPathNetwork_degree_last k hk]
  rw [heq]
  convert (hterm.add hterm).tendsto using 1 <;> norm_num <;> rfl

theorem perturbedPathInverseDegreeSum_tendsto_right (k : ℕ) (hk : 1 ≤ k) :
    Tendsto (perturbedPathInverseDegreeSum k) (𝓝[>] (0 : ℝ)) (𝓝 (2 : ℝ)) :=
  (perturbedPathInverseDegreeSum_tendsto k hk).mono_left nhdsWithin_le_nhds

/-- For positive ε, the formula agrees with the existing canonical Green kernel. -/
theorem perturbedPathResistance_eq_canonical
    (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    perturbedPathResistance k ε =
      ((perturbedPathNetwork k ε).canonicalGreenKernel
        (perturbedPathNetwork_strictlyComplete k ε hε)).effectiveResistance 0 (Fin.last k) := by
  apply regularizedGreenKernel_effectiveResistance_eq
  intro h
  have := congrArg Fin.val h
  simp at this
  omega

/-- All sufficiently small positive completions violate the endpoint bound. -/
theorem perturbedPath_counterexample_for_small_epsilon (k : ℕ) (hk : 3 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ ε : ℝ, 0 < ε → ε < δ →
      perturbedPathInverseDegreeSum k ε < perturbedPathResistance k ε := by
  have hevent : ∀ᶠ ε : ℝ in 𝓝 (0 : ℝ),
      perturbedPathInverseDegreeSum k ε < perturbedPathResistance k ε :=
    Filter.Tendsto.eventually_lt (perturbedPathInverseDegreeSum_tendsto k (by omega))
      (perturbedPathResistance_tendsto k (by omega))
      (by exact_mod_cast (show 2 < k by omega))
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hevent
  refine ⟨δ, hδ, ?_⟩
  intro ε hε hεδ
  apply hbound
  simpa [Real.dist_eq, abs_of_pos hε] using hεδ

/-- The counterexample uses the actual canonical inverse of a complete
network with strictly positive conductances. -/
theorem perturbedPath_canonical_counterexample (k : ℕ) (hk : 3 ≤ k) :
    ∃ ε : ℝ, ∃ hε : 0 < ε,
      1 / (perturbedPathNetwork k ε).degree 0 +
        1 / (perturbedPathNetwork k ε).degree (Fin.last k) <
      ((perturbedPathNetwork k ε).canonicalGreenKernel
        (perturbedPathNetwork_strictlyComplete k ε hε)).effectiveResistance 0 (Fin.last k) := by
  obtain ⟨δ, hδ, hbound⟩ := perturbedPath_counterexample_for_small_epsilon k hk
  have hε : 0 < δ / 2 := by linarith
  refine ⟨δ / 2, hε, ?_⟩
  have h := hbound (δ / 2) hε (by linarith)
  rw [perturbedPathResistance_eq_canonical k (by omega) _ hε] at h
  exact h

/-- For every dimension d ≥ 4, completeness and positive edge weights alone
do not imply the covariance theorem's endpoint-resistance bound. -/
theorem complete_positive_network_counterexample_every_dimension (d : ℕ) (hd : 4 ≤ d) :
    letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
    ∃ N : ConductanceNetwork (Fin d), ∃ hN : N.IsStrictlyComplete,
      ∃ i j : Fin d, i ≠ j ∧
        1 / N.degree i + 1 / N.degree j < (N.canonicalGreenKernel hN).effectiveResistance i j := by
  letI : Nonempty (Fin d) := ⟨⟨0, by omega⟩⟩
  cases d with
  | zero => omega
  | succ k =>
    obtain ⟨ε, hε, hbound⟩ := perturbedPath_canonical_counterexample k (by omega)
    refine ⟨perturbedPathNetwork k ε, perturbedPathNetwork_strictlyComplete k ε hε,
      0, Fin.last k, ?_, hbound⟩
    intro heq
    have := congrArg Fin.val heq
    simp at this
    omega

end

end CoefficientOne
