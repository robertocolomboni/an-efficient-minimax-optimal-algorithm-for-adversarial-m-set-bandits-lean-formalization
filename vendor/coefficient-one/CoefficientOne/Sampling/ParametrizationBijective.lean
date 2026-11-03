import CoefficientOne.Sampling.ParametrizationKernel

/-!
# Bijectivity of the normalized exponential-family mean map
-/

open scoped BigOperators Topology
open EffectiveResistance

namespace CoefficientOne.Sampling
noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ}

def coordinateDot (u : ι → ℝ) : (ι → ℝ) →L[ℝ] ℝ :=
  ∑ i, u i • ContinuousLinearMap.proj i

@[simp] theorem coordinateDot_apply (u x : ι → ℝ) :
    coordinateDot u x = ∑ i, u i * x i := by simp [coordinateDot]

theorem exponentialMean_line_derivative (hk : k ≤ Fintype.card ι)
    (θ u : ι → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => coordinateDot u (exponentialMean k (θ + s • u)))
      (quadraticForm (covarianceMatrix (fun i => Real.exp ((θ + t • u) i)) k) u) t := by
  have hline : HasDerivAt (fun s : ℝ => θ + s • u) u t := by
    convert (hasDerivAt_const t θ).add ((hasDerivAt_id t).smul_const u) using 1 <;>
      first | rfl | simp
  have hmean := (exponentialMean_hasFDerivAt hk (θ + t • u)).comp_hasDerivAt t hline
  have hd := (coordinateDot u).hasFDerivAt.comp_hasDerivAt t hmean
  convert hd using 1 <;> try rfl
  simp only [coordinateDot_apply, quadraticForm, dotProduct]
  apply Finset.sum_congr rfl
  intro i _
  rw [meanDerivative_apply hk]

theorem exponentialMean_injective_zeroSum
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ η : ι → ℝ)
    (hθ : ∑ i, θ i = 0) (hη : ∑ i, η i = 0)
    (hmean : exponentialMean k θ = exponentialMean k η) : θ = η := by
  by_contra hne
  let u := η - θ
  have hu : u ≠ 0 := sub_ne_zero.mpr (Ne.symm hne)
  have hsum : ∑ i, u i = 0 := by simp [u, Finset.sum_sub_distrib, hθ, hη]
  have hmono : StrictMono (fun t : ℝ => coordinateDot u (exponentialMean k (θ + t • u))) :=
    strictMono_of_hasDerivAt_pos (exponentialMean_line_derivative hktop.le θ u)
      (fun t => covariance_quadratic_pos_zeroSum hkpos hktop (θ + t • u) u hsum hu)
  have hlt := hmono (show (0 : ℝ) < 1 by norm_num)
  have heq : θ + u = η := by dsimp [u]; abel
  simp only [zero_smul, add_zero, one_smul, heq, hmean] at hlt
  exact lt_irrefl _ hlt

theorem fullSupport_lawMean_interior
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (p : FiniteLaw (RankSubset ι k)) (hp : ∀ S, 0 < p.val S) :
    lawMean p ∈ interiorHypersimplex ι k := by
  refine ⟨?_, sum_lawMean p⟩
  intro i
  haveI : Nontrivial ι := Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨j, hij⟩ := exists_ne i
  obtain ⟨T, hi, hj, hT⟩ := exists_exchange_background hkpos hktop i j hij.symm
  let S := exchangeInsert k T hT i hi
  let U := exchangeInsert k T hT j hj
  have hindS : indicator i S.val = 1 := by simp [S, exchangeInsert, indicator]
  have hindU : indicator i U.val = 0 := by simp [U, exchangeInsert, indicator, hij.symm, hi]
  constructor
  · apply Finset.sum_pos'
    · intro A _
      exact mul_nonneg (p.property.1 A) (by simp [indicator]; split_ifs <;> norm_num)
    · exact ⟨S, Finset.mem_univ S, by change 0 < p.val S * indicator i S.val; rw [hindS, mul_one]; exact hp S⟩
  · have hlt : (∑ A, p.val A * indicator i A.val) < ∑ A, p.val A := by
      apply Finset.sum_lt_sum
      · intro A _
        exact mul_le_of_le_one_right (p.property.1 A) (by simp [indicator]; split_ifs <;> norm_num)
      · exact ⟨U, Finset.mem_univ U, by rw [hindU, mul_zero]; exact hp U⟩
    simpa only [law_sum, lawMean, lawExpectation] using hlt

theorem exponentialMean_mem_interior
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι) (θ : ι → ℝ) :
    exponentialMean k θ ∈ interiorHypersimplex ι k :=
  fullSupport_lawMean_interior hkpos hktop
    (externalFieldLaw (fun i => Real.exp (θ i)) (fun i => Real.exp_pos (θ i)) hktop.le)
    (subsetProbability_pos _ (fun i => Real.exp_pos (θ i)) hktop.le)

theorem exponentialMean_surjective_interior (x : ι → ℝ)
    (hx : x ∈ interiorHypersimplex ι k) :
    ∃ θ : ι → ℝ, (∑ i, θ i = 0) ∧ exponentialMean k θ = x := by
  let X : hypersimplex ι k := ⟨x, interiorHypersimplex_subset hx⟩
  obtain ⟨θ, hsum, hlaw⟩ := maximumEntropyLaw_eq_externalFieldLaw X hx.1
  refine ⟨θ, hsum, ?_⟩
  have hh := maximumEntropyLaw_mean X
  rw [hlaw] at hh
  exact hh

theorem existsUnique_exponential_parameter
    (hkpos : 1 ≤ k) (hktop : k < Fintype.card ι)
    (x : ι → ℝ) (hx : x ∈ interiorHypersimplex ι k) :
    ∃! θ : ι → ℝ, (∑ i, θ i = 0) ∧ exponentialMean k θ = x := by
  obtain ⟨θ, hθ, hmean⟩ := exponentialMean_surjective_interior x hx
  refine ⟨θ, ⟨hθ, hmean⟩, ?_⟩
  intro η hη
  exact exponentialMean_injective_zeroSum hkpos hktop η θ hη.1 hθ (hη.2.trans hmean.symm)

end
end CoefficientOne.Sampling
