import CoefficientOne.Sampling.FiniteLawMeasure

/-!
# Relabelling finite laws and their actual covariances

Residual coordinate sets in the sampler need not have type `Fin N`.  These
identities identify their laws and matrices with the already formalized ones.
-/

open scoped BigOperators
open EffectiveResistance

namespace CoefficientOne.Sampling

noncomputable section

variable {α β : Type*} [Fintype α] [Fintype β]

/-- Relabel a finite law through a bijection. -/
def transportLaw (e : α ≃ β) (p : FiniteLaw α) : FiniteLaw β :=
  ⟨fun b => p.val (e.symm b),
    ⟨fun b => law_nonneg p (e.symm b), by
      rw [e.symm.sum_comp]
      exact law_sum p⟩⟩

@[simp] theorem transportLaw_apply (e : α ≃ β) (p : FiniteLaw α) (b : β) :
    (transportLaw e p).val b = p.val (e.symm b) := rfl

theorem lawExpectation_transport (e : α ≃ β) (p : FiniteLaw α) (f : β → ℝ) :
    lawExpectation (transportLaw e p) f = lawExpectation p (fun a => f (e a)) := by
  unfold lawExpectation
  change (∑ b, p.val (e.symm b) * f b) = _
  rw [← e.sum_comp (fun b => p.val (e.symm b) * f b)]
  simp only [e.symm_apply_apply]

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- The bijection of fixed-rank subsets induced by a coordinate relabelling. -/
def rankSubsetEquiv (e : ι ≃ κ) (k : ℕ) : RankSubset ι k ≃ RankSubset κ k where
  toFun S := ⟨e.finsetCongr S.val, by simpa using S.property⟩
  invFun S := ⟨e.symm.finsetCongr S.val, by simpa using S.property⟩
  left_inv S := by
    apply Subtype.ext
    exact e.finsetCongr.left_inv S.val
  right_inv S := by
    apply Subtype.ext
    exact e.finsetCongr.right_inv S.val

@[simp] theorem rankSubsetEquiv_val (e : ι ≃ κ) (k : ℕ) (S : RankSubset ι k) :
    (rankSubsetEquiv e k S).val = e.finsetCongr S.val := rfl

@[simp] theorem indicator_rankSubsetEquiv (e : ι ≃ κ) (k : ℕ)
    (S : RankSubset ι k) (i : ι) :
    indicator (e i) (rankSubsetEquiv e k S).val = indicator i S.val := by
  simp [indicator, Equiv.finsetCongr_apply]

theorem subsetWeight_reindex (e : ι ≃ κ) (w : ι → ℝ) (S : Finset ι) :
    subsetWeight (fun j => w (e.symm j)) (e.finsetCongr S) = subsetWeight w S := by
  simp [subsetWeight, Equiv.finsetCongr_apply]

theorem elementarySum_reindex (e : ι ≃ κ) (w : ι → ℝ) (k : ℕ) :
    elementarySum (fun j => w (e.symm j)) k = elementarySum w k := by
  unfold elementarySum
  rw [← (rankSubsetEquiv e k).sum_comp
    (fun S => subsetWeight (fun j => w (e.symm j)) S.val)]
  apply Finset.sum_congr rfl
  intro S _
  exact subsetWeight_reindex e w S.val

theorem subsetProbability_reindex (e : ι ≃ κ) (w : ι → ℝ) (k : ℕ)
    (S : RankSubset ι k) :
    subsetProbability (fun j => w (e.symm j)) k (rankSubsetEquiv e k S) =
      subsetProbability w k S := by
  simp only [subsetProbability, rankSubsetEquiv_val, subsetWeight_reindex,
    elementarySum_reindex]

theorem expectation_reindex (e : ι ≃ κ) (w : ι → ℝ) (k : ℕ)
    (f : RankSubset κ k → ℝ) :
    expectation (fun j => w (e.symm j)) k f =
      expectation w k (fun S => f (rankSubsetEquiv e k S)) := by
  unfold expectation
  rw [← (rankSubsetEquiv e k).sum_comp
    (fun S => subsetProbability (fun j => w (e.symm j)) k S * f S)]
  simp only [subsetProbability_reindex]

theorem inclusionMean_reindex (e : ι ≃ κ) (w : ι → ℝ) (k : ℕ) (i : ι) :
    inclusionMean (fun j => w (e.symm j)) k (e i) = inclusionMean w k i := by
  unfold inclusionMean
  rw [expectation_reindex]
  simp only [indicator_rankSubsetEquiv]

theorem covarianceMatrix_reindex (e : ι ≃ κ) (w : ι → ℝ) (k : ℕ) (i j : ι) :
    covarianceMatrix (fun b => w (e.symm b)) k (e i) (e j) =
      covarianceMatrix w k i j := by
  unfold covarianceMatrix
  rw [expectation_reindex]
  simp only [indicator_rankSubsetEquiv, inclusionMean_reindex]

theorem lawMean_transport (e : ι ≃ κ) (k : ℕ)
    (p : FiniteLaw (RankSubset ι k)) (i : ι) :
    lawMean (transportLaw (rankSubsetEquiv e k) p) (e i) = lawMean p i := by
  unfold lawMean
  rw [lawExpectation_transport]
  simp only [indicator_rankSubsetEquiv]

theorem lawCovariance_transport (e : ι ≃ κ) (k : ℕ)
    (p : FiniteLaw (RankSubset ι k)) (i j : ι) :
    lawCovariance (transportLaw (rankSubsetEquiv e k) p) (e i) (e j) =
      lawCovariance p i j := by
  unfold lawCovariance
  rw [lawExpectation_transport]
  simp only [indicator_rankSubsetEquiv, lawMean_transport]

end
end CoefficientOne.Sampling
