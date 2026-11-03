import CoefficientOne.Sampling.Model
import CoefficientOne.Sampling.Seed

/-!
# The sequential sampler on a concrete common seed

The recursion follows Appendix E.2: process a fixed order, use the conditional
product-weight threshold, and force the two terminal quotas.  The cardinality
invariant below holds for every seed, including uniform coordinates 0 and 1.
-/

open scoped BigOperators unitInterval
open EffectiveResistance MeasureTheory

namespace CoefficientOne.Sampling

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The elementary symmetric polynomial restricted to a remaining set. -/
def restrictedElementary (w : ι → ℝ) (R : Finset ι) (r : ℕ) : ℝ :=
  ∑ S ∈ R.powersetCard r, subsetWeight w S

/-- The product-weight conditional threshold in a nonterminal state. -/
def sequentialThreshold (w : ι → ℝ) (R : Finset ι) (r : ℕ) (i : ι) : ℝ :=
  w i * restrictedElementary w (R.erase i) (r - 1) / restrictedElementary w R r

/-- The deterministic recursion underlying the common-seed sampler. -/
def sequentialList (w u : ι → ℝ) : List ι → ℕ → Finset ι
  | [], _ => ∅
  | i :: tail, r =>
    if r = 0 then ∅
    else if r = (i :: tail).length then (i :: tail).toFinset
    else if u i ≤ sequentialThreshold w (i :: tail).toFinset r i then
      insert i (sequentialList w u tail (r - 1))
    else sequentialList w u tail r

@[simp] theorem sequentialList_nil (w u : ι → ℝ) (r : ℕ) :
    sequentialList w u [] r = ∅ := rfl

@[simp] theorem sequentialList_zero (w u : ι → ℝ) (order : List ι) :
    sequentialList w u order 0 = ∅ := by
  cases order <;> simp [sequentialList]

theorem sequentialList_full (w u : ι → ℝ) (order : List ι) :
    sequentialList w u order order.length = order.toFinset := by
  cases order <;> simp [sequentialList]

theorem sequentialList_subset (w u : ι → ℝ) (order : List ι) (r : ℕ) :
    sequentialList w u order r ⊆ order.toFinset := by
  induction order generalizing r with
  | nil => simp
  | cons i tail ih =>
    simp only [sequentialList]
    split_ifs with hzero hfull htake
    · exact Finset.empty_subset _
    · exact Finset.Subset.rfl
    · simpa only [List.toFinset_cons] using Finset.insert_subset_insert i (ih (r - 1))
    · exact (ih r).trans (by simp only [List.toFinset_cons]; exact Finset.subset_insert _ _)

/-- Exact cardinality is pointwise; it does not discard exceptional seeds. -/
theorem sequentialList_card (w u : ι → ℝ) (order : List ι)
    (hn : order.Nodup) (r : ℕ) (hr : r ≤ order.length) :
    (sequentialList w u order r).card = r := by
  induction order generalizing r with
  | nil =>
    have : r = 0 := by simpa using hr
    subst r
    simp
  | cons i tail ih =>
    obtain ⟨hi, ht⟩ := List.nodup_cons.mp hn
    simp only [sequentialList]
    split_ifs with hzero hfull htake
    · subst r; simp
    · simpa only [List.toFinset_card_of_nodup hn] using hfull.symm
    · have hnot : i ∉ sequentialList w u tail (r - 1) := by
        intro h
        exact hi (List.mem_toFinset.mp (sequentialList_subset w u tail (r - 1) h))
      rw [Finset.card_insert_of_notMem hnot, ih ht (r - 1) (by simp only [List.length_cons] at hr; omega)]
      omega
    · exact ih ht r (by simp only [List.length_cons] at hr hfull; omega)

@[fun_prop] theorem measurable_restrictedElementary (R : Finset ι) (r : ℕ) :
    Measurable (fun w : ι → ℝ => restrictedElementary w R r) := by
  unfold restrictedElementary subsetWeight
  fun_prop

@[fun_prop] theorem measurable_sequentialThreshold (R : Finset ι) (r : ℕ) (i : ι) :
    Measurable (fun w : ι → ℝ => sequentialThreshold w R r i) := by
  unfold sequentialThreshold
  fun_prop

/-- Joint measurability in the weights and all uniform coordinates. -/
theorem measurable_sequentialList (order : List ι) (r : ℕ) :
    Measurable (fun wu : (ι → ℝ) × (ι → ℝ) => sequentialList wu.1 wu.2 order r) := by
  induction order generalizing r with
  | nil => exact measurable_const
  | cons i tail ih =>
    simp only [sequentialList]
    by_cases hzero : r = 0
    · simp only [hzero, ↓reduceIte]; exact measurable_const
    · simp only [hzero, ↓reduceIte]
      by_cases hfull : r = (i :: tail).length
      · simp only [hfull, ↓reduceIte]; exact measurable_const
      · simp only [hfull, ↓reduceIte]
        apply Measurable.ite
        · exact measurableSet_le ((measurable_pi_apply i).comp measurable_snd)
            ((measurable_sequentialThreshold _ _ _).comp measurable_fst)
        · exact (measurable_of_finite (fun S : Finset ι => insert i S)).comp (ih (r - 1))
        · exact ih r

/-- The positive-weight sampler on the manuscript's actual common seed. -/
def sequentialSampler {n : ℕ} (w : Fin n → ℝ) (k : ℕ) (ω : Seed n) : Finset (Fin n) :=
  sequentialList w (fun i => (ω.2 i : ℝ)) (List.ofFn ω.1) k

theorem sequentialSampler_card {n : ℕ} (w : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) (ω : Seed n) : (sequentialSampler w k ω).card = k := by
  apply sequentialList_card
  · exact List.nodup_ofFn.mpr ω.1.injective
  · simpa using hk

/-- Borel measurability uses the same finite recursion for every input. -/
theorem measurable_sequentialSampler {n : ℕ} (k : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × Seed n => sequentialSampler z.1 k z.2) := by
  have h : Measurable (fun t : Equiv.Perm (Fin n) ×
      ((Fin n → ℝ) × (Fin n → ℝ)) => sequentialList t.2.1 t.2.2 (List.ofFn t.1) k) := by
    exact measurable_from_prod_countable_right (fun π => measurable_sequentialList (List.ofFn π) k)
  have hg : Measurable (fun z : (Fin n → ℝ) × Seed n =>
      (z.2.1, (z.1, fun i => (z.2.2 i : ℝ)))) := by
    apply Measurable.prodMk
    · exact measurable_fst.comp measurable_snd
    · apply Measurable.prodMk measurable_fst
      exact measurable_pi_iff.mpr fun i =>
        measurable_subtype_coe.comp ((measurable_seedUniform n i).comp measurable_snd)
  exact h.comp hg

end
end CoefficientOne.Sampling
