import MsetsPaper.Probability.AmbientHistoryRegret
import Mathlib.Data.Set.Finite.Lemmas

/-! Hindsight maximization over all fixed comparator distributions. The
maximizer is an actual Dirac law; no measurability of its hindsight choice
is required by this pointwise assertion. -/

noncomputable section
open MsetsLower MsetsPaper.Upper MsetsPaper.Probability
open MsetsPaper.Probability.AmbientHistory
open scoped BigOperators

namespace MsetsPaper.Alignment

def diracWeights {α : Type*} [DecidableEq α] (a : α) : α → ℝ :=
  fun b ↦ if b = a then 1 else 0

theorem finite_comparator_max_attained {α : Type*} [Fintype α] [Nonempty α]
    [DecidableEq α] (J : ℝ) (c : α → ℝ) :
    IsGreatest {r : ℝ | ∃ q : α → ℝ, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧
      J - (∑ a, q a * c a) = r} (J - sInf (Set.range c)) ∧
    ∃ a : α, J - (∑ b, diracWeights a b * c b) = J - sInf (Set.range c) := by
  classical
  obtain ⟨a, _, ha⟩ := Set.exists_min_image Set.univ c (Set.toFinite _) Set.univ_nonempty
  have hi : sInf (Set.range c) = c a := by
    apply le_antisymm
    · exact csInf_le (Set.finite_range c).bddBelow ⟨a, rfl⟩
    · apply le_csInf (Set.range_nonempty c)
      rintro _ ⟨b, rfl⟩
      exact ha b (Set.mem_univ b)
  have hdirac : J - (∑ b, diracWeights a b * c b) = J - sInf (Set.range c) := by
    rw [hi]
    simp [diracWeights]
  have hbound (q : α → ℝ) (hq : ∀ b, 0 ≤ q b) (hs : ∑ b, q b = 1) :
      J - (∑ b, q b * c b) ≤ J - sInf (Set.range c) := by
    have h := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset α)) ↦
      mul_le_mul_of_nonneg_left (ha b (Set.mem_univ b)) (hq b))
    rw [← Finset.sum_mul, hs, one_mul] at h
    rw [hi]
    linarith
  refine ⟨⟨?_, ?_⟩, a, hdirac⟩
  · exact ⟨diracWeights a, (fun b ↦ by simp only [diracWeights]; split_ifs <;> norm_num),
      by simp [diracWeights], hdirac⟩
  · rintro r ⟨q, hq, hs, rfl⟩
    exact hbound q hq hs

def ambientComparatorRegret {Ω : Type*} {d m : ℕ}
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ) (T : ℕ)
    (q : Action d m → ℝ) (ω : Ω) : ℝ :=
  ∑ t ∈ Finset.range T, (actionLoss (X t ω) (ell t ω) -
    finiteExpectation q (fun a ↦ actionLoss a (ell t ω)))

theorem ambientComparatorRegret_eq {Ω : Type*} {d m : ℕ}
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ) (T : ℕ)
    (q : Action d m → ℝ) (ω : Ω) :
    ambientComparatorRegret X ell T q ω =
      (∑ t ∈ Finset.range T, actionLoss (X t ω) (ell t ω)) -
        ∑ a, q a * (∑ t ∈ Finset.range T, actionLoss a (ell t ω)) := by
  unfold ambientComparatorRegret finiteExpectation
  rw [Finset.sum_sub_distrib]
  congr 1
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

/-- Exactly the footnote's maximum, for each realized history: every law
is bounded by external regret, and a Dirac law attains it. -/
theorem regret_eq_max_comparator {Ω : Type*} {d m : ℕ} (hmd : m ≤ d)
    (X : ℕ → Ω → Action d m) (ell : ℕ → Ω → Fin d → ℝ) (T : ℕ) (ω : Ω) :
    IsGreatest {r : ℝ | ∃ q : Action d m → ℝ,
      IsDistribution q ∧ ambientComparatorRegret X ell T q ω = r} (regret X ell T ω) ∧
    ∃ a : Action d m, IsDistribution (diracWeights a) ∧
      ambientComparatorRegret X ell T (diracWeights a) ω = regret X ell T ω := by
  classical
  letI : Nonempty (Action d m) := nonempty_MSetAction hmd
  have h := finite_comparator_max_attained
    (∑ t ∈ Finset.range T, actionLoss (X t ω) (ell t ω))
    (fun a : Action d m ↦ ∑ t ∈ Finset.range T, actionLoss a (ell t ω))
  have hset : {r : ℝ | ∃ q : Action d m → ℝ,
      IsDistribution q ∧ ambientComparatorRegret X ell T q ω = r} =
      {r : ℝ | ∃ q : Action d m → ℝ, (∀ a, 0 ≤ q a) ∧ (∑ a, q a = 1) ∧
        (∑ t ∈ Finset.range T, actionLoss (X t ω) (ell t ω)) -
          (∑ a, q a * (∑ t ∈ Finset.range T, actionLoss a (ell t ω))) = r} := by
    ext r
    simp only [Set.mem_setOf_eq, IsDistribution, ambientComparatorRegret_eq, and_assoc]
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact h.1
  · obtain ⟨a, ha⟩ := h.2
    refine ⟨a, ⟨?_, ?_⟩, ?_⟩
    · intro b
      simp only [diracWeights]; split_ifs <;> norm_num
    · simp [diracWeights]
    · rw [ambientComparatorRegret_eq]
      exact ha

end MsetsPaper.Alignment
