import CoefficientOne.Sampling.DummyLift
import CoefficientOne.Sampling.OutputMetric

/-! # Cardinality bounds forced by the zero and one dummy marginals -/

open scoped BigOperators
open Set MeasureTheory

namespace CoefficientOne.Sampling
noncomputable section

def initialSegment (n m : ℕ) : Finset (Fin n) := Finset.univ.filter (fun i => i.val < m)

@[simp] theorem mem_initialSegment {n m : ℕ} {i : Fin n} :
    i ∈ initialSegment n m ↔ i.val < m := by simp [initialSegment]

theorem initialSegment_card {n m : ℕ} (hm : m ≤ n) : (initialSegment n m).card = m := by
  classical
  have he : initialSegment n m = Finset.univ.map (Fin.castLEEmb hm) := by
    ext i
    simp only [mem_initialSegment, Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [he, Finset.card_map, Finset.card_univ, Fintype.card_fin]

theorem dummyCoordinate_eq_zero_iff (σ : ℝ) (j : ℕ) :
    dummyCoordinate σ j = 0 ↔ σ ≤ j := by
  have h := dummyCoordinate_pos_iff σ j
  constructor
  · intro hz
    by_contra hn
    have hp := h.mpr (lt_of_not_ge hn)
    rw [hz] at hp
    exact (lt_irrefl 0 hp)
  · intro hσ
    unfold dummyCoordinate
    rw [max_eq_left (sub_nonpos.mpr hσ)]
    norm_num

theorem dummyCoordinate_eq_one_iff (σ : ℝ) (j : ℕ) :
    dummyCoordinate σ j = 1 ↔ (j : ℝ) + 1 ≤ σ := by
  constructor
  · intro ho
    by_contra hn
    have h := (dummyCoordinate_lt_one_iff σ j).mpr (lt_of_not_ge hn)
    rw [ho] at h
    exact (lt_irrefl 1 h)
  · intro hσ
    exact min_eq_left (le_max_of_le_right (by linarith))

/-- Only the coordinates of marginal zero and one are used here. -/
theorem dummySelected_card_floor_or_ceil {k : ℕ} {σ : ℝ}
    (hσ : 0 ≤ σ) (hσk : σ ≤ k) (D : Finset (Fin k))
    (hzero : ∀ j, dummyCoordinate σ j.val = 0 → j ∉ D)
    (hone : ∀ j, dummyCoordinate σ j.val = 1 → j ∈ D) :
    D.card = ⌊σ⌋₊ ∨ D.card = ⌈σ⌉₊ := by
  have hfk : ⌊σ⌋₊ ≤ k := (Nat.cast_le (α := ℝ)).mp ((Nat.floor_le hσ).trans hσk)
  have hck : ⌈σ⌉₊ ≤ k := Nat.ceil_le.mpr hσk
  have hlow : initialSegment k ⌊σ⌋₊ ⊆ D := by
    intro j hj
    apply hone
    apply (dummyCoordinate_eq_one_iff σ j.val).mpr
    have hh : (j.val : ℝ) + 1 ≤ (⌊σ⌋₊ : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt (mem_initialSegment.mp hj)
    exact hh.trans (Nat.floor_le hσ)
  have hupp : D ⊆ initialSegment k ⌈σ⌉₊ := by
    intro j hj
    apply mem_initialSegment.mpr
    by_contra hn
    have hle : (⌈σ⌉₊ : ℝ) ≤ j.val := by exact_mod_cast (Nat.le_of_not_gt hn)
    exact hzero j ((dummyCoordinate_eq_zero_iff σ j.val).mpr ((Nat.le_ceil σ).trans hle)) hj
  have hl := Finset.card_le_card hlow
  have hu := Finset.card_le_card hupp
  rw [initialSegment_card hfk] at hl
  rw [initialSegment_card hck] at hu
  have hc := Nat.ceil_le_floor_add_one σ
  omega

theorem complement_card_floor_or_ceil {k m d : ℕ} {s : ℝ}
    (hs : 0 ≤ s) (hsk : s ≤ k) (hcard : m + d = k)
    (hd : d = ⌊(k : ℝ) - s⌋₊ ∨ d = ⌈(k : ℝ) - s⌉₊) :
    m = ⌊s⌋₊ ∨ m = ⌈s⌉₊ := by
  have hσ : 0 ≤ (k : ℝ) - s := sub_nonneg.mpr hsk
  have hc : (m : ℝ) + d = k := by exact_mod_cast hcard
  rcases hd with hd | hd
  · have h1 : (d : ℝ) ≤ (k : ℝ) - s := hd ▸ Nat.floor_le hσ
    have h2 : (k : ℝ) - s < (d : ℝ) + 1 := hd ▸ Nat.lt_floor_add_one ((k : ℝ) - s)
    right
    by_cases hm : m = 0
    · subst m
      symm
      apply Nat.ceil_eq_zero.mpr
      simp only [Nat.cast_zero, zero_add] at hc
      linarith
    · symm
      apply (Nat.ceil_eq_iff hm).mpr
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      constructor <;> linarith
  · have h1 : (k : ℝ) - s ≤ d := hd ▸ Nat.le_ceil ((k : ℝ) - s)
    left
    by_cases hd0 : d = 0
    · rw [hd0] at hc h1
      simp only [Nat.cast_zero, add_zero] at hc h1
      have he : s = m := by linarith
      rw [he, Nat.floor_natCast]
    · have h2 : (d : ℝ) - 1 < (k : ℝ) - s := by
        have hh := ((Nat.ceil_eq_iff hd0).mp hd.symm).1
        rw [Nat.cast_sub (by omega : 1 ≤ d), Nat.cast_one] at hh
        exact hh
      symm
      apply (Nat.floor_eq_iff hs).mpr
      constructor <;> linarith

theorem realSelected_card_floor_or_ceil {ι : Type*} [Fintype ι] [DecidableEq ι]
    {k : ℕ} {s : ℝ} (hs : 0 ≤ s) (hsk : s ≤ k) (T : Finset (ι ⊕ Fin k))
    (hcard : T.card = k)
    (hzero : ∀ j, dummyCoordinate ((k : ℝ) - s) j.val = 0 → Sum.inr j ∉ T)
    (hone : ∀ j, dummyCoordinate ((k : ℝ) - s) j.val = 1 → Sum.inr j ∈ T) :
    T.toLeft.card = ⌊s⌋₊ ∨ T.toLeft.card = ⌈s⌉₊ := by
  apply complement_card_floor_or_ceil hs hsk
    (Finset.card_toLeft_add_card_toRight.trans hcard)
  apply dummySelected_card_floor_or_ceil (sub_nonneg.mpr hsk) (by linarith) T.toRight
  · intro j hj
    simpa only [Finset.mem_toRight] using hzero j hj
  · intro j hj
    simpa only [Finset.mem_toRight] using hone j hj

theorem outputDistance_toLeft_le {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (S T : Finset (ι ⊕ κ)) :
    outputDistance S.toLeft T.toLeft ≤ outputDistance S T := by
  have he : symmDiff S.toLeft T.toLeft = (symmDiff S T).toLeft := by
    ext i
    simp only [Finset.mem_symmDiff, Finset.mem_toLeft]
  unfold outputDistance
  rw [he]
  exact_mod_cast Finset.card_toLeft_le (u := symmDiff S T)

end
end CoefficientOne.Sampling
