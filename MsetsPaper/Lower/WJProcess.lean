import MsetsPaper.Lower.SparseCappedBinaryAverage

/-! # The two actual capped history laws in the introductory W,J experiment

The favorable sets are S and insert J S. The loss process and its observable
history law are the previously verified capped process, specialized to m=1.
No information bound or event probability is postulated by this interface.
-/

namespace MsetsPaper.Lower.WJ

open MsetsLower MsetsLower.History MsetsPaper.Probability
open MeasureTheory ProbabilityTheory InformationTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

def bitsOfSet {d : ℕ} (S : Finset (Fin d)) : SparseCapped.Bits d :=
  fun i => decide (i ∈ S)

@[simp] theorem bitsOfSet_apply {d : ℕ} (S : Finset (Fin d)) (i : Fin d) :
    bitsOfSet S i = true ↔ i ∈ S := by simp [bitsOfSet]

theorem bitsOfSet_insert {d : ℕ} (S : Finset (Fin d)) (j : Fin d) :
    bitsOfSet (insert j S) = Function.update (bitsOfSet S) j true := by
  funext i
  by_cases h : i = j
  · subst i; simp [bitsOfSet]
  · simp [bitsOfSet, h]

theorem bitsOfSet_update_false {d : ℕ} (S : Finset (Fin d)) (j : Fin d)
    (hj : j ∉ S) : Function.update (bitsOfSet S) j false = bitsOfSet S := by
  funext i
  by_cases h : i = j
  · subst i; simp [bitsOfSet, hj]
  · simp [Function.update_of_ne h]

def allInactive {d : ℕ} (S : Finset (Fin d)) (c T : ℕ) : Set (History d 1 T) :=
  {h | ∀ i ∈ S, (c : ℝ) ≤ selectedCount i T h}

def testEvent {d : ℕ} (S : Finset (Fin d)) (j : Fin d) (c T : ℕ) :
    Set (History d 1 T) :=
  allInactive S c T ∩ {h | selectedCount j T h < (c : ℝ)}

theorem measurableSet_allInactive {d : ℕ} (S : Finset (Fin d)) (c T : ℕ) :
    MeasurableSet (allInactive S c T) := by
  simp only [allInactive, Set.ofPred_forall]
  exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun _ =>
    measurableSet_le measurable_const (measurable_selectedCount i T)

theorem measurableSet_testEvent {d : ℕ} (S : Finset (Fin d)) (j : Fin d) (c T : ℕ) :
    MeasurableSet (testEvent S j c T) :=
  (measurableSet_allInactive S c T).inter
    (measurableSet_lt (measurable_selectedCount j T) measurable_const)

def historyLaw {d : ℕ} (P : Policy d 1) (S : Finset (Fin d)) (c T : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    Measure (History d 1 T) :=
  (SparseCapped.observableProcess P (by omega) c epsilon he hs (bitsOfSet S)).law T

instance historyLaw_isProbabilityMeasure {d : ℕ} (P : Policy d 1)
    (S : Finset (Fin d)) (c T : ℕ) (epsilon : ℝ)
    (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    IsProbabilityMeasure (historyLaw P S c T epsilon he hs) := by
  unfold historyLaw
  infer_instance

/-- The history laws differ only on the capped selections of J. -/
theorem historyLaw_KL_le {d : ℕ} (hd : 1 ≤ d) (P : Policy d 1)
    (S : Finset (Fin d)) (j : Fin d) (hj : j ∉ S) (c T : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    klDiv (historyLaw P S c T epsilon he hs)
      (historyLaw P (insert j S) c T epsilon he hs) ≤
        ENNReal.ofReal (128 * epsilon ^ 2 * c) := by
  have h := SparseCapped.observable_bit_KL_le_cap (T := T) P (by omega) hd c he hs
    (bitsOfSet S) j
  rw [bitsOfSet_update_false S j hj, ← bitsOfSet_insert] at h
  simpa only [historyLaw, Nat.cast_one, div_one] using h

def pSection {d : ℕ} (P : Policy d 1) (S : Finset (Fin d)) (j : Fin d)
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) : ℝ :=
  (historyLaw P S c T epsilon he hs).real (testEvent S j c T)

def qSection {d : ℕ} (P : Policy d 1) (S : Finset (Fin d)) (j : Fin d)
    (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) : ℝ :=
  (historyLaw P (insert j S) c T epsilon he hs).real (testEvent S j c T)

theorem pSection_mem_Icc {d : ℕ} (P : Policy d 1) (S : Finset (Fin d))
    (j : Fin d) (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    pSection P S j c T epsilon he hs ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

theorem qSection_mem_Icc {d : ℕ} (P : Policy d 1) (S : Finset (Fin d))
    (j : Fin d) (c T : ℕ) (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    qSection P S j c T epsilon he hs ∈ Icc (0 : ℝ) 1 :=
  ⟨measureReal_nonneg, measureReal_le_one⟩

theorem section_compatible {d : ℕ} (hd : 1 ≤ d) (P : Policy d 1)
    (S : Finset (Fin d)) (j : Fin d) (hj : j ∉ S) (c T : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    BinaryCompatible (pSection P S j c T epsilon he hs)
      (qSection P S j c T epsilon he hs) := by
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (historyLaw_KL_le hd P S j hj c T epsilon he hs)
  exact binaryKL_event_compatible _ _ (measurableSet_testEvent S j c T)
    (klDiv_ne_top_iff.mp hf).1

/-- Data processing is applied to the literal test event E. -/
theorem section_binaryKL_le {d : ℕ} (hd : 1 ≤ d) (P : Policy d 1)
    (S : Finset (Fin d)) (j : Fin d) (hj : j ∉ S) (c T : ℕ)
    (epsilon : ℝ) (he : 0 ≤ epsilon) (hs : epsilon ≤ 1 / 16) :
    binaryKL (pSection P S j c T epsilon he hs)
      (qSection P S j c T epsilon he hs) ≤ 128 * epsilon ^ 2 * c := by
  have hkl := historyLaw_KL_le hd P S j hj c T epsilon he hs
  have hf := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hkl
  exact (binaryKL_event_le_klDiv _ _ (measurableSet_testEvent S j c T) hf).trans
    (ENNReal.toReal_le_of_le_ofReal (by positivity) hkl)

end

end MsetsPaper.Lower.WJ
