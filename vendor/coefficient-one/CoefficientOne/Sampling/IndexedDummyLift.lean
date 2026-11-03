import CoefficientOne.Sampling.DummyCardinality

/-! # Relabelling the dummy lift to the seed space with n+k coordinates -/

open scoped BigOperators

namespace CoefficientOne.Sampling
noncomputable section

variable {n k : ℕ}

def indexedDummyLift (k : ℕ) (x : Fin n → ℝ) (i : Fin (n + k)) : ℝ :=
  dummyLift k x (finSumFinEquiv.symm i)

theorem indexedDummyLift_mem_hypersimplex {x : Fin n → ℝ}
    (hx : x ∈ atMostHypersimplex (Fin n) k) :
    indexedDummyLift k x ∈ hypersimplex (Fin (n + k)) k := by
  have h := dummyLift_mem_hypersimplex hx
  refine ⟨fun i => h.1 (finSumFinEquiv.symm i), ?_⟩
  unfold indexedDummyLift
  rw [finSumFinEquiv.symm.sum_comp]
  exact h.2

def liftedExactInput (x : atMostHypersimplex (Fin n) k) : hypersimplex (Fin (n + k)) k :=
  ⟨indexedDummyLift k x.val, indexedDummyLift_mem_hypersimplex x.property⟩

theorem continuous_indexedDummyLift : Continuous (indexedDummyLift (n := n) k) := by
  apply continuous_pi
  intro i
  exact (continuous_apply (finSumFinEquiv.symm i)).comp (continuous_dummyLift k)

theorem continuous_liftedExactInput : Continuous (liftedExactInput (n := n) (k := k)) :=
  (continuous_indexedDummyLift.comp continuous_subtype_val).subtype_mk _

theorem indexedDummyLift_l1 {x y : Fin n → ℝ}
    (hx : x ∈ atMostHypersimplex (Fin n) k) (hy : y ∈ atMostHypersimplex (Fin n) k) :
    vectorL1 (fun i => indexedDummyLift k x i - indexedDummyLift k y i) ≤
      2 * vectorL1 (fun i => x i - y i) := by
  have he : vectorL1 (fun i => indexedDummyLift k x i - indexedDummyLift k y i) =
      vectorL1 (fun a => dummyLift k x a - dummyLift k y a) := by
    unfold vectorL1 EffectiveResistance.l1Norm indexedDummyLift
    exact finSumFinEquiv.symm.sum_comp
      (fun a : Fin n ⊕ Fin k => |dummyLift k x a - dummyLift k y a|)
  rw [he]
  exact dummyLift_l1_le_two hx hy

def splitLiftedOutput (S : Finset (Fin (n + k))) : Finset (Fin n ⊕ Fin k) :=
  S.map finSumFinEquiv.symm.toEmbedding

def realOutput (S : Finset (Fin (n + k))) : Finset (Fin n) := (splitLiftedOutput S).toLeft

@[simp] theorem splitLiftedOutput_card (S : Finset (Fin (n + k))) :
    (splitLiftedOutput S).card = S.card := Finset.card_map _

@[simp] theorem mem_splitLiftedOutput {S : Finset (Fin (n + k))} {a : Fin n ⊕ Fin k} :
    a ∈ splitLiftedOutput S ↔ finSumFinEquiv a ∈ S := by
  simp [splitLiftedOutput]

@[simp] theorem mem_realOutput {S : Finset (Fin (n + k))} {i : Fin n} :
    i ∈ realOutput S ↔ finSumFinEquiv (Sum.inl i) ∈ S := by
  simp [realOutput]

theorem outputDistance_map_equiv {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ] (e : ι ≃ κ) (S T : Finset ι) :
    outputDistance (S.map e.toEmbedding) (T.map e.toEmbedding) = outputDistance S T := by
  have he : symmDiff (S.map e.toEmbedding) (T.map e.toEmbedding) =
      (symmDiff S T).map e.toEmbedding := by
    simp only [Finset.map_eq_image]
    exact (Finset.image_symmDiff S T e.injective).symm
  unfold outputDistance
  rw [he, Finset.card_map]

theorem realOutput_distance_le (S T : Finset (Fin (n + k))) :
    outputDistance (realOutput S) (realOutput T) ≤ outputDistance S T := by
  apply (outputDistance_toLeft_le (splitLiftedOutput S) (splitLiftedOutput T)).trans
  exact le_of_eq (outputDistance_map_equiv finSumFinEquiv.symm S T)

theorem indicator_realOutput (i : Fin n) (S : Finset (Fin (n + k))) :
    EffectiveResistance.indicator i (realOutput S) =
      EffectiveResistance.indicator (finSumFinEquiv (Sum.inl i)) S := by
  simp only [EffectiveResistance.indicator, mem_realOutput]

theorem indicator_splitLiftedOutput (a : Fin n ⊕ Fin k) (S : Finset (Fin (n + k))) :
    EffectiveResistance.indicator a (splitLiftedOutput S) =
      EffectiveResistance.indicator (finSumFinEquiv a) S := by
  simp only [EffectiveResistance.indicator, mem_splitLiftedOutput]

@[simp] theorem indexedDummyLift_real (x : Fin n → ℝ) (i : Fin n) :
    indexedDummyLift k x (finSumFinEquiv (Sum.inl i)) = x i := by
  simp [indexedDummyLift, dummyLift]

@[simp] theorem indexedDummyLift_dummy (x : Fin n → ℝ) (j : Fin k) :
    indexedDummyLift k x (finSumFinEquiv (Sum.inr j)) =
      dummyCoordinate ((k : ℝ) - coordinateSum x) j.val := by
  simp [indexedDummyLift, dummyLift]

end
end CoefficientOne.Sampling
