import MsetsLower.Lower.Sparse.Gamma
import MsetsLower.Lower.Sparse.TableChange
import MsetsLower.Lower.Sparse.MixtureTV
import MsetsLower.Lower.Sparse.FinalArithmetic

/-!
# Changed-law lower bound for the sparse group maxima

This file implements the application of `lem:changed-law-maximum` in the
completion of the sparse proof.  The score bounds hold on the genuine
feedback support, so it uses the support-safe version of that lemma.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

private theorem measurable_sparseHiddenTableCoordinateJointMap
    {n k B T : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) :
    Measurable (sparseHiddenTableCoordinateJointMap
      (B := B) (k := k) (T := T) a ha j) :=
  ((sparseHiddenTableCoordinateEquiv B n a ha j).measurable.comp
    measurable_fst).prodMk measurable_snd

/-- Integrating a coordinate score under its changed law is exactly
integrating the same score after the full-table change of variables under the
base law.  The action--feedback history is held fixed by the map. -/
theorem integral_sparseObservableCoordinateScore_changedLaw
    {n n' k B T : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hn' : n' <= n) (q c0 : Nat) (j : Fin n') :
    (∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) j T z.2
        ∂(sparseJointLaw (sparseHiddenTableMeasure B n) P F T).withDensity
          (sparseHiddenTableCoordinateJointLikelihood F a ha
            (sparseSignalCoordinate hn' j) T)) =
      ∫ z, sparseObservableCoordinateScore
          (F.at (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) z.1)) hn' q c0
          (sparseHiddenTableU
            (sparseHiddenTableCoordinateEquiv B n a ha
              (sparseSignalCoordinate hn' j) z.1)) j T z.2
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T := by
  let score : SparseHiddenTable B n × History n k T -> Real := fun z =>
    sparseObservableCoordinateScore (F.at z.1) hn' q c0
      (sparseHiddenTableU z.1) j T z.2
  have hscore : Measurable score :=
    measurable_sparseFamilyObservableCoordinateScore F sparseHiddenTableU
      (fun b i => measurable_sparseHiddenTableU B n b i) hn' q c0 j T
  rw [← sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
    P F a ha (sparseSignalCoordinate hn' j) T]
  rw [MeasureTheory.integral_map
    (measurable_sparseHiddenTableCoordinateJointMap
      (k := k) (T := T) a ha (sparseSignalCoordinate hn' j)).aemeasurable
    hscore.aestronglyMeasurable]
  rfl

/-- Every coordinate-changed joint law remains on the same feedback support,
because its measurable table transformation leaves the history component
unchanged. -/
theorem ae_sparseChangedJointLaw_history_support
    {n n' k B T : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hn' : n' <= n) (j : Fin n') :
    ∀ᵐ z ∂(sparseJointLaw (sparseHiddenTableMeasure B n) P F T).withDensity
        (sparseHiddenTableCoordinateJointLikelihood F a ha
          (sparseSignalCoordinate hn' j) T),
      sparseHistoryInFeedbackSupport T z.2 := by
  rw [← sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
    P F a ha (sparseSignalCoordinate hn' j) T]
  apply (MeasureTheory.ae_map_iff
    (measurable_sparseHiddenTableCoordinateJointMap
      (k := k) (T := T) a ha
        (sparseSignalCoordinate hn' j)).aemeasurable
    ((measurableSet_sparseHistoryInFeedbackSupport (n := n) (k := k)
      T).preimage measurable_snd)).2
  filter_upwards [ae_sparseJointLaw_history_support
    (sparseHiddenTableMeasure B n) P F T] with z hz
  exact hz

set_option maxHeartbeats 2000000 in
-- The finite-subtype maximum and support-safe changed-law comparison are elaboration-heavy.
/-- One group of the manuscript's changed-law maximum estimate.  The changed
measures and their uniform mixture are the literal full-table RN-density
laws used by the chi-square calculation. -/
theorem integral_sparseObservableGroupMax_lower
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) (g : Fin k)
    (Qg : Measure (SparseHiddenTable B n × History n k T))
    [IsFiniteMeasure Qg]
    [IsFiniteMeasure (sparseJointLaw (sparseHiddenTableMeasure B n)
      (sparseCenteredPolicy P)
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T)]
    (hQg : Qg = MsetsLower.Probability.averageMeasure (fun j :
      ↥(sparsePartitionGroup hprod sigma g) =>
        Measure.map (sparseHiddenTableCoordinateJointMap sparseA
          (by norm_num [sparseA]) (sparseSignalCoordinate hn' j.1))
          (sparseJointLaw (sparseHiddenTableMeasure B n)
            (sparseCenteredPolicy P)
            (sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B) T))) :
    let F := sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
    let mu := sparseJointLaw (sparseHiddenTableMeasure B n)
      (sparseCenteredPolicy P) F T
    let G := sparsePartitionGroup hprod sigma g
    (∫ z, sparseObservableGroupMax hprod hr sigma (F.at z.1)
          hn' q c0 (sparseHiddenTableU z.1) g T z.2 ∂mu) >=
      (r : Real)⁻¹ *
          ∑ j ∈ G,
            ∫ z, sparseObservableCoordinateScore (F.at z.1) hn' q c0
                (sparseHiddenTableU z.1) j T z.2
              ∂Measure.map (sparseHiddenTableCoordinateJointMap sparseA
                (by norm_num [sparseA]) (sparseSignalCoordinate hn' j)) mu -
        2 * (T : Real) * MsetsLower.Probability.totalVariationDistance
          Qg (sparseJointLaw (sparseHiddenTableMeasure B n)
            (sparseCenteredPolicy P) F T) := by
  classical
  dsimp only
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n)
    (sparseCenteredPolicy P) F T
  let G := sparsePartitionGroup hprod sigma g
  have hG : G.Nonempty := sparsePartitionGroup_nonempty hprod hr sigma g
  let score : Fin n' ->
      SparseHiddenTable B n × History n k T -> Real := fun j z =>
    sparseObservableCoordinateScore (F.at z.1) hn' q c0
      (sparseHiddenTableU z.1) j T z.2
  let Q : ↥G -> Measure (SparseHiddenTable B n × History n k T) := fun j =>
    Measure.map (sparseHiddenTableCoordinateJointMap sparseA
      (by norm_num [sparseA]) (sparseSignalCoordinate hn' j.1)) mu
  have hQg' : Qg = MsetsLower.Probability.averageMeasure Q := by
    simpa [Q, G, mu, F] using hQg
  subst Qg
  let S : ↥G -> SparseHiddenTable B n × History n k T -> Real := fun j =>
    score j.1
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    unfold sparseJointLaw
    infer_instance
  letI (j : ↥G) : IsProbabilityMeasure (Q j) := by
    rw [isProbabilityMeasure_iff]
    dsimp [Q]
    rw [Measure.map_apply
      (measurable_sparseHiddenTableCoordinateJointMap
        (B := B) (k := k) (T := T) sparseA (by norm_num [sparseA])
          (sparseSignalCoordinate hn' j.1)) MeasurableSet.univ]
    simp
  have hscoreMeas : forall j : Fin n', Measurable (score j) := by
    intro j
    exact measurable_sparseFamilyObservableCoordinateScore F
      sparseHiddenTableU
      (fun b i => measurable_sparseHiddenTableU B n b i)
      hn' q c0 j T
  have hbaseSupport : ∀ᵐ z ∂mu,
      sparseHistoryInFeedbackSupport T z.2 := by
    exact ae_sparseJointLaw_history_support
      (sparseHiddenTableMeasure B n) (sparseCenteredPolicy P) F T
  have hchangedSupport : forall j : ↥G, ∀ᵐ z ∂Q j,
      sparseHistoryInFeedbackSupport T z.2 := by
    intro j
    dsimp [Q, mu]
    rw [sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
      (sparseCenteredPolicy P) F sparseA (by norm_num [sparseA])
        (sparseSignalCoordinate hn' j.1) T]
    exact ae_sparseChangedJointLaw_history_support
      (T := T) (sparseCenteredPolicy P) F sparseA
        (by norm_num [sparseA]) hn' j.1
  have hscoreRange (j : Fin n')
      (z : SparseHiddenTable B n × History n k T)
      (hz : sparseHistoryInFeedbackSupport T z.2) :
      score j z ∈ Icc (-(T : Real)) (T : Real) := by
    exact (abs_le).1 <| sparseObservableCoordinateScore_abs_le
      (q := q) (c0 := c0) (F.at z.1) hn' (sparseHiddenTableU z.1)
        (sparseHiddenTableU_abs_le_one z.1) j T z.2 hz
  have hchanged :=
    MsetsLower.Probability.changed_law_maximum_of_ae_range
      mu Q S (M := (T : Real)) (by positivity)
      (fun j => hscoreMeas j.1)
      (fun j => by
        filter_upwards [hbaseSupport] with z hz
        exact hscoreRange j.1 z hz)
      (fun i j => by
        filter_upwards [hchangedSupport j] with z hz
        exact hscoreRange i.1 z hz)
  have hmax : (fun z => MsetsLower.Probability.finiteMax S z) =
      fun z => sparseObservableGroupMax hprod hr sigma (F.at z.1)
        hn' q c0 (sparseHiddenTableU z.1) g T z.2 := by
    funext z
    unfold MsetsLower.Probability.finiteMax S score
      sparseObservableGroupMax
    apply le_antisymm
    · apply Finset.sup'_le
      intro j _hj
      exact Finset.le_sup' (fun i : Fin n' =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) i T z.2) j.2
    · apply Finset.sup'_le
      intro j hj
      exact Finset.le_sup' (fun i : ↥G =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) i.1 T z.2)
        (Finset.mem_univ (⟨j, hj⟩ : ↥G))
  have hcard : Fintype.card (↥G) = r := by
    rw [Fintype.card_coe]
    exact card_sparsePartitionGroup hprod sigma g
  have hsum :
      (∑ j : ↥G, ∫ z, S j z ∂Q j) =
        ∑ j ∈ G, ∫ z, score j z
          ∂Measure.map (sparseHiddenTableCoordinateJointMap sparseA
            (by norm_num [sparseA]) (sparseSignalCoordinate hn' j)) mu := by
    simpa [S, Q] using
      (Finset.sum_attach G
        (fun j : Fin n' => ∫ z, score j z
          ∂Measure.map (sparseHiddenTableCoordinateJointMap sparseA
            (by norm_num [sparseA]) (sparseSignalCoordinate hn' j)) mu))
  rw [hmax] at hchanged
  rw [hcard, hsum] at hchanged
  exact hchanged

theorem measurable_sparseJointObservableGroupMax
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (g : Fin k) :
    Measurable (fun z : SparseHiddenTable B n × History n k T =>
      sparseObservableGroupMax hprod hr sigma
        ((sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1)
        g T z.2) := by
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  have hcoord : forall j : Fin n', Measurable
      (fun z : SparseHiddenTable B n × History n k T =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) j T z.2) := fun j =>
    measurable_sparseFamilyObservableCoordinateScore F sparseHiddenTableU
      (fun b i => measurable_sparseHiddenTableU B n b i)
      hn' q c0 j T
  let G := sparsePartitionGroup hprod sigma g
  let hG := sparsePartitionGroup_nonempty hprod hr sigma g
  have hm : Measurable (G.sup' hG (fun j => fun z :
      SparseHiddenTable B n × History n k T =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) j T z.2)) :=
    Finset.measurable_sup' hG (fun j _hj => hcoord j)
  have heq : G.sup' hG (fun j => fun z :
      SparseHiddenTable B n × History n k T =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) j T z.2) =
      fun z => G.sup' hG (fun j =>
        sparseObservableCoordinateScore (F.at z.1) hn' q c0
          (sparseHiddenTableU z.1) j T z.2) := by
    funext z
    exact Finset.apply_sup'_eq_sup'_comp hG
      (fun f : (SparseHiddenTable B n × History n k T -> Real) => f z)
      (fun (_ _ : SparseHiddenTable B n × History n k T -> Real) => rfl)
  unfold sparseObservableGroupMax
  rw [← heq]
  exact hm

theorem integrable_sparseJointObservableGroupMax
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) (g : Fin k) :
    Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseObservableGroupMax hprod hr sigma
        ((sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1)
        g T z.2)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B) T) := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_sparseJointObservableGroupMax
      (B := B) hk eta heta0 heta q c0 hn' hprod hr sigma g).aestronglyMeasurable
    (T : Real)
  filter_upwards [ae_sparseJointLaw_history_support
    (sparseHiddenTableMeasure B n) P
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T]
      with z hz
  simpa only [Real.norm_eq_abs, mu] using
    sparseObservableGroupMax_abs_le hprod hr sigma
      ((sparseHiddenTableParameterFamily hk eta heta0 heta
        n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1)
      (sparseHiddenTableU_abs_le_one z.1) g z.2 hz

theorem measurable_sparseJointObservableLearnerScore
    {n n' k B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) :
    Measurable (fun z : SparseHiddenTable B n × History n k T =>
      sparseObservableLearnerScore
        ((sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B).at z.1) n' q c0 (sparseHiddenTableU z.1) T z.2) := by
  exact measurable_sparseFamilyObservableLearnerScore
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
    sparseHiddenTableU
    (fun b i => measurable_sparseHiddenTableU B n b i) n' q c0 T

theorem integrable_sparseJointObservableLearnerScore
    {n n' k B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (P : Policy n k) :
    Integrable (fun z : SparseHiddenTable B n × History n k T =>
      sparseObservableLearnerScore
        ((sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B).at z.1) n' q c0 (sparseHiddenTableU z.1) T z.2)
      (sparseJointLaw (sparseHiddenTableMeasure B n) P
        (sparseHiddenTableParameterFamily hk eta heta0 heta
          n' q c0 B) T) := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  letI : IsProbabilityMeasure mu := by
    dsimp [mu]
    unfold sparseJointLaw
    infer_instance
  apply Integrable.of_bound
    (measurable_sparseJointObservableLearnerScore
      (B := B) hk eta heta0 heta q c0).aestronglyMeasurable
    ((k : Real) * T)
  filter_upwards [ae_sparseJointLaw_history_support
    (sparseHiddenTableMeasure B n) P
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T]
      with z hz
  simpa only [Real.norm_eq_abs, mu] using
    sparseObservableLearnerScore_abs_le hk
      ((sparseHiddenTableParameterFamily hk eta heta0 heta
        n' q c0 B).at z.1) (sparseHiddenTableU z.1)
      (sparseHiddenTableU_abs_le_one z.1) T z.2 hz

/-- Integral expansion of the observable `Gamma` into the group maxima and
the learner score. -/
theorem integral_sparseGamma_eq_groupSum_sub_learner
    {n n' k r B T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (P : Policy n k) :
    (∫ z, sparseGamma hk eta heta0 heta q c0 hn' hprod hr sigma T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
          (sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B) T) =
      (∑ g : Fin k,
        ∫ z, sparseObservableGroupMax hprod hr sigma
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1)
            g T z.2
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
            (sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B) T) -
        ∫ z, sparseObservableLearnerScore
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at z.1) n' q c0 (sparseHiddenTableU z.1) T z.2
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P
            (sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B) T := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n) P
    (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  have hgroups : forall g : Fin k, Integrable
      (fun z : SparseHiddenTable B n × History n k T =>
        sparseObservableGroupMax hprod hr sigma
          ((sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B).at z.1) hn' q c0 (sparseHiddenTableU z.1)
          g T z.2) mu := fun g =>
    integrable_sparseJointObservableGroupMax hk eta heta0 heta q c0 hn'
      hprod hr sigma P g
  have hlearner := integrable_sparseJointObservableLearnerScore
    (B := B) (n' := n') (T := T) hk eta heta0 heta q c0 P
  unfold sparseGamma sparseHistoryGamma
  rw [integral_sub (integrable_finsetSum _ fun g _hg => hgroups g) hlearner,
    integral_finsetSum Finset.univ (fun g _hg => hgroups g)]

/-- The labeled equipartition counts every signal coordinate exactly once. -/
theorem sum_sum_sparsePartitionGroup
    {n' k r : Nat} (hprod : n' = k * r)
    (sigma : Equiv.Perm (Fin n')) (f : Fin n' -> Real) :
    (∑ g : Fin k, ∑ j ∈ sparsePartitionGroup hprod sigma g, f j) =
      ∑ j : Fin n', f j := by
  classical
  unfold sparsePartitionGroup
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  simp

/-- Exact algebraic summation of the groupwise changed-law maximum bounds,
the score-bias estimate, the positive drift estimate, and the average-TV
penalty.  This is the displayed computation immediately before
`eq:lower-sparse-positive-event`. -/
theorem sparse_changed_group_mean_combination
    {n' k r T : Nat} (hk : 1 <= k) (hprod : n' = k * r)
    (sigma : Equiv.Perm (Fin n'))
    (changed base : Fin n' -> Real) (group eps : Fin k -> Real)
    (learner gammaMean : Real)
    (hgroup : forall g : Fin k,
      (r : Real)⁻¹ *
          ∑ j ∈ sparsePartitionGroup hprod sigma g, changed j -
        2 * (T : Real) * eps g <= group g)
    (hdrift : sparseA / 3 * (k : Real) * T <=
      (r : Real)⁻¹ * ∑ j : Fin n', (changed j - base j))
    (hbias : -(48 * Real.sqrt sparseRho * (k : Real) * T) <=
      (r : Real)⁻¹ * ∑ j : Fin n', base j - learner)
    (htv : (∑ g : Fin k, eps g) / (k : Real) <=
      (2 : Real) ^ (-16 : Int))
    (hgamma : (∑ g : Fin k, group g) - learner <= gammaMean) :
    sparseA / 4 * (k : Real) * T <= gammaMean := by
  have hkR : 0 < (k : Real) := by exact_mod_cast hk
  have hsumGroup := Finset.sum_le_sum fun g
      (_hg : g ∈ (Finset.univ : Finset (Fin k))) => hgroup g
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsumGroup
  rw [sum_sum_sparsePartitionGroup hprod sigma changed] at hsumGroup
  have hsumEps : (∑ g : Fin k, eps g) <=
      (2 : Real) ^ (-16 : Int) * (k : Real) := by
    exact (div_le_iff₀ hkR).mp htv
  have hpenalty :
      2 * (T : Real) * (∑ g : Fin k, eps g) <=
        (1 / (2 : Real) ^ 15) * (k : Real) * T := by
    calc
      2 * (T : Real) * (∑ g : Fin k, eps g) <=
          2 * (T : Real) *
            ((2 : Real) ^ (-16 : Int) * (k : Real)) :=
        mul_le_mul_of_nonneg_left hsumEps (by positivity)
      _ = (1 / (2 : Real) ^ 15) * (k : Real) * T := by
        norm_num [zpow_neg]
        ring
  have hsplit :
      (r : Real)⁻¹ * ∑ j : Fin n', changed j - learner =
        ((r : Real)⁻¹ * ∑ j : Fin n', (changed j - base j)) +
          ((r : Real)⁻¹ * ∑ j : Fin n', base j - learner) := by
    rw [Finset.sum_sub_distrib]
    ring
  have htoGamma :
      ((r : Real)⁻¹ * ∑ j : Fin n', (changed j - base j)) +
          ((r : Real)⁻¹ * ∑ j : Fin n', base j - learner) -
          2 * (T : Real) * (∑ g : Fin k, eps g) <= gammaMean := by
    rw [← hsplit]
    exact (by linarith [hsumGroup, hgamma])
  exact sparse_mean_combination (Nat.cast_nonneg k) (Nat.cast_nonneg T)
    hdrift hbias hpenalty htoGamma

#print axioms integral_sparseObservableCoordinateScore_changedLaw
#print axioms integral_sparseObservableGroupMax_lower
#print axioms integral_sparseGamma_eq_groupSum_sub_learner
#print axioms sparse_changed_group_mean_combination

end

end MsetsLower.Lower.Sparse
