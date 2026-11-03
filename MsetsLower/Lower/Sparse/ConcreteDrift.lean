import MsetsLower.Lower.Sparse.ConcreteDiagonal
import MsetsLower.Lower.Sparse.PositiveDriftExpectation
import MsetsLower.Lower.Sparse.GammaMean

/-!
# Concrete positive drift on the genuine finite hidden table

The pathwise drift lemma is naturally stated for the infinite table obtained
by changing one coordinate.  The likelihood experiment, however, changes a
column of the genuine finite hidden table.  This file proves that the two
descriptions agree at every round before `q * B`, integrates the resulting
pathwise inequality, and discharges the positive-core premise using the
actual hidden-table joint law.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback Set
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-- Before the active horizon, scoring the genuinely transformed finite
table is exactly the same as scoring the pointwise transformed infinite
table.  This is the finite-table bridge needed by the positive-drift proof. -/
theorem sparseObservableCoordinateScore_coordinateEquiv_eq
    {B n n' k q c0 : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (hn' : n' <= n) (j : Fin n') (table : SparseHiddenTable B n) :
    forall T (h : History n k T), T <= q * B ->
      sparseObservableCoordinateScore
          ((sparseHiddenTableParameterFamily hk eta heta0 heta
            n' q c0 B).at
            (sparseHiddenTableCoordinateEquiv B n a
              (by rw [abs_of_nonneg ha0]; exact ha)
              (sparseSignalCoordinate hn' j) table))
          hn' q c0
          (sparseHiddenTableU
            (sparseHiddenTableCoordinateEquiv B n a
              (by rw [abs_of_nonneg ha0]; exact ha)
              (sparseSignalCoordinate hn' j) table))
          j T h =
        sparseObservableCoordinateScore
          (sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
            (sparseTransformTableCoordinate a hn'
              (sparseHiddenTableU table) j)
            (fun b i => (abs_le).2
              (sparseTransformTableCoordinate_mem_Icc ha0 ha hn'
                (fun b i => (abs_le).1
                  (sparseHiddenTableU_abs_le_one table b i)) j b i)))
          hn' q c0
          (sparseTransformTableCoordinate a hn'
            (sparseHiddenTableU table) j)
          j T h := by
  intro T
  induction T with
  | zero =>
      intro h _hT
      rfl
  | succ t ih =>
      intro h hT
      rw [sparseObservableCoordinateScore_succ,
        sparseObservableCoordinateScore_succ,
        ih h.1 (by omega)]
      have ht : t < q * B := by omega
      have hb : t / q < B := sparse_block_index_lt ht
      let transformed := sparseHiddenTableCoordinateEquiv B n a
        (by rw [abs_of_nonneg ha0]; exact ha)
        (sparseSignalCoordinate hn' j) table
      have hread : forall i,
          sparseHiddenTableU transformed (t / q) i =
            sparseTransformTableCoordinate a hn'
              (sparseHiddenTableU table) j (t / q) i := by
        intro i
        exact sparseHiddenTableU_coordinateEquiv_of_lt
          a (by rw [abs_of_nonneg ha0]; exact ha) hn' j table hb i
      have hparameter := sparseFeedbackParameter_congr_currentBlock
        (n' := n') (q := q) (c0 := c0) eta t hread h.1 h.2.1
      congr 1
      change
        sparseHiddenTableU transformed (t / q)
              (sparseSignalCoordinate hn' j) *
              sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
              feedbackScoreShape
                (sparseFeedbackParameter eta n' q c0
                  (sparseHiddenTableU transformed) t h.1 h.2.1) h.2.2 =
          sparseTransformTableCoordinate a hn'
              (sparseHiddenTableU table) j (t / q)
                (sparseSignalCoordinate hn' j) *
              sparseActive q c0 (sparseSignalCoordinate hn' j) t h.1 *
              feedbackScoreShape
                (sparseFeedbackParameter eta n' q c0
                  (sparseTransformTableCoordinate a hn'
                    (sparseHiddenTableU table) j) t h.1 h.2.1) h.2.2
      rw [hread, hparameter]

/-- Pathwise drift for the literal finite-table coordinate changes used in
the likelihood experiment. -/
theorem sparseHiddenTable_total_drift
    {B n n' k q c0 T : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha0 : 0 <= a) (ha : a <= (1 : Real) / 8)
    (hn' : n' <= n) (table : SparseHiddenTable B n)
    (hT : T <= q * B) (h : History n k T)
    (hsupp : sparseHistoryInFeedbackSupport T h) :
    (∑ j : Fin n',
        (sparseObservableCoordinateScore
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at
              (sparseHiddenTableCoordinateEquiv B n a
                (by rw [abs_of_nonneg ha0]; exact ha)
                (sparseSignalCoordinate hn' j) table))
            hn' q c0
            (sparseHiddenTableU
              (sparseHiddenTableCoordinateEquiv B n a
                (by rw [abs_of_nonneg ha0]; exact ha)
                (sparseSignalCoordinate hn' j) table))
            j T h -
          sparseObservableCoordinateScore
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at table)
            hn' q c0 (sparseHiddenTableU table) j T h)) >=
      a * sparseFamilyTotalPositiveCore
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
          hn' q c0 (fun table : SparseHiddenTable B n =>
            sparseHiddenTableU table) T (table, h) -
        6 * a * eta * (T : Real) := by
  let U := sparseHiddenTableU table
  let V := (sparseHiddenTableParameterFamily hk eta heta0 heta
    n' q c0 B).at table
  let W : Fin n' -> SparseAdaptiveParameters n k := fun j =>
    sparseAdaptiveParametersOfTable hk eta heta0 heta n' q c0
      (sparseTransformTableCoordinate a hn' U j)
      (fun b i => (abs_le).2
        (sparseTransformTableCoordinate_mem_Icc ha0 ha hn'
          (fun b i => (abs_le).1
            (sparseHiddenTableU_abs_le_one table b i)) j b i))
  have hraw := sparse_observable_total_drift hk hn' ha0 ha heta0 U
    (fun b i => (abs_le).1 (sparseHiddenTableU_abs_le_one table b i))
    V W (fun j t h A => by
      dsimp [W, V, U]
      exact sparse_concrete_parameter_shift hk hn' heta0 heta ha0 ha
        (sparseHiddenTableU table)
        (fun b i => (abs_le).1
          (sparseHiddenTableU_abs_le_one table b i)) j t h A)
    h hsupp
  have heq (j : Fin n') :
      sparseObservableCoordinateScore (W j) hn' q c0
          (sparseTransformTableCoordinate a hn' U j) j T h =
        sparseObservableCoordinateScore
            ((sparseHiddenTableParameterFamily hk eta heta0 heta
              n' q c0 B).at
              (sparseHiddenTableCoordinateEquiv B n a
                (by rw [abs_of_nonneg ha0]; exact ha)
                (sparseSignalCoordinate hn' j) table))
            hn' q c0
            (sparseHiddenTableU
              (sparseHiddenTableCoordinateEquiv B n a
                (by rw [abs_of_nonneg ha0]; exact ha)
                (sparseSignalCoordinate hn' j) table))
            j T h := by
    symm
    exact sparseObservableCoordinateScore_coordinateEquiv_eq
      hk eta heta0 heta a ha0 ha hn' j table T h hT
  simpa only [V, W, U, sparseFamilyTotalPositiveCore,
    sparseObservableTotalPositiveCore, heq] using hraw

/- Concrete expected positive drift, in precisely the changed/base integral
form consumed by the group-maximum argument. -/
set_option maxHeartbeats 10000000 in
-- The theorem expands several dependent history integrals and finite sums.
theorem lower_positive_drift_concreteFullTable
    {B n n' k q c0 r ell T : Nat} (P : Policy n k)
    (hk : 1 <= k) (eta : Real) (heta0 : 0 <= eta)
    (heta : eta <= (1 : Real) / 16) (hn' : n' <= n)
    (hr : 0 < r) (hrLarge : 2 ^ 32 <= r) (hell : 0 < ell)
    (hprod : n' = k * r) (hqeq : q = r * ell)
    (hc0eq : c0 = 8 * ell) (hT : T <= B * q) :
    sparseA / 3 * (k : Real) * T <=
      (r : Real)⁻¹ * ∑ j : Fin n',
        ((∫ z,
            sparseObservableCoordinateScore
              ((sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B).at z.1)
              hn' q c0 (sparseHiddenTableU z.1) j T z.2
            ∂Measure.map
              (sparseHiddenTableCoordinateJointMap sparseA
                (by norm_num [sparseA]) (sparseSignalCoordinate hn' j))
              (sparseJointLaw (sparseHiddenTableMeasure B n)
                (sparseCenteredPolicy P)
                (sparseHiddenTableParameterFamily hk eta heta0 heta
                  n' q c0 B) T)) -
          (∫ z,
            sparseObservableCoordinateScore
              ((sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B).at z.1)
              hn' q c0 (sparseHiddenTableU z.1) j T z.2
            ∂sparseJointLaw (sparseHiddenTableMeasure B n)
              (sparseCenteredPolicy P)
              (sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B) T)) := by
  classical
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n)
    (sparseCenteredPolicy P) F T
  let base : Fin n' -> SparseHiddenTable B n × History n k T -> Real :=
    fun j z => sparseObservableCoordinateScore (F.at z.1) hn' q c0
      (sparseHiddenTableU z.1) j T z.2
  let changed : Fin n' -> SparseHiddenTable B n × History n k T -> Real :=
    fun j z => sparseObservableCoordinateScore
      (F.at (sparseHiddenTableCoordinateEquiv B n sparseA
        (by norm_num [sparseA]) (sparseSignalCoordinate hn' j) z.1))
      hn' q c0
      (sparseHiddenTableU
        (sparseHiddenTableCoordinateEquiv B n sparseA
          (by norm_num [sparseA]) (sparseSignalCoordinate hn' j) z.1))
      j T z.2
  let core := sparseFamilyTotalPositiveCore F hn' q c0
    (fun table : SparseHiddenTable B n => sparseHiddenTableU table) T
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, sparseJointLaw]
    infer_instance
  have hbaseMeas (j : Fin n') : Measurable (base j) := by
    dsimp [base, F]
    exact measurable_sparseFamilyObservableCoordinateScore
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
      sparseHiddenTableU
      (fun b i => measurable_sparseHiddenTableU B n b i) hn' q c0 j T
  have hchangedMeas (j : Fin n') : Measurable (changed j) := by
    let score : SparseHiddenTable B n × History n k T -> Real := fun z =>
      sparseObservableCoordinateScore (F.at z.1) hn' q c0
        (sparseHiddenTableU z.1) j T z.2
    have hscore : Measurable score := by
      dsimp [score, F]
      exact measurable_sparseFamilyObservableCoordinateScore
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
        sparseHiddenTableU
        (fun b i => measurable_sparseHiddenTableU B n b i) hn' q c0 j T
    let jointMap : SparseHiddenTable B n × History n k T ->
        SparseHiddenTable B n × History n k T := fun z =>
      (sparseHiddenTableCoordinateEquiv B n sparseA
        (by norm_num [sparseA]) (sparseSignalCoordinate hn' j) z.1, z.2)
    have hjointMap : Measurable jointMap :=
      (((sparseHiddenTableCoordinateEquiv B n sparseA
        (by norm_num [sparseA]) (sparseSignalCoordinate hn' j)).measurable.comp
          measurable_fst).prodMk measurable_snd)
    have heq : changed j = score ∘ jointMap := rfl
    rw [heq]
    exact hscore.comp hjointMap
  have hsupport : ∀ᵐ z ∂mu,
      sparseHistoryInFeedbackSupport T z.2 := by
    dsimp [mu, F]
    exact ae_sparseJointLaw_history_support
      (sparseHiddenTableMeasure B n) (sparseCenteredPolicy P)
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T
  have hbaseInt (j : Fin n') : Integrable (base j) mu := by
    apply Integrable.of_bound (hbaseMeas j).aestronglyMeasurable (T : Real)
    filter_upwards [hsupport] with z hz
    simpa only [Real.norm_eq_abs, base, F] using
      sparseObservableCoordinateScore_abs_le
        (q := q) (c0 := c0) (F.at z.1) hn'
        (sparseHiddenTableU z.1) (sparseHiddenTableU_abs_le_one z.1)
        j T z.2 hz
  have hchangedInt (j : Fin n') : Integrable (changed j) mu := by
    apply Integrable.of_bound (hchangedMeas j).aestronglyMeasurable (T : Real)
    filter_upwards [hsupport] with z hz
    simpa only [Real.norm_eq_abs, changed, F] using
      sparseObservableCoordinateScore_abs_le
        (q := q) (c0 := c0)
        (F.at (sparseHiddenTableCoordinateEquiv B n sparseA
          (by norm_num [sparseA]) (sparseSignalCoordinate hn' j) z.1))
        hn'
        (sparseHiddenTableU
          (sparseHiddenTableCoordinateEquiv B n sparseA
            (by norm_num [sparseA]) (sparseSignalCoordinate hn' j) z.1))
        (sparseHiddenTableU_abs_le_one
          (sparseHiddenTableCoordinateEquiv B n sparseA
            (by norm_num [sparseA]) (sparseSignalCoordinate hn' j) z.1))
        j T z.2 hz
  have hcoreInt : Integrable core mu := by
    dsimp [core, mu, F]
    exact integrable_sparseFamilyTotalPositiveCore_jointLaw
      (sparseHiddenTableMeasure B n) (sparseCenteredPolicy P)
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
      hn' (fun table : SparseHiddenTable B n => sparseHiddenTableU table)
      (fun b i => measurable_sparseHiddenTableU B n b i)
      (fun table b i => (abs_le).1
        (sparseHiddenTableU_abs_le_one table b i))
  have hpath : ∀ᵐ z ∂mu,
      sparseA * core z - 6 * sparseA * eta * (T : Real) <=
        ∑ j : Fin n', (changed j z - base j z) := by
    filter_upwards [hsupport] with z hz
    dsimp [changed, base, core, F]
    simpa [Nat.mul_comm] using sparseHiddenTable_total_drift
      hk eta heta0 heta sparseA (by norm_num [sparseA])
      (by norm_num [sparseA]) hn' z.1 (by simpa [Nat.mul_comm] using hT)
      z.2 hz
  have hdiffInt (j : Fin n') :
      Integrable (fun z => changed j z - base j z) mu :=
    (hchangedInt j).sub (hbaseInt j)
  have hint := integral_mono_ae
    ((hcoreInt.const_mul sparseA).sub (integrable_const _))
    (integrable_finsetSum _ fun j _ => hdiffInt j)
    hpath
  change (∫ z, sparseA * core z - 6 * sparseA * eta * (T : Real) ∂mu) <=
      ∫ z, (∑ j : Fin n', (changed j z - base j z)) ∂mu at hint
  rw [integral_sub (hcoreInt.const_mul sparseA) (integrable_const _),
    integral_const_mul, integral_const, probReal_univ, one_smul,
    integral_finsetSum Finset.univ
      (fun j _ => hdiffInt j)] at hint
  simp_rw [integral_sub (hchangedInt _) (hbaseInt _)] at hint
  have hcoreLower := integral_sparseHiddenTableTotalPositiveCore_div_r_lower
    (sparseCenteredPolicy P) hk eta heta0 heta hn' hr hell hprod hqeq
      hc0eq hT
  have hrReal : 0 < (r : Real) := by exact_mod_cast hr
  have hnormalized :
      sparseA * ((1 / (r : Real)) * ∫ z, core z ∂mu) -
          6 * sparseA * eta * (T : Real) / (r : Real) <=
        (r : Real)⁻¹ * ∑ j : Fin n',
          ((∫ z, changed j z ∂mu) - (∫ z, base j z ∂mu)) := by
    have hs := mul_le_mul_of_nonneg_left hint
      (by positivity : (0 : Real) <= 1 / (r : Real))
    calc
      sparseA * ((1 / (r : Real)) * ∫ z, core z ∂mu) -
            6 * sparseA * eta * (T : Real) / (r : Real) =
          (1 / (r : Real)) *
            (sparseA * (∫ z, core z ∂mu) -
              6 * sparseA * eta * (T : Real)) := by ring
      _ <= (1 / (r : Real)) * ∑ j : Fin n',
          ((∫ z, changed j z ∂mu) - (∫ z, base j z ∂mu)) := hs
      _ = (r : Real)⁻¹ * ∑ j : Fin n',
          ((∫ z, changed j z ∂mu) - (∫ z, base j z ∂mu)) := by
        rw [one_div]
  have hdrift := lower_positive_drift_arithmetic
    (a := sparseA) (eta := eta) (r := (r : Real)) (k := (k : Real))
    (T := (T : Real)) (core := (1 / (r : Real)) * ∫ z, core z ∂mu)
    (drift := (r : Real)⁻¹ * ∑ j : Fin n',
      ((∫ z, changed j z ∂mu) - (∫ z, base j z ∂mu)))
    (by norm_num [sparseA]) heta0 (by exact_mod_cast hrLarge)
    (by exact_mod_cast hk) (Nat.cast_nonneg T) heta hcoreLower hnormalized
  have hmap (j : Fin n') :
      (∫ z, base j z ∂Measure.map
          (sparseHiddenTableCoordinateJointMap sparseA
            (by norm_num [sparseA]) (sparseSignalCoordinate hn' j)) mu) =
        ∫ z, changed j z ∂mu := by
    rw [sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
      (sparseCenteredPolicy P) F sparseA (by norm_num [sparseA])
        (sparseSignalCoordinate hn' j) T]
    exact integral_sparseObservableCoordinateScore_changedLaw
      (sparseCenteredPolicy P) F sparseA (by norm_num [sparseA])
        hn' q c0 j
  dsimp [F, mu, base] at hmap
  dsimp [F, mu, base, changed, core] at hdrift
  simpa only [hmap] using hdrift

#print axioms sparseObservableCoordinateScore_coordinateEquiv_eq
#print axioms sparseHiddenTable_total_drift
#print axioms lower_positive_drift_concreteFullTable

end

end MsetsLower.Lower.Sparse
