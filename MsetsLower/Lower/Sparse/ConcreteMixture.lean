import MsetsLower.Lower.Sparse.ConcreteLikelihood
import MsetsLower.Lower.Sparse.FinalArithmetic
import MsetsLower.Lower.Sparse.MixtureArithmetic

/-!
# Concrete chi-square mixture for the sparse lower bound

This file specializes the full hidden-table likelihood estimates to the
manuscript's numerical chi-square and total-variation budgets.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower.Lower Feedback MeasureTheory Probability ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-- The aggregate off-diagonal term produced by the good-partition theorem is
literally the cross term displayed in the manuscript. -/
theorem sparseConcrete_cross_aggregate_identity
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T) :
    (128 * sparseA ^ 2 * sparseEta n k T ^ 2 *
          Real.exp (128 *
            (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)))) *
        ((sparseT0 n k T : Real) / (k : Real)) /
          ((k : Real) * (sparseRatio n k : Real) ^ 2) =
      (16 * sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) /
          (sparseRatio n k : Real)) *
        Real.exp (128 * sparseA ^ 2 * sparseRho *
          (sparseBlockCount n k : Real)) := by
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hrposNat : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hBposNat : 0 < sparseBlockCount n k :=
    sparseBlockCount_one_le hr
  have hcNat := sparseC0_ge hk hr hT
  have hcposNat : 0 < sparseC0 n k T :=
    lt_of_lt_of_le (by positivity : 0 < 256 * k ^ 2) hcNat
  have hellpos : 0 < sparseEll n k T := by
    simpa [sparseC0] using hcposNat
  have ht0posNat : 0 < sparseT0 n k T := by
    simp only [sparseT0, sparseQ]
    positivity
  have hkpos : 0 < (k : Real) := by exact_mod_cast hkposNat
  have hrpos : 0 < (sparseRatio n k : Real) := by
    exact_mod_cast hrposNat
  have ht0pos : 0 < (sparseT0 n k T : Real) := by
    exact_mod_cast ht0posNat
  have hid := sparseEta_mul_T0_sq_identity hk hr hT
  have hid' :
      (sparseT0 n k T : Real) *
          (sparseEta n k T ^ 2 * (sparseT0 n k T : Real)) =
        (sparseT0 n k T : Real) *
          (sparseRho / 8 * (sparseSignalCount n k : Real) *
            (k : Real) * (sparseBlockCount n k : Real)) := by
    calc
      (sparseT0 n k T : Real) *
          (sparseEta n k T ^ 2 * (sparseT0 n k T : Real)) =
        (sparseEta n k T * (sparseT0 n k T : Real)) ^ 2 := by ring
      _ = sparseRho / 8 * (sparseSignalCount n k : Real) * (k : Real) *
          (sparseT0 n k T : Real) * (sparseBlockCount n k : Real) := hid
      _ = (sparseT0 n k T : Real) *
          (sparseRho / 8 * (sparseSignalCount n k : Real) *
            (k : Real) * (sparseBlockCount n k : Real)) := by ring
  have hetaT :
      sparseEta n k T ^ 2 * (sparseT0 n k T : Real) =
        sparseRho / 8 * (sparseSignalCount n k : Real) *
          (k : Real) * (sparseBlockCount n k : Real) := by
    exact mul_left_cancel₀ ht0pos.ne' hid'
  rw [show (sparseSignalCount n k : Real) =
      (k : Real) * (sparseRatio n k : Real) by
    simp [sparseSignalCount]] at hetaT
  field_simp [hkpos.ne', hrpos.ne']
  nlinarith [hetaT]

/-- The concrete full-table good partition has average density chi-square at
most `2^-30`, exactly the hypothesis used in `eq:lower-mixture-tv`. -/
theorem exists_sparseConcrete_goodPartition_average_densityChiSquare_le_two_zpow
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) :
    ∃ sigma : Equiv.Perm (Fin (sparseSignalCount n k)),
      (forall g : Fin k,
        (sparsePartitionGroup (rfl : sparseSignalCount n k =
            k * sparseRatio n k) sigma g).card = sparseRatio n k) ∧
      (∑ g : Fin k, densityChiSquare (sparseConcreteJointLaw hk hr hT P)
          (finsetUniformMixtureDensity
            (sparsePartitionGroup (rfl : sparseSignalCount n k =
              k * sparseRatio n k) sigma g)
            (fun j => ennrealDensityReal
              (sparseConcreteCoordinateLikelihood hk hr hT j)))) / (k : Real) <=
        (2 : Real) ^ (-30 : Int) := by
  obtain ⟨sigma, hcard, hchi⟩ :=
    exists_sparseConcrete_goodPartition_average_densityChiSquare_le
      hk hr hT P
  refine ⟨sigma, hcard, hchi.trans ?_⟩
  rw [sparseConcrete_cross_aggregate_identity hk hr hT]
  exact sparse_mixture_chiSquare_budget_parameters hr

/-- The literal uniform mixture of the full-table coordinate-changed laws in
one group of a permutation equipartition. -/
def sparseConcreteGroupMixtureMeasure
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (sigma : Equiv.Perm (Fin (sparseSignalCount n k)))
    (g : Fin k) :
    Measure (SparseHiddenTable (sparseBlockCount n k) n ×
      History n k (sparseT0 n k T)) :=
  (sparseConcreteJointLaw hk hr hT P).withDensity (fun z => ENNReal.ofReal
    (finsetUniformMixtureDensity
      (sparsePartitionGroup (rfl : sparseSignalCount n k =
        k * sparseRatio n k) sigma g)
      (fun j => ennrealDensityReal
        (sparseConcreteCoordinateLikelihood hk hr hT j)) z))

/-- Every concrete group mixture is a probability measure.  This follows from
the exact full-table pushforward identity for each coordinate, rather than
from an assumed density-normalization premise. -/
theorem sparseConcreteGroupMixtureMeasure_isProbability
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (sigma : Equiv.Perm (Fin (sparseSignalCount n k)))
    (g : Fin k) :
    IsProbabilityMeasure
      (sparseConcreteGroupMixtureMeasure hk hr hT P sigma g) := by
  let base := sparseConcreteJointLaw hk hr hT P
  let Lambda : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> ENNReal :=
    sparseConcreteCoordinateLikelihood hk hr hT
  let L : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> Real :=
    fun j => ennrealDensityReal (Lambda j)
  let G : Finset (Fin (sparseSignalCount n k)) :=
    sparsePartitionGroup (rfl : sparseSignalCount n k =
      k * sparseRatio n k) sigma g
  letI : IsProbabilityMeasure base := by
    dsimp [base, sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  have hLambda : forall j, Measurable (Lambda j) := by
    intro j
    exact measurable_sparseConcreteCoordinateLikelihood hk hr hT j
  have hdiag : forall j,
      (∫⁻ z, Lambda j z * Lambda j z ∂base) <=
        ENNReal.ofReal (Real.exp
          (10 * sparseA ^ 2 * (sparseBlockCount n k : Real))) := by
    intro j
    simpa [base, Lambda, sparseConcreteJointLaw,
      sparseConcreteCoordinateLikelihood, pow_two] using
        lower_likelihood_diagonal_concreteFullTable hk hr hT P j
  have hfinite : forall j, ∀ᵐ z ∂base, Lambda j z < ∞ := by
    intro j
    have hmoment :
        (∫⁻ z, Lambda j z * Lambda j z ∂base) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiag j)
    have hae : ∀ᵐ z ∂base, Lambda j z * Lambda j z < ∞ :=
      ae_lt_top ((hLambda j).mul (hLambda j)) hmoment
    filter_upwards [hae] with z hz
    rw [lt_top_iff_ne_top]
    intro hjtop
    rw [hjtop] at hz
    simp at hz
  have hcomponentQ : forall j,
      IsProbabilityMeasure (base.withDensity (Lambda j)) := by
    intro j
    have hmap : Measurable
        (sparseHiddenTableCoordinateJointMap
          (B := sparseBlockCount n k) (k := k) (T := sparseT0 n k T)
          sparseA (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j)) :=
      ((sparseHiddenTableCoordinateEquiv (sparseBlockCount n k) n sparseA
          (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j)).measurable.comp
        measurable_fst).prodMk measurable_snd
    have hchange :
        Measure.map
            (sparseHiddenTableCoordinateJointMap
              (B := sparseBlockCount n k) (k := k) (T := sparseT0 n k T)
              sparseA (by norm_num [sparseA])
              (sparseSignalCoordinate (sparseSignalCount_le n k) j)) base =
          base.withDensity (Lambda j) := by
      simpa [base, Lambda, sparseConcreteJointLaw,
        sparseConcreteCoordinateLikelihood] using
          sparseHiddenTableCoordinateJointLaw_map_eq_withDensity P
            (sparseConcreteHiddenTableParameterFamily hk hr hT)
            sparseA (by norm_num [sparseA])
            (sparseSignalCoordinate (sparseSignalCount_le n k) j)
            (sparseT0 n k T)
    rw [← hchange, isProbabilityMeasure_iff,
      Measure.map_apply hmap MeasurableSet.univ]
    simp
  have hG : G.Nonempty := by
    have hcard : G.card = sparseRatio n k :=
      card_sparsePartitionGroup (rfl : sparseSignalCount n k = k * sparseRatio n k) sigma g
    exact Finset.card_pos.mp (hcard.symm ▸ lt_of_lt_of_le (by norm_num) hr)
  have hmixture := probability_withDensity_finsetUniformMixtureDensity
    base G hG L
    (fun j _hj => measurable_ennrealDensityReal (hLambda j))
    (fun j _hj z => ennrealDensityReal_nonneg (Lambda j) z)
    (fun j _hj => by
      rw [withDensity_ofReal_ennrealDensityReal_eq
        base (Lambda j) (hfinite j)]
      exact hcomponentQ j)
  simpa [sparseConcreteGroupMixtureMeasure, base, Lambda, L, G] using hmixture

/-- The same group measure written as the literal uniform average of the
coordinate-changed pushforward laws.  The local nonemptiness proof is packaged
here because `averageMeasure` uses it as a typeclass argument. -/
def sparseConcreteGroupAverageMap
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (sigma : Equiv.Perm (Fin (sparseSignalCount n k)))
    (g : Fin k) :
    Measure (SparseHiddenTable (sparseBlockCount n k) n ×
      History n k (sparseT0 n k T)) := by
  let G := sparsePartitionGroup (rfl : sparseSignalCount n k =
    k * sparseRatio n k) sigma g
  have hG : G.Nonempty := by
    have hcard : G.card = sparseRatio n k :=
      card_sparsePartitionGroup (rfl : sparseSignalCount n k = k * sparseRatio n k) sigma g
    exact Finset.card_pos.mp (hcard.symm ▸ lt_of_lt_of_le (by norm_num) hr)
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
  exact Probability.averageMeasure (fun j : ↥G =>
    Measure.map
      (sparseHiddenTableCoordinateJointMap
        (B := sparseBlockCount n k) (k := k) (T := sparseT0 n k T)
        sparseA (by norm_num [sparseA])
        (sparseSignalCoordinate (sparseSignalCount_le n k) j.1))
      (sparseConcreteJointLaw hk hr hT P))

/-- The concrete density mixture is exactly the average of the corresponding
full-table coordinate-change pushforwards. -/
theorem sparseConcreteGroupMixtureMeasure_eq_average_map
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (sigma : Equiv.Perm (Fin (sparseSignalCount n k)))
    (g : Fin k) :
    sparseConcreteGroupMixtureMeasure hk hr hT P sigma g =
      sparseConcreteGroupAverageMap hk hr hT P sigma g := by
  classical
  let base := sparseConcreteJointLaw hk hr hT P
  let Lambda : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> ENNReal :=
    sparseConcreteCoordinateLikelihood hk hr hT
  let L : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> Real :=
    fun j => ennrealDensityReal (Lambda j)
  let G : Finset (Fin (sparseSignalCount n k)) :=
    sparsePartitionGroup (rfl : sparseSignalCount n k =
      k * sparseRatio n k) sigma g
  letI : IsProbabilityMeasure base := by
    dsimp [base, sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  have hG : G.Nonempty := by
    have hcard : G.card = sparseRatio n k :=
      card_sparsePartitionGroup (rfl : sparseSignalCount n k = k * sparseRatio n k) sigma g
    exact Finset.card_pos.mp (hcard.symm ▸ lt_of_lt_of_le (by norm_num) hr)
  letI : Nonempty (↥G) := Finset.nonempty_coe_sort.mpr hG
  have hLambda : forall j, Measurable (Lambda j) := by
    intro j
    exact measurable_sparseConcreteCoordinateLikelihood hk hr hT j
  have hdiag : forall j,
      (∫⁻ z, Lambda j z * Lambda j z ∂base) <=
        ENNReal.ofReal (Real.exp
          (10 * sparseA ^ 2 * (sparseBlockCount n k : Real))) := by
    intro j
    simpa [base, Lambda, sparseConcreteJointLaw,
      sparseConcreteCoordinateLikelihood, pow_two] using
        lower_likelihood_diagonal_concreteFullTable hk hr hT P j
  have hfinite : forall j, ∀ᵐ z ∂base, Lambda j z < ∞ := by
    intro j
    have hmoment :
        (∫⁻ z, Lambda j z * Lambda j z ∂base) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiag j)
    have hae : ∀ᵐ z ∂base, Lambda j z * Lambda j z < ∞ :=
      ae_lt_top ((hLambda j).mul (hLambda j)) hmoment
    filter_upwards [hae] with z hz
    rw [lt_top_iff_ne_top]
    intro hjtop
    rw [hjtop] at hz
    simp at hz
  change base.withDensity (fun z => ENNReal.ofReal
      (finsetUniformMixtureDensity G L z)) =
    Probability.averageMeasure (fun j : ↥G =>
      Measure.map
        (sparseHiddenTableCoordinateJointMap
          (B := sparseBlockCount n k) (k := k) (T := sparseT0 n k T)
          sparseA (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j.1)) base)
  rw [← averageMeasure_finset_withDensity_eq_withDensity
    base G hG L
      (fun j _hj => measurable_ennrealDensityReal (hLambda j))
      (fun j _hj z => ennrealDensityReal_nonneg (Lambda j) z)]
  apply congrArg Probability.averageMeasure
  funext j
  rw [withDensity_ofReal_ennrealDensityReal_eq
    base (Lambda j.1) (hfinite j.1)]
  symm
  simpa [base, Lambda, sparseConcreteJointLaw,
    sparseConcreteCoordinateLikelihood] using
      sparseHiddenTableCoordinateJointLaw_map_eq_withDensity P
        (sparseConcreteHiddenTableParameterFamily hk hr hT)
        sparseA (by norm_num [sparseA])
        (sparseSignalCoordinate (sparseSignalCount_le n k) j.1)
        (sparseT0 n k T)

/-- Total variation between one concrete group mixture and the base joint law.
The probability proofs needed by the finite-measure API are discharged inside
this definition. -/
def sparseConcreteGroupMixtureTV
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (sigma : Equiv.Perm (Fin (sparseSignalCount n k)))
    (g : Fin k) : Real := by
  let base := sparseConcreteJointLaw hk hr hT P
  let Q := sparseConcreteGroupMixtureMeasure hk hr hT P sigma g
  letI : IsProbabilityMeasure base := by
    dsimp [base, sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  letI : IsProbabilityMeasure Q := by
    dsimp [Q]
    exact sparseConcreteGroupMixtureMeasure_isProbability hk hr hT P sigma g
  exact totalVariationDistance Q base

/-- Concrete `eq:lower-mixture-tv`: the uniform mixtures of the actual
full-table coordinate-changed laws have average total variation at most
`2^-16`. -/
theorem exists_sparseConcrete_goodPartition_average_totalVariationDistance_le
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) :
    ∃ sigma : Equiv.Perm (Fin (sparseSignalCount n k)),
      (forall g : Fin k,
        (sparsePartitionGroup (rfl : sparseSignalCount n k =
            k * sparseRatio n k) sigma g).card = sparseRatio n k) ∧
      (∑ g : Fin k,
          sparseConcreteGroupMixtureTV hk hr hT P sigma g) / (k : Real) <=
        (2 : Real) ^ (-16 : Int) := by
  obtain ⟨sigma, hcard, hchi⟩ :=
    exists_sparseConcrete_goodPartition_average_densityChiSquare_le_two_zpow
      hk hr hT P
  let base := sparseConcreteJointLaw hk hr hT P
  let Lambda : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> ENNReal :=
    sparseConcreteCoordinateLikelihood hk hr hT
  let L : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> Real :=
    fun j => ennrealDensityReal (Lambda j)
  let G : Fin k -> Finset (Fin (sparseSignalCount n k)) := fun g =>
    sparsePartitionGroup (rfl : sparseSignalCount n k =
      k * sparseRatio n k) sigma g
  letI : IsProbabilityMeasure base := by
    dsimp [base, sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  have hLambda : forall j, Measurable (Lambda j) := by
    intro j
    exact measurable_sparseConcreteCoordinateLikelihood hk hr hT j
  have hdiag : forall j,
      (∫⁻ z, Lambda j z * Lambda j z ∂base) <=
        ENNReal.ofReal (Real.exp
          (10 * sparseA ^ 2 * (sparseBlockCount n k : Real))) := by
    intro j
    simpa [base, Lambda, sparseConcreteJointLaw,
      sparseConcreteCoordinateLikelihood, pow_two] using
        lower_likelihood_diagonal_concreteFullTable hk hr hT P j
  have hLambdaFinite : forall j, ∀ᵐ z ∂base, Lambda j z < ∞ := by
    intro j
    have hmoment :
        (∫⁻ z, Lambda j z * Lambda j z ∂base) ≠ ∞ :=
      ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiag j)
    have hae : ∀ᵐ z ∂base, Lambda j z * Lambda j z < ∞ :=
      ae_lt_top ((hLambda j).mul (hLambda j)) hmoment
    filter_upwards [hae] with z hz
    rw [lt_top_iff_ne_top]
    intro hjtop
    rw [hjtop] at hz
    simp at hz
  have hcomponentQ : forall j,
      IsProbabilityMeasure (base.withDensity (Lambda j)) := by
    intro j
    have hmap : Measurable
        (sparseHiddenTableCoordinateJointMap
          (B := sparseBlockCount n k) (k := k) (T := sparseT0 n k T)
          sparseA (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j)) :=
      ((sparseHiddenTableCoordinateEquiv (sparseBlockCount n k) n sparseA
          (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j)).measurable.comp
        measurable_fst).prodMk measurable_snd
    have hchange :
        Measure.map
            (sparseHiddenTableCoordinateJointMap
              (B := sparseBlockCount n k) (k := k) (T := sparseT0 n k T)
              sparseA (by norm_num [sparseA])
              (sparseSignalCoordinate (sparseSignalCount_le n k) j)) base =
          base.withDensity (Lambda j) := by
      simpa [base, Lambda, sparseConcreteJointLaw,
        sparseConcreteCoordinateLikelihood] using
          sparseHiddenTableCoordinateJointLaw_map_eq_withDensity P
            (sparseConcreteHiddenTableParameterFamily hk hr hT)
            sparseA (by norm_num [sparseA])
            (sparseSignalCoordinate (sparseSignalCount_le n k) j)
            (sparseT0 n k T)
    rw [← hchange, isProbabilityMeasure_iff,
      Measure.map_apply hmap MeasurableSet.univ]
    simp
  have hL : forall j, Measurable (L j) := by
    intro j
    exact measurable_ennrealDensityReal (hLambda j)
  have hL0 : forall j z, 0 <= L j z := by
    intro j z
    exact ennrealDensityReal_nonneg (Lambda j) z
  have hLint : forall j, Integrable (L j) base := by
    intro j
    exact (ennrealDensityReal_integrable_and_integral_eq_one
      base (Lambda j) (hLambda j) (hLambdaFinite j) (hcomponentQ j)).1
  have hmomentFinite : forall j l,
      (∫⁻ z, Lambda j z * Lambda l z ∂base) ≠ ∞ := by
    intro j l
    by_cases hjl : j = l
    · subst l
      exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hdiag j)
    · exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (by
        simpa [base, Lambda] using
          lower_likelihood_cross_concreteFullTable_expectedN hk hr hT P hjl)
  have hpairInt : forall j l,
      Integrable (fun z => L j z * L l z) base := by
    intro j l
    exact (ennrealDensityReal_pair_integrable_and_integral_eq
      base (Lambda j) (Lambda l) (hLambda j) (hLambda l)
        (hLambdaFinite j) (hLambdaFinite l) (hmomentFinite j l)).1
  have hG : forall g, (G g).Nonempty := by
    intro g
    apply Finset.card_pos.mp
    dsimp [G]
    rw [hcard g]
    exact lt_of_lt_of_le (by norm_num) hr
  have hQg : forall g, IsProbabilityMeasure
      (base.withDensity (fun z => ENNReal.ofReal
        (finsetUniformMixtureDensity (G g) L z))) := by
    intro g
    apply probability_withDensity_finsetUniformMixtureDensity
      base (G g) (hG g) L
    · intro j _hj
      exact hL j
    · intro j _hj z
      exact hL0 j z
    · intro j _hj
      rw [withDensity_ofReal_ennrealDensityReal_eq
        base (Lambda j) (hLambdaFinite j)]
      exact hcomponentQ j
  letI : Nonempty (Fin k) := ⟨⟨0, hk⟩⟩
  refine ⟨sigma, hcard, ?_⟩
  simpa [sparseConcreteGroupMixtureTV, sparseConcreteGroupMixtureMeasure,
    base, Lambda, L, G] using
    (lower_mixture_tv_finset_groups_of_average_chiSquare_le
      base G hG L hL hL0 hLint hpairInt hQg (by
        simpa [base, Lambda, L, G] using hchi))

#print axioms sparseConcrete_cross_aggregate_identity
#print axioms exists_sparseConcrete_goodPartition_average_densityChiSquare_le_two_zpow
#print axioms sparseConcreteGroupMixtureMeasure_isProbability
#print axioms sparseConcreteGroupMixtureMeasure_eq_average_map
#print axioms exists_sparseConcrete_goodPartition_average_totalVariationDistance_le

end

end MsetsLower.Lower.Sparse
