import MsetsLower.Lower.Sparse.Table

/-!
# Measurable changes of one full-table coordinate

The sparse likelihood calculation changes every block entry in one signal
column while leaving all other columns fixed.  This file lifts the column
diffeomorphism to the genuine finite hidden table and proves its exact
push-forward density under the iid table law.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory

noncomputable section

/-! ## Two finite-product measure helpers -/

/-- A measurable equivalence transports a density by composition with its
inverse. -/
theorem map_withDensity_measurableEquiv
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (mu : Measure X) (e : X ≃ᵐ Y) (d : X -> ENNReal)
    (hd : Measurable d) :
    Measure.map e (mu.withDensity d) =
      (Measure.map e mu).withDensity (d ∘ e.symm) := by
  ext s hs
  rw [Measure.map_apply e.measurable hs,
    withDensity_apply _ (hs.preimage e.measurable),
    withDensity_apply _ hs]
  rw [← lintegral_indicator (hs.preimage e.measurable)]
  rw [← lintegral_indicator hs]
  rw [lintegral_map
    ((hd.comp e.symm.measurable).indicator hs) e.measurable]
  apply lintegral_congr
  intro x
  by_cases hx : e x ∈ s <;> simp [Set.indicator, hx]

/-- Replacing one marginal of a finite probability product by a density is
the same as placing that density on the corresponding evaluation map. -/
theorem pi_withDensity_eval
    {N : Nat} {X : Type*} [MeasurableSpace X]
    (mu nu : Measure X) [IsProbabilityMeasure mu]
    [IsProbabilityMeasure nu] (j : Fin (N + 1))
    (d : X -> ENNReal) (hd : Measurable d)
    (hnu : nu = mu.withDensity d) :
    (Measure.pi (fun _ : Fin (N + 1) => mu)).withDensity
        (fun x => d (x j)) =
      Measure.pi (fun i : Fin (N + 1) => if i = j then nu else mu) := by
  let split := MeasurableEquiv.piFinSuccAbove
    (fun _ : Fin (N + 1) => X) j
  let rest : Measure (Fin N -> X) := Measure.pi (fun _ : Fin N => mu)
  let changed : Fin (N + 1) -> Measure X :=
    fun i => if i = j then nu else mu
  have hbase : Measure.map split
      (Measure.pi (fun _ : Fin (N + 1) => mu)) = mu.prod rest := by
    exact (measurePreserving_piFinSuccAbove
      (fun _ : Fin (N + 1) => mu) j).map_eq
  have hchanged : Measure.map split (Measure.pi changed) =
      nu.prod rest := by
    have hmp := (measurePreserving_piFinSuccAbove changed j).map_eq
    rw [hmp]
    change (if j = j then nu else mu).prod
        (Measure.pi fun i : Fin N =>
          if j.succAbove i = j then nu else mu) = _
    simp [rest]
  apply split.measurableEmbedding.map_injective
  change Measure.map split
      ((Measure.pi (fun _ : Fin (N + 1) => mu)).withDensity
        (d ∘ Function.eval j)) = _
  rw [map_withDensity_measurableEquiv _ split _
      (hd.comp (measurable_pi_apply j)), hbase, hchanged]
  have hdcomp : ((d ∘ Function.eval j) ∘ split.symm) =
      (fun z : X × (Fin N -> X) => d z.1) := by
    funext z
    simp [split]
  rw [hdcomp]
  calc
    (mu.prod rest).withDensity (fun z => d z.1) =
        (mu.withDensity d).prod
          (rest.withDensity (fun _ : Fin N -> X => (1 : ENNReal))) := by
      simpa only [Pi.one_apply, mul_one] using
        (prod_withDensity (μ := mu) (ν := rest) hd
          (measurable_const : Measurable
            (fun _ : Fin N -> X => (1 : ENNReal)))).symm
    _ = nu.prod rest := by
      rw [show (fun _ : Fin N -> X => (1 : ENNReal)) = 1 by rfl,
        withDensity_one, ← hnu]

/-! ## One-column transformation of the genuine hidden table -/

def sparseHiddenTableCoordinateEquiv
    (B n : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) : SparseHiddenTable B n ≃ᵐ SparseHiddenTable B n :=
  MeasurableEquiv.piCongrRight fun i : Fin n =>
    if i = j then sparseHiddenColumnEquiv B a ha
    else MeasurableEquiv.refl (SparseHiddenColumn B)

@[simp] theorem sparseHiddenTableCoordinateEquiv_apply
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j i : Fin n) (table : SparseHiddenTable B n) :
    sparseHiddenTableCoordinateEquiv B n a ha j table i =
      if i = j then sparseHiddenColumnEquiv B a ha (table i)
      else table i := by
  change (if i = j then sparseHiddenColumnEquiv B a ha
      else MeasurableEquiv.refl (SparseHiddenColumn B)) (table i) = _
  by_cases hij : i = j <;> simp [hij]

def sparseHiddenTableCoordinateImageDensity
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (table : SparseHiddenTable B n) : ENNReal :=
  sparseHiddenColumnImageDensity a ha B (table j)

theorem measurable_sparseHiddenTableCoordinateImageDensity
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) :
    Measurable (sparseHiddenTableCoordinateImageDensity (B := B) a ha j) :=
  (measurable_sparseHiddenColumnImageDensity a ha B).comp
    (measurable_pi_apply j)

/-- Exact full-table hidden push-forward density for changing one column. -/
theorem map_sparseHiddenTableCoordinateEquiv_measure
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) :
    Measure.map (sparseHiddenTableCoordinateEquiv B n a ha j)
        (sparseHiddenTableMeasure B n) =
      (sparseHiddenTableMeasure B n).withDensity
        (sparseHiddenTableCoordinateImageDensity a ha j) := by
  cases n with
  | zero => exact Fin.elim0 j
  | succ N =>
      let mu := sparseHiddenColumnMeasure B
      let e := sparseHiddenColumnEquiv B a ha
      let d := sparseHiddenColumnImageDensity a ha B
      let nu := Measure.map e mu
      letI : IsProbabilityMeasure mu := by dsimp [mu]; infer_instance
      letI : IsProbabilityMeasure nu := by
        rw [isProbabilityMeasure_iff]
        dsimp [nu]
        rw [Measure.map_apply e.measurable MeasurableSet.univ]
        simp
      have hnu : nu = mu.withDensity d := by
        dsimp [nu, mu, d, e]
        exact map_sparseHiddenColumnEquiv_measure a ha B
      have hpi := pi_withDensity_eval mu nu j d
        (measurable_sparseHiddenColumnImageDensity a ha B) hnu
      have hmap :
          Measure.map (sparseHiddenTableCoordinateEquiv B (N + 1) a ha j)
              (sparseHiddenTableMeasure B (N + 1)) =
            Measure.pi (fun i : Fin (N + 1) =>
              if i = j then nu else mu) := by
        unfold sparseHiddenTableMeasure sparseHiddenTableCoordinateEquiv
        change Measure.map
          (fun table i =>
            (if i = j then sparseHiddenColumnEquiv B a ha
              else MeasurableEquiv.refl (SparseHiddenColumn B)) (table i))
          (Measure.pi (fun _ : Fin (N + 1) =>
            sparseHiddenColumnMeasure B)) = _
        rw [Measure.pi_map_pi]
        · congr 1
          funext i
          by_cases hij : i = j
          · subst i
            simp [nu, mu, e]
          · simp only [hij, if_false]
            change Measure.map id (sparseHiddenColumnMeasure B) =
              sparseHiddenColumnMeasure B
            exact Measure.map_id
        · intro i
          by_cases hij : i = j
          · subst i
            simp only [if_pos]
            exact (sparseHiddenColumnEquiv B a ha).measurable.aemeasurable
          · simp only [if_neg hij]
            exact (MeasurableEquiv.refl
              (SparseHiddenColumn B)).measurable.aemeasurable
      rw [hmap]
      change Measure.pi (fun i : Fin (N + 1) =>
          if i = j then nu else mu) =
        (Measure.pi (fun _ : Fin (N + 1) => mu)).withDensity
          (fun table => d (table j))
      exact hpi.symm

/-! ## Reading the transformed table -/

private theorem measurableEquiv_prodCongr_apply
    {X Y X' Y' : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace X'] [MeasurableSpace Y']
    (e : X ≃ᵐ X') (f : Y ≃ᵐ Y') (x : X) (y : Y) :
    e.prodCongr f (x, y) = (e x, f y) := by
  rfl

theorem sparseHiddenColumnEquiv_succ_apply
    {B : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (column : SparseHiddenColumn B) (last : Real) :
    sparseHiddenColumnEquiv (B + 1) a ha (column, last) =
      (sparseHiddenColumnEquiv B a ha column,
        sparseHiddenEquiv a ha last) := by
  change ((sparseHiddenColumnEquiv B a ha).prodCongr
    (sparseHiddenEquiv a ha)) (column, last) = _
  rfl

theorem sparseHiddenColumnRawAt_equiv
    {B : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (column : SparseHiddenColumn B) (b : Fin B) :
    sparseHiddenColumnRawAt (sparseHiddenColumnEquiv B a ha column) b =
      sparseHiddenEquiv a ha (sparseHiddenColumnRawAt column b) := by
  induction B with
  | zero => exact Fin.elim0 b
  | succ B ih =>
      rcases column with ⟨column, last⟩
      rw [sparseHiddenColumnEquiv_succ_apply]
      refine Fin.lastCases ?_ (fun q => ?_) b
      · simp [sparseHiddenColumnRawAt]
      · simpa [sparseHiddenColumnRawAt] using ih column q

theorem sparseClampUnit_hiddenEquiv
    (a : Real) (ha : |a| <= (1 : Real) / 8) (u : Real) :
    sparseClampUnit (sparseHiddenEquiv a ha u) =
      sparseHiddenMapCore a (sparseClampUnit u) := by
  by_cases hu : u ∈ Icc (-1 : Real) 1
  · have hmap := sparseHiddenMapCore_mem_Icc ha hu
    rw [sparseHiddenEquiv_apply_of_mem ha hu,
      sparseClampUnit_eq_self hu, sparseClampUnit_eq_self hmap]
  · have hout : u < -1 ∨ 1 < u := by
      simp only [mem_Icc, not_and_or, not_le] at hu
      exact hu
    have heq : sparseHiddenEquiv a ha u = u := by
      simp [sparseHiddenEquiv, sparseHiddenMap, hu]
    rw [heq]
    rcases hout with hleft | hright
    · have hu1 : u <= 1 := by linarith
      rw [sparseClampUnit, min_eq_right hu1, max_eq_left hleft.le]
      simp [sparseHiddenMapCore, Feedback.shape]
    · have hneg : -1 <= (1 : Real) := by norm_num
      rw [sparseClampUnit, min_eq_left hright.le, max_eq_right hneg]
      simp [sparseHiddenMapCore, Feedback.shape]

theorem sparseHiddenColumnAt_equiv
    {B : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (column : SparseHiddenColumn B) {b : Nat} (hb : b < B) :
    sparseHiddenColumnAt (sparseHiddenColumnEquiv B a ha column) b =
      sparseHiddenMapCore a (sparseHiddenColumnAt column b) := by
  simp only [sparseHiddenColumnAt, dif_pos hb]
  rw [sparseHiddenColumnRawAt_equiv,
    sparseClampUnit_hiddenEquiv]

theorem sparseHiddenTableU_coordinateEquiv_of_lt
    {B n n' : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (hn' : n' <= n) (j : Fin n') (table : SparseHiddenTable B n)
    {b : Nat} (hb : b < B) (i : Fin n) :
    sparseHiddenTableU
        (sparseHiddenTableCoordinateEquiv B n a ha
          (sparseSignalCoordinate hn' j) table) b i =
      sparseTransformTableCoordinate a hn'
        (sparseHiddenTableU table) j b i := by
  unfold sparseHiddenTableU sparseTransformTableCoordinate
  rw [sparseHiddenTableCoordinateEquiv_apply]
  by_cases hi : i = sparseSignalCoordinate hn' j
  · simp only [hi, if_pos]
    rw [sparseHiddenColumnAt_equiv a ha _ hb]
    unfold sparseHiddenMapCore
    rfl
  · simp [hi]

/-! ## Full-table joint likelihood and diagonal moment -/

def sparseHiddenTableCoordinateJacobianAtSource
    {B n : Nat} (a : Real) (j : Fin n)
    (table : SparseHiddenTable B n) : ENNReal :=
  sparseHiddenColumnJacobianAtSource a B (table j)

theorem measurable_sparseHiddenTableCoordinateJacobianAtSource
    {B n : Nat} (a : Real) (j : Fin n) :
    Measurable (sparseHiddenTableCoordinateJacobianAtSource
      (B := B) a j) :=
  (measurable_sparseHiddenColumnJacobianAtSource a B).comp
    (measurable_pi_apply j)

@[simp] theorem sparseHiddenTableCoordinateImageDensity_apply_equiv
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (table : SparseHiddenTable B n) :
    sparseHiddenTableCoordinateImageDensity a ha j
        (sparseHiddenTableCoordinateEquiv B n a ha j table) =
      sparseHiddenTableCoordinateJacobianAtSource a j table := by
  unfold sparseHiddenTableCoordinateImageDensity
    sparseHiddenTableCoordinateJacobianAtSource
  rw [sparseHiddenTableCoordinateEquiv_apply]
  simp only [if_pos]
  exact sparseHiddenColumnImageDensity_apply_equiv a ha B (table j)

def sparseHiddenTableCoordinateJointMap
    {n k B T : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) :
    SparseHiddenTable B n × History n k T ->
      SparseHiddenTable B n × History n k T :=
  fun z => (sparseHiddenTableCoordinateEquiv B n a ha j z.1, z.2)

def sparseHiddenTableCoordinateJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (T : Nat) :
    SparseHiddenTable B n × History n k T -> ENNReal :=
  fun z => sparseHiddenTableCoordinateImageDensity a ha j z.1 *
    sparseFamilyLikelihoodProduct F
      (sparseHiddenTableCoordinateEquiv B n a ha j) T z

theorem measurable_sparseHiddenTableCoordinateJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (T : Nat) :
    Measurable (sparseHiddenTableCoordinateJointLikelihood F a ha j T) :=
  ((measurable_sparseHiddenTableCoordinateImageDensity a ha j).comp
      measurable_fst).mul
    (measurable_sparseFamilyLikelihoodProduct F
      (sparseHiddenTableCoordinateEquiv B n a ha j) T)

theorem sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (T : Nat) :
    Measure.map (sparseHiddenTableCoordinateJointMap a ha j)
        (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) =
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T).withDensity
        (sparseHiddenTableCoordinateJointLikelihood F a ha j T) := by
  exact sparseJointLaw_map_eq_withDensity
    (sparseHiddenTableMeasure B n) P F T
    (sparseHiddenTableCoordinateEquiv B n a ha j)
    (sparseHiddenTableCoordinateImageDensity a ha j)
    (measurable_sparseHiddenTableCoordinateImageDensity a ha j)
    (map_sparseHiddenTableCoordinateEquiv_measure a ha j)

theorem sparseHiddenTableCoordinateJointLikelihood_apply_map
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (T : Nat) (table : SparseHiddenTable B n)
    (h : History n k T) :
    sparseHiddenTableCoordinateJointLikelihood F a ha j T
        (sparseHiddenTableCoordinateJointMap a ha j (table, h)) =
      sparseHiddenTableCoordinateJacobianAtSource a j table *
        sparseLikelihoodProduct (F.at table)
          (F.at (sparseHiddenTableCoordinateEquiv B n a ha j table)) T h := by
  unfold sparseHiddenTableCoordinateJointLikelihood
    sparseHiddenTableCoordinateJointMap
  rw [sparseHiddenTableCoordinateImageDensity_apply_equiv,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
  simp

theorem sparseHiddenTableCoordinateJointLikelihood_secondMoment_eq
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j : Fin n) (T : Nat) :
    (∫⁻ z, sparseHiddenTableCoordinateJointLikelihood F a ha j T z ^ 2
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) =
      ∫⁻ z, sparseHiddenTableCoordinateJacobianAtSource a j z.1 *
          sparseLikelihoodProduct (F.at z.1)
            (F.at (sparseHiddenTableCoordinateEquiv B n a ha j z.1)) T z.2
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T := by
  rw [lintegral_likelihood_sq_eq_map_comp
    (sparseJointLaw (sparseHiddenTableMeasure B n) P F T)
    (MeasurableEquiv.prodCongr
      (sparseHiddenTableCoordinateEquiv B n a ha j)
      (MeasurableEquiv.refl (History n k T)))
    (sparseHiddenTableCoordinateJointLikelihood F a ha j T)
    (measurable_sparseHiddenTableCoordinateJointLikelihood F a ha j T)]
  · apply lintegral_congr
    intro z
    exact sparseHiddenTableCoordinateJointLikelihood_apply_map
      F a ha j T z.1 z.2
  · exact sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
      P F a ha j T

theorem lintegral_sparseHiddenTableCoordinateJacobianAtSource
    {B n : Nat} (a : Real) (j : Fin n) :
    (∫⁻ table, sparseHiddenTableCoordinateJacobianAtSource a j table
        ∂sparseHiddenTableMeasure B n) =
      ∫⁻ column, sparseHiddenColumnJacobianAtSource a B column
        ∂sparseHiddenColumnMeasure B := by
  have hmap : Measure.map (Function.eval j)
      (sparseHiddenTableMeasure B n) = sparseHiddenColumnMeasure B := by
    exact (measurePreserving_eval
      (fun _ : Fin n => sparseHiddenColumnMeasure B) j).map_eq
  rw [← hmap]
  exact (lintegral_map
    (μ := sparseHiddenTableMeasure B n)
    (f := sparseHiddenColumnJacobianAtSource a B)
    (g := Function.eval j)
    (measurable_sparseHiddenColumnJacobianAtSource a B)
    (measurable_pi_apply j)).symm

/-- Full-table diagonal likelihood estimate.  It is the concrete analogue of
`eq:lower-likelihood-diagonal`; only the changed column contributes a hidden
Jacobian. -/
theorem lower_likelihood_diagonal_fullTable
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a rho : Real) (ha : |a| <= (1 : Real) / 8)
    (hrho0 : 0 <= rho) (hrho : 8 + 128 * rho <= (10 : Real))
    (j : Fin n) (T : Nat)
    (henergy : forall (table : SparseHiddenTable B n)
      (h : History n k T),
      sparseCumulativeEnergy (F.at table)
          (F.at (sparseHiddenTableCoordinateEquiv B n a ha j table)) T h <=
        a ^ 2 * rho * B) :
    (∫⁻ z, sparseHiddenTableCoordinateJointLikelihood F a ha j T z ^ 2
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) <=
      ENNReal.ofReal (Real.exp (10 * a ^ 2 * B)) := by
  rw [sparseHiddenTableCoordinateJointLikelihood_secondMoment_eq
    P F a ha j T]
  let e := sparseHiddenTableCoordinateEquiv B n a ha j
  let K := sparseFamilyLawKernel P F T
  let J := sparseHiddenTableCoordinateJacobianAtSource (B := B) a j
  let Lsrc : SparseHiddenTable B n × History n k T -> ENNReal :=
    fun z => sparseFamilyLikelihoodProduct F e T (e z.1, z.2)
  have hLsrc : Measurable Lsrc :=
    (measurable_sparseFamilyLikelihoodProduct F e T).comp <|
      (e.measurable.comp measurable_fst).prodMk measurable_snd
  have hJ : Measurable J :=
    measurable_sparseHiddenTableCoordinateJacobianAtSource a j
  have hfun : (fun z : SparseHiddenTable B n × History n k T =>
      J z.1 * sparseLikelihoodProduct (F.at z.1) (F.at (e z.1)) T z.2) =
      fun z => J z.1 * Lsrc z := by
    funext z
    congr 1
    unfold Lsrc
    rw [sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
    simp
  rw [hfun]
  change (∫⁻ z, J z.1 * Lsrc z
      ∂sparseHiddenTableMeasure B n ⊗ₘ K) <= _
  rw [Measure.lintegral_compProd]
  swap
  · exact (hJ.comp measurable_fst).mul hLsrc
  let C : Real := a ^ 2 * rho * B
  let E : ENNReal := ENNReal.ofReal (Real.exp (128 * C))
  calc
    (∫⁻ table, ∫⁻ h, J table * Lsrc (table, h) ∂K table
        ∂sparseHiddenTableMeasure B n) <=
      ∫⁻ table, J table * E ∂sparseHiddenTableMeasure B n := by
        apply lintegral_mono
        intro table
        have hinner : (∫⁻ h, Lsrc (table, h) ∂K table) <= E := by
          have hLU : (fun h => Lsrc (table, h)) =
              sparseLikelihoodProduct (F.at table) (F.at (e table)) T := by
            funext h
            unfold Lsrc
            rw [sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct]
            simp
          rw [hLU, sparseFamilyLawKernel_apply]
          exact lower_likelihood_diagonal_temporal P
            (F.at table) (F.at (e table)) T C (henergy table)
        change (∫⁻ h, J table * Lsrc (table, h) ∂K table) <= J table * E
        rw [lintegral_const_mul (J table)]
        · exact mul_le_mul_right hinner (J table)
        · exact hLsrc.comp (measurable_const.prodMk measurable_id)
    _ = E * (∫⁻ table, J table ∂sparseHiddenTableMeasure B n) := by
      rw [show (fun table => J table * E) = fun table => E * J table by
        funext table; ac_rfl, lintegral_const_mul E hJ]
    _ <= E * ENNReal.ofReal (Real.exp (8 * a ^ 2 * B)) := by
      apply mul_le_mul_right
      rw [lintegral_sparseHiddenTableCoordinateJacobianAtSource a j]
      exact integral_sparseHiddenColumnJacobianAtSource_le
        (ha.trans (by norm_num))
    _ = ENNReal.ofReal (Real.exp ((8 + 128 * rho) * a ^ 2 * B)) := by
      unfold E C
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]
      congr 2
      ring
    _ <= ENNReal.ofReal (Real.exp (10 * a ^ 2 * B)) := by
      apply ENNReal.ofReal_le_ofReal
      apply Real.exp_le_exp.mpr
      have hab : 0 <= a ^ 2 * (B : Real) :=
        mul_nonneg (sq_nonneg a) (Nat.cast_nonneg B)
      nlinarith

#print axioms map_withDensity_measurableEquiv
#print axioms pi_withDensity_eval
#print axioms map_sparseHiddenTableCoordinateEquiv_measure
#print axioms sparseHiddenTableCoordinateJointLaw_map_eq_withDensity
#print axioms lower_likelihood_diagonal_fullTable

end

end MsetsLower.Lower.Sparse
