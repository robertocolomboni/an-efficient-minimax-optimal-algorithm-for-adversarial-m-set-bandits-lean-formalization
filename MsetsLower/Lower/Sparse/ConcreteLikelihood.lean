import MsetsLower.Lower.Sparse.ConcreteDiagonal
import MsetsLower.Lower.Sparse.MixtureTV

/-!
# Concrete full-table likelihood moments

This file instantiates the hidden-coordinate likelihood calculus on the
genuine iid table `SparseHiddenTable B n`.  In particular, the two-coordinate
change below acts on the actual signal columns and its density is obtained
from the literal push-forward of the table law.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped ENNReal ProbabilityTheory BigOperators

noncomputable section

/-! ## Two distinct changes of a full hidden table -/

/-- Change the two indicated full-table columns, first `j` and then `l`. -/
def sparseHiddenTableBothCoordinateEquiv
    (B n : Nat) (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) : SparseHiddenTable B n ≃ᵐ SparseHiddenTable B n :=
  (sparseHiddenTableCoordinateEquiv B n a ha j).trans
    (sparseHiddenTableCoordinateEquiv B n a ha l)

@[simp] theorem sparseHiddenTableBothCoordinateEquiv_apply
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) (table : SparseHiddenTable B n) :
    sparseHiddenTableBothCoordinateEquiv B n a ha j l table =
      sparseHiddenTableCoordinateEquiv B n a ha l
        (sparseHiddenTableCoordinateEquiv B n a ha j table) := rfl

theorem sparseHiddenTableCoordinateEquiv_comm
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (table : SparseHiddenTable B n) :
    sparseHiddenTableCoordinateEquiv B n a ha l
        (sparseHiddenTableCoordinateEquiv B n a ha j table) =
      sparseHiddenTableCoordinateEquiv B n a ha j
        (sparseHiddenTableCoordinateEquiv B n a ha l table) := by
  funext i
  simp only [sparseHiddenTableCoordinateEquiv_apply]
  by_cases hij : i = j
  · subst i
    simp [hjl]
  · by_cases hil : i = l
    · subst i
      simp [hij]
    · simp [hij, hil]

@[simp] theorem sparseHiddenTableCoordinateEquiv_symm_apply_both_left
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (table : SparseHiddenTable B n) :
    (sparseHiddenTableCoordinateEquiv B n a ha j).symm
        (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) =
      sparseHiddenTableCoordinateEquiv B n a ha l table := by
  rw [sparseHiddenTableBothCoordinateEquiv_apply,
    sparseHiddenTableCoordinateEquiv_comm a ha hjl]
  exact (sparseHiddenTableCoordinateEquiv B n a ha j).symm_apply_apply _

@[simp] theorem sparseHiddenTableCoordinateEquiv_symm_apply_both_right
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) (table : SparseHiddenTable B n) :
    (sparseHiddenTableCoordinateEquiv B n a ha l).symm
        (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) =
      sparseHiddenTableCoordinateEquiv B n a ha j table := by
  exact (sparseHiddenTableCoordinateEquiv B n a ha l).symm_apply_apply _

theorem sparseHiddenTableCoordinateImageDensity_other
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (table : SparseHiddenTable B n) :
    sparseHiddenTableCoordinateImageDensity a ha j
        (sparseHiddenTableCoordinateEquiv B n a ha l table) =
      sparseHiddenTableCoordinateImageDensity a ha j table := by
  unfold sparseHiddenTableCoordinateImageDensity
  rw [sparseHiddenTableCoordinateEquiv_apply]
  simp [hjl]

def sparseHiddenTableBothImageDensity
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) (table : SparseHiddenTable B n) : ENNReal :=
  sparseHiddenTableCoordinateImageDensity a ha j table *
    sparseHiddenTableCoordinateImageDensity a ha l table

theorem measurable_sparseHiddenTableBothImageDensity
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) :
    Measurable (sparseHiddenTableBothImageDensity (B := B) a ha j l) :=
  (measurable_sparseHiddenTableCoordinateImageDensity a ha j).mul
    (measurable_sparseHiddenTableCoordinateImageDensity a ha l)

theorem sparseHiddenTableCoordinateJacobianAtSource_other
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (table : SparseHiddenTable B n) :
    sparseHiddenTableCoordinateJacobianAtSource a j
        (sparseHiddenTableCoordinateEquiv B n a ha l table) =
      sparseHiddenTableCoordinateJacobianAtSource a j table := by
  unfold sparseHiddenTableCoordinateJacobianAtSource
  rw [sparseHiddenTableCoordinateEquiv_apply]
  simp [hjl]

@[simp] theorem sparseHiddenTableBothImageDensity_apply_both
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (table : SparseHiddenTable B n) :
    sparseHiddenTableBothImageDensity a ha j l
        (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) =
      sparseHiddenTableCoordinateJacobianAtSource a j table *
        sparseHiddenTableCoordinateJacobianAtSource a l table := by
  unfold sparseHiddenTableBothImageDensity
  rw [sparseHiddenTableBothCoordinateEquiv_apply,
    sparseHiddenTableCoordinateImageDensity_other a ha hjl,
    sparseHiddenTableCoordinateImageDensity_apply_equiv,
    sparseHiddenTableCoordinateImageDensity_apply_equiv,
    sparseHiddenTableCoordinateJacobianAtSource_other a ha hjl.symm]

/-- Exact two-column push-forward density of the genuine iid full table. -/
theorem map_sparseHiddenTableBothCoordinateEquiv_measure
    {B n : Nat} (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) :
    Measure.map (sparseHiddenTableBothCoordinateEquiv B n a ha j l)
        (sparseHiddenTableMeasure B n) =
      (sparseHiddenTableMeasure B n).withDensity
        (sparseHiddenTableBothImageDensity a ha j l) := by
  let mu := sparseHiddenTableMeasure B n
  let eJ := sparseHiddenTableCoordinateEquiv B n a ha j
  let eL := sparseHiddenTableCoordinateEquiv B n a ha l
  let dJ := sparseHiddenTableCoordinateImageDensity (B := B) a ha j
  let dL := sparseHiddenTableCoordinateImageDensity (B := B) a ha l
  have hdJ : Measurable dJ :=
    measurable_sparseHiddenTableCoordinateImageDensity a ha j
  have hdL : Measurable dL :=
    measurable_sparseHiddenTableCoordinateImageDensity a ha l
  have hcomp : dJ ∘ eL.symm = dJ := by
    funext table
    let source := eL.symm table
    have hother := sparseHiddenTableCoordinateImageDensity_other
      a ha hjl source
    change dJ (eL source) = dJ source at hother
    simpa [source] using hother.symm
  change Measure.map (eJ.trans eL) mu =
    mu.withDensity (fun table => dJ table * dL table)
  change Measure.map (eL ∘ eJ) mu =
    mu.withDensity (fun table => dJ table * dL table)
  rw [← Measure.map_map eL.measurable eJ.measurable]
  rw [map_sparseHiddenTableCoordinateEquiv_measure a ha j]
  rw [map_withDensity_measurableEquiv mu eL dJ hdJ]
  rw [hcomp, map_sparseHiddenTableCoordinateEquiv_measure a ha l]
  rw [← withDensity_mul mu hdL hdJ]
  congr 1
  funext table
  exact mul_comm _ _

/-! ## The full-table four-corner likelihood -/

def sparseHiddenTableBothJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) (T : Nat) :
    SparseHiddenTable B n × History n k T -> ENNReal :=
  fun z => sparseHiddenTableBothImageDensity a ha j l z.1 *
    sparseFamilyLikelihoodProduct F
      (sparseHiddenTableBothCoordinateEquiv B n a ha j l) T z

theorem measurable_sparseHiddenTableBothJointLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n) (T : Nat) :
    Measurable (sparseHiddenTableBothJointLikelihood F a ha j l T) :=
  ((measurable_sparseHiddenTableBothImageDensity a ha j l).comp
      measurable_fst).mul
    (measurable_sparseFamilyLikelihoodProduct F
      (sparseHiddenTableBothCoordinateEquiv B n a ha j l) T)

theorem sparseHiddenTableBothJointLaw_map_eq_withDensity
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (T : Nat) :
    Measure.map
        (fun z : SparseHiddenTable B n × History n k T =>
          (sparseHiddenTableBothCoordinateEquiv B n a ha j l z.1, z.2))
        (sparseJointLaw (sparseHiddenTableMeasure B n) P F T) =
      (sparseJointLaw (sparseHiddenTableMeasure B n) P F T).withDensity
        (sparseHiddenTableBothJointLikelihood F a ha j l T) := by
  exact sparseJointLaw_map_eq_withDensity
    (sparseHiddenTableMeasure B n) P F T
    (sparseHiddenTableBothCoordinateEquiv B n a ha j l)
    (sparseHiddenTableBothImageDensity a ha j l)
    (measurable_sparseHiddenTableBothImageDensity a ha j l)
    (map_sparseHiddenTableBothCoordinateEquiv_measure a ha hjl)

/-- The four parameter fields at a full-table base point. -/
def sparseHiddenTableRectangle
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A)
    (table : SparseHiddenTable B n) : SparseAdaptiveRectangle n k where
  base := F.at table
  left := F.at (sparseHiddenTableCoordinateEquiv B n a ha j table)
  right := F.at (sparseHiddenTableCoordinateEquiv B n a ha l table)
  both := F.at (sparseHiddenTableBothCoordinateEquiv B n a ha j l table)
  rectangle := hrectangle table

def sparseHiddenTableCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A)
    (T : Nat) (z : SparseHiddenTable B n × History n k T) : ENNReal :=
  sparseCrossLikelihood
    (sparseHiddenTableRectangle F a ha j l hrectangle z.1) T z.2

private theorem measurable_sparseHiddenTableCrossLogIncrement
    {n k B t : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A) :
    Measurable (fun z : SparseHiddenTable B n × History n k (t + 1) =>
      sparseCrossLogIncrement
        (sparseHiddenTableRectangle F a ha j l hrectangle z.1) t z.2) := by
  let eJ := sparseHiddenTableCoordinateEquiv B n a ha j
  let eL := sparseHiddenTableCoordinateEquiv B n a ha l
  let eB := sparseHiddenTableBothCoordinateEquiv B n a ha j l
  let parameter := fun (e : SparseHiddenTable B n ≃ᵐ SparseHiddenTable B n)
      (z : SparseHiddenTable B n × History n k (t + 1)) =>
    F.value t (e z.1) z.2.1 z.2.2.1
  have hp : forall e : SparseHiddenTable B n ≃ᵐ SparseHiddenTable B n,
      Measurable (parameter e) := by
    intro e
    exact (F.measurable_value t).comp <|
      (((e.measurable.comp measurable_fst).prodMk
        (measurable_fst.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
  let y := fun z : SparseHiddenTable B n × History n k (t + 1) => z.2.2.2
  have hy : Measurable y :=
    measurable_snd.comp (measurable_snd.comp measurable_snd)
  change Measurable (fun z : SparseHiddenTable B n × History n k (t + 1) =>
    if y z ∈ Icc (-1 / 2 : Real) (1 / 2 : Real) then
      feedbackLogJacobian (parameter eB z) (y z) -
        feedbackLogJacobian (parameter eL z) (y z) -
        feedbackLogJacobian (parameter eJ z) (y z) +
        feedbackLogJacobian (F.value t z.1 z.2.1 z.2.2.1) (y z)
    else 0)
  apply Measurable.ite
  · exact hy measurableSet_Icc
  · have hbase : Measurable (fun z :
        SparseHiddenTable B n × History n k (t + 1) =>
      F.value t z.1 z.2.1 z.2.2.1) :=
      (F.measurable_value t).comp <|
        ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
          (measurable_fst.comp (measurable_snd.comp measurable_snd)))
    exact (((measurable_feedbackLogJacobian_uncurry.comp
          ((hp eB).prodMk hy)).sub
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp eL).prodMk hy))).sub
        (measurable_feedbackLogJacobian_uncurry.comp
          ((hp eJ).prodMk hy))).add
        (measurable_feedbackLogJacobian_uncurry.comp
          (hbase.prodMk hy))
  · exact measurable_const

theorem measurable_sparseHiddenTableCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A) :
    forall T, Measurable
      (sparseHiddenTableCrossLikelihood F a ha j l hrectangle T) := by
  intro T
  have hlog : Measurable (fun z : SparseHiddenTable B n × History n k T =>
    sparseCrossLog
      (sparseHiddenTableRectangle F a ha j l hrectangle z.1) T z.2) := by
    induction T with
    | zero => exact measurable_const
    | succ t ih =>
        change Measurable (fun z :
            SparseHiddenTable B n × History n k (t + 1) =>
          sparseCrossLog
              (sparseHiddenTableRectangle F a ha j l hrectangle z.1) t z.2.1 +
            sparseCrossLogIncrement
              (sparseHiddenTableRectangle F a ha j l hrectangle z.1) t z.2)
        exact (ih.comp
          (measurable_fst.prodMk
            (measurable_fst.comp measurable_snd))).add
          (measurable_sparseHiddenTableCrossLogIncrement
            F a ha j l hrectangle)
  exact hlog.exp.ennreal_ofReal

@[simp] theorem sparseHiddenTableCoordinateJointLikelihood_apply_both_left
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (T : Nat)
    (table : SparseHiddenTable B n) (h : History n k T) :
    sparseHiddenTableCoordinateJointLikelihood F a ha j T
        (sparseHiddenTableBothCoordinateEquiv B n a ha j l table, h) =
      sparseHiddenTableCoordinateJacobianAtSource a j table *
      sparseLikelihoodProduct
          (F.at (sparseHiddenTableCoordinateEquiv B n a ha l table))
          (F.at (sparseHiddenTableBothCoordinateEquiv B n a ha j l table)) T h := by
  have hsource :
      (sparseHiddenTableCoordinateEquiv B n a ha j).symm
          (sparseHiddenTableCoordinateEquiv B n a ha l
            (sparseHiddenTableCoordinateEquiv B n a ha j table)) =
        sparseHiddenTableCoordinateEquiv B n a ha l table := by
    rw [sparseHiddenTableCoordinateEquiv_comm a ha hjl]
    exact (sparseHiddenTableCoordinateEquiv B n a ha j).symm_apply_apply _
  unfold sparseHiddenTableCoordinateJointLikelihood
  rw [sparseHiddenTableBothCoordinateEquiv_apply,
    sparseHiddenTableCoordinateImageDensity_other a ha hjl,
    sparseHiddenTableCoordinateImageDensity_apply_equiv,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct,
    hsource]

@[simp] theorem sparseHiddenTableCoordinateJointLikelihood_apply_both_right
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (T : Nat)
    (table : SparseHiddenTable B n) (h : History n k T) :
    sparseHiddenTableCoordinateJointLikelihood F a ha l T
        (sparseHiddenTableBothCoordinateEquiv B n a ha j l table, h) =
      sparseHiddenTableCoordinateJacobianAtSource a l table *
      sparseLikelihoodProduct
          (F.at (sparseHiddenTableCoordinateEquiv B n a ha j table))
          (F.at (sparseHiddenTableBothCoordinateEquiv B n a ha j l table)) T h := by
  have hsource :
      (sparseHiddenTableCoordinateEquiv B n a ha l).symm
          (sparseHiddenTableCoordinateEquiv B n a ha l
            (sparseHiddenTableCoordinateEquiv B n a ha j table)) =
        sparseHiddenTableCoordinateEquiv B n a ha j table :=
    (sparseHiddenTableCoordinateEquiv B n a ha l).symm_apply_apply _
  unfold sparseHiddenTableCoordinateJointLikelihood
  rw [sparseHiddenTableBothCoordinateEquiv_apply,
    sparseHiddenTableCoordinateImageDensity_apply_equiv,
    sparseHiddenTableCoordinateJacobianAtSource_other a ha hjl.symm,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct,
    hsource]

@[simp] theorem sparseHiddenTableBothJointLikelihood_apply_both
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l) (T : Nat)
    (table : SparseHiddenTable B n) (h : History n k T) :
    sparseHiddenTableBothJointLikelihood F a ha j l T
        (sparseHiddenTableBothCoordinateEquiv B n a ha j l table, h) =
      (sparseHiddenTableCoordinateJacobianAtSource a j table *
          sparseHiddenTableCoordinateJacobianAtSource a l table) *
        sparseLikelihoodProduct (F.at table)
          (F.at (sparseHiddenTableBothCoordinateEquiv B n a ha j l table)) T h := by
  unfold sparseHiddenTableBothJointLikelihood
  rw [sparseHiddenTableBothImageDensity_apply_both a ha hjl,
    sparseFamilyLikelihoodProduct_eq_sparseLikelihoodProduct,
    (sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm_apply_apply]

theorem sparseHiddenTableJointLikelihood_cross_balance_apply_both
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A)
    (T : Nat) (table : SparseHiddenTable B n) (h : History n k T)
    (hsupp : sparseHistoryInFeedbackSupport T h) :
    sparseHiddenTableCoordinateJointLikelihood F a ha j T
          (sparseHiddenTableBothCoordinateEquiv B n a ha j l table, h) *
        sparseHiddenTableCoordinateJointLikelihood F a ha l T
          (sparseHiddenTableBothCoordinateEquiv B n a ha j l table, h) =
      sparseHiddenTableBothJointLikelihood F a ha j l T
          (sparseHiddenTableBothCoordinateEquiv B n a ha j l table, h) *
        sparseHiddenTableCrossLikelihood F a ha j l hrectangle T (table, h) := by
  let R := sparseHiddenTableRectangle F a ha j l hrectangle table
  have hbalance := sparseLikelihoodProduct_cross_balance R T h hsupp
  rw [sparseHiddenTableCoordinateJointLikelihood_apply_both_left
      F a ha hjl,
    sparseHiddenTableCoordinateJointLikelihood_apply_both_right
      F a ha hjl,
    sparseHiddenTableBothJointLikelihood_apply_both F a ha hjl]
  change
    (sparseHiddenTableCoordinateJacobianAtSource a j table *
          sparseLikelihoodProduct R.right R.both T h) *
        (sparseHiddenTableCoordinateJacobianAtSource a l table *
          sparseLikelihoodProduct R.left R.both T h) =
      ((sparseHiddenTableCoordinateJacobianAtSource a j table *
            sparseHiddenTableCoordinateJacobianAtSource a l table) *
          sparseLikelihoodProduct R.base R.both T h) *
        sparseCrossLikelihood R T h
  calc
    (sparseHiddenTableCoordinateJacobianAtSource a j table *
          sparseLikelihoodProduct R.right R.both T h) *
        (sparseHiddenTableCoordinateJacobianAtSource a l table *
          sparseLikelihoodProduct R.left R.both T h) =
      (sparseHiddenTableCoordinateJacobianAtSource a j table *
          sparseHiddenTableCoordinateJacobianAtSource a l table) *
        (sparseLikelihoodProduct R.right R.both T h *
          sparseLikelihoodProduct R.left R.both T h) := by ac_rfl
    _ = (sparseHiddenTableCoordinateJacobianAtSource a j table *
          sparseHiddenTableCoordinateJacobianAtSource a l table) *
        (sparseLikelihoodProduct R.base R.both T h *
          sparseCrossLikelihood R T h) := by rw [hbalance]
    _ = _ := by ac_rfl

def sparseHiddenTableTargetCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A)
    (T : Nat) (z : SparseHiddenTable B n × History n k T) : ENNReal :=
  sparseHiddenTableCrossLikelihood F a ha j l hrectangle T
    ((sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm z.1, z.2)

theorem measurable_sparseHiddenTableTargetCrossLikelihood
    {n k B : Nat}
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    (j l : Fin n)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A)
    (T : Nat) :
    Measurable
      (sparseHiddenTableTargetCrossLikelihood F a ha j l hrectangle T) :=
  (measurable_sparseHiddenTableCrossLikelihood F a ha j l hrectangle T).comp <|
    (((sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm.measurable.comp
      measurable_fst).prodMk measurable_snd)

/-- Exact full-table change-of-variables identity for the cross moment. -/
theorem sparseHiddenTableJointLikelihood_cross_integral_eq
    {n k B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a : Real) (ha : |a| <= (1 : Real) / 8)
    {j l : Fin n} (hjl : j ≠ l)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha j l table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha j table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha l table) h A)
    (T : Nat) :
    (∫⁻ z, sparseHiddenTableCoordinateJointLikelihood F a ha j T z *
          sparseHiddenTableCoordinateJointLikelihood F a ha l T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) =
      ∫⁻ z, sparseHiddenTableCrossLikelihood F a ha j l hrectangle T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T := by
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  let e : SparseHiddenTable B n × History n k T ->
      SparseHiddenTable B n × History n k T :=
    fun z => (sparseHiddenTableBothCoordinateEquiv B n a ha j l z.1, z.2)
  have he : Measurable e :=
    ((sparseHiddenTableBothCoordinateEquiv B n a ha j l).measurable.comp
      measurable_fst).prodMk measurable_snd
  let target := sparseHiddenTableTargetCrossLikelihood
    F a ha j l hrectangle T
  let both := sparseHiddenTableBothJointLikelihood F a ha j l T
  have htarget : Measurable target :=
    measurable_sparseHiddenTableTargetCrossLikelihood
      F a ha j l hrectangle T
  have hboth : Measurable both :=
    measurable_sparseHiddenTableBothJointLikelihood F a ha j l T
  have hmap : Measure.map e mu = mu.withDensity both := by
    exact sparseHiddenTableBothJointLaw_map_eq_withDensity
      P F a ha hjl T
  have hbalance : ∀ᵐ z ∂mu,
      sparseHiddenTableCoordinateJointLikelihood F a ha j T z *
          sparseHiddenTableCoordinateJointLikelihood F a ha l T z =
        both z * target z := by
    filter_upwards [ae_sparseJointLaw_history_support
      (sparseHiddenTableMeasure B n) P F T] with z hz
    have h := sparseHiddenTableJointLikelihood_cross_balance_apply_both
      F a ha hjl hrectangle T
      ((sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm z.1) z.2 hz
    change sparseHiddenTableCoordinateJointLikelihood F a ha j T z *
          sparseHiddenTableCoordinateJointLikelihood F a ha l T z =
      sparseHiddenTableBothJointLikelihood F a ha j l T z *
        sparseHiddenTableCrossLikelihood F a ha j l hrectangle T
          ((sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm z.1, z.2)
    simpa using h
  calc
    (∫⁻ z, sparseHiddenTableCoordinateJointLikelihood F a ha j T z *
          sparseHiddenTableCoordinateJointLikelihood F a ha l T z ∂mu) =
        ∫⁻ z, both z * target z ∂mu := lintegral_congr_ae hbalance
    _ = ∫⁻ z, target z ∂mu.withDensity both :=
      (lintegral_withDensity_eq_lintegral_mul mu hboth htarget).symm
    _ = ∫⁻ z, target z ∂Measure.map e mu := by rw [hmap]
    _ = ∫⁻ z, target (e z) ∂mu := lintegral_map htarget he
    _ = ∫⁻ z, sparseHiddenTableCrossLikelihood
        F a ha j l hrectangle T z ∂mu := by
      apply lintegral_congr
      intro z
      change sparseHiddenTableCrossLikelihood F a ha j l hrectangle T
          ((sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm
            (sparseHiddenTableBothCoordinateEquiv B n a ha j l z.1), z.2) =
        sparseHiddenTableCrossLikelihood F a ha j l hrectangle T z
      rw [(sparseHiddenTableBothCoordinateEquiv B n a ha j l).symm_apply_apply]

/-- Quantitative cross bound on the genuine full table.  The assumptions are
the two pathwise estimates, while all RN and change-of-variables statements
are proved above. -/
theorem lower_likelihood_cross_fullTable
    {n n' k q c0 B : Nat} (P : Policy n k)
    (F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k)
    (a eta : Real) (ha : |a| <= (1 : Real) / 8)
    (hn' : n' <= n) {j l : Fin n'} (hjl : j ≠ l)
    (hrectangle : forall table t h A,
      F.value t (sparseHiddenTableBothCoordinateEquiv B n a ha
          (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l) table) h A +
          F.value t table h A =
        F.value t (sparseHiddenTableCoordinateEquiv B n a ha
          (sparseSignalCoordinate hn' j) table) h A +
          F.value t (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' l) table) h A)
    (T : Nat) (C : Real)
    (henergyN : forall table (h : History n k T),
      sparseCrossEnergy
          (sparseHiddenTableRectangle F a ha
            (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
            hrectangle table) T h <=
        a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h)
    (hbudget : forall h : History n k T,
      a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h <= C) :
    (∫⁻ z, sparseHiddenTableCoordinateJointLikelihood F a ha
            (sparseSignalCoordinate hn' j) T z *
          sparseHiddenTableCoordinateJointLikelihood F a ha
            (sparseSignalCoordinate hn' l) T z
        ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) <=
      1 + ENNReal.ofReal
          (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C)) *
        (∫⁻ z, ENNReal.ofReal (sparseN hn' q c0 j l T z.2)
          ∂sparseJointLaw (sparseHiddenTableMeasure B n) P F T) := by
  have hcoord : sparseSignalCoordinate hn' j ≠
      sparseSignalCoordinate hn' l := by
    exact fun h => hjl ((sparseSignalCoordinate_injective hn') h)
  rw [sparseHiddenTableJointLikelihood_cross_integral_eq
    P F a ha hcoord hrectangle T]
  let mu := sparseJointLaw (sparseHiddenTableMeasure B n) P F T
  let c : Real := a ^ 2 * eta ^ 2
  let K : ENNReal := ENNReal.ofReal (128 * Real.exp (128 * C))
  let D : ENNReal := ENNReal.ofReal
    (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C))
  have hc : 0 <= c := mul_nonneg (sq_nonneg a) (sq_nonneg eta)
  have hfactor : K * ENNReal.ofReal c = D := by
    change ENNReal.ofReal (128 * Real.exp (128 * C)) *
        ENNReal.ofReal c =
      ENNReal.ofReal (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C))
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (by norm_num) (Real.exp_pos _).le)]
    apply congrArg ENNReal.ofReal
    dsimp [c]
    ring
  have hpoint : forall z : SparseHiddenTable B n × History n k T,
      sparseHiddenTableCrossLikelihood F a ha
          (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
          hrectangle T z <=
        1 + D * ENNReal.ofReal (sparseN hn' q c0 j l T z.2) := by
    intro z
    let R := sparseHiddenTableRectangle F a ha
      (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
      hrectangle z.1
    have hEC : forall h : History n k T, sparseCrossEnergy R T h <= C := by
      intro h
      exact (henergyN z.1 h).trans (hbudget h)
    have hbase := sparseCrossLikelihood_le R T C hEC z.2
    have hEN : ENNReal.ofReal (sparseCrossEnergy R T z.2) <=
        ENNReal.ofReal c *
          ENNReal.ofReal (sparseN hn' q c0 j l T z.2) := by
      calc
        ENNReal.ofReal (sparseCrossEnergy R T z.2) <=
            ENNReal.ofReal
              (c * sparseN hn' q c0 j l T z.2) :=
          ENNReal.ofReal_le_ofReal (henergyN z.1 z.2)
        _ = ENNReal.ofReal c *
            ENNReal.ofReal (sparseN hn' q c0 j l T z.2) := by
          rw [ENNReal.ofReal_mul hc]
    change sparseCrossLikelihood R T z.2 <= _
    calc
      sparseCrossLikelihood R T z.2 <=
          1 + K * ENNReal.ofReal (sparseCrossEnergy R T z.2) := hbase
      _ <= 1 + K * (ENNReal.ofReal c *
          ENNReal.ofReal (sparseN hn' q c0 j l T z.2)) :=
        add_le_add le_rfl (mul_le_mul_right hEN K)
      _ = 1 + D * ENNReal.ofReal
          (sparseN hn' q c0 j l T z.2) := by
        rw [← mul_assoc, hfactor]
  have hNmeas : Measurable (fun z :
      SparseHiddenTable B n × History n k T =>
      ENNReal.ofReal (sparseN hn' q c0 j l T z.2)) :=
    (Measurable.ennreal_ofReal (measurable_sparseN hn' j l T)).comp
      measurable_snd
  letI : IsProbabilityMeasure mu := by
    dsimp [mu, sparseJointLaw]
    infer_instance
  calc
    (∫⁻ z, sparseHiddenTableCrossLikelihood F a ha
          (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
          hrectangle T z ∂mu) <=
        ∫⁻ z, (1 + D *
          ENNReal.ofReal (sparseN hn' q c0 j l T z.2)) ∂mu :=
      lintegral_mono hpoint
    _ = (∫⁻ _z : SparseHiddenTable B n × History n k T,
          (1 : ENNReal) ∂mu) +
        ∫⁻ z, D * ENNReal.ofReal
          (sparseN hn' q c0 j l T z.2) ∂mu := by
      rw [lintegral_add_left]
      exact measurable_const
    _ = 1 + D *
        (∫⁻ z, ENNReal.ofReal (sparseN hn' q c0 j l T z.2) ∂mu) := by
      rw [lintegral_const_mul D hNmeas]
      simp
    _ = 1 + ENNReal.ofReal
          (128 * a ^ 2 * eta ^ 2 * Real.exp (128 * C)) *
        (∫⁻ z, ENNReal.ofReal (sparseN hn' q c0 j l T z.2) ∂mu) := rfl

/-! ## Instantiation on the manuscript's parameter family -/

theorem sparseTransformTableCoordinate_comm
    {n n' : Nat} (a : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real) {j l : Fin n'} (hjl : j ≠ l) :
    sparseTransformTableCoordinate a hn'
        (sparseTransformTableCoordinate a hn' U j) l =
      sparseTransformTableCoordinate a hn'
        (sparseTransformTableCoordinate a hn' U l) j := by
  funext b i
  unfold sparseTransformTableCoordinate
  have hcoord : sparseSignalCoordinate hn' j ≠
      sparseSignalCoordinate hn' l := by
    exact fun h => hjl ((sparseSignalCoordinate_injective hn') h)
  by_cases hij : i = sparseSignalCoordinate hn' j
  · subst i
    simp [hcoord]
  · by_cases hil : i = sparseSignalCoordinate hn' l
    · subst i
      simp [hij]
    · simp [hij, hil]

/-- A round parameter reads only the current row `t/q`. -/
theorem sparseFeedbackParameter_congr_currentBlock_fullTable
    {n k n' q c0 : Nat} (eta : Real)
    {U V : Nat -> Fin n -> Real} (t : Nat)
    (hUV : forall i, U (t / q) i = V (t / q) i)
    (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0 U t h A =
      sparseFeedbackParameter eta n' q c0 V t h A := by
  unfold sparseFeedbackParameter sparseActionScore actionLoss
  congr 2
  funext i
  by_cases hmem : i ∈ A.1 <;>
    by_cases hi : i.1 < n' <;>
      simp [hmem, sparseSignalWeight, hi, hUV]

theorem sparseFullTable_block_index_lt
    {q B t : Nat} (ht : t < q * B) : t / q < B := by
  have hq : 0 < q := by
    by_contra hq0
    have : q = 0 := Nat.eq_zero_of_not_pos hq0
    simp [this] at ht
  exact (Nat.div_lt_iff_lt_mul hq).2
    (by simpa [Nat.mul_comm] using ht)

theorem sparseFeedbackParameter_coordinateEquiv_of_block
    {B n n' k q c0 : Nat} (eta a : Real)
    (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    (j : Fin n') (table : SparseHiddenTable B n) (t : Nat)
    (hb : t / q < B) (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table)) t h A =
      sparseFeedbackParameter eta n' q c0
        (sparseTransformTableCoordinate a hn'
          (sparseHiddenTableU table) j) t h A := by
  apply sparseFeedbackParameter_congr_currentBlock_fullTable eta t
  intro i
  exact sparseHiddenTableU_coordinateEquiv_of_lt
    a ha hn' j table hb i

theorem sparseTransformTableCoordinate_congr_at
    {n n' : Nat} (a : Real) (hn' : n' <= n)
    {U V : Nat -> Fin n -> Real} (j : Fin n') (b : Nat) (i : Fin n)
    (hUV : U b i = V b i) :
    sparseTransformTableCoordinate a hn' U j b i =
      sparseTransformTableCoordinate a hn' V j b i := by
  unfold sparseTransformTableCoordinate
  split_ifs <;> rw [hUV]

theorem sparseFeedbackParameter_bothCoordinateEquiv_of_block
    {B n n' k q c0 : Nat} (eta a : Real)
    (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    (j l : Fin n') (table : SparseHiddenTable B n) (t : Nat)
    (hb : t / q < B) (h : History n k t) (A : MSetAction n k) :
    sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableBothCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
            table)) t h A =
      sparseFeedbackParameter eta n' q c0
        (sparseTransformTableCoordinate a hn'
          (sparseTransformTableCoordinate a hn'
            (sparseHiddenTableU table) j) l) t h A := by
  apply sparseFeedbackParameter_congr_currentBlock_fullTable eta t
  intro i
  rw [sparseHiddenTableBothCoordinateEquiv_apply]
  calc
    sparseHiddenTableU
        (sparseHiddenTableCoordinateEquiv B n a ha
          (sparseSignalCoordinate hn' l)
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table)) (t / q) i =
      sparseTransformTableCoordinate a hn'
        (sparseHiddenTableU
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table)) l (t / q) i :=
        sparseHiddenTableU_coordinateEquiv_of_lt
          a ha hn' l _ hb i
    _ = sparseTransformTableCoordinate a hn'
        (sparseTransformTableCoordinate a hn'
          (sparseHiddenTableU table) j) l (t / q) i := by
      apply sparseTransformTableCoordinate_congr_at a hn' l (t / q) i
      exact sparseHiddenTableU_coordinateEquiv_of_lt
        a ha hn' j table hb i

theorem sparseHiddenTableParameterFamily_rectangle
    {n n' k q c0 B : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    {j l : Fin n'} (hjl : j ≠ l) :
    forall table t h A,
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).value t
          (sparseHiddenTableBothCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
            table) h A +
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).value t
          table h A =
      (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).value t
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table) h A +
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).value t
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' l) table) h A := by
  intro table t h A
  change
    sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableBothCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
            table)) t h A +
      sparseFeedbackParameter eta n' q c0 (sparseHiddenTableU table) t h A =
    sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table)) t h A +
      sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' l) table)) t h A
  by_cases hb : t / q < B
  · rw [sparseFeedbackParameter_bothCoordinateEquiv_of_block
        eta a ha hn' j l table t hb,
      sparseFeedbackParameter_coordinateEquiv_of_block
        eta a ha hn' j table t hb,
      sparseFeedbackParameter_coordinateEquiv_of_block
        eta a ha hn' l table t hb,
      sparseTransformTableCoordinate_comm a hn'
        (sparseHiddenTableU table) hjl]
    exact sparseFeedbackParameter_transform_rectangle
      a eta hn' (sparseHiddenTableU table) hjl t h A
  · have hread : forall (changed : SparseHiddenTable B n) i,
        sparseHiddenTableU changed (t / q) i =
          sparseHiddenTableU table (t / q) i := by
      intro changed i
      simp [sparseHiddenTableU, sparseHiddenColumnAt, hb]
    have hboth := sparseFeedbackParameter_congr_currentBlock_fullTable
      (n' := n') (q := q) (c0 := c0) eta t
      (hread (sparseHiddenTableBothCoordinateEquiv B n a ha
        (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
        table)) h A
    have hleft := sparseFeedbackParameter_congr_currentBlock_fullTable
      (n' := n') (q := q) (c0 := c0) eta t
      (hread (sparseHiddenTableCoordinateEquiv B n a ha
        (sparseSignalCoordinate hn' j) table)) h A
    have hright := sparseFeedbackParameter_congr_currentBlock_fullTable
      (n' := n') (q := q) (c0 := c0) eta t
      (hread (sparseHiddenTableCoordinateEquiv B n a ha
        (sparseSignalCoordinate hn' l) table)) h A
    rw [hboth, hleft, hright]

/-- The overlap-energy estimate with perturbation identities required only
before a fixed terminal time. -/
theorem sparseCrossEnergy_le_a_eta_sq_mul_sparseN_before
    {n n' k q c0 Tmax : Nat} (hk : 1 <= k)
    (a eta : Real) (hn' : n' <= n)
    (U : Nat -> Fin n -> Real)
    (hU : forall b i, U b i ∈ Icc (-1 : Real) 1)
    (j l : Fin n') (R : SparseAdaptiveRectangle n k)
    (hleft : forall t h A, t < Tmax ->
      R.left.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U j t h A)
    (hright : forall t h A, t < Tmax ->
      R.right.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U l t h A) :
    forall T (h : History n k T), T <= Tmax ->
      sparseCrossEnergy R T h <=
        a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h := by
  intro T h hT
  have hscaled : sparseCrossEnergy R T h <=
      (a * eta / (k : Real)) ^ 2 *
        sparsePairPullSum hn' q c0 j l T h := by
    induction T with
    | zero => norm_num [sparseCrossEnergy]
    | succ t ih =>
        have ht : t < Tmax := by omega
        have hround : sparseCrossRoundEnergy R t (h.1, h.2.1) <=
            (a * eta / (k : Real)) ^ 2 *
              (sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
                sparsePullIndicator hn' q c0 l t h.1 h.2.1) := by
          rw [sparseCrossRoundEnergy,
            hleft t h.1 h.2.1 ht, hright t h.1 h.2.1 ht]
          exact abs_sparseCoordinatePerturbation_mul_le
            a eta hn' U hU j l h.1 h.2.1
        rw [sparseCrossEnergy, sparsePairPullSum_succ]
        calc
          _ <= (a * eta / (k : Real)) ^ 2 *
                sparsePairPullSum hn' q c0 j l t h.1 +
              (a * eta / (k : Real)) ^ 2 *
                (sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
                  sparsePullIndicator hn' q c0 l t h.1 h.2.1) :=
            add_le_add (ih h.1 (by omega)) hround
          _ = _ := by ring
  have hk0 : (k : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  calc
    sparseCrossEnergy R T h <=
        (a * eta / (k : Real)) ^ 2 *
          sparsePairPullSum hn' q c0 j l T h := hscaled
    _ = a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h := by
      unfold sparseN
      field_simp [hk0]

theorem sparseHiddenTableParameterFamily_crossEnergy_le
    {n n' k q c0 B : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    {j l : Fin n'} (hjl : j ≠ l)
    (table : SparseHiddenTable B n) (T : Nat) (h : History n k T)
    (hT : T <= q * B) :
    sparseCrossEnergy
        (sparseHiddenTableRectangle
          (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B)
          a ha (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l)
          (sparseHiddenTableParameterFamily_rectangle
            hk eta heta0 heta a ha hn' hjl) table) T h <=
      a ^ 2 * eta ^ 2 * sparseN hn' q c0 j l T h := by
  let F : SparseAdaptiveParameterFamily (SparseHiddenTable B n) n k :=
    sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B
  let rect := sparseHiddenTableParameterFamily_rectangle
    (q := q) (c0 := c0) (B := B)
    hk eta heta0 heta a ha hn' hjl
  let R := sparseHiddenTableRectangle F a ha
    (sparseSignalCoordinate hn' j) (sparseSignalCoordinate hn' l) rect table
  let U := sparseHiddenTableU table
  have hU : forall b i, U b i ∈ Icc (-1 : Real) 1 := by
    intro b i
    exact (abs_le).1 (sparseHiddenTableU_abs_le_one table b i)
  have hleft : forall t h A, t < T ->
      R.left.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U j t h A := by
    intro t h A ht
    have hb : t / q < B :=
      sparseFullTable_block_index_lt (lt_of_lt_of_le ht hT)
    change sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU
            (sparseHiddenTableCoordinateEquiv B n a ha
              (sparseSignalCoordinate hn' j) table)) t h A -
        sparseFeedbackParameter eta n' q c0 (sparseHiddenTableU table) t h A = _
    rw [sparseFeedbackParameter_coordinateEquiv_of_block
      eta a ha hn' j table t hb]
    exact sparseFeedbackParameter_transform_coordinate_sub
      a eta hn' U j t h A
  have hright : forall t h A, t < T ->
      R.right.value t h A - R.base.value t h A =
        sparseCoordinatePerturbation a eta hn' q c0 U l t h A := by
    intro t h A ht
    have hb : t / q < B :=
      sparseFullTable_block_index_lt (lt_of_lt_of_le ht hT)
    change sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU
            (sparseHiddenTableCoordinateEquiv B n a ha
              (sparseSignalCoordinate hn' l) table)) t h A -
        sparseFeedbackParameter eta n' q c0 (sparseHiddenTableU table) t h A = _
    rw [sparseFeedbackParameter_coordinateEquiv_of_block
      eta a ha hn' l table t hb]
    exact sparseFeedbackParameter_transform_coordinate_sub
      a eta hn' U l t h A
  exact sparseCrossEnergy_le_a_eta_sq_mul_sparseN_before
    hk a eta hn' U hU j l R hleft hright T h le_rfl

theorem sparsePairPullSum_le_sparseObservablePullCount
    {n n' k q c0 : Nat} (hn' : n' <= n) (j l : Fin n') :
    forall T (h : History n k T),
      sparsePairPullSum hn' q c0 j l T h <=
        sparseObservablePullCount hn' q c0 j T h := by
  intro T
  induction T with
  | zero => intro h; rfl
  | succ t ih =>
      intro h
      rw [sparsePairPullSum_succ, sparseObservablePullCount_succ]
      have hj := sparsePullIndicator_mem_Icc
        (q := q) (c0 := c0) hn' j h.1 h.2.1
      have hl := sparsePullIndicator_mem_Icc
        (q := q) (c0 := c0) hn' l h.1 h.2.1
      have hround :
          sparsePullIndicator hn' q c0 j t h.1 h.2.1 *
              sparsePullIndicator hn' q c0 l t h.1 h.2.1 <=
            sparsePullIndicator hn' q c0 j t h.1 h.2.1 := by
        simpa using mul_le_mul_of_nonneg_left hl.2 hj.1
      exact add_le_add (ih h.1) hround

theorem sparseN_le_blockBudget_div
    {n n' k q c0 B : Nat} (hn' : n' <= n) (j l : Fin n')
    (h : History n k (q * B)) :
    sparseN hn' q c0 j l (q * B) h <=
      ((B * c0 : Nat) : Real) / (k : Real) ^ 2 := by
  unfold sparseN
  calc
    sparsePairPullSum hn' q c0 j l (q * B) h / (k : Real) ^ 2 <=
        sparseObservablePullCount hn' q c0 j (q * B) h /
          (k : Real) ^ 2 :=
      div_le_div_of_nonneg_right
        (sparsePairPullSum_le_sparseObservablePullCount hn' j l _ h)
        (sq_nonneg _)
    _ <= ((B * c0 : Nat) : Real) / (k : Real) ^ 2 :=
      div_le_div_of_nonneg_right
        (sparseObservablePullCount_le_blockBudget hn' j h)
        (sq_nonneg _)

theorem sparseConcrete_cross_budget
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (j l : Fin (sparseSignalCount n k))
    (h : History n k (sparseT0 n k T)) :
    sparseA ^ 2 * sparseEta n k T ^ 2 *
        sparseN (sparseSignalCount_le n k) (sparseQ n k T)
          (sparseC0 n k T) j l (sparseT0 n k T) h <=
      sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) := by
  have hN : sparseN (sparseSignalCount_le n k) (sparseQ n k T)
        (sparseC0 n k T) j l (sparseT0 n k T) h <=
      (((sparseBlockCount n k * sparseC0 n k T : Nat) : Real)) /
        (k : Real) ^ 2 := by
    simpa [sparseT0] using
      (sparseN_le_blockBudget_div
        (k := k) (q := sparseQ n k T) (c0 := sparseC0 n k T)
        (B := sparseBlockCount n k)
        (sparseSignalCount_le n k) j l
        (by simpa [sparseT0] using h))
  have hk0 : (k : Real) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hk)
  calc
    sparseA ^ 2 * sparseEta n k T ^ 2 *
        sparseN (sparseSignalCount_le n k) (sparseQ n k T)
          (sparseC0 n k T) j l (sparseT0 n k T) h <=
      sparseA ^ 2 * sparseEta n k T ^ 2 *
        ((((sparseBlockCount n k * sparseC0 n k T : Nat) : Real)) /
          (k : Real) ^ 2) :=
        mul_le_mul_of_nonneg_left hN
          (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = (sparseA * sparseEta n k T / (k : Real)) ^ 2 *
        (((sparseBlockCount n k * sparseC0 n k T : Nat) : Real)) := by
      field_simp [hk0]
    _ = sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) :=
      sparseEta_blockBudget_identity hk hr hT

def sparseConcreteJointLaw
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) :
    Measure (SparseHiddenTable (sparseBlockCount n k) n ×
      History n k (sparseT0 n k T)) :=
  sparseJointLaw (sparseHiddenTableMeasure (sparseBlockCount n k) n) P
    (sparseConcreteHiddenTableParameterFamily hk hr hT)
    (sparseT0 n k T)

def sparseConcreteCoordinateLikelihood
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (j : Fin (sparseSignalCount n k)) :
    SparseHiddenTable (sparseBlockCount n k) n ×
        History n k (sparseT0 n k T) -> ENNReal :=
  sparseHiddenTableCoordinateJointLikelihood
    (sparseConcreteHiddenTableParameterFamily hk hr hT)
    sparseA (by norm_num [sparseA])
    (sparseSignalCoordinate (sparseSignalCount_le n k) j)
    (sparseT0 n k T)

def sparseConcreteHistoryLaw
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) : Measure (History n k (sparseT0 n k T)) :=
  Measure.map Prod.snd (sparseConcreteJointLaw hk hr hT P)

theorem measurable_sparseConcreteCoordinateLikelihood
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (j : Fin (sparseSignalCount n k)) :
    Measurable (sparseConcreteCoordinateLikelihood hk hr hT j) :=
  measurable_sparseHiddenTableCoordinateJointLikelihood
    (sparseConcreteHiddenTableParameterFamily hk hr hT)
    sparseA (by norm_num [sparseA])
    (sparseSignalCoordinate (sparseSignalCount_le n k) j)
    (sparseT0 n k T)

/-- The manuscript's off-diagonal likelihood moment on the genuine hidden
table, with the literal constant and no remaining RN or energy premise. -/
theorem lower_likelihood_cross_concreteFullTable
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) {j l : Fin (sparseSignalCount n k)} (hjl : j ≠ l) :
    (∫⁻ z,
        sparseHiddenTableCoordinateJointLikelihood
            (sparseConcreteHiddenTableParameterFamily hk hr hT)
            sparseA (by norm_num [sparseA])
            (sparseSignalCoordinate (sparseSignalCount_le n k) j)
            (sparseT0 n k T) z *
          sparseHiddenTableCoordinateJointLikelihood
            (sparseConcreteHiddenTableParameterFamily hk hr hT)
            sparseA (by norm_num [sparseA])
            (sparseSignalCoordinate (sparseSignalCount_le n k) l)
            (sparseT0 n k T) z
      ∂sparseJointLaw
        (sparseHiddenTableMeasure (sparseBlockCount n k) n) P
        (sparseConcreteHiddenTableParameterFamily hk hr hT)
        (sparseT0 n k T)) <=
      1 + ENNReal.ofReal
          (128 * sparseA ^ 2 * sparseEta n k T ^ 2 *
            Real.exp (128 *
              (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)))) *
        (∫⁻ z, ENNReal.ofReal
            (sparseN (sparseSignalCount_le n k) (sparseQ n k T)
              (sparseC0 n k T) j l (sparseT0 n k T) z.2)
          ∂sparseJointLaw
            (sparseHiddenTableMeasure (sparseBlockCount n k) n) P
            (sparseConcreteHiddenTableParameterFamily hk hr hT)
            (sparseT0 n k T)) := by
  let eta := sparseEta n k T
  let heta : eta <= (1 : Real) / 16 :=
    (sparseEta_bounds hk hr hT).1.trans
      (sparseEta_bounds hk hr hT).2.le
  let F : SparseAdaptiveParameterFamily
      (SparseHiddenTable (sparseBlockCount n k) n) n k :=
    sparseHiddenTableParameterFamily hk eta
    (sparseEta_nonneg n k T) heta
    (sparseSignalCount n k) (sparseQ n k T) (sparseC0 n k T)
    (sparseBlockCount n k)
  let rect := sparseHiddenTableParameterFamily_rectangle
    (q := sparseQ n k T) (c0 := sparseC0 n k T)
    (B := sparseBlockCount n k)
    hk eta (sparseEta_nonneg n k T) heta sparseA
    (by norm_num [sparseA]) (sparseSignalCount_le n k) hjl
  change
    (∫⁻ z, sparseHiddenTableCoordinateJointLikelihood F sparseA
          (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j)
          (sparseT0 n k T) z *
        sparseHiddenTableCoordinateJointLikelihood F sparseA
          (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) l)
          (sparseT0 n k T) z
      ∂sparseJointLaw
        (sparseHiddenTableMeasure (sparseBlockCount n k) n) P F
        (sparseT0 n k T)) <= _
  refine lower_likelihood_cross_fullTable
    (n' := sparseSignalCount n k) (q := sparseQ n k T)
    (c0 := sparseC0 n k T) (B := sparseBlockCount n k)
    P F sparseA eta (by norm_num [sparseA])
    (sparseSignalCount_le n k) hjl rect (sparseT0 n k T)
    (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)) ?_ ?_
  · intro table h
    exact sparseHiddenTableParameterFamily_crossEnergy_le
      (q := sparseQ n k T) (c0 := sparseC0 n k T)
      (B := sparseBlockCount n k)
      hk eta (sparseEta_nonneg n k T) heta sparseA
      (by norm_num [sparseA]) (sparseSignalCount_le n k) hjl
      table (sparseT0 n k T) h (by simp [sparseT0])
  · intro h
    exact sparseConcrete_cross_budget hk hr hT j l h

/-- Cross moment in the exact interface consumed by the RN-density
chi-square theorem: the last factor is the expectation under the actual
history marginal of the base joint law. -/
theorem lower_likelihood_cross_concreteFullTable_expectedN
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) {j l : Fin (sparseSignalCount n k)} (hjl : j ≠ l) :
    (∫⁻ z, sparseConcreteCoordinateLikelihood hk hr hT j z *
          sparseConcreteCoordinateLikelihood hk hr hT l z
        ∂sparseConcreteJointLaw hk hr hT P) <=
      ENNReal.ofReal
        (1 + (128 * sparseA ^ 2 * sparseEta n k T ^ 2 *
              Real.exp (128 *
                (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)))) *
            sparseExpectedN (sparseConcreteHistoryLaw hk hr hT P)
              (sparseSignalCount_le n k) (sparseQ n k T)
              (sparseC0 n k T) j l) := by
  let base := sparseConcreteJointLaw hk hr hT P
  let mu := sparseConcreteHistoryLaw hk hr hT P
  let K : Real := 128 * sparseA ^ 2 * sparseEta n k T ^ 2 *
    Real.exp (128 *
      (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)))
  have hK0 : 0 <= K := by
    dsimp [K]
    positivity
  letI : IsProbabilityMeasure base := by
    dsimp [base, sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  letI : IsProbabilityMeasure mu := by
    rw [isProbabilityMeasure_iff]
    dsimp [mu, sparseConcreteHistoryLaw]
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]
    simp
  have hNint : Integrable
      (sparseN (sparseSignalCount_le n k) (sparseQ n k T)
        (sparseC0 n k T) j l (sparseT0 n k T)) mu :=
    integrable_sparseN hk (sparseSignalCount_le n k) j l mu
  have hlin :
      (∫⁻ z, ENNReal.ofReal
          (sparseN (sparseSignalCount_le n k) (sparseQ n k T)
            (sparseC0 n k T) j l (sparseT0 n k T) z.2) ∂base) =
        ENNReal.ofReal
          (sparseExpectedN mu (sparseSignalCount_le n k)
            (sparseQ n k T) (sparseC0 n k T) j l) := by
    rw [← lintegral_map
      (Measurable.ennreal_ofReal
        (measurable_sparseN (sparseSignalCount_le n k) j l
          (sparseT0 n k T))) measurable_snd]
    change (∫⁻ h, ENNReal.ofReal
        (sparseN (sparseSignalCount_le n k) (sparseQ n k T)
          (sparseC0 n k T) j l (sparseT0 n k T) h) ∂mu) = _
    rw [← ofReal_integral_eq_lintegral_ofReal hNint]
    · rfl
    · exact ae_of_all _ fun h =>
        sparseN_nonneg (sparseSignalCount_le n k) j l h
  have hraw := lower_likelihood_cross_concreteFullTable
    hk hr hT P hjl
  change (∫⁻ z, sparseConcreteCoordinateLikelihood hk hr hT j z *
        sparseConcreteCoordinateLikelihood hk hr hT l z ∂base) <= _
  calc
    (∫⁻ z, sparseConcreteCoordinateLikelihood hk hr hT j z *
        sparseConcreteCoordinateLikelihood hk hr hT l z ∂base) <=
      1 + ENNReal.ofReal K *
        (∫⁻ z, ENNReal.ofReal
          (sparseN (sparseSignalCount_le n k) (sparseQ n k T)
            (sparseC0 n k T) j l (sparseT0 n k T) z.2) ∂base) := by
      simpa [base, K, sparseConcreteJointLaw,
        sparseConcreteCoordinateLikelihood] using hraw
    _ = 1 + ENNReal.ofReal K * ENNReal.ofReal
        (sparseExpectedN mu (sparseSignalCount_le n k)
          (sparseQ n k T) (sparseC0 n k T) j l) := by rw [hlin]
    _ = ENNReal.ofReal
        (1 + K * sparseExpectedN mu (sparseSignalCount_le n k)
          (sparseQ n k T) (sparseC0 n k T) j l) := by
      have hN0 := sparseExpectedN_nonneg
        (q := sparseQ n k T) (c0 := sparseC0 n k T) mu
        (sparseSignalCount_le n k) j l
      rw [ENNReal.ofReal_add (by norm_num) (mul_nonneg hK0 hN0),
        ENNReal.ofReal_mul hK0]
      norm_num

/-! ## The genuine full-table good partition -/

/-- The full hidden-table likelihoods, with the manuscript's concrete
parameters, have an equipartition whose average density chi-square is bounded
by the exact diagonal-plus-cross expression.  In particular, none of the
normalization, finiteness, diagonal-moment, or cross-moment hypotheses from the
abstract partition theorem remain in the statement. -/
theorem exists_sparseConcrete_goodPartition_average_densityChiSquare_le
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
        (Real.exp (10 * sparseA ^ 2 * (sparseBlockCount n k : Real)) - 1) /
            (sparseRatio n k : Real) +
          (128 * sparseA ^ 2 * sparseEta n k T ^ 2 *
              Real.exp (128 *
                (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)))) *
            ((sparseT0 n k T : Real) / (k : Real)) /
              ((k : Real) * (sparseRatio n k : Real) ^ 2) := by
  let base := sparseConcreteJointLaw hk hr hT P
  let mu := sparseConcreteHistoryLaw hk hr hT P
  let Lambda : Fin (sparseSignalCount n k) ->
      SparseHiddenTable (sparseBlockCount n k) n ×
          History n k (sparseT0 n k T) -> ENNReal :=
    sparseConcreteCoordinateLikelihood hk hr hT
  let D : Real := Real.exp
    (10 * sparseA ^ 2 * (sparseBlockCount n k : Real))
  let K : Real := 128 * sparseA ^ 2 * sparseEta n k T ^ 2 *
    Real.exp (128 *
      (sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real)))
  have hr1 : 1 <= sparseRatio n k :=
    (by norm_num : 1 <= 2 ^ 32).trans hr
  have hr2 : 2 <= sparseRatio n k :=
    (by norm_num : 2 <= 2 ^ 32).trans hr
  have hn'2 : 2 <= sparseSignalCount n k := by
    simpa [sparseSignalCount] using Nat.mul_le_mul hk hr2
  letI : IsProbabilityMeasure base := by
    dsimp [base, sparseConcreteJointLaw, sparseJointLaw]
    infer_instance
  letI : IsProbabilityMeasure mu := by
    rw [isProbabilityMeasure_iff]
    dsimp [mu, sparseConcreteHistoryLaw]
    rw [Measure.map_apply measurable_snd MeasurableSet.univ]
    simp
  have hLambda : forall j, Measurable (Lambda j) := by
    intro j
    exact measurable_sparseConcreteCoordinateLikelihood hk hr hT j
  have hdiag : forall j,
      (∫⁻ z, Lambda j z * Lambda j z ∂base) <= ENNReal.ofReal D := by
    intro j
    simpa [base, Lambda, D, sparseConcreteJointLaw,
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
  have hQ : forall j,
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
  have hD0 : 0 <= D := by
    dsimp [D]
    positivity
  have hK0 : 0 <= K := by
    dsimp [K]
    positivity
  have hcross : forall j l, j ≠ l ->
      (∫⁻ z, Lambda j z * Lambda l z ∂base) <=
        ENNReal.ofReal
          (1 + K * sparseExpectedN mu (sparseSignalCount_le n k)
            (sparseQ n k T) (sparseC0 n k T) j l) := by
    intro j l hjl
    simpa [base, mu, Lambda, K] using
      lower_likelihood_cross_concreteFullTable_expectedN hk hr hT P hjl
  simpa [base, mu, Lambda, D, K] using
    (exists_sparse_good_partition_average_densityChiSquare_le_of_ennreal
      (n := n) (n' := sparseSignalCount n k) (k := k)
      (r := sparseRatio n k) (q := sparseQ n k T)
      (c0 := sparseC0 n k T) (t := sparseT0 n k T)
      hk hr1 hn'2 (sparseSignalCount_le n k)
      (rfl : sparseSignalCount n k = k * sparseRatio n k)
      base mu Lambda hLambda hLambdaFinite hQ D K hD0 hK0 hdiag hcross)

#print axioms map_sparseHiddenTableBothCoordinateEquiv_measure
#print axioms sparseHiddenTableBothJointLaw_map_eq_withDensity
#print axioms sparseHiddenTableJointLikelihood_cross_integral_eq
#print axioms lower_likelihood_cross_fullTable
#print axioms sparseHiddenTableParameterFamily_crossEnergy_le
#print axioms sparseConcrete_cross_budget
#print axioms lower_likelihood_cross_concreteFullTable
#print axioms lower_likelihood_cross_concreteFullTable_expectedN
#print axioms exists_sparseConcrete_goodPartition_average_densityChiSquare_le

end

end MsetsLower.Lower.Sparse
