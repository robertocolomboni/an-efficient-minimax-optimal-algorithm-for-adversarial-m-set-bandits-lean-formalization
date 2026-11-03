import MsetsLower.Lower.MainAssembly
import MsetsLower.Lower.OrdinaryBandit

/-!
# Qualitative statements derived from the explicit theorem

The paper states its headline theorem using existential universal constants
and a polynomially bounded horizon threshold.  The appendix then supplies
literal witnesses.  This module formalizes that implication without treating
the explicit theorem as an assumption hidden in a declaration.
-/

namespace MsetsLower.Lower

open MsetsLower Set

noncomputable section

/-- The concrete polynomial upper bound displayed immediately after the
explicit lower-bound theorem. -/
def lowerThresholdPolynomial (d : Nat) (delta : Real) : Real :=
  1 + (d : Real) ^ 2 + 64 * (d : Real) ^ 3 +
    4 * (d : Real) ^ 3 * confidenceLog delta

/-- Literal semantic form of `thm:lower-bound`, including witnesses for the
universal constants and an explicit polynomial upper bound on the threshold. -/
def QualitativeLowerBound : Prop :=
  ∃ (c delta0 : Real) (threshold : Nat → Nat → Real → Nat),
    0 < c ∧ delta0 ∈ Ioo (0 : Real) 1 ∧
    (∀ d m delta, (_hd : 2 ≤ d) → (_hm : 1 ≤ m) →
      (_hmdelta : m ≤ d - 1) → (_hdelta : 0 < delta) →
      (_hdeltaSmall : delta ≤ delta0) →
      (threshold d m delta : Real) ≤ lowerThresholdPolynomial d delta) ∧
    (∀ d m delta T, (_hd : 2 ≤ d) → (_hm : 1 ≤ m) →
      (hmdelta : m ≤ d - 1) → (_hdelta : 0 < delta) →
      (_hdeltaSmall : delta ≤ delta0) →
      (_hT : threshold d m delta ≤ T) →
      ∀ P : Policy d m,
        HasRegretLowerTail (by omega : m ≤ d) P T
          (c * Real.sqrt ((d : Real) * (T : Real) *
            lowerComplexity d m delta)) delta)

/-- The explicit quantitative theorem supplies the witnesses stated by the
qualitative headline theorem. -/
theorem qualitativeLowerBound_of_explicit
    (hexplicit : ∀ {d m T : Nat} {delta : Real},
      (_hd : 2 ≤ d) → (_hm : 1 ≤ m) → (hmdelta : m ≤ d - 1) →
      (_hdelta : 0 < delta) →
      (_hdeltaSmall : delta ≤ 1 / (2 : Real) ^ 36) →
      (_hT : explicitHorizonThreshold d (sparseSize d m) delta ≤ T) →
      ExplicitLowerConclusion d m T (by omega) delta) :
    QualitativeLowerBound := by
  refine ⟨finalLowerConstant, 1 / (2 : Real) ^ 36,
    fun d m delta => explicitHorizonThreshold d (sparseSize d m) delta,
    ?_, ?_, ?_, ?_⟩
  · norm_num [finalLowerConstant]
  · constructor <;> norm_num
  · intro d m delta hd hm hmdelta hdelta hdeltaSmall
    have hmd : m ≤ d := by omega
    have hsBounds := sparseSize_bounds hm hmdelta
    have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans (by norm_num)
    simpa [lowerThresholdPolynomial] using
      explicit_threshold_polynomial_bound hsBounds.1
        (sparseSize_le_dimension hmd) hdelta hdeltaOne
  · intro d m delta T hd hm hmdelta hdelta hdeltaSmall hT P
    exact hexplicit hd hm hmdelta hdelta hdeltaSmall hT P

/-- Literal qualitative form of the ordinary-bandit corollary. -/
def QualitativeOrdinaryBanditLowerBound : Prop :=
  ∃ (c delta0 : Real) (threshold : Nat → Real → Nat),
    0 < c ∧ delta0 ∈ Ioo (0 : Real) 1 ∧
    (∀ K delta, (_hK : 2 ≤ K) → (_hdelta : 0 < delta) →
      (_hdeltaSmall : delta ≤ delta0) →
      (threshold K delta : Real) ≤ lowerThresholdPolynomial K delta) ∧
    (∀ K delta T, (hK : 2 ≤ K) → (_hdelta : 0 < delta) →
      (_hdeltaSmall : delta ≤ delta0) → (_hT : threshold K delta ≤ T) →
      ∀ P : Policy K 1,
        ∃ L : LossProcess K 1,
          (∀ t (h : History K 1 t) i,
            L.itemLoss t h i ∈ Icc (0 : Real) 1) ∧
          ENNReal.ofReal delta ≤
            regretTailProbability (by omega : 1 ≤ K) P L T
              (c * Real.sqrt ((K : Real) * (T : Real) *
                (Real.log (K : Real) + confidenceLog delta))))

/-- The explicit m-set theorem at `m=1` gives the ordinary-bandit corollary
with the same universal constants and polynomial threshold. -/
theorem qualitativeOrdinaryBanditLowerBound_of_explicit
    (hexplicit : ∀ {d m T : Nat} {delta : Real},
      (_hd : 2 ≤ d) → (_hm : 1 ≤ m) → (hmdelta : m ≤ d - 1) →
      (_hdelta : 0 < delta) →
      (_hdeltaSmall : delta ≤ 1 / (2 : Real) ^ 36) →
      (_hT : explicitHorizonThreshold d (sparseSize d m) delta ≤ T) →
      ExplicitLowerConclusion d m T (by omega) delta) :
    QualitativeOrdinaryBanditLowerBound := by
  refine ⟨finalLowerConstant, 1 / (2 : Real) ^ 36,
    fun K delta => explicitHorizonThreshold K 1 delta,
    ?_, ?_, ?_, ?_⟩
  · norm_num [finalLowerConstant]
  · constructor <;> norm_num
  · intro K delta hK hdelta hdeltaSmall
    have hdeltaOne : delta ≤ 1 := hdeltaSmall.trans (by norm_num)
    simpa [lowerThresholdPolynomial] using
      explicit_threshold_polynomial_bound (by omega : 1 ≤ 1)
        (by omega : 1 ≤ K) hdelta hdeltaOne
  · intro K delta T hK hdelta hdeltaSmall hT P
    have hsparse : sparseSize K 1 = 1 := by
      have : 1 ≤ K - 1 := by omega
      simp [sparseSize, min_eq_left this]
    have hexp : ExplicitLowerConclusion K 1 T (by omega) delta :=
      hexplicit hK (by omega) (by omega) hdelta hdeltaSmall (by
        simpa [hsparse] using hT)
    exact ordinaryBanditConclusion_of_explicit hK hexp P

/-- The headline qualitative theorem, modulo the single sparse capstone
interface used by the explicit theorem. -/
theorem lower_bound_of_sparseCapstone
    (hSparse : SparseActionCountCapstone) : QualitativeLowerBound := by
  apply qualitativeLowerBound_of_explicit
  intro d m T delta hd hm hmdelta hdelta hdeltaSmall hT
  exact lower_bound_explicit_of_sparseCapstone hSparse
    hd hm hmdelta hdelta hdeltaSmall hT

/-- The ordinary-bandit qualitative corollary, with the same isolated sparse
capstone input. -/
theorem ordinary_bandits_lower_bound_of_sparseCapstone
    (hSparse : SparseActionCountCapstone) :
    QualitativeOrdinaryBanditLowerBound := by
  apply qualitativeOrdinaryBanditLowerBound_of_explicit
  intro d m T delta hd hm hmdelta hdelta hdeltaSmall hT
  exact lower_bound_explicit_of_sparseCapstone hSparse
    hd hm hmdelta hdelta hdeltaSmall hT

/-- `thm:lower-bound`, with the explicit constants and polynomial threshold
as witnesses. -/
theorem lower_bound : QualitativeLowerBound :=
  lower_bound_of_sparseCapstone lower_sparseActionCountCapstone

/-- The paper's ordinary-bandit qualitative corollary. -/
theorem ordinary_bandits_lower_bound : QualitativeOrdinaryBanditLowerBound :=
  ordinary_bandits_lower_bound_of_sparseCapstone
    lower_sparseActionCountCapstone

#print axioms qualitativeLowerBound_of_explicit
#print axioms qualitativeOrdinaryBanditLowerBound_of_explicit
#print axioms lower_bound_of_sparseCapstone
#print axioms ordinary_bandits_lower_bound_of_sparseCapstone
#print axioms lower_bound
#print axioms ordinary_bandits_lower_bound

end

end MsetsLower.Lower
