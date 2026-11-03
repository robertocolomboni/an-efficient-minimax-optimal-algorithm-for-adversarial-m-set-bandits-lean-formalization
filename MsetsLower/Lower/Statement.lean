import MsetsLower.Lower.Complement
import MsetsLower.Lower.Parameters
import MsetsLower.Lower.RegretMeasurability
import MsetsLower.Lower.ThresholdArithmetic
import MsetsLower.Lower.FinalArithmetic

/-!
# Semantic statements for the lower bound

The paper's conclusions are probabilities of external-regret events under the
actual adaptive run law.  This module packages that statement once, and proves
that the complement reduction transports the whole tail event without changing
either its threshold or its probability.
-/

set_option linter.style.header false

namespace MsetsLower.Lower

open MsetsLower MeasureTheory ProbabilityTheory

noncomputable section

/-- Probability, under the genuine protocol law, that external regret at
horizon `T` is at least `threshold`. -/
def regretTailProbability {d m : Nat} (hmd : m ≤ d)
    (P : Policy d m) (L : LossProcess d m) (T : Nat)
    (threshold : Real) : ENNReal :=
  letI := nonempty_MSetAction hmd
  runLaw P L T {h | threshold ≤ pathRegret L T h}

/-- A deterministic non-anticipating adversary witnessing a lower tail bound
for a fixed randomized policy.  Determinism and non-anticipation are built into
`LossProcess`; its field `action_mem_Icc` is the literal `[0,1]` action-loss
condition from the manuscript. -/
def HasRegretLowerTail {d m : Nat} (hmd : m ≤ d)
    (P : Policy d m) (T : Nat)
    (threshold probability : Real) : Prop :=
  ∃ (L : LossProcess d m),
    ENNReal.ofReal probability ≤ regretTailProbability hmd P L T threshold

/-- Weakening the regret threshold or the requested probability preserves a
lower-tail witness. -/
theorem HasRegretLowerTail.mono
    {d m T : Nat} {hmd : m ≤ d} {P : Policy d m}
    {threshold probability threshold' probability' : Real}
    (h : HasRegretLowerTail hmd P T threshold probability)
    (hthreshold : threshold' ≤ threshold)
    (hprobability : probability' ≤ probability) :
    HasRegretLowerTail hmd P T threshold' probability' := by
  letI : Nonempty (MSetAction d m) := nonempty_MSetAction hmd
  rcases h with ⟨L, hL⟩
  refine ⟨L, (ENNReal.ofReal_le_ofReal hprobability).trans (hL.trans ?_)⟩
  apply measure_mono
  intro history hhistory
  exact hthreshold.trans hhistory

/-- The complement map preserves the full regret-tail probability, not merely
the pathwise regret value. -/
theorem regretTailProbability_complement
    {d s : Nat} (hsd : s ≤ d) (hm : 0 < d - s)
    (P : Policy d (d - s)) (G : LossProcess d s) (T : Nat)
    (threshold : Real) :
    regretTailProbability (Nat.sub_le d s) P
        (complementLossProcess hsd hm G) T threshold =
      regretTailProbability hsd (complementPolicy hsd P) G T threshold := by
  letI : Nonempty (MSetAction d (d - s)) :=
    nonempty_MSetAction (Nat.sub_le d s)
  letI : Nonempty (MSetAction d s) := nonempty_MSetAction hsd
  let e := historyComplementEquiv d s hsd T
  let source := runLaw P (complementLossProcess hsd hm G) T
  let target := runLaw (complementPolicy hsd P) G T
  let event : Set (History d s T) :=
    {h | threshold ≤ pathRegret G T h}
  have hevent : MeasurableSet event := by
    dsimp [event]
    exact measurableSet_pathRegret_ge_of_le hsd G T threshold
  have hmap : source.map e = target := by
    simpa [source, target, e] using complement_runLaw hsd hm P G T
  unfold regretTailProbability
  change source {h | threshold ≤
    pathRegret (complementLossProcess hsd hm G) T h} = target event
  have hpreimage :
      {h | threshold ≤ pathRegret (complementLossProcess hsd hm G) T h} =
        e ⁻¹' event := by
    ext h
    change (threshold ≤ pathRegret (complementLossProcess hsd hm G) T h) ↔
      threshold ≤ pathRegret G T (e h)
    rw [pathRegret_complement hsd hm G T h]
  calc
    source {h | threshold ≤
        pathRegret (complementLossProcess hsd hm G) T h} =
        source (e ⁻¹' event) := by rw [hpreimage]
    _ = (source.map e) event := by
      rw [Measure.map_apply e.measurable hevent]
    _ = target event := by rw [hmap]

/-- Any lower-tail witness for the complementary sparse policy transports to
the original exact-`(d-s)` policy with exactly the same constants. -/
theorem hasRegretLowerTail_complement
    {d s T : Nat} (hsd : s ≤ d) (hm : 0 < d - s)
    (P : Policy d (d - s)) (threshold probability : Real)
    (h : HasRegretLowerTail hsd (complementPolicy hsd P) T
      threshold probability) :
    HasRegretLowerTail (Nat.sub_le d s) P T threshold probability := by
  rcases h with ⟨G, hG⟩
  refine ⟨complementLossProcess hsd hm G, ?_⟩
  rwa [regretTailProbability_complement hsd hm P G T threshold]

/-- The literal logarithmic complexity appearing in the final theorem. -/
def lowerComplexity (d m : Nat) (delta : Real) : Real :=
  Real.log (Nat.choose d m : Real) + confidenceLog delta

/-- Probability supplied by the common action-count corollary. -/
def actionCountProbability : Real := 1 / (2 : Real) ^ 14

/-- Constant supplied by the confidence proposition. -/
def confidenceTailConstant : Real := 1 / (2 : Real) ^ 17

/-- Semantic form of `cor:lower-action-count` at fixed parameters. -/
def ActionCountConclusion (d s T : Nat) (hsd : s ≤ d) : Prop :=
  ∀ P : Policy d s,
    HasRegretLowerTail hsd P T
      (actionCountConstant * Real.sqrt ((d : Real) * T *
        Real.log (Nat.choose d s : Real))) actionCountProbability

/-- Semantic form of `prop:lower-confidence` at fixed parameters. -/
def ConfidenceConclusion (d s T : Nat) (hsd : s ≤ d)
    (delta : Real) : Prop :=
  ∀ P : Policy d s,
    HasRegretLowerTail hsd P T
      (confidenceTailConstant * Real.sqrt ((d : Real) * T *
        confidenceLog delta)) delta

theorem log_choose_nonneg {d s : Nat} (hsd : s ≤ d) :
    0 ≤ Real.log (Nat.choose d s : Real) := by
  apply Real.log_nonneg
  exact_mod_cast Nat.choose_pos hsd

/-- The final case split `H ≥ L` versus `L > H`, including the deliberate
factor-two loss from `max H L` to `H+L`. -/
theorem actionCount_confidence_final_assembly
    {d s T : Nat} (hsd : s ≤ d) {delta : Real}
    (hdelta_pos : 0 < delta) (hdelta_small : delta ≤ 1 / (2 : Real) ^ 36)
    (haction : ActionCountConclusion d s T hsd)
    (hconfidence : ConfidenceConclusion d s T hsd delta) :
    ∀ P : Policy d s,
      HasRegretLowerTail hsd P T
        (finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d s delta)) delta := by
  intro P
  let H : Real := Real.log (Nat.choose d s : Real)
  let L : Real := confidenceLog delta
  have hH : 0 ≤ H := by
    dsimp [H]
    exact log_choose_nonneg hsd
  have hdelta_one : delta ≤ 1 := hdelta_small.trans (by norm_num)
  have hL : 0 ≤ L := by
    dsimp [L]
    exact confidenceLog_nonneg hdelta_pos hdelta_one
  have hd : 0 ≤ (d : Real) := by positivity
  have hT : 0 ≤ (T : Real) := by positivity
  have hfinalmax := final_constant_sqrt_sum_le_sqrt_max hd hT hH hL
  by_cases hHL : L ≤ H
  · have hthreshold :
        finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d s delta) ≤
        actionCountConstant * Real.sqrt ((d : Real) * T * H) := by
      dsimp [lowerComplexity, H, L] at hfinalmax ⊢
      rw [max_eq_left hHL] at hfinalmax
      exact hfinalmax
    have hprobability : delta ≤ actionCountProbability := by
      dsimp [actionCountProbability]
      exact hdelta_small.trans (by norm_num)
    exact (haction P).mono hthreshold hprobability
  · have hLH : H ≤ L := le_of_not_ge hHL
    have hbase :
        finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d s delta) ≤
        actionCountConstant * Real.sqrt ((d : Real) * T * L) := by
      dsimp [lowerComplexity, H, L] at hfinalmax ⊢
      rw [max_eq_right hLH] at hfinalmax
      exact hfinalmax
    have hconstants : actionCountConstant ≤ confidenceTailConstant := by
      norm_num [actionCountConstant, confidenceTailConstant]
    have hsqrt : 0 ≤ Real.sqrt ((d : Real) * T * L) := Real.sqrt_nonneg _
    have hthreshold :
        finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d s delta) ≤
        confidenceTailConstant * Real.sqrt ((d : Real) * T * L) :=
      hbase.trans (mul_le_mul_of_nonneg_right hconstants hsqrt)
    exact (hconfidence P).mono (by
      simpa [L] using hthreshold) le_rfl

/-- The explicit quantitative conclusion, with the exact quantifier order of
`thm:lower-bound-explicit`.  Its hypotheses are kept outside this definition so
that the eventual theorem exposes them literally. -/
def ExplicitLowerConclusion (d m T : Nat) (hmd : m ≤ d)
    (delta : Real) : Prop :=
  ∀ P : Policy d m,
    HasRegretLowerTail hmd P T
      (finalLowerConstant * Real.sqrt ((d : Real) * T *
        lowerComplexity d m delta)) delta

/-- No transport is needed when the original action size already is the
smaller one. -/
theorem explicitLowerConclusion_of_eq
    {d m s T : Nat} (hmd : m ≤ d) (hsd : s ≤ d) (hms : m = s)
    {delta : Real}
    (h : ∀ P : Policy d s,
      HasRegretLowerTail hsd P T
        (finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d s delta)) delta) :
    ExplicitLowerConclusion d m T hmd delta := by
  subst m
  simpa [ExplicitLowerConclusion] using h

/-- When the original action size is `d-s`, the semantic complement theorem
transports the sparse lower-tail witness and binomial symmetry identifies the
displayed complexity exactly. -/
theorem explicitLowerConclusion_of_complement
    {d m s T : Nat} (hmd : m ≤ d) (hsd : s ≤ d)
    (hm : 0 < d - s) (hms : m = d - s) {delta : Real}
    (h : ∀ P : Policy d s,
      HasRegretLowerTail hsd P T
        (finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d s delta)) delta) :
    ExplicitLowerConclusion d m T hmd delta := by
  subst m
  intro P
  have hsparse := h (complementPolicy hsd P)
  have htransport := hasRegretLowerTail_complement hsd hm P
    (finalLowerConstant * Real.sqrt ((d : Real) * T *
      lowerComplexity d s delta)) delta hsparse
  have hcomplexity :
      lowerComplexity d (d - s) delta = lowerComplexity d s delta := by
    simp only [lowerComplexity, Nat.choose_symm hsd]
  simpa [ExplicitLowerConclusion, hcomplexity] using htransport

/-- The manuscript choice `s=min(m,d-m)` is either `m` itself or its
complement, so the preceding two exact transports cover all cases. -/
theorem explicitLowerConclusion_of_sparseSize
    {d m T : Nat} (hm_one : 1 ≤ m) (hm_lt : m ≤ d - 1)
    {delta : Real}
    (h : ∀ P : Policy d (sparseSize d m),
      HasRegretLowerTail (sparseSize_le_dimension (by omega : m ≤ d)) P T
        (finalLowerConstant * Real.sqrt ((d : Real) * T *
          lowerComplexity d (sparseSize d m) delta)) delta) :
    ExplicitLowerConclusion d m T (by omega) delta := by
  have hmd : m ≤ d := by omega
  have hsd : sparseSize d m ≤ d := sparseSize_le_dimension hmd
  have hspos : 1 ≤ sparseSize d m := (sparseSize_bounds hm_one hm_lt).1
  by_cases hmhalf : m ≤ d - m
  · have heq : m = sparseSize d m := by
      simp [sparseSize, min_eq_left hmhalf]
    exact explicitLowerConclusion_of_eq hmd hsd heq (by
      simpa only [proof_irrel_heq] using h)
  · have hsparse : sparseSize d m = d - m := by
      exact min_eq_right (le_of_not_ge hmhalf)
    have hcomp : m = d - sparseSize d m := by
      rw [hsparse, Nat.sub_sub_self hmd]
    have hpositive : 0 < d - sparseSize d m := by
      rw [← hcomp]
      omega
    exact explicitLowerConclusion_of_complement hmd hsd hpositive hcomp (by
      simpa only [proof_irrel_heq] using h)

#print axioms regretTailProbability_complement
#print axioms hasRegretLowerTail_complement
#print axioms HasRegretLowerTail.mono
#print axioms actionCount_confidence_final_assembly
#print axioms explicitLowerConclusion_of_sparseSize

end

end MsetsLower.Lower
