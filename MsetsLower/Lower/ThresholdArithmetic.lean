import MsetsLower.Prelude
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# The explicit horizon threshold

These declarations formalize `eq:lower-explicit-threshold` and the arithmetic
immediately following `thm:lower-bound-explicit`.  In particular, the single
ceiling hypothesis is split into the three hypotheses consumed by the
action-count and confidence constructions.
-/

namespace MsetsLower.Lower

noncomputable section

/-- The action-count logarithm `log(e d / s)`. -/
def actionCountLog (d s : Nat) : Real :=
  Real.log (Real.exp 1 * (d : Real) / (s : Real))

/-- The confidence logarithm `log(1/δ)`. -/
def confidenceLog (delta : Real) : Real := Real.log (1 / delta)

/-- The real expression inside the ceiling in
`eq:lower-explicit-threshold`. -/
def explicitThresholdArgument (d s : Nat) (delta : Real) : Real :=
  (d : Real) ^ 2
    + 64 * (d : Real) * (s : Real) * actionCountLog d s
    + 4 * (d : Real) * (s : Real) ^ 2 * confidenceLog delta

/-- The literal natural-valued ceiling used by the explicit theorem. -/
def explicitHorizonThreshold (d s : Nat) (delta : Real) : Nat :=
  Nat.ceil (explicitThresholdArgument d s delta)

theorem actionCountLog_nonneg
    {d s : Nat} (hs : 1 ≤ s) (hsd : s ≤ d) :
    0 ≤ actionCountLog d s := by
  have hspos : 0 < (s : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  have hratio : (1 : Real) ≤ (d : Real) / (s : Real) := by
    apply (le_div_iff₀ hspos).2
    norm_num
    exact_mod_cast hsd
  have hexp : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have harg : (1 : Real) ≤ Real.exp 1 * (d : Real) / (s : Real) := by
    calc
      (1 : Real) = 1 * 1 := by ring
      _ ≤ Real.exp 1 * ((d : Real) / (s : Real)) :=
        mul_le_mul hexp hratio (by norm_num) (Real.exp_pos 1).le
      _ = Real.exp 1 * (d : Real) / (s : Real) := by ring
  exact Real.log_nonneg harg

theorem confidenceLog_nonneg
    {delta : Real} (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    0 ≤ confidenceLog delta := by
  apply Real.log_nonneg
  apply (le_div_iff₀ hdelta).2
  simpa using hdelta_one

theorem explicitThresholdArgument_nonneg
    {d s : Nat} {delta : Real}
    (hs : 1 ≤ s) (hsd : s ≤ d)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    0 ≤ explicitThresholdArgument d s delta := by
  have haction := actionCountLog_nonneg hs hsd
  have hconfidence := confidenceLog_nonneg hdelta hdelta_one
  dsimp [explicitThresholdArgument]
  positivity

theorem explicitThresholdArgument_le_threshold
    {d s : Nat} {delta : Real} :
    explicitThresholdArgument d s delta ≤
      (explicitHorizonThreshold d s delta : Real) := by
  exact Nat.le_ceil _

/-- The explicit ceiling hypothesis implies, separately, the `d²`,
action-count, and confidence horizon bounds used later in the proof. -/
theorem explicit_threshold_splits
    {d s T : Nat} {delta : Real}
    (hs : 1 ≤ s) (hsd : s ≤ d)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1)
    (hT : explicitHorizonThreshold d s delta ≤ T) :
    (d : Real) ^ 2 ≤ (T : Real) ∧
      64 * (d : Real) * (s : Real) * actionCountLog d s ≤ (T : Real) ∧
      4 * (d : Real) * (s : Real) ^ 2 * confidenceLog delta ≤ (T : Real) := by
  have hceil : (explicitHorizonThreshold d s delta : Real) ≤ (T : Real) := by
    exact_mod_cast hT
  have hsum : explicitThresholdArgument d s delta ≤ (T : Real) :=
    explicitThresholdArgument_le_threshold.trans hceil
  have haction := actionCountLog_nonneg hs hsd
  have hconfidence := confidenceLog_nonneg hdelta hdelta_one
  have hd : (0 : Real) ≤ d := by positivity
  have hs' : (0 : Real) ≤ s := by positivity
  dsimp [explicitThresholdArgument] at hsum
  constructor
  · nlinarith [mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) ≤ 64) hd) hs')
        haction,
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) ≤ 4) hd)
        (sq_nonneg (s : Real))) hconfidence]
  constructor
  · nlinarith [sq_nonneg (d : Real),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) ≤ 4) hd)
        (sq_nonneg (s : Real))) hconfidence]
  · nlinarith [sq_nonneg (d : Real),
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num : (0 : Real) ≤ 64) hd) hs')
        haction]

/-- For `1 ≤ s ≤ d`, the manuscript's coarse estimate
`log(e d / s) ≤ d`. -/
theorem actionCountLog_le_dimension
    {d s : Nat} (hs : 1 ≤ s) (hsd : s ≤ d) :
    actionCountLog d s ≤ (d : Real) := by
  have hspos : 0 < (s : Real) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hs)
  have hdposNat : 0 < d := lt_of_lt_of_le (lt_of_lt_of_le Nat.zero_lt_one hs) hsd
  have hdpos : 0 < (d : Real) := by exact_mod_cast hdposNat
  have hratio : (d : Real) / (s : Real) ≤ (d : Real) := by
    apply (div_le_iff₀ hspos).2
    have hsreal : (1 : Real) ≤ (s : Real) := by exact_mod_cast hs
    nlinarith
  have hargle : Real.exp 1 * (d : Real) / (s : Real) ≤
      Real.exp 1 * (d : Real) := by
    calc
      Real.exp 1 * (d : Real) / (s : Real) =
          Real.exp 1 * ((d : Real) / (s : Real)) := by ring
      _ ≤ Real.exp 1 * (d : Real) :=
        mul_le_mul_of_nonneg_left hratio (Real.exp_pos 1).le
  have hargpos : 0 < Real.exp 1 * (d : Real) / (s : Real) := by positivity
  have hupperpos : 0 < Real.exp 1 * (d : Real) := mul_pos (Real.exp_pos 1) hdpos
  have hlogmono : Real.log (Real.exp 1 * (d : Real) / (s : Real)) ≤
      Real.log (Real.exp 1 * (d : Real)) :=
    Real.strictMonoOn_log.monotoneOn hargpos hupperpos hargle
  have hlogd : Real.log (d : Real) ≤ (d : Real) - 1 :=
    Real.log_le_sub_one_of_pos hdpos
  rw [Real.log_mul (Real.exp_ne_zero 1) (ne_of_gt hdpos), Real.log_exp] at hlogmono
  dsimp [actionCountLog]
  linarith

/-- The natural threshold is bounded by the polynomial displayed after the
explicit theorem. -/
theorem explicit_threshold_polynomial_bound
    {d s : Nat} {delta : Real}
    (hs : 1 ≤ s) (hsd : s ≤ d)
    (hdelta : 0 < delta) (hdelta_one : delta ≤ 1) :
    (explicitHorizonThreshold d s delta : Real) ≤
      1 + (d : Real) ^ 2 + 64 * (d : Real) ^ 3
        + 4 * (d : Real) ^ 3 * confidenceLog delta := by
  have hargnonneg := explicitThresholdArgument_nonneg hs hsd hdelta hdelta_one
  have hceil_lt : (explicitHorizonThreshold d s delta : Real) <
      explicitThresholdArgument d s delta + 1 := Nat.ceil_lt_add_one hargnonneg
  have haction_nonneg := actionCountLog_nonneg hs hsd
  have haction_le := actionCountLog_le_dimension hs hsd
  have hconfidence := confidenceLog_nonneg hdelta hdelta_one
  have hsdreal : (s : Real) ≤ (d : Real) := by exact_mod_cast hsd
  have hterm_action :
      64 * (d : Real) * (s : Real) * actionCountLog d s ≤ 64 * (d : Real) ^ 3 := by
    have hd : (0 : Real) ≤ d := by positivity
    have hfirst : 64 * (d : Real) * (s : Real) ≤ 64 * (d : Real) * (d : Real) :=
      mul_le_mul_of_nonneg_left hsdreal (mul_nonneg (by norm_num) hd)
    calc
      64 * (d : Real) * (s : Real) * actionCountLog d s ≤
          64 * (d : Real) * (d : Real) * actionCountLog d s :=
        mul_le_mul_of_nonneg_right hfirst haction_nonneg
      _ ≤ 64 * (d : Real) * (d : Real) * (d : Real) :=
        mul_le_mul_of_nonneg_left haction_le
          (mul_nonneg (mul_nonneg (by norm_num) hd) hd)
      _ = 64 * (d : Real) ^ 3 := by ring
  have hsquare : (s : Real) ^ 2 ≤ (d : Real) ^ 2 := by nlinarith
  have hterm_confidence :
      4 * (d : Real) * (s : Real) ^ 2 * confidenceLog delta ≤
        4 * (d : Real) ^ 3 * confidenceLog delta := by
    have hd : (0 : Real) ≤ d := by positivity
    have hpre : 4 * (d : Real) * (s : Real) ^ 2 ≤
        4 * (d : Real) * (d : Real) ^ 2 :=
      mul_le_mul_of_nonneg_left hsquare (mul_nonneg (by norm_num) hd)
    have hmul := mul_le_mul_of_nonneg_right hpre hconfidence
    calc
      4 * (d : Real) * (s : Real) ^ 2 * confidenceLog delta ≤
          4 * (d : Real) * (d : Real) ^ 2 * confidenceLog delta := hmul
      _ = 4 * (d : Real) ^ 3 * confidenceLog delta := by ring
  dsimp [explicitThresholdArgument] at hceil_lt
  linarith

end

end MsetsLower.Lower
