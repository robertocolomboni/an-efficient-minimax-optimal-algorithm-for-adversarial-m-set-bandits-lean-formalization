import MsetsLower.Lower.Sparse.Parameters
import MsetsLower.Lower.Statement
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Final numerical arithmetic of the sparse branch

This module records the constant spending after the three probabilistic sparse
estimates.  It deliberately does not assume any of those estimates under a
different name; it only combines their numerical right-hand sides.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower.Lower

noncomputable section

theorem sparseSqrtRho_eq : Real.sqrt sparseRho = 1 / (2 : Real) ^ 18 := by
  have hrho : sparseRho = ((1 : Real) / (2 : Real) ^ 18) ^ 2 := by
    norm_num [sparseRho]
  rw [hrho, Real.sqrt_sq_eq_abs, abs_of_nonneg]
  norm_num

theorem sparse_probability_constant : sparseA / 16 = 1 / (2 : Real) ^ 10 := by
  norm_num [sparseA]

/-- The exact numerical check below the expectation estimate for `Gamma`. -/
theorem sparse_error_budget_lt :
    48 * Real.sqrt sparseRho + 1 / (2 : Real) ^ 15 < sparseA / 12 := by
  rw [sparseSqrtRho_eq]
  norm_num [sparseA]

/-- The exact identity `(eta T0)^2=(rho/8)n'kT0B` from the manuscript. -/
theorem sparseEta_mul_T0_sq_identity
    {n k T : Nat} (hk : 1 ≤ k)
    (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    (sparseEta n k T * (sparseT0 n k T : Real)) ^ 2 =
      sparseRho / 8 * (sparseSignalCount n k : Real) * (k : Real) *
        (sparseT0 n k T : Real) * (sparseBlockCount n k : Real) := by
  have hcNat := sparseC0_ge hk hr hT
  have hcposNat : 0 < sparseC0 n k T :=
    lt_of_lt_of_le (by positivity : 0 < 256 * k ^ 2) hcNat
  have hellpos : 0 < sparseEll n k T := by
    simpa [sparseC0] using hcposNat
  have hcpos : 0 < (sparseC0 n k T : Real) := by exact_mod_cast hcposNat
  have hquot : 0 ≤ sparseRho / (sparseC0 n k T : Real) :=
    div_nonneg sparseRho_pos.le hcpos.le
  rw [sparseEta, mul_pow, mul_pow, Real.sq_sqrt hquot]
  simp only [sparseT0, sparseQ, sparseC0, sparseSignalCount,
    Nat.cast_mul, Nat.cast_ofNat]
  have hellreal : (0 : Real) < sparseEll n k T := by exact_mod_cast hellpos
  field_simp [ne_of_gt hellreal]

/-- The signal block `n'=k floor(n/k)` retains at least half the ambient
coordinates in the sparse regime. -/
theorem sparseSignalCount_ge_half
    {n k : Nat} (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k) :
    (n : Real) / 2 ≤ (sparseSignalCount n k : Real) := by
  have hkpos : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hrem : n % k < k := Nat.mod_lt n hkpos
  have hdecomp := Nat.div_add_mod n k
  have hnlt : n < sparseSignalCount n k + k := by
    dsimp [sparseSignalCount, sparseRatio]
    omega
  have hksignal : k ≤ sparseSignalCount n k := sparseSignalCount_ge hr
  have htwice : n ≤ 2 * sparseSignalCount n k := by omega
  have htwiceReal : (n : Real) ≤ 2 * (sparseSignalCount n k : Real) := by
    exact_mod_cast htwice
  linarith

/-- The floor `B=floor(log r)` loses at most a factor two when `r≥2^32`. -/
theorem sparseBlockCount_ge_half_log
    {n k : Nat} (hr : 2 ^ 32 ≤ sparseRatio n k) :
    Real.log (sparseRatio n k : Real) / 2 ≤
      (sparseBlockCount n k : Real) := by
  have hrposNat : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hrpos : 0 < (sparseRatio n k : Real) := by exact_mod_cast hrposNat
  have hrreal : (2 : Real) ^ 32 ≤ (sparseRatio n k : Real) := by
    exact_mod_cast hr
  have hlogmono :
    Real.log ((2 : Real) ^ 32) ≤
        Real.log (sparseRatio n k : Real) :=
    Real.strictMonoOn_log.monotoneOn
      (show (2 : Real) ^ 32 ∈ Set.Ioi 0 by norm_num) hrpos hrreal
  rw [Real.log_pow] at hlogmono
  have hlogtwo : (2 : Real) < 32 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogtwo' : (2 : Real) < Real.log (sparseRatio n k : Real) :=
    hlogtwo.trans_le hlogmono
  have hfloor : Real.log (sparseRatio n k : Real) - 1 <
      (sparseBlockCount n k : Real) := by
    exact Nat.sub_one_lt_floor _
  linarith

/-- Lower bound on `eta T0` before converting `log r` to the binomial
complexity.  This is the square-root consequence of the exact identity and
the three factor-two floor losses. -/
theorem sparseEta_mul_T0_ge_logRatio
    {n k T : Nat} (hk : 1 ≤ k)
    (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    Real.sqrt sparseRho / 8 *
        Real.sqrt ((n : Real) * (k : Real) * (T : Real) *
          Real.log (sparseRatio n k : Real)) ≤
      sparseEta n k T * (sparseT0 n k T : Real) := by
  let logR : Real := Real.log (sparseRatio n k : Real)
  have hlog : 0 ≤ logR := by
    dsimp [logR]
    apply Real.log_nonneg
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 32) hr)
  have hn := sparseSignalCount_ge_half hk hr
  have hT0 := (sparseT0_bounds hk hr hT).1
  have hB := sparseBlockCount_ge_half_log hr
  have hn0 : 0 ≤ (n : Real) / 2 := by positivity
  have hT0' : 0 ≤ (T : Real) / 2 := by positivity
  have hlog0 : 0 ≤ logR / 2 := by positivity
  have hsignal0 : 0 ≤ (sparseSignalCount n k : Real) := by positivity
  have hactive0 : 0 ≤ (sparseT0 n k T : Real) := by positivity
  have hproduct :
      (n : Real) * (T : Real) * logR / 8 ≤
        (sparseSignalCount n k : Real) * (sparseT0 n k T : Real) *
          (sparseBlockCount n k : Real) := by
    calc
      (n : Real) * (T : Real) * logR / 8 =
          ((n : Real) / 2) * ((T : Real) / 2) * (logR / 2) := by ring
      _ ≤ (sparseSignalCount n k : Real) * ((T : Real) / 2) *
          (logR / 2) := by gcongr
      _ ≤ (sparseSignalCount n k : Real) * (sparseT0 n k T : Real) *
          (logR / 2) := by gcongr
      _ ≤ (sparseSignalCount n k : Real) * (sparseT0 n k T : Real) *
          (sparseBlockCount n k : Real) := by gcongr
  have hscale : 0 ≤ sparseRho / 8 * (k : Real) :=
    mul_nonneg (div_nonneg sparseRho_pos.le (by norm_num)) (by positivity)
  have hscaled := mul_le_mul_of_nonneg_left hproduct hscale
  have hcomplexity :
      0 ≤ (n : Real) * (k : Real) * (T : Real) * logR := by positivity
  have htarget0 : 0 ≤ Real.sqrt sparseRho / 8 *
      Real.sqrt ((n : Real) * (k : Real) * (T : Real) * logR) := by
    positivity
  have heta0 : 0 ≤ sparseEta n k T * (sparseT0 n k T : Real) :=
    mul_nonneg (sparseEta_nonneg n k T) (by positivity)
  apply (sq_le_sq₀ htarget0 heta0).mp
  calc
    (Real.sqrt sparseRho / 8 *
        Real.sqrt ((n : Real) * (k : Real) * (T : Real) * logR)) ^ 2 =
        sparseRho / 64 *
          ((n : Real) * (k : Real) * (T : Real) * logR) := by
      rw [mul_pow, div_pow, Real.sq_sqrt sparseRho_pos.le,
        Real.sq_sqrt hcomplexity]
      ring
    _ = (sparseRho / 8 * (k : Real)) *
        ((n : Real) * (T : Real) * logR / 8) := by ring
    _ ≤ (sparseRho / 8 * (k : Real)) *
        ((sparseSignalCount n k : Real) * (sparseT0 n k T : Real) *
          (sparseBlockCount n k : Real)) := hscaled
    _ = (sparseEta n k T * (sparseT0 n k T : Real)) ^ 2 := by
      rw [sparseEta_mul_T0_sq_identity hk hr hT]
      ring

private theorem pow_div_exp_le_factorial {k : Nat} (hk : 1 ≤ k) :
    ((k : Real) / Real.exp 1) ^ k ≤ (k.factorial : Real) := by
  have hkreal : (1 : Real) ≤ k := by exact_mod_cast hk
  have hsqrt : 1 ≤ Real.sqrt (2 * Real.pi * (k : Real)) := by
    rw [Real.one_le_sqrt]
    nlinarith [Real.pi_gt_three]
  have hpow : 0 ≤ ((k : Real) / Real.exp 1) ^ k := by positivity
  calc
    ((k : Real) / Real.exp 1) ^ k ≤
        Real.sqrt (2 * Real.pi * (k : Real)) *
          ((k : Real) / Real.exp 1) ^ k := by
      nlinarith
    _ ≤ (k.factorial : Real) := Stirling.le_factorial_stirling k

/-- The standard entropy upper bound
`log (n choose k) ≤ k log(e n/k)`, proved here from the factorial form rather
than imported as an external estimate. -/
theorem log_choose_le_mul_actionCountLog
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n) :
    Real.log (n.choose k : Real) ≤ (k : Real) * actionCountLog n k := by
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : 0 < (k : Real) := by exact_mod_cast hkposNat
  have hchoosePosNat : 0 < n.choose k := Nat.choose_pos hkn
  have hchoosePos : 0 < (n.choose k : Real) := by exact_mod_cast hchoosePosNat
  have hfactorial := pow_div_exp_le_factorial hk
  have hfactorialPos : 0 < (k.factorial : Real) := by positivity
  have hbasePos : 0 < (k : Real) / Real.exp 1 := div_pos hkpos (Real.exp_pos 1)
  have hpowPos : 0 < ((k : Real) / Real.exp 1) ^ k := pow_pos hbasePos _
  have hchooseDiv :
      (n.choose k : Real) ≤ (n : Real) ^ k / (k.factorial : Real) :=
    Nat.choose_le_pow_div k n
  have hdiv :
      (n : Real) ^ k / (k.factorial : Real) ≤
        (n : Real) ^ k / (((k : Real) / Real.exp 1) ^ k) :=
    div_le_div_of_nonneg_left (by positivity) hpowPos hfactorial
  have halgebra :
      (n : Real) ^ k / (((k : Real) / Real.exp 1) ^ k) =
        (Real.exp 1 * (n : Real) / (k : Real)) ^ k := by
    rw [← div_pow]
    congr 1
    field_simp
  have hchoosePow :
      (n.choose k : Real) ≤
        (Real.exp 1 * (n : Real) / (k : Real)) ^ k := by
    exact hchooseDiv.trans (hdiv.trans_eq halgebra)
  have hargPos : 0 < Real.exp 1 * (n : Real) / (k : Real) := by
    have hnposNat : 0 < n := lt_of_lt_of_le hkposNat hkn
    positivity
  have hlog := Real.log_le_log hchoosePos hchoosePow
  rw [Real.log_pow] at hlog
  simpa [actionCountLog] using hlog

/-- In the sparse regime, `log(e n/k) ≤ 2 log floor(n/k)`. -/
theorem actionCountLog_le_two_log_sparseRatio
    {n k : Nat} (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k) :
    actionCountLog n k ≤ 2 * Real.log (sparseRatio n k : Real) := by
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : 0 < (k : Real) := by exact_mod_cast hkposNat
  have hrposNat : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hrpos : 0 < (sparseRatio n k : Real) := by exact_mod_cast hrposNat
  have hrem : n % k < k := Nat.mod_lt n hkposNat
  have hnltNat : n < (sparseRatio n k + 1) * k := by
    calc
      n = k * (n / k) + n % k := (Nat.div_add_mod n k).symm
      _ < k * (n / k) + k := Nat.add_lt_add_left hrem _
      _ = (sparseRatio n k + 1) * k := by
        simp [sparseRatio, Nat.mul_add, Nat.mul_comm]
  have hnlt :
      (n : Real) / (k : Real) < (sparseRatio n k : Real) + 1 := by
    apply (div_lt_iff₀ hkpos).2
    exact_mod_cast hnltNat
  have hrFourNat : 4 ≤ sparseRatio n k :=
    (by norm_num : 4 ≤ 2 ^ 32).trans hr
  have hrFour : (4 : Real) ≤ sparseRatio n k := by exact_mod_cast hrFourNat
  have hsquare :
      3 * ((sparseRatio n k : Real) + 1) ≤
        (sparseRatio n k : Real) ^ 2 := by
    have hprod : 0 ≤ ((sparseRatio n k : Real) - 4) *
        ((sparseRatio n k : Real) + 1) := by positivity
    nlinarith
  have hargLe :
      Real.exp 1 * (n : Real) / (k : Real) ≤
        (sparseRatio n k : Real) ^ 2 := by
    calc
      Real.exp 1 * (n : Real) / (k : Real) =
          Real.exp 1 * ((n : Real) / (k : Real)) := by ring
      _ ≤ 3 * ((n : Real) / (k : Real)) := by
        exact mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le (by positivity)
      _ ≤ 3 * ((sparseRatio n k : Real) + 1) := by
        exact mul_le_mul_of_nonneg_left hnlt.le (by norm_num)
      _ ≤ (sparseRatio n k : Real) ^ 2 := hsquare
  have hargPos : 0 < Real.exp 1 * (n : Real) / (k : Real) := by
    have hnposNat : 0 < n := by
      have : 0 < k * sparseRatio n k := Nat.mul_pos hkposNat hrposNat
      exact lt_of_lt_of_le this (sparseSignalCount_le n k)
    positivity
  have hlog := Real.log_le_log hargPos hargLe
  rw [Real.log_pow] at hlog
  simpa [actionCountLog] using hlog

/-- The exact binomial-complexity comparison used after the sparse parameter
identity. -/
theorem log_choose_le_two_mul_k_log_sparseRatio
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hr : 2 ^ 32 ≤ sparseRatio n k) :
    Real.log (n.choose k : Real) ≤
      2 * (k : Real) * Real.log (sparseRatio n k : Real) := by
  calc
    Real.log (n.choose k : Real) ≤
        (k : Real) * actionCountLog n k :=
      log_choose_le_mul_actionCountLog hk hkn
    _ ≤ (k : Real) *
        (2 * Real.log (sparseRatio n k : Real)) := by
      gcongr
      exact actionCountLog_le_two_log_sparseRatio hk hr
    _ = 2 * (k : Real) * Real.log (sparseRatio n k : Real) := by ring

/-- Conversion of the `eta T0` lower bound from `log r` to the literal
binomial action-count complexity. -/
theorem sparseEta_mul_T0_ge_logChoose
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    Real.sqrt sparseRho / 16 *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)) ≤
      sparseEta n k T * (sparseT0 n k T : Real) := by
  let logChoose : Real := Real.log (n.choose k : Real)
  let logR : Real := Real.log (sparseRatio n k : Real)
  let target : Real := (n : Real) * (T : Real) * logChoose
  let reference : Real := (n : Real) * (k : Real) * (T : Real) * logR
  have hchooseOneNat : 1 ≤ n.choose k :=
    Nat.one_le_iff_ne_zero.mpr (Nat.choose_ne_zero hkn)
  have hlogChoose : 0 ≤ logChoose := by
    dsimp [logChoose]
    apply Real.log_nonneg
    exact_mod_cast hchooseOneNat
  have hlogR : 0 ≤ logR := by
    dsimp [logR]
    apply Real.log_nonneg
    exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 32) hr)
  have hcomparison := log_choose_le_two_mul_k_log_sparseRatio hk hkn hr
  have hmul := mul_le_mul_of_nonneg_left hcomparison
    (mul_nonneg (Nat.cast_nonneg n) (Nat.cast_nonneg T))
  have htarget : 0 ≤ target := by
    dsimp [target]
    positivity
  have hreference : 0 ≤ reference := by
    dsimp [reference]
    positivity
  have hinside : target ≤ 4 * reference := by
    dsimp [target, reference, logChoose, logR]
    nlinarith
  have hsqrt : Real.sqrt target ≤ 2 * Real.sqrt reference := by
    calc
      Real.sqrt target ≤ Real.sqrt (4 * reference) :=
        Real.sqrt_le_sqrt hinside
      _ = 2 * Real.sqrt reference := by
        rw [Real.sqrt_mul (by norm_num : (0 : Real) ≤ 4)]
        have hsqrtFour : Real.sqrt (4 : Real) = 2 := by
          rw [show (4 : Real) = (2 : Real) ^ 2 by norm_num,
            Real.sqrt_sq_eq_abs]
          norm_num
        rw [hsqrtFour]
  have hscale : 0 ≤ Real.sqrt sparseRho / 16 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left hsqrt hscale
  have hratio := sparseEta_mul_T0_ge_logRatio hk hr hT
  dsimp [target, reference, logChoose, logR] at hscaled
  calc
    Real.sqrt sparseRho / 16 *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)) ≤
      Real.sqrt sparseRho / 8 *
        Real.sqrt ((n : Real) * (k : Real) * (T : Real) *
          Real.log (sparseRatio n k : Real)) := by
        nlinarith
    _ ≤ sparseEta n k T * (sparseT0 n k T : Real) := hratio

/-- Combining the changed-score drift, the learner score bias, and the average
TV penalty yields the manuscript's `a k T0/4` mean. -/
theorem sparse_mean_combination
    {k T0 drift bias tvPenalty gammaMean : Real}
    (hk : 0 ≤ k) (hT0 : 0 ≤ T0)
    (hdrift : sparseA / 3 * k * T0 ≤ drift)
    (hbias : -(48 * Real.sqrt sparseRho * k * T0) ≤ bias)
    (htv : tvPenalty ≤ (1 / (2 : Real) ^ 15) * k * T0)
    (hgamma : drift + bias - tvPenalty ≤ gammaMean) :
    sparseA / 4 * k * T0 ≤ gammaMean := by
  have herror := sparse_error_budget_lt.le
  have hprod :
      (48 * Real.sqrt sparseRho + 1 / (2 : Real) ^ 15) * (k * T0) ≤
        (sparseA / 12) * (k * T0) :=
    mul_le_mul_of_nonneg_right herror (mul_nonneg hk hT0)
  calc
    sparseA / 4 * k * T0 =
        sparseA / 3 * k * T0 - (sparseA / 12) * (k * T0) := by ring
    _ ≤ sparseA / 3 * k * T0 -
        (48 * Real.sqrt sparseRho + 1 / (2 : Real) ^ 15) * (k * T0) := by
      linarith
    _ = sparseA / 3 * k * T0 -
        48 * Real.sqrt sparseRho * k * T0 -
          (1 / (2 : Real) ^ 15) * k * T0 := by ring
    _ ≤ drift + bias - tvPenalty := by linarith
    _ ≤ gammaMean := hgamma

/-- The pathwise cancellation of `k` when the score event is inserted into
the regret identity. -/
theorem sparse_score_event_implies_regret_eta
    {k T0 eta gamma regret : Real}
    (hk : 0 < k) (heta : 0 ≤ eta)
    (hgamma : sparseA / 8 * k * T0 ≤ gamma)
    (hregret : eta / k * gamma ≤ regret) :
    sparseA * eta * T0 / 8 ≤ regret := by
  have hscale : 0 ≤ eta / k := div_nonneg heta hk.le
  calc
    sparseA * eta * T0 / 8 =
        eta / k * (sparseA / 8 * k * T0) := by field_simp
    _ ≤ eta / k * gamma := mul_le_mul_of_nonneg_left hgamma hscale
    _ ≤ regret := hregret

/-- Substitution of `a=2^-6` and `sqrt(rho)=2^-18` in the final sparse regret
threshold. -/
theorem sparse_eta_threshold_implies_two_neg_31
    {etaT0 complexity : Real}
    (hetaT0 : Real.sqrt sparseRho / 16 * Real.sqrt complexity ≤ etaT0) :
    (1 / (2 : Real) ^ 31) * Real.sqrt complexity ≤
      sparseA * etaT0 / 8 := by
  have ha : 0 ≤ sparseA / 8 := by norm_num [sparseA]
  have hmul := mul_le_mul_of_nonneg_left hetaT0 ha
  rw [sparseSqrtRho_eq] at hmul
  calc
    (1 / (2 : Real) ^ 31) * Real.sqrt complexity =
        sparseA / 8 *
          ((1 / (2 : Real) ^ 18) / 16 * Real.sqrt complexity) := by
      norm_num [sparseA]
      ring
    _ ≤ sparseA / 8 * etaT0 := hmul
    _ = sparseA * etaT0 / 8 := by ring

/-- The sparse construction is stronger than the common action-count
constants used after the sparse/dense case split. -/
theorem sparse_tail_implies_actionCountTail
    {n k T : Nat} (hkn : k ≤ n) (P : Policy n k)
    (h : HasRegretLowerTail hkn P T
      ((1 / (2 : Real) ^ 31) *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)))
      (1 / (2 : Real) ^ 10)) :
    HasRegretLowerTail hkn P T
      (actionCountConstant *
        Real.sqrt ((n : Real) * (T : Real) *
          Real.log (n.choose k : Real)))
      actionCountProbability := by
  apply h.mono
  · have hsqrt : 0 ≤ Real.sqrt ((n : Real) * (T : Real) *
        Real.log (n.choose k : Real)) := Real.sqrt_nonneg _
    apply mul_le_mul_of_nonneg_right _ hsqrt
    norm_num [actionCountConstant]
  · norm_num [actionCountProbability]

#print axioms sparse_error_budget_lt
#print axioms sparseEta_mul_T0_sq_identity
#print axioms sparseSignalCount_ge_half
#print axioms sparseBlockCount_ge_half_log
#print axioms sparseEta_mul_T0_ge_logRatio
#print axioms log_choose_le_mul_actionCountLog
#print axioms actionCountLog_le_two_log_sparseRatio
#print axioms log_choose_le_two_mul_k_log_sparseRatio
#print axioms sparseEta_mul_T0_ge_logChoose
#print axioms sparse_mean_combination
#print axioms sparse_score_event_implies_regret_eta
#print axioms sparse_eta_threshold_implies_two_neg_31
#print axioms sparse_tail_implies_actionCountTail

end

end MsetsLower.Lower.Sparse
