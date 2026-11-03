import MsetsLower.Lower.ThresholdArithmetic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Parameters for the sparse action-count construction

This file formalizes the parameter choices at the beginning of
`prop:lower-sparse-action` (manuscript lines 4332--4391).  The floor operations
are literal natural floors, and the horizon hypothesis is the displayed
real-valued inequality `eq:lower-sparse-horizon`.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower.Lower

noncomputable section

/-- The fixed amplitude `a=2⁻⁶`. -/
def sparseA : Real := (2 : Real)⁻¹ ^ 6

/-- The fixed probability scale `rho=2⁻³⁶`. -/
def sparseRho : Real := (2 : Real)⁻¹ ^ 36

/-- The manuscript's `r=floor(n/k)`, represented by natural division. -/
def sparseRatio (n k : Nat) : Nat := n / k

/-- The number `n'=kr` of signal coordinates. -/
def sparseSignalCount (n k : Nat) : Nat := k * sparseRatio n k

/-- The number `B=floor(log r)` of blocks. -/
def sparseBlockCount (n k : Nat) : Nat :=
  ⌊Real.log (sparseRatio n k : Real)⌋₊

/-- The real block scale `x=T/(rB)`. -/
def sparseX (n k T : Nat) : Real :=
  (T : Real) /
    ((sparseRatio n k : Real) * (sparseBlockCount n k : Real))

/-- The integer sub-block length `ell=floor x`. -/
def sparseEll (n k T : Nat) : Nat := ⌊sparseX n k T⌋₊

/-- The block length `q=r ell`. -/
def sparseQ (n k T : Nat) : Nat :=
  sparseRatio n k * sparseEll n k T

/-- The active-pull cutoff `c0=8 ell`. -/
def sparseC0 (n k T : Nat) : Nat := 8 * sparseEll n k T

/-- The active construction horizon `T0=qB`. -/
def sparseT0 (n k T : Nat) : Nat :=
  sparseQ n k T * sparseBlockCount n k

/-- The perturbation size `eta=k sqrt(rho/c0)`. -/
def sparseEta (n k T : Nat) : Real :=
  (k : Real) * Real.sqrt (sparseRho / (sparseC0 n k T : Real))

theorem sparseEta_nonneg (n k T : Nat) : 0 ≤ sparseEta n k T := by
  exact mul_nonneg (Nat.cast_nonneg k) (Real.sqrt_nonneg _)

theorem sparseA_eq : sparseA = (1 : Real) / 64 := by
  norm_num [sparseA]

theorem sparseRho_eq : sparseRho = (1 : Real) / 2 ^ 36 := by
  norm_num [sparseRho]

theorem sparseRho_pos : 0 < sparseRho := by
  norm_num [sparseRho]

theorem sparseSignalCount_le (n k : Nat) :
    sparseSignalCount n k ≤ n := by
  simpa [sparseSignalCount, sparseRatio] using Nat.mul_div_le n k

theorem sparseSignalCount_ge {n k : Nat}
    (hr : 2 ^ 32 ≤ sparseRatio n k) :
    k ≤ sparseSignalCount n k := by
  have hrone : 1 ≤ sparseRatio n k :=
    (by norm_num : 1 ≤ 2 ^ 32).trans hr
  calc
    k = k * 1 := by simp
    _ ≤ k * sparseRatio n k := Nat.mul_le_mul_left k hrone
    _ = sparseSignalCount n k := rfl

/-- `r≥2^32` implies the manuscript's `B≥1`. -/
theorem sparseBlockCount_one_le {n k : Nat}
    (hr : 2 ^ 32 ≤ sparseRatio n k) :
    1 ≤ sparseBlockCount n k := by
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
  have hlogPower : (1 : Real) < 32 * Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogone : (1 : Real) ≤ Real.log (sparseRatio n k : Real) := by
    exact hlogPower.le.trans hlogmono
  exact (Nat.one_le_floor_iff (Real.log (sparseRatio n k : Real))).2 hlogone

private theorem sparseBlockCount_cast_le_log {n k : Nat}
    (hr : 2 ^ 32 ≤ sparseRatio n k) :
    (sparseBlockCount n k : Real) ≤
      Real.log (sparseRatio n k : Real) := by
  apply Nat.floor_le
  apply Real.log_nonneg
  exact_mod_cast (le_trans (by norm_num : 1 ≤ 2 ^ 32) hr)

/-- The comparison `B≤log(en/k)` used in the proof. -/
theorem sparseBlockCount_le_actionCountLog {n k : Nat}
    (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k) :
    (sparseBlockCount n k : Real) ≤ actionCountLog n k := by
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  have hratioPosNat : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hratioPos : 0 < (sparseRatio n k : Real) := by
    exact_mod_cast hratioPosNat
  have hmul : k * sparseRatio n k ≤ n :=
    sparseSignalCount_le n k
  have hratioLe :
      (sparseRatio n k : Real) ≤ (n : Real) / (k : Real) := by
    apply (le_div_iff₀ hkpos).2
    exact_mod_cast (show sparseRatio n k * k ≤ n by simpa [mul_comm] using hmul)
  have hexp : (1 : Real) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hnDivPos : 0 < (n : Real) / (k : Real) :=
    lt_of_lt_of_le hratioPos hratioLe
  have hargLe :
      (sparseRatio n k : Real) ≤
        Real.exp 1 * (n : Real) / (k : Real) := by
    calc
      (sparseRatio n k : Real) ≤ (n : Real) / (k : Real) := hratioLe
      _ = 1 * ((n : Real) / (k : Real)) := by ring
      _ ≤ Real.exp 1 * ((n : Real) / (k : Real)) :=
        mul_le_mul_of_nonneg_right hexp hnDivPos.le
      _ = Real.exp 1 * (n : Real) / (k : Real) := by ring
  have hlogLe :
      Real.log (sparseRatio n k : Real) ≤
        Real.log (Real.exp 1 * (n : Real) / (k : Real)) :=
    Real.strictMonoOn_log.monotoneOn hratioPos
      (show Real.exp 1 * (n : Real) / (k : Real) ∈ Set.Ioi 0 by
        have hnposNat : 0 < n :=
          lt_of_lt_of_le
            (Nat.mul_pos (lt_of_lt_of_le Nat.zero_lt_one hk) hratioPosNat) hmul
        have hnpos : 0 < (n : Real) := by exact_mod_cast hnposNat
        exact div_pos (mul_pos (Real.exp_pos 1) hnpos) hkpos) hargLe
  exact (sparseBlockCount_cast_le_log hr).trans hlogLe

/-- From the horizon bound, `x≥64 k²`. -/
theorem sparseX_ge {n k T : Nat}
    (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    64 * (k : Real) ^ 2 ≤ sparseX n k T := by
  have hrposNat : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hBposNat : 0 < sparseBlockCount n k :=
    sparseBlockCount_one_le hr
  have hrpos : 0 < (sparseRatio n k : Real) := by exact_mod_cast hrposNat
  have hBpos : 0 < (sparseBlockCount n k : Real) := by exact_mod_cast hBposNat
  have hk0 : 0 ≤ (k : Real) := Nat.cast_nonneg k
  have hkrnNat : k * sparseRatio n k ≤ n := sparseSignalCount_le n k
  have hkrn : (k : Real) * (sparseRatio n k : Real) ≤ n := by
    exact_mod_cast hkrnNat
  have hBlog := sparseBlockCount_le_actionCountLog hk hr
  have htarget :
      64 * (k : Real) ^ 2 *
          ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) ≤
        64 * (n : Real) * (k : Real) * actionCountLog n k := by
    have hleft :
        (k : Real) * (sparseRatio n k : Real) *
            (sparseBlockCount n k : Real) ≤
          (n : Real) * actionCountLog n k := by
      calc
        (k : Real) * (sparseRatio n k : Real) *
            (sparseBlockCount n k : Real) ≤
          (n : Real) * (sparseBlockCount n k : Real) :=
            mul_le_mul_of_nonneg_right hkrn hBpos.le
        _ ≤ (n : Real) * actionCountLog n k :=
          mul_le_mul_of_nonneg_left hBlog (Nat.cast_nonneg n)
    nlinarith
  apply (le_div_iff₀ (mul_pos hrpos hBpos)).2
  exact htarget.trans hT

/-- The floor loses at most a factor two: `ell≥x/2`. -/
theorem sparseEll_ge_half {n k T : Nat}
    (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    sparseX n k T / 2 ≤ (sparseEll n k T : Real) := by
  have hx := sparseX_ge hk hr hT
  have hkreal : (1 : Real) ≤ k := by exact_mod_cast hk
  have hx2 : 2 ≤ sparseX n k T := by nlinarith [sq_nonneg ((k : Real) - 1)]
  have hfloor : sparseX n k T - 1 < (sparseEll n k T : Real) := by
    exact Nat.sub_one_lt_floor _
  nlinarith

/-- The active horizon satisfies `T/2≤T0≤T`. -/
theorem sparseT0_bounds {n k T : Nat}
    (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    (T : Real) / 2 ≤ sparseT0 n k T ∧ sparseT0 n k T ≤ T := by
  have hrposNat : 0 < sparseRatio n k :=
    lt_of_lt_of_le (by norm_num) hr
  have hBposNat : 0 < sparseBlockCount n k := sparseBlockCount_one_le hr
  have hrpos : 0 < (sparseRatio n k : Real) := by exact_mod_cast hrposNat
  have hBpos : 0 < (sparseBlockCount n k : Real) := by exact_mod_cast hBposNat
  have hdenpos :
      0 < (sparseRatio n k : Real) * (sparseBlockCount n k : Real) :=
    mul_pos hrpos hBpos
  have hx0 : 0 ≤ sparseX n k T := by
    exact div_nonneg (Nat.cast_nonneg T) hdenpos.le
  have hellLe :
      (sparseEll n k T : Real) ≤ sparseX n k T := Nat.floor_le hx0
  have hellHalf := sparseEll_ge_half hk hr hT
  have hTformula :
      ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) *
          sparseX n k T = T := by
    rw [sparseX]
    exact mul_div_cancel₀ (T : Real) (ne_of_gt hdenpos)
  have hT0cast :
      (sparseT0 n k T : Real) =
        ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) *
          (sparseEll n k T : Real) := by
    simp [sparseT0, sparseQ]
    ring
  constructor
  · rw [hT0cast]
    calc
      (T : Real) / 2 =
          ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) *
            (sparseX n k T / 2) := by rw [← hTformula]; ring
      _ ≤ ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) *
            (sparseEll n k T : Real) :=
        mul_le_mul_of_nonneg_left hellHalf hdenpos.le
  · have hupperReal : (sparseT0 n k T : Real) ≤ (T : Real) := by
      rw [hT0cast]
      calc
        ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) *
            (sparseEll n k T : Real) ≤
          ((sparseRatio n k : Real) * (sparseBlockCount n k : Real)) *
            sparseX n k T := mul_le_mul_of_nonneg_left hellLe hdenpos.le
        _ = T := hTformula
    exact_mod_cast hupperReal

/-- The cutoff satisfies `c0≥256 k²`. -/
theorem sparseC0_ge {n k T : Nat}
    (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    256 * k ^ 2 ≤ sparseC0 n k T := by
  have hx := sparseX_ge hk hr hT
  have hell := sparseEll_ge_half hk hr hT
  have hreal : (256 : Real) * (k : Real) ^ 2 ≤
      (sparseC0 n k T : Real) := by
    simp only [sparseC0, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  exact_mod_cast hreal

/-- The perturbation bound `eta≤sqrt(rho)/16<1/16`. -/
theorem sparseEta_bounds {n k T : Nat}
    (hk : 1 ≤ k) (hr : 2 ^ 32 ≤ sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k ≤ T) :
    sparseEta n k T ≤ Real.sqrt sparseRho / 16 ∧
      Real.sqrt sparseRho / 16 < (1 : Real) / 16 := by
  have hcNat := sparseC0_ge hk hr hT
  have hkpos : 0 < (k : Real) := by exact_mod_cast hk
  have hcposNat : 0 < sparseC0 n k T :=
    lt_of_lt_of_le (by positivity : 0 < 256 * k ^ 2) hcNat
  have hcpos : 0 < (sparseC0 n k T : Real) := by exact_mod_cast hcposNat
  have hcReal : (256 : Real) * (k : Real) ^ 2 ≤
      (sparseC0 n k T : Real) := by exact_mod_cast hcNat
  have hsqrtC : (16 : Real) * k ≤ Real.sqrt (sparseC0 n k T : Real) := by
    have hnonneg : 0 ≤ (16 : Real) * k := by positivity
    calc
      (16 : Real) * k = Real.sqrt (((16 : Real) * k) ^ 2) := by
        rw [Real.sqrt_sq hnonneg]
      _ ≤ Real.sqrt (sparseC0 n k T : Real) :=
        Real.sqrt_le_sqrt (by nlinarith)
  have hsqrtCpos : 0 < Real.sqrt (sparseC0 n k T : Real) :=
    Real.sqrt_pos.2 hcpos
  have heta : sparseEta n k T ≤ Real.sqrt sparseRho / 16 := by
    rw [sparseEta,
      Real.sqrt_div (le_of_lt sparseRho_pos) (sparseC0 n k T : Real)]
    have hsqrtRho0 : 0 ≤ Real.sqrt sparseRho := Real.sqrt_nonneg _
    have hratio : (k : Real) / Real.sqrt (sparseC0 n k T : Real) ≤
        (1 : Real) / 16 := by
      apply (div_le_iff₀ hsqrtCpos).2
      nlinarith
    calc
      (k : Real) * (Real.sqrt sparseRho /
          Real.sqrt (sparseC0 n k T : Real)) =
          Real.sqrt sparseRho *
            ((k : Real) / Real.sqrt (sparseC0 n k T : Real)) := by ring
      _ ≤ Real.sqrt sparseRho * ((1 : Real) / 16) :=
        mul_le_mul_of_nonneg_left hratio hsqrtRho0
      _ = Real.sqrt sparseRho / 16 := by ring
  constructor
  · exact heta
  · apply (div_lt_div_iff_of_pos_right (by norm_num : (0 : Real) < 16)).2
    rw [Real.sqrt_lt (le_of_lt sparseRho_pos) (by norm_num : (0 : Real) ≤ 1)]
    norm_num [sparseRho]

#print axioms sparseBlockCount_one_le
#print axioms sparseX_ge
#print axioms sparseEll_ge_half
#print axioms sparseT0_bounds
#print axioms sparseC0_ge
#print axioms sparseEta_bounds

end

end MsetsLower.Lower.Sparse
