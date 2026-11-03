import MsetsLower.Lower.Sparse.TableChange
import MsetsLower.Lower.Sparse.PositiveDrift

/-!
# The concrete diagonal likelihood bound

This file discharges the pathwise energy premise of the full-table change of
measure with the literal sparse parameter family.  The key deterministic
fact is that one coordinate can be pulled actively at most `c0` times in
each of the `B` blocks.
-/

set_option linter.style.header false

namespace MsetsLower.Lower.Sparse

open MsetsLower Feedback MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal ProbabilityTheory

noncomputable section

/-! ## The per-coordinate active-pull budget -/

/-- The real-valued within-block counter is always the cast of a natural
number.  This is the discrete fact needed at the strict cutoff `C<c0`. -/
theorem sparseBlockSelectedCount_eq_natCast
    {n k q : Nat} (i : Fin n) : forall t (h : History n k t),
    exists m : Nat, sparseBlockSelectedCount q i t h = (m : Real) := by
  intro t
  induction t with
  | zero =>
      intro h
      exact ⟨0, by simp⟩
  | succ t ih =>
      intro h
      by_cases hblock : t / q = (t + 1) / q
      · rcases ih h.1 with ⟨m, hm⟩
        by_cases hselected : i ∈ h.2.1.1
        · refine ⟨m + 1, ?_⟩
          rw [sparseBlockSelectedCount_succ, if_pos hblock, hm]
          simp [History.selectedIndicator, hselected]
        · refine ⟨m, ?_⟩
          rw [sparseBlockSelectedCount_succ, if_pos hblock, hm]
          simp [History.selectedIndicator, hselected]
      · refine ⟨0, ?_⟩
        rw [sparseBlockSelectedCount_succ, if_neg hblock]
        norm_num

/-- Capping a natural counter and then accepting one more pull is exactly
the same as incrementing first and capping afterwards. -/
private theorem min_natCast_add_active (m c : Nat) :
    min (c : Real) (m : Real) +
        (if (m : Real) < (c : Real) then 1 else 0) =
      min (c : Real) ((m : Real) + 1) := by
  by_cases hmc : (m : Real) < (c : Real)
  · have hmcNat : m < c := by exact_mod_cast hmc
    have hsuccNat : m + 1 <= c := by omega
    have hsucc : (m : Real) + 1 <= (c : Real) := by exact_mod_cast hsuccNat
    rw [if_pos hmc, min_eq_right hmc.le, min_eq_right hsucc]
  · have hcm : (c : Real) <= (m : Real) := le_of_not_gt hmc
    rw [if_neg hmc, min_eq_left hcm,
      min_eq_left (hcm.trans (by linarith))]
    norm_num

/-- A convenient ceiling invariant for the cumulative active pulls.  The
completed blocks cost `c0` each; the last term is the capped counter in the
current block. -/
theorem sparseObservablePullCount_le_completedBlocks_add
    {n n' k q c0 : Nat} (hq : 0 < q) (hn' : n' <= n)
    (j : Fin n') : forall T (h : History n k T),
    sparseObservablePullCount hn' q c0 j T h <=
      (c0 : Real) * (T / q : Nat) +
        min (c0 : Real)
          (sparseBlockSelectedCount q
            (sparseSignalCoordinate hn' j) T h) := by
  intro T
  induction T with
  | zero =>
      intro h
      simp [sparseObservablePullCount]
  | succ t ih =>
      intro h
      let i := sparseSignalCoordinate hn' j
      let C := sparseBlockSelectedCount q i t h.1
      have hCnat := sparseBlockSelectedCount_eq_natCast
        (q := q) i t h.1
      rcases hCnat with ⟨m, hm⟩
      have hCm : C = (m : Real) := by simpa [C] using hm
      have hpull : sparsePullIndicator hn' q c0 j t h.1 h.2.1 =
          (if C < (c0 : Real) then 1 else 0) *
            History.selectedIndicator i h.2.1 := by rfl
      have hmin :
          min (c0 : Real) C +
              (if C < (c0 : Real) then 1 else 0) =
            min (c0 : Real) (C + 1) := by
        simpa [hCm] using min_natCast_add_active m c0
      by_cases hselected : i ∈ h.2.1.1
      have hs : History.selectedIndicator i h.2.1 = (1 : Real) := by
        simp [History.selectedIndicator, hselected]
      by_cases hblock : t / q = (t + 1) / q
      · have hcount : sparseBlockSelectedCount q i (t + 1) h =
            C + History.selectedIndicator i h.2.1 := by
          rw [sparseBlockSelectedCount_succ, if_pos hblock]
        have hcount' : sparseBlockSelectedCount q i (t + 1) h = C + 1 := by
          simpa [hs] using hcount
        rw [sparseObservablePullCount_succ, hpull, hs, mul_one,
          hcount', <- hblock]
        have hprev : sparseObservablePullCount hn' q c0 j t h.1 <=
            (c0 : Real) * (t / q : Nat) + min (c0 : Real) C := by
          simpa [i, C] using ih h.1
        linarith
      · have hquot : (t + 1) / q = t / q + 1 := by
          rw [Nat.succ_div]
          by_cases hdvd : q ∣ t + 1
          · simp [hdvd]
          · exfalso
            apply hblock
            simp [Nat.succ_div, hdvd]
        have hcount : sparseBlockSelectedCount q i (t + 1) h = 0 := by
          rw [sparseBlockSelectedCount_succ, if_neg hblock]
        have hcap :
            min (c0 : Real) C +
                (if C < (c0 : Real) then 1 else 0) <=
              (c0 : Real) := by
          rw [hmin]
          exact min_le_left _ _
        rw [sparseObservablePullCount_succ, hpull, hs, mul_one, hcount, hquot]
        have hprev : sparseObservablePullCount hn' q c0 j t h.1 <=
            (c0 : Real) * (t / q : Nat) + min (c0 : Real) C := by
          simpa [i, C] using ih h.1
        rw [min_eq_right (Nat.cast_nonneg c0)]
        push_cast
        linarith
      · have hs : History.selectedIndicator i h.2.1 = (0 : Real) := by
          simp [History.selectedIndicator, hselected]
        by_cases hblock : t / q = (t + 1) / q
        · have hcount : sparseBlockSelectedCount q i (t + 1) h = C := by
            rw [sparseBlockSelectedCount_succ, if_pos hblock, hs, add_zero]
          rw [sparseObservablePullCount_succ, hpull, hs, mul_zero, add_zero,
            hcount, <- hblock]
          simpa [i, C] using ih h.1
        · have hdivle : t / q <= (t + 1) / q :=
            Nat.div_le_div_right (by omega)
          have hdivlt : t / q < (t + 1) / q :=
            lt_of_le_of_ne hdivle hblock
          have hcount : sparseBlockSelectedCount q i (t + 1) h = 0 := by
            rw [sparseBlockSelectedCount_succ, if_neg hblock]
          rw [sparseObservablePullCount_succ, hpull, hs, mul_zero, add_zero,
            hcount]
          have hprev : sparseObservablePullCount hn' q c0 j t h.1 <=
              (c0 : Real) * (t / q : Nat) + min (c0 : Real) C := by
            simpa [i, C] using ih h.1
          have hminle : min (c0 : Real) C <= (c0 : Real) := min_le_left _ _
          have hquot : t / q + 1 <= (t + 1) / q := by omega
          have hc0 : 0 <= (c0 : Real) := Nat.cast_nonneg _
          have hmul : (c0 : Real) * ((t / q : Nat) + 1) <=
              (c0 : Real) * ((t + 1) / q : Nat) := by
            exact mul_le_mul_of_nonneg_left (by exact_mod_cast hquot) hc0
          have hzero : min (c0 : Real) 0 = 0 := by simp [hc0]
          rw [hzero]
          push_cast at hmul ⊢
          nlinarith

/-- If `t<T0=qB`, then the table index actually read at round `t` is one
of the genuine hidden rows. -/
theorem sparse_block_index_lt
    {q B t : Nat} (ht : t < q * B) : t / q < B := by
  have hq : 0 < q := by
    by_contra hq0
    have : q = 0 := Nat.eq_zero_of_not_pos hq0
    simp [this] at ht
  exact (Nat.div_lt_iff_lt_mul hq).2 (by simpa [Nat.mul_comm] using ht)

private theorem sparseObservablePullCount_eq_zero_of_horizon_eq_zero
    {n n' k q c0 T : Nat} (hn' : n' <= n) (j : Fin n')
    (hT : T = 0) (h : History n k T) :
    sparseObservablePullCount hn' q c0 j T h = 0 := by
  subst T
  rfl

/-- At a positive-length block boundary the within-block counter has just
been reset. -/
theorem sparseBlockSelectedCount_eq_zero_of_mod_eq_zero
    {n k q T : Nat} (hq : 0 < q) (i : Fin n)
    (h : History n k T) (hmod : T % q = 0) :
    sparseBlockSelectedCount q i T h = 0 := by
  cases T with
  | zero => rfl
  | succ t =>
      rw [sparseBlockSelectedCount_succ]
      have hdvd : q ∣ t + 1 := Nat.dvd_iff_mod_eq_zero.2 hmod
      have hquot : (t + 1) / q = t / q + 1 := by
        simp [Nat.succ_div, hdvd]
      rw [if_neg (by omega)]

/-- Pathwise, each signal coordinate has at most `B*c0` active pulls during
the literal active horizon `T0=qB`. -/
theorem sparseObservablePullCount_le_blockBudget
    {n n' k q c0 B : Nat} (hn' : n' <= n) (j : Fin n')
    (h : History n k (q * B)) :
    sparseObservablePullCount hn' q c0 j (q * B) h <=
      ((B * c0 : Nat) : Real) := by
  by_cases hq : q = 0
  · subst q
    rw [sparseObservablePullCount_eq_zero_of_horizon_eq_zero
      hn' j (by omega) h]
    positivity
  · have hqpos : 0 < q := Nat.pos_of_ne_zero hq
    have hbound := sparseObservablePullCount_le_completedBlocks_add
      (q := q) (c0 := c0)
      hqpos hn' j (q * B) h
    have hdiv : q * B / q = B := by
      simpa [Nat.mul_comm] using Nat.mul_div_left B hqpos
    have hcount : sparseBlockSelectedCount q
        (sparseSignalCoordinate hn' j) (q * B) h = 0 := by
      apply sparseBlockSelectedCount_eq_zero_of_mod_eq_zero hqpos
      simp
    rw [hdiv, hcount] at hbound
    norm_num at hbound
    simpa [Nat.cast_mul, mul_comm] using hbound

/-! ## The concrete full-table energy budget -/

/-- A feedback parameter at round `t` only reads row `t/q` of its hidden
table. -/
theorem sparseFeedbackParameter_congr_currentBlock
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

/-- Exact one-round energy of the genuine hidden-table family under a
single-column transformation.  The hypothesis `t<qB` is used precisely to
justify reading the transformed finite table. -/
theorem sparseHiddenTableParameterFamily_roundEnergy_eq
    {n n' k q c0 B t : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    (j : Fin n') (table : SparseHiddenTable B n)
    (h : History n k t) (A : MSetAction n k) (ht : t < q * B) :
    sparseRoundEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table))
        t (h, A) =
      (a * eta / (k : Real)) ^ 2 *
        sparsePullIndicator hn' q c0 j t h A ^ 2 *
          Feedback.shape
            (sparseHiddenTableU table (t / q)
              (sparseSignalCoordinate hn' j)) ^ 2 := by
  let transformed := sparseHiddenTableCoordinateEquiv B n a ha
    (sparseSignalCoordinate hn' j) table
  have hb : t / q < B := sparse_block_index_lt ht
  have hread : forall i,
      sparseHiddenTableU transformed (t / q) i =
        sparseTransformTableCoordinate a hn'
          (sparseHiddenTableU table) j (t / q) i := by
    intro i
    exact sparseHiddenTableU_coordinateEquiv_of_lt
      a ha hn' j table hb i
  have hparameter :
      sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU transformed) t h A =
        sparseFeedbackParameter eta n' q c0
          (sparseTransformTableCoordinate a hn'
            (sparseHiddenTableU table) j) t h A :=
    sparseFeedbackParameter_congr_currentBlock eta t hread h A
  have hdelta := sparseFeedbackParameter_transform_coordinate_sub
    (q := q) (c0 := c0) a eta hn' (sparseHiddenTableU table) j t h A
  unfold sparseRoundEnergy
  change
    (sparseFeedbackParameter eta n' q c0 (sparseHiddenTableU table) t h A -
      sparseFeedbackParameter eta n' q c0
        (sparseHiddenTableU transformed) t h A) ^ 2 = _
  rw [hparameter]
  rw [show sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU table) t h A -
        sparseFeedbackParameter eta n' q c0
          (sparseTransformTableCoordinate a hn'
            (sparseHiddenTableU table) j) t h A =
      -(sparseFeedbackParameter eta n' q c0
          (sparseTransformTableCoordinate a hn'
            (sparseHiddenTableU table) j) t h A -
        sparseFeedbackParameter eta n' q c0
          (sparseHiddenTableU table) t h A) by ring,
    hdelta]
  ring

/-- The one-round energy is bounded by the active-pull indicator itself. -/
theorem sparseHiddenTableParameterFamily_roundEnergy_le_pull
    {n n' k q c0 B t : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    (j : Fin n') (table : SparseHiddenTable B n)
    (h : History n k t) (A : MSetAction n k) (ht : t < q * B) :
    sparseRoundEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table))
        t (h, A) <=
      (a * eta / (k : Real)) ^ 2 *
        sparsePullIndicator hn' q c0 j t h A := by
  rw [sparseHiddenTableParameterFamily_roundEnergy_eq
    hk eta heta0 heta a ha hn' j table h A ht,
    sparsePullIndicator_eq_indicator]
  by_cases hj : j ∈ sparseActiveSelectedSignals hn' q c0 t h A
  · rw [if_pos hj]
    simp only [one_pow, mul_one]
    have hx := sparseHiddenTableU_abs_le_one table (t / q)
      (sparseSignalCoordinate hn' j)
    have hg := Feedback.shape_mem_Icc ((abs_le).1 hx)
    have hgsq : Feedback.shape
        (sparseHiddenTableU table (t / q)
          (sparseSignalCoordinate hn' j)) ^ 2 <= 1 := by
      nlinarith [mul_nonneg hg.1 (sub_nonneg.mpr hg.2)]
    have hmul := mul_le_mul_of_nonneg_left hgsq
      (sq_nonneg (a * eta / (k : Real)))
    simpa using hmul
  · rw [if_neg hj]
    norm_num

/-- Up to any prefix of `T0=qB`, the cumulative energy is the squared
perturbation scale times the active-pull count. -/
theorem sparseHiddenTableParameterFamily_energy_le_pullCount
    {n n' k q c0 B : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    (j : Fin n') (table : SparseHiddenTable B n) : forall T
    (h : History n k T), T <= q * B ->
    sparseCumulativeEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table))
        T h <=
      (a * eta / (k : Real)) ^ 2 *
        sparseObservablePullCount hn' q c0 j T h := by
  intro T
  induction T with
  | zero =>
      intro h _
      simp [sparseCumulativeEnergy, sparseObservablePullCount]
  | succ t ih =>
      intro h hT
      have ht : t < q * B := by omega
      rw [sparseCumulativeEnergy, sparseObservablePullCount_succ]
      calc
        sparseCumulativeEnergy
              ((sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B).at table)
              ((sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B).at
                (sparseHiddenTableCoordinateEquiv B n a ha
                  (sparseSignalCoordinate hn' j) table)) t h.1 +
            sparseRoundEnergy
              ((sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B).at table)
              ((sparseHiddenTableParameterFamily hk eta heta0 heta
                n' q c0 B).at
                (sparseHiddenTableCoordinateEquiv B n a ha
                  (sparseSignalCoordinate hn' j) table)) t (h.1, h.2.1) <=
          (a * eta / (k : Real)) ^ 2 *
              sparseObservablePullCount hn' q c0 j t h.1 +
            (a * eta / (k : Real)) ^ 2 *
              sparsePullIndicator hn' q c0 j t h.1 h.2.1 := by
          exact add_le_add (ih h.1 (by omega))
            (sparseHiddenTableParameterFamily_roundEnergy_le_pull
              hk eta heta0 heta a ha hn' j table h.1 h.2.1 ht)
        _ = (a * eta / (k : Real)) ^ 2 *
            (sparseObservablePullCount hn' q c0 j t h.1 +
              sparsePullIndicator hn' q c0 j t h.1 h.2.1) := by ring

/-- The literal `B*c0` pathwise energy bound for the true hidden-table
parameter family. -/
theorem sparseHiddenTableParameterFamily_energy_le_blockBudget
    {n n' k q c0 B : Nat} (hk : 1 <= k)
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (a : Real) (ha : |a| <= (1 : Real) / 8) (hn' : n' <= n)
    (j : Fin n') (table : SparseHiddenTable B n)
    (h : History n k (q * B)) :
    sparseCumulativeEnergy
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          table)
        ((sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B).at
          (sparseHiddenTableCoordinateEquiv B n a ha
            (sparseSignalCoordinate hn' j) table))
        (q * B) h <=
      (a * eta / (k : Real)) ^ 2 * ((B * c0 : Nat) : Real) := by
  calc
    _ <= (a * eta / (k : Real)) ^ 2 *
        sparseObservablePullCount hn' q c0 j (q * B) h :=
      sparseHiddenTableParameterFamily_energy_le_pullCount
        hk eta heta0 heta a ha hn' j table (q * B) h le_rfl
    _ <= (a * eta / (k : Real)) ^ 2 * ((B * c0 : Nat) : Real) :=
      mul_le_mul_of_nonneg_left
        (sparseObservablePullCount_le_blockBudget hn' j h) (sq_nonneg _)

/-! ## Manuscript parameters and the diagonal moment -/

/-- The actual hidden-table feedback family with all of the manuscript's
integer parameter choices substituted. -/
def sparseConcreteHiddenTableParameterFamily
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T) :
    SparseAdaptiveParameterFamily
      (SparseHiddenTable (sparseBlockCount n k) n) n k :=
  sparseHiddenTableParameterFamily hk (sparseEta n k T)
    (sparseEta_nonneg n k T)
    ((sparseEta_bounds hk hr hT).1.trans
      (sparseEta_bounds hk hr hT).2.le)
    (sparseSignalCount n k) (sparseQ n k T) (sparseC0 n k T)
    (sparseBlockCount n k)

/-- The perturbation scale times the literal `B*c0` pull budget is exactly
`a^2 rho B` for the manuscript's choice `eta=k sqrt(rho/c0)`. -/
theorem sparseEta_blockBudget_identity
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T) :
    (sparseA * sparseEta n k T / (k : Real)) ^ 2 *
        (((sparseBlockCount n k * sparseC0 n k T : Nat) : Real)) =
      sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) := by
  have hkposNat : 0 < k := lt_of_lt_of_le Nat.zero_lt_one hk
  have hkpos : 0 < (k : Real) := by exact_mod_cast hkposNat
  have hcNat := sparseC0_ge hk hr hT
  have hcposNat : 0 < sparseC0 n k T :=
    lt_of_lt_of_le (by positivity : 0 < 256 * k ^ 2) hcNat
  have hcpos : 0 < (sparseC0 n k T : Real) := by exact_mod_cast hcposNat
  have hquot : 0 <= sparseRho / (sparseC0 n k T : Real) :=
    div_nonneg sparseRho_pos.le hcpos.le
  rw [sparseEta]
  have hcancel :
      sparseA *
          ((k : Real) * Real.sqrt
            (sparseRho / (sparseC0 n k T : Real))) / (k : Real) =
        sparseA * Real.sqrt
          (sparseRho / (sparseC0 n k T : Real)) := by
    field_simp [ne_of_gt hkpos]
  rw [hcancel, mul_pow, Real.sq_sqrt hquot]
  push_cast
  field_simp [ne_of_gt hcpos]

/-- Concrete pathwise energy premise needed by the full-table diagonal
change of measure. -/
theorem sparseConcreteHiddenTableParameterFamily_energy_le
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (j : Fin (sparseSignalCount n k))
    (table : SparseHiddenTable (sparseBlockCount n k) n)
    (h : History n k (sparseT0 n k T)) :
    sparseCumulativeEnergy
        ((sparseConcreteHiddenTableParameterFamily hk hr hT).at table)
        ((sparseConcreteHiddenTableParameterFamily hk hr hT).at
          (sparseHiddenTableCoordinateEquiv (sparseBlockCount n k) n sparseA
            (by norm_num [sparseA])
            (sparseSignalCoordinate (sparseSignalCount_le n k) j) table))
        (sparseT0 n k T) h <=
      sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) := by
  have hraw := sparseHiddenTableParameterFamily_energy_le_blockBudget
    (q := sparseQ n k T) (c0 := sparseC0 n k T)
    (B := sparseBlockCount n k)
    hk (sparseEta n k T) (sparseEta_nonneg n k T)
    ((sparseEta_bounds hk hr hT).1.trans
      (sparseEta_bounds hk hr hT).2.le)
    sparseA (by norm_num [sparseA]) (sparseSignalCount_le n k) j table
    (by simpa [sparseT0] using h)
  change sparseCumulativeEnergy
      ((sparseConcreteHiddenTableParameterFamily hk hr hT).at table)
      ((sparseConcreteHiddenTableParameterFamily hk hr hT).at
        (sparseHiddenTableCoordinateEquiv (sparseBlockCount n k) n sparseA
          (by norm_num [sparseA])
          (sparseSignalCoordinate (sparseSignalCount_le n k) j) table))
      (sparseT0 n k T) h <= _
  calc
    _ <= (sparseA * sparseEta n k T / (k : Real)) ^ 2 *
        (((sparseBlockCount n k * sparseC0 n k T : Nat) : Real)) := by
      simpa [sparseConcreteHiddenTableParameterFamily, sparseT0] using hraw
    _ = sparseA ^ 2 * sparseRho * (sparseBlockCount n k : Real) :=
      sparseEta_blockBudget_identity hk hr hT

/-- The genuine full-table diagonal moment bound, with no abstract family or
energy premise left: this is `eq:lower-likelihood-diagonal` for every signal
coordinate `j : Fin n'`. -/
theorem lower_likelihood_diagonal_concreteFullTable
    {n k T : Nat} (hk : 1 <= k)
    (hr : 2 ^ 32 <= sparseRatio n k)
    (hT : 64 * (n : Real) * (k : Real) * actionCountLog n k <= T)
    (P : Policy n k) (j : Fin (sparseSignalCount n k)) :
    (∫⁻ z,
        sparseHiddenTableCoordinateJointLikelihood
            (sparseConcreteHiddenTableParameterFamily hk hr hT)
            sparseA (by norm_num [sparseA])
            (sparseSignalCoordinate (sparseSignalCount_le n k) j)
            (sparseT0 n k T) z ^ 2
      ∂sparseJointLaw
        (sparseHiddenTableMeasure (sparseBlockCount n k) n) P
        (sparseConcreteHiddenTableParameterFamily hk hr hT)
        (sparseT0 n k T)) <=
      ENNReal.ofReal
        (Real.exp (10 * sparseA ^ 2 * sparseBlockCount n k)) := by
  apply lower_likelihood_diagonal_fullTable P
    (sparseConcreteHiddenTableParameterFamily hk hr hT)
    sparseA sparseRho (by norm_num [sparseA])
    sparseRho_pos.le (by norm_num [sparseRho])
    (sparseSignalCoordinate (sparseSignalCount_le n k) j)
    (sparseT0 n k T)
  intro table h
  exact sparseConcreteHiddenTableParameterFamily_energy_le
    hk hr hT j table h

#print axioms sparseObservablePullCount_le_blockBudget
#print axioms sparseHiddenTableParameterFamily_energy_le_blockBudget
#print axioms sparseConcreteHiddenTableParameterFamily_energy_le
#print axioms lower_likelihood_diagonal_concreteFullTable

end

end MsetsLower.Lower.Sparse
