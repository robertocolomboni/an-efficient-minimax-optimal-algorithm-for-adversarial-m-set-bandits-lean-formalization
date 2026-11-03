import MsetsPaper.Lower.SparseCappedThreshold
import MsetsPaper.Lower.MainNewRouteArithmetic
import MsetsPaper.Alignment.UpperAlgorithm
import MsetsPaper.RateSynthesis

/-! Explicit symmetric entropy bounds for the unnumbered rate gloss.
These supplement the two-sided sparse-scale theorem; no asymptotic notation
is introduced and the actual upper-bound algorithm remains the same. -/

noncomputable section

namespace MsetsPaper.Alignment

open MsetsPaper.Lower MsetsLower MeasureTheory MsetsPaper.Upper

theorem log_choose_symmetric_bounds {d m : ℕ}
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) :
    let s := min m (d - m)
    (s : ℝ) * Real.log ((d : ℝ) / s) ≤ Real.log (d.choose m : ℝ) ∧
    Real.log (d.choose m : ℝ) ≤ (s : ℝ) * (1 + Real.log ((d : ℝ) / s)) := by
  let s := min m (d - m)
  have hs : 0 < s := (NewRoute.min_size_bounds hm hmtop).1
  have hsd : s ≤ d := (min_le_left m (d - m)).trans (by omega)
  have hsym := NewRoute.choose_min_size (show m ≤ d by omega)
  have hlo := SparseCapped.log_choose_ge_mul_log_div hs hsd
  have hhi := SparseCapped.log_choose_le_entropy hs hsd
  have hratio : 1 / SparseCapped.ratio d s = (d : ℝ) / s := by
    simp [SparseCapped.ratio, one_div, inv_div]
  rw [hratio] at hhi
  change (d.choose s : ℕ) = d.choose m at hsym
  rw [hsym] at hlo hhi
  exact ⟨hlo, hhi⟩

theorem regretRate_le_symmetric_entropy {d m T : ℕ} (delta : ℝ)
    (hm : 1 ≤ m) (hmtop : m ≤ d - 1) :
    let s := min m (d - m)
    regretRate d m T delta ≤ Real.sqrt ((d : ℝ) * T *
      ((s : ℝ) * (1 + Real.log ((d : ℝ) / s)) + Real.log (1 / delta))) := by
  unfold regretRate
  apply Real.sqrt_le_sqrt
  have h := mul_le_mul_of_nonneg_left (log_choose_symmetric_bounds hm hmtop).2
    (show (0 : ℝ) ≤ (d : ℝ) * T by positivity)
  nlinarith

/-- The actual high-probability theorem with the symmetric s=min(m,d-m)
rate displayed in the prose; this is a consequence, not a new algorithm. -/
theorem upper_main_regret_symmetric_entropy {d m : ℕ}
    (L : SignedLossProcess d m) (hm : 1 ≤ m) (hmtop : m ≤ d - 1)
    (T : ℕ) (hT : 0 < T) {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta < 1) :
    let s := min m (d - m)
    1 - delta ≤ (signedRunLaw (mainAlgorithm T delta (by omega)) L T).real
      {h | observableSignedRegret L T h ≤ 160 * Real.sqrt ((d : ℝ) * T *
        ((s : ℝ) * (1 + Real.log ((d : ℝ) / s)) + Real.log (1 / delta)))} := by
  apply (upper_main_regret L hm hmtop T hT hdelta hdelta1).trans
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro h hh
  exact hh.trans (mul_le_mul_of_nonneg_left
    (regretRate_le_symmetric_entropy delta hm hmtop) (by norm_num))

end MsetsPaper.Alignment
