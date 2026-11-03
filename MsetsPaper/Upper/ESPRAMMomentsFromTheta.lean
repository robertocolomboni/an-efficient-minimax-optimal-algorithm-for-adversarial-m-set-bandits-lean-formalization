import MsetsPaper.Upper.ESPRAMMoments
import MsetsPaper.Upper.SamplerRAMCache

/-! L9 moment routines from the actual parameter vector. The exponential
weights are built once. Both their construction and the original theta buffer
are included in the operational bounds, not hidden behind a weight oracle.
-/

noncomputable section

namespace MsetsPaper.Upper.RAMPrograms

variable {d m : ℕ}

def momentTableFromThetaRAM (theta : Array ℝ) (d m : ℕ) : MomentBatchResult :=
  let weights := weightsRAM theta d
  let run := momentTableRAM weights.value d m
  ⟨run.values, weights.work + run.work + 3, weights.allocated + run.allocated + 5,
    max (theta.size + weights.allocated + 10) (theta.size + run.peak + 10)⟩

theorem momentTableFromThetaRAM_values (theta : Array ℝ) (d m : ℕ) (hm : 1 ≤ m) :
    (momentTableFromThetaRAM theta d m).values =
      (espMatrixCells d).map (fun ij => secondMoment
        (weightedLaw (m := m) (fun i : Fin d => theta[i.val]?.getD 0)) ij.1 ij.2) := by
  exact momentTableRAM_values (fun i : Fin d => theta[i.val]?.getD 0)
    (weightsRAM theta d).value (weightsRAM_values theta d) hm

theorem momentTableFromThetaRAM_length (theta : Array ℝ) (d m : ℕ) :
    (momentTableFromThetaRAM theta d m).values.length = d * d :=
  momentTableRAM_length (weightsRAM theta d).value d m

/-- The diagonal entries of this same computed table are the actual marginals;
the premise only identifies the row-major job at the requested list position. -/
theorem momentTableFromThetaRAM_diagonal (theta : Array ℝ) (d m : ℕ)
    (hm : 1 ≤ m) (i : Fin d) (k : ℕ)
    (hdiag : (espMatrixCells d)[k]? = some (i, i)) :
    (momentTableFromThetaRAM theta d m).values[k]? =
      some (weightedMarginal (m := m) (fun j : Fin d => theta[j.val]?.getD 0) i) := by
  rw [momentTableFromThetaRAM_values theta d m hm, List.getElem?_map, hdiag]
  simp only [Option.map_some, secondMoment_diagonal_eq_marginal]

theorem momentTableFromThetaRAM_work (theta : Array ℝ) (d m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentTableFromThetaRAM theta d m).work ≤ 400 * d ^ 3 * m := by
  have hw := (weightsRAM_bounds theta d).1
  have hr := momentTableRAM_work (weightsRAM theta d).value d m hd hm
  have hd2 : 1 ≤ d ^ 2 := by nlinarith
  have hdm : d ≤ d * m := by nlinarith
  have hbig : d ≤ d ^ 3 * m := by nlinarith
  dsimp only [momentTableFromThetaRAM]
  nlinarith

theorem momentTableFromThetaRAM_peak (theta : Array ℝ) (hsize : theta.size = d)
    (m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentTableFromThetaRAM theta d m).peak ≤ 400 * (d * m + d ^ 2 + 1) := by
  have hw := (weightsRAM_bounds theta d).2
  have hr := momentTableRAM_peak (weightsRAM theta d).value (weightsRAM_size theta d) m hd hm
  have hdm : d ≤ d * m := by nlinarith
  dsimp only [momentTableFromThetaRAM]
  rw [hsize]
  apply max_le <;> nlinarith

theorem momentTableFromThetaRAM_peak_order (theta : Array ℝ) (hsize : theta.size = d)
    (m : ℕ) (hd : 1 ≤ d) (hm : 1 ≤ m) :
    (momentTableFromThetaRAM theta d m).peak ≤ 800 * (d * m + d ^ 2) := by
  have h := momentTableFromThetaRAM_peak theta hsize m hd hm
  have hdm : 1 ≤ d * m := by nlinarith
  omega

end MsetsPaper.Upper.RAMPrograms
