import MsetsLower.Lower.Sparse.EventFixing
import MsetsLower.Lower.Sparse.Truncation

/-!
# Fixing the sparse table at the original horizon

The probabilistic sparse construction is active for `T0` rounds and is zero
afterwards.  This file performs the fixing while retaining that concrete
zero-suffix witness, so the lower tail transfers from `T0` to the original
horizon `T` without weakening its probability or threshold.
-/

namespace MsetsLower.Lower.Sparse

open MsetsLower Set MeasureTheory ProbabilityTheory

noncomputable section

/-- A lower bound for the centered `Gamma` event at the active horizon fixes
one genuine auxiliary table and gives the same regret tail at every larger
horizon. -/
theorem lower_sparse_fixed_tail_at_larger_horizon_of_centeredGamma_event
    {n n' k r B T0 T : Nat} (P : Policy n k) (hk : 1 <= k)
    (hkn' : k <= n')
    (eta : Real) (heta0 : 0 <= eta) (heta : eta <= (1 : Real) / 16)
    (q c0 : Nat) (hn' : n' <= n) (hprod : n' = k * r) (hr : 0 < r)
    (sigma : Equiv.Perm (Fin n')) (hT0 : T0 <= T) (probability : Real)
    (hGammaProbability : probability <=
      (sparseJointLaw (sparseHiddenTableMeasure B n) (sparseCenteredPolicy P)
        (sparseHiddenTableParameterFamily hk eta heta0 heta n' q c0 B) T0).real
          (sparseCenteredGammaEvent hk eta heta0 heta q c0 hn'
            hprod hr sigma (sparseA / 8 * (k : Real) * (T0 : Real)))) :
    HasRegretLowerTail (hkn'.trans hn') P T
      (sparseA * eta * (T0 : Real) / 8) probability := by
  let L : ParametricLossProcess (SparseAuxTable B n T0) n k :=
    sparseTableLossProcess hk eta heta0 heta n' q c0 T0 B
  let mu : Measure (SparseAuxTable B n T0) := sparseAuxTableMeasure B n T0
  have htransfer := sparseAuxGammaEvent_measure_eq_centered
    (B := B) (T := T0)
    P hk eta heta0 heta q c0 hn' hprod hr sigma
      (sparseA / 8 * (k : Real) * (T0 : Real))
  have hGammaAux : probability <=
      (sparseAuxParametricJointMeasure P hk eta heta0 heta
        n' q c0 T0 B).real
        (sparseAuxGammaEvent hk eta heta0 heta q c0 hn' hprod hr sigma
          (sparseA / 8 * (k : Real) * (T0 : Real))) := by
    simpa [measureReal_def, htransfer] using hGammaProbability
  have haverage : probability <=
      ((parametricRunWithParameterKernel P L T0) ∘ₘ mu).real
        (parametricRegretEvent L T0
          (sparseA * eta * (T0 : Real) / 8)) := by
    change probability <=
      (sparseAuxParametricJointMeasure P hk eta heta0 heta
        n' q c0 T0 B).real
        (parametricRegretEvent L T0
          (sparseA * eta * (T0 : Real) / 8))
    exact hGammaAux.trans <|
      sparseAuxGammaEvent_measure_le_regretEvent
        P hk hkn' eta heta0 heta q c0 hn' hprod hr sigma
  obtain ⟨table, htable⟩ := exists_fixed_parametric_regret
    (hkn'.trans hn') mu P L T0 (sparseA * eta * (T0 : Real) / 8)
      probability haverage
  let extra := T - T0
  have hdecomp : T0 + extra = T := Nat.add_sub_of_le hT0
  refine ⟨L.at table, ?_⟩
  unfold regretTailProbability
  apply (ENNReal.ofReal_le_iff_le_toReal (measure_ne_top _ _)).2
  change probability <=
    (runLaw P (L.at table) T).real
      {h | sparseA * eta * (T0 : Real) / 8 <=
        pathRegret (L.at table) T h}
  rw [← hdecomp]
  have hsuffix := sparse_runLaw_add_regretTailProbability
    (hkn'.trans hn') P hk eta heta0 heta n' q c0 T0
      (sparseTableU table) (sparseTableU_abs_le_one table)
      (sparseTableZ table) (sparseTableZ_mem_Icc table)
      extra (sparseA * eta * (T0 : Real) / 8)
  have hLat : L.at table =
      sparseLossProcess hk eta heta0 heta n' q c0 T0
        (sparseTableU table) (sparseTableU_abs_le_one table)
        (sparseTableZ table) (sparseTableZ_mem_Icc table) := by
    dsimp [L]
    exact sparseTableLossProcess_at hk eta heta0 heta n' q c0 T0 B table
  rw [hLat]
  rw [hsuffix]
  simpa [L, hLat] using htable

#print axioms lower_sparse_fixed_tail_at_larger_horizon_of_centeredGamma_event

end

end MsetsLower.Lower.Sparse
