import CoefficientOne.Sampling.StoppedVariation

/-! # Joint measurability of the actual histories and first terminal state -/

open MeasureTheory
namespace CoefficientOne.Sampling
noncomputable section

theorem measurable_historySelected_joint {n : ℕ} (k ℓ : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × Seed n => historySelected z.1 k ℓ z.2) := by
  simp_rw [historySelected_eq_output_inter]
  have htake : Measurable (fun z : (Fin n → ℝ) × Seed n =>
      ((List.ofFn z.2.1).take ℓ).toFinset) :=
    (measurable_of_finite (fun π : Equiv.Perm (Fin n) =>
      ((List.ofFn π).take ℓ).toFinset)).comp (measurable_fst.comp measurable_snd)
  exact (measurable_of_finite (fun p : Finset (Fin n) × Finset (Fin n) => p.1 ∩ p.2)).comp
    ((measurable_sequentialSampler k).prodMk htake)

theorem measurable_historyRemaining_joint {n : ℕ} (ℓ : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × Seed n => historyRemaining ℓ z.2) :=
  (measurable_of_finite (fun π : Equiv.Perm (Fin n) =>
    ((List.ofFn π).drop ℓ).toFinset)).comp (measurable_fst.comp measurable_snd)

theorem measurable_historyQuota_joint {n : ℕ} (k ℓ : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × Seed n => historyQuota z.1 k ℓ z.2) :=
  (measurable_of_finite (fun S : Finset (Fin n) => k - S.card)).comp
    (measurable_historySelected_joint k ℓ)

theorem measurable_samplerHistoryState_joint {n : ℕ} (k ℓ : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × Seed n => samplerHistoryState z.1 k ℓ z.2) :=
  (measurable_historyRemaining_joint ℓ).prodMk (measurable_historyQuota_joint k ℓ)

theorem measurable_historyTrajectory_joint {n : ℕ} (k : ℕ) :
    Measurable (fun z : (Fin n → ℝ) × Seed n =>
      fun ℓ : ℕ => (historySelected z.1 k ℓ z.2, samplerHistoryState z.1 k ℓ z.2)) := by
  apply measurable_pi_iff.mpr
  intro ℓ
  exact (measurable_historySelected_joint k ℓ).prodMk
    (measurable_samplerHistoryState_joint k ℓ)

theorem measurableSet_historyTerminal_joint {n : ℕ} (k ℓ : ℕ) :
    MeasurableSet {z : (Fin n → ℝ) × Seed n | HistoryTerminal z.1 k ℓ z.2} := by
  have hcard : Measurable (fun z : (Fin n → ℝ) × Seed n =>
      (historyRemaining ℓ z.2).card) :=
    (measurable_of_finite (fun S : Finset (Fin n) => S.card)).comp
      (measurable_historyRemaining_joint ℓ)
  exact (measurableSet_eq_fun (measurable_historyQuota_joint k ℓ) measurable_const).union
    (measurableSet_eq_fun (measurable_historyQuota_joint k ℓ) hcard)

theorem measurable_samplerTerminalTime_joint {n : ℕ} (k : ℕ) (hk : k ≤ n) :
    Measurable (fun z : (Fin n → ℝ) × Seed n => samplerTerminalTime z.1 k hk z.2) := by
  exact measurable_find
    (fun z : (Fin n → ℝ) × Seed n => ⟨n, historyTerminal_last z.1 k hk z.2⟩)
    (measurableSet_historyTerminal_joint k)

end
end CoefficientOne.Sampling
