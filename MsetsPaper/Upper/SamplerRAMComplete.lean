import MsetsPaper.Upper.SamplerRAMCache

/-! End-to-end RAM sampler from a stored parameter array. All deterministic
preprocessing is performed by the program; no table-correctness or
distribution-equality certificate is supplied by its caller. Its output is
a nodup list of exactly m indices. Finset conversion appears only in the
mathematical specification, not in the counted computation. -/

namespace MsetsPaper.Upper.RAMPrograms
open ESPSampling
open scoped unitInterval
noncomputable section

theorem cachedSamplerRAM_output (theta : Array ℝ) (d m : ℕ)
    (u : Fin d → unitInterval) :
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.value.toFinset =
      (sampleMSet (fun i : Fin d => (realLoad theta i.val).value) m u).output := by
  simp only [cachedSamplerRAM, samplerCacheRAM_order, randomSamplerRAM_resource]
  exact samplerRAM_weighted_output _ _ _ m
    (samplerCacheRAM_weights theta d m) (samplerCacheRAM_rows theta d m) u

theorem cachedSamplerRAM_card (theta : Array ℝ) (d m : ℕ) (hmd : m ≤ d)
    (u : Fin d → unitInterval) :
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.value.length = m := by
  simp only [cachedSamplerRAM, samplerCacheRAM_order, randomSamplerRAM_resource]
  exact samplerRAM_weighted_card _ _ _ hmd
    (samplerCacheRAM_weights theta d m) (samplerCacheRAM_rows theta d m) u

theorem cachedSamplerRAM_nodup (theta : Array ℝ) (d m : ℕ)
    (u : Fin d → unitInterval) :
    (cachedSamplerRAM (samplerCacheRAM theta d m).value m u).1.value.Nodup := by
  simp only [cachedSamplerRAM, samplerCacheRAM_order, randomSamplerRAM_resource]
  exact samplerRAM_nodup _ _ _ _ d m 0 (by simp) (List.nodup_finRange d)

def samplerFromThetaRAM (theta : Array ℝ) (d m : ℕ) (u : Fin d → unitInterval) :
    ResourceRun (List (Fin d)) × ℕ :=
  let cache := samplerCacheRAM theta d m
  let sampled := cachedSamplerRAM cache.value m u
  (⟨sampled.1.value, cache.work + sampled.1.work + 2,
    cache.allocated + sampled.1.allocated + 2⟩, sampled.2)

theorem samplerFromThetaRAM_output (theta : Array ℝ) (d m : ℕ)
    (u : Fin d → unitInterval) :
    (samplerFromThetaRAM theta d m u).1.value.toFinset =
      (sampleMSet (fun i : Fin d => (realLoad theta i.val).value) m u).output :=
  cachedSamplerRAM_output theta d m u

theorem samplerFromThetaRAM_card_nodup (theta : Array ℝ) (d m : ℕ) (hmd : m ≤ d)
    (u : Fin d → unitInterval) :
    (samplerFromThetaRAM theta d m u).1.value.length = m ∧
    (samplerFromThetaRAM theta d m u).1.value.Nodup :=
  ⟨cachedSamplerRAM_card theta d m hmd u, cachedSamplerRAM_nodup theta d m u⟩

theorem samplerFromThetaRAM_probability (theta : Array ℝ) (d m : ℕ) (hmd : m ≤ d)
    (a : Action d m) :
    uniformCube (Fin d) {u | (samplerFromThetaRAM theta d m u).1.value.toFinset = a.val} =
      ENNReal.ofReal (weightedLaw (fun i : Fin d => (realLoad theta i.val).value) a) :=
  cachedSamplerRAM_probability theta d m hmd a

theorem samplerFromThetaRAM_linear (theta : Array ℝ) (d m : ℕ)
    (hd : 1 ≤ d) (hm : 1 ≤ m) (u : Fin d → unitInterval) :
    (samplerFromThetaRAM theta d m u).1.work ≤ 158 * d * m ∧
    (samplerFromThetaRAM theta d m u).1.allocated ≤ 158 * d * m ∧
    (samplerFromThetaRAM theta d m u).2 ≤ d := by
  have hc := samplerCacheRAM_linear theta d m hd hm
  have hs := cachedSamplerRAM_linear theta d m u
  have hdm : d ≤ d * m := by nlinarith
  have hone : 1 ≤ d * m := by nlinarith
  dsimp only [samplerFromThetaRAM]
  refine ⟨?_, ?_, hs.2.2⟩
  · nlinarith only [hc.1, hs.1, hdm, hone]
  · nlinarith only [hc.2, hs.2.1, hdm, hone]

/-- Input parameter cells are counted in addition to all new allocations.
The algorithm needs no lifetime reuse to obtain this linear-dm peak bound. -/
theorem samplerFromThetaRAM_peak_with_input (theta : Array ℝ) (d m : ℕ)
    (hsize : theta.size = d) (hd : 1 ≤ d) (hm : 1 ≤ m)
    (u : Fin d → unitInterval) :
    theta.size + 1 + (samplerFromThetaRAM theta d m u).1.allocated ≤ 160 * d * m := by
  have ha := (samplerFromThetaRAM_linear theta d m hd hm u).2.1
  have hdm : d ≤ d * m := by nlinarith
  have hone : 1 ≤ d * m := by nlinarith
  rw [hsize]
  nlinarith only [ha, hdm, hone]

end
end MsetsPaper.Upper.RAMPrograms
