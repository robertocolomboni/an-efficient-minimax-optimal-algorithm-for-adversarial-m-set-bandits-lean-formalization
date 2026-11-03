import CoefficientOne.Sampling.LocalCoupling

/-! # Local coupling for genuinely one-sided differentiable paths

An arbitrary within-derivative is extended at the base point by its affine
first-order approximation outside its domain. This is an explicit proof of
the endpoint clause, without assuming a two-sided derivative of the given path.
-/

open scoped Topology
open Filter MeasureTheory Set

namespace CoefficientOne.Sampling
noncomputable section
set_option maxHeartbeats 1000000

def parameterDerivativeExtension {n : ℕ} (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ)
    (s : Set ℝ) (t : ℝ) : Fin n → ℝ := by
  classical
  exact if t ∈ s then θ t else θ 0 + t • a

theorem parameterDerivativeExtension_zero {n : ℕ} (θ : ℝ → Fin n → ℝ)
    (a : Fin n → ℝ) (s : Set ℝ) : parameterDerivativeExtension θ a s 0 = θ 0 := by
  unfold parameterDerivativeExtension
  split_ifs <;> simp

theorem parameterDerivativeExtension_hasDerivAt {n : ℕ} (θ : ℝ → Fin n → ℝ)
    (a : Fin n → ℝ) (s : Set ℝ) (hθ : HasDerivWithinAt θ a s 0) :
    HasDerivAt (parameterDerivativeExtension θ a s) a 0 := by
  classical
  have hs : HasDerivWithinAt (parameterDerivativeExtension θ a s) a s 0 :=
    hθ.congr (fun t ht => by simp only [parameterDerivativeExtension, if_pos ht])
      (parameterDerivativeExtension_zero θ a s)
  have ha : HasDerivAt (fun t : ℝ => θ 0 + t • a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const a).const_add (θ 0)
  have hc : HasDerivWithinAt (parameterDerivativeExtension θ a s) a sᶜ 0 :=
    ha.hasDerivWithinAt.congr
      (fun t ht => by simp only [parameterDerivativeExtension, if_neg ht])
      (by simp [parameterDerivativeExtension_zero])
  have hu := hs.union hc
  simpa only [Set.union_compl_self, hasDerivWithinAt_univ] using hu

theorem parameter_local_coupling_within {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ) (s : Set ℝ)
    (hθ : HasDerivWithinAt θ a s 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[s \ {0}] (0 : ℝ),
      expectedOutputDistance (seedMeasure n)
          (sequentialSampler (fun i => Real.exp (θ 0 i)) k)
          (sequentialSampler (fun i => Real.exp (θ t i)) k) / |t| ≤
        2 * samplerVariation (fun i => Real.exp (θ 0 i)) k a + ε := by
  intro ε hε
  have h := parameter_local_coupling k hk (parameterDerivativeExtension θ a s) a
    (parameterDerivativeExtension_hasDerivAt θ a s hθ) ε hε
  have hsub : 𝓝[s \ {0}] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (fun t ht => ht.2)
  filter_upwards [h.filter_mono hsub, self_mem_nhdsWithin] with t ht hs
  have hz := parameterDerivativeExtension_zero θ a s
  have he : parameterDerivativeExtension θ a s t = θ t := by
    simp only [parameterDerivativeExtension, if_pos hs.1]
  simpa only [hz, he] using ht

theorem parameter_local_coupling_right {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ)
    (hθ : HasDerivWithinAt θ a (Ici 0) 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[>] (0 : ℝ),
      expectedOutputDistance (seedMeasure n)
          (sequentialSampler (fun i => Real.exp (θ 0 i)) k)
          (sequentialSampler (fun i => Real.exp (θ t i)) k) / |t| ≤
        2 * samplerVariation (fun i => Real.exp (θ 0 i)) k a + ε := by
  have he : Ici (0 : ℝ) \ {0} = Ioi 0 := by
    ext t
    simp only [Set.mem_sdiff, mem_Ici, mem_singleton_iff, mem_Ioi]
    constructor
    · rintro ⟨h, hn⟩
      exact lt_of_le_of_ne h (Ne.symm hn)
    · intro h
      exact ⟨h.le, h.ne'⟩
  simpa only [he] using parameter_local_coupling_within k hk θ a (Ici 0) hθ

theorem parameter_local_coupling_left {n : ℕ} (k : ℕ) (hk : k ≤ n)
    (θ : ℝ → Fin n → ℝ) (a : Fin n → ℝ)
    (hθ : HasDerivWithinAt θ a (Iic 0) 0) :
    ∀ ε > (0 : ℝ), ∀ᶠ t in 𝓝[<] (0 : ℝ),
      expectedOutputDistance (seedMeasure n)
          (sequentialSampler (fun i => Real.exp (θ 0 i)) k)
          (sequentialSampler (fun i => Real.exp (θ t i)) k) / |t| ≤
        2 * samplerVariation (fun i => Real.exp (θ 0 i)) k a + ε := by
  have he : Iic (0 : ℝ) \ {0} = Iio 0 := by
    ext t
    simp only [Set.mem_sdiff, mem_Iic, mem_singleton_iff, mem_Iio]
    constructor
    · rintro ⟨h, hn⟩
      exact lt_of_le_of_ne h hn
    · intro h
      exact ⟨h.le, h.ne⟩
  simpa only [he] using parameter_local_coupling_within k hk θ a (Iic 0) hθ

end
end CoefficientOne.Sampling
