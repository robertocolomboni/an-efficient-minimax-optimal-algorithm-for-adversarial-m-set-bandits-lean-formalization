import MsetsLower.Lower.Confidence.Score

/-!
# Averaging the confidence scores

This module formalizes the deterministic averaging argument leading to
`eq:lower-confidence-average-score`.  It uses the literal stopped score on a
concrete history; probability enters only in later modules.
-/

namespace MsetsLower.Lower.Confidence

open MsetsLower
open scoped BigOperators

noncomputable section

theorem sum_missedIndicator
    {n k : Nat} (hkn : k ≤ n) (A : MSetAction n k) :
    ∑ i ∈ confidenceCandidates n k hkn, missedIndicator i A =
      ((confidenceCandidates n k hkn).card : Real) - candidateCount hkn A := by
  classical
  have hcard : (A.1 ∩ confidenceCandidates n k hkn).card ≤
      (confidenceCandidates n k hkn).card :=
    Finset.card_mono Finset.inter_subset_right
  have hcount : candidateCount hkn A ≤
      (confidenceCandidates n k hkn).card := by
    simpa [candidateCount] using hcard
  have hsdiff :
      (confidenceCandidates n k hkn \ A.1).card =
        (confidenceCandidates n k hkn).card - candidateCount hkn A := by
    rw [Finset.card_sdiff]
    simp [candidateCount]
  calc
    ∑ i ∈ confidenceCandidates n k hkn, missedIndicator i A =
        ((confidenceCandidates n k hkn \ A.1).card : Real) := by
      rw [show ∑ i ∈ confidenceCandidates n k hkn, missedIndicator i A =
          (∑ i ∈ confidenceCandidates n k hkn,
            if i ∉ A.1 then (1 : Real) else 0) by rfl,
        Finset.sum_boole]
      congr 2
      ext i
      simp
    _ = (((confidenceCandidates n k hkn).card - candidateCount hkn A : Nat) : Real) :=
      congrArg Nat.cast hsdiff
    _ = ((confidenceCandidates n k hkn).card : Real) - candidateCount hkn A := by
      rw [Nat.cast_sub hcount]

/-- Sum of the planted scores over all candidates. -/
def totalConfidenceScore
    {n k : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (t : Nat) (h : History n k t) : Real :=
  ∑ i ∈ confidenceCandidates n k hkn,
    confidenceScore hkn noise Delta B i t h

/-- Sum of `g(Z_s)` through a concrete horizon. -/
def noiseShapeSum {n k : Nat} (noise : Nat → Real) :
    (t : Nat) → History n k t → Real
  | 0, _ => 0
  | t + 1, h => noiseShapeSum noise t h.1 + Feedback.shape (noise t)

@[simp] theorem noiseShapeSum_zero
    {n k : Nat} (noise : Nat → Real) (h : History n k 0) :
    noiseShapeSum noise 0 h = 0 := rfl

@[simp] theorem noiseShapeSum_succ
    {n k t : Nat} (noise : Nat → Real) (h : History n k (t + 1)) :
    noiseShapeSum noise (t + 1) h =
      noiseShapeSum noise t h.1 + Feedback.shape (noise t) := rfl

theorem totalConfidenceScore_zero
    {n k : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (h : History n k 0) :
    totalConfidenceScore hkn noise Delta B 0 h = 0 := by
  simp [totalConfidenceScore]

theorem totalConfidenceScore_succ
    {n k t : Nat} (hkn : k ≤ n) (noise : Nat → Real)
    (Delta B : Real) (h : History n k (t + 1)) :
    totalConfidenceScore hkn noise Delta B (t + 1) h =
      totalConfidenceScore hkn noise Delta B t h.1 +
        ((confidenceCandidates n k hkn).card : Real) * candidatePenalty hkn h.2.1 +
        Delta * Feedback.shape (noise t) * activeIndicator hkn B t h.1 *
          (((confidenceCandidates n k hkn).card : Real) - candidateCount hkn h.2.1) := by
  classical
  unfold totalConfidenceScore
  simp_rw [confidenceScore_succ]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  rw [← Finset.mul_sum, sum_missedIndicator]

/-- The one-round inequality behind the second line after
`eq:lower-confidence-average-score`. -/
theorem total_score_increment_lower
    {k h : Nat} {N Delta g : Real}
    (hk : 1 ≤ k) (hh_one : 1 ≤ h) (hh_le : h ≤ k)
    (hN : 2 ≤ N) (hDelta : 0 ≤ Delta) (hg : g ∈ Set.Icc (0 : Real) 1)
    (hscale : Delta / N ≤ 1 / (8 * (k : Real))) :
    N * (((h : Real) - 1) / (8 * (k : Real))) + Delta * g * (N - h) ≥
      Delta * (N / 2) * g := by
  have hkpos : (0 : Real) < k := by exact_mod_cast hk
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  have hhreal : (1 : Real) ≤ h := by exact_mod_cast hh_one
  have hhleReal : (h : Real) ≤ k := by exact_mod_cast hh_le
  have hDelta_le : Delta ≤ N / (8 * (k : Real)) := by
    have hm := (div_le_iff₀ hNpos).mp hscale
    calc
      Delta ≤ (1 / (8 * (k : Real))) * N := hm
      _ = N / (8 * (k : Real)) := by ring
  have hDg_le : Delta * g ≤ N / (8 * (k : Real)) := by
    calc
      Delta * g ≤ Delta * 1 := mul_le_mul_of_nonneg_left hg.2 hDelta
      _ ≤ N / (8 * (k : Real)) := by simpa using hDelta_le
  have hprod : Delta * g * ((h : Real) - 1) ≤
      N * (((h : Real) - 1) / (8 * (k : Real))) := by
    have hm := mul_le_mul_of_nonneg_right hDg_le (sub_nonneg.mpr hhreal)
    calc
      Delta * g * ((h : Real) - 1) ≤
          (N / (8 * (k : Real))) * ((h : Real) - 1) := hm
      _ = N * (((h : Real) - 1) / (8 * (k : Real))) := by ring
  have hhalf : N / 2 ≤ N - 1 := by linarith
  have hDg_nonneg : 0 ≤ Delta * g := mul_nonneg hDelta hg.1
  calc
    N * (((h : Real) - 1) / (8 * (k : Real))) + Delta * g * (N - h) =
        Delta * g * (N - 1) +
          (N * (((h : Real) - 1) / (8 * (k : Real))) -
            Delta * g * ((h : Real) - 1)) := by ring
    _ ≥ Delta * g * (N - 1) := by linarith
    _ ≥ Delta * g * (N / 2) :=
      mul_le_mul_of_nonneg_left hhalf hDg_nonneg
    _ = Delta * (N / 2) * g := by ring

/-- On `C_T<B`, every prefix is still active and the total candidate score
is bounded below by `(N Δ/2) Σ g(Z_t)`. -/
theorem totalConfidenceScore_lower_of_cumulative_lt
    {n k : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN : 2 ≤ (confidenceCandidates n k hkn).card)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hscale : Delta / (confidenceCandidates n k hkn).card ≤
      1 / (8 * (k : Real))) (B : Real) :
    ∀ (t : Nat) (h : History n k t), cumulativePenalty hkn t h < B →
      Delta * (((confidenceCandidates n k hkn).card : Real) / 2) *
          noiseShapeSum noise t h ≤
        totalConfidenceScore hkn noise Delta B t h := by
  intro t
  induction t with
  | zero =>
      intro h hlt
      simp [noiseShapeSum, totalConfidenceScore]
  | succ t ih =>
      rintro ⟨hprev, ⟨A, y⟩⟩ hfinal
      have hpnonneg := (candidatePenalty_mem_Ico hk hkn A).1
      have hprevlt : cumulativePenalty hkn t hprev < B := by
        rw [cumulativePenalty_succ] at hfinal
        linarith
      have ihprev := ih hprev hprevlt
      have hactive : activeIndicator hkn B t hprev = 1 := by
        simp [activeIndicator, hprevlt]
      have hinc := total_score_increment_lower hk
        (candidateCount_pos hk hkn A) (candidateCount_le hkn A)
        (show (2 : Real) ≤ (confidenceCandidates n k hkn).card by exact_mod_cast hN)
        hDelta (Feedback.shape_mem_Icc (hnoise t)) hscale
      rw [noiseShapeSum_succ, totalConfidenceScore_succ, hactive, mul_one]
      calc
        Delta * (((confidenceCandidates n k hkn).card : Real) / 2) *
              (noiseShapeSum noise t hprev + Feedback.shape (noise t)) =
            Delta * (((confidenceCandidates n k hkn).card : Real) / 2) *
                noiseShapeSum noise t hprev +
              Delta * (((confidenceCandidates n k hkn).card : Real) / 2) *
                Feedback.shape (noise t) := by ring
        _ ≤ totalConfidenceScore hkn noise Delta B t hprev +
              (((confidenceCandidates n k hkn).card : Real) *
                  (((candidateCount hkn A : Real) - 1) / (8 * (k : Real))) +
                Delta * Feedback.shape (noise t) *
                  (((confidenceCandidates n k hkn).card : Real) -
                    candidateCount hkn A)) := add_le_add ihprev hinc
        _ = totalConfidenceScore hkn noise Delta B t hprev +
              ((confidenceCandidates n k hkn).card : Real) * candidatePenalty hkn A +
              Delta * Feedback.shape (noise t) *
                (((confidenceCandidates n k hkn).card : Real) - candidateCount hkn A) := by
              rw [candidatePenalty]
              ring

/-- Equation `eq:lower-confidence-average-score`: on the good deterministic
conditions, the average candidate score is at least `ΔT/4`. -/
theorem lower_confidence_average_score
    {n k T : Nat} (hk : 1 ≤ k) (hkn : k ≤ n)
    (hN : 2 ≤ (confidenceCandidates n k hkn).card)
    (noise : Nat → Real) (hnoise : ∀ t, noise t ∈ Set.Icc (-1 : Real) 1)
    (Delta : Real) (hDelta : 0 ≤ Delta)
    (hscale : Delta / (confidenceCandidates n k hkn).card ≤
      1 / (8 * (k : Real))) (B : Real) (h : History n k T)
    (hpenalty : cumulativePenalty hkn T h < B)
    (hshape : (T : Real) / 2 ≤ noiseShapeSum noise T h) :
    Delta * T / 4 ≤
      totalConfidenceScore hkn noise Delta B T h /
        (confidenceCandidates n k hkn).card := by
  have htotal := totalConfidenceScore_lower_of_cumulative_lt hk hkn hN noise hnoise
    Delta hDelta hscale B T h hpenalty
  have hNpos : (0 : Real) < (confidenceCandidates n k hkn).card := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hN)
  have hscaled :
      Delta * (((confidenceCandidates n k hkn).card : Real) / 2) * (T / 2) ≤
        totalConfidenceScore hkn noise Delta B T h := by
    calc
      Delta * (((confidenceCandidates n k hkn).card : Real) / 2) * (T / 2) ≤
          Delta * (((confidenceCandidates n k hkn).card : Real) / 2) *
            noiseShapeSum noise T h := by
              gcongr
      _ ≤ totalConfidenceScore hkn noise Delta B T h := htotal
  apply (le_div_iff₀ hNpos).2
  nlinarith

end

end MsetsLower.Lower.Confidence
