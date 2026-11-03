import MsetsLower.Core.Protocol

/-!
# Prefixes of finite protocol histories

The protocol history is right-nested by time.  This module provides the
measurable operation which removes a finite suffix, together with the
projective consistency of `runLaw`.  The latter is needed when a lower-bound
construction is active only until an internal horizon `T0`.
-/

namespace MsetsLower

open MeasureTheory Set

namespace History

@[simp] theorem snoc_fst {d m t : Nat} (h : History d m t)
    (a : MSetAction d m) (feedback : Real) :
    (h.snoc a feedback).1 = h := rfl

/-- Remove the final `r` observations from a history of length `s+r`. -/
def dropSuffix {d m : Nat} (s : Nat) :
    (r : Nat) → History d m (s + r) → History d m s
  | 0, h => h
  | r + 1, h => dropSuffix s r h.1

@[simp] theorem dropSuffix_zero {d m s : Nat} (h : History d m s) :
    dropSuffix s 0 h = h := rfl

@[simp] theorem dropSuffix_succ {d m s r : Nat}
    (h : History d m (s + (r + 1))) :
    dropSuffix s (r + 1) h = dropSuffix s r h.1 := rfl

theorem measurable_dropSuffix {d m : Nat} (s : Nat) :
    ∀ r, Measurable (dropSuffix (d := d) (m := m) s r) := by
  intro r
  induction r with
  | zero => exact measurable_id
  | succ r ih => exact ih.comp measurable_fst

end History

/-- Taking the preceding-history component of a one-round extension recovers
the input history. -/
theorem fst_extendRun {d m t : Nat} (L : LossProcess d m)
    (p : History d m t × MSetAction d m) :
    (extendRun L t p).1 = p.1 := rfl

/-- The marginal of the next-round law on its preceding history is exactly
the current run law. -/
theorem runLaw_succ_map_fst {d m : Nat} (P : Policy d m)
    (L : LossProcess d m) (t : Nat) :
    (runLaw P L (t + 1)).map
        (fun h : History d m (t + 1) => h.1) =
      runLaw P L t := by
  let previous : History d m (t + 1) → History d m t := fun h => h.1
  have hprevious : Measurable previous := measurable_fst
  change (runLaw P L (t + 1)).map previous = runLaw P L t
  ext s hs
  rw [Measure.map_apply hprevious hs, runLaw_succ_apply P L t
    (hprevious hs)]
  have hround (h : History d m t) :
      roundKernel P L t h (previous ⁻¹' s) = s.indicator 1 h := by
    rw [roundKernel_apply P L t h (hprevious hs)]
    by_cases hh : h ∈ s
    · have hpre : {a : MSetAction d m |
          h.snoc a (actionLoss a (L.itemLoss t h)) ∈ previous ⁻¹' s} = Set.univ := by
        ext a
        simp [previous, hh]
      rw [hpre, measure_univ]
      simp [Set.indicator, hh]
    · have hpre : {a : MSetAction d m |
          h.snoc a (actionLoss a (L.itemLoss t h)) ∈ previous ⁻¹' s} = ∅ := by
        ext a
        simp [previous, hh]
      rw [hpre, measure_empty]
      simp [Set.indicator, hh]
  simp_rw [hround]
  rw [MeasureTheory.lintegral_indicator hs]
  simp

/-- Projective consistency at an arbitrary earlier horizon. -/
theorem runLaw_add_map_dropSuffix {d m : Nat} (P : Policy d m)
    (L : LossProcess d m) (s : Nat) :
    ∀ r, (runLaw P L (s + r)).map (History.dropSuffix s r) = runLaw P L s := by
  intro r
  induction r with
  | zero => exact Measure.map_id
  | succ r ih =>
      change (runLaw P L ((s + r) + 1)).map
          (fun h => History.dropSuffix s r h.1) = runLaw P L s
      let previous : History d m ((s + r) + 1) → History d m (s + r) :=
        fun h => h.1
      have hprevious : Measurable previous := measurable_fst
      change (runLaw P L ((s + r) + 1)).map
          (fun h => History.dropSuffix s r (previous h)) = runLaw P L s
      calc
        (runLaw P L ((s + r) + 1)).map
            (fun h => History.dropSuffix s r (previous h)) =
          ((runLaw P L ((s + r) + 1)).map previous).map
            (History.dropSuffix s r) := by
              rw [Measure.map_map (History.measurable_dropSuffix s r) hprevious]
              rfl
        _ = (runLaw P L (s + r)).map (History.dropSuffix s r) := by
          rw [show (runLaw P L ((s + r) + 1)).map previous =
              runLaw P L (s + r) by
            exact runLaw_succ_map_fst P L (s + r)]
        _ = runLaw P L s := ih

#print axioms runLaw_succ_map_fst
#print axioms runLaw_add_map_dropSuffix

end MsetsLower
