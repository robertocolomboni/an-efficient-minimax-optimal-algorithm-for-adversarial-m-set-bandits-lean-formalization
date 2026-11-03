import MsetsPaper.Upper.SPDSchurComplete
import MsetsPaper.Upper.ResourceCombinators
import MsetsPaper.Upper.AlgorithmUpdate

/-! # Linear stored-vector correction and parameter updates

All vector passes traverse lists in order. The common scalar in the
correction is computed once, not once per output coordinate. Resource work
includes real operations, list traversal, output cells and control work.
-/

namespace MsetsPaper.Upper.VectorProgram

open MsetsLower MsetsLower.History
open SchurSolver
open scoped BigOperators

noncomputable section

theorem storedVector_as_ofFn {d : ℕ} (x : StoredVector d) :
    List.ofFn (storedVector x) = x.1 := by
  rcases x with ⟨xs, rfl⟩
  exact List.ofFn_getElem

def resourceCorrection {d : ℕ} (m : ℝ) (mu : StoredVector d) : ResourceRun (StoredVector d) :=
  let terms := resourceMap (fun u ↦ (⟨u / (1 - u), 2, 2⟩ : ResourceRun ℝ)) mu.1
  let total := MsetsPaper.Upper.resourceSum terms.value
  let common := (1 + total.value) / m
  let output := resourceMap
    (fun u ↦ (⟨4 * (common + (1 - 2 * u) / (u * (1 - u))), 7, 7⟩ : ResourceRun ℝ)) mu.1
  ⟨⟨output.value, by simp [output, resourceMap_values, mu.2]⟩,
    terms.work + total.work + output.work + 3,
    terms.allocated + total.allocated + output.allocated + 3⟩

theorem resourceCorrection_exact {d : ℕ} (m : ℝ) (mu : StoredVector d) :
    storedVector (resourceCorrection m mu).value = correction m (storedVector mu) := by
  have hsum : (mu.1.map (fun u ↦ u / (1 - u))).sum =
      ∑ i, storedVector mu i / (1 - storedVector mu i) := by
    rw [← storedVector_as_ofFn mu, List.map_ofFn, List.sum_ofFn]
    rfl
  ext i
  simp only [resourceCorrection, resourceMap_values, MsetsPaper.Upper.resourceSum_values,
    hsum, storedVector, cachedRealVector, List.getElem_map, correction]

theorem resourceCorrection_bounds {d : ℕ} (m : ℝ) (mu : StoredVector d) :
    (resourceCorrection m mu).work ≤ 16 * d + 6 ∧
      (resourceCorrection m mu).allocated ≤ 17 * d + 6 := by
  let terms := resourceMap (fun u ↦ (⟨u / (1 - u), 2, 2⟩ : ResourceRun ℝ)) mu.1
  have hterms := resourceMap_bounds
    (fun u ↦ (⟨u / (1 - u), 2, 2⟩ : ResourceRun ℝ)) mu.1 2 2 (by simp)
  have hlength : terms.value.length = d := by simp [terms, resourceMap_values, mu.2]
  have htotal := MsetsPaper.Upper.resourceSum_counts terms.value
  rw [hlength] at htotal
  have hout := resourceMap_bounds
    (fun u ↦ (⟨4 * ((1 + (MsetsPaper.Upper.resourceSum terms.value).value) / m +
      (1 - 2 * u) / (u * (1 - u))), 7, 7⟩ : ResourceRun ℝ)) mu.1 7 7 (by simp)
  rw [mu.2] at hterms hout
  change terms.work ≤ _ ∧ terms.allocated ≤ _ at hterms
  dsimp only [terms] at hterms htotal hout
  dsimp only [resourceCorrection]
  constructor <;> omega

/-- One synchronous pass produces both z=estimate-eta*c and theta-eta*z. -/
def resourceUpdate (eta : ℝ) : List ℝ → List ℝ → List ℝ →
    ResourceRun (List ℝ × List ℝ)
  | th :: theta, est :: estimate, co :: correction =>
    let tail := resourceUpdate eta theta estimate correction
    let z := est - eta * co
    let next := th - eta * z
    ⟨(z :: tail.value.1, next :: tail.value.2), tail.work + 9, tail.allocated + 14⟩
  | _, _, _ => ⟨([], []), 3, 1⟩

theorem resourceUpdate_values (eta : ℝ) : ∀ (d : ℕ)
    (theta estimate c : Fin d → ℝ),
    (resourceUpdate eta (List.ofFn theta) (List.ofFn estimate) (List.ofFn c)).value =
      (List.ofFn (fun i ↦ estimate i - eta * c i),
        List.ofFn (fun i ↦ theta i - eta * (estimate i - eta * c i))) := by
  intro d
  induction d with
  | zero => intro theta estimate c; simp [resourceUpdate]
  | succ d ih => intro theta estimate c; simp [List.ofFn_succ, resourceUpdate, ih]

theorem resourceUpdate_counts (eta : ℝ) : ∀ (d : ℕ)
    (theta estimate c : List ℝ), theta.length = d → estimate.length = d → c.length = d →
    (resourceUpdate eta theta estimate c).work = 9 * d + 3 ∧
      (resourceUpdate eta theta estimate c).allocated = 14 * d + 1 := by
  intro d
  induction d with
  | zero =>
    intro theta estimate c ht he hc
    have ht' : theta = [] := List.eq_nil_of_length_eq_zero ht
    have he' : estimate = [] := List.eq_nil_of_length_eq_zero he
    have hc' : c = [] := List.eq_nil_of_length_eq_zero hc
    simp [ht', he', hc', resourceUpdate]
  | succ d ih =>
    intro theta estimate c ht he hc
    cases theta with
    | nil => simp at ht
    | cons th theta =>
      cases estimate with
      | nil => simp at he
      | cons est estimate =>
        cases c with
        | nil => simp at hc
        | cons co c =>
          have hh := ih theta estimate c (by simpa using ht)
            (by simpa using he) (by simpa using hc)
          simp only [resourceUpdate]
          constructor <;> omega

def resourceUpdateStored {d : ℕ} (eta : ℝ)
    (theta estimate c : StoredVector d) : ResourceRun (StoredVector d × StoredVector d) :=
  let output := resourceUpdate eta theta.1 estimate.1 c.1
  have hvalues : output.value =
      (List.ofFn (fun i ↦ storedVector estimate i - eta * storedVector c i),
        List.ofFn (fun i ↦ storedVector theta i -
          eta * (storedVector estimate i - eta * storedVector c i))) := by
    simpa only [storedVector_as_ofFn] using resourceUpdate_values eta d
      (storedVector theta) (storedVector estimate) (storedVector c)
  ⟨(⟨output.value.1, by rw [hvalues]; simp⟩,
      ⟨output.value.2, by rw [hvalues]; simp⟩), output.work + 2, output.allocated + 2⟩

theorem resourceUpdateStored_exact {d : ℕ} (eta : ℝ)
    (theta estimate c : StoredVector d) :
    storedVector (resourceUpdateStored eta theta estimate c).value.1 =
      storedVector estimate - eta • storedVector c ∧
    storedVector (resourceUpdateStored eta theta estimate c).value.2 =
      storedVector theta - eta • (storedVector estimate - eta • storedVector c) := by
  have hvalues := resourceUpdate_values eta d
    (storedVector theta) (storedVector estimate) (storedVector c)
  simp only [storedVector_as_ofFn] at hvalues
  constructor <;> ext i <;>
    simp [resourceUpdateStored, storedVector, cachedRealVector, hvalues]

theorem resourceUpdateStored_counts {d : ℕ} (eta : ℝ)
    (theta estimate c : StoredVector d) :
    (resourceUpdateStored eta theta estimate c).work = 9 * d + 5 ∧
      (resourceUpdateStored eta theta estimate c).allocated = 14 * d + 3 := by
  have h := resourceUpdate_counts eta d theta.1 estimate.1 c.1 theta.2 estimate.2 c.2
  dsimp only [resourceUpdateStored]
  constructor <;> omega

/-- The complete linear part of the feedback update, after solving for the estimate. -/
def resourceUnprojected {d : ℕ} (m eta : ℝ)
    (theta estimate mu : StoredVector d) : ResourceRun (StoredVector d × StoredVector d) :=
  let c := resourceCorrection m mu
  let output := resourceUpdateStored eta theta estimate c.value
  ⟨output.value, c.work + output.work + 1, c.allocated + output.allocated + 1⟩

theorem resourceUnprojected_exact {d : ℕ} (m eta : ℝ)
    (theta estimate mu : StoredVector d) :
    storedVector (resourceUnprojected m eta theta estimate mu).value.1 =
      storedVector estimate - eta • correction m (storedVector mu) ∧
    storedVector (resourceUnprojected m eta theta estimate mu).value.2 =
      storedVector theta - eta •
        (storedVector estimate - eta • correction m (storedVector mu)) := by
  simpa only [resourceUnprojected, resourceCorrection_exact] using
    resourceUpdateStored_exact eta theta estimate (resourceCorrection m mu).value

theorem resourceUnprojected_bounds {d : ℕ} (m eta : ℝ)
    (theta estimate mu : StoredVector d) :
    (resourceUnprojected m eta theta estimate mu).work ≤ 25 * d + 12 ∧
      (resourceUnprojected m eta theta estimate mu).allocated ≤ 31 * d + 10 := by
  have hc := resourceCorrection_bounds m mu
  have hu := resourceUpdateStored_counts eta theta estimate (resourceCorrection m mu).value
  dsimp only [resourceUnprojected]
  constructor <;> omega

/-- Data refinement for the observable algorithm; the round program below supplies
the moment and estimate equalities from actual ESP and Schur computations. -/
theorem resourceUnprojected_feedback {d m : ℕ} (eta : ℝ)
    (theta estimate mu : StoredVector d) (a : Action d m) (y : ℝ)
    (he : storedVector estimate = estimateFromFeedback (storedVector theta) a y)
    (hm : storedVector mu = weightedMarginal (m := m) (storedVector theta)) :
    storedVector (resourceUnprojected m eta theta estimate mu).value.2 =
      unprojectedFromFeedback (storedVector theta) eta a y := by
  rw [(resourceUnprojected_exact m eta theta estimate mu).2, he, hm]
  rfl

end

end MsetsPaper.Upper.VectorProgram
