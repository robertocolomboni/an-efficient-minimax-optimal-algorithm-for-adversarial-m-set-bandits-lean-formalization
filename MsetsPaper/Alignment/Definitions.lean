import MsetsPaper.Upper.FiniteKL

/-!
The unnumbered equivalence between exact OMD and an exponential update
followed by KL projection (definitive TeX, equations at lines 739--762).
The common log-normalizer cancels for every pair of feasible distributions.
This is a direct formal statement of the asserted equality of minimizers,
not just the already available pointwise KL identity.
-/

noncomputable section
open scoped BigOperators
open MsetsPaper.Upper

namespace MsetsPaper.Alignment

variable {α : Type*} [Fintype α]

theorem omd_objective_comparison (p q r z : α → ℝ) (eta : ℝ)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1)
    (hqsum : ∑ x, q x = 1) (hrsum : ∑ x, r x = 1) :
    (eta * finiteExpectation q z + finiteKL q p ≤
      eta * finiteExpectation r z + finiteKL r p) ↔
    finiteKL q (mwUpdate p z eta) ≤ finiteKL r (mwUpdate p z eta) := by
  rw [finiteKL_mwUpdate q p z eta hqsum hp hpsum,
    finiteKL_mwUpdate r p z eta hrsum hp hpsum]
  constructor <;> intro h <;> linarith

/-- The same minimizers over any constraint set of normalized distributions;
in the paper the constraint set is P_lambda. -/
theorem exact_omd_iff_kl_projection (p q z : α → ℝ) (eta : ℝ)
    (C : Set (α → ℝ)) (hC : ∀ r ∈ C, ∑ x, r x = 1)
    (hp : ∀ x, 0 < p x) (hpsum : ∑ x, p x = 1) :
    (q ∈ C ∧ ∀ r ∈ C, eta * finiteExpectation q z + finiteKL q p ≤
      eta * finiteExpectation r z + finiteKL r p) ↔
    (q ∈ C ∧ ∀ r ∈ C, finiteKL q (mwUpdate p z eta) ≤
      finiteKL r (mwUpdate p z eta)) := by
  constructor
  · rintro ⟨hq, hmin⟩
    exact ⟨hq, fun r hr =>
      (omd_objective_comparison p q r z eta hp hpsum (hC q hq) (hC r hr)).mp (hmin r hr)⟩
  · rintro ⟨hq, hmin⟩
    exact ⟨hq, fun r hr =>
      (omd_objective_comparison p q r z eta hp hpsum (hC q hq) (hC r hr)).mpr (hmin r hr)⟩

end MsetsPaper.Alignment
