import MsetsLower.Prelude
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin

/-!
# Simultaneous selection from two averaged bounds

This module formalizes the deterministic core of
`lem:select-good-index`.  The measure-theoretic corollary will instantiate
`eventProb` with event probabilities and `weight` with expectations.
-/

namespace MsetsLower.Probability

open Finset
open MeasureTheory
open scoped BigOperators

noncomputable section

/-- If event probabilities average at least `p` and nonnegative costs average
at most `w`, one index has event probability at least `p / 2` and cost at most
`2w / p`.  This is the exact finite averaging argument used in the paper. -/
theorem exists_good_index_of_averages
    {N : Nat} (hN : 0 < N)
    (eventProb weight : Fin N → Real) {p w : Real}
    (hp : 0 < p) (_hp_one : p ≤ 1)
    (_hevent_nonneg : ∀ i, 0 ≤ eventProb i)
    (hevent_le_one : ∀ i, eventProb i ≤ 1)
    (hweight_nonneg : ∀ i, 0 ≤ weight i)
    (hevent_average : (N : Real) * p ≤ ∑ i, eventProb i)
    (hweight_average : ∑ i, weight i ≤ (N : Real) * w) :
    ∃ i, p / 2 ≤ eventProb i ∧ weight i ≤ 2 * w / p := by
  classical
  let good : Finset (Fin N) :=
    Finset.univ.filter fun i => p / 2 ≤ eventProb i
  have hp_nonneg : 0 ≤ p := hp.le
  have hgood_sum :
      ∑ i ∈ good, eventProb i ≤ (good.card : Real) := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul good eventProb (1 : Real)
        (fun i _hi => hevent_le_one i))
  have hbad_sum :
      ∑ i ∈ (Finset.univ.filter fun i : Fin N => ¬p / 2 ≤ eventProb i),
          eventProb i ≤
        ((Finset.univ.filter fun i : Fin N => ¬p / 2 ≤ eventProb i).card :
          Real) * (p / 2) := by
    simpa [nsmul_eq_mul] using
      (Finset.sum_le_card_nsmul
        (Finset.univ.filter fun i : Fin N => ¬p / 2 ≤ eventProb i)
        eventProb (p / 2) (by
          intro i hi
          exact le_of_lt (not_le.mp (Finset.mem_filter.mp hi).2)))
  have hbad_card :
      ((Finset.univ.filter fun i : Fin N => ¬p / 2 ≤ eventProb i).card :
          Real) ≤ N := by
    have hbad_card_nat :
        (Finset.univ.filter fun i : Fin N =>
          ¬p / 2 ≤ eventProb i).card ≤ N := by
      simpa using (Finset.card_filter_le
        (s := (Finset.univ : Finset (Fin N)))
        (p := fun i : Fin N => ¬p / 2 ≤ eventProb i))
    exact_mod_cast hbad_card_nat
  have htotal_upper :
      (∑ i, eventProb i) ≤ (good.card : Real) + (N : Real) * (p / 2) := by
    calc
      (∑ i, eventProb i) =
          (∑ i ∈ good, eventProb i) +
            ∑ i ∈ (Finset.univ.filter fun i : Fin N =>
              ¬p / 2 ≤ eventProb i), eventProb i := by
            simpa [good] using
              (Finset.sum_filter_add_sum_filter_not
                (s := (Finset.univ : Finset (Fin N)))
                (p := fun i : Fin N => p / 2 ≤ eventProb i)
                eventProb).symm
      _ ≤ (good.card : Real) +
          ((Finset.univ.filter fun i : Fin N =>
            ¬p / 2 ≤ eventProb i).card : Real) * (p / 2) :=
        add_le_add hgood_sum hbad_sum
      _ ≤ (good.card : Real) + (N : Real) * (p / 2) := by
        gcongr
  have hgood_card : (N : Real) * p / 2 ≤ (good.card : Real) := by
    linarith
  have hgood_nonempty : good.Nonempty := by
    have hleft_pos : 0 < (N : Real) * p / 2 := by positivity
    have hcard_pos : 0 < (good.card : Real) := hleft_pos.trans_le hgood_card
    exact Finset.card_pos.mp (by exact_mod_cast hcard_pos)
  have hsum_weight_nonneg : 0 ≤ ∑ i, weight i :=
    Finset.sum_nonneg fun i _hi => hweight_nonneg i
  have hw_nonneg : 0 ≤ w := by
    have hN_real : 0 < (N : Real) := by exact_mod_cast hN
    have hprod : 0 ≤ (N : Real) * w :=
      hsum_weight_nonneg.trans hweight_average
    nlinarith
  have hgood_weight_le_total :
      ∑ i ∈ good, weight i ≤ ∑ i, weight i := by
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset _ _) (by
        intro i _hi _hnot
        exact hweight_nonneg i)
  have hscale_nonneg : 0 ≤ 2 * w / p :=
    div_nonneg (mul_nonneg (by norm_num) hw_nonneg) hp.le
  have hNw_eq :
      (N : Real) * w = ((N : Real) * p / 2) * (2 * w / p) := by
    field_simp [hp.ne']
  have hNw_le_good :
      (N : Real) * w ≤ (good.card : Real) * (2 * w / p) := by
    rw [hNw_eq]
    exact mul_le_mul_of_nonneg_right hgood_card hscale_nonneg
  have hgood_weight_le_constant :
      ∑ i ∈ good, weight i ≤ ∑ _i ∈ good, (2 * w / p) := by
    calc
      ∑ i ∈ good, weight i ≤ ∑ i, weight i := hgood_weight_le_total
      _ ≤ (N : Real) * w := hweight_average
      _ ≤ (good.card : Real) * (2 * w / p) := hNw_le_good
      _ = ∑ _i ∈ good, (2 * w / p) := by simp
  obtain ⟨i, hi_good, hi_weight⟩ :=
    Finset.exists_le_of_sum_le hgood_nonempty hgood_weight_le_constant
  exact ⟨i, (Finset.mem_filter.mp hi_good).2, hi_weight⟩

/-- Measure-theoretic form of `lem:select-good-index`.  Expectations are
Bochner integrals of real-valued nonnegative random variables. -/
theorem select_good_index
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    {N : Nat} (hN : 0 < N)
    (E : Fin N → Set Ω) (W : Fin N → Ω → Real)
    (_hE : ∀ i, MeasurableSet (E i))
    (hW_nonneg : ∀ i, 0 ≤ᵐ[P] W i)
    {p w : Real} (hp : 0 < p) (hp_one : p ≤ 1)
    (hprob_average : (N : Real) * p ≤ ∑ i, P.real (E i))
    (hexpect_average :
      ∑ i, ∫ ω, W i ω ∂P ≤ (N : Real) * w) :
    ∃ i,
      p / 2 ≤ P.real (E i) ∧
      (∫ ω, W i ω ∂P) ≤ 2 * w / p := by
  exact exists_good_index_of_averages hN
    (fun i => P.real (E i)) (fun i => ∫ ω, W i ω ∂P)
    hp hp_one
    (fun _i => measureReal_nonneg)
    (fun _i => measureReal_le_one)
    (fun i => integral_nonneg_of_ae (hW_nonneg i))
    hprob_average hexpect_average

/-- Reindex a sum over a finset by its canonical finite type. -/
theorem sum_equivFin_symm
    {ι M : Type*} [AddCommMonoid M]
    (s : Finset ι) (f : ι → M) :
    ∑ j : Fin s.card, f (s.equivFin.symm j).1 = ∑ i ∈ s, f i := by
  classical
  rw [← s.sum_attach, Finset.attach_eq_univ, ← s.equivFin.symm.sum_comp]

/-- Finset-indexed form of `select_good_index`.  This avoids changing the
paper's concrete candidate set into an artificial `Fin N` at every use. -/
theorem select_good_index_finset
    {Ω ι : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (s : Finset ι) (hs : s.Nonempty)
    (E : ι → Set Ω) (W : ι → Ω → Real)
    (hE : ∀ i ∈ s, MeasurableSet (E i))
    (hW_nonneg : ∀ i ∈ s, 0 ≤ᵐ[P] W i)
    {p w : Real} (hp : 0 < p) (hp_one : p ≤ 1)
    (hprob_average : (s.card : Real) * p ≤ ∑ i ∈ s, P.real (E i))
    (hexpect_average :
      ∑ i ∈ s, ∫ ω, W i ω ∂P ≤ (s.card : Real) * w) :
    ∃ i ∈ s,
      p / 2 ≤ P.real (E i) ∧
      (∫ ω, W i ω ∂P) ≤ 2 * w / p := by
  classical
  let e : Fin s.card → ι := fun j => (s.equivFin.symm j).1
  have he_mem (j : Fin s.card) : e j ∈ s := (s.equivFin.symm j).2
  let E' : Fin s.card → Set Ω := fun j => E (e j)
  let W' : Fin s.card → Ω → Real := fun j => W (e j)
  have hcard : 0 < s.card := hs.card_pos
  have hE' : ∀ j, MeasurableSet (E' j) := by
    intro j
    exact hE (e j) (he_mem j)
  have hW' : ∀ j, 0 ≤ᵐ[P] W' j := by
    intro j
    exact hW_nonneg (e j) (he_mem j)
  have hprob' : (s.card : Real) * p ≤ ∑ j, P.real (E' j) := by
    rw [show (∑ j, P.real (E' j)) = ∑ i ∈ s, P.real (E i) by
      simpa [E', e] using sum_equivFin_symm s (fun i => P.real (E i))]
    exact hprob_average
  have hexpect' :
      ∑ j, ∫ ω, W' j ω ∂P ≤ (s.card : Real) * w := by
    rw [show (∑ j, ∫ ω, W' j ω ∂P) =
        ∑ i ∈ s, ∫ ω, W i ω ∂P by
      simpa [W', e] using
        sum_equivFin_symm s (fun i => ∫ ω, W i ω ∂P)]
    exact hexpect_average
  obtain ⟨j, hjprob, hjexpect⟩ :=
    select_good_index P hcard E' W' hE' hW' hp hp_one hprob' hexpect'
  exact ⟨e j, he_mem j, hjprob, hjexpect⟩

end

end MsetsLower.Probability
