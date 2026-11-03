import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic

/-!
Finite sampling identities for the introductory fixed-cardinality experiment.
The two parametrizations select either a marked (k+1)-set or a k-set with a
marked point outside it. The equivalence retains the actual selected sets.
-/

namespace MsetsPaper.Lower.WJ

open scoped BigOperators
noncomputable section

abbrev Subset (d k : ℕ) := {s : Finset (Fin d) // s.card = k}
abbrev Marked (d k : ℕ) := (w : Subset d (k + 1)) × {j : Fin d // j ∈ w.val}
abbrev Exterior (d k : ℕ) := (s : Subset d k) × {j : Fin d // j ∉ s.val}

theorem card_subset (d k : ℕ) : Fintype.card (Subset d k) = d.choose k := by
  simp [Subset]

theorem subset_nonempty {d k : ℕ} (hk : k ≤ d) : Nonempty (Subset d k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_subset]
  exact Nat.choose_pos hk

def markedToExterior {d k : ℕ} (x : Marked d k) : Exterior d k :=
  ⟨⟨x.1.val.erase x.2.val, by
      rw [Finset.card_erase_of_mem x.2.property, x.1.property]
      omega⟩,
    ⟨x.2.val, Finset.notMem_erase _ _⟩⟩

def exteriorToMarked {d k : ℕ} (x : Exterior d k) : Marked d k :=
  ⟨⟨insert x.2.val x.1.val, by
      rw [Finset.card_insert_of_notMem x.2.property, x.1.property]⟩,
    ⟨x.2.val, Finset.mem_insert_self _ _⟩⟩

def markedEquivExterior (d k : ℕ) : Marked d k ≃ Exterior d k where
  toFun := markedToExterior
  invFun := exteriorToMarked
  left_inv := by
    rintro ⟨⟨w, hw⟩, ⟨j, hj⟩⟩
    simp only [markedToExterior, exteriorToMarked]
    have he : insert j (w.erase j) = w := Finset.insert_erase hj
    apply Sigma.ext (Subtype.ext he)
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change x ∈ insert j (w.erase j) ↔ x ∈ w
      rw [he])).mpr rfl
  right_inv := by
    rintro ⟨⟨s, hs⟩, ⟨j, hj⟩⟩
    simp only [markedToExterior, exteriorToMarked]
    have he : (insert j s).erase j = s := Finset.erase_insert hj
    apply Sigma.ext (Subtype.ext he)
    exact (Subtype.heq_iff_coe_eq (fun x => by
      change x ∉ (insert j s).erase j ↔ x ∉ s
      rw [he])).mpr rfl

def uniformAverage {α : Type*} [Fintype α] (f : α → ℝ) : ℝ :=
  (∑ x, f x) / Fintype.card α

theorem uniformAverage_const {α : Type*} [Fintype α] [Nonempty α] (c : ℝ) :
    uniformAverage (fun _ : α => c) = c := by
  simp [uniformAverage, Finset.sum_const, Fintype.card_ne_zero]

theorem uniformAverage_nonneg {α : Type*} [Fintype α] {f : α → ℝ}
    (hf : ∀ x, 0 ≤ f x) : 0 ≤ uniformAverage f := by
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (Nat.cast_nonneg _)

theorem uniformAverage_mono {α : Type*} [Fintype α] {f g : α → ℝ}
    (hfg : ∀ x, f x ≤ g x) : uniformAverage f ≤ uniformAverage g := by
  exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun x _ => hfg x) (Nat.cast_nonneg _)

theorem uniformAverage_mem_Icc {α : Type*} [Fintype α] [Nonempty α] {f : α → ℝ}
    (hf : ∀ x, f x ∈ Set.Icc (0 : ℝ) 1) : uniformAverage f ∈ Set.Icc (0 : ℝ) 1 := by
  refine ⟨uniformAverage_nonneg (fun x => (hf x).1), ?_⟩
  exact (uniformAverage_mono (fun x => (hf x).2)).trans_eq (uniformAverage_const 1)

theorem uniformAverage_add {α : Type*} [Fintype α] (f g : α → ℝ) :
    uniformAverage (fun x => f x + g x) = uniformAverage f + uniformAverage g := by
  simp [uniformAverage, Finset.sum_add_distrib, add_div]

theorem uniformAverage_mul_const {α : Type*} [Fintype α] (f : α → ℝ) (c : ℝ) :
    uniformAverage (fun x => f x * c) = uniformAverage f * c := by
  unfold uniformAverage
  dsimp only
  rw [← Finset.sum_mul]
  ring

theorem uniformAverage_const_mul {α : Type*} [Fintype α] (c : ℝ) (f : α → ℝ) :
    uniformAverage (fun x => c * f x) = c * uniformAverage f := by
  simp only [mul_comm c, uniformAverage_mul_const]

theorem uniformAverage_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : β → ℝ) : uniformAverage (f ∘ e) = uniformAverage f := by
  unfold uniformAverage
  rw [Fintype.card_congr e]
  congr 1
  exact e.sum_comp f

theorem marked_average_eq_exterior {d k : ℕ} (f : Marked d k → ℝ) :
    uniformAverage f = uniformAverage (f ∘ exteriorToMarked) := by
  exact (uniformAverage_equiv (markedEquivExterior d k).symm f).symm

theorem card_marked_fiber {d k : ℕ} (w : Subset d (k + 1)) :
    Fintype.card {j : Fin d // j ∈ w.val} = k + 1 := by
  exact (Fintype.card_coe w.val).trans w.property

theorem card_exterior_fiber {d k : ℕ} (s : Subset d k) :
    Fintype.card {j : Fin d // j ∉ s.val} = d - k := by
  rw [Fintype.card_subtype_compl]
  simp [Fintype.card_coe, s.property]

theorem card_marked (d k : ℕ) : Fintype.card (Marked d k) = d.choose (k + 1) * (k + 1) := by
  rw [Fintype.card_sigma]
  simp only [card_marked_fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, card_subset]

theorem card_exterior (d k : ℕ) : Fintype.card (Exterior d k) = d.choose k * (d - k) := by
  rw [Fintype.card_sigma]
  simp only [card_exterior_fiber, Finset.sum_const, Finset.card_univ, smul_eq_mul, card_subset]

theorem marked_nonempty {d k : ℕ} (hk : k < d) : Nonempty (Marked d k) := by
  apply Fintype.card_pos_iff.mp
  rw [card_marked]
  exact Nat.mul_pos (Nat.choose_pos hk) (Nat.succ_pos k)

theorem exterior_nonempty {d k : ℕ} (hk : k < d) : Nonempty (Exterior d k) := by
  exact (markedEquivExterior d k).nonempty_congr.mp (marked_nonempty hk)

theorem uniformAverage_sigma {α : Type*} {β : α → Type*}
    [Fintype α] [∀ a, Fintype (β a)] (n : ℕ)
    (hn : ∀ a, Fintype.card (β a) = n) (f : (a : α) × β a → ℝ) :
    uniformAverage f = uniformAverage (fun a => (∑ b, f ⟨a, b⟩) / n) := by
  unfold uniformAverage
  rw [Fintype.sum_sigma, Fintype.card_sigma]
  simp only [hn, Finset.sum_const, Finset.card_univ, smul_eq_mul, Nat.cast_mul]
  rw [← Finset.sum_div]
  ring

theorem marked_average_fibers {d k : ℕ} (f : Marked d k → ℝ) :
    uniformAverage f = uniformAverage
      (fun w : Subset d (k + 1) => (∑ j, f ⟨w, j⟩) / (k + 1 : ℕ)) :=
  uniformAverage_sigma (k + 1) card_marked_fiber f

theorem exterior_average_fibers {d k : ℕ} (f : Exterior d k → ℝ) :
    uniformAverage f = uniformAverage
      (fun s : Subset d k => (∑ j, f ⟨s, j⟩) / (d - k : ℕ)) :=
  uniformAverage_sigma (d - k) card_exterior_fiber f

/-- Under Q there is at most one distinguished active point for each W. -/
theorem marked_event_unique {d : ℕ} (w a : Finset (Fin d))
    {i j : Fin d} (_hi : i ∈ w) (hj : j ∈ w)
    (_hiA : i ∈ a) (hjA : j ∈ a)
    (hdis : Disjoint (w.erase i) a) (_hdis' : Disjoint (w.erase j) a) : i = j := by
  by_contra hij
  exact Finset.disjoint_left.mp hdis (Finset.mem_erase.mpr ⟨Ne.symm hij, hj⟩) hjA

theorem marked_event_card_le_one {d : ℕ} (w a : Finset (Fin d)) :
    (w.filter fun j => Disjoint (w.erase j) a ∧ j ∈ a).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro i hi j hj
  simp only [Finset.mem_filter] at hi hj
  exact marked_event_unique w a hi.1 hj.1 hi.2.2 hj.2.2 hi.2.1 hj.2.1

/-- On P's exhaustion event every active point is outside the favorable set. -/
theorem exterior_event_filter {d : ℕ} (s a : Finset (Fin d))
    (hsa : Disjoint s a) :
    (Finset.univ.filter fun j => j ∉ s ∧ j ∈ a) = a := by
  ext j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨And.right, fun hj => ⟨fun hs => Finset.disjoint_left.mp hsa hs hj, hj⟩⟩

theorem exterior_event_card {d : ℕ} (s a : Finset (Fin d))
    (hsa : Disjoint s a) :
    (Finset.univ.filter fun j => j ∉ s ∧ j ∈ a).card = a.card := by
  rw [exterior_event_filter s a hsa]

theorem uniformAverage_indicator_finset {d : ℕ} (s : Finset (Fin d))
    (p : Fin d → Prop) [DecidablePred p] :
    uniformAverage (fun j : {j : Fin d // j ∈ s} => if p j.val then 1 else 0) =
      (s.filter p).card / (s.card : ℝ) := by
  unfold uniformAverage
  dsimp only
  rw [Fintype.card_coe]
  have hsum : (∑ j : {j : Fin d // j ∈ s}, if p j.val then (1 : ℝ) else 0) =
      ∑ j ∈ s, if p j then (1 : ℝ) else 0 :=
    Finset.sum_coe_sort s (fun j => if p j then (1 : ℝ) else 0)
  rw [hsum, Finset.sum_boole]

/-- The Q-side conditional probability is at most 1/(k+1). -/
theorem marked_event_average_le {d k : ℕ} (w : Subset d (k + 1))
    (a : Finset (Fin d)) :
    uniformAverage (fun j : {j : Fin d // j ∈ w.val} =>
      if Disjoint (w.val.erase j.val) a ∧ j.val ∈ a then 1 else 0) ≤
      1 / (k + 1 : ℕ) := by
  rw [uniformAverage_indicator_finset w.val
    (fun j => Disjoint (w.val.erase j) a ∧ j ∈ a), w.property]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact_mod_cast marked_event_card_le_one w.val a

/-- The P-side conditional probability is exactly the active fraction among
the points outside S, provided all favorable points are exhausted. -/
theorem exterior_event_average_eq {d k : ℕ} (s : Subset d k)
    (a : Finset (Fin d)) (hsa : Disjoint s.val a) :
    uniformAverage (fun j : {j : Fin d // j ∉ s.val} =>
      if j.val ∈ a then 1 else 0) = a.card / (d - k : ℕ) := by
  unfold uniformAverage
  dsimp only
  rw [card_exterior_fiber]
  congr 1
  rw [← Finset.sum_subtype (Finset.univ.filter fun j => j ∉ s.val) (by simp)
    (fun j => if j ∈ a then (1 : ℝ) else 0)]
  rw [Finset.sum_boole]
  congr 1
  rw [Finset.filter_filter]
  exact exterior_event_card s.val a hsa

theorem exterior_event_average_ge_three_quarters {d k : ℕ}
    (hk : k < d) (s : Subset d k) (a : Finset (Fin d))
    (hsa : Disjoint s.val a) (ha : 3 * d ≤ 4 * a.card) :
    (3 : ℝ) / 4 ≤ uniformAverage
      (fun j : {j : Fin d // j ∉ s.val} => if j.val ∈ a then 1 else 0) := by
  rw [exterior_event_average_eq s a hsa]
  have hden : (0 : ℝ) < (d - k : ℕ) := by exact_mod_cast Nat.sub_pos_of_lt hk
  apply (le_div_iff₀ hden).mpr
  have hsub : ((d - k : ℕ) : ℝ) ≤ d := by exact_mod_cast Nat.sub_le d k
  have ha' : (3 : ℝ) * d ≤ 4 * a.card := by exact_mod_cast ha
  linarith

theorem exterior_joint_event_average_ge {d k : ℕ}
    (hk : k < d) (s : Subset d k) (a : Finset (Fin d))
    (ha : 3 * d ≤ 4 * a.card) :
    (3 : ℝ) / 4 * (if Disjoint s.val a then 1 else 0) ≤ uniformAverage
      (fun j : {j : Fin d // j ∉ s.val} =>
        if Disjoint s.val a ∧ j.val ∈ a then 1 else 0) := by
  by_cases hsa : Disjoint s.val a
  · simpa only [hsa, true_and, ite_true, mul_one] using
      exterior_event_average_ge_three_quarters hk s a hsa ha
  · simp [hsa, uniformAverage]

end
end MsetsPaper.Lower.WJ
