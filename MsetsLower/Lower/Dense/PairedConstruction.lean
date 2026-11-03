import MsetsLower.Core.Protocol

/-!
# The finite paired construction in the dense action-count lower bound

This file isolates the deterministic, one-round part of
`prop:lower-bounded-action` (manuscript lines 5028--5392).  The random item
`J_t \in [2k]` is represented without an indexing convention by a pair number
and a Boolean side.  All expectations below are literal finite sums under
`p_\theta`; no KL, sequential-law, or Assouad argument is used here.
-/

namespace MsetsLower.Lower.Dense

open MsetsLower
open ProbabilityTheory
open scoped BigOperators

noncomputable section

/-- The two values of a Rademacher sign. -/
inductive PairSign
  | neg
  | pos
  deriving DecidableEq

instance : Fintype PairSign where
  elems := {.neg, .pos}
  complete s := by cases s <;> simp

namespace PairSign

/-- The real value of a paired hypothesis coordinate. -/
def value : PairSign → Real
  | neg => -1
  | pos => 1

@[simp] theorem value_neg : value neg = (-1 : Real) := rfl
@[simp] theorem value_pos : value pos = (1 : Real) := rfl

theorem value_mem (s : PairSign) : value s = -1 ∨ value s = 1 := by
  cases s <;> simp

theorem value_sq (s : PairSign) : value s ^ 2 = (1 : Real) := by
  cases s <;> norm_num

@[simp] theorem value_mul_self (s : PairSign) :
    value s * value s = (1 : Real) := by
  simpa [pow_two] using value_sq s

end PairSign

/-- A coordinate in the first `D = 2k` items, represented as a pair and a
side.  `false` is item `2g-1` in the manuscript's one-based notation and
`true` is item `2g`. -/
abbrev PairItem (k : Nat) := Fin k × Bool

/-- Zero-based side offset inside a pair. -/
def pairSide : Bool → Nat
  | false => 0
  | true => 1

/-- Embed the paired block into the first `2k` coordinates of `Fin n`. -/
def pairCoordinate {n k : Nat} (hD : 2 * k ≤ n) (j : PairItem k) : Fin n :=
  ⟨2 * j.1.1 + pairSide j.2, by
    rcases j with ⟨g, b⟩
    cases b <;> simp [pairSide] <;> omega⟩

@[simp] theorem pairCoordinate_left {n k : Nat} (hD : 2 * k ≤ n)
    (g : Fin k) :
    (pairCoordinate hD (g, false)).1 = 2 * g.1 := by
  simp [pairCoordinate, pairSide]

@[simp] theorem pairCoordinate_right {n k : Nat} (hD : 2 * k ≤ n)
    (g : Fin k) :
    (pairCoordinate hD (g, true)).1 = 2 * g.1 + 1 := by
  simp [pairCoordinate, pairSide]

theorem pairCoordinate_injective {n k : Nat} (hD : 2 * k ≤ n) :
    Function.Injective (pairCoordinate hD) := by
  rintro ⟨g, b⟩ ⟨g', b'⟩ h
  apply Prod.ext
  · apply Fin.ext
    have hv := congrArg Fin.val h
    cases b <;> cases b' <;> simp [pairCoordinate, pairSide] at hv ⊢ <;> omega
  · have hv := congrArg Fin.val h
    cases b <;> cases b' <;> simp [pairCoordinate, pairSide] at hv ⊢ <;> omega

/-- Equation `eq:lower-dense-epsilon`: the literal dense-construction
perturbation. -/
def denseEpsilon (k T : Nat) : Real :=
  (k : Real) / (8 * Real.sqrt T)

theorem lower_dense_epsilon (k T : Nat) :
    denseEpsilon k T = (k : Real) / (8 * Real.sqrt T) :=
  rfl

/-- The paper's horizon and action-size hypotheses imply the stated
`epsilon ≤ 1/16` bound. -/
theorem denseEpsilon_le_sixteenth {n k T : Nat}
    (hk : 1 ≤ k) (hk_half : k ≤ n / 2) (hT : n ^ 2 ≤ T) :
    denseEpsilon k T ≤ (1 : Real) / 16 := by
  have hkn : 2 * k ≤ n := by omega
  have hn : 0 ≤ (n : Real) := Nat.cast_nonneg n
  have hk_real : (2 : Real) * k ≤ n := by exact_mod_cast hkn
  have hT_real : (n : Real) ^ 2 ≤ (T : Real) := by exact_mod_cast hT
  have hsqrt_n : Real.sqrt ((n : Real) ^ 2) = n := by
    rw [Real.sqrt_sq_eq_abs, abs_of_nonneg hn]
  have hn_sqrt : (n : Real) ≤ Real.sqrt T := by
    rw [← hsqrt_n]
    exact Real.sqrt_le_sqrt hT_real
  have hk_sqrt : (2 : Real) * k ≤ Real.sqrt T := hk_real.trans hn_sqrt
  have hsqrt_pos : 0 < Real.sqrt T := by
    have hk_pos : (0 : Real) < k := by exact_mod_cast hk
    linarith
  rw [denseEpsilon]
  apply (div_le_iff₀ (by positivity : (0 : Real) < 8 * Real.sqrt T)).2
  nlinarith

theorem denseEpsilon_nonneg (k T : Nat) : 0 ≤ denseEpsilon k T := by
  exact div_nonneg (Nat.cast_nonneg k)
    (mul_nonneg (by norm_num) (Real.sqrt_nonneg T))

theorem denseEpsilon_mem_Icc_zero_one {n k T : Nat}
    (hk : 1 ≤ k) (hk_half : k ≤ n / 2) (hT : n ^ 2 ≤ T) :
    denseEpsilon k T ∈ Set.Icc (0 : Real) 1 := by
  exact ⟨denseEpsilon_nonneg k T,
    (denseEpsilon_le_sixteenth hk hk_half hT).trans (by norm_num)⟩

/-- The mass function `p_θ` from lines 5062--5071. -/
def pairedProbability {k : Nat} (θ : Fin k → PairSign) (ε : Real)
    (j : PairItem k) : Real :=
  match j.2 with
  | false => (1 - ε * PairSign.value (θ j.1)) / (2 * (k : Real))
  | true => (1 + ε * PairSign.value (θ j.1)) / (2 * (k : Real))

@[simp] theorem pairedProbability_left {k : Nat} (θ : Fin k → PairSign)
    (ε : Real) (g : Fin k) :
    pairedProbability θ ε (g, false) =
      (1 - ε * PairSign.value (θ g)) / (2 * (k : Real)) :=
  rfl

@[simp] theorem pairedProbability_right {k : Nat} (θ : Fin k → PairSign)
    (ε : Real) (g : Fin k) :
    pairedProbability θ ε (g, true) =
      (1 + ε * PairSign.value (θ g)) / (2 * (k : Real)) :=
  rfl

/-- The two probabilities in one pair have mass `1/k`. -/
theorem pairedProbability_pair_sum {k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) (ε : Real) (g : Fin k) :
    pairedProbability θ ε (g, false) + pairedProbability θ ε (g, true) =
      1 / (k : Real) := by
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [pairedProbability_left, pairedProbability_right]
  field_simp
  ring

/-- Thus the displayed `p_θ` is normalized. -/
theorem pairedProbability_sum {k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) (ε : Real) :
    ∑ j : PairItem k, pairedProbability θ ε j = 1 := by
  rw [Fintype.sum_prod_type]
  have hpair (g : Fin k) :
      ∑ b : Bool, pairedProbability θ ε (g, b) = 1 / (k : Real) := by
    rw [Fintype.sum_bool]
    linarith [pairedProbability_pair_sum hk θ ε g]
  simp_rw [hpair]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp [hk0]

/-- Nonnegativity of the displayed masses in the range used by the paper. -/
theorem pairedProbability_nonneg {k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) {ε : Real} (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (j : PairItem k) :
    0 ≤ pairedProbability θ ε j := by
  rcases j with ⟨g, b⟩
  cases b
  · cases hθ : θ g
    · rw [pairedProbability_left, hθ, PairSign.value_neg]
      exact div_nonneg (by linarith) (by positivity)
    · rw [pairedProbability_left, hθ, PairSign.value_pos]
      exact div_nonneg (by linarith) (by positivity)
  · cases hθ : θ g
    · rw [pairedProbability_right, hθ, PairSign.value_neg]
      exact div_nonneg (by linarith) (by positivity)
    · rw [pairedProbability_right, hθ, PairSign.value_pos]
      exact div_nonneg (by linarith) (by positivity)

/-- The genuine finite probability mass function determined by the displayed
weights `p_θ`. -/
def pairedPMF {k : Nat} (hk : 1 ≤ k) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) : PMF (PairItem k) :=
  PMF.ofFintype (fun j => ENNReal.ofReal (pairedProbability θ ε j)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun j _ => pairedProbability_nonneg hk θ hε0 hε1 j),
      pairedProbability_sum hk θ ε]
    norm_num)

@[simp] theorem pairedPMF_apply {k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (j : PairItem k) :
    pairedPMF hk θ ε hε0 hε1 j =
      ENNReal.ofReal (pairedProbability θ ε j) :=
  rfl

theorem pairedPMF_toReal {k : Nat} (hk : 1 ≤ k)
    (θ : Fin k → PairSign) (ε : Real) (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (j : PairItem k) :
    (pairedPMF hk θ ε hε0 hε1 j).toReal = pairedProbability θ ε j := by
  rw [pairedPMF_apply, ENNReal.toReal_ofReal
    (pairedProbability_nonneg hk θ hε0 hε1 j)]

/-- The PMF used by the manuscript after substituting
`ε = k/(8√T)`. -/
def densePairedPMF {n k T : Nat} (hk : 1 ≤ k) (hk_half : k ≤ n / 2)
    (hT : n ^ 2 ≤ T) (θ : Fin k → PairSign) : PMF (PairItem k) :=
  pairedPMF hk θ (denseEpsilon k T) (denseEpsilon_nonneg k T)
    ((denseEpsilon_le_sixteenth hk hk_half hT).trans (by norm_num))

/-- The first `D = 2k` coordinates, enumerated by their pair and side. -/
def firstDBlock {n k : Nat} (hD : 2 * k ≤ n) : Finset (Fin n) :=
  Finset.univ.image (pairCoordinate hD)

/-- The paired enumeration is exactly the initial coordinate block
`{0, ..., 2k-1}`. -/
theorem mem_firstDBlock_iff {n k : Nat} (hD : 2 * k ≤ n) (i : Fin n) :
    i ∈ firstDBlock hD ↔ i.1 < 2 * k := by
  classical
  constructor
  · rw [firstDBlock, Finset.mem_image]
    rintro ⟨⟨g, b⟩, -, rfl⟩
    cases b
    · simp [pairCoordinate, pairSide]
    · simp [pairCoordinate, pairSide]
      omega
  · intro hi
    have hdiv := Nat.div_add_mod i.1 2
    have hmod := Nat.mod_lt i.1 (by omega : 0 < 2)
    have hg : i.1 / 2 < k := by omega
    let g : Fin k := ⟨i.1 / 2, hg⟩
    rw [firstDBlock, Finset.mem_image]
    by_cases hzero : i.1 % 2 = 0
    · refine ⟨(g, false), Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp [pairCoordinate, pairSide, g]
      omega
    · have hone : i.1 % 2 = 1 := by omega
      refine ⟨(g, true), Finset.mem_univ _, ?_⟩
      apply Fin.ext
      simp [pairCoordinate, pairSide, g]
      omega

theorem card_firstDBlock {n k : Nat} (hD : 2 * k ≤ n) :
    (firstDBlock hD).card = 2 * k := by
  classical
  rw [firstDBlock, Finset.card_image_of_injective _
    (pairCoordinate_injective hD), Finset.card_univ]
  simp [Nat.mul_comm]

/-- The indicator `1_[D]` in equation `eq:paired-loss`. -/
def firstDIndicator {n k : Nat} (hD : 2 * k ≤ n) (i : Fin n) : Real :=
  if i ∈ firstDBlock hD then 1 else 0

/-- The standard basis vector at the sampled paired item. -/
def pairBasis {n k : Nat} (hD : 2 * k ≤ n) (J : PairItem k)
    (i : Fin n) : Real :=
  if i = pairCoordinate hD J then 1 else 0

/-- Equation `eq:paired-loss`, with `D` definitionally equal to `2k`. -/
def pairedLoss {n k : Nat} (hD : 2 * k ≤ n) (J : PairItem k) :
    Fin n → Real :=
  fun i =>
    1 / (3 * (k : Real)) +
      (2 / 3 : Real) *
        (pairBasis hD J i - (1 / (2 * (k : Real))) * firstDIndicator hD i)

theorem paired_loss {n k : Nat} (hD : 2 * k ≤ n) (J : PairItem k) :
    pairedLoss hD J = fun i =>
      1 / (3 * (k : Real)) +
        (2 / 3 : Real) *
          (pairBasis hD J i -
            (1 / (2 * (k : Real))) * firstDIndicator hD i) :=
  rfl

/-- `S = A ∩ [D]` from the manuscript. -/
def pairedSection {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) : Finset (Fin n) :=
  A.1 ∩ firstDBlock hD

theorem pairedSection_eq_filter {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) :
    pairedSection hD A = A.1.filter (fun i => i.1 < 2 * k) := by
  ext i
  simp [pairedSection, mem_firstDBlock_iff]

theorem pairCoordinate_mem_firstDBlock {n k : Nat} (hD : 2 * k ≤ n)
    (j : PairItem k) : pairCoordinate hD j ∈ firstDBlock hD := by
  classical
  exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

@[simp] theorem pairCoordinate_mem_pairedSection_iff {n k : Nat}
    (hD : 2 * k ≤ n) (A : MSetAction n k) (j : PairItem k) :
    pairCoordinate hD j ∈ pairedSection hD A ↔
      pairCoordinate hD j ∈ A.1 := by
  simp [pairedSection, pairCoordinate_mem_firstDBlock]

/-- Indicator of the manuscript event `J ∈ S`, where `S = A ∩ [D]`. -/
def pairedSelected {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (j : PairItem k) : Real :=
  if pairCoordinate hD j ∈ pairedSection hD A then 1 else 0

/-- The cardinality `h = |S|`. -/
def pairedSectionCard {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) : Nat :=
  (pairedSection hD A).card

theorem pairedSectionCard_le {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) :
    pairedSectionCard hD A ≤ k := by
  dsimp [pairedSectionCard, pairedSection]
  exact (Finset.card_le_card Finset.inter_subset_left).trans_eq A.2

/-- The size of `S` is the number of paired coordinates selected by `A`. -/
theorem pairedSectionCard_eq_indicator_sum {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) :
    (pairedSectionCard hD A : Real) =
      ∑ j : PairItem k, pairedSelected hD A j := by
  classical
  let U : Finset (PairItem k) :=
    Finset.univ.filter fun j => pairCoordinate hD j ∈ A.1
  have himage : U.image (pairCoordinate hD) = pairedSection hD A := by
    ext i
    simp only [U, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and,
      pairedSection, Finset.mem_inter, firstDBlock]
    constructor
    · rintro ⟨j, hjA, hji⟩
      exact ⟨hji ▸ hjA, ⟨j, hji⟩⟩
    · rintro ⟨hiA, ⟨j, hji⟩⟩
      exact ⟨j, hji.symm ▸ hiA, hji⟩
  change ((pairedSection hD A).card : Real) = _
  rw [← himage, Finset.card_image_of_injective _
    (pairCoordinate_injective hD)]
  simp [U, pairedSelected]

/-- Summing a constant item loss over an exact `k`-set. -/
theorem actionLoss_const {n k : Nat} (A : MSetAction n k) (c : Real) :
    actionLoss A (fun _ => c) = (k : Real) * c := by
  rw [actionLoss_eq_finset_sum]
  simp [A.2]

theorem actionLoss_mul_left {n k : Nat} (A : MSetAction n k)
    (c : Real) (f : Fin n → Real) :
    actionLoss A (fun i => c * f i) = c * actionLoss A f := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum, Finset.mul_sum]

theorem actionLoss_sub {n k : Nat} (A : MSetAction n k)
    (f g : Fin n → Real) :
    actionLoss A (fun i => f i - g i) = actionLoss A f - actionLoss A g := by
  rw [actionLoss_eq_finset_sum, actionLoss_eq_finset_sum,
    actionLoss_eq_finset_sum, Finset.sum_sub_distrib]

/-- An action sees the sampled basis vector exactly when it contains the
sampled coordinate. -/
theorem actionLoss_pairBasis {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (J : PairItem k) :
    actionLoss A (pairBasis hD J) =
      if pairCoordinate hD J ∈ A.1 then 1 else 0 := by
  classical
  rw [actionLoss_eq_finset_sum]
  by_cases hJ : pairCoordinate hD J ∈ A.1
  · simp [pairBasis, hJ]
  · simp [pairBasis, hJ]

/-- Summing `1_[D]` over an action gives `h = |S|`. -/
theorem actionLoss_firstDIndicator {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) :
    actionLoss A (firstDIndicator hD) = (pairedSectionCard hD A : Real) := by
  classical
  rw [actionLoss_eq_finset_sum]
  simp [firstDIndicator, pairedSectionCard, pairedSection]

/-- Equation `eq:lower-dense-action-loss`. -/
theorem lower_dense_action_loss {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (A : MSetAction n k) (J : PairItem k) :
    actionLoss A (pairedLoss hD J) =
      (1 : Real) / 3 + (2 / 3 : Real) *
        (pairedSelected hD A J -
          (pairedSectionCard hD A : Real) / (2 * (k : Real))) := by
  classical
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  change actionLoss A (fun i =>
      1 / (3 * (k : Real)) + (2 / 3 : Real) *
        (pairBasis hD J i -
          (1 / (2 * (k : Real))) * firstDIndicator hD i)) = _
  simp only [pairedSelected, pairCoordinate_mem_pairedSection_iff]
  rw [actionLoss_add, actionLoss_const, actionLoss_mul_left, actionLoss_sub,
    actionLoss_pairBasis, actionLoss_mul_left, actionLoss_firstDIndicator]
  field_simp

/-- Every exact action loss in the paired construction belongs to `[0,1]`,
as asserted in `eq:lower-dense-action-loss`. -/
theorem lower_dense_action_loss_mem_Icc {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (A : MSetAction n k) (J : PairItem k) :
    actionLoss A (pairedLoss hD J) ∈ Set.Icc (0 : Real) 1 := by
  rw [lower_dense_action_loss hk hD A J]
  have hk_pos : (0 : Real) < k := by exact_mod_cast hk
  have hh_nat := pairedSectionCard_le hD A
  have hh_nonneg : (0 : Real) ≤ pairedSectionCard hD A := Nat.cast_nonneg _
  have hh_le : (pairedSectionCard hD A : Real) ≤ k := by exact_mod_cast hh_nat
  have hden : (0 : Real) < 2 * k := mul_pos (by norm_num) hk_pos
  have hratio_nonneg :
      0 ≤ (pairedSectionCard hD A : Real) / (2 * (k : Real)) :=
    div_nonneg hh_nonneg hden.le
  have hratio_le_half :
      (pairedSectionCard hD A : Real) / (2 * (k : Real)) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).2
    nlinarith
  by_cases hJ : pairCoordinate hD J ∈ A.1 <;>
    simp [pairedSelected, pairCoordinate_mem_pairedSection_iff, hJ] <;>
    constructor <;> nlinarith

/-- The manuscript's `z_g(S)`, with the same left-minus-right convention. -/
def pairedZ {n k : Nat} (hD : 2 * k ≤ n) (A : MSetAction n k)
    (g : Fin k) : Real :=
  pairedSelected hD A (g, false) - pairedSelected hD A (g, true)

/-- The deterministic quantity `h_θ(S) = k - Σ_g θ_g z_g(S)`. -/
def pairedDisagreement {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) : Real :=
  (k : Real) - ∑ g : Fin k, PairSign.value (θ g) * pairedZ hD A g

/-- The Bernoulli parameter `P_θ(J ∈ S)` as a finite sum. -/
def pairedBernoulliParameter {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (ε : Real) (A : MSetAction n k) : Real :=
  ∑ j : PairItem k, pairedProbability θ ε j * pairedSelected hD A j

private theorem pairedProbability_selected_pair {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (A : MSetAction n k) (g : Fin k) :
    pairedProbability θ ε (g, false) * pairedSelected hD A (g, false) +
        pairedProbability θ ε (g, true) * pairedSelected hD A (g, true) =
      (pairedSelected hD A (g, false) + pairedSelected hD A (g, true)) /
          (2 * (k : Real)) -
        ε / (2 * (k : Real)) *
          (PairSign.value (θ g) * pairedZ hD A g) := by
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  simp only [pairedProbability_left, pairedProbability_right, pairedZ]
  field_simp
  ring

/-- Equation `eq:lower-dense-bernoulli-parameter`. -/
theorem lower_dense_bernoulli_parameter {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (A : MSetAction n k) :
    pairedBernoulliParameter hD θ ε A =
      (pairedSectionCard hD A : Real) / (2 * (k : Real)) -
        ε / (2 * (k : Real)) *
          ∑ g : Fin k, PairSign.value (θ g) * pairedZ hD A g := by
  have hcard :
      (pairedSectionCard hD A : Real) =
        ∑ g : Fin k,
          (pairedSelected hD A (g, false) +
            pairedSelected hD A (g, true)) := by
    rw [pairedSectionCard_eq_indicator_sum hD A, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro g _
    rw [Fintype.sum_bool]
    simp only [pairedSelected]
    ring
  rw [pairedBernoulliParameter, Fintype.sum_prod_type]
  simp_rw [Fintype.sum_bool]
  simp_rw [add_comm
    (pairedProbability θ ε (_, true) * pairedSelected hD A (_, true))]
  simp_rw [pairedProbability_selected_pair hk hD θ ε A]
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, ← Finset.mul_sum, ← hcard]

theorem pairedSelected_mem_Icc {n k : Nat} (hD : 2 * k ≤ n)
    (A : MSetAction n k) (j : PairItem k) :
    pairedSelected hD A j ∈ Set.Icc (0 : Real) 1 := by
  by_cases hj : pairCoordinate hD j ∈ A.1 <;> simp [pairedSelected, hj]

/-- As a check on the probability interpretation, the finite parameter lies
in `[0,1]` whenever the displayed masses do. -/
theorem pairedBernoulliParameter_mem_Icc {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    pairedBernoulliParameter hD θ ε A ∈ Set.Icc (0 : Real) 1 := by
  rw [pairedBernoulliParameter]
  constructor
  · exact Finset.sum_nonneg fun j _ =>
      mul_nonneg (pairedProbability_nonneg hk θ hε0 hε1 j)
        (pairedSelected_mem_Icc hD A j).1
  · calc
      (∑ j : PairItem k,
          pairedProbability θ ε j * pairedSelected hD A j) ≤
          ∑ j : PairItem k, pairedProbability θ ε j * 1 :=
        Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
          (pairedSelected_mem_Icc hD A j).2
          (pairedProbability_nonneg hk θ hε0 hε1 j)
      _ = 1 := by simpa using pairedProbability_sum hk θ ε

/-- The one-round expectation of an exact action under the genuine finite
law `p_θ`.  Its proof arguments enforce the probability range. -/
def pairedExpectedActionLoss {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) : Real :=
  ∑ j : PairItem k,
    (pairedPMF hk θ ε hε0 hε1 j).toReal * actionLoss A (pairedLoss hD j)

/-- In the probability range, the preceding weighted sum is literally the
finite expectation under `pairedPMF`. -/
theorem pairedExpectedActionLoss_eq_pmf_sum {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) (A : MSetAction n k) :
    pairedExpectedActionLoss hk hD θ ε hε0 hε1 A =
      ∑ j : PairItem k,
        (pairedPMF hk θ ε hε0 hε1 j).toReal *
          actionLoss A (pairedLoss hD j) := by
  rfl

private theorem sum_weight_affine {ι : Type*} [Fintype ι]
    (p q : ι → Real) (a c r : Real) :
    (∑ j : ι, p j * (a + c * (q j - r))) =
      a * (∑ j : ι, p j) +
        c * ((∑ j : ι, p j * q j) - r * ∑ j : ι, p j) := by
  classical
  calc
    (∑ j : ι, p j * (a + c * (q j - r))) =
        ∑ j : ι, (a * p j + c * (p j * q j) - (c * r) * p j) := by
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = a * (∑ j : ι, p j) +
        c * ((∑ j : ι, p j * q j) - r * ∑ j : ι, p j) := by
      rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
      ring

/-- The finite expectation first reduces to the Bernoulli parameter in exactly
the way described after `eq:lower-dense-action-loss`. -/
theorem pairedExpectedActionLoss_eq_parameter {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : MSetAction n k) :
    pairedExpectedActionLoss hk hD θ ε hε0 hε1 A =
      (1 : Real) / 3 + (2 / 3 : Real) *
        (pairedBernoulliParameter hD θ ε A -
          (pairedSectionCard hD A : Real) / (2 * (k : Real))) := by
  have hsum := pairedProbability_sum hk θ ε
  rw [pairedExpectedActionLoss]
  simp_rw [pairedPMF_toReal]
  simp_rw [lower_dense_action_loss hk hD A]
  change (∑ j : PairItem k,
      pairedProbability θ ε j *
        ((1 : Real) / 3 + (2 / 3 : Real) *
          (pairedSelected hD A j -
            (pairedSectionCard hD A : Real) / (2 * (k : Real))))) = _
  rw [sum_weight_affine]
  simp only [hsum, mul_one]
  rfl

/-- A convenient closed form for the expected one-round action loss. -/
theorem pairedExpectedActionLoss_closed {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : MSetAction n k) :
    pairedExpectedActionLoss hk hD θ ε hε0 hε1 A =
      (1 : Real) / 3 -
        (2 * ε) / (3 * (2 * (k : Real))) *
          ∑ g : Fin k, PairSign.value (θ g) * pairedZ hD A g := by
  rw [pairedExpectedActionLoss_eq_parameter hk hD θ ε hε0 hε1 A,
    lower_dense_bernoulli_parameter hk hD θ ε A]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp
  ring

/-- The side selected by the fixed comparator: it is the less likely member
of its pair. -/
def lessLikelySide : PairSign → Bool
  | PairSign.neg => true
  | PairSign.pos => false

/-- The less likely item of pair `g` under hypothesis `θ`. -/
def pairedChosenItem {k : Nat} (θ : Fin k → PairSign) (g : Fin k) :
    PairItem k :=
  (g, lessLikelySide (θ g))

theorem pairedChosenItem_injective {k : Nat} (θ : Fin k → PairSign) :
    Function.Injective (pairedChosenItem θ) := by
  intro g g' h
  exact congrArg Prod.fst h

/-- The fixed exact `k`-set `x^θ` from lines 5129--5131. -/
def pairedComparator {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) : MSetAction n k :=
  ⟨Finset.univ.image fun g => pairCoordinate hD (pairedChosenItem θ g), by
    rw [Finset.card_image_of_injective]
    · simp
    · exact (pairCoordinate_injective hD).comp
        (pairedChosenItem_injective θ)⟩

theorem pairCoordinate_mem_pairedComparator_iff {n k : Nat}
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (j : PairItem k) :
    pairCoordinate hD j ∈ (pairedComparator hD θ).1 ↔
      j.2 = lessLikelySide (θ j.1) := by
  classical
  simp only [pairedComparator, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨g, hg⟩
    have hitem : pairedChosenItem θ g = j :=
      pairCoordinate_injective hD hg
    have hfirst : g = j.1 := congrArg Prod.fst hitem
    have hsecond : lessLikelySide (θ g) = j.2 := congrArg Prod.snd hitem
    simpa [hfirst] using hsecond.symm
  · intro hside
    refine ⟨j.1, ?_⟩
    apply congrArg (pairCoordinate hD)
    apply Prod.ext
    · rfl
    · simpa [pairedChosenItem] using hside.symm

/-- On the comparator, `z_g = θ_g` for every pair. -/
theorem pairedZ_comparator {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (g : Fin k) :
    pairedZ hD (pairedComparator hD θ) g = PairSign.value (θ g) := by
  cases hθ : θ g <;>
    simp [pairedZ, pairedSelected, pairCoordinate_mem_pairedComparator_iff,
      lessLikelySide, hθ]

/-- Consequently `h_θ(x^θ ∩ [D]) = 0`. -/
theorem pairedDisagreement_comparator {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) :
    pairedDisagreement hD θ (pairedComparator hD θ) = 0 := by
  rw [pairedDisagreement]
  simp_rw [pairedZ_comparator]
  simp_rw [PairSign.value_mul_self]
  simp

/-- The expected loss of the fixed comparator is `1/3 - ε/3`. -/
theorem pairedExpectedComparatorLoss {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1) :
    pairedExpectedActionLoss hk hD θ ε hε0 hε1 (pairedComparator hD θ) =
      (1 : Real) / 3 - ε / 3 := by
  rw [pairedExpectedActionLoss_closed hk hD θ ε hε0 hε1]
  simp_rw [pairedZ_comparator]
  simp_rw [PairSign.value_mul_self]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  field_simp

/-- Equation `eq:paired-pseudoregret`, as a literal finite conditional
expectation identity.  Here the past-fixed `S_t` is the arbitrary action `A`.
-/
theorem paired_pseudoregret {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) (ε : Real)
    (hε0 : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : MSetAction n k) :
    (pairedExpectedActionLoss hk hD θ ε hε0 hε1 A -
        pairedExpectedActionLoss hk hD θ ε hε0 hε1
          (pairedComparator hD θ) =
      (2 * ε) / (3 * (2 * (k : Real))) * pairedDisagreement hD θ A) ∧
    (pairedExpectedActionLoss hk hD θ ε hε0 hε1 A -
        pairedExpectedActionLoss hk hD θ ε hε0 hε1
          (pairedComparator hD θ) =
      ε / (3 * (k : Real)) * pairedDisagreement hD θ A) := by
  rw [pairedExpectedActionLoss_closed hk hD θ ε hε0 hε1 A,
    pairedExpectedComparatorLoss hk hD θ ε hε0 hε1]
  have hk0 : (k : Real) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hk)
  constructor <;> simp only [pairedDisagreement] <;> field_simp <;> ring

/-- Each signed pair contribution lies in `[-1,1]`. -/
theorem signed_pairedZ_mem_Icc {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) (g : Fin k) :
    PairSign.value (θ g) * pairedZ hD A g ∈ Set.Icc (-1 : Real) 1 := by
  by_cases hl : pairCoordinate hD (g, false) ∈ A.1
  · by_cases hr : pairCoordinate hD (g, true) ∈ A.1
    · cases θ g <;> simp [pairedZ, pairedSelected, hl, hr]
    · cases θ g <;> simp [pairedZ, pairedSelected, hl, hr]
  · by_cases hr : pairCoordinate hD (g, true) ∈ A.1
    · cases θ g <;> simp [pairedZ, pairedSelected, hl, hr]
    · cases θ g <;> simp [pairedZ, pairedSelected, hl, hr]

/-- The pathwise discrepancy count satisfies the exact range used in
`eq:paired-pseudoregret`. -/
theorem pairedDisagreement_mem_Icc {n k : Nat} (hD : 2 * k ≤ n)
    (θ : Fin k → PairSign) (A : MSetAction n k) :
    pairedDisagreement hD θ A ∈ Set.Icc (0 : Real) (2 * (k : Real)) := by
  have hsum_upper :
      (∑ g : Fin k, PairSign.value (θ g) * pairedZ hD A g) ≤
        ∑ _g : Fin k, (1 : Real) :=
    Finset.sum_le_sum fun g _ => (signed_pairedZ_mem_Icc hD θ A g).2
  have hsum_lower :
      (∑ _g : Fin k, (-1 : Real)) ≤
        ∑ g : Fin k, PairSign.value (θ g) * pairedZ hD A g :=
    Finset.sum_le_sum fun g _ => (signed_pairedZ_mem_Icc hD θ A g).1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one] at hsum_upper
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul] at hsum_lower
  rw [pairedDisagreement]
  constructor <;> nlinarith

/-- The complete interval clause of `eq:paired-pseudoregret`. -/
theorem paired_pseudoregret_mem_Icc {n k : Nat} (hk : 1 ≤ k)
    (hD : 2 * k ≤ n) (θ : Fin k → PairSign) {ε : Real}
    (hε : 0 ≤ ε) (hε1 : ε ≤ 1)
    (A : MSetAction n k) :
    pairedExpectedActionLoss hk hD θ ε hε hε1 A -
        pairedExpectedActionLoss hk hD θ ε hε hε1
          (pairedComparator hD θ) ∈
      Set.Icc (0 : Real) (2 * ε / 3) := by
  rw [(paired_pseudoregret hk hD θ ε hε hε1 A).2]
  have hk_pos : (0 : Real) < k := by exact_mod_cast hk
  have hcoefficient : 0 ≤ ε / (3 * (k : Real)) := by positivity
  have hdis := pairedDisagreement_mem_Icc hD θ A
  constructor
  · exact mul_nonneg hcoefficient hdis.1
  · calc
      ε / (3 * (k : Real)) * pairedDisagreement hD θ A ≤
          ε / (3 * (k : Real)) * (2 * (k : Real)) :=
        mul_le_mul_of_nonneg_left hdis.2 hcoefficient
      _ = 2 * ε / 3 := by
        have hk0 : (k : Real) ≠ 0 := ne_of_gt hk_pos
        field_simp

#print axioms lower_dense_epsilon
#print axioms denseEpsilon_le_sixteenth
#print axioms pairedProbability_sum
#print axioms paired_loss
#print axioms lower_dense_action_loss
#print axioms lower_dense_action_loss_mem_Icc
#print axioms lower_dense_bernoulli_parameter
#print axioms paired_pseudoregret
#print axioms paired_pseudoregret_mem_Icc

end

end MsetsLower.Lower.Dense
