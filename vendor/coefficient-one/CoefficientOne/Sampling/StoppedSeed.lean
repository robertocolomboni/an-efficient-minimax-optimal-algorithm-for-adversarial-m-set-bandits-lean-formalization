import CoefficientOne.Sampling.SeedConditioning

/-!
# The residual seed at a stopping time

We describe the prefix sigma-algebra through its sections at each possible
discrete prefix. Its continuous part consists of arbitrary Borel events in the
revealed uniforms. Partitioning a stopped event over its finite time and prefix
gives the stopped product-seed identity directly, without optional stopping or
an assumption of conditional independence. The value `⊤` means no stop.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace CoefficientOne.Sampling

def prefixKey {n : ℕ} (ℓ : ℕ) (π : Equiv.Perm (Fin n)) : Fin n → Option (Fin n) :=
  fun j => if j.val < ℓ then some (π j) else none

abbrev PrefixKey (n ℓ : ℕ) :=
  {p : Fin n → Option (Fin n) // ∃ π : Equiv.Perm (Fin n), prefixKey ℓ π = p}

instance prefixKey_fintype (n ℓ : ℕ) : Fintype (PrefixKey n ℓ) := Fintype.ofFinite _

def prefixReference {n ℓ : ℕ} (p : PrefixKey n ℓ) : Equiv.Perm (Fin n) :=
  Classical.choose p.property

theorem prefixReference_key {n ℓ : ℕ} (p : PrefixKey n ℓ) :
    prefixKey ℓ (prefixReference p) = p.val := Classical.choose_spec p.property

theorem prefixMatches_iff_key_eq {n ℓ : ℕ} (ρ π : Equiv.Perm (Fin n)) :
    PrefixMatches ℓ ρ π ↔ prefixKey ℓ π = prefixKey ℓ ρ := by
  constructor
  · intro h
    funext j
    by_cases hj : j.val < ℓ <;> simp [prefixKey, hj, h j]
  · intro h j hj
    have he := congrFun h j
    simpa [prefixKey, hj] using he

theorem prefixMatches_reference_iff {n ℓ : ℕ} (p : PrefixKey n ℓ)
    (π : Equiv.Perm (Fin n)) :
    PrefixMatches ℓ (prefixReference p) π ↔ prefixKey ℓ π = p.val := by
  rw [prefixMatches_iff_key_eq, prefixReference_key]

/-- Membership is decided by the revealed indices and revealed uniforms alone. -/
def PrefixObservableEvent {n : ℕ} (ℓ : ℕ) (E : Set (Seed n)) : Prop :=
  ∀ ρ : Equiv.Perm (Fin n), ∃ B : Set (PastUniforms ℓ ρ), MeasurableSet B ∧
    ∀ ω : Seed n, PrefixMatches ℓ ρ ω.1 →
      (ω ∈ E ↔ (splitUniforms ℓ ρ ω.2).1 ∈ B)

def prefixPastSection {n : ℕ} {ℓ : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (ρ : Equiv.Perm (Fin n)) :
    Set (PastUniforms ℓ ρ) := Classical.choose (hE ρ)

theorem measurableSet_prefixPastSection {n : ℕ} {ℓ : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (ρ : Equiv.Perm (Fin n)) :
    MeasurableSet (prefixPastSection hE ρ) := (Classical.choose_spec (hE ρ)).1

theorem prefixPastSection_spec {n : ℕ} {ℓ : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (ρ : Equiv.Perm (Fin n)) (ω : Seed n)
    (hπ : PrefixMatches ℓ ρ ω.1) :
    ω ∈ E ↔ (splitUniforms ℓ ρ ω.2).1 ∈ prefixPastSection hE ρ :=
  (Classical.choose_spec (hE ρ)).2 ω hπ

theorem prefixPastSection_event {n : ℕ} {ℓ : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (p : PrefixKey n ℓ) :
    prefixEvent ℓ (prefixReference p) (prefixPastSection hE (prefixReference p)) Set.univ =
      {ω : Seed n | ω ∈ E ∧ prefixKey ℓ ω.1 = p.val} := by
  rw [prefixPastEvent_eq]
  ext ω
  constructor
  · rintro ⟨hπ, hB⟩
    exact ⟨(prefixPastSection_spec hE _ ω hπ).mpr hB,
      (prefixMatches_reference_iff p ω.1).mp hπ⟩
  · rintro ⟨hω, hp⟩
    have hπ := (prefixMatches_reference_iff p ω.1).mpr hp
    exact ⟨hπ, (prefixPastSection_spec hE _ ω hπ).mp hω⟩

theorem PrefixObservableEvent.measurableSet {n : ℕ} {ℓ : ℕ} {E : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) : MeasurableSet E := by
  have hcover : E = ⋃ p : PrefixKey n ℓ,
      prefixEvent ℓ (prefixReference p) (prefixPastSection hE (prefixReference p)) Set.univ := by
    ext ω
    simp only [mem_iUnion, prefixPastSection_event, mem_setOf_eq]
    constructor
    · intro hω
      exact ⟨⟨prefixKey ℓ ω.1, ⟨ω.1, rfl⟩⟩, hω, rfl⟩
    · rintro ⟨_, hω, _⟩
      exact hω
  rw [hcover]
  exact MeasurableSet.iUnion fun p => measurableSet_prefixEvent _ _
    (measurableSet_prefixPastSection hE _) MeasurableSet.univ

theorem prefixObservableEvent_univ (n ℓ : ℕ) :
    PrefixObservableEvent ℓ (Set.univ : Set (Seed n)) := by
  intro ρ
  exact ⟨Set.univ, MeasurableSet.univ, fun _ _ => Iff.rfl⟩

theorem PrefixObservableEvent.inter {n : ℕ} {ℓ : ℕ} {E F : Set (Seed n)}
    (hE : PrefixObservableEvent ℓ E) (hF : PrefixObservableEvent ℓ F) :
    PrefixObservableEvent ℓ (E ∩ F) := by
  intro ρ
  obtain ⟨B, hB, hBE⟩ := hE ρ
  obtain ⟨C, hC, hCF⟩ := hF ρ
  exact ⟨B ∩ C, hB.inter hC, fun ω hω => and_congr (hBE ω hω) (hCF ω hω)⟩

abbrev StopIndex (n : ℕ) := (t : Fin (n + 1)) × PrefixKey n t.val

def stoppedSlice {n : ℕ} (τ : Seed n → WithTop ℕ) (E : Set (Seed n))
    (a : StopIndex n) : Set (Seed n) :=
  {ω | ω ∈ E ∧ τ ω = (a.1.val : WithTop ℕ) ∧ prefixKey a.1.val ω.1 = a.2.val}

theorem stoppedSlice_pairwiseDisjoint {n : ℕ} (τ : Seed n → WithTop ℕ)
    (E : Set (Seed n)) : Pairwise (fun a b : StopIndex n =>
      Disjoint (stoppedSlice τ E a) (stoppedSlice τ E b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro ω ha hb
  have ht : a.1 = b.1 := by
    apply Fin.ext
    exact WithTop.coe_injective (ha.2.1.symm.trans hb.2.1)
  cases a with
  | mk ta pa =>
    cases b with
    | mk tb pb =>
      dsimp at ht
      subst tb
      have hp : pa = pb := Subtype.ext (ha.2.2.symm.trans hb.2.2)
      exact hab (hp ▸ rfl)

theorem iUnion_stoppedSlice {n : ℕ} (τ : Seed n → WithTop ℕ) (E : Set (Seed n))
    (hbound : ∀ ω, τ ω ≠ ⊤ → τ ω ≤ (n : WithTop ℕ)) :
    (⋃ a : StopIndex n, stoppedSlice τ E a) = E ∩ {ω | τ ω ≠ ⊤} := by
  ext ω
  simp only [mem_iUnion, stoppedSlice, mem_setOf_eq, mem_inter_iff]
  constructor
  · rintro ⟨a, hE, ht, _⟩
    exact ⟨hE, ht ▸ WithTop.coe_ne_top⟩
  · rintro ⟨hE, ht⟩
    obtain ⟨t, htt⟩ := WithTop.ne_top_iff_exists.mp ht
    have htn : t ≤ n := WithTop.coe_le_coe.mp (htt ▸ hbound ω ht)
    refine ⟨⟨⟨t, by omega⟩, ⟨prefixKey t ω.1, ⟨ω.1, rfl⟩⟩⟩, hE, ?_, rfl⟩
    exact htt.symm

/-- A stopped past event: its intersection with each finite stopping time is prefix observable. -/
def StoppedObservableEvent {n : ℕ} (τ : Seed n → WithTop ℕ) (E : Set (Seed n)) : Prop :=
  ∀ t : Fin (n + 1), PrefixObservableEvent t.val (E ∩ {ω | τ ω = (t.val : WithTop ℕ)})

def stoppedPastSection {n : ℕ} {τ : Seed n → WithTop ℕ} {E : Set (Seed n)}
    (hE : StoppedObservableEvent τ E) (a : StopIndex n) :
    Set (PastUniforms a.1.val (prefixReference a.2)) :=
  prefixPastSection (hE a.1) (prefixReference a.2)

theorem stoppedPastSection_event {n : ℕ} {τ : Seed n → WithTop ℕ} {E : Set (Seed n)}
    (hE : StoppedObservableEvent τ E) (a : StopIndex n) :
    prefixEvent a.1.val (prefixReference a.2) (stoppedPastSection hE a) Set.univ =
      stoppedSlice τ E a := by
  rw [stoppedPastSection, prefixPastSection_event]
  ext ω
  simp only [mem_setOf_eq, mem_inter_iff, stoppedSlice, and_assoc]

theorem measurableSet_stoppedSlice {n : ℕ} {τ : Seed n → WithTop ℕ} {E : Set (Seed n)}
    (hE : StoppedObservableEvent τ E) (a : StopIndex n) :
    MeasurableSet (stoppedSlice τ E a) := by
  rw [← stoppedPastSection_event hE a]
  exact measurableSet_prefixEvent _ _ (measurableSet_prefixPastSection _ _) MeasurableSet.univ

def stoppedFutureEvent {n : ℕ} {τ : Seed n → WithTop ℕ} {E : Set (Seed n)}
    (hE : StoppedObservableEvent τ E)
    (C : (a : StopIndex n) → Set (PrefixOrders a.1.val (prefixReference a.2) ×
      FutureUniforms a.1.val (prefixReference a.2))) : Set (Seed n) :=
  ⋃ a : StopIndex n,
    prefixEvent a.1.val (prefixReference a.2) (stoppedPastSection hE a) (C a)

/-- The exact stopped-seed identity, for every Borel event of the stopped past. -/
theorem stoppedSeed_factorization {n : ℕ} {τ : Seed n → WithTop ℕ} {E : Set (Seed n)}
    (hE : StoppedObservableEvent τ E)
    (C : (a : StopIndex n) → Set (PrefixOrders a.1.val (prefixReference a.2) ×
      FutureUniforms a.1.val (prefixReference a.2)))
    (hC : ∀ a, MeasurableSet (C a)) :
    seedMeasure n (stoppedFutureEvent hE C) =
      ∑ a : StopIndex n, seedMeasure n (stoppedSlice τ E a) *
        prefixFutureMeasure a.1.val (prefixReference a.2) (C a) := by
  classical
  have hsub (a : StopIndex n) :
      prefixEvent a.1.val (prefixReference a.2) (stoppedPastSection hE a) (C a) ⊆
        stoppedSlice τ E a := by
    rw [← stoppedPastSection_event hE a]
    exact prefixEvent_subset_past _ _ _ _
  have hd : Pairwise (fun a b : StopIndex n => Disjoint
      (prefixEvent a.1.val (prefixReference a.2) (stoppedPastSection hE a) (C a))
      (prefixEvent b.1.val (prefixReference b.2) (stoppedPastSection hE b) (C b))) := by
    intro a b hab
    exact (stoppedSlice_pairwiseDisjoint τ E hab).mono (hsub a) (hsub b)
  rw [stoppedFutureEvent, measure_iUnion hd]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _
    have hB : MeasurableSet (stoppedPastSection hE a) :=
      measurableSet_prefixPastSection (hE a.1) (prefixReference a.2)
    rw [seedMeasure_prefixEvent_eq_past_mul_future _ _ hB (hC a),
      stoppedPastSection_event hE a]
  · intro a
    exact measurableSet_prefixEvent _ _ (measurableSet_prefixPastSection _ _) (hC a)

/-- Uniform bounds on the residual event remain valid after stopping, including no-stop seeds. -/
theorem stoppedSeed_bound {n : ℕ} {τ : Seed n → WithTop ℕ} {E : Set (Seed n)}
    (hE : StoppedObservableEvent τ E)
    (hbound : ∀ ω, τ ω ≠ ⊤ → τ ω ≤ (n : WithTop ℕ))
    (C : (a : StopIndex n) → Set (PrefixOrders a.1.val (prefixReference a.2) ×
      FutureUniforms a.1.val (prefixReference a.2)))
    (hC : ∀ a, MeasurableSet (C a)) (c : ℝ≥0∞)
    (hc : ∀ a, prefixFutureMeasure a.1.val (prefixReference a.2) (C a) ≤ c) :
    seedMeasure n (stoppedFutureEvent hE C) ≤
      seedMeasure n (E ∩ {ω | τ ω ≠ ⊤}) * c := by
  rw [stoppedSeed_factorization hE C hC]
  calc
    _ ≤ ∑ a : StopIndex n, seedMeasure n (stoppedSlice τ E a) * c :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hc a) zero_le
    _ = (∑ a : StopIndex n, seedMeasure n (stoppedSlice τ E a)) * c :=
      (Finset.sum_mul _ _ _).symm
    _ = seedMeasure n (E ∩ {ω | τ ω ≠ ⊤}) * c := by
      have hsum : (∑ a : StopIndex n, seedMeasure n (stoppedSlice τ E a)) =
          seedMeasure n (E ∩ {ω | τ ω ≠ ⊤}) := by
        calc
          _ = ∑' a : StopIndex n, seedMeasure n (stoppedSlice τ E a) :=
            (tsum_fintype _).symm
          _ = seedMeasure n (⋃ a : StopIndex n, stoppedSlice τ E a) :=
            (measure_iUnion (stoppedSlice_pairwiseDisjoint τ E)
              (measurableSet_stoppedSlice hE)).symm
          _ = _ := congrArg (seedMeasure n) (iUnion_stoppedSlice τ E hbound)
      rw [hsum]

end CoefficientOne.Sampling
