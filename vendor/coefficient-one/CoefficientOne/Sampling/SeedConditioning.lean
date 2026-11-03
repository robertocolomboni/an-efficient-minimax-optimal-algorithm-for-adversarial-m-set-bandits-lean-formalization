import CoefficientOne.Sampling.Seed

/-!
# Factorization of the seed at a revealed prefix

A prefix fixes the first entries of a permutation, but does not expose its tail.
The remaining order is represented by the finite set of all extensions of this
prefix. Each extension is equally likely. Splitting the uniforms on the revealed
and unrevealed coordinates gives an independent product, including for arbitrary
Borel events in the continuously valued revealed uniforms.
-/

noncomputable section

open MeasureTheory Set
open scoped ENNReal unitInterval

namespace CoefficientOne.Sampling

theorem uniformMeasure_singleton (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (a : α) :
    uniformMeasure α {a} = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformMeasure, Measure.uniformOfFinset_apply_singleton]

theorem uniformMeasure_restrict (α : Type*) [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (s : Set α)
    [Fintype s] [Nonempty s] :
    (uniformMeasure α).restrict s =
      ((Fintype.card s : ℝ≥0∞) / Fintype.card α) •
        (uniformMeasure s).map (Subtype.val : s → α) := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [Measure.restrict_apply (measurableSet_singleton a), Measure.smul_apply,
    smul_eq_mul, Measure.map_apply measurable_subtype_coe (measurableSet_singleton a)]
  by_cases ha : a ∈ s
  · have hleft : ({a} : Set α) ∩ s = {a} := by ext x; simp [ha]
    have hright : (Subtype.val : s → α) ⁻¹' {a} = {⟨a, ha⟩} := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, Subtype.ext_iff]
    rw [hleft, hright, uniformMeasure_singleton, uniformMeasure_singleton]
    have hcard : (Fintype.card s : ℝ≥0∞) ≠ 0 := by
      exact_mod_cast Fintype.card_ne_zero
    rw [div_eq_mul_inv, mul_right_comm, ENNReal.mul_inv_cancel hcard (by simp), one_mul]
  · have hleft : ({a} : Set α) ∩ s = ∅ := by ext x; simp [ha]
    have hright : (Subtype.val : s → α) ⁻¹' {a} = ∅ := by
      ext x
      simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]
      exact fun h => ha (h ▸ x.property)
    simp [hleft, hright]

theorem uniformMeasure_equiv {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass α] [MeasurableSingletonClass β] (e : α ≃ β) :
    MeasurePreserving e (uniformMeasure α) (uniformMeasure β) := by
  refine ⟨measurable_of_finite _, Measure.ext_of_singleton fun b => ?_⟩
  rw [Measure.map_apply (measurable_of_finite _) (measurableSet_singleton b)]
  have hp : e ⁻¹' {b} = {e.symm b} := by
    ext a
    exact e.apply_eq_iff_eq_symm_apply
  rw [hp, uniformMeasure_singleton, uniformMeasure_singleton, Fintype.card_congr e]

theorem measure_eq_uniform_of_singletons {α : Type*} [Fintype α] [Nonempty α]
    [MeasurableSpace α] [MeasurableSingletonClass α] (μ : Measure α)
    (hμ : μ Set.univ = 1) (hs : ∀ a b, μ {a} = μ {b}) : μ = uniformMeasure α := by
  classical
  apply Measure.ext_of_singleton
  intro a
  rw [uniformMeasure_singleton]
  have hsum : ∑ b : α, μ {b} = 1 := by
    calc
      _ = μ Set.univ := by simpa using
        (MeasureTheory.sum_measure_singleton (μ := μ) (s := Finset.univ))
      _ = 1 := hμ
  have hmul : (Fintype.card α : ℝ≥0∞) * μ {a} = 1 := by
    have hconst : (∑ b : α, μ {b}) = ∑ _b : α, μ {a} :=
      Finset.sum_congr rfl fun b _ => hs b a
    rw [hconst] at hsum
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using hsum
  have hc : (Fintype.card α : ℝ≥0∞) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  calc
    μ {a} = (Fintype.card α : ℝ≥0∞)⁻¹ * ((Fintype.card α : ℝ≥0∞) * μ {a}) := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel hc (by simp), one_mul]
    _ = (Fintype.card α : ℝ≥0∞)⁻¹ := by rw [hmul, mul_one]

def postcomposeEquiv {α β : Type*} (s : Equiv.Perm β) : (α ≃ β) ≃ (α ≃ β) where
  toFun e := e.trans s
  invFun e := e.trans s.symm
  left_inv e := by ext a; simp
  right_inv e := by ext a; simp

/-- A uniformly chosen bijection sends a fixed argument to a uniform image. -/
theorem uniformMeasure_equiv_eval {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β]
    [Nonempty (α ≃ β)] [Nonempty β]
    [MeasurableSpace (α ≃ β)] [MeasurableSingletonClass (α ≃ β)]
    [MeasurableSpace β] [MeasurableSingletonClass β] (a : α) :
    MeasurePreserving (fun e : α ≃ β => e a) (uniformMeasure (α ≃ β)) (uniformMeasure β) := by
  classical
  have hm : Measurable (fun e : α ≃ β => e a) := measurable_of_finite _
  refine ⟨hm, measure_eq_uniform_of_singletons _ ?_ ?_⟩
  · rw [Measure.map_apply hm MeasurableSet.univ]
    simp
  · intro b c
    rw [Measure.map_apply hm (measurableSet_singleton b),
      Measure.map_apply hm (measurableSet_singleton c)]
    have hmp := uniformMeasure_equiv (postcomposeEquiv (α := α) (Equiv.swap b c))
    have hpre : (postcomposeEquiv (α := α) (Equiv.swap b c)) ⁻¹'
        ((fun e : α ≃ β => e a) ⁻¹' {c}) = ((fun e : α ≃ β => e a) ⁻¹' {b}) := by
      ext e
      change Equiv.swap b c (e a) = c ↔ e a = b
      constructor
      · intro h
        exact (Equiv.swap b c).injective (h.trans (Equiv.swap_apply_left b c).symm)
      · intro h
        rw [h, Equiv.swap_apply_left]
    have h := hmp.measure_preimage ((measurableSet_singleton c).preimage hm).nullMeasurableSet
    simpa only [hpre] using h

def PrefixMatches {n : ℕ} (ℓ : ℕ) (ρ π : Equiv.Perm (Fin n)) : Prop :=
  ∀ j : Fin n, j.val < ℓ → π j = ρ j

abbrev PrefixOrders {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :=
  {π : Equiv.Perm (Fin n) // PrefixMatches ℓ ρ π}

instance prefixOrders_nonempty {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Nonempty (PrefixOrders ℓ ρ) := ⟨⟨ρ, fun _ _ => rfl⟩⟩

instance prefixOrders_fintype {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Fintype (PrefixOrders ℓ ρ) := Fintype.ofFinite _

def Revealed {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) (i : Fin n) : Prop :=
  (ρ.symm i).val < ℓ

instance revealed_decidable {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    DecidablePred (Revealed ℓ ρ) := fun i => Nat.decLt (ρ.symm i).val ℓ

theorem prefixMatches_revealed_iff {n : ℕ} {ℓ : ℕ} {ρ π : Equiv.Perm (Fin n)}
    (hπ : PrefixMatches ℓ ρ π) (j : Fin n) :
    Revealed ℓ ρ (π j) ↔ j.val < ℓ := by
  constructor
  · intro h
    have heq : π (ρ.symm (π j)) = π j := by
      rw [hπ _ h, ρ.apply_symm_apply]
    exact π.injective heq ▸ h
  · intro h
    simpa [Revealed, hπ j h] using h

def fixedPrefixEquiv {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    {j : Fin n // j.val < ℓ} ≃ {i : Fin n // Revealed ℓ ρ i} where
  toFun j := ⟨ρ j, by simpa [Revealed] using j.property⟩
  invFun i := ⟨ρ.symm i, i.property⟩
  left_inv j := by ext; simp
  right_inv i := by ext; simp

abbrev RemainingOrder {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :=
  {j : Fin n // ¬j.val < ℓ} ≃ {i : Fin n // ¬ Revealed ℓ ρ i}

def remainingOrder {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (π : PrefixOrders ℓ ρ) : RemainingOrder ℓ ρ where
  toFun j := ⟨π.val j, fun h => j.property ((prefixMatches_revealed_iff π.property j).mp h)⟩
  invFun i := ⟨π.val.symm i, by
    intro h
    apply i.property
    simpa using (prefixMatches_revealed_iff π.property (π.val.symm i)).mpr h⟩
  left_inv j := by ext; simp
  right_inv i := by ext; simp

def extendRemainingOrder {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (e : RemainingOrder ℓ ρ) : PrefixOrders ℓ ρ :=
  ⟨Equiv.subtypeCongr (fixedPrefixEquiv ℓ ρ) e, by
    intro j hj
    simp [Equiv.subtypeCongr, Equiv.sumCompl, hj, fixedPrefixEquiv]⟩

/-- An extension of the prefix is exactly an ordering of all remaining coordinates. -/
def prefixOrdersEquivRemainingOrder {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    PrefixOrders ℓ ρ ≃ RemainingOrder ℓ ρ where
  toFun := remainingOrder ℓ ρ
  invFun := extendRemainingOrder ℓ ρ
  left_inv π := by
    apply Subtype.ext
    apply Equiv.ext
    intro j
    by_cases hj : j.val < ℓ
    · simp [extendRemainingOrder, Equiv.subtypeCongr,
        Equiv.sumCompl, hj, fixedPrefixEquiv, π.property j hj]
    · simp [extendRemainingOrder, Equiv.subtypeCongr,
        Equiv.sumCompl, hj, remainingOrder]
  right_inv e := by
    apply Equiv.ext
    intro j
    apply Subtype.ext
    simp [remainingOrder, extendRemainingOrder, Equiv.subtypeCongr,
      Equiv.sumCompl, j.property]

instance remainingOrder_measurableSpace {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    MeasurableSpace (RemainingOrder ℓ ρ) := ⊤

instance remainingOrder_discreteMeasurableSpace {n : ℕ} (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) : DiscreteMeasurableSpace (RemainingOrder ℓ ρ) :=
  ⟨fun _ => trivial⟩

instance remainingOrder_nonempty {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Nonempty (RemainingOrder ℓ ρ) :=
  ⟨remainingOrder ℓ ρ ⟨ρ, fun _ _ => rfl⟩⟩

theorem remainingOrder_eval_measurePreserving {n : ℕ} (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) [Nonempty {i // ¬Revealed ℓ ρ i}]
    (j : {j : Fin n // ¬j.val < ℓ}) :
    MeasurePreserving (fun π : PrefixOrders ℓ ρ => remainingOrder ℓ ρ π j)
      (uniformMeasure (PrefixOrders ℓ ρ)) (uniformMeasure {i // ¬Revealed ℓ ρ i}) := by
  exact (uniformMeasure_equiv_eval j).comp
    (uniformMeasure_equiv (prefixOrdersEquivRemainingOrder ℓ ρ))

abbrev PastUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :=
  {i : Fin n // Revealed ℓ ρ i} → unitInterval

abbrev FutureUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :=
  {i : Fin n // ¬ Revealed ℓ ρ i} → unitInterval

def splitUniforms {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    (Fin n → unitInterval) ≃ᵐ (PastUniforms ℓ ρ × FutureUniforms ℓ ρ) := by
  classical
  exact MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n => unitInterval) (Revealed ℓ ρ)

theorem splitUniforms_measurePreserving {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    MeasurePreserving (splitUniforms ℓ ρ) (uniformCube (Fin n))
      ((uniformCube {i // Revealed ℓ ρ i}).prod (uniformCube {i // ¬ Revealed ℓ ρ i})) := by
  classical
  exact measurePreserving_piEquivPiSubtypeProd (fun _ : Fin n => volume) (Revealed ℓ ρ)

def prefixWeight {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) : ℝ≥0∞ :=
  (Fintype.card (PrefixOrders ℓ ρ) : ℝ≥0∞) / Fintype.card (Equiv.Perm (Fin n))

abbrev SplitPrefixSeed {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :=
  PrefixOrders ℓ ρ × (PastUniforms ℓ ρ × FutureUniforms ℓ ρ)

def prefixProductMeasure {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measure (SplitPrefixSeed ℓ ρ) :=
  (uniformMeasure (PrefixOrders ℓ ρ)).prod
    ((uniformCube {i // Revealed ℓ ρ i}).prod (uniformCube {i // ¬ Revealed ℓ ρ i}))

instance prefixProductMeasure_isProbabilityMeasure {n : ℕ} (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) : IsProbabilityMeasure (prefixProductMeasure ℓ ρ) := by
  unfold prefixProductMeasure
  infer_instance

def assemblePrefixSeed {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (z : SplitPrefixSeed ℓ ρ) : Seed n :=
  (z.1.val, (splitUniforms ℓ ρ).symm z.2)

@[fun_prop]
theorem measurable_assemblePrefixSeed {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measurable (assemblePrefixSeed ℓ ρ) := by
  exact (measurable_subtype_coe.comp measurable_fst).prodMk
    ((splitUniforms ℓ ρ).symm.measurable.comp measurable_snd)

theorem assemblePrefixSeed_prefix {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (z : SplitPrefixSeed ℓ ρ) : PrefixMatches ℓ ρ (assemblePrefixSeed ℓ ρ z).1 := z.1.property

theorem seedMeasure_restrict_prefix {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    (seedMeasure n).restrict {ω | PrefixMatches ℓ ρ ω.1} =
      prefixWeight ℓ ρ • (prefixProductMeasure ℓ ρ).map (assemblePrefixSeed ℓ ρ) := by
  classical
  letI : Nonempty {π : Equiv.Perm (Fin n) | PrefixMatches ℓ ρ π} :=
    prefixOrders_nonempty ℓ ρ
  letI : Fintype {π : Equiv.Perm (Fin n) | PrefixMatches ℓ ρ π} :=
    prefixOrders_fintype ℓ ρ
  have hsplit := (splitUniforms_measurePreserving ℓ ρ).symm (splitUniforms ℓ ρ)
  have hprod := Measure.map_prod_map (uniformMeasure (PrefixOrders ℓ ρ))
    ((uniformCube {i // Revealed ℓ ρ i}).prod (uniformCube {i // ¬ Revealed ℓ ρ i}))
    measurable_subtype_coe (splitUniforms ℓ ρ).symm.measurable
  have hset : {ω : Seed n | PrefixMatches ℓ ρ ω.1} =
      {π : Equiv.Perm (Fin n) | PrefixMatches ℓ ρ π} ×ˢ Set.univ := by ext ω; simp
  rw [hset, seedMeasure, ← Measure.prod_restrict, Measure.restrict_univ,
    uniformMeasure_restrict, Measure.prod_smul_left]
  apply congrArg (fun μ : Measure (Seed n) => prefixWeight ℓ ρ • μ)
  rw [← hsplit.map_eq]
  exact hprod

theorem assemblePrefixSeed_measurableEmbedding {n : ℕ} (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) : MeasurableEmbedding (assemblePrefixSeed ℓ ρ) := by
  exact (MeasurableEmbedding.subtype_coe (Set.to_countable _).measurableSet).prodMap
    (splitUniforms ℓ ρ).symm.measurableEmbedding

def prefixFutureMeasure {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n)) :
    Measure (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ) :=
  (uniformMeasure (PrefixOrders ℓ ρ)).prod (uniformCube {i // ¬ Revealed ℓ ρ i})

instance prefixFutureMeasure_isProbabilityMeasure {n : ℕ} (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) : IsProbabilityMeasure (prefixFutureMeasure ℓ ρ) := by
  unfold prefixFutureMeasure
  infer_instance

/-- The next index is uniform in the residual set, independently of its fresh uniform. -/
theorem nextReveal_measurePreserving {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    [Nonempty {i // ¬Revealed ℓ ρ i}] (j : {j : Fin n // ¬j.val < ℓ}) :
    MeasurePreserving
      (fun z : PrefixOrders ℓ ρ × FutureUniforms ℓ ρ =>
        (remainingOrder ℓ ρ z.1 j, z.2 (remainingOrder ℓ ρ z.1 j)))
      (prefixFutureMeasure ℓ ρ)
      ((uniformMeasure {i // ¬Revealed ℓ ρ i}).prod (volume : Measure unitInterval)) := by
  unfold prefixFutureMeasure
  apply (remainingOrder_eval_measurePreserving ℓ ρ j).skew_product
    (g := fun π (u : FutureUniforms ℓ ρ) => u (remainingOrder ℓ ρ π j))
  · exact measurable_from_prod_countable_right fun π =>
      measurable_pi_apply (remainingOrder ℓ ρ π j)
  · exact Filter.Eventually.of_forall fun π =>
      (measurePreserving_eval (fun _ : {i // ¬Revealed ℓ ρ i} =>
        (volume : Measure unitInterval)) (remainingOrder ℓ ρ π j)).map_eq

/-- A Borel event in the revealed uniforms together with an event in the entire future seed. -/
def prefixEvent {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (B : Set (PastUniforms ℓ ρ)) (C : Set (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ)) :
    Set (Seed n) :=
  assemblePrefixSeed ℓ ρ '' {z | z.2.1 ∈ B ∧ (z.1, z.2.2) ∈ C}

theorem prefixEvent_subset_past {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (B : Set (PastUniforms ℓ ρ)) (C : Set (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ)) :
    prefixEvent ℓ ρ B C ⊆ prefixEvent ℓ ρ B Set.univ := by
  rintro ω ⟨z, hz, rfl⟩
  exact ⟨z, ⟨hz.1, Set.mem_univ _⟩, rfl⟩

theorem prefixPastEvent_eq {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    (B : Set (PastUniforms ℓ ρ)) :
    prefixEvent ℓ ρ B Set.univ =
      {ω | PrefixMatches ℓ ρ ω.1 ∧ (splitUniforms ℓ ρ ω.2).1 ∈ B} := by
  ext ω
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact ⟨z.1.property, by simpa [assemblePrefixSeed] using hz.1⟩
  · rintro ⟨hπ, hB⟩
    refine ⟨(⟨ω.1, hπ⟩, splitUniforms ℓ ρ ω.2), ⟨hB, Set.mem_univ _⟩, ?_⟩
    simp [assemblePrefixSeed]

theorem measurableSet_prefixEvent {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    {B : Set (PastUniforms ℓ ρ)} {C : Set (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ)}
    (hB : MeasurableSet B) (hC : MeasurableSet C) : MeasurableSet (prefixEvent ℓ ρ B C) := by
  apply (assemblePrefixSeed_measurableEmbedding ℓ ρ).measurableSet_image'
  exact (hB.preimage (by fun_prop)).inter (hC.preimage (by fun_prop))

theorem prefixProductMeasure_rectangle {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    {B : Set (PastUniforms ℓ ρ)} {C : Set (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ)}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    prefixProductMeasure ℓ ρ {z | z.2.1 ∈ B ∧ (z.1, z.2.2) ∈ C} =
      uniformCube {i // Revealed ℓ ρ i} B * prefixFutureMeasure ℓ ρ C := by
  have hm : MeasurableSet {z : SplitPrefixSeed ℓ ρ | z.2.1 ∈ B ∧ (z.1, z.2.2) ∈ C} :=
    (hB.preimage (by fun_prop)).inter (hC.preimage (by fun_prop))
  rw [prefixProductMeasure, Measure.prod_apply hm]
  have hsec (π : PrefixOrders ℓ ρ) :
      Prod.mk π ⁻¹' {z : SplitPrefixSeed ℓ ρ | z.2.1 ∈ B ∧ (z.1, z.2.2) ∈ C} =
        B ×ˢ (Prod.mk π ⁻¹' C) := by ext z; rfl
  simp_rw [hsec, Measure.prod_prod]
  rw [lintegral_const_mul _ (measurable_of_finite _),
    prefixFutureMeasure, Measure.prod_apply hC]

/-- The concrete prefix conditioning identity. It includes arbitrary Borel past events. -/
theorem seedMeasure_prefixEvent {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    {B : Set (PastUniforms ℓ ρ)} {C : Set (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ)}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    seedMeasure n (prefixEvent ℓ ρ B C) =
      prefixWeight ℓ ρ * uniformCube {i // Revealed ℓ ρ i} B * prefixFutureMeasure ℓ ρ C := by
  have hm := measurableSet_prefixEvent ℓ ρ hB hC
  have hsub : prefixEvent ℓ ρ B C ⊆ {ω | PrefixMatches ℓ ρ ω.1} := by
    rintro ω ⟨z, _, rfl⟩
    exact assemblePrefixSeed_prefix ℓ ρ z
  rw [← Set.inter_eq_left.mpr hsub, ← Measure.restrict_apply hm,
    seedMeasure_restrict_prefix, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (measurable_assemblePrefixSeed ℓ ρ) hm]
  rw [prefixEvent, Set.preimage_image_eq _ (assemblePrefixSeed_measurableEmbedding ℓ ρ).injective,
    prefixProductMeasure_rectangle ℓ ρ hB hC, mul_assoc]

theorem seedMeasure_prefixPast {n : ℕ} (ℓ : ℕ) (ρ : Equiv.Perm (Fin n))
    {B : Set (PastUniforms ℓ ρ)} (hB : MeasurableSet B) :
    seedMeasure n (prefixEvent ℓ ρ B Set.univ) =
      prefixWeight ℓ ρ * uniformCube {i // Revealed ℓ ρ i} B := by
  simpa using seedMeasure_prefixEvent ℓ ρ hB MeasurableSet.univ

theorem seedMeasure_prefixEvent_eq_past_mul_future {n : ℕ} (ℓ : ℕ)
    (ρ : Equiv.Perm (Fin n)) {B : Set (PastUniforms ℓ ρ)}
    {C : Set (PrefixOrders ℓ ρ × FutureUniforms ℓ ρ)}
    (hB : MeasurableSet B) (hC : MeasurableSet C) :
    seedMeasure n (prefixEvent ℓ ρ B C) =
      seedMeasure n (prefixEvent ℓ ρ B Set.univ) * prefixFutureMeasure ℓ ρ C := by
  rw [seedMeasure_prefixEvent ℓ ρ hB hC, seedMeasure_prefixPast ℓ ρ hB]

end CoefficientOne.Sampling
