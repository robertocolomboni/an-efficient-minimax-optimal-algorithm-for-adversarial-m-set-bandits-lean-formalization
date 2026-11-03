import AlgebraicCombinatorics.SymmetricFunctions.LittlewoodRichardson

/-!
# Determinant identities for raising one alternant exponent

This file supplies the determinant algebra used in Step 1 of the manuscript's
signed-load identity. The core identity is proved over every commutative ring
by expanding the determinant and reindexing its finite permutation sum. It
therefore also applies to multivariate polynomials and to repeated numerical
letters, without a distinct-letter assumption or division by a Vandermonde.

The convention is `det (x_column ^ exponent_row)`, agreeing with
`AlgebraicCombinatorics.alternantMatrix`. Natural exponents are the manuscript's
integer shifted exponents plus the common offset `N`.
-/

noncomputable section

namespace CoefficientOne.AlternantIdentities

open Finset Matrix

variable {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommRing R]

def powerMatrix (x : ι → R) (e : ι → ℕ) : Matrix ι ι R :=
  Matrix.of fun i j => x j ^ e i

def detAlternant (x : ι → R) (e : ι → ℕ) : R := (powerMatrix x e).det

def powerSum (x : ι → R) (t : ℕ) : R := ∑ i, x i ^ t

/-- Raise only source row `q`, retaining natural exponents. -/
def raiseExponent (e : ι → ℕ) (q : ι) (t : ℕ) : ι → ℕ :=
  Function.update e q (e q + t)

@[simp] theorem raiseExponent_self (e : ι → ℕ) (q : ι) (t : ℕ) :
    raiseExponent e q t q = e q + t := by
  simp [raiseExponent]

@[simp] theorem raiseExponent_of_ne (e : ι → ℕ) (q i : ι) (t : ℕ) (hi : i ≠ q) :
    raiseExponent e q t i = e i := by
  simp [raiseExponent, hi]

theorem raiseExponent_comp (e : ι → ℕ) (σ : Equiv.Perm ι) (q : ι) (t : ℕ) :
    raiseExponent e (σ q) t ∘ σ = raiseExponent (e ∘ σ) q t := by
  funext i
  by_cases h : i = q
  · subst i
    simp
  · have hσ : σ i ≠ σ q := σ.injective.ne h
    simp [Function.comp_apply, raiseExponent, h, hσ]

/-- Raising one exponent multiplies that permutation monomial by one power. -/
theorem prod_raiseExponent (x : ι → R) (e : ι → ℕ) (q : ι) (t : ℕ) :
    (∏ i, x i ^ raiseExponent e q t i) = x q ^ t * ∏ i, x i ^ e i := by
  rw [← Finset.mul_prod_erase univ (fun i => x i ^ raiseExponent e q t i)
      (Finset.mem_univ q),
    ← Finset.mul_prod_erase univ (fun i => x i ^ e i) (Finset.mem_univ q)]
  have hrest :
      (∏ i ∈ univ.erase q, x i ^ raiseExponent e q t i) =
        ∏ i ∈ univ.erase q, x i ^ e i := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [raiseExponent_of_ne e q i t (Finset.mem_erase.mp hi).1]
  rw [hrest, raiseExponent_self, pow_add]
  ring

/--
Multiply an alternant by a power sum by raising each source row once. This is
the actual determinant expansion, not an assumed identity of Schur functions.
-/
theorem powerSum_mul_detAlternant (x : ι → R) (e : ι → ℕ) (t : ℕ) :
    powerSum x t * detAlternant x e =
      ∑ q, detAlternant x (raiseExponent e q t) := by
  unfold powerSum detAlternant
  simp only [Matrix.det_apply, powerMatrix, Matrix.of_apply]
  rw [Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ _
  calc
    (∑ i, x i ^ t) * (Equiv.Perm.sign σ • ∏ i, x i ^ e (σ i)) =
        ∑ i, Equiv.Perm.sign σ • (x i ^ t * ∏ z, x z ^ e (σ z)) := by
      simp only [Finset.sum_mul, mul_smul_comm, Finset.smul_sum]
    _ = ∑ i, Equiv.Perm.sign σ • ∏ z, x z ^ raiseExponent e (σ i) t (σ z) := by
      apply Finset.sum_congr rfl
      intro i _
      have h := prod_raiseExponent x (e ∘ σ) i t
      rw [← raiseExponent_comp e σ i t] at h
      simpa only [Function.comp_apply] using congrArg (fun z => Equiv.Perm.sign σ • z) h.symm
    _ = ∑ q, Equiv.Perm.sign σ • ∏ z, x z ^ raiseExponent e q t (σ z) :=
      Equiv.sum_comp σ (fun q => Equiv.Perm.sign σ • ∏ z, x z ^ raiseExponent e q t (σ z))

theorem detAlternant_eq_zero_of_repeated (x : ι → R) (e : ι → ℕ)
    {i j : ι} (hij : i ≠ j) (he : e i = e j) :
    detAlternant x e = 0 := by
  apply Matrix.det_zero_of_row_eq hij
  funext z
  simp only [powerMatrix, Matrix.of_apply, he]

/-- A raised row vanishes exactly as needed when its destination collides with another row. -/
theorem detAlternant_raise_eq_zero_of_collision (x : ι → R) (e : ι → ℕ)
    (q r : ι) (t : ℕ) (hqr : q ≠ r) (hcollision : e q + t = e r) :
    detAlternant x (raiseExponent e q t) = 0 := by
  apply detAlternant_eq_zero_of_repeated x _ hqr
  simpa only [raiseExponent_self, raiseExponent_of_ne e q r t hqr.symm] using hcollision

/-- Permuting source exponents gives the usual determinant sign. -/
theorem detAlternant_comp (x : ι → R) (e : ι → ℕ) (σ : Equiv.Perm ι) :
    detAlternant x (e ∘ σ) = (Equiv.Perm.sign σ : R) * detAlternant x e := by
  exact Matrix.det_permute σ (powerMatrix x e)

variable {N : ℕ}

/-- Precomposition moves source row `b` to `a`, shifting intervening rows down. -/
def moveUp (a b : Fin N) : Equiv.Perm (Fin N) :=
  (Fin.cycleRange b).symm * Fin.cycleRange a

theorem cycleRange_val (p i : Fin N) :
    (Fin.cycleRange p i).val =
      if i.val < p.val then i.val + 1 else if i.val = p.val then 0 else i.val := by
  by_cases h : i.val < p.val
  · rw [Fin.coe_cycleRange_of_lt h]
    simp [h]
  · by_cases heq : i.val = p.val
    · have hi : i = p := Fin.ext heq
      subst i
      rw [Fin.coe_cycleRange_of_le (le_refl p)]
      simp
    · have hpi : p < i := by omega
      rw [Fin.cycleRange_of_gt hpi]
      simp [h, heq]

theorem moveUp_val (a b i : Fin N) (hab : a ≤ b) :
    (moveUp a b i).val =
      if i.val < a.val then i.val else if i.val = a.val then b.val
      else if i.val ≤ b.val then i.val - 1 else i.val := by
  have hrel : Fin.cycleRange b (moveUp a b i) = Fin.cycleRange a i := by
    simp [moveUp, Equiv.Perm.coe_mul]
  have hv := congrArg Fin.val hrel
  rw [cycleRange_val, cycleRange_val] at hv
  split_ifs at hv ⊢ <;> omega

theorem moveUp_self (a b : Fin N) (hab : a ≤ b) : moveUp a b a = b := by
  apply Fin.ext
  rw [moveUp_val a b a hab]
  simp

theorem moveUp_eq_source_iff (a b i : Fin N) (hab : a ≤ b) :
    moveUp a b i = b ↔ i = a := by
  calc
    moveUp a b i = b ↔ moveUp a b i = moveUp a b a := by rw [moveUp_self a b hab]
    _ ↔ i = a := (moveUp a b).injective.eq_iff

theorem moveUp_of_lt (a b i : Fin N) (hab : a ≤ b) (hi : i < a) :
    moveUp a b i = i := by
  apply Fin.ext
  rw [moveUp_val a b i hab]
  simp [show i.val < a.val from hi]

theorem moveUp_of_gt (a b i : Fin N) (hab : a ≤ b) (hi : b < i) :
    moveUp a b i = i := by
  apply Fin.ext
  rw [moveUp_val a b i hab]
  split_ifs <;> omega

theorem moveUp_between (a b i : Fin N) (hab : a ≤ b) (hai : a < i) (hib : i ≤ b) :
    a ≤ moveUp a b i ∧ moveUp a b i < b := by
  have hv := moveUp_val a b i hab
  split_ifs at hv <;> omega

/-- All unraised rows retain their mutual order. -/
theorem moveUp_lt_of_ne (a b i j : Fin N) (hab : a ≤ b)
    (hij : i < j) (hi : i ≠ a) (hj : j ≠ a) :
    moveUp a b i < moveUp a b j := by
  have hia : i.val ≠ a.val := fun h => hi (Fin.ext h)
  have hja : j.val ≠ a.val := fun h => hj (Fin.ext h)
  have hvi := moveUp_val a b i hab
  have hvj := moveUp_val a b j hab
  split_ifs at hvi hvj <;> omega

theorem sign_moveUp (a b : Fin N) (hab : a ≤ b) :
    Equiv.Perm.sign (moveUp a b) = (-1 : ℤˣ) ^ (b.val - a.val) := by
  simp only [moveUp, Equiv.Perm.sign_mul, Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  rw [← pow_add]
  have h : b.val + a.val = (b.val - a.val) + 2 * a.val := by omega
  rw [h, pow_add, pow_mul]
  simp <;> rfl

set_option backward.isDefEq.respectTransparency false in
theorem detAlternant_moveUp {R : Type*} [CommRing R] (x : Fin N → R)
    (e : Fin N → ℕ) (a b : Fin N) (hab : a ≤ b) :
    detAlternant x (e ∘ moveUp a b) =
      (-1 : R) ^ (b.val - a.val) * detAlternant x e := by
  rw [detAlternant_comp, sign_moveUp a b hab]
  simp only [Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- The explicit row cycle really sorts the raised vector under its insertion inequalities. -/
theorem raiseExponent_moveUp_strictAnti (e : Fin N → ℕ) (he : StrictAnti e)
    (a b : Fin N) (t : ℕ) (hab : a ≤ b)
    (hbefore : ∀ i, i < a → e b + t < e i)
    (hafter : ∀ i, a ≤ i → i < b → e i < e b + t) :
    StrictAnti (raiseExponent e b t ∘ moveUp a b) := by
  intro i j hij
  simp only [Function.comp_apply]
  by_cases hi : i = a
  · subst i
    have hja : j ≠ a := ne_of_gt hij
    have hmj : moveUp a b j ≠ b := by
      simpa only [ne_eq, moveUp_eq_source_iff a b j hab] using hja
    rw [moveUp_self a b hab, raiseExponent_self,
      raiseExponent_of_ne e b (moveUp a b j) t hmj]
    by_cases hjb : j ≤ b
    · exact hafter _ (moveUp_between a b j hab hij hjb).1
        (moveUp_between a b j hab hij hjb).2
    · have hbj : b < j := lt_of_not_ge hjb
      rw [moveUp_of_gt a b j hab hbj]
      have hj' := he hbj
      omega
  · have hmi : moveUp a b i ≠ b := by
      simpa only [ne_eq, moveUp_eq_source_iff a b i hab] using hi
    by_cases hj : j = a
    · subst j
      rw [moveUp_self a b hab, raiseExponent_self,
        raiseExponent_of_ne e b (moveUp a b i) t hmi,
        moveUp_of_lt a b i hab hij]
      exact hbefore i hij
    · have hmj : moveUp a b j ≠ b := by
        simpa only [ne_eq, moveUp_eq_source_iff a b j hab] using hj
      rw [raiseExponent_of_ne e b (moveUp a b i) t hmi,
        raiseExponent_of_ne e b (moveUp a b j) t hmj]
      exact he (moveUp_lt_of_ne a b i j hab hij hi hj)

/-- The actual source indices whose exponents the raised row crosses. -/
def crossingRows (e : Fin N → ℕ) (b : Fin N) (t : ℕ) : Finset (Fin N) :=
  univ.filter (fun i => e b < e i ∧ e i < e b + t)

theorem crossingRows_eq_Ico (e : Fin N → ℕ) (he : StrictAnti e)
    (a b : Fin N) (t : ℕ)
    (hbefore : ∀ i, i < a → e b + t < e i)
    (hafter : ∀ i, a ≤ i → i < b → e i < e b + t) :
    crossingRows e b t = Ico a b := by
  ext i
  simp only [crossingRows, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ico]
  constructor
  · rintro ⟨hlo, hhi⟩
    constructor
    · by_contra h
      have hb := hbefore i (lt_of_not_ge h)
      omega
    · by_contra h
      have hb := he.antitone (le_of_not_gt h)
      omega
  · rintro ⟨hlo, hhi⟩
    exact ⟨he hhi, hafter i hlo hhi⟩

theorem crossingRows_card (e : Fin N → ℕ) (he : StrictAnti e)
    (a b : Fin N) (t : ℕ)
    (hbefore : ∀ i, i < a → e b + t < e i)
    (hafter : ∀ i, a ≤ i → i < b → e i < e b + t) :
    (crossingRows e b t).card = b.val - a.val := by
  rw [crossingRows_eq_Ico e he a b t hbefore hafter, Fin.card_Ico]

/-- The row-sorting sign is the parity of the actual number of crossed rows. -/
theorem detAlternant_raise_sort {R : Type*} [CommRing R] (x : Fin N → R)
    (e : Fin N → ℕ) (he : StrictAnti e) (a b : Fin N) (t : ℕ) (hab : a ≤ b)
    (hbefore : ∀ i, i < a → e b + t < e i)
    (hafter : ∀ i, a ≤ i → i < b → e i < e b + t) :
    detAlternant x (raiseExponent e b t ∘ moveUp a b) =
      (-1 : R) ^ (crossingRows e b t).card * detAlternant x (raiseExponent e b t) := by
  rw [detAlternant_moveUp x (raiseExponent e b t) a b hab,
    crossingRows_card e he a b t hbefore hafter]


/-- Choose the insertion position from the first old exponent at most the raised value. -/
theorem exists_insertionPosition (e : Fin N → ℕ) (he : StrictAnti e)
    (b : Fin N) (t : ℕ) (hcollision : ∀ i, i ≠ b → e i ≠ e b + t) :
    ∃ a : Fin N, a ≤ b ∧
      (∀ i, i < a → e b + t < e i) ∧
      (∀ i, a ≤ i → i < b → e i < e b + t) := by
  let s : Finset (Fin N) := univ.filter (fun i => e i ≤ e b + t)
  have hb : b ∈ s := by simp [s]
  have hs : s.Nonempty := ⟨b, hb⟩
  let a := s.min' hs
  have ha : a ∈ s := Finset.min'_mem s hs
  have haM : e a ≤ e b + t := (Finset.mem_filter.mp ha).2
  refine ⟨a, Finset.min'_le s b hb, ?_, ?_⟩
  · intro i hi
    by_contra h
    have himem : i ∈ s := by simp only [s, Finset.mem_filter, Finset.mem_univ, true_and]; omega
    have hmin : a ≤ i := Finset.min'_le s i himem
    exact (not_le_of_gt hi) hmin
  · intro i hai hib
    have hia : e i ≤ e a := he.antitone hai
    have hne : e i ≠ e b + t := hcollision i (ne_of_lt hib)
    omega

/-- Every noncolliding row raise admits the explicit sorting cycle and its crossing sign. -/
theorem exists_sorted_raise {R : Type*} [CommRing R] (x : Fin N → R)
    (e : Fin N → ℕ) (he : StrictAnti e) (b : Fin N) (t : ℕ)
    (hcollision : ∀ i, i ≠ b → e i ≠ e b + t) :
    ∃ a : Fin N, a ≤ b ∧
      StrictAnti (raiseExponent e b t ∘ moveUp a b) ∧
      detAlternant x (raiseExponent e b t ∘ moveUp a b) =
        (-1 : R) ^ (crossingRows e b t).card *
          detAlternant x (raiseExponent e b t) := by
  obtain ⟨a, hab, hbefore, hafter⟩ := exists_insertionPosition e he b t hcollision
  exact ⟨a, hab, raiseExponent_moveUp_strictAnti e he a b t hab hbefore hafter,
    detAlternant_raise_sort x e he a b t hab hbefore hafter⟩

/-- Convert the manuscript's shifted integer exponents to actual nonnegative powers. -/
def shiftedExponent (c : Fin N → ℤ) (offset : ℤ) : Fin N → ℕ :=
  fun i => (c i + offset).toNat

theorem shiftedExponent_raise (c : Fin N → ℤ) (offset : ℤ) (b : Fin N) (t : ℕ)
    (hb : 0 ≤ c b + offset) :
    raiseExponent (shiftedExponent c offset) b t =
      shiftedExponent (Function.update c b (c b + t)) offset := by
  funext i
  by_cases hi : i = b
  · subst i
    simp only [raiseExponent_self, shiftedExponent, Function.update_self]
    omega
  · simp [raiseExponent, shiftedExponent, hi]

theorem shiftedExponent_strictAnti (c : Fin N → ℤ) (hc : StrictAnti c)
    (offset : ℤ) (hpos : ∀ i, 0 ≤ c i + offset) :
    StrictAnti (shiftedExponent c offset) := by
  intro i j hij
  have he := hc hij
  have hi := hpos i
  have hj := hpos j
  simp only [shiftedExponent]
  omega

/-- The actual crossed integer exponents, independently of how rows are indexed. -/
def crossingExponents (c : Fin N → ℤ) (b : Fin N) (t : ℕ) : Finset ℤ :=
  (univ.image c).filter (fun z => c b < z ∧ z < c b + t)

/-- Shifting exponents by a common offset preserves the actual crossing count. -/
theorem crossingRows_shifted_card (c : Fin N → ℤ) (hc : Function.Injective c)
    (offset : ℤ) (hpos : ∀ i, 0 ≤ c i + offset) (b : Fin N) (t : ℕ) :
    (crossingRows (shiftedExponent c offset) b t).card =
      (crossingExponents c b t).card := by
  refine Finset.card_bij (fun i _ => c i) ?_ ?_ ?_
  · intro i hi
    rw [crossingRows, Finset.mem_filter] at hi
    simp only [Finset.mem_univ, true_and,
      shiftedExponent] at hi
    simp only [crossingExponents, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and]
    have hib := hpos b
    have hii := hpos i
    exact ⟨⟨i, rfl⟩, by omega, by omega⟩
  · intro i hi j hj hij
    exact hc hij
  · intro z hz
    simp only [crossingExponents, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and] at hz
    obtain ⟨⟨i, rfl⟩, hlo, hhi⟩ := hz
    refine ⟨i, ?_, rfl⟩
    rw [crossingRows, Finset.mem_filter]
    simp only [Finset.mem_univ, true_and,
      shiftedExponent]
    have hib := hpos b
    have hii := hpos i
    omega

/-- Compatibility with the imported library's alternant convention. -/
theorem alternant_eq_detAlternant {R : Type*} [CommRing R] (e : Fin N → ℕ) :
    (AlgebraicCombinatorics.alternant e : MvPolynomial (Fin N) R) =
      detAlternant (MvPolynomial.X : Fin N → MvPolynomial (Fin N) R) e := by
  rw [AlgebraicCombinatorics.alternant_eq_det]
  rfl

/-- The power-sum identity expressed directly using the Schur library's alternant. -/
theorem powerSum_mul_alternant {R : Type*} [CommRing R] (e : Fin N → ℕ) (t : ℕ) :
    powerSum (MvPolynomial.X : Fin N → MvPolynomial (Fin N) R) t *
      AlgebraicCombinatorics.alternant e =
      ∑ q, AlgebraicCombinatorics.alternant (raiseExponent e q t) := by
  simp only [alternant_eq_detAlternant]
  exact powerSum_mul_detAlternant _ e t



/-- Reversing the sorting equality uses that its sign squares to one. -/
theorem detAlternant_raise_eq_signed_sort {R : Type*} [CommRing R] (x : Fin N → R)
    (e : Fin N → ℕ) (he : StrictAnti e) (a b : Fin N) (t : ℕ) (hab : a ≤ b)
    (hbefore : ∀ i, i < a → e b + t < e i)
    (hafter : ∀ i, a ≤ i → i < b → e i < e b + t) :
    detAlternant x (raiseExponent e b t) =
      (-1 : R) ^ (crossingRows e b t).card *
        detAlternant x (raiseExponent e b t ∘ moveUp a b) := by
  rw [detAlternant_raise_sort x e he a b t hab hbefore hafter]
  rw [← mul_assoc, ← mul_pow]
  simp

/-- A strict decreasing enumeration is uniquely determined by its image. -/
theorem eq_of_strictAnti_image_eq {α : Type*} [LinearOrder α]
    (e f : Fin N → α) (he : StrictAnti e) (hf : StrictAnti f)
    (himage : univ.image e = univ.image f) : e = f := by
  apply (he.range_inj hf).mp
  have h := congrArg (fun s : Finset α => (s : Set α)) himage
  simpa only [Finset.coe_image, Finset.coe_univ, Set.image_univ] using h

/-- Raising an injectively indexed exponent replaces just that element in its image. -/
theorem image_raiseExponent (e : Fin N → ℕ) (he : Function.Injective e)
    (b : Fin N) (t : ℕ) :
    univ.image (raiseExponent e b t) = insert (e b + t) ((univ.image e).erase (e b)) := by
  have hrest : (univ.erase b).image (raiseExponent e b t) = (univ.erase b).image e := by
    apply Finset.image_congr
    intro i hi
    exact raiseExponent_of_ne e b i t (Finset.mem_erase.mp hi).1
  calc
    univ.image (raiseExponent e b t) =
        (insert b (univ.erase b)).image (raiseExponent e b t) := by
      rw [Finset.insert_erase (Finset.mem_univ b)]
    _ = insert (e b + t) ((univ.erase b).image e) := by
      rw [Finset.image_insert, raiseExponent_self, hrest]
    _ = insert (e b + t) ((univ.image e).erase (e b)) := by
      rw [Finset.image_erase he univ b]

theorem image_comp_perm {α : Type*} [DecidableEq α] (e : Fin N → α)
    (σ : Equiv.Perm (Fin N)) : univ.image (e ∘ σ) = univ.image e := by
  ext z
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Function.comp_apply]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨σ i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨σ.symm i, by simpa using hi⟩

/--
A row vector reconstructed from the raised exponent set is the actual sorted
vector. This connects finite-set cancellation proofs to actual determinants.
-/
theorem detAlternant_raise_eq_signed_of_image {R : Type*} [CommRing R]
    (x : Fin N → R) (e f : Fin N → ℕ) (he : StrictAnti e) (hf : StrictAnti f)
    (b : Fin N) (t : ℕ) (hcollision : ∀ i, i ≠ b → e i ≠ e b + t)
    (himage : univ.image f = insert (e b + t) ((univ.image e).erase (e b))) :
    detAlternant x (raiseExponent e b t) =
      (-1 : R) ^ (crossingRows e b t).card * detAlternant x f := by
  obtain ⟨a, hab, hbefore, hafter⟩ := exists_insertionPosition e he b t hcollision
  have hs := raiseExponent_moveUp_strictAnti e he a b t hab hbefore hafter
  have him : univ.image (raiseExponent e b t ∘ moveUp a b) = univ.image f := by
    rw [image_comp_perm, image_raiseExponent e he.injective b t, himage]
  have hsorted := eq_of_strictAnti_image_eq _ f hs hf him
  rw [← hsorted]
  exact detAlternant_raise_eq_signed_sort x e he a b t hab hbefore hafter



end CoefficientOne.AlternantIdentities

end
