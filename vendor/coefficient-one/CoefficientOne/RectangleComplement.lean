import CoefficientOne.SchurFoundations
import CoefficientOne.AlternantIdentities

/-!
# Rectangle complementation: determinant foundations

The proof follows the manuscript's bialternant argument: factor powers of
each letter from the columns and reverse the rows. Repeated positive letters
will be handled by continuity. The completed results below do not assume
any reciprocal Schur identity.
-/

noncomputable section

namespace CoefficientOne.RectangleComplement

open Finset Matrix AlgebraicCombinatorics CoefficientOne.AlternantIdentities

variable {N : ℕ}

theorem detAlternant_add_const {R : Type*} [CommRing R]
    (a : Fin N → R) (e : Fin N → ℕ) (q : ℕ) :
    detAlternant a (fun i => e i + q) = detAlternant a e * (∏ i, a i) ^ q := by
  have hM : powerMatrix a (fun i => e i + q) =
      powerMatrix a e * Matrix.diagonal (fun i => a i ^ q) := by
    ext i j
    simp [powerMatrix, Matrix.mul_diagonal, pow_add]
  unfold detAlternant
  rw [hM, Matrix.det_mul, Matrix.det_diagonal]
  simp [detAlternant, Finset.prod_pow]

theorem alternant_add_const (e : Fin N → ℕ) (q : ℕ) :
    (alternant (fun i => e i + q) : MvPolynomial (Fin N) ℝ) =
      alternant e * (∏ i, MvPolynomial.X i) ^ q := by
  simpa only [detAlternant, powerMatrix, alternant_eq_det, alternantMatrix] using
    detAlternant_add_const (fun i : Fin N => (MvPolynomial.X i : MvPolynomial (Fin N) ℝ)) e q

theorem schurPoly_const (q : ℕ) :
    (schurPoly (fun _ : Fin N => q) : MvPolynomial (Fin N) ℝ) =
      (∏ i : Fin N, MvPolynomial.X i) ^ q := by
  have hpart : AlgebraicCombinatorics.IsNPartition (fun _ : Fin N => q) := by
    intro i j hij
    rfl
  have h := schurPoly_eq_alternant_div (R := ℝ) (fun _ : Fin N => q) hpart
  apply (alternant_rho_isRegular (R := ℝ) (N := N)).left
  calc
    _ = alternant ((fun _ : Fin N => q) + rho N) := h.symm
    _ = alternant (fun i => rho N i + q) := by
      congr 1
      funext i
      simp [add_comm]
    _ = _ := alternant_add_const (rho N) q

theorem schurValue_const (a : Fin N → ℝ) (q : ℕ) :
    schurValue (fun _ : Fin N => q) a = (∏ i, a i) ^ q := by
  unfold schurValue
  rw [schurPoly_const]
  simp

def reverseRows (N : ℕ) : Equiv.Perm (Fin N) :=
  { toFun := Fin.rev, invFun := Fin.rev, left_inv := by intro i; simp, right_inv := by intro i; simp }

@[simp] theorem reverseRows_apply (i : Fin N) : reverseRows N i = i.rev := rfl

@[simp] theorem reverseRows_value (i : Fin N) :
    (reverseRows N i).val = N - 1 - i.val := by
  simp [reverseRows, Fin.rev]
  omega

theorem reverseSign_ne_zero (N : ℕ) : (Equiv.Perm.sign (reverseRows N) : ℝ) ≠ 0 := by
  exact_mod_cast (Units.ne_zero (Equiv.Perm.sign (reverseRows N)))

theorem detAlternant_rho_ne_zero (a : Fin N → ℝ) (ha : Function.Injective a) :
    detAlternant a (rho N) ≠ 0 := by
  have he : rho N = (fun i : Fin N => i.val) ∘ reverseRows N := by
    funext i
    simp [rho, Function.comp_apply]
    omega
  have hd : detAlternant a (fun i : Fin N => i.val) ≠ 0 := by
    change (Matrix.vandermonde a).transpose.det ≠ 0
    rw [Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr ha
  rw [he, detAlternant_comp]
  exact mul_ne_zero (reverseSign_ne_zero N) hd

theorem eval_alternant (a : Fin N → ℝ) (e : Fin N → ℕ) :
    MvPolynomial.eval a (alternant e : MvPolynomial (Fin N) ℝ) = detAlternant a e := by
  rw [alternant_eq_det, RingHom.map_det]
  congr 1
  ext i j
  simp [alternantMatrix, powerMatrix]

theorem detAlternant_partition (a : Fin N → ℝ) (lam : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam) :
    detAlternant a (lam + rho N) = detAlternant a (rho N) * schurValue lam a := by
  have h := congrArg (MvPolynomial.eval a)
    (schurPoly_eq_alternant_div (R := ℝ) lam hlam)
  simpa only [map_mul, eval_alternant, schurValue] using h

theorem inverse_pow_mul_pow (x : ℝ) (hx : x ≠ 0) (m d : ℕ) (hmd : m ≤ d) :
    x⁻¹ ^ m * x ^ d = x ^ (d - m) := by
  calc
    _ = (x ^ m)⁻¹ * (x ^ (d - m) * x ^ m) := by
      rw [inv_pow, ← pow_add, Nat.sub_add_cancel hmd]
    _ = _ := by field_simp

theorem detAlternant_inverse_complement (a : Fin N → ℝ) (ha : ∀ i, a i ≠ 0)
    (e : Fin N → ℕ) (d : ℕ) (he : ∀ i, e i ≤ d) :
    detAlternant (fun i => (a i)⁻¹) e * (∏ i, a i) ^ d =
      detAlternant a (fun i => d - e i) := by
  have hM : powerMatrix a (fun i => d - e i) =
      powerMatrix (fun i => (a i)⁻¹) e * Matrix.diagonal (fun i => a i ^ d) := by
    ext i j
    simp only [powerMatrix, Matrix.mul_diagonal, Matrix.of_apply]
    exact (inverse_pow_mul_pow (a j) (ha j) (e i) d (he i)).symm
  unfold detAlternant
  rw [hM, Matrix.det_mul, Matrix.det_diagonal]
  simp [detAlternant, Finset.prod_pow]
def complementShape (q : ℕ) (lam : Fin N → ℕ) : Fin N → ℕ :=
  fun i => q - lam (reverseRows N i)

theorem complementShape_partition (q : ℕ) (lam : Fin N → ℕ)
    (hlam : AlgebraicCombinatorics.IsNPartition lam) :
    AlgebraicCombinatorics.IsNPartition (complementShape q lam) := by
  intro i j hij
  have hrev : reverseRows N j ≤ reverseRows N i := by
    change (reverseRows N j).val ≤ (reverseRows N i).val
    rw [reverseRows_value, reverseRows_value]
    have := i.isLt
    have := j.isLt
    change i.val ≤ j.val at hij
    omega
  exact Nat.sub_le_sub_left (hlam _ _ hrev) q

theorem complementShape_involution (q : ℕ) (lam : Fin N → ℕ)
    (hlam : ∀ i, lam i ≤ q) : complementShape q (complementShape q lam) = lam := by
  funext i
  have hi := hlam i
  simp [complementShape]
  omega

theorem rho_complement :
    (fun i : Fin N => N - 1 - rho N i) = rho N ∘ reverseRows N := by
  funext i
  have hi := i.isLt
  simp [rho, Function.comp_apply]
  omega

theorem partition_complement_exponents (q : ℕ) (lam : Fin N → ℕ)
    (hlam : ∀ i, lam i ≤ q) :
    (fun i => (q + (N - 1)) - (lam + rho N) i) =
      (complementShape q lam + rho N) ∘ reverseRows N := by
  funext i
  have hi := i.isLt
  have hq := hlam i
  simp [complementShape, rho, Function.comp_apply]
  omega

theorem detAlternant_inverse_rho (a : Fin N → ℝ) (ha : ∀ i, a i ≠ 0) :
    detAlternant (fun i => (a i)⁻¹) (rho N) * (∏ i, a i) ^ (N - 1) =
      (Equiv.Perm.sign (reverseRows N) : ℝ) * detAlternant a (rho N) := by
  rw [detAlternant_inverse_complement a ha (rho N) (N - 1)
    (fun i => Nat.sub_le _ _), rho_complement, detAlternant_comp]

theorem detAlternant_inverse_partition (a : Fin N → ℝ) (ha : ∀ i, a i ≠ 0)
    (q : ℕ) (lam : Fin N → ℕ) (hlam : ∀ i, lam i ≤ q) :
    detAlternant (fun i => (a i)⁻¹) (lam + rho N) * (∏ i, a i) ^ (q + (N - 1)) =
      (Equiv.Perm.sign (reverseRows N) : ℝ) *
        detAlternant a (complementShape q lam + rho N) := by
  have hb : ∀ i, (lam + rho N) i ≤ q + (N - 1) := by
    intro i
    have hq := hlam i
    simp only [Pi.add_apply, rho]
    omega
  rw [detAlternant_inverse_complement a ha (lam + rho N) (q + (N - 1)) hb,
    partition_complement_exponents q lam hlam, detAlternant_comp]

theorem schurValue_complement_of_injective (a : Fin N → ℝ)
    (ha : ∀ i, a i ≠ 0) (hinj : Function.Injective a)
    (q : ℕ) (lam : Fin N → ℕ) (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hbound : ∀ i, lam i ≤ q) :
    (∏ i, a i) ^ q * schurValue lam (fun i => (a i)⁻¹) =
      schurValue (complementShape q lam) a := by
  have hnum := detAlternant_inverse_partition a ha q lam hbound
  have hden := detAlternant_inverse_rho a ha
  rw [detAlternant_partition _ lam hlam,
    detAlternant_partition _ _ (complementShape_partition q lam hlam)] at hnum
  have heq :
      ((Equiv.Perm.sign (reverseRows N) : ℝ) * detAlternant a (rho N)) *
          ((∏ i, a i) ^ q * schurValue lam (fun i => (a i)⁻¹)) =
        ((Equiv.Perm.sign (reverseRows N) : ℝ) * detAlternant a (rho N)) *
          schurValue (complementShape q lam) a := by
    calc
      _ = (detAlternant (fun i => (a i)⁻¹) (rho N) * (∏ i, a i) ^ (N - 1)) *
          ((∏ i, a i) ^ q * schurValue lam (fun i => (a i)⁻¹)) := by rw [hden]
      _ = (detAlternant (fun i => (a i)⁻¹) (rho N) *
          schurValue lam (fun i => (a i)⁻¹)) * (∏ i, a i) ^ (q + (N - 1)) := by
            rw [pow_add]
            ring
      _ = _ := by rw [hnum]; ring
  exact mul_left_cancel₀ (mul_ne_zero (reverseSign_ne_zero N)
    (detAlternant_rho_ne_zero a hinj)) heq
open Filter Topology

/-- A perturbation that separates equal letters without changing their limit. -/
def perturbAlphabet (a : Fin N → ℝ) (t : ℝ) : Fin N → ℝ :=
  fun i => a i + t * (i.val : ℝ)

theorem perturbAlphabet_pos (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (t : ℝ) (ht : 0 ≤ t) : ∀ i, 0 < perturbAlphabet a t i := by
  intro i
  unfold perturbAlphabet
  have hterm : 0 ≤ t * (i.val : ℝ) := mul_nonneg ht (Nat.cast_nonneg _)
  linarith [ha i]

theorem perturbAlphabet_tendsto (a : Fin N → ℝ) :
    Tendsto (perturbAlphabet a) (𝓝[>] (0 : ℝ)) (𝓝 a) := by
  have hc : Continuous (perturbAlphabet a) := by
    unfold perturbAlphabet
    fun_prop
  have hzero : perturbAlphabet a 0 = a := by
    funext i
    simp [perturbAlphabet]
  have hlim : Tendsto (perturbAlphabet a) (𝓝[>] (0 : ℝ))
      (𝓝 (perturbAlphabet a 0)) :=
    (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left nhdsWithin_le_nhds
  rw [hzero] at hlim
  exact hlim

theorem perturbAlphabet_eventually_injective (a : Fin N → ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), Function.Injective (perturbAlphabet a t) := by
  change ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ i j, perturbAlphabet a t i = perturbAlphabet a t j → i = j
  apply Filter.eventually_all.mpr
  intro i
  apply Filter.eventually_all.mpr
  intro j
  by_cases hij : i = j
  · exact Filter.Eventually.of_forall (fun t h => hij)
  by_cases haij : a i = a j
  · have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    filter_upwards [htpos] with t ht
    intro heq
    have hmul : t * (i.val : ℝ) = t * (j.val : ℝ) := by
      dsimp [perturbAlphabet] at heq
      linarith
    have hv := mul_left_cancel₀ (ne_of_gt ht) hmul
    exact Fin.ext (by exact_mod_cast hv)
  · have hc : Continuous (fun t : ℝ => perturbAlphabet a t i - perturbAlphabet a t j) := by
      unfold perturbAlphabet
      fun_prop
    have hlim : Tendsto (fun t : ℝ => perturbAlphabet a t i - perturbAlphabet a t j)
        (𝓝[>] (0 : ℝ)) (𝓝 (a i - a j)) := by
      simpa [perturbAlphabet] using
        (hc.continuousAt (x := (0 : ℝ))).tendsto.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    have hne := hlim.eventually_ne (sub_ne_zero.mpr haij)
    filter_upwards [hne] with t ht
    intro heq
    exact False.elim (ht (sub_eq_zero.mpr heq))

theorem schurValue_continuous (lam : Fin N → ℕ) : Continuous (schurValue lam) := by
  exact MvPolynomial.continuous_eval (schurPoly lam)

theorem reciprocalSchur_continuousAt (a : Fin N → ℝ) (ha : ∀ i, a i ≠ 0)
    (q : ℕ) (lam : Fin N → ℕ) :
    ContinuousAt (fun x : Fin N → ℝ =>
      (∏ i, x i) ^ q * schurValue lam (fun i => (x i)⁻¹)) a := by
  have hp : Continuous (fun x : Fin N → ℝ => ∏ i, x i) := by fun_prop
  have hi : ContinuousAt (fun x : Fin N → ℝ => fun i => (x i)⁻¹) a := by
    apply continuousAt_pi.mpr
    intro i
    exact (continuous_apply i).continuousAt.inv₀ (ha i)
  exact (hp.continuousAt.pow q).mul ((schurValue_continuous lam).continuousAt.comp hi)

/-- Rectangle complementation for all positive letters, including repetitions.
The final step is the manuscript's continuity argument, with an explicit
perturbation and a proved eventually-injective property. -/
theorem schurValue_complement (a : Fin N → ℝ) (ha : ∀ i, 0 < a i)
    (q : ℕ) (lam : Fin N → ℕ) (hlam : AlgebraicCombinatorics.IsNPartition lam)
    (hbound : ∀ i, lam i ≤ q) :
    (∏ i, a i) ^ q * schurValue lam (fun i => (a i)⁻¹) =
      schurValue (complementShape q lam) a := by
  have hf := (reciprocalSchur_continuousAt a (fun i => ne_of_gt (ha i)) q lam).tendsto.comp
    (perturbAlphabet_tendsto a)
  have hg := (schurValue_continuous (complementShape q lam)).continuousAt.tendsto.comp
    (perturbAlphabet_tendsto a)
  have heq : (fun t => (∏ i, perturbAlphabet a t i) ^ q *
        schurValue lam (fun i => (perturbAlphabet a t i)⁻¹)) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun t => schurValue (complementShape q lam) (perturbAlphabet a t)) := by
    have htpos : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
    filter_upwards [perturbAlphabet_eventually_injective a, htpos] with t htinj ht
    exact schurValue_complement_of_injective _
      (fun i => ne_of_gt (perturbAlphabet_pos a ha t ht.le i)) htinj q lam hlam hbound
  exact tendsto_nhds_unique (Filter.Tendsto.congr' heq hf) hg
end CoefficientOne.RectangleComplement
