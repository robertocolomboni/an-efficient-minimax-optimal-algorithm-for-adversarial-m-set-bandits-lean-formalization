import MsetsPaper.Upper.EllipsoidVolume
import MsetsPaper.Upper.EllipsoidContraction

/-! The actual central-cut recursion and its finite-iteration correctness.
The oracle supplies cut vectors, not a precomputed accurate point. -/

noncomputable section
open scoped BigOperators
open Matrix

namespace MsetsPaper.Upper

variable {d : ℕ}

structure EllipsoidState (d : ℕ) where
  center : Fin d → ℝ
  shape : Matrix (Fin d) (Fin d) ℝ

def ellipsoidInitial (R : ℝ) : EllipsoidState d := ⟨0, (R ^ 2) • 1⟩

def ellipsoidStep (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (st : EllipsoidState d) : EllipsoidState d :=
  let g := oracle st.center
  if g = 0 then st
  else ⟨ellipsoidNextCenter st.center g st.shape, ellipsoidNextShape st.shape g⟩

def ellipsoidRun (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (R : ℝ) : ℕ → EllipsoidState d
  | 0 => ellipsoidInitial R
  | n + 1 => ellipsoidStep oracle (ellipsoidRun oracle R n)

theorem ellipsoidInitial_posDef (R : ℝ) (hR : 0 < R) :
    (ellipsoidInitial (d := d) R).shape.PosDef :=
  Matrix.PosDef.one.smul (sq_pos_of_pos hR)

theorem ellipsoidStep_posDef (hd : 2 ≤ d) (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (st : EllipsoidState d) (hst : st.shape.PosDef) :
    (ellipsoidStep oracle st).shape.PosDef := by
  dsimp only [ellipsoidStep]
  split_ifs with hg
  · exact hst
  · exact ellipsoidNextShape_posDef hd st.shape hst _ hg

theorem ellipsoidRun_posDef (hd : 2 ≤ d) (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (R : ℝ) (hR : 0 < R) (n : ℕ) : (ellipsoidRun oracle R n).shape.PosDef := by
  induction n with
  | zero => exact ellipsoidInitial_posDef R hR
  | succ n ih => exact ellipsoidStep_posDef hd oracle _ ih

theorem ellipsoidInitial_inverse (R : ℝ) (hR : 0 < R) :
    (ellipsoidInitial (d := d) R).shape⁻¹ = (1 / R ^ 2) • 1 := by
  apply Matrix.inv_eq_right_inv
  change (R ^ 2 • (1 : Matrix (Fin d) (Fin d) ℝ)) * ((1 / R ^ 2) • 1) = 1
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul]
  have heq : R ^ 2 * (1 / R ^ 2) = 1 := by field_simp
  rw [heq, one_smul]

theorem ellipsoidInitial_contains (R : ℝ) (hR : 0 < R)
    (x : Fin d → ℝ) (hx : euclideanNorm x ≤ R) :
    x ∈ ellipsoidSet (ellipsoidInitial R).center (ellipsoidInitial R).shape := by
  change ellipsoidQuadratic (ellipsoidInitial R).shape⁻¹ (x - 0) ≤ 1
  rw [sub_zero, ellipsoidInitial_inverse R hR]
  simp only [ellipsoidQuadratic, Matrix.smul_mulVec, Matrix.one_mulVec,
    dotProduct_smul, smul_eq_mul]
  have hnorm : x ⬝ᵥ x ≤ R ^ 2 := by
    have := euclideanNorm_sq x
    simp only [pow_two, dotProduct] at *
    nlinarith [euclideanNorm_nonneg x]
  have hscaled := mul_le_mul_of_nonneg_left hnorm (by positivity : 0 ≤ 1 / R ^ 2)
  have heq : (1 / R ^ 2) * R ^ 2 = 1 := by field_simp
  rwa [heq] at hscaled

theorem ellipsoidStep_contains (hd : 2 ≤ d) (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (st : EllipsoidState d) (hst : st.shape.PosDef) (x : Fin d → ℝ)
    (hx : x ∈ ellipsoidSet st.center st.shape)
    (hcut : (x - st.center) ⬝ᵥ oracle st.center ≤ 0) :
    x ∈ ellipsoidSet (ellipsoidStep oracle st).center (ellipsoidStep oracle st).shape := by
  dsimp only [ellipsoidStep]
  split_ifs with hg
  · exact hx
  · exact ellipsoid_central_cut_contains hd st.shape hst st.center _ x hg hx hcut

theorem ellipsoidRun_contains (hd : 2 ≤ d) (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (R : ℝ) (hR : 0 < R) (x : Fin d → ℝ) (hx : euclideanNorm x ≤ R)
    (n : ℕ) (hcuts : ∀ k < n, (x - (ellipsoidRun oracle R k).center) ⬝ᵥ
      oracle (ellipsoidRun oracle R k).center ≤ 0) :
    x ∈ ellipsoidSet (ellipsoidRun oracle R n).center (ellipsoidRun oracle R n).shape := by
  induction n with
  | zero => exact ellipsoidInitial_contains R hR x hx
  | succ n ih =>
    exact ellipsoidStep_contains hd oracle _ (ellipsoidRun_posDef hd oracle R hR n) x
      (ih (fun k hk => hcuts k (by omega))) (hcuts n (by omega))

theorem ellipsoidRun_det (hd : 2 ≤ d) (oracle : (Fin d → ℝ) → (Fin d → ℝ))
    (R : ℝ) (hR : 0 < R) (n : ℕ)
    (hnonzero : ∀ k < n, oracle (ellipsoidRun oracle R k).center ≠ 0) :
    (ellipsoidRun oracle R n).shape.det = (ellipsoidDetFactor d) ^ n * (R ^ 2) ^ d := by
  induction n with
  | zero => simp [ellipsoidRun, ellipsoidInitial, Matrix.det_smul]
  | succ n ih =>
    have hg := hnonzero n (by omega)
    simp only [ellipsoidRun, ellipsoidStep, hg, ↓reduceIte]
    rw [ellipsoidNextShape_det hd _ (ellipsoidRun_posDef hd oracle R hR n) _ hg,
      ih (fun k hk => hnonzero k (by omega)), pow_succ]
    unfold ellipsoidDetFactor
    ring

theorem ellipsoidRun_log_det_bound (hd : 2 ≤ d)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (R : ℝ) (hR : 0 < R) (n : ℕ)
    (hnonzero : ∀ k < n, oracle (ellipsoidRun oracle R k).center ≠ 0) :
    Real.log (ellipsoidRun oracle R n).shape.det ≤
      -(n : ℝ) / (2 * ((d : ℝ) + 1)) + 2 * (d : ℝ) * Real.log R := by
  rw [ellipsoidRun_det hd oracle R hR n hnonzero,
    Real.log_mul (pow_pos (ellipsoidDetFactor_pos hd) _).ne'
      (pow_pos (sq_pos_of_pos hR) _).ne', Real.log_pow, Real.log_pow, Real.log_pow]
  have h := mul_le_mul_of_nonneg_left (ellipsoidDetFactor_log_le hd)
    (Nat.cast_nonneg n : (0 : ℝ) ≤ n)
  push_cast
  calc
    _ ≤ (n : ℝ) * (-1 / (2 * ((d : ℝ) + 1))) + (d : ℝ) * (2 * Real.log R) := by linarith
    _ = _ := by ring

/-- The determinant formula computes the contraction of genuine Lebesgue
volume. This is the volume-decrease inequality used in the paper. -/
theorem ellipsoidRun_log_volume_bound (hd : 2 ≤ d)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (R : ℝ) (hR : 0 < R) (n : ℕ)
    (hnonzero : ∀ k < n, oracle (ellipsoidRun oracle R k).center ≠ 0) :
    Real.log (normalizedEllipsoidVolume (ellipsoidRun oracle R n).center
      (ellipsoidRun oracle R n).shape) ≤
      -(n : ℝ) / (4 * ((d : ℝ) + 1)) + (d : ℝ) * Real.log R := by
  rw [normalizedEllipsoidVolume_eq _ (ellipsoidRun_posDef hd oracle R hR n),
    Real.log_sqrt (ellipsoidRun_posDef hd oracle R hR n).det_pos.le]
  have h := ellipsoidRun_log_det_bound hd oracle R hR n hnonzero
  calc
    _ ≤ (-(n : ℝ) / (2 * ((d : ℝ) + 1)) + 2 * (d : ℝ) * Real.log R) / 2 :=
      div_le_div_of_nonneg_right h (by norm_num)
    _ = _ := by
      have hd1 : (d : ℝ) + 1 ≠ 0 := by positivity
      field_simp
      <;> ring

/-- No convergence premise: after this many concrete updates, one queried
center satisfies `Good`, provided its failure gives a valid nonzero central
cut preserving the explicitly supplied ball. -/
theorem ellipsoidRun_finds_good (hd : 2 ≤ d)
    (oracle : (Fin d → ℝ) → (Fin d → ℝ)) (Good : (Fin d → ℝ) → Prop)
    (R rho : ℝ) (hR : 0 < R) (hrho : 0 < rho) (u : Fin d → ℝ)
    (hinit : ∀ x, euclideanNorm (x - u) ≤ rho → euclideanNorm x ≤ R)
    (hcut : ∀ c, ¬ Good c → oracle c ≠ 0 ∧
      ∀ x, euclideanNorm (x - u) ≤ rho → (x - c) ⬝ᵥ oracle c ≤ 0)
    (N : ℕ) (hN : 4 * (d : ℝ) * ((d : ℝ) + 1) * Real.log (R / rho) < N) :
    ∃ k < N, Good (ellipsoidRun oracle R k).center := by
  by_contra hnone
  have hbad : ∀ k < N, ¬ Good (ellipsoidRun oracle R k).center := by
    intro k hk hgood
    exact hnone ⟨k, hk, hgood⟩
  have hnz : ∀ k < N, oracle (ellipsoidRun oracle R k).center ≠ 0 :=
    fun k hk => (hcut _ (hbad k hk)).1
  have hball : ∀ x, euclideanNorm (x - u) ≤ rho →
      x ∈ ellipsoidSet (ellipsoidRun oracle R N).center (ellipsoidRun oracle R N).shape := by
    intro x hx
    exact ellipsoidRun_contains hd oracle R hR x (hinit x hx) N
      (fun k hk => (hcut _ (hbad k hk)).2 x hx)
  have hloglow := ellipsoid_ball_log_volume_lower _ (ellipsoidRun_posDef hd oracle R hR N)
    _ u rho hrho hball
  have hlogupper := ellipsoidRun_log_volume_bound hd oracle R hR N hnz
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hden : (0 : ℝ) < 4 * ((d : ℝ) + 1) := by linarith
  have hle : (N : ℝ) / (4 * ((d : ℝ) + 1)) ≤
      (d : ℝ) * (Real.log R - Real.log rho) := by
    rw [neg_div] at hlogupper
    nlinarith only [hloglow, hlogupper]
  have hle' := (div_le_iff₀ hden).mp hle
  rw [Real.log_div hR.ne' hrho.ne'] at hN
  nlinarith

end MsetsPaper.Upper
