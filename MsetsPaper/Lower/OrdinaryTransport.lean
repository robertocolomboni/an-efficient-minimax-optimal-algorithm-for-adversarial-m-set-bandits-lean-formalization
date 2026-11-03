import MsetsPaper.Lower.OrdinaryProtocol
import MsetsPaper.Lower.OrdinaryNewRoute

/-! # Exact transport from ordinary arms to singleton-set actions

The policy translation uses only the action/history equivalences.  The loss
translation is subsequently applied to the adversary returned by the m-set
theorem.  The identities below hold at every history, not only almost surely.
-/

namespace MsetsPaper.Lower.Ordinary

open MeasureTheory ProbabilityTheory

noncomputable section

def armEquiv (K : ℕ) : Fin K ≃ᵐ MsetsLower.MSetAction K 1 where
  toEquiv := NewRoute.ordinaryArmEquiv K
  measurable_toFun := measurable_of_finite _
  measurable_invFun := measurable_of_finite _

@[simp] theorem armEquiv_loss {K : ℕ} (i : Fin K) (ell : Fin K → ℝ) :
    MsetsLower.actionLoss (armEquiv K i) ell = ell i :=
  NewRoute.ordinaryArmEquiv_loss i ell

def historyEquiv (K : ℕ) : (t : ℕ) → History K t ≃ᵐ MsetsLower.History K 1 t
  | 0 => MeasurableEquiv.refl Unit
  | t + 1 => MeasurableEquiv.prodCongr (historyEquiv K t)
      (MeasurableEquiv.prodCongr (armEquiv K) (MeasurableEquiv.refl ℝ))

@[simp] theorem historyEquiv_succ {K : ℕ} (t : ℕ)
    (h : History K t) (i : Fin K) (z : ℝ) :
    historyEquiv K (t + 1) (h.snoc i z) =
      (historyEquiv K t h).snoc (armEquiv K i) z := rfl

/-- Translate a learner before selecting any loss process. -/
def toMsetPolicy {K : ℕ} (P : Policy K) : MsetsLower.Policy K 1 where
  kernel t := Kernel.map
    (Kernel.comap (P.kernel t) (historyEquiv K t).symm
      (historyEquiv K t).symm.measurable) (armEquiv K)
  isMarkov t := by
    letI : IsMarkovKernel (P.kernel t) := P.isMarkov t
    exact Kernel.IsMarkovKernel.map _ (armEquiv K).measurable

theorem toMsetPolicy_kernel {K : ℕ} (P : Policy K) (t : ℕ) (h : History K t) :
    (toMsetPolicy P).kernel t (historyEquiv K t h) =
      (P.kernel t h).map (armEquiv K) := by
  change (Kernel.map
    (Kernel.comap (P.kernel t) (historyEquiv K t).symm
      (historyEquiv K t).symm.measurable) (armEquiv K)) (historyEquiv K t h) = _
  rw [Kernel.map_apply _ (armEquiv K).measurable, Kernel.comap_apply]
  simp

def fromMsetLoss {K : ℕ} (G : MsetsLower.LossProcess K 1) : LossProcess K where
  loss t h := G.itemLoss t (historyEquiv K t h)
  measurable_loss t := (G.measurable_itemLoss t).comp (historyEquiv K t).measurable
  loss_mem_Icc t h i := NewRoute.ordinary_item_range G t (historyEquiv K t h) i

@[simp] theorem fromMsetLoss_loss {K : ℕ} (G : MsetsLower.LossProcess K 1)
    (t : ℕ) (h : History K t) :
    (fromMsetLoss G).loss t h = G.itemLoss t (historyEquiv K t h) := rfl

/-- One full update preserves both the chosen arm and the scalar feedback. -/
theorem extendRun_transport {K : ℕ} (G : MsetsLower.LossProcess K 1)
    (t : ℕ) (h : History K t) (i : Fin K) :
    historyEquiv K (t + 1) (extendRun (fromMsetLoss G) t (h, i)) =
      MsetsLower.extendRun G t (historyEquiv K t h, armEquiv K i) := by
  change (historyEquiv K t h).snoc (armEquiv K i) (G.itemLoss t (historyEquiv K t h) i) =
    (historyEquiv K t h).snoc (armEquiv K i)
      (MsetsLower.actionLoss (armEquiv K i) (G.itemLoss t (historyEquiv K t h)))
  rw [armEquiv_loss]

theorem roundKernel_transport {K : ℕ} (P : Policy K)
    (G : MsetsLower.LossProcess K 1) (t : ℕ) (h : History K t) :
    MsetsLower.roundKernel (toMsetPolicy P) G t (historyEquiv K t h) =
      (roundKernel P (fromMsetLoss G) t h).map (historyEquiv K (t + 1)) := by
  ext S hS
  rw [MsetsLower.roundKernel_apply _ _ _ _ hS, toMsetPolicy_kernel,
    Measure.map_apply (armEquiv K).measurable (MeasurableSet.of_discrete : MeasurableSet
      {a : MsetsLower.MSetAction K 1 | (historyEquiv K t h).snoc a
        (MsetsLower.actionLoss a (G.itemLoss t (historyEquiv K t h))) ∈ S}),
    Measure.map_apply (historyEquiv K (t + 1)).measurable hS,
    roundKernel_apply _ _ _ _ ((historyEquiv K (t + 1)).measurable hS)]
  congr 1
  ext i
  change MsetsLower.extendRun G t (historyEquiv K t h, armEquiv K i) ∈ S ↔
    historyEquiv K (t + 1) (extendRun (fromMsetLoss G) t (h, i)) ∈ S
  rw [extendRun_transport]

private theorem comap_comp_eq_comp_map
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (e : α ≃ᵐ β) (μ : Measure α) (κ : Kernel β γ) :
    (Kernel.comap κ e e.measurable) ∘ₘ μ = κ ∘ₘ μ.map e := by
  ext S hS
  rw [Measure.bind_apply hS (Kernel.aemeasurable _),
    Measure.bind_apply hS (Kernel.aemeasurable _),
    MeasureTheory.lintegral_map (Kernel.measurable_coe κ hS) e.measurable]
  rfl

/-- The native ordinary interaction law is transported exactly at every horizon. -/
theorem runLaw_transport {K : ℕ} (P : Policy K)
    (G : MsetsLower.LossProcess K 1) : ∀ t,
    (runLaw P (fromMsetLoss G) t).map (historyEquiv K t) =
      MsetsLower.runLaw (toMsetPolicy P) G t := by
  intro t
  induction t with
  | zero => exact Measure.map_dirac' (historyEquiv K 0).measurable ()
  | succ t ih =>
      rw [runLaw_succ, MsetsLower.runLaw_succ,
        Measure.map_comp _ _ (historyEquiv K (t + 1)).measurable]
      have hk : (roundKernel P (fromMsetLoss G) t).map (historyEquiv K (t + 1)) =
          Kernel.comap (MsetsLower.roundKernel (toMsetPolicy P) G t)
            (historyEquiv K t) (historyEquiv K t).measurable := by
        ext h S hS
        rw [Kernel.map_apply _ (historyEquiv K (t + 1)).measurable, Kernel.comap_apply]
        exact congrArg (fun μ : Measure (MsetsLower.History K 1 (t + 1)) ↦ μ S)
          (roundKernel_transport P G t h).symm
      rw [hk, comap_comp_eq_comp_map, ih]

theorem realizedCumulativeLoss_transport {K : ℕ} (G : MsetsLower.LossProcess K 1) :
    ∀ t (h : History K t), realizedCumulativeLoss (fromMsetLoss G) t h =
      MsetsLower.Lower.realizedCumulativeLoss G t (historyEquiv K t h) := by
  intro t
  induction t with
  | zero => intro h; rfl
  | succ t ih =>
      rintro ⟨h, i, z⟩
      change realizedCumulativeLoss (fromMsetLoss G) t h + G.itemLoss t (historyEquiv K t h) i =
        MsetsLower.Lower.realizedCumulativeLoss G t (historyEquiv K t h) +
          MsetsLower.actionLoss (armEquiv K i) (G.itemLoss t (historyEquiv K t h))
      rw [ih, armEquiv_loss]

theorem comparatorCumulativeLoss_transport {K : ℕ} (G : MsetsLower.LossProcess K 1) :
    ∀ t (h : History K t) (i : Fin K), comparatorCumulativeLoss (fromMsetLoss G) t h i =
      MsetsLower.Lower.comparatorCumulativeLoss G t (historyEquiv K t h) (armEquiv K i) := by
  intro t
  induction t with
  | zero => intro h i; rfl
  | succ t ih =>
      rintro ⟨h, played, z⟩ i
      change comparatorCumulativeLoss (fromMsetLoss G) t h i + G.itemLoss t (historyEquiv K t h) i =
        MsetsLower.Lower.comparatorCumulativeLoss G t (historyEquiv K t h) (armEquiv K i) +
          MsetsLower.actionLoss (armEquiv K i) (G.itemLoss t (historyEquiv K t h))
      rw [ih, armEquiv_loss]

theorem bestComparatorCumulativeLoss_transport {K : ℕ} (G : MsetsLower.LossProcess K 1)
    (t : ℕ) (h : History K t) :
    bestComparatorCumulativeLoss (fromMsetLoss G) t h =
      MsetsLower.Lower.bestComparatorCumulativeLoss G t (historyEquiv K t h) := by
  unfold bestComparatorCumulativeLoss MsetsLower.Lower.bestComparatorCumulativeLoss
  congr 1
  ext z
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨armEquiv K i, (comparatorCumulativeLoss_transport G t h i).symm⟩
  · rintro ⟨a, rfl⟩
    refine ⟨(armEquiv K).symm a, ?_⟩
    simpa using comparatorCumulativeLoss_transport G t h ((armEquiv K).symm a)

theorem pathRegret_transport {K : ℕ} (G : MsetsLower.LossProcess K 1)
    (t : ℕ) (h : History K t) :
    pathRegret (fromMsetLoss G) t h =
      MsetsLower.Lower.pathRegret G t (historyEquiv K t h) := by
  unfold pathRegret MsetsLower.Lower.pathRegret
  rw [realizedCumulativeLoss_transport, bestComparatorCumulativeLoss_transport]

theorem regret_tail_transport {K : ℕ} (hK : 1 ≤ K) (P : Policy K)
    (G : MsetsLower.LossProcess K 1) (T : ℕ) (b : ℝ) :
    (runLaw P (fromMsetLoss G) T).real {h | b ≤ pathRegret (fromMsetLoss G) T h} =
      (MsetsLower.runLaw (toMsetPolicy P) G T).real
        {h | b ≤ MsetsLower.Lower.pathRegret G T h} := by
  have hE := MsetsLower.Lower.measurableSet_pathRegret_ge_of_le hK G T b
  have hevents : {h | b ≤ pathRegret (fromMsetLoss G) T h} =
      (historyEquiv K T) ⁻¹' {h | b ≤ MsetsLower.Lower.pathRegret G T h} := by
    ext h
    simp only [Set.mem_setOf_eq, Set.mem_preimage, pathRegret_transport]
  rw [hevents, ← runLaw_transport P G T]
  exact congrArg ENNReal.toReal
    (Measure.map_apply (historyEquiv K T).measurable hE).symm

end
end MsetsPaper.Lower.Ordinary
