import CoefficientOne.Main
import EffectiveResistance.RegressionIdentity

/-!
# The elementary electrical-network examples

The two-vertex reduction and the two-edge path are evaluated directly from
their Laplacians. Explicit symmetric Green kernels solve every zero-sum
demand, so the examples do not assume existence of an inverse.
-/

open scoped BigOperators
open Matrix EffectiveResistance

namespace CoefficientOne

noncomputable section

def twoVertexNetwork (v : ℝ) (hv : 0 ≤ v) : ConductanceNetwork (Fin 2) where
  conductance := !![0, v; v, 0]
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  nonnegative := by
    intro i j
    fin_cases i <;> fin_cases j <;> simpa using hv
  diagonal_zero := by intro i; fin_cases i <;> rfl

def twoVertexGreenKernel (v : ℝ) (hv : 0 < v) : GreenKernel (twoVertexNetwork v hv.le) where
  kernel := Matrix.diagonal ![v⁻¹, 0]
  symmetric := Matrix.isSymm_diagonal _
  solves_zeroSum y hy := by
    have hsum : y 0 + y 1 = 0 := by simpa [IsZeroSum, Fin.sum_univ_two] using hy
    ext i
    fin_cases i <;>
      simp [ConductanceNetwork.laplacian, ConductanceNetwork.degree,
        twoVertexNetwork, Matrix.mulVec, dotProduct, Fin.sum_univ_two, hv.ne'] <;>
      linarith

/-- The resistance of the two-vertex graph is the reciprocal conductance. -/
theorem twoVertex_effectiveResistance (v : ℝ) (hv : 0 < v) :
    (twoVertexGreenKernel v hv).effectiveResistance 0 1 = 1 / v := by
  simp [GreenKernel.effectiveResistance, GreenKernel.potential, twoVertexGreenKernel,
    quadraticForm, pairDemand, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_two,
    one_div]

/-- Identifying all vertices other than i leaves the total incident
conductance, whose reciprocal is precisely the two-vertex resistance. -/
theorem contracted_vertex_effectiveResistance
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (N : ConductanceNetwork ι) (i : ι) (hi : 0 < N.degree i) :
    (twoVertexGreenKernel (N.degree i) hi).effectiveResistance 0 1 =
      1 / (∑ j, N.conductance i j) :=
  twoVertex_effectiveResistance (N.degree i) hi

def twoEdgePathNetwork (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ConductanceNetwork (Fin 3) where
  conductance := !![0, a, 0; a, 0, b; 0, b, 0]
  symmetric := by
    apply Matrix.IsSymm.ext
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  nonnegative := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp_all
  diagonal_zero := by intro i; fin_cases i <;> rfl

def twoEdgePathGreenKernel (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    GreenKernel (twoEdgePathNetwork a b ha.le hb.le) where
  kernel := Matrix.diagonal ![a⁻¹, 0, b⁻¹]
  symmetric := Matrix.isSymm_diagonal _
  solves_zeroSum y hy := by
    have hsum : y 0 + y 1 + y 2 = 0 := by
      simpa [IsZeroSum, Fin.sum_univ_three, add_assoc] using hy
    ext i
    fin_cases i <;>
      simp [ConductanceNetwork.laplacian, ConductanceNetwork.degree,
        twoEdgePathNetwork, Matrix.mulVec, dotProduct, Fin.sum_univ_three, ha.ne', hb.ne'] <;>
      linarith

/-- The two resistances on a two-edge path add. -/
theorem twoEdgePath_effectiveResistance (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (twoEdgePathGreenKernel a b ha hb).effectiveResistance 0 2 = 1 / a + 1 / b := by
  simp [GreenKernel.effectiveResistance, GreenKernel.potential, twoEdgePathGreenKernel,
    pairDemand, Matrix.mulVec_diagonal, dotProduct, Fin.sum_univ_three, one_div]

theorem twoEdgePath_endpoint_degrees (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (twoEdgePathNetwork a b ha hb).degree 0 = a ∧
      (twoEdgePathNetwork a b ha hb).degree 2 = b := by
  simp [ConductanceNetwork.degree, twoEdgePathNetwork, Fin.sum_univ_three]

theorem twoEdgePath_effectiveResistance_eq_inverse_degrees
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    (twoEdgePathGreenKernel a b ha hb).effectiveResistance 0 2 =
      1 / (twoEdgePathNetwork a b ha.le hb.le).degree 0 +
      1 / (twoEdgePathNetwork a b ha.le hb.le).degree 2 := by
  rw [(twoEdgePath_endpoint_degrees a b ha.le hb.le).1,
    (twoEdgePath_endpoint_degrees a b ha.le hb.le).2]
  exact twoEdgePath_effectiveResistance a b ha hb

end

end CoefficientOne
