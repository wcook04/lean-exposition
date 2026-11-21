import Breakdown.CertTorus.RegularStatements

open Filter
open scoped Topology

noncomputable section

namespace Breakdown.FarField

namespace Internal.BilinLeibnizShift

theorem tendsto_of_quotient {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : ℝ → E →L[ℝ] E) (v v' : E)
    (hv : Tendsto (fun t : ℝ => t⁻¹ • (T t v - v)) (𝓝[≠] 0) (𝓝 v')) :
    Tendsto (fun t : ℝ => T t v) (𝓝[≠] 0) (𝓝 v) := by
  have ht : Tendsto (fun t : ℝ => t) (𝓝[≠] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hlim : Tendsto (fun t : ℝ => v + t • (t⁻¹ • (T t v - v))) (𝓝[≠] 0)
      (𝓝 (v + (0 : ℝ) • v')) := tendsto_const_nhds.add (ht.smul hv)
  rw [zero_smul, add_zero] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t (htne : t ≠ 0)
  rw [smul_smul, mul_inv_cancel₀ htne, one_smul, add_sub_cancel]

theorem leibniz_of_covariant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E) (T : ℝ → E →L[ℝ] E) (u u' v v' : E)
    (hcov : ∀ t, B (T t u) (T t v) = T t (B u v))
    (hu : Tendsto (fun t : ℝ => t⁻¹ • (T t u - u)) (𝓝[≠] 0) (𝓝 u'))
    (hv : Tendsto (fun t : ℝ => t⁻¹ • (T t v - v)) (𝓝[≠] 0) (𝓝 v')) :
    Tendsto (fun t : ℝ => t⁻¹ • (T t (B u v) - B u v)) (𝓝[≠] 0) (𝓝 (B u' v + B u v')) := by
  have hTv := tendsto_of_quotient T v v' hv
  have h1 : Tendsto (fun t : ℝ => B (t⁻¹ • (T t u - u)) (T t v)) (𝓝[≠] 0) (𝓝 (B u' v)) :=
    (B.continuous₂.tendsto (u', v)).comp (hu.prodMk_nhds hTv)
  have h2 : Tendsto (fun t : ℝ => B u (t⁻¹ • (T t v - v))) (𝓝[≠] 0) (𝓝 (B u v')) :=
    ((B u).continuous.tendsto v').comp hv
  refine (h1.add h2).congr' (Eventually.of_forall fun t => ?_)
  beta_reduce
  rw [← hcov t]
  simp only [map_sub, map_smul, sub_apply, smul_apply,
    smul_sub]
  abel

end Internal.BilinLeibnizShift

open Freq SmoothFlow

theorem bilinLeibnizOfShift_holds : BilinLeibnizOfShift := by
  intro hSc hDq τ hτ j u u' v v' hu hv
  exact (hDq j _ _).2 (Internal.BilinLeibnizShift.leibniz_of_covariant (bilinX τ)
    (fun t => shiftX (-(t • unitVector j))) u u' v v' (fun t => hSc τ hτ _ u v)
    ((hDq j u u').1 hu) ((hDq j v v').1 hv))

end Breakdown.FarField
