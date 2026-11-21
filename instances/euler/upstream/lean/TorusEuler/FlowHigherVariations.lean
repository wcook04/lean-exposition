import TorusEuler.LabelFlowGeometry
import TorusEuler.HigherFlowBounds
import TorusEuler.LinearODEParameterDependence
import Mathlib.Analysis.Calculus.ContDiff.FaaDiBruno
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Smooth dependence of a finite-dimensional trajectory family. The differentiated
system on a state and its label Jacobian gives an induction on the spatial order. -/

open Asymptotics ContinuousLinearMap Filter MeasureTheory Metric Set
open scoped BigOperators ContDiff NNReal Topology

namespace TorusEuler

section SpatialDerivatives

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem hasFDerivAt_slice {V : ℝ × E → F} {T t : ℝ}
    (hV : DifferentiableOn ℝ V (Icc 0 T ×ˢ (univ : Set E))) (ht : t ∈ Icc 0 T) (x : E) :
    HasFDerivAt (fun y => V (t, y))
      ((fderivWithin ℝ V (Icc 0 T ×ˢ (univ : Set E)) (t, x)).comp (inr ℝ ℝ E)) x :=
  (hV (t, x) ⟨ht, mem_univ _⟩).hasFDerivWithinAt.comp_hasFDerivAt x
    (hasFDerivAt_prodMk_right (𝕜 := ℝ) t x) (Eventually.of_forall fun y => ⟨ht, mem_univ y⟩)

/-- Spatial differentiation preserves joint smoothness on the slab. The within
derivative is applied only to spatial increments, including at the time endpoints. -/
private theorem contDiffOn_spatialFDeriv {f : ℝ → E → F} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × E => fderiv ℝ (f p.1) p.2) (Icc 0 T ×ˢ (univ : Set E)) := by
  let S := Icc 0 T ×ˢ (univ : Set E)
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  refine ((hf.fderivWithin hS (m := ∞) (by simp)).clm_comp
    (contDiffOn_const (c := inr ℝ ℝ E))).congr ?_
  rintro ⟨t, x⟩ hx
  exact (hasFDerivAt_slice (hf.differentiableOn (by simp)) hx.1 x).fderiv

private theorem differentiable_spatialSlice {f : ℝ → E → F} {T t : ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E)))
    (ht : t ∈ Icc 0 T) : Differentiable ℝ (f t) :=
  fun x => (hasFDerivAt_slice (hf.differentiableOn (by simp)) ht x).differentiableAt

private theorem contDiff_spatialSlice {f : ℝ → E → F} {T t : ℝ}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

private theorem norm_taylor_on_convex {f : E → F} {s : Set E} {K : ℝ≥0}
    (hs : Convex ℝ s) (hf : ∀ x ∈ s, DifferentiableAt ℝ f x)
    (hLip : LipschitzOnWith K (fderiv ℝ f) s) {x y : E} (hx : x ∈ s) (hy : y ∈ s) :
    ‖f y - f x - fderiv ℝ f x (y - x)‖ ≤ (K : ℝ) * ‖y - x‖ ^ 2 := by
  rw [pow_two, ← mul_assoc]
  have hy' : y ∈ closedBall x ‖y - x‖ := by simp [dist_eq_norm]
  refine (hs.inter (convex_closedBall x ‖y - x‖)).norm_image_sub_le_of_norm_fderiv_le'
    (fun z hz => hf z hz.1) (fun z hz => ?_) ⟨hx, mem_closedBall_self (norm_nonneg _)⟩ ⟨hy, hy'⟩
  have hd := (mem_closedBall.mp hz.2 : dist z x ≤ ‖y - x‖)
  simpa only [dist_eq_norm] using
    (hLip.dist_le_mul z hz.1 x hx).trans (mul_le_mul_of_nonneg_left hd K.coe_nonneg)

end SpatialDerivatives

private theorem uniform_gronwall {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {x dx : ℝ → F} {T K δ ε t : ℝ} (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hx : ∀ u ∈ Icc 0 T, HasDerivWithinAt x (dx u) (Icc 0 T) u)
    (hinit : ‖x 0‖ ≤ δ) (hd : ∀ u ∈ Icc 0 T, ‖dx u‖ ≤ K * ‖x u‖ + ε)
    (ht : t ∈ Icc 0 T) : ‖x t‖ ≤ gronwallBound δ K ε T := by
  have hb := norm_le_gronwallBound_of_norm_deriv_right_le (HasDerivWithinAt.continuousOn hx)
    (fun u hu => (hx u (Ico_subset_Icc_self hu)).mono_of_mem_nhdsWithin
      (Icc_mem_nhdsGE_of_mem hu)) hinit (fun u hu => hd u (Ico_subset_Icc_self hu)) t ht
  simp only [sub_zero] at hb
  exact hb.trans (gronwallBound_mono ((norm_nonneg _).trans hinit) hε hK ht.2)

private theorem gronwallBound_mul_data (A K C d T : ℝ) :
    gronwallBound (A * d) K (C * d) T = gronwallBound A K C T * d := by
  by_cases hK : K = 0 <;> simp [gronwallBound, hK] <;> ring

private theorem hasDerivWithinAt_linearImage
    {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
    [NormedAddCommGroup B] [NormedSpace ℝ B] (L : A →L[ℝ] B)
    {u : ℝ → A} {du : A} {I : Set ℝ} {t : ℝ}
    (hu : HasDerivWithinAt u du I t) : HasDerivWithinAt (fun s => L (u s)) (L du) I t :=
  L.hasFDerivAt.comp_hasDerivWithinAt t hu

section DifferentiatedSystem

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 600000 in
/-- A jointly continuous trajectory family of a smooth ordinary differential
equation has a jointly continuous spatial derivative. The derivative satisfies
the first variational equation with the spatial derivative of the initial data. -/
theorem trajectoryFamily_spatialDerivative
    {f : ℝ → E → E} {Y : ℝ → P → E} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E)))
    (hYc : ContinuousOn (Function.uncurry Y) (Icc 0 T ×ˢ (univ : Set P)))
    (hYt : ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => Y s p) (f t (Y t p)) (Icc 0 T) t)
    (hY₀ : ContDiff ℝ ∞ (Y 0)) :
    let J (t : ℝ) := fderiv ℝ (Y t)
    (∀ t ∈ Icc 0 T, Differentiable ℝ (Y t)) ∧
    ContinuousOn (Function.uncurry J) (Icc 0 T ×ˢ (univ : Set P)) ∧
    ∀ p t, t ∈ Icc 0 T → HasDerivWithinAt (fun s => J s p)
      ((fderiv ℝ (f t) (Y t p)).comp (J t p)) (Icc 0 T) t := by
  let A (t : ℝ) (p : P) := fderiv ℝ (f t) (Y t p)
  let G (t : ℝ) (x : E) := fderiv ℝ (f t) x
  have hG : ContDiffOn ℝ ∞ (Function.uncurry G) (Icc 0 T ×ˢ (univ : Set E)) :=
    contDiffOn_spatialFDeriv hT hf
  have hH : ContinuousOn (fun q : ℝ × E => fderiv ℝ (G q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set E)) := (contDiffOn_spatialFDeriv hT hG).continuousOn
  have hA (p : P) : ContinuousOn (fun t => A t p) (Icc 0 T) :=
    hG.continuousOn.comp (continuousOn_id.prodMk (HasDerivWithinAt.continuousOn (hYt p)))
      (fun t ht => ⟨ht, mem_univ (Y t p)⟩)
  let compLeft := ContinuousLinearMap.compL ℝ P E E
  have hExist (p : P) := linearODE_exists_Icc (E := P →L[ℝ] E)
    (A := fun t => compLeft (A t p)) hT.le (compLeft.continuous.comp_continuousOn (hA p))
    (fderiv ℝ (Y 0) p)
  choose W hW₀ hWt using hExist
  let V (t : ℝ) (p : P) := W p t
  have hVt (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun s => V s p) ((A t p).comp (V t p)) (Icc 0 T) t :=
    hWt p t ht
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hLocal (p : P) :
      (∀ t ∈ Icc 0 T, HasFDerivAt (Y t) (V t p) p) ∧
      ContinuousOn (Function.uncurry V) (Icc 0 T ×ˢ closedBall p 1) := by
    let S := closedBall p 1
    have hS : IsCompact S := isCompact_closedBall _ _
    have hp : p ∈ S := mem_closedBall_self zero_le_one
    have hSlab : IsCompact (Icc (0 : ℝ) T ×ˢ S) := isCompact_Icc.prod hS
    obtain ⟨M, hM⟩ := hSlab.exists_bound_of_continuousOn (f := Function.uncurry Y)
      (hYc.mono (prod_subset_prod_right (subset_univ S)))
    let R := closedBall (0 : E) M
    have hYmem (q : P) (hq : q ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T) : Y t q ∈ R := by
      simpa only [R, mem_closedBall, dist_zero_right, Function.uncurry_apply_pair]
        using hM (t, q) ⟨ht, hq⟩
    have hRC : IsCompact (Icc (0 : ℝ) T ×ˢ R) :=
      isCompact_Icc.prod (isCompact_closedBall _ _)
    obtain ⟨k, hk⟩ := hRC.exists_bound_of_continuousOn (f := Function.uncurry G)
      (hG.continuousOn.mono (prod_subset_prod_right (subset_univ R)))
    obtain ⟨l, hl⟩ := hRC.exists_bound_of_continuousOn (f := fun q : ℝ × E =>
      fderiv ℝ (G q.1) q.2) (hH.mono (prod_subset_prod_right (subset_univ R)))
    let K := Real.toNNReal k
    let L := Real.toNNReal l
    have hK (t : ℝ) (ht : t ∈ Icc 0 T) (x : E) (hx : x ∈ R) : ‖G t x‖ ≤ K :=
      (hk (t, x) ⟨ht, hx⟩).trans (Real.le_coe_toNNReal k)
    have hfLip (t : ℝ) (ht : t ∈ Icc 0 T) : LipschitzOnWith K (f t) R :=
      (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => differentiable_spatialSlice hf ht x) (fun x hx => by
          exact_mod_cast hK t ht x hx)
    have hGLip (t : ℝ) (ht : t ∈ Icc 0 T) : LipschitzOnWith L (G t) R :=
      (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun x _ => differentiable_spatialSlice hG ht x) (fun x hx => by
          exact_mod_cast (hl (t, x) ⟨ht, hx⟩).trans (Real.le_coe_toNNReal l))
    have hJ₀ : ContDiff ℝ ∞ (fderiv ℝ (Y 0)) := (contDiff_infty_iff_fderiv.mp hY₀).2
    obtain ⟨d, hd⟩ := hS.exists_bound_of_continuousOn (f := fderiv ℝ (Y 0)) hJ₀.continuous.continuousOn
    obtain ⟨b, hb⟩ := hS.exists_bound_of_continuousOn (f := fderiv ℝ (fderiv ℝ (Y 0)))
      (contDiff_infty_iff_fderiv.mp hJ₀).2.continuous.continuousOn
    let D := Real.toNNReal d
    let B := Real.toNNReal b
    have hD (q : P) (hq : q ∈ S) : ‖fderiv ℝ (Y 0) q‖ ≤ D :=
      (hd q hq).trans (Real.le_coe_toNNReal d)
    have hinitLip : LipschitzOnWith D (Y 0) S :=
      (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun q _ => hY₀.differentiable (by simp) q) (fun q hq => by exact_mod_cast hD q hq)
    have hJ₀Lip : LipschitzOnWith B (fderiv ℝ (Y 0)) S :=
      (convex_closedBall _ _).lipschitzOnWith_of_nnnorm_fderiv_le
        (fun q _ => hJ₀.differentiable (by simp) q) (fun q hq => by
          exact_mod_cast (hb q hq).trans (Real.le_coe_toNNReal b))
    let Q := (D : ℝ) * Real.exp ((K : ℝ) * T)
    have hQ : 0 ≤ Q := mul_nonneg D.coe_nonneg (Real.exp_pos _).le
    have hYlip (q r : P) (hq : q ∈ S) (hr : r ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T) :
        ‖Y t q - Y t r‖ ≤ Q * ‖q - r‖ := by
      have hinit : ‖Y 0 q - Y 0 r‖ ≤ D * ‖q - r‖ := by
        simpa only [dist_eq_norm] using hinitLip.dist_le_mul q hq r hr
      have hrate (u : ℝ) (hu : u ∈ Icc 0 T) :
          ‖f u (Y u q) - f u (Y u r)‖ ≤ K * ‖Y u q - Y u r‖ + 0 := by
        simpa only [dist_eq_norm, add_zero] using
          (hfLip u hu).dist_le_mul _ (hYmem q hq u hu) _ (hYmem r hr u hu)
      have h := uniform_gronwall K.coe_nonneg (le_refl 0)
        (fun u hu => (hYt q u hu).sub (hYt r u hu)) hinit hrate ht
      rw [gronwallBound_ε0] at h
      exact h.trans_eq (by dsimp only [Q]; ring)
    have hVbound (q : P) (hq : q ∈ S) (t : ℝ) (ht : t ∈ Icc 0 T) : ‖V t q‖ ≤ Q := by
      have hinit : ‖V 0 q‖ ≤ (D : ℝ) := by simpa only [V, hW₀ q] using hD q hq
      have hrate (u : ℝ) (hu : u ∈ Icc 0 T) :
          ‖(A u q).comp (V u q)‖ ≤ K * ‖V u q‖ + 0 := by
        rw [add_zero]
        exact (opNorm_comp_le _ _).trans
          (mul_le_mul_of_nonneg_right (hK u hu _ (hYmem q hq u hu)) (norm_nonneg _))
      have h := uniform_gronwall K.coe_nonneg (le_refl 0) (hVt q) hinit hrate ht
      rwa [gronwallBound_ε0] at h
    constructor
    · intro t ht
      let Pbound := gronwallBound B K ((L : ℝ) * Q ^ 2) T
      have hErr (q : P) (hq : q ∈ S) :
          ‖Y t q - Y t p - V t p (q - p)‖ ≤ Pbound * ‖q - p‖ ^ 2 := by
        let Δ (u : ℝ) := Y u q - Y u p
        let err (u : ℝ) := Δ u - V u p (q - p)
        let dErr (u : ℝ) :=
          A u p (err u) + (f u (Y u q) - f u (Y u p) - A u p (Δ u))
        have hErrD (u : ℝ) (hu : u ∈ Icc 0 T) : HasDerivWithinAt err (dErr u) (Icc 0 T) u := by
          refine (((hYt q u hu).sub (hYt p u hu)).sub
            ((hVt p u hu).clm_apply (hasDerivWithinAt_const u (Icc 0 T) (q - p)))).congr_deriv ?_
          simp [err, dErr, map_sub]
        have hinit : ‖err 0‖ ≤ (B : ℝ) * ‖q - p‖ ^ 2 := by
          simpa only [err, Δ, V, hW₀ p] using
            norm_taylor_on_convex (convex_closedBall _ _) (fun q _ => hY₀.differentiable (by simp) q)
              hJ₀Lip hp hq
        have hrate (u : ℝ) (hu : u ∈ Icc 0 T) :
            ‖dErr u‖ ≤ K * ‖err u‖ + ((L : ℝ) * Q ^ 2) * ‖q - p‖ ^ 2 := by
          have htaylor := norm_taylor_on_convex (convex_closedBall _ _)
            (fun x _ => differentiable_spatialSlice hf hu x) (hGLip u hu)
            (hYmem p hp u hu) (hYmem q hq u hu)
          calc
            ‖dErr u‖ ≤ ‖A u p (err u)‖ + ‖f u (Y u q) - f u (Y u p) - A u p (Δ u)‖ :=
              norm_add_le _ _
            _ ≤ K * ‖err u‖ + (L : ℝ) * (Q * ‖q - p‖) ^ 2 :=
              add_le_add ((A u p).le_of_opNorm_le (hK u hu _ (hYmem p hp u hu)) _)
                (htaylor.trans (mul_le_mul_of_nonneg_left
                  (pow_le_pow_left₀ (norm_nonneg _) (hYlip q p hq hp u hu) 2) L.coe_nonneg))
            _ = _ := by ring
        have h := uniform_gronwall K.coe_nonneg (by positivity) hErrD hinit hrate ht
        rwa [gronwallBound_mul_data] at h
      rw [hasFDerivAt_iff_isLittleO_nhds_zero, isLittleO_iff]
      intro c hc
      have hCont : Continuous (fun h : P => Pbound * ‖h‖) := by fun_prop
      have hsmall : Tendsto (fun h : P => Pbound * ‖h‖) (𝓝 0) (𝓝 0) := by
        simpa only [norm_zero, mul_zero] using hCont.continuousAt (x := (0 : P)).tendsto
      filter_upwards [hsmall (Iio_mem_nhds hc), closedBall_mem_nhds (0 : P) one_pos] with x hx hunit
      have hmem : p + x ∈ S := by simpa [S, dist_eq_norm] using hunit
      have hbound := hErr (p + x) hmem
      rw [add_sub_cancel_left] at hbound
      exact hbound.trans (by
        rw [pow_two, ← mul_assoc]
        exact mul_le_mul_of_nonneg_right (mem_Iio.mp hx).le (norm_nonneg _))
    · let c (t : ℝ) (q : S) := compLeft (A t q)
      let z (t : ℝ) (q : S) := V t q
      have hcLeft (M : E →L[ℝ] E) : ‖compLeft M‖ ≤ ‖M‖ := by
        refine ContinuousLinearMap.opNorm_le_bound (compLeft M) (norm_nonneg M) fun N => ?_
        exact opNorm_comp_le M N
      have hcBound (t : ℝ) (ht : t ∈ Icc 0 T) (q : S) : ‖c t q‖ ≤ (K : ℝ) :=
        (hcLeft (A t q)).trans (hK t ht _ (hYmem q q.property t ht))
      have hcLip (t : ℝ) (ht : t ∈ Icc 0 T) : LipschitzWith (L * Q.toNNReal) (c t) := by
        refine LipschitzWith.of_dist_le_mul fun q r => ?_
        have hgrad : ‖A t q - A t r‖ ≤ (L : ℝ) * ‖Y t q - Y t r‖ := by
          simpa only [dist_eq_norm] using
            (hGLip t ht).dist_le_mul _ (hYmem q q.property t ht) _ (hYmem r r.property t ht)
        have hAqr := hgrad.trans
          (mul_le_mul_of_nonneg_left (hYlip q r q.property r.property t ht) L.coe_nonneg)
        have hcdist : dist (c t q) (c t r) = ‖c t q - c t r‖ :=
          dist_eq_norm (c t q) (c t r)
        have hqrdist : dist q r = ‖q.val - r.val‖ := dist_eq_norm q.val r.val
        calc
          dist (c t q) (c t r) = ‖compLeft (A t q - A t r)‖ := by
            rw [hcdist, map_sub]
          _ ≤ ‖A t q - A t r‖ := hcLeft _
          _ ≤ (L : ℝ) * (Q * ‖q.val - r.val‖) := hAqr
          _ = (↑(L * Q.toNNReal) : ℝ) * dist q r := by
            rw [NNReal.coe_mul, Real.coe_toNNReal _ hQ, ← mul_assoc, hqrdist]
      have hinitV : LipschitzWith B (z 0) := by
        have heq : z 0 = S.domRestrict (fderiv ℝ (Y 0)) := funext fun q => hW₀ q
        rw [heq]
        exact lipschitzOnWith_iff_restrict.mp hJ₀Lip
      have hz (q : S) (t : ℝ) (ht : t ∈ Icc 0 T) :
          HasDerivWithinAt (fun s => z s q) (c t q (z t q) + 0) (Icc 0 T) t := by
        rw [add_zero]
        exact hWt q t ht
      obtain ⟨K', hlip, _⟩ := linearODE_parameters_joint_continuous
        (P := S) (A := c) (x := z) (f := fun _ _ => 0) (H := 0)
        hT.le hQ hcBound hcLip (fun _ _ => LipschitzWith.const _) hinitV hz
        (fun t ht q => hVbound q q.property t ht)
      have hLipOn (t : ℝ) (ht : t ∈ Icc 0 T) : LipschitzOnWith K' (V t) S :=
        lipschitzOnWith_iff_restrict.mpr (hlip t ht)
      exact continuousOn_prod_of_continuousOn_lipschitzOnWith' _ K' hLipOn
        (fun p _ => HasDerivWithinAt.continuousOn (hVt p))
  have hD (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) : HasFDerivAt (Y t) (V t p) p := (hLocal p).1 t ht
  have hVjoint : ContinuousOn (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set P)) := by
    rintro ⟨t, p⟩ hp
    have hp' : (t, p) ∈ Icc 0 T ×ˢ closedBall p 1 := ⟨hp.1, mem_closedBall_self zero_le_one⟩
    apply ((hLocal p).2 (t, p) hp').mono_of_mem_nhdsWithin
    have hN : (fun q : ℝ × P => q.2) ⁻¹' closedBall p 1 ∈ 𝓝 (t, p) :=
      continuous_snd.continuousAt (x := (t, p)) (closedBall_mem_nhds p one_pos)
    have hI : (Icc 0 T : Set ℝ) ×ˢ (univ : Set P) ∈ 𝓝[Icc 0 T ×ˢ (univ : Set P)] (t, p) :=
      self_mem_nhdsWithin
    exact mem_of_superset (inter_mem hI (mem_nhdsWithin_of_mem_nhds hN))
      (fun q hq => ⟨hq.1.1, hq.2⟩)
  have heq (t : ℝ) (ht : t ∈ Icc 0 T) (p : P) : fderiv ℝ (Y t) p = V t p := (hD p t ht).fderiv
  dsimp only
  refine ⟨fun t ht p => (hD p t ht).differentiableAt, hVjoint.congr (fun q hq => heq q.1 hq.1 q.2),
    fun p t ht => ?_⟩
  rw [heq t ht p]
  exact (hVt p t ht).congr_of_mem (fun s hs => heq s hs p) ht

end DifferentiatedSystem

set_option maxHeartbeats 600000 in
/-- Every spatial jet of the trajectory is jointly continuous and solves
the time equation obtained by taking the same spatial jet of the right-hand side.
Induction uses the ordinary differential equation on the pair of a trajectory
and its spatial derivative. -/
theorem trajectoryFamily_spatialJets (n : ℕ) {P E : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {f : ℝ → E → E} {Y : ℝ → P → E} {T : ℝ} (hT : 0 < T)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set E)))
    (hYc : ContinuousOn (Function.uncurry Y) (Icc 0 T ×ˢ (univ : Set P)))
    (hYt : ∀ p t, t ∈ Icc 0 T →
      HasDerivWithinAt (fun s => Y s p) (f t (Y t p)) (Icc 0 T) t)
    (hY₀ : ContDiff ℝ ∞ (Y 0)) :
    (∀ t ∈ Icc 0 T, ContDiff ℝ n (Y t)) ∧
    ContinuousOn (fun q : ℝ × P => iteratedFDeriv ℝ n (Y q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set P)) ∧
    ContinuousOn (fun q : ℝ × P => iteratedFDeriv ℝ n (f q.1 ∘ Y q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set P)) ∧
    ∀ p t, t ∈ Icc 0 T → HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (Y s) p)
      (iteratedFDeriv ℝ n (f t ∘ Y t) p) (Icc 0 T) t := by
  induction n generalizing E with
  | zero =>
      let c := (continuousMultilinearCurryFin0 ℝ P E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      refine ⟨fun t ht => ?_, ?_, ?_, fun p t ht => ?_⟩
      · rw [Nat.cast_zero, contDiff_zero]
        exact continuousOn_univ.mp (hYc.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun p _ => ⟨ht, mem_univ p⟩))
      · simp only [iteratedFDeriv_zero_eq_comp]
        exact c.continuous.comp_continuousOn hYc
      · have hcomp : ContinuousOn (fun q : ℝ × P => f q.1 (Y q.1 q.2))
            (Icc 0 T ×ˢ (univ : Set P)) :=
          hf.continuousOn.comp (continuous_fst.continuousOn.prodMk hYc)
            (fun q hq => ⟨hq.1, mem_univ (Y q.1 q.2)⟩)
        simp only [iteratedFDeriv_zero_eq_comp]
        exact c.continuous.comp_continuousOn hcomp
      · simp only [iteratedFDeriv_zero_eq_comp, Function.comp_apply]
        exact c.hasFDerivAt.comp_hasDerivWithinAt t (hYt p t ht)
  | succ n ih =>
      obtain ⟨hDiff, hJc, hJt⟩ := trajectoryFamily_spatialDerivative hT hf hYc hYt hY₀
      let D := P →L[ℝ] E
      let W (t : ℝ) (p : P) : E × D := (Y t p, fderiv ℝ (Y t) p)
      let g (t : ℝ) (e : E × D) : E × D :=
        (f t e.1, (fderiv ℝ (f t) e.1).comp e.2)
      let pi (q : ℝ × (E × D)) := (q.1, q.2.1)
      have hpi : ContDiffOn ℝ ∞ pi (Icc 0 T ×ˢ (univ : Set (E × D))) := by
        unfold pi
        fun_prop
      have hMaps : MapsTo pi (Icc 0 T ×ˢ (univ : Set (E × D))) (Icc 0 T ×ˢ (univ : Set E)) :=
        fun q hq => ⟨hq.1, mem_univ (pi q).2⟩
      have hg : ContDiffOn ℝ ∞ (Function.uncurry g) (Icc 0 T ×ˢ (univ : Set (E × D))) := by
        have hgrad := (contDiffOn_spatialFDeriv hT hf).comp hpi hMaps
        have hJ : ContDiffOn ℝ ∞ (fun q : ℝ × (E × D) => q.2.2)
            (Icc 0 T ×ˢ (univ : Set (E × D))) := by fun_prop
        exact (hf.comp hpi hMaps).prodMk (hgrad.clm_comp hJ)
      have hWc : ContinuousOn (Function.uncurry W) (Icc 0 T ×ˢ (univ : Set P)) :=
        hYc.prodMk hJc
      have hWt (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
          HasDerivWithinAt (fun s => W s p) (g t (W t p)) (Icc 0 T) t :=
        (hYt p t ht).prodMk (hJt p t ht)
      have hW₀ : ContDiff ℝ ∞ (W 0) := hY₀.prodMk (contDiff_infty_iff_fderiv.mp hY₀).2
      obtain ⟨hW, hJets, hRJets, hEq⟩ := ih hg hWc hWt hW₀
      let sndD := ContinuousLinearMap.snd ℝ E D
      let toJet := (continuousMultilinearCurryRightEquiv' ℝ n P E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      let projectJet := (ContinuousLinearMap.compContinuousMultilinearMapL ℝ
        (fun _ : Fin n => P) (E × D) D) sndD
      let recoverJet := toJet.comp projectJet
      have hProject (h : P → E × D) (hh : ContDiff ℝ n h) (p : P) :
          projectJet (iteratedFDeriv ℝ n h p) = iteratedFDeriv ℝ n (sndD ∘ h) p := by
        rw [sndD.iteratedFDeriv_comp_left hh.contDiffAt le_rfl]
        rfl
      have hYjet (s : ℝ) (hs : s ∈ Icc 0 T) (p : P) :
          recoverJet (iteratedFDeriv ℝ n (W s) p) = iteratedFDeriv ℝ (n + 1) (Y s) p := by
        change toJet (projectJet (iteratedFDeriv ℝ n (W s) p)) = _
        rw [hProject (W s) (hW s hs), iteratedFDeriv_succ_eq_comp_right]
        rfl
      have hRjet (s : ℝ) (hs : s ∈ Icc 0 T) (p : P) :
          recoverJet (iteratedFDeriv ℝ n (g s ∘ W s) p) =
            iteratedFDeriv ℝ (n + 1) (f s ∘ Y s) p := by
        have hR : ContDiff ℝ n (g s ∘ W s) :=
          ((contDiff_spatialSlice hg hs).of_le (by simp)).comp (hW s hs)
        have hderiv : sndD ∘ g s ∘ W s = fderiv ℝ (f s ∘ Y s) := by
          funext p
          exact (((differentiable_spatialSlice hf hs _).hasFDerivAt.comp p
            (hDiff s hs p).hasFDerivAt).fderiv).symm
        change toJet (projectJet (iteratedFDeriv ℝ n (g s ∘ W s) p)) = _
        rw [hProject (g s ∘ W s) hR, hderiv,
          iteratedFDeriv_succ_eq_comp_right]
        rfl
      refine ⟨fun t ht => ?_, ?_, ?_, fun p t ht => ?_⟩
      · rw [Nat.cast_succ]
        apply contDiff_succ_iff_fderiv.mpr
        exact ⟨hDiff t ht, by simp, sndD.contDiff.comp (hW t ht)⟩
      · exact (recoverJet.continuous.comp_continuousOn hJets).congr
          (fun q hq => (hYjet q.1 hq.1 q.2).symm)
      · exact (recoverJet.continuous.comp_continuousOn hRJets).congr
          (fun q hq => (hRjet q.1 hq.1 q.2).symm)
      · have hd : HasDerivWithinAt (fun s => recoverJet (iteratedFDeriv ℝ n (W s) p))
            (recoverJet (iteratedFDeriv ℝ n (g t ∘ W t) p)) (Icc 0 T) t :=
          hasDerivWithinAt_linearImage
            (A := ContinuousMultilinearMap ℝ (fun _ : Fin n => P) (E × D))
            (B := ContinuousMultilinearMap ℝ (fun _ : Fin (n + 1) => P) E)
            recoverJet (hEq p t ht)
        rw [hRjet t ht p] at hd
        exact hd.congr_of_mem (fun s hs => (hYjet s hs p).symm) ht

/-- A smooth periodic velocity supplies actual smooth spatial flow slices and
the differentiated trajectory equation at every finite order. -/
theorem IsLabelFlowOn.labelJets_evolve {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (n : ℕ)
    (hT : 0 < T) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) :
    (∀ t ∈ Icc 0 T, ContDiff ℝ n (X 0 t)) ∧
    ContinuousOn (fun q : ℝ × Vec3 => iteratedFDeriv ℝ n (X 0 q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    ContinuousOn (fun q : ℝ × Vec3 => iteratedFDeriv ℝ n (U q.1 ∘ X 0 q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
    ∀ a t, t ∈ Icc 0 T → HasDerivWithinAt (fun s => iteratedFDeriv ℝ n (X 0 s) a)
      (iteratedFDeriv ℝ n (U t ∘ X 0 t) a) (Icc 0 T) t := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hinitial : X 0 0 = id := funext fun a => hX.initial 0 h₀ a
  exact trajectoryFamily_spatialJets n hT hU (hX.continuousOn_time_label hK h₀)
    (fun a => hX.trajectory 0 h₀ a) (hinitial.symm ▸ contDiff_id)

/-- Positive spatial derivatives of the lifted transition are periodic. -/
theorem IsLabelFlowOn.iteratedFDeriv_add_latticeVector
    {U : Velocity} {X : ℝ → Velocity} {l r : ℝ} {K : ℝ≥0}
    (hX : IsLabelFlowOn U X (Icc l r))
    (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u))
    (hper : ∀ u ∈ Icc l r, SpatiallyPeriodic (U u))
    {s t : ℝ} (hs : s ∈ Icc l r) (ht : t ∈ Icc l r)
    {n : ℕ} (hn : 1 ≤ n) (p : Fin 3 → ℤ) (x : Vec3) :
    iteratedFDeriv ℝ n (X s t) (x + latticeVector p) =
      iteratedFDeriv ℝ n (X s t) x := by
  rw [← iteratedFDeriv_comp_add_right n (latticeVector p) x]
  rw [show (fun y => X s t (y + latticeVector p)) = (fun y => X s t y + latticeVector p) from
    funext (hX.add_latticeVector hLip hper hs ht p)]
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = k + 1 := by omega
  rw [hn']
  have hEq : fderiv ℝ (fun y => X s t y + latticeVector p) = fderiv ℝ (X s t) :=
    funext fun _ => fderiv_add_const _
  simp only [iteratedFDeriv_succ_eq_comp_right, hEq]

/-- Joint continuity of a positive-order jet and periodicity of the velocity
give a uniform bound on the lifted slab. -/
theorem IsLabelFlowOn.exists_bound_iteratedFDeriv
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 1 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ u ∈ Icc 0 T, SpatiallyPeriodic (U u))
    {n : ℕ} (hn : 1 ≤ n)
    (hJet : ContinuousOn (fun q : ℝ × Vec3 => iteratedFDeriv ℝ n (X 0 q.1) q.2)
      (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ∃ B : ℝ, ∀ t ∈ Icc 0 T, ∀ a, ‖iteratedFDeriv ℝ n (X 0 t) a‖ ≤ B := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  obtain ⟨K, hLip⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT hU hper
  let f (q : ℝ × Vec3) := iteratedFDeriv ℝ n (X 0 q.1) q.2
  have hS : IsCompact (Icc (0 : ℝ) T ×ˢ centeredCell) := isCompact_Icc.prod isCompact_centeredCell
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn (f := f)
    (hJet.mono (prod_subset_prod_right (subset_univ centeredCell)))
  refine ⟨B, fun t ht a => ?_⟩
  obtain ⟨p, hp⟩ := exists_sub_latticeVector_mem_centeredCell a
  have hshift := hX.iteratedFDeriv_add_latticeVector hLip hper h₀ ht hn p
    (a - latticeVector p)
  rw [sub_add_cancel] at hshift
  rw [hshift]
  exact hB (t, a - latticeVector p) ⟨ht, hp⟩
private def flowJetSinglePartition (n : ℕ) (hn : 0 < n) : OrderedFinpartition n where
  length := 1
  partSize _ := n
  partSize_pos _ := hn
  emb _ := id
  emb_strictMono _ := strictMono_id
  parts_strictMono := Subsingleton.strictMono _
  disjoint i _ j _ hij := (hij (Subsingleton.elim i j)).elim
  cover i := ⟨0, i, rfl⟩

private theorem flowJetPartition_eq_single {n : ℕ} (hn : 0 < n) (c : OrderedFinpartition n)
    (hc : c.length = 1) : c = flowJetSinglePartition n hn := by
  have hsum : ∑ i, c.partSize i = n := by
    simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
  rcases c with ⟨length, partSize, partSize_pos, emb, emb_strictMono, parts_strictMono,
    disjoint, cover⟩
  change length = 1 at hc
  subst length
  change (∑ i : Fin 1, partSize i) = n at hsum
  have hsize : partSize = fun _ => n := by
    funext i
    rw [Subsingleton.elim i (0 : Fin 1)]
    simpa only [Fin.sum_univ_one] using hsum
  subst partSize
  have hemb : emb = fun _ => id := funext fun i => (emb_strictMono i).eq_id
  subst emb
  rfl

section SpatialJets

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem flowJet_single_term {f : F → G} {g : E → F} {x : E} {n : ℕ} (hn : 0 < n) :
    (ftaylorSeries ℝ f (g x)).compAlongOrderedFinpartition (ftaylorSeries ℝ g x)
        (flowJetSinglePartition n hn) =
      (fderiv ℝ f (g x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n g x) := by
  ext v : 1
  simp [flowJetSinglePartition, ftaylorSeries, OrderedFinpartition.applyOrderedFinpartition_apply]

/-- The Faà di Bruno expansion with its one-block term removed. -/
theorem iteratedFDeriv_comp_sub_linear_eq_sum {f : F → G} {g : E → F} {x : E} {n : ℕ}
    (hn : 0 < n) (hf : ContDiffAt ℝ n f (g x)) (hg : ContDiffAt ℝ n g x) :
    iteratedFDeriv ℝ n (f ∘ g) x -
      (fderiv ℝ f (g x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n g x) =
      ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length),
        (ftaylorSeries ℝ f (g x)).compAlongOrderedFinpartition (ftaylorSeries ℝ g x) c := by
  classical
  let nontrivialPart (c : OrderedFinpartition n) := 2 ≤ c.length
  have hfilter : Finset.univ.filter (fun c : OrderedFinpartition n => ¬nontrivialPart c) =
      {flowJetSinglePartition n hn} := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro hc
      apply flowJetPartition_eq_single hn c
      have h₁ := c.length_pos hn
      dsimp only [nontrivialPart] at hc
      omega
    · rintro rfl
      simp [nontrivialPart, flowJetSinglePartition]
  change _ = ∑ c ∈ Finset.univ.filter nontrivialPart, _
  rw [iteratedFDeriv_comp hf hg le_rfl, FormalMultilinearSeries.taylorComp,
    ← Finset.sum_filter_add_sum_filter_not _ nontrivialPart, hfilter,
    Finset.sum_singleton, flowJet_single_term hn, add_sub_cancel_right]

/-- The forcing in the higher variational equation is bounded by the
Faà di Bruno terms with at least two positive blocks. -/
theorem norm_iteratedFDeriv_comp_sub_linear_le {f : F → G} {g : E → F} {x : E} {n : ℕ}
    (hn : 0 < n) (hf : ContDiffAt ℝ n f (g x)) (hg : ContDiffAt ℝ n g x) :
    ‖iteratedFDeriv ℝ n (f ∘ g) x -
      (fderiv ℝ f (g x)).compContinuousMultilinearMap (iteratedFDeriv ℝ n g x)‖ ≤
      ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length),
        ‖iteratedFDeriv ℝ c.length f (g x)‖ * ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) g x‖ := by
  rw [iteratedFDeriv_comp_sub_linear_eq_sum hn hf hg]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ =>
    c.norm_compAlongOrderedFinpartition_le _ _)

/-- The identity transition has zero spatial jets at orders at least two. -/
theorem iteratedFDeriv_id_eq_zero_of_two_le {n : ℕ} (hn : 2 ≤ n) (x : E) :
    iteratedFDeriv ℝ n (id : E → E) x = 0 := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hn
  have hn' : n = (k + 1) + 1 := by omega
  have hD : fderiv ℝ (id : E → E) = fun _ => ContinuousLinearMap.id ℝ E :=
    funext fun _ => fderiv_id
  apply norm_eq_zero.mp
  rw [hn', ← norm_iteratedFDeriv_fderiv, hD, iteratedFDeriv_succ_const]
  simp

end SpatialJets
private theorem sum_partSize {n : ℕ} (c : OrderedFinpartition n) :
    ∑ i, c.partSize i = n := by
  simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))

/-- A term in the higher flow recursion, including the `D ^ 2` propagator
bound, costs at most `D ^ (5 * n - 4)` when the partition has at least two
positive blocks. -/
theorem flowJet_partitionPower_le {D : ℝ} (hD : 1 ≤ D) {n : ℕ}
    (c : OrderedFinpartition n) (hc : 2 ≤ c.length) :
    D ^ 2 * D ^ c.length * (∏ i, D ^ (5 * c.partSize i - 4)) ≤ D ^ (5 * n - 4) := by
  have hs : (∑ i, (5 * c.partSize i - 4)) + 4 * c.length = 5 * n := by
    calc
      _ = ∑ i, ((5 * c.partSize i - 4) + 4) := by
        rw [Finset.sum_add_distrib]
        simp [mul_comm]
      _ = ∑ i, 5 * c.partSize i := by
        apply Finset.sum_congr rfl
        intro i _
        have hi := c.partSize_pos i
        omega
      _ = 5 * n := by rw [← Finset.mul_sum, sum_partSize c]
  rw [Finset.prod_pow_eq_pow_sum, ← pow_add, ← pow_add]
  exact pow_le_pow_right₀ hD (by omega)

/-- The constants in the scalar flow recurrence of Proposition 5.1 are
uniform over the parent scale and every sequence satisfying the recurrence.
The sum is over ordered partitions with at least two blocks. -/
theorem flowJet_recursion_le {R : ℕ → ℝ} {C₁ : ℝ}
    (hR : ∀ n, 0 ≤ R n) (hC₁ : 0 ≤ C₁) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ D : ℝ, 1 ≤ D → ∀ v : ℕ → ℝ, (∀ n, 0 ≤ v n) → v 1 ≤ C₁ * D →
        (∀ n ≥ 2, v n ≤ R n * D ^ 2 *
          ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length),
            D ^ c.length * ∏ i, v (c.partSize i)) →
        ∀ n ≥ 1, v n ≤ C n * D ^ (5 * n - 4) := by
  classical
  let admissible (D : ℝ) (v : ℕ → ℝ) :=
    (∀ n, 0 ≤ v n) ∧ v 1 ≤ C₁ * D ∧
      ∀ n ≥ 2, v n ≤ R n * D ^ 2 *
        ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length),
          D ^ c.length * ∏ i, v (c.partSize i)
  have hAll (n : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
      ∀ D : ℝ, 1 ≤ D → ∀ v : ℕ → ℝ, admissible D v → 1 ≤ n →
        v n ≤ B * D ^ (5 * n - 4) := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      by_cases hn₀ : n = 0
      · subst n
        exact ⟨0, le_rfl, fun _ _ _ _ hn => by omega⟩
      by_cases hn₁ : n = 1
      · subst n
        exact ⟨C₁, hC₁, fun _ _ _ hv _ => by simpa using hv.2.1⟩
      have hn : 2 ≤ n := by omega
      have hPrior (m : ℕ) : ∃ B : ℝ, 0 ≤ B ∧
          (m < n → ∀ D : ℝ, 1 ≤ D → ∀ v : ℕ → ℝ, admissible D v → 1 ≤ m →
            v m ≤ B * D ^ (5 * m - 4)) := by
        by_cases hm : m < n
        · obtain ⟨B, hB, hbound⟩ := ih m hm
          exact ⟨B, hB, fun _ => hbound⟩
        · exact ⟨0, le_rfl, fun h => (hm h).elim⟩
      choose prior hprior₀ hprior using hPrior
      let S := Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length)
      let B := R n * ∑ c ∈ S, ∏ i, prior (c.partSize i)
      refine ⟨B, mul_nonneg (hR n) (Finset.sum_nonneg fun _ _ => Finset.prod_nonneg
        fun _ _ => hprior₀ _), fun D hD v hv _ => ?_⟩
      have hD₀ : 0 ≤ D := zero_le_one.trans hD
      have hterm (c : OrderedFinpartition n) (hc : c ∈ S) :
          D ^ 2 * (D ^ c.length * ∏ i, v (c.partSize i)) ≤
            (∏ i, prior (c.partSize i)) * D ^ (5 * n - 4) := by
        have hlen : 2 ≤ c.length := (Finset.mem_filter.mp hc).2
        have hblocks (i : Fin c.length) : c.partSize i < n := by
          obtain ⟨j, hj⟩ := @exists_ne (Fin c.length) (Fin.nontrivial_iff_two_le.mpr hlen) i
          calc
            c.partSize i < ∑ u, c.partSize u :=
              Finset.single_lt_sum hj (Finset.mem_univ _) (Finset.mem_univ _)
                (c.partSize_pos j) (fun _ _ _ => Nat.zero_le _)
            _ = n := sum_partSize c
        have hproduct : (∏ i, v (c.partSize i)) ≤
            ∏ i, prior (c.partSize i) * D ^ (5 * c.partSize i - 4) := by
          apply Finset.prod_le_prod
          · intro i _
            exact hv.1 _
          · intro i _
            exact hprior _ (hblocks i) D hD v hv (c.partSize_pos i)
        calc
          _ ≤ D ^ 2 * (D ^ c.length *
                ∏ i, prior (c.partSize i) * D ^ (5 * c.partSize i - 4)) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hproduct (pow_nonneg hD₀ _)) (pow_nonneg hD₀ _)
          _ = (∏ i, prior (c.partSize i)) *
                (D ^ 2 * D ^ c.length * ∏ i, D ^ (5 * c.partSize i - 4)) := by
            rw [Finset.prod_mul_distrib]
            ring
          _ ≤ _ := mul_le_mul_of_nonneg_left (flowJet_partitionPower_le hD c hlen)
            (Finset.prod_nonneg fun _ _ => hprior₀ _)
      calc
        v n ≤ R n * D ^ 2 * ∑ c ∈ S, D ^ c.length * ∏ i, v (c.partSize i) :=
          hv.2.2 n hn
        _ = R n * ∑ c ∈ S, D ^ 2 * (D ^ c.length * ∏ i, v (c.partSize i)) := by
          rw [mul_assoc, Finset.mul_sum]
        _ ≤ R n * ∑ c ∈ S, (∏ i, prior (c.partSize i)) * D ^ (5 * n - 4) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun c hc => hterm c hc) (hR n)
        _ = B * D ^ (5 * n - 4) := by rw [← Finset.sum_mul, mul_assoc]
  choose C hC hbound using hAll
  exact ⟨C, hC, fun D hD v hv hbase hrec n hn => hbound n D hD v ⟨hv, hbase, hrec⟩ hn⟩

set_option maxHeartbeats 500000 in
/-- The variational propagator bound acts on a multilinear spatial jet by
acting on its value at each tuple of directions. -/
theorem IsLabelFlowOn.norm_multilinear_forcedVariation_le
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s)) (a : Vec3)
    {n : ℕ} {z N : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec3) Vec3}
    {D C t : ℝ}
    (hM : ContinuousOn (fun s => fderiv ℝ (U s) (X 0 s a)) (Icc 0 T))
    (hN : ContinuousOn N (Icc 0 T))
    (hNbound : ∀ s ∈ Icc 0 T, ‖N s‖ ≤ C)
    (hF : ∀ s ∈ Icc 0 T, ‖fderiv ℝ (X 0 s) a‖ ≤ D)
    (hG : ∀ s ∈ Icc 0 T, ‖fderiv ℝ (X s 0) (X 0 s a)‖ ≤ D)
    (hz₀ : z 0 = 0)
    (hz : ∀ s ∈ Icc 0 T, HasDerivWithinAt z
      ((fderiv ℝ (U s) (X 0 s a)).compContinuousMultilinearMap (z s) + N s) (Icc 0 T) s)
    (ht : t ∈ Icc 0 T) :
    ‖z t‖ ≤ D ^ 2 * C := by
  have hC : 0 ≤ C := (norm_nonneg _).trans (hNbound t ht)
  refine ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (sq_nonneg D) hC) fun m => ?_
  let eval := ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Vec3) Vec3 m
  have hEvalN : ContinuousOn (fun s => N s m) (Icc 0 T) :=
    eval.continuous.comp_continuousOn hN
  have hEvalz : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun u => z u m)
      ((fderiv ℝ (U s) (X 0 s a)) (z s m) + N s m) (Icc 0 T) s := by
    intro s hs
    simpa only [eval, Function.comp_def, ContinuousMultilinearMap.apply_apply,
      _root_.add_apply, ContinuousLinearMap.compContinuousMultilinearMap_coe] using
      eval.hasFDerivAt.comp_hasDerivWithinAt s (hz s hs)
  have hEvalz₀ : z 0 m = 0 := by simp [hz₀]
  have hsub : Icc (0 : ℝ) t ⊆ Icc 0 T := Icc_subset_Icc_right ht.2
  have hInt : IntervalIntegrable (fun s => D ^ 2 * ‖N s m‖) volume 0 t :=
    (continuousOn_const.mul (hEvalN.mono hsub).norm).intervalIntegrable_of_Icc ht.1
  let B := (D ^ 2 * C) * ∏ i, ‖m i‖
  have hP : 0 ≤ ∏ i, ‖m i‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg (sq_nonneg D) hC) hP
  have hforced : ‖z t m‖ ≤ ∫ s in (0 : ℝ)..t, D ^ 2 * ‖N s m‖ :=
    hX.norm_forcedVariation_le hT hU hper a (z := fun s => z s m) (N := fun s => N s m)
      (D := D) (t := t) hM hEvalN hF hG hEvalz₀ hEvalz ht
  have hpoint (s : ℝ) (hs : s ∈ Icc (0 : ℝ) t) : D ^ 2 * ‖N s m‖ ≤ B := by
    have hnm : ‖N s m‖ ≤ ‖N s‖ * ∏ i, ‖m i‖ := (N s).le_opNorm m
    have hmn : ‖N s‖ * (∏ i, ‖m i‖) ≤ C * (∏ i, ‖m i‖) :=
      mul_le_mul_of_nonneg_right (hNbound s (hsub hs)) hP
    calc
      D ^ 2 * ‖N s m‖ ≤ D ^ 2 * (C * ∏ i, ‖m i‖) :=
        mul_le_mul_of_nonneg_left (hnm.trans hmn) (sq_nonneg _)
      _ = B := (mul_assoc _ _ _).symm
  have hIntegral : (∫ s in (0 : ℝ)..t, D ^ 2 * ‖N s m‖) ≤ ∫ _ in (0 : ℝ)..t, B :=
    intervalIntegral.integral_mono_on ht.1 hInt intervalIntegrable_const hpoint
  have hConst : (∫ _ in (0 : ℝ)..t, B) = t * B := by
    simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hTime : t * B ≤ B := mul_le_of_le_one_left hB (ht.2.trans hT₁)
  exact hforced.trans (hIntegral.trans (hConst.trans_le hTime))

set_option maxHeartbeats 500000 in
/-- The differentiated trajectory equation and the lower-order jet bounds
give the pointwise estimate behind the parent-flow recurrence (5.9). -/
theorem IsLabelFlowOn.norm_iteratedFDeriv_le_flowRecursion
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} (hT : 0 < T) (hT₁ : T ≤ 1)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s)) (a : Vec3)
    {n : ℕ} (hn : 2 ≤ n) {D C t : ℝ} {v : ℕ → ℝ}
    (hD : 0 ≤ D) (hC : 0 ≤ C)
    (hM : ContinuousOn (fun s => fderiv ℝ (U s) (X 0 s a)) (Icc 0 T))
    (hRHS : ContinuousOn (fun s => iteratedFDeriv ℝ n (U s ∘ X 0 s) a) (Icc 0 T))
    (hF : ∀ s ∈ Icc 0 T, ‖fderiv ℝ (X 0 s) a‖ ≤ D)
    (hG : ∀ s ∈ Icc 0 T, ‖fderiv ℝ (X s 0) (X 0 s a)‖ ≤ D)
    (hUs : ∀ s ∈ Icc 0 T, ContDiffAt ℝ n (U s) (X 0 s a))
    (hXs : ∀ s ∈ Icc 0 T, ContDiffAt ℝ n (X 0 s) a)
    (hUjet : ∀ k, 2 ≤ k → k ≤ n →
      ∀ s ∈ Icc 0 T, ‖iteratedFDeriv ℝ k (U s) (X 0 s a)‖ ≤ C * D ^ k)
    (hXjet : ∀ k, 1 ≤ k → k < n →
      ∀ s ∈ Icc 0 T, ‖iteratedFDeriv ℝ k (X 0 s) a‖ ≤ v k)
    (hODE : ∀ s ∈ Icc 0 T, HasDerivWithinAt (fun u => iteratedFDeriv ℝ n (X 0 u) a)
      (iteratedFDeriv ℝ n (U s ∘ X 0 s) a) (Icc 0 T) s)
    (ht : t ∈ Icc 0 T) :
    ‖iteratedFDeriv ℝ n (X 0 t) a‖ ≤ C * D ^ 2 *
      ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length),
        D ^ c.length * ∏ i, v (c.partSize i) := by
  classical
  let z (s : ℝ) := iteratedFDeriv ℝ n (X 0 s) a
  let N (s : ℝ) := iteratedFDeriv ℝ n (U s ∘ X 0 s) a -
    (fderiv ℝ (U s) (X 0 s a)).compContinuousMultilinearMap (z s)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hX₀ : X 0 0 = id := funext (hX.initial 0 h₀)
  have hz₀ : z 0 = 0 := by
    dsimp only [z]
    rw [hX₀]
    exact iteratedFDeriv_id_eq_zero_of_two_le hn a
  let comp := ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin n => Vec3) Vec3 Vec3
  have hComp : ContinuousOn (fun s => comp (fderiv ℝ (U s) (X 0 s a))) (Icc 0 T) :=
    comp.continuous.comp_continuousOn hM
  have hzcont : ContinuousOn z (Icc 0 T) := HasDerivWithinAt.continuousOn hODE
  have hNcont : ContinuousOn N (Icc 0 T) := hRHS.sub (hComp.clm_apply hzcont)
  have hz : ∀ s ∈ Icc 0 T, HasDerivWithinAt z
      ((fderiv ℝ (U s) (X 0 s a)).compContinuousMultilinearMap (z s) + N s) (Icc 0 T) s := by
    intro s hs
    refine (hODE s hs).congr_deriv ?_
    dsimp only [N]
    abel
  let S := Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length)
  let B := ∑ c ∈ S, D ^ c.length * ∏ i, v (c.partSize i)
  have hNbound (s : ℝ) (hs : s ∈ Icc 0 T) : ‖N s‖ ≤ C * B := by
    have hTerm (c : OrderedFinpartition n) (hc : c ∈ S) :
        ‖iteratedFDeriv ℝ c.length (U s) (X 0 s a)‖ *
            ∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (X 0 s) a‖ ≤
          C * (D ^ c.length * ∏ i, v (c.partSize i)) := by
      have hlen : 2 ≤ c.length := (Finset.mem_filter.mp hc).2
      have hsum : ∑ i, c.partSize i = n := by
        simpa using c.sum_sigma_eq_sum (fun _ => (1 : ℕ))
      have hi (i : Fin c.length) : c.partSize i < n := by
        obtain ⟨j, hj⟩ := @exists_ne (Fin c.length) (Fin.nontrivial_iff_two_le.mpr hlen) i
        calc
          c.partSize i < ∑ u, c.partSize u :=
            Finset.single_lt_sum hj (Finset.mem_univ _) (Finset.mem_univ _)
              (c.partSize_pos j) (fun _ _ _ => Nat.zero_le _)
          _ = n := hsum
      have hprod : (∏ i, ‖iteratedFDeriv ℝ (c.partSize i) (X 0 s) a‖) ≤
          ∏ i, v (c.partSize i) :=
        Finset.prod_le_prod (fun _ _ => norm_nonneg _)
          (fun i _ => hXjet _ (c.partSize_pos i) (hi i) s hs)
      rw [← mul_assoc]
      exact mul_le_mul (hUjet _ hlen c.length_le s hs) hprod
        (Finset.prod_nonneg fun _ _ => norm_nonneg _) (mul_nonneg hC (pow_nonneg hD _))
    refine (norm_iteratedFDeriv_comp_sub_linear_le (by omega : 0 < n) (hUs s hs) (hXs s hs)).trans ?_
    dsimp only [B]
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum (fun c hc => hTerm c hc)
  have hbound := hX.norm_multilinear_forcedVariation_le hT hT₁ hU hper a hM hNcont
    hNbound hF hG hz₀ hz ht
  change ‖z t‖ ≤ C * D ^ 2 * B
  calc
    _ ≤ D ^ 2 * (C * B) := hbound
    _ = _ := by ring

/-- Given the parent gradient and inverse Jacobian bounds, Proposition 5.1
supplies all forward label-flow jets with constants independent of the parent
and of the scale. The supplied derivative bound for the velocity uses the
single constant `R n` through order `n`. -/
theorem exists_forward_flowJetBounds (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n ≥ 2, ∀ k, 2 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
        ∀ n ≥ 1, ∀ t ∈ Icc 0 T, ∀ a,
          ‖iteratedFDeriv ℝ n (X 0 t) a‖ ≤ C n * D ^ (5 * n - 4) := by
  obtain ⟨C, hC, hbound⟩ := flowJet_recursion_le hR (zero_le_one : (0 : ℝ) ≤ 1)
  refine ⟨C, hC, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUjet
  have hU₁ : ContDiffOn ℝ 1 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  let values (n : ℕ) : Set ℝ :=
    {x | ∃ t ∈ Icc 0 T, ∃ a, x = ‖iteratedFDeriv ℝ n (X 0 t) a‖}
  let v (n : ℕ) := if 1 ≤ n then sSup (values n) else 0
  have hne (n : ℕ) : (values n).Nonempty := ⟨_, 0, h₀, (0 : Vec3), rfl⟩
  have hBdd (n : ℕ) (hn : 1 ≤ n) : BddAbove (values n) := by
    obtain ⟨B, hB⟩ := hX.exists_bound_iteratedFDeriv hT hU₁ hper hn
      (hX.labelJets_evolve n hT hU hper).2.1
    exact ⟨B, by rintro _ ⟨s, hs, a, rfl⟩; exact hB s hs a⟩
  have hJetLe (n : ℕ) (hn : 1 ≤ n) (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
      ‖iteratedFDeriv ℝ n (X 0 t) a‖ ≤ v n := by
    rw [show v n = sSup (values n) from ite_eq_left hn]
    exact le_csSup (hBdd n hn) ⟨t, ht, a, rfl⟩
  have hv (n : ℕ) : 0 ≤ v n := by
    by_cases hn : 1 ≤ n
    · exact (norm_nonneg _).trans (hJetLe n hn 0 h₀ 0)
    · simp [v, hn]
  have hbase : v 1 ≤ 1 * D := by
    rw [show v 1 = sSup (values 1) from ite_eq_left le_rfl, one_mul]
    refine csSup_le (hne 1) ?_
    rintro _ ⟨t, ht, a, rfl⟩
    rw [← norm_iteratedFDeriv_fderiv (n := 0), norm_iteratedFDeriv_zero]
    exact hF t ht a
  have hRec (n : ℕ) (hn : 2 ≤ n) :
      v n ≤ R n * D ^ 2 *
        ∑ c ∈ Finset.univ.filter (fun c : OrderedFinpartition n => 2 ≤ c.length),
          D ^ c.length * ∏ i, v (c.partSize i) := by
    rw [show v n = sSup (values n) from ite_eq_left (by omega)]
    refine csSup_le (hne n) ?_
    rintro _ ⟨t, ht, a, rfl⟩
    obtain ⟨hFlow, _, hRhsJets, hFlowODE⟩ := hX.labelJets_evolve n hT hU hper
    have hM : ContinuousOn (fun s => fderiv ℝ (U s) (X 0 s a)) (Icc 0 T) :=
      (contDiffOn_spatialFDeriv hT hU).continuousOn.comp
        (continuousOn_id.prodMk (HasDerivWithinAt.continuousOn (hX.trajectory 0 h₀ a)))
        (fun s hs => ⟨hs, mem_univ (X 0 s a)⟩)
    have hRhs : ContinuousOn (fun s => iteratedFDeriv ℝ n (U s ∘ X 0 s) a) (Icc 0 T) :=
      hRhsJets.comp (continuousOn_id.prodMk continuousOn_const)
        (fun s hs => ⟨hs, mem_univ a⟩)
    have hUs (s : ℝ) (hs : s ∈ Icc 0 T) : ContDiffAt ℝ n (U s) (X 0 s a) :=
      ((contDiff_spatialSlice hU hs).of_le (by simp)).contDiffAt
    exact hX.norm_iteratedFDeriv_le_flowRecursion hT hT₁ hU₂ hper a hn (zero_le_one.trans hD)
      (hR n) hM hRhs (fun s hs => hF s hs a) (fun s hs => hG s hs a)
      hUs (fun s hs => (hFlow s hs).contDiffAt)
      (fun k hk hkn s hs => hUjet n hn k hk hkn s hs (X 0 s a))
      (fun k hk _ s hs => hJetLe k hk s hs a) (hFlowODE a) ht
  intro n hn t ht a
  exact (hJetLe n hn t ht a).trans (hbound D hD v hv hbase hRec n hn)

/-- The (n)-th spatial derivative of the forward Jacobian has the exponent
(5n+1) from Proposition 5.1. -/
theorem norm_iteratedFDeriv_labelJacobian_le_of_flowJets
    {Y : Vec3 → Vec3} {a : Vec3} {D : ℝ} {C : ℕ → ℝ} (n : ℕ)
    (h : ‖iteratedFDeriv ℝ (n + 1) Y a‖ ≤ C (n + 1) * D ^ (5 * (n + 1) - 4)) :
    ‖iteratedFDeriv ℝ n (fderiv ℝ Y) a‖ ≤ C (n + 1) * D ^ (5 * n + 1) := by
  rw [norm_iteratedFDeriv_fderiv]
  have he : 5 * (n + 1) - 4 = 5 * n + 1 := by omega
  rwa [he] at h

end TorusEuler
