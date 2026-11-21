import TorusEuler.EndpointSpatialDerivativeHierarchy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.UniformLimitsDeriv

/-! Joint smoothness from finite families of label derivative words on the closed slab. -/

open Asymptotics BoundedContinuousFunction ContinuousLinearMap Filter Set
open scoped ContDiff Topology

namespace TorusEuler

private theorem norm_endpointCoordinateDirection (i : Fin 3) :
    ‖EuclideanSpace.single (𝕜 := ℝ) i 1‖ = 1 := by
  simp [EuclideanSpace.single, PiLp.norm_single]

/-- On the Euclidean lift, continuous basis line derivatives give the full
Fréchet derivative, with the prescribed coordinate columns. -/
theorem hasFDerivAt_of_endpointCoordinateDerivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : Vec3 → E} {d : Fin 3 → Vec3 → E} (x : Vec3)
    (hc : ∀ i, ContinuousAt (d i) x)
    (hline : ∀ (i : Fin 3) (y : Vec3) (s : ℝ),
      HasDerivAt (fun r : ℝ => f (y + r • EuclideanSpace.single i (1 : ℝ)))
        (d i (y + s • EuclideanSpace.single i 1)) s) :
    HasFDerivAt f (∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (d i x)) x := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hε₃ : 0 < ε / 3 := by positivity
  have hnear (i : Fin 3) : ∃ δ > 0, ∀ y, dist y x < δ → dist (d i y) (d i x) < ε / 3 :=
    Metric.continuousAt_iff.mp (hc i) _ hε₃
  choose δ hδ hsmall using hnear
  let ρ := min (δ 0) (min (δ 1) (δ 2))
  have hρ : 0 < ρ := lt_min (hδ 0) (lt_min (hδ 1) (hδ 2))
  have hρle (i : Fin 3) : ρ ≤ δ i := by
    fin_cases i
    · exact min_le_left _ _
    · exact (min_le_right _ _).trans (min_le_left _ _)
    · exact (min_le_right _ _).trans (min_le_right _ _)
  filter_upwards [Metric.ball_mem_nhds x (show 0 < ρ / 4 by positivity)] with y hy
  let v := y - x
  have hv : ‖v‖ < ρ / 4 := by
    simpa only [v, dist_eq_norm] using Metric.mem_ball.mp hy
  let e (i : Fin 3) : Vec3 := EuclideanSpace.single i 1
  let u (i : Fin 3) : Vec3 := v i • e i
  have hcoord (i : Fin 3) : ‖v i‖ ≤ ‖v‖ := PiLp.norm_apply_le v i
  have hu (i : Fin 3) : ‖u i‖ ≤ ‖v‖ := by
    simpa only [u, norm_smul, e, norm_endpointCoordinateDirection, mul_one] using hcoord i
  have hstep (i : Fin 3) (z : Vec3) (hz : ‖z - x‖ ≤ 2 * ‖v‖) :
      ‖f (z + u i) - f z - v i • d i x‖ ≤ ε / 3 * ‖v‖ := by
    let F (s : ℝ) := f (z + s • u i) - s • (v i • d i x)
    have hF (s : ℝ) : HasDerivAt F
        (v i • (d i (z + s • u i) - d i x)) s := by
      have hlin : HasDerivAt (fun r : ℝ => r * v i) (v i) s := by
        simpa only [one_mul, id_eq] using (hasDerivAt_id s).mul_const (v i)
      have h := (hline i z (s * v i)).scomp s hlin
      have hs := h.sub ((hasDerivAt_id s).smul_const (v i • d i x))
      change HasDerivAt
        (fun r : ℝ => f (z + (r * v i) • e i) - r • (v i • d i x))
        (v i • d i (z + (s * v i) • e i) - (1 : ℝ) • (v i • d i x)) s at hs
      simpa only [F, u, smul_smul, smul_sub, one_mul] using hs
    have hFbound (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        ‖v i • (d i (z + s • u i) - d i x)‖ ≤ ε / 3 * ‖v‖ := by
      have hdist : dist (z + s • u i) x < δ i := by
        rw [dist_eq_norm, show z + s • u i - x = (z - x) + s • u i by abel]
        calc
          ‖(z - x) + s • u i‖ ≤ ‖z - x‖ + ‖s • u i‖ := norm_add_le _ _
          _ ≤ 2 * ‖v‖ + ‖v‖ := by
            refine add_le_add hz ?_
            rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hs.1]
            exact (mul_le_mul_of_nonneg_right hs.2 (norm_nonneg _)).trans (by simpa using hu i)
          _ < ρ := by linarith
          _ ≤ δ i := hρle i
      rw [norm_smul, mul_comm]
      exact mul_le_mul (by simpa only [dist_eq_norm] using (hsmall i _ hdist).le)
        (hcoord i) (norm_nonneg _) hε₃.le
    have hmd := (convex_Icc (0 : ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun s _ => (hF s).hasDerivWithinAt) hFbound
      (left_mem_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num))
      (right_mem_Icc.mpr (show (0 : ℝ) ≤ 1 by norm_num))
    simpa only [F, one_smul, zero_smul, add_zero, sub_zero, norm_one, mul_one,
      sub_sub, add_comm] using hmd
  let z1 := x + u 0
  let z2 := z1 + u 1
  have hz1 : ‖z1 - x‖ ≤ 2 * ‖v‖ := by
    change ‖x + u 0 - x‖ ≤ 2 * ‖v‖
    rw [add_sub_cancel_left]
    linarith [hu 0, norm_nonneg v]
  have hz2 : ‖z2 - x‖ ≤ 2 * ‖v‖ := by
    change ‖x + u 0 + u 1 - x‖ ≤ 2 * ‖v‖
    rw [show x + u 0 + u 1 - x = u 0 + u 1 by abel]
    exact (norm_add_le _ _).trans (by linarith [hu 0, hu 1])
  have hy' : z2 + u 2 = y := by
    have heq : u 0 + u 1 + u 2 = v := by
      simpa only [u, e, EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
        Fin.sum_univ_three] using (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v
    change x + u 0 + u 1 + u 2 = y
    rw [add_assoc x, add_assoc x, heq]
    change x + (y - x) = y
    abel
  have hb0 := hstep 0 x (by simp [norm_nonneg v])
  have hb1 := hstep 1 z1 hz1
  have hb2 := hstep 2 z2 hz2
  rw [hy'] at hb2
  have heq : f y - f x - (∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (d i x)) (y - x) =
      (f (x + u 0) - f x - v 0 • d 0 x) +
      (f (z1 + u 1) - f z1 - v 1 • d 1 x) +
      (f y - f z2 - v 2 • d 2 x) := by
    simp only [Fin.sum_univ_three]
    change f y - f x - (v 0 • d 0 x + v 1 • d 1 x + v 2 • d 2 x) =
      (f z1 - f x - v 0 • d 0 x) +
      (f z2 - f z1 - v 1 • d 1 x) +
      (f y - f z2 - v 2 • d 2 x)
    abel
  rw [heq]
  refine (norm_add_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans ?_)
  exact (add_le_add (add_le_add hb0 hb1) hb2).trans
    (le_of_eq (show ε / 3 * ‖v‖ + ε / 3 * ‖v‖ + ε / 3 * ‖v‖ = ε * ‖v‖ by ring))

/-- The spatial derivative of a lifted endpoint field is reconstructed from
its three torus directional derivatives. -/
theorem HalfHolder.hasFDerivAt_lift_of_coordinateDerivatives
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HalfHolder (UnitAddTorus (Fin 3)) E}
    {d : Fin 3 → HalfHolder (UnitAddTorus (Fin 3)) E}
    (hd : ∀ i, endpointTorusHasSpatialDerivative (EuclideanSpace.single i (1 : ℝ)) f (d i))
    (x : Vec3) :
    HasFDerivAt (fun y => HalfHolder.eval (toUnitTorus y) f)
      (∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight
        (HalfHolder.eval (toUnitTorus x) (d i))) x := by
  refine hasFDerivAt_of_endpointCoordinateDerivatives
    (f := fun y => HalfHolder.eval (toUnitTorus y) f)
    (d := fun i y => HalfHolder.eval (toUnitTorus y) (d i)) x
    (fun i => ?_) (fun i y s => ?_)
  · exact ((d i).val.1.continuous.comp lipschitzWith_toUnitTorus.continuous).continuousAt
  · simpa only [toUnitTorus_add] using hd i (toUnitTorus y) s

end TorusEuler

namespace TorusEuler

noncomputable section

local notation "A" => UnitAddTorus (Fin 3)

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private def endpointEvaluateTorusLine (a : A) (u : Vec3) :
    HalfHolder A E →L[ℝ] (ℝ →ᵇ E) :=
  let line : C(ℝ, A) := ⟨fun r => a + toUnitTorus (r • u),
    continuous_const.add (lipschitzWith_toUnitTorus.continuous.comp
      (continuous_id.smul continuous_const))⟩
  (compContinuousCLM E ℝ line).comp
    ((fst ℝ (A →ᵇ E) (DistinctPairs A →ᵇ E)).comp
      (halfHolderSubspace A E).toSubmodule.subtypeL)

private theorem endpointEvaluateTorusLine_apply (a : A) (u : Vec3)
    (f : HalfHolder A E) (s : ℝ) :
    endpointEvaluateTorusLine a u f s = HalfHolder.eval (a + toUnitTorus (s • u)) f :=
  rfl

/-- Within the closed time slab, differentiating a half-Hölder-valued curve
preserves its directional spatial derivative relation. -/
theorem endpointTorusHasSpatialDerivative_of_hasDerivWithinAt_uniform
    {T t : ℝ} (hT : 0 < T) (ht : t ∈ Icc 0 T) (u : Vec3)
    {f df : ℝ → HalfHolder A E} {ft dft : HalfHolder A E}
    (hSpatial : ∀ r ∈ Icc 0 T, endpointTorusHasSpatialDerivative u (f r) (df r))
    (hF : HasDerivWithinAt f ft (Icc 0 T) t)
    (hDF : HasDerivWithinAt df dft (Icc 0 T) t) :
    endpointTorusHasSpatialDerivative u ft dft := by
  classical
  let I := Icc (0 : ℝ) T
  let l := 𝓝[I \ ({t} : Set ℝ)] t
  let Q (g : ℝ → HalfHolder A E) (r : ℝ) := if r ∈ I then slope g t r else 0
  let : NeBot l := accPt_principal_iff_nhdsWithin.mp ((uniqueDiffOn_Icc hT t ht).accPt)
  have hQ {g : ℝ → HalfHolder A E} {dg : HalfHolder A E} (hd : HasDerivWithinAt g dg I t) :
      Tendsto (Q g) l (𝓝 dg) := by
    refine (hasDerivWithinAt_iff_tendsto_slope.mp hd).congr' ?_
    have hmem : ∀ᶠ r in l, r ∈ I \ ({t} : Set ℝ) := self_mem_nhdsWithin
    exact hmem.mono fun r hr => by simp only [Q, hr.1, ite_true]
  intro a s
  let L : HalfHolder A E →L[ℝ] (ℝ →ᵇ E) := endpointEvaluateTorusLine a u
  have huniform {g : ℝ → HalfHolder A E} {dg : HalfHolder A E}
      (hd : HasDerivWithinAt g dg I t) :
      TendstoUniformly (fun r z => L (Q g r) z) (L dg : ℝ → E) l :=
    BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (L.continuous.continuousAt.tendsto.comp (hQ hd))
  change HasDerivAt (L ft : ℝ → E) (L dft s) s
  refine hasDerivAt_of_tendstoUniformly (f := fun r z => L (Q f r) z) (huniform hDF) ?_
    (fun z => (huniform hF).tendsto_at z) s
  have hmem : ∀ᶠ r in l, r ∈ I \ ({t} : Set ℝ) := self_mem_nhdsWithin
  filter_upwards [hmem] with r hr
  intro z
  have h := ((hSpatial r hr.1 a z).sub (hSpatial t ht a z)).const_smul ((r - t)⁻¹ : ℝ)
  simpa only [L, Q, hr.1, ite_true, endpointEvaluateTorusLine_apply, slope, vsub_eq_sub,
    map_smul, map_sub, BoundedContinuousFunction.coe_smul, BoundedContinuousFunction.coe_sub,
    Pi.smul_def, Pi.sub_def] using h

end

end TorusEuler

namespace TorusEuler

noncomputable section

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem endpointWord_hasFDerivWithinAt_eval
    {I : Set ℝ} {J : ℝ → V →ᵇ E} {t : ℝ} {x : V}
    {d : V →ᵇ E} {D : V →L[ℝ] E}
    (ht : HasDerivWithinAt J d I t)
    (hx : HasFDerivAt (fun y => J t y) D x) :
    HasFDerivWithinAt (fun p : ℝ × V => J p.1 p.2)
      (((ContinuousLinearMap.id ℝ ℝ).smulRight (d x)).coprod D) (I ×ˢ univ) (t, x) := by
  rw [hasFDerivWithinAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  let l := 𝓝[I ×ˢ (univ : Set V)] (t, x)
  have h₁ : Tendsto Prod.fst l (𝓝[I] t) := by
    change Tendsto Prod.fst (𝓝[I ×ˢ (univ : Set V)] (t, x)) (𝓝[I] t)
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact tendsto_fst
  have h₂ : Tendsto Prod.snd l (𝓝 x) := by
    change Tendsto Prod.snd (𝓝[I ×ˢ (univ : Set V)] (t, x)) (𝓝 x)
    rw [nhdsWithin_prod_eq, nhdsWithin_univ]
    exact tendsto_snd
  have hδ : 0 < ε / 3 := by positivity
  have hct : Tendsto (fun y => ‖d y - d x‖) (𝓝 x) (𝓝 0) := by
    simpa only [sub_self, norm_zero] using ((d.continuous.continuousAt (x := x)).tendsto.sub
      (tendsto_const_nhds (x := d x))).norm
  filter_upwards [h₁.eventually (isLittleO_iff.mp ht.isLittleO hδ),
    h₂.eventually (isLittleO_iff.mp hx.isLittleO hδ),
    h₂.eventually (hct.eventually (gt_mem_nhds hδ))] with p hp₁ hp₂ hp₃
  let r := J p.1 - J t - (p.1 - t) • d
  have hrem : ‖r p.2‖ ≤ ε / 3 * ‖p.1 - t‖ :=
    (r.norm_coe_le_norm p.2).trans hp₁
  have hcross : ‖(p.1 - t) • (d p.2 - d x)‖ ≤ ε / 3 * ‖p.1 - t‖ := by
    rw [norm_smul, mul_comm]
    exact mul_le_mul_of_nonneg_right hp₃.le (norm_nonneg _)
  have hfst : ‖p.1 - t‖ ≤ ‖p - (t, x)‖ := norm_fst_le (p - (t, x))
  have hsnd : ‖p.2 - x‖ ≤ ‖p - (t, x)‖ := norm_snd_le (p - (t, x))
  calc
    _ = ‖r p.2 + (p.1 - t) • (d p.2 - d x) +
        (J t p.2 - J t x - D (p.2 - x))‖ := by
      rw [coprod_apply]
      simp only [r, BoundedContinuousFunction.coe_sub, BoundedContinuousFunction.coe_smul, Pi.sub_apply,
        ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.id_apply, Prod.fst_sub, Prod.snd_sub, smul_sub]
      abel_nf
    _ ≤ ‖r p.2‖ + ‖(p.1 - t) • (d p.2 - d x)‖ + ‖J t p.2 - J t x - D (p.2 - x)‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ ε / 3 * ‖p.1 - t‖ + ε / 3 * ‖p.1 - t‖ + ε / 3 * ‖p.2 - x‖ :=
      add_le_add (add_le_add hrem hcross) hp₂
    _ ≤ ε / 3 * ‖p - (t, x)‖ + ε / 3 * ‖p - (t, x)‖ + ε / 3 * ‖p - (t, x)‖ :=
      add_le_add (add_le_add (mul_le_mul_of_nonneg_left hfst hδ.le)
        (mul_le_mul_of_nonneg_left hfst hδ.le)) (mul_le_mul_of_nonneg_left hsnd hδ.le)
    _ = _ := by ring

local notation "𝕋" => UnitAddTorus (Fin 3)
local notation "C½" => HalfHolder 𝕋 E

private def endpointWordLift (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :
    HalfHolder 𝕋 E →L[ℝ] Vec3 →ᵇ E :=
  (BoundedContinuousFunction.compContinuousCLM E ℝ
    (⟨toUnitTorus, lipschitzWith_toUnitTorus.continuous⟩ : C(Vec3, 𝕋))).comp
    ((ContinuousLinearMap.fst ℝ (𝕋 →ᵇ E) (DistinctPairs 𝕋 →ᵇ E)).comp
      (halfHolderSubspace 𝕋 E).toSubmodule.subtypeL)

private theorem endpointWordLift_apply (f : C½) (x : Vec3) :
    endpointWordLift E f x = HalfHolder.eval (toUnitTorus x) f := rfl

set_option maxHeartbeats 800000 in
/-- A finite family of directional spatial derivatives with smooth time slices
has the corresponding joint regularity on the closed slab. -/
theorem contDiffOn_endpointWordLift_of_time_and_spatial
    {T : ℝ} (hT : 0 < T) {N n : ℕ} {q : List (Fin 3)} (hq : q.length + n ≤ N)
    (g : List (Fin 3) → ℝ → C½)
    (htime : ∀ p, p.length ≤ N → ContDiffOn ℝ ∞ (g p) (Icc 0 T))
    (hspace : ∀ p, p.length < N → ∀ i t, t ∈ Icc 0 T →
      endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (g p t) (g (i :: p) t)) :
    ContDiffOn ℝ n (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (g q z.1))
      (Icc 0 T ×ˢ univ) := by
  let I := Icc (0 : ℝ) T
  induction n generalizing q g with
  | zero =>
    rw [show (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (g q z.1)) =
      (fun z : ℝ × Vec3 => endpointWordLift E (g q z.1) z.2) from
        funext fun z => (endpointWordLift_apply _ _).symm]
    apply contDiffOn_zero.mpr
    have hG : ContinuousOn (fun z : ℝ × Vec3 => endpointWordLift E (g q z.1))
        (I ×ˢ univ) :=
      (endpointWordLift E).continuous.comp_continuousOn
        ((htime q (by omega)).continuousOn.comp continuous_fst.continuousOn mapsTo_fst_prod)
    exact continuous_eval.comp_continuousOn (hG.prodMk continuous_snd.continuousOn)
  | succ n ih =>
    let dg (p : List (Fin 3)) : ℝ → C½ := derivWithin (g p) I
    have hdiff (p : List (Fin 3)) (hp : p.length ≤ N) (t : ℝ) (ht : t ∈ I) :
        HasDerivWithinAt (g p) (dg p t) I t :=
      ((htime p hp).differentiableOn (by simp) t ht).hasDerivWithinAt
    have hdt (p : List (Fin 3)) (hp : p.length ≤ N) : ContDiffOn ℝ ∞ (dg p) I :=
      (htime p hp).derivWithin (uniqueDiffOn_Icc hT) (by simp)
    have hds (p : List (Fin 3)) (hp : p.length < N) (i : Fin 3) (t : ℝ) (ht : t ∈ I) :
        endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (dg p t) (dg (i :: p) t) :=
      endpointTorusHasSpatialDerivative_of_hasDerivWithinAt_uniform hT ht _
        (fun u hu => hspace p hp i u hu)
        (hdiff p (by omega) t ht) (hdiff (i :: p) (by simp; omega) t ht)
    let U (z : ℝ × Vec3) := HalfHolder.eval (toUnitTorus z.2) (dg q z.1)
    let W (i : Fin 3) (z : ℝ × Vec3) := HalfHolder.eval (toUnitTorus z.2) (g (i :: q) z.1)
    let A : E →L[ℝ] (ℝ × Vec3) →L[ℝ] E :=
      (ContinuousLinearMap.smulRightL ℝ (ℝ × Vec3) E) (fst ℝ ℝ Vec3)
    let B (i : Fin 3) : E →L[ℝ] (ℝ × Vec3) →L[ℝ] E :=
      (ContinuousLinearMap.smulRightL ℝ (ℝ × Vec3) E)
        ((EuclideanSpace.proj (𝕜 := ℝ) i).comp (snd ℝ ℝ Vec3))
    let F (z : ℝ × Vec3) := A (U z) + ∑ i : Fin 3, B i (W i z)
    have hUc : ContDiffOn ℝ n U (I ×ˢ univ) :=
      ih (by omega) dg hdt hds
    have hWc (i : Fin 3) : ContDiffOn ℝ n (W i) (I ×ˢ univ) :=
      ih (q := i :: q) (by simp; omega) g htime hspace
    have hFc : ContDiffOn ℝ n F (I ×ˢ univ) := by
      apply (A.contDiff.comp_contDiffOn hUc).add
      exact ContDiffOn.sum (fun i _ => (B i).contDiff.comp_contDiffOn (hWc i))
    have hF (z : ℝ × Vec3) (hz : z ∈ I ×ˢ univ) :
        HasFDerivWithinAt (fun w : ℝ × Vec3 => HalfHolder.eval (toUnitTorus w.2) (g q w.1))
          (F z) (I ×ˢ univ) z := by
      let J : ℝ → Vec3 →ᵇ E := endpointWordLift E ∘ g q
      let dJ := endpointWordLift E (dg q z.1)
      let dx : Vec3 →L[ℝ] E := ∑ i : Fin 3, (EuclideanSpace.proj (𝕜 := ℝ) i).smulRight (W i z)
      have hj : HasDerivWithinAt J dJ I z.1 :=
        (endpointWordLift E).hasFDerivAt.comp_hasDerivWithinAt z.1
          (hdiff q (by omega) z.1 hz.1)
      have hdx : HasFDerivAt (fun y => J z.1 y) dx z.2 :=
        HalfHolder.hasFDerivAt_lift_of_coordinateDerivatives
          (fun i => hspace q (by omega) i z.1 hz.1) z.2
      have hD := endpointWord_hasFDerivWithinAt_eval hj hdx
      apply hD.congr_fderiv
      apply ContinuousLinearMap.ext
      intro w
      simp only [F, A, B, U, dx, dJ, coprod_apply, _root_.add_apply, _root_.sum_apply,
        ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.smulRightL_apply_apply,
        ContinuousLinearMap.id_apply, ContinuousLinearMap.comp_apply, endpointWordLift_apply]
      rfl
    have hI := (uniqueDiffOn_Icc hT).prod (uniqueDiffOn_univ (𝕜 := ℝ) (E := Vec3))
    rw [Nat.cast_succ]
    exact (contDiffOn_succ_iff_fderivWithin hI).mpr
      ⟨fun p hp => (hF p hp).differentiableWithinAt, by simp,
        hFc.congr fun p hp => (hF p hp).fderivWithin (hI p hp)⟩

/-- A separate finite jet family at each order suffices to recover joint
smoothness of the common zeroth curve. -/
theorem contDiffOn_endpointLift_of_finite_spatialJets
    {T : ℝ} (hT : 0 < T) {f : ℝ → C½}
    (hjets : ∀ n : ℕ, ∃ g : List (Fin 3) → ℝ → C½,
      EqOn (g []) f (Icc 0 T) ∧
      (∀ p, p.length ≤ n → ContDiffOn ℝ ∞ (g p) (Icc 0 T)) ∧
      (∀ p, p.length < n → ∀ i t, t ∈ Icc 0 T →
        endpointTorusHasSpatialDerivative (EuclideanSpace.single i 1) (g p t) (g (i :: p) t))) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => HalfHolder.eval (toUnitTorus z.2) (f z.1))
      (Icc 0 T ×ˢ univ) := by
  apply contDiffOn_infty.mpr
  intro n
  obtain ⟨g, hEq, htime, hspace⟩ := hjets n
  refine (contDiffOn_endpointWordLift_of_time_and_spatial hT (N := n) (q := [])
    (by simp) g htime hspace).congr ?_
  intro z hz
  rw [hEq hz.1]


end
end TorusEuler
