import Breakdown.CertCell.ShapeStatements

open scoped ContDiff Topology
open Set Filter

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

section Generic

variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [NormedAddCommGroup H] [NormedSpace ℝ H]

def GradSlopeOn (s : Set E) (f : E → F) : Prop :=
  ContDiffOn ℝ 1 f s ∧ LocallyLipschitzOn s (fderiv ℝ f)

theorem locSlopeBound_congr {s : Set E} {u v : E → F} (hu : LocallyLipschitzOn s u)
    (h : ∀ y ∈ s, u y = v y) : LocallyLipschitzOn s v := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := hu hx
  refine ⟨K, t ∩ s, inter_mem ht self_mem_nhdsWithin, ?_⟩
  intro a ha b hb
  rw [← h a ha.2, ← h b hb.2]
  exact hK ha.1 hb.1

theorem locSlopeBound_comp {s : Set E} {t : Set F} {g : F → G} {c : E → F} (hg : LocallyLipschitzOn t g)
    (hc : LocallyLipschitzOn s c) (hst : MapsTo c s t) : LocallyLipschitzOn s (fun y => g (c y)) := by
  intro x hx
  obtain ⟨Kg, u, hu, hKg⟩ := hg (hst hx)
  obtain ⟨Kc, w, hw, hKc⟩ := hc hx
  have hT : Tendsto c (𝓝[s] x) (𝓝[t] (c x)) :=
    tendsto_nhdsWithin_iff.2 ⟨hc.continuousOn x hx, eventually_nhdsWithin_of_forall fun y hy => hst hy⟩
  refine ⟨Kg * Kc, w ∩ (s ∩ c ⁻¹' u), inter_mem hw (inter_mem self_mem_nhdsWithin (hT hu)), ?_⟩
  exact hKg.comp (hKc.mono inter_subset_left) (fun y hy => hy.2.2)

theorem locSlopeBound_comp_global {s : Set E} {u : E → F} {φ : F → G} {K : NNReal} (hφ : LipschitzWith K φ)
    (hu : LocallyLipschitzOn s u) : LocallyLipschitzOn s (fun y => φ (u y)) := by
  intro x hx
  obtain ⟨Ku, t, ht, hK⟩ := hu hx
  exact ⟨K * Ku, t, ht, hφ.comp_lipschitzOnWith hK⟩

theorem locSlopeBound_bilin (B : F →L[ℝ] G →L[ℝ] H) {s : Set E} {u : E → F} {v : E → G}
    (hu : LocallyLipschitzOn s u) (hv : LocallyLipschitzOn s v) :
    LocallyLipschitzOn s (fun y => B (u y) (v y)) := by
  intro x hx
  obtain ⟨Ku, tu, htu, hKu⟩ := hu hx
  obtain ⟨Kv, tv, htv, hKv⟩ := hv hx
  have ht : tu ∩ tv ∩ Metric.ball x 1 ∈ 𝓝[s] x :=
    inter_mem (inter_mem htu htv) (mem_nhdsWithin_of_mem_nhds (Metric.ball_mem_nhds x one_pos))
  have hxu : x ∈ tu := mem_of_mem_nhdsWithin hx htu
  have hxv : x ∈ tv := mem_of_mem_nhdsWithin hx htv
  have bu : ∀ y ∈ tu ∩ tv ∩ Metric.ball x 1, ‖u y‖ ≤ ‖u x‖ + Ku := by
    intro y hy
    have h1 := hKu.dist_le_mul y hy.1.1 x hxu
    have h2 : dist y x < 1 := hy.2
    have h3 : ‖u y‖ - ‖u x‖ ≤ dist (u y) (u x) := by rw [dist_eq_norm]; exact norm_sub_norm_le _ _
    have h4 : (Ku : ℝ) * dist y x ≤ Ku := by
      have := Ku.2
      nlinarith [dist_nonneg (x := y) (y := x)]
    linarith
  have bv : ∀ y ∈ tu ∩ tv ∩ Metric.ball x 1, ‖v y‖ ≤ ‖v x‖ + Kv := by
    intro y hy
    have h1 := hKv.dist_le_mul y hy.1.2 x hxv
    have h2 : dist y x < 1 := hy.2
    have h3 : ‖v y‖ - ‖v x‖ ≤ dist (v y) (v x) := by rw [dist_eq_norm]; exact norm_sub_norm_le _ _
    have h4 : (Kv : ℝ) * dist y x ≤ Kv := by
      have := Kv.2
      nlinarith [dist_nonneg (x := y) (y := x)]
    linarith
  refine ⟨‖B‖₊ * (Ku * (‖v x‖₊ + Kv) + (‖u x‖₊ + Ku) * Kv), _, ht, ?_⟩
  apply LipschitzOnWith.of_dist_le_mul
  intro a ha b hb
  have e : B (u a) (v a) - B (u b) (v b) = B (u a - u b) (v a) + B (u b) (v a - v b) := by
    simp only [map_sub, sub_apply]
    abel
  have hua : ‖u a - u b‖ ≤ Ku * dist a b := by
    rw [← dist_eq_norm]; exact hKu.dist_le_mul a ha.1.1 b hb.1.1
  have hva : ‖v a - v b‖ ≤ Kv * dist a b := by
    rw [← dist_eq_norm]; exact hKv.dist_le_mul a ha.1.2 b hb.1.2
  have h1 : ‖B‖ * ‖u a - u b‖ * ‖v a‖ ≤ ‖B‖ * (Ku * dist a b) * (‖v x‖ + Kv) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hua (norm_nonneg _)) (bv a ha) (norm_nonneg _) (by positivity)
  have h2 : ‖B‖ * ‖u b‖ * ‖v a - v b‖ ≤ ‖B‖ * (‖u x‖ + Ku) * (Kv * dist a b) :=
    mul_le_mul (mul_le_mul_of_nonneg_left (bu b hb) (norm_nonneg _)) hva (norm_nonneg _) (by positivity)
  rw [dist_eq_norm (B (u a) (v a)), e]
  calc ‖B (u a - u b) (v a) + B (u b) (v a - v b)‖
      ≤ ‖B (u a - u b) (v a)‖ + ‖B (u b) (v a - v b)‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖u a - u b‖ * ‖v a‖ + ‖B‖ * ‖u b‖ * ‖v a - v b‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ ≤ ‖B‖ * (Ku * dist a b) * (‖v x‖ + Kv) + ‖B‖ * (‖u x‖ + Ku) * (Kv * dist a b) := add_le_add h1 h2
    _ = ((‖B‖₊ * (Ku * (‖v x‖₊ + Kv) + (‖u x‖₊ + Ku) * Kv) : NNReal) : ℝ) * dist a b := by
        push_cast
        ring

theorem locSlopeBound_of_contDiffOn {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ 1 f s) :
    LocallyLipschitzOn s f := by
  intro x hx
  obtain ⟨K, t, ht, hK⟩ := (hf.contDiffAt (hs.mem_nhds hx)).exists_lipschitzOnWith
  exact ⟨K, t, mem_nhdsWithin_of_mem_nhds ht, hK⟩

theorem gradSlope_of_two {s : Set E} (hs : IsOpen s) {f : E → F} (hf : ContDiffOn ℝ 2 f s) :
    GradSlopeOn s f := by
  refine ⟨hf.of_le (by norm_num), ?_⟩
  have h1 : ContDiffOn ℝ 1 (fun y => fderiv ℝ f y) s := hf.fderiv_of_isOpen hs (by norm_num)
  exact locSlopeBound_of_contDiffOn hs h1

theorem gradSlope_congr {s : Set E} (hs : IsOpen s) {f g : E → F} (hf : GradSlopeOn s f)
    (h : ∀ y ∈ s, f y = g y) : GradSlopeOn s g := by
  refine ⟨hf.1.congr fun y hy => (h y hy).symm, locSlopeBound_congr hf.2 fun y hy => ?_⟩
  have : f =ᶠ[𝓝 y] g := Filter.eventuallyEq_of_mem (hs.mem_nhds hy) h
  exact this.fderiv_eq

theorem gradSlope_add {s : Set E} (hs : IsOpen s) {f g : E → F} (hf : GradSlopeOn s f)
    (hg : GradSlopeOn s g) : GradSlopeOn s (fun y => f y + g y) := by
  refine ⟨hf.1.add hg.1, locSlopeBound_congr (hf.2.add hg.2) fun y hy => ?_⟩
  have df := (hf.1.differentiableOn one_ne_zero y hy).differentiableAt (hs.mem_nhds hy)
  have dg := (hg.1.differentiableOn one_ne_zero y hy).differentiableAt (hs.mem_nhds hy)
  exact (fderiv_add df dg).symm

theorem gradSlope_bilin {s : Set E} (hs : IsOpen s) (B : F →L[ℝ] G →L[ℝ] H) {f : E → F} {g : E → G}
    (hf : GradSlopeOn s f) (hg : GradSlopeOn s g) : GradSlopeOn s (fun y => B (f y) (g y)) := by
  refine ⟨(B.contDiff.comp_contDiffOn hf.1).clm_apply hg.1, ?_⟩
  have h1 := locSlopeBound_bilin (B.precompR E) (locSlopeBound_of_contDiffOn hs hf.1) hg.2
  have h2 := locSlopeBound_bilin (B.precompL E) hf.2 (locSlopeBound_of_contDiffOn hs hg.1)
  refine locSlopeBound_congr (h1.add h2) fun y hy => ?_
  have df := (hf.1.differentiableOn one_ne_zero y hy).differentiableAt (hs.mem_nhds hy)
  have dg := (hg.1.differentiableOn one_ne_zero y hy).differentiableAt (hs.mem_nhds hy)
  exact (B.fderiv_of_bilinear df dg).symm

theorem gradSlope_comp {s : Set E} {t : Set F} (hs : IsOpen s) (ht : IsOpen t) {g : F → G} {c : E → F}
    (hg : GradSlopeOn t g) (hc : GradSlopeOn s c) (hst : MapsTo c s t) :
    GradSlopeOn s (fun y => g (c y)) := by
  refine ⟨hg.1.comp hc.1 hst, ?_⟩
  have h1 := locSlopeBound_bilin (ContinuousLinearMap.compL ℝ E F G)
    (locSlopeBound_comp hg.2 (locSlopeBound_of_contDiffOn hs hc.1) hst) hc.2
  refine locSlopeBound_congr h1 fun y hy => ?_
  have dc := (hc.1.differentiableOn one_ne_zero y hy).differentiableAt (hs.mem_nhds hy)
  have dg := (hg.1.differentiableOn one_ne_zero (c y) (hst hy)).differentiableAt (ht.mem_nhds (hst hy))
  rw [show (fun y => g (c y)) = g ∘ c from rfl, fderiv_comp y dg dc]
  rfl

theorem gradSlope_mul {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] {s : Set E} (hs : IsOpen s)
    {f g : E → A} (hf : GradSlopeOn s f) (hg : GradSlopeOn s g) : GradSlopeOn s (fun y => f y * g y) :=
  gradSlope_bilin hs (ContinuousLinearMap.mul ℝ A) hf hg

theorem gradSlope_smul {s : Set E} (hs : IsOpen s) {f : E → ℂ} {g : E → F} [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F] (hf : GradSlopeOn s f) (hg : GradSlopeOn s g) :
    GradSlopeOn s (fun y => f y • g y) :=
  gradSlope_bilin hs (ContinuousLinearMap.lsmul ℝ ℂ) hf hg

theorem gradSlope_neg {s : Set E} (hs : IsOpen s) {f : E → F} (hf : GradSlopeOn s f) :
    GradSlopeOn s (fun y => -f y) := by
  have h := gradSlope_comp hs isOpen_univ
    (gradSlope_of_two isOpen_univ (-ContinuousLinearMap.id ℝ F).contDiff.contDiffOn) hf (mapsTo_univ _ _)
  simpa using h

theorem gradSlope_const {s : Set E} (hs : IsOpen s) (a : F) : GradSlopeOn s (fun _ => a) :=
  gradSlope_of_two hs contDiffOn_const

theorem gradSlope_ofReal {s : Set E} (hs : IsOpen s) {f : E → ℝ} (hf : GradSlopeOn s f) :
    GradSlopeOn s (fun y => (f y : ℂ)) :=
  gradSlope_comp hs isOpen_univ (gradSlope_of_two isOpen_univ Complex.ofRealCLM.contDiff.contDiffOn) hf
    (mapsTo_univ _ _)

theorem gradSlope_slopeBound_of_compact {s K : Set E} {f : E → F} (hf : GradSlopeOn s f) (hK : IsCompact K)
    (hKs : K ⊆ s) : ∃ L : NNReal, LipschitzOnWith L (fderiv ℝ f) K :=
  (hf.2.mono hKs).exists_lipschitzOnWith_of_compact hK

theorem gradSlope_mono {s t : Set E} {f : E → F} (hf : GradSlopeOn t f) (hst : s ⊆ t) : GradSlopeOn s f :=
  ⟨hf.1.mono hst, hf.2.mono hst⟩

end Generic

section Chart

open CellCert.GivenFields (Spline weightPoly radialScale heightDeriv heightRatio radialVec polarVecQ azimVecQ qOf)

def chartBand : Set (ℝ × ℝ) := Prod.fst ⁻¹' Ioo (-1) 1

theorem chartBand_open : IsOpen chartBand := isOpen_Ioo.preimage continuous_fst

def chartPair (P : ShapeParams) (y : Space) : ℝ × ℝ := (chartCoord P y, heightRatio y)

theorem chartCoord_mem (P : ShapeParams) (hL : 0 < P.chartLength) (y : Space) :
    chartCoord P y ∈ Ioo (-1 : ℝ) 1 := by
  have hd : 0 < ‖y‖ + P.chartLength := by positivity
  have h0 : 0 ≤ chartCoord P y := div_nonneg (norm_nonneg _) hd.le
  refine ⟨by linarith, ?_⟩
  show ‖y‖ / (‖y‖ + P.chartLength) < 1
  rw [div_lt_one hd]
  linarith

theorem ratio_cdAt {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ 2 (fun y : Space => y i / ‖y‖) y :=
  ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.contDiffAt).div (contDiffAt_norm ℝ hy) (norm_ne_zero_iff.2 hy)

theorem height_cdAt {y : Space} (hy : y ≠ 0) : ContDiffAt ℝ 2 heightRatio y := ratio_cdAt hy 2

theorem polar_cdAt {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ 2 (fun y => polarVecQ y i) y := by
  have hh := height_cdAt hy
  fin_cases i
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (ratio_cdAt hy 0)
  · simpa [polarVecQ, mul_div_assoc] using hh.mul (ratio_cdAt hy 1)
  · simpa [polarVecQ, qOf] using (contDiffAt_const.sub (hh.pow 2)).neg

theorem azim_cdAt {y : Space} (hy : y ≠ 0) (i : Fin 3) : ContDiffAt ℝ 2 (fun y => azimVecQ y i) y := by
  fin_cases i
  · simpa [azimVecQ, neg_div] using (ratio_cdAt hy 1).neg
  · simpa [azimVecQ] using ratio_cdAt hy 0
  · simpa [azimVecQ] using (contDiffAt_const : ContDiffAt ℝ 2 (fun _ : Space => (0 : ℝ)) y)

theorem vecC_cd {v : Space → Fin 3 → ℝ} (h : ∀ y : Space, y ≠ 0 → ∀ i, ContDiffAt ℝ 2 (fun y => v y i) y) :
    ContDiffOn ℝ 2 (fun y => fun i => ((v y i : ℝ) : ℂ)) {0}ᶜ :=
  contDiffOn_pi.2 fun i y hy => (Complex.ofRealCLM.contDiff.contDiffAt.comp y (h y hy i)).contDiffWithinAt

theorem chartPair_cd (P : ShapeParams) (hL : 0 < P.chartLength) : ContDiffOn ℝ 2 (chartPair P) {0}ᶜ := by
  intro y hy
  have hy' : y ≠ 0 := hy
  have hn : ContDiffAt ℝ 2 (fun y : Space => ‖y‖) y := contDiffAt_norm ℝ hy'
  have hne : ‖y‖ + P.chartLength ≠ 0 := by positivity
  have hT : ContDiffAt ℝ 2 (chartCoord P) y := hn.div (hn.add contDiffAt_const) hne
  exact (hT.prodMk (height_cdAt hy')).contDiffWithinAt

theorem weightPoly_cd (a b : ℕ) {n : WithTop ℕ∞} : ContDiff ℝ n (weightPoly a b) := by
  show ContDiff ℝ n (fun t : ℝ => ((t ^ a * (1 - t) ^ b : ℝ) : ℂ))
  exact Complex.ofRealCLM.contDiff.comp ((contDiff_id.pow a).mul ((contDiff_const.sub contDiff_id).pow b))

theorem phaseSlope_cd (P : ShapeParams) (hP : IsShapeParams P) : ContDiffOn ℝ 2 (phaseSlope P) (Iio 1) := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hdf : ContDiffOn ℝ 2 (deriv P.radialPhase) (Ioi (-δ)) := hf.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hcr : ContDiffOn ℝ 2 (chartRadius P) (Iio 1) := by
    intro t ht
    have hne : 1 - t ≠ 0 := by have : t < 1 := ht; linarith
    exact ((contDiffAt_const.mul contDiffAt_id).div (contDiffAt_const.sub contDiffAt_id) hne).contDiffWithinAt
  have hcr2 : ContDiffOn ℝ 2 (fun t => chartRadius P t ^ 2) (Iio 1) := hcr.pow 2
  have hc : ContDiffOn ℝ 2 (fun t => deriv P.radialPhase (chartRadius P t ^ 2)) (Iio 1) :=
    hdf.comp hcr2 fun t _ => show -δ < chartRadius P t ^ 2 by nlinarith [sq_nonneg (chartRadius P t)]
  exact (contDiffOn_const.mul hcr2).mul hc

theorem keyPhase_cd (P : ShapeParams) (hP : IsShapeParams P) (κ : FieldKey) (σ : ℝ) (h2 : κ.label.1 = 0) :
    ContDiff ℝ 2 (keyPhase P κ σ) := by
  obtain ⟨δ, hδ, hf⟩ := hP.phase.smooth
  have hr : ContDiff ℝ 2 (fun y : Space => P.radialPhase (‖y‖ ^ 2)) := by
    rw [← contDiffOn_univ]
    exact (hf.of_le (by norm_num)).comp (contDiff_norm_sq ℝ).contDiffOn
      fun y _ => show -δ < ‖y‖ ^ 2 by nlinarith [sq_nonneg ‖y‖]
  have hk : ((labelAzimuth P.azimuthOrder κ.label : ℤ) : ℝ) = 0 := by simp [labelAzimuth, h2]
  have he : keyPhase P κ σ = fun y => Complex.exp ((((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
      (κ.phaseIndex : ℝ) * P.radialPhase (‖y‖ ^ 2)) : ℝ) : ℂ) * Complex.I) := by
    funext y
    simp only [keyPhase, hk, zero_mul, add_zero]
  rw [he]
  exact Complex.contDiff_exp.comp
    ((Complex.ofRealCLM.contDiff.comp (contDiff_const.add (contDiff_const.mul hr))).mul contDiff_const)

end Chart

section Amplitude

open CellCert.GivenFields (Spline weightPoly radialScale heightDeriv heightRatio radialVec polarVecQ azimVecQ qOf)

theorem spline_cd (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) : ContDiff ℝ 1 (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) :=
  (hsm a b S hS).of_le (le_min (by exact_mod_cast ha) (by exact_mod_cast hb))

theorem spline_gs (hsm : JoinedSplineSmooth) (hsl : JoinedSplineGradSlopeBound) {a b : ℕ} {S : Spline}
    (hS : IsJoinedSpline a b S) (ha : 1 ≤ a) (hb : 1 ≤ b) (s : Set (ℝ × ℝ)) :
    GradSlopeOn s (fun z : ℝ × ℝ => S.evalHalf z.1 z.2) := by
  refine gradSlope_mono (t := univ) ⟨(spline_cd hsm hS ha hb).contDiffOn, ?_⟩ (subset_univ s)
  intro z _
  obtain ⟨L, hL⟩ := hsl a b S hS ha hb (‖z‖ + 1)
  refine ⟨L, _, mem_nhdsWithin_of_mem_nhds ?_, hL⟩
  exact mem_of_superset (Metric.isOpen_ball.mem_nhds (by simp)) Metric.ball_subset_closedBall

theorem slice_second (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (t x : ℝ) : DifferentiableAt ℝ (fun x' => S.evalHalf t x') x :=
  ((spline_cd hsm hS ha hb).differentiable one_ne_zero (t, x)).comp x
    ((differentiableAt_const t).prodMk differentiableAt_id)

theorem slice_first (hsm : JoinedSplineSmooth) {a b : ℕ} {S : Spline} (hS : IsJoinedSpline a b S) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (t x : ℝ) : DifferentiableAt ℝ (fun t' => S.evalHalf t' x) t :=
  by
    have h := ((spline_cd hsm hS ha hb).differentiable one_ne_zero (t, x)).comp
      (f := fun t' : ℝ => ((t', x) : ℝ × ℝ)) t (differentiableAt_id.prodMk (differentiableAt_const x))
    exact h

theorem originDeriv_gs (g : OriginProfile) (hg : ContDiffOn ℝ 2 g.eval (Iio 1) ∧
    ∀ R : ℝ, R < 1 → ∃ L : NNReal, LipschitzOnWith L (deriv (deriv g.eval)) (Icc (-R) R)) :
    GradSlopeOn (Ioo (-1 : ℝ) 1) (deriv g.eval) := by
  have h1 : ContDiffOn ℝ 1 (deriv g.eval) (Iio 1) := hg.1.deriv_of_isOpen isOpen_Iio (by norm_num)
  refine ⟨h1.mono Ioo_subset_Iio_self, ?_⟩
  have hdd : LocallyLipschitzOn (Ioo (-1 : ℝ) 1) (deriv (deriv g.eval)) := by
    intro t ht
    have h3 : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    have h4 := neg_abs_le t
    have h5 := le_abs_self t
    obtain ⟨L, hL⟩ := hg.2 ((|t| + 1) / 2) (by linarith)
    refine ⟨L, _, mem_nhdsWithin_of_mem_nhds (Icc_mem_nhds ?_ ?_), hL⟩ <;> linarith
  refine locSlopeBound_congr (locSlopeBound_comp_global (ContinuousLinearMap.toSpanSingletonLIE ℝ ℝ).lipschitz hdd) fun t _ => ?_
  simp [toSpanSingleton_deriv]

def compZero (P : ShapeParams) (A : KeyAmp) (z : ℝ × ℝ) : ℂ :=
  -(weightPoly 1 A.highOrder z.1 * ((((-(2 * z.2)) : ℝ) : ℂ) * streamValue P A z.1 z.2 +
      polarFactor z.2 * (A.axisCoef * ((P.origin.eval z.1 : ℝ) : ℂ) + (xDerivSpline A.stream).evalHalf z.1 z.2)))

def compOne (P : ShapeParams) (j : ℤ) (A : KeyAmp) (z : ℝ × ℝ) : ℂ :=
  -((((z.1 * (1 - z.1)) : ℝ) : ℂ) * (deriv (weightPoly 1 A.highOrder) z.1 * streamValue P A z.1 z.2 +
        weightPoly 1 A.highOrder z.1 * (A.axisCoef * ((deriv P.origin.eval z.1 * z.2 : ℝ) : ℂ) +
          (tDerivSpline A.stream).evalHalf z.1 z.2)) +
      Complex.I * ((((j : ℝ) * phaseSlope P z.1) : ℝ) : ℂ) * (weightPoly 1 A.highOrder z.1 * streamValue P A z.1 z.2) +
      2 * (weightPoly 1 A.highOrder z.1 * streamValue P A z.1 z.2))

def compTwo (A : KeyAmp) (z : ℝ × ℝ) : ℂ := weightPoly 1 A.highOrder z.1 * A.swirl.evalHalf z.1 z.2

theorem reduced_zero (hsm : JoinedSplineSmooth) (hder : SplineDerivatives) (P : ShapeParams) (κ : FieldKey)
    (A : KeyAmp) (h2 : κ.label.1 = 0) (hS : IsJoinedSpline 2 2 A.stream) (t x : ℝ) :
    reducedComps P κ A t x 0 = compZero P A (t, x) := by
  have hΨ : HasDerivAt (fun x' => A.stream.evalHalf t x') ((xDerivSpline A.stream).evalHalf t x) x := by
    rw [← ((hder 2 2 A.stream hS).2 (by norm_num)).2 t x]
    exact (slice_second hsm hS (by norm_num) (by norm_num) t x).hasDerivAt
  have h1 : HasDerivAt (fun x' : ℝ => ((P.origin.eval t * x' : ℝ) : ℂ)) ((P.origin.eval t : ℝ) : ℂ) x := by
    simpa using ((hasDerivAt_id x).const_mul (P.origin.eval t)).ofReal_comp
  have hsv : HasDerivAt (fun x' => streamValue P A t x')
      (A.axisCoef * ((P.origin.eval t : ℝ) : ℂ) + (xDerivSpline A.stream).evalHalf t x) x :=
    (h1.const_mul A.axisCoef).add hΨ
  have hq : HasDerivAt (fun x' : ℝ => 1 - x' ^ 2) (-(2 * x)) x := by
    simpa using (hasDerivAt_pow 2 x).const_sub 1
  have hpf : HasDerivAt polarFactor (((-(2 * x)) : ℝ) : ℂ) x := hq.ofReal_comp
  have hprod : HasDerivAt (fun x' => polarFactor x' * streamValue P A t x') _ x := hpf.mul hsv
  simp only [reducedComps, if_pos h2, Matrix.cons_val_zero, heightDeriv, hprod.deriv, compZero]

theorem reduced_one (hsm : JoinedSplineSmooth) (hder : SplineDerivatives) (P : ShapeParams) (κ : FieldKey)
    (A : KeyAmp) (h2 : κ.label.1 = 0) (hS : IsJoinedSpline 2 2 A.stream)
    (hg : ContDiffOn ℝ 2 P.origin.eval (Iio 1)) (t x : ℝ) (ht : t < 1) :
    reducedComps P κ A t x 1 = compOne P κ.phaseIndex A (t, x) := by
  have hΨ : HasDerivAt (fun t' => A.stream.evalHalf t' x) ((tDerivSpline A.stream).evalHalf t x) t := by
    rw [← ((hder 2 2 A.stream hS).1 (by norm_num)).2 t x]
    exact (slice_first hsm hS (by norm_num) (by norm_num) t x).hasDerivAt
  have hgd : HasDerivAt P.origin.eval (deriv P.origin.eval t) t :=
    ((hg.differentiableOn (by norm_num) t ht).differentiableAt (isOpen_Iio.mem_nhds ht)).hasDerivAt
  have hsv : HasDerivAt (fun t' => streamValue P A t' x)
      (A.axisCoef * ((deriv P.origin.eval t * x : ℝ) : ℂ) + (tDerivSpline A.stream).evalHalf t x) t :=
    ((hgd.mul_const x).ofReal_comp.const_mul A.axisCoef).add hΨ
  have hp : HasDerivAt (weightPoly 1 A.highOrder) (deriv (weightPoly 1 A.highOrder) t) t :=
    ((weightPoly_cd 1 A.highOrder (n := 1)).differentiable one_ne_zero t).hasDerivAt
  have hprod : HasDerivAt (fun t' => weightPoly 1 A.highOrder t' * streamValue P A t' x) _ t := hp.mul hsv
  simp only [reducedComps, if_pos h2, Matrix.cons_val_one, Matrix.cons_val_zero, shiftedScale, radialScale,
    hprod.deriv, compOne]

theorem reduced_two (P : ShapeParams) (κ : FieldKey) (A : KeyAmp) (h2 : κ.label.1 = 0) (t x : ℝ) :
    reducedComps P κ A t x 2 = compTwo A (t, x) := by
  simp [reducedComps, h2, compTwo]

end Amplitude

section Assembly

open CellCert.GivenFields (Spline weightPoly radialScale heightDeriv heightRatio radialVec polarVecQ azimVecQ qOf)

def radialC (y : Space) : Fin 3 → ℂ := fun i => ((radialVec y i : ℝ) : ℂ)

def polarC (y : Space) : Fin 3 → ℂ := fun i => ((polarVecQ y i : ℝ) : ℂ)

def azimC (y : Space) : Fin 3 → ℂ := fun i => ((azimVecQ y i : ℝ) : ℂ)

theorem keyVector_eq (hsm : JoinedSplineSmooth) (hder : SplineDerivatives) (P : ShapeParams) (κ : FieldKey)
    (A : KeyAmp) (σ : ℝ) (hL : 0 < P.chartLength) (h2 : κ.label.1 = 0) (hS : IsJoinedSpline 2 2 A.stream)
    (hg : ContDiffOn ℝ 2 P.origin.eval (Iio 1)) :
    keyVector P κ A σ = fun y => keyPhase P κ σ y • (compZero P A (chartPair P y) • radialC y +
      compOne P κ.phaseIndex A (chartPair P y) • polarC y + compTwo A (chartPair P y) • azimC y) := by
  funext y i
  have ht : chartCoord P y < 1 := (chartCoord_mem P hL y).2
  simp only [keyVector, reduced_zero hsm hder P κ A h2 hS, reduced_one hsm hder P κ A h2 hS hg _ _ ht,
    reduced_two P κ A h2, Pi.smul_apply, Pi.add_apply, smul_eq_mul, radialC, polarC, azimC, chartPair]

theorem amplitude_gs (hsm : JoinedSplineSmooth) (hder : SplineDerivatives) (hsl : JoinedSplineGradSlopeBound)
    (P : ShapeParams) (hP : IsShapeParams P) (j : ℤ) (A : KeyAmp) (hS : IsJoinedSpline 2 2 A.stream)
    (hG : IsJoinedSpline 1 1 A.swirl)
    (hg : ContDiffOn ℝ 2 P.origin.eval (Iio 1) ∧
      ∀ R : ℝ, R < 1 → ∃ L : NNReal, LipschitzOnWith L (deriv (deriv P.origin.eval)) (Icc (-R) R)) :
    GradSlopeOn chartBand (compZero P A) ∧ GradSlopeOn chartBand (compOne P j A) ∧
      GradSlopeOn chartBand (compTwo A) := by
  have hV := chartBand_open
  have hfst : MapsTo (fun z : ℝ × ℝ => z.1) chartBand (Ioo (-1) 1) := fun z hz => hz
  have hfst' : MapsTo (fun z : ℝ × ℝ => z.1) chartBand (Iio 1) := fun z hz => (hz : z.1 ∈ Ioo (-1 : ℝ) 1).2
  have smooth : ∀ {f : ℝ × ℝ → ℂ}, ContDiffOn ℝ 2 f chartBand → GradSlopeOn chartBand f :=
    fun h => gradSlope_of_two hV h
  have hw : GradSlopeOn chartBand (fun z : ℝ × ℝ => weightPoly 1 A.highOrder z.1) :=
    smooth ((weightPoly_cd 1 A.highOrder (n := 2)).comp contDiff_fst).contDiffOn
  have hwd : GradSlopeOn chartBand (fun z : ℝ × ℝ => deriv (weightPoly 1 A.highOrder) z.1) := by
    have h : ContDiff ℝ 2 (deriv (weightPoly 1 A.highOrder)) :=
      (contDiff_succ_iff_deriv.1 (weightPoly_cd 1 A.highOrder (n := 2 + 1))).2.2
    exact smooth (h.comp contDiff_fst).contDiffOn
  have hge : ContDiffOn ℝ 2 (fun z : ℝ × ℝ => P.origin.eval z.1) chartBand :=
    hg.1.comp contDiff_fst.contDiffOn hfst'
  have hgeC : ContDiffOn ℝ 2 (fun z : ℝ × ℝ => ((P.origin.eval z.1 : ℝ) : ℂ)) chartBand :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hge
  have hsnd : ContDiff ℝ 2 (fun z : ℝ × ℝ => z.2) := contDiff_snd
  have hΨ := spline_gs hsm hsl hS (by norm_num) (by norm_num) chartBand
  have hΨx := spline_gs hsm hsl ((hder 2 2 A.stream hS).2 (by norm_num)).1 (by norm_num) (by norm_num) chartBand
  have hΨt := spline_gs hsm hsl ((hder 2 2 A.stream hS).1 (by norm_num)).1 (by norm_num) (by norm_num) chartBand
  have hGs := spline_gs hsm hsl hG (by norm_num) (by norm_num) chartBand
  have hαx : GradSlopeOn chartBand (fun z : ℝ × ℝ => A.axisCoef * ((P.origin.eval z.1 * z.2 : ℝ) : ℂ)) :=
    smooth (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn (hge.mul hsnd.contDiffOn)))
  have hsv : GradSlopeOn chartBand (fun z : ℝ × ℝ => streamValue P A z.1 z.2) := gradSlope_add hV hαx hΨ
  have hq : GradSlopeOn chartBand (fun z : ℝ × ℝ => (((-(2 * z.2)) : ℝ) : ℂ)) :=
    smooth (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hsnd).neg).contDiffOn
  have hpf : GradSlopeOn chartBand (fun z : ℝ × ℝ => polarFactor z.2) :=
    smooth (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub (hsnd.pow 2))).contDiffOn
  have hαg : GradSlopeOn chartBand (fun z : ℝ × ℝ => A.axisCoef * ((P.origin.eval z.1 : ℝ) : ℂ)) :=
    smooth (contDiffOn_const.mul hgeC)
  have h0 : GradSlopeOn chartBand (fun z : ℝ × ℝ => -(weightPoly 1 A.highOrder z.1 *
      ((((-(2 * z.2)) : ℝ) : ℂ) * streamValue P A z.1 z.2 + polarFactor z.2 *
        (A.axisCoef * ((P.origin.eval z.1 : ℝ) : ℂ) + (xDerivSpline A.stream).evalHalf z.1 z.2)))) :=
    gradSlope_neg hV (gradSlope_mul hV hw (gradSlope_add hV (gradSlope_mul hV hq hsv)
      (gradSlope_mul hV hpf (gradSlope_add hV hαg hΨx))))
  have hgd : GradSlopeOn chartBand (fun z : ℝ × ℝ => deriv P.origin.eval z.1) :=
    gradSlope_comp hV isOpen_Ioo (originDeriv_gs P.origin hg) (gradSlope_of_two hV contDiff_fst.contDiffOn) hfst
  have hαd : GradSlopeOn chartBand (fun z : ℝ × ℝ => A.axisCoef * ((deriv P.origin.eval z.1 * z.2 : ℝ) : ℂ)) :=
    gradSlope_mul hV (gradSlope_const hV _)
      (gradSlope_ofReal hV (gradSlope_mul hV hgd (gradSlope_of_two hV hsnd.contDiffOn)))
  have htt : GradSlopeOn chartBand (fun z : ℝ × ℝ => (((z.1 * (1 - z.1)) : ℝ) : ℂ)) :=
    smooth (Complex.ofRealCLM.contDiff.comp (contDiff_fst.mul (contDiff_const.sub contDiff_fst))).contDiffOn
  have hps : GradSlopeOn chartBand (fun z : ℝ × ℝ => Complex.I * ((((j : ℝ) * phaseSlope P z.1) : ℝ) : ℂ)) :=
    smooth (contDiffOn_const.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn
      (contDiffOn_const.mul ((phaseSlope_cd P hP).comp contDiff_fst.contDiffOn hfst'))))
  have hws := gradSlope_mul hV hw hsv
  have h1 : GradSlopeOn chartBand (fun z : ℝ × ℝ => -((((z.1 * (1 - z.1)) : ℝ) : ℂ) *
      (deriv (weightPoly 1 A.highOrder) z.1 * streamValue P A z.1 z.2 +
        weightPoly 1 A.highOrder z.1 * (A.axisCoef * ((deriv P.origin.eval z.1 * z.2 : ℝ) : ℂ) +
          (tDerivSpline A.stream).evalHalf z.1 z.2)) +
      Complex.I * ((((j : ℝ) * phaseSlope P z.1) : ℝ) : ℂ) * (weightPoly 1 A.highOrder z.1 * streamValue P A z.1 z.2) +
      2 * (weightPoly 1 A.highOrder z.1 * streamValue P A z.1 z.2))) :=
    gradSlope_neg hV (gradSlope_add hV (gradSlope_add hV
      (gradSlope_mul hV htt (gradSlope_add hV (gradSlope_mul hV hwd hsv)
        (gradSlope_mul hV hw (gradSlope_add hV hαd hΨt))))
      (gradSlope_mul hV hps hws)) (gradSlope_mul hV (gradSlope_const hV _) hws))
  exact ⟨h0, h1, gradSlope_mul hV hw hGs⟩

end Assembly

end Internal

open CellCert.GivenFields (Spline heightRatio radialVec polarVecQ azimVecQ)

open Internal in
theorem typeTwoKey_offOrigin_of (hsm : JoinedSplineSmooth) (hder : SplineDerivatives)
    (hsl : JoinedSplineGradSlopeBound) (hor : OriginProfileSmooth) (P : ShapeParams) (D : TimeFieldData)
    (κ : FieldKey) (σ : ℝ) (hP : IsShapeParams P) (hD : IsTimeFieldData D) (hκ : κ ∈ D.keys)
    (h2 : κ.label.1 = 0) :
    ContDiffOn ℝ 1 (keyVector P κ (D.amp κ) σ) {0}ᶜ ∧ ∀ ρ R : ℝ, 0 < ρ → ∃ L : NNReal,
      LipschitzOnWith L (fderiv ℝ (keyVector P κ (D.amp κ) σ)) {y | ρ ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
  have hU : IsOpen ({0}ᶜ : Set Space) := isOpen_compl_singleton
  have hL := hP.chartLength_pos
  have hS := hD.stream_class κ hκ h2
  have hG := hD.swirl_class κ hκ h2
  have hg := hor P.origin hP.origin
  obtain ⟨h0, h1, h2'⟩ := amplitude_gs hsm hder hsl P hP κ.phaseIndex (D.amp κ) hS hG hg
  have hch : GradSlopeOn {0}ᶜ (chartPair P) := gradSlope_of_two hU (chartPair_cd P hL)
  have hmap : MapsTo (chartPair P) {0}ᶜ chartBand := fun y _ => chartCoord_mem P hL y
  have hfr : ∀ {v : Space → Fin 3 → ℝ}, (∀ y : Space, y ≠ 0 → ∀ i, ContDiffAt ℝ 2 (fun y => v y i) y) →
      GradSlopeOn {0}ᶜ (fun y => fun i => ((v y i : ℝ) : ℂ)) := fun h => gradSlope_of_two hU (vecC_cd h)
  have hR : GradSlopeOn {0}ᶜ radialC := hfr fun y hy i => ratio_cdAt hy i
  have hQ : GradSlopeOn {0}ᶜ polarC := hfr fun y hy i => polar_cdAt hy i
  have hA : GradSlopeOn {0}ᶜ azimC := hfr fun y hy i => azim_cdAt hy i
  have hΦ : GradSlopeOn {0}ᶜ (keyPhase P κ σ) :=
    gradSlope_of_two hU (keyPhase_cd P hP κ σ h2).contDiffOn
  have hall := gradSlope_smul hU hΦ (gradSlope_add hU (gradSlope_add hU
    (gradSlope_smul hU (gradSlope_comp hU chartBand_open h0 hch hmap) hR)
    (gradSlope_smul hU (gradSlope_comp hU chartBand_open h1 hch hmap) hQ))
    (gradSlope_smul hU (gradSlope_comp hU chartBand_open h2' hch hmap) hA))
  rw [keyVector_eq hsm hder P κ (D.amp κ) σ hL h2 hS hg.1]
  refine ⟨hall.1, fun ρ R hρ => gradSlope_slopeBound_of_compact hall ?_ ?_⟩
  · refine (isCompact_closedBall (0 : Space) R).of_isClosed_subset
      ((isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)) ?_
    intro y hy
    exact mem_closedBall_zero_iff.2 hy.2
  · intro y hy h0y
    have h0y' : y = 0 := h0y
    subst h0y'
    have h3 : ρ ≤ ‖(0 : Space)‖ := hy.1
    rw [norm_zero] at h3
    linarith

end GivenShape

end CertCell

end Breakdown
