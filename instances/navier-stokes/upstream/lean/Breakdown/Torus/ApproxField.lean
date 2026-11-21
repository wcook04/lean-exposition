import Breakdown.Torus.StatementsApprox

open MeasureTheory Set Real Filter Topology
open scoped ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace ApproxField.Internal

section UnitIntegral

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]

def sliceFDeriv {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G] (F : ℝ × E → G) (s : ℝ)
    (y : E) : E →L[ℝ] G :=
  (fderiv ℝ F (s, y)).comp (ContinuousLinearMap.inr ℝ ℝ E)

theorem hasFDerivAt_unitIntegral {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (F : ℝ × E → G) (hF : ContDiff ℝ 1 F) (y : E) :
    HasFDerivAt (fun p => ∫ s in (0 : ℝ)..1, F (s, p)) (∫ s in (0 : ℝ)..1, sliceFDeriv F s y) y := by
  have hD : Continuous (fun w : ℝ × E => sliceFDeriv F w.1 w.2) :=
    (hF.continuous_fderiv one_ne_zero).clm_comp continuous_const
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod (isCompact_closedBall y 1)).exists_bound_of_continuousOn
    hD.continuousOn
  have hsl : ∀ p : E, Continuous (fun s : ℝ => F (s, p)) := fun p =>
    hF.continuous.comp (continuous_id.prodMk continuous_const)
  have hsl' : Continuous (fun s : ℝ => sliceFDeriv F s y) :=
    hD.comp (continuous_id.prodMk continuous_const)
  refine intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (bound := fun _ => C)
    (F' := fun p s => sliceFDeriv F s p) (Metric.ball_mem_nhds y one_pos)
    (Eventually.of_forall fun p => (hsl p).aestronglyMeasurable)
    ((hsl y).intervalIntegrable 0 1) hsl'.aestronglyMeasurable ?_ intervalIntegrable_const ?_
  · refine Eventually.of_forall fun s hs p hp => hC (s, p) ⟨?_, Metric.ball_subset_closedBall hp⟩
    rw [uIoc_of_le zero_le_one] at hs
    exact Ioc_subset_Icc_self hs
  · exact Eventually.of_forall fun s _ p _ =>
      ((hF.differentiable one_ne_zero) (s, p)).hasFDerivAt.comp p (hasFDerivAt_prodMk_right s p)

theorem contDiff_unitIntegral_nat (n : ℕ) : ∀ {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (F : ℝ × E → G), ContDiff ℝ ∞ F →
      ContDiff ℝ n (fun p => ∫ s in (0 : ℝ)..1, F (s, p)) := by
  induction n with
  | zero =>
    intro G _ _ _ F hF
    exact contDiff_zero.2 (continuous_iff_continuousAt.2 fun p =>
      (hasFDerivAt_unitIntegral F (hF.of_le (by simp)) p).continuousAt)
  | succ n ih =>
    intro G _ _ _ F hF
    have h1 : ContDiff ℝ 1 F := hF.of_le (by simp)
    have hfd : fderiv ℝ (fun p => ∫ s in (0 : ℝ)..1, F (s, p)) =
        fun p => ∫ s in (0 : ℝ)..1, sliceFDeriv F s p :=
      funext fun p => (hasFDerivAt_unitIntegral F h1 p).fderiv
    rw [Nat.cast_succ]
    refine contDiff_succ_iff_fderiv.2
      ⟨fun p => (hasFDerivAt_unitIntegral F h1 p).differentiableAt, by simp, ?_⟩
    rw [hfd]
    exact ih (fun w => sliceFDeriv F w.1 w.2)
      ((contDiff_infty_iff_fderiv.1 hF).2.clm_comp contDiff_const)

theorem contDiff_unitIntegral {G : Type} [NormedAddCommGroup G] [NormedSpace ℝ G]
    [CompleteSpace G] (F : ℝ × E → G) (hF : ContDiff ℝ ∞ F) :
    ContDiff ℝ ∞ (fun p => ∫ s in (0 : ℝ)..1, F (s, p)) :=
  contDiff_infty.2 fun n => contDiff_unitIntegral_nat n F hF

end UnitIntegral

theorem contDiff_cross_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {u v : X → Space}
    (hu : ContDiff ℝ ∞ u) (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (fun y => cross (u y) (v y)) := by
  have hc : ∀ w : X → Space, ContDiff ℝ ∞ w → ∀ i, ContDiff ℝ ∞ (fun y => w y i) :=
    fun w hw i => (contDiff_piLp 2).1 hw i
  refine (contDiff_piLp 2).2 fun i => ?_
  fin_cases i
  · exact ((hc u hu 1).mul (hc v hv 2)).sub ((hc u hu 2).mul (hc v hv 1))
  · exact ((hc u hu 2).mul (hc v hv 0)).sub ((hc u hu 0).mul (hc v hv 2))
  · exact ((hc u hu 0).mul (hc v hv 1)).sub ((hc u hu 1).mul (hc v hv 0))

theorem cross_zero_left (b : Space) : cross 0 b = 0 := by
  simp [cross]

def timeClamp (a δ t : ℝ) : ℝ := t - (t - a) * smoothTransition ((t - a) / δ)

theorem contDiff_timeClamp (a δ : ℝ) : ContDiff ℝ ∞ (timeClamp a δ) := by
  unfold timeClamp
  have h1 : ContDiff ℝ ∞ (fun t : ℝ => t - a) := contDiff_id.sub contDiff_const
  exact contDiff_id.sub (h1.mul ((smoothTransition.contDiff (n := ⊤)).comp (h1.div_const δ)))

theorem timeClamp_of_le {a δ t : ℝ} (hδ : 0 < δ) (h : t ≤ a) : timeClamp a δ t = t := by
  have : (t - a) / δ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le
  simp [timeClamp, smoothTransition.zero_of_nonpos this]

theorem timeClamp_le {a δ : ℝ} (hδ : 0 < δ) (t : ℝ) : timeClamp a δ t ≤ a + δ := by
  unfold timeClamp
  rcases le_or_gt t (a + δ) with h | h
  · have : 0 ≤ (t - a) * smoothTransition ((t - a) / δ) := by
      rcases le_or_gt t a with h' | h'
      · rw [smoothTransition.zero_of_nonpos (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ.le)]
        simp
      · exact mul_nonneg (by linarith) (smoothTransition.nonneg _)
    linarith
  · have : 1 ≤ (t - a) / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [smoothTransition.one_of_one_le this]
    linarith

theorem contDiffOn_of_clamped {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] (T : ℝ)
    (f : ℝ → Space → X)
    (h : ∀ ψ : ℝ → ℝ, ContDiff ℝ ∞ ψ → (∀ t, ψ t < T) →
      ContDiff ℝ ∞ (fun z : ℝ × Space => f (ψ z.1) z.2)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Iio T ×ˢ univ) := by
  intro z hz
  have hz1 : z.1 < T := hz.1
  set δ := (T - z.1) / 3 with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hψ : ∀ t, timeClamp (z.1 + δ) δ t < T := fun t => by
    have := timeClamp_le (a := z.1 + δ) hδ t
    rw [hδdef] at this ⊢
    linarith
  have hG := h _ (contDiff_timeClamp (z.1 + δ) δ) hψ
  refine (hG.contDiffAt.congr_of_eventuallyEq ?_).contDiffWithinAt
  have hmem : Iio (z.1 + δ) ×ˢ (univ : Set Space) ∈ 𝓝 z :=
    (isOpen_Iio.prod isOpen_univ).mem_nhds ⟨show z.1 < z.1 + δ by linarith, mem_univ _⟩
  filter_upwards [hmem] with w hw
  rw [timeClamp_of_le hδ (le_of_lt hw.1)]

theorem contDiff_centralCut : ContDiff ℝ ∞ centralCut := centralBump.contDiff

theorem contDiff_gradient_centralCut : ContDiff ℝ ∞ (gradientAt centralCut) := by
  have hd : ContDiff ℝ ∞ (fderiv ℝ centralCut) := (contDiff_infty_iff_fderiv.1 contDiff_centralCut).2
  unfold gradientAt
  exact ContDiff.sum fun i _ => (hd.clm_apply contDiff_const).smul contDiff_const

theorem contDiff_cutoffField_family (g : ℝ × Space → Space) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (fun z : ℝ × Space => cutoffField centralCut center (fun x => g (z.1, x)) z.2) := by
  have hF : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × Space) =>
      w.1 • cross (g (w.2.1, center + w.1 • (w.2.2 - center))) (w.2.2 - center)) := by
    have hd : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × Space) => w.2.2 - center) :=
      (contDiff_snd.comp contDiff_snd).sub contDiff_const
    have harg : ContDiff ℝ ∞ (fun w : ℝ × (ℝ × Space) =>
        ((w.2.1, center + w.1 • (w.2.2 - center)) : ℝ × Space)) :=
      (contDiff_fst.comp contDiff_snd).prodMk (contDiff_const.add (contDiff_fst.smul hd))
    exact contDiff_fst.smul (contDiff_cross_comp (hg.comp harg) hd)
  have hpot : ContDiff ℝ ∞
      (fun z : ℝ × Space => homotopyPotential center (fun x => g (z.1, x)) z.2) :=
    contDiff_unitIntegral _ hF
  unfold cutoffField
  exact ((contDiff_centralCut.comp contDiff_snd).smul hg).add
    (contDiff_cross_comp (contDiff_gradient_centralCut.comp contDiff_snd) hpot)

theorem centralCut_outer {x : Space} (hx : centralRadius / 2 ≤ dist x center) : centralCut x = 0 :=
  centralBump.zero_of_le_dist hx

theorem centralCut_inner {x : Space} (hx : dist x center ≤ centralRadius / 4) : centralCut x = 1 :=
  centralBump.one_of_mem_closedBall (Metric.mem_closedBall.2 hx)

theorem fderiv_centralCut_outer {x : Space} (hx : centralRadius / 2 ≤ dist x center) :
    fderiv ℝ centralCut x = 0 := by
  have h0 : centralCut x = 0 := centralCut_outer hx
  refine IsLocalMin.fderiv_eq_zero (Eventually.of_forall fun y => ?_)
  rw [h0]
  exact centralBump.nonneg

theorem fderiv_centralCut_inner {x : Space} (hx : dist x center ≤ centralRadius / 4) :
    fderiv ℝ centralCut x = 0 := by
  have h1 : centralCut x = 1 := centralCut_inner hx
  refine IsLocalMax.fderiv_eq_zero (Eventually.of_forall fun y => ?_)
  rw [h1]
  exact centralBump.le_one

theorem gradient_eq_zero_of_fderiv {x : Space} (h : fderiv ℝ centralCut x = 0) :
    gradientAt centralCut x = 0 := by
  simp [gradientAt, h]

end ApproxField.Internal

open ApproxField.Internal

theorem approxFieldProperties (hS : SelfSimilarSolves) (_hC : HomotopyCurl)
    (hD : CutoffDivergenceFree) : ApproxFieldProperties := by
  intro W q C T hW hT
  obtain ⟨hSW, hSq, hSdiv⟩ := hS W q C T hW hT
  have hslice : ∀ t < T, ContDiff ℝ ∞ (selfSimilar W T t) := fun t ht =>
    hSW.comp_contDiff (contDiff_const.prodMk contDiff_id) (fun x => ⟨ht, mem_univ x⟩)
  refine ⟨?_, ?_, fun t ht x => ⟨?_, fun hx => ⟨?_, ?_⟩, fun hx => ?_⟩⟩
  · refine contDiffOn_of_clamped T (approxField W T) fun ψ hψ hψT => ?_
    have hg : ContDiff ℝ ∞ (fun z : ℝ × Space => selfSimilar W T (ψ z.1) z.2) :=
      hSW.comp_contDiff ((hψ.comp contDiff_fst).prodMk contDiff_snd)
        (fun z => ⟨hψT z.1, mem_univ _⟩)
    exact contDiff_cutoffField_family (fun z => selfSimilar W T (ψ z.1) z.2) hg
  · have hP : ContDiffOn ℝ ∞ (fun z : ℝ × Space => selfSimilarPressure q T z.1 pressureAnchor)
        (Iio T ×ˢ univ) :=
      hSq.comp (contDiff_fst.prodMk contDiff_const).contDiffOn
        (fun z hz => ⟨hz.1, mem_univ _⟩)
    exact ((contDiff_centralCut.comp contDiff_snd).contDiffOn).mul (hSq.sub hP)
  · exact (hD centralCut center (selfSimilar W T t) contDiff_centralCut (hslice t ht)
      (fun y => (hSdiv t ht y).1)).2 x
  · show centralCut x • selfSimilar W T t x +
        cross (gradientAt centralCut x) (homotopyPotential center (selfSimilar W T t) x) = 0
    rw [gradient_eq_zero_of_fderiv (fderiv_centralCut_outer hx), cross_zero_left,
      centralCut_outer hx]
    simp
  · show centralCut x * _ = 0
    rw [centralCut_outer hx]
    simp
  · show centralCut x • selfSimilar W T t x +
        cross (gradientAt centralCut x) (homotopyPotential center (selfSimilar W T t) x) = _
    rw [gradient_eq_zero_of_fderiv (fderiv_centralCut_inner hx), cross_zero_left,
      centralCut_inner hx]
    simp

end Breakdown.Periodic
