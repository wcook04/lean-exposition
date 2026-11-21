import Breakdown.CellReduction.PotThetaScalar
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeSplineSmooth
import Breakdown.CertCell.ShapeSplineSlope
import Breakdown.CertCell.ShapeJetUnit
import Breakdown.CertCell.ShapeAngularFactor
import Breakdown.FracCell.GivenAuxPinSmoothLocal

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace ScalarOrigin

namespace Internal

section Tame

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def TameNear (f : E → F) (p : E) : Prop :=
  ∃ U ∈ 𝓝 p, (∀ q ∈ U, DifferentiableAt ℝ f q) ∧ ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) U

theorem tameNear_of_contDiffAt {f : E → F} {p : E} (hf : ContDiffAt ℝ 2 f p) : TameNear f p := by
  have h1 : ContDiffAt ℝ 1 (fderiv ℝ f) p := hf.fderiv_right (by norm_num)
  obtain ⟨K, t, ht, hK⟩ := h1.exists_lipschitzOnWith
  have hev : ∀ᶠ q in 𝓝 p, ContDiffAt ℝ 2 f q := hf.eventually (by simp)
  exact ⟨t ∩ {q | ContDiffAt ℝ 2 f q}, inter_mem ht hev,
    fun q hq => (show ContDiffAt ℝ 2 f q from hq.2).differentiableAt (by norm_num), K, hK.mono Set.inter_subset_left⟩

theorem tameNear_congr {f g : E → F} {p : E} (hg : TameNear g p) (he : f =ᶠ[𝓝 p] g) : TameNear f p := by
  obtain ⟨U, hU, hd, K, hK⟩ := hg
  have hW : interior {q | f q = g q} ∈ 𝓝 p := interior_mem_nhds.2 he
  have hloc : ∀ q ∈ interior {q | f q = g q}, f =ᶠ[𝓝 q] g := fun q hq =>
    Filter.mem_of_superset (isOpen_interior.mem_nhds hq) interior_subset
  refine ⟨U ∩ interior {q | f q = g q}, inter_mem hU hW, fun q hq => ?_, K, ?_⟩
  · exact (hd q hq.1).congr_of_eventuallyEq (hloc q hq.2)
  · refine LipschitzOnWith.of_dist_le_mul fun q hq w hw => ?_
    rw [(hloc q hq.2).fderiv_eq, (hloc w hw.2).fderiv_eq]
    exact hK.dist_le_mul q hq.1 w hw.1

theorem tameNear_ball {f : E → F} {p : E} (h : TameNear f p) :
    ∃ r > 0, ∃ A B : ℝ, ∃ K : NNReal, (∀ q ∈ Metric.ball p r, DifferentiableAt ℝ f q) ∧
      (∀ q ∈ Metric.ball p r, ‖f q‖ ≤ A) ∧ (∀ q ∈ Metric.ball p r, ‖fderiv ℝ f q‖ ≤ B) ∧
      LipschitzOnWith (Real.toNNReal B) f (Metric.ball p r) ∧
      LipschitzOnWith K (fderiv ℝ f) (Metric.ball p r) := by
  obtain ⟨U, hU, hd, K, hK⟩ := h
  obtain ⟨r0, hr0, hsub0⟩ := Metric.mem_nhds_iff.1 hU
  set r := min r0 1 with hr
  have hrpos : 0 < r := lt_min hr0 one_pos
  have hsub : Metric.ball p r ⊆ U := (Metric.ball_subset_ball (min_le_left _ _)).trans hsub0
  set B := ‖fderiv ℝ f p‖ + K with hB
  have hb : ∀ q ∈ Metric.ball p r, ‖fderiv ℝ f q‖ ≤ B := by
    intro q hq
    have h1 := hK.dist_le_mul q (hsub hq) p (hsub (Metric.mem_ball_self hrpos))
    rw [dist_eq_norm] at h1
    have h2 : dist q p < 1 := lt_of_lt_of_le hq (min_le_right _ _)
    have h3 : ‖fderiv ℝ f q‖ ≤ ‖fderiv ℝ f p‖ + ‖fderiv ℝ f q - fderiv ℝ f p‖ := by
      have := norm_sub_norm_le (fderiv ℝ f q) (fderiv ℝ f p)
      linarith
    have h4 : (K : ℝ) * dist q p ≤ K := by
      have := K.2
      nlinarith [dist_nonneg (x := q) (y := p)]
    rw [hB]
    linarith
  have hlip : LipschitzOnWith (Real.toNNReal B) f (Metric.ball p r) :=
    (convex_ball p r).lipschitzOnWith_of_nnnorm_fderiv_le (fun q hq => hd q (hsub hq)) (fun q hq => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal']
      exact (hb q hq).trans (le_max_left _ _))
  refine ⟨r, hrpos, ‖f p‖ + B, B, K, fun q hq => hd q (hsub hq), fun q hq => ?_, hb, hlip, hK.mono hsub⟩
  have h1 := hlip.dist_le_mul q hq p (Metric.mem_ball_self hrpos)
  rw [dist_eq_norm] at h1
  have h2 : dist q p < 1 := lt_of_lt_of_le hq (min_le_right _ _)
  have h3 : ‖f q‖ ≤ ‖f p‖ + ‖f q - f p‖ := by
    have := norm_sub_norm_le (f q) (f p)
    linarith
  have h4 : (Real.toNNReal B : ℝ) * dist q p ≤ B := by
    have hB0 : 0 ≤ B := by positivity
    rw [Real.coe_toNNReal _ hB0]
    nlinarith [dist_nonneg (x := q) (y := p)]
  linarith


theorem slope_pair {s : Set E} {a : E → F} {b : E → G} {H : Type*} [NormedAddCommGroup H] (Φ : F → G → H)
    (hΦ : ∀ x x' y y', ‖Φ x y - Φ x' y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖) {A B : ℝ} {La Lb : NNReal}
    (hA : ∀ q ∈ s, ‖a q‖ ≤ A) (hB : ∀ q ∈ s, ‖b q‖ ≤ B) (ha : LipschitzOnWith La a s)
    (hb : LipschitzOnWith Lb b s) : ∃ K : NNReal, LipschitzOnWith K (fun q => Φ (a q) (b q)) s := by
  refine ⟨Real.toNNReal (A * Lb + La * B), LipschitzOnWith.of_dist_le_mul fun q hq w hw => ?_⟩
  have h1 := hb.dist_le_mul q hq w hw
  have h2 := ha.dist_le_mul q hq w hw
  rw [dist_eq_norm] at h1 h2 ⊢
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA q hq)
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB w hw)
  have hd : 0 ≤ dist q w := dist_nonneg
  calc ‖Φ (a q) (b q) - Φ (a w) (b w)‖ ≤ ‖a q‖ * ‖b q - b w‖ + ‖a q - a w‖ * ‖b w‖ := hΦ _ _ _ _
    _ ≤ A * (Lb * dist q w) + (La * dist q w) * B :=
        add_le_add (mul_le_mul (hA q hq) h1 (norm_nonneg _) hA0) (mul_le_mul h2 (hB w hw) (norm_nonneg _)
          (by positivity))
    _ = (A * Lb + La * B) * dist q w := by ring
    _ ≤ (Real.toNNReal (A * Lb + La * B) : ℝ) * dist q w :=
        mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) hd

theorem smul_pair_bound (x x' : ℂ) (y y' : E →L[ℝ] ℂ) :
    ‖x • y - x' • y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖ := by
  have e : x • y - x' • y' = x • (y - y') + (x - x') • y' := by
    rw [smul_sub, sub_smul]
    abel
  rw [e]
  refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
  · exact norm_smul_le _ _
  · exact norm_smul_le _ _

theorem comp_pair_bound (x x' : F →L[ℝ] G) (y y' : E →L[ℝ] F) :
    ‖x.comp y - x'.comp y'‖ ≤ ‖x‖ * ‖y - y'‖ + ‖x - x'‖ * ‖y'‖ := by
  have e : x.comp y - x'.comp y' = x.comp (y - y') + (x - x').comp y' := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
    abel
  rw [e]
  exact (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
    (ContinuousLinearMap.opNorm_comp_le _ _))

theorem tameNear_mul {c d : E → ℂ} {p : E} (hc : TameNear c p) (hd : TameNear d p) :
    TameNear (fun q => c q * d q) p := by
  obtain ⟨r1, hr1, A1, B1, K1, hd1, hA1, hB1, hl1, hK1⟩ := tameNear_ball hc
  obtain ⟨r2, hr2, A2, B2, K2, hd2, hA2, hB2, hl2, hK2⟩ := tameNear_ball hd
  set s := Metric.ball p (min r1 r2) with hs
  have s1 : s ⊆ Metric.ball p r1 := Metric.ball_subset_ball (min_le_left _ _)
  have s2 : s ⊆ Metric.ball p r2 := Metric.ball_subset_ball (min_le_right _ _)
  have hdiff : ∀ q ∈ s, DifferentiableAt ℝ (fun q => c q * d q) q := fun q hq =>
    (hd1 q (s1 hq)).mul (hd2 q (s2 hq))
  have he : ∀ q ∈ s, fderiv ℝ (fun q => c q * d q) q = c q • fderiv ℝ d q + d q • fderiv ℝ c q :=
    fun q hq => fderiv_mul (hd1 q (s1 hq)) (hd2 q (s2 hq))
  obtain ⟨Ka, hKa⟩ := slope_pair (s := s) (fun x y => x • y) smul_pair_bound (fun q hq => hA1 q (s1 hq))
    (fun q hq => hB2 q (s2 hq)) (hl1.mono s1) (hK2.mono s2)
  obtain ⟨Kb, hKb⟩ := slope_pair (s := s) (fun x y => x • y) smul_pair_bound (fun q hq => hA2 q (s2 hq))
    (fun q hq => hB1 q (s1 hq)) (hl2.mono s2) (hK1.mono s1)
  refine ⟨s, Metric.ball_mem_nhds p (lt_min hr1 hr2), hdiff, Ka + Kb, ?_⟩
  have hsum := hKa.add hKb
  refine LipschitzOnWith.of_dist_le_mul fun q hq w hw => ?_
  rw [he q hq, he w hw]
  exact hsum.dist_le_mul q hq w hw

theorem tameNear_comp {g : F → G} {Φ : E → F} {p : E} (hg : TameNear g (Φ p)) (hΦ : TameNear Φ p) :
    TameNear (fun q => g (Φ q)) p := by
  obtain ⟨r1, hr1, A1, B1, K1, hd1, hA1, hB1, hl1, hK1⟩ := tameNear_ball hg
  obtain ⟨r2, hr2, A2, B2, K2, hd2, hA2, hB2, hl2, hK2⟩ := tameNear_ball hΦ
  obtain ⟨r3, hr3, h3⟩ := Metric.continuousAt_iff.1 (hd2 p (Metric.mem_ball_self hr2)).continuousAt r1 hr1
  set s := Metric.ball p (min r2 r3) with hs
  have s2 : s ⊆ Metric.ball p r2 := Metric.ball_subset_ball (min_le_left _ _)
  have hmap : Set.MapsTo Φ s (Metric.ball (Φ p) r1) := fun q hq =>
    h3 (lt_of_lt_of_le hq (min_le_right _ _))
  have hdiff : ∀ q ∈ s, DifferentiableAt ℝ (fun q => g (Φ q)) q := fun q hq =>
    (hd1 (Φ q) (hmap hq)).comp q (hd2 q (s2 hq))
  have he : ∀ q ∈ s, fderiv ℝ (fun q => g (Φ q)) q = (fderiv ℝ g (Φ q)).comp (fderiv ℝ Φ q) :=
    fun q hq => fderiv_comp q (hd1 (Φ q) (hmap hq)) (hd2 q (s2 hq))
  have hgl : LipschitzOnWith (K1 * Real.toNNReal B2) (fun q => fderiv ℝ g (Φ q)) s :=
    hK1.comp (hl2.mono s2) hmap
  obtain ⟨K, hK⟩ := slope_pair (s := s) (fun x y => ContinuousLinearMap.comp x y) comp_pair_bound
    (fun q hq => hB1 (Φ q) (hmap hq)) (fun q hq => hB2 q (s2 hq)) hgl (hK2.mono s2)
  refine ⟨s, Metric.ball_mem_nhds p (lt_min hr2 hr3), hdiff, K, ?_⟩
  refine LipschitzOnWith.of_dist_le_mul fun q hq w hw => ?_
  rw [he q hq, he w hw]
  exact hK.dist_le_mul q hq w hw

theorem tameNear_of_slope {f : E → F} (hd : Differentiable ℝ f)
    (hl : ∀ R : ℝ, ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) (Metric.closedBall 0 R)) (p : E) :
    TameNear f p := by
  obtain ⟨K, hK⟩ := hl (‖p‖ + 1)
  refine ⟨Metric.closedBall 0 (‖p‖ + 1), Metric.closedBall_mem_nhds_of_mem ?_, fun q _ => hd q, K, hK⟩
  rw [Metric.mem_ball, dist_zero_right]
  linarith

end Tame

section Scaling

def scaleMap (s : ℝ) : Space →L[ℝ] ℝ × Space :=
  (0 : Space →L[ℝ] ℝ).prod (s⁻¹ • ContinuousLinearMap.id ℝ Space)

theorem scaleMap_norm (s : ℝ) (hs : 0 < s) : ‖scaleMap s‖ ≤ s⁻¹ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hs.le) (fun v => ?_)
  simp only [scaleMap, ContinuousLinearMap.prod_apply, zero_apply,
    smul_apply, ContinuousLinearMap.id_apply, Prod.norm_def, norm_zero, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.2 hs)]
  exact max_le (by positivity) le_rfl

theorem scaled_deriv {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space → G}
    {F : ℝ × Space → G} {r0 : ℝ}
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → s * ‖v‖ < r0 → f (s • v) = (s ^ 2) • F (s, v))
    {s : ℝ} (hs : 0 < s) {w : Space} (hw : w ≠ 0) (hwr : ‖w‖ < r0)
    (hd : DifferentiableAt ℝ F (s, s⁻¹ • w)) :
    HasFDerivAt f ((s ^ 2) • (fderiv ℝ F (s, s⁻¹ • w)).comp (scaleMap s)) w := by
  have hT : HasFDerivAt (fun w' : Space => ((s, s⁻¹ • w') : ℝ × Space)) (scaleMap s) w :=
    (hasFDerivAt_const s w).prodMk ((hasFDerivAt_id w).const_smul s⁻¹)
  have h1 := (hd.hasFDerivAt.comp w hT).const_smul (s ^ 2)
  refine h1.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_ne.mem_nhds hw, (isOpen_lt continuous_norm continuous_const).mem_nhds hwr]
    with w' hw' hwr'
  have hv : s⁻¹ • w' ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') hw'
  have hn : s * ‖s⁻¹ • w'‖ < r0 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
    exact hwr'
  have e := hscale s hs (s⁻¹ • w') hv hn
  rw [smul_inv_smul₀ hs.ne'] at e
  rw [e]
  rfl

theorem origin_of_scaling {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f : Space → G}
    {F : ℝ × Space → G} {ρ r0 : ℝ} (hρ : 0 < ρ) (hρr : ρ < r0) (hf0 : f 0 = 0)
    (hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → s * ‖v‖ < r0 → f (s • v) = (s ^ 2) • F (s, v))
    (hF : ∀ p ∈ Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)), TameNear F p) :
    HasFDerivAt f (0 : Space →L[ℝ] G) 0 ∧ ∃ C : ℝ, (∀ y ∈ Metric.ball (0 : Space) ρ,
      DifferentiableAt ℝ f y ∧ ‖f y‖ ≤ C * ‖y‖ ^ 2 ∧ ‖fderiv ℝ f y‖ ≤ C * ‖y‖) ∧
      ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ f) (Metric.ball 0 ρ) := by
  set Cs : Set (ℝ × Space) := Set.Icc 0 ρ ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2))
    with hCs
  have hCc : IsCompact Cs := isCompact_Icc.prod ((isCompact_closedBall _ _).diff Metric.isOpen_ball)
  have hdiff : ∀ p ∈ Cs, DifferentiableAt ℝ F p := by
    intro p hp
    obtain ⟨U, hU, hd, -⟩ := hF p hp
    exact hd p (mem_of_mem_nhds hU)
  have hloc : LocallyLipschitzOn Cs (fderiv ℝ F) := by
    intro p hp
    obtain ⟨U, hU, -, K, hK⟩ := hF p hp
    exact ⟨K, U, mem_nhdsWithin_of_mem_nhds hU, hK⟩
  obtain ⟨L, hL⟩ := hloc.exists_lipschitzOnWith_of_compact hCc
  obtain ⟨M, hM⟩ := hCc.exists_bound_of_continuousOn hL.continuousOn
  obtain ⟨N, hN⟩ := hCc.exists_bound_of_continuousOn
    (fun p hp => (hdiff p hp).continuousAt.continuousWithinAt : ContinuousOn F Cs)
  have hpt : ((ρ, EuclideanSpace.single 0 1) : ℝ × Space) ∈ Cs :=
    ⟨⟨hρ.le, le_rfl⟩, by norm_num [mem_closedBall_zero_iff], by norm_num [mem_ball_zero_iff]⟩
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM _ hpt)
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN _ hpt)
  have memC : ∀ s w, 0 < s → s ≤ ρ → s / 2 ≤ ‖w‖ → ‖w‖ ≤ s → ((s, s⁻¹ • w) : ℝ × Space) ∈ Cs := by
    intro s w hs hsρ h1 h2
    have hn : ‖s⁻¹ • w‖ = s⁻¹ * ‖w‖ := by rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
    refine ⟨⟨hs.le, hsρ⟩, ?_, ?_⟩
    · rw [mem_closedBall_zero_iff, hn, inv_mul_le_iff₀ hs]
      linarith
    · rw [mem_ball_zero_iff, hn, not_lt, le_inv_mul_iff₀ hs]
      linarith
  have hrep : ∀ h : Space, h ≠ 0 → ‖h‖ < r0 → f h = (‖h‖ ^ 2) • F (‖h‖, ‖h‖⁻¹ • h) := by
    intro h h0 hr
    have hs : 0 < ‖h‖ := norm_pos_iff.2 h0
    have hv : ‖h‖⁻¹ • h ≠ 0 := smul_ne_zero (inv_ne_zero hs.ne') h0
    have hn : ‖h‖ * ‖‖h‖⁻¹ • h‖ < r0 := by
      rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hs.le), ← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul]
      exact hr
    have e := hscale ‖h‖ hs _ hv hn
    rwa [smul_inv_smul₀ hs.ne'] at e
  have hval : ∀ h : Space, ‖h‖ < ρ → ‖f h‖ ≤ N * ‖h‖ ^ 2 := by
    intro h hh
    by_cases h0 : h = 0
    · simp [h0, hf0]
    have hs : 0 < ‖h‖ := norm_pos_iff.2 h0
    rw [hrep h h0 (hh.trans hρr), norm_smul, norm_pow, norm_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (hN _ (memC _ _ hs hh.le (by linarith) le_rfl)) (by positivity)
  have hd0 : HasFDerivAt f (0 : Space →L[ℝ] G) 0 := by
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    have hbig : (fun h : Space => f (0 + h) - f 0 - (0 : Space →L[ℝ] G) h) =O[𝓝 0] fun h => ‖h‖ ^ 2 := by
      refine Asymptotics.IsBigO.of_bound N ?_
      filter_upwards [Metric.ball_mem_nhds (0 : Space) hρ] with h hh
      rw [mem_ball_zero_iff] at hh
      simp only [zero_add, hf0, sub_zero, zero_apply, norm_pow, norm_norm]
      exact hval h hh
    exact hbig.trans_isLittleO (Asymptotics.isLittleO_norm_pow_id (by norm_num))
  have hat : ∀ s w, 0 < s → s ≤ ρ → s / 2 ≤ ‖w‖ → ‖w‖ ≤ s →
      fderiv ℝ f w = (s ^ 2) • (fderiv ℝ F (s, s⁻¹ • w)).comp (scaleMap s) := by
    intro s w hs hsρ h1 h2
    have hw : w ≠ 0 := by
      rintro rfl
      rw [norm_zero] at h1
      linarith
    exact (scaled_deriv hscale hs hw (by linarith) (hdiff _ (memC s w hs hsρ h1 h2))).fderiv
  have hbound : ∀ w, ‖w‖ < ρ → ‖fderiv ℝ f w‖ ≤ M * ‖w‖ := by
    intro w hw
    by_cases h0 : w = 0
    · rw [h0, hd0.fderiv]
      simp
    have hs : 0 < ‖w‖ := norm_pos_iff.2 h0
    rw [hat ‖w‖ w hs hw.le (by linarith) le_rfl, norm_smul, norm_pow, norm_norm]
    calc ‖w‖ ^ 2 * ‖(fderiv ℝ F (‖w‖, ‖w‖⁻¹ • w)).comp (scaleMap ‖w‖)‖
        ≤ ‖w‖ ^ 2 * (M * ‖w‖⁻¹) := by
          gcongr
          exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
            (mul_le_mul (hM _ (memC _ _ hs hw.le (by linarith) le_rfl)) (scaleMap_norm _ hs)
              (norm_nonneg _) hM0)
      _ = M * ‖w‖ * (‖w‖ * ‖w‖⁻¹) := by ring
      _ = M * ‖w‖ := by rw [mul_inv_cancel₀ hs.ne', mul_one]
  have key : ∀ y z, ‖y‖ < ρ → ‖z‖ ≤ ‖y‖ → ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ (L + 4 * M) * ‖y - z‖ := by
    intro y z hy hzy
    by_cases hfar : ‖y‖ ≤ 2 * ‖y - z‖
    · calc ‖fderiv ℝ f y - fderiv ℝ f z‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ f z‖ := norm_sub_le _ _
        _ ≤ M * ‖y‖ + M * ‖z‖ := add_le_add (hbound y hy) (hbound z (lt_of_le_of_lt hzy hy))
        _ ≤ 4 * M * ‖y - z‖ := by
          nlinarith [mul_le_mul_of_nonneg_left hzy hM0, mul_le_mul_of_nonneg_left hfar hM0]
        _ ≤ (L + 4 * M) * ‖y - z‖ :=
          mul_le_mul_of_nonneg_right (by linarith [NNReal.coe_nonneg L]) (norm_nonneg _)
    · rw [not_le] at hfar
      have hs : 0 < ‖y‖ := by
        have := norm_nonneg (y - z)
        linarith
      have hz1 : ‖y‖ / 2 ≤ ‖z‖ := by
        have := norm_sub_norm_le y z
        linarith
      rw [hat ‖y‖ y hs hy.le (by linarith) le_rfl, hat ‖y‖ z hs hy.le hz1 hzy, ← smul_sub,
        ← ContinuousLinearMap.sub_comp, norm_smul, norm_pow, norm_norm]
      have hyC := memC _ y hs hy.le (by linarith) le_rfl
      have hzC := memC _ z hs hy.le hz1 hzy
      have hLd := hL.dist_le_mul _ hyC _ hzC
      have hdist : dist ((‖y‖, ‖y‖⁻¹ • y) : ℝ × Space) (‖y‖, ‖y‖⁻¹ • z) = ‖y‖⁻¹ * ‖y - z‖ := by
        rw [Prod.dist_eq, dist_self, dist_eq_norm, ← smul_sub, norm_smul,
          Real.norm_of_nonneg (inv_nonneg.2 hs.le)]
        exact max_eq_right (by positivity)
      rw [hdist, dist_eq_norm] at hLd
      calc ‖y‖ ^ 2 * ‖(fderiv ℝ F (‖y‖, ‖y‖⁻¹ • y) - fderiv ℝ F (‖y‖, ‖y‖⁻¹ • z)).comp (scaleMap ‖y‖)‖
          ≤ ‖y‖ ^ 2 * ((L * (‖y‖⁻¹ * ‖y - z‖)) * ‖y‖⁻¹) := by
            gcongr
            exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
              (mul_le_mul hLd (scaleMap_norm _ hs) (norm_nonneg _) (by positivity))
        _ = L * ‖y - z‖ * (‖y‖ * ‖y‖⁻¹) ^ 2 := by ring
        _ = L * ‖y - z‖ := by rw [mul_inv_cancel₀ hs.ne', one_pow, mul_one]
        _ ≤ (L + 4 * M) * ‖y - z‖ := mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  refine ⟨hd0, max N M, fun y hy => ⟨?_, ?_, ?_⟩, Real.toNNReal (L + 4 * M),
    LipschitzOnWith.of_dist_le_mul fun y hy z hz => ?_⟩
  · rw [mem_ball_zero_iff] at hy
    by_cases h0 : y = 0
    · rw [h0]
      exact hd0.differentiableAt
    have hs : 0 < ‖y‖ := norm_pos_iff.2 h0
    exact (scaled_deriv hscale hs h0 (by linarith)
      (hdiff _ (memC _ y hs hy.le (by linarith) le_rfl))).differentiableAt
  · rw [mem_ball_zero_iff] at hy
    exact (hval y hy).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
  · rw [mem_ball_zero_iff] at hy
    exact (hbound y hy).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  · rw [mem_ball_zero_iff] at hy hz
    rw [dist_eq_norm, dist_eq_norm]
    have hc : (L + 4 * M) ≤ (Real.toNNReal (L + 4 * M) : ℝ) := Real.le_coe_toNNReal _
    rcases le_total ‖z‖ ‖y‖ with h | h
    · exact (key y z hy h).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))
    · rw [norm_sub_rev (fderiv ℝ f y), norm_sub_rev y]
      exact (key z y hz h).trans (mul_le_mul_of_nonneg_right hc (norm_nonneg _))

end Scaling

section Jet

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline TensorMesh cellCount cellIndex atSecond xDeriv)

theorem coeff_eq_zero_of_iterate (P : Polynomial ℂ) (o : ℕ)
    (h : (Polynomial.derivative^[o] P).eval (((0 : ℝ) : ℂ)) = 0) : P.coeff o = 0 := by
  have e := Polynomial.coeff_iterate_derivative (k := o) P 0
  rw [Complex.ofReal_zero] at h
  rw [Polynomial.coeff_zero_eq_eval_zero, h, zero_add, Nat.descFactorial_self, nsmul_eq_mul] at e
  exact (mul_eq_zero.1 e.symm).resolve_left (by exact_mod_cast Nat.factorial_ne_zero o)

theorem startAxis_facts (A : JetAxis) (hA : IsJetAxis A 0 1) :
    A.breaks.getD 0 0 = 0 ∧ 0 < A.breaks.getD 1 0 ∧
      ∀ u, u < A.breaks.getD 1 0 → cellIndex A.breaks u = 0 := by
  have hf := hA.first
  have hl := hA.last
  have hs := hA.sorted
  match hb : A.breaks with
  | [] => simp [hb] at hf
  | [a] =>
    rw [hb] at hf hl
    simp at hf hl
    rw [hf] at hl
    norm_num at hl
  | a :: b :: l =>
    rw [hb] at hf hs
    simp only [List.head?_cons, Option.some.injEq] at hf
    subst hf
    have hab : 0 < b := List.rel_of_pairwise_cons hs (by simp)
    have hbl : ∀ c ∈ l, b < c := fun c hc => List.rel_of_pairwise_cons (List.Pairwise.of_cons hs) hc
    refine ⟨rfl, hab, fun u hu => ?_⟩
    have hu' : u < b := hu
    unfold cellIndex
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    have hc' : c ∈ b :: l := List.mem_of_mem_dropLast hc
    have hbc : b ≤ c := by
      rcases List.mem_cons.1 hc' with h | h
      · exact h.ge
      · exact (hbl c h).le
    simp only [decide_eq_true_eq, not_le]
    linarith

theorem interior_bounds (l : List ℝ) (hs : l.Pairwise (· < ·)) {lo hi : ℝ} (hf : l.head? = some lo)
    (hl : l.getLast? = some hi) : ∀ b ∈ (l.drop 1).dropLast, lo < b ∧ b < hi := by
  match l, hs, hf, hl with
  | [], _, hf, _ => simp at hf
  | [a], _, _, _ =>
    intro b hb
    simp at hb
  | a :: c :: l', hs, hf, hl =>
    intro b hb
    simp only [List.head?_cons, Option.some.injEq] at hf
    subst hf
    have hb' : b ∈ (c :: l').dropLast := hb
    have hmem : b ∈ c :: l' := List.mem_of_mem_dropLast hb'
    refine ⟨List.rel_of_pairwise_cons hs hmem, ?_⟩
    have hne : (c :: l') ≠ [] := List.cons_ne_nil _ _
    have hlast : (c :: l').getLast hne = hi := by
      have h1 : (a :: c :: l').getLast? = (c :: l').getLast? := by simp
      rw [h1, List.getLast?_eq_some_getLast hne] at hl
      exact Option.some.inj hl
    have hsp : (c :: l').Pairwise (· < ·) := List.Pairwise.of_cons hs
    rw [← List.dropLast_append_getLast hne, List.pairwise_append] at hsp
    have := hsp.2.2 b hb' ((c :: l').getLast hne) (by simp)
    rwa [hlast] at this

theorem endCells_index (l : List ℝ) (hs : l.Pairwise (· < ·)) (hf : l.head? = some (-1))
    (hl : l.getLast? = some 1) :
    (∀ᶠ x in 𝓝 (1 : ℝ), cellIndex l x = cellCount l - 1) ∧ (∀ᶠ x in 𝓝 (-1 : ℝ), cellIndex l x = 0) := by
  have hI := interior_bounds l hs hf hl
  have hfin : {b | b ∈ (l.drop 1).dropLast}.Finite := List.finite_toSet _
  constructor
  · have hev : ∀ᶠ x in 𝓝 (1 : ℝ), ∀ b ∈ {b | b ∈ (l.drop 1).dropLast}, b ≤ x :=
      (Filter.eventually_all_finite hfin).2 fun b hb => (eventually_gt_nhds (hI b hb).2).mono fun x hx => hx.le
    filter_upwards [hev] with x hx
    unfold cellIndex cellCount
    rw [List.filter_eq_self.2 (fun b hb => by simpa using hx b hb), List.length_dropLast, List.length_drop]
  · have hev : ∀ᶠ x in 𝓝 (-1 : ℝ), ∀ b ∈ {b | b ∈ (l.drop 1).dropLast}, x < b :=
      (Filter.eventually_all_finite hfin).2 fun b hb => eventually_lt_nhds (hI b hb).1
    filter_upwards [hev] with x hx
    unfold cellIndex
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro b hb
    simpa using hx b hb

theorem startPoly_dvd (A : JetAxis) (hA : IsJetAxis A 0 1) {z : ℕ} (hz : z ≤ A.depth) (d : JetDof)
    (hd : ∀ p < z, d ≠ JetDof.node 0 p) : (Polynomial.X : Polynomial ℂ) ^ z ∣ A.dofPoly 0 d := by
  obtain ⟨ha0, hb, -⟩ := startAxis_facts A hA
  have hab : A.breaks.getD 0 0 ≠ A.breaks.getD 1 0 := by
    rw [ha0]
    exact hb.ne
  rw [Polynomial.X_pow_dvd_iff]
  intro o ho
  apply coeff_eq_zero_of_iterate
  have hon : o < A.depth := lt_of_lt_of_le ho hz
  rw [← ha0]
  cases d with
  | node k p =>
    simp only [JetAxis.dofPoly]
    split_ifs with hp hk hk1
    · subst hk
      have hop : o ≠ p := by
        intro h
        subst h
        exact hd _ ho rfl
      exact (iterate_derivative_nodalLeft_eval_left A.depth p o hab hon).trans (if_neg hop)
    · exact iterate_derivative_nodalRight_eval_left A.depth p o hab hon
    · simp
    · simp
  | bubble i s =>
    simp only [JetAxis.dofPoly]
    split_ifs
    · exact iterate_derivative_bubblePoly_eval_left A.depth s o _ _ hon
    · simp

theorem xDeriv_X0_mul (z o : ℕ) (R : MvPolynomial (Fin 2) ℂ) :
    xDeriv o (MvPolynomial.X 0 ^ z * R) = MvPolynomial.X 0 ^ z * xDeriv o R := by
  induction o with
  | zero => rfl
  | succ o ih =>
    simp only [xDeriv] at ih ⊢
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, Derivation.leibniz,
      Derivation.leibniz_pow, MvPolynomial.pderiv_X_of_ne (by decide : (0 : Fin 2) ≠ 1)]
    simp

theorem atSecond_X0_mul (c : ℂ) (z : ℕ) (R : MvPolynomial (Fin 2) ℂ) :
    atSecond c (MvPolynomial.X 0 ^ z * R) = MvPolynomial.X 0 ^ z * atSecond c R := by
  simp only [atSecond, map_mul, map_pow, MvPolynomial.bind₁_X_right, if_neg (by decide : ¬ (0 : Fin 2) = 1)]

theorem endPiece_zero (H : JetSpline) (hax : AxisCellsVanish H) (j : ℕ)
    (hj : j = 0 ∨ j = cellCount H.xAxis.breaks - 1) (i : ℕ) : H.toSpline.piece i j = 0 := by
  show ∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs, _ = 0
  refine Finset.sum_eq_zero fun d _ => Finset.sum_eq_zero fun e he => ?_
  by_cases hm : dofMeetsEndCells (cellCount H.xAxis.breaks) e
  · rw [hax d e he hm]
    simp
  · have h0 : H.xAxis.dofPoly j e = 0 := by
      cases e with
      | node k p =>
        simp only [dofMeetsEndCells, not_or, not_le] at hm
        simp only [JetAxis.dofPoly]
        split_ifs <;> first | rfl | omega
      | bubble i' s =>
        simp only [dofMeetsEndCells, not_or, not_le] at hm
        simp only [JetAxis.dofPoly]
        split_ifs <;> first | rfl | omega
    rw [h0]
    simp [embedSecond]

theorem spline_tame {G : Spline} (hG : IsJoinedSpline 1 1 G) (p : ℝ × ℝ) :
    TameNear (fun z : ℝ × ℝ => G.evalHalf z.1 z.2) p :=
  tameNear_of_slope ((joinedSplineSmooth 1 1 G hG).differentiable (by simp))
    (fun R => joinedSplineGradSlopeBound_of_smooth joinedSplineSmooth 1 1 G hG le_rfl le_rfl R) p

theorem start_quotient (H : JetSpline) (hc : IsJetClass 1 1 H) {z : ℕ} (hz : z ≤ H.tAxis.depth)
    (hv : StartVanishOrder H z) :
    ∃ G : Spline, IsJoinedSpline 1 1 G ∧ 0 < H.tAxis.breaks.getD 1 0 ∧
      (∀ τ x, τ < H.tAxis.breaks.getD 1 0 → H.toSpline.evalHalf τ x = (τ : ℂ) ^ z * G.evalHalf τ x) ∧
      (AxisCellsVanish H → (∀ᶠ x in 𝓝 (1 : ℝ), ∀ τ, G.evalHalf τ x = 0) ∧
        (∀ᶠ x in 𝓝 (-1 : ℝ), ∀ τ, G.evalHalf τ x = 0)) := by
  obtain ⟨-, ht1, hidx⟩ := startAxis_facts H.tAxis hc.t_axis
  have hdvd : ∀ j, (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ z ∣ H.toSpline.piece 0 j := by
    intro j
    show _ ∣ ∑ d ∈ H.tAxis.dofs, ∑ e ∈ H.xAxis.dofs, _
    refine Finset.dvd_sum fun d _ => Finset.dvd_sum fun e _ => ?_
    by_cases hd : ∃ p < z, d = JetDof.node 0 p
    · obtain ⟨p, hp, rfl⟩ := hd
      rw [hv p hp e]
      simp
    · push Not at hd
      obtain ⟨R, hR⟩ := startPoly_dvd H.tAxis hc.t_axis hz d hd
      have h2 : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ z ∣ embedFirst (H.tAxis.dofPoly 0 d) :=
        ⟨embedFirst R, by simp only [hR, embedFirst, map_mul, map_pow, Polynomial.aeval_X]⟩
      exact (h2.mul_left _).mul_right _
  choose Q hQ using hdvd
  have hX : (MvPolynomial.X 0 : MvPolynomial (Fin 2) ℂ) ^ z ≠ 0 := pow_ne_zero _ (MvPolynomial.X_ne_zero _)
  have hJ := jetSplineJoined H hc.t_axis hc.x_axis
  have htc : 0 < cellCount H.tAxis.breaks := by
    have h2 : 0 < H.tAxis.breaks.getD 1 0 := ht1
    by_contra hcon
    have hlen : H.tAxis.breaks.length ≤ 1 := by
      unfold cellCount at hcon
      omega
    rw [List.getD_eq_default _ _ (by omega)] at h2
    exact lt_irrefl _ h2
  let G : Spline := ⟨⟨[0, 1], H.xAxis.breaks⟩, fun _ j => Q j⟩
  refine ⟨G, ⟨⟨by show ([0, 1] : List ℝ).Pairwise (· < ·); norm_num, hc.x_axis.sorted, rfl, rfl, hc.x_axis.first, hc.x_axis.last⟩, ?_, ?_⟩, ht1, ?_, ?_⟩
  · intro i h1 h2
    have h3 : cellCount G.mesh.tBreaks = 1 := rfl
    omega
  · intro j hj1 hj2 i _ o ho
    have h := hJ.x_joins j hj1 hj2 0 htc o (le_trans ho (by have := hc.x_depth; omega))
    have e1 := hQ (j - 1)
    have e2 := hQ j
    simp only [JetSpline.toSpline] at e1 e2 h
    rw [e1, e2, xDeriv_X0_mul, xDeriv_X0_mul, atSecond_X0_mul, atSecond_X0_mul] at h
    exact mul_left_cancel₀ hX h
  · intro τ x hτ
    show MvPolynomial.eval ![(τ : ℂ), (x : ℂ)]
        (H.toSpline.piece (cellIndex H.tAxis.breaks τ) (cellIndex H.xAxis.breaks x)) =
      (τ : ℂ) ^ z * MvPolynomial.eval ![(τ : ℂ), (x : ℂ)] (Q (cellIndex H.xAxis.breaks x))
    rw [hidx τ hτ, hQ, map_mul, map_pow, MvPolynomial.eval_X]
    simp
  · intro hax
    obtain ⟨h1, h2⟩ := endCells_index H.xAxis.breaks hc.x_axis.sorted hc.x_axis.first hc.x_axis.last
    have hzero : ∀ j, (j = 0 ∨ j = cellCount H.xAxis.breaks - 1) → Q j = 0 := by
      intro j hj
      have hp := endPiece_zero H hax j hj 0
      rw [hQ] at hp
      exact (mul_eq_zero.1 hp).resolve_left hX
    refine ⟨h1.mono fun x hx τ => ?_, h2.mono fun x hx τ => ?_⟩
    · show MvPolynomial.eval ![(τ : ℂ), (x : ℂ)] (Q (cellIndex H.xAxis.breaks x)) = 0
      rw [hx, hzero _ (Or.inr rfl), map_zero]
    · show MvPolynomial.eval ![(τ : ℂ), (x : ℂ)] (Q (cellIndex H.xAxis.breaks x)) = 0
      rw [hx, hzero _ (Or.inl rfl), map_zero]

end Jet

end Internal

end ScalarOrigin

end PotentialShape

end Breakdown
