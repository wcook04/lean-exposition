import Breakdown.Frac.StTorusStepCompare
import Breakdown.Frac.TorusSource
import Breakdown.Frac.TorusForce
import Breakdown.Frac.TorusHeat
import Breakdown.Torus.CompareStatements
import Breakdown.Torus.SeqOps
import Breakdown.Torus.ChainTorus

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Periodic

namespace FracCompareWindow.Internal

variable {Z XT XR Y : Type} [NormedAddCommGroup Z] [NormedSpace ℝ Z]
  [NormedAddCommGroup XT] [NormedSpace ℝ XT] [NormedAddCommGroup XR] [NormedSpace ℝ XR]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem intervalIntegrable_of_singular (f : ℝ → Y) {u K : ℝ} (hu : 0 ≤ u)
    (hc : ContinuousOn f (Ioo 0 u)) (hb : ∀ σ ∈ Ioo 0 u, ‖f σ‖ ≤ K * (u - σ) ^ (-(3 / 4 : ℝ))) :
    IntervalIntegrable f volume 0 u := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu, integrableOn_Ioc_iff_integrableOn_Ioo]
  have h1 : IntervalIntegrable (fun x : ℝ => x ^ (-(3 / 4 : ℝ))) volume 0 u :=
    intervalIntegral.intervalIntegrable_rpow' (by norm_num)
  have h2 := (h1.comp_sub_left u).symm.const_mul K
  simp only [sub_zero, sub_self] at h2
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hu, integrableOn_Ioc_iff_integrableOn_Ioo] at h2
  exact h2.mono' (hc.aestronglyMeasurable measurableSet_Ioo)
    ((ae_restrict_iff' measurableSet_Ioo).2 (Eventually.of_forall hb))

theorem continuousOn_apply_shift (Λ : ℝ → Z →L[ℝ] XT)
    (hc : ∀ ζ, ContinuousOn (fun τ => Λ τ ζ) (Ioi 0)) {K : ℝ} (hK : 0 ≤ K)
    (hb : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ K * τ ^ (-(3 / 4 : ℝ))) {x : ℝ → Z} (hx : Continuous x)
    {u e : ℝ} (he : 0 ≤ e) (hue : u ≤ 1 - e) :
    ContinuousOn (fun σ => Λ (1 - σ - e) (x σ)) (Ioo 0 u) := by
  intro σ₀ h₀
  have ht0 : 0 < 1 - σ₀ - e := by linarith [h₀.2]
  have hτ : Continuous (fun σ : ℝ => 1 - σ - e) := by fun_prop
  have hB : ∀ᶠ σ in 𝓝[Ioo 0 u] σ₀, ‖Λ (1 - σ - e)‖ ≤ K * ((1 - σ₀ - e) / 2) ^ (-(3 / 4 : ℝ)) := by
    have h2 : ∀ᶠ σ in 𝓝[Ioo 0 u] σ₀, σ < σ₀ + (1 - σ₀ - e) / 2 :=
      nhdsWithin_le_nhds (gt_mem_nhds (by linarith))
    filter_upwards [h2, self_mem_nhdsWithin] with σ hσ hσ'
    refine (hb _ (by linarith) (by linarith [hσ'.1])).trans (mul_le_mul_of_nonneg_left ?_ hK)
    exact Real.rpow_le_rpow_of_nonpos (by linarith) (by linarith) (by norm_num)
  exact SeqOps.Internal.tendsto_apply Λ hc ht0 ((hτ.tendsto σ₀).mono_left nhdsWithin_le_nhds)
    ((hx.tendsto σ₀).mono_left nhdsWithin_le_nhds) hB

theorem norm_term_le (Λ : ℝ → Z →L[ℝ] XT) (G : XT →L[ℝ] Y) {K M Cw Cx : ℝ} (hK : 0 ≤ K)
    (hM : 0 ≤ M) (hCw : 0 ≤ Cw) (hCx : 0 ≤ Cx) (hG : ‖G‖ ≤ M)
    (hb : ∀ τ, 0 < τ → τ ≤ 1 → ‖Λ τ‖ ≤ K * τ ^ (-(3 / 4 : ℝ))) {w : ℝ} {z : Z} (hw : ‖w‖ ≤ Cw)
    (hz : ‖z‖ ≤ Cx) {τ v : ℝ} (hv : 0 < v) (hvτ : v ≤ τ) (hτ1 : τ ≤ 1) :
    ‖w • G (Λ τ z)‖ ≤ Cw * M * K * Cx * v ^ (-(3 / 4 : ℝ)) := by
  have hτ0 : 0 < τ := lt_of_lt_of_le hv hvτ
  have hr : τ ^ (-(3 / 4 : ℝ)) ≤ v ^ (-(3 / 4 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hv hvτ (by norm_num)
  have hΛ : ‖Λ τ z‖ ≤ K * τ ^ (-(3 / 4 : ℝ)) * Cx :=
    ((Λ τ).le_opNorm z).trans (mul_le_mul (hb τ hτ0 hτ1) hz (norm_nonneg _) (by positivity))
  have hGz : ‖G (Λ τ z)‖ ≤ M * (K * τ ^ (-(3 / 4 : ℝ)) * Cx) :=
    (G.le_opNorm _).trans (mul_le_mul hG hΛ (norm_nonneg _) hM)
  rw [norm_smul]
  calc ‖w‖ * ‖G (Λ τ z)‖ ≤ Cw * (M * (K * τ ^ (-(3 / 4 : ℝ)) * Cx)) :=
        mul_le_mul hw hGz (norm_nonneg _) hCw
    _ ≤ Cw * (M * (K * v ^ (-(3 / 4 : ℝ)) * Cx)) := by gcongr
    _ = Cw * M * K * Cx * v ^ (-(3 / 4 : ℝ)) := by ring

theorem window_piece [CompleteSpace Y] (hSp : SplitIntegralBound) (ΛT : ℝ → Z →L[ℝ] XT)
    (ΛR : ℝ → Z →L[ℝ] XR) (GT : XT →L[ℝ] Y) (GR : XR →L[ℝ] Y)
    (hcT : ∀ ζ, ContinuousOn (fun τ => ΛT τ ζ) (Ioi 0))
    (hcR : ∀ ζ, ContinuousOn (fun τ => ΛR τ ζ) (Ioi 0)) {KT KR MT MR Cw Cx : ℝ} (hKT : 0 ≤ KT)
    (hKR : 0 ≤ KR) (hMT : 0 ≤ MT) (hMR : 0 ≤ MR) (hCw : 0 ≤ Cw) (hCx : 0 ≤ Cx)
    (hbT : ∀ τ, 0 < τ → τ ≤ 1 → ‖ΛT τ‖ ≤ KT * τ ^ (-(3 / 4 : ℝ)))
    (hbR : ∀ τ, 0 < τ → τ ≤ 1 → ‖ΛR τ‖ ≤ KR * τ ^ (-(3 / 4 : ℝ))) (hGT : ‖GT‖ ≤ MT)
    (hGR : ‖GR‖ ≤ MR) {w : ℝ → ℝ} (hw : Continuous w) (hwb : ∀ σ, ‖w σ‖ ≤ Cw) {x : ℝ → Z}
    (hx : Continuous x) (hxb : ∀ σ, ‖x σ‖ ≤ Cx) {u e ε a₀ : ℝ} (hu : 0 ≤ u) (he : 0 ≤ e)
    (hue : u ≤ 1 - e) (hε : 0 < ε) (ha₀ : 0 ≤ a₀)
    (hfar : ∀ σ ∈ Ioo 0 u, ε ≤ 1 - σ - e →
      ‖GT (ΛT (1 - σ - e) (x σ)) - GR (ΛR (1 - σ - e) (x σ))‖ ≤ a₀)
    (fT fR : ℝ → Y) (hfT : ∀ σ, fT σ = w σ • GT (ΛT (1 - σ - e) (x σ)))
    (hfR : ∀ σ, fR σ = w σ • GR (ΛR (1 - σ - e) (x σ))) :
    ‖(∫ σ in (0 : ℝ)..u, fT σ) - ∫ σ in (0 : ℝ)..u, fR σ‖ ≤
      Cw * a₀ * u + 4 * (Cw * (MT * KT + MR * KR) * Cx) * ε ^ (1 / 4 : ℝ) := by
  obtain rfl : fT = fun σ => w σ • GT (ΛT (1 - σ - e) (x σ)) := funext hfT
  obtain rfl : fR = fun σ => w σ • GR (ΛR (1 - σ - e) (x σ)) := funext hfR
  have hσ : ∀ σ ∈ Ioo 0 u, 0 < u - σ ∧ u - σ ≤ 1 - σ - e ∧ 1 - σ - e ≤ 1 := fun σ h =>
    ⟨by linarith [h.2], by linarith, by linarith [h.1]⟩
  have hbdT : ∀ σ ∈ Ioo 0 u, ‖w σ • GT (ΛT (1 - σ - e) (x σ))‖ ≤
      Cw * MT * KT * Cx * (u - σ) ^ (-(3 / 4 : ℝ)) := fun σ h =>
    norm_term_le ΛT GT hKT hMT hCw hCx hGT hbT (hwb σ) (hxb σ) (hσ σ h).1 (hσ σ h).2.1 (hσ σ h).2.2
  have hbdR : ∀ σ ∈ Ioo 0 u, ‖w σ • GR (ΛR (1 - σ - e) (x σ))‖ ≤
      Cw * MR * KR * Cx * (u - σ) ^ (-(3 / 4 : ℝ)) := fun σ h =>
    norm_term_le ΛR GR hKR hMR hCw hCx hGR hbR (hwb σ) (hxb σ) (hσ σ h).1 (hσ σ h).2.1 (hσ σ h).2.2
  have hiT : IntervalIntegrable (fun σ => w σ • GT (ΛT (1 - σ - e) (x σ))) volume 0 u :=
    intervalIntegrable_of_singular _ hu
      (hw.continuousOn.smul (GT.continuous.comp_continuousOn
        (continuousOn_apply_shift ΛT hcT hKT hbT hx he hue))) hbdT
  have hiR : IntervalIntegrable (fun σ => w σ • GR (ΛR (1 - σ - e) (x σ))) volume 0 u :=
    intervalIntegrable_of_singular _ hu
      (hw.continuousOn.smul (GR.continuous.comp_continuousOn
        (continuousOn_apply_shift ΛR hcR hKR hbR hx he hue))) hbdR
  rw [← intervalIntegral.integral_sub hiT hiR]
  refine hSp Y (fun σ => w σ • GT (ΛT (1 - σ - e) (x σ)) - w σ • GR (ΛR (1 - σ - e) (x σ)))
    u ε (Cw * a₀) (Cw * (MT * KT + MR * KR) * Cx) hu hε (mul_nonneg hCw ha₀) (by positivity) ?_
  intro σ h
  by_cases hfr : ε ≤ 1 - σ - e
  · left
    rw [← smul_sub, norm_smul]
    exact mul_le_mul (hwb σ) (hfar σ h hfr) (norm_nonneg _) hCw
  · right
    refine ⟨by linarith, ?_⟩
    refine (norm_sub_le _ _).trans ?_
    have := add_le_add (hbdT σ h) (hbdR σ h)
    linarith

theorem exponent_nonneg {α : ℝ} (hα : 1 < α) : 0 ≤ dilExponent α := by
  have h : 3 / (4 * α) ≤ 3 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  unfold dilExponent
  linarith

theorem rpow_kernel_le {α τ : ℝ} (hα : 1 < α) (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    τ ^ (-(3 / (4 * α))) ≤ τ ^ (-(3 / 4 : ℝ)) := by
  have h : 3 / (4 * α) ≤ 3 / 4 := div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  exact Real.rpow_le_rpow_of_exponent_ge hτ hτ1 (by linarith)

theorem sim_pos {α μ : ℝ} (hμ : 0 < μ) : 0 < simScale α μ := Real.rpow_pos_of_pos hμ _

theorem sim_le_one {α μ : ℝ} (hα : 1 < α) (hμ : 0 < μ) (hμ1 : μ ≤ 1) : simScale α μ ≤ 1 :=
  Real.rpow_le_one hμ.le hμ1 (one_div_nonneg.2 (by linarith))

theorem sim_mono {α μ T : ℝ} (hα : 1 < α) (hμ : 0 < μ) (h : μ ≤ T) : simScale α μ ≤ simScale α T :=
  Real.rpow_le_rpow hμ.le h (one_div_nonneg.2 (by linarith))

theorem sim_mul {α a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c) :
    simScale α (a * c) = simScale α a * simScale α c := by
  unfold simScale
  exact Real.mul_rpow ha hc

theorem sim_lt {α T X : ℝ} (hα : 1 < α) (hT : 0 < T) (hX : 0 < X) (h : T < X ^ α) :
    simScale α T < X := by
  have hα0 : 0 < α := by linarith
  have h1 : T ^ (1 / α) < (X ^ α) ^ (1 / α) := Real.rpow_lt_rpow hT.le h (by positivity)
  have h2 : (X ^ α) ^ (1 / α) = X := by
    rw [← Real.rpow_mul hX.le, mul_one_div_cancel hα0.ne', Real.rpow_one]
  unfold simScale
  rwa [h2] at h1

theorem norm_restrictTorus_le {C : ℝ} (hC : 0 ≤ C) (hb : ∀ μ b z, ‖restrictTorusFun μ b z‖ ≤ C * ‖z‖)
    (μ b : ℝ) : ‖restrictTorus μ b‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC fun z => hb μ b z

theorem norm_dil_le {α : ℝ} (hα : 1 < α) (hD : Freq.FracDilationAlgebra α) {c : ℝ} (hc : 0 < c)
    (hc1 : c ≤ 1) : ‖Freq.fracDilX α c‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  rw [hD.1 c hc x]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_one hc.le hc1 (exponent_nonneg hα)) (norm_nonneg _)

theorem norm_smul_id_le {α c : ℝ} (hα : 1 < α) (hc : 0 < c) (hc1 : c ≤ 1) :
    ‖(c ^ dilExponent α) • ContinuousLinearMap.id ℝ V‖ ≤ 1 := by
  refine (norm_smul_le _ _).trans ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hc.le _)]
  calc c ^ dilExponent α * ‖ContinuousLinearMap.id ℝ V‖ ≤ 1 * 1 :=
        mul_le_mul (Real.rpow_le_one hc.le hc1 (exponent_nonneg hα)) (ContinuousLinearMap.norm_id_le)
          (norm_nonneg _) zero_le_one
    _ = 1 := one_mul 1

theorem rpow_quarter_le {r ε : ℝ} (hr : 0 ≤ r) (hε : 0 ≤ ε) (h : ε ≤ r ^ 4) :
    ε ^ (1 / 4 : ℝ) ≤ r := by
  have h1 : ε ^ (1 / 4 : ℝ) ≤ (r ^ 4) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hε h (by norm_num)
  have h2 : (r ^ 4) ^ (1 / 4 : ℝ) = r := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hr]
    norm_num
  rwa [h2] at h1

theorem sqrt_mul_le_of_lt {T b : ℝ} (hT : 0 < T) (hb : 0 < b) (h : T < 1 / (64 * b ^ 2)) :
    Real.sqrt T * b ≤ 1 / 8 := by
  have h1 : T * (64 * b ^ 2) < 1 := (lt_div_iff₀ (by positivity)).1 h
  have hs : Real.sqrt T ^ 2 = T := Real.sq_sqrt hT.le
  have h0 : 0 ≤ Real.sqrt T * b := by positivity
  nlinarith [sq_nonneg (Real.sqrt T * b - 1 / 8)]

theorem source_continuous {α : ℝ} (hα : 1 < α) : FracSourceOpContinuous α := by
  have hF : FracTorusForceAlgebra α :=
    fracTorusForceAlgebra α hα.le (fracTorusHeatAlgebra α)
  exact fracSourceOpContinuous α hα (fracSourceOpExists α hα hF) hF

theorem window_term {α : ℝ} (hα : 1 < α) (hSp : SplitIntegralBound) (hFr : FracFrameChange α)
    (hC : FracHeatSolenoidalContinuous α) (hSC : FracSourceOpContinuous α)
    (hD : Freq.FracDilationAlgebra α) (φ : Space → Space) (hφ : IsTestField φ) {b L : ℝ}
    (w : C(Icc (0 : ℝ) L, ℝ)) (zz : Piece ShellData L)
    {CA Cad CRL CTL CRR Crt Cz μm μs μn c e u ε δ : ℝ} (hCA : 0 ≤ CA) (hCad0 : 0 ≤ Cad) (hCRL0 : 0 ≤ CRL)
    (hCTL0 : 0 ≤ CTL) (hCRR0 : 0 ≤ CRR) (hCrt0 : 0 ≤ Crt) (hCz : 0 ≤ Cz)
    (hwb : ‖w‖ ≤ CA) (hφb : ‖Freq.embedX φ‖ ≤ CA) (hzb : ‖zz‖ ≤ Cz)
    (hCad : ∀ z, (eLpNorm (advectShell φ hφ b z : Space → Space) (3 / 2) volume).toReal ≤
      Cad * ‖Freq.embedX φ‖ * ‖z‖)
    (hsupp : ∀ z, ∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b →
      (advectShell φ hφ b z : Space → Space) y = 0)
    (hCRL : ∀ τ, 0 < τ → ∀ z,
      ‖fracLambdaR3 α φ hφ b τ z‖ ≤ CRL * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖z‖)
    (hCTL : ∀ τ, 0 < τ → μm * τ ≤ 1 → ∀ z,
      ‖fracLambdaTorus α φ hφ b μm τ z‖ ≤ CTL * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖z‖)
    (hCRR : ∀ b, ‖restrictR3 b‖ ≤ CRR) (hCrt : ∀ μ b z, ‖restrictTorusFun μ b z‖ ≤ Crt * ‖z‖)
    (hμm0 : 0 < μm) (hμm1 : μm ≤ 1) (hshell : IsShellScale μs (Real.sqrt (simScale α c) * b))
    (hc0 : 0 < c) (hc1 : c ≤ 1) (hμn : μn = μs * simScale α c) (hu : 0 ≤ u) (he : 0 ≤ e)
    (hue : u ≤ 1 - e) (hε : 0 < ε) (hε1 : ε ≤ 1) (hδ : 0 ≤ δ)
    (hcmp : ∀ τ ∈ Icc ε ε⁻¹, ∀ B : Freq.L2R,
      (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → B y = 0) →
      ‖restrictTorus μs (Real.sqrt (simScale α c) * b) ((μm ^ (-(1 / (4 * α)))) • fracSourceOp α μm τ B) -
        restrictR3 (Real.sqrt (simScale α c) * b) (Freq.fracHeatSolenoidal α τ B)‖ ≤
      δ * (eLpNorm (B : Space → Space) (3 / 2) volume).toReal) :
    ‖(∫ σ in (0 : ℝ)..u, extendPiece w σ • restrictTorus μn b
          (c ^ dilExponent α • (-((μm ^ (-(1 / (4 * α)))) •
            fracSourceOp α μm (1 - σ - e) (advectShell φ hφ b (extendPiece zz σ)))))) -
        ∫ σ in (0 : ℝ)..u, extendPiece w σ • restrictR3 b (Freq.fracDilX α c
          (-(Freq.fracHeatSolenoidal α (1 - σ - e) (advectShell φ hφ b (extendPiece zz σ)))))‖ ≤
      CA * (δ * (Cad * CA * Cz)) * u +
        4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Cz) * ε ^ (1 / 4 : ℝ) := by
  subst hμn
  have hzσ : ∀ σ, ‖extendPiece zz σ‖ ≤ Cz := fun σ => (SeqOps.Internal.norm_extend_le zz σ).trans hzb
  have hbT : ∀ τ, 0 < τ → τ ≤ 1 → ‖fracLambdaTorus α φ hφ b μm τ‖ ≤ (CTL * CA) * τ ^ (-(3 / 4 : ℝ)) := by
    intro τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    refine (hCTL τ hτ (mul_le_one₀ hμm1 hτ.le hτ1) z).trans ?_
    have hk := rpow_kernel_le hα hτ hτ1
    calc CTL * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖z‖ ≤ CTL * τ ^ (-(3 / 4 : ℝ)) * CA * ‖z‖ := by
          gcongr
      _ = CTL * CA * τ ^ (-(3 / 4 : ℝ)) * ‖z‖ := by ring
  have hbR : ∀ τ, 0 < τ → τ ≤ 1 → ‖fracLambdaR3 α φ hφ b τ‖ ≤ (CRL * CA) * τ ^ (-(3 / 4 : ℝ)) := by
    intro τ hτ hτ1
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
    refine (hCRL τ hτ z).trans ?_
    have hk := rpow_kernel_le hα hτ hτ1
    calc CRL * τ ^ (-(3 / (4 * α))) * ‖Freq.embedX φ‖ * ‖z‖ ≤ CRL * τ ^ (-(3 / 4 : ℝ)) * CA * ‖z‖ := by
          gcongr
      _ = CRL * CA * τ ^ (-(3 / 4 : ℝ)) * ‖z‖ := by ring
  have hGT : ‖(restrictTorus (μs * simScale α c) b).comp
      ((c ^ dilExponent α) • ContinuousLinearMap.id ℝ V)‖ ≤ Crt := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h := mul_le_mul (norm_restrictTorus_le hCrt0 hCrt (μs * simScale α c) b)
      (norm_smul_id_le hα hc0 hc1) (norm_nonneg _) hCrt0
    simpa using h
  have hGR : ‖(restrictR3 b).comp (Freq.fracDilX α c)‖ ≤ CRR := by
    refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
    have h := mul_le_mul (hCRR b) (norm_dil_le hα hD hc0 hc1) (norm_nonneg _) hCRR0
    simpa using h
  have hcT : ∀ z, ContinuousOn (fun τ => fracLambdaTorus α φ hφ b μm τ z) (Ioi 0) := fun z =>
    ((hSC μm (advectShell φ hφ b z) hμm0).const_smul (μm ^ (-(1 / (4 * α))))).neg
  refine window_piece hSp (fun τ => fracLambdaTorus α φ hφ b μm τ) (fun τ => fracLambdaR3 α φ hφ b τ)
    ((restrictTorus (μs * simScale α c) b).comp ((c ^ dilExponent α) • ContinuousLinearMap.id ℝ V))
    ((restrictR3 b).comp (Freq.fracDilX α c)) hcT
    (fun z => (hC (advectShell φ hφ b z)).neg)
    (by positivity) (by positivity) hCrt0 hCRR0 hCA hCz hbT hbR hGT hGR
    (SeqOps.Internal.extend_continuous w) (fun σ => (SeqOps.Internal.norm_extend_le w σ).trans hwb)
    (SeqOps.Internal.extend_continuous zz) hzσ hu he hue hε (by positivity) ?_ _ _
    (fun σ => rfl) (fun σ => rfl)
  intro σ hσ hfr
  have hτ1 : 1 - σ - e ≤ 1 := by linarith [hσ.1]
  have hτi : 1 - σ - e ≤ ε⁻¹ := hτ1.trans ((one_le_inv₀ hε).2 hε1)
  show ‖restrictTorus (μs * simScale α c) b
      (c ^ dilExponent α • fracLambdaTorus α φ hφ b μm (1 - σ - e) (extendPiece zz σ)) -
    restrictR3 b (Freq.fracDilX α c (fracLambdaR3 α φ hφ b (1 - σ - e) (extendPiece zz σ)))‖ ≤ _
  refine (hFr μs c b hc0 hc1 hshell _ _).trans ?_
  have h1 : fracLambdaTorus α φ hφ b μm (1 - σ - e) (extendPiece zz σ) =
      -((μm ^ (-(1 / (4 * α)))) • fracSourceOp α μm (1 - σ - e)
        (advectShell φ hφ b (extendPiece zz σ))) := rfl
  have h2 : fracLambdaR3 α φ hφ b (1 - σ - e) (extendPiece zz σ) =
      -(Freq.fracHeatSolenoidal α (1 - σ - e) (advectShell φ hφ b (extendPiece zz σ))) := rfl
  rw [h1, h2, map_neg, map_neg, neg_sub_neg, norm_sub_rev]
  have hc := hcmp (1 - σ - e) ⟨hfr, hτi⟩ _ (hsupp (extendPiece zz σ))
  have hadv := hCad (extendPiece zz σ)
  have hc14 : c ^ dilExponent α ≤ 1 := Real.rpow_le_one hc0.le hc1 (exponent_nonneg hα)
  refine (mul_le_mul hc14 (hc.trans (mul_le_mul_of_nonneg_left hadv hδ)) (norm_nonneg _)
    zero_le_one).trans ?_
  rw [one_mul]
  gcongr
  exact hzσ σ

theorem final_arith {θ η N M₁ M₂ δ r ε Z CA Cad Crt CTL CRR CRL : ℝ} {j j₀ terms : ℕ}
    (hθ0 : 0 < θ) (hθi : 1 ≤ θ⁻¹) (hj : j ≤ j₀) (hZ : 0 ≤ Z) (hM₁ : M₁ = CA * Cad * CA)
    (hM₂ : M₂ = CA * (Crt * (CTL * CA) + CRR * (CRL * CA))) (hM₁0 : 0 ≤ M₁) (hM₂0 : 0 ≤ M₂)
    (hN : N = (θ⁻¹) ^ j₀ * ((terms : ℝ) + 1)) (hN0 : 0 < N) (hδ : δ = η / (2 * N * (M₁ + 1)))
    (hδ0 : 0 ≤ δ) (hr : r = η / (8 * N * (M₂ + 1))) (hr0 : 0 ≤ r) (hε0 : 0 ≤ ε) (hεr : ε ≤ r ^ 4) :
    ‖(θ⁻¹) ^ j‖ * ((terms : ℝ) * (CA * (δ * (Cad * CA * Z)) +
      4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Z) * ε ^ (1 / 4 : ℝ))) ≤ η * Z := by
  have hq : ε ^ (1 / 4 : ℝ) ≤ r := rpow_quarter_le hr0 hε0 hεr
  have hB : CA * (δ * (Cad * CA * Z)) + 4 * (CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) * Z) *
      ε ^ (1 / 4 : ℝ) = Z * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)) := by
    rw [hM₁, hM₂]; ring
  rw [hB]
  have hq0 : 0 ≤ ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hε0 _
  have h1 : δ * M₁ ≤ η / (2 * N) := by
    calc δ * M₁ ≤ δ * (M₁ + 1) := by nlinarith
      _ = η / (2 * N) := by rw [hδ]; field_simp
  have h2 : 4 * M₂ * ε ^ (1 / 4 : ℝ) ≤ η / (2 * N) := by
    calc 4 * M₂ * ε ^ (1 / 4 : ℝ) ≤ 4 * (M₂ + 1) * r :=
          mul_le_mul (by linarith) hq hq0 (by linarith)
      _ = η / (2 * N) := by rw [hr]; field_simp; ring
  have hsum : η / (2 * N) + η / (2 * N) = η / N := by field_simp; ring
  have hQ : δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ) ≤ η / N := by linarith
  have hQ0 : 0 ≤ δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ) := by positivity
  have hθp : 0 < θ⁻¹ := inv_pos.2 hθ0
  have hpow : ‖(θ⁻¹) ^ j‖ ≤ (θ⁻¹) ^ j₀ := by
    rw [norm_pow, Real.norm_eq_abs, abs_of_pos hθp]
    exact pow_le_pow_right₀ hθi hj
  have hterms : (θ⁻¹) ^ j₀ * (terms : ℝ) ≤ N := by
    rw [hN]
    have := pow_pos hθp j₀
    nlinarith
  have ht0 : (0 : ℝ) ≤ terms := Nat.cast_nonneg _
  calc ‖(θ⁻¹) ^ j‖ * ((terms : ℝ) * (Z * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)))) ≤
        (θ⁻¹) ^ j₀ * ((terms : ℝ) * (Z * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)))) :=
        mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = ((θ⁻¹) ^ j₀ * terms) * (δ * M₁ + 4 * M₂ * ε ^ (1 / 4 : ℝ)) * Z := by ring
    _ ≤ N * (η / N) * Z := mul_le_mul_of_nonneg_right (mul_le_mul hterms hQ hQ0 hN0.le) hZ
    _ = η * Z := by field_simp

end FracCompareWindow.Internal

set_option maxHeartbeats 1000000 in
open FracCompareWindow.Internal in
theorem fracWindowBound (α : ℝ) (hα : 1 < α) (hR : FracR3EntryFormula α)
    (hT : FracTorusEntryFormula α hα) (hFr : FracFrameChange α) (hSp : SplitIntegralBound)
    (hHLC : FracHeatSolenoidalComparison α) (hRB : FracR3LambdaBound α) (hTB : FracTorusLambdaBound α)
    (hRR : RestrictR3Bound) (hAd : AdvectShellBounds) (hD : Freq.FracDilationAlgebra α)
    (hC : FracHeatSolenoidalContinuous α) : FracWindowBound α hα := by
  intro F hFK hFG hFD P k θ b A hl hl1 hP hk hL hθl hθ1 hb j₀ η hη
  have hSC : FracSourceOpContinuous α := source_continuous hα
  have hk' : (0 : ℝ) < k := Nat.cast_pos.2 hk
  have hlt : Real.exp (-(P / k)) < 1 := Real.exp_lt_one_iff.2 (by have := div_pos hP hk'; linarith)
  have hhalf : 1 / 2 ≤ Real.exp (-(P / k)) := by
    have := hL
    simp only [MildFramework.stepLength] at this
    linarith
  have hθ0 : 0 < θ := lt_of_le_of_lt (Real.rpow_nonneg hl.le _) hθl
  obtain ⟨CA₀, hCA₀⟩ := A.bound
  obtain ⟨CA, hCA0, hCA⟩ : ∃ CA : ℝ, 0 ≤ CA ∧ ∀ n l, ‖Freq.embedX (A.field n l)‖ ≤ CA ∧ ‖A.weight n l‖ ≤ CA :=
    ⟨max CA₀ 0, le_max_right _ _, fun n l => ⟨(hCA₀ n l).1.trans (le_max_left _ _), (hCA₀ n l).2.trans (le_max_left _ _)⟩⟩
  obtain ⟨⟨Cad, hCad0, hCad⟩, hsupp⟩ := hAd
  obtain ⟨CRL, hCRL0, hCRL⟩ := hRB
  obtain ⟨CTL, hCTL0, hCTL⟩ := hTB
  obtain ⟨CRR, hCRR0, hCRR⟩ := hRR
  obtain ⟨Crt, hCrt0, hCrt⟩ := restrictTorusFun_bound
  obtain ⟨M₁, hM₁⟩ : ∃ M₁ : ℝ, M₁ = CA * Cad * CA := ⟨_, rfl⟩
  obtain ⟨M₂, hM₂⟩ : ∃ M₂ : ℝ, M₂ = CA * (Crt * (CTL * CA) + CRR * (CRL * CA)) := ⟨_, rfl⟩
  have hM₁0 : 0 ≤ M₁ := by rw [hM₁]; positivity
  have hM₂0 : 0 ≤ M₂ := by rw [hM₂]; positivity
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = (θ⁻¹) ^ j₀ * ((A.terms : ℝ) + 1) := ⟨_, rfl⟩
  have hθi : 1 ≤ θ⁻¹ := (one_le_inv₀ hθ0).2 hθ1.le
  have hN0 : 0 < N := by rw [hN]; positivity
  obtain ⟨δ', hδ'⟩ : ∃ δ' : ℝ, δ' = η / (2 * N * (M₁ + 1)) := ⟨_, rfl⟩
  have hδ'0 : 0 < δ' := by rw [hδ']; positivity
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = η / (8 * N * (M₂ + 1)) := ⟨_, rfl⟩
  have hr0 : 0 < r := by rw [hr]; positivity
  obtain ⟨ε', hε'0, hε'1, hε'r⟩ : ∃ ε' : ℝ, 0 < ε' ∧ ε' ≤ 1 ∧ ε' ≤ r ^ 4 :=
    ⟨min 1 (r ^ 4), lt_min zero_lt_one (by positivity), min_le_left _ _, min_le_right _ _⟩
  have hμ : ∀ j : ℕ, ∃ μ₀ : ℝ, 0 < μ₀ ∧ ∀ μ : ℝ, 0 < μ → μ < μ₀ →
      ∀ τ ∈ Icc ε' ε'⁻¹, ∀ B : Freq.L2R,
        (∀ᵐ y ∂volume, y ∉ Metric.closedBall (0 : Space) b → B y = 0) →
        ‖restrictTorus (simScale α μ) (Real.sqrt (simScale α (Real.exp (-(P / k)) ^ j)) * b)
            ((μ ^ (-(1 / (4 * α)))) • fracSourceOp α μ τ B) -
          restrictR3 (Real.sqrt (simScale α (Real.exp (-(P / k)) ^ j)) * b) (Freq.fracHeatSolenoidal α τ B)‖ ≤
        δ' * (eLpNorm (B : Space → Space) (3 / 2) volume).toReal := fun j =>
    hHLC _ b ε' δ' (mul_pos (Real.sqrt_pos.2 (sim_pos (pow_pos hl j))) hb) hb hε'0 hδ'0
  choose μ₀ hμ₀ hμ₀b using hμ
  have hX : (0 : ℝ) < 1 / (64 * b ^ 2) := by positivity
  refine ⟨min ((1 / (64 * b ^ 2)) ^ α) ((Finset.range (j₀ + 1)).inf' ⟨0, by simp⟩ μ₀),
    lt_min (Real.rpow_pos_of_pos hX _) ((Finset.lt_inf'_iff _).2 fun j _ => hμ₀ j), ?_⟩
  intro T hTp hT1 hTT ζ m j hj s
  have hT64 : simScale α T < 1 / (64 * b ^ 2) :=
    sim_lt hα hTp hX (lt_of_lt_of_le hTT (min_le_left _ _))
  have hTμ : T < μ₀ j := lt_of_lt_of_le hTT ((min_le_right _ _).trans
    (Finset.inf'_le _ (Finset.mem_range.2 (by omega))))
  have hsq : Real.sqrt (simScale α T) * b ≤ 1 / 8 := sqrt_mul_le_of_lt (sim_pos hTp) hb hT64
  have eT := hT T (Real.exp (-(P / k))) θ hTp hT1 hl hl1 b A hlt hhalf hθ0 hb hsq ζ m j s
  have eR := hR F hFK hFG hFD P k θ b A hP hk hL hθ0 hb ζ m j s
  rw [eT, eR, ← smul_sub, ← Finset.sum_sub_distrib]
  clear eT eR
  have hc0 : 0 < Real.exp (-(P / k)) ^ j := pow_pos hl j
  have hc1 : Real.exp (-(P / k)) ^ j ≤ 1 := pow_le_one₀ hl.le hl1
  have hμm0 : 0 < stepScale T (Real.exp (-(P / k))) m := stepScale_pos hTp hl m
  have hμmT : stepScale T (Real.exp (-(P / k))) m ≤ T :=
    mul_le_of_le_one_right hTp.le (pow_le_one₀ hl.le hl1)
  have hμm1 : stepScale T (Real.exp (-(P / k))) m ≤ 1 := hμmT.trans hT1
  have hsm0 : 0 < simScale α (stepScale T (Real.exp (-(P / k))) m) := sim_pos hμm0
  have hsm1 : simScale α (stepScale T (Real.exp (-(P / k))) m) ≤ 1 := sim_le_one hα hμm0 hμm1
  have hsqm : Real.sqrt (simScale α (stepScale T (Real.exp (-(P / k))) m)) * b ≤ 1 / 8 :=
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (sim_mono hα hμm0 hμmT)) hb.le).trans hsq
  have hshell : IsShellScale (simScale α (stepScale T (Real.exp (-(P / k))) m)) b :=
    ⟨hsm0, hsm1, hb, hsqm⟩
  have hsc1 : Real.sqrt (simScale α (Real.exp (-(P / k)) ^ j)) ≤ 1 :=
    Real.sqrt_le_one.2 (sim_le_one hα hc0 hc1)
  have hshell' : IsShellScale (simScale α (stepScale T (Real.exp (-(P / k))) m))
      (Real.sqrt (simScale α (Real.exp (-(P / k)) ^ j)) * b) := by
    refine ⟨hsm0, hsm1, mul_pos (Real.sqrt_pos.2 (sim_pos hc0)) hb, ?_⟩
    calc Real.sqrt (simScale α (stepScale T (Real.exp (-(P / k))) m)) *
          (Real.sqrt (simScale α (Real.exp (-(P / k)) ^ j)) * b) ≤
          Real.sqrt (simScale α (stepScale T (Real.exp (-(P / k))) m)) * (1 * b) := by gcongr
      _ = Real.sqrt (simScale α (stepScale T (Real.exp (-(P / k))) m)) * b := by ring
      _ ≤ 1 / 8 := hsqm
  have hstep : stepScale T (Real.exp (-(P / k))) (m + j) =
      stepScale T (Real.exp (-(P / k))) m * Real.exp (-(P / k)) ^ j := by
    simp only [stepScale, pow_add]
    ring
  have hμn : simScale α (stepScale T (Real.exp (-(P / k))) (m + j)) =
      simScale α (stepScale T (Real.exp (-(P / k))) m) * simScale α (Real.exp (-(P / k)) ^ j) := by
    rw [hstep, sim_mul hμm0.le hc0.le]
  have hs0 : (0 : ℝ) ≤ s := s.2.1
  have hsL : (s : ℝ) ≤ 1 - Real.exp (-(P / k)) := s.2.2
  have he0 : 0 ≤ Real.exp (-(P / k)) ^ j * (1 - s) := mul_nonneg hc0.le (by linarith)
  have hu0 : 0 ≤ (if j = 0 then (s : ℝ) else 1 - Real.exp (-(P / k))) := by
    split_ifs
    · exact hs0
    · linarith
  have hu1 : (if j = 0 then (s : ℝ) else 1 - Real.exp (-(P / k))) ≤ 1 := by
    split_ifs
    · linarith
    · linarith
  have hue : (if j = 0 then (s : ℝ) else 1 - Real.exp (-(P / k))) ≤
      1 - Real.exp (-(P / k)) ^ j * (1 - s) := by
    split_ifs with hj0
    · subst hj0; simp
    · have h1 : Real.exp (-(P / k)) ^ j ≤ Real.exp (-(P / k)) := pow_le_of_le_one hl.le hl1 hj0
      have h2 : Real.exp (-(P / k)) ^ j * (1 - s) ≤ Real.exp (-(P / k)) ^ j :=
        mul_le_of_le_one_right (pow_nonneg hl.le j) (by linarith)
      linarith
  have hζm : ‖ζ m‖ ≤ ‖ζ‖ := lp.norm_apply_le_norm ENNReal.top_ne_zero ζ m
  have hB0 : 0 ≤ CA * (δ' * (Cad * CA * ‖ζ‖)) := by positivity
  refine (norm_smul_le _ _).trans ?_
  refine (mul_le_mul_of_nonneg_left (norm_sum_le _ _) (norm_nonneg _)).trans ?_
  refine (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ =>
    ((window_term hα hSp hFr hC hSC hD (A.field m l) (A.isTest m l) (A.weight m l) (ζ m)
      hCA0 hCad0 hCRL0 hCTL0 hCRR0 hCrt0 (norm_nonneg ζ) (hCA m l).2 (hCA m l).1 hζm
      (hCad (A.field m l) (A.isTest m l) b) (hsupp (A.field m l) (A.isTest m l) b)
      (hCRL (A.field m l) (A.isTest m l) b)
      (fun τ hτ hμτ z => hCTL (A.field m l) (A.isTest m l) b _ τ hμm0 hμm1 hshell hτ hμτ z)
      hCRR hCrt hμm0 hμm1 hshell' hc0 hc1 hμn hu0 he0 hue hε'0 hε'1 hδ'0.le
      (fun τ hτ B hB => hμ₀b j _ hμm0 (lt_of_le_of_lt hμmT hTμ) τ hτ B hB)).trans
      (add_le_add (mul_le_of_le_one_right hB0 hu1) le_rfl))) (norm_nonneg _)).trans ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  exact final_arith hθ0 hθi hj (norm_nonneg ζ) hM₁ hM₂ hM₁0 hM₂0 hN hN0 hδ' hδ'0.le hr hr0.le
    hε'0.le hε'r

end Breakdown.Periodic
