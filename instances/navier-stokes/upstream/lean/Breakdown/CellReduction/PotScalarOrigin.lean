import Breakdown.CellReduction.PotScalarOriginAngular

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Breakdown

namespace PotentialShape

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline heightRatio weightPoly)

namespace ScalarOrigin

namespace Internal

theorem assemble_eq {a b c g W T R s2 : ℂ} (h : W * T = s2 * R) :
    a * b * W * c * (T * g) = s2 * (R * a * (b * c * g)) := by
  linear_combination (a * b * c * g) * h

end Internal

end ScalarOrigin

open ScalarOrigin.Internal

theorem scalarValue_origin_bounds (P : ShapeParams) (κ : FieldKey) (M : ℤ) (ws : Bool) (S : PotScalar) (σ : ℝ)
    (hP : IsShapeParams P) (hc : IsJetClass 1 1 S.amp) (hadm : AxisAdmissible M ws S)
    (hzs : ∃ z ≤ S.amp.tAxis.depth, 2 ≤ S.lowOrder + z ∧ StartVanishOrder S.amp z) :
    HasFDerivAt (scalarValue P κ M ws S σ) (0 : Space →L[ℝ] ℂ) 0 ∧ ∃ δ > (0 : ℝ), ∃ C : ℝ,
      (∀ y ∈ Metric.ball (0 : Space) δ, DifferentiableAt ℝ (scalarValue P κ M ws S σ) y ∧
        ‖scalarValue P κ M ws S σ y‖ ≤ C * ‖y‖ ^ 2 ∧ ‖fderiv ℝ (scalarValue P κ M ws S σ) y‖ ≤ C * ‖y‖) ∧
      ∃ K : NNReal, LipschitzOnWith K (fderiv ℝ (scalarValue P κ M ws S σ)) (Metric.ball 0 δ) := by
  obtain ⟨z, hz, hzl, hv⟩ := hzs
  obtain ⟨G, hG, ht1, hfac, hvan⟩ := start_quotient S.amp hc hz hv
  have hL : 0 < P.chartLength := hP.chartLength_pos
  set t1 := S.amp.tAxis.breaks.getD 1 0 with ht1d
  set r0 := P.chartLength * t1 with hr0
  have hr0p : 0 < r0 := mul_pos hL ht1
  set k := S.lowOrder + z - 2 with hk
  have hkz : S.lowOrder + z = k + 2 := by omega
  set ell : ℝ × Space → ℝ := fun p => ‖p.2‖ / (p.1 * ‖p.2‖ + P.chartLength) with hell
  set F : ℝ × Space → ℂ := fun p =>
    ((p.1 ^ k * ell p ^ S.lowOrder * ell p ^ z * (1 - p.1 * ell p) ^ S.highOrder : ℝ) : ℂ) *
      Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
        (κ.phaseIndex : ℝ) * P.radialPhase (p.1 ^ 2 * ‖p.2‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
      (angular M ws S.axisPower p.2 * G.evalHalf (p.1 * ell p) (heightRatio p.2)) with hF
  have hf0 : scalarValue P κ M ws S σ 0 = 0 := by
    have hc0 : chartCoord P 0 = 0 := by simp [chartCoord]
    unfold scalarValue
    rw [hc0, hfac 0 _ ht1]
    rcases Nat.eq_zero_or_pos S.lowOrder with he | he
    · have hz2 : z ≠ 0 := by omega
      simp [hz2]
    · simp [weightPoly, he.ne']
  have hscale : ∀ s : ℝ, 0 < s → ∀ v : Space, v ≠ 0 → s * ‖v‖ < r0 →
      scalarValue P κ M ws S σ (s • v) = (s ^ 2) • F (s, v) := by
    intro s hs v hv hsv
    have hn : ‖s • v‖ = s * ‖v‖ := by rw [norm_smul, Real.norm_of_nonneg hs.le]
    have hτ : chartCoord P (s • v) = s * ell (s, v) := by
      simp only [chartCoord, hn, hell]
      rw [mul_div_assoc]
    have hτ1 : chartCoord P (s • v) < t1 := by
      rw [chartCoord, hn, div_lt_iff₀ (add_pos (mul_pos hs (norm_pos_iff.2 hv)) hL)]
      have h1 : 0 ≤ t1 * (s * ‖v‖) := mul_nonneg ht1.le (mul_nonneg hs.le (norm_nonneg _))
      nlinarith
    have hexp : Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ + (M : ℝ) * pointAngle v +
          (κ.phaseIndex : ℝ) * P.radialPhase (s ^ 2 * ‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
          (κ.phaseIndex : ℝ) * P.radialPhase (s ^ 2 * ‖v‖ ^ 2) : ℝ) : ℂ) * Complex.I) *
        Complex.exp ((((M : ℝ) * pointAngle v : ℝ) : ℂ) * Complex.I) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hWT : weightPoly S.lowOrder S.highOrder (s * ell (s, v)) * ((s * ell (s, v) : ℝ) : ℂ) ^ z =
        ((s ^ 2 : ℝ) : ℂ) * ((s ^ k * ell (s, v) ^ S.lowOrder * ell (s, v) ^ z *
          (1 - s * ell (s, v)) ^ S.highOrder : ℝ) : ℂ) := by
      rw [weightPoly, ← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_mul]
      congr 1
      have hp : s ^ S.lowOrder * s ^ z = s ^ 2 * s ^ k := by
        rw [← pow_add, hkz, pow_add, mul_comm]
      calc (s * ell (s, v)) ^ S.lowOrder * (1 - s * ell (s, v)) ^ S.highOrder * (s * ell (s, v)) ^ z
          = (s ^ S.lowOrder * s ^ z) * (ell (s, v) ^ S.lowOrder * ell (s, v) ^ z *
              (1 - s * ell (s, v)) ^ S.highOrder) := by ring
        _ = (s ^ 2 * s ^ k) * (ell (s, v) ^ S.lowOrder * ell (s, v) ^ z *
              (1 - s * ell (s, v)) ^ S.highOrder) := by rw [hp]
        _ = s ^ 2 * (s ^ k * ell (s, v) ^ S.lowOrder * ell (s, v) ^ z *
              (1 - s * ell (s, v)) ^ S.highOrder) := by ring
    unfold scalarValue
    rw [heightRatio_smul hs, pointAngle_smul hs, polarSine_smul hs, hfac _ _ hτ1, hτ, hn,
      show (s * ‖v‖) ^ 2 = s ^ 2 * ‖v‖ ^ 2 by ring, hexp, Complex.real_smul, hF]
    simp only [angular]
    exact assemble_eq hWT
  have htame : ∀ p ∈ Set.Icc 0 (r0 / 2) ×ˢ (Metric.closedBall (0 : Space) 1 \ Metric.ball 0 (1 / 2)),
      TameNear F p := by
    rintro ⟨s0, v0⟩ ⟨⟨hs0, -⟩, -, hvn⟩
    have hv0 : v0 ≠ 0 := by
      rintro rfl
      exact hvn (Metric.mem_ball_self (by norm_num))
    have hden : s0 * ‖v0‖ + P.chartLength ≠ 0 :=
      (add_pos_of_nonneg_of_pos (mul_nonneg hs0 (norm_nonneg _)) hL).ne'
    have hn : ContDiffAt ℝ 2 (fun q : ℝ × Space => ‖q.2‖) (s0, v0) :=
      (contDiffAt_norm ℝ hv0).comp (s0, v0) contDiffAt_snd
    have hell' : ContDiffAt ℝ 2 ell (s0, v0) := hn.div ((contDiffAt_fst.mul hn).add contDiffAt_const) hden
    have hR : ContDiffAt ℝ 2 (fun q : ℝ × Space => q.1 ^ k * ell q ^ S.lowOrder * ell q ^ z *
        (1 - q.1 * ell q) ^ S.highOrder) (s0, v0) :=
      (((contDiffAt_fst.pow k).mul (hell'.pow _)).mul (hell'.pow _)).mul
        ((contDiffAt_const.sub (contDiffAt_fst.mul hell')).pow _)
    obtain ⟨δ, hδ, hph⟩ := hP.phase.smooth
    have hsq : ContDiffAt ℝ 2 (fun q : ℝ × Space => q.1 ^ 2 * ‖q.2‖ ^ 2) (s0, v0) :=
      (contDiffAt_fst.pow 2).mul (((contDiff_norm_sq ℝ).contDiffAt).comp (s0, v0) contDiffAt_snd)
    have hmem : s0 ^ 2 * ‖v0‖ ^ 2 ∈ Set.Ioi (-δ) := by
      rw [Set.mem_Ioi]
      have : 0 ≤ s0 ^ 2 * ‖v0‖ ^ 2 := by positivity
      linarith
    have hphase : ContDiffAt ℝ 2 P.radialPhase (s0 ^ 2 * ‖v0‖ ^ 2) :=
      (hph.contDiffAt (isOpen_Ioi.mem_nhds hmem)).of_le (by norm_num)
    have hE : ContDiffAt ℝ 2 (fun q : ℝ × Space => Complex.exp (((2 * Real.pi * (labelTime κ.label : ℝ) * σ +
        (κ.phaseIndex : ℝ) * P.radialPhase (q.1 ^ 2 * ‖q.2‖ ^ 2) : ℝ) : ℂ) * Complex.I)) (s0, v0) :=
      Complex.contDiff_exp.contDiffAt.comp (s0, v0)
        ((ofReal_contDiffAt (contDiffAt_const.add (contDiffAt_const.mul (hphase.comp (s0, v0) hsq)))).mul
          contDiffAt_const)
    have hΨ : ContDiffAt ℝ 2 (fun q : ℝ × Space => (q.1 * ell q, heightRatio q.2)) (s0, v0) :=
      (contDiffAt_fst.mul hell').prodMk ((heightRatio_contDiffAt hv0).comp (s0, v0) contDiffAt_snd)
    have hGt : TameNear (fun q : ℝ × Space => G.evalHalf (q.1 * ell q) (heightRatio q.2)) (s0, v0) :=
      tameNear_comp (g := fun w : ℝ × ℝ => G.evalHalf w.1 w.2)
        (Φ := fun q : ℝ × Space => (q.1 * ell q, heightRatio q.2)) (p := (s0, v0))
        (spline_tame hG ((s0 * ell (s0, v0), heightRatio v0))) (tameNear_of_contDiffAt hΨ)
    have hvan' : AxisCellsVanish S.amp → planeOfPoint v0 = 0 →
        (fun q : ℝ × Space => G.evalHalf (q.1 * ell q) (heightRatio q.2)) =ᶠ[𝓝 (s0, v0)] 0 := by
      intro hax hw
      obtain ⟨h1, h2⟩ := hvan hax
      have hct0 : ContDiffAt ℝ 2 (fun q : ℝ × Space => heightRatio q.2) (s0, v0) :=
        (heightRatio_contDiffAt hv0).comp (s0, v0) contDiffAt_snd
      have hct : ContinuousAt (fun q : ℝ × Space => heightRatio q.2) (s0, v0) := hct0.continuousAt
      have hx : ∀ᶠ x in 𝓝 (heightRatio v0), ∀ τ, G.evalHalf τ x = 0 := by
        rcases heightRatio_axis hv0 hw with h | h
        · rw [h]
          exact h1
        · rw [h]
          exact h2
      filter_upwards [Filter.Tendsto.eventually hct hx] with q hq
      exact hq _
    exact tameNear_mul (tameNear_mul (tameNear_of_contDiffAt (ofReal_contDiffAt hR)) (tameNear_of_contDiffAt hE))
      (angular_prod_tame hadm hv0 hGt hvan')
  obtain ⟨hd0, C, hC, K, hK⟩ := origin_of_scaling (f := scalarValue P κ M ws S σ) (F := F)
    (half_pos hr0p) (by linarith) hf0 hscale htame
  exact ⟨hd0, r0 / 2, half_pos hr0p, C, hC, K, hK⟩

theorem scalarSmoothNearOrigin : ScalarSmoothNearOrigin := by
  intro P κ M ws S σ hP hc hadm hzs
  obtain ⟨-, δ, hδ, C, hC, K, hK⟩ := scalarValue_origin_bounds P κ M ws S σ hP hc hadm hzs
  refine ⟨?_, δ / 2, half_pos hδ, K, hK.mono (Metric.closedBall_subset_ball (by linarith))⟩
  have hdiffOn : DifferentiableOn ℝ (scalarValue P κ M ws S σ) (Metric.ball 0 δ) :=
    fun y hy => (hC y hy).1.differentiableWithinAt
  have hcd : ContDiffOn ℝ 1 (scalarValue P κ M ws S σ) (Metric.ball 0 δ) := by
    have h := (contDiffOn_succ_iff_fderiv_of_isOpen (𝕜 := ℝ) (n := 0) (f := scalarValue P κ M ws S σ)
      Metric.isOpen_ball).2 ⟨hdiffOn, by simp, contDiffOn_zero.2 hK.continuousOn⟩
    simpa using h
  exact hcd.contDiffAt (Metric.ball_mem_nhds 0 hδ)

end PotentialShape

end Breakdown
