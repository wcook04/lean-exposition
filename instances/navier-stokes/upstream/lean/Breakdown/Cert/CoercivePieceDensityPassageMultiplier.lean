import Breakdown.Cert.CoerciveDensityPassagePairing
import Breakdown.Cert.CoercivePassageCommon
import Breakdown.Cert.CoerciveFrequencySeminormBound
import Breakdown.Cert.CoercivePieceField
import Breakdown.Cert.CoerciveDensityPassageLinear

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PieceDensityPassageMultiplier

open PairingSplitInternal ModeL2Internal

theorem multiplier_norm_eq (hSolenoidal : SolenoidalModeHolds) {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {M₁ M₂ : ℝ → Space → Space}
    (h₁ : m.IsMultiplierField v G H M₁) (h₂ : m.IsMultiplierField v G H M₂) :
    periodNorm M₁ = periodNorm M₂ := by
  have s1 : IsSquareField M₁ := ⟨h₁.1, h₁.2.1, h₁.2.2.1⟩
  have s2 : IsSquareField M₂ := ⟨h₂.1, h₂.2.1, h₂.2.2.1⟩
  have eD : (fun σ y => (1 : ℝ) • M₁ σ y + (-1 : ℝ) • M₂ σ y) = fun σ y => M₁ σ y - M₂ σ y := by
    funext σ y
    simp [sub_eq_add_neg]
  have hD : IsSquareField (fun σ y => M₁ σ y - M₂ σ y) := by
    have := square_lin s1 s2 1 (-1)
    rwa [eD] at this
  have hlin : ∀ Z, IsSquareField Z →
      periodPairing (fun σ y => M₁ σ y - M₂ σ y) Z = periodPairing M₁ Z - periodPairing M₂ Z := fun Z hZ => by
    rw [← eD, pairing_lin_left s1 s2 hZ 1 (-1)]
    ring
  have hDψ : ∀ ψ, IsPeriodicTestField ψ →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₁ σ y - M₂ σ y) (ψ σ y) = 0 := fun ψ hψ => by
    have := hlin ψ (testField_square hψ)
    unfold periodPairing at this
    rw [this, h₁.2.2.2.2 ψ hψ, h₂.2.2.2.2 ψ hψ, sub_self]
  have hDg : ∀ q, IsPeriodicTestPotential q →
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M₁ σ y - M₂ σ y) (gradientAt (q σ) y) = 0 := fun q hq => by
    have := hlin _ (gradient_square hq)
    unfold periodPairing at this
    rw [this, h₁.2.2.2.1 q hq, h₂.2.2.2.1 q hq, sub_self]
  have hDD := DensityPassage.pairing_eq_zero_of_orthogonal hSolenoidal hD hDψ hD hDg
  have hDM := DensityPassage.pairing_eq_zero_of_orthogonal hSolenoidal hD hDψ s2 h₂.2.2.2.1
  have hnD : periodNorm (fun σ y => M₁ σ y - M₂ σ y) ^ 2 = 0 := by
    rw [normSq_eq hD]
    rw [pairing_eq hD hD] at hDD
    simpa only [real_inner_self_eq_norm_sq] using hDD
  have hnD' : periodNorm (fun σ y => M₁ σ y - M₂ σ y) = 0 := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hnD
  have hsum := normSq_add hD s2
  rw [hnD', hDM] at hsum
  have e5 : (fun σ y => (M₁ σ y - M₂ σ y) + M₂ σ y) = M₁ := by
    funext σ y
    abel
  rw [e5] at hsum
  have hsq : periodNorm M₁ ^ 2 = periodNorm M₂ ^ 2 := by linarith
  exact (sq_eq_sq₀ (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).1 hsq

theorem iterated_sub {A B : ℝ → Space → ℝ}
    (hA : Integrable (fun z : ℝ × Space => A z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (hB : Integrable (fun z : ℝ × Space => B z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (A σ y - B σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, A σ y) - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, B σ y := by
  have hAB : Integrable (fun z : ℝ × Space => A z.1 z.2 - B z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := hA.sub hB
  rw [← integral_prod _ hA, ← integral_prod _ hB, ← integral_prod _ hAB, integral_sub hA hB]

theorem pairing_sub {A B Z : ℝ → Space → Space}
    (hA : Integrable (fun z : ℝ × Space => inner ℝ (A z.1 z.2) (Z z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (hB : Integrable (fun z : ℝ × Space => inner ℝ (B z.1 z.2) (Z z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (A σ y - B σ y) (Z σ y)) =
      (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (A σ y) (Z σ y))
        - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (B σ y) (Z σ y) := by
  simp only [inner_sub_left]
  exact iterated_sub (A := fun σ y => inner ℝ (A σ y) (Z σ y)) (B := fun σ y => inner ℝ (B σ y) (Z σ y)) hA hB

theorem multiplier_sub (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {Γ : Set Symmetry}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {u' : ℝ → Space → Space} (hu' : IsSmoothPerturbation P u')
    {M₁ M₂ : ℝ → Space → Space}
    (h₁ : m.IsMultiplierField u' (gradField u') (secondDerivField u') M₁) (h₂ : m.IsMultiplierField v G H M₂) :
    m.IsMultiplierField (fun σ y => u' σ y - v σ y) (fun σ y => gradField u' σ y - G σ y)
      (fun σ y => secondDerivField u' σ y - H σ y) (fun σ y => M₁ σ y - M₂ σ y) := by
  have hu := hSP P u' hu'
  have hD := PassageCommon.isPerturbation_sub hu hv
  have s1 : IsSquareField M₁ := ⟨h₁.1, h₁.2.1, h₁.2.2.1⟩
  have s2 : IsSquareField M₂ := ⟨h₂.1, h₂.2.1, h₂.2.2.1⟩
  have eD : (fun σ y => (1 : ℝ) • M₁ σ y + (-1 : ℝ) • M₂ σ y) = fun σ y => M₁ σ y - M₂ σ y := by
    funext σ y
    simp [sub_eq_add_neg]
  have hDs : IsSquareField (fun σ y => M₁ σ y - M₂ σ y) := by
    have := square_lin s1 s2 1 (-1)
    rwa [eD] at this
  refine ⟨h₁.1.sub h₂.1, fun σ y => ?_, hDs.2.2, fun q hq => ?_, fun ψ hψ => ?_⟩
  · show M₁ (σ + 1) y - M₂ (σ + 1) y = M₁ σ y - M₂ σ y
    rw [h₁.2.1 σ y, h₂.2.1 σ y]
  · have hg := gradient_square hq
    have i1 := Internal.Field.pairing_integrable h₁.1 hg.1 h₁.2.2.1 hg.2.2
    have i2 := Internal.Field.pairing_integrable h₂.1 hg.1 h₂.2.2.1 hg.2.2
    have e := pairing_sub (A := M₁) (B := M₂) (Z := fun σ y => gradientAt (q σ) y) i1 i2
    beta_reduce at e ⊢
    rw [e, h₁.2.2.2.1 q hq, h₂.2.2.2.1 q hq, sub_self]
  · have hT := Internal.Field.testField_aestronglyMeasurable hψ
    have hT2 := Internal.Field.testField_sq_lt_top hψ
    have i1 := Internal.Field.pairing_integrable h₁.1 hT h₁.2.2.1 hT2
    have i2 := Internal.Field.pairing_integrable h₂.1 hT h₂.2.2.1 hT2
    have hae := DensityPassageLinear.ae_period (DensityPassageLinear.ae_mode_sub hu hv)
    have key : ∀ ι : ℤ × ℤ,
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, PieceField.Internal.pieceIntegrand m (fun σ y => u' σ y - v σ y)
          (fun σ y => gradField u' σ y - G σ y) ψ ι σ y) =
        (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, PieceField.Internal.pieceIntegrand m u' (gradField u') ψ ι σ y)
          - ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, PieceField.Internal.pieceIntegrand m v G ψ ι σ y := by
      intro ι
      have j1 := PieceField.Internal.pieceIntegrand_integrable hPars hDer hRot m P h w ∅ W hm hu hψ ι
      have j2 := PieceField.Internal.pieceIntegrand_integrable hPars hDer hRot m P h w Γ W hm hv hψ ι
      have j3 := PieceField.Internal.pieceIntegrand_integrable hPars hDer hRot m P h w ∅ W hm hD hψ ι
      rw [← integral_prod _ j1, ← integral_prod _ j2, ← integral_prod _ j3, ← integral_sub j1 j2]
      refine integral_congr_ae ?_
      filter_upwards [hae] with z hz
      obtain ⟨e1, e2⟩ := hz ι
      unfold PieceField.Internal.pieceIntegrand
      rw [e1, e2, DensityPassageLinear.curlOfGrad_sub]
      simp only [DensityPassageLinear.cdot_sub_left, mul_sub, Complex.sub_re, Finset.sum_sub_distrib]
      ring
    have hsum := (PieceField.Internal.pieceIntegral_summable hPars hDer hRot m P h w ∅ W hm hu hψ).tsum_sub
      (PieceField.Internal.pieceIntegral_summable hPars hDer hRot m P h w Γ W hm hv hψ)
    have hE1 := h₁.2.2.2.2 ψ hψ
    have hE2 := h₂.2.2.2.2 ψ hψ
    have hH := DensityPassageLinear.secondDerivPart_sub hu hv hψ
    change _ = _ + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      PieceField.Internal.pieceIntegrand m (fun σ y => u' σ y - v σ y)
        (fun σ y => gradField u' σ y - G σ y) ψ ι σ y
    change _ = _ + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      PieceField.Internal.pieceIntegrand m u' (gradField u') ψ ι σ y at hE1
    change _ = _ + ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      PieceField.Internal.pieceIntegrand m v G ψ ι σ y at hE2
    have e := pairing_sub (A := M₁) (B := M₂) (Z := ψ) i1 i2
    beta_reduce
    rw [e, tsum_congr key, hsum, hE1, hE2, hH]
    ring

theorem multiplier_tendsto_of (hPars : ModeSquareSumHolds) (hDer : ModeDerivativeHolds) (hRot : ModeRotationHolds)
    (hField : PieceFieldExistsHolds) (hSolenoidal : SolenoidalModeHolds) (hSP : SmoothPerturbationIsPerturbationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ) {k : ℕ}
    (Γ : Set Symmetry) (W : ℝ → Space → Space) (act : Fin k → ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) (hWp : IsTimePeriodic W)
    (hWdiv : ∀ σ y, divergenceAt (W σ) y = 0)
    (hWdecay : ∃ D, ∀ σ y, ∀ j ≤ 2, ‖iteratedFDeriv ℝ j (W σ) y‖ ≤ D / (1 + ‖y‖) ^ (j + 1))
    (hwb : ∃ B, ∀ y, w y ≤ B)
    (hactm : ∀ i, AEStronglyMeasurable (fun z : ℝ × Space => act i z.1 z.2) volume)
    (hactp : ∀ i, IsTimePeriodic (act i))
    (hact2 : ∀ i, periodLIntegral (fun σ y => ‖act i σ y‖ ^ 2) < ⊤)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (u : ℕ → ℝ → Space → Space) (hv : IsPerturbation Γ P v G H g) (hu : IsSmoothApproximation P v G H g u)
    (κ : Fin k → ℝ) (F M : ℝ → Space → Space)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hR : IsRightSide W act κ v G g F)
    (hMF : m.IsMultiplierField v G H M)
    (Mn : ℕ → ℝ → Space → Space)
    (hMn : ∀ n, m.IsMultiplierField (u n) (gradField (u n)) (secondDerivField (u n)) (Mn n)) :
    Tendsto (fun n => periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2)) atTop (𝓝 0) := by
  have hpd := fun n => PassageCommon.difference_isPerturbation hSP hv hu n
  have hex := fun n => (hField m P h w ∅ W hm hwb _ _ _ _ (hpd n)).2
  choose M' hM' hMb using hex
  have hsub := fun n => multiplier_sub hPars hDer hRot hSP m P h w W hm hv (hu.1 n) (hMn n) hMF
  have heq : ∀ n, periodNorm (fun σ y => Mn n σ y - M σ y) = periodNorm (M' n) := fun n =>
    multiplier_norm_eq hSolenoidal (hsub n) (hM' n)
  set K : ℝ := Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ) with hK
  set e : ℕ → ℝ := fun n => m.c * weightedEnergy w (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y) + m.cμ * (m.seminormSq P (fun σ y => u n σ y - v σ y)).toReal with he
  have he0 : ∀ n, 0 ≤ e n := fun n =>
    add_nonneg (mul_nonneg hm.c_pos.le ENNReal.toReal_nonneg) (mul_nonneg hm.cμ_pos.le ENNReal.toReal_nonneg)
  have hb : ∀ n, periodNorm (fun σ y => Mn n σ y - M σ y) ^ 2 ≤ K ^ 2 * e n := fun n => by
    rw [heq n]
    have h1 := hMb n
    have h0 : 0 ≤ periodNorm (M' n) := Real.sqrt_nonneg _
    calc periodNorm (M' n) ^ 2 ≤ (K * Real.sqrt (e n)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = K ^ 2 * e n := by rw [mul_pow, Real.sq_sqrt (he0 n)]
  obtain ⟨Bw, hBw⟩ := hwb
  have hw0 : ∀ y, 0 ≤ w y := fun y => hm.weight_pos.le.trans (hm.weight_lower y)
  have hBw0 : 0 ≤ Bw := (hw0 0).trans (hBw 0)
  have hpn := fun n => hSP P (u n) (hu.1 n)
  have hE : Tendsto (fun n => periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField (u n) σ y - H σ y)‖ ^ 2
      + w y * matSq (gradField (u n) σ y - G σ y))) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => ENNReal.ofReal 3 * periodLIntegral (fun σ y => secondDerivSq (secondDerivField (u n) σ y - H σ y))
        + ENNReal.ofReal Bw * periodLIntegral (fun σ y => matSq (gradField (u n) σ y - G σ y))) atTop (𝓝 0) := by
      have := (ENNReal.Tendsto.const_mul hu.2.2.1 (Or.inr (ENNReal.ofReal_ne_top (r := 3)))).add
        (ENNReal.Tendsto.const_mul hu.2.1 (Or.inr (ENNReal.ofReal_ne_top (r := Bw))))
      simpa using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun _ => zero_le) fun n => ?_
    have m1 : AEMeasurable (fun z : ℝ × Space => 3 * secondDerivSq (secondDerivField (u n) z.1 z.2 - H z.1 z.2)) volume :=
      ((PassageLimit.continuous_secondDerivSq.comp_aestronglyMeasurable
        ((hpn n).measurable_secondDeriv.sub hv.measurable_secondDeriv)).aemeasurable).const_mul 3
    have m2 : AEMeasurable (fun z : ℝ × Space => Bw * matSq (gradField (u n) z.1 z.2 - G z.1 z.2)) volume :=
      ((PassageCommon.continuous_matSq.comp_aestronglyMeasurable
        ((hpn n).measurable_gradient.sub hv.measurable_gradient)).aemeasurable).const_mul Bw
    calc periodLIntegral (fun σ y => ‖secondDerivTrace (secondDerivField (u n) σ y - H σ y)‖ ^ 2
          + w y * matSq (gradField (u n) σ y - G σ y))
        ≤ periodLIntegral (fun σ y => 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y)
          + Bw * matSq (gradField (u n) σ y - G σ y)) := PassageLimit.periodLIntegral_mono fun σ y =>
            add_le_add (PassageLimit.traceSq_le_three_secondDerivSq _)
              (mul_le_mul_of_nonneg_right (hBw y) (PassageCommon.matSq_nonneg _))
      _ = periodLIntegral (fun σ y => 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y))
          + periodLIntegral (fun σ y => Bw * matSq (gradField (u n) σ y - G σ y)) :=
          PassageLimit.periodLIntegral_add (f := fun σ y => 3 * secondDerivSq (secondDerivField (u n) σ y - H σ y))
            (g := fun σ y => Bw * matSq (gradField (u n) σ y - G σ y)) m1 m2
            (fun σ y => mul_nonneg (by norm_num) (PassageLimit.secondDerivSq_nonneg _))
            (fun σ y => mul_nonneg hBw0 (PassageCommon.matSq_nonneg _))
      _ ≤ _ := add_le_add (PassageLimit.periodLIntegral_le_mul (by norm_num) fun σ y => le_refl _)
          (PassageLimit.periodLIntegral_le_mul hBw0 fun σ y => le_refl _)
  have hEr : Tendsto (fun n => weightedEnergy w (fun σ y => gradField (u n) σ y - G σ y)
      (fun σ y => secondDerivField (u n) σ y - H σ y)) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    simpa [Function.comp_def, weightedEnergy] using this
  obtain ⟨Bm, hBm⟩ := hm.mu_decay
  have hS := (FrequencyBound.pieceSeminormSq_tendsto_of_approximation m hPars hDer hRot hSP hv
    hm.period_pos hm.mu_wt_nonneg (fun β y => ⟨(hBm β y).1, (hBm β y).2.1⟩)
    (fun β => let ⟨_, hK⟩ := hm.mu_increment β; hK.continuous.measurable) hu).1
  have hSr : Tendsto (fun n => (m.seminormSq P (fun σ y => u n σ y - v σ y)).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hS
    simpa [Function.comp_def] using this
  have hEt : Tendsto e atTop (𝓝 0) := by
    have := (hEr.const_mul m.c).add (hSr.const_mul m.cμ)
    simpa [he] using this
  have hKt : Tendsto (fun n => ENNReal.ofReal (K ^ 2 * e n)) atTop (𝓝 0) := by
    have := ENNReal.tendsto_ofReal (hEt.const_mul (K ^ 2))
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hKt (fun _ => zero_le) fun n => ?_
  have hfin := (hsub n).2.2.1
  have hL : periodLIntegral (fun σ y => ‖Mn n σ y - M σ y‖ ^ 2) =
      ENNReal.ofReal (periodNorm (fun σ y => Mn n σ y - M σ y) ^ 2) := by
    unfold periodNorm
    rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hfin.ne]
  rw [hL]
  exact ENNReal.ofReal_le_ofReal (hb n)

end Internal.PieceDensityPassageMultiplier

end Coercive

end Breakdown
