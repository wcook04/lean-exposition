import TorusEuler.TerminalCoefficientTimeProduct
import TorusEuler.TerminalTransverseCoefficients
import TorusEuler.TerminalCoefficientTimeNorms

/-! The old-parent mixed bounds of the four coefficients of the selected transverse equation. -/

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

private theorem terminalMixedJetBound_constant {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {q p : ℕ} {D : ℝ} (hD : 1 ≤ D) (v : E) :
    TerminalMixedJetBound 0 T q p D 1 (fun _ => ‖v‖) (fun _ _ => v) := by
  intro i _ n t _ x
  have heq : slabTimeJet 0 T i (fun _ _ => v) t = (fun _ => if i = 0 then v else 0) :=
    funext fun _ => iteratedDerivWithin_const
  rw [heq]
  cases n with
  | zero => by_cases hi : i = 0 <;> simp [norm_iteratedFDeriv_zero, hi]
  | succ n =>
    rw [iteratedFDeriv_const_of_ne (by omega)]
    simpa only [Pi.zero_apply, norm_zero, mul_one] using
      mul_nonneg (norm_nonneg v) (pow_nonneg (zero_le_one.trans hD) (p * (n + 1)))

local notation "End" => (Vec3 →L[ℝ] Vec3)
local notation "Row" => (Vec3 →L[ℝ] ℝ)
local notation "MP" => HierarchyTwistedProfile T k End
local notation "VP" => HierarchyTwistedProfile T k Vec3

private def terminalRankOne : Vec3 →L[ℝ] Vec3 →L[ℝ] End :=
  (ContinuousLinearMap.smulRightL ℝ Vec3 Vec3).comp (innerSL ℝ)

private theorem terminalRankOne_eq (v : Vec3) :
    terminalRankOne v v = InnerProductSpace.rankOne ℝ v v := rfl

private theorem affineWaveAmplitudeOperator_split (M : End) (κ : Vec3) :
    affineWaveAmplitudeOperator M κ =
      -M + (2 : ℝ) • ((((‖κ‖ ^ 2)⁻¹ : ℝ) • InnerProductSpace.rankOne ℝ κ κ).comp M) := by
  ext v
  simp only [affineWaveAmplitudeOperator, add_apply, neg_apply,
    ContinuousLinearMap.comp_apply, _root_.smul_apply, smul_smul, div_eq_mul_inv]

private theorem terminalCoefficient_bilinear_smooth {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    {s : Set (ℝ × Vec3)} {f : ℝ → Vec3 → E} {g : ℝ → Vec3 → F}
    (B : E →L[ℝ] F →L[ℝ] G)
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) s) (hg : ContDiffOn ℝ ∞ (Function.uncurry g) s) :
    ContDiffOn ℝ ∞ (Function.uncurry (fun t x => B (f t x) (g t x))) s := by
  have hB : ContDiff ℝ ∞ (fun u : E => B u) := ContinuousLinearMap.contDiff B
  exact (hB.comp_contDiffOn hf).clm_apply hg

set_option maxHeartbeats 2200000 in
/-- One old-parent power bounds all four actual coefficients. The cost is
chosen before the carrier, slab, or stage and depends on the two derivative orders. -/
theorem exists_transverseTimeCoefficientBounds
    (q : ℕ) (CM Cκ CQ : ℕ → ℝ)
    (hCM : ∀ j, 0 ≤ CM j) (hCκ : ∀ j, 0 ≤ Cκ j) (hCQ : ∀ j, 0 ≤ CQ j) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {T : ℝ} {k : Vec3} {M : HierarchyTwistedProfile T k End}
        {κ : HierarchyTwistedProfile T k Vec3}
        (d : TransverseCoefficients M κ) {freq D ℓ h : ℝ}
        (hT : 0 < T) (_hT₁ : T ≤ 1) (hfreq : freq ≠ 0) (_hD : 1 ≤ D) (_hℓ : 0 ≤ ℓ)
        {p eM eκ eQ : ℕ}, ℓ * D ^ p ≤ 1 →
        (let θ (t : ℝ) (x : Vec3) := freq⁻¹ • d.covector t x
         TerminalMixedJetBound 0 T q p D (D ^ eM) CM d.strain →
         TerminalMixedJetBound 0 T q p D (D ^ eκ) Cκ θ →
         TerminalMixedJetBound 0 T q p D (D ^ eQ) CQ (fun t x => (‖θ t x‖ ^ 2)⁻¹) →
         let E := eM + 2 * eκ + eQ
         TerminalMixedJetBound 0 T q p D (D ^ E) C
           (fun t x => affineWaveAmplitudeOperator (d.strain t x) (d.covector t x)) ∧
         TerminalMixedJetBound 0 T q p D (D ^ E) C
           (fun t x => hierarchyRelayPressureAmplitudeCoefficient (d.strain t x) (θ t x)) ∧
         ∀ n : ℕ, let coef := d.timeCoefficients freq hfreq
           let N := unweightedSeminorm (E := End) (k := k) False ℓ h n hT
           let NP := unweightedSeminorm (E := Row) (k := k) False ℓ h n hT
           let B := C n * D ^ E
           timeJetSeminorm hT q N coef.velocity ≤ B ∧
             timeJetSeminorm hT q N coef.source ≤ B ∧
             timeJetSeminorm hT q NP coef.pressureVelocity ≤ B ∧
             timeJetSeminorm hT q NP coef.pressureSource ≤ B) := by
  let actionEnd : ℝ →L[ℝ] End →L[ℝ] End := lsmul ℝ ℝ
  let actionRow : ℝ →L[ℝ] Row →L[ℝ] Row := lsmul ℝ ℝ
  let compEnd : End →L[ℝ] End →L[ℝ] End := compL ℝ Vec3 Vec3 Vec3
  let compRow : Row →L[ℝ] End →L[ℝ] Row := compL ℝ Vec3 Vec3 ℝ
  let neg : End →L[ℝ] End := -(ContinuousLinearMap.id ℝ End)
  let twice : End →L[ℝ] End := (2 : ℝ) • ContinuousLinearMap.id ℝ End
  let minusTwice : Row →L[ℝ] Row := (-2 : ℝ) • ContinuousLinearMap.id ℝ Row
  let L : Vec3 →L[ℝ] Row := innerSL ℝ
  let Cconst : ℕ → ℝ := fun _ => ‖ContinuousLinearMap.id ℝ Vec3‖
  let Crank := terminalMixedProductCost q terminalRankOne Cκ Cκ
  let Cproj := terminalMixedProductCost q actionEnd CQ Crank
  let Ccomp := terminalMixedProductCost q compEnd Cproj CM
  let Cline (j : ℕ) := ‖L‖ * Cκ j
  let ClineM := terminalMixedProductCost q compRow Cline CM
  let CpressV := terminalMixedProductCost q actionRow CQ ClineM
  let CpressF := terminalMixedProductCost q actionRow CQ Cline
  let CA (j : ℕ) := ‖neg‖ * CM j + ‖twice‖ * Ccomp j
  let CB (j : ℕ) := Cconst j + ‖neg‖ * Cproj j
  let CP (j : ℕ) := ‖minusTwice‖ * CpressV j
  let CS := CpressF
  have hConst (j : ℕ) : 0 ≤ Cconst j := norm_nonneg _
  have hRank := terminalMixedProductCost_nonneg q terminalRankOne hCκ hCκ
  have hProj := terminalMixedProductCost_nonneg q actionEnd hCQ hRank
  have hComp := terminalMixedProductCost_nonneg q compEnd hProj hCM
  have hLine (j : ℕ) : 0 ≤ Cline j := mul_nonneg (norm_nonneg L) (hCκ j)
  have hLineM := terminalMixedProductCost_nonneg q compRow hLine hCM
  have hPressV := terminalMixedProductCost_nonneg q actionRow hCQ hLineM
  have hPressF := terminalMixedProductCost_nonneg q actionRow hCQ hLine
  have hCA (j : ℕ) : 0 ≤ CA j :=
    add_nonneg (mul_nonneg (norm_nonneg neg) (hCM j)) (mul_nonneg (norm_nonneg twice) (hComp j))
  have hCB (j : ℕ) : 0 ≤ CB j := add_nonneg (hConst j) (mul_nonneg (norm_nonneg neg) (hProj j))
  have hCP (j : ℕ) : 0 ≤ CP j := mul_nonneg (norm_nonneg minusTwice) (hPressV j)
  have hCS (j : ℕ) : 0 ≤ CS j := hPressF j
  let Cnorm (n : ℕ) := max (max (terminalLabelTimeSeminormCost CA q n) (terminalLabelTimeSeminormCost CB q n))
    (max (terminalLabelTimeSeminormCost CP q n) (terminalLabelTimeSeminormCost CS q n))
  let C (n : ℕ) := max (max (CA n) (CP n)) (Cnorm n)
  refine ⟨C, fun n => (hCA n).trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro T k M κ d freq D ℓ h hT hT₁ hfreq hD hℓ p eM eκ eQ hscale θ Mjets κjets Qjets E
  let domain := Icc (0 : ℝ) T ×ˢ (univ : Set Vec3)
  let invQ (t : ℝ) (x : Vec3) := (‖θ t x‖ ^ 2)⁻¹
  let R (t : ℝ) (x : Vec3) := terminalRankOne (θ t x) (θ t x)
  let proj (t : ℝ) (x : Vec3) := actionEnd (invQ t x) (R t x)
  let comp (t : ℝ) (x : Vec3) := compEnd (proj t x) (d.strain t x)
  let line (t : ℝ) (x : Vec3) := L (θ t x)
  let lineM (t : ℝ) (x : Vec3) := compRow (line t x) (d.strain t x)
  let pressV (t : ℝ) (x : Vec3) := actionRow (invQ t x) (lineM t x)
  let pressF (t : ℝ) (x : Vec3) := actionRow (invQ t x) (line t x)
  have hD₀ := zero_le_one.trans hD
  have hpow (j : ℕ) : 0 ≤ D ^ j := pow_nonneg hD₀ _
  have hM := d.strain_smooth
  have hθ : ContDiffOn ℝ ∞ (Function.uncurry θ) domain := d.covector_smooth.const_smul _
  have hQ : ContDiffOn ℝ ∞ (Function.uncurry invQ) domain := by
    refine (hθ.norm_sq ℝ).inv fun z hz => pow_ne_zero _ (norm_ne_zero_iff.mpr ?_)
    apply smul_ne_zero (inv_ne_zero hfreq)
    have hκ := d.covector_ne_zero z.1 hz.1 z.2
    rwa [d.covector_value _ ⟨hz.1, mem_univ _⟩] at hκ
  have hR : ContDiffOn ℝ ∞ (Function.uncurry R) domain :=
    terminalCoefficient_bilinear_smooth terminalRankOne hθ hθ
  have hP : ContDiffOn ℝ ∞ (Function.uncurry proj) domain :=
    terminalCoefficient_bilinear_smooth actionEnd hQ hR
  have hCompReg : ContDiffOn ℝ ∞ (Function.uncurry comp) domain :=
    terminalCoefficient_bilinear_smooth compEnd hP hM
  have hLineReg : ContDiffOn ℝ ∞ (Function.uncurry line) domain := L.contDiff.comp_contDiffOn hθ
  have hLineMReg : ContDiffOn ℝ ∞ (Function.uncurry lineM) domain :=
    terminalCoefficient_bilinear_smooth compRow hLineReg hM
  have hPVReg : ContDiffOn ℝ ∞ (Function.uncurry pressV) domain :=
    terminalCoefficient_bilinear_smooth actionRow hQ hLineMReg
  have Rjets := TerminalMixedJetBound.bilinear terminalRankOne hT hD₀ (hpow eκ) (hpow eκ)
    hCκ hCκ κjets κjets hθ hθ
  have Pjets := TerminalMixedJetBound.bilinear actionEnd hT hD₀ (hpow eQ)
    (mul_nonneg (hpow eκ) (hpow eκ)) hCQ hRank Qjets Rjets hQ hR
  have Cjets := TerminalMixedJetBound.bilinear compEnd hT hD₀
    (mul_nonneg (hpow eQ) (mul_nonneg (hpow eκ) (hpow eκ))) (hpow eM)
    hProj hCM Pjets Mjets hP hM
  have lineJets := κjets.apply_clm hT hθ L
  have lineMJets := TerminalMixedJetBound.bilinear compRow hT hD₀
    (hpow eκ) (hpow eM) hLine hCM lineJets Mjets hLineReg hM
  have PVjets := TerminalMixedJetBound.bilinear actionRow hT hD₀
    (hpow eQ) (mul_nonneg (hpow eκ) (hpow eM)) hCQ hLineM Qjets lineMJets hQ hLineMReg
  have PFjets := TerminalMixedJetBound.bilinear actionRow hT hD₀
    (hpow eQ) (hpow eκ) hCQ hLine Qjets lineJets hQ hLineReg
  have hAE : 0 ≤ D ^ E := hpow E
  have hME : D ^ eM ≤ D ^ E := pow_le_pow_right₀ hD (by dsimp [E]; omega)
  have hPE : D ^ eQ * (D ^ eκ * D ^ eκ) ≤ D ^ E := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hD (by dsimp [E]; omega)
  have hCE : (D ^ eQ * (D ^ eκ * D ^ eκ)) * D ^ eM ≤ D ^ E := by
    rw [← pow_add, ← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hD (by dsimp [E]; omega)
  have hPVE : D ^ eQ * (D ^ eκ * D ^ eM) ≤ D ^ E := by
    rw [← pow_add, ← pow_add]
    exact pow_le_pow_right₀ hD (by dsimp [E]; omega)
  have hPFE : D ^ eQ * D ^ eκ ≤ D ^ E := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hD (by dsimp [E]; omega)
  have hNegM := ((Mjets.mono_amplitude hD₀ hCM hME).apply_clm hT hM neg)
  have hTwiceComp := ((Cjets.mono_amplitude hD₀ hComp hCE).apply_clm hT hCompReg twice)
  have hNegProj := ((Pjets.mono_amplitude hD₀ hProj hPE).apply_clm hT hP neg)
  have hId : TerminalMixedJetBound 0 T q p D (D ^ E) Cconst
      (fun _ _ => ContinuousLinearMap.id ℝ Vec3) :=
    (terminalMixedJetBound_constant (T := T) (q := q) (p := p) hD
      (ContinuousLinearMap.id ℝ Vec3)).mono_amplitude hD₀ hConst (one_le_pow₀ hD)
  have hAjets := hNegM.add hTwiceComp hT (neg.contDiff.comp_contDiffOn hM)
    (twice.contDiff.comp_contDiffOn hCompReg)
  have hBjets := hId.add hNegProj hT contDiffOn_const (neg.contDiff.comp_contDiffOn hP)
  have hPVjets := (PVjets.mono_amplitude hD₀ hPressV hPVE).apply_clm hT hPVReg minusTwice
  have hPFjets := PFjets.mono_amplitude hD₀ hPressF hPFE
  have hproj_eq (t : ℝ) (x : Vec3) :
      proj t x = (‖d.covector t x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (d.covector t x) (d.covector t x) := by
    change (‖θ t x‖ ^ 2)⁻¹ • terminalRankOne (θ t x) (θ t x) = _
    rw [terminalRankOne_eq]
    exact rankOne_directionProjection_smul (d.covector t x) (inv_ne_zero hfreq)
  have hAeq (t : ℝ) (x : Vec3) :
      neg (d.strain t x) + twice (comp t x) = affineWaveAmplitudeOperator (d.strain t x) (d.covector t x) := by
    change -d.strain t x + (2 : ℝ) • (proj t x).comp (d.strain t x) = _
    rw [hproj_eq, affineWaveAmplitudeOperator_split]
  have hPVeq (t : ℝ) (x : Vec3) :
      minusTwice (pressV t x) = hierarchyRelayPressureAmplitudeCoefficient (d.strain t x) (θ t x) := by
    change (-2 : ℝ) • ((‖θ t x‖ ^ 2)⁻¹ • (innerSL ℝ (θ t x)).comp (d.strain t x)) = _
    rw [smul_smul, hierarchyRelayPressureAmplitudeCoefficient]
  have hCA_le (j : ℕ) : CA j ≤ C j := (le_max_left _ _).trans (le_max_left _ _)
  have hCP_le (j : ℕ) : CP j ≤ C j := (le_max_right _ _).trans (le_max_left _ _)
  refine ⟨(hAjets.mono_constant hD₀ hAE hCA_le).congr
      (fun t _ x => hAeq t x),
    (hPVjets.mono_constant hD₀ hAE hCP_le).congr
      (fun t _ x => hPVeq t x), ?_⟩
  intro n coef N NP B
  have hAval (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
      coef.velocity.val.val.val (t, x, s) = neg (d.strain t x) + twice (comp t x) :=
    (coef.velocity_value t ht x s).trans (hAeq t x).symm
  have hBval (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
      coef.source.val.val.val (t, x, s) = ContinuousLinearMap.id ℝ Vec3 + neg (proj t x) := by
    rw [coef.source_value t ht x s, oscillatoryTransverseProjection, sub_eq_add_neg]
    change _ = ContinuousLinearMap.id ℝ Vec3 + -(proj t x)
    rw [hproj_eq]
  have hPVval (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
      coef.pressureVelocity.val.val.val (t, x, s) = minusTwice (pressV t x) :=
    (coef.pressureVelocity_value t ht x s).trans (hPVeq t x).symm
  have hPFval (t : ℝ) (ht : t ∈ Icc 0 T) (x : Vec3) (s : ℝ) :
      coef.pressureSource.val.val.val (t, x, s) = pressF t x :=
    coef.pressureSource_value t ht x s
  have hAn := unweighted_timeJetSeminorm_le_of_labelMixedJetBound (h := h) hT hT₁ hℓ hD₀ hAE hscale
    coef.velocity (fun z hz => hAval z.1 hz.1 z.2.1 z.2.2) hAjets hCA n
  have hBn := unweighted_timeJetSeminorm_le_of_labelMixedJetBound (h := h) hT hT₁ hℓ hD₀ hAE hscale
    coef.source (fun z hz => hBval z.1 hz.1 z.2.1 z.2.2) hBjets hCB n
  have hPVn := unweighted_timeJetSeminorm_le_of_labelMixedJetBound (h := h) hT hT₁ hℓ hD₀ hAE hscale
    coef.pressureVelocity (fun z hz => hPVval z.1 hz.1 z.2.1 z.2.2) hPVjets hCP n
  have hPFn := unweighted_timeJetSeminorm_le_of_labelMixedJetBound (h := h) hT hT₁ hℓ hD₀ hAE hscale
    coef.pressureSource (fun z hz => hPFval z.1 hz.1 z.2.1 z.2.2) hPFjets hCS n
  have hNorm_le : Cnorm n ≤ C n := le_max_right _ _
  exact ⟨hAn.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans ((le_max_left _ _).trans hNorm_le)) hAE),
    hBn.trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans ((le_max_left _ _).trans hNorm_le)) hAE),
    hPVn.trans (mul_le_mul_of_nonneg_right
      ((le_max_left _ _).trans ((le_max_right _ _).trans hNorm_le)) hAE),
    hPFn.trans (mul_le_mul_of_nonneg_right
      ((le_max_right _ _).trans ((le_max_right _ _).trans hNorm_le)) hAE)⟩

end

end TorusEuler.HierarchyTwistedProfile
