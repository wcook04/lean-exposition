import Breakdown.FracCell.LayoutRowValueModes
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.GaugeFluxParts
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.SegmentModesPressure
import Breakdown.FracCell.LayoutRowPressureSideCore

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown.FracInternal.LayoutRowPressureBoundaryParts

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly LayoutRowPressureSideCore
open CellCert.CellFormula.Internal.GaugeFluxParts (cyl_eq cyl_cont frame_cont cyl_dr cyl_dz cyl_dt ang_dt
  cyl_per ang_per radius_cont height_cont param_deriv frame_trace cyl_radius cyl_height)

theorem pressure_angular_mode {k N : ℕ} {c : FracCellData k N} {L : CellLayout} {x : FieldTuple k}
    (hx : IsAdmissible c x) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 →
      (p.1 : ℂ) * L.pressureGradMode n x 1 p = (azimuth L.order n : ℂ) * Complex.I * L.pressMode n x p := by
  have hG : IsGradientField x.2.2.2.2 := hx.2.1
  have hq := CellFormula.MeshGaugeLinearPotential.potentialOf_spec x.2.2.2.2 hG
  have hf : LocallyIntegrable (L.pressureOf x) volume :=
    (Breakdown.FracInternal.MeshDataAffineModes.pot_locInt hq).sub (locallyIntegrable_const _)
  obtain ⟨_, _, hQ2, hQm, _⟩ := hG
  have hg : LocallyIntegrable x.2.2.2.2 volume := Breakdown.FracInternal.MeshDataAffineModes.locInt_of_sq hQm hQ2
  have hweak : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * L.pressureOf x y = -∫ y, φ y * inner ℝ (x.2.2.2.2 y) (unitVector j) := by
    intro φ hφ j
    have h := pressure_weak hx.2.1 (L.gaugeValue x / L.gaugeUnit).re φ hφ j
    simp only [smul_eq_mul, innerSL_apply_apply] at h
    exact h
  set w : ℝ := azimuth L.order n with hw
  set E : ℝ → ℂ := fun θ => Complex.exp (-(w * θ : ℝ) * Complex.I) with hE
  have hEs : ContDiff ℝ ∞ E := by
    rw [hE]
    exact Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)).neg.mul contDiff_const)
  have hEp : Function.Periodic E (2 * Real.pi) := by
    intro θ
    simp only [hE, hw, azimuth]
    have : -((((n : ℝ) * (L.order : ℝ)) * (θ + 2 * Real.pi) : ℝ) : ℂ) * Complex.I =
        -((((n : ℝ) * (L.order : ℝ)) * θ : ℝ) : ℂ) * Complex.I + ((-(n * (L.order : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  have hEd : ∀ θ, deriv E θ = E θ * (-(w : ℂ) * Complex.I) := by
    intro θ
    have h1 : HasDerivAt (fun θ : ℝ => (-(w * θ : ℝ) : ℂ) * Complex.I) (-(w : ℂ) * Complex.I) θ := by
      have := (((hasDerivAt_id θ).const_mul w).ofReal_comp).neg.mul_const Complex.I
      simpa using this
    exact h1.cexp.deriv
  have hC := (CellEnergy.circleWeak (L.pressureOf x) x.2.2.2.2 hf hg hweak).2 E hEs hEp
  filter_upwards [hC] with p hp hp0
  have h := hp hp0
  simp only [hEd] at h
  have hl : ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((p.1 * inner ℝ (x.2.2.2.2 (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) =
      (p.1 : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (x.2.2.2.2 (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by push_cast; ring
  have hr : ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (-(w : ℂ) * Complex.I) * ((L.pressureOf x (cylPoint p.1 θ p.2) : ℝ) : ℂ) =
      (-(w : ℂ) * Complex.I) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((L.pressureOf x (cylPoint p.1 θ p.2) : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr fun θ _ => by ring
  rw [hl, hr] at h
  have e1 : L.pressureGradMode n x 1 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (x.2.2.2.2 (cylPoint p.1 θ p.2)) (angularUnit θ) : ℝ) : ℂ) := rfl
  have e2 : L.pressMode n x p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((L.pressureOf x (cylPoint p.1 θ p.2) : ℝ) : ℂ) := rfl
  rw [e1, e2]
  linear_combination (1 / (2 * Real.pi) : ℂ) * h

private theorem cmode_deriv {f : Space → Space} (hf : ContDiff ℝ 2 f) (γ γ' : ℝ → ℝ → Space)
    (hγ : Continuous (fun p : ℝ × ℝ => γ p.1 p.2)) (hγ' : Continuous (fun p : ℝ × ℝ => γ' p.1 p.2))
    (hdγ : ∀ s θ, HasDerivAt (fun s => γ s θ) (γ' s θ) s) (u : ℝ → Space) (hu : Continuous u)
    {E : ℝ → ℂ} (hE : Continuous E) (x : ℝ) :
    HasDerivAt (fun s => ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (γ s θ)) (u θ) : ℝ) : ℂ))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (fderiv ℝ f (γ x θ) (γ' x θ)) (u θ) : ℝ) : ℂ)) x := by
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  refine param_deriv (F := fun s θ => E θ * ((inner ℝ (f (γ s θ)) (u θ) : ℝ) : ℂ))
    (F' := fun s θ => E θ * ((inner ℝ (fderiv ℝ f (γ s θ) (γ' s θ)) (u θ) : ℝ) : ℂ)) ?_ ?_ ?_ 0 (2 * Real.pi) x
  · exact (hE.comp continuous_snd).mul
      (Complex.continuous_ofReal.comp ((hf.continuous.comp hγ).inner (hu.comp continuous_snd)))
  · exact (hE.comp continuous_snd).mul
      (Complex.continuous_ofReal.comp (((hfd.comp hγ).clm_apply hγ').inner (hu.comp continuous_snd)))
  · intro s θ
    have h := ((hdf (γ s θ)).hasFDerivAt.comp_hasDerivAt s (hdγ s θ)).inner ℝ (hasDerivAt_const s (u θ))
    have h2 := (h.ofReal_comp).const_mul (E θ)
    simpa using h2

theorem row_mode_divergence {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (n : ℤ) :
    ∀ p ∈ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂, 0 < p.1 →
      CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p +
        (azimuth c.order n : ℂ) * Complex.I * rowModeVec c a n p 1 +
          (p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p = 0 := by
  rintro ⟨x, z⟩ ⟨hx, hz⟩ hx0
  simp only at hx0
  have hr1 := hD.box.r_order.1
  have hz1 := hD.box.z_order.1
  obtain ⟨f, hf, hvf⟩ := hR.row_smooth a ha (x / 2) (by linarith)
  set U : Set Space := {y | K.r₁ < CellAnalysis.cylRadius y ∧ CellAnalysis.cylRadius y < K.r₂ ∧ K.z₁ < y 2 ∧
    y 2 < K.z₂ ∧ x / 2 < CellAnalysis.cylRadius y} with hU
  have hUo : IsOpen U := by
    simp only [hU, Set.ofPred_and]
    exact (isOpen_lt continuous_const radius_cont).inter ((isOpen_lt radius_cont continuous_const).inter
      ((isOpen_lt continuous_const height_cont).inter ((isOpen_lt height_cont continuous_const).inter
        (isOpen_lt continuous_const radius_cont))))
  have hUs : ∀ y ∈ U, y ∈ K.solid := by
    rintro y ⟨h1, h2, h3, h4, _⟩
    have hpos : 0 ≤ y 2 := by linarith
    have e : |cylHeight y| = y 2 := abs_of_nonneg hpos
    exact ⟨h1.le, h2.le, by rw [e]; exact h3.le, by rw [e]; exact h4.le⟩
  have hUeq : ∀ y ∈ U, c.row a y = f y := by
    intro y hy
    exact hvf y (hUs y hy) (show 0 ≤ y 2 by linarith [hy.2.2.1]) hy.2.2.2.2.le
  have hcylU : ∀ s θ t, s ∈ Ioo (max K.r₁ (x / 2)) K.r₂ → t ∈ Ioo K.z₁ K.z₂ → cylPoint s θ t ∈ U := by
    intro s θ t hs ht
    obtain ⟨hs1, hs2⟩ := max_lt_iff.1 hs.1
    have hs0 : 0 ≤ s := by linarith
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [CellCert.CellFormula.Internal.GaugeFluxParts.cyl_radius hs0]; exact hs1
    · rw [CellCert.CellFormula.Internal.GaugeFluxParts.cyl_radius hs0]; exact hs.2
    · rw [CellCert.CellFormula.Internal.GaugeFluxParts.cyl_height]; exact ht.1
    · rw [CellCert.CellFormula.Internal.GaugeFluxParts.cyl_height]; exact ht.2
    · rw [CellCert.CellFormula.Internal.GaugeFluxParts.cyl_radius hs0]; exact hs2
  have hx' : x ∈ Ioo (max K.r₁ (x / 2)) K.r₂ := ⟨max_lt hx.1 (by linarith), hx.2⟩
  have hDf : ∀ θ, fderiv ℝ (c.row a) (cylPoint x θ z) = fderiv ℝ f (cylPoint x θ z) := fun θ =>
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hUo.mem_nhds (hcylU x θ z hx' hz)) hUeq)
  set w : ℝ := azimuth c.order n with hw
  set E : ℝ → ℂ := fun θ => Complex.exp (-(w * θ : ℝ) * Complex.I) with hE
  have hEc : Continuous E := by rw [hE]; fun_prop
  have hV : ∀ s ∈ Ioo (max K.r₁ (x / 2)) K.r₂, ∀ t ∈ Ioo K.z₁ K.z₂,
      rowModeVec c a n (s, t) 0 = (1 / (2 * Real.pi) : ℂ) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint s θ t)) (radialUnit θ) : ℝ) : ℂ) ∧
      rowModeVec c a n (s, t) 1 = (1 / (2 * Real.pi) : ℂ) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint s θ t)) (angularUnit θ) : ℝ) : ℂ) ∧
      rowModeVec c a n (s, t) 2 = (1 / (2 * Real.pi) : ℂ) *
          ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint s θ t)) axialUnit : ℝ) : ℂ) := by
    intro s hs t ht
    have e : ∀ θ, c.row a (cylPoint s θ t) = f (cylPoint s θ t) := fun θ => hUeq _ (hcylU s θ t hs ht)
    refine ⟨?_, ?_, ?_⟩ <;> simp only [rowModeVec, modeVec, frameVec, e, hE, hw] <;> rfl
  have hfd : Continuous (fderiv ℝ f) := hf.continuous_fderiv (by norm_num)
  have hdf : Differentiable ℝ f := hf.differentiable (by norm_num)
  set A : ℝ → ℝ := fun θ => inner ℝ (f (cylPoint x θ z)) (radialUnit θ) with hA
  set G : ℝ → ℝ := fun θ => inner ℝ (f (cylPoint x θ z)) (angularUnit θ) with hG
  set Mr : ℝ → ℝ := fun θ => inner ℝ (fderiv ℝ f (cylPoint x θ z) (radialUnit θ)) (radialUnit θ) with hMr
  set Mt : ℝ → ℝ := fun θ => inner ℝ (fderiv ℝ f (cylPoint x θ z) (angularUnit θ)) (angularUnit θ) with hMt
  set Mz : ℝ → ℝ := fun θ => inner ℝ (fderiv ℝ f (cylPoint x θ z) axialUnit) axialUnit with hMz
  have hcx : Continuous (fun θ : ℝ => cylPoint x θ z) := (cyl_cont z).comp (continuous_const.prodMk continuous_id)
  have hAc : Continuous A := (hf.continuous.comp hcx).inner (frame_cont 0)
  have hGc : Continuous G := (hf.continuous.comp hcx).inner (frame_cont 1)
  have hMrc : Continuous Mr := ((hfd.comp hcx).clm_apply (frame_cont 0)).inner (frame_cont 0)
  have hMtc : Continuous Mt := ((hfd.comp hcx).clm_apply (frame_cont 1)).inner (frame_cont 1)
  have hMzc : Continuous Mz := ((hfd.comp hcx).clm_apply continuous_const).inner continuous_const
  have htr : ∀ θ, Mr θ + Mt θ + Mz θ = 0 := by
    intro θ
    have h := frame_trace θ (fderiv ℝ f (cylPoint x θ z))
    rw [← hDf θ, hR.row_solenoidal a ha _ (hUs _ (hcylU x θ z hx' hz)), hDf θ] at h
    simpa [frameMat, hMr, hMt, hMz] using h
  have dR : HasDerivAt (fun s => ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint s θ z)) (radialUnit θ) : ℝ) : ℂ))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((Mr θ : ℝ) : ℂ)) x :=
    cmode_deriv hf (fun s θ => cylPoint s θ z) (fun _ θ => radialUnit θ) (cyl_cont z)
      ((frame_cont 0).comp continuous_snd) (fun s θ => cyl_dr s θ z) radialUnit (frame_cont 0) hEc x
  have hcz : Continuous (fun p : ℝ × ℝ => cylPoint x p.2 p.1) := by
    simp only [cyl_eq]; fun_prop
  have dZ : HasDerivAt (fun t => ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint x θ t)) axialUnit : ℝ) : ℂ))
      (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((Mz θ : ℝ) : ℂ)) z :=
    cmode_deriv hf (fun t θ => cylPoint x θ t) (fun _ _ => axialUnit) hcz continuous_const
      (fun t θ => cyl_dz x θ t) (fun _ => axialUnit) continuous_const hEc z
  have hrad : CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) (x, z) =
      (1 / (2 * Real.pi) : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((A θ : ℝ) : ℂ)) +
        (x : ℂ) * ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((Mr θ : ℝ) : ℂ)) := by
    unfold CellBox.radialDeriv
    have e1 : (fun s : ℝ => ((s, z).1 : ℂ) * rowModeVec c a n (s, z) 0) =ᶠ[nhds x] (fun s : ℝ => (s : ℂ) *
        ((1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint s θ z)) (radialUnit θ) : ℝ) : ℂ))) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hx') fun s hs => by
        simp only; rw [(hV s hs z hz).1]
    have hd := (Complex.ofRealCLM.hasDerivAt (x := x)).mul (dR.const_mul (1 / (2 * Real.pi) : ℂ))
    rw [(hd.congr_of_eventuallyEq e1).deriv]
    simp [hA]
  have hhei : CellBox.heightDeriv (fun q => rowModeVec c a n q 2) (x, z) =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((Mz θ : ℝ) : ℂ) := by
    unfold CellBox.heightDeriv
    have e2 : (fun t : ℝ => rowModeVec c a n ((x, z).1, t) 2) =ᶠ[nhds z] (fun t : ℝ =>
        (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((inner ℝ (f (cylPoint x θ t)) axialUnit : ℝ) : ℂ)) :=
      Filter.eventuallyEq_of_mem (isOpen_Ioo.mem_nhds hz) fun t ht => by
        simp only; rw [(hV x hx' t ht).2.2]
    exact ((dZ.const_mul _).congr_of_eventuallyEq e2).deriv
  have hang : (w : ℂ) * Complex.I * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((G θ : ℝ) : ℂ) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ) := by
    have hGd : ∀ θ, HasDerivAt G (-A θ + x * Mt θ) θ := by
      intro θ
      have h := ((hdf (cylPoint x θ z)).hasFDerivAt.comp_hasDerivAt θ (cyl_dt x θ z)).inner ℝ (ang_dt θ)
      refine h.congr_deriv ?_
      simp only [hA, hMt, Function.comp_apply, map_smul, inner_neg_right, real_inner_smul_left]
    have hEd : ∀ θ, HasDerivAt E (E θ * (-(w : ℂ) * Complex.I)) θ := by
      intro θ
      have h1 : HasDerivAt (fun θ : ℝ => (-(w * θ : ℝ) : ℂ) * Complex.I) (-(w : ℂ) * Complex.I) θ := by
        have := (((hasDerivAt_id θ).const_mul w).ofReal_comp).neg.mul_const Complex.I
        simpa using this
      exact h1.cexp
    have hprod : ∀ θ, HasDerivAt (fun θ => E θ * ((G θ : ℝ) : ℂ))
        (E θ * (-(w : ℂ) * Complex.I) * ((G θ : ℝ) : ℂ) + E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ)) θ :=
      fun θ => (hEd θ).mul (hGd θ).ofReal_comp
    have hcont1 : Continuous (fun θ => E θ * (-(w : ℂ) * Complex.I) * ((G θ : ℝ) : ℂ)) :=
      (hEc.mul continuous_const).mul (Complex.continuous_ofReal.comp hGc)
    have hcont2 : Continuous (fun θ => E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ)) :=
      hEc.mul (Complex.continuous_ofReal.comp (hAc.neg.add (continuous_const.mul hMtc)))
    have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun θ _ => hprod θ)
      ((hcont1.add hcont2).intervalIntegrable (μ := volume) 0 (2 * Real.pi))
    rw [intervalIntegral.integral_add (hcont1.intervalIntegrable _ _) (hcont2.intervalIntegrable _ _)] at hint
    have hper : E (2 * Real.pi) * ((G (2 * Real.pi) : ℝ) : ℂ) = E 0 * ((G 0 : ℝ) : ℂ) := by
      have e1 : G (2 * Real.pi) = G 0 := by
        simp only [hG]
        have q1 := cyl_per x 0 z
        have q2 := ang_per 0
        rw [zero_add] at q1 q2
        rw [q1, q2]
      have e2 : E (2 * Real.pi) = E 0 := by
        simp only [hE, hw, azimuth]
        have : (-(((n : ℝ) * (c.order : ℝ)) * (2 * Real.pi) : ℝ) : ℂ) * Complex.I =
            ((-(n * (c.order : ℤ)) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
        rw [this, Complex.exp_int_mul_two_pi_mul_I]
        simp
      rw [e1, e2]
    rw [hper, sub_self] at hint
    have hpull : ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (-(w : ℂ) * Complex.I) * ((G θ : ℝ) : ℂ) =
        (-(w : ℂ) * Complex.I) * ∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((G θ : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun θ _ => by ring
    rw [hpull] at hint
    linear_combination -hint
  have hsum : (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((A θ : ℝ) : ℂ)) +
      (x : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((Mr θ : ℝ) : ℂ)) +
      (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ)) +
      (x : ℂ) * (∫ θ in (0 : ℝ)..(2 * Real.pi), E θ * ((Mz θ : ℝ) : ℂ)) = 0 := by
    have c1 : Continuous (fun θ => E θ * ((A θ : ℝ) : ℂ)) := hEc.mul (Complex.continuous_ofReal.comp hAc)
    have c2 : Continuous (fun θ => (x : ℂ) * (E θ * ((Mr θ : ℝ) : ℂ))) :=
      continuous_const.mul (hEc.mul (Complex.continuous_ofReal.comp hMrc))
    have c3 : Continuous (fun θ => E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ)) :=
      hEc.mul (Complex.continuous_ofReal.comp (hAc.neg.add (continuous_const.mul hMtc)))
    have c4 : Continuous (fun θ => (x : ℂ) * (E θ * ((Mz θ : ℝ) : ℂ))) :=
      continuous_const.mul (hEc.mul (Complex.continuous_ofReal.comp hMzc))
    have hz0 : ∫ θ in (0 : ℝ)..(2 * Real.pi), (E θ * ((A θ : ℝ) : ℂ) + (x : ℂ) * (E θ * ((Mr θ : ℝ) : ℂ)) +
        E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ) + (x : ℂ) * (E θ * ((Mz θ : ℝ) : ℂ))) = 0 := by
      rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℂ)) (fun θ _ => by
        have h := htr θ
        simp only
        have h' : ((Mr θ : ℝ) : ℂ) + ((Mt θ : ℝ) : ℂ) + ((Mz θ : ℝ) : ℂ) = 0 := by exact_mod_cast h
        push_cast
        linear_combination (x : ℂ) * E θ * h')]
      simp
    have c12 : Continuous (fun θ => E θ * ((A θ : ℝ) : ℂ) + (x : ℂ) * (E θ * ((Mr θ : ℝ) : ℂ))) := c1.add c2
    have c123 : Continuous (fun θ => E θ * ((A θ : ℝ) : ℂ) + (x : ℂ) * (E θ * ((Mr θ : ℝ) : ℂ)) + E θ * (((-A θ + x * Mt θ) : ℝ) : ℂ)) := c12.add c3
    rw [intervalIntegral.integral_add (c123.intervalIntegrable (μ := volume) 0 (2 * Real.pi)) (c4.intervalIntegrable _ _),
      intervalIntegral.integral_add (c12.intervalIntegrable (μ := volume) 0 (2 * Real.pi)) (c3.intervalIntegrable _ _),
      intervalIntegral.integral_add (c1.intervalIntegrable (μ := volume) 0 (2 * Real.pi)) (c2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at hz0
    exact hz0
  rw [hrad, hhei, (hV x hx' z hz).2.1]
  simp only
  have hw' : (azimuth c.order n : ℂ) = (w : ℂ) := rfl
  rw [hw']
  linear_combination (1 / (2 * Real.pi) : ℂ) * hsum + (1 / (2 * Real.pi) : ℂ) * hang

theorem strip_partition {ι : Type*} (T : Finset ι) (lo hi : ι → ℝ) {z₁ z₂ : ℝ}
    (hcov : ∀ u ∈ Icc z₁ z₂, ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s) (hin : ∀ s ∈ T, z₁ ≤ lo s ∧ hi s ≤ z₂)
    (hdis : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s) {A : Set ℝ} (hA : MeasurableSet A) {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn f (A ×ˢ Icc z₁ z₂)) :
    ∫ p in A ×ˢ Icc z₁ z₂, f p = ∑ s ∈ T, ∫ p in A ×ˢ Icc (lo s) (hi s), f p := by
  classical
  have hU : A ×ˢ Icc z₁ z₂ = ⋃ i : T, A ×ˢ Icc (lo i) (hi i) := by
    ext p
    simp only [mem_prod, mem_iUnion, Subtype.exists, exists_prop, mem_Icc]
    constructor
    · rintro ⟨hA, hp⟩
      obtain ⟨s, hs, h1, h2⟩ := hcov p.2 hp
      exact ⟨s, hs, hA, h1, h2⟩
    · rintro ⟨s, hs, hA, h1, h2⟩
      exact ⟨hA, (hin s hs).1.trans h1, h2.trans (hin s hs).2⟩
  have hnull : ∀ (x : ℝ), (volume : Measure (ℝ × ℝ)) (A ×ˢ {x}) = 0 := by
    intro x
    rw [Measure.volume_eq_prod]
    exact measure_mono_null (prod_mono (subset_univ A) subset_rfl) (by rw [Measure.prod_prod]; simp)
  rw [hU, integral_iUnion_ae]
  · rw [tsum_fintype]
    exact Finset.sum_coe_sort T (fun s => ∫ p in A ×ˢ Icc (lo s) (hi s), f p)
  · intro i
    exact (hA.prod measurableSet_Icc).nullMeasurableSet
  · intro i j hij
    have hne : (i : ι) ≠ j := fun e => hij (Subtype.ext e)
    rcases hdis i i.2 j j.2 hne with h | h
    · refine measure_mono_null ?_ (hnull (hi i))
      rintro p ⟨⟨hA, _, h2⟩, _, h3, _⟩
      exact ⟨hA, le_antisymm h2 (h.trans h3)⟩
    · refine measure_mono_null ?_ (hnull (hi j))
      rintro p ⟨⟨hA, h1, _⟩, _, _, h4⟩
      exact ⟨hA, le_antisymm h4 (h.trans h1)⟩
  · rw [← hU]; exact hf

theorem strip_partition_fst {ι : Type*} (T : Finset ι) (lo hi : ι → ℝ) {r₁ r₂ : ℝ}
    (hcov : ∀ u ∈ Icc r₁ r₂, ∃ s ∈ T, lo s ≤ u ∧ u ≤ hi s) (hin : ∀ s ∈ T, r₁ ≤ lo s ∧ hi s ≤ r₂)
    (hdis : ∀ s ∈ T, ∀ s' ∈ T, s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s) {A : Set ℝ} (hA : MeasurableSet A)
    {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (Icc r₁ r₂ ×ˢ A)) :
    ∫ p in Icc r₁ r₂ ×ˢ A, f p = ∑ s ∈ T, ∫ p in Icc (lo s) (hi s) ×ˢ A, f p := by
  classical
  have hU : Icc r₁ r₂ ×ˢ A = ⋃ i : T, Icc (lo i) (hi i) ×ˢ A := by
    ext p
    simp only [mem_prod, mem_iUnion, Subtype.exists, exists_prop, mem_Icc]
    constructor
    · rintro ⟨hp, hA⟩
      obtain ⟨s, hs, h1, h2⟩ := hcov p.1 hp
      exact ⟨s, hs, ⟨h1, h2⟩, hA⟩
    · rintro ⟨s, hs, ⟨h1, h2⟩, hA⟩
      exact ⟨⟨(hin s hs).1.trans h1, h2.trans (hin s hs).2⟩, hA⟩
  have hnull : ∀ (x : ℝ), (volume : Measure (ℝ × ℝ)) ({x} ×ˢ A) = 0 := by
    intro x
    rw [Measure.volume_eq_prod]
    exact measure_mono_null (prod_mono subset_rfl (subset_univ A)) (by rw [Measure.prod_prod]; simp)
  rw [hU, integral_iUnion_ae]
  · rw [tsum_fintype]
    exact Finset.sum_coe_sort T (fun s => ∫ p in Icc (lo s) (hi s) ×ˢ A, f p)
  · intro i
    exact (measurableSet_Icc.prod hA).nullMeasurableSet
  · intro i j hij
    have hne : (i : ι) ≠ j := fun e => hij (Subtype.ext e)
    rcases hdis i i.2 j j.2 hne with h | h
    · refine measure_mono_null ?_ (hnull (hi i))
      rintro p ⟨⟨⟨_, h2⟩, hA⟩, ⟨h3, _⟩, _⟩
      exact ⟨le_antisymm h2 (h.trans h3), hA⟩
    · refine measure_mono_null ?_ (hnull (hi j))
      rintro p ⟨⟨⟨h1, _⟩, hA⟩, ⟨_, h4⟩, _⟩
      exact ⟨le_antisymm h4 (h.trans h1), hA⟩
  · rw [← hU]; exact hf

theorem radial_side_cover {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsPressureLayout c K S B L) {v : ℝ} (hv : v = K.r₂ ∨ (v = K.r₁ ∧ K.r₁ ≠ 0)) :
    (∀ u ∈ Icc K.z₁ K.z₂, ∃ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = true ∧ (L.presSegment s).level = v),
        (L.presSegment s).lo ≤ u ∧ u ≤ (L.presSegment s).hi) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = true ∧ (L.presSegment s).level = v),
        K.z₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.z₂) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = true ∧ (L.presSegment s).level = v),
      ∀ s' ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = true ∧ (L.presSegment s).level = v), s ≠ s' →
        (L.presSegment s).hi ≤ (L.presSegment s').lo ∨ (L.presSegment s').hi ≤ (L.presSegment s).lo) := by
  refine ⟨fun u hu => ?_, fun s hs => ?_, fun s hs s' hs' hne => ?_⟩
  · rcases hv with hv | ⟨hv, h0⟩
    · obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 1 (fun h => absurd h (by decide)) u (by simpa using hu)
      refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using h1, by rw [hv]; simpa using h2⟩, h3, h4⟩
    · obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 0 (fun _ => h0) u (by simpa using hu)
      refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using h1, by rw [hv]; simpa using h2⟩, h3, h4⟩
  · obtain ⟨_, hr, _⟩ := Finset.mem_filter.1 hs
    rcases hL.presSegment_on_side s with ⟨_, _, h1, h2, _⟩ | ⟨h, _⟩
    · exact ⟨h1, h2⟩
    · exact absurd hr h
  · obtain ⟨_, hr, hl⟩ := Finset.mem_filter.1 hs
    obtain ⟨_, hr', hl'⟩ := Finset.mem_filter.1 hs'
    exact hL.presSides_disjoint s s' hne (by rw [hr, hr']) (by rw [hl, hl'])

theorem height_side_cover {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hL : IsPressureLayout c K S B L) {v : ℝ} (hv : v = K.z₁ ∨ v = K.z₂) :
    (∀ u ∈ Icc K.r₁ K.r₂, ∃ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = false ∧ (L.presSegment s).level = v),
        (L.presSegment s).lo ≤ u ∧ u ≤ (L.presSegment s).hi) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = false ∧ (L.presSegment s).level = v),
        K.r₁ ≤ (L.presSegment s).lo ∧ (L.presSegment s).hi ≤ K.r₂) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = false ∧ (L.presSegment s).level = v),
      ∀ s' ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = false ∧ (L.presSegment s).level = v), s ≠ s' →
        (L.presSegment s).hi ≤ (L.presSegment s').lo ∨ (L.presSegment s').hi ≤ (L.presSegment s).lo) := by
  refine ⟨fun u hu => ?_, fun s hs => ?_, fun s hs s' hs' hne => ?_⟩
  · rcases hv with hv | hv
    · obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 2 (fun h => absurd h (by decide)) u (by simpa using hu)
      refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using h1, by rw [hv]; simpa using h2⟩, h3, h4⟩
    · obtain ⟨s, h1, h2, h3, h4⟩ := hL.presSides_cover 3 (fun h => absurd h (by decide)) u (by simpa using hu)
      refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, by simpa using h1, by rw [hv]; simpa using h2⟩, h3, h4⟩
  · obtain ⟨_, hr, _⟩ := Finset.mem_filter.1 hs
    rcases hL.presSegment_on_side s with ⟨h, _⟩ | ⟨_, _, h1, h2⟩
    · rw [hr] at h; exact absurd h (by decide)
    · exact ⟨h1, h2⟩
  · obtain ⟨_, hr, hl⟩ := Finset.mem_filter.1 hs
    obtain ⟨_, hr', hl'⟩ := Finset.mem_filter.1 hs'
    exact hL.presSides_disjoint s s' hne (by rw [hr, hr']) (by rw [hl, hl'])

theorem radialDeriv_conj (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun q => (starRingEnd ℂ) (G q)) p = (starRingEnd ℂ) (CellBox.radialDeriv G p) := by
  unfold CellBox.radialDeriv
  exact deriv.star

theorem heightDeriv_conj (G : ℝ × ℝ → ℂ) (p : ℝ × ℝ) :
    CellBox.heightDeriv (fun q => (starRingEnd ℂ) (G q)) p = (starRingEnd ℂ) (CellBox.heightDeriv G p) := by
  unfold CellBox.heightDeriv
  exact deriv.star

private theorem lp_cyl_sub (r r' θ z z' : ℝ) : cylPoint r θ z - cylPoint r' θ z' = cylPoint (r - r') θ (z - z') := by
  ext i
  fin_cases i <;> simp [cylPoint] <;> ring

private theorem lp_cyl_radius (r θ z : ℝ) (hr : 0 ≤ r) : CellAnalysis.cylRadius (cylPoint r θ z) = r := by
  unfold CellAnalysis.cylRadius
  simp [cylPoint]
  rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr

private theorem lp_cyl_height (r θ z : ℝ) : cylHeight (cylPoint r θ z) = z := by
  simp [cylHeight, cylPoint]

private theorem lp_cyl_mem {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid ∩ {y | 0 ≤ cylHeight y} := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 h1
  have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 h3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [lp_cyl_radius _ _ _ hr0]; exact h1
  · rw [lp_cyl_radius _ _ _ hr0]; exact h2
  · rw [lp_cyl_height, abs_of_nonneg hz0]; exact h3
  · rw [lp_cyl_height, abs_of_nonneg hz0]; exact h4
  · show 0 ≤ cylHeight (cylPoint p.1 θ p.2)
    rw [lp_cyl_height]; exact hz0

private theorem lp_cyl_dist (r r' θ z z' : ℝ) :
    ‖cylPoint r θ z - cylPoint r' θ z'‖ ≤ 2 * dist (r, z) (r', z') := by
  rw [lp_cyl_sub, ModeVelSquareInternal.cylPoint_norm, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have ha := le_max_left |r - r'| |z - z'|
  have hb := le_max_right |r - r'| |z - z'|
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs (r - r'), sq_abs (z - z'), abs_nonneg (r - r'), abs_nonneg (z - z')]

private theorem lp_cyl_cont (r z : ℝ) : Continuous fun θ : ℝ => cylPoint r θ z := by
  unfold cylPoint
  exact (((ModeVelSquareInternal.single_cont 0).comp (continuous_const.mul Real.continuous_cos)).add
    ((ModeVelSquareInternal.single_cont 1).comp (continuous_const.mul Real.continuous_sin))).add continuous_const

private theorem lp_integrand_cont {v : Space → Space} {s : Set Space} (hv : ContinuousOn v s) {r z : ℝ}
    (hs : ∀ θ, cylPoint r θ z ∈ s) (w : ℝ) (i : Fin 3) :
    Continuous (fun θ : ℝ => Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) i : ℂ)) := by
  have hc1 : Continuous (fun θ : ℝ => v (cylPoint r θ z)) := hv.comp_continuous (lp_cyl_cont r z) hs
  have hc2 : Continuous (fun θ : ℝ => frameVec θ (v (cylPoint r θ z)) i) := by
    simp_rw [ModeVelSquareInternal.frameVec_eq]
    exact hc1.inner (ModeVelSquareInternal.frameUnit_cont i)
  have hc3 : Continuous (fun θ : ℝ => Complex.exp (-(w * θ : ℝ) * Complex.I)) := by fun_prop
  exact hc3.mul (Complex.continuous_ofReal.comp hc2)

private theorem lp_integrand_diff {v : Space → Space} {s : Set Space} {L₀ : NNReal} (hv : LipschitzOnWith L₀ v s)
    {r z r' z' : ℝ} (hs : ∀ θ, cylPoint r θ z ∈ s) (hs' : ∀ θ, cylPoint r' θ z' ∈ s) (w : ℝ) (i : Fin 3) (θ : ℝ) :
    ‖Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) i : ℂ) -
      Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r' θ z')) i : ℂ)‖ ≤
        (2 * L₀ : ℝ) * dist (r, z) (r', z') := by
  rw [← mul_sub, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have hlin : frameVec θ (v (cylPoint r θ z)) i - frameVec θ (v (cylPoint r' θ z')) i =
      frameVec θ (v (cylPoint r θ z) - v (cylPoint r' θ z')) i := by
    simp only [ModeVelSquareInternal.frameVec_eq, inner_sub_left]
  rw [hlin]
  refine (ModeVelSquareInternal.frameVec_abs _ _ _).trans ?_
  rw [← dist_eq_norm]
  refine (hv.dist_le_mul _ (hs θ) _ (hs' θ)).trans ?_
  rw [dist_eq_norm]
  have := lp_cyl_dist r r' θ z z'
  have hL : (0 : ℝ) ≤ L₀ := L₀.2
  calc (L₀ : ℝ) * ‖cylPoint r θ z - cylPoint r' θ z'‖ ≤ L₀ * (2 * dist (r, z) (r', z')) :=
        mul_le_mul_of_nonneg_left this hL
    _ = (2 * L₀ : ℝ) * dist (r, z) (r', z') := by ring

private theorem lp_mode_slope {v : Space → Space} {s : Set Space} {L₀ : NNReal} (hv : LipschitzOnWith L₀ v s)
    {T : Set (ℝ × ℝ)} (hT : ∀ p ∈ T, ∀ θ, cylPoint p.1 θ p.2 ∈ s) (m : ℕ) (n : ℤ) (i : Fin 3) :
    LipschitzOnWith (2 * L₀) (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 i) T := by
  refine LipschitzOnWith.of_dist_le_mul (fun p hp q hq => ?_)
  rw [dist_eq_norm]
  unfold modeVec
  rw [← mul_sub, ← intervalIntegral.integral_sub
    ((lp_integrand_cont hv.continuousOn (hT p hp) (azimuth m n) i).intervalIntegrable _ _)
    ((lp_integrand_cont hv.continuousOn (hT q hq) (azimuth m n) i).intervalIntegrable _ _), norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (fun θ _ => lp_integrand_diff hv (hT p hp) (hT q hq) (azimuth m n) i θ)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [sub_zero, abs_of_pos (by positivity)] at hI
  rw [h2]
  have hd : dist (p.1, p.2) (q.1, q.2) = dist p q := rfl
  rw [hd] at hI
  calc 1 / (2 * Real.pi) * ‖_‖ ≤ 1 / (2 * Real.pi) * ((2 * L₀ : ℝ) * dist p q * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ((2 * L₀ : NNReal) : ℝ) * dist p q := by push_cast; field_simp

private theorem lp_row_slope {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3) :
    ∃ C : NNReal, LipschitzOnWith C (fun p => rowModeVec c a n p i) K.rect := by
  obtain ⟨L₀, hL₀⟩ := hR.row_slope a ha
  exact ⟨2 * L₀, lp_mode_slope hL₀ (fun p hp θ => lp_cyl_mem hD.box hp θ) c.order n i⟩

private theorem lp_coord_slope {u : ℝ × ℝ → ℂ} {C : NNReal} {T : Set (ℝ × ℝ)} (hu : LipschitzOnWith C u T)
    {Rb M : ℝ} (hRb : ∀ p ∈ T, |p.1| ≤ Rb) (hM : ∀ p ∈ T, ‖u p‖ ≤ M) (hRb0 : 0 ≤ Rb) (hM0 : 0 ≤ M) :
    LipschitzOnWith (Real.toNNReal (Rb * C + M)) (fun p : ℝ × ℝ => (p.1 : ℂ) * (starRingEnd ℂ) (u p)) T := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have e : (p.1 : ℂ) * (starRingEnd ℂ) (u p) - (q.1 : ℂ) * (starRingEnd ℂ) (u q) =
      (p.1 : ℂ) * (starRingEnd ℂ) (u p - u q) + ((p.1 - q.1 : ℝ) : ℂ) * (starRingEnd ℂ) (u q) := by
    rw [map_sub]; push_cast; ring
  rw [e]
  have h1 : ‖u p - u q‖ ≤ C * dist p q := by rw [← dist_eq_norm]; exact hu.dist_le_mul p hp q hq
  have h2 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj, Complex.norm_conj,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have hd : 0 ≤ dist p q := dist_nonneg
  calc |p.1| * ‖u p - u q‖ + |p.1 - q.1| * ‖u q‖ ≤ Rb * (C * dist p q) + dist p q * M :=
        add_le_add (mul_le_mul (hRb p hp) h1 (norm_nonneg _) hRb0) (mul_le_mul h2 (hM q hq) (norm_nonneg _) hd)
    _ = (Rb * C + M) * dist p q := by ring

private theorem lp_test_cont (F : FaceSegment) (d : ℕ) : Continuous (F.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

private theorem lp_edge_sq (c o : ℝ) : edgeSign c o * edgeSign c o = 1 := by
  unfold edgeSign; split_ifs <;> norm_num

private theorem lp_box_sub (a b : ℝ) : Icc a b ⊆ Icc (-(|a| + |b|)) (|a| + |b|) := by
  intro s hs
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hs.1]
  · linarith [le_abs_self b, abs_nonneg a, hs.2]

private theorem radial_side_sum {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsPressureLayout c K S B L) {F dF dFz : ℝ × ℝ → ℂ}
    (hW : IsRadialWeakPair F dF) {G : ℝ × ℝ → ℂ} (hGc : ContinuousOn G K.rect)
    (cf : Fin L.presCount → Fin L.degSide → ℂ) {v o : ℝ} (hv : v = K.r₂ ∨ (v = K.r₁ ∧ K.r₁ ≠ 0))
    (ho : o = K.r₁ + K.r₂ - v)
    (hGv : ∀ s, (L.presSegment s).radial = true → (L.presSegment s).level = v → ∀ z ∈ Icc K.z₁ K.z₂,
      G (v, z) = (v : ℂ) * ∑ d : Fin L.degSide, (starRingEnd ℂ) (cf s d) * ((L.presSegment s).test d z : ℂ)) :
    ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) * G (v, p.2) =
      ∑ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = true ∧ (L.presSegment s).level = v),
        ∑ d : Fin L.degSide, edgeSign (L.presSegment s).level (L.presSegment s).other *
          ((L.presSegment s).level : ℂ) * (starRingEnd ℂ) (cf s d) * (L.presSegment s).moment true F dF dFz d := by
  have hr := hK.r_order
  have hvo : v ≠ o ∧ min v o = K.r₁ ∧ max v o = K.r₂ := by
    rw [ho]
    rcases hv with h | ⟨h, _⟩ <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> simp [min_def, max_def] <;> intros <;> linarith
  have hvmem : v ∈ Icc K.r₁ K.r₂ := by
    rcases hv with h | ⟨h, _⟩ <;> rw [h] <;> constructor <;> linarith
  set Z := |K.z₁| + |K.z₂| with hZ
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hF : IntegrableOn F K.rect :=
    (hW.1 K.r₂ Z).1.mono_set (prod_mono (Icc_subset_Icc_left hr.1) (lp_box_sub _ _))
  have hdFt : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) K.rect := by
    rcases hr.1.lt_or_eq with h0 | h0
    · have hd : IntegrableOn dF K.rect := (hW.2.1 K.r₁ K.r₂ Z h0).mono_set (prod_mono subset_rfl (lp_box_sub _ _))
      exact IntegrableOn.continuousOn_mul (by fun_prop) hd hcomp
    · have ho0 : o = 0 := by
        rcases hv with h | ⟨_, h⟩
        · rw [ho, h, ← h0]; ring
        · exact absurd h0.symm h
      have hrd : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) K.rect :=
        (hW.1 K.r₂ Z).2.mono_set (prod_mono (Icc_subset_Icc_left hr.1) (lp_box_sub _ _))
      refine IntegrableOn.congr_fun (hrd.const_mul (((1 / (v - o) : ℝ)) : ℂ)) (fun p _ => ?_) hmeas
      simp only [ho0, sub_zero]; push_cast; ring
  have hWint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p))
      K.rect := (hF.const_mul _).add hdFt
  have hGvc : ContinuousOn (fun p : ℝ × ℝ => G (v, p.2)) K.rect :=
    hGc.comp (continuous_const.prodMk continuous_snd).continuousOn (fun p hp => ⟨hvmem, hp.2⟩)
  have hfull := hWint.mul_continuousOn hGvc hcomp
  obtain ⟨hcov, hin, hdis⟩ := radial_side_cover hL hv
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect] at hfull hWint ⊢
  rw [strip_partition _ (fun s => (L.presSegment s).lo) (fun s => (L.presSegment s).hi) hcov hin hdis
    measurableSet_Icc hfull]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
  have hoth : (L.presSegment s).other = o := by
    rw [(hL.presSegment_other_in_box s).1 hrad, hlev, ho]
  have hsub : Icc K.r₁ K.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi ⊆ Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ :=
    prod_mono subset_rfl (Icc_subset_Icc (hin s hs).1 (hin s hs).2)
  have hsm : MeasurableSet (Icc K.r₁ K.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hint_d : ∀ d : Fin L.degSide, IntegrableOn (fun p : ℝ × ℝ =>
      ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        (((L.presSegment s).test d p.2 : ℝ) : ℂ)) (Icc K.r₁ K.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi) :=
    fun d => (hWint.mono_set hsub).mul_continuousOn
      (Complex.continuous_ofReal.comp ((lp_test_cont _ d).comp continuous_snd)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)
  have hmom : ∀ d : Fin L.degSide, (L.presSegment s).moment true F dF dFz d = edgeSign v o *
      ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          (((L.presSegment s).test d p.2 : ℝ) : ℂ) := by
    intro d
    simp only [FaceSegment.moment, hrad, ↓reduceIte, radialStripMoment, hlev, hoth, hvo.2.1, hvo.2.2]
  rw [setIntegral_congr_fun hsm (g := fun p => ∑ d : Fin L.degSide, ((v : ℂ) * (starRingEnd ℂ) (cf s d)) *
      (((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        (((L.presSegment s).test d p.2 : ℝ) : ℂ))) (fun p hp => ?_)]
  · rw [integral_finsetSum _ (fun d _ => (hint_d d).const_mul _)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [integral_const_mul, hmom d, hlev, hoth]
    linear_combination (-(v : ℂ) * (starRingEnd ℂ) (cf s d) *
      ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          (((L.presSegment s).test d p.2 : ℝ) : ℂ)) * lp_edge_sq v o
  · simp only
    rw [hGv s hrad hlev p.2 (Icc_subset_Icc (hin s hs).1 (hin s hs).2 hp.2), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring

private theorem height_side_sum {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsPressureLayout c K S B L) {F dF dFr : ℝ × ℝ → ℂ}
    (hW : IsHeightWeakPair (fun r => r) F dF) {G : ℝ × ℝ → ℂ} (hGc : ContinuousOn G K.rect)
    (cf : Fin L.presCount → Fin L.degSide → ℂ) {v o : ℝ} (hv : v = K.z₁ ∨ v = K.z₂)
    (ho : o = K.z₁ + K.z₂ - v)
    (hGv : ∀ s, (L.presSegment s).radial = false → (L.presSegment s).level = v → ∀ r ∈ Icc K.r₁ K.r₂,
      G (r, v) = ∑ d : Fin L.degSide, (starRingEnd ℂ) (cf s d) * ((L.presSegment s).test d r : ℂ)) :
    ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * G (p.1, v)) =
      ∑ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = false ∧ (L.presSegment s).level = v),
        ∑ d : Fin L.degSide, edgeSign (L.presSegment s).level (L.presSegment s).other *
          (starRingEnd ℂ) (cf s d) * (L.presSegment s).moment true F dFr dF d := by
  have hr := hK.r_order
  have hz := hK.z_order
  have hvo : v ≠ o ∧ min v o = K.z₁ ∧ max v o = K.z₂ := by
    rw [ho]
    rcases hv with h | h <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> simp [min_def, max_def] <;> intros <;> linarith
  have hvmem : v ∈ Icc K.z₁ K.z₂ := by
    rcases hv with h | h <;> rw [h] <;> constructor <;> linarith
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hbox : K.rect ⊆ Icc (-(|K.r₁| + |K.r₂|)) (|K.r₁| + |K.r₂|) ×ˢ Icc (-(|K.z₁| + |K.z₂|)) (|K.z₁| + |K.z₂|) :=
    prod_mono (lp_box_sub _ _) (lp_box_sub _ _)
  have hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) K.rect := (hW.1 _ _).1.mono_set hbox
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) K.rect := (hW.1 _ _).2.mono_set hbox
  have hWint : ∀ g : ℝ × ℝ → ℂ, ContinuousOn g K.rect → ∀ T ⊆ K.rect, MeasurableSet T → IsCompact T →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * g p)) T := by
    intro g hg T hT hTm hTc
    have h1 : IntegrableOn (fun p : ℝ × ℝ => (((((1 / (v - o) : ℝ)) : ℂ) * ((p.1 : ℂ) * F p)) +
        (((p.2 - o) / (v - o) : ℝ) : ℂ) * ((p.1 : ℂ) * dF p)) * g p) T :=
      IntegrableOn.mul_continuousOn (((hF.mono_set hT).const_mul _).add (IntegrableOn.continuousOn_mul
        (show Continuous fun p : ℝ × ℝ => ((((p.2 - o) / (v - o) : ℝ)) : ℂ) by fun_prop).continuousOn (hdF.mono_set hT) hTc))
        (hg.mono hT) hTc
    exact h1.congr_fun (fun p _ => by ring) hTm
  have hGvc : ContinuousOn (fun p : ℝ × ℝ => G (p.1, v)) K.rect :=
    hGc.comp (continuous_fst.prodMk continuous_const).continuousOn (fun p hp => ⟨hp.1, hvmem⟩)
  have hfull := hWint _ hGvc K.rect subset_rfl hmeas hcomp
  obtain ⟨hcov, hin, hdis⟩ := height_side_cover hL hv
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect] at hfull ⊢
  rw [strip_partition_fst _ (fun s => (L.presSegment s).lo) (fun s => (L.presSegment s).hi) hcov hin hdis
    measurableSet_Icc hfull]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
  have hnr : ¬ (L.presSegment s).radial := by simp [hrad]
  have hoth : (L.presSegment s).other = o := by
    rw [(hL.presSegment_other_in_box s).2 hnr, hlev, ho]
  have hsub : Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc K.z₁ K.z₂ ⊆ K.rect :=
    prod_mono (Icc_subset_Icc (hin s hs).1 (hin s hs).2) subset_rfl
  have hsm : MeasurableSet (Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc K.z₁ K.z₂) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hsc : IsCompact (Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc K.z₁ K.z₂) :=
    isCompact_Icc.prod isCompact_Icc
  have hint_d : ∀ d : Fin L.degSide, IntegrableOn (fun p : ℝ × ℝ =>
      ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * (((L.presSegment s).test d p.1 : ℝ) : ℂ))) (Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc K.z₁ K.z₂) :=
    fun d => hWint _ (Complex.continuous_ofReal.comp ((lp_test_cont _ d).comp continuous_fst)).continuousOn _ hsub hsm hsc
  have hmom : ∀ d : Fin L.degSide, (L.presSegment s).moment true F dFr dF d = edgeSign v o *
      ∫ p in Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc K.z₁ K.z₂,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          ((p.1 : ℂ) * (((L.presSegment s).test d p.1 : ℝ) : ℂ)) := by
    intro d
    simp only [FaceSegment.moment, hrad, Bool.false_eq_true, ↓reduceIte, heightStripMoment, hlev, hoth, hvo.2.1,
      hvo.2.2, Complex.ofReal_mul]
  rw [setIntegral_congr_fun hsm (g := fun p => ∑ d : Fin L.degSide, (starRingEnd ℂ) (cf s d) *
      (((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * (((L.presSegment s).test d p.1 : ℝ) : ℂ)))) (fun p hp => ?_)]
  · rw [integral_finsetSum _ (fun d _ => (hint_d d).const_mul _)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [integral_const_mul, hmom d, hlev, hoth]
    linear_combination (-(starRingEnd ℂ) (cf s d) *
      ∫ p in Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc K.z₁ K.z₂,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          ((p.1 : ℂ) * (((L.presSegment s).test d p.1 : ℝ) : ℂ))) * lp_edge_sq v o
  · simp only
    rw [hGv s hrad hlev p.1 (Icc_subset_Icc (hin s hs).1 (hin s hs).2 hp.1), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring

theorem radial_side_pairing {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (n : ℤ) (cf : Fin L.presCount → Fin L.degSide → ℂ)
    (hcf : ∀ s, ∀ p ∈ K.rect,
      ((L.presSegment s).radial → p.1 = (L.presSegment s).level →
          rowModeVec c a n p 0 = ∑ d, cf s d * ((L.presSegment s).test d p.2 : ℂ)) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level →
          rowModeVec c a n p 2 = ∑ d, cf s d * ((L.presSegment s).test d p.1 : ℂ))) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.pressureGradMode n x 0 p * (starRingEnd ℂ) (rowModeVec c a n p 0) +
        L.pressMode n x p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p)) K.rect ∧
    ∫ p in K.rect, ((p.1 : ℂ) * L.pressureGradMode n x 0 p * (starRingEnd ℂ) (rowModeVec c a n p 0) +
        L.pressMode n x p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p)) =
      ∑ s : Fin L.presCount, ∑ d : Fin L.degSide,
        (if (L.presSegment s).radial then
          edgeSign (L.presSegment s).level (L.presSegment s).other * ((L.presSegment s).level : ℂ) *
            (starRingEnd ℂ) (cf s d) *
            (L.presSegment s).moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d
        else 0) := by
  have hK := hD.box
  have hr := hK.r_order
  have hord : L.order = c.order := hL.layout.order_eq
  have hW := modes_radial_pair_pressure c x hx L hord n
  obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n 0
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hC.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (K.r₁, K.z₁) ⟨⟨le_rfl, hr.2.le⟩, le_rfl, hK.z_order.2.le⟩)
  have hRb : ∀ p ∈ K.rect, |p.1| ≤ K.r₂ := fun p hp => by
    rw [abs_of_nonneg (hr.1.trans hp.1.1)]; exact hp.1.2
  have hGL := lp_coord_slope hC hRb hM (hr.1.trans hr.2.le) hM0
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun q => (q.1 : ℂ) * (starRingEnd ℂ) (rowModeVec c a n q 0) := ⟨_, rfl⟩
  rw [← hGdef] at hGL
  have hfun : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.pressureGradMode n x 0 p * (starRingEnd ℂ) (rowModeVec c a n p 0) +
        L.pressMode n x p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q 0) p)) =
      fun p => L.pressureGradMode n x 0 p * G p + L.pressMode n x p * CellBox.radialDeriv G p := by
    funext p
    rw [← radialDeriv_conj]
    have e : (fun q : ℝ × ℝ => (starRingEnd ℂ) ((q.1 : ℂ) * rowModeVec c a n q 0)) = G := by
      rw [hGdef]; funext q; simp [map_mul, Complex.conj_ofReal]
    rw [e, hGdef]
    ring
  have hGa : K.r₁ = 0 → ∀ z ∈ Icc K.z₁ K.z₂, G (K.r₁, z) = 0 := by
    intro h0 z _; rw [hGdef]; simp [h0]
  obtain ⟨hI, hE⟩ := radial_slope_parts hW hr.1 hr.2 hGL hGa
  rw [hfun]
  refine ⟨hI, ?_⟩
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  have hGv : ∀ v ∈ Icc K.r₁ K.r₂, ∀ s, (L.presSegment s).radial = true → (L.presSegment s).level = v →
      ∀ z ∈ Icc K.z₁ K.z₂,
      G (v, z) = (v : ℂ) * ∑ d : Fin L.degSide, (starRingEnd ℂ) (cf s d) * ((L.presSegment s).test d z : ℂ) := by
    intro v hv s hrad hlev z hz
    have h := (hcf s (v, z) ⟨hv, hz⟩).1 hrad hlev.symm
    rw [hGdef]
    simp only
    rw [h, map_sum]
    simp [map_mul, Complex.conj_ofReal]
  have hGc : ContinuousOn G K.rect := hGL.continuousOn
  have h2 := radial_side_sum (dFz := L.pressureGradMode n x 2) hK hL hW hGc cf (v := K.r₂) (o := K.r₁) (Or.inl rfl)
    (by ring) (hGv K.r₂ ⟨hr.2.le, le_rfl⟩)
  rw [hrect] at h2
  rw [hrect, hE, h2]
  have h1 : (∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂,
        ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * L.pressMode n x p + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) *
          L.pressureGradMode n x 0 p) * G (K.r₁, p.2)) =
      ∑ s ∈ Finset.univ.filter (fun s => (L.presSegment s).radial = true ∧ (L.presSegment s).level = K.r₁),
        ∑ d : Fin L.degSide, edgeSign (L.presSegment s).level (L.presSegment s).other *
          ((L.presSegment s).level : ℂ) * (starRingEnd ℂ) (cf s d) *
          (L.presSegment s).moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d := by
    by_cases h0 : K.r₁ = 0
    · rw [Finset.sum_eq_zero]
      · rw [hGdef]; simp [h0]
      · intro s hs
        obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
        rcases hL.presSegment_on_side s with ⟨_, _, _, _, hne⟩ | ⟨hnr, _⟩
        · exact absurd (hlev.trans h0) hne
        · exact absurd hrad hnr
    · have h := radial_side_sum (dFz := L.pressureGradMode n x 2) hK hL hW hGc cf (v := K.r₁) (o := K.r₂)
        (Or.inr ⟨rfl, h0⟩) (by ring) (hGv K.r₁ ⟨le_rfl, hr.2.le⟩)
      rw [hrect] at h
      exact h
  rw [h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rcases hL.presSegment_on_side s with ⟨hrad, hlev, _, _, _⟩ | ⟨hnr, _⟩
  · have hrad' : (L.presSegment s).radial = true := hrad
    rcases hlev with h | h
    · simp [hrad', h, hr.2.ne]
    · simp [hrad', h, hr.2.ne']
  · have hnr' : (L.presSegment s).radial = false := by simpa using hnr
    simp [hnr']

theorem height_side_pairing {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (n : ℤ) (cf : Fin L.presCount → Fin L.degSide → ℂ)
    (hcf : ∀ s, ∀ p ∈ K.rect,
      ((L.presSegment s).radial → p.1 = (L.presSegment s).level →
          rowModeVec c a n p 0 = ∑ d, cf s d * ((L.presSegment s).test d p.2 : ℂ)) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level →
          rowModeVec c a n p 2 = ∑ d, cf s d * ((L.presSegment s).test d p.1 : ℂ))) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.pressureGradMode n x 2 p * (starRingEnd ℂ) (rowModeVec c a n p 2) +
        L.pressMode n x p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p)) K.rect ∧
    ∫ p in K.rect, ((p.1 : ℂ) * L.pressureGradMode n x 2 p * (starRingEnd ℂ) (rowModeVec c a n p 2) +
        L.pressMode n x p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p)) =
      ∑ s : Fin L.presCount, ∑ d : Fin L.degSide,
        (if (L.presSegment s).radial then 0 else
          edgeSign (L.presSegment s).level (L.presSegment s).other * (starRingEnd ℂ) (cf s d) *
            (L.presSegment s).moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d) := by
  have hK := hD.box
  have hr := hK.r_order
  have hz := hK.z_order
  have hord : L.order = c.order := hL.layout.order_eq
  have hW := modes_height_pair_pressure c x hx L hord n
  obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n 2
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun q => (starRingEnd ℂ) (rowModeVec c a n q 2) := ⟨_, rfl⟩
  have hGL : LipschitzOnWith C G K.rect := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [hGdef]
    simp only
    rw [Complex.dist_conj_conj]
    exact hC.dist_le_mul p hp q hq
  have hfun : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.pressureGradMode n x 2 p * (starRingEnd ℂ) (rowModeVec c a n p 2) +
        L.pressMode n x p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p)) =
      fun p => (p.1 : ℂ) * (L.pressureGradMode n x 2 p * G p + L.pressMode n x p * CellBox.heightDeriv G p) := by
    funext p
    have e : CellBox.heightDeriv G p = (starRingEnd ℂ) (CellBox.heightDeriv (fun q => rowModeVec c a n q 2) p) := by
      rw [hGdef]; exact heightDeriv_conj _ p
    rw [e, hGdef, map_mul, Complex.conj_ofReal]
    ring
  obtain ⟨hI, hE⟩ := height_slope_parts hW hr.1 hz.2 hGL
  rw [hfun]
  refine ⟨hI, ?_⟩
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  have hGv : ∀ v ∈ Icc K.z₁ K.z₂, ∀ s, (L.presSegment s).radial = false → (L.presSegment s).level = v →
      ∀ r ∈ Icc K.r₁ K.r₂,
      G (r, v) = ∑ d : Fin L.degSide, (starRingEnd ℂ) (cf s d) * ((L.presSegment s).test d r : ℂ) := by
    intro v hv s hrad hlev r hr'
    have h := (hcf s (r, v) ⟨hr', hv⟩).2 (by simp [hrad]) hlev.symm
    rw [hGdef]
    simp only
    rw [h, map_sum]
    simp [map_mul, Complex.conj_ofReal]
  have hGc : ContinuousOn G K.rect := hGL.continuousOn
  have h2 := height_side_sum (dFr := L.pressureGradMode n x 0) hK hL hW hGc cf (v := K.z₂) (o := K.z₁) (Or.inr rfl)
    (by ring) (hGv K.z₂ ⟨hz.2.le, le_rfl⟩)
  have h1 := height_side_sum (dFr := L.pressureGradMode n x 0) hK hL hW hGc cf (v := K.z₁) (o := K.z₂) (Or.inl rfl)
    (by ring) (hGv K.z₁ ⟨le_rfl, hz.2.le⟩)
  rw [hrect] at h1 h2
  rw [hrect, hE, h2, h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rcases hL.presSegment_on_side s with ⟨hrad, _⟩ | ⟨hnr, hlev, _, _⟩
  · have hrad' : (L.presSegment s).radial = true := hrad
    simp [hrad']
  · have hnr' : (L.presSegment s).radial = false := by simpa using hnr
    rcases hlev with h | h
    · simp [hnr', h, hz.2.ne]
    · simp [hnr', h, hz.2.ne']

end Breakdown.FracInternal.LayoutRowPressureBoundaryParts
