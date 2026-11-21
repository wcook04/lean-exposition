import Breakdown.FracCell.FormulaDataDefs
import Breakdown.FracCell.CylIntegral
import Breakdown.FracCert.LinearSolveCore

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CellCert.CellFormula.Internal.PlaneDeleted

open SteadyCert Assembly CellAnalysis Real



def sR (a : Fin 3) : ℝ := if a = 2 then -1 else 1

theorem sR_sq (a : Fin 3) : sR a * sR a = 1 := by
  unfold sR; split_ifs <;> norm_num

theorem mirror_eq (y : Space) : LinearSolveCore.mirrorIsometry y = mirror y := rfl

theorem mirror_mirror' (y : Space) : mirror (mirror y) = y := by
  ext i; fin_cases i <;> simp [mirror]

theorem mirror_unit (j : Fin 3) : mirror (unitVector j) = sR j • unitVector j := by
  ext i; fin_cases j <;> fin_cases i <;> simp [mirror, unitVector, sR]

theorem weak_mirror {u w : Space → Space} (j : Fin 3) (σ : ℝ) (hσ : σ * σ = 1)
    (hweak : ∀ φ : Space → ℝ, IsTestScalar φ → ∫ y, fderiv ℝ φ y (unitVector j) • u y = -∫ y, φ y • w y)
    (hu : ∀ᵐ y ∂volume, u (mirror y) = σ • mirror (u y)) (hw : MemLp w 2 volume) :
    ∀ᵐ y ∂volume, w (mirror y) = (σ * sR j) • mirror (w y) := by
  have hmp : MeasurePreserving mirror volume volume := LinearSolveCore.mirror_measurePreserving
  have hemb : MeasurableEmbedding mirror := LinearSolveCore.mirrorIsometry.toHomeomorph.measurableEmbedding
  have hint : ∀ g : Space → Space, ∫ y, g (mirror y) = ∫ y, g y := fun g => hmp.integral_comp hemb g
  have hcomm : ∀ f : Space → Space, ∫ y, LinearSolveCore.mirrorIsometry (f y) =
      LinearSolveCore.mirrorIsometry (∫ y, f y) := fun f =>
    LinearSolveCore.mirrorIsometry.toLinearIsometry.integral_comp_comm f
  have h1 : LocallyIntegrable (fun y => w (mirror y)) volume :=
    (hw.comp_measurePreserving hmp).locallyIntegrable (by norm_num)
  have h2 : LocallyIntegrable (fun y => (σ * sR j) • mirror (w y)) volume := by
    have : MemLp (fun y => (σ * sR j) • mirror (w y)) 2 volume :=
      (LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv.toContinuousLinearMap.comp_memLp' hw).const_smul
        (σ * sR j)
    exact this.locallyIntegrable (by norm_num)
  refine ae_eq_of_integral_contDiff_smul_eq h1 h2 fun φ hφ hφc => ?_
  have hψ : IsTestScalar (fun y => φ (mirror y)) :=
    ⟨hφ.comp LinearSolveCore.mirrorIsometry.contDiff,
      hφc.comp_homeomorph LinearSolveCore.mirrorIsometry.toHomeomorph⟩
  have hd : ∀ y, fderiv ℝ (fun y => φ (mirror y)) y (unitVector j) =
      sR j * fderiv ℝ φ (mirror y) (unitVector j) := by
    intro y
    have : (fun y => φ (mirror y)) = φ ∘ LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv := rfl
    rw [this, ContinuousLinearEquiv.comp_right_fderiv, ContinuousLinearMap.comp_apply]
    change fderiv ℝ φ (mirror y) (mirror (unitVector j)) = _
    rw [mirror_unit, map_smul, smul_eq_mul]
  set A := ∫ y, fderiv ℝ φ (mirror y) (unitVector j) • u y with hA
  have hB : ∫ y, fderiv ℝ φ y (unitVector j) • u y = σ • LinearSolveCore.mirrorIsometry A := by
    rw [← hint (fun y => fderiv ℝ φ y (unitVector j) • u y)]
    have : ∀ᵐ y ∂volume, fderiv ℝ φ (mirror y) (unitVector j) • u (mirror y) =
        σ • LinearSolveCore.mirrorIsometry (fderiv ℝ φ (mirror y) (unitVector j) • u y) := by
      filter_upwards [hu] with y hy
      rw [hy, map_smul, mirror_eq, smul_comm]
    rw [integral_congr_ae this, integral_smul, hcomm]
  have hL : ∫ y, φ y • w (mirror y) = -(sR j • A) := by
    have e1 : ∫ y, φ y • w (mirror y) = ∫ y, φ (mirror y) • w y := by
      rw [← hint (fun y => φ (mirror y) • w y)]
      simp only [mirror_mirror']
    have e2 := hweak _ hψ
    simp only [hd, mul_smul] at e2
    rw [integral_smul] at e2
    rw [e1, e2, neg_neg]
  have e4 : ∫ y, φ y • w y = -(σ • LinearSolveCore.mirrorIsometry A) := by
    rw [← hB, hweak φ ⟨hφ, hφc⟩, neg_neg]
  have hR : ∫ y, φ y • ((σ * sR j) • mirror (w y)) = -(sR j • A) := by
    have e3 : ∀ y, φ y • ((σ * sR j) • mirror (w y)) =
        (σ * sR j) • LinearSolveCore.mirrorIsometry (φ y • w y) := by
      intro y; rw [map_smul, mirror_eq, smul_comm]
    simp only [e3]
    rw [integral_smul, hcomm, e4, map_neg, map_smul, mirror_eq, mirror_eq, mirror_mirror', smul_neg, smul_smul]
    congr 2
    linear_combination sR j * hσ
  rw [hL, hR]




theorem memLp_grad {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (h2 : Integrable (fun y => entrySq (G y))) (j : Fin 3) :
    MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume := hm.apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hmj).2 ?_
  refine h2.mono' (hmj.norm.pow 2) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
    (Finset.mem_univ j)

theorem memLp_second {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (h2 : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2))
    (i j : Fin 3) : MemLp (fun y => H y (unitVector i) (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => H y (unitVector i) (unitVector j)) volume :=
    (hm.apply_continuousLinearMap _).apply_continuousLinearMap _
  refine (memLp_two_iff_integrable_sq_norm hmj).2 ?_
  refine h2.mono' (hmj.norm.pow 2) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖H y (unitVector i) (unitVector j)‖ ^ 2 ≤ ∑ j' : Fin 3, ‖H y (unitVector i) (unitVector j')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ‖H y (unitVector i) (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ j)
    _ ≤ _ := Finset.single_le_sum (f := fun i' => ∑ j' : Fin 3, ‖H y (unitVector i') (unitVector j')‖ ^ 2)
          (fun _ _ => by positivity) (Finset.mem_univ i)

theorem field_mirror {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) :
    ∀ᵐ y ∂volume, v (mirror y) = mirror (v y) ∧
      (∀ j, G (mirror y) (unitVector j) = sR j • mirror (G y (unitVector j))) ∧
      (∀ i j, H (mirror y) (unitVector j) (unitVector i) =
        (sR i * sR j) • mirror (H y (unitVector j) (unitVector i))) := by
  have hv : ∀ᵐ y ∂volume, v (mirror y) = (1 : ℝ) • mirror (v y) := by
    filter_upwards [h.symmetric.2] with y hy
    rw [hy, one_smul]
  have hG : ∀ j, ∀ᵐ y ∂volume, G (mirror y) (unitVector j) = sR j • mirror (G y (unitVector j)) := by
    intro j
    have := weak_mirror (u := v) (w := fun y => G y (unitVector j)) j 1 (by norm_num)
      (fun φ hφ => h.weak_gradient φ hφ j) hv (memLp_grad h.measurable_gradient h.gradient_two j)
    filter_upwards [this] with y hy
    rw [hy, one_mul]
  have hH : ∀ i j, ∀ᵐ y ∂volume, H (mirror y) (unitVector j) (unitVector i) =
      (sR i * sR j) • mirror (H y (unitVector j) (unitVector i)) := fun i j =>
    weak_mirror (u := fun y => G y (unitVector i)) (w := fun y => H y (unitVector j) (unitVector i)) j (sR i)
      (sR_sq i) (fun φ hφ => h.weak_second φ hφ i j) (hG i) (memLp_second h.measurable_second h.second_two j i)
  filter_upwards [h.symmetric.2, ae_all_iff.2 hG, ae_all_iff.2 fun i => ae_all_iff.2 (hH i)] with y h1 h2 h3
  exact ⟨h1, h2, h3⟩

def mirrorClm : Space →L[ℝ] Space := LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv.toContinuousLinearMap

theorem mirrorClm_apply (y : Space) : mirrorClm y = mirror y := rfl

theorem mirror_smul' (c : ℝ) (y : Space) : mirror (c • y) = c • mirror y := by
  rw [← mirror_eq, map_smul, mirror_eq]

theorem clm_ext {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {L L' : Space →L[ℝ] E}
    (h : ∀ i, L (unitVector i) = L' (unitVector i)) : L = L' :=
  ContinuousLinearMap.coe_injective ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext fun i => by
    simpa [unitVector] using h i)

theorem grad_at {G : Space →L[ℝ] Space} {G' : Space →L[ℝ] Space}
    (h : ∀ j, G' (unitVector j) = sR j • mirror (G (unitVector j))) (u : Space) :
    G' u = mirror (G (mirror u)) := by
  have : G' = mirrorClm.comp (G.comp mirrorClm) := clm_ext fun j => by
    rw [h j, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, mirrorClm_apply, mirrorClm_apply,
      mirror_unit, map_smul, mirror_smul']
  rw [this]
  rfl

theorem second_at {H H' : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ i j, H' (unitVector j) (unitVector i) = (sR i * sR j) • mirror (H (unitVector j) (unitVector i)))
    (u w : Space) : H' u w = mirror (H (mirror u) (mirror w)) := by
  have : H' = (ContinuousLinearMap.compL ℝ Space Space Space mirrorClm).comp
      (((ContinuousLinearMap.compL ℝ Space Space Space).flip mirrorClm).comp (H.comp mirrorClm)) := by
    refine clm_ext fun j => clm_ext fun i => ?_
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply,
      mirrorClm_apply, h i j, mirror_unit, map_smul, smul_apply, smul_smul]
    rw [mul_comm]
  rw [this]
  rfl




open Breakdown.CellCert.Spectral.Internal.CylIntegral in
theorem cyl_ae {P : Space → Prop} (hP : ∀ᵐ y ∂volume, P y) :
    ∀ᵐ q : ℝ × ℝ ∂volume, 0 < q.1 → ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-π) π)), P (cylPoint q.1 θ q.2) := by
  set N := toMeasurable volume {y | ¬ P y} with hNdef
  have hN0 : volume N = 0 := by rw [hNdef, measure_toMeasurable]; exact ae_iff.1 hP
  have hNm : MeasurableSet N := measurableSet_toMeasurable _ _
  have hsub : ∀ y, y ∉ N → P y := fun y hy => by
    by_contra h
    exact hy (subset_toMeasurable _ _ h)
  set N' := toSpace ⁻¹' N with hN'def
  have hN'm : MeasurableSet N' := toSpace.measurable hNm
  have hN'0 : volume N' = 0 := by
    rw [hN'def, toSpace_mp.measure_preimage hNm.nullMeasurableSet]; exact hN0
  have hsym : ∀ x : (ℝ × ℝ) × ℝ, cylMap.symm x = ((x.1.1 * Real.cos x.1.2, x.1.1 * Real.sin x.1.2), x.2) := by
    intro x
    rfl
  have hlin := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume cylMap.open_target.measurableSet
      (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn (N'.indicator 1)
  have hle : ∫⁻ x in cylMap.symm '' cylMap.target, N'.indicator 1 x = 0 := by
    refine le_antisymm ?_ bot_le
    calc _ ≤ ∫⁻ x, N'.indicator 1 x := setLIntegral_le_lintegral _ _
      _ = volume N' := lintegral_indicator_one hN'm
      _ = 0 := hN'0
  rw [hle, setLIntegral_congr_fun cylMap.open_target.measurableSet
    (g := fun x => ENNReal.ofReal x.1.1 * N'.indicator 1 (cylMap.symm x))
    (fun x hx => by rw [abs_det_eq hx])] at hlin
  have hmeas : Measurable fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * N'.indicator 1 (cylMap.symm x) := by
    refine (measurable_fst.fst.ennreal_ofReal).mul ((measurable_const.indicator hN'm).comp ?_)
    rw [show (cylMap.symm : (ℝ × ℝ) × ℝ → (ℝ × ℝ) × ℝ) = fun x =>
      ((x.1.1 * Real.cos x.1.2, x.1.1 * Real.sin x.1.2), x.2) from funext hsym]
    fun_prop
  have hz := (lintegral_eq_zero_iff hmeas).1 hlin.symm
  have hae1 : ∀ᵐ x ∂(volume.restrict cylMap.target), P (cylPoint x.1.1 x.1.2 x.2) := by
    filter_upwards [hz, ae_restrict_mem cylMap.open_target.measurableSet] with x hx hxt
    have hpos : 0 < x.1.1 := hxt.1.1
    have h0 : N'.indicator (1 : (ℝ × ℝ) × ℝ → ENNReal) (cylMap.symm x) = 0 := by
      have := hx
      simp only [Pi.zero_apply, mul_eq_zero, ENNReal.ofReal_eq_zero] at this
      rcases this with h | h
      · exact absurd h (not_le.2 hpos)
      · exact h
    have hnot : cylMap.symm x ∉ N' := by
      intro hm
      rw [Set.indicator_of_mem hm] at h0
      simp at h0
    apply hsub
    rw [hN'def, Set.mem_preimage, hsym, toSpace_apply] at hnot
    exact hnot
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hae2 := hmp.quasiMeasurePreserving.ae hae1
  rw [swapEquiv_preimage, Measure.volume_eq_prod, ← Measure.prod_restrict] at hae2
  have hae3 := Measure.ae_ae_of_ae_prod hae2
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at hae3
  filter_upwards [hae3] with q hq hpos
  exact hq ⟨hpos, trivial⟩

theorem exp_per (m : ℕ) (n : ℤ) :
    Function.Periodic (fun θ : ℝ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I)) (2 * π) := by
  intro θ
  refine Complex.exp_eq_exp_iff_exists_int.2 ⟨-(n * m), ?_⟩
  simp only [azimuth]
  push_cast
  ring

theorem cyl_per (r z θ : ℝ) : cylPoint r (θ + 2 * π) z = cylPoint r θ z := by
  simp [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem radial_per (θ : ℝ) : radialUnit (θ + 2 * π) = radialUnit θ := by
  simp [radialUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem angular_per (θ : ℝ) : angularUnit (θ + 2 * π) = angularUnit θ := by
  simp [angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem circle_congr {f g : ℝ → ℂ} (hf : Function.Periodic f (2 * π)) (hg : Function.Periodic g (2 * π))
    (h : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-π) π)), f θ = g θ) :
    ∫ θ in (0 : ℝ)..(2 * π), f θ = ∫ θ in (0 : ℝ)..(2 * π), g θ := by
  have e : ∀ u : ℝ → ℂ, Function.Periodic u (2 * π) →
      ∫ θ in (0 : ℝ)..(2 * π), u θ = ∫ θ in Set.Ioo (-π) π, u θ := by
    intro u hu
    have := hu.intervalIntegral_add_eq 0 (-π)
    rw [zero_add, show -π + 2 * π = π by ring] at this
    rw [this, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]
  rw [e f hf, e g hg]
  exact integral_congr_ae h

theorem inner_mirror (u w : Space) : inner ℝ (mirror u) w = inner ℝ u (mirror w) := by
  have := LinearSolveCore.mirrorIsometry.inner_map_map u (mirror w)
  simpa [mirror_eq, mirror_mirror'] using this

theorem cyl_neg (r θ z : ℝ) : cylPoint r θ (-z) = mirror (cylPoint r θ z) := by
  ext i; fin_cases i <;> simp [cylPoint, mirror]

theorem frame_mirror (θ : ℝ) (b : Fin 3) :
    mirror (![radialUnit θ, angularUnit θ, axialUnit] b) = sR b • ![radialUnit θ, angularUnit θ, axialUnit] b := by
  fin_cases b <;> ext i <;> fin_cases i <;> simp [mirror, radialUnit, angularUnit, axialUnit, sR]

theorem frameVec_mirror (θ : ℝ) (u : Space) (a : Fin 3) : frameVec θ (mirror u) a = sR a * frameVec θ u a := by
  have h := frame_mirror θ a
  fin_cases a <;> simp_all [frameVec, inner_mirror, inner_smul_right]

theorem frameMat_mirror (θ : ℝ) {G G' : Space →L[ℝ] Space} (h : ∀ u, G' u = mirror (G (mirror u))) (a b : Fin 3) :
    frameMat θ G' a b = sR a * sR b * frameMat θ G a b := by
  simp only [frameMat, h, inner_mirror, frame_mirror, map_smul, inner_smul_left, inner_smul_right]
  simp only [RCLike.conj_to_real]
  ring

theorem frameThird_mirror (θ : ℝ) {H H' : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ u w, H' u w = mirror (H (mirror u) (mirror w))) (a b c : Fin 3) :
    frameThird θ H' a b c = sR a * sR b * sR c * frameThird θ H a b c := by
  simp only [frameThird, frameUnit, h, inner_mirror, frame_mirror, map_smul, smul_apply,
    inner_smul_left, inner_smul_right]
  simp only [RCLike.conj_to_real]
  ring




theorem exp_per' (m : ℕ) (n : ℤ) (θ : ℝ) :
    Complex.exp (-(azimuth m n * (θ + 2 * π) : ℝ) * Complex.I) = Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) :=
  exp_per m n θ

theorem mode_congr (m : ℕ) (n : ℤ) (s : ℂ) {Φ Ψ : ℝ → ℂ} (hΦ : ∀ θ, Φ (θ + 2 * π) = Φ θ)
    (hΨ : ∀ θ, Ψ (θ + 2 * π) = Ψ θ) (h : ∀ᵐ θ ∂(volume.restrict (Set.Ioo (-π) π)), Φ θ = s * Ψ θ) :
    (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Φ θ =
      s * ((1 / (2 * Real.pi) : ℂ) *
        ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Ψ θ) := by
  have key : ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Φ θ =
      ∫ θ in (0 : ℝ)..(2 * Real.pi), s * (Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * Ψ θ) := by
    refine circle_congr (fun θ => ?_) (fun θ => ?_) ?_
    · simp only [exp_per', hΦ]
    · simp only [exp_per', hΨ]
    · filter_upwards [h] with θ hθ
      rw [hθ]
      ring
  rw [key, intervalIntegral.integral_const_mul]
  ring

theorem modes_mirror {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (h : IsSecondOrderField m v G H) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (∀ a, modeVec m n v p.1 (-p.2) a = (sR a : ℂ) * modeVec m n v p.1 p.2 a) ∧
      (∀ a b, gradMode m n G a b (p.1, -p.2) = (sR a : ℂ) * (sR b : ℂ) * gradMode m n G a b p) ∧
      (∀ a b c, modeThird m n H a b c (p.1, -p.2) =
        (sR a : ℂ) * (sR b : ℂ) * (sR c : ℂ) * modeThird m n H a b c p) := by
  filter_upwards [cyl_ae (field_mirror h)] with p hp hpos
  have hθ := hp hpos
  refine ⟨fun a => ?_, fun a b => ?_, fun a b c => ?_⟩
  · unfold modeVec
    refine mode_congr m n (sR a) (Φ := fun θ => (frameVec θ (v (cylPoint p.1 θ (-p.2))) a : ℂ))
      (Ψ := fun θ => (frameVec θ (v (cylPoint p.1 θ p.2)) a : ℂ))
      (fun θ => by simp only [frameVec, cyl_per, radial_per, angular_per])
      (fun θ => by simp only [frameVec, cyl_per, radial_per, angular_per]) ?_
    filter_upwards [hθ] with θ hy
    rw [cyl_neg, hy.1, frameVec_mirror]
    push_cast
    ring
  · unfold gradMode modeMat
    refine mode_congr m n ((sR a : ℂ) * (sR b : ℂ))
      (Φ := fun θ => (frameMat θ (G (cylPoint p.1 θ (-p.2))) a b : ℂ))
      (Ψ := fun θ => (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ))
      (fun θ => by simp only [frameMat, cyl_per, radial_per, angular_per])
      (fun θ => by simp only [frameMat, cyl_per, radial_per, angular_per]) ?_
    filter_upwards [hθ] with θ hy
    rw [cyl_neg, frameMat_mirror θ (grad_at hy.2.1) a b]
    push_cast
    ring
  · unfold modeThird
    refine mode_congr m n ((sR a : ℂ) * (sR b : ℂ) * (sR c : ℂ))
      (Φ := fun θ => (frameThird θ (H (cylPoint p.1 θ (-p.2))) a b c : ℂ))
      (Ψ := fun θ => (frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℂ))
      (fun θ => by simp only [frameThird, frameUnit, cyl_per, radial_per, angular_per])
      (fun θ => by simp only [frameThird, frameUnit, cyl_per, radial_per, angular_per]) ?_
    filter_upwards [hθ] with θ hy
    rw [cyl_neg, frameThird_mirror θ (second_at hy.2.2) a b c]
    push_cast
    ring




def MirrorModes (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : Prop :=
  ∀ n : ℤ, ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
    (∀ a, modeVec m n v p.1 (-p.2) a = (sR a : ℂ) * modeVec m n v p.1 p.2 a) ∧
    (∀ a b, gradMode m n G a b (p.1, -p.2) = (sR a : ℂ) * (sR b : ℂ) * gradMode m n G a b p) ∧
    (∀ a b c, modeThird m n H a b c (p.1, -p.2) = (sR a : ℂ) * (sR b : ℂ) * (sR c : ℂ) * modeThird m n H a b c p)

def refl : ℝ × ℝ ≃ᵐ ℝ × ℝ := MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)

theorem refl_apply (p : ℝ × ℝ) : refl p = (p.1, -p.2) := rfl

theorem refl_mp : MeasurePreserving refl volume volume :=
  (MeasurePreserving.id volume).prod (Measure.measurePreserving_neg volume)

theorem reflect_integral (X : Set ℝ) (a b : ℝ) (f : ℝ × ℝ → ℂ) :
    ∫ p in X ×ˢ Set.Icc (-b) (-a), f p = ∫ p in X ×ˢ Set.Icc a b, f (p.1, -p.2) := by
  have h : refl ⁻¹' (X ×ˢ Set.Icc (-b) (-a)) = X ×ˢ Set.Icc a b := by
    ext p
    simp only [Set.mem_preimage, refl_apply, Set.mem_prod, Set.mem_Icc, neg_le_neg_iff]
    tauto
  rw [← refl_mp.setIntegral_preimage_emb refl.measurableEmbedding, h]
  rfl

theorem ae_fst_ne : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : (volume : Measure (ℝ × ℝ)) ({0} ×ˢ Set.univ) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  rw [ae_iff]
  refine measure_mono_null (fun p hp => ?_) h
  simp only [not_not] at hp
  exact ⟨hp, trivial⟩

theorem edgeSign_neg {o : ℝ} (ho : o ≠ 0) : edgeSign 0 (-o) = -edgeSign 0 o := by
  unfold edgeSign
  rcases lt_or_gt_of_ne ho with h | h
  · have h1 : ¬ (-o < 0) := by linarith
    simp [h, h1]
  · have h1 : ¬ (o < 0) := by linarith
    have h2 : -o < 0 := by linarith
    simp [h1, h2]

theorem min_neg (o : ℝ) : min 0 (-o) = -max 0 o := by
  simpa using min_neg_neg (0 : ℝ) o

theorem max_neg (o : ℝ) : max 0 (-o) = -min 0 o := by
  simpa using max_neg_neg (0 : ℝ) o

theorem coefA (o : ℝ) : ((1 / (0 - -o) : ℝ) : ℂ) = -((1 / (0 - o) : ℝ) : ℂ) := by
  rw [show (0 : ℝ) - -o = -(0 - o) by ring, div_neg, Complex.ofReal_neg]

theorem coefB (z o : ℝ) : (((-z - -o) / (0 - -o) : ℝ) : ℂ) = (((z - o) / (0 - o) : ℝ) : ℂ) := by
  rw [show (-z - -o) = -(z - o) by ring, show (0 : ℝ) - -o = -(0 - o) by ring, neg_div_neg_eq]

theorem height_reflect (o lo hi : ℝ) (ho : o ≠ 0) (hlo : 0 ≤ lo) (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → F (p.1, -p.2) = -F p ∧ dF (p.1, -p.2) = dF p) :
    heightStripMoment 0 (-o) lo hi wt F dF t = -heightStripMoment 0 o lo hi wt F dF t := by
  unfold heightStripMoment
  rw [min_neg, max_neg, reflect_integral, edgeSign_neg ho, neg_mul]
  congr 2
  refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
  filter_upwards [hF, ae_fst_ne] with p hp hne hmem
  have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hlo hmem.1.1) (Ne.symm hne)
  obtain ⟨h1, h2⟩ := hp hpos
  rw [h1, h2, coefA, coefB]
  ring

theorem corner_reflect (cr orr oz : ℝ) (hoz : oz ≠ 0) (hr : 0 ≤ min cr orr) (F Fr Fz Frz : ℝ × ℝ → ℂ)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → F (p.1, -p.2) = -F p ∧ Fr (p.1, -p.2) = -Fr p ∧
      Fz (p.1, -p.2) = Fz p ∧ Frz (p.1, -p.2) = Frz p) :
    cornerMoment cr orr 0 (-oz) F Fr Fz Frz = -cornerMoment cr orr 0 oz F Fr Fz Frz := by
  unfold cornerMoment
  rw [min_neg, max_neg, reflect_integral, edgeSign_neg hoz, mul_neg, neg_mul]
  congr 2
  refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
  filter_upwards [hF, ae_fst_ne] with p hp hne hmem
  have hpos : 0 < p.1 := lt_of_le_of_ne (le_trans hr hmem.1.1) (Ne.symm hne)
  obtain ⟨h1, h2, h3, h4⟩ := hp hpos
  rw [h1, h2, h3, h4, coefA, coefB]
  ring

theorem height_zero (o lo hi : ℝ) (ho : o ≠ 0) (hlo : 0 ≤ lo) (wt t : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → F (p.1, -p.2) = -F p ∧ dF (p.1, -p.2) = dF p)
    (h : heightStripMoment 0 o lo hi wt F dF t = heightStripMoment 0 (-o) lo hi wt F dF t) :
    heightStripMoment 0 o lo hi wt F dF t = 0 := by
  rw [height_reflect o lo hi ho hlo wt t F dF hF] at h
  linear_combination h / 2

theorem corner_zero (cr orr oz : ℝ) (hoz : oz ≠ 0) (hr : 0 ≤ min cr orr) (F Fr Fz Frz : ℝ × ℝ → ℂ)
    (hF : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → F (p.1, -p.2) = -F p ∧ Fr (p.1, -p.2) = -Fr p ∧
      Fz (p.1, -p.2) = Fz p ∧ Frz (p.1, -p.2) = Frz p)
    (h : cornerMoment cr orr 0 oz F Fr Fz Frz = cornerMoment cr orr 0 (-oz) F Fr Fz Frz) :
    cornerMoment cr orr 0 oz F Fr Fz Frz = 0 := by
  rw [corner_reflect cr orr oz hoz hr F Fr Fz Frz hF] at h
  linear_combination h / 2



theorem modes_ae {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k) (L : CellLayout)
    (hord : L.order = c.order) (hmm : MirrorModes c.order x.1 x.2.1 x.2.2.1) (n : ℤ) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (∀ a, L.velMode n x a (p.1, -p.2) = (sR a : ℂ) * L.velMode n x a p) ∧
      (∀ a b, L.gradModeOf n x a b (p.1, -p.2) = (sR a : ℂ) * (sR b : ℂ) * L.gradModeOf n x a b p) ∧
      (∀ a b e, L.secondModeOf n x a b e (p.1, -p.2) = (sR a : ℂ) * (sR b : ℂ) * (sR e : ℂ) * L.secondModeOf n x a b e p) := by
  filter_upwards [hmm n] with p hp hpos
  obtain ⟨h1, h2, h3⟩ := hp hpos
  refine ⟨fun a => ?_, fun a b => ?_, fun a b e => ?_⟩
  · simp only [CellLayout.velMode, hord]
    exact h1 a
  · simp only [CellLayout.gradModeOf, hord]
    exact h2 a b
  · simp only [CellLayout.secondModeOf, hord]
    exact h3 a b e

theorem weight_swap (c o lo hi : ℝ) (wt t wt' t' : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ)
    (hw : ∀ r, wt r * t r = wt' r * t' r) :
    heightStripMoment c o lo hi wt F dF t = heightStripMoment c o lo hi wt' F dF t' := by
  simp only [heightStripMoment, hw]

theorem seg_zero (hS : SegmentIndependenceStatement) {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k)
    (hx : IsAdmissible c x) (L : CellLayout) (hord : L.order = c.order)
    (hmm : MirrorModes c.order x.1 x.2.1 x.2.2.1) (n : ℤ) (Sg : FaceSegment) (hv : IsFaceSegment Sg)
    (hrad : Sg.radial = false) (hlev : Sg.level = 0) (hlo : 0 ≤ Sg.lo) (e : ℕ) :
    Sg.moment false (L.velMode n x 2) (L.gradModeOf n x 2 0) (L.gradModeOf n x 2 2) e = 0 ∧
      ∀ a : Fin 3, a ≠ 2 → Sg.moment true (L.gradModeOf n x a 2) (L.secondModeOf n x a 2 0)
        (L.secondModeOf n x a 2 2) e = 0 := by
  have ho : Sg.other ≠ 0 := hlev ▸ hv.other_ne
  let S' : FaceSegment := ⟨Sg.radial, Sg.level, -Sg.other, Sg.lo, Sg.hi, Sg.testCoef⟩
  have hv' : IsFaceSegment S' := ⟨by simp only [S', hlev]; exact neg_ne_zero.mpr ho, hv.lo_lt_hi, hv.test_leading⟩
  have hrad' : (S'.radial = true) → S'.level ≠ 0 := fun h => by simp [S', hrad] at h
  have key := fun a => hS c x hx L hord n Sg S' hv hv' rfl rfl rfl rfl rfl (fun h => by simp [hrad] at h)
    (fun h => by simp [hrad] at h) a e
  have hae := modes_ae c x L hord hmm n
  refine ⟨?_, fun a ha => ?_⟩
  · obtain ⟨k1, -, -⟩ := key 2
    simp only [FaceSegment.moment, S', hrad, Bool.false_eq_true, if_false, hlev] at k1 ⊢
    refine height_zero _ _ _ ho hlo _ _ _ _ ?_ k1
    filter_upwards [hae] with p hp hpos
    obtain ⟨h1, h2, -⟩ := hp hpos
    rw [h1, h2]
    simp [sR]
  · obtain ⟨-, k2, -⟩ := key a
    simp only [FaceSegment.moment, S', hrad, Bool.false_eq_true, if_false, hlev] at k2 ⊢
    refine height_zero _ _ _ ho hlo _ _ _ _ ?_ k2
    filter_upwards [hae] with p hp hpos
    obtain ⟨-, h2, h3⟩ := hp hpos
    rw [h2, h3]
    simp [sR, ha]



theorem planeDeleted_of_mirror (hS : SegmentIndependenceStatement) (hC : CornerIndependenceStatement)
    (hM : ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
      MirrorModes c.order x.1 x.2.1 x.2.2.1) : PlaneDeletedStatement := by
  intro k N c K S B L hP x hx d hd
  have hL := hP.layout
  have hmm := hM c x hx
  have hord : L.order = c.order := hL.order_eq
  have hbox := hL.box_valid
  have hr := hbox.r_order
  have hz := hbox.z_order
  rcases d with i | i | i | i | i | i | i | i
  · simp [CellLayout.IsPlaneDeleted] at hd
  · simp [CellLayout.IsPlaneDeleted] at hd
  · obtain ⟨n, s, a, e⟩ := i
    simp only [CellLayout.IsPlaneDeleted, Sum.elim_inl, Sum.elim_inr] at hd
    obtain ⟨hrad, hlev, rfl⟩ := hd
    have hrad' : (L.segment s).radial = false := by simpa using hrad
    have hlo : 0 ≤ (L.segment s).lo := by
      rcases hL.segment_on_side s with h | h
      · exact absurd h.1 hrad
      · linarith [h.2.2.1]
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    exact (seg_zero hS c x hx L hord hmm n (L.segment s) (hL.segment_valid s) hrad' hlev hlo e).1
  · obtain ⟨n, s, a, e⟩ := i
    simp only [CellLayout.IsPlaneDeleted, Sum.elim_inl, Sum.elim_inr] at hd
    obtain ⟨hrad, hlev, ha⟩ := hd
    have hrad' : (L.segment s).radial = false := by simpa using hrad
    have hlo : 0 ≤ (L.segment s).lo := by
      rcases hL.segment_on_side s with h | h
      · exact absurd h.1 hrad
      · linarith [h.2.2.1]
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr, hrad', Bool.false_eq_true, if_false]
    exact (seg_zero hS c x hx L hord hmm n (L.segment s) (hL.segment_valid s) hrad' hlev hlo e).2 a ha
  · simp [CellLayout.IsPlaneDeleted] at hd
  · obtain ⟨n, cc, a⟩ := i
    simp only [CellLayout.IsPlaneDeleted, Sum.elim_inl, Sum.elim_inr] at hd
    obtain ⟨hcz, rfl⟩ := hd
    obtain ⟨hcr, hcz', hcr0⟩ := hL.corner_is_corner cc
    obtain ⟨hor, hoz⟩ := hL.corner_other cc
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    rw [hcz]
    set cr := (L.corner cc).1
    set orr := (L.cornerOther cc).1
    set oz := (L.cornerOther cc).2
    have hoz0 : oz ≠ 0 := by
      rcases hcz' with h | h <;> rw [hcz] at hoz h <;> intro h' <;> linarith
    have horr : orr ≠ cr := by
      rcases hcr with h | h <;> intro h' <;> linarith
    have hmin : 0 ≤ min cr orr := by
      rcases hcr with h | h <;> exact le_min (by linarith) (by linarith)
    have key := hC c x hx L hord n cr 0 orr oz orr (-oz) hcr0 horr hoz0 horr (neg_ne_zero.mpr hoz0) hmin hmin 2
    refine corner_zero _ _ _ hoz0 hmin _ _ _ _ ?_ key
    filter_upwards [modes_ae c x L hord hmm n] with p hp hpos
    obtain ⟨h1, h2, h3⟩ := hp hpos
    rw [h1, h2, h2, h3]
    simp [sR]
  · simp only [CellLayout.IsPlaneDeleted, Sum.elim_inl, Sum.elim_inr] at hd
    simp only [CellLayout.trueData, Sum.elim_inl, Sum.elim_inr]
    obtain ⟨hcr, hcz', hcr0⟩ := hL.corner_is_corner i
    obtain ⟨hor, hoz⟩ := hL.corner_other i
    rw [hd]
    set cr := (L.corner i).1
    set oz := (L.cornerOther i).2
    have hoz0 : oz ≠ 0 := by
      rcases hcz' with h | h <;> rw [hd] at hoz h <;> intro h' <;> linarith
    have hcrpos : 0 < cr := by
      rcases hcr with h | h
      · exact lt_of_le_of_ne (by linarith) (Ne.symm hcr0)
      · linarith
    let Sg : FaceSegment := ⟨false, 0, oz, 0, cr, fun d j => if j = d then 1 else 0⟩
    have hv : IsFaceSegment Sg := ⟨hoz0, hcrpos, fun d => by simp [Sg]⟩
    have h0 := (seg_zero hS c x hx L hord hmm 0 Sg hv rfl rfl le_rfl 1).1
    simp only [FaceSegment.moment, Sg, Bool.false_eq_true, if_false] at h0
    rw [← h0]
    refine weight_swap _ _ _ _ _ _ _ _ _ _ fun r => ?_
    simp [FaceSegment.test]
  · simp [CellLayout.IsPlaneDeleted] at hd


end Breakdown.CellCert.CellFormula.Internal.PlaneDeleted

namespace Breakdown.CellCert.CellFormula

theorem planeDeleted_of (hS : SegmentIndependenceStatement) (hC : CornerIndependenceStatement) :
    PlaneDeletedStatement :=
  Internal.PlaneDeleted.planeDeleted_of_mirror hS hC fun _ _ hx => Internal.PlaneDeleted.modes_mirror hx.1

end Breakdown.CellCert.CellFormula
