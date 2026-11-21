import Breakdown.CertTorus.BilinSymbol

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

private theorem window_mild_sobolev (hOw : OrbitWindows) (hMr : MildRestrict) (hMs : MildSmoothing)
    {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space} (hw : realization.F.IsOrbit (realization.rot R) w P)
    (s₀ : ℝ) :
    IsMildX (fun t => dilX (1 - t)⁻¹ (w (s₀ - Real.log (1 - t)))) (1 / 4) (3 / 4) ∧
      ∀ k, IsHomSobolevCurve k (fun t => dilX (1 - t)⁻¹ (w (s₀ - Real.log (1 - t))))
        (Icc (1 / 4) (3 / 4)) := by
  have hM := hOw w P R hw s₀ (3 / 4) (by norm_num) (by norm_num)
  exact ⟨hMr _ 0 (1 / 4) (3 / 4) hM (by norm_num) (by norm_num),
    fun k => hMs _ 0 (3 / 4) (by norm_num) hM (1 / 4) ⟨by norm_num, by norm_num⟩ k⟩

private theorem isSmoothX_orbit (hOw : OrbitWindows) (hMr : MildRestrict) (hMs : MildSmoothing)
    (hDl : DilateSymbol) {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (hw : realization.F.IsOrbit (realization.rot R) w P) (σ : ℝ) : IsSmoothX (w σ) := by
  intro k
  have h := ((window_mild_sobolev hOw hMr hMs hw (σ - Real.log 2)).2 k).1 (1 / 2)
    ⟨by norm_num, by norm_num⟩
  have e : σ - Real.log 2 - Real.log (1 - 1 / 2) = σ := by
    rw [show (1 : ℝ) - 1 / 2 = 2⁻¹ by norm_num, Real.log_inv]
    ring
  beta_reduce at h
  rw [e, (hDl _ (by norm_num) _).1 k] at h
  rcases ENNReal.mul_lt_top_iff.1 h with h1 | h1 | h1
  · exact h1.2
  · exfalso
    rw [ENNReal.ofReal_eq_zero] at h1
    have : (0 : ℝ) < (1 - 1 / 2 : ℝ)⁻¹ ^ ((k : ℝ) + 1 / 2) := Real.rpow_pos_of_pos (by norm_num) _
    linarith
  · rw [h1]
    exact ENNReal.zero_lt_top

private theorem orbit_point (hOw : OrbitWindows) (hMr : MildRestrict) (hMs : MildSmoothing)
    (hSc : SymbolCurve) (hWs : WienerSolution) (hDl : DilateSymbol) (hWr : WindowResidual)
    (hWi : HomWiener) {w : ℝ → X} {P : ℝ} {R : Space ≃ₗᵢ[ℝ] Space}
    (hw : realization.F.IsOrbit (realization.rot R) w P) (s : ℝ) (y : Space) :
    ContDiffAt ℝ ∞ (fun z : ℝ × Space => orbitField w z.1 z.2) (s, y) ∧
      ContDiffAt ℝ ∞ (fun z : ℝ × Space => orbitPressure w z.1 z.2) (s, y) ∧
      SimilarityResidual (orbitField w) (orbitPressure w) s y = 0 ∧
      divergenceAt (orbitField w s) y = 0 := by
  set s₀ := s - Real.log 2 with hs₀
  set u : ℝ → X := fun t => dilX (1 - t)⁻¹ (w (s₀ - Real.log (1 - t))) with hu
  obtain ⟨hM, hc⟩ := window_mild_sobolev hOw hMr hMs hw s₀
  have hS := hSc u (1 / 4) (3 / 4) (by norm_num) hM hc
  have hsm : ∀ σ, IsSmoothX (w σ) := isSmoothX_orbit hOw hMr hMs hDl hw
  obtain ⟨hF, hp, hder, hdiv⟩ := hWs (fun t => velSymbol (u t)) (1 / 4) (3 / 4) (by norm_num)
    (fun t ht => ⟨Internal.BilinSymbolOfVelocity.isSolenoidal_velSymbol _,
      fun k => Internal.BilinSymbolOfVelocity.memLp_weight_velSymbol hWi (fun m => (hc m).1 t ht) k⟩) hS
  have hid : ∀ t : ℝ, t < 1 → physicalField (orbitField w) s₀ t = physField (velSymbol (u t)) := by
    intro t ht
    funext x
    have hμ : (0 : ℝ) < (1 - t)⁻¹ := inv_pos.2 (sub_pos.2 ht)
    rw [hu, (hDl _ hμ _).2.2.1 (hsm _) x]
    rfl
  have hidp : ∀ t : ℝ, t < 1 →
      (fun x' : Space => (1 - t)⁻¹ * orbitPressure w (s₀ - Real.log (1 - t))
        ((Real.sqrt (1 - t))⁻¹ • x')) = physScalar (pressureSymbol (velSymbol (u t))) := by
    intro t ht
    funext x
    have hμ : (0 : ℝ) < (1 - t)⁻¹ := inv_pos.2 (sub_pos.2 ht)
    rw [hu, (hDl _ hμ _).2.2.2 (hsm _) x, Real.sqrt_inv]
    rfl
  have hlt : ∀ t ∈ Icc (1 / 4 : ℝ) (3 / 4), t < 1 := fun t ht => lt_of_le_of_lt ht.2 (by norm_num)
  have h1 : ContDiffOn ℝ ∞ (fun z : ℝ × Space => physicalField (orbitField w) s₀ z.1 z.2)
      (Icc (1 / 4) (3 / 4) ×ˢ univ) := by
    refine hF.congr fun z hz => ?_
    show physicalField (orbitField w) s₀ z.1 z.2 = physField (velSymbol (u z.1)) z.2
    rw [hid z.1 (hlt _ hz.1)]
  have h2 : ContDiffOn ℝ ∞ (fun z : ℝ × Space =>
      (1 - z.1)⁻¹ * orbitPressure w (s₀ - Real.log (1 - z.1)) ((Real.sqrt (1 - z.1))⁻¹ • z.2))
      (Icc (1 / 4) (3 / 4) ×ˢ univ) := by
    refine hp.congr fun z hz => ?_
    exact congrFun (hidp z.1 (hlt _ hz.1)) z.2
  have h3 : ∀ t ∈ Ioo (1 / 4 : ℝ) (3 / 4), ∀ x, HasDerivAt (fun τ => physicalField (orbitField w) s₀ τ x)
      (sumSecondPartialsAt (physicalField (orbitField w) s₀ t) x -
        advectionAt (physicalField (orbitField w) s₀ t) x -
        gradientAt (fun x' => (1 - t)⁻¹ * orbitPressure w (s₀ - Real.log (1 - t))
          ((Real.sqrt (1 - t))⁻¹ • x')) x) t := by
    intro t ht x
    have ht1 : t < 1 := lt_trans ht.2 (by norm_num)
    rw [hid t ht1, hidp t ht1]
    refine (hder t ht x).congr_of_eventuallyEq ?_
    filter_upwards [Iio_mem_nhds ht1] with τ hτ
    rw [hid τ hτ]
  have h4 : ∀ t ∈ Icc (1 / 4 : ℝ) (3 / 4), ∀ x, divergenceAt (physicalField (orbitField w) s₀ t) x = 0 := by
    intro t ht x
    rw [hid t (hlt t ht)]
    exact hdiv t ht x
  have hl1 : 0 < Real.log 2 + Real.log (1 - 1 / 4) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_pos (by norm_num)
  have hl2 : Real.log 2 + Real.log (1 - 3 / 4) < 0 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    exact Real.log_neg (by norm_num) (by norm_num)
  exact hWr (orbitField w) (orbitPressure w) s₀ (1 / 4) (3 / 4) (by norm_num) (by norm_num)
    (by norm_num) h1 h2 h3 h4 s ⟨by rw [hs₀]; linarith, by rw [hs₀]; linarith⟩ y

theorem orbitSmoothOfWindows_holds : OrbitSmoothOfWindows := by
  intro hOw hMr hMs hSc hWs hDl hWr hWi w P R hw
  have key := orbit_point hOw hMr hMs hSc hWs hDl hWr hWi hw
  exact ⟨isSmoothX_orbit hOw hMr hMs hDl hw,
    contDiff_iff_contDiffAt.2 fun z => (key z.1 z.2).1,
    contDiff_iff_contDiffAt.2 fun z => (key z.1 z.2).2.1,
    fun s y => (key s y).2.2.1, fun s y => (key s y).2.2.2⟩

end Breakdown.FarField
