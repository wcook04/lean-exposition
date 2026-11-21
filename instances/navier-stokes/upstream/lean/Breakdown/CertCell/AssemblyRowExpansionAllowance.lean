import Breakdown.CertCell.AssemblyRowExpansionRestTests

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

open Coupling CellCert.CellAnalysis CellCert.CellFormula CellCalculus _root_.Breakdown.CertCell.Assembly.Internal

private theorem allowWeighted_lin {K : CellBox} {X Z : ℝ × ℝ → ℝ}
    (hXi : IntegrableOn (fun p => p.1 * X p) K.rect) (hZi : IntegrableOn (fun p => p.1 * Z p) K.rect) (a b : ℝ) :
    ∫ p in K.rect, p.1 * (a * X p + b * Z p) = a * (∫ p in K.rect, p.1 * X p) + b * (∫ p in K.rect, p.1 * Z p) := by
  have h := weighted_two_eq hXi hZi 1 a b
  simpa only [one_mul] using h

private theorem allowWeighted_three_le {K : CellBox} (hK : IsCellBox K) {X Y Z : ℝ × ℝ → ℝ}
    (hXi : IntegrableOn (fun p => p.1 * X p) K.rect) (hYi : IntegrableOn (fun p => p.1 * Y p) K.rect)
    (hZi : IntegrableOn (fun p => p.1 * Z p) K.rect)
    (hX : ∀ p, 0 ≤ X p) (hY : ∀ p, 0 ≤ Y p) (hZ : ∀ p, 0 ≤ Z p) {a b c a' b' c' : ℝ}
    (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c') :
    a * (∫ p in K.rect, p.1 * X p) + b * (∫ p in K.rect, p.1 * Y p) + c * (∫ p in K.rect, p.1 * Z p)
      ≤ ∫ p in K.rect, p.1 * (a' * X p + b' * Y p + c' * Z p) := by
  have e : (fun p : ℝ × ℝ => p.1 * (a' * X p + b' * Y p + c' * Z p))
      = fun p => a' * (p.1 * X p) + b' * (p.1 * Y p) + c' * (p.1 * Z p) := by
    funext p; ring
  have i1 : IntegrableOn (fun p : ℝ × ℝ => a' * (p.1 * X p) + b' * (p.1 * Y p)) K.rect :=
    (hXi.const_mul a').add (hYi.const_mul b')
  rw [e, integral_add (f := fun p : ℝ × ℝ => a' * (p.1 * X p) + b' * (p.1 * Y p))
    (g := fun p : ℝ × ℝ => c' * (p.1 * Z p)) i1 (hZi.const_mul c'),
    integral_add (f := fun p : ℝ × ℝ => a' * (p.1 * X p)) (g := fun p : ℝ × ℝ => b' * (p.1 * Y p))
      (hXi.const_mul a') (hYi.const_mul b'), integral_const_mul, integral_const_mul, integral_const_mul]
  have h1 := weighted_integral_nonneg hK hX
  have h2 := weighted_integral_nonneg hK hY
  have h3 := weighted_integral_nonneg hK hZ
  nlinarith [mul_le_mul_of_nonneg_right ha h1, mul_le_mul_of_nonneg_right hb h2, mul_le_mul_of_nonneg_right hc h3]

theorem allowanceSplit_holds : AllowanceSplitHolds := by
  intro k C nE nM D R A P states hstates _hReg hTF hCC _hP hC hF K q v G H g κ F Pg ht
  have hK := hC.mesh_valid.box_valid K
  have hbl := hCC.box_link K
  obtain ⟨heC, hdC, hLC, hHC, _⟩ := hF.costs_pos K
  have hX0 : ∀ ι p, 0 ≤ modeCurlSq D ι G p := fun ι p => by unfold modeCurlSq; positivity
  have hZ0 : ∀ ι p, 0 ≤ modeVelSq D ι v p := fun ι p => by unfold modeVelSq; positivity
  have hY0 : ∀ ι p, 0 ≤ sumSq (gradArray D.azimuthOrder ι G p) := fun ι p => by unfold sumSq; positivity
  have hls : ∀ ι, longSourceCost D R K (A.blocks K) ι ≤ (A.blocks K).longLowCost + (A.blocks K).longHighCost := by
    intro ι
    unfold longSourceCost
    split_ifs <;> linarith
  refine ⟨?_, ?_, ?_⟩
  · unfold freqAllowance errorAllowance longAllowance boxAmount pairSlackAmount pairStrainSlack
    have hT : D.mesh.tested K = D.mesh.resolved K ∩ D.mesh.tested K :=
      (Finset.inter_eq_right.mpr (hC.mesh_valid.tested_sub K)).symm
    rw [hT, ← Finset.sum_ite_mem, ← Finset.sum_ite_mem, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ι hι => ?_)
    obtain ⟨hZi, hXi, _⟩ := profile_integrable D hTF hK ht ι
    have hYi := sumSq_integrable D hTF hK ht ι
    rw [weighted_two_eq hXi hZi, weighted_two_eq hXi hZi]
    have e : ∀ c0 : ℝ, (if ι ∈ D.mesh.tested K then c0 * ∫ p in (D.mesh.box K).rect, p.1 * modeVelSq D ι v p else 0)
        = (if ι ∈ D.mesh.tested K then c0 else 0) * ∫ p in (D.mesh.box K).rect, p.1 * modeVelSq D ι v p := by
      intro c0; split_ifs <;> simp
    have eY : ∀ w : ℝ, (if ι ∈ R.pairSlackLabels K then w * ∫ p in (D.mesh.box K).rect,
          p.1 * ∑ a : Fin 3, ∑ b : Fin 3, ‖gradAt D.azimuthOrder ι G a b p‖ ^ 2 else 0)
        = (if ι ∈ R.pairSlackLabels K then w else 0)
          * ∫ p in (D.mesh.box K).rect, p.1 * sumSq (gradArray D.azimuthOrder ι G p) := by
      intro w; split_ifs
      · rfl
      · simp
    rw [e, eY]
    have hbY : (if ι ∈ R.pairSlackLabels K then R.pairSlackWeight K ι else 0) ≤ (R.leaves K).boxStrain ι := by
      split_ifs with hs
      · exact hF.box_strain_pair K ι hι hs
      · exact le_trans hbl.constants_pos.2.2.1 (hbl.box_strain ι hι)
    have key := allowWeighted_three_le hK hXi hYi hZi (hX0 ι) (hY0 ι) (hZ0 ι)
      (hF.box_curl_rows K ι hι) hbY (hF.box_velocity_rows K ι hι)
    refine le_trans (le_of_eq ?_) (le_of_le_of_eq key ?_)
    · ring
    · rfl
  · unfold errorAllowance longAllowance bandAllowance
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ι hι => ?_)
    obtain ⟨hZi, hXi, _⟩ := profile_integrable D hTF hK ht ι
    rw [weighted_two_eq hXi hZi, weighted_two_eq hXi hZi]
    have h1 := (hF.band_allowance_rows K ι hι).1
    have h2 := (hF.band_allowance_rows K ι hι).2
    have key := weighted_two_le hK hXi hZi (hX0 ι) (hZ0 ι)
      (a := 2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
        + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVelocity ^ 2)
      (c := 2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
        + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVorticity ^ 2)
      (a' := (A.blocks K).bandCurlAllowance ι) (c' := (A.blocks K).bandVelAllowance ι)
      h1 h2
    refine le_trans (le_of_eq ?_) key
    ring
  · have hS : deactSources D K (P.potential K) ⊆ (A.blocks K).leakModes := hF.sources_leak K
    have hsum : ∀ Fn : ℤ × ℤ → ℝ, ∑ ι ∈ deactSources D K (P.potential K), Fn ι
        = ∑ ι ∈ (A.blocks K).leakModes, if ι ∈ deactSources D K (P.potential K) then Fn ι else 0 := by
      intro Fn
      rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hS]
    unfold errorAllowance longAllowance deactAllowance rowLeakAmount
    rw [hsum, hsum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum (fun ι hι => ?_)
    obtain ⟨hZi, hXi, _⟩ := profile_integrable D hTF hK ht ι
    have hIX := weighted_integral_nonneg hK (hX0 ι)
    have hIZ := weighted_integral_nonneg hK (hZ0 ι)
    set sV := ∑ j, (if ι ∈ (P.potential K).rowPartners j then (P.potential K).groupVel j ^ 2 else 0) with hsV
    set sC := ∑ j, (if ι ∈ (P.potential K).rowPartners j then (P.potential K).groupCurl j ^ 2 else 0) with hsC
    have dd : ∫ p in (D.mesh.box K).rect, p.1 * (2 * (A.blocks K).deactCost *
        (sV * modeCurlSq D ι G p + sC * modeVelSq D ι v p))
        = (2 * (A.blocks K).deactCost * sV) * (∫ p in (D.mesh.box K).rect, p.1 * modeCurlSq D ι G p)
          + (2 * (A.blocks K).deactCost * sC) * (∫ p in (D.mesh.box K).rect, p.1 * modeVelSq D ι v p) := by
      rw [← allowWeighted_lin hXi hZi]
      refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only
      ring
    rw [dd, allowWeighted_lin hXi hZi, allowWeighted_lin hXi hZi, allowWeighted_lin hXi hZi]
    have hc := hF.leak_curl K ι hι
    have hv := hF.leak_vel K ι hι
    rw [← hsV] at hc
    rw [← hsC] at hv
    have hgc : 0 ≤ (if ∃ ι₀ ∈ D.mesh.tested K, ι₀ - ι ∈ (P.potential K).harmonicLabels then
        2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
          + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVelocity ^ 2 else 0) := by
      split_ifs <;> positivity
    have hgv : 0 ≤ (if ∃ ι₀ ∈ D.mesh.tested K, ι₀ - ι ∈ (P.potential K).harmonicLabels then
        2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
          + 2 * ((A.blocks K).longLowCost + (A.blocks K).longHighCost) * (R.long K).errVorticity ^ 2 else 0) := by
      split_ifs <;> positivity
    have hl1 := mul_le_mul_of_nonneg_right (hls ι) (sq_nonneg (R.long K).errVelocity)
    have hl2 := mul_le_mul_of_nonneg_right (hls ι) (sq_nonneg (R.long K).errVorticity)
    by_cases hιS : ι ∈ deactSources D K (P.potential K)
    · have hg : ∃ ι₀ ∈ D.mesh.tested K, ι₀ - ι ∈ (P.potential K).harmonicLabels := by
        have h' := hιS
        unfold deactSources at h'
        rw [Finset.mem_filter, Finset.mem_image] at h'
        obtain ⟨⟨x, hx, hxι⟩, _⟩ := h'
        rw [Finset.mem_product] at hx
        exact ⟨x.1, hx.1, by rw [← hxι, sub_sub_cancel]; exact hx.2⟩
      rw [if_pos hg] at hc hv
      rw [if_pos hιS, if_pos hιS]
      have c1 : 2 * (A.blocks K).errorCost * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
          + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVelocity ^ 2
          + 2 * (A.blocks K).deactCost * sV ≤ (A.blocks K).leakCurl ι := by nlinarith
      have c2 : 2 * (A.blocks K).errorCost * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
          + 2 * longSourceCost D R K (A.blocks K) ι * (R.long K).errVorticity ^ 2
          + 2 * (A.blocks K).deactCost * sC ≤ (A.blocks K).leakVel ι := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right c1 hIX, mul_le_mul_of_nonneg_right c2 hIZ]
    · rw [if_neg hιS, if_neg hιS]
      have c1 : 2 * (A.blocks K).deactCost * sV ≤ (A.blocks K).leakCurl ι := by linarith
      have c2 : 2 * (A.blocks K).deactCost * sC ≤ (A.blocks K).leakVel ι := by linarith
      nlinarith [mul_le_mul_of_nonneg_right c1 hIX, mul_le_mul_of_nonneg_right c2 hIZ]

end Assembly

end CertCell

end Breakdown
