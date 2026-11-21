import Breakdown.CertCell.PatchModeWeak

open scoped ContDiff ENNReal ComplexOrder
open MeasureTheory Set Filter Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.PatchCreditLinks

theorem upperTrace_integrableOn {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ξ : ℤ × ℤ) {ρ₁ ρ₂ h : ℝ}
    (hρ₁ : 0 < ρ₁) (hρ : ρ₁ ≤ ρ₂) (hh : 0 < h) :
    IntegrableOn (fun r => upperTrace (planeVel ξ v 2 r) (planeVelHeight ξ G 2 r) h) (Icc ρ₁ ρ₂) := by
  set k : ℝ × ℝ → ℂ := fun p => planeVelHeight ξ G 2 p.1 p.2 * ((1 - p.2 / h : ℝ) : ℂ) -
    planeVel ξ v 2 p.1 p.2 / (h : ℂ) with hk
  set R := ρ₂ + h + 1 with hR
  have hS : MeasurableSet (Icc ρ₁ ρ₂ ×ˢ Icc (0 : ℝ) h) := measurableSet_Icc.prod measurableSet_Icc
  have hbox : Icc ρ₁ ρ₂ ×ˢ Icc (0 : ℝ) h ⊆ Icc ρ₁ R ×ˢ Icc (-R) R := fun p hp =>
    ⟨⟨hp.1.1, by linarith [hp.1.2, hR]⟩, by linarith [hp.2.1, hp.2.2, hR, hρ₁, hρ, hh],
      by linarith [hp.2.1, hp.2.2, hR, hρ₁, hρ, hh]⟩
  have hfin : IsFiniteMeasure (volume.restrict (Icc ρ₁ R ×ˢ Icc (-R) R)) :=
    isFiniteMeasure_restrict.2 (isCompact_Icc.prod isCompact_Icc).measure_lt_top.ne
  have iH : IntegrableOn (fun p : ℝ × ℝ => planeVelHeight ξ G 2 p.1 p.2) (Icc ρ₁ ρ₂ ×ˢ Icc (0 : ℝ) h) :=
    IntegrableOn.mono_set ((planeHeight_memLp hv ξ (R := R) hρ₁).integrable (by norm_num)) hbox
  have iU : IntegrableOn (fun p : ℝ × ℝ => planeVel ξ v 2 p.1 p.2) (Icc ρ₁ ρ₂ ×ˢ Icc (0 : ℝ) h) :=
    IntegrableOn.mono_set ((planeVel_memLp hv ξ 2 (R := R) hρ₁).integrable (by norm_num)) hbox
  have ik : IntegrableOn k (Icc ρ₁ ρ₂ ×ˢ Icc (0 : ℝ) h) := by
    refine Integrable.sub ?_ (iU.div_const _)
    refine iH.mul_bdd (c := 1) (Complex.continuous_ofReal.comp (by fun_prop :
      Continuous fun p : ℝ × ℝ => 1 - p.2 / h)).aestronglyMeasurable ?_
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun p hp => ?_)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_le]
    have e1 : p.2 / h ≤ 1 := (div_le_one hh).2 hp.2.2
    have e2 : 0 ≤ p.2 / h := div_nonneg hp.2.1 hh.le
    constructor <;> linarith
  have ik' : Integrable k ((volume.restrict (Icc ρ₁ ρ₂)).prod (volume.restrict (Icc (0 : ℝ) h))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact ik
  refine (ik'.integral_prod_left.neg).congr (Eventually.of_forall fun r => ?_)
  simp only [Pi.neg_apply, upperTrace, hk]
  rw [intervalIntegral.integral_of_le hh.le, ← integral_Icc_eq_integral_Ioc]

theorem termwise_intervalIntegrable {u : ℝ → ℂ} {ρ₁ ρ₂ : ℝ} (hρ : ρ₁ ≤ ρ₂) (hu : IntegrableOn u (Icc ρ₁ ρ₂))
    {f : ℝ × ℝ → ℝ} {K : NNReal} (hf : LipschitzWith K f) :
    IntervalIntegrable (fun r => u r * (f (r, 0) : ℂ) * (r : ℂ)) volume ρ₁ ρ₂ := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hρ]
  have c1 : Continuous fun r : ℝ => (f (r, 0) : ℂ) :=
    Complex.continuous_ofReal.comp (hf.continuous.comp (by fun_prop))
  have c2 : Continuous fun r : ℝ => (r : ℂ) := Complex.continuous_ofReal
  exact (hu.mul_continuousOn c1.continuousOn isCompact_Icc).mul_continuousOn c2.continuousOn isCompact_Icc

theorem combination_slopeBound {N : ℕ} (φ : Fin N → ℝ × ℝ → ℝ) {K : NNReal} (hφ : ∀ i, LipschitzWith K (φ i))
    (c : Fin N → ℂ) (s : Finset (Fin N)) :
    ∃ K' : NNReal, LipschitzWith K' (fun p => ∑ i ∈ s, (starRingEnd ℂ) (c i) * (φ i p : ℂ)) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp [LipschitzWith.const (0 : ℂ)]⟩
  | insert a s ha ih =>
    obtain ⟨K1, h1⟩ := ih
    have h2 : LipschitzWith (‖(starRingEnd ℂ) (c a)‖₊ * (1 * K))
        (fun p => (starRingEnd ℂ) (c a) • ((φ a p : ℝ) : ℂ)) :=
      (lipschitzWith_smul ((starRingEnd ℂ) (c a))).comp
        (Complex.isometry_ofReal.lipschitz.comp (hφ a))
    have e : (fun p => ∑ i ∈ insert a s, (starRingEnd ℂ) (c i) * (φ i p : ℂ)) =
        fun p => (starRingEnd ℂ) (c a) • ((φ a p : ℝ) : ℂ) + ∑ i ∈ s, (starRingEnd ℂ) (c i) * (φ i p : ℂ) := by
      funext p
      simp only [Finset.sum_insert ha, smul_eq_mul]
    rw [e]
    exact ⟨_, h2.add h1⟩

end Internal.PatchCreditLinks

open Internal.PatchCreditLinks in
theorem patchCredit (hG : Coupling.InverseFormCreditHolds) (hT : PatchTraceBoundHolds) :
    PatchCreditHolds := by
  intro Γ P v G H g hv hflip ξ ρ₁ ρ₂ h b N φ K Gp hρ₁ hρ hh hbm hb0 hb1 hφ hside htop hGp hE
  set u : ℝ → ℂ := fun r => upperTrace (planeVel ξ v 2 r) (planeVelHeight ξ G 2 r) h with hu
  have hui : IntegrableOn u (Icc ρ₁ ρ₂) := upperTrace_integrableOn hv ξ hρ₁ hρ.le hh
  set A : ℝ := ∫ p in patch ρ₁ ρ₂ h, b p * cnormSq (modeVel (flipLabel ξ) v 0 (planePoint p)) * p.1 with hA
  obtain ⟨b₀, hb₀, hbb₀⟩ := hb0
  have hS : MeasurableSet (patch ρ₁ ρ₂ h) := measurableSet_Icc.prod measurableSet_Icc
  have hA0 : 0 ≤ A := by
    refine setIntegral_nonneg hS fun p hp => ?_
    have hbp : 0 < b p := lt_of_lt_of_le hb₀ (hbb₀ p)
    have hr : 0 ≤ p.1 := by linarith [hp.1.1]
    have hc : 0 ≤ cnormSq (modeVel (flipLabel ξ) v 0 (planePoint p)) := by
      unfold cnormSq
      positivity
    exact mul_nonneg (mul_nonneg hbp.le hc) hr
  refine hG Gp _ A hGp hA0 fun c => ?_
  set ψ : ℝ × ℝ → ℂ := fun p => ∑ i, (starRingEnd ℂ) (c i) * (φ i p : ℂ) with hψ
  have hlin : star c ⬝ᵥ (fun i => patchTrace ξ v G ρ₁ ρ₂ h (fun p => (φ i p : ℂ))) =
      patchTrace ξ v G ρ₁ ρ₂ h ψ := by
    have e : ∀ r : ℝ, u r * ψ (r, 0) * (r : ℂ) =
        ∑ i, (starRingEnd ℂ) (c i) * (u r * (φ i (r, 0) : ℂ) * (r : ℂ)) := by
      intro r
      rw [hψ, Finset.mul_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have e2 : patchTrace ξ v G ρ₁ ρ₂ h ψ = ∫ r in ρ₁..ρ₂, u r * ψ (r, 0) * (r : ℂ) := rfl
    rw [e2]
    simp_rw [e]
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      (termwise_intervalIntegrable hρ.le hui (hφ i)).const_mul _]
    simp only [dotProduct, Pi.star_apply, intervalIntegral.integral_const_mul]
    rfl
  obtain ⟨K', hK'⟩ := combination_slopeBound φ hφ c Finset.univ
  have hside' : ∀ z, ψ (ρ₁, z) = 0 ∧ ψ (ρ₂, z) = 0 := fun z => by
    simp [hψ, (hside _ z).1, (hside _ z).2]
  have htop' : ∀ r, ψ (r, h) = 0 := fun r => by
    simp [hψ, htop _ r]
  have hb : ‖patchTrace ξ v G ρ₁ ρ₂ h ψ‖ ^ 2 ≤
      A * ∫ p in patch ρ₁ ρ₂ h, patchGradSq ξ.2 ψ p / b p * p.1 :=
    hT Γ P v G H g hv hflip ξ ρ₁ ρ₂ h b ψ K' hρ₁ hρ hh hbm ⟨b₀, hb₀, hbb₀⟩ hb1 hK' hside' htop'
  rw [hlin]
  exact hb.trans (mul_le_mul_of_nonneg_left (hE c) hA0)

end Bridge

end CertCell

end Breakdown
