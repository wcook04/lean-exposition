import Breakdown.CertCell.LocalFieldDefs2

open scoped ContDiff
open MeasureTheory Matrix Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy

namespace Internal

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_measurable (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem integrableOn_continuous_mul {K : CellBox} {g f : ℝ × ℝ → ℂ} (hg : Continuous g)
    (hf : IntegrableOn f K.rect) : IntegrableOn (fun p => g p * f p) K.rect :=
  IntegrableOn.continuousOn_mul hg.continuousOn hf (rect_compact K)

theorem integral_pair_of {s : Set (ℝ × ℝ)} {f g h : ℝ × ℝ → ℂ} (hf : IntegrableOn f s)
    (hg : IntegrableOn g s) (hh : ∀ p, h p = f p + Complex.I * g p) :
    ∫ p in s, h p = (∫ p in s, f p) + Complex.I * ∫ p in s, g p := by
  rw [← integral_const_mul, ← integral_add hf (hg.const_mul _)]
  exact congrArg _ (funext hh)

theorem lineWeight_continuous (K : CellBox) :
    Continuous (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) := by
  by_cases h : K.r₁ = 0
  · simp only [CellBox.lineWeight, if_pos h]
    fun_prop
  · simp only [CellBox.lineWeight, if_neg h]
    fun_prop

theorem radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  exact continuous_finsetSum _ fun i _ => by fun_prop

theorem heightPoly_continuous (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  exact continuous_finsetSum _ fun i _ => by fun_prop

theorem coef_pair (B : CellBases) (K : CellBox) {F₁ F₂ : ℝ × ℝ → ℂ} (h₁ : IntegrableOn F₁ K.rect)
    (h₂ : IntegrableOn F₂ K.rect) (j l : ℕ) :
    B.coef K (fun p => F₁ p + Complex.I * F₂ p) j l = B.coef K F₁ j l + Complex.I * B.coef K F₂ j l := by
  have hb : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
    have := radialPoly_continuous B j
    have := heightPoly_continuous B l
    fun_prop
  have i₁ := (integrableOn_continuous_mul (lineWeight_continuous K) h₁).mul_continuousOn hb.continuousOn
    (rect_compact K)
  have i₂ := (integrableOn_continuous_mul (lineWeight_continuous K) h₂).mul_continuousOn hb.continuousOn
    (rect_compact K)
  unfold CellBases.coef
  exact integral_pair_of i₁ i₂ (fun p => by push_cast; ring)

theorem radial_term_integrable {K : CellBox} {F dF : ℝ × ℝ → ℂ} (h : RadialTracePair K F dF) (c o : ℝ)
    (hco : K.r₁ ≠ 0 ∨ o = 0) {t : ℝ → ℝ} (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((t p.2 : ℝ) : ℂ)) K.rect := by
  have hA : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * t p.2 : ℝ) : ℂ) * F p) K.rect :=
    integrableOn_continuous_mul (by fun_prop) h.1
  have hB : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) * t p.2 : ℝ) : ℂ) * dF p) K.rect := by
    rcases hco with h0 | h0
    · exact integrableOn_continuous_mul (by fun_prop) (h.2.2.1 h0)
    · have := integrableOn_continuous_mul (g := fun p : ℝ × ℝ => (((1 / (c - o)) * t p.2 : ℝ) : ℂ))
        (by fun_prop) h.2.1
      refine this.congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only [h0]
      push_cast
      ring
  refine (hA.add hB).congr_fun (fun p _ => ?_) (rect_measurable K)
  simp only [Pi.add_apply]
  push_cast
  ring

theorem height_term_integrable {K : CellBox} {F dF : ℝ × ℝ → ℂ} (h : HeightWeakPair K F dF) (c o : ℝ)
    {t : ℝ → ℝ} (ht : Continuous t) :
    IntegrableOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p)
      * ((p.1 * t p.1 : ℝ) : ℂ)) K.rect := by
  have hw : Continuous (fun r : ℝ => r * t r) := by fun_prop
  have hd : 0 < K.r₁ ∨ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ r, r * t r = r * t₀ r := Or.inr ⟨t, ht, fun _ => rfl⟩
  have hA := (h (fun r => r * t r) (fun _ => 1 / (c - o)) hw continuous_const hd).1
  have hB := (h (fun r => r * t r) (fun z => (z - o) / (c - o)) hw (by fun_prop) hd).2.1
  refine (hA.add hB).congr_fun (fun p _ => ?_) (rect_measurable K)
  simp only [Pi.add_apply]
  push_cast
  ring

theorem fin_two_eq_zero {e : Fin 2} (h : ¬e = 1) : e = 0 := by
  fin_cases e
  · rfl
  · exact absurd rfl h

theorem radialFaceMoment_pair {K : CellBox} (hK : IsCellBox K) {F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : RadialTracePair K F₁ dF₁) (h₂ : RadialTracePair K F₂ dF₂) (e : Fin 2) (he : e = 0 → K.r₁ ≠ 0)
    {t : ℝ → ℝ} (ht : Continuous t) :
    radialFaceMoment K (fun p => F₁ p + Complex.I * F₂ p) (fun p => dF₁ p + Complex.I * dF₂ p) e t =
      radialFaceMoment K F₁ dF₁ e t + Complex.I * radialFaceMoment K F₂ dF₂ e t := by
  have hlt := hK.r_order.2
  unfold radialFaceMoment radialStripMoment
  split_ifs with h1
  · have hS : Set.Icc (min K.r₂ K.r₁) (max K.r₂ K.r₁) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
      rw [min_eq_right hlt.le, max_eq_left hlt.le]
      rfl
    have hco : K.r₁ ≠ 0 ∨ K.r₁ = 0 := ne_or_eq _ _
    rw [hS, mul_left_comm Complex.I, ← mul_add]
    congr 1
    exact integral_pair_of (radial_term_integrable h₁ K.r₂ K.r₁ hco ht)
      (radial_term_integrable h₂ K.r₂ K.r₁ hco ht) (fun p => by push_cast; ring)
  · have hS : Set.Icc (min K.r₁ K.r₂) (max K.r₁ K.r₂) ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := by
      rw [min_eq_left hlt.le, max_eq_right hlt.le]
      rfl
    have hco : K.r₁ ≠ 0 ∨ K.r₂ = 0 := Or.inl (he (fin_two_eq_zero h1))
    rw [hS, mul_left_comm Complex.I, ← mul_add]
    congr 1
    exact integral_pair_of (radial_term_integrable h₁ K.r₁ K.r₂ hco ht)
      (radial_term_integrable h₂ K.r₁ K.r₂ hco ht) (fun p => by push_cast; ring)

theorem heightFaceMoment_pair {K : CellBox} (hK : IsCellBox K) {F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : HeightWeakPair K F₁ dF₁) (h₂ : HeightWeakPair K F₂ dF₂) (e : Fin 2)
    {t : ℝ → ℝ} (ht : Continuous t) :
    heightFaceMoment K (fun p => F₁ p + Complex.I * F₂ p) (fun p => dF₁ p + Complex.I * dF₂ p) e t =
      heightFaceMoment K F₁ dF₁ e t + Complex.I * heightFaceMoment K F₂ dF₂ e t := by
  have hlt := hK.z_order.2
  unfold heightFaceMoment heightStripMoment
  split_ifs with h1
  · have hS : Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc (min K.z₂ K.z₁) (max K.z₂ K.z₁) = K.rect := by
      rw [min_eq_right hlt.le, max_eq_left hlt.le]
      rfl
    rw [hS, mul_left_comm Complex.I, ← mul_add]
    congr 1
    exact integral_pair_of (height_term_integrable h₁ K.z₂ K.z₁ ht)
      (height_term_integrable h₂ K.z₂ K.z₁ ht) (fun p => by push_cast; ring)
  · have hS : Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc (min K.z₁ K.z₂) (max K.z₁ K.z₂) = K.rect := by
      rw [min_eq_left hlt.le, max_eq_right hlt.le]
      rfl
    rw [hS, mul_left_comm Complex.I, ← mul_add]
    congr 1
    exact integral_pair_of (height_term_integrable h₁ K.z₁ K.z₂ ht)
      (height_term_integrable h₂ K.z₁ K.z₂ ht) (fun p => by push_cast; ring)

theorem trace_term_integrable {K : CellBox} {F dF : ℝ × ℝ → ℂ} (h : RadialTracePair K F dF)
    {ψ t : ℝ → ℝ} (hψ : ContDiff ℝ 1 ψ) (ht : Continuous t) (hd : K.r₁ ≠ 0 ∨ ψ 0 = 0) :
    IntegrableOn (fun p : ℝ × ℝ => dF p * ((ψ p.1 * t p.2 : ℝ) : ℂ)
      + F p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect := by
  have hψ' : Continuous (deriv ψ) := hψ.continuous_deriv le_rfl
  have hψc : Continuous ψ := hψ.continuous
  have hB : IntegrableOn (fun p : ℝ × ℝ => F p * ((deriv ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect :=
    h.1.mul_continuousOn (by fun_prop : Continuous (fun p : ℝ × ℝ => ((deriv ψ p.1 * t p.2 : ℝ) : ℂ))).continuousOn
      (rect_compact K)
  have hA : IntegrableOn (fun p : ℝ × ℝ => dF p * ((ψ p.1 * t p.2 : ℝ) : ℂ)) K.rect := by
    by_cases h0 : K.r₁ = 0
    · have hψ0 : ψ 0 = 0 := hd.resolve_left (not_not.mpr h0)
      have hχ : Continuous (dslope ψ 0) :=
        continuousOn_univ.mp ((continuousOn_dslope Filter.univ_mem).mpr
          ⟨hψc.continuousOn, hψ.differentiable one_ne_zero 0⟩)
      have hfac : ∀ r, ψ r = r * dslope ψ 0 r := fun r => by
        have := sub_smul_dslope ψ 0 r
        simp only [sub_zero, smul_eq_mul, hψ0] at this
        exact this.symm
      have := integrableOn_continuous_mul (g := fun p : ℝ × ℝ => ((dslope ψ 0 p.1 * t p.2 : ℝ) : ℂ))
        (by fun_prop) h.2.1
      refine this.congr_fun (fun p _ => ?_) (rect_measurable K)
      simp only
      rw [hfac p.1]
      push_cast
      ring
    · exact (h.2.2.1 h0).mul_continuousOn
        (by fun_prop : Continuous (fun p : ℝ × ℝ => ((ψ p.1 * t p.2 : ℝ) : ℂ))).continuousOn (rect_compact K)
  exact hA.add hB

theorem radialTracePair_pair {K : CellBox} (hK : IsCellBox K) {F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : RadialTracePair K F₁ dF₁) (h₂ : RadialTracePair K F₂ dF₂) :
    RadialTracePair K (fun p => F₁ p + Complex.I * F₂ p) (fun p => dF₁ p + Complex.I * dF₂ p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h₁.1.add (h₂.1.const_mul Complex.I)
  · refine (h₁.2.1.add (h₂.2.1.const_mul Complex.I)).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    ring
  · intro h0
    exact (h₁.2.2.1 h0).add ((h₂.2.2.1 h0).const_mul Complex.I)
  · intro ψ t hψ ht hd
    have i₁ := trace_term_integrable h₁ hψ ht hd
    have i₂ := trace_term_integrable h₂ hψ ht hd
    have hStrain := radialFaceMoment_pair hK h₁ h₂ 1 (fun h => absurd h (by decide)) ht
    have hM0 : ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K (fun p => F₁ p + Complex.I * F₂ p)
          (fun p => dF₁ p + Complex.I * dF₂ p) 0 t =
        ((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K F₁ dF₁ 0 t
          + Complex.I * (((ψ K.r₁ : ℝ) : ℂ) * radialFaceMoment K F₂ dF₂ 0 t) := by
      by_cases h0 : K.r₁ = 0
      · have hψ0 : ψ K.r₁ = 0 := by rw [h0]; exact hd.resolve_left (not_not.mpr h0)
        simp [hψ0]
      · rw [radialFaceMoment_pair hK h₁ h₂ 0 (fun _ => h0) ht]
        ring
    refine (integral_pair_of i₁ i₂ fun p => ?_).trans ?_
    · ring
    rw [h₁.2.2.2 ψ t hψ ht hd, h₂.2.2.2 ψ t hψ ht hd]
    linear_combination hM0 - ((ψ K.r₂ : ℝ) : ℂ) * hStrain

theorem heightWeakPair_pair {K : CellBox} {F₁ dF₁ F₂ dF₂ : ℝ × ℝ → ℂ}
    (h₁ : HeightWeakPair K F₁ dF₁) (h₂ : HeightWeakPair K F₂ dF₂) :
    HeightWeakPair K (fun p => F₁ p + Complex.I * F₂ p) (fun p => dF₁ p + Complex.I * dF₂ p) := by
  intro t s ht hs hd
  obtain ⟨a₁, b₁, c₁⟩ := h₁ t s ht hs hd
  obtain ⟨a₂, b₂, c₂⟩ := h₂ t s ht hs hd
  refine ⟨?_, ?_, ?_⟩
  · refine (a₁.add (a₂.const_mul Complex.I)).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    ring
  · refine (b₁.add (b₂.const_mul Complex.I)).congr_fun (fun p _ => ?_) (rect_measurable K)
    simp only [Pi.add_apply]
    ring
  · intro hs1 hs0 hs2
    have hs' : Continuous (deriv s) := hs1.continuous_deriv le_rfl
    have a₁' := (h₁ t (deriv s) ht hs' hd).1
    have a₂' := (h₂ t (deriv s) ht hs' hd).1
    refine (integral_pair_of b₁ b₂ fun p => ?_).trans ?_
    · ring
    rw [c₁ hs1 hs0 hs2, c₂ hs1 hs0 hs2,
      integral_pair_of a₁' a₂' (h := fun p => ((t p.1 * deriv s p.2 : ℝ) : ℂ) * (F₁ p + Complex.I * F₂ p))
        (fun p => by ring)]
    ring

theorem row_pair {D : Type} [Fintype D] (row u₁ u₂ : D → ℂ) :
    rowApply row (fun d => u₁ d + Complex.I * u₂ d) = rowApply row u₁ + Complex.I * rowApply row u₂ := by
  unfold rowApply
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun d _ => by ring

end Internal

open _root_.Breakdown.CertCell.LocalField.Internal in
theorem localModeDataPair_of (hT : LocalRadialTraceStatement) (hW : LocalHeightModeWeakStatement)
    (hA : LocalAngularFrameStatement) : LocalModeDataPairStatement := by
  intro D _ _ modes Q q m K B I v₁ G₁ H₁ v₂ G₂ H₂ u₁ u₂ hK hB hv₁ hv₂ hR₁ hR₂
  have hT₁ : ∀ (n : ℤ) (a b : Fin 3), RadialTracePair K (gradMode m n G₁ a b) (modeThird m n H₁ a b 0) :=
    fun n a b => hT K hK m v₁ G₁ H₁ hv₁ n a b
  have hT₂ : ∀ (n : ℤ) (a b : Fin 3), RadialTracePair K (gradMode m n G₂ a b) (modeThird m n H₂ a b 0) :=
    fun n a b => hT K hK m v₂ G₂ H₂ hv₂ n a b
  have hW₁ : ∀ (n : ℤ) (a b : Fin 3), HeightWeakPair K (gradMode m n G₁ a b) (modeThird m n H₁ a b 2) :=
    fun n a b => hW m v₁ G₁ H₁ hv₁ K hK n a b
  have hW₂ : ∀ (n : ℤ) (a b : Fin 3), HeightWeakPair K (gradMode m n G₂ a b) (modeThird m n H₂ a b 2) :=
    fun n a b => hW m v₂ G₂ H₂ hv₂ K hK n a b
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n a b j l
    rw [hR₁.strain, hR₂.strain]
    exact (coef_pair B K (hT₁ n a b).1 (hT₂ n a b).1 j l).symm
  · intro n e a b l he
    rw [row_pair, hR₁.radial_face n e a b l he, hR₂.radial_face n e a b l he]
    exact (radialFaceMoment_pair hK (hT₁ n a b) (hT₂ n a b) e he (heightPoly_continuous B l)).symm
  · intro n e a b j
    rw [row_pair, hR₁.height_face, hR₂.height_face]
    exact (heightFaceMoment_pair hK (hW₁ n a b) (hW₂ n a b) e (radialPoly_continuous B j)).symm
  · intro n a b
    exact radialTracePair_pair hK (hT₁ n a b) (hT₂ n a b)
  · intro n a b
    exact heightWeakPair_pair (hW₁ n a b) (hW₂ n a b)
  · intro n a b
    exact integrableOn_continuous_mul (lineWeight_continuous K) ((hT₁ n a b).1.add ((hT₂ n a b).1.const_mul Complex.I))
  · intro n a b
    filter_upwards [hA m v₁ G₁ H₁ hv₁ K hK n a b, hA m v₂ G₂ H₂ hv₂ K hK n a b] with p h1 h2
    calc (p.1 : ℂ) * (modeThird m n H₁ a b 1 p + Complex.I * modeThird m n H₂ a b 1 p)
        = angularGradMode m n H₁ a b p + Complex.I * angularGradMode m n H₂ a b p := by
          unfold angularGradMode
          ring
      _ = _ := by
          rw [h1, h2, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun a' _ => ?_
          rw [Finset.mul_sum, ← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun b' _ => by ring

end LocalField

end CertCell

end Breakdown
