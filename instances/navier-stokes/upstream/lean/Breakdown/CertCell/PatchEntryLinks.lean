import Breakdown.CertCell.StripDataFlipLinks

open MeasureTheory Set Matrix

noncomputable section

namespace Breakdown.CertCell.Bridge

namespace Internal.PatchEntryLinks

theorem realQuad_pullback {m n : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (T : Matrix (Fin m) (Fin n) ℝ)
    (x : Fin n → ℂ) :
    Coupling.realQuadForm (Tᵀ * A * T) x = Coupling.realQuadForm A (T.map (fun t : ℝ => (t : ℂ)) *ᵥ x) := by
  unfold Coupling.realQuadForm
  congr 1
  have hT : (T.map (fun t : ℝ => (t : ℂ)))ᵀ = (T.map (fun t : ℝ => (t : ℂ)))ᴴ := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have e : (Tᵀ * A * T).map (fun t : ℝ => (t : ℂ)) =
      (T.map (fun t : ℝ => (t : ℂ)))ᴴ * A.map (fun t : ℝ => (t : ℂ)) * T.map (fun t : ℝ => (t : ℂ)) := by
    show (Tᵀ * A * T).map Complex.ofRealHom = _
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.transpose_map]
    exact congrArg (fun M => M * A.map (fun t : ℝ => (t : ℂ)) * T.map (fun t : ℝ => (t : ℂ))) hT
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.star_mulVec]

theorem trace_integrableOn {F dF : ℝ × ℝ → ℂ} {lo hi h : ℝ} (hh : 0 < h)
    (hF : IntegrableOn F (Icc lo hi ×ˢ Icc 0 h)) (hdF : IntegrableOn dF (Icc lo hi ×ˢ Icc 0 h)) :
    IntegrableOn (fun r => upperTrace (fun z => F (r, z)) (fun z => dF (r, z)) h) (Icc lo hi) := by
  have hK : IsCompact (Icc lo hi ×ˢ Icc (0 : ℝ) h) := isCompact_Icc.prod isCompact_Icc
  have hc : Continuous (fun p : ℝ × ℝ => ((1 - p.2 / h : ℝ) : ℂ)) := by fun_prop
  have hk : IntegrableOn (fun p : ℝ × ℝ => dF p * ((1 - p.2 / h : ℝ) : ℂ) - F p / (h : ℂ))
      (Icc lo hi ×ˢ Icc 0 h) :=
    (hdF.mul_continuousOn hc.continuousOn hK).sub (hF.div_const _)
  have hk' : Integrable (fun p : ℝ × ℝ => dF p * ((1 - p.2 / h : ℝ) : ℂ) - F p / (h : ℂ))
      ((volume.restrict (Icc lo hi)).prod (volume.restrict (Icc (0 : ℝ) h))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact hk
  refine hk'.integral_prod_left.neg.congr (Filter.Eventually.of_forall (fun r => ?_))
  rw [Pi.neg_apply]
  simp only [upperTrace]
  rw [intervalIntegral.integral_of_le hh.le, integral_Icc_eq_integral_Ioc]

theorem ae_ne_all {k : ℕ} (lo : Fin k → ℝ) : ∀ᵐ r : ℝ, ∀ s, r ≠ lo s := by
  rw [ae_all_iff]
  intro s
  rw [ae_iff]
  simp

theorem sum_segments (φ : ℝ → ℂ) {inner outer : ℝ} {k : ℕ} (lo hi : Fin k → ℝ)
    (hφ : IntegrableOn φ (Icc inner outer)) (hio : inner ≤ outer) (hlohi : ∀ s, lo s ≤ hi s)
    (cover : ∀ r, inner ≤ r → r ≤ outer → ∃ s, lo s ≤ r ∧ r ≤ hi s)
    (disj : ∀ s s', s ≠ s' → hi s ≤ lo s' ∨ hi s' ≤ lo s)
    (inside : ∀ s, inner ≤ lo s ∧ hi s ≤ outer) :
    ∑ s, ∫ r in lo s..hi s, φ r = ∫ r in inner..outer, φ r := by
  simp_rw [intervalIntegral.integral_of_le (hlohi _), intervalIntegral.integral_of_le hio,
    ← integral_indicator measurableSet_Ioc]
  rw [← integral_finsetSum]
  · refine integral_congr_ae ?_
    filter_upwards [ae_ne_all lo] with r hr
    by_cases hm : r ∈ Ioc inner outer
    · obtain ⟨s, hs1, hs2⟩ := cover r hm.1.le hm.2
      have hs : r ∈ Ioc (lo s) (hi s) := ⟨lt_of_le_of_ne hs1 (hr s).symm, hs2⟩
      rw [Finset.sum_eq_single s, indicator_of_mem hm, indicator_of_mem hs]
      · intro s' _ hs'
        refine indicator_of_notMem (fun h' => ?_) _
        rcases disj s s' (Ne.symm hs') with h | h
        · linarith [hs.2, h'.1]
        · linarith [h'.2, hs.1]
      · intro h
        exact absurd (Finset.mem_univ s) h
    · rw [indicator_of_notMem hm]
      refine Finset.sum_eq_zero (fun s _ => indicator_of_notMem (fun h => hm ?_) _)
      exact ⟨lt_of_le_of_lt (inside s).1 h.1, h.2.trans (inside s).2⟩
  · intro s _
    exact (integrable_indicator_iff measurableSet_Ioc).2
      (hφ.mono_set (fun r hr => ⟨(inside s).1.trans hr.1.le, hr.2.trans (inside s).2⟩))

open Internal.StripFlipLinks in
theorem data_eq (hS : StripMomentTraceHolds) (hT : TraceHeightHolds) (hD : ModeHeightDerivHolds)
    (R : PatchEntry) (hR : IsPatchEntry R) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (d : Fin R.dataCount) :
    R.data v G d =
      ∫ r in (R.segment (R.dataOf d).1).lower..(R.segment (R.dataOf d).1).upper,
        upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height
          * (((R.segment (R.dataOf d).1).test (R.dataOf d).2 r : ℝ) : ℂ) := by
  have hDa := hD Γ P v G H g hp R.label 2
  rw [ae_restrict_iff' measurableSet_Ioi] at hDa
  have hseg := hR.segments (R.dataOf d).1
  obtain ⟨jF, jFz, -⟩ := plane_rect_integrable hp R.label 2 (b₁ := (R.segment (R.dataOf d).1).upper)
    (c₁ := 0) (d₁ := (R.segment (R.dataOf d).1).height) hseg.lower_pos
  have e0 := hS (R.segment (R.dataOf d).1).height (R.segment (R.dataOf d).1).lower
    (R.segment (R.dataOf d).1).upper (fun _ => 1) ((R.segment (R.dataOf d).1).test (R.dataOf d).2)
    _ _ hseg.height_pos hseg.lower_lt_upper jF jFz continuous_const (hseg.test_continuous _)
  refine e0.trans (intervalIntegral.integral_congr_ae ?_)
  filter_upwards [hDa] with r hr hmem
  rw [uIoc_of_le hseg.lower_lt_upper.le] at hmem
  have h2 := hr (hseg.lower_pos.trans hmem.1)
  have e := trace_eq_at_heights hT (fun k hk => (h2 k hk).1) hseg.height_pos hR.height_pos
  show (((1 : ℝ) * (R.segment (R.dataOf d).1).test (R.dataOf d).2 r : ℝ) : ℂ) *
      upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) (R.segment (R.dataOf d).1).height = _
  rw [e]
  push_cast
  ring

open Internal.StripFlipLinks in
theorem trace_data (hS : StripMomentTraceHolds) (hT : TraceHeightHolds) (hD : ModeHeightDerivHolds)
    (R : PatchEntry) (hR : IsPatchEntry R) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) :
    R.traceMap.map (fun t : ℝ => (t : ℂ)) *ᵥ R.data v G =
      fun i => patchTrace R.label v G R.inner R.outer R.height (fun p => (R.test i p : ℂ)) := by
  obtain ⟨iF, iFz, -⟩ := plane_rect_integrable hp R.label 2 (b₁ := R.outer) (c₁ := 0) (d₁ := R.height)
    hR.inner_pos
  have huI : IntegrableOn
      (fun r => upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height)
      (Icc R.inner R.outer) :=
    trace_integrableOn (F := fun p => planeVel R.label v 2 p.1 p.2)
      (dF := fun p => planeVelHeight R.label G 2 p.1 p.2) hR.height_pos iF iFz
  have hsub : ∀ s, Icc (R.segment s).lower (R.segment s).upper ⊆ Icc R.inner R.outer := fun s r hr =>
    ⟨(hR.segments_inside s).1.trans hr.1, hr.2.trans (hR.segments_inside s).2⟩
  have hdata := data_eq hS hT hD R hR hp
  funext i
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, hdata]
  calc ∑ d, ((R.traceMap i d : ℝ) : ℂ) *
        ∫ r in (R.segment (R.dataOf d).1).lower..(R.segment (R.dataOf d).1).upper,
          upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height
            * (((R.segment (R.dataOf d).1).test (R.dataOf d).2 r : ℝ) : ℂ)
      = ∑ d, ∑ s, ∫ r in (R.segment s).lower..(R.segment s).upper,
          upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height
            * (((if (R.dataOf d).1 = s then R.traceMap i d * (R.segment (R.dataOf d).1).test (R.dataOf d).2 r
                else 0 : ℝ)) : ℂ) := by
        refine Finset.sum_congr rfl (fun d _ => ?_)
        rw [Finset.sum_eq_single (R.dataOf d).1]
        · simp only [if_true]
          rw [← intervalIntegral.integral_const_mul]
          refine intervalIntegral.integral_congr (fun r _ => ?_)
          push_cast
          ring
        · intro s _ hs
          simp [Ne.symm hs]
        · intro h
          exact absurd (Finset.mem_univ _) h
    _ = ∑ s, ∑ d, ∫ r in (R.segment s).lower..(R.segment s).upper,
          upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height
            * (((if (R.dataOf d).1 = s then R.traceMap i d * (R.segment (R.dataOf d).1).test (R.dataOf d).2 r
                else 0 : ℝ)) : ℂ) := Finset.sum_comm
    _ = ∑ s, ∫ r in (R.segment s).lower..(R.segment s).upper,
          upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height
            * ((r * R.test i (r, 0) : ℝ) : ℂ) := by
        refine Finset.sum_congr rfl (fun s _ => ?_)
        have hseg := hR.segments s
        rw [← intervalIntegral.integral_finsetSum]
        · refine intervalIntegral.integral_congr (fun r hr => ?_)
          rw [uIcc_of_le hseg.lower_lt_upper.le] at hr
          rw [← Finset.mul_sum, ← Complex.ofReal_sum, hR.trace_expansion i s r hr.1 hr.2]
        · intro d _
          rw [intervalIntegrable_iff_integrableOn_Icc_of_le hseg.lower_lt_upper.le]
          refine (huI.mono_set (hsub s)).mul_continuousOn ?_ isCompact_Icc
          refine (Complex.continuous_ofReal.comp ?_).continuousOn
          exact Continuous.if_const _ (continuous_const.mul ((hR.segments _).test_continuous _))
            continuous_const
    _ = ∫ r in R.inner..R.outer,
          upperTrace (planeVel R.label v 2 r) (planeVelHeight R.label G 2 r) R.height
            * ((r * R.test i (r, 0) : ℝ) : ℂ) := by
        refine sum_segments _ (fun s => (R.segment s).lower) (fun s => (R.segment s).upper) ?_
          hR.inner_lt_outer.le (fun s => (hR.segments s).lower_lt_upper.le) hR.segments_cover
          hR.segments_disjoint hR.segments_inside
        refine huI.mul_continuousOn ?_ isCompact_Icc
        refine (Complex.continuous_ofReal.comp ?_).continuousOn
        exact continuous_id.mul (((hR.test_slope_bound i).continuous).comp (continuous_id.prodMk continuous_const))
    _ = patchTrace R.label v G R.inner R.outer R.height (fun p => (R.test i p : ℂ)) := by
        unfold patchTrace
        refine intervalIntegral.integral_congr (fun r _ => ?_)
        simp only []
        push_cast
        ring


end Internal.PatchEntryLinks

open Internal.PatchEntryLinks in
theorem patchEntryCredit (hC : PatchCreditHolds) (hF : Coupling.InverseFormFactorHolds)
    (hS : StripMomentTraceHolds) (hT : TraceHeightHolds) (hD : ModeHeightDerivHolds) :
    PatchEntryCreditHolds := by
  intro R hR Γ P v G H g hp hflip
  have key := trace_data hS hT hD R hR hp
  have hmat : (R.factor * R.traceMap)ᵀ * (R.factor * R.traceMap) =
      R.traceMapᵀ * (R.factorᵀ * R.factor) * R.traceMap := by
    rw [Matrix.transpose_mul]
    simp only [Matrix.mul_assoc]
  calc Coupling.quadForm R.credit (R.data v G)
      ≤ Coupling.realQuadForm ((R.factor * R.traceMap)ᵀ * (R.factor * R.traceMap)) (R.data v G)
          / (1 + R.factorSlack) := hR.credit_le _
    _ = Coupling.realQuadForm (R.factorᵀ * R.factor)
          (fun i => patchTrace R.label v G R.inner R.outer R.height (fun p => (R.test i p : ℂ)))
          / (1 + R.factorSlack) := by
        rw [hmat, realQuad_pullback, key]
    _ ≤ Coupling.realQuadForm R.testForm⁻¹
          (fun i => patchTrace R.label v G R.inner R.outer R.height (fun p => (R.test i p : ℂ))) :=
        hF R.testForm R.factor R.factorSlack hR.form_posDef hR.slack_nonneg hR.factor_bound _
    _ ≤ _ := hC Γ P v G H g hp hflip R.label R.inner R.outer R.height R.charge R.test R.testSlope
        R.testForm hR.inner_pos hR.inner_lt_outer hR.height_pos hR.charge_measurable
        ⟨R.chargeLower, hR.charge_lower_pos, fun p => (hR.charge_between p).1⟩
        ⟨R.chargeUpper, fun p => (hR.charge_between p).2⟩ hR.test_slope_bound hR.test_sides hR.test_top
        hR.form_posDef hR.form_bound

end Breakdown.CertCell.Bridge
