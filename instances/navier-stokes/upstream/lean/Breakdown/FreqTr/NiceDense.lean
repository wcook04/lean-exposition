import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.NiceDense

def outerSet (n : ℕ) : Set Space := {ξ | ‖ξ‖ < 1 / ((n : ℝ) + 1) ∨ (n : ℝ) + 1 < ‖ξ‖}

def projField (m : Space → CSpace) (ξ : Space) : CSpace := m ξ - longitudinal ξ (m ξ)

def symField (m : Space → CSpace) (ξ : Space) : CSpace := (1 / 2 : ℝ) • (m ξ + conjVec (m (-ξ)))

theorem norm_longitudinal_le (ξ : Space) : ‖longitudinal ξ‖ ≤ ‖complexifyVec‖ ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have hf : ‖freqVec ξ‖ ≤ ‖complexifyVec‖ * ‖ξ‖ := complexifyVec.le_opNorm ξ
  have hin : ‖inner ℂ (freqVec ξ) z‖ ≤ ‖freqVec ξ‖ * ‖z‖ := norm_inner_le_norm _ _
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [longitudinal]
    positivity
  · have hξn : 0 < ‖ξ‖ := norm_pos_iff.mpr hξ
    simp only [longitudinal, smul_apply, ContinuousLinearMap.coe_restrictScalars',
      ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
    rw [norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity)]
    have h2 : ‖inner ℂ (freqVec ξ) z‖ * ‖freqVec ξ‖ ≤ (‖complexifyVec‖ * ‖ξ‖) ^ 2 * ‖z‖ := by
      calc ‖inner ℂ (freqVec ξ) z‖ * ‖freqVec ξ‖ ≤ (‖freqVec ξ‖ * ‖z‖) * ‖freqVec ξ‖ :=
            mul_le_mul_of_nonneg_right hin (norm_nonneg _)
        _ = ‖freqVec ξ‖ ^ 2 * ‖z‖ := by ring
        _ ≤ (‖complexifyVec‖ * ‖ξ‖) ^ 2 * ‖z‖ := by gcongr
    calc (‖ξ‖ ^ 2)⁻¹ * (‖inner ℂ (freqVec ξ) z‖ * ‖freqVec ξ‖)
        ≤ (‖ξ‖ ^ 2)⁻¹ * ((‖complexifyVec‖ * ‖ξ‖) ^ 2 * ‖z‖) := by gcongr
      _ = ‖complexifyVec‖ ^ 2 * ‖z‖ := by field_simp

theorem aestronglyMeasurable_longitudinal : AEStronglyMeasurable longitudinal volume := by
  have hc : AEStronglyMeasurable (fun ξ : Space => ((‖ξ‖ ^ 2)⁻¹ : ℝ)) volume :=
    ((measurable_norm.pow_const 2).inv).aestronglyMeasurable
  have hfv : Continuous freqVec := complexifyVec.continuous
  have hG : Continuous (fun ξ : Space =>
      ((ContinuousLinearMap.smulRight (innerSL ℂ (freqVec ξ)) (freqVec ξ)).restrictScalars ℝ :
        CSpace →L[ℝ] CSpace)) := by
    rw [continuous_clm_apply]
    intro z
    simp only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
      innerSL_apply_apply]
    exact ((hfv.inner (𝕜 := ℂ) continuous_const).smul hfv)
  exact hc.smul hG.aestronglyMeasurable

theorem sig_ae (h1 : FieldOpRealized) (χ : X) :
    (∀ᵐ ξ ∂volume, conjVec ((χ : L2C) (-ξ)) = (χ : L2C) ξ) ∧
    (∀ᵐ ξ ∂volume, longitudinal ξ ((χ : L2C) ξ) = 0) := by
  have hmem := χ.2
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hmem
  obtain ⟨hA, hB⟩ := hmem
  constructor
  · have hneg : (⇑(ContinuousLinearEquiv.neg ℝ : Space ≃L[ℝ] Space)) = fun ξ => -ξ := by
      funext ξ; rfl
    have hR := h1 (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖
      aestronglyMeasurable_const (fun _ => le_rfl)
    rw [hneg] at hR
    have h1' := hR (χ : L2C)
    change ((reflConj (χ : L2C) : L2C) : Space → CSpace) =ᵐ[volume] _ at h1'
    rw [hA] at h1'
    filter_upwards [h1'] with ξ hξ using hξ.symm
  · have hid : (⇑(ContinuousLinearEquiv.refl ℝ Space)) = id := rfl
    have hL := h1 (ContinuousLinearEquiv.refl ℝ Space) longitudinal _
      aestronglyMeasurable_longitudinal norm_longitudinal_le
    rw [hid] at hL
    have h2 := hL (χ : L2C)
    rw [hB] at h2
    filter_upwards [h2, Lp.coeFn_zero CSpace 2 volume] with ξ h h0
    have h' : (longitudinal ξ) ((χ : L2C) ξ) = ((0 : L2C) : Space → CSpace) ξ := h.symm
    rw [h', h0]
    rfl

theorem tail_small {g : Space → CSpace} (hg : MemLp g 2 volume) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ n in Filter.atTop, eLpNorm ((outerSet n).indicator g) 2 volume < ENNReal.ofReal δ := by
  have hmeas : ∀ n, MeasurableSet (outerSet n) := by
    intro n
    exact (measurableSet_lt measurable_norm measurable_const).union
      (measurableSet_lt measurable_const measurable_norm)
  have h2 : ((2 : ℝ≥0∞)).toReal = 2 := by norm_num
  have hfin : ∫⁻ ξ, ‖g ξ‖ₑ ^ (2 : ℝ) ∂volume ≠ ⊤ := by
    have := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2) two_ne_zero ENNReal.ofNat_ne_top
      hg.eLpNorm_lt_top
    rw [h2] at this
    exact this.ne
  have hlim : Filter.Tendsto (fun n : ℕ => ∫⁻ ξ, ‖(outerSet n).indicator g ξ‖ₑ ^ (2 : ℝ) ∂volume)
      Filter.atTop (nhds (∫⁻ _ξ : Space, (0 : ℝ≥0∞) ∂volume)) := by
    refine tendsto_lintegral_of_dominated_convergence' (fun ξ => ‖g ξ‖ₑ ^ (2 : ℝ)) ?_ ?_ hfin ?_
    · intro n
      exact ((hg.1.indicator (hmeas n)).enorm).pow_const _
    · intro n
      exact Filter.Eventually.of_forall fun ξ =>
        ENNReal.rpow_le_rpow (enorm_indicator_le_enorm_self g ξ) (by norm_num)
    · have h0 : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
        rw [ae_iff]; simp
      filter_upwards [h0] with ξ hξ
      have hξ' : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
      obtain ⟨N, hN⟩ := exists_nat_gt (max ‖ξ‖ (1 / ‖ξ‖))
      apply tendsto_const_nhds.congr'
      filter_upwards [Filter.eventually_ge_atTop N] with n hn
      have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hA : ‖ξ‖ < (n : ℝ) + 1 := by
        have := le_max_left ‖ξ‖ (1 / ‖ξ‖); linarith
      have hB : 1 / ((n : ℝ) + 1) < ‖ξ‖ := by
        have h3 := le_max_right ‖ξ‖ (1 / ‖ξ‖)
        have h4 : 1 / ‖ξ‖ < (n : ℝ) + 1 := by linarith
        rw [div_lt_iff₀ (by positivity)]
        rw [div_lt_iff₀ hξ'] at h4
        linarith
      have hnot : ξ ∉ outerSet n := by
        simp only [outerSet, Set.mem_ofPred_eq, not_or, not_lt]
        exact ⟨hB.le, hA.le⟩
      simp [Set.indicator_of_notMem hnot]
  have hlim2 : Filter.Tendsto
      (fun n : ℕ => (∫⁻ ξ, ‖(outerSet n).indicator g ξ‖ₑ ^ (2 : ℝ) ∂volume) ^ (1 / (2 : ℝ)))
      Filter.atTop (nhds 0) := by
    have := ((ENNReal.continuous_rpow_const (y := 1 / (2 : ℝ))).tendsto _).comp hlim
    simpa [Function.comp_def, ENNReal.zero_rpow_of_pos] using this
  have hpos : (0 : ℝ≥0∞) < ENNReal.ofReal δ := ENNReal.ofReal_pos.2 hδ
  filter_upwards [(tendsto_order.1 hlim2).2 _ hpos] with n hn
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal two_ne_zero ENNReal.ofNat_ne_top, h2]
  exact hn

theorem smooth_annulus {f : Space → CSpace} (hf : MemLp f 2 volume) {r R : ℝ} (hr : 0 < r)
    (hrR : r ≤ R) (hsupp : ∀ ξ, ‖ξ‖ < r ∨ R < ‖ξ‖ → f ξ = 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ m : Space → CSpace, ContDiff ℝ ∞ m ∧ (∀ ξ, ‖ξ‖ < r / 2 → m ξ = 0) ∧
      (∀ ξ, 2 * R ≤ ‖ξ‖ → m ξ = 0) ∧ eLpNorm (m - f) 2 volume < ENNReal.ofReal δ := by
  have hR : 0 < R := lt_of_lt_of_le hr hrR
  obtain ⟨g, -, hg, hfg⟩ := hf.exist_eLpNorm_sub_le (p := 2) (by norm_num) (by norm_num)
    (half_pos hδ)
  let bR : ContDiffBump (0 : Space) := ⟨R, 2 * R, hR, by linarith⟩
  let br : ContDiffBump (0 : Space) := ⟨r / 2, r, half_pos hr, by linarith⟩
  let η : Space → ℝ := fun ξ => bR ξ * (1 - br ξ)
  have hη0 : ∀ ξ, 0 ≤ η ξ := fun ξ => mul_nonneg (bR.nonneg) (sub_nonneg.2 br.le_one)
  have hη1 : ∀ ξ, η ξ ≤ 1 := fun ξ => by
    have h1 := bR.le_one (x := ξ)
    have h2 := br.nonneg (x := ξ)
    have h3 := bR.nonneg (x := ξ)
    have h4 := br.le_one (x := ξ)
    simp only [η]
    nlinarith
  have hηf : ∀ ξ, f ξ ≠ 0 → η ξ = 1 := by
    intro ξ hξ
    have hm : r ≤ ‖ξ‖ ∧ ‖ξ‖ ≤ R := by
      by_contra hc
      apply hξ
      apply hsupp
      rcases not_and_or.1 hc with h | h
      · exact Or.inl (lt_of_not_ge h)
      · exact Or.inr (lt_of_not_ge h)
    have e1 : bR ξ = 1 := bR.one_of_mem_closedBall (by simpa using hm.2)
    have e2 : br ξ = 0 := br.zero_of_le_dist (by simpa using hm.1)
    simp only [η, e1, e2]
    norm_num
  refine ⟨fun ξ => η ξ • g ξ, ?_, ?_, ?_, ?_⟩
  · exact (bR.contDiff.mul (contDiff_const.sub br.contDiff)).smul hg
  · intro ξ hξ
    have e2 : br ξ = 1 := br.one_of_mem_closedBall (by simpa using hξ.le)
    simp [η, e2]
  · intro ξ hξ
    have e1 : bR ξ = 0 := bR.zero_of_le_dist (by simpa using hξ)
    simp [η, e1]
  · have hpt : ∀ ξ, ‖((fun ξ => η ξ • g ξ) - f) ξ‖ ≤ ‖(f - g) ξ‖ := by
      intro ξ
      by_cases hξ : f ξ = 0
      · simp only [Pi.sub_apply, hξ, sub_zero, zero_sub, norm_neg, norm_smul,
          Real.norm_eq_abs, abs_of_nonneg (hη0 ξ)]
        exact mul_le_of_le_one_left (norm_nonneg _) (hη1 ξ)
      · simp only [Pi.sub_apply, hηf ξ hξ, one_smul]
        rw [norm_sub_rev]
    calc eLpNorm ((fun ξ => η ξ • g ξ) - f) 2 volume ≤ eLpNorm (f - g) 2 volume :=
          eLpNorm_mono hpt
      _ ≤ ENNReal.ofReal (δ / 2) := hfg
      _ < ENNReal.ofReal δ := (ENNReal.ofReal_lt_ofReal_iff hδ).2 (half_lt_self hδ)

private theorem inner_freqVec (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) z = ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * z i := by
  simp [freqVec, complexifyVec, PiLp.inner_apply, mul_comm]

private theorem norm_freqVec (ξ : Space) : ‖freqVec ξ‖ = ‖ξ‖ := by
  simp [freqVec, complexifyVec, EuclideanSpace.norm_eq]

private theorem longitudinal_eq (ξ : Space) (z : CSpace) :
    longitudinal ξ z = ((((‖ξ‖ ^ 2)⁻¹ : ℝ) : ℂ) * inner ℂ (freqVec ξ) z) • freqVec ξ := by
  rw [mul_smul, Complex.coe_smul]; rfl

private theorem inner_freqVec_proj (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) (z - longitudinal ξ z) = 0 := by
  rw [longitudinal_eq, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, norm_freqVec]
  rcases eq_or_ne ξ 0 with rfl | h
  · simp [freqVec]
  · have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr h
    push_cast
    field_simp
    simp

theorem norm_proj_le (ξ : Space) (z : CSpace) : ‖z - longitudinal ξ z‖ ≤ ‖z‖ := by
  have h0 : inner ℂ (z - longitudinal ξ z) (longitudinal ξ z) = 0 := by
    rw [← inner_conj_symm, longitudinal_eq, inner_smul_left, ← longitudinal_eq, inner_freqVec_proj]
    simp
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h0
  rw [sub_add_cancel] at h
  have : ‖z - longitudinal ξ z‖ ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [sq, sq]; nlinarith [h, mul_self_nonneg ‖longitudinal ξ z‖]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

theorem div_proj (ξ : Space) (z : CSpace) :
    ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * (z - longitudinal ξ z) i = 0 := by
  rw [← inner_freqVec]; exact inner_freqVec_proj ξ z

theorem contDiff_projField {m : Space → CSpace} (hm : ContDiff ℝ ∞ m) {r : ℝ} (hr : 0 < r)
    (h0 : ∀ ξ, ‖ξ‖ < r → m ξ = 0) : ContDiff ℝ ∞ (projField m) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ‖ξ‖ < r
  · have hev : projField m =ᶠ[nhds ξ] fun _ => (0 : CSpace) := by
      have hopen : IsOpen {x : Space | ‖x‖ < r} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds hξ] with x hx
      simp [projField, h0 x hx]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hne : ξ ≠ 0 := by
      intro h
      apply hξ
      simpa [h] using hr
    have heq : projField m = fun x => m x - ((‖x‖ ^ 2)⁻¹ : ℝ) •
        ((inner ℂ (freqVec x) (m x) : ℂ) • freqVec x) := by
      funext x
      simp [projField, longitudinal]
    rw [heq]
    have hf : ContDiff ℝ ∞ freqVec := complexifyVec.contDiff
    have hinv : ContDiffAt ℝ ∞ (fun x : Space => (‖x‖ ^ 2)⁻¹) ξ :=
      (contDiff_norm_sq ℝ).contDiffAt.inv (by positivity)
    have hin : ContDiffAt ℝ ∞ (fun x => (inner ℂ (freqVec x) (m x) : ℂ)) ξ :=
      ContDiffAt.inner ℂ hf.contDiffAt hm.contDiffAt
    exact hm.contDiffAt.sub (hinv.smul (hin.smul hf.contDiffAt))

theorem norm_conjVec (z : CSpace) : ‖conjVec z‖ = ‖z‖ := by
  simp [EuclideanSpace.norm_eq, conjVec]

theorem eLpNorm_symField_sub_le {u v : Space → CSpace} (hu : AEStronglyMeasurable u volume)
    (hv : AEStronglyMeasurable v volume) (hvs : ∀ᵐ ξ ∂volume, conjVec (v (-ξ)) = v ξ) :
    eLpNorm (symField u - v) 2 volume ≤ eLpNorm (u - v) 2 volume := by
  have hneg : MeasurePreserving (fun ξ : Space => -ξ) volume volume :=
    Measure.measurePreserving_neg volume
  set w : Space → CSpace := u - v with hw
  have hwm : AEStronglyMeasurable w volume := hu.sub hv
  have hw'm : AEStronglyMeasurable (fun ξ => conjVec (w (-ξ))) volume :=
    conjVec.continuous.comp_aestronglyMeasurable (hwm.comp_measurePreserving hneg)
  have hae : symField u - v =ᵐ[volume] (1 / 2 : ℝ) • (w + fun ξ => conjVec (w (-ξ))) := by
    filter_upwards [hvs] with ξ hξ
    simp only [Pi.sub_apply, Pi.smul_apply, Pi.add_apply, symField, hw, map_sub]
    rw [← hξ]
    module
  have h2 : eLpNorm (fun ξ => conjVec (w (-ξ))) 2 volume = eLpNorm w 2 volume := by
    rw [eLpNorm_congr_norm_ae (g := fun ξ => w (-ξ)) (Filter.Eventually.of_forall fun ξ => norm_conjVec _)]
    exact eLpNorm_comp_measurePreserving hwm hneg
  rw [eLpNorm_congr_ae hae, eLpNorm_const_smul]
  calc ‖(1 / 2 : ℝ)‖ₑ * eLpNorm (w + fun ξ => conjVec (w (-ξ))) 2 volume
      ≤ ‖(1 / 2 : ℝ)‖ₑ * (eLpNorm w 2 volume + eLpNorm (fun ξ => conjVec (w (-ξ))) 2 volume) := by
        gcongr
        exact eLpNorm_add_le hwm hw'm (by norm_num)
    _ = eLpNorm w 2 volume := by
        rw [h2, ← two_mul, ← mul_assoc]
        have : ‖(1 / 2 : ℝ)‖ₑ * 2 = 1 := by
          rw [Real.enorm_eq_ofReal (by norm_num)]
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
        rw [this, one_mul]

theorem eLpNorm_ssp_le {u : Space → CSpace} {R : ℝ} (_hR : 0 ≤ R) (hu : ∀ ξ, R ≤ ‖ξ‖ → u ξ = 0) :
    eLpNorm (fun ξ => sspFactor ξ • u ξ) 2 volume ≤
      ENNReal.ofReal (4 * π ^ 2 * R ^ 2) * eLpNorm u 2 volume := by
  have key : ∀ ξ, ‖sspFactor ξ • u ξ‖ ≤ (4 * π ^ 2 * R ^ 2) * ‖u ξ‖ := by
    intro ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by unfold sspFactor; positivity)]
    by_cases h : R ≤ ‖ξ‖
    · simp [hu ξ h]
    · replace h := lt_of_not_ge h
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      unfold sspFactor
      have h2 : ‖ξ‖ ^ 2 ≤ R ^ 2 := by gcongr
      have hp : 0 ≤ 4 * π ^ 2 := by positivity
      exact mul_le_mul_of_nonneg_left h2 hp
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall key) 2

theorem conjVec_conjVec (z : CSpace) : conjVec (conjVec z) = z := by
  ext i
  simp [conjVec]

theorem nice_symField_projField {m : Space → CSpace} (hm : ContDiff ℝ ∞ m) {r R : ℝ} (hr : 0 < r)
    (h0 : ∀ ξ, ‖ξ‖ < r → m ξ = 0) (hR : ∀ ξ, R ≤ ‖ξ‖ → m ξ = 0) :
    IsNiceSymbol (symField (projField m)) ∧ ∀ ξ, R ≤ ‖ξ‖ → symField (projField m) ξ = 0 := by
  have hp := contDiff_projField hm hr h0
  have hp0 : ∀ ξ, ‖ξ‖ < r → projField m ξ = 0 := fun ξ h => by simp [projField, h0 ξ h]
  have hpR : ∀ ξ, R ≤ ‖ξ‖ → projField m ξ = 0 := fun ξ h => by simp [projField, hR ξ h]
  have hs0 : ∀ ξ, ‖ξ‖ < r → symField (projField m) ξ = 0 := fun ξ h => by
    simp [symField, hp0 ξ h, hp0 (-ξ) (by rwa [norm_neg])]
  have hsR : ∀ ξ, R ≤ ‖ξ‖ → symField (projField m) ξ = 0 := fun ξ h => by
    simp [symField, hpR ξ h, hpR (-ξ) (by rwa [norm_neg])]
  refine ⟨⟨?_, ?_, ⟨r, hr, hs0⟩, ?_, ?_⟩, hsR⟩
  · unfold symField
    exact (contDiff_const (c := (1 / 2 : ℝ))).smul (hp.add (conjVec.contDiff.comp (hp.comp contDiff_neg)))
  · apply HasCompactSupport.intro (isCompact_closedBall (0 : Space) R)
    intro ξ hξ
    apply hsR
    simp only [Metric.mem_closedBall, dist_zero_right, not_le] at hξ
    exact hξ.le
  · intro ξ
    simp only [symField, neg_neg, map_smul, map_add, conjVec_conjVec]
    rw [add_comm]
  · intro ξ
    have hA := div_proj ξ (m ξ)
    have hB := congrArg star (div_proj (-ξ) (m (-ξ)))
    simp only [Fin.sum_univ_three] at hA hB ⊢
    simp only [symField, projField, conjVec] at hA hB ⊢
    simp at hA hB ⊢
    linear_combination (1 / 2 : ℂ) * hA - (1 / 2 : ℂ) * hB

end Internal.NiceDense

open Internal.NiceDense in
theorem niceDense (h1 : FieldOpRealized) :
    NiceDense := by
  intro χ ψ hχψ ε hε
  obtain ⟨hsym, hdiv⟩ := sig_ae h1 χ
  set f : Space → CSpace := ((χ : L2C) : Space → CSpace) with hfdef
  have hf2 : MemLp f 2 volume := Lp.memLp _
  have hψf : (fun ξ => sspFactor ξ • f ξ) =ᵐ[volume] ((ψ : L2C) : Space → CSpace) := by
    filter_upwards [hχψ] with ξ h using h.symm
  have hl2 : MemLp (fun ξ => sspFactor ξ • f ξ) 2 volume := (Lp.memLp _).ae_eq hψf.symm
  have hε2 : 0 < ε / 2 := by positivity
  obtain ⟨n, hn1, hn2⟩ := ((tail_small hf2 hε2).and (tail_small hl2 hε2)).exists
  have hmeas : MeasurableSet (outerSet n) := by
    unfold outerSet
    exact (measurableSet_lt measurable_norm measurable_const).union
      (measurableSet_lt measurable_const measurable_norm)
  set r : ℝ := 1 / ((n : ℝ) + 1) with hrdef
  set R : ℝ := (n : ℝ) + 1 with hRdef
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hr : 0 < r := by positivity
  have hR : 0 < R := by positivity
  have hrR : r ≤ R := by
    have : r ≤ 1 := by rw [hrdef, div_le_one (by positivity)]; linarith
    linarith
  set f₁ : Space → CSpace := (outerSet n)ᶜ.indicator f with hf₁def
  have hf₁supp : ∀ ξ, ‖ξ‖ < r ∨ R < ‖ξ‖ → f₁ ξ = 0 := by
    intro ξ hξ
    apply indicator_of_notMem
    exact fun hc => hc hξ
  have hf₁2 : MemLp f₁ 2 volume := hf2.indicator hmeas.compl
  have hff₁ : f = f₁ + (outerSet n).indicator f := (indicator_compl_add_self _ _).symm
  set C : ℝ := 4 * π ^ 2 * (2 * R) ^ 2 with hCdef
  have hC : 0 ≤ C := by positivity
  set δ : ℝ := ε / 2 / (1 + C) with hδdef
  have hδ : 0 < δ := by positivity
  obtain ⟨m₀, hm₀, hm₀0, hm₀R, hm₀err⟩ := smooth_annulus hf₁2 hr hrR hf₁supp hδ
  obtain ⟨hnice, hmR⟩ := nice_symField_projField hm₀ (half_pos hr) hm₀0 hm₀R
  set m : Space → CSpace := symField (projField m₀) with hmdef
  have hf₁sym : ∀ᵐ ξ ∂volume, conjVec (f₁ (-ξ)) = f₁ ξ := by
    filter_upwards [hsym] with ξ h
    by_cases hξ : ξ ∈ outerSet n
    · have h' : -ξ ∈ outerSet n := by simpa [outerSet] using hξ
      simp [hf₁def, hξ, h']
    · have h' : -ξ ∉ outerSet n := by simpa [outerSet] using hξ
      simp [hf₁def, hξ, h', h]
  have hf₁proj : ∀ᵐ ξ ∂volume, longitudinal ξ (f₁ ξ) = 0 := by
    filter_upwards [hdiv] with ξ h
    by_cases hξ : ξ ∈ outerSet n
    · simp [hf₁def, hξ]
    · simp [hf₁def, hξ, h]
  have hpm : AEStronglyMeasurable (projField m₀) volume :=
    (contDiff_projField hm₀ (half_pos hr) hm₀0).continuous.aestronglyMeasurable
  have herr1 : eLpNorm (m - f₁) 2 volume < ENNReal.ofReal δ := by
    calc eLpNorm (m - f₁) 2 volume ≤ eLpNorm (projField m₀ - f₁) 2 volume :=
          eLpNorm_symField_sub_le hpm hf₁2.aestronglyMeasurable hf₁sym
      _ ≤ eLpNorm (m₀ - f₁) 2 volume := by
          apply eLpNorm_mono_ae
          filter_upwards [hf₁proj] with ξ h
          have e : (projField m₀ - f₁) ξ = (m₀ ξ - f₁ ξ) - longitudinal ξ (m₀ ξ - f₁ ξ) := by
            simp only [Pi.sub_apply, projField, map_sub, h]
            abel
          rw [e]
          exact norm_proj_le ξ _
      _ < ENNReal.ofReal δ := hm₀err
  have hmc : AEStronglyMeasurable m volume := hnice.1.continuous.aestronglyMeasurable
  have hδC : ENNReal.ofReal C * ENNReal.ofReal δ ≤ ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    rw [hδdef, mul_div_assoc']
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hδle : ENNReal.ofReal δ ≤ ENNReal.ofReal (ε / 2) := by
    apply ENNReal.ofReal_le_ofReal
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hsum : ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) = ENNReal.ofReal ε := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
  refine ⟨m, hnice, ?_, ?_⟩
  · apply ENNReal.toReal_lt_of_lt_ofReal
    have e : (fun ξ => m ξ - (χ : L2C) ξ) = (m - f₁) - (outerSet n).indicator f := by
      funext ξ
      have := congrFun hff₁ ξ
      simp only [Pi.add_apply] at this
      simp only [Pi.sub_apply, ← hfdef]
      rw [this]
      abel
    rw [e]
    calc eLpNorm ((m - f₁) - (outerSet n).indicator f) 2 volume
        ≤ eLpNorm (m - f₁) 2 volume + eLpNorm ((outerSet n).indicator f) 2 volume :=
          eLpNorm_sub_le (hmc.sub hf₁2.aestronglyMeasurable)
            (hf2.aestronglyMeasurable.indicator hmeas) (by norm_num)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) :=
          ENNReal.add_lt_add (herr1.trans_le hδle) hn1
      _ = ENNReal.ofReal ε := hsum
  · apply ENNReal.toReal_lt_of_lt_ofReal
    have e : (fun ξ => sspFactor ξ • m ξ - (ψ : L2C) ξ) =ᵐ[volume]
        (fun ξ => sspFactor ξ • (m - f₁) ξ) - (outerSet n).indicator (fun ξ => sspFactor ξ • f ξ) := by
      filter_upwards [hψf] with ξ h
      have := congrFun hff₁ ξ
      simp only [Pi.add_apply] at this
      simp only [Pi.sub_apply, ← h]
      rw [this, smul_add, smul_sub]
      by_cases hξ : ξ ∈ outerSet n
      · simp [hξ]
        abel
      · simp [hξ]
    rw [eLpNorm_congr_ae e]
    have hsspc : Continuous sspFactor := by unfold sspFactor; fun_prop
    have hu : ∀ ξ, 2 * R ≤ ‖ξ‖ → (m - f₁) ξ = 0 := by
      intro ξ hξ
      simp only [Pi.sub_apply, hmR ξ hξ, hf₁supp ξ (Or.inr (by linarith)), sub_zero]
    calc eLpNorm ((fun ξ => sspFactor ξ • (m - f₁) ξ) -
          (outerSet n).indicator (fun ξ => sspFactor ξ • f ξ)) 2 volume
        ≤ eLpNorm (fun ξ => sspFactor ξ • (m - f₁) ξ) 2 volume +
          eLpNorm ((outerSet n).indicator (fun ξ => sspFactor ξ • f ξ)) 2 volume :=
          eLpNorm_sub_le
            (hsspc.aestronglyMeasurable.smul (hmc.sub hf₁2.aestronglyMeasurable))
            (hl2.aestronglyMeasurable.indicator hmeas) (by norm_num)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          have hA : eLpNorm (fun ξ => sspFactor ξ • (m - f₁) ξ) 2 volume ≤ ENNReal.ofReal (ε / 2) := by
            calc eLpNorm (fun ξ => sspFactor ξ • (m - f₁) ξ) 2 volume
                ≤ ENNReal.ofReal C * eLpNorm (m - f₁) 2 volume := by
                  have := eLpNorm_ssp_le (u := m - f₁) (by positivity : (0 : ℝ) ≤ 2 * R) hu
                  simpa [hCdef] using this
              _ ≤ ENNReal.ofReal C * ENNReal.ofReal δ := by gcongr
              _ ≤ ENNReal.ofReal (ε / 2) := hδC
          exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA) hA hn2
      _ = ENNReal.ofReal ε := hsum

end Breakdown.Freq
