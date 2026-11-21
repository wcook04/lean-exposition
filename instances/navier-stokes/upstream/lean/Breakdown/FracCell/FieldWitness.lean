import Breakdown.FracCell.FieldWitnessSt
import Breakdown.FracCell.AxisClosed
import Breakdown.FracCell.IntervalMinimal
import Breakdown.FracCell.IntervalIdentity
import Breakdown.FracCell.IntervalMonotone

open MeasureTheory Polynomial Set
open scoped Interval Topology

noncomputable section

namespace Breakdown.CellCert.Spectral

open SteadyCert Breakdown.FracInternal.AxisClosedParts

namespace Internal.FieldWitness

theorem axisClosed_uniform (q : ℕ) (M μ : ℝ) (hM : AxisGradientBound q M) (hμ : 24 ≤ μ) :
    ∃ χ : ℝ → ℝ, χ 1 = 0 ∧ (∃ K, LipschitzWith K χ) ∧ ∀ i : ℕ, i ≤ 1 → ∀ p : ℝ[X], p.natDegree ≤ q →
      (i = 1 → X ∣ p) → axisFunctional i χ μ p ≤ axisClosed q M μ * ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r := by
  have hμ0 : 0 < μ := by linarith
  set e : ℝ := μ ^ (-(1 / 2 : ℝ)) with he
  have he0 : 0 < e := Real.rpow_pos_of_pos hμ0 _
  have he2 : e ^ 2 = μ⁻¹ := by
    rw [he, ← Real.rpow_natCast, ← Real.rpow_mul hμ0.le]
    norm_num
    exact Real.rpow_neg_one μ
  have hs6 : Real.sqrt 6 ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  set δ : ℝ := Real.sqrt 6 * e with hδ
  have hδ0 : 0 < δ := by positivity
  have hδne : δ ≠ 0 := hδ0.ne'
  have hm0 : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ0.le
  have hδ2 : δ ^ 2 = 6 * μ⁻¹ := by rw [hδ, mul_pow, hs6, he2]
  have hδhalf : δ ≤ 1 / 2 := by
    have hinv : μ⁻¹ ≤ 1 / 24 := by
      rw [inv_le_comm₀ hμ0 (by norm_num)]; norm_num; linarith
    nlinarith
  set a : ℝ := 1 - δ with ha
  have ha_half : 1 / 2 ≤ a := by linarith
  have ha1 : a < 1 := by linarith
  set χ : ℝ → ℝ := fun r => min 1 ((1 - r) / δ) with hχ
  refine ⟨χ, ?_, ?_, fun i hi p hp hdiv => ?_⟩
  · simp [hχ]
  · refine ⟨Real.toNNReal δ⁻¹, ?_⟩
    refine LipschitzWith.const_min ?_ 1
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (inv_nonneg.2 hδ0.le),
      show (1 - x) / δ - (1 - y) / δ = δ⁻¹ * (y - x) by field_simp; ring, abs_mul,
      abs_of_pos (inv_pos.2 hδ0), abs_sub_comm]
  · set S := ∫ r in (0 : ℝ)..1, p.eval r ^ 2 * r with hS
    set G : ℝ → ℝ := fun r => ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r
      with hG
    set Hc : ℝ → ℝ := fun r => (((r - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) * (p.eval r ^ 2 * r) with hHc
    set g : ℝ → ℝ := fun r => 2 * μ⁻¹ * G r + (Ioi a).indicator Hc r with hg
    have hGc : Continuous G := grad_cont i hi p hdiv
    have hHcc : Continuous Hc := by rw [hHc]; fun_prop
    have hGint : IntegrableOn G (Ioc 0 1) := (hGc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hHint : IntegrableOn Hc (Ioc 0 1) := (hHcc.integrableOn_Icc).mono_set Ioc_subset_Icc_self
    have hgint : Integrable g (volume.restrict (Ioc 0 1)) :=
      (hGint.const_mul (2 * μ⁻¹)).add (hHint.indicator measurableSet_Ioi)
    have hpt : ∀ r, r ∈ Ioc (0 : ℝ) 1 → r ≠ a →
        ((1 - χ r) ^ 2 * p.eval r ^ 2 + μ⁻¹ * (deriv (fun s => χ s * p.eval s) r ^ 2
          + (i : ℝ) ^ 2 * χ r ^ 2 * p.eval r ^ 2 / r ^ 2)) * r ≤ g r := by
      intro r hr hra
      rcases lt_or_gt_of_ne hra with hlt | hgt
      · have hev : (fun s => χ s * p.eval s) =ᶠ[𝓝 r] fun s => p.eval s := by
          filter_upwards [Iio_mem_nhds hlt] with s hs
          have : 1 ≤ (1 - s) / δ := by
            rw [le_div_iff₀ hδ0]; simp only [mem_Iio] at hs; linarith
          simp [hχ, min_eq_left this]
        have hχr : χ r = 1 := min_eq_left (by rw [le_div_iff₀ hδ0]; linarith)
        rw [hev.deriv_eq, Polynomial.deriv, hχr]
        have hnot : r ∉ Ioi a := fun h => absurd (mem_Ioi.1 h) (not_lt.2 hlt.le)
        simp only [hg, indicator_of_notMem hnot, add_zero, hG]
        have hT : 0 ≤ ((derivative p).eval r ^ 2 + (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) * r :=
          mul_nonneg (by positivity) hr.1.le
        have e1 : (i : ℝ) ^ 2 * 1 ^ 2 * p.eval r ^ 2 / r ^ 2 = (i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2 := by
          ring
        rw [e1]
        nlinarith [mul_nonneg hm0 hT]
      · have hev : (fun s => χ s * p.eval s) =ᶠ[𝓝 r] fun s => (1 - s) / δ * p.eval s := by
          filter_upwards [Ioi_mem_nhds hgt] with s hs
          have : (1 - s) / δ ≤ 1 := by
            rw [div_le_one hδ0]; simp only [mem_Ioi] at hs; linarith
          simp [hχ, min_eq_right this]
        have hd : HasDerivAt (fun s => (1 - s) / δ * p.eval s)
            (-(1 / δ) * p.eval r + (1 - r) / δ * (derivative p).eval r) r := by
          have h1 : HasDerivAt (fun s : ℝ => (1 - s) / δ) (-(1 / δ)) r := by
            have := ((hasDerivAt_id' r).const_sub 1).div_const δ
            exact this.congr_deriv (by ring)
          exact h1.mul (p.hasDerivAt r)
        have hc1 : (1 - r) / δ ≤ 1 := by rw [div_le_one hδ0]; linarith
        have hc0 : 0 ≤ (1 - r) / δ := div_nonneg (by linarith [hr.2]) hδ0.le
        have hχr : χ r = (1 - r) / δ := min_eq_right hc1
        have hin : r ∈ Ioi a := hgt
        rw [hev.deriv_eq, hd.deriv, hχr]
        simp only [hg, indicator_of_mem hin, hHc, hG]
        have h1c : (r - a) / δ = 1 - (1 - r) / δ := by rw [ha]; field_simp; ring
        rw [h1c]
        have key := pt_upper ((1 - r) / δ) (p.eval r / δ) ((derivative p).eval r)
          ((i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) r μ⁻¹ (p.eval r) δ hc0 hc1 (by positivity)
          hr.1.le hm0 rfl
        have e1 : (i : ℝ) ^ 2 * ((1 - r) / δ) ^ 2 * p.eval r ^ 2 / r ^ 2
            = ((1 - r) / δ) ^ 2 * ((i : ℝ) ^ 2 * p.eval r ^ 2 / r ^ 2) := by ring
        rw [e1]
        linarith [key]
    have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ a := by
      have := compl_mem_ae_iff.mpr (show (volume : Measure ℝ) {a} = 0 from measure_singleton a)
      filter_upwards [this] with r hr
      simpa using hr
    have hmain : axisFunctional i χ μ p ≤ ∫ r in Ioc (0 : ℝ) 1, g r := by
      unfold axisFunctional
      rw [intervalIntegral.integral_of_le zero_le_one]
      refine integral_mono_of_nonneg ?_ hgint ?_
      · filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact mul_nonneg (add_nonneg (by positivity) (mul_nonneg hm0 (by positivity))) hr.1.le
      · filter_upwards [ae_restrict_mem measurableSet_Ioc, ae_restrict_of_ae hne] with r hr hra
        exact hpt r hr hra
    have hset : Ioc (0 : ℝ) 1 ∩ Ioi a = Ioc a 1 := by
      rw [Ioc_inter_Ioi, sup_eq_right.2 (by linarith : (0 : ℝ) ≤ a)]
    have hgval : ∫ r in Ioc (0 : ℝ) 1, g r
        = 2 * μ⁻¹ * (∫ r in (0 : ℝ)..1, G r) + ∫ r in Ioc a 1, Hc r := by
      simp only [hg]
      rw [integral_add (hGint.const_mul _) (hHint.indicator measurableSet_Ioi), integral_const_mul,
        setIntegral_indicator measurableSet_Ioi, hset, intervalIntegral.integral_of_le zero_le_one]
    have hw : ∫ r in a..1, (((r - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) = δ / 3 + 2 * μ⁻¹ / δ := by
      have hF : ∀ x ∈ [[a, 1]], HasDerivAt (fun r => (r - a) ^ 3 / (3 * δ ^ 2) + 2 * μ⁻¹ / δ ^ 2 * r)
          (((x - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) x := by
        intro x _
        have := ((((hasDerivAt_id' x).sub_const a).pow 3).div_const (3 * δ ^ 2)).add
          ((hasDerivAt_id' x).const_mul (2 * μ⁻¹ / δ ^ 2))
        refine this.congr_deriv ?_
        simp only [Nat.reduceSub, Nat.cast_ofNat, mul_one, div_pow]
        field_simp
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hF
        (by apply Continuous.intervalIntegrable; fun_prop), ha]
      field_simp
      ring
    have hHb : ∫ r in Ioc a 1, Hc r ≤ (δ / 3 + 2 * μ⁻¹ / δ) * (4 * ((q : ℝ) + 1) ^ 2 * S) := by
      have hB := fun r (hr : r ∈ Ioc a 1) => sup_bound q p hp r (by linarith [hr.1]) hr.2
      calc ∫ r in Ioc a 1, Hc r
          ≤ ∫ r in Ioc a 1, (((r - a) / δ) ^ 2 + 2 * μ⁻¹ / δ ^ 2) * (4 * ((q : ℝ) + 1) ^ 2 * S) := by
            refine setIntegral_mono_on (hHcc.integrableOn_Icc.mono_set Ioc_subset_Icc_self) ?_
              measurableSet_Ioc ?_
            · exact (Continuous.integrableOn_Icc (by fun_prop)).mono_set Ioc_subset_Icc_self
            · intro r hr
              simp only [hHc]
              exact mul_le_mul_of_nonneg_left (hB r hr)
                (add_nonneg (sq_nonneg _) (div_nonneg (mul_nonneg zero_le_two hm0) (sq_nonneg _)))
        _ = (δ / 3 + 2 * μ⁻¹ / δ) * (4 * ((q : ℝ) + 1) ^ 2 * S) := by
            rw [integral_mul_const, ← intervalIntegral.integral_of_le ha1.le, hw]
    have hGb : ∫ r in (0 : ℝ)..1, G r ≤ M * S := hM i hi p hp hdiv
    have h6 : 2 * e ^ 2 / (Real.sqrt 6 * e) = Real.sqrt 6 * e / 3 := by
      rw [div_eq_iff (by positivity)]
      linear_combination (-(e ^ 2) / 3) * hs6
    have hkey : δ / 3 + 2 * μ⁻¹ / δ = 2 * Real.sqrt 6 * e / 3 := by
      rw [← he2, hδ, h6]; ring
    unfold axisClosed
    rw [← he]
    calc axisFunctional i χ μ p ≤ ∫ r in Ioc (0 : ℝ) 1, g r := hmain
      _ = 2 * μ⁻¹ * (∫ r in (0 : ℝ)..1, G r) + ∫ r in Ioc a 1, Hc r := hgval
      _ ≤ 2 * μ⁻¹ * (M * S) + (δ / 3 + 2 * μ⁻¹ / δ) * (4 * ((q : ℝ) + 1) ^ 2 * S) :=
          add_le_add (mul_le_mul_of_nonneg_left hGb (mul_nonneg zero_le_two hm0)) hHb
      _ = (8 * Real.sqrt 6 / 3 * ((q : ℝ) + 1) ^ 2 * e + 2 * M * μ⁻¹) * S := by
          rw [hkey]; ring

theorem certMin_mem (S : Finset (ℝ × ℝ)) (μ : ℝ) :
    certMin S μ ∈ insert (1 : ℝ) {v | ∃ ν, (ν, v) ∈ S ∧ ν ≤ μ} := by
  have hfin : (insert (1 : ℝ) {v | ∃ ν, (ν, v) ∈ S ∧ ν ≤ μ}).Finite := by
    refine Set.Finite.insert _ ?_
    refine (S.finite_toSet.image Prod.snd).subset ?_
    rintro v ⟨ν, h, -⟩
    exact ⟨(ν, v), h, rfl⟩
  exact Set.Nonempty.csInf_mem (Set.insert_nonempty _ _) hfin

theorem interval_trivial (μ : ℝ) (hμ : 0 < μ) (p : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * p.eval x) ≤ 1 * ∫ x in (-1 : ℝ)..1, p.eval x ^ 2 := by
  have h := intervalMinimal_of intervalIdentity μ p hμ (fun _ => 0) ⟨0, LipschitzWith.const 0⟩ rfl rfl
  simpa using h

theorem axis_trivial (q : ℕ) (μ : ℝ) (hμ : 0 < μ) : AxisCertificate q μ 1 (fun _ => 0) := by
  refine ⟨hμ, rfl, ⟨0, LipschitzWith.const 0⟩, fun i _ p _ _ => ?_⟩
  unfold axisFunctional
  simp

theorem intervalUpper_cert (hC : IntervalClosedStatement) {k N : ℕ} {c : FracCellData k N} {sd : SpectralData}
    (hsd : IsSpectralData c sd) (q : ℕ) (μ : ℝ) (hμ : 0 < μ) : IntervalCertificate q μ (sd.intervalUpper q μ) := by
  refine ⟨hμ, fun p hp => ?_⟩
  unfold SpectralData.intervalUpper
  rcases min_choice (certMin (sd.intervalCerts q) μ) (intervalClosed q μ) with h | h
  · rw [h]
    rcases certMin_mem (sd.intervalCerts q) μ with h1 | ⟨ν, hν, hνμ⟩
    · rw [h1]
      exact interval_trivial μ hμ p
    · have hc := hsd.interval_bounded q _ hν
      exact (intervalMonotone_of intervalIdentity (intervalMinimal_of intervalIdentity) ν μ p hc.1 hνμ).trans
        (hc.2 p hp)
  · rw [h]
    exact hC q μ p hμ hp

theorem axisUpper_cert {k N : ℕ} {c : FracCellData k N} {sd : SpectralData} (hsd : IsSpectralData c sd)
    (a : Fin N) (hax : (sd.block (c.blockIndex a)).onAxis = true)
    (μ : ℝ) (hμ : 0 < μ) : ∃ ν χ, ν ≤ μ ∧
      AxisCertificate (sd.block (c.blockIndex a)).degree ν (sd.axisUpper (sd.block (c.blockIndex a)).degree μ) χ := by
  set q := (sd.block (c.blockIndex a)).degree with hq
  unfold SpectralData.axisUpper
  rcases min_choice (certMin (sd.axisCerts q) μ)
      (if 24 ≤ μ then axisClosed q (sd.axisGradient q) μ else 1) with h | h
  · rw [h]
    rcases certMin_mem (sd.axisCerts q) μ with h1 | ⟨ν, hν, hνμ⟩
    · rw [h1]
      exact ⟨μ, fun _ => 0, le_rfl, axis_trivial q μ hμ⟩
    · exact ⟨ν, sd.axisCutoff q (ν, certMin (sd.axisCerts q) μ), hνμ, hsd.axis_bounded q _ hν⟩
  · rw [h]
    by_cases h24 : 24 ≤ μ
    · rw [if_pos h24]
      obtain ⟨χ, h1, h2, h3⟩ := axisClosed_uniform q (sd.axisGradient q) μ (hsd.axis_gradient a hax) h24
      exact ⟨μ, χ, le_rfl, hμ, h1, h2, h3⟩
    · rw [if_neg h24]
      exact ⟨μ, fun _ => 0, le_rfl, axis_trivial q μ hμ⟩

theorem resolvent_pair (h1 : IntervalIdentityStatement) (μ : ℝ) (hμ : 0 < μ) (p g : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, intervalResolvent μ p x * g.eval x)
      = (∫ x in (-1 : ℝ)..1, intervalResolvent μ p x * intervalResolvent μ g x)
        + μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv (intervalResolvent μ p) x * deriv (intervalResolvent μ g) x := by
  obtain ⟨hCp, hp0, hp1, -⟩ := h1 μ p hμ
  obtain ⟨hCg, -, -, -⟩ := h1 μ g hμ
  set u := intervalResolvent μ p with hu
  set v := intervalResolvent μ g with hv
  have hODE : ∀ x, g.eval x = v x - μ⁻¹ * deriv (deriv v) x := by
    intro x
    rw [hv, IntervalMinimalInternal.resolvent_second μ hμ g x]
    field_simp
    ring
  have huAC : AbsolutelyContinuousOnInterval u (-1) 1 :=
    (hCp.of_le (by norm_num)).contDiffOn.absolutelyContinuousOnInterval
  have hC1 : ContDiff ℝ 1 (deriv v) := hCg.deriv'
  have hv'AC : AbsolutelyContinuousOnInterval (deriv v) (-1) 1 :=
    hC1.contDiffOn.absolutelyContinuousOnInterval
  have hIBP : ∫ x in (-1 : ℝ)..1, u x * deriv (deriv v) x = -∫ x in (-1 : ℝ)..1, deriv u x * deriv v x := by
    rw [huAC.integral_mul_deriv_eq_deriv_mul hv'AC, hp0, hp1]
    ring
  have hcu : Continuous u := hCp.continuous
  have hcv : Continuous v := hCg.continuous
  have hcv2 : Continuous (deriv (deriv v)) := hC1.continuous_deriv le_rfl
  have e1 : (fun x => u x * g.eval x) = fun x => u x * v x - μ⁻¹ * (u x * deriv (deriv v) x) := by
    funext x
    rw [hODE x]
    ring
  have hi1 : IntervalIntegrable (fun x => u x * v x) volume (-1) 1 :=
    (hcu.mul hcv).intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun x => μ⁻¹ * (u x * deriv (deriv v) x)) volume (-1) 1 :=
    ((hcu.mul hcv2).intervalIntegrable _ _).const_mul _
  rw [e1, intervalIntegral.integral_sub hi1 hi2, intervalIntegral.integral_const_mul, hIBP]
  ring

theorem interval_scaled (h1 : IntervalIdentityStatement) (q : ℕ) (r0 r1 lam v : ℝ) (hlam : 0 < lam)
    (hr : r0 < r1) (hc : IntervalCertificate q (lam * (r1 - r0) ^ 2 / 4) v) (p : ℝ[X]) (hp : p.natDegree ≤ q) :
    (∫ r in r0..r1, (p.eval r - intervalResolvent (lam * (r1 - r0) ^ 2 / 4)
        (p.comp (C ((r1 - r0) / 2) * X + C ((r0 + r1) / 2))) (2 / (r1 - r0) * r - (r0 + r1) / (r1 - r0))) ^ 2)
      + lam⁻¹ * (∫ r in r0..r1, deriv (fun s => intervalResolvent (lam * (r1 - r0) ^ 2 / 4)
        (p.comp (C ((r1 - r0) / 2) * X + C ((r0 + r1) / 2))) (2 / (r1 - r0) * s - (r0 + r1) / (r1 - r0))) r ^ 2)
      ≤ v * ∫ r in r0..r1, p.eval r ^ 2 := by
  have hL : 0 < r1 - r0 := sub_pos.2 hr
  set L := r1 - r0 with hLdef
  set μ := lam * L ^ 2 / 4 with hμdef
  have hμ : 0 < μ := by positivity
  set c := 2 / L with hcdef
  set d := (r0 + r1) / L with hddef
  have hc0 : c ≠ 0 := by positivity
  set pt := p.comp (C (L / 2) * X + C ((r0 + r1) / 2)) with hptdef
  set R := intervalResolvent μ pt with hRdef
  obtain ⟨hC, -, -, hid⟩ := h1 μ pt hμ
  have hptdeg : pt.natDegree ≤ q := by
    refine natDegree_comp_le.trans ?_
    have : (C (L / 2) * X + C ((r0 + r1) / 2)).natDegree ≤ 1 := natDegree_linear_le
    nlinarith
  have hpt : ∀ r, p.eval r = pt.eval (c * r - d) := by
    intro r
    simp only [hptdef, eval_comp, eval_add, eval_mul, eval_C, eval_X]
    congr 1
    rw [hcdef, hddef]
    field_simp
    ring
  have hdR : ∀ r, deriv (fun s => R (c * s - d)) r = c * deriv R (c * r - d) := by
    intro r
    have hd : DifferentiableAt ℝ R (c * r - d) := (hC.differentiable (by norm_num)).differentiableAt
    have h2 : HasDerivAt (fun s => c * s - d) c r := by
      simpa using ((hasDerivAt_id r).const_mul c).sub_const d
    have h3 := hd.hasDerivAt.comp r h2
    rw [show (fun s => R (c * s - d)) = R ∘ (fun s => c * s - d) from rfl, h3.deriv]
    ring
  have hcv : ∀ f : ℝ → ℝ, ∫ r in r0..r1, f (c * r - d) = (L / 2) * ∫ x in (-1 : ℝ)..1, f x := by
    intro f
    rw [intervalIntegral.integral_comp_mul_sub (f := f) hc0 d, smul_eq_mul]
    have e0 : c * r0 - d = -1 := by rw [hcdef, hddef]; field_simp; ring
    have e1 : c * r1 - d = 1 := by rw [hcdef, hddef]; field_simp; ring
    rw [e0, e1, hcdef]
    congr 1
    field_simp
  have hA := hcv (fun x => (pt.eval x - R x) ^ 2)
  have hB := hcv (fun x => deriv R x ^ 2)
  have hN := hcv (fun x => pt.eval x ^ 2)
  have e2 : (fun r => deriv (fun s => R (c * s - d)) r ^ 2) = fun r => c ^ 2 * deriv R (c * r - d) ^ 2 := by
    funext r
    rw [hdR r]
    ring
  simp_rw [hpt]
  rw [e2, intervalIntegral.integral_const_mul, hA, hB, hN]
  have key := (hc.2 pt hptdeg)
  rw [← hid] at key
  have hcμ : lam⁻¹ * c ^ 2 = μ⁻¹ := by
    rw [hcdef, hμdef]
    field_simp
    norm_num
  have hL2 : 0 < L / 2 := by positivity
  calc (L / 2 * ∫ x in (-1 : ℝ)..1, (pt.eval x - R x) ^ 2)
        + lam⁻¹ * (c ^ 2 * (L / 2 * ∫ x in (-1 : ℝ)..1, deriv R x ^ 2))
      = L / 2 * ((∫ x in (-1 : ℝ)..1, (pt.eval x - R x) ^ 2)
        + (lam⁻¹ * c ^ 2) * ∫ x in (-1 : ℝ)..1, deriv R x ^ 2) := by ring
    _ ≤ L / 2 * (v * ∫ x in (-1 : ℝ)..1, pt.eval x ^ 2) := by
        rw [hcμ]
        exact mul_le_mul_of_nonneg_left key hL2.le
    _ = v * (L / 2 * ∫ x in (-1 : ℝ)..1, pt.eval x ^ 2) := by ring

theorem evenSeries_eq_range (μ : ℝ) (p : ℝ[X]) (N : ℕ) (hN : p.natDegree + 1 ≤ N) :
    evenSeries μ p = ∑ i ∈ Finset.range N, (μ ^ i)⁻¹ • derivative^[2 * i] p := by
  unfold evenSeries
  refine Finset.sum_subset (Finset.range_mono hN) fun i _ hni => ?_
  rw [Finset.mem_range, not_lt] at hni
  rw [iterate_derivative_eq_zero (by omega), smul_zero]

theorem evenSeries_linear (μ a b : ℝ) (p g : ℝ[X]) :
    evenSeries μ (a • p + b • g) = a • evenSeries μ p + b • evenSeries μ g := by
  rw [evenSeries_eq_range μ _ ((a • p + b • g).natDegree + p.natDegree + g.natDegree + 1) (by omega),
    evenSeries_eq_range μ p ((a • p + b • g).natDegree + p.natDegree + g.natDegree + 1) (by omega),
    evenSeries_eq_range μ g ((a • p + b • g).natDegree + p.natDegree + g.natDegree + 1) (by omega)]
  simp only [Finset.smul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Module.End.coe_pow, map_add, map_smul, map_smul]
  module

theorem resolvent_linear (μ a b : ℝ) (p g : ℝ[X]) (x : ℝ) :
    intervalResolvent μ (a • p + b • g) x = a * intervalResolvent μ p x + b * intervalResolvent μ g x := by
  have hR : ∀ f : ℝ[X], intervalResolvent μ f x = (evenSeries μ f).eval x
      - ((evenSeries μ f).eval 1 + (evenSeries μ f).eval (-1)) / (2 * Real.cosh (Real.sqrt μ))
        * Real.cosh (Real.sqrt μ * x)
      - ((evenSeries μ f).eval 1 - (evenSeries μ f).eval (-1)) / (2 * Real.sinh (Real.sqrt μ))
        * Real.sinh (Real.sqrt μ * x) := by
    intro f
    simp only [intervalResolvent, intervalSmoothed]
    ring
  rw [hR, hR p, hR g, evenSeries_linear]
  simp only [eval_add, eval_smul, smul_eq_mul]
  ring

theorem smoothed_pair (h1 : IntervalIdentityStatement) (μ : ℝ) (hμ : 0 < μ) (p g : ℝ[X]) :
    (∫ x in (-1 : ℝ)..1, intervalSmoothed μ p x * g.eval x)
      = (∫ x in (-1 : ℝ)..1, (p.eval x - intervalResolvent μ p x) * (g.eval x - intervalResolvent μ g x))
        + μ⁻¹ * ∫ x in (-1 : ℝ)..1, deriv (intervalResolvent μ p) x * deriv (intervalResolvent μ g) x := by
  obtain ⟨hCp, -, -, -⟩ := h1 μ p hμ
  obtain ⟨hCg, -, -, -⟩ := h1 μ g hμ
  have hpair := resolvent_pair h1 μ hμ g p
  set u := intervalResolvent μ p with hu
  set v := intervalResolvent μ g with hv
  have hsm : (fun x => intervalSmoothed μ p x * g.eval x) = fun x => (p.eval x - u x) * g.eval x := by
    funext x
    simp [hu, intervalResolvent]
  have hcu : Continuous u := hCp.continuous
  have hcv : Continuous v := hCg.continuous
  have hpc : Continuous fun x => p.eval x := p.continuous
  have hgc : Continuous fun x => g.eval x := g.continuous
  have e : (fun x => (p.eval x - u x) * (g.eval x - v x))
      = fun x => (p.eval x - u x) * g.eval x - (v x * p.eval x - u x * v x) := by
    funext x
    ring
  have i1 : IntervalIntegrable (fun x => (p.eval x - u x) * g.eval x) volume (-1) 1 :=
    ((hpc.sub hcu).mul hgc).intervalIntegrable _ _
  have i2 : IntervalIntegrable (fun x => v x * p.eval x - u x * v x) volume (-1) 1 :=
    ((hcv.mul hpc).sub (hcu.mul hcv)).intervalIntegrable _ _
  have i3 : IntervalIntegrable (fun x => v x * p.eval x) volume (-1) 1 := (hcv.mul hpc).intervalIntegrable _ _
  have i4 : IntervalIntegrable (fun x => u x * v x) volume (-1) 1 := (hcu.mul hcv).intervalIntegrable _ _
  have c1 : ∫ x in (-1 : ℝ)..1, v x * u x = ∫ x in (-1 : ℝ)..1, u x * v x := by
    congr 1
    funext x
    ring
  have c2 : ∫ x in (-1 : ℝ)..1, deriv v x * deriv u x = ∫ x in (-1 : ℝ)..1, deriv u x * deriv v x := by
    congr 1
    funext x
    ring
  rw [hsm, e, intervalIntegral.integral_sub i1 i2, intervalIntegral.integral_sub i3 i4, hpair, c1, c2]
  ring

end Internal.FieldWitness

open Internal.FieldWitness in
theorem fieldWitness_of_cores (hC : IntervalClosedStatement) (hOff : OffAxisCoreStatement) (hOn : OnAxisCoreStatement) :
    FieldWitnessStatement := by
  intro k N c sd hsd lam hlam a φ hφ hφL
  obtain ⟨hR, hH, hl0, -⟩ := hsd.block_geometry a
  have hμz : 0 < lam * ((sd.block (c.blockIndex a)).upperHeight - (sd.block (c.blockIndex a)).lowerHeight) ^ 2 / 4 := by
    have := sub_pos.2 hH
    positivity
  have hRp := sub_pos.2 hR
  unfold blockInner
  by_cases hax : (sd.block (c.blockIndex a)).onAxis = true
  · rw [if_pos hax]
    obtain ⟨hin, hmode, -⟩ := hsd.on_axis a hax
    obtain ⟨ν, χ, hνμ, hcert⟩ := axisUpper_cert hsd a hax
      (lam * ((sd.block (c.blockIndex a)).outerRadius - (sd.block (c.blockIndex a)).innerRadius) ^ 2)
      (by positivity)
    exact hOn _ lam ν _ _ χ hlam hax hin hmode hR hH hl0 hνμ hcert
      (intervalUpper_cert hC hsd _ _ hμz) φ hφ hφL
  · rw [if_neg hax]
    have hoff : (sd.block (c.blockIndex a)).onAxis = false := by simpa using hax
    have hμr : 0 < lam * ((sd.block (c.blockIndex a)).outerRadius - (sd.block (c.blockIndex a)).innerRadius) ^ 2 / 4 := by
      positivity
    exact hOff _ lam _ _ hlam hoff (hsd.off_axis a hoff) hR hH hl0 (intervalUpper_cert hC hsd _ _ hμr)
      (intervalUpper_cert hC hsd _ _ hμz) φ hφ hφL

end Breakdown.CellCert.Spectral
