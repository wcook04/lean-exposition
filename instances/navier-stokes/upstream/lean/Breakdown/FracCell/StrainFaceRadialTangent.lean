import Breakdown.FracCell.StrainFaceDefs
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.ModeHeightAxis
import Breakdown.FracCell.ModeWeakIdentity

open MeasureTheory Set Filter Topology
open scoped ContDiff Real

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

def ModeThirdSwapStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (n : ℤ) (a : Fin 3), ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → modeThird m n H a 2 0 p = modeThird m n H a 0 2 p

def RadialStripIbpStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a : Fin 3) (c o : ℝ),
      ((c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁)) →
      IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 0 p) K.rect ∧
        IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p
          + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) K.rect ∧
        ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h K.z₁ = 0 → h K.z₂ = 0 →
          ∫ p in K.rect,
            ((((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 0 p) * ((deriv h p.2 : ℝ) : ℂ)
              + (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) * ((h p.2 : ℝ) : ℂ)) = 0

def StripIbpStatement : Prop :=
  ∀ (F dF : ℝ × ℝ → ℂ) (f : ℝ → ℝ) (a b z₁ z₂ : ℝ), 0 ≤ a → a < b → z₁ < z₂ → ContDiff ℝ ∞ f →
    IntegrableOn (fun p : ℝ × ℝ => ((f p.1 : ℝ) : ℂ) * F p) (Set.Icc a b ×ˢ Set.Icc z₁ z₂) →
    IntegrableOn (fun p : ℝ × ℝ => ((f p.1 : ℝ) : ℂ) * dF p) (Set.Icc a b ×ˢ Set.Icc z₁ z₂) →
    (∀ ψ : ℝ × ℝ → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ → (∀ p ∈ tsupport ψ, 0 < p.1) →
      ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * F p = -∫ p, (ψ p : ℂ) * dF p) →
    ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h z₁ = 0 → h z₂ = 0 →
      ∫ p in Set.Icc a b ×ˢ Set.Icc z₁ z₂,
        (((f p.1 * deriv h p.2 : ℝ) : ℂ) * F p + ((f p.1 * h p.2 : ℝ) : ℂ) * dF p) = 0

end Breakdown.CellCert.CellFormula

namespace Breakdown.FracInternal.StripIbp

def cut (e α β s : ℝ) : ℝ := Real.smoothTransition ((s - α) / e - 1) * Real.smoothTransition ((β - s) / e - 1)

def cutD (e α β s : ℝ) : ℝ :=
  deriv Real.smoothTransition ((s - α) / e - 1) * (1 / e) * Real.smoothTransition ((β - s) / e - 1)
    + Real.smoothTransition ((s - α) / e - 1) * (deriv Real.smoothTransition ((β - s) / e - 1) * ((0 - 1) / e))

theorem sm_diff : Differentiable ℝ Real.smoothTransition :=
  (Real.smoothTransition.contDiff (n := 1)).differentiable (by simp)

theorem sd_cont : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 1)).continuous_deriv le_rfl

theorem sd_zero {x : ℝ} (hx : x < 0 ∨ 1 < x) : deriv Real.smoothTransition x = 0 := by
  rcases hx with hx | hx
  · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hx] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [e.deriv_eq]; simp
  · have e : Real.smoothTransition =ᶠ[𝓝 x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [e.deriv_eq]; simp

theorem sd_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ x, |deriv Real.smoothTransition x| ≤ D := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn sd_cont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  by_cases hx : x ∈ Icc (0 : ℝ) 1
  · exact le_trans (by simpa [Real.norm_eq_abs] using hC x hx : |deriv Real.smoothTransition x| ≤ C) (le_max_left _ _)
  · rw [sd_zero (by simp only [mem_Icc, not_and_or, not_le] at hx; exact hx)]
    simp

theorem cut_smooth (e α β : ℝ) : ContDiff ℝ ∞ (cut e α β) := by
  unfold cut
  have hs : ContDiff ℝ ∞ Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hs.comp (((contDiff_id.sub contDiff_const).div_const _).sub contDiff_const)).mul
    (hs.comp (((contDiff_const.sub contDiff_id).div_const _).sub contDiff_const))

theorem cut_hasDeriv (e α β s : ℝ) : HasDerivAt (cut e α β) (cutD e α β s) s := by
  have h1 : HasDerivAt (fun s => (s - α) / e - 1) (1 / e) s :=
    (((hasDerivAt_id s).sub_const α).div_const e).sub_const 1
  have h2 : HasDerivAt (fun s => (β - s) / e - 1) ((0 - 1) / e) s :=
    (((hasDerivAt_const s β).sub (hasDerivAt_id s)).div_const e).sub_const 1
  have g1 := (sm_diff ((s - α) / e - 1)).hasDerivAt.comp s h1
  have g2 := (sm_diff ((β - s) / e - 1)).hasDerivAt.comp s h2
  exact g1.mul g2

theorem cut_zero {e α β s : ℝ} (he : 0 < e) (hs : s ≤ α + e ∨ β - e ≤ s) : cut e α β s = 0 := by
  unfold cut
  rcases hs with hs | hs
  · rw [Real.smoothTransition.zero_of_nonpos, zero_mul]
    rw [sub_nonpos, div_le_one he]; linarith
  · rw [Real.smoothTransition.zero_of_nonpos (x := (β - s) / e - 1), mul_zero]
    rw [sub_nonpos, div_le_one he]; linarith

theorem cut_le (e α β s : ℝ) : |cut e α β s| ≤ 1 := by
  unfold cut
  rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _))]
  exact mul_le_one₀ (Real.smoothTransition.le_one _) (Real.smoothTransition.nonneg _) (Real.smoothTransition.le_one _)

theorem cut_lim {α β s : ℝ} (hs : s ∈ Ioo α β) :
    ∀ᶠ k : ℕ in atTop, cut (1 / ((k : ℝ) + 1)) α β s = 1 ∧ cutD (1 / ((k : ℝ) + 1)) α β s = 0 := by
  have hδ : 0 < min (s - α) (β - s) / 3 := by
    have := hs.1; have := hs.2
    exact div_pos (lt_min (by linarith) (by linarith)) (by norm_num)
  filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)] with k hk
  have he : 0 < 1 / ((k : ℝ) + 1) := by positivity
  set e := 1 / ((k : ℝ) + 1)
  have hm1 := min_le_left (s - α) (β - s)
  have hm2 := min_le_right (s - α) (β - s)
  have u1 : 1 < (s - α) / e - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ he]; linarith
  have u2 : 1 < (β - s) / e - 1 := by
    rw [lt_sub_iff_add_lt, lt_div_iff₀ he]; linarith
  refine ⟨?_, ?_⟩
  · unfold cut
    rw [Real.smoothTransition.one_of_one_le u1.le, Real.smoothTransition.one_of_one_le u2.le, one_mul]
  · unfold cutD
    rw [sd_zero (Or.inr u1), sd_zero (Or.inr u2)]
    ring

theorem h_slopeBound {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) {z₁ z₂ M : ℝ} (hM : ∀ z ∈ Icc z₁ z₂, |deriv h z| ≤ M)
    {x y : ℝ} (hx : x ∈ Icc z₁ z₂) (hy : y ∈ Icc z₁ z₂) : |h y - h x| ≤ M * |y - x| := by
  have hd : Differentiable ℝ h := hh.differentiable (by simp)
  have := (convex_Icc z₁ z₂).norm_image_sub_le_of_norm_deriv_le (fun z _ => hd z)
    (fun z hz => by simpa [Real.norm_eq_abs] using hM z hz) hx hy
  simpa [Real.norm_eq_abs] using this

theorem hcut_bound {h : ℝ → ℝ} {z₁ z₂ M D e z : ℝ} (he : 0 < e) (hM0 : 0 ≤ M) (hD0 : 0 ≤ D)
    (hD : ∀ x, |deriv Real.smoothTransition x| ≤ D)
    (hl : |h z| ≤ M * (z - z₁)) (hr : |h z| ≤ M * (z₂ - z)) :
    |h z * cutD e z₁ z₂ z| ≤ 4 * M * D := by
  have key : ∀ (u d : ℝ), |h z| ≤ M * (d * e) → (u < 0 ∨ 1 < u → deriv Real.smoothTransition u = 0) →
      (0 ≤ u → u ≤ 1 → d ≤ 2) → |h z| * |deriv Real.smoothTransition u| * (1 / e) ≤ 2 * M * D := by
    intro u d hdh hz hu
    by_cases hu' : u < 0 ∨ 1 < u
    · rw [hz hu', abs_zero, mul_zero, zero_mul]; positivity
    · push Not at hu'
      have hd2 := hu hu'.1 hu'.2
      have h1 : |h z| ≤ 2 * M * e := hdh.trans (by
        calc M * (d * e) = (M * e) * d := by ring
          _ ≤ (M * e) * 2 := mul_le_mul_of_nonneg_left hd2 (mul_nonneg hM0 he.le)
          _ = 2 * M * e := by ring)
      have h2 := hD u
      calc |h z| * |deriv Real.smoothTransition u| * (1 / e) ≤ (2 * M * e) * D * (1 / e) := by
            gcongr
        _ = 2 * M * D := by field_simp
  have t1 := key ((z - z₁) / e - 1) ((z - z₁) / e) (by rw [div_mul_cancel₀ _ he.ne']; exact hl) sd_zero
    (fun _ h1 => by linarith)
  have t2 := key ((z₂ - z) / e - 1) ((z₂ - z) / e) (by rw [div_mul_cancel₀ _ he.ne']; exact hr) sd_zero
    (fun _ h1 => by linarith)
  unfold cutD
  have s1 := Real.smoothTransition.nonneg ((z₂ - z) / e - 1)
  have s2 := Real.smoothTransition.le_one ((z₂ - z) / e - 1)
  have s3 := Real.smoothTransition.nonneg ((z - z₁) / e - 1)
  have s4 := Real.smoothTransition.le_one ((z - z₁) / e - 1)
  have ee : (0 - 1) / e = -(1 / e) := by ring
  rw [ee, mul_add]
  refine (abs_add_le _ _).trans ?_
  have a1 : |h z * (deriv Real.smoothTransition ((z - z₁) / e - 1) * (1 / e) *
      Real.smoothTransition ((z₂ - z) / e - 1))| ≤ 2 * M * D := by
    rw [abs_mul, abs_mul, abs_mul, abs_of_pos (one_div_pos.2 he), abs_of_nonneg s1]
    calc |h z| * (|deriv Real.smoothTransition ((z - z₁) / e - 1)| * (1 / e) * Real.smoothTransition ((z₂ - z) / e - 1))
        ≤ |h z| * (|deriv Real.smoothTransition ((z - z₁) / e - 1)| * (1 / e) * 1) := by gcongr
      _ ≤ 2 * M * D := by rw [mul_one, ← mul_assoc]; exact t1
  have a2 : |h z * (Real.smoothTransition ((z - z₁) / e - 1) *
      (deriv Real.smoothTransition ((z₂ - z) / e - 1) * -(1 / e)))| ≤ 2 * M * D := by
    rw [abs_mul, abs_mul, abs_mul, abs_neg, abs_of_pos (one_div_pos.2 he), abs_of_nonneg s3]
    calc |h z| * (Real.smoothTransition ((z - z₁) / e - 1) * (|deriv Real.smoothTransition ((z₂ - z) / e - 1)| * (1 / e)))
        ≤ |h z| * (1 * (|deriv Real.smoothTransition ((z₂ - z) / e - 1)| * (1 / e))) := by gcongr
      _ ≤ 2 * M * D := by rw [one_mul, ← mul_assoc]; exact t2
  linarith


theorem cutD_cont (e α β : ℝ) : Continuous (cutD e α β) := by
  have h1 := sd_cont
  have h2 := Real.smoothTransition.continuous
  unfold cutD
  fun_prop

theorem line_null1 (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ c := by
  have h0 : volume (({c} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp h
  exact hp ⟨h, trivial⟩

theorem line_null2 (c : ℝ) : ∀ᵐ p : ℝ × ℝ ∂volume, p.2 ≠ c := by
  have h0 : volume ((univ : Set ℝ) ×ˢ ({c} : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp h
  exact hp ⟨trivial, h⟩

end Breakdown.FracInternal.StripIbp

namespace Breakdown.CellCert.CellFormula

open Breakdown.FracInternal.StripIbp

theorem stripIbp_holds : StripIbpStatement := by
  intro F dF f a b z₁ z₂ ha hab hz hf hF hdF hW h hh h1 h2
  set R := Icc a b ×ˢ Icc z₁ z₂ with hRdef
  have hRc : IsCompact R := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet R := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨D, hD0, hD⟩ := sd_bound
  have hdc : Continuous (deriv h) := hh.continuous_deriv (by simp)
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := z₁) (b := z₂)).exists_bound_of_continuousOn hdc.continuousOn
  obtain ⟨M2, hM2⟩ := (isCompact_Icc (a := z₁) (b := z₂)).exists_bound_of_continuousOn hh.continuous.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM z₁ (left_mem_Icc.2 hz.le))
  have hM20 : 0 ≤ M2 := (norm_nonneg _).trans (hM2 z₁ (left_mem_Icc.2 hz.le))
  have hMa : ∀ z ∈ Icc z₁ z₂, |deriv h z| ≤ M := fun z hzz => by simpa [Real.norm_eq_abs] using hM z hzz
  have hM2a : ∀ z ∈ Icc z₁ z₂, |h z| ≤ M2 := fun z hzz => by simpa [Real.norm_eq_abs] using hM2 z hzz
  have hl : ∀ z ∈ Icc z₁ z₂, |h z| ≤ M * (z - z₁) := fun z hzz => by
    have := h_slopeBound hh hMa (left_mem_Icc.2 hz.le) hzz
    rwa [h1, sub_zero, abs_of_nonneg (by linarith [hzz.1] : 0 ≤ z - z₁)] at this
  have hr : ∀ z ∈ Icc z₁ z₂, |h z| ≤ M * (z₂ - z) := fun z hzz => by
    have := h_slopeBound hh hMa hzz (right_mem_Icc.2 hz.le)
    rwa [h2, zero_sub, abs_neg, abs_of_nonneg (by linarith [hzz.2] : 0 ≤ z₂ - z)] at this
  set e : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1) with hedef
  have he : ∀ k, 0 < e k := fun k => by positivity
  set G1 : ℝ × ℝ → ℂ := fun p => ((f p.1 : ℝ) : ℂ) * F p with hG1
  set G2 : ℝ × ℝ → ℂ := fun p => ((f p.1 : ℝ) : ℂ) * dF p with hG2
  have iG1 : Integrable G1 (volume.restrict R) := hF
  have iG2 : Integrable G2 (volume.restrict R) := hdF
  set ψ : ℕ → ℝ × ℝ → ℝ := fun k p => (cut (e k) a b p.1 * f p.1) * (h p.2 * cut (e k) z₁ z₂ p.2) with hψdef
  set B' : ℕ → ℝ → ℝ := fun k z => deriv h z * cut (e k) z₁ z₂ z + h z * cutD (e k) z₁ z₂ z with hB'def
  have hB' : ∀ k z, HasDerivAt (fun z => h z * cut (e k) z₁ z₂ z) (B' k z) z := fun k z =>
    (hh.differentiable (by simp) z).hasDerivAt.mul (cut_hasDeriv _ _ _ z)
  have hψs : ∀ k, ContDiff ℝ ∞ (ψ k) := fun k =>
    (((cut_smooth _ _ _).mul hf).comp contDiff_fst).mul ((hh.mul (cut_smooth _ _ _)).comp contDiff_snd)
  have hzero : ∀ k p, ¬ (p.1 ∈ Icc (a + e k) (b - e k) ∧ p.2 ∈ Icc (z₁ + e k) (z₂ - e k)) → ψ k p = 0 := by
    intro k p hp
    simp only [mem_Icc, not_and_or, not_le] at hp
    rcases hp with (hp | hp) | (hp | hp)
    · simp [hψdef, cut_zero (he k) (Or.inl hp.le)]
    · simp [hψdef, cut_zero (he k) (Or.inr hp.le)]
    · simp [hψdef, cut_zero (he k) (Or.inl hp.le)]
    · simp [hψdef, cut_zero (he k) (Or.inr hp.le)]
  have hQc : ∀ k, IsCompact (Icc (a + e k) (b - e k) ×ˢ Icc (z₁ + e k) (z₂ - e k)) := fun k =>
    isCompact_Icc.prod isCompact_Icc
  have hcs : ∀ k, HasCompactSupport (ψ k) := fun k =>
    HasCompactSupport.intro (hQc k) (fun p hp => hzero k p hp)
  have hts : ∀ k, tsupport (ψ k) ⊆ Icc (a + e k) (b - e k) ×ˢ Icc (z₁ + e k) (z₂ - e k) := fun k =>
    closure_minimal (fun p hp => by by_contra hc; exact hp (hzero k p hc)) (hQc k).isClosed
  have hpos : ∀ k, ∀ p ∈ tsupport (ψ k), 0 < p.1 := fun k p hp => by
    have := (hts k hp).1.1; have := he k; linarith
  have hQR : ∀ k, Icc (a + e k) (b - e k) ×ˢ Icc (z₁ + e k) (z₂ - e k) ⊆ R := fun k =>
    prod_mono (Icc_subset_Icc (by linarith [he k]) (by linarith [he k]))
      (Icc_subset_Icc (by linarith [he k]) (by linarith [he k]))
  have hfd : ∀ k p, fderiv ℝ (ψ k) p ((0 : ℝ), (1 : ℝ)) = (cut (e k) a b p.1 * f p.1) * B' k p.2 := by
    intro k p
    have hd : DifferentiableAt ℝ (ψ k) p := (hψs k).differentiable (by simp) p
    have hline : HasDerivAt (fun t : ℝ => p + t • ((0 : ℝ), (1 : ℝ))) ((0 : ℝ), (1 : ℝ)) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ((0 : ℝ), (1 : ℝ))).const_add p
    have c1 := hd.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hline (by simp)
    have c2 : HasDerivAt (fun t : ℝ => ψ k (p + t • ((0 : ℝ), (1 : ℝ))))
        ((cut (e k) a b p.1 * f p.1) * B' k p.2) 0 := by
      have ee : (fun t : ℝ => ψ k (p + t • ((0 : ℝ), (1 : ℝ)))) =
          fun t => (cut (e k) a b p.1 * f p.1) * (h (p.2 + t) * cut (e k) z₁ z₂ (p.2 + t)) := by
        funext t; simp [hψdef]
      rw [ee]
      exact (HasDerivAt.comp_const_add (a := p.2) (x := 0) (by simpa using hB' k p.2)).const_mul _
    exact c1.unique c2
  have eW : ∀ k, ∫ p in R, ((((cut (e k) a b p.1 * f p.1) * B' k p.2 : ℝ)) : ℂ) * F p =
      -∫ p in R, ((ψ k p : ℝ) : ℂ) * dF p := by
    intro k
    have w := hW (ψ k) (hψs k) (hcs k) (hpos k)
    simp only [hfd] at w
    have s1 : ∫ p in R, ((((cut (e k) a b p.1 * f p.1) * B' k p.2 : ℝ)) : ℂ) * F p =
        ∫ p, ((((cut (e k) a b p.1 * f p.1) * B' k p.2 : ℝ)) : ℂ) * F p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      have hp' : p ∉ tsupport (ψ k) := fun hq => hp (hQR k (hts k hq))
      have h0 : fderiv ℝ (ψ k) p = 0 := by
        by_contra hne
        exact hp' (support_fderiv_subset ℝ (Function.mem_support.2 hne))
      rw [← hfd, h0]; simp
    have s2 : ∫ p in R, ((ψ k p : ℝ) : ℂ) * dF p = ∫ p, ((ψ k p : ℝ) : ℂ) * dF p := by
      refine setIntegral_eq_integral_of_forall_compl_eq_zero fun p hp => ?_
      rw [hzero k p (fun hq => hp (hQR k hq))]; simp
    rw [s1, s2, w]
  have hint : ∀ᵐ p ∂(volume.restrict R), p.1 ∈ Ioo a b ∧ p.2 ∈ Ioo z₁ z₂ := by
    filter_upwards [ae_restrict_mem hRm, ae_restrict_of_ae (line_null1 a), ae_restrict_of_ae (line_null1 b),
      ae_restrict_of_ae (line_null2 z₁), ae_restrict_of_ae (line_null2 z₂)] with p hp q1 q2 q3 q4
    exact ⟨⟨lt_of_le_of_ne hp.1.1 (Ne.symm q1), lt_of_le_of_ne hp.1.2 q2⟩,
      ⟨lt_of_le_of_ne hp.2.1 (Ne.symm q3), lt_of_le_of_ne hp.2.2 q4⟩⟩
  have cc : ∀ k, Continuous (fun p : ℝ × ℝ => cut (e k) a b p.1) := fun k =>
    (cut_smooth _ _ _).continuous.comp continuous_fst
  have cz : ∀ k, Continuous (fun p : ℝ × ℝ => cut (e k) z₁ z₂ p.2) := fun k =>
    (cut_smooth _ _ _).continuous.comp continuous_snd
  have cD : ∀ k, Continuous (fun p : ℝ × ℝ => cutD (e k) z₁ z₂ p.2) := fun k =>
    (cutD_cont _ _ _).comp continuous_snd
  have tA : Tendsto (fun k => ∫ p in R, ((((cut (e k) a b p.1 * f p.1) * B' k p.2 : ℝ)) : ℂ) * F p) atTop
      (𝓝 (∫ p in R, ((deriv h p.2 : ℝ) : ℂ) * G1 p)) := by
    have ee : ∀ k, (fun p : ℝ × ℝ => ((((cut (e k) a b p.1 * f p.1) * B' k p.2 : ℝ)) : ℂ) * F p) =
        fun p => ((cut (e k) a b p.1 * B' k p.2 : ℝ) : ℂ) * G1 p := fun k => by
      funext p; simp only [hG1]; push_cast; ring
    simp only [ee]
    refine tendsto_integral_of_dominated_convergence (fun p => (M + 4 * M * D) * ‖G1 p‖) (fun k => ?_)
      (iG1.norm.const_mul _) (fun k => ?_) ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul iG1.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp ((cc k).mul (((hdc.comp continuous_snd).mul (cz k)).add
        ((hh.continuous.comp continuous_snd).mul (cD k))))
    · filter_upwards [ae_restrict_mem hRm] with p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have b1 := cut_le (e k) a b p.1
      have b2 := cut_le (e k) z₁ z₂ p.2
      have b3 := hMa p.2 hp.2
      have b4 := hcut_bound (h := h) (he k) hM0 hD0 hD (hl p.2 hp.2) (hr p.2 hp.2)
      simp only [hB'def]
      rw [abs_mul]
      calc |cut (e k) a b p.1| * |deriv h p.2 * cut (e k) z₁ z₂ p.2 + h p.2 * cutD (e k) z₁ z₂ p.2|
          ≤ 1 * (M * 1 + 4 * M * D) := by
            gcongr
            refine (abs_add_le _ _).trans (add_le_add ?_ b4)
            rw [abs_mul]; gcongr
        _ = M + 4 * M * D := by ring
    · filter_upwards [hint] with p hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [cut_lim hp.1, cut_lim hp.2] with k k1 k2
      have c1 : cut (e k) a b p.1 = 1 := k1.1
      have c2 : cut (e k) z₁ z₂ p.2 = 1 := k2.1
      have c3 : cutD (e k) z₁ z₂ p.2 = 0 := k2.2
      simp only [hB'def, c1, c2, c3]
      push_cast; ring
  have tB : Tendsto (fun k => ∫ p in R, ((ψ k p : ℝ) : ℂ) * dF p) atTop
      (𝓝 (∫ p in R, ((h p.2 : ℝ) : ℂ) * G2 p)) := by
    have ee : ∀ k, (fun p : ℝ × ℝ => ((ψ k p : ℝ) : ℂ) * dF p) =
        fun p => ((cut (e k) a b p.1 * (h p.2 * cut (e k) z₁ z₂ p.2) : ℝ) : ℂ) * G2 p := fun k => by
      funext p; simp only [hG2, hψdef]; push_cast; ring
    simp only [ee]
    refine tendsto_integral_of_dominated_convergence (fun p => M2 * ‖G2 p‖) (fun k => ?_)
      (iG2.norm.const_mul _) (fun k => ?_) ?_
    · refine (Continuous.aestronglyMeasurable ?_).mul iG2.aestronglyMeasurable
      exact Complex.continuous_ofReal.comp ((cc k).mul ((hh.continuous.comp continuous_snd).mul (cz k)))
    · filter_upwards [ae_restrict_mem hRm] with p hp
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
      have b1 := cut_le (e k) a b p.1
      have b2 := cut_le (e k) z₁ z₂ p.2
      have b3 := hM2a p.2 hp.2
      rw [abs_mul, abs_mul]
      calc |cut (e k) a b p.1| * (|h p.2| * |cut (e k) z₁ z₂ p.2|) ≤ 1 * (M2 * 1) := by gcongr
        _ = M2 := by ring
    · filter_upwards [hint] with p hp
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [cut_lim hp.1, cut_lim hp.2] with k k1 k2
      have c1 : cut (e k) a b p.1 = 1 := k1.1
      have c2 : cut (e k) z₁ z₂ p.2 = 1 := k2.1
      simp only [c1, c2]
      push_cast; ring
  have lim : ∫ p in R, ((deriv h p.2 : ℝ) : ℂ) * G1 p = -∫ p in R, ((h p.2 : ℝ) : ℂ) * G2 p :=
    tendsto_nhds_unique tA (tB.neg.congr fun k => (eW k).symm)
  have j1 : Integrable (fun p : ℝ × ℝ => ((deriv h p.2 : ℝ) : ℂ) * G1 p) (volume.restrict R) :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp (hdc.comp continuous_snd)).continuousOn iG1 hRc
  have j2 : Integrable (fun p : ℝ × ℝ => ((h p.2 : ℝ) : ℂ) * G2 p) (volume.restrict R) :=
    IntegrableOn.continuousOn_mul (Complex.continuous_ofReal.comp (hh.continuous.comp continuous_snd)).continuousOn
      iG2 hRc
  have ef : (fun p : ℝ × ℝ => ((f p.1 * deriv h p.2 : ℝ) : ℂ) * F p + ((f p.1 * h p.2 : ℝ) : ℂ) * dF p) =
      fun p => ((deriv h p.2 : ℝ) : ℂ) * G1 p + ((h p.2 : ℝ) : ℂ) * G2 p := by
    funext p; simp only [hG1, hG2]; push_cast; ring
  rw [ef, integral_add j1 j2, lim, neg_add_cancel]

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula.RadialTangentInternal

open SteadyCert Assembly CellAnalysis LowEntry.Internal

private theorem poly_cont2 (q : Polynomial ℝ) : Continuous (fun p : ℝ × ℝ => ((q.eval p.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (q.continuous.comp continuous_snd)

private theorem hbase {c o z₁ z₂ : ℝ} (hz : z₁ < z₂) {V G0 G2 S02 S20 : ℝ × ℝ → ℂ}
    (hA : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p)
      (Icc (min c o) (max c o) ×ˢ Icc z₁ z₂))
    (hB : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * G2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * S02 p)
      (Icc (min c o) (max c o) ×ˢ Icc z₁ z₂))
    (hS : ∀ᵐ p ∂(volume.restrict (Icc (min c o) (max c o) ×ˢ Icc z₁ z₂)), S20 p = S02 p)
    (hI : ∀ h : ℝ → ℝ, ContDiff ℝ ∞ h → h z₁ = 0 → h z₂ = 0 →
      ∫ p in Icc (min c o) (max c o) ×ˢ Icc z₁ z₂,
        ((((1 / (c - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p) * ((deriv h p.2 : ℝ) : ℂ)
          + (((1 / (c - o) : ℝ) : ℂ) * G2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * S02 p) * ((h p.2 : ℝ) : ℂ)) = 0)
    (q : Polynomial ℝ) (t : ℝ → ℝ) (ht : ∀ u, t u = q.eval u) :
    radialStripMoment c o z₁ z₂ G2 S20 t =
      ((t z₂ : ℝ) : ℂ) * cornerMoment c o z₂ z₁ V G0 G2 S02
        - ((t z₁ : ℝ) : ℂ) * cornerMoment c o z₁ z₂ V G0 G2 S02
        - radialStripMoment c o z₁ z₂ V G0 (deriv t) := by
  obtain rfl : t = fun u => q.eval u := funext ht
  set R := Icc (min c o) (max c o) ×ˢ Icc z₁ z₂ with hRdef
  have hR : IsCompact R := isCompact_Icc.prod isCompact_Icc
  set A := fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * V p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * G0 p with hAdef
  set B := fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * G2 p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * S02 p with hBdef
  have iA : ∀ g : ℝ × ℝ → ℂ, Continuous g → Integrable (fun p => A p * g p) (volume.restrict R) :=
    fun g hg => hA.mul_continuousOn hg.continuousOn hR
  have iB : ∀ g : ℝ × ℝ → ℂ, Continuous g → Integrable (fun p => B p * g p) (volume.restrict R) :=
    fun g hg => hB.mul_continuousOn hg.continuousOn hR
  have hz' : z₂ - z₁ ≠ 0 := sub_ne_zero.2 hz.ne'
  have hz'' : z₁ - z₂ ≠ 0 := sub_ne_zero.2 hz.ne
  have hdt : ∀ u, deriv (fun u => q.eval u) u = q.derivative.eval u := fun u => (q.hasDerivAt u).deriv
  set h : ℝ → ℝ := fun u => q.eval u - q.eval z₂ * ((u - z₁) / (z₂ - z₁)) - q.eval z₁ * ((u - z₂) / (z₁ - z₂))
    with hh
  have hdh : ∀ u, HasDerivAt h (q.derivative.eval u - q.eval z₂ * (1 / (z₂ - z₁)) - q.eval z₁ * (1 / (z₁ - z₂))) u := by
    intro u
    have h1 : HasDerivAt (fun u : ℝ => (u - z₁) / (z₂ - z₁)) (1 / (z₂ - z₁)) u :=
      ((hasDerivAt_id u).sub_const z₁).div_const _
    have h0 : HasDerivAt (fun u : ℝ => (u - z₂) / (z₁ - z₂)) (1 / (z₁ - z₂)) u :=
      ((hasDerivAt_id u).sub_const z₂).div_const _
    exact ((q.hasDerivAt u).sub (h1.const_mul _)).sub (h0.const_mul _)
  have hq : ContDiff ℝ ∞ (fun u => q.eval u) := by
    rw [show (fun u => q.eval u) = fun u => ∑ i ∈ Finset.range (q.natDegree + 1), q.coeff i * u ^ i from
      funext fun u => q.eval_eq_sum_range u]
    exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_id.pow i)
  have hC1 : ContDiff ℝ ∞ h :=
    (hq.sub (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _))).sub
      (contDiff_const.mul ((contDiff_id.sub contDiff_const).div_const _))
  have h1 : h z₁ = 0 := by simp only [hh]; field_simp; ring
  have h2 : h z₂ = 0 := by simp only [hh]; field_simp; ring
  have key := hI h hC1 h1 h2
  have cP1 : Continuous (fun p : ℝ × ℝ => (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)) := by fun_prop
  have cP0 : Continuous (fun p : ℝ × ℝ => (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ)) := by fun_prop
  have ekey : (fun p : ℝ × ℝ => A p * ((deriv h p.2 : ℝ) : ℂ) + B p * ((h p.2 : ℝ) : ℂ)) =
      fun p => ((A p * ((q.derivative.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p)
          + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * A p)
        + ((B p * ((q.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)))
          + (-((q.eval z₁ : ℝ) : ℂ)) * (B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))) := by
    funext p
    rw [(hdh p.2).deriv]
    simp only [hh]
    push_cast
    ring
  have iAD : Integrable (fun p => A p * ((q.derivative.eval p.2 : ℝ) : ℂ)) (volume.restrict R) :=
    iA _ (poly_cont2 q.derivative)
  have iBT : Integrable (fun p => B p * ((q.eval p.2 : ℝ) : ℂ)) (volume.restrict R) := iB _ (poly_cont2 q)
  have iB1 : Integrable (fun p => B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)) (volume.restrict R) := iB _ cP1
  have iB0 : Integrable (fun p => B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ)) (volume.restrict R) := iB _ cP0
  have hA' : Integrable A (volume.restrict R) := hA
  rw [ekey] at key
  have e1 : ∫ p in R, ((A p * ((q.derivative.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p)
          + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * A p)
        + ((B p * ((q.eval p.2 : ℝ) : ℂ) + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)))
          + (-((q.eval z₁ : ℝ) : ℂ)) * (B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))) =
      ((∫ p in R, A p * ((q.derivative.eval p.2 : ℝ) : ℂ)) + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * (∫ p in R, A p)
          + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * ∫ p in R, A p)
        + ((∫ p in R, B p * ((q.eval p.2 : ℝ) : ℂ))
          + (-((q.eval z₂ : ℝ) : ℂ)) * (∫ p in R, B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ))
          + (-((q.eval z₁ : ℝ) : ℂ)) * ∫ p in R, B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ)) := by
    have jA1 : Integrable (fun p => A p * ((q.derivative.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p) (volume.restrict R) := iAD.add (hA'.const_mul _)
    have jA2 : Integrable (fun p => (A p * ((q.derivative.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ * (1 / (z₂ - z₁)) : ℝ) : ℂ)) * A p) + (-((q.eval z₁ * (1 / (z₁ - z₂)) : ℝ) : ℂ)) * A p)
        (volume.restrict R) := jA1.add (hA'.const_mul _)
    have jB1 : Integrable (fun p => B p * ((q.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ))) (volume.restrict R) :=
      iBT.add (iB1.const_mul _)
    have jB2 : Integrable (fun p => (B p * ((q.eval p.2 : ℝ) : ℂ)
        + (-((q.eval z₂ : ℝ) : ℂ)) * (B p * (((p.2 - z₁) / (z₂ - z₁) : ℝ) : ℂ)))
        + (-((q.eval z₁ : ℝ) : ℂ)) * (B p * (((p.2 - z₂) / (z₁ - z₂) : ℝ) : ℂ))) (volume.restrict R) :=
      jB1.add (iB0.const_mul _)
    rw [integral_add jA2 jB2, integral_add jA1 (hA'.const_mul _), integral_add iAD (hA'.const_mul _),
      integral_add jB1 (iB0.const_mul _), integral_add iBT (iB1.const_mul _),
      integral_const_mul, integral_const_mul, integral_const_mul, integral_const_mul]
  rw [e1] at key
  have eC : ∀ cz oz : ℝ, cornerMoment c o cz oz V G0 G2 S02 = edgeSign c o * edgeSign cz oz *
      ∫ p in Icc (min c o) (max c o) ×ˢ Icc (min cz oz) (max cz oz),
        (A p * ((1 / (cz - oz) : ℝ) : ℂ) + B p * (((p.2 - oz) / (cz - oz) : ℝ) : ℂ)) := by
    intro cz oz
    unfold cornerMoment
    congr 2
    funext p
    simp only [hAdef, hBdef]
    ring
  have eV : radialStripMoment c o z₁ z₂ V G0 (deriv fun u => q.eval u) =
      edgeSign c o * ∫ p in R, A p * ((q.derivative.eval p.2 : ℝ) : ℂ) := by
    unfold radialStripMoment
    congr 2
    funext p
    rw [hdt]
  have eL : radialStripMoment c o z₁ z₂ G2 S20 (fun u => q.eval u) =
      edgeSign c o * ∫ p in R, B p * ((q.eval p.2 : ℝ) : ℂ) := by
    unfold radialStripMoment
    congr 1
    refine integral_congr_ae ?_
    filter_upwards [hS] with p hp
    simp only [hBdef]
    rw [hp]
  have s1 : edgeSign z₂ z₁ = 1 := by simp [edgeSign, hz]
  have s0 : edgeSign z₁ z₂ = -1 := by simp [edgeSign, not_lt.2 hz.le]
  rw [eL, eV, eC, eC, min_eq_right hz.le, max_eq_left hz.le, min_eq_left hz.le, max_eq_right hz.le, s1, s0,
    integral_add (hA'.mul_const _) iB1, integral_add (hA'.mul_const _) iB0, integral_mul_const, integral_mul_const]
  beta_reduce
  push_cast at key ⊢
  linear_combination (edgeSign c o) * key


private theorem axis_null : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h0 : volume (({0} : Set ℝ) ×ˢ (univ : Set ℝ)) = 0 := by
    rw [Measure.volume_eq_prod, Measure.prod_prod]
    simp
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp h
  exact hp ⟨h, trivial⟩

private theorem swap_on {K : CellBox} (hK : IsCellBox K) {S20 S02 : ℝ × ℝ → ℂ}
    (h : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → S20 p = S02 p) : ∀ᵐ p ∂(volume.restrict K.rect), S20 p = S02 p := by
  have hm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  filter_upwards [ae_restrict_of_ae h, ae_restrict_of_ae axis_null, ae_restrict_mem hm] with p h1 h2 h3
  exact h1 (lt_of_le_of_ne (hK.r_order.1.trans h3.1.1) (Ne.symm h2))


private theorem dtest {φ : Space → ℝ} (hφ : IsTestScalar φ) (u : Space) :
    IsTestScalar (fun y => fderiv ℝ φ y u) :=
  ⟨(hφ.1.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const,
    hφ.2.fderiv_apply (𝕜 := ℝ) u⟩

private theorem mixed3 {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (y u w : Space) :
    fderiv ℝ (fun x => fderiv ℝ φ x u) y w = fderiv ℝ (fun x => fderiv ℝ φ x w) y u := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp)
  have e : ∀ u', fderiv ℝ (fun x => fderiv ℝ φ x u') y = (fderiv ℝ (fderiv ℝ φ) y).flip u' := by
    intro u'
    rw [fderiv_clm_apply (hd y) (differentiableAt_const u')]
    simp
  rw [e, e]
  simp only [ContinuousLinearMap.flip_apply]
  exact (hφ.contDiffAt.isSymmSndFDerivAt (by simp; norm_cast)) w u

private theorem weak_swap {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (φ : Space → ℝ)
    (hφ : IsTestScalar φ) (i j : Fin 3) :
    ∫ y, φ y • H y (unitVector j) (unitVector i) = ∫ y, φ y • H y (unitVector i) (unitVector j) := by
  have a1 := hs.weak_second φ hφ i j
  have a2 := hs.weak_second φ hφ j i
  have b1 := hs.weak_gradient _ (dtest hφ (unitVector j)) i
  have b2 := hs.weak_gradient _ (dtest hφ (unitVector i)) j
  beta_reduce at b1 b2
  have mx : (fun y => fderiv ℝ (fun x => fderiv ℝ φ x (unitVector j)) y (unitVector i) • v y) =
      fun y => fderiv ℝ (fun x => fderiv ℝ φ x (unitVector i)) y (unitVector j) • v y :=
    funext fun y => by rw [mixed3 hφ.1]
  rw [mx, a1] at b1
  rw [a2, b1] at b2
  simpa using b2

private theorem col_memLp {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (j i : Fin 3) :
    MemLp (fun y => H y (unitVector j) (unitVector i)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
    (hm.apply_continuousLinearMap (unitVector j)).apply_continuousLinearMap (unitVector i)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc ‖H y (unitVector j) (unitVector i)‖ ^ 2 ≤ ∑ i' : Fin 3, ‖H y (unitVector j) (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ‖H y (unitVector j) (unitVector i')‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
    _ ≤ ∑ j' : Fin 3, ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

private theorem sym_ae {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    ∀ᵐ y ∂volume, ∀ i j : Fin 3, H y (unitVector j) (unitVector i) = H y (unitVector i) (unitVector j) := by
  have hloc : ∀ j i : Fin 3, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume :=
    fun j i => (col_memLp hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)
  rw [ae_all_iff]
  intro i
  rw [ae_all_iff]
  intro j
  have h0 := ae_eq_zero_of_integral_contDiff_smul_eq_zero ((hloc j i).sub (hloc i j)) (fun g hg hgc => by
    have e : (fun x => g x • (H x (unitVector j) (unitVector i) - H x (unitVector i) (unitVector j))) =
        fun x => g x • H x (unitVector j) (unitVector i) - g x • H x (unitVector i) (unitVector j) :=
      funext fun x => smul_sub _ _ _
    simp only [Pi.sub_apply]
    rw [e, integral_sub ((hloc j i).integrable_smul_left_of_hasCompactSupport hg.continuous hgc)
      ((hloc i j).integrable_smul_left_of_hasCompactSupport hg.continuous hgc), weak_swap hs g ⟨hg, hgc⟩ i j,
      sub_self])
  filter_upwards [h0] with y hy
  exact sub_eq_zero.1 hy

private theorem vec_sum (u : Space) : u = ∑ k : Fin 3, u k • unitVector k := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

private theorem sym_all (M : Space →L[ℝ] Space →L[ℝ] Space)
    (h : ∀ i j : Fin 3, M (unitVector j) (unitVector i) = M (unitVector i) (unitVector j)) (u w : Space) :
    M u w = M w u := by
  rw [vec_sum u, vec_sum w]
  simp only [Fin.sum_univ_three, map_add, map_smul, add_apply, smul_apply]
  rw [h 0 1, h 0 2, h 1 2]
  module

private theorem frameThird_per (θ : ℝ) (M : Space →L[ℝ] Space →L[ℝ] Space) (a b c : Fin 3) :
    frameThird (θ + 2 * π) M a b c = frameThird θ M a b c := by
  simp only [frameThird, frameUnit, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem third_Ioo (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a b c : Fin 3)
    (p : ℝ × ℝ) : modeThird m n H a b c p = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameThird θ (H (cylPoint p.1 θ p.2)) a b c : ℂ) := by
  unfold modeThird
  rw [per_interval]
  intro θ
  simp only [phase_per, cylPoint_per, frameThird_per]

end Breakdown.CellCert.CellFormula.RadialTangentInternal

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis LowEntry.Internal RadialTangentInternal

theorem modeThirdSwap_holds : ModeThirdSwapStatement := by
  intro m v G H hs n a
  have h1 : ∀ᵐ q ∂muU, ∀ i j : Fin 3,
      H (cylArg q) (unitVector j) (unitVector i) = H (cylArg q) (unitVector i) (unitVector j) := qmp.ae (sym_ae hs)
  rw [muU_def] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h2
  filter_upwards [h2] with p hp hp1
  have hp' := hp ⟨hp1, trivial⟩
  rw [third_Ioo, third_Ioo]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hp'] with θ hθ
  have hθ' : ∀ i j : Fin 3, H (cylPoint p.1 θ p.2) (unitVector j) (unitVector i) =
      H (cylPoint p.1 θ p.2) (unitVector i) (unitVector j) := hθ
  simp only [frameThird]
  rw [sym_all _ hθ' (frameUnit θ 0) (frameUnit θ 2)]


theorem radialTangent_of (hI : RadialStripIbpStatement) : RadialTangentStatement := by
  intro k N c K S B L hL x hx n e a t he hax ht
  obtain ⟨q, hq⟩ := ht
  have hK := hL.box_valid
  have hf : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := hL.order_eq ▸ hx.1
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have hr : K.r₁ < K.r₂ := hK.r_order.2
  have hsw := swap_on hK (modeThirdSwap_holds _ _ _ _ hf n a)
  unfold CellLayout.cornerValue CellLayout.sideVelocityValue radialFaceMoment CellLayout.sideRadialIndex
  rw [if_pos he]
  simp only [CellLayout.gradModeOf, CellLayout.secondModeOf, hL.box_eq]
  obtain he0 | he1 : e.val = 0 ∨ e.val = 1 := by omega
  · have hne := hax he0
    simp only [he0, if_true, eq_false (show (0 : Fin 2) ≠ 1 by decide), if_false]
    have hRr : Icc (min K.r₁ K.r₂) (max K.r₁ K.r₂) ×ˢ Icc K.z₁ K.z₂ = K.rect := by
      rw [min_eq_left hr.le, max_eq_right hr.le]; rfl
    obtain ⟨i1, i2, i3⟩ := hI _ _ _ _ hf K hK n a K.r₁ K.r₂ (Or.inl ⟨rfl, rfl, hne⟩)
    rw [← hRr] at i1 i2 i3 hsw
    exact hbase hz i1 i2 hsw i3 q t hq
  · simp only [he1, one_ne_zero, if_false, if_true, eq_false (show (1 : Fin 2) ≠ 0 by decide)]
    have hRr : Icc (min K.r₂ K.r₁) (max K.r₂ K.r₁) ×ˢ Icc K.z₁ K.z₂ = K.rect := by
      rw [min_eq_right hr.le, max_eq_left hr.le]; rfl
    obtain ⟨i1, i2, i3⟩ := hI _ _ _ _ hf K hK n a K.r₂ K.r₁ (Or.inr ⟨rfl, rfl⟩)
    rw [← hRr] at i1 i2 i3 hsw
    exact hbase hz i1 i2 hsw i3 q t hq

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula.RadialTangentInternal

open SteadyCert Assembly CellAnalysis LowEntry.Internal

private theorem rect_cpt (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

private theorem rect_ms (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

private theorem rect_sub (K : CellBox) (hK : IsCellBox K) : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ :=
  prod_mono (Icc_subset_Icc hK.r_order.1 le_rfl) (Icc_subset_Icc (by linarith [hK.z_order.1, hK.z_order.2]) le_rfl)

private theorem int_mix (K : CellBox) {F : ℝ × ℝ → ℂ} {f k : ℝ → ℝ}
    (hF : IntegrableOn (fun p : ℝ × ℝ => ((f p.1 : ℝ) : ℂ) * F p) K.rect) (hk : Continuous k) :
    IntegrableOn (fun p : ℝ × ℝ => ((f p.1 * k p.2 : ℝ) : ℂ) * F p) K.rect := by
  have h := hF.continuousOn_mul (g := fun p : ℝ × ℝ => ((k p.2 : ℝ) : ℂ))
    (Complex.continuous_ofReal.comp (hk.comp continuous_snd)).continuousOn (rect_cpt K)
  refine h.congr_fun (fun p _ => ?_) (rect_ms K)
  simp only
  push_cast
  ring

private theorem phi_mode (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {X : Space → (Space →L[ℝ] Space)}
    (hX1 : AEStronglyMeasurable X volume) (hX2 : Integrable (fun y => entrySq (X y))) (a b : Fin 3) (c o : ℝ)
    (hco : (c = K.r₁ ∧ o = K.r₂ ∧ K.r₁ ≠ 0) ∨ (c = K.r₂ ∧ o = K.r₁)) :
    IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n X a b p) K.rect := by
  have gi := gradMode_int K hK m n hX1 hX2 a b
  by_cases h0 : K.r₁ = 0
  · obtain ⟨rfl, rfl⟩ : c = K.r₂ ∧ o = K.r₁ := by
      rcases hco with h | h
      · exact absurd h0 h.2.2
      · exact h
    refine IntegrableOn.congr_fun (Integrable.const_mul gi ((1 / (K.r₂ - K.r₁) : ℝ) : ℂ)) (fun p _ => ?_) (rect_ms K)
    simp only [CellBox.lineWeight, h0, if_true]
    push_cast
    ring
  · have g1 : IntegrableOn (gradMode m n X a b) K.rect := by
      refine gi.congr_fun (fun p _ => ?_) (rect_ms K)
      simp only [CellBox.lineWeight, h0, if_false]
      push_cast
      ring
    exact g1.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ))
      (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)).continuousOn (rect_cpt K)

private theorem third_as_grad (m : ℕ) (n : ℤ) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : Fin 3) (p : ℝ × ℝ) :
    modeThird m n H a 0 2 p = gradMode m n (fun y => H y axialUnit) a 0 p := rfl

private theorem axial_sq {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) :
    Integrable (fun y => entrySq (H y axialUnit)) := by
  refine hi.mono' ?_ (Filter.Eventually.of_forall fun y => ?_)
  · unfold entrySq
    exact Finset.aestronglyMeasurable_sum (f := fun i y => ‖H y axialUnit (unitVector i)‖ ^ 2) Finset.univ fun i _ =>
      (((hm.apply_continuousLinearMap axialUnit).apply_continuousLinearMap (unitVector i)).norm.pow 2)
  · rw [Real.norm_eq_abs, abs_of_nonneg (by unfold entrySq; positivity)]
    unfold entrySq
    exact Finset.single_le_sum (f := fun i => ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ (2 : Fin 3))

end Breakdown.CellCert.CellFormula.RadialTangentInternal

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis LowEntry.Internal RadialTangentInternal FracInternal.ModeHeightAxis

theorem radialStripIbp_of (hS : StripIbpStatement) : RadialStripIbpStatement := by
  intro m v G H hs K hK n a c o hco
  have hr := hK.r_order
  have hz := hK.z_order
  have iV : IntegrableOn (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) K.rect := by
    have h := vel_int K.r₂ K.z₂ hs.velocity_six (velKernel m n a) (velKernel_cont m n a) (velKernel_bound m n a)
    rw [show (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p => (1 / (2 * π) : ℂ) *
      ∫ θ in Ioo (-π) π, velKernel m n a θ (v (cylPoint p.1 θ p.2)) from funext fun p => modeVec_eq m n v a p]
    exact IntegrableOn.mono_set (Integrable.const_mul h _) (rect_sub K hK)
  have iG2 : IntegrableOn (gradMode m n G a 2) K.rect :=
    (modeHeightAxis m v G H hs n a K.r₂ K.z₂).mono_set (rect_sub K hK)
  have iG0 := phi_mode K hK m n hs.measurable_gradient hs.gradient_two a 0 c o hco
  have iS : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) K.rect :=
    phi_mode K hK m n (hs.measurable_second.apply_continuousLinearMap axialUnit)
      (axial_sq hs.measurable_second hs.second_two) a 0 c o hco
  have iV' : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a) K.rect :=
    iV.const_mul _
  have iG2' : IntegrableOn (fun p : ℝ × ℝ => ((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p) K.rect :=
    iG2.const_mul _
  refine ⟨iV'.add iG0, iG2'.add iS, fun h hh h1 h2 => ?_⟩
  have W := modeWeakIdentity m v G H hs n a
  have e1 := hS (fun p => modeVec m n v p.1 p.2 a) (gradMode m n G a 2) (fun _ => 1 / (c - o)) K.r₁ K.r₂ K.z₁ K.z₂
    hr.1 hr.2 hz.2 contDiff_const iV' iG2' (fun ψ q1 q2 q3 => (W ψ q1 q2 q3).2.1) h hh h1 h2
  have e2 := hS (gradMode m n G a 0) (modeThird m n H a 0 2) (fun r => (r - o) / (c - o)) K.r₁ K.r₂ K.z₁ K.z₂
    hr.1 hr.2 hz.2 ((contDiff_id.sub contDiff_const).div_const _) iG0 iS (fun ψ q1 q2 q3 => (W ψ q1 q2 q3).2.2.2)
    h hh h1 h2
  have hdc : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have j1 : IntegrableOn (fun p : ℝ × ℝ => (((1 / (c - o)) * deriv h p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
      + (((1 / (c - o)) * h p.2 : ℝ) : ℂ) * gradMode m n G a 2 p) K.rect :=
    (int_mix K (f := fun _ => 1 / (c - o)) iV' hdc).add (int_mix K (f := fun _ => 1 / (c - o)) iG2' hh.continuous)
  have j2 : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) * deriv h p.2 : ℝ) : ℂ) * gradMode m n G a 0 p
      + (((p.1 - o) / (c - o) * h p.2 : ℝ) : ℂ) * modeThird m n H a 0 2 p) K.rect :=
    (int_mix K (f := fun r => (r - o) / (c - o)) iG0 hdc).add
      (int_mix K (f := fun r => (r - o) / (c - o)) iS hh.continuous)
  have e : (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * gradMode m n G a 0 p) * ((deriv h p.2 : ℝ) : ℂ)
              + (((1 / (c - o) : ℝ) : ℂ) * gradMode m n G a 2 p
                + (((p.1 - o) / (c - o) : ℝ) : ℂ) * modeThird m n H a 0 2 p) * ((h p.2 : ℝ) : ℂ))) =
      fun p => ((((1 / (c - o)) * deriv h p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
        + (((1 / (c - o)) * h p.2 : ℝ) : ℂ) * gradMode m n G a 2 p)
        + ((((p.1 - o) / (c - o) * deriv h p.2 : ℝ) : ℂ) * gradMode m n G a 0 p
        + (((p.1 - o) / (c - o) * h p.2 : ℝ) : ℂ) * modeThird m n H a 0 2 p) := by
    funext p
    push_cast
    ring
  rw [e, integral_add j1 j2]
  have e1' : ∫ p in K.rect, ((((1 / (c - o)) * deriv h p.2 : ℝ) : ℂ) * modeVec m n v p.1 p.2 a
      + (((1 / (c - o)) * h p.2 : ℝ) : ℂ) * gradMode m n G a 2 p) = 0 := e1
  have e2' : ∫ p in K.rect, ((((p.1 - o) / (c - o) * deriv h p.2 : ℝ) : ℂ) * gradMode m n G a 0 p
      + (((p.1 - o) / (c - o) * h p.2 : ℝ) : ℂ) * modeThird m n H a 0 2 p) = 0 := e2
  rw [e1', e2', add_zero]

theorem radialTangent_of_strip (hS : StripIbpStatement) : RadialTangentStatement :=
  radialTangent_of (radialStripIbp_of hS)

end Breakdown.CellCert.CellFormula

namespace Breakdown.CellCert.CellFormula

theorem radialTangent_holds : RadialTangentStatement :=
  radialTangent_of_strip stripIbp_holds

end Breakdown.CellCert.CellFormula
