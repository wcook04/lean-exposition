import Breakdown.Frac.StRealize
import Breakdown.FreqTr.NiceDense
import Breakdown.FreqTr.Realization

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

private theorem contDiff_weight_smul {m : Space → CSpace} (hm : ContDiff ℝ ∞ m) {r : ℝ}
    (hr : 0 < r) (h0 : ∀ ξ : Space, ‖ξ‖ < r → m ξ = 0) (p : ℝ) :
    ContDiff ℝ ∞ (fun ξ => ((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) := by
  rw [contDiff_iff_contDiffAt]
  intro ξ
  by_cases hξ : ‖ξ‖ < r
  · have hev : (fun ξ => ((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) =ᶠ[nhds ξ] fun _ => (0 : CSpace) := by
      have hopen : IsOpen {x : Space | ‖x‖ < r} := isOpen_lt continuous_norm continuous_const
      filter_upwards [hopen.mem_nhds hξ] with x hx
      simp [h0 x hx]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hne : ξ ≠ 0 := by
      intro h
      apply hξ
      simpa [h] using hr
    have hn : ContDiffAt ℝ ∞ (fun x : Space => 2 * π * ‖x‖) ξ :=
      contDiffAt_const.mul (contDiffAt_norm ℝ hne)
    have hpos : 2 * π * ‖ξ‖ ≠ 0 := mul_ne_zero (by positivity) (norm_ne_zero_iff.2 hne)
    exact (hn.rpow_const_of_ne hpos).smul hm.contDiffAt

private theorem nice_weight {m : Space → CSpace} (hm : IsNiceSymbol m) (p : ℝ) :
    IsNiceSymbol (fun ξ => ((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) := by
  obtain ⟨hc, hs, ⟨r, hr, h0⟩, hh, hd⟩ := hm
  have hsupp : HasCompactSupport (fun ξ => ((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) :=
    HasCompactSupport.smul_left (f := fun ξ : Space => ((2 * π * ‖ξ‖) ^ p : ℝ)) hs
  have hz : ∀ ξ : Space, ‖ξ‖ < r → ((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ = 0 := by
    intro ξ hξ
    rw [h0 ξ hξ, smul_zero]
  have hconjSym : ∀ ξ : Space, ((2 * π * ‖-ξ‖) ^ p : ℝ) • m (-ξ) =
      conjVec (((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) := by
    intro ξ
    rw [norm_neg, hh ξ, ContinuousLinearMap.map_smul]
  have hdiv : ∀ ξ : Space, ∑ i : Fin 3, ((ξ i : ℝ) : ℂ) * ((((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) i) = 0 := by
    intro ξ
    have e : ∀ i : Fin 3, ((ξ i : ℝ) : ℂ) * ((((2 * π * ‖ξ‖) ^ p : ℝ) • m ξ) i) =
        (((2 * π * ‖ξ‖) ^ p : ℝ) : ℂ) * (((ξ i : ℝ) : ℂ) * m ξ i) := by
      intro i
      rw [PiLp.smul_apply, Complex.real_smul]
      ring
    rw [Finset.sum_congr rfl (fun i _ => e i), ← Finset.mul_sum, hd ξ, mul_zero]
  exact ⟨contDiff_weight_smul hc hr h0 p, hsupp, ⟨r, hr, hz⟩, hconjSym, hdiv⟩

private theorem eLpNorm_weight_le {u : Space → CSpace} {R : ℝ} (_hR : 0 ≤ R) {α : ℝ}
    (hα : 0 < α) (hu : ∀ ξ, R ≤ ‖ξ‖ → u ξ = 0) :
    eLpNorm (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • u ξ) 2 volume ≤
      ENNReal.ofReal ((2 * π * R) ^ (2 * α)) * eLpNorm u 2 volume := by
  have key : ∀ ξ, ‖((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • u ξ‖ ≤ (2 * π * R) ^ (2 * α) * ‖u ξ‖ := by
    intro ξ
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    by_cases h : R ≤ ‖ξ‖
    · simp only [hu ξ h, norm_zero, mul_zero, le_refl]
    · replace h := lt_of_not_ge h
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply Real.rpow_le_rpow (by positivity) _ (by linarith)
      have := pi_pos
      nlinarith [norm_nonneg ξ]
  exact eLpNorm_le_mul_eLpNorm_of_ae_le_mul (Filter.Eventually.of_forall key) 2

private theorem continuous_weight {α : ℝ} (hα : 0 < α) :
    Continuous (fun ξ : Space => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ)) :=
  (continuous_const.mul continuous_norm).rpow_const (fun _ => Or.inr (by linarith))


open Internal.NiceDense in
private theorem symbolDense (α : ℝ) (hα : 0 < α) (χ ψ : X) (hχψ : IsFracOf α χ ψ) (ε : ℝ)
    (hε : 0 < ε) : ∃ m, IsNiceSymbol m ∧
      (eLpNorm (fun ξ => m ξ - (χ : L2C) ξ) 2 volume).toReal < ε ∧
      (eLpNorm (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ - (ψ : L2C) ξ) 2 volume).toReal
        < ε := by
  obtain ⟨hsym, hdiv⟩ := sig_ae fieldOpRealized_holds χ
  set f : Space → CSpace := ((χ : L2C) : Space → CSpace) with hfdef
  have hf2 : MemLp f 2 volume := Lp.memLp _
  have hψf : (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • f ξ) =ᵐ[volume]
      ((ψ : L2C) : Space → CSpace) := by
    filter_upwards [hχψ] with ξ h using h.symm
  have hl2 : MemLp (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • f ξ) 2 volume :=
    (Lp.memLp _).ae_eq hψf.symm
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
  set C : ℝ := (2 * π * (2 * R)) ^ (2 * α) with hCdef
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
    have e : (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ - (ψ : L2C) ξ) =ᵐ[volume]
        (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • (m - f₁) ξ) -
          (outerSet n).indicator (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • f ξ) := by
      filter_upwards [hψf] with ξ h
      have := congrFun hff₁ ξ
      simp only [Pi.add_apply] at this
      simp only [Pi.sub_apply, ← h]
      rw [this, smul_add, smul_sub]
      by_cases hξ : ξ ∈ outerSet n
      · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
        abel
      · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ, smul_zero]
        abel
    rw [eLpNorm_congr_ae e]
    have hu : ∀ ξ, 2 * R ≤ ‖ξ‖ → (m - f₁) ξ = 0 := by
      intro ξ hξ
      simp only [Pi.sub_apply, hmR ξ hξ, hf₁supp ξ (Or.inr (by linarith)), sub_zero]
    calc eLpNorm ((fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • (m - f₁) ξ) -
          (outerSet n).indicator (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • f ξ)) 2 volume
        ≤ eLpNorm (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • (m - f₁) ξ) 2 volume +
          eLpNorm ((outerSet n).indicator
            (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • f ξ)) 2 volume :=
          eLpNorm_sub_le
            ((continuous_weight hα).aestronglyMeasurable.smul
              (hmc.sub hf₁2.aestronglyMeasurable))
            (hl2.aestronglyMeasurable.indicator hmeas) (by norm_num)
      _ < ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
          have hA : eLpNorm (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • (m - f₁) ξ) 2 volume ≤
              ENNReal.ofReal (ε / 2) := by
            calc eLpNorm (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • (m - f₁) ξ) 2 volume
                ≤ ENNReal.ofReal C * eLpNorm (m - f₁) 2 volume :=
                  eLpNorm_weight_le (by positivity : (0 : ℝ) ≤ 2 * R) hα hu
              _ ≤ ENNReal.ofReal C * ENNReal.ofReal δ := by gcongr
              _ ≤ ENNReal.ofReal (ε / 2) := hδC
          exact ENNReal.add_lt_add_of_le_of_lt (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA) hA hn2
      _ = ENNReal.ofReal ε := hsum

theorem fracNiceGraphDense (α : ℝ) (hα : 1 < α) (hα2 : α < 3 / 2) (h2 : NiceEmbedSymbol)
    (h3 : ∀ m, IsNiceSymbol m → fractionalPowerAt α (niceField m) =
      niceField (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ)) : FracNiceGraphDense α := by
  intro χ ψ hχψ ε hε
  obtain ⟨m, hm, e1, e2⟩ := symbolDense α (by linarith) χ ψ hχψ ε hε
  set n : Space → CSpace := fun ξ => ((2 * π * ‖ξ‖) ^ (-1 : ℝ) : ℝ) • m ξ with hndef
  have hn : IsNiceSymbol n := nice_weight hm (-1)
  have hwn : IsNiceSymbol (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • n ξ) := nice_weight hn (2 * α)
  obtain ⟨r, hr, h0⟩ := hm.2.2.1
  have hback : ∀ ξ, (2 * π * ‖ξ‖) • n ξ = m ξ := by
    intro ξ
    rcases eq_or_ne ξ 0 with rfl | hξ
    · simp [hndef, h0 0 (by simpa using hr)]
    · have hp : 2 * π * ‖ξ‖ ≠ 0 := mul_ne_zero (by positivity) (norm_ne_zero_iff.2 hξ)
      simp only [hndef, smul_smul, Real.rpow_neg_one, mul_inv_cancel₀ hp, one_smul]
  refine ⟨niceField n, ⟨n, hn, rfl⟩, ?_, ?_⟩
  · have hae := h2 n hn
    change ‖(embedX (niceField n) : L2C) - (χ : L2C)‖ < ε
    rw [Lp.norm_def, eLpNorm_congr_ae (g := fun ξ => m ξ - (χ : L2C) ξ) ?_]
    · exact e1
    filter_upwards [Lp.coeFn_sub (embedX (niceField n) : L2C) (χ : L2C), hae] with ξ h h'
    rw [h, Pi.sub_apply, h', hback]
  · rw [h3 n hn]
    have hae := h2 _ hwn
    change ‖(embedX (niceField (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • n ξ)) : L2C) -
      (ψ : L2C)‖ < ε
    rw [Lp.norm_def, eLpNorm_congr_ae
      (g := fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • m ξ - (ψ : L2C) ξ) ?_]
    · exact e2
    filter_upwards [Lp.coeFn_sub (embedX (niceField
      (fun ξ => ((2 * π * ‖ξ‖) ^ (2 * α) : ℝ) • n ξ)) : L2C) (ψ : L2C), hae] with ξ h h'
    rw [h, Pi.sub_apply, h', smul_comm, hback]

end Breakdown.Freq
