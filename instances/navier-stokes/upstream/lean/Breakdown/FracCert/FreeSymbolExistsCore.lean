import Breakdown.FracCert.FreeSymbolExistsExp
import Breakdown.FracCert.FreeSymbolExistsClass
import Breakdown.FracCert.FreeSymbolExistsBasic

open scoped ContDiff ENNReal
open MeasureTheory Real

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeSymbolCoreInternal

open FreeSymbolSmoothInternal FreeSymbolEquationInternal

theorem flow_norm (α a : ℝ) (ζ : Space) (t : ℝ) : ‖flowPt α a ζ t‖ = Real.exp (-t / (2 * α)) * ‖ζ‖ := by
  rw [flowPt, norm_smul, rot_norm', Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem kernel_nonpos {α a r : ℝ} (hα : 0 < α) {s : Space → Freq.CSpace} (hr0 : ∀ ξ : Space, ‖ξ‖ < r → s ξ = 0)
    {ζ : Space} (hζ : ‖ζ‖ < r) {σ : ℝ} (hσ : σ ≤ 0) : kernel α a s ζ σ = 0 := by
  have hle : Real.exp (σ / (2 * α)) ≤ 1 := Real.exp_le_one_iff.2 (div_nonpos_of_nonpos_of_nonneg hσ (by linarith))
  have hn : ‖Real.exp (σ / (2 * α)) • axialRotationFormula (-(a * σ)) ζ‖ < r := by
    rw [norm_smul, rot_norm', Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc Real.exp (σ / (2 * α)) * ‖ζ‖ ≤ 1 * ‖ζ‖ := mul_le_mul_of_nonneg_right hle (norm_nonneg _)
      _ < r := by rw [one_mul]; exact hζ
  unfold kernel damped
  rw [hr0 _ hn, smul_zero, FreeSymbolExistsInternal.rotC_zero, smul_zero]

theorem core_homog {α a : ℝ} (hα1 : 1 < α) {s : Space → Freq.CSpace} (hs : Freq.IsNiceSymbol s) :
    ∃ r : ℝ, 0 < r ∧ ∀ ζ : Space, ζ ≠ 0 → ‖ζ‖ < r → ∀ t : ℝ, 0 ≤ t →
      hbase α a s (flowPt α a ζ t) = Real.exp (-((1 - 2 / α) * t)) • axialRotationC (a * t) (hbase α a s ζ) := by
  have hα : 0 < α := by linarith
  obtain ⟨r, hr, hr0⟩ := hs.2.2.1
  obtain ⟨R, hR, hint⟩ := core_eq_interval (a := a) hα hs
  refine ⟨r, hr, fun ζ hζ0 hζ t ht => ?_⟩
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 hζ0
  have hfn : 0 < ‖flowPt α a ζ t‖ := by rw [flow_norm]; positivity
  have hfle : ‖flowPt α a ζ t‖ ≤ ‖ζ‖ := by
    rw [flow_norm]
    have : Real.exp (-t / (2 * α)) ≤ 1 := Real.exp_le_one_iff.2 (by
      apply div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    nlinarith
  set ε : ℝ := ‖flowPt α a ζ t‖ / 2 with hε
  have hεpos : 0 < ε := by positivity
  set T : ℝ := 2 * α * (R / ε) + t with hT
  have hKc : Continuous (kernel α a s ζ) := kernel_cont α a hs ζ
  rw [hint _ ε T hεpos (by linarith) (by linarith)]
  simp_rw [kernel_shift]
  rw [intervalIntegral.integral_smul]
  set L : Freq.CSpace →L[ℝ] Freq.CSpace := Real.cos (a * t) • ContinuousLinearMap.id ℝ Freq.CSpace +
    Real.sin (a * t) • turnCLC + (1 - Real.cos (a * t)) • axisCLC with hLdef
  have hL : ∀ z, axialRotationC (a * t) z = L z := by
    intro z
    rw [rotC_decomp]
    simp [L]
  simp_rw [hL]
  have hii : IntervalIntegrable (fun x => kernel α a s ζ (x - t)) volume 0 T :=
    (hKc.comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hz : ∫ σ in (-t)..0, kernel α a s ζ σ = 0 := by
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : Freq.CSpace)) ?_]
    · simp
    · intro σ hσ
      rw [Set.uIcc_of_le (by linarith)] at hσ
      exact kernel_nonpos hα hr0 hζ hσ.2
  rw [L.intervalIntegral_comp_comm hii, intervalIntegral.integral_comp_sub_right (kernel α a s ζ) t,
    ← intervalIntegral.integral_add_adjacent_intervals (hKc.intervalIntegrable (0 - t) 0)
      (hKc.intervalIntegrable 0 (T - t)),
    ← hint ζ ε (T - t) hεpos (by linarith) (by linarith), zero_sub, hz, zero_add]

theorem rotC_bound (θ : ℝ) (z : Freq.CSpace) :
    ‖axialRotationC θ z‖ ≤ (1 + ‖turnCLC‖ + 2 * ‖axisCLC‖) * ‖z‖ := by
  rw [rotC_decomp]
  have h1 : ‖Real.cos θ • z‖ ≤ ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one θ)
  have h2 : ‖Real.sin θ • turnCLC z‖ ≤ ‖turnCLC‖ * ‖z‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    exact le_trans (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one θ)) (turnCLC.le_opNorm z)
  have h3 : ‖(1 - Real.cos θ) • axisCLC z‖ ≤ 2 * (‖axisCLC‖ * ‖z‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    have : |1 - Real.cos θ| ≤ 2 := by
      rw [abs_le]
      constructor <;> linarith [Real.neg_one_le_cos θ, Real.cos_le_one θ]
    exact mul_le_mul this (axisCLC.le_opNorm z) (norm_nonneg _) (by norm_num)
  calc ‖Real.cos θ • z + Real.sin θ • turnCLC z + (1 - Real.cos θ) • axisCLC z‖
      ≤ ‖Real.cos θ • z‖ + ‖Real.sin θ • turnCLC z‖ + ‖(1 - Real.cos θ) • axisCLC z‖ := norm_add₃_le
    _ ≤ ‖z‖ + ‖turnCLC‖ * ‖z‖ + 2 * (‖axisCLC‖ * ‖z‖) := by linarith
    _ = (1 + ‖turnCLC‖ + 2 * ‖axisCLC‖) * ‖z‖ := by ring

theorem core_bound : FreeCoreBoundStatement := by
  intro α hα1 hα2 a s hs j
  have hα : 0 < α := by linarith
  obtain ⟨r, hr, hhom⟩ := core_homog (a := a) hα1 hs
  set ρ1 : ℝ := r / 2 with hρ1
  have hρ1pos : 0 < ρ1 := by positivity
  set U : Set Space := {η : Space | η ≠ 0} with hU
  have hUo : IsOpen U := isOpen_ne
  have hCU : ContDiffOn ℝ ∞ (hbase α a s) U := fun η hη => (core_contDiffAt hα hs hη).contDiffWithinAt
  have hcont : ContinuousOn (iteratedFDeriv ℝ j (hbase α a s)) U := by
    have h := hCU.continuousOn_iteratedFDerivWithin (m := j) (by exact_mod_cast le_top) hUo.uniqueDiffOn
    exact h.congr fun ξ hξ => (iteratedFDerivWithin_of_isOpen j hUo hξ).symm
  have hSU : Metric.sphere (0 : Space) ρ1 ⊆ U := fun ξ hξ h0 => by
    rw [mem_sphere_zero_iff_norm, h0, norm_zero] at hξ
    linarith
  obtain ⟨M, hM⟩ := (isCompact_sphere (0 : Space) ρ1).exists_bound_of_continuousOn (hcont.mono hSU)
  set Kr : ℝ := 1 + ‖turnCLC‖ + 2 * ‖axisCLC‖ with hKr
  have hKr0 : 0 ≤ Kr := by positivity
  set e : ℝ := 2 * α - 4 - (j : ℝ) with he
  refine ⟨ρ1, hρ1pos, Kr * max M 0 * ρ1 ^ (-e), fun η hη hηρ => ?_⟩
  have hn : 0 < ‖η‖ := norm_pos_iff.2 hη
  set μ : ℝ := ‖η‖ / ρ1 with hμ
  have hμpos : 0 < μ := by positivity
  have hμ1 : μ ≤ 1 := by rw [hμ, div_le_one hρ1pos]; exact hηρ.le
  set t : ℝ := -(2 * α * Real.log μ) with ht
  have ht0 : 0 ≤ t := by
    have : Real.log μ ≤ 0 := Real.log_nonpos hμpos.le hμ1
    nlinarith
  set θ : ℝ := a * t with hθ
  have hexp : Real.exp (-t / (2 * α)) = μ := by
    rw [show -t / (2 * α) = Real.log μ by rw [ht]; field_simp]
    exact Real.exp_log hμpos
  set P : Space ≃L[ℝ] Space := (FreeSymbolClassInternal.rotIso (-θ)).toContinuousLinearEquiv.trans
    (LinearEquiv.smulOfNeZero ℝ Space μ⁻¹ (inv_ne_zero hμpos.ne')).toContinuousLinearEquiv with hP
  have hPa : ∀ x, P x = μ⁻¹ • axialRotationFormula (-θ) x := fun x => rfl
  have hPn : ∀ x, ‖P x‖ = μ⁻¹ * ‖x‖ := fun x => by
    rw [hPa, norm_smul, rot_norm', Real.norm_eq_abs, abs_of_pos (inv_pos.2 hμpos)]
  have hflow : ∀ x, flowPt α a (P x) t = x := fun x => by
    rw [flowPt, hexp, hPa, rot_smul', rot_rot, smul_smul, mul_inv_cancel₀ hμpos.ne', one_smul,
      show a * t + -θ = 0 by rw [hθ]; ring, FreeSymbolEquationInternal.rot_zero]
  set Rl : Freq.CSpace ≃L[ℝ] Freq.CSpace := (FreeSymbolClassInternal.rotCLE θ).restrictScalars ℝ with hRl
  have hRla : ∀ z, Rl z = axialRotationC θ z := fun z => rfl
  set g : Space → Freq.CSpace := fun x => Real.exp (-((1 - 2 / α) * t)) • (Rl ∘ (hbase α a s ∘ P)) x with hg
  have hopen : IsOpen {x : Space | ‖P x‖ < r ∧ P x ≠ 0} :=
    (isOpen_lt (continuous_norm.comp P.continuous) continuous_const).inter (isOpen_ne_fun P.continuous continuous_const)
  have hPη : ‖P η‖ = ρ1 := by
    rw [hPn, hμ]
    field_simp
  have hmem : η ∈ {x : Space | ‖P x‖ < r ∧ P x ≠ 0} := by
    refine ⟨by rw [hPη]; linarith, fun h => ?_⟩
    rw [h, norm_zero] at hPη
    linarith
  have hev : hbase α a s =ᶠ[nhds η] g := by
    refine Filter.eventually_of_mem (hopen.mem_nhds hmem) fun x hx => ?_
    have h := hhom (P x) hx.2 hx.1 t ht0
    rw [hflow] at h
    rw [h]
    rfl
  have hat : ContDiffAt ℝ j (Rl ∘ (hbase α a s ∘ P)) η := by
    have h1 : ContDiffAt ℝ ∞ (hbase α a s) (P η) := core_contDiffAt hα hs hmem.2
    exact (Rl.contDiff.contDiffAt.comp η (h1.comp η P.contDiff.contDiffAt)).of_le (by exact_mod_cast le_top)
  have hcomp : iteratedFDeriv ℝ j (hbase α a s ∘ P) η =
      (iteratedFDeriv ℝ j (hbase α a s) (P η)).compContinuousLinearMap fun _ => (P : Space →L[ℝ] Space) := by
    have h := P.iteratedFDerivWithin_comp_right (hbase α a s) uniqueDiffOn_univ (Set.mem_univ (P η)) j
    simpa [iteratedFDerivWithin_univ] using h
  rw [(hev.iteratedFDeriv ℝ j).eq_of_nhds, hg, iteratedFDeriv_const_smul_apply' hat,
    Rl.iteratedFDeriv_comp_left, hcomp, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have hRn : ‖(Rl : Freq.CSpace →L[ℝ] Freq.CSpace)‖ ≤ Kr :=
    ContinuousLinearMap.opNorm_le_bound _ hKr0 fun z => by
      change ‖Rl z‖ ≤ _
      rw [hRla]
      exact rotC_bound θ z
  have hPo : ‖(P : Space →L[ℝ] Space)‖ ≤ μ⁻¹ :=
    ContinuousLinearMap.opNorm_le_bound _ (inv_nonneg.2 hμpos.le) fun x => by
      change ‖P x‖ ≤ _
      rw [hPn]
  have hMb : ‖iteratedFDeriv ℝ j (hbase α a s) (P η)‖ ≤ max M 0 :=
    le_trans (hM _ (by rw [mem_sphere_zero_iff_norm]; exact hPη)) (le_max_left _ _)
  have hb1 := (Rl : Freq.CSpace →L[ℝ] Freq.CSpace).norm_compContinuousMultilinearMap_le
    ((iteratedFDeriv ℝ j (hbase α a s) (P η)).compContinuousLinearMap fun _ => (P : Space →L[ℝ] Space))
  have hb2 := (iteratedFDeriv ℝ j (hbase α a s) (P η)).norm_compContinuousLinearMap_le
    fun _ => (P : Space →L[ℝ] Space)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hb2
  have hpow : ‖(P : Space →L[ℝ] Space)‖ ^ j ≤ μ⁻¹ ^ j := pow_le_pow_left₀ (norm_nonneg _) hPo j
  have hE : Real.exp (-((1 - 2 / α) * t)) = μ ^ (2 * α - 4) := by
    rw [Real.rpow_def_of_pos hμpos, ht]
    congr 1
    field_simp
    ring
  have hfin : μ ^ (2 * α - 4) * μ⁻¹ ^ j = ‖η‖ ^ e * ρ1 ^ (-e) := by
    rw [← Real.rpow_natCast, Real.inv_rpow hμpos.le, ← Real.rpow_neg hμpos.le, ← Real.rpow_add hμpos, hμ,
      Real.div_rpow hn.le hρ1pos.le, Real.rpow_neg hρ1pos.le, div_eq_mul_inv]
    congr 2
  have hX : ‖(Rl : Freq.CSpace →L[ℝ] Freq.CSpace).compContinuousMultilinearMap
      ((iteratedFDeriv ℝ j (hbase α a s) (P η)).compContinuousLinearMap fun _ => (P : Space →L[ℝ] Space))‖ ≤
      Kr * (max M 0 * μ⁻¹ ^ j) := by
    refine le_trans hb1 (mul_le_mul hRn (le_trans hb2 ?_) (norm_nonneg _) hKr0)
    exact mul_le_mul hMb hpow (pow_nonneg (norm_nonneg _) _) (le_max_right _ _)
  calc Real.exp (-((1 - 2 / α) * t)) * ‖(Rl : Freq.CSpace →L[ℝ] Freq.CSpace).compContinuousMultilinearMap
        ((iteratedFDeriv ℝ j (hbase α a s) (P η)).compContinuousLinearMap fun _ => (P : Space →L[ℝ] Space))‖
      ≤ Real.exp (-((1 - 2 / α) * t)) * (Kr * (max M 0 * μ⁻¹ ^ j)) :=
        mul_le_mul_of_nonneg_left hX (Real.exp_pos _).le
    _ = Kr * max M 0 * (μ ^ (2 * α - 4) * μ⁻¹ ^ j) := by rw [hE]; ring
    _ = Kr * max M 0 * ρ1 ^ (-e) * ‖η‖ ^ e := by rw [hfin]; ring

end FreeSymbolCoreInternal

theorem freeCoreBound : FreeCoreBoundStatement := FreeSymbolCoreInternal.core_bound

end SteadyCert

end Breakdown
