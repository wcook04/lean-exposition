import Breakdown.Weak.StatementsSlice
import Breakdown.FreqTr.WeakInX

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem sq_norm_L2R_eq_integral (p : L2R) :
    ‖p‖ ^ 2 = ∫ y, ‖(p : Space → Space) y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  congr 1
  funext y
  exact real_inner_self_eq_norm_sq _

private theorem norm_unitVector_eq (j : Fin 3) : ‖unitVector j‖ = 1 := by
  simp [unitVector]

private theorem sq_norm_embed_eq_sum_partial {ψ : Space → Space} (hψ : IsTestField ψ) :
    ‖embedX ψ‖ ^ 2 = ∑ j : Fin 3, ‖partialX j (embedX ψ)‖ ^ 2 := by
  have hd := isDecayField_of_isTestField hψ
  have hp : ∀ j, (partialX j (embedX ψ) : Space → Space) =ᵐ[volume] partialField ψ j :=
    fun j => partial_holds.1 ψ hd j
  have hsq : ∀ j : Fin 3, (fun y => ‖(partialX j (embedX ψ) : Space → Space) y‖ ^ 2) =ᵐ[volume]
      fun y => ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2 := by
    intro j
    filter_upwards [hp j] with y hy
    rw [hy]
    rfl
  have hint : ∀ j : Fin 3, Integrable (fun y => ‖fderiv ℝ ψ y (unitVector j)‖ ^ 2) volume :=
    fun j => ((Lp.memLp (partialX j (embedX ψ))).integrable_norm_pow two_ne_zero).congr (hsq j)
  rw [embedNormLinear_holds.1 ψ hd, integral_finsetSum _ (fun j _ => hint j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sq_norm_L2R_eq_integral, integral_congr_ae (hsq j)]

private theorem sq_norm_eq_sum_partial (v : X) :
    ‖v‖ ^ 2 = ∑ j : Fin 3, ‖partialX j v‖ ^ 2 := by
  have hL : Continuous (fun z : X => ‖z‖ ^ 2) := continuous_norm.pow 2
  have hR : Continuous (fun z : X => ∑ j : Fin 3, ‖partialX j z‖ ^ 2) :=
    continuous_finsetSum _ fun j _ => ((partialX j).continuous.norm).pow 2
  have hsub : (testSpan : Set X) ⊆ {z : X | ‖z‖ ^ 2 = ∑ j : Fin 3, ‖partialX j z‖ ^ 2} := by
    intro z hz
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds z hz
    exact sq_norm_embed_eq_sum_partial hψ
  have hcl := closure_minimal hsub (isClosed_eq hL hR)
  rw [testDense_holds.2.closure_eq] at hcl
  exact hcl (mem_univ v)

private theorem sq_norm_partial_le {g : Space → (Space →L[ℝ] Space)} {C : ℝ}
    (hC : ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) ≤ ENNReal.ofReal C) (x : X) (j : Fin 3)
    (hx : (partialX j x : Space → Space) =ᵐ[volume] gradComponent g j) :
    ‖partialX j x‖ ^ 2 ≤ max C 0 := by
  have hm : AEStronglyMeasurable (fun y => ‖(partialX j x : Space → Space) y‖ ^ 2) volume :=
    (Lp.aestronglyMeasurable (partialX j x)).norm.pow 2
  rw [sq_norm_L2R_eq_integral, integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun y => sq_nonneg _) hm, ← ENNReal.toReal_ofReal' (r := C)]
  apply ENNReal.toReal_mono ENNReal.ofReal_ne_top
  calc ∫⁻ y, ENNReal.ofReal (‖(partialX j x : Space → Space) y‖ ^ 2)
      = ∫⁻ y, ENNReal.ofReal (‖g y (unitVector j)‖ ^ 2) := by
        apply lintegral_congr_ae
        filter_upwards [hx] with y hy
        rw [hy]
        rfl
    _ ≤ ∫⁻ y, ENNReal.ofReal (‖g y‖ ^ 2) := by
        apply lintegral_mono
        intro y
        apply ENNReal.ofReal_le_ofReal
        have h1 : ‖g y (unitVector j)‖ ≤ ‖g y‖ := by
          calc ‖g y (unitVector j)‖ ≤ ‖g y‖ * ‖unitVector j‖ := (g y).le_opNorm _
            _ = ‖g y‖ := by rw [norm_unitVector_eq, mul_one]
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ ENNReal.ofReal C := hC

private theorem memLp_six_of_bound {f : Space → Space} {C : ℝ} (hf : LocallyIntegrable f volume)
    (hC : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) ≤ ENNReal.ofReal C) : MemLp f 6 volume := by
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top (by norm_num) (by norm_num)]
  have he : ∀ y, ‖f y‖ₑ ^ (6 : ℝ≥0∞).toReal = ENNReal.ofReal (‖f y‖ ^ 6) := by
    intro y
    rw [← ofReal_norm, ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num)]
    congr 1
    norm_num
  simp_rw [he]
  exact lt_of_le_of_lt hC ENNReal.ofReal_lt_top

theorem sliceEmbedding_holds : SliceEmbedding := by
  intro _ hVWG hZG hGF f g C hS
  obtain ⟨x, hx⟩ := hGF f g C hS
  obtain ⟨hfl, -, hweak⟩ := hS.grad
  have hf6 : MemLp f 6 volume := memLp_six_of_bound hfl hS.six
  have hv6 : MemLp (velocity x : Space → Space) 6 volume := Lp.memLp (velocity x)
  have hvl : LocallyIntegrable (velocity x : Space → Space) volume :=
    hv6.locallyIntegrable (by norm_num)
  refine ⟨x, ?_, hx, ?_⟩
  · have hzero := hZG (fun y => (velocity x : Space → Space) y - f y) (hv6.sub hf6) (by
      intro φ hφ j
      have hc : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
        (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
      have hs : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
        hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)
      have i1 := hvl.integrable_smul_left_of_hasCompactSupport hc hs
      have i2 := hfl.integrable_smul_left_of_hasCompactSupport hc hs
      simp_rw [smul_sub]
      rw [integral_sub i1 i2]
      have e1 := hVWG x φ hφ j
      have e2 : ∫ y, φ y • (partialX j x : Space → Space) y =
          ∫ y, φ y • g y (unitVector j) := by
        apply integral_congr_ae
        filter_upwards [hx j] with y hy
        rw [hy]
        rfl
      have e3 := hweak φ hφ j
      rw [sub_eq_zero]
      exact neg_inj.1 (e1.symm.trans (e2.trans e3)))
    filter_upwards [hzero] with y hy
    exact sub_eq_zero.1 hy
  · rw [sq_norm_eq_sum_partial]
    calc ∑ j : Fin 3, ‖partialX j x‖ ^ 2 ≤ ∑ _j : Fin 3, max C 0 :=
          Finset.sum_le_sum fun j _ => sq_norm_partial_le hS.two x j (hx j)
      _ = 3 * max C 0 := by simp

end Breakdown.WeakProfile
