import Breakdown.FracCell.AdmissiblePotential
import Breakdown.FracCell.FormulaDataDefs
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

open MeasureTheory Filter Topology
open scoped Convolution ContDiff

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace MeshGaugeLinearPotential

open SteadyCert

private theorem loc_int {q : Space → ℝ} (hm : AEStronglyMeasurable q volume)
    (h2 : IsLocalSquareIntegrable (fun y => q y ^ 2)) : LocallyIntegrable q volume := by
  rw [locallyIntegrable_iff]
  intro K hK
  have : IsFiniteMeasure (volume.restrict K) := ⟨by rw [Measure.restrict_apply_univ]; exact hK.measure_lt_top⟩
  have hL : MemLp q 2 (volume.restrict K) := (memLp_two_iff_integrable_sq hm.restrict).mpr (h2 K hK)
  exact hL.integrable one_le_two

private theorem test_int {q : Space → ℝ} (hq : LocallyIntegrable q volume) (φ : Space → ℝ) (hφ : IsTestScalar φ)
    (j : Fin 3) : Integrable (fun y => fderiv ℝ φ y (unitVector j) * q y) := by
  have hc : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.2.fderiv ℝ).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
  simpa [smul_eq_mul] using hq.integrable_smul_left_of_hasCompactSupport hc hs

private theorem clm_zero (D : Space →L[ℝ] ℝ) (h : ∀ j : Fin 3, D (unitVector j) = 0) : D = 0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.ext
  intro j
  simpa [unitVector] using h j

private theorem conv_deriv_zero (h : Space → ℝ) (hloc : LocallyIntegrable h volume)
    (hz : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3, ∫ y, fderiv ℝ φ y (unitVector j) * h y = 0)
    (ψ : Space → ℝ) (hψ : IsTestScalar ψ) (x : Space) :
    HasFDerivAt (h ⋆[(ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip, volume] ψ)
      (0 : Space →L[ℝ] ℝ) x := by
  have h1 : ContDiff ℝ 1 ψ := hψ.1.of_le (by exact_mod_cast le_top)
  have hd := hψ.2.hasFDerivAt_convolution_right
    ((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip) hloc h1 x
  suffices hz' : (h ⋆[((ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip).precompR Space, volume]
      fderiv ℝ ψ) x = 0 by
    rw [hz'] at hd
    exact hd
  apply clm_zero
  intro j
  rw [convolution_precompR_apply _ hloc (hψ.2.fderiv ℝ) (h1.continuous_fderiv one_ne_zero) x (unitVector j),
    convolution_def]
  simp only [ContinuousLinearMap.flip_apply, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hχ : IsTestScalar (fun y => ψ (x - y)) := by
    refine ⟨hψ.1.comp (contDiff_const.sub contDiff_id), ?_⟩
    exact hψ.2.comp_homeomorph (Homeomorph.subLeft x)
  have hder : ∀ y, fderiv ℝ (fun y => ψ (x - y)) y (unitVector j) = -(fderiv ℝ ψ (x - y) (unitVector j)) := by
    intro y
    have hψd : DifferentiableAt ℝ ψ (x - y) := (h1.differentiable one_ne_zero).differentiableAt
    have : HasFDerivAt (fun y => ψ (x - y)) ((fderiv ℝ ψ (x - y)).comp (0 - ContinuousLinearMap.id ℝ Space)) y :=
      hψd.hasFDerivAt.comp y ((hasFDerivAt_const x y).sub (hasFDerivAt_id y))
    rw [this.fderiv]
    simp
  have := hz _ hχ j
  simp only [hder, neg_mul, integral_neg, neg_eq_zero] at this
  rw [← this]

theorem const_of_zero_grad (h : Space → ℝ) (hloc : LocallyIntegrable h volume)
    (hz : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3, ∫ y, fderiv ℝ φ y (unitVector j) * h y = 0) :
    ∃ C : ℝ, h =ᵐ[volume] fun _ => C := by
  let φ : ℕ → ContDiffBump (0 : Space) := fun n =>
    ⟨1 / ((n : ℝ) + 1), 2 / ((n : ℝ) + 1), by positivity, by
      apply div_lt_div_of_pos_right (by norm_num) (by positivity)⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
    simp only [mul_zero] at this
    refine this.congr (fun n => ?_)
    simp [φ]
    ring
  have h'φ : ∀ᶠ n in atTop, (φ n).rOut ≤ 2 * (φ n).rIn := Eventually.of_forall fun n => by
    simp [φ]
    ring_nf
    rfl
  have hae := ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (μ := volume) hφ h'φ hloc
  have hconst : ∀ n (x y : Space), ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x =
      ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) y := by
    intro n x y
    rw [← convolution_flip]
    have hψ : IsTestScalar ((φ n).normed volume) := ⟨(φ n).contDiff_normed, (φ n).hasCompactSupport_normed⟩
    have hD := conv_deriv_zero h hloc hz _ hψ
    exact is_const_of_fderiv_eq_zero (fun z => (hD z).differentiableAt) (fun z => (hD z).fderiv) x y
  obtain ⟨x0, hx0⟩ := hae.exists
  refine ⟨h x0, ?_⟩
  filter_upwards [hae] with x hx
  have e : (fun n => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x) =
      fun n => ((φ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] h) x0 :=
    funext fun n => hconst n x x0
  rw [e] at hx
  exact tendsto_nhds_unique hx hx0

theorem potentialOf_spec (Q : Space → Space) (hQ : IsGradientField Q) : IsPotentialOf Q (potentialOf Q) := by
  obtain ⟨q, hq⟩ := admissiblePotential_holds Q hQ
  have hex : ∃ q, IsPotentialOf Q q := ⟨q, hq⟩
  unfold potentialOf
  rw [dif_pos hex]
  exact hex.choose_spec

private theorem pot_zero_grad {Q : Space → Space} {q1 q2 : Space → ℝ} (h1 : IsPotentialOf Q q1)
    (h2 : IsPotentialOf Q q2) : ∃ C : ℝ, q1 =ᵐ[volume] fun y => q2 y + C := by
  obtain ⟨m1, s1, i1⟩ := h1
  obtain ⟨m2, s2, i2⟩ := h2
  have l1 := loc_int m1 s1
  have l2 := loc_int m2 s2
  obtain ⟨C, hC⟩ := const_of_zero_grad (fun y => q1 y - q2 y) (l1.sub l2) (fun φ hφ j => by
    have e : (fun y => fderiv ℝ φ y (unitVector j) * (q1 y - q2 y)) =
        fun y => fderiv ℝ φ y (unitVector j) * q1 y - fderiv ℝ φ y (unitVector j) * q2 y := by
      funext y; ring
    rw [e, integral_sub (test_int l1 φ hφ j) (test_int l2 φ hφ j), i1 φ hφ j, i2 φ hφ j, sub_self])
  refine ⟨C, ?_⟩
  filter_upwards [hC] with y hy
  have hy' : q1 y - q2 y = C := hy
  linarith

private theorem pot_combo {Q Q' : Space → Space} (hQ : IsGradientField Q) (hQ' : IsGradientField Q')
    {q q' : Space → ℝ} (h1 : IsPotentialOf Q q) (h2 : IsPotentialOf Q' q') (a b : ℝ) :
    IsPotentialOf (a • Q + b • Q') (fun y => a * q y + b * q' y) := by
  obtain ⟨m1, s1, i1⟩ := h1
  obtain ⟨m2, s2, i2⟩ := h2
  obtain ⟨_, _, hQ2, hQm, _⟩ := hQ
  obtain ⟨_, _, hQ2', hQm', _⟩ := hQ'
  have l1 := loc_int m1 s1
  have l2 := loc_int m2 s2
  have m3 : AEStronglyMeasurable (fun y => a * q y + b * q' y) volume :=
    (m1.const_mul a).add (m2.const_mul b)
  refine ⟨m3, ?_, ?_⟩
  · intro K hK
    have hb : IntegrableOn (fun y => 2 * a ^ 2 * q y ^ 2 + 2 * b ^ 2 * q' y ^ 2) K :=
      ((s1 K hK).const_mul _).add ((s2 K hK).const_mul _)
    refine hb.mono' (m3.pow 2).restrict (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    nlinarith [sq_nonneg (a * q y - b * q' y)]
  · intro φ hφ j
    have e : (fun y => fderiv ℝ φ y (unitVector j) * (a * q y + b * q' y)) =
        fun y => a * (fderiv ℝ φ y (unitVector j) * q y) + b * (fderiv ℝ φ y (unitVector j) * q' y) := by
      funext y; ring
    have e2 : (fun y => φ y * inner ℝ ((a • Q + b • Q') y) (unitVector j)) =
        fun y => a * (φ y * inner ℝ (Q y) (unitVector j)) + b * (φ y * inner ℝ (Q' y) (unitVector j)) := by
      funext y
      simp only [Pi.add_apply, Pi.smul_apply, inner_add_left, real_inner_smul_left]
      ring
    have t1 := AdmissiblePotentialInternal.test_mul_integrable Q j hQ2 hQm φ hφ
    have t2 := AdmissiblePotentialInternal.test_mul_integrable Q' j hQ2' hQm' φ hφ
    rw [e, e2, integral_add ((test_int l1 φ hφ j).const_mul a) ((test_int l2 φ hφ j).const_mul b),
      integral_add (t1.const_mul a) (t2.const_mul b), integral_const_mul, integral_const_mul,
      integral_const_mul, integral_const_mul, i1 φ hφ j, i2 φ hφ j]
    ring

theorem potential_affine (Q Q' : Space → Space) (hQ : IsGradientField Q) (hQ' : IsGradientField Q') (a b : ℝ) :
    ∃ C : ℝ, potentialOf (a • Q + b • Q') =ᵐ[volume] fun y => a * potentialOf Q y + b * potentialOf Q' y + C := by
  have hc := pot_combo hQ hQ' (potentialOf_spec Q hQ) (potentialOf_spec Q' hQ') a b
  have hex : ∃ q, IsPotentialOf (a • Q + b • Q') q := ⟨_, hc⟩
  have h3 : IsPotentialOf (a • Q + b • Q') (potentialOf (a • Q + b • Q')) := by
    unfold potentialOf
    rw [dif_pos hex]
    exact hex.choose_spec
  exact pot_zero_grad h3 hc

end MeshGaugeLinearPotential

end CellFormula

end CellCert

end Breakdown
