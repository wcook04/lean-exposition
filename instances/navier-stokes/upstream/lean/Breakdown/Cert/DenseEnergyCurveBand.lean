import Breakdown.Cert.Nodes
import Breakdown.Cert.PeriodIntegral
import Breakdown.FreqTr.Phi
import Breakdown.FreqTr.Dilation
import Breakdown.FreqTr.DilationCont
import Breakdown.FreqTr.Heat
import Breakdown.FreqTr.FieldOp

open MeasureTheory Filter Topology Set

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.DenseEnergyBand

def bandCut (R : ℝ) (ξ : Space) : ℝ := min (max (‖ξ‖ - R) 0) 1

def halfSspCut (R : ℝ) (ξ : Space) : ℝ := 2 * Real.pi * min ‖ξ‖ R

def bandOp (R : ℝ) : Freq.X →L[ℝ] L2C :=
  (fieldOp id (fun ξ => bandCut R ξ • ContinuousLinearMap.id ℝ CSpace)).comp Sig.subtypeL

def bandX (R : ℝ) : Submodule ℝ Freq.X := LinearMap.ker (bandOp R : Freq.X →ₗ[ℝ] L2C)

def halfSspX (R : ℝ) : Freq.X →L[ℝ] Freq.X :=
  restrictX (fieldOp id (fun ξ => halfSspCut R ξ • ContinuousLinearMap.id ℝ CSpace))

def semigroupX (s : ℝ) : Freq.X →L[ℝ] Freq.X :=
  (dilX (Real.exp (-s))).comp (heatX (1 - Real.exp (-s)))

def mildIntegral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : ℝ → E →L[ℝ] E)
    (G : ℝ → E) (P σ : ℝ) : E :=
  ∫ τ in Ioi (0 : ℝ), T τ (G (σ - τ / P))

theorem isClosed_bandX (R : ℝ) : IsClosed (bandX R : Set Freq.X) :=
  ContinuousLinearMap.isClosed_ker (bandOp R)

private theorem bandCut_cont (R : ℝ) : Continuous (bandCut R) := by
  unfold bandCut
  fun_prop

private theorem bandCut_le (R : ℝ) (ξ : Space) : |bandCut R ξ| ≤ 1 := by
  have h0 : 0 ≤ min (max (‖ξ‖ - R) 0) 1 := le_min (le_max_right _ _) zero_le_one
  unfold bandCut
  rw [abs_of_nonneg h0]
  exact min_le_right _ _

private theorem bandCut_ne_zero {R : ℝ} {ξ : Space} (h : R < ‖ξ‖) : bandCut R ξ ≠ 0 :=
  (lt_min (lt_max_of_lt_left (sub_pos.2 h)) one_pos).ne'

private theorem bandCut_eq_zero {R : ℝ} {ξ : Space} (h : ¬ R < ‖ξ‖) : bandCut R ξ = 0 := by
  have h' : ‖ξ‖ - R ≤ 0 := by linarith [not_lt.1 h]
  unfold bandCut
  rw [max_eq_right h', min_eq_left zero_le_one]

theorem mem_bandX_iff (R : ℝ) (y : Freq.X) :
    y ∈ bandX R ↔ ∀ᵐ ξ ∂(volume : Measure Space), R < ‖ξ‖ → (y : L2C) ξ = 0 := by
  have hae := Breakdown.Freq.Internal.Phi.scalarOp_ae fieldOpRealized (bandCut_cont R)
    (bandCut_le R) (y : L2C)
  have e : y ∈ bandX R ↔
      fieldOp id (fun ξ => bandCut R ξ • ContinuousLinearMap.id ℝ CSpace) (y : L2C) = 0 :=
    Iff.rfl
  rw [e, Lp.eq_zero_iff_ae_eq_zero]
  constructor
  · intro h
    filter_upwards [h, hae] with ξ h1 h2 hR
    have h3 : bandCut R ξ • (y : L2C) ξ = 0 := h2.symm.trans h1
    exact (smul_eq_zero.1 h3).resolve_left (bandCut_ne_zero hR)
  · intro h
    filter_upwards [h, hae] with ξ h1 h2
    rw [h2]
    by_cases hR : R < ‖ξ‖
    · rw [h1 hR, smul_zero]
      rfl
    · rw [bandCut_eq_zero hR, zero_smul]
      rfl

private theorem halfSspCut_cont (R : ℝ) : Continuous (halfSspCut R) := by
  unfold halfSspCut
  exact continuous_const.mul (continuous_norm.min continuous_const)

private theorem halfSspCut_le (R : ℝ) (ξ : Space) : |halfSspCut R ξ| ≤ 2 * Real.pi * |R| := by
  unfold halfSspCut
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases le_total R 0 with hR | hR
  · rw [min_eq_right (hR.trans (norm_nonneg ξ))]
  · rw [abs_of_nonneg (le_min (norm_nonneg ξ) hR), abs_of_nonneg hR]
    exact min_le_right _ _

private theorem halfSspCut_neg (R : ℝ) (ξ : Space) : halfSspCut R (-ξ) = halfSspCut R ξ := by
  unfold halfSspCut
  rw [norm_neg]

theorem halfSspX_coe (R : ℝ) (y : Freq.X) :
    (halfSspX R y : L2C) =
      fieldOp id (fun ξ => halfSspCut R ξ • ContinuousLinearMap.id ℝ CSpace) (y : L2C) :=
  restrictX_coe (fun _ hx => Breakdown.Freq.Internal.Phi.scalarOp_mem fieldOpRealized
    (halfSspCut_cont R) (halfSspCut_le R) (halfSspCut_neg R) hx) y

theorem halfSspX_ae (R : ℝ) (y : Freq.X) :
    ((halfSspX R y : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => halfSspCut R ξ • (y : L2C) ξ := by
  rw [halfSspX_coe]
  exact Breakdown.Freq.Internal.Phi.scalarOp_ae fieldOpRealized (halfSspCut_cont R)
    (halfSspCut_le R) (y : L2C)

theorem bandX_mono {R R' : ℝ} (h : R ≤ R') : bandX R ≤ bandX R' := by
  intro y hy
  rw [mem_bandX_iff] at hy ⊢
  filter_upwards [hy] with ξ h1 hR
  exact h1 (lt_of_le_of_lt h hR)

theorem halfSspX_mem_band (R : ℝ) (y : Freq.X) (hy : y ∈ bandX R) : halfSspX R y ∈ bandX R := by
  rw [mem_bandX_iff] at hy ⊢
  filter_upwards [halfSspX_ae R y, hy] with ξ h1 h2 hR
  rw [h1, h2 hR, smul_zero]

theorem isHalfSspOf_of_mem_band (R : ℝ) (y : Freq.X) (hy : y ∈ bandX R) :
    IsHalfSspOf y (halfSspX R y) := by
  rw [mem_bandX_iff] at hy
  filter_upwards [halfSspX_ae R y, hy] with ξ h1 h2
  rw [h1]
  by_cases hR : R < ‖ξ‖
  · rw [h2 hR, smul_zero, smul_zero]
  · have hm : min ‖ξ‖ R = ‖ξ‖ := min_eq_left (not_lt.1 hR)
    simp only [halfSspCut, hm]

theorem inner_halfSspX (R : ℝ) (y z : Freq.X) :
    inner ℝ (halfSspX R y) z = inner ℝ y (halfSspX R z) := by
  change inner ℝ ((halfSspX R y : Freq.X) : L2C) (z : L2C) =
    inner ℝ (y : L2C) ((halfSspX R z : Freq.X) : L2C)
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [halfSspX_ae R y, halfSspX_ae R z] with ξ hy hz
  rw [hy, hz, real_inner_smul_left, real_inner_smul_right]

theorem semigroupX_mem_band (R τ : ℝ) (hτ : 0 ≤ τ) (y : Freq.X) (hy : y ∈ bandX R) :
    semigroupX τ y ∈ bandX R := by
  have hμ : 0 < Real.exp (-τ) := Real.exp_pos _
  have e1 : ((semigroupX τ y : Freq.X) : L2C) =
      dilL2 (Real.exp (-τ)) ((heatX (1 - Real.exp (-τ)) y : Freq.X) : L2C) :=
    Breakdown.Freq.Internal.Dilation.dilX_coe fieldOpRealized hμ _
  have e2 : ((heatX (1 - Real.exp (-τ)) y : Freq.X) : L2C) = heatL2 (1 - Real.exp (-τ)) y :=
    Breakdown.Freq.Internal.Heat.heatX_coe fieldOpRealized _ y
  rw [mem_bandX_iff] at hy ⊢
  have hf : ∀ᵐ η ∂(volume : Measure Space), R < ‖η‖ →
      ((heatX (1 - Real.exp (-τ)) y : Freq.X) : L2C) η = 0 := by
    rw [e2]
    filter_upwards [Breakdown.Freq.Internal.Heat.heat_ae fieldOpRealized (1 - Real.exp (-τ))
      (y : L2C), hy] with η a b hR
    rw [a, b hR, smul_zero]
  have hs : 0 < Real.sqrt (Real.exp (-τ)) := Real.sqrt_pos.2 hμ
  have hs1 : Real.sqrt (Real.exp (-τ)) ≤ 1 :=
    Real.sqrt_le_one.2 (Real.exp_le_one_iff.2 (neg_nonpos.2 hτ))
  have hc : (Real.sqrt (Real.exp (-τ)))⁻¹ ≠ 0 := (inv_pos.2 hs).ne'
  have hc1 : 1 ≤ (Real.sqrt (Real.exp (-τ)))⁻¹ := (one_le_inv₀ hs).2 hs1
  have h3 : ∀ᵐ ξ ∂(volume : Measure Space), R < ‖(Real.sqrt (Real.exp (-τ)))⁻¹ • ξ‖ →
      ((heatX (1 - Real.exp (-τ)) y : Freq.X) : L2C) ((Real.sqrt (Real.exp (-τ)))⁻¹ • ξ) = 0 :=
    (Breakdown.Freq.Internal.FieldOp.qmp
      (LinearEquiv.smulOfNeZero ℝ Space _ hc).toContinuousLinearEquiv).tendsto_ae.eventually hf
  filter_upwards [Breakdown.Freq.Internal.Dilation.dilL2_ae fieldOpRealized hμ
    ((heatX (1 - Real.exp (-τ)) y : Freq.X) : L2C), h3] with ξ hd hh hR
  have hn : R < ‖(Real.sqrt (Real.exp (-τ)))⁻¹ • ξ‖ := by
    rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 hs).le]
    exact lt_of_lt_of_le hR (le_mul_of_one_le_left (norm_nonneg _) hc1)
  rw [e1, hd, hh hn, smul_zero]

theorem semigroupX_zero (y : Freq.X) : semigroupX 0 y = y := by
  have H := heatSemigroup fieldOpRealized
  have D := dilationAlgebra fieldOpRealized H
  show dilX (Real.exp (-0)) (heatX (1 - Real.exp (-0)) y) = y
  rw [neg_zero, Real.exp_zero, sub_self, D.2.1, H.1]
  rfl

theorem semigroup_add_of_families {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dil heat : ℝ → E →L[ℝ] E)
    (hDG : ∀ μ t, 0 < μ → 0 ≤ t → (dil μ).comp (heat (μ * t)) = (heat t).comp (dil μ))
    (hH : ∀ s t, 0 ≤ s → 0 ≤ t → heat (s + t) = (heat s).comp (heat t))
    (hD : ∀ μ ν, 0 < μ → 0 < ν → dil (μ * ν) = (dil μ).comp (dil ν))
    (s τ : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    (dil (Real.exp (-(s + τ)))).comp (heat (1 - Real.exp (-(s + τ)))) =
      ((dil (Real.exp (-s))).comp (heat (1 - Real.exp (-s)))).comp
        ((dil (Real.exp (-τ))).comp (heat (1 - Real.exp (-τ)))) := by
  have ha : 0 ≤ 1 - Real.exp (-s) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hs)
    linarith
  have hb : 0 ≤ 1 - Real.exp (-τ) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hτ)
    linarith
  have hμ : 0 < Real.exp (-τ) := Real.exp_pos _
  have hsum : Real.exp (-τ) * (1 - Real.exp (-s)) + (1 - Real.exp (-τ)) =
      1 - Real.exp (-(s + τ)) := by
    rw [neg_add, Real.exp_add]
    ring
  have hprod : Real.exp (-s) * Real.exp (-τ) = Real.exp (-(s + τ)) := by
    rw [neg_add, Real.exp_add]
  refine ContinuousLinearMap.ext fun y => ?_
  simp only [ContinuousLinearMap.comp_apply]
  have e1 : heat (1 - Real.exp (-s)) (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y)) =
      dil (Real.exp (-τ)) (heat (Real.exp (-τ) * (1 - Real.exp (-s)))
        (heat (1 - Real.exp (-τ)) y)) :=
    (congrArg (fun L : E →L[ℝ] E => L (heat (1 - Real.exp (-τ)) y))
      (hDG (Real.exp (-τ)) (1 - Real.exp (-s)) hμ ha)).symm
  have e2 : heat (Real.exp (-τ) * (1 - Real.exp (-s))) (heat (1 - Real.exp (-τ)) y) =
      heat (1 - Real.exp (-(s + τ))) y := by
    rw [← hsum, hH _ _ (mul_nonneg hμ.le ha) hb, ContinuousLinearMap.comp_apply]
  have e3 : ∀ z : E, dil (Real.exp (-s)) (dil (Real.exp (-τ)) z) =
      dil (Real.exp (-(s + τ))) z := fun z => by
    rw [← hprod, hD _ _ (Real.exp_pos _) hμ, ContinuousLinearMap.comp_apply]
  rw [e1, e2, e3]

theorem semigroupX_add (s τ : ℝ) (hs : 0 ≤ s) (hτ : 0 ≤ τ) :
    semigroupX (s + τ) = (semigroupX s).comp (semigroupX τ) := by
  have H := heatSemigroup fieldOpRealized
  have D := dilationAlgebra fieldOpRealized H
  unfold semigroupX
  exact semigroup_add_of_families dilX heatX D.2.2.2.1 H.2.1 D.2.2.1 s τ hs hτ

theorem norm_semigroupX_le (τ : ℝ) (hτ : 0 ≤ τ) : ‖semigroupX τ‖ ≤ Real.exp (-(τ / 4)) := by
  have H := heatSemigroup fieldOpRealized
  have D := dilationAlgebra fieldOpRealized H
  have ha : 0 ≤ 1 - Real.exp (-τ) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hτ)
    linarith
  have hpow : Real.exp (-τ) ^ (1 / 4 : ℝ) = Real.exp (-(τ / 4)) := by
    rw [← Real.exp_mul]
    ring_nf
  refine ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos _).le fun y => ?_
  show ‖dilX (Real.exp (-τ)) (heatX (1 - Real.exp (-τ)) y)‖ ≤ Real.exp (-(τ / 4)) * ‖y‖
  rw [D.1 _ (Real.exp_pos _), hpow]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  calc ‖heatX (1 - Real.exp (-τ)) y‖ ≤ ‖heatX (1 - Real.exp (-τ))‖ * ‖y‖ :=
        (heatX (1 - Real.exp (-τ))).le_opNorm y
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right (H.2.2.1 _ ha) (norm_nonneg _)
    _ = ‖y‖ := one_mul _

theorem semigroup_continuousOn_of_families {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (dil heat : ℝ → E →L[ℝ] E)
    (hDc : ∀ z, ContinuousOn (fun μ => dil μ z) (Ioi 0))
    (hDle : ∀ μ, 0 < μ → μ ≤ 1 → ∀ z, ‖dil μ z‖ ≤ ‖z‖)
    (hHc : ∀ z, ContinuousOn (fun t => heat t z) (Ici 0)) (y : E) :
    ContinuousOn (fun τ => (dil (Real.exp (-τ))).comp (heat (1 - Real.exp (-τ))) y) (Ici 0) := by
  simp only [ContinuousLinearMap.comp_apply]
  have hmapH : MapsTo (fun τ : ℝ => 1 - Real.exp (-τ)) (Ici 0) (Ici 0) := fun τ hτ => by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 (mem_Ici.1 hτ))
    simp only [mem_Ici]
    linarith
  have hb : ContinuousOn (fun τ : ℝ => heat (1 - Real.exp (-τ)) y) (Ici 0) :=
    (hHc y).comp (by fun_prop : Continuous fun τ : ℝ => 1 - Real.exp (-τ)).continuousOn hmapH
  have hmapD : MapsTo (fun τ : ℝ => Real.exp (-τ)) (Ici 0) (Ioi 0) := fun τ _ => Real.exp_pos _
  intro τ₀ hτ₀
  have hA : ContinuousWithinAt
      (fun τ => dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ₀)) y)) (Ici 0) τ₀ :=
    ((hDc _).comp (by fun_prop : Continuous fun τ : ℝ => Real.exp (-τ)).continuousOn hmapD) τ₀ hτ₀
  have hB := hb τ₀ hτ₀
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero] at hA hB ⊢
  have hAB := hA.add hB
  rw [zero_add] at hAB
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_ hAB
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have e : dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y) -
      dil (Real.exp (-τ₀)) (heat (1 - Real.exp (-τ₀)) y) =
      dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y - heat (1 - Real.exp (-τ₀)) y) +
      (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ₀)) y) -
        dil (Real.exp (-τ₀)) (heat (1 - Real.exp (-τ₀)) y)) := by
    rw [map_sub]
    abel
  rw [e]
  have h1 := norm_add_le (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ)) y -
      heat (1 - Real.exp (-τ₀)) y)) (dil (Real.exp (-τ)) (heat (1 - Real.exp (-τ₀)) y) -
        dil (Real.exp (-τ₀)) (heat (1 - Real.exp (-τ₀)) y))
  have h2 := hDle (Real.exp (-τ)) (Real.exp_pos _)
    (Real.exp_le_one_iff.2 (neg_nonpos.2 (mem_Ici.1 hτ)))
    (heat (1 - Real.exp (-τ)) y - heat (1 - Real.exp (-τ₀)) y)
  linarith

theorem continuousOn_semigroupX (y : Freq.X) :
    ContinuousOn (fun τ => semigroupX τ y) (Ici 0) := by
  have H := heatSemigroup fieldOpRealized
  have D := dilationAlgebra fieldOpRealized H
  have Dc := dilationContinuous fieldOpRealized D
  have hDle : ∀ μ : ℝ, 0 < μ → μ ≤ 1 → ∀ z : Freq.X, ‖dilX μ z‖ ≤ ‖z‖ := fun μ hμ hμ1 z => by
    rw [D.1 μ hμ z]
    exact mul_le_of_le_one_left (norm_nonneg _)
      (Real.rpow_le_one hμ.le hμ1 (by norm_num))
  unfold semigroupX
  exact semigroup_continuousOn_of_families dilX heatX Dc hDle H.2.2.2.1 y

private theorem bandCut_eq_zero' {R : ℝ} {ξ : Space} (h : bandCut R ξ = 0) : ‖ξ‖ ≤ R := by
  unfold bandCut at h
  have h1 : max (‖ξ‖ - R) 0 = 0 := by
    rcases min_eq_iff.1 h with ⟨h2, _⟩ | ⟨h2, _⟩
    · exact h2
    · norm_num at h2
  have := le_max_left (‖ξ‖ - R) 0
  linarith

private theorem continuous_halfSspCut' (R : ℝ) : Continuous (halfSspCut R) := by
  unfold halfSspCut
  fun_prop

private theorem halfSspCut_bound' (R : ℝ) (ξ : Space) : |halfSspCut R ξ| ≤ 2 * Real.pi * |R| := by
  unfold halfSspCut
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rcases le_total ‖ξ‖ R with h | h
  · rw [min_eq_left h, abs_of_nonneg (norm_nonneg _)]
    exact h.trans (le_abs_self R)
  · rw [min_eq_right h]

private theorem halfSspCut_neg' (R : ℝ) (ξ : Space) : halfSspCut R (-ξ) = halfSspCut R ξ := by
  simp only [halfSspCut, norm_neg]

private theorem continuous_bandCut' (R : ℝ) : Continuous (bandCut R) := by
  unfold bandCut
  fun_prop

private theorem bandCut_bound' (R : ℝ) (ξ : Space) : |bandCut R ξ| ≤ 1 := by
  unfold bandCut
  rw [abs_le]
  constructor
  · have := le_max_right (‖ξ‖ - R) 0
    exact le_min (by linarith) (by norm_num)
  · exact min_le_right _ _

private theorem halfSspX_coe' (R : ℝ) (y : Freq.X) :
    (halfSspX R y : L2C) = fieldOp id (fun ξ => halfSspCut R ξ • ContinuousLinearMap.id ℝ CSpace) y :=
  restrictX_coe (fun _ hx => Freq.Internal.Phi.scalarOp_mem fieldOpRealized
    (continuous_halfSspCut' R) (halfSspCut_bound' R) (halfSspCut_neg' R) hx) y

private theorem halfSspX_ae' (R : ℝ) (y : Freq.X) :
    ((halfSspX R y : L2C) : Space → CSpace) =ᵐ[volume]
      fun ξ => halfSspCut R ξ • ((y : L2C) : Space → CSpace) ξ := by
  rw [halfSspX_coe']
  exact Freq.Internal.Phi.scalarOp_ae fieldOpRealized (continuous_halfSspCut' R) (halfSspCut_bound' R) _

private theorem band_ae' (R : ℝ) (y : Freq.X) (hy : y ∈ bandX R) :
    ∀ᵐ ξ ∂(volume : Measure Space), bandCut R ξ • ((y : L2C) : Space → CSpace) ξ = 0 := by
  have h0 : bandOp R y = 0 := hy
  have h1 := Freq.Internal.Phi.scalarOp_ae fieldOpRealized (continuous_bandCut' R) (bandCut_bound' R)
    (y : L2C)
  have h2 : (fieldOp id (fun ξ => bandCut R ξ • ContinuousLinearMap.id ℝ CSpace) (y : L2C) : Space → CSpace)
      =ᵐ[volume] (0 : L2C) := by
    have e : fieldOp id (fun ξ => bandCut R ξ • ContinuousLinearMap.id ℝ CSpace) (y : L2C) = 0 := h0
    rw [e]
  filter_upwards [h1, h2, Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ e1 e2 e3
  rw [← e1, e2, e3]
  rfl

private theorem smoothH_coe' {t : ℝ} (ht : 0 < t) (x : Freq.X) :
    (smoothH t x : L2C) = fieldOp id (fun ξ => phiFactor t ξ • ContinuousLinearMap.id ℝ CSpace) x :=
  restrictX_coe (fun _ hx => Freq.Internal.Phi.scalarOp_mem fieldOpRealized
    (Freq.Internal.Phi.continuous_phiFactor t) (Freq.Internal.Phi.phiFactor_le ht)
    (fun ξ => by simp only [phiFactor, norm_neg]) hx) x

private theorem smoothH_eq_heat' (R : ℝ) {t : ℝ} (ht : 0 < t) (y : Freq.X) (hy : y ∈ bandX R) :
    (smoothH t y : L2C) = heatL2 t (halfSspX R y : L2C) := by
  rw [smoothH_coe' ht]
  apply Lp.ext
  filter_upwards [Freq.Internal.Phi.scalarOp_ae fieldOpRealized
      (Freq.Internal.Phi.continuous_phiFactor t) (Freq.Internal.Phi.phiFactor_le ht) (y : L2C),
    Freq.Internal.Dilation.heatL2_ae fieldOpRealized t (halfSspX R y : L2C), halfSspX_ae' R y,
    band_ae' R y hy] with ξ e1 e2 e3 e4
  rw [e1, e2, e3, smul_smul]
  by_cases hb : bandCut R ξ = 0
  · have hξ := bandCut_eq_zero' hb
    congr 1
    simp only [phiFactor, heatFactor, halfSspCut, min_eq_left hξ, max_eq_left ht.le]
    ring
  · have hz : ((y : L2C) : Space → CSpace) ξ = 0 := (smul_eq_zero.1 e4).resolve_left hb
    rw [hz, smul_zero, smul_zero]

theorem slicePropagator_eq_of_mem_band (R τ : ℝ) (hτ : 0 < τ) (y : Freq.X) (hy : y ∈ bandX R) :
    slicePropagator τ y = semigroupX τ (halfSspX R y) := by
  have ht : 0 < 1 - Real.exp (-τ) := by
    have := Real.exp_lt_exp.2 (neg_lt_zero.2 hτ)
    rw [Real.exp_zero] at this
    linarith
  have hμ : 0 < Real.exp (-τ) := Real.exp_pos _
  apply Subtype.ext
  show (dilX (Real.exp (-τ)) (smoothH (1 - Real.exp (-τ)) y) : L2C) =
    (dilX (Real.exp (-τ)) (heatX (1 - Real.exp (-τ)) (halfSspX R y)) : L2C)
  rw [Freq.Internal.Dilation.dilX_coe fieldOpRealized hμ, Freq.Internal.Dilation.dilX_coe fieldOpRealized hμ,
    Freq.Internal.Heat.heatX_coe fieldOpRealized, smoothH_eq_heat' R ht y hy]

private theorem normSq_L2C (g : L2C) : ‖g‖ ^ 2 = ∫ ξ, ‖(g : Space → CSpace) ξ‖ ^ 2 := by
  have h := L2.inner_def (𝕜 := ℂ) g g
  rw [inner_self_eq_norm_sq_to_K] at h
  have h2 : (∫ ξ, inner ℂ ((g : Space → CSpace) ξ) ((g : Space → CSpace) ξ)) =
      ∫ ξ, ((‖(g : Space → CSpace) ξ‖ ^ 2 : ℝ) : ℂ) := by
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp only [inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  rw [h2, integral_complex_ofReal] at h
  have h4 := congrArg Complex.re h
  simpa [← Complex.ofReal_pow] using h4

private def sqY (y : Freq.X) (ξ : Space) : ℝ := ‖((y : L2C) : Space → CSpace) ξ‖ ^ 2

private theorem integrable_sqY (y : Freq.X) : Integrable (sqY y) volume :=
  (memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _)

private theorem sqY_nonneg (y : Freq.X) (ξ : Space) : 0 ≤ sqY y ξ := by
  unfold sqY
  positivity

private def heatInt (y : Freq.X) (t : ℝ) : ℝ :=
  ∫ ξ, Real.exp (t * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) * sqY y ξ

private theorem norm_sq_semigroupX (y : Freq.X) {s : ℝ} (hs : 0 ≤ s) :
    ‖semigroupX s y‖ ^ 2 = Real.exp (s * (-(1 / 2))) * heatInt y (1 - Real.exp (-s)) := by
  have hμ : 0 < Real.exp (-s) := Real.exp_pos _
  have ht : 0 ≤ 1 - Real.exp (-s) := by
    have := Real.exp_le_one_iff.2 (neg_nonpos.2 hs)
    linarith
  have e1 : ‖semigroupX s y‖ = ‖dilL2 (Real.exp (-s)) (heatL2 (1 - Real.exp (-s)) (y : L2C))‖ := by
    show ‖(dilX (Real.exp (-s)) (heatX (1 - Real.exp (-s)) y) : L2C)‖ = _
    rw [Freq.Internal.Dilation.dilX_coe fieldOpRealized hμ, Freq.Internal.Heat.heatX_coe fieldOpRealized]
  have e2 : (∫ ξ, ‖((heatL2 (1 - Real.exp (-s)) (y : L2C) : L2C) : Space → CSpace) ξ‖ ^ 2) =
      heatInt y (1 - Real.exp (-s)) := by
    unfold heatInt sqY
    refine integral_congr_ae ?_
    filter_upwards [Freq.Internal.Dilation.heatL2_ae fieldOpRealized (1 - Real.exp (-s)) (y : L2C)]
      with ξ hξ
    rw [hξ, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, heatFactor, max_eq_left ht, sq (Real.exp _),
      ← Real.exp_add]
    congr 2
    ring
  have e3 : (Real.exp (-s) ^ (1 / 4 : ℝ)) ^ 2 = Real.exp (s * (-(1 / 2))) := by
    rw [← Real.exp_mul, sq, ← Real.exp_add]
    congr 1
    ring
  rw [e1, Freq.Internal.Dilation.norm_dilL2 fieldOpRealized hμ, mul_pow, normSq_L2C, e2, e3]

private theorem hasDerivAt_heatInt (R : ℝ) (y : Freq.X) (hy : y ∈ bandX R) :
    HasDerivAt (heatInt y) (∫ ξ, (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) * sqY y ξ) 0 := by
  have hint := integrable_sqY y
  have hmeas : ∀ t : ℝ, AEStronglyMeasurable
      (fun ξ : Space => Real.exp (t * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) * sqY y ξ) volume := fun t =>
    (Continuous.aestronglyMeasurable (by fun_prop)).mul hint.aestronglyMeasurable
  have hF0 : Integrable (fun ξ : Space => Real.exp ((0 : ℝ) * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) * sqY y ξ)
      volume := by
    simpa using hint
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume) (x₀ := (0 : ℝ))
    (s := Metric.ball (0 : ℝ) 1)
    (F := fun t ξ => Real.exp (t * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) * sqY y ξ)
    (F' := fun t ξ => Real.exp (t * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))
      * sqY y ξ)
    (bound := fun ξ => Real.exp (8 * Real.pi ^ 2 * R ^ 2) * (8 * Real.pi ^ 2 * R ^ 2) * sqY y ξ)
    (Metric.ball_mem_nhds 0 one_pos) (Eventually.of_forall hmeas) hF0
    ((Continuous.aestronglyMeasurable (by fun_prop)).mul hint.aestronglyMeasurable) ?_
    (hint.const_mul _) ?_
  · refine key.2.congr_deriv ?_
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    simp
  · filter_upwards [band_ae' R y hy] with ξ hξ t ht
    rw [Metric.mem_ball, Real.dist_eq, sub_zero] at ht
    by_cases hb : bandCut R ξ = 0
    · have hR := bandCut_eq_zero' hb
      have hsq : ‖ξ‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hR 2
      have ha : 8 * Real.pi ^ 2 * ‖ξ‖ ^ 2 ≤ 8 * Real.pi ^ 2 * R ^ 2 := by gcongr
      have ha0 : 0 ≤ 8 * Real.pi ^ 2 * ‖ξ‖ ^ 2 := by positivity
      have ht' := abs_lt.1 ht
      have he : Real.exp (t * (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2))) ≤ Real.exp (8 * Real.pi ^ 2 * R ^ 2) :=
        Real.exp_le_exp.2 (by nlinarith)
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos (Real.exp_pos _), abs_neg,
        abs_of_nonneg ha0, abs_of_nonneg (sqY_nonneg y ξ)]
      exact mul_le_mul_of_nonneg_right (mul_le_mul he ha ha0 (Real.exp_pos _).le) (sqY_nonneg y ξ)
    · have hz : ((y : L2C) : Space → CSpace) ξ = 0 := (smul_eq_zero.1 hξ).resolve_left hb
      simp [sqY, hz]
  · exact Eventually.of_forall fun ξ t _ => ((hasDerivAt_mul_const _).exp).mul_const _

private theorem norm_sq_halfSspX (R : ℝ) (y : Freq.X) (hy : y ∈ bandX R) :
    ‖halfSspX R y‖ ^ 2 = ∫ ξ, 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2 * sqY y ξ := by
  rw [show ‖halfSspX R y‖ = ‖(halfSspX R y : L2C)‖ from rfl, normSq_L2C]
  refine integral_congr_ae ?_
  filter_upwards [halfSspX_ae' R y, band_ae' R y hy] with ξ e1 e2
  rw [e1, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  by_cases hb : bandCut R ξ = 0
  · rw [halfSspCut, min_eq_left (bandCut_eq_zero' hb)]
    unfold sqY
    ring
  · have hz : ((y : L2C) : Space → CSpace) ξ = 0 := (smul_eq_zero.1 e2).resolve_left hb
    simp [sqY, hz]

theorem hasDerivWithinAt_norm_sq_semigroupX (R : ℝ) (y : Freq.X) (hy : y ∈ bandX R) :
    HasDerivWithinAt (fun s => ‖semigroupX s y‖ ^ 2)
      (-(1 / 2 : ℝ) * ‖y‖ ^ 2 - 2 * ‖halfSspX R y‖ ^ 2) (Ici 0) 0 := by
  have hh := hasDerivAt_heatInt R y hy
  have hin : HasDerivAt (fun s : ℝ => 1 - Real.exp (-s)) 1 0 := by
    have := ((hasDerivAt_neg (0 : ℝ)).exp).const_sub 1
    simpa using this
  have hcomp := HasDerivAt.comp_of_eq (0 : ℝ) hh hin (by simp)
  have hexp : HasDerivAt (fun s : ℝ => Real.exp (s * (-(1 / 2))))
      (Real.exp (0 * (-(1 / 2))) * (-(1 / 2))) 0 := (hasDerivAt_mul_const _).exp
  have hprod := hexp.mul hcomp
  have hw := hprod.hasDerivWithinAt (s := Ici (0 : ℝ))
  have hw2 : HasDerivWithinAt (fun s => ‖semigroupX s y‖ ^ 2)
      (Real.exp (0 * (-(1 / 2))) * (-(1 / 2)) * heatInt y (1 - Real.exp (-0)) +
        Real.exp (0 * (-(1 / 2))) * ((∫ ξ, (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) * sqY y ξ) * 1))
      (Ici 0) 0 :=
    hw.congr (fun s hs => norm_sq_semigroupX y hs) (norm_sq_semigroupX y le_rfl)
  convert hw2 using 1
  have h0 : heatInt y 0 = ‖y‖ ^ 2 := by
    rw [show ‖y‖ = ‖(y : L2C)‖ from rfl, normSq_L2C]
    unfold heatInt sqY
    simp
  have h1 : (∫ ξ, (-(8 * Real.pi ^ 2 * ‖ξ‖ ^ 2)) * sqY y ξ) = -(2 * ‖halfSspX R y‖ ^ 2) := by
    rw [norm_sq_halfSspX R y hy, ← integral_const_mul, ← integral_neg]
    refine integral_congr_ae (Eventually.of_forall fun ξ => ?_)
    ring
  simp only [zero_mul, Real.exp_zero, neg_zero, sub_self, one_mul, mul_one, h0, h1]
  ring

theorem exists_bound_of_periodic {E : Type*} [NormedAddCommGroup E] (G : ℝ → E)
    (hG : Continuous G) (hGp : ∀ σ, G (σ + 1) = G σ) : ∃ C, ∀ σ, ‖G σ‖ ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn
    hG.continuousOn
  refine ⟨C, fun σ => ?_⟩
  obtain ⟨y, hy, hyeq⟩ := (show Function.Periodic G 1 from hGp).exists_mem_Ico₀ one_pos σ
  rw [hyeq]
  exact hC y (Ico_subset_Icc_self hy)

section Abstract

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem continuousOn_apply_comp (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (g : ℝ → E) (hg : Continuous g) : ContinuousOn (fun τ => T τ (g τ)) (Ici 0) := by
  intro τ₀ hτ₀
  have h1 : Tendsto (fun τ => T τ (g τ - g τ₀)) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun τ => ‖g τ - g τ₀‖)
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      have hτ' : (0 : ℝ) ≤ τ := hτ
      have he : Real.exp (-(τ / 4)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
      calc ‖T τ (g τ - g τ₀)‖ ≤ ‖T τ‖ * ‖g τ - g τ₀‖ := (T τ).le_opNorm _
        _ ≤ 1 * ‖g τ - g τ₀‖ :=
          mul_le_mul_of_nonneg_right ((hnorm τ hτ').trans he) (norm_nonneg _)
        _ = ‖g τ - g τ₀‖ := one_mul _
    · have h : Tendsto (fun τ => ‖g τ - g τ₀‖) (𝓝 τ₀) (𝓝 ‖g τ₀ - g τ₀‖) :=
        ((hg.sub continuous_const).norm).tendsto τ₀
      rw [sub_self, norm_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto (fun τ => T τ (g τ₀)) (𝓝[Ici 0] τ₀) (𝓝 (T τ₀ (g τ₀))) := hcont (g τ₀) τ₀ hτ₀
  have h3 := h1.add h2
  rw [zero_add] at h3
  exact Tendsto.congr (fun τ => by rw [← map_add, sub_add_cancel]) h3

private theorem integrand_bound (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (G : ℝ → E) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) {P : ℝ} (σ : ℝ) :
    ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), ‖T τ (G (σ - τ / P))‖ ≤ Real.exp (-(1 / 4) * τ) * C := by
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun τ hτ => ?_
  have hτ' : (0 : ℝ) ≤ τ := le_of_lt hτ
  have he : Real.exp (-(τ / 4)) = Real.exp (-(1 / 4) * τ) := by ring_nf
  calc ‖T τ (G (σ - τ / P))‖ ≤ ‖T τ‖ * ‖G (σ - τ / P)‖ := (T τ).le_opNorm _
    _ ≤ Real.exp (-(τ / 4)) * C :=
      mul_le_mul (hnorm τ hτ') (hC _) (norm_nonneg _) (Real.exp_pos _).le
    _ = Real.exp (-(1 / 4) * τ) * C := by rw [he]

private theorem integrable_bound (C : ℝ) :
    Integrable (fun τ : ℝ => Real.exp (-(1 / 4) * τ) * C) (volume.restrict (Ioi (0 : ℝ))) :=
  (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).mul_const C

private theorem aesm_integrand (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) {P : ℝ} (σ : ℝ) :
    AEStronglyMeasurable (fun τ => T τ (G (σ - τ / P))) (volume.restrict (Ioi (0 : ℝ))) :=
  ((continuousOn_apply_comp T hnorm hcont (fun τ => G (σ - τ / P))
    (hG.comp (continuous_const.sub (continuous_id.div_const P)))).mono
    Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi

private theorem integrable_integrand (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) {P : ℝ} (σ : ℝ) :
    Integrable (fun τ => T τ (G (σ - τ / P))) (volume.restrict (Ioi (0 : ℝ))) :=
  (integrable_bound C).mono' (aesm_integrand T hnorm hcont G hG σ)
    (integrand_bound T hnorm G C hC σ)

theorem mild_continuous (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) {P : ℝ} (hP : 0 < P) :
    Continuous (fun σ => mildIntegral T G P σ) := by
  unfold mildIntegral
  exact continuous_of_dominated (fun σ => aesm_integrand T hnorm hcont G hG σ)
    (fun σ => integrand_bound T hnorm G C hC σ) (integrable_bound C)
    (Eventually.of_forall fun τ => (T τ).continuous.comp
      (hG.comp (continuous_id.sub continuous_const)))

theorem mild_periodic (T : ℝ → E →L[ℝ] E) (G : ℝ → E) (hGp : ∀ σ, G (σ + 1) = G σ)
    (P σ : ℝ) : mildIntegral T G P (σ + 1) = mildIntegral T G P σ := by
  unfold mildIntegral
  congr 1
  funext τ
  rw [show σ + 1 - τ / P = (σ - τ / P) + 1 by ring, hGp]

theorem mild_mem (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (K : Submodule ℝ E) (hK : IsClosed (K : Set E)) (hTK : ∀ τ, 0 ≤ τ → ∀ y ∈ K, T τ y ∈ K)
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) (hGK : ∀ σ, G σ ∈ K)
    {P : ℝ} (hP : 0 < P) (σ : ℝ) : mildIntegral T G P σ ∈ K := by
  haveI : CompleteSpace K := hK.completeSpace_coe
  have hint := integrable_integrand T hnorm hcont G hG C hC (P := P) σ
  rw [← K.orthogonal_orthogonal]
  intro u hu
  unfold mildIntegral
  rw [← integral_inner hint u]
  have hz : ∫ τ in Ioi (0 : ℝ), inner ℝ u (T τ (G (σ - τ / P))) = ∫ τ in Ioi (0 : ℝ), (0 : ℝ) :=
    setIntegral_congr_fun measurableSet_Ioi fun τ hτ =>
      Submodule.inner_left_of_mem_orthogonal (hTK τ (le_of_lt hτ) _ (hGK _)) hu
  rw [hz, integral_zero]


section EnergyW

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

private theorem norm_apply_le_of (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4))) {τ : ℝ} (hτ : 0 ≤ τ) (y : E) :
    ‖T τ y‖ ≤ ‖y‖ := by
  have h1 : Real.exp (-(τ / 4)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  calc ‖T τ y‖ ≤ ‖T τ‖ * ‖y‖ := (T τ).le_opNorm y
    _ ≤ 1 * ‖y‖ := mul_le_mul_of_nonneg_right ((hnorm τ hτ).trans h1) (norm_nonneg _)
    _ = ‖y‖ := one_mul _

private theorem continuousOn_apply_of (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0)) (g : ℝ → E) (hg : Continuous g) :
    ContinuousOn (fun τ => T τ (g τ)) (Ici 0) := by
  intro τ₀ hτ₀
  have h2 : Tendsto (fun τ => ‖g τ - g τ₀‖) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    exact (tendsto_iff_norm_sub_tendsto_zero.1 (hg.tendsto τ₀)).mono_left nhdsWithin_le_nhds
  have h1 : Tendsto (fun τ => T τ (g τ - g τ₀)) (𝓝[Ici 0] τ₀) (𝓝 0) := by
    refine squeeze_zero_norm' ?_ h2
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact norm_apply_le_of T hnorm hτ _
  have h3 : Tendsto (fun τ => T τ (g τ₀) + T τ (g τ - g τ₀)) (𝓝[Ici 0] τ₀) (𝓝 (T τ₀ (g τ₀) + 0)) :=
    Tendsto.add (hcont (g τ₀) τ₀ hτ₀) h1
  rw [add_zero] at h3
  refine h3.congr (fun τ => ?_)
  rw [← map_add, add_sub_cancel]

private theorem integrableOn_mild_of (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) (P t : ℝ) :
    IntegrableOn (fun τ => T τ (G (t - τ / P))) (Ioi 0) := by
  have hc : ContinuousOn (fun τ => T τ (G (t - τ / P))) (Ici 0) :=
    continuousOn_apply_of T hnorm hcont (fun τ => G (t - τ / P))
      (hG.comp (continuous_const.sub (continuous_id.div_const P)))
  have hexp : IntegrableOn (fun τ : ℝ => Real.exp (-(1 / 4 : ℝ) * τ) * C) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).mul_const C
  refine Integrable.mono' hexp ((hc.mono Ioi_subset_Ici_self).aestronglyMeasurable measurableSet_Ioi) ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi (fun τ hτ => ?_)
  have hτ0 : (0 : ℝ) ≤ τ := le_of_lt hτ
  have e : -(1 / 4 : ℝ) * τ = -(τ / 4) := by ring
  rw [e]
  calc ‖T τ (G (t - τ / P))‖ ≤ ‖T τ‖ * ‖G (t - τ / P)‖ := (T τ).le_opNorm _
    _ ≤ Real.exp (-(τ / 4)) * C :=
        mul_le_mul (hnorm τ hτ0) (hC _) (norm_nonneg _) (Real.exp_pos _).le

private theorem setIntegral_Ioi_shift (F : ℝ → E) (s : ℝ) :
    ∫ τ in Ioi s, F τ = ∫ τ in Ioi (0 : ℝ), F (τ + s) := by
  have h := integral_add_right_eq_self (μ := (volume : Measure ℝ)) ((Ioi s).indicator F) s
  rw [← integral_indicator measurableSet_Ioi, ← integral_indicator measurableSet_Ioi, ← h]
  congr 1
  funext τ
  by_cases hτ : 0 < τ
  · have h' : s < τ + s := by linarith
    simp only [indicator, mem_Ioi, if_pos hτ, if_pos h']
  · have h' : ¬ s < τ + s := by intro h''; exact hτ (by linarith)
    simp only [indicator, mem_Ioi, if_neg hτ, if_neg h']

private theorem mild_split (T : ℝ → E →L[ℝ] E)
    (hadd : ∀ s τ, 0 ≤ s → 0 ≤ τ → T (s + τ) = (T s).comp (T τ))
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) {P : ℝ} (hP : 0 < P)
    (σ t : ℝ) (hσt : σ ≤ t) :
    mildIntegral T G P t = T (P * (t - σ)) (mildIntegral T G P σ) +
      ∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P)) := by
  have hs : 0 ≤ P * (t - σ) := mul_nonneg hP.le (by linarith)
  have hi := integrableOn_mild_of T hnorm hcont G hG C hC P t
  have hi' := integrableOn_mild_of T hnorm hcont G hG C hC P σ
  have h1 : mildIntegral T G P t = (∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P))) +
      ∫ τ in Ioi (P * (t - σ)), T τ (G (t - τ / P)) := by
    rw [mildIntegral, ← Ioc_union_Ioi_eq_Ioi hs, setIntegral_union (Ioc_disjoint_Ioi le_rfl)
      measurableSet_Ioi (hi.mono_set Ioc_subset_Ioi_self) (hi.mono_set (Ioi_subset_Ioi hs)),
      intervalIntegral.integral_of_le hs]
  have h2 : ∫ τ in Ioi (P * (t - σ)), T τ (G (t - τ / P)) = T (P * (t - σ)) (mildIntegral T G P σ) := by
    rw [setIntegral_Ioi_shift, mildIntegral, ← ContinuousLinearMap.integral_comp_comm _ hi']
    refine setIntegral_congr_fun measurableSet_Ioi (fun τ hτ => ?_)
    have hτ0 : (0 : ℝ) ≤ τ := le_of_lt hτ
    have e : t - (P * (t - σ) + τ) / P = σ - τ / P := by field_simp; ring
    rw [add_comm τ, hadd _ τ hs hτ0, ContinuousLinearMap.comp_apply, e]
  rw [h1, h2, add_comm]

private theorem hasDerivWithinAt_inner_of_zero {A B : ℝ → E} {b : E} {s : Set ℝ} {σ : ℝ}
    (hB0 : B σ = 0) (hB : HasDerivWithinAt B b s σ) (hA : ContinuousWithinAt A s σ) :
    HasDerivWithinAt (fun t => inner ℝ (A t) (B t)) (inner ℝ (A σ) b) s σ := by
  rw [hasDerivWithinAt_iff_tendsto_slope] at hB ⊢
  have hA' : Tendsto A (𝓝[s \ {σ}] σ) (𝓝 (A σ)) := hA.mono_left (nhdsWithin_mono _ sdiff_subset)
  refine (hA'.inner hB).congr (fun t => ?_)
  simp only [slope_def_module, hB0, inner_zero_right, sub_zero, inner_smul_right, smul_eq_mul]

private theorem hasDerivWithinAt_rest (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0)) (hzero : ∀ y, T 0 y = y)
    (G : ℝ → E) (hG : Continuous G) {P : ℝ} (hP : 0 < P) (σ : ℝ) :
    HasDerivWithinAt (fun t => ∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P))) (P • G σ)
      (Ici σ) σ := by
  rw [hasDerivWithinAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set η := ε / (2 * P) with hη
  have hηpos : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ₁, hδ₁, hG1⟩ := Metric.continuous_iff.1 hG σ (η / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, hT2⟩ := Metric.continuousWithinAt_iff.1 (hcont (G σ) 0 (mem_Ici.2 le_rfl)) (η / 2)
    (by linarith)
  refine ⟨min δ₁ (δ₂ / P), lt_min hδ₁ (div_pos hδ₂ hP), fun {t} ht hdist => ?_⟩
  have htσ : σ < t := lt_of_le_of_ne ht.1 (fun h => ht.2 h.symm)
  have hd : t - σ < min δ₁ (δ₂ / P) := by
    rw [Real.dist_eq, abs_of_pos (by linarith)] at hdist
    exact hdist
  have hd1 : t - σ < δ₁ := lt_of_lt_of_le hd (min_le_left _ _)
  have hd2 : P * (t - σ) < δ₂ := by
    have := lt_of_lt_of_le hd (min_le_right _ _)
    rw [lt_div_iff₀ hP] at this
    linarith
  have hs : 0 ≤ P * (t - σ) := mul_nonneg hP.le (by linarith)
  have hcI : ContinuousOn (fun τ => T τ (G (t - τ / P))) (Ici 0) :=
    continuousOn_apply_of T hnorm hcont (fun τ => G (t - τ / P))
      (hG.comp (continuous_const.sub (continuous_id.div_const P)))
  have hint : IntervalIntegrable (fun τ => T τ (G (t - τ / P))) volume 0 (P * (t - σ)) := by
    refine ContinuousOn.intervalIntegrable (hcI.mono ?_)
    rw [uIcc_of_le hs]
    exact Icc_subset_Ici_self
  have hbound : ∀ τ ∈ uIoc (0 : ℝ) (P * (t - σ)), ‖T τ (G (t - τ / P)) - G σ‖ ≤ η := by
    intro τ hτ
    rw [uIoc_of_le hs] at hτ
    have hτ0 : (0 : ℝ) ≤ τ := le_of_lt hτ.1
    have hu : dist (t - τ / P) σ < δ₁ := by
      have h1 : τ / P ≤ t - σ := by rw [div_le_iff₀ hP]; linarith [hτ.2]
      have h2 : 0 ≤ τ / P := div_nonneg hτ0 hP.le
      rw [Real.dist_eq, abs_lt]
      constructor <;> linarith
    have hv : dist τ 0 < δ₂ := by
      rw [Real.dist_eq, sub_zero, abs_of_nonneg hτ0]
      linarith [hτ.2]
    have e1 := hG1 _ hu
    have e2 := hT2 hτ0 hv
    rw [dist_eq_norm] at e1 e2
    rw [hzero] at e2
    calc ‖T τ (G (t - τ / P)) - G σ‖
        = ‖T τ (G (t - τ / P) - G σ) + (T τ (G σ) - G σ)‖ := by
          rw [map_sub]; congr 1; abel
      _ ≤ ‖T τ (G (t - τ / P) - G σ)‖ + ‖T τ (G σ) - G σ‖ := norm_add_le _ _
      _ ≤ ‖G (t - τ / P) - G σ‖ + ‖T τ (G σ) - G σ‖ :=
          add_le_add (norm_apply_le_of T hnorm hτ0 _) le_rfl
      _ ≤ η := by linarith
  have hdiff : (∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P))) - (P * (t - σ)) • G σ =
      ∫ τ in (0 : ℝ)..P * (t - σ), (T τ (G (t - τ / P)) - G σ) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const, intervalIntegral.integral_const,
      sub_zero]
  have hn := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [← hdiff, sub_zero, abs_of_nonneg hs] at hn
  have hB0 : (∫ τ in (0 : ℝ)..P * (σ - σ), T τ (G (σ - τ / P))) = 0 := by
    rw [sub_self, mul_zero, intervalIntegral.integral_same]
  rw [dist_eq_norm, slope_def_module, hB0, sub_zero]
  have htσ' : 0 < t - σ := by linarith
  have e : (t - σ)⁻¹ • (∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P))) - P • G σ =
      (t - σ)⁻¹ • ((∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P))) - (P * (t - σ)) • G σ) := by
    rw [smul_sub, smul_smul]
    congr 2
    field_simp
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.2 htσ')]
  calc (t - σ)⁻¹ * ‖(∫ τ in (0 : ℝ)..P * (t - σ), T τ (G (t - τ / P))) - (P * (t - σ)) • G σ‖
      ≤ (t - σ)⁻¹ * (η * (P * (t - σ))) :=
        mul_le_mul_of_nonneg_left hn (inv_pos.2 htσ').le
    _ = ε / 2 := by rw [hη]; field_simp
    _ < ε := by linarith

theorem mild_energy (T : ℝ → E →L[ℝ] E)
    (hadd : ∀ s τ, 0 ≤ s → 0 ≤ τ → T (s + τ) = (T s).comp (T τ))
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ / 4)))
    (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0)) (hzero : ∀ y, T 0 y = y)
    (K : Submodule ℝ E) (hK : IsClosed (K : Set E)) (hTK : ∀ τ, 0 ≤ τ → ∀ y ∈ K, T τ y ∈ K)
    (Q : E → ℝ) (hQ : Continuous Q)
    (hder : ∀ y ∈ K, HasDerivWithinAt (fun s => ‖T s y‖ ^ 2) (Q y) (Ici 0) 0)
    (G : ℝ → E) (hG : Continuous G) (C : ℝ) (hC : ∀ σ, ‖G σ‖ ≤ C) (hGK : ∀ σ, G σ ∈ K)
    {P : ℝ} (hP : 0 < P) (a b : ℝ) (hab : a ≤ b) :
    ‖mildIntegral T G P b‖ ^ 2 - ‖mildIntegral T G P a‖ ^ 2 =
      ∫ σ in a..b, P * (2 * inner ℝ (mildIntegral T G P σ) (G σ) + Q (mildIntegral T G P σ)) := by
  have hc : Continuous (fun σ => mildIntegral T G P σ) :=
    mild_continuous T hnorm hcont G hG C hC hP
  have hderσ : ∀ σ, HasDerivWithinAt (fun t => ‖mildIntegral T G P t‖ ^ 2)
      (P * (2 * inner ℝ (mildIntegral T G P σ) (G σ) + Q (mildIntegral T G P σ))) (Ici σ) σ := by
    intro σ
    have hx := mild_mem T hnorm hcont K hK hTK G hG C hC hGK hP σ
    have hφ : HasDerivWithinAt (fun t : ℝ => P * (t - σ)) P (Ici σ) σ := by
      have := ((hasDerivAt_id σ).sub_const σ).const_mul P
      simpa using this.hasDerivWithinAt
    have hmaps : MapsTo (fun t : ℝ => P * (t - σ)) (Ici σ) (Ici 0) := fun t ht =>
      mul_nonneg hP.le (sub_nonneg.2 ht)
    have hg : HasDerivWithinAt (fun s => ‖T s (mildIntegral T G P σ)‖ ^ 2) (Q (mildIntegral T G P σ))
        (Ici 0) (P * (σ - σ)) := by
      rw [sub_self, mul_zero]
      exact hder _ hx
    have dA := hg.scomp σ hφ hmaps
    have cA : ContinuousWithinAt (fun t => T (P * (t - σ)) (mildIntegral T G P σ)) (Ici σ) σ :=
      ((hcont (mildIntegral T G P σ)).comp
        (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn hmaps) σ
        (mem_Ici.2 le_rfl)
    have dB := hasDerivWithinAt_rest T hnorm hcont hzero G hG hP σ
    have hB0 : (∫ τ in (0 : ℝ)..P * (σ - σ), T τ (G (σ - τ / P))) = 0 := by
      rw [sub_self, mul_zero, intervalIntegral.integral_same]
    have dAB := hasDerivWithinAt_inner_of_zero hB0 dB cA
    have dBB := hasDerivWithinAt_inner_of_zero hB0 dB dB.continuousWithinAt
    have hAσ : T (P * (σ - σ)) (mildIntegral T G P σ) = mildIntegral T G P σ := by
      rw [sub_self, mul_zero, hzero]
    have dsum := (dA.add (dAB.const_mul 2)).add dBB
    refine (dsum.congr_of_mem (fun t ht => ?_) (mem_Ici.2 le_rfl)).congr_deriv ?_
    · simp only [Pi.add_apply, Function.comp_apply]
      rw [mild_split T hadd hnorm hcont G hG C hC hP σ t ht, norm_add_sq_real,
        real_inner_self_eq_norm_sq]
    · rw [hAσ, hB0, inner_zero_left, inner_smul_right, smul_eq_mul]
      ring
  have hcf : Continuous (fun σ => P * (2 * inner ℝ (mildIntegral T G P σ) (G σ) + Q (mildIntegral T G P σ))) :=
    continuous_const.mul ((continuous_const.mul (hc.inner hG)).add (hQ.comp hc))
  exact (intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hab
    ((hc.norm.pow 2).continuousOn) (fun σ _ => (hderσ σ).mono Ioi_subset_Ici_self)
    (hcf.intervalIntegrable a b)).symm

end EnergyW

end Abstract

theorem final_identity {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (M : E →L[ℝ] E) (hM : ∀ y z, inner ℝ (M y) z = inner ℝ y (M z))
    (f k c F : ℝ → E) (hf : ∀ᵐ σ : ℝ, f σ = F σ) (hk : ∀ᵐ σ : ℝ, k σ = M (c σ))
    {P : ℝ} (hP : 0 < P) (a b : ℝ)
    (hen : ‖c b‖ ^ 2 - ‖c a‖ ^ 2 = ∫ σ in a..b, P * (2 * inner ℝ (c σ) (M (F σ)) +
      (-(1 / 2 : ℝ) * ‖c σ‖ ^ 2 - 2 * ‖M (c σ)‖ ^ 2))) :
    (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
      ∫ σ in a..b, (inner ℝ (f σ) (k σ) - ‖k σ‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) := by
  rw [hen, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf, hk] with σ h1 h2 _
  rw [h1, h2, ← hM, real_inner_comm (F σ)]
  field_simp
  ring

def denseSet : Set HH :=
  {f | ∃ R : ℝ, ∃ F : ℝ → Freq.X, Continuous F ∧ (∀ σ, F (σ + 1) = F σ) ∧
    (∀ σ, F σ ∈ bandX R) ∧ ∀ᵐ σ : ℝ, (f : TimeCircle → HBar) (σ : TimeCircle) = F σ}

theorem denseSet_add {f g : HH} (hf : f ∈ denseSet) (hg : g ∈ denseSet) :
    f + g ∈ denseSet := by
  obtain ⟨R₁, F₁, hc₁, hp₁, hb₁, ha₁⟩ := hf
  obtain ⟨R₂, F₂, hc₂, hp₂, hb₂, ha₂⟩ := hg
  refine ⟨max R₁ R₂, fun σ => F₁ σ + F₂ σ, hc₁.add hc₂, fun σ => congrArg₂ (· + ·) (hp₁ σ) (hp₂ σ),
    fun σ => add_mem (bandX_mono (le_max_left _ _) (hb₁ σ)) (bandX_mono (le_max_right _ _) (hb₂ σ)),
    ?_⟩
  filter_upwards [ha₁, ha₂, (ae_coe_iff (fun t => ((f + g : HH) : TimeCircle → HBar) t =
    ((f : TimeCircle → HBar) + (g : TimeCircle → HBar)) t)).1 (Lp.coeFn_add f g)] with σ h1 h2 h3
  exact h3.trans (congrArg₂ (· + ·) h1 h2)

theorem denseSet_zero : (0 : HH) ∈ denseSet := by
  refine ⟨0, fun _ => 0, continuous_const, fun _ => rfl, fun _ => zero_mem _, ?_⟩
  exact (ae_coe_iff (fun t => ((0 : HH) : TimeCircle → HBar) t = (0 : TimeCircle → HBar) t)).1
    (Lp.coeFn_zero HBar 2 (volume : Measure TimeCircle))

theorem denseSet_smul (c : ℝ) {f : HH} (hf : f ∈ denseSet) : c • f ∈ denseSet := by
  obtain ⟨R, F, hc, hp, hb, ha⟩ := hf
  refine ⟨R, fun σ => c • F σ, hc.const_smul c, fun σ => congrArg (c • ·) (hp σ),
    fun σ => Submodule.smul_mem _ c (hb σ), ?_⟩
  filter_upwards [ha, (ae_coe_iff (fun t => ((c • f : HH) : TimeCircle → HBar) t =
    (c • (f : TimeCircle → HBar)) t)).1 (Lp.coeFn_smul c f)] with σ h1 h2
  exact h2.trans (congrArg (c • ·) h1)

def denseClass : Submodule ℝ HH where
  carrier := denseSet
  add_mem' := fun hf hg => denseSet_add hf hg
  zero_mem' := denseSet_zero
  smul_mem' := fun c _ hf => denseSet_smul c hf

theorem tendsto_Lp_two_of_dominated {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] (u : ℕ → Lp E 2 μ) (v : Lp E 2 μ) (b : α → ℝ) (hbi : Integrable b μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖(u n : α → E) x - (v : α → E) x‖ ^ 2 ≤ b x)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => (u n : α → E) x) atTop (𝓝 ((v : α → E) x))) :
    Tendsto u atTop (𝓝 v) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm : ∀ n, ‖u n - v‖ =
      (∫ x, ‖((u n - v : Lp E 2 μ) : α → E) x‖ ^ (2 : ℝ) ∂μ) ^ (2 : ℝ)⁻¹ := by
    intro n
    rw [Lp.norm_def, (Lp.memLp (u n - v)).eLpNorm_eq_integral_rpow_norm two_ne_zero
      ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat, ENNReal.toReal_ofReal]
    exact Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _
  have hs : ∀ᵐ x ∂μ, ∀ n, ((u n - v : Lp E 2 μ) : α → E) x = (u n : α → E) x - (v : α → E) x :=
    ae_all_iff.2 fun n => Lp.coeFn_sub (u n) v
  have hint : Tendsto (fun n => ∫ x, ‖((u n - v : Lp E 2 μ) : α → E) x‖ ^ (2 : ℝ) ∂μ) atTop
      (𝓝 (∫ x, (0 : ℝ) ∂μ)) := by
    refine tendsto_integral_of_dominated_convergence b (fun n => ?_) hbi (fun n => ?_) ?_
    · exact ((Lp.aestronglyMeasurable (u n - v)).norm.aemeasurable.pow_const (2 : ℝ)).aestronglyMeasurable
    · filter_upwards [hb n, hs] with x hx hsx
      rw [hsx n, Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _), Real.rpow_two]
      exact hx
    · filter_upwards [hs, hlim] with x hsx hl
      have h1 : Tendsto (fun n => (u n : α → E) x - (v : α → E) x) atTop (𝓝 0) := by
        have := hl.sub_const ((v : α → E) x)
        rwa [sub_self] at this
      have h2 := (tendsto_norm_zero.comp h1).rpow_const (p := (2 : ℝ)) (Or.inr (by norm_num))
      rw [Real.zero_rpow two_ne_zero] at h2
      refine h2.congr fun n => ?_
      simp only [Function.comp_apply, hsx n]
  rw [integral_zero] at hint
  have h3 := hint.rpow_const (p := (2 : ℝ)⁻¹) (Or.inr (by norm_num))
  rw [Real.zero_rpow (by norm_num)] at h3
  exact h3.congr fun n => (hnorm n).symm

def cutFn (n : ℕ) (ξ : Space) : ℝ := max 0 (min 1 ((n : ℝ) + 1 - ‖ξ‖))

theorem continuous_cutFn (n : ℕ) : Continuous (cutFn n) :=
  continuous_const.max (continuous_const.min (continuous_const.sub continuous_norm))

theorem cutFn_nonneg (n : ℕ) (ξ : Space) : 0 ≤ cutFn n ξ := le_max_left _ _

theorem cutFn_le_one (n : ℕ) (ξ : Space) : cutFn n ξ ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem abs_cutFn_le (n : ℕ) (ξ : Space) : |cutFn n ξ| ≤ 1 := by
  rw [abs_of_nonneg (cutFn_nonneg n ξ)]
  exact cutFn_le_one n ξ

theorem cutFn_neg (n : ℕ) (ξ : Space) : cutFn n (-ξ) = cutFn n ξ := by
  simp only [cutFn, norm_neg]

def cutL2 (n : ℕ) : L2C →L[ℝ] L2C :=
  fieldOp id (fun ξ => cutFn n ξ • ContinuousLinearMap.id ℝ CSpace)

theorem cutL2_mem (n : ℕ) : ∀ x ∈ Sig, cutL2 n x ∈ Sig := fun _ hx =>
  Internal.Phi.scalarOp_mem fieldOpRealized (continuous_cutFn n) (abs_cutFn_le n) (cutFn_neg n) hx

theorem cutL2_ae (n : ℕ) (f : L2C) :
    (cutL2 n f : Space → CSpace) =ᵐ[volume] fun ξ => cutFn n ξ • (f : Space → CSpace) ξ :=
  Internal.Phi.scalarOp_ae fieldOpRealized (continuous_cutFn n) (abs_cutFn_le n) f

def cutX (n : ℕ) : Freq.X →L[ℝ] Freq.X := restrictX (cutL2 n)

theorem cutX_coe (n : ℕ) (x : Freq.X) : ((cutX n x : Freq.X) : L2C) = cutL2 n x :=
  restrictX_coe (cutL2_mem n) x

theorem norm_cutX_le (n : ℕ) (x : Freq.X) : ‖cutX n x‖ ≤ ‖x‖ := by
  have h := Internal.Phi.scalarOp_norm_le fieldOpRealized (continuous_cutFn n) (abs_cutFn_le n)
    (x : L2C)
  rw [one_mul] at h
  have e : ‖cutX n x‖ = ‖cutL2 n x‖ := by
    rw [← cutX_coe]
    rfl
  rw [e]
  exact h

theorem continuous_bandCut (R : ℝ) : Continuous (bandCut R) :=
  ((continuous_norm.sub continuous_const).max continuous_const).min continuous_const

theorem abs_bandCut_le (R : ℝ) (ξ : Space) : |bandCut R ξ| ≤ 1 := by
  have h0 : 0 ≤ bandCut R ξ := le_min (le_max_right _ _) zero_le_one
  rw [abs_of_nonneg h0]
  exact min_le_right _ _

theorem cut_band_zero (n : ℕ) (ξ : Space) (v : CSpace) :
    bandCut ((n : ℝ) + 1) ξ • cutFn n ξ • v = 0 := by
  by_cases h : ‖ξ‖ ≤ (n : ℝ) + 1
  · have : bandCut ((n : ℝ) + 1) ξ = 0 := by
      simp only [bandCut]
      rw [max_eq_right (by linarith), min_eq_left zero_le_one]
    rw [this, zero_smul]
  · have : cutFn n ξ = 0 := by
      simp only [cutFn]
      rw [min_eq_right (by linarith), max_eq_left (by linarith)]
    rw [this, zero_smul, smul_zero]

theorem cutX_mem_band (n : ℕ) (x : Freq.X) : cutX n x ∈ bandX ((n : ℝ) + 1) := by
  show (bandOp ((n : ℝ) + 1) : Freq.X →ₗ[ℝ] L2C) (cutX n x) = 0
  have e : (bandOp ((n : ℝ) + 1)) (cutX n x) =
      fieldOp id (fun ξ => bandCut ((n : ℝ) + 1) ξ • ContinuousLinearMap.id ℝ CSpace)
        (cutL2 n x) :=
    congrArg (fieldOp id (fun ξ => bandCut ((n : ℝ) + 1) ξ • ContinuousLinearMap.id ℝ CSpace))
      (cutX_coe n x)
  show (bandOp ((n : ℝ) + 1)) (cutX n x) = 0
  rw [e]
  apply Lp.ext
  filter_upwards [Internal.Phi.scalarOp_ae fieldOpRealized (continuous_bandCut ((n : ℝ) + 1))
      (abs_bandCut_le ((n : ℝ) + 1)) (cutL2 n x), cutL2_ae n x,
    Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ h1 h2 h3
  rw [h1, h2, h3]
  exact cut_band_zero n ξ _

theorem tendsto_cutX (y : Freq.X) : Tendsto (fun n => cutX n y) atTop (𝓝 y) := by
  rw [tendsto_subtype_rng]
  have e : (fun n => ((cutX n y : Freq.X) : L2C)) = fun n => cutL2 n (y : L2C) :=
    funext fun n => cutX_coe n y
  rw [e]
  refine tendsto_Lp_two_of_dominated (fun n => cutL2 n (y : L2C)) (y : L2C)
    (fun ξ => ‖((y : L2C) : Space → CSpace) ξ‖ ^ 2)
    ((memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable _)).1 (Lp.memLp _))
    (fun n => ?_) ?_
  · filter_upwards [cutL2_ae n (y : L2C)] with ξ h
    rw [h]
    have e2 : cutFn n ξ • ((y : L2C) : Space → CSpace) ξ - ((y : L2C) : Space → CSpace) ξ =
        (cutFn n ξ - 1) • ((y : L2C) : Space → CSpace) ξ := by
      rw [sub_smul, one_smul]
    rw [e2, norm_smul, Real.norm_eq_abs, mul_pow]
    have h0 := cutFn_nonneg n ξ
    have h1 := cutFn_le_one n ξ
    have hsq : |cutFn n ξ - 1| ^ 2 ≤ 1 := by
      rw [sq_abs]
      nlinarith
    exact le_trans (mul_le_mul_of_nonneg_right hsq (sq_nonneg _)) (le_of_eq (one_mul _))
  · filter_upwards [ae_all_iff.2 fun n => cutL2_ae n (y : L2C)] with ξ h
    refine tendsto_atTop_of_eventually_const (i₀ := ⌈‖ξ‖⌉₊) fun n hn => ?_
    rw [h n]
    have hn' : ‖ξ‖ ≤ (n : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hn)
    have : cutFn n ξ = 1 := by
      simp only [cutFn]
      rw [min_eq_left (by linarith), max_eq_right zero_le_one]
    rw [this, one_smul]

def cutMap (n : ℕ) (g : C(TimeCircle, Freq.X)) : C(TimeCircle, Freq.X) :=
  ContinuousMap.comp ⟨cutX n, (cutX n).continuous⟩ g

theorem toLp_cutMap_mem (n : ℕ) (g : C(TimeCircle, Freq.X)) :
    ContinuousMap.toLp (E := Freq.X) 2 (volume : Measure TimeCircle) ℝ (cutMap n g) ∈
      denseClass := by
  refine ⟨(n : ℝ) + 1, fun σ => cutX n (g (σ : TimeCircle)),
    (cutX n).continuous.comp (g.continuous.comp (AddCircle.continuous_mk' 1)),
    fun σ => ?_, fun σ => cutX_mem_band n _, ?_⟩
  · exact congrArg (fun t => cutX n (g t)) (AddCircle.coe_add_period (1 : ℝ) σ)
  · exact (ae_coe_iff _).1 (ContinuousMap.coeFn_toLp (E := Freq.X) (p := 2)
      (μ := (volume : Measure TimeCircle)) (𝕜 := ℝ) (cutMap n g))

theorem tendsto_toLp_comp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (C : ℕ → E →L[ℝ] E) (hC : ∀ n y, ‖C n y‖ ≤ ‖y‖)
    (hlim : ∀ y, Tendsto (fun n => C n y) atTop (𝓝 y)) (g : C(TimeCircle, E)) :
    Tendsto (fun n => ContinuousMap.toLp (E := E) 2 (volume : Measure TimeCircle) ℝ
      (ContinuousMap.comp ⟨C n, (C n).continuous⟩ g)) atTop
      (𝓝 (ContinuousMap.toLp (E := E) 2 (volume : Measure TimeCircle) ℝ g)) := by
  refine tendsto_Lp_two_of_dominated _ _ (fun _ => (2 * ‖g‖) ^ 2) (integrable_const _)
    (fun n => ?_) ?_
  · filter_upwards [ContinuousMap.coeFn_toLp (E := E) (p := 2)
      (μ := (volume : Measure TimeCircle)) (𝕜 := ℝ) (ContinuousMap.comp ⟨C n, (C n).continuous⟩ g),
      ContinuousMap.coeFn_toLp (E := E) (p := 2)
      (μ := (volume : Measure TimeCircle)) (𝕜 := ℝ) g] with t h1 h2
    rw [h1, h2]
    have a1 : ‖C n (g t) - g t‖ ≤ 2 * ‖g‖ := by
      have := norm_sub_le (C n (g t)) (g t)
      have := hC n (g t)
      have := g.norm_coe_le_norm t
      linarith
    exact pow_le_pow_left₀ (norm_nonneg _) a1 2
  · filter_upwards [ae_all_iff.2 fun n => ContinuousMap.coeFn_toLp (E := E) (p := 2)
      (μ := (volume : Measure TimeCircle)) (𝕜 := ℝ) (ContinuousMap.comp ⟨C n, (C n).continuous⟩ g),
      ContinuousMap.coeFn_toLp (E := E) (p := 2)
      (μ := (volume : Measure TimeCircle)) (𝕜 := ℝ) g] with t h1 h2
    rw [h2]
    exact (hlim (g t)).congr fun n => (h1 n).symm

theorem tendsto_toLp_cutMap (g : C(TimeCircle, Freq.X)) :
    Tendsto (fun n => ContinuousMap.toLp (E := Freq.X) 2 (volume : Measure TimeCircle) ℝ
      (cutMap n g)) atTop
      (𝓝 (ContinuousMap.toLp (E := Freq.X) 2 (volume : Measure TimeCircle) ℝ g)) :=
  tendsto_toLp_comp cutX norm_cutX_le tendsto_cutX g

theorem dense_denseClass : Dense (denseClass : Set HH) := by
  have hd := ContinuousMap.toLp_denseRange Freq.X (volume : Measure TimeCircle) ℝ (p := 2)
    ENNReal.ofNat_ne_top
  have hsub : Set.range (ContinuousMap.toLp (E := Freq.X) 2 (volume : Measure TimeCircle) ℝ) ⊆
      closure (denseClass : Set HH) := by
    rintro _ ⟨g, rfl⟩
    exact mem_closure_of_tendsto (tendsto_toLp_cutMap g)
      (Eventually.of_forall fun n => toLp_cutMap_mem n g)
  exact dense_closure.1 (hd.mono hsub)

private theorem lpIntegral_ae_of_kernel {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E]
    (g : ℝ → Lp (α := TimeCircle) E 2) (hg : IntegrableOn g (Ioi 0))
    (Γ : ℝ → TimeCircle → E)
    (hΓ : ∀ τ ∈ Ioi (0 : ℝ), (g τ : TimeCircle → E) =ᵐ[volume] Γ τ)
    (hm : AEStronglyMeasurable (Function.uncurry Γ)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure TimeCircle)))
    (b : ℝ → ℝ) (hb : IntegrableOn b (Ioi 0)) (hΓb : ∀ τ, 0 < τ → ∀ t, ‖Γ τ t‖ ≤ b τ) :
    ((∫ τ in Ioi (0 : ℝ), g τ : Lp (α := TimeCircle) E 2) : TimeCircle → E) =ᵐ[volume]
      fun t => ∫ τ in Ioi (0 : ℝ), Γ τ t := by
  have hfst : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure TimeCircle)),
      0 < z.1 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
  have hint : Integrable (Function.uncurry Γ)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure TimeCircle)) := by
    refine Integrable.mono' (Integrable.mul_prod hb (integrable_const (1 : ℝ))) hm ?_
    filter_upwards [hfst] with z hz
    show ‖Γ z.1 z.2‖ ≤ b z.1 * 1
    rw [mul_one]
    exact hΓb z.1 hz z.2
  have hcm : AEStronglyMeasurable (fun t : TimeCircle => ∫ τ in Ioi (0 : ℝ), Γ τ t)
      (volume : Measure TimeCircle) :=
    hm.prod_swap.integral_prod_right'
  have hmem : MemLp (fun t : TimeCircle => ∫ τ in Ioi (0 : ℝ), Γ τ t) 2 volume :=
    MemLp.of_bound hcm (∫ τ in Ioi (0 : ℝ), b τ) (Eventually.of_forall fun t =>
      norm_integral_le_of_norm_le hb ((ae_restrict_mem measurableSet_Ioi).mono fun τ hτ => hΓb τ hτ t))
  have hw : ∀ w : Lp (α := TimeCircle) E 2, Integrable (fun z : ℝ × TimeCircle =>
      inner ℝ ((w : TimeCircle → E) z.2) (Γ z.1 z.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure TimeCircle)) := fun w => by
    refine Integrable.mono' (Integrable.mul_prod hb
      ((Lp.memLp w).integrable one_le_two).norm) ((Lp.aestronglyMeasurable w).comp_snd.inner hm) ?_
    filter_upwards [hfst] with z hz
    exact (norm_inner_le_norm _ _).trans (by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_right (hΓb z.1 hz z.2) (norm_nonneg _))
  have heq : (∫ τ in Ioi (0 : ℝ), g τ) = hmem.toLp _ := by
    refine ext_inner_right ℝ fun w => ?_
    have h1 : ∫ τ in Ioi (0 : ℝ), inner ℝ w (g τ) =
        ∫ τ in Ioi (0 : ℝ), ∫ t, inner ℝ ((w : TimeCircle → E) t) (Γ τ t) := by
      refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hΓ τ hτ] with t ht
      rw [ht]
    have h2 : ∫ t, ∫ τ in Ioi (0 : ℝ), inner ℝ ((w : TimeCircle → E) t) (Γ τ t) =
        inner ℝ w (hmem.toLp _) := by
      rw [L2.inner_def]
      refine integral_congr_ae ?_
      filter_upwards [hint.prod_left_ae, hmem.coeFn_toLp] with t ht ht'
      rw [ht']
      exact integral_inner ht _
    calc inner ℝ (∫ τ in Ioi (0 : ℝ), g τ) w = inner ℝ w (∫ τ in Ioi (0 : ℝ), g τ) :=
          real_inner_comm _ _
      _ = ∫ τ in Ioi (0 : ℝ), inner ℝ w (g τ) := (integral_inner hg w).symm
      _ = ∫ τ in Ioi (0 : ℝ), ∫ t, inner ℝ ((w : TimeCircle → E) t) (Γ τ t) := h1
      _ = ∫ t, ∫ τ in Ioi (0 : ℝ), inner ℝ ((w : TimeCircle → E) t) (Γ τ t) :=
          integral_integral_swap (hw w)
      _ = inner ℝ w (hmem.toLp _) := h2
      _ = inner ℝ (hmem.toLp _) w := real_inner_comm _ _
  rw [heq]
  exact hmem.coeFn_toLp

private theorem continuous_apply_of_semigroup {E Y : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [TopologicalSpace Y] (T : ℝ → E →L[ℝ] E)
    (hnorm : ∀ τ, 0 ≤ τ → ‖T τ‖ ≤ 1) (hcont : ∀ y, ContinuousOn (fun τ => T τ y) (Ici 0))
    (a : Y → ℝ) (ha : Continuous a) (ha0 : ∀ y, 0 ≤ a y) (v : Y → E) (hv : Continuous v) :
    Continuous (fun y => T (a y) (v y)) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  have h2 : Continuous (fun y => T (a y) (v y₀)) :=
    (hcont (v y₀)).comp_continuous ha (fun y => ha0 y)
  have h1 : Tendsto (fun y => T (a y) (v y) - T (a y) (v y₀)) (𝓝 y₀) (𝓝 0) := by
    refine squeeze_zero_norm (fun y => ?_) (?_ : Tendsto (fun y => ‖v y - v y₀‖) (𝓝 y₀) (𝓝 0))
    · rw [← map_sub]
      exact ((T (a y)).le_opNorm _).trans
        (by simpa using mul_le_mul_of_nonneg_right (hnorm _ (ha0 y)) (norm_nonneg (v y - v y₀)))
    · have := ((hv.sub (continuous_const (y := v y₀))).norm).tendsto y₀
      simpa using this
  have := h1.add (h2.tendsto y₀)
  show Tendsto _ _ _
  simpa using this

open scoped Classical in
private theorem spec_of_dite' {α : Type*} [Zero α] {p : α → Prop} (h : ∃ a, p a) :
    p (if h : ∃ a, p a then h.choose else 0) := by
  rw [dif_pos h]
  exact h.choose_spec

private theorem gradInv_eq' (h1 : GradInvHolds) {P : ℝ} (hP : 0 < P) (f : HH) :
    gradInv P f = ∫ τ in Ioi (0 : ℝ), propagatorIntegrand P f τ :=
  spec_of_dite' (h1 P hP).2 f

private theorem continuous_lift' (F : ℝ → Freq.X) (hFc : Continuous F)
    (hper : Function.Periodic F 1) : Continuous hper.lift :=
  continuous_quot_lift _ hFc

private theorem continuous_coe_circle' : Continuous (fun x : ℝ => (x : TimeCircle)) :=
  continuous_quot_mk

private def kernel' (R P : ℝ) (L : TimeCircle → Freq.X) (τ : ℝ) (t : TimeCircle) : Freq.X :=
  semigroupX (max τ 0) (halfSspX R (L (t + ((-(τ / P) : ℝ) : TimeCircle))))

private theorem continuous_kernel' (R P : ℝ) (L : TimeCircle → Freq.X) (hL : Continuous L) :
    Continuous (Function.uncurry (kernel' R P L)) :=
  continuous_apply_of_semigroup semigroupX
    (fun τ hτ => (norm_semigroupX_le τ hτ).trans (by
      rw [Real.exp_le_one_iff]
      linarith))
    continuousOn_semigroupX (fun z : ℝ × TimeCircle => max z.1 0)
    (continuous_fst.max continuous_const) (fun z => le_max_right _ _)
    (fun z : ℝ × TimeCircle => halfSspX R (L (z.2 + ((-(z.1 / P) : ℝ) : TimeCircle))))
    ((halfSspX R).continuous.comp (hL.comp (continuous_snd.add
      (continuous_coe_circle'.comp ((continuous_fst.div_const P).neg)))))

private theorem norm_kernel_le' (R P C : ℝ) (L : TimeCircle → Freq.X)
    (hC : ∀ t, ‖halfSspX R (L t)‖ ≤ C) (τ : ℝ) (hτ : 0 < τ) (t : TimeCircle) :
    ‖kernel' R P L τ t‖ ≤ C * Real.exp (-(1 / 4) * τ) := by
  have h := (semigroupX (max τ 0)).le_opNorm (halfSspX R (L (t + ((-(τ / P) : ℝ) : TimeCircle))))
  have h2 := norm_semigroupX_le (max τ 0) (le_max_right _ _)
  rw [max_eq_left hτ.le] at h h2
  have e : -(τ / 4) = -(1 / 4) * τ := by ring
  rw [e] at h2
  calc ‖kernel' R P L τ t‖ ≤ ‖semigroupX τ‖ * ‖halfSspX R (L (t + ((-(τ / P) : ℝ) : TimeCircle)))‖ := by
        unfold kernel'
        rw [max_eq_left hτ.le]
        exact h
    _ ≤ Real.exp (-(1 / 4) * τ) * C :=
        mul_le_mul h2 (hC _) (norm_nonneg _) (Real.exp_pos _).le
    _ = C * Real.exp (-(1 / 4) * τ) := mul_comm _ _

private theorem integrand_ae' (R P : ℝ) (f : HH) (L : TimeCircle → Freq.X)
    (hLb : ∀ t, L t ∈ bandX R)
    (hfc : (f : TimeCircle → HBar) =ᵐ[volume] L) (τ : ℝ) (hτ : 0 < τ) :
    (propagatorIntegrand P f τ : TimeCircle → HBar) =ᵐ[volume] kernel' R P L τ := by
  have hA : ∀ᵐ t ∂(volume : Measure TimeCircle), (propagatorIntegrand P f τ : TimeCircle → HBar) t =
      slicePropagator τ ((shiftLp (-(τ / P)) f : TimeCircle → HBar) t) :=
    ContinuousLinearMap.coeFn_compLpL _ _
  have hB : (shiftLp (E := HBar) (-(τ / P)) f : TimeCircle → HBar) =ᵐ[volume]
      fun t => (f : TimeCircle → HBar) (t + ((-(τ / P) : ℝ) : TimeCircle)) :=
    Lp.coeFn_compMeasurePreserving f _
  have hC : (fun t => (f : TimeCircle → HBar) (t + ((-(τ / P) : ℝ) : TimeCircle))) =ᵐ[volume]
      fun t => L (t + ((-(τ / P) : ℝ) : TimeCircle)) :=
    (measurePreserving_add_right volume (((-(τ / P) : ℝ) : TimeCircle))).quasiMeasurePreserving.ae_eq hfc
  filter_upwards [hA, hB, hC] with t e1 e2 e3
  have e4 := slicePropagator_eq_of_mem_band R τ hτ _ (hLb (t + ((-(τ / P) : ℝ) : TimeCircle)))
  have e5 : kernel' R P L τ t = semigroupX τ (halfSspX R (L (t + ((-(τ / P) : ℝ) : TimeCircle)))) := by
    unfold kernel'
    rw [max_eq_left hτ.le]
  exact e1.trans ((congrArg (slicePropagator τ) (e2.trans e3)).trans (e4.trans e5.symm))

theorem gradInv_ae_mild (h0 : PropagatorBoundHolds) (h1 : GradInvHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) (R : ℝ) (F : ℝ → Freq.X) (hFc : Continuous F) (hFp : ∀ σ, F (σ + 1) = F σ)
    (hFR : ∀ σ, F σ ∈ bandX R) (hfF : ∀ᵐ σ : ℝ, (f : TimeCircle → HBar) (σ : TimeCircle) = F σ) :
    ∀ᵐ σ : ℝ, mildIntegral semigroupX (fun σ => halfSspX R (F σ)) P σ =
      (gradInv P f : TimeCircle → HBar) (σ : TimeCircle) := by
  have hper : Function.Periodic F 1 := hFp
  have hlift : ∀ σ : ℝ, hper.lift (σ : TimeCircle) = F σ := fun σ => hper.lift_coe σ
  have hband : ∀ t : TimeCircle, hper.lift t ∈ bandX R := fun t => by
    obtain ⟨σ, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact (hlift σ).symm ▸ hFR σ
  have hGc : Continuous (fun σ => halfSspX R (F σ)) := (halfSspX R).continuous.comp hFc
  have hGp : ∀ σ, halfSspX R (F (σ + 1)) = halfSspX R (F σ) := fun σ => congrArg (halfSspX R) (hFp σ)
  refine (exists_bound_of_periodic (fun σ => halfSspX R (F σ)) hGc hGp).elim fun C hC => ?_
  have hCl : ∀ t, ‖halfSspX R (hper.lift t)‖ ≤ C := fun t => by
    obtain ⟨σ, rfl⟩ := QuotientAddGroup.mk_surjective t
    exact (hlift σ).symm ▸ hC σ
  have hfc : (f : TimeCircle → HBar) =ᵐ[volume] hper.lift :=
    (ae_coe_iff _).2 (hfF.mono fun σ h => h.trans (hlift σ).symm)
  have hb : IntegrableOn (fun τ : ℝ => C * Real.exp (-(1 / 4) * τ)) (Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 (by norm_num : (0 : ℝ) < 1 / 4)).const_mul C
  have hm : AEStronglyMeasurable (Function.uncurry (kernel' R P hper.lift))
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume : Measure TimeCircle)) :=
    (continuous_kernel' R P hper.lift (continuous_lift' F hFc hper)).aestronglyMeasurable
  have hL := lpIntegral_ae_of_kernel (propagatorIntegrand P f) ((h1 P hP).1 f)
    (kernel' R P hper.lift) (fun τ hτ => integrand_ae' R P f hper.lift hband hfc τ hτ) hm _ hb
    (fun τ hτ t => norm_kernel_le' R P C hper.lift hCl τ hτ t)
  have hG : (gradInv P f : TimeCircle → HBar) =ᵐ[volume]
      fun t => ∫ τ in Ioi (0 : ℝ), kernel' R P hper.lift τ t :=
    (EventuallyEq.of_eq (congrArg (fun u : HH => (u : TimeCircle → HBar)) (gradInv_eq' h1 hP f))).trans hL
  filter_upwards [(ae_coe_iff _).1 hG] with σ hσ
  refine Eq.trans ?_ hσ.symm
  refine setIntegral_congr_fun measurableSet_Ioi fun τ hτ => ?_
  have e : hper.lift ((σ : TimeCircle) + ((-(τ / P) : ℝ) : TimeCircle)) = F (σ - τ / P) := by
    rw [← AddCircle.coe_add, hlift, ← sub_eq_add_neg]
  show semigroupX τ (halfSspX R (F (σ - τ / P))) =
    semigroupX (max τ 0) (halfSspX R (hper.lift ((σ : TimeCircle) + ((-(τ / P) : ℝ) : TimeCircle))))
  rw [max_eq_left (le_of_lt hτ), e]

theorem isHalfSspOf_congr (R : ℝ) (y y' k : Freq.X) (hy : y = y') (hk : k = halfSspX R y)
    (h : IsHalfSspOf y (halfSspX R y)) : IsHalfSspOf y' k := by
  subst hy
  subst hk
  exact h

theorem curve_of_band (h0 : PropagatorBoundHolds) (h1 : GradInvHolds) {P : ℝ} (hP : 0 < P)
    (f : HH) (R : ℝ) (F : ℝ → Freq.X) (hFc : Continuous F) (hFp : ∀ σ, F (σ + 1) = F σ)
    (hFR : ∀ σ, F σ ∈ bandX R) (hfF : ∀ᵐ σ : ℝ, (f : TimeCircle → HBar) (σ : TimeCircle) = F σ) :
    ∃ (k : HH) (c : ℝ → Freq.X),
      Continuous c ∧ (∀ σ, c (σ + 1) = c σ) ∧
      (∀ᵐ σ : ℝ, c σ = (gradInv P f : TimeCircle → HBar) (σ : TimeCircle)) ∧
      (∀ᵐ t : TimeCircle, IsHalfSspOf ((gradInv P f : TimeCircle → HBar) t)
        ((k : TimeCircle → HBar) t)) ∧
      ∀ a b : ℝ, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
        ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
            ((k : TimeCircle → HBar) (σ : TimeCircle))
          - ‖(k : TimeCircle → HBar) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) := by
  have hGc : Continuous (fun σ => halfSspX R (F σ)) := (halfSspX R).continuous.comp hFc
  have hGp : ∀ σ, halfSspX R (F (σ + 1)) = halfSspX R (F σ) := fun σ => congrArg (halfSspX R) (hFp σ)
  refine (exists_bound_of_periodic (fun σ => halfSspX R (F σ)) hGc hGp).elim fun C hC => ?_
  have hGK : ∀ σ, halfSspX R (F σ) ∈ bandX R := fun σ => halfSspX_mem_band R _ (hFR σ)
  have hae := gradInv_ae_mild h0 h1 hP f R F hFc hFp hFR hfF
  have hkae : ∀ᵐ σ : ℝ, (ContinuousLinearMap.compLpL 2 volume (halfSspX R) (gradInv P f) :
      TimeCircle → HBar) (σ : TimeCircle) =
      halfSspX R ((gradInv P f : TimeCircle → HBar) (σ : TimeCircle)) :=
    (ae_coe_iff _).1 (ContinuousLinearMap.coeFn_compLpL (halfSspX R) (gradInv P f))
  have hmem : ∀ σ, mildIntegral semigroupX (fun σ => halfSspX R (F σ)) P σ ∈ bandX R := fun σ =>
    mild_mem semigroupX norm_semigroupX_le continuousOn_semigroupX (bandX R) (isClosed_bandX R)
      (fun τ hτ y hy => semigroupX_mem_band R τ hτ y hy) (fun σ => halfSspX R (F σ)) hGc C hC hGK hP σ
  have hk : ∀ᵐ σ : ℝ, (ContinuousLinearMap.compLpL 2 volume (halfSspX R) (gradInv P f) :
      TimeCircle → HBar) (σ : TimeCircle) =
      halfSspX R (mildIntegral semigroupX (fun σ => halfSspX R (F σ)) P σ) := by
    filter_upwards [hae, hkae] with σ e1 e2
    exact e2.trans (congrArg (halfSspX R) e1.symm)
  have hQ : Continuous (fun y : Freq.X => -(1 / 2 : ℝ) * ‖y‖ ^ 2 - 2 * ‖halfSspX R y‖ ^ 2) :=
    (continuous_const.mul (continuous_norm.pow 2)).sub
      (continuous_const.mul (((halfSspX R).continuous.norm).pow 2))
  refine ⟨ContinuousLinearMap.compLpL 2 volume (halfSspX R) (gradInv P f),
    fun σ => mildIntegral semigroupX (fun σ => halfSspX R (F σ)) P σ,
    mild_continuous semigroupX norm_semigroupX_le continuousOn_semigroupX
      (fun σ => halfSspX R (F σ)) hGc C hC hP,
    fun σ => mild_periodic semigroupX (fun σ => halfSspX R (F σ)) hGp P σ, hae, ?_, ?_⟩
  · refine (ae_coe_iff _).2 ?_
    filter_upwards [hae, hk] with σ e1 e2
    exact isHalfSspOf_congr R _ _ _ e1 e2 (isHalfSspOf_of_mem_band R _ (hmem σ))
  · intro a b hab
    exact final_identity (halfSspX R) (inner_halfSspX R)
      (fun σ : ℝ => (f : TimeCircle → HBar) (σ : TimeCircle))
      (fun σ : ℝ => (ContinuousLinearMap.compLpL 2 volume (halfSspX R) (gradInv P f) :
        TimeCircle → HBar) (σ : TimeCircle))
      (fun σ => mildIntegral semigroupX (fun σ => halfSspX R (F σ)) P σ) F hfF hk hP a b
      (mild_energy semigroupX semigroupX_add norm_semigroupX_le continuousOn_semigroupX
        semigroupX_zero (bandX R) (isClosed_bandX R)
        (fun τ hτ y hy => semigroupX_mem_band R τ hτ y hy) _ hQ
        (fun y hy => hasDerivWithinAt_norm_sq_semigroupX R y hy) (fun σ => halfSspX R (F σ)) hGc C hC hGK
        hP a b hab)

end Internal.DenseEnergyBand

open Internal.DenseEnergyBand in
theorem exists_dense_energyCurve_band (h0 : PropagatorBoundHolds) (h1 : GradInvHolds)
    (_h2 : GraphClosedHolds) {P : ℝ} (hP : 0 < P) :
    ∃ D : Submodule ℝ HH, Dense (D : Set HH) ∧ ∀ f ∈ D, ∃ (k : HH) (c : ℝ → Freq.X),
      Continuous c ∧ (∀ σ, c (σ + 1) = c σ) ∧
      (∀ᵐ σ : ℝ, c σ = (gradInv P f : TimeCircle → HBar) (σ : TimeCircle)) ∧
      (∀ᵐ t : TimeCircle, IsHalfSspOf ((gradInv P f : TimeCircle → HBar) t)
        ((k : TimeCircle → HBar) t)) ∧
      ∀ a b : ℝ, a ≤ b → (1 / (2 * P)) * (‖c b‖ ^ 2 - ‖c a‖ ^ 2) =
        ∫ σ in a..b, (inner ℝ ((f : TimeCircle → HBar) (σ : TimeCircle))
            ((k : TimeCircle → HBar) (σ : TimeCircle))
          - ‖(k : TimeCircle → HBar) (σ : TimeCircle)‖ ^ 2 - (1 / 4 : ℝ) * ‖c σ‖ ^ 2) :=
  ⟨denseClass, dense_denseClass, fun f hf => hf.elim fun R hR => hR.elim fun F hF =>
    curve_of_band h0 h1 hP f R F hF.1 hF.2.1 hF.2.2.1 hF.2.2.2⟩

end Breakdown.Cert
