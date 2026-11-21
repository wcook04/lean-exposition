import Breakdown.FracCert.StHeldParts
import Breakdown.Frac.NNiceField
import Breakdown.Frac.NNicePairing
import Breakdown.Uniqueness.CutoffBounds
import Breakdown.FracCert.StQuadratic
import Breakdown.FracCert.PowerSymbolRapid

open scoped ContDiff ENNReal SchwartzMap
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

def ProfileEmbedDataStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, AEStronglyMeasurable (d.profile p) volume ∧ MemLp (d.profile p) 6 volume ∧
      AEStronglyMeasurable (d.gradProfile p) volume ∧ Integrable (fun y => entrySq (d.gradProfile p y)) ∧
      IsWeakGradientOf (d.profile p) (d.gradProfile p) ∧
      (∀ᵐ y ∂volume, ∑ i : Fin 3, inner ℝ (d.gradProfile p y (unitVector i)) (unitVector i) = 0)

def HeldQuadraticL2Statement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d →
    ∀ p ∈ box d.radius, ∀ v G H, IsSecondOrderField d.order v G H →
      MemLp (fun y => (d.gradProfile p y + G y) (d.profile p y + v y)) 2 volume

def NiceSolenoidalStatement : Prop := ∀ φ, Freq.IsNiceField φ → IsSolenoidalL2 φ

def DriftNicePairingStatement : Prop :=
  ∀ α a : ℝ, 0 < α → ∀ (v : Space → Space) (G : Space → (Space →L[ℝ] Space)),
    AEStronglyMeasurable v volume → MemLp v 6 volume → AEStronglyMeasurable G volume →
    Integrable (fun y => entrySq (G y)) → IsWeakGradientOf v G → ∀ φ, Freq.IsNiceField φ →
      Integrable (fun y => inner ℝ (v y) (FracCert.driftAdjoint α a φ y)) ∧
      ∫ y, inner ℝ (driftField α a v G y) (φ y) = ∫ y, inner ℝ (v y) (FracCert.driftAdjoint α a φ y)

def WeakPowerNiceStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ v P : Space → Space, AEStronglyMeasurable v volume →
    MemLp v 6 volume → IsWeakFractionalPower α v P → ∀ φ, Freq.IsNiceField φ →
      Integrable (fun y => inner ℝ (v y) (fractionalPowerAt α φ y)) ∧
      ∫ y, inner ℝ (P y) (φ y) = ∫ y, inner ℝ (v y) (fractionalPowerAt α φ y)

namespace HeldWeakProfilePartsInternal

theorem test_ibp {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {φ : Space → ℝ} (hφ : IsTestScalar φ)
    {g : Space → E} (hg : ContDiff ℝ 1 g) (v : Space) :
    ∫ y, (fderiv ℝ φ y v) • g y = -∫ y, φ y • fderiv ℝ g y v := by
  have hφc : Continuous φ := hφ.1.continuous
  have hφd : Continuous (fun y => fderiv ℝ φ y v) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hgd : Continuous (fun y => fderiv ℝ g y v) := (hg.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have c0 : HasCompactSupport φ := hφ.2
  have c1 : HasCompactSupport (fun y => fderiv ℝ φ y v) := c0.fderiv_apply (𝕜 := ℝ) v
  have key := integral_bilinear_fderiv_right_eq_neg_left_of_integrable (μ := volume)
    (B := ContinuousLinearMap.lsmul ℝ ℝ) (f := φ) (g := g) (v := v)
    (by
      simp only [ContinuousLinearMap.lsmul_apply]
      exact (hφd.smul hg.continuous).integrable_of_hasCompactSupport (c1.smul_right))
    (by
      simp only [ContinuousLinearMap.lsmul_apply]
      exact (hφc.smul hgd).integrable_of_hasCompactSupport (c0.smul_right))
    (by
      simp only [ContinuousLinearMap.lsmul_apply]
      exact (hφc.smul hg.continuous).integrable_of_hasCompactSupport (c0.smul_right))
    (fun x _ => hφ.1.differentiable (by simp) x) (fun x _ => hg.differentiable one_ne_zero x)
  simp only [ContinuousLinearMap.lsmul_apply] at key
  rw [key, neg_neg]

theorem inner_gradient (a : Space) (ψ : Space → ℝ) (y : Space) :
    inner ℝ a (gradientAt ψ y) = ∑ i : Fin 3, fderiv ℝ ψ y (unitVector i) • a i := by
  simp only [gradientAt, inner_sum, real_inner_smul_right, unitVector, EuclideanSpace.inner_single_right,
    one_mul, smul_eq_mul]
  simp

theorem coord_fderiv {φ : Space → Space} (hφ : Differentiable ℝ φ) (i : Fin 3) (y v : Space) :
    fderiv ℝ (fun x => φ x i) y v = fderiv ℝ φ y v i := by
  have h : HasFDerivAt (fun x => φ x i)
      ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp (fderiv ℝ φ y)) y :=
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).hasFDerivAt.comp y (hφ y).hasFDerivAt
  rw [h.fderiv]
  rfl

theorem weak_component {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (j k : Fin 3)
    (hv : LocallyIntegrable v volume) (hG : LocallyIntegrable (fun y => G y (unitVector j)) volume)
    (hw : IsWeakGradientOf v G) {ψ : Space → ℝ} (hψ : ContDiff ℝ ∞ ψ)
    (i1 : Integrable (fun y => fderiv ℝ ψ y (unitVector j) * v y k))
    (i2 : Integrable (fun y => ψ y * v y k))
    (i3 : Integrable (fun y => ψ y * G y (unitVector j) k)) :
    ∫ y, fderiv ℝ ψ y (unitVector j) * v y k = -∫ y, ψ y * G y (unitVector j) k := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  set χ : ℕ → Space → ℝ := fun n => radialCutoff ((n : ℝ) + 1) with hχ
  have hχs : ∀ n, ContDiff ℝ ∞ (χ n) := fun n => contDiff_radialCutoff (hr n)
  have hψn : ∀ n, IsTestScalar (fun y => χ n y * ψ y) := fun n =>
    ⟨(hχs n).mul hψ, (hasCompactSupport_radialCutoff (hr n)).mul_right⟩
  have hder : ∀ n y, fderiv ℝ (fun y => χ n y * ψ y) y (unitVector j) =
      χ n y * fderiv ℝ ψ y (unitVector j) + ψ y * fderiv ℝ (χ n) y (unitVector j) := by
    intro n y
    have hd := ((hχs n).differentiable (by simp) y).hasFDerivAt.mul
      ((hψ.differentiable (by simp) y).hasFDerivAt)
    rw [show (fun y => χ n y * ψ y) = χ n * ψ from rfl, hd.fderiv]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hE : ∀ n, ∫ y, fderiv ℝ (fun y => χ n y * ψ y) y (unitVector j) * v y k =
      -∫ y, (χ n y * ψ y) * G y (unitVector j) k := by
    intro n
    have h := hw _ (hψn n) j
    have c1 : Continuous (fun y => fderiv ℝ (fun y => χ n y * ψ y) y (unitVector j)) :=
      ((hψn n).1.continuous_fderiv (by simp)).clm_apply continuous_const
    have int1 := hv.integrable_smul_left_of_hasCompactSupport c1
      ((hψn n).2.fderiv_apply (𝕜 := ℝ) (unitVector j))
    have int2 := hG.integrable_smul_left_of_hasCompactSupport (hψn n).1.continuous (hψn n).2
    have e1 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm int1
    have e2 := (EuclideanSpace.proj k : Space →L[ℝ] ℝ).integral_comp_comm int2
    have h' := congrArg (EuclideanSpace.proj k : Space →L[ℝ] ℝ) h
    rw [map_neg, ← e1, ← e2] at h'
    simpa [smul_eq_mul] using h'
  have hχ1 : ∀ y, ∀ᶠ n : ℕ in Filter.atTop, χ n y = 1 := by
    intro y
    filter_upwards [Filter.eventually_ge_atTop ⌈‖y‖⌉₊] with n hn
    apply radialCutoff_eq_one (hr n)
    have := Nat.le_ceil ‖y‖
    have h2 : (⌈‖y‖⌉₊ : ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have hdχ : ∀ n y, |fderiv ℝ (χ n) y (unitVector j)| ≤ c / ((n : ℝ) + 1) := by
    intro n y
    have h1 := (fderiv ℝ (χ n) y).le_opNorm (unitVector j)
    have hu : ‖unitVector j‖ = 1 := by simp [unitVector]
    rw [hu, mul_one, Real.norm_eq_abs] at h1
    exact h1.trans (hc _ (hr n) y)
  have hc0 : 0 ≤ c := by
    have := (abs_nonneg _).trans (hdχ 0 0)
    simpa using this
  have hdχ' : ∀ n y, |fderiv ℝ (χ n) y (unitVector j)| ≤ c := fun n y =>
    (hdχ n y).trans (div_le_self hc0 (by linarith [hr n, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]))
  have hdχ0 : ∀ y, Filter.Tendsto (fun n : ℕ => fderiv ℝ (χ n) y (unitVector j)) Filter.atTop (nhds 0) := by
    intro y
    have ht : Filter.Tendsto (fun n : ℕ => c * (1 / ((n : ℝ) + 1))) Filter.atTop (nhds (c * 0)) :=
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul c
    rw [mul_zero] at ht
    refine squeeze_zero_norm (fun n => ?_) ht
    rw [Real.norm_eq_abs, mul_one_div]
    exact hdχ n y
  have hχb : ∀ n y, |χ n y| ≤ 1 := fun n y => by
    rw [abs_of_nonneg (radialCutoff_nonneg _ _)]
    exact radialCutoff_le_one _ _
  have L1 : Filter.Tendsto (fun n => ∫ y, fderiv ℝ (fun y => χ n y * ψ y) y (unitVector j) * v y k)
      Filter.atTop (nhds (∫ y, fderiv ℝ ψ y (unitVector j) * v y k)) := by
    simp only [hder]
    refine tendsto_integral_of_dominated_convergence
      (fun y => |fderiv ℝ ψ y (unitVector j) * v y k| + c * |ψ y * v y k|) (fun n => ?_)
      (i1.abs.add (i2.abs.const_mul c)) (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have hvk : AEStronglyMeasurable (fun y => v y k) volume :=
        (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable
      have hcont : Continuous (fun y => χ n y * fderiv ℝ ψ y (unitVector j) +
          ψ y * fderiv ℝ (χ n) y (unitVector j)) :=
        ((hχs n).continuous.mul ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)).add
          (hψ.continuous.mul (((hχs n).continuous_fderiv (by simp)).clm_apply continuous_const))
      exact hcont.aestronglyMeasurable.mul hvk
    · rw [Real.norm_eq_abs, add_mul, abs_le]
      have a1 : |χ n y * fderiv ℝ ψ y (unitVector j) * v y k| ≤ |fderiv ℝ ψ y (unitVector j) * v y k| := by
        rw [mul_assoc, abs_mul]
        exact mul_le_of_le_one_left (abs_nonneg _) (hχb n y)
      have a2 : |ψ y * fderiv ℝ (χ n) y (unitVector j) * v y k| ≤ c * |ψ y * v y k| := by
        rw [mul_comm (ψ y), mul_assoc, abs_mul]
        exact mul_le_mul_of_nonneg_right (hdχ' n y) (abs_nonneg _)
      constructor <;> linarith [abs_le.1 a1, abs_le.1 a2]
    · have t1 : Filter.Tendsto (fun n => χ n y) Filter.atTop (nhds 1) :=
        tendsto_const_nhds.congr' (by filter_upwards [hχ1 y] with n hn; exact hn.symm)
      have := ((t1.mul_const (fderiv ℝ ψ y (unitVector j))).add
        ((hdχ0 y).const_mul (ψ y))).mul_const (v y k)
      simpa using this
  have L2 : Filter.Tendsto (fun n => -∫ y, (χ n y * ψ y) * G y (unitVector j) k)
      Filter.atTop (nhds (-∫ y, ψ y * G y (unitVector j) k)) := by
    refine Filter.Tendsto.neg ?_
    refine tendsto_integral_of_dominated_convergence (fun y => |ψ y * G y (unitVector j) k|) (fun n => ?_)
      i3.abs (fun n => ae_of_all _ fun y => ?_) (ae_of_all _ fun y => ?_)
    · have hGk : AEStronglyMeasurable (fun y => G y (unitVector j) k) volume :=
        (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable hG.aestronglyMeasurable
      exact (((hχs n).continuous.mul hψ.continuous).aestronglyMeasurable).mul hGk
    · rw [Real.norm_eq_abs, mul_assoc, abs_mul]
      exact mul_le_of_le_one_left (abs_nonneg _) (hχb n y)
    · have t1 : Filter.Tendsto (fun n => χ n y) Filter.atTop (nhds 1) :=
        tendsto_const_nhds.congr' (by filter_upwards [hχ1 y] with n hn; exact hn.symm)
      have := (t1.mul_const (ψ y)).mul_const (G y (unitVector j) k)
      simpa using this
  exact tendsto_nhds_unique (L1.congr hE) L2

theorem norm_apply_sq_le (A : Space →L[ℝ] Space) (w : Space) :
    ‖A w‖ ^ 2 ≤ 3 * ‖w‖ ^ 2 * entrySq A := by
  have hw : w = ∑ i : Fin 3, w i • unitVector i := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
    simpa [unitVector] using this.symm
  have h1 : ‖A w‖ ≤ ∑ i : Fin 3, ‖w‖ * ‖A (unitVector i)‖ := by
    conv_lhs => rw [hw]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [map_smul, norm_smul]
    exact mul_le_mul_of_nonneg_right (by simpa using PiLp.norm_apply_le w i) (norm_nonneg _)
  have h2 : (∑ i : Fin 3, ‖w‖ * ‖A (unitVector i)‖) ^ 2 ≤ 3 * ‖w‖ ^ 2 * entrySq A := by
    unfold entrySq
    simp only [Fin.sum_univ_three]
    nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖),
      sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖),
      sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖), sq_nonneg ‖w‖]
  exact (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2

theorem weight_split (t x : ℝ) (ht : 0 ≤ t) (hx : 0 ≤ x) : t ^ 2 * x ≤ t ^ 3 + x ^ 3 := by
  rcases le_total x t with h | h
  · nlinarith [pow_nonneg hx 3, mul_le_mul_of_nonneg_left h (sq_nonneg t)]
  · nlinarith [pow_nonneg ht 3, mul_le_mul_of_nonneg_left h (sq_nonneg x),
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ ht h 2) hx]

theorem decay_mul_integrable {s f : Space → ℝ} (hs : Continuous s) {B : ℝ}
    (hB : ∀ y, (1 + ‖y‖) ^ 4 * |s y| ≤ B) (hf : AEStronglyMeasurable f volume) {n : ℕ} (hn : 1 ≤ n)
    (hfn : Integrable (fun y => |f y| ^ n)) : Integrable (fun y => s y * f y) := by
  have i4 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4:ℝ))) :=
    integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; norm_num)
  have hs' : ∀ y, |s y| ≤ B * (1 + ‖y‖) ^ (-(4:ℝ)) := by
    intro y
    have hp : 0 < (1 + ‖y‖) ^ 4 := by positivity
    rw [Real.rpow_neg (by positivity), show ((1 + ‖y‖) ^ (4:ℝ)) = (1 + ‖y‖) ^ (4:ℕ) by norm_cast,
      ← div_eq_mul_inv, le_div_iff₀ hp, mul_comm]
    exact hB y
  have hB0 : 0 ≤ B := (mul_nonneg (by positivity) (abs_nonneg _)).trans (hB 0)
  have hsb : ∀ y, |s y| ≤ B := fun y => (hs' y).trans (mul_le_of_le_one_right hB0
    (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)))
  refine ((i4.const_mul B).add (hfn.const_mul B)).mono' (hs.aestronglyMeasurable.mul hf)
    (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |f y| ≤ 1 + |f y| ^ n := by
    rcases le_total (|f y|) 1 with h | h
    · linarith [pow_nonneg (abs_nonneg (f y)) n]
    · linarith [le_self_pow₀ h (by omega : n ≠ 0)]
  calc |s y| * |f y| ≤ |s y| * (1 + |f y| ^ n) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    _ = |s y| + |s y| * |f y| ^ n := by ring
    _ ≤ B * (1 + ‖y‖) ^ (-(4:ℝ)) + B * |f y| ^ n :=
        add_le_add (hs' y) (mul_le_mul_of_nonneg_right (hsb y) (by positivity))

theorem weak_vector {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (j : Fin 3)
    (hvm : AEStronglyMeasurable v volume) (h6 : MemLp v 6 volume)
    (hGm : AEStronglyMeasurable G volume) (hG : Integrable (fun y => entrySq (G y)))
    (hw : IsWeakGradientOf v G) {Φ : Space → Space} (hΦ : ContDiff ℝ ∞ Φ) {B : ℝ}
    (hB : ∀ y, (1 + ‖y‖) ^ 4 * ‖Φ y‖ ≤ B) (hB' : ∀ y, (1 + ‖y‖) ^ 4 * ‖fderiv ℝ Φ y‖ ≤ B) :
    ∫ y, inner ℝ (v y) (fderiv ℝ Φ y (unitVector j)) = -∫ y, inner ℝ (G y (unitVector j)) (Φ y) := by
  have hcol : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hGm.prodMk aestronglyMeasurable_const)
  have hG2 : Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) := by
    refine hG.mono' (hcol.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold entrySq
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  have hGL : MemLp (fun y => G y (unitVector j)) 2 volume := (memLp_two_iff_integrable_sq_norm hcol).2 hG2
  have hv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    have := h6.integrable_norm_pow (p := 6) (by norm_num)
    simpa using this
  have hvl : LocallyIntegrable v volume := h6.locallyIntegrable (by norm_num)
  have hGl : LocallyIntegrable (fun y => G y (unitVector j)) volume := hGL.locallyIntegrable (by norm_num)
  have hproj : ∀ k : Fin 3, Continuous (fun z : Space => z k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).continuous
  have hvk : ∀ k : Fin 3, AEStronglyMeasurable (fun y => v y k) volume := fun k =>
    (hproj k).comp_aestronglyMeasurable hvm
  have hGk : ∀ k : Fin 3, AEStronglyMeasurable (fun y => G y (unitVector j) k) volume := fun k =>
    (hproj k).comp_aestronglyMeasurable hcol
  have hvk6 : ∀ k : Fin 3, Integrable (fun y => |v y k| ^ 6) := fun k =>
    hv6.mono' ((hvk k).norm.pow 6) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using PiLp.norm_apply_le (v y) k) 6)
  have hGk2 : ∀ k : Fin 3, Integrable (fun y => |G y (unitVector j) k| ^ 2) := fun k =>
    hG2.mono' ((hGk k).norm.pow 2) (ae_of_all _ fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa using PiLp.norm_apply_le (G y (unitVector j)) k) 2)
  have hΦk : ∀ k : Fin 3, ContDiff ℝ ∞ (fun y => Φ y k) := fun k =>
    (EuclideanSpace.proj k : Space →L[ℝ] ℝ).contDiff.comp hΦ
  have hΦd : Differentiable ℝ Φ := hΦ.differentiable (by simp)
  have hBk : ∀ k y, (1 + ‖y‖) ^ 4 * |Φ y k| ≤ B := fun k y =>
    (mul_le_mul_of_nonneg_left (by simpa using PiLp.norm_apply_le (Φ y) k) (by positivity)).trans (hB y)
  have hBk' : ∀ k y, (1 + ‖y‖) ^ 4 * |fderiv ℝ (fun y => Φ y k) y (unitVector j)| ≤ B := by
    intro k y
    rw [coord_fderiv hΦd]
    have h1 : |fderiv ℝ Φ y (unitVector j) k| ≤ ‖fderiv ℝ Φ y‖ := by
      refine (by simpa using PiLp.norm_apply_le (fderiv ℝ Φ y (unitVector j)) k : _ ≤ _).trans ?_
      have := (fderiv ℝ Φ y).le_opNorm (unitVector j)
      simpa [unitVector] using this
    exact (mul_le_mul_of_nonneg_left h1 (by positivity)).trans (hB' y)
  have hcd : ∀ k : Fin 3, Continuous (fun y => fderiv ℝ (fun y => Φ y k) y (unitVector j)) := fun k =>
    ((hΦk k).continuous_fderiv (by simp)).clm_apply continuous_const
  have key : ∀ k : Fin 3, ∫ y, fderiv ℝ (fun y => Φ y k) y (unitVector j) * v y k =
      -∫ y, Φ y k * G y (unitVector j) k := fun k =>
    weak_component j k hvl hGl hw (hΦk k)
      (decay_mul_integrable (hcd k) (hBk' k) (hvk k) (by norm_num) (hvk6 k))
      (decay_mul_integrable (hΦk k).continuous (hBk k) (hvk k) (by norm_num) (hvk6 k))
      (decay_mul_integrable (hΦk k).continuous (hBk k) (hGk k) (by norm_num) (hGk2 k))
  have eL : ∀ y, inner ℝ (v y) (fderiv ℝ Φ y (unitVector j)) =
      ∑ k : Fin 3, fderiv ℝ (fun y => Φ y k) y (unitVector j) * v y k := by
    intro y
    simp only [coord_fderiv hΦd, PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  have eR : ∀ y, inner ℝ (G y (unitVector j)) (Φ y) = ∑ k : Fin 3, Φ y k * G y (unitVector j) k := by
    intro y
    simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
  simp only [eL, eR]
  rw [integral_finsetSum _ (fun k _ => decay_mul_integrable (hcd k) (hBk' k) (hvk k) (by norm_num) (hvk6 k)),
    integral_finsetSum _ (fun k _ => decay_mul_integrable (hΦk k).continuous (hBk k) (hGk k) (by norm_num) (hGk2 k)),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun k _ => key k

theorem inner_decay_integrable {f X : Space → Space} (hX : Continuous X) {B : ℝ}
    (hB : ∀ y, (1 + ‖y‖) ^ 4 * ‖X y‖ ≤ B) (hf : AEStronglyMeasurable f volume) {n : ℕ} (hn : 1 ≤ n)
    (hfn : Integrable (fun y => ‖f y‖ ^ n)) : Integrable (fun y => inner ℝ (f y) (X y)) := by
  have h := decay_mul_integrable (s := fun y => ‖X y‖) (f := fun y => ‖f y‖) hX.norm
    (B := B) (fun y => by simpa using hB y) hf.norm hn (by simpa using hfn)
  refine h.mono' (hf.inner hX.aestronglyMeasurable) (ae_of_all _ fun y => ?_)
  rw [Real.norm_eq_abs, mul_comm]
  exact abs_real_inner_le_norm _ _

theorem weighted_pair {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (j : Fin 3)
    (hvm : AEStronglyMeasurable v volume) (h6 : MemLp v 6 volume)
    (hGm : AEStronglyMeasurable G volume) (hG : Integrable (fun y => entrySq (G y)))
    (hw : IsWeakGradientOf v G) (ℓ : Space →L[ℝ] ℝ) (S : 𝓢(Space, Space)) {B : ℝ}
    (hS0 : ∀ y, (1 + ‖y‖) ^ 5 * ‖S y‖ ≤ B) (hS1 : ∀ y, (1 + ‖y‖) ^ 5 * ‖fderiv ℝ S y‖ ≤ B) :
    Integrable (fun y => inner ℝ (G y (unitVector j)) (ℓ y • S y)) ∧
    Integrable (fun y => inner ℝ (v y) (ℓ (unitVector j) • S y + ℓ y • fderiv ℝ S y (unitVector j))) ∧
    ∫ y, inner ℝ (v y) (ℓ (unitVector j) • S y + ℓ y • fderiv ℝ S y (unitVector j)) =
      -∫ y, inner ℝ (G y (unitVector j)) (ℓ y • S y) := by
  have hSs : ContDiff ℝ ∞ (⇑S) := S.smooth ⊤
  have hΦ : ContDiff ℝ ∞ (fun y => ℓ y • S y) := ℓ.contDiff.smul hSs
  have hder : ∀ y, fderiv ℝ (fun y => ℓ y • S y) y = ℓ y • fderiv ℝ S y + ℓ.smulRight (S y) := fun y =>
    (ℓ.hasFDerivAt.smul (S.differentiableAt.hasFDerivAt)).fderiv
  have hB0 : 0 ≤ B := (mul_nonneg (by positivity) (norm_nonneg _)).trans (hS0 0)
  have hp1 : ∀ y : Space, ‖y‖ ≤ 1 + ‖y‖ := fun y => by linarith
  have hpow : ∀ y : Space, (1 + ‖y‖) ^ 4 * (1 + ‖y‖) = (1 + ‖y‖) ^ 5 := fun y => by ring
  have bΦ : ∀ y, (1 + ‖y‖) ^ 4 * ‖ℓ y • S y‖ ≤ ‖ℓ‖ * B := by
    intro y
    rw [norm_smul, Real.norm_eq_abs]
    have h1 : |ℓ y| ≤ ‖ℓ‖ * (1 + ‖y‖) := by
      have := ℓ.le_opNorm y
      rw [Real.norm_eq_abs] at this
      exact this.trans (mul_le_mul_of_nonneg_left (hp1 y) (norm_nonneg _))
    calc (1 + ‖y‖) ^ 4 * (|ℓ y| * ‖S y‖) ≤ (1 + ‖y‖) ^ 4 * ((‖ℓ‖ * (1 + ‖y‖)) * ‖S y‖) := by
          gcongr
      _ = ‖ℓ‖ * ((1 + ‖y‖) ^ 5 * ‖S y‖) := by rw [← hpow]; ring
      _ ≤ ‖ℓ‖ * B := mul_le_mul_of_nonneg_left (hS0 y) (norm_nonneg _)
  have bD : ∀ y, (1 + ‖y‖) ^ 4 * ‖fderiv ℝ (fun y => ℓ y • S y) y‖ ≤ ‖ℓ‖ * B + ‖ℓ‖ * B := by
    intro y
    rw [hder]
    have h1 : ‖ℓ y • fderiv ℝ S y + ℓ.smulRight (S y)‖ ≤ ‖ℓ‖ * (1 + ‖y‖) * ‖fderiv ℝ S y‖ + ‖ℓ‖ * ‖S y‖ := by
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · rw [norm_smul, Real.norm_eq_abs]
        have := ℓ.le_opNorm y
        rw [Real.norm_eq_abs] at this
        exact mul_le_mul_of_nonneg_right (this.trans (mul_le_mul_of_nonneg_left (hp1 y) (norm_nonneg _)))
          (norm_nonneg _)
      · rw [ContinuousLinearMap.norm_smulRight_apply]
    have h2 : (1 + ‖y‖) ^ 4 * ‖S y‖ ≤ B := by
      refine le_trans ?_ (hS0 y)
      rw [← hpow]
      have : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      have hq : 0 ≤ (1 + ‖y‖) ^ 4 * ‖S y‖ := by positivity
      calc (1 + ‖y‖) ^ 4 * ‖S y‖ = (1 + ‖y‖) ^ 4 * ‖S y‖ * 1 := by ring
        _ ≤ (1 + ‖y‖) ^ 4 * ‖S y‖ * (1 + ‖y‖) := mul_le_mul_of_nonneg_left this hq
        _ = (1 + ‖y‖) ^ 4 * (1 + ‖y‖) * ‖S y‖ := by ring
    calc (1 + ‖y‖) ^ 4 * ‖ℓ y • fderiv ℝ S y + ℓ.smulRight (S y)‖
        ≤ (1 + ‖y‖) ^ 4 * (‖ℓ‖ * (1 + ‖y‖) * ‖fderiv ℝ S y‖ + ‖ℓ‖ * ‖S y‖) :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ‖ℓ‖ * ((1 + ‖y‖) ^ 5 * ‖fderiv ℝ S y‖) + ‖ℓ‖ * ((1 + ‖y‖) ^ 4 * ‖S y‖) := by
          rw [← hpow]; ring
      _ ≤ ‖ℓ‖ * B + ‖ℓ‖ * B := add_le_add (mul_le_mul_of_nonneg_left (hS1 y) (norm_nonneg _))
          (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
  have bΦ' : ∀ y, (1 + ‖y‖) ^ 4 * ‖ℓ y • S y‖ ≤ ‖ℓ‖ * B + ‖ℓ‖ * B := fun y =>
    (bΦ y).trans (by nlinarith [norm_nonneg ℓ])
  have key := weak_vector j hvm h6 hGm hG hw hΦ bΦ' bD
  have happ : ∀ y, fderiv ℝ (fun y => ℓ y • S y) y (unitVector j) =
      ℓ (unitVector j) • S y + ℓ y • fderiv ℝ S y (unitVector j) := by
    intro y
    rw [hder]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
    abel
  simp only [happ] at key
  have hcol : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hGm.prodMk aestronglyMeasurable_const)
  have hG2 : Integrable (fun y => ‖G y (unitVector j)‖ ^ 2) := by
    refine hG.mono' (hcol.norm.pow 2) (ae_of_all _ fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    unfold entrySq
    exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity)
      (Finset.mem_univ j)
  have hv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    have := h6.integrable_norm_pow (p := 6) (by norm_num)
    simpa using this
  have hc1 : Continuous (fun y => fderiv ℝ S y (unitVector j)) :=
    (hSs.continuous_fderiv (by simp)).clm_apply continuous_const
  have hcD : Continuous (fun y => ℓ (unitVector j) • S y + ℓ y • fderiv ℝ S y (unitVector j)) := by
    refine Continuous.add ?_ ?_
    · exact (continuous_const : Continuous (fun _ : Space => ℓ (unitVector j))).smul S.continuous
    · exact ℓ.continuous.smul hc1
  have bD' : ∀ y, (1 + ‖y‖) ^ 4 * ‖ℓ (unitVector j) • S y + ℓ y • fderiv ℝ S y (unitVector j)‖ ≤
      (‖ℓ‖ * B + ‖ℓ‖ * B) := by
    intro y
    rw [← happ]
    refine le_trans ?_ (bD y)
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have := (fderiv ℝ (fun y => ℓ y • S y) y).le_opNorm (unitVector j)
    simpa [unitVector] using this
  exact ⟨inner_decay_integrable (ℓ.continuous.smul S.continuous) bΦ' hcol (by norm_num) hG2,
    inner_decay_integrable hcD bD' hvm (by norm_num) hv6, key⟩

theorem int_add {f g : Space → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun y => f y + g y) := hf.add hg

theorem int_cmul {f : Space → ℝ} (c : ℝ) (hf : Integrable f) : Integrable (fun y => c * f y) :=
  hf.const_mul c

theorem int_sub {f g : Space → ℝ} (hf : Integrable f) (hg : Integrable g) :
    Integrable (fun y => f y - g y) := hf.sub hg

theorem int_fsum {f : Fin 3 → Space → ℝ} (hf : ∀ j, Integrable (f j)) :
    Integrable (fun y => ∑ j : Fin 3, f j y) := integrable_finsetSum _ fun j _ => hf j

theorem axialTurn_add (x z : Space) : axialTurn (x + z) = axialTurn x + axialTurn z := by
  ext i
  fin_cases i <;> simp [axialTurn] <;> ring

theorem axialTurn_smul (c : ℝ) (x : Space) : axialTurn (c • x) = c • axialTurn x := by
  ext i
  fin_cases i <;> simp [axialTurn]

def turnCLM : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := axialTurn
      map_add' := axialTurn_add
      map_smul' := axialTurn_smul }

theorem turnCLM_apply (x : Space) : turnCLM x = axialTurn x := rfl

theorem norm_axialTurn_le' (z : Space) : ‖axialTurn z‖ ≤ ‖z‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  apply Real.sqrt_le_sqrt
  simp [axialTurn, Fin.sum_univ_three]
  nlinarith [sq_nonneg (z 2)]

theorem inner_axialTurn (x z : Space) : inner ℝ (axialTurn x) z = -inner ℝ x (axialTurn z) := by
  simp [axialTurn, PiLp.inner_apply, Fin.sum_univ_three]

theorem axialTurn_unit_self (j : Fin 3) : axialTurn (unitVector j) j = 0 := by
  fin_cases j <;> simp [axialTurn, unitVector]

theorem expand_apply (L : Space →L[ℝ] Space) (w : Space) :
    L w = ∑ j : Fin 3, w j • L (unitVector j) := by
  have hw : w = ∑ j : Fin 3, w j • unitVector j := by
    have := (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr w
    simpa [unitVector] using this.symm
  conv_lhs => rw [hw]
  rw [map_sum]
  simp only [map_smul]

end HeldWeakProfilePartsInternal

open HeldWeakProfilePartsInternal

theorem niceSolenoidal : NiceSolenoidalStatement := by
  intro φ hφ
  obtain ⟨m, hm, rfl⟩ := hφ
  have hS := FracInternal.NiceField.fieldS_coe hm
  refine ⟨?_, ?_⟩
  · rw [← hS]
    exact (FracInternal.NiceField.fieldS hm).memLp 2 volume
  intro ψ hψ
  set S := FracInternal.NiceField.fieldS hm
  rw [← hS]
  have hSd : Differentiable ℝ (⇑S) := S.differentiable
  have hSc : ∀ i : Fin 3, ContDiff ℝ 1 (fun x => S x i) := fun i =>
    (EuclideanSpace.proj i : Space →L[ℝ] ℝ).contDiff.comp ((S.smooth ⊤).of_le (by simp))
  have hψc : Continuous ψ := hψ.1.continuous
  have int1 : ∀ i : Fin 3, Integrable (fun y => fderiv ℝ ψ y (unitVector i) • S y i) := by
    intro i
    exact (((hψ.1.continuous_fderiv (by simp)).clm_apply continuous_const).smul
      (hSc i).continuous).integrable_of_hasCompactSupport
      ((hψ.2.fderiv_apply (𝕜 := ℝ) (unitVector i)).smul_right)
  have int2 : ∀ i : Fin 3, Integrable (fun y => ψ y • fderiv ℝ (fun x => S x i) y (unitVector i)) := by
    intro i
    exact (hψc.smul (((hSc i).continuous_fderiv one_ne_zero).clm_apply continuous_const)).integrable_of_hasCompactSupport
      (hψ.2.smul_right)
  simp only [inner_gradient]
  rw [integral_finsetSum _ (fun i _ => int1 i)]
  simp only [fun i => test_ibp hψ (hSc i) (unitVector i)]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => int2 i), neg_eq_zero]
  refine integral_eq_zero_of_ae (ae_of_all _ fun y => ?_)
  simp only [smul_eq_mul, ← Finset.mul_sum, coord_fderiv hSd]
  have hdiv : ∑ i : Fin 3, (fderiv ℝ (⇑S) y (unitVector i)) i = 0 :=
    FracInternal.NiceField.divergence_fieldS hm y
  simp [hdiv]

theorem profileEmbedData : ProfileEmbedDataStatement := by
  intro α _ _ k N d hd p hp
  have hc := hd.profile_smooth p hp
  have hgc : Continuous (d.gradProfile p) := hc.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hd.profile_bounds
  have hb1 := fun y => (hC p hp y).1
  have hb2 := fun y => (hC p hp y).2.1
  have hC0 : 0 ≤ C := by
    have h := hb1 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  refine ⟨hc.continuous.aestronglyMeasurable, ?_, hgc.aestronglyMeasurable, ?_, ?_, ?_⟩
  · have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6:ℝ))) :=
      integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; norm_num)
    rw [← integrable_norm_rpow_iff hc.continuous.aestronglyMeasurable (by norm_num) (by norm_num)]
    have h6 : ((6 : ℝ≥0∞).toReal) = (6:ℝ) := by norm_num
    rw [h6]
    refine (hi.const_mul (C ^ (6:ℝ))).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact (hc.continuous.norm.rpow_const (fun _ => Or.inr (by norm_num))).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      have hpos : 0 < 1 + ‖y‖ := by positivity
      calc ‖d.profile p y‖ ^ (6:ℝ) ≤ (C * (1 + ‖y‖) ^ (-(1:ℝ))) ^ (6:ℝ) :=
            Real.rpow_le_rpow (norm_nonneg _) (hb1 y) (by norm_num)
        _ = C ^ (6:ℝ) * (1 + ‖y‖) ^ (-(6:ℝ)) := by
            rw [Real.mul_rpow hC0 (Real.rpow_nonneg hpos.le _), ← Real.rpow_mul hpos.le]
            norm_num
  · have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(4:ℝ))) :=
      integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; norm_num)
    refine (hi.const_mul (3 * C ^ 2)).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact (continuous_finsetSum _ fun i _ =>
        ((hgc.clm_apply continuous_const).norm.pow 2)).aestronglyMeasurable
    · have hpos : 0 < 1 + ‖y‖ := by positivity
      have hG : ‖d.gradProfile p y‖ ^ 2 ≤ C ^ 2 * (1 + ‖y‖) ^ (-(4:ℝ)) := by
        calc ‖d.gradProfile p y‖ ^ 2 ≤ (C * (1 + ‖y‖) ^ (-(2:ℝ))) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (hb2 y) 2
          _ = C ^ 2 * (1 + ‖y‖) ^ (-(4:ℝ)) := by
              rw [mul_pow, ← Real.rpow_natCast ((1 + ‖y‖) ^ (-(2:ℝ))), ← Real.rpow_mul hpos.le]
              norm_num
      have he : ∀ i : Fin 3, ‖d.gradProfile p y (unitVector i)‖ ^ 2 ≤ ‖d.gradProfile p y‖ ^ 2 := by
        intro i
        have h1 := (d.gradProfile p y).le_opNorm (unitVector i)
        have hu : ‖unitVector i‖ = 1 := by simp [unitVector]
        rw [hu, mul_one] at h1
        exact pow_le_pow_left₀ (norm_nonneg _) h1 2
      unfold entrySq
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
      calc ∑ i : Fin 3, ‖d.gradProfile p y (unitVector i)‖ ^ 2 ≤ ∑ _i : Fin 3, ‖d.gradProfile p y‖ ^ 2 :=
            Finset.sum_le_sum fun i _ => he i
        _ = 3 * ‖d.gradProfile p y‖ ^ 2 := by simp
        _ ≤ 3 * C ^ 2 * (1 + ‖y‖) ^ (-(4:ℝ)) := by
            rw [mul_assoc]
            exact mul_le_mul_of_nonneg_left hG (by norm_num)
  · intro φ hφ j
    exact test_ibp hφ hc (unitVector j)
  · refine ae_of_all _ fun y => ?_
    have h := hd.profile_divergence p hp y
    unfold divergenceAt at h
    simpa [unitVector, EuclideanSpace.inner_single_right, FracCertData.gradProfile] using h

theorem heldQuadraticL2_of (q : QuadraticSquareIntegrableStatement) : HeldQuadraticL2Statement := by
  intro α _ _ k N d hd p hp v G H hs
  have hc := hd.profile_smooth p hp
  have hgc : Continuous (d.gradProfile p) := hc.continuous_fderiv one_ne_zero
  obtain ⟨C, hC⟩ := hd.profile_bounds
  have hb1 := fun y => (hC p hp y).1
  have hb2 := fun y => (hC p hp y).2.1
  have hC0 : 0 ≤ C := by
    have h := hb1 0
    simp only [norm_zero, add_zero, Real.one_rpow, mul_one] at h
    exact (norm_nonneg _).trans h
  have hpos : ∀ y : Space, 0 < 1 + ‖y‖ := fun y => by positivity
  have hb1' : ∀ y, ‖d.profile p y‖ ≤ C := fun y => (hb1 y).trans
    (mul_le_of_le_one_right hC0 (Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y]) (by norm_num)))
  have i6 : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(6:ℝ))) :=
    integrable_one_add_norm (by simp only [finrank_euclideanSpace_fin, Nat.cast_ofNat]; norm_num)
  have hvm := hs.measurable_velocity
  have app : ∀ {L : Space → (Space →L[ℝ] Space)} {w : Space → Space}, AEStronglyMeasurable L volume →
      AEStronglyMeasurable w volume → AEStronglyMeasurable (fun y => L y (w y)) volume :=
    fun hL hw => isBoundedBilinearMap_apply.continuous.comp_aestronglyMeasurable (hL.prodMk hw)
  have T0 := q _ v G H hs
  have T1 : MemLp (fun y => d.gradProfile p y (d.profile p y)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm (app hgc.aestronglyMeasurable hc.continuous.aestronglyMeasurable)).2 ?_
    refine (i6.const_mul (C ^ 4)).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((isBoundedBilinearMap_apply.continuous.comp (hgc.prodMk hc.continuous)).norm.pow 2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have e1 := (d.gradProfile p y).le_opNorm (d.profile p y)
      have e2 : ‖d.gradProfile p y‖ * ‖d.profile p y‖ ≤ (C * (1 + ‖y‖) ^ (-(2:ℝ))) * (C * (1 + ‖y‖) ^ (-(1:ℝ))) :=
        mul_le_mul (hb2 y) (hb1 y) (norm_nonneg _) (by positivity)
      have e3 : ((C * (1 + ‖y‖) ^ (-(2:ℝ))) * (C * (1 + ‖y‖) ^ (-(1:ℝ)))) ^ 2 = C ^ 4 * (1 + ‖y‖) ^ (-(6:ℝ)) := by
        rw [show ((C * (1 + ‖y‖) ^ (-(2:ℝ))) * (C * (1 + ‖y‖) ^ (-(1:ℝ)))) ^ 2 =
          C ^ 4 * ((1 + ‖y‖) ^ (-(2:ℝ)) * (1 + ‖y‖) ^ (-(1:ℝ))) ^ 2 by ring]
        rw [← Real.rpow_add (hpos y), ← Real.rpow_natCast ((1 + ‖y‖) ^ (-(2:ℝ) + -(1:ℝ))) 2,
          ← Real.rpow_mul (hpos y).le]
        norm_num
      rw [← e3]
      exact pow_le_pow_left₀ (norm_nonneg _) (e1.trans e2) 2
  have T2 : MemLp (fun y => d.gradProfile p y (v y)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm (app hgc.aestronglyMeasurable hvm)).2 ?_
    have hv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
      have := hs.velocity_six.integrable_norm_pow (p := 6) (by norm_num)
      simpa using this
    refine ((i6.const_mul (C ^ 2)).add (hv6.const_mul (C ^ 2))).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((app hgc.aestronglyMeasurable hvm).norm.pow 2)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have e1 := (d.gradProfile p y).le_opNorm (v y)
      set t := (1 + ‖y‖) ^ (-(2:ℝ)) with ht
      have ht0 : 0 ≤ t := by positivity
      have e2 : ‖d.gradProfile p y (v y)‖ ^ 2 ≤ C ^ 2 * (t ^ 2 * (‖v y‖ ^ 2)) := by
        calc ‖d.gradProfile p y (v y)‖ ^ 2 ≤ (C * t * ‖v y‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (e1.trans (mul_le_mul_of_nonneg_right (hb2 y) (norm_nonneg _))) 2
          _ = C ^ 2 * (t ^ 2 * (‖v y‖ ^ 2)) := by ring
      have e3 : t ^ 3 = (1 + ‖y‖) ^ (-(6:ℝ)) := by
        rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul (hpos y).le]
        norm_num
      have e4 := weight_split t (‖v y‖ ^ 2) ht0 (by positivity)
      rw [e3] at e4
      calc ‖d.gradProfile p y (v y)‖ ^ 2 ≤ C ^ 2 * (t ^ 2 * (‖v y‖ ^ 2)) := e2
        _ ≤ C ^ 2 * ((1 + ‖y‖) ^ (-(6:ℝ)) + (‖v y‖ ^ 2) ^ 3) := mul_le_mul_of_nonneg_left e4 (by positivity)
        _ = C ^ 2 * (1 + ‖y‖) ^ (-(6:ℝ)) + C ^ 2 * ‖v y‖ ^ 6 := by ring
  have T3 : MemLp (fun y => G y (d.profile p y)) 2 volume := by
    refine (memLp_two_iff_integrable_sq_norm (app hs.measurable_gradient hc.continuous.aestronglyMeasurable)).2 ?_
    refine (hs.gradient_two.const_mul (3 * C ^ 2)).mono' ?_ (ae_of_all _ fun y => ?_)
    · exact ((app hs.measurable_gradient hc.continuous.aestronglyMeasurable).norm.pow 2)
    · rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have e1 := norm_apply_sq_le (G y) (d.profile p y)
      have e2 : ‖d.profile p y‖ ^ 2 ≤ C ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hb1' y) 2
      have e3 : 0 ≤ entrySq (G y) := Finset.sum_nonneg fun i _ => by positivity
      nlinarith
  have hsum := ((T1.add T2).add T3).add T0
  refine hsum.congr_norm ?_ ?_
  · exact app (hgc.aestronglyMeasurable.add hs.measurable_gradient) (hc.continuous.aestronglyMeasurable.add hvm)
  · refine ae_of_all _ fun y => ?_
    congr 1
    simp only [Pi.add_apply, map_add, ContinuousLinearMap.add_apply]
    abel

theorem driftNicePairing : DriftNicePairingStatement := by
  intro α a _ v G hvm h6 hGm hG hw φ hφ
  obtain ⟨S, rfl⟩ := Freq.Internal.NicePairing.rapid_of_nice hφ
  set B := 2 ^ 5 * (Finset.Iic ((5, 1) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S with hBdef
  have hS0 : ∀ y, (1 + ‖y‖) ^ 5 * ‖S y‖ ≤ B := fun y => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5, 1) : ℕ × ℕ)) (k := 5) (n := 0)
      le_rfl (by norm_num) S y
    rwa [norm_iteratedFDeriv_zero] at this
  have hS1 : ∀ y, (1 + ‖y‖) ^ 5 * ‖fderiv ℝ S y‖ ≤ B := fun y => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((5, 1) : ℕ × ℕ)) (k := 5) (n := 1)
      le_rfl le_rfl S y
    rwa [norm_iteratedFDeriv_one] at this
  have hS4 : ∀ y, (1 + ‖y‖) ^ 4 * ‖S y‖ ≤ B := by
    intro y
    refine le_trans ?_ (hS0 y)
    have h1 : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    have hq : 0 ≤ (1 + ‖y‖) ^ 4 * ‖S y‖ := by positivity
    calc (1 + ‖y‖) ^ 4 * ‖S y‖ = (1 + ‖y‖) ^ 4 * ‖S y‖ * 1 := by ring
      _ ≤ (1 + ‖y‖) ^ 4 * ‖S y‖ * (1 + ‖y‖) := mul_le_mul_of_nonneg_left h1 hq
      _ = (1 + ‖y‖) ^ 5 * ‖S y‖ := by ring
  have hJS4 : ∀ y, (1 + ‖y‖) ^ 4 * ‖axialTurn (S y)‖ ≤ B := fun y =>
    (mul_le_mul_of_nonneg_left (norm_axialTurn_le' _) (by positivity)).trans (hS4 y)
  have hv6 : Integrable (fun y => ‖v y‖ ^ 6) := by
    have := h6.integrable_norm_pow (p := 6) (by norm_num)
    simpa using this
  have i0 : Integrable (fun y => inner ℝ (v y) (S y)) :=
    inner_decay_integrable S.continuous hS4 hvm (by norm_num) hv6
  have ic : Integrable (fun y => inner ℝ (v y) (axialTurn (S y))) :=
    inner_decay_integrable (turnCLM.continuous.comp S.continuous) hJS4 hvm (by norm_num) hv6
  have P1 := fun j => weighted_pair j hvm h6 hGm hG hw (EuclideanSpace.proj j : Space →L[ℝ] ℝ) S hS0 hS1
  have P2 := fun j => weighted_pair j hvm h6 hGm hG hw
    ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) S hS0 hS1
  set β := 1 / (2 * α) with hβ
  have eL : ∀ y, inner ℝ (driftField α a v G y) (S y) =
      (1 - β) * inner ℝ (v y) (S y)
      + β * ∑ j : Fin 3, inner ℝ (G y (unitVector j)) ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) y • S y)
      + a * ∑ j : Fin 3, inner ℝ (G y (unitVector j))
          (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) y • S y)
      + a * inner ℝ (v y) (axialTurn (S y)) := by
    intro y
    have h1 : inner ℝ (G y y) (S y) = ∑ j : Fin 3, inner ℝ (G y (unitVector j))
        ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) y • S y) := by
      rw [← Freq.Internal.NicePairing.sum_coord_inner (G y) y (S y)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_right]
      rfl
    have h2 : inner ℝ (G y (axialTurn y)) (S y) = ∑ j : Fin 3, inner ℝ (G y (unitVector j))
        (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) y • S y) := by
      rw [← Freq.Internal.NicePairing.sum_coord_inner (G y) (axialTurn y) (S y)]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [real_inner_smul_right]
      rfl
    simp only [driftField, inner_add_left, inner_sub_left, real_inner_smul_left, h1, h2, inner_axialTurn]
    ring
  have eR : ∀ y, inner ℝ (v y) (FracCert.driftAdjoint α a S y) =
      (1 - β) * inner ℝ (v y) (S y)
      - β * ∑ j : Fin 3, inner ℝ (v y) ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) (unitVector j) • S y
          + (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y • fderiv ℝ S y (unitVector j))
      - a * ∑ j : Fin 3, inner ℝ (v y) (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) (unitVector j) • S y
          + ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) y • fderiv ℝ S y (unitVector j))
      + a * inner ℝ (v y) (axialTurn (S y)) := by
    intro y
    have k1 : ∑ j : Fin 3, inner ℝ (v y) ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) (unitVector j) • S y
          + (EuclideanSpace.proj j : Space →L[ℝ] ℝ) y • fderiv ℝ S y (unitVector j)) =
        3 * inner ℝ (v y) (S y) + inner ℝ (v y) (fderiv ℝ S y y) := by
      rw [expand_apply (fderiv ℝ S y) y, inner_sum]
      simp only [inner_add_right, real_inner_smul_right, Finset.sum_add_distrib]
      simp [unitVector, Fin.sum_univ_three]
    have k2 : ∑ j : Fin 3, inner ℝ (v y) (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) (unitVector j) • S y
          + ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) y • fderiv ℝ S y (unitVector j)) =
        inner ℝ (v y) (fderiv ℝ S y (axialTurn y)) := by
      rw [expand_apply (fderiv ℝ S y) (axialTurn y), inner_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have e0 : (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (axialTurn (unitVector j)) = 0 := axialTurn_unit_self j
      have e1 : (EuclideanSpace.proj j : Space →L[ℝ] ℝ) (axialTurn y) = axialTurn y j := rfl
      simp only [ContinuousLinearMap.comp_apply, turnCLM_apply]
      rw [e0, e1, zero_smul, zero_add]
    rw [k1, k2]
    simp only [FracCert.driftAdjoint, inner_sub_right, real_inner_smul_right]
    ring
  have I1 : Integrable (fun y => ∑ j : Fin 3, inner ℝ (G y (unitVector j))
      ((EuclideanSpace.proj j : Space →L[ℝ] ℝ) y • S y)) := int_fsum fun j => (P1 j).1
  have I2 : Integrable (fun y => ∑ j : Fin 3, inner ℝ (G y (unitVector j))
      (((EuclideanSpace.proj j : Space →L[ℝ] ℝ).comp turnCLM) y • S y)) := int_fsum fun j => (P2 j).1
  have J1 := int_fsum fun j => (P1 j).2.1
  have J2 := int_fsum fun j => (P2 j).2.1
  refine ⟨(int_add (int_sub (int_sub (int_cmul _ i0) (int_cmul β J1)) (int_cmul a J2)) (int_cmul a ic)).congr
    (Filter.Eventually.of_forall fun y => (eR y).symm), ?_⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall eL), integral_congr_ae (Filter.Eventually.of_forall eR)]
  rw [integral_add (int_add (int_add (int_cmul _ i0) (int_cmul β I1)) (int_cmul a I2)) (int_cmul a ic),
    integral_add (int_add (int_cmul _ i0) (int_cmul β I1)) (int_cmul a I2),
    integral_add (int_cmul _ i0) (int_cmul β I1),
    integral_add (int_sub (int_sub (int_cmul _ i0) (int_cmul β J1)) (int_cmul a J2)) (int_cmul a ic),
    integral_sub (int_sub (int_cmul _ i0) (int_cmul β J1)) (int_cmul a J2),
    integral_sub (int_cmul _ i0) (int_cmul β J1)]
  simp only [integral_const_mul]
  rw [integral_finsetSum _ (fun j _ => (P1 j).1), integral_finsetSum _ (fun j _ => (P2 j).1),
    integral_finsetSum _ (fun j _ => (P1 j).2.1), integral_finsetSum _ (fun j _ => (P2 j).2.1)]
  simp only [fun j => (P1 j).2.2, fun j => (P2 j).2.2, Finset.sum_neg_distrib]
  ring

theorem weakPowerNice : WeakPowerNiceStatement := by
  intro α hα1 hα2 v P hvm hv6 hW φ hφ
  have hprops := Freq.niceFieldProps α hα1 (by linarith) φ hφ
  obtain ⟨ψ, hψ⟩ := hprops.1
  obtain ⟨S, hS⟩ := (Freq.niceFieldProps α hα1 (by linarith) _ hprops.2.2.2.1).1
  have hS4 : ∀ y, (1 + ‖y‖) ^ 4 * ‖S y‖ ≤
      2 ^ 4 * (Finset.Iic ((4, 0) : ℕ × ℕ)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) S := fun y => by
    have := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((4, 0) : ℕ × ℕ)) (k := 4) (n := 0)
      le_rfl le_rfl S y
    rwa [norm_iteratedFDeriv_zero] at this
  have hv6' : Integrable (fun y => ‖v y‖ ^ 6) := by
    have := hv6.integrable_norm_pow (p := 6) (by norm_num)
    simpa using this
  refine ⟨?_, ?_⟩
  · rw [← hS]
    exact inner_decay_integrable S.continuous hS4 hvm (by norm_num) hv6'
  · rw [← hψ]
    exact rapidWeakPower α hα1 (by linarith) v P hvm hv6 hW ψ

end SteadyCert

end Breakdown
