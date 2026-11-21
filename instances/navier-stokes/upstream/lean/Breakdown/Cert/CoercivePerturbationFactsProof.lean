import Breakdown.Cert.CoercivePerturbationFacts
import Breakdown.Cert.CoerciveBordered
import Breakdown.Cert.SliceFields
import Breakdown.Weak.SliceEmbedding
import Breakdown.Weak.PairingVelocity
import Breakdown.Weak.VelocityWeakGradient
import Breakdown.Weak.ZeroGradient
import Breakdown.Weak.GradientFreqTr

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.PerturbationFacts

def bump (n : ℕ) : ContDiffBump (0 : Space) :=
  ⟨1 / ((n : ℝ) + 1), 2 / ((n : ℝ) + 1), by positivity,
    div_lt_div_of_pos_right (by norm_num) (by positivity)⟩

def kernel (n : ℕ) : Space → ℝ := (bump n).normed volume

def convolve (κ f : Space → ℝ) : Space → ℝ :=
  convolution κ f (ContinuousLinearMap.lsmul ℝ ℝ) volume

def IsWeakPartial (f g : Space → ℝ) (k : Fin 3) : Prop :=
  ∀ φ, IsTestFunction φ → ∫ y, φ y * g y = -∫ y, fderiv ℝ φ y (unitVector k) * f y

theorem fderiv_convolve {κ f : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (hf : LocallyIntegrable f volume) (k : Fin 3) (y : Space) :
    fderiv ℝ (convolve κ f) y (unitVector k) =
      convolve (fun t => fderiv ℝ κ t (unitVector k)) f y := by
  have hd := hc.hasFDerivAt_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ)
    (hκ.of_le (by exact_mod_cast le_top)) hf y
  have hex := (hc.fderiv (𝕜 := ℝ)).convolutionExists_left
    ((ContinuousLinearMap.lsmul ℝ ℝ).precompL Space) (hκ.continuous_fderiv (by simp)) hf y
  unfold convolve
  rw [hd.fderiv, convolution_def, ContinuousLinearMap.integral_apply hex, convolution_def]
  simp

theorem convolve_partial_eq {κ f g : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    {k : Fin 3} (hw : IsWeakPartial f g k) (y : Space) :
    convolve (fun t => fderiv ℝ κ t (unitVector k)) f y = convolve κ g y := by
  unfold convolve
  rw [convolution_eq_swap, convolution_eq_swap]
  simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  have hψs : ContDiff ℝ ∞ (fun t => κ (y - t)) := hκ.comp (contDiff_const.sub contDiff_id)
  have hψc : HasCompactSupport (fun t => κ (y - t)) := hc.comp_homeomorph (Homeomorph.subLeft y)
  have hder : ∀ t, fderiv ℝ (fun t => κ (y - t)) t (unitVector k) =
      -fderiv ℝ κ (y - t) (unitVector k) := by
    intro t
    have h1 : HasFDerivAt (fun t => κ (y - t)) ((fderiv ℝ κ (y - t)).comp
        (-ContinuousLinearMap.id ℝ Space)) t :=
      ((hκ.differentiable (by simp)) (y - t)).hasFDerivAt.comp t ((hasFDerivAt_id t).const_sub y)
    rw [h1.fderiv]
    simp
  rw [hw _ ⟨hψs, hψc⟩]
  simp only [hder, neg_mul, integral_neg, neg_neg]

theorem sq_lintegral_mul_le {A B : Space → ℝ≥0∞} (hA : AEMeasurable A volume)
    (hB : AEMeasurable B volume) :
    (∫⁻ x, A x * B x) ^ 2 ≤ (∫⁻ x, A x) * ∫⁻ x, A x * B x ^ 2 := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (f := fun x => A x ^ (1 / 2 : ℝ)) (g := fun x => A x ^ (1 / 2 : ℝ) * B x) (hA.pow_const _)
    ((hA.pow_const _).mul hB)
  have e1 : ∀ x, A x ^ (1 / 2 : ℝ) * (A x ^ (1 / 2 : ℝ) * B x) = A x * B x := by
    intro x
    rw [← mul_assoc, ← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e2 : ∀ x, (A x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = A x := by
    intro x
    rw [← ENNReal.rpow_mul]
    norm_num
  have e3 : ∀ x, (A x ^ (1 / 2 : ℝ) * B x) ^ (2 : ℝ) = A x * B x ^ 2 := by
    intro x
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), e2, ENNReal.rpow_two]
  simp only [Pi.mul_apply, e1, e2, e3] at h
  calc (∫⁻ x, A x * B x) ^ 2
      ≤ ((∫⁻ x, A x) ^ (1 / 2 : ℝ) * (∫⁻ x, A x * B x ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by gcongr
    _ = (∫⁻ x, A x) * ∫⁻ x, A x * B x ^ 2 := by
        rw [mul_pow, ← ENNReal.rpow_two, ← ENNReal.rpow_two, ← ENNReal.rpow_mul, ← ENNReal.rpow_mul]
        norm_num

theorem lintegral_convolve_sq_le {κ f : Space → ℝ} (hκ : Continuous κ)
    (hf : AEStronglyMeasurable f volume) :
    ∫⁻ y, ENNReal.ofReal (convolve κ f y ^ 2) ≤
      (∫⁻ t, ‖κ t‖ₑ) ^ 2 * ∫⁻ y, ENNReal.ofReal (f y ^ 2) := by
  have hF : AEMeasurable (fun y => ENNReal.ofReal (f y ^ 2)) volume :=
    (hf.aemeasurable.pow_const 2).ennreal_ofReal
  have hsq : ∀ x : ℝ, ENNReal.ofReal (x ^ 2) = ‖x‖ₑ ^ 2 := by
    intro x
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]
  have hpt : ∀ y, ENNReal.ofReal (convolve κ f y ^ 2) ≤
      (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ t, ‖κ t‖ₑ * ENNReal.ofReal (f (y - t) ^ 2) := by
    intro y
    have h1 : ‖convolve κ f y‖ₑ ≤ ∫⁻ t, ‖κ t‖ₑ * ‖f (y - t)‖ₑ := by
      unfold convolve
      rw [convolution_def]
      refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
      simp only [ContinuousLinearMap.lsmul_apply, smul_eq_mul, enorm_mul]
    have hm : AEMeasurable (fun t => ‖f (y - t)‖ₑ) volume :=
      (hf.aemeasurable.enorm).comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left volume y)
    rw [hsq]
    calc ‖convolve κ f y‖ₑ ^ 2 ≤ (∫⁻ t, ‖κ t‖ₑ * ‖f (y - t)‖ₑ) ^ 2 := by gcongr
      _ ≤ (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ t, ‖κ t‖ₑ * ‖f (y - t)‖ₑ ^ 2 :=
          sq_lintegral_mul_le hκ.enorm.aemeasurable hm
      _ = (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ t, ‖κ t‖ₑ * ENNReal.ofReal (f (y - t) ^ 2) := by
          simp only [hsq]
  have hjoint : AEMeasurable (fun p : Space × Space => ‖κ p.2‖ₑ * ENNReal.ofReal (f (p.1 - p.2) ^ 2))
      (volume.prod volume) :=
    (hκ.enorm.measurable.comp measurable_snd).aemeasurable.mul
      (hF.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_of_right_invariant volume volume))
  calc ∫⁻ y, ENNReal.ofReal (convolve κ f y ^ 2)
      ≤ ∫⁻ y, (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ t, ‖κ t‖ₑ * ENNReal.ofReal (f (y - t) ^ 2) := lintegral_mono hpt
    _ = (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ y, ∫⁻ t, ‖κ t‖ₑ * ENNReal.ofReal (f (y - t) ^ 2) :=
        lintegral_const_mul'' _ hjoint.lintegral_prod_right'
    _ = (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ t, ∫⁻ y, ‖κ t‖ₑ * ENNReal.ofReal (f (y - t) ^ 2) := by
        rw [lintegral_lintegral_swap hjoint]
    _ = (∫⁻ t, ‖κ t‖ₑ) * ∫⁻ t, ‖κ t‖ₑ * ∫⁻ y, ENNReal.ofReal (f y ^ 2) := by
        congr 1
        refine lintegral_congr fun t => ?_
        have hm : AEMeasurable (fun y => ENNReal.ofReal (f (y - t) ^ 2)) volume :=
          hF.comp_quasiMeasurePreserving (measurePreserving_sub_right volume t).quasiMeasurePreserving
        rw [lintegral_const_mul'' _ hm]
        congr 1
        exact lintegral_sub_right_eq_self (fun y => ENNReal.ofReal (f y ^ 2)) t
    _ = (∫⁻ t, ‖κ t‖ₑ) ^ 2 * ∫⁻ y, ENNReal.ofReal (f y ^ 2) := by
        rw [lintegral_mul_const'' _ hκ.enorm.aemeasurable, sq, mul_assoc]

structure IsSliceData (u : Space → ℝ) (a : Fin 3 → Space → ℝ) (h : Fin 3 → Fin 3 → Space → ℝ) :
    Prop where
  loc_u : LocallyIntegrable u volume
  loc_a : ∀ j, LocallyIntegrable (a j) volume
  loc_h : ∀ k j, LocallyIntegrable (h k j) volume
  weak_a : ∀ j, IsWeakPartial u (a j) j
  weak_h : ∀ k j, IsWeakPartial (a j) (h k j) k
  sq_a : ∀ j, ∫⁻ y, ENNReal.ofReal (a j y ^ 2) < ⊤

theorem two_le_smooth : (2 : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.2 le_top

theorem second_symm {f : Space → ℝ} (hf : ContDiff ℝ ∞ f) (i j : Fin 3) (y : Space) :
    fderiv ℝ (fun y => fderiv ℝ f y (unitVector i)) y (unitVector j) =
      fderiv ℝ (fun y => fderiv ℝ f y (unitVector j)) y (unitVector i) := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    (hf.fderiv_right (m := 1) two_le_smooth).differentiable (by simp)
  have e : ∀ a b : Fin 3, fderiv ℝ (fun y => fderiv ℝ f y (unitVector a)) y (unitVector b) =
      fderiv ℝ (fderiv ℝ f) y (unitVector b) (unitVector a) := by
    intro a b
    rw [fderiv_clm_apply (hd y) (differentiableAt_const _)]
    simp
  rw [e, e]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by simpa using two_le_smooth)) _ _

theorem convolve_contDiff {κ f : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (hc : HasCompactSupport κ)
    (hf : LocallyIntegrable f volume) : ContDiff ℝ ∞ (convolve κ f) :=
  hc.contDiff_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hf

theorem partial_contDiff {κ : Space → ℝ} (hκ : ContDiff ℝ ∞ κ) (k : Fin 3) :
    ContDiff ℝ ∞ (fun t => fderiv ℝ κ t (unitVector k)) :=
  (hκ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const

theorem partial_hasCompactSupport {κ : Space → ℝ} (hc : HasCompactSupport κ) (k : Fin 3) :
    HasCompactSupport (fun t => fderiv ℝ κ t (unitVector k)) :=
  hc.fderiv_apply (𝕜 := ℝ) (unitVector k)

theorem memLp_convolve {κ f : Space → ℝ} (hκ : Continuous κ) (hc : HasCompactSupport κ)
    (hf : LocallyIntegrable f volume) (h2 : ∫⁻ y, ENNReal.ofReal (f y ^ 2) < ⊤) :
    MemLp (convolve κ f) 2 volume := by
  have hcont : Continuous (convolve κ f) :=
    hc.continuous_convolution_left (ContinuousLinearMap.lsmul ℝ ℝ) hκ hf
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine ⟨(hcont.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun y => sq_nonneg _)]
  have hK : ∫⁻ t, ‖κ t‖ₑ < ⊤ := (hκ.integrable_of_hasCompactSupport hc).hasFiniteIntegral
  exact (lintegral_convolve_sq_le hκ hf.aestronglyMeasurable).trans_lt
    (ENNReal.mul_lt_top (ENNReal.pow_lt_top hK) h2)

theorem integral_identity {b : Fin 3 → Space → ℝ} (hb : ∀ j, ContDiff ℝ ∞ (b j))
    (h0 : ∀ j, MemLp (b j) 2 volume)
    (h1 : ∀ k j, MemLp (fun y => fderiv ℝ (b j) y (unitVector k)) 2 volume)
    (h2 : ∀ l k j, MemLp (fun y => fderiv ℝ (fun y => fderiv ℝ (b j) y (unitVector k)) y
      (unitVector l)) 2 volume)
    (hsym : ∀ k j y, fderiv ℝ (b j) y (unitVector k) = fderiv ℝ (b k) y (unitVector j))
    (k j : Fin 3) :
    ∫ y, fderiv ℝ (b j) y (unitVector k) ^ 2 =
      ∫ y, fderiv ℝ (b j) y (unitVector j) * fderiv ℝ (b k) y (unitVector k) := by
  have hdiff : ∀ j, Differentiable ℝ (b j) := fun j => (hb j).differentiable (by simp)
  have hdiff1 : ∀ k j, Differentiable ℝ (fun y => fderiv ℝ (b j) y (unitVector k)) := fun k j =>
    (((hb j).fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const).differentiable
      (by simp)
  have s1 : ∫ y, b j y * fderiv ℝ (fun y => fderiv ℝ (b k) y (unitVector j)) y (unitVector k) =
      -∫ y, fderiv ℝ (b j) y (unitVector k) * fderiv ℝ (b k) y (unitVector j) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ((h1 k j).integrable_mul (h1 j k))
      ((h0 j).integrable_mul (h2 k j k)) ((h0 j).integrable_mul (h1 j k))
      (fun y _ => hdiff j y) (fun y _ => hdiff1 j k y)
  have s2 : ∫ y, b j y * fderiv ℝ (fun y => fderiv ℝ (b k) y (unitVector k)) y (unitVector j) =
      -∫ y, fderiv ℝ (b j) y (unitVector j) * fderiv ℝ (b k) y (unitVector k) :=
    integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable ((h1 j j).integrable_mul (h1 k k))
      ((h0 j).integrable_mul (h2 j k k)) ((h0 j).integrable_mul (h1 k k))
      (fun y _ => hdiff j y) (fun y _ => hdiff1 k k y)
  have e : ∀ y, fderiv ℝ (fun y => fderiv ℝ (b k) y (unitVector j)) y (unitVector k) =
      fderiv ℝ (fun y => fderiv ℝ (b k) y (unitVector k)) y (unitVector j) :=
    fun y => second_symm (hb k) j k y
  simp only [e] at s1
  have e2 : ∀ y, fderiv ℝ (b j) y (unitVector k) ^ 2 =
      fderiv ℝ (b j) y (unitVector k) * fderiv ℝ (b k) y (unitVector j) := by
    intro y
    rw [sq]
    congr 1
    exact hsym k j y
  simp only [e2]
  linarith

theorem kernel_contDiff (n : ℕ) : ContDiff ℝ ∞ (kernel n) := (bump n).contDiff_normed

theorem kernel_hasCompactSupport (n : ℕ) : HasCompactSupport (kernel n) :=
  (bump n).hasCompactSupport_normed

theorem real_identity {d : Fin 3 → Fin 3 → Space → ℝ} (h1 : ∀ k j, MemLp (d k j) 2 volume)
    (hid : ∀ k j, ∫ y, d k j y ^ 2 = ∫ y, d j j y * d k k y) :
    ∫⁻ y, ∑ k, ∑ j, ENNReal.ofReal (d k j y ^ 2) =
      ∫⁻ y, ENNReal.ofReal ((∑ j, d j j y) ^ 2) := by
  have hint : ∀ k j, Integrable (fun y => d k j y ^ 2) volume := fun k j => (h1 k j).integrable_sq
  have hprod : ∀ k j, Integrable (fun y => d j j y * d k k y) volume := fun k j =>
    (h1 j j).integrable_mul (h1 k k)
  have p1 : ∀ y, ∑ k, ∑ j, ENNReal.ofReal (d k j y ^ 2) =
      ENNReal.ofReal (∑ k, ∑ j, d k j y ^ 2) := by
    intro y
    rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => Finset.sum_nonneg fun j _ => sq_nonneg _)]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => sq_nonneg _)]
  have hsqeq : ∀ y, (∑ j, d j j y) ^ 2 = ∑ k, ∑ j, d j j y * d k k y := by
    intro y
    rw [sq, Finset.sum_mul_sum, Finset.sum_comm]
  have hI1 : Integrable (fun y => ∑ k, ∑ j, d k j y ^ 2) volume :=
    integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint k j
  have hI2 : Integrable (fun y => (∑ j, d j j y) ^ 2) volume := by
    simp only [hsqeq]
    exact integrable_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hprod k j
  rw [lintegral_congr p1, ← ofReal_integral_eq_lintegral_ofReal hI1
    (Eventually.of_forall fun y => Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ =>
      sq_nonneg _),
    ← ofReal_integral_eq_lintegral_ofReal hI2 (Eventually.of_forall fun y => sq_nonneg _)]
  congr 1
  calc ∫ y, ∑ k, ∑ j, d k j y ^ 2 = ∑ k, ∑ j, ∫ y, d k j y ^ 2 := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hint k j]
        exact Finset.sum_congr rfl fun k _ => integral_finsetSum _ fun j _ => hint k j
    _ = ∑ k, ∑ j, ∫ y, d j j y * d k k y :=
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => hid k j
    _ = ∫ y, ∑ k, ∑ j, d j j y * d k k y := by
        rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun j _ => hprod k j]
        exact Finset.sum_congr rfl fun k _ => (integral_finsetSum _ fun j _ => hprod k j).symm
    _ = ∫ y, (∑ j, d j j y) ^ 2 := by simp only [hsqeq]

theorem slice_identity {u : Space → ℝ} {a : Fin 3 → Space → ℝ} {h : Fin 3 → Fin 3 → Space → ℝ}
    (hd : IsSliceData u a h) (n : ℕ) :
    ∫⁻ y, ∑ k, ∑ j, ENNReal.ofReal (convolve (kernel n) (h k j) y ^ 2) =
      ∫⁻ y, ENNReal.ofReal ((∑ j, convolve (kernel n) (h j j) y) ^ 2) := by
  have hρs : ContDiff ℝ ∞ (kernel n) := kernel_contDiff n
  have hρc : HasCompactSupport (kernel n) := kernel_hasCompactSupport n
  have hb : ∀ j, ContDiff ℝ ∞ (convolve (kernel n) (a j)) := fun j =>
    convolve_contDiff hρs hρc (hd.loc_a j)
  have hW : ContDiff ℝ ∞ (convolve (kernel n) u) := convolve_contDiff hρs hρc hd.loc_u
  have hWb : ∀ j, (fun y => fderiv ℝ (convolve (kernel n) u) y (unitVector j)) =
      convolve (kernel n) (a j) := fun j => funext fun y => by
    rw [fderiv_convolve hρs hρc hd.loc_u j y, convolve_partial_eq hρs hρc (hd.weak_a j) y]
  have hD1 : ∀ k j, (fun y => fderiv ℝ (convolve (kernel n) (a j)) y (unitVector k)) =
      convolve (fun t => fderiv ℝ (kernel n) t (unitVector k)) (a j) := fun k j =>
    funext fun y => fderiv_convolve hρs hρc (hd.loc_a j) k y
  have hDh : ∀ k j y, convolve (kernel n) (h k j) y =
      fderiv ℝ (convolve (kernel n) (a j)) y (unitVector k) := fun k j y => by
    rw [fderiv_convolve hρs hρc (hd.loc_a j) k y, convolve_partial_eq hρs hρc (hd.weak_h k j) y]
  have hsym : ∀ k j y, fderiv ℝ (convolve (kernel n) (a j)) y (unitVector k) =
      fderiv ℝ (convolve (kernel n) (a k)) y (unitVector j) := by
    intro k j y
    rw [← hWb j, ← hWb k]
    exact second_symm hW j k y
  have h0 : ∀ j, MemLp (convolve (kernel n) (a j)) 2 volume := fun j =>
    memLp_convolve hρs.continuous hρc (hd.loc_a j) (hd.sq_a j)
  have h1 : ∀ k j, MemLp (fun y => fderiv ℝ (convolve (kernel n) (a j)) y (unitVector k)) 2 volume :=
    fun k j => by
      rw [hD1 k j]
      exact memLp_convolve (partial_contDiff hρs k).continuous (partial_hasCompactSupport hρc k)
        (hd.loc_a j) (hd.sq_a j)
  have h2 : ∀ l k j, MemLp (fun y => fderiv ℝ (fun y => fderiv ℝ (convolve (kernel n) (a j)) y
      (unitVector k)) y (unitVector l)) 2 volume := fun l k j => by
    rw [hD1 k j]
    have e : (fun y => fderiv ℝ (convolve (fun t => fderiv ℝ (kernel n) t (unitVector k)) (a j)) y
        (unitVector l)) = convolve (fun t => fderiv ℝ (fun t => fderiv ℝ (kernel n) t (unitVector k))
          t (unitVector l)) (a j) :=
      funext fun y => fderiv_convolve (partial_contDiff hρs k) (partial_hasCompactSupport hρc k)
        (hd.loc_a j) l y
    rw [e]
    exact memLp_convolve (partial_contDiff (partial_contDiff hρs k) l).continuous
      (partial_hasCompactSupport (partial_hasCompactSupport hρc k) l) (hd.loc_a j) (hd.sq_a j)
  have hid := integral_identity hb h0 h1 h2 hsym
  simp only [hDh]
  exact real_identity h1 hid

theorem kernel_nonneg (n : ℕ) (y : Space) : 0 ≤ kernel n y := (bump n).nonneg_normed y

theorem lintegral_kernel (n : ℕ) : ∫⁻ t, ‖kernel n t‖ₑ = 1 := by
  have hi : Integrable (kernel n) volume :=
    (kernel_contDiff n).continuous.integrable_of_hasCompactSupport (kernel_hasCompactSupport n)
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi]
  simp only [Real.norm_eq_abs, abs_of_nonneg (kernel_nonneg n _)]
  rw [show ∫ t, kernel n t = 1 from (bump n).integral_normed]
  simp

theorem slice_trace_le {u : Space → ℝ} {a : Fin 3 → Space → ℝ} {h : Fin 3 → Fin 3 → Space → ℝ}
    (hd : IsSliceData u a h) (n : ℕ) :
    ∫⁻ y, ENNReal.ofReal ((∑ j, convolve (kernel n) (h j j) y) ^ 2) ≤
      ∫⁻ y, ENNReal.ofReal ((∑ j, h j j y) ^ 2) := by
  have hρs : ContDiff ℝ ∞ (kernel n) := kernel_contDiff n
  have hρc : HasCompactSupport (kernel n) := kernel_hasCompactSupport n
  have hsum : ∀ y, ∑ j, convolve (kernel n) (h j j) y =
      convolve (kernel n) (fun x => ∑ j, h j j x) y := by
    intro y
    unfold convolve
    simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul, Finset.mul_sum]
    rw [integral_finsetSum]
    intro j _
    exact hρc.convolutionExists_left (ContinuousLinearMap.lsmul ℝ ℝ) hρs.continuous (hd.loc_h j j) y
  simp only [hsum]
  have hm : AEStronglyMeasurable (fun x => ∑ j, h j j x) volume :=
    Finset.aestronglyMeasurable_fun_sum _ fun j _ => (hd.loc_h j j).aestronglyMeasurable
  calc ∫⁻ y, ENNReal.ofReal (convolve (kernel n) (fun x => ∑ j, h j j x) y ^ 2)
      ≤ (∫⁻ t, ‖kernel n t‖ₑ) ^ 2 * ∫⁻ y, ENNReal.ofReal ((∑ j, h j j y) ^ 2) :=
        lintegral_convolve_sq_le hρs.continuous hm
    _ = ∫⁻ y, ENNReal.ofReal ((∑ j, h j j y) ^ 2) := by rw [lintegral_kernel]; simp

theorem bump_rOut_tendsto : Tendsto (fun n : ℕ => (bump n).rOut) atTop (𝓝 0) := by
  show Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 1)) atTop (𝓝 0)
  have := (tendsto_one_div_add_atTop_nhds_zero_nat).const_mul (2 : ℝ)
  simpa only [mul_one_div, mul_zero] using this

theorem slice_secondDeriv_le {u : Space → ℝ} {a : Fin 3 → Space → ℝ} {h : Fin 3 → Fin 3 → Space → ℝ}
    (hd : IsSliceData u a h) :
    ∫⁻ y, ∑ k, ∑ j, ENNReal.ofReal (h k j y ^ 2) ≤ ∫⁻ y, ENNReal.ofReal ((∑ j, h j j y) ^ 2) := by
  have hconv : ∀ k j, ∀ᵐ y, Tendsto (fun n => convolve (kernel n) (h k j) y) atTop
      (𝓝 (h k j y)) := fun k j =>
    ContDiffBump.ae_convolution_tendsto_right_of_locallyIntegrable (φ := bump) (K := 2)
      bump_rOut_tendsto (Eventually.of_forall fun n => le_of_eq (by
        show 2 / ((n : ℝ) + 1) = 2 * (1 / ((n : ℝ) + 1))
        ring)) (hd.loc_h k j)
  have hall : ∀ᵐ y, ∀ k j, Tendsto (fun n => convolve (kernel n) (h k j) y) atTop
      (𝓝 (h k j y)) := ae_all_iff.2 fun k => ae_all_iff.2 fun j => hconv k j
  have hlim : ∀ᵐ y, ∑ k, ∑ j, ENNReal.ofReal (h k j y ^ 2) =
      Filter.liminf (fun n => ∑ k, ∑ j, ENNReal.ofReal (convolve (kernel n) (h k j) y ^ 2)) atTop := by
    filter_upwards [hall] with y hy
    have ht : Tendsto (fun n => ∑ k, ∑ j, ENNReal.ofReal (convolve (kernel n) (h k j) y ^ 2)) atTop
        (𝓝 (∑ k, ∑ j, ENNReal.ofReal (h k j y ^ 2))) :=
      tendsto_finsetSum _ fun k _ => tendsto_finsetSum _ fun j _ =>
        (ENNReal.continuous_ofReal.tendsto _).comp ((hy k j).pow 2)
    exact ht.liminf_eq.symm
  have hmeas : ∀ n, AEMeasurable (fun y => ∑ k, ∑ j,
      ENNReal.ofReal (convolve (kernel n) (h k j) y ^ 2)) volume := fun n => by
    have hc : ∀ k j, Continuous (convolve (kernel n) (h k j)) := fun k j =>
      (kernel_hasCompactSupport n).continuous_convolution_left _ (kernel_contDiff n).continuous
        (hd.loc_h k j)
    exact (continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun j _ =>
      ENNReal.continuous_ofReal.comp ((hc k j).pow 2)).aemeasurable
  calc ∫⁻ y, ∑ k, ∑ j, ENNReal.ofReal (h k j y ^ 2)
      = ∫⁻ y, Filter.liminf (fun n => ∑ k, ∑ j,
          ENNReal.ofReal (convolve (kernel n) (h k j) y ^ 2)) atTop := lintegral_congr_ae hlim
    _ ≤ Filter.liminf (fun n => ∫⁻ y, ∑ k, ∑ j,
          ENNReal.ofReal (convolve (kernel n) (h k j) y ^ 2)) atTop := lintegral_liminf_le' hmeas
    _ = Filter.liminf (fun n => ∫⁻ y,
          ENNReal.ofReal ((∑ j, convolve (kernel n) (h j j) y) ^ 2)) atTop := by
        simp only [slice_identity hd]
    _ ≤ ∫⁻ y, ENNReal.ofReal ((∑ j, h j j y) ^ 2) :=
        Filter.liminf_le_of_frequently_le' (Frequently.of_forall fun n => slice_trace_le hd n)

theorem norm_unitVector_eq (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem component_locallyIntegrable {f : Space → Space} (hf : LocallyIntegrable f volume) (i : Fin 3) :
    LocallyIntegrable (fun y => f y i) volume :=
  hf.mono ((EuclideanSpace.proj i : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable) (Eventually.of_forall fun y => PiLp.norm_apply_le (f y) i)

theorem apply_locallyIntegrable {F : Space → (Space →L[ℝ] Space)} (hF : LocallyIntegrable F volume)
    (k : Fin 3) : LocallyIntegrable (fun y => F y (unitVector k)) volume :=
  hF.mono ((ContinuousLinearMap.apply ℝ Space (unitVector k)).continuous.comp_aestronglyMeasurable
    hF.aestronglyMeasurable) (Eventually.of_forall fun y => by
      simpa [norm_unitVector_eq] using (F y).le_opNorm (unitVector k))

theorem weak_component {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f F) (j i : Fin 3) :
    IsWeakPartial (fun y => f y i) (fun y => F y (unitVector j) i) j := by
  intro φ hφ
  have e := hg.2.2 φ hφ j
  have hc : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
    (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
  have hs : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
    hφ.2.fderiv_apply (𝕜 := ℝ) (unitVector j)
  have i1 := (apply_locallyIntegrable hg.2.1 j).integrable_smul_left_of_hasCompactSupport
    hφ.1.continuous hφ.2
  have i2 := hg.1.integrable_smul_left_of_hasCompactSupport hc hs
  have e2 := congrArg (EuclideanSpace.proj i : Space →L[ℝ] ℝ) e
  rw [← ContinuousLinearMap.integral_comp_comm _ i1, map_neg,
    ← ContinuousLinearMap.integral_comp_comm _ i2] at e2
  simpa using e2

theorem sliceData_of {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    {S : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hg : IsWeakGradient f F)
    (hh : ∀ j : Fin 3, IsWeakGradient (fun y => F y (unitVector j)) (fun y => (S y).flip (unitVector j)))
    (hfin : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤) (i : Fin 3) :
    IsSliceData (fun y => f y i) (fun j y => F y (unitVector j) i)
      (fun k j y => S y (unitVector k) (unitVector j) i) where
  loc_u := component_locallyIntegrable hg.1 i
  loc_a j := component_locallyIntegrable (hh j).1 i
  loc_h k j := component_locallyIntegrable (apply_locallyIntegrable (hh j).2.1 k) i
  weak_a j := weak_component hg j i
  weak_h k j := weak_component (hh j) k i
  sq_a j := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal ?_) hfin
    calc F y (unitVector j) i ^ 2 ≤ ‖F y (unitVector j)‖ ^ 2 := by
          have := PiLp.norm_apply_le (F y (unitVector j)) i
          rw [Real.norm_eq_abs] at this
          nlinarith [abs_nonneg (F y (unitVector j) i), sq_abs (F y (unitVector j) i)]
      _ ≤ matSq (F y) := Finset.single_le_sum (f := fun l : Fin 3 => ‖F y (unitVector l)‖ ^ 2)
          (fun l _ => sq_nonneg _) (Finset.mem_univ j)

theorem secondDerivSq_eq (A : Space →L[ℝ] Space →L[ℝ] Space) :
    ENNReal.ofReal (secondDerivSq A) =
      ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, ENNReal.ofReal ((A (unitVector k) (unitVector j) i) ^ 2) := by
  have e : secondDerivSq A = ∑ i : Fin 3, ∑ k : Fin 3, ∑ j : Fin 3, (A (unitVector k) (unitVector j) i) ^ 2 := by
    unfold secondDerivSq
    simp only [EuclideanSpace.real_norm_sq_eq]
    calc ∑ k : Fin 3, ∑ j : Fin 3, ∑ i : Fin 3, (A (unitVector k) (unitVector j) i) ^ 2
        = ∑ k : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, (A (unitVector k) (unitVector j) i) ^ 2 :=
          Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = _ := Finset.sum_comm
  rw [e, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun k _ => by positivity)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]

theorem traceSq_eq (A : Space →L[ℝ] Space →L[ℝ] Space) :
    ENNReal.ofReal (‖secondDerivTrace A‖ ^ 2) =
      ∑ i : Fin 3, ENNReal.ofReal ((∑ j : Fin 3, A (unitVector j) (unitVector j) i) ^ 2) := by
  unfold secondDerivTrace
  rw [EuclideanSpace.real_norm_sq_eq, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  simp

theorem slice_secondDerivSq_le {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    {S : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hg : IsWeakGradient f F)
    (hh : ∀ j : Fin 3, IsWeakGradient (fun y => F y (unitVector j)) (fun y => (S y).flip (unitVector j)))
    (hfin : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤) :
    ∫⁻ y, ENNReal.ofReal (secondDerivSq (S y)) ≤ ∫⁻ y, ENNReal.ofReal (‖secondDerivTrace (S y)‖ ^ 2) := by
  have hd := sliceData_of hg hh hfin
  simp only [secondDerivSq_eq, traceSq_eq]
  have hm1 : ∀ i, AEMeasurable (fun y => ∑ k : Fin 3, ∑ j : Fin 3,
      ENNReal.ofReal ((S y (unitVector k) (unitVector j) i) ^ 2)) volume := fun i =>
    Finset.aemeasurable_fun_sum _ fun k _ => Finset.aemeasurable_fun_sum _ fun j _ =>
      (((hd i).loc_h k j).aestronglyMeasurable.aemeasurable.pow_const 2).ennreal_ofReal
  have hm2 : ∀ i, AEMeasurable (fun y =>
      ENNReal.ofReal ((∑ j : Fin 3, S y (unitVector j) (unitVector j) i) ^ 2)) volume := fun i =>
    ((Finset.aemeasurable_fun_sum _ fun j _ =>
      ((hd i).loc_h j j).aestronglyMeasurable.aemeasurable).pow_const 2).ennreal_ofReal
  rw [lintegral_finsetSum' _ fun i _ => hm1 i, lintegral_finsetSum' _ fun i _ => hm2 i]
  exact Finset.sum_le_sum fun i _ => slice_secondDeriv_le (hd i)

theorem continuous_matNorm : Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  exact continuous_finsetSum _ fun i _ => (continuous_id.clm_apply continuous_const).norm.pow 2

theorem aemeasurable_matNorm {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hm : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) :
    AEMeasurable (fun σ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) volume := by
  have h : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2)))
      (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact (continuous_matNorm.comp_aestronglyMeasurable hm).aemeasurable.ennreal_ofReal
  exact h.lintegral_prod_right'

theorem ae_matSq_lt_top {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ :=
  ae_lt_top' (aemeasurable_matNorm hv.measurable_gradient).restrict hv.gradient_finite.ne

theorem secondDeriv_bound {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    periodLIntegral (fun σ y => secondDerivSq (H σ y)) ≤
      periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) := by
  unfold periodLIntegral
  refine lintegral_mono_ae ?_
  filter_upwards [ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.weak_secondDeriv,
    ae_matSq_lt_top hv] with σ h1 h2 h3
  exact slice_secondDerivSq_le h1 h2 h3

theorem opNorm_le_sum_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun i _ => norm_nonneg _) fun v => ?_
  have hv : v = ∑ i : Fin 3, v.ofLp i • unitVector i := by
    conv_lhs => rw [← (EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr v]
    simp [unitVector]
  calc ‖A v‖ = ‖∑ i : Fin 3, v.ofLp i • A (unitVector i)‖ := by
        conv_lhs => rw [hv]
        rw [map_sum]
        simp only [map_smul]
    _ ≤ ∑ i : Fin 3, ‖v.ofLp i • A (unitVector i)‖ := norm_sum_le _ _
    _ ≤ ∑ i : Fin 3, ‖v‖ * ‖A (unitVector i)‖ := Finset.sum_le_sum fun i _ => by
        rw [norm_smul]
        exact mul_le_mul_of_nonneg_right (PiLp.norm_apply_le v i) (norm_nonneg _)
    _ = (∑ i : Fin 3, ‖A (unitVector i)‖) * ‖v‖ := by rw [← Finset.mul_sum, mul_comm]

theorem gradient_locallyIntegrable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    LocallyIntegrable (fun z : ℝ × Space => G z.1 z.2) volume := by
  have hcol : ∀ i, LocallyIntegrable (fun z : ℝ × Space => ‖G z.1 z.2 (unitVector i)‖) volume :=
    fun i => Cert.Internal.CoerciveBordered.column_locallyIntegrable hv.measurable_gradient
      hv.periodic_gradient hv.gradient_finite i
  have hs := locallyIntegrable_finsetSum Finset.univ fun i _ => hcol i
  refine hs.mono hv.measurable_gradient (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => norm_nonneg _)]
  exact opNorm_le_sum_apply _

theorem secondDeriv_locallyIntegrable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    LocallyIntegrable (fun z : ℝ × Space => H z.1 z.2) volume := by
  have hent : ∀ j l : Fin 3, LocallyIntegrable
      (fun z : ℝ × Space => ‖H z.1 z.2 (unitVector j) (unitVector l)‖) volume := by
    intro j l
    refine Cert.Internal.CoerciveBordered.locallyIntegrable_of_periodic_sq
      (fun σ y => ‖H σ y (unitVector j) (unitVector l)‖)
      ((show Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => ‖A (unitVector j) (unitVector l)‖) from
        ((continuous_id.clm_apply continuous_const).clm_apply continuous_const).norm).comp_aestronglyMeasurable
        hv.measurable_secondDeriv) (fun σ y => by simp only [hv.periodic_secondDeriv σ y]) ?_
    refine lt_of_le_of_lt (Cert.Internal.CoerciveBordered.periodLIntegral_mono fun σ y => ?_)
      ((secondDeriv_bound hv).trans_lt hv.sumSecondPartials_finite)
    unfold secondDerivSq
    exact (Finset.single_le_sum (f := fun l : Fin 3 => ‖H σ y (unitVector j) (unitVector l)‖ ^ 2)
      (fun l _ => sq_nonneg _) (Finset.mem_univ l)).trans
      (Finset.single_le_sum (f := fun j : Fin 3 => ∑ l : Fin 3, ‖H σ y (unitVector j) (unitVector l)‖ ^ 2)
        (fun j _ => Finset.sum_nonneg fun l _ => sq_nonneg _) (Finset.mem_univ j))
  have hs := locallyIntegrable_finsetSum Finset.univ fun j _ =>
    locallyIntegrable_finsetSum Finset.univ fun l _ => hent j l
  refine hs.mono hv.measurable_secondDeriv (Eventually.of_forall fun z => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun l _ => norm_nonneg _)]
  exact (opNorm_le_sum_apply _).trans (Finset.sum_le_sum fun j _ => opNorm_le_sum_apply _)

theorem sq_norm_le_three_matNorm (A : Space →L[ℝ] Space) : ‖A‖ ^ 2 ≤ 3 * matSq A := by
  have h := opNorm_le_sum_apply A
  have h0 : 0 ≤ ‖A‖ := norm_nonneg _
  unfold matSq
  simp only [Fin.sum_univ_three] at h ⊢
  have := norm_nonneg (A (unitVector 0))
  have := norm_nonneg (A (unitVector 1))
  have := norm_nonneg (A (unitVector 2))
  nlinarith [sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 1)‖),
    sq_nonneg (‖A (unitVector 1)‖ - ‖A (unitVector 2)‖),
    sq_nonneg (‖A (unitVector 0)‖ - ‖A (unitVector 2)‖)]

theorem slice_embed {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f F) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (F y (unitVector i)) i = 0)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤) :
    ∃ x : Freq.X, (Freq.velocity x : Space → Space) =ᵐ[volume] f ∧
      ENNReal.ofReal (‖x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (matSq (F y)) := by
  have hG2 : ∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono fun y => ENNReal.ofReal_le_ofReal
      (sq_norm_le_three_matNorm (F y))) ?_
    simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 3)]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top h2
  set C := max (∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6)).toReal (∫⁻ y, ENNReal.ofReal (‖F y‖ ^ 2)).toReal
  have hS : WeakProfile.IsSlice f F C :=
    ⟨hg, hdiv, (ENNReal.ofReal_toReal h6.ne).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _)),
      (ENNReal.ofReal_toReal hG2.ne).symm.le.trans (ENNReal.ofReal_le_ofReal (le_max_right _ _))⟩
  obtain ⟨x, hx1, hx2, -⟩ := WeakProfile.sliceEmbedding_holds WeakProfile.pairingVelocity_holds
    WeakProfile.velocityWeakGradient_holds WeakProfile.zeroGradientSix_holds
    WeakProfile.gradientFreqTr_holds f F C hS
  have hnorm : ENNReal.ofReal (‖x‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (matSq (F y)) := by
    rw [← Cert.Internal.SliceFields.sum_norm_partialX_sq x,
      ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _)]
    unfold matSq
    rw [lintegral_congr fun y => ENNReal.ofReal_sum_of_nonneg (fun i _ => sq_nonneg _),
      lintegral_finsetSum' _ fun i _ =>
        ((apply_locallyIntegrable hg.2.1 i).aestronglyMeasurable.norm.aemeasurable.pow_const 2).ennreal_ofReal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Cert.Internal.SliceFields.integral_norm_sq_L2R,
      ofReal_integral_eq_lintegral_ofReal (Cert.Internal.SliceFields.integrable_norm_sq_L2R _)
        (Eventually.of_forall fun y => sq_nonneg _)]
    exact lintegral_congr_ae ((hx2 i).mono fun y hy => by dsimp only; rw [hy]; rfl)
  exact ⟨x, hx1, hnorm⟩

theorem slice_ball_bound {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f F) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (F y (unitVector i)) i = 0)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤)
    (y₀ : Space) :
    ∫⁻ y in Metric.ball y₀ 1, ‖f y‖ₑ ≤
      ENNReal.ofReal ‖Freq.velocity‖ * (1 + ∫⁻ y, ENNReal.ofReal (matSq (F y))) *
        volume (Metric.ball y₀ (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
  obtain ⟨x, hx1, hnorm⟩ := slice_embed hg hdiv h6 h2
  calc ∫⁻ y in Metric.ball y₀ 1, ‖f y‖ₑ
      = ∫⁻ y in Metric.ball y₀ 1, ‖(Freq.velocity x : Space → Space) y‖ₑ :=
        lintegral_congr_ae (ae_restrict_of_ae (hx1.mono fun y hy => by dsimp only; rw [hy]))
    _ ≤ ENNReal.ofReal (‖Freq.velocity‖ * ‖x‖) *
          volume (Metric.ball y₀ (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) :=
        Cert.Internal.CoerciveBordered.lintegral_ball_velocity_le x y₀
    _ ≤ _ := by
        gcongr
        rw [ENNReal.ofReal_mul (norm_nonneg _)]
        gcongr
        rw [← hnorm, ← ENNReal.ofReal_one, ← ENNReal.ofReal_add (by norm_num) (sq_nonneg _)]
        exact ENNReal.ofReal_le_ofReal (by nlinarith [sq_nonneg (‖x‖ - 1)])

theorem lintegral_sq_eq_eLpNorm (f : Space → Space) (μ : Measure Space) :
    ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 2) ∂μ = eLpNorm f 2 μ ^ 2 := by
  have h := lintegral_rpow_enorm_eq_rpow_eLpNorm' (f := f) (μ := μ) (q := 2) (by norm_num)
  rw [eLpNorm_eq_eLpNorm' (by norm_num) (by simp)]
  simp only [ENNReal.toReal_ofNat]
  rw [← ENNReal.rpow_two, ← h]
  refine lintegral_congr fun y => ?_
  rw [ENNReal.rpow_two, ← ofReal_norm, ENNReal.ofReal_pow (norm_nonneg _)]

theorem slice_ball_sq_bound {f : Space → Space} {F : Space → (Space →L[ℝ] Space)}
    (hg : IsWeakGradient f F) (hdiv : ∀ᵐ y, ∑ i : Fin 3, (F y (unitVector i)) i = 0)
    (h6 : ∫⁻ y, ENNReal.ofReal (‖f y‖ ^ 6) < ⊤) (h2 : ∫⁻ y, ENNReal.ofReal (matSq (F y)) < ⊤)
    (R : ℝ) :
    ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖f y‖ ^ 2) ≤
      (ENNReal.ofReal ‖Freq.velocity‖ * volume (Metric.closedBall (0 : Space) R) ^
        (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 *
        ∫⁻ y, ENNReal.ofReal (matSq (F y)) := by
  obtain ⟨x, hx1, hnorm⟩ := slice_embed hg hdiv h6 h2
  calc ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖f y‖ ^ 2)
      = ∫⁻ y in Metric.closedBall (0 : Space) R,
          ENNReal.ofReal (‖(Freq.velocity x : Space → Space) y‖ ^ 2) :=
        lintegral_congr_ae (ae_restrict_of_ae (hx1.mono fun y hy => by dsimp only; rw [hy]))
    _ = eLpNorm (Freq.velocity x : Space → Space) 2
          (volume.restrict (Metric.closedBall (0 : Space) R)) ^ 2 := lintegral_sq_eq_eLpNorm _ _
    _ ≤ (ENNReal.ofReal (‖Freq.velocity‖ * ‖x‖) * volume (Metric.closedBall (0 : Space) R) ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 := by
        gcongr
        have h1 := eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (μ := volume.restrict (Metric.closedBall (0 : Space) R)) (p := 2) (q := 6) (by norm_num)
          (Lp.aestronglyMeasurable (Freq.velocity x)).restrict
        rw [Measure.restrict_apply_univ] at h1
        refine h1.trans ?_
        gcongr
        calc eLpNorm (Freq.velocity x : Space → Space) 6
              (volume.restrict (Metric.closedBall (0 : Space) R))
            ≤ eLpNorm (Freq.velocity x : Space → Space) 6 volume :=
              eLpNorm_mono_measure _ Measure.restrict_le_self
          _ = ‖Freq.velocity x‖ₑ := (Lp.enorm_def _).symm
          _ = ENNReal.ofReal ‖Freq.velocity x‖ := (ofReal_norm _).symm
          _ ≤ ENNReal.ofReal (‖Freq.velocity‖ * ‖x‖) :=
              ENNReal.ofReal_le_ofReal (Freq.velocity.le_opNorm x)
    _ = (ENNReal.ofReal ‖Freq.velocity‖ * volume (Metric.closedBall (0 : Space) R) ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 * ENNReal.ofReal (‖x‖ ^ 2) := by
        rw [ENNReal.ofReal_mul (norm_nonneg _), ENNReal.ofReal_pow (norm_nonneg _)]
        ring
    _ = _ := by rw [hnorm]

theorem velocity_localSquare {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (R : ℝ) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R,
      ENNReal.ofReal (‖v σ y‖ ^ 2) < ⊤ := by
  have hK : (ENNReal.ofReal ‖Freq.velocity‖ * volume (Metric.closedBall (0 : Space) R) ^
      (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_closedBall_lt_top.ne))
  calc ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y in Metric.closedBall (0 : Space) R, ENNReal.ofReal (‖v σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, (ENNReal.ofReal ‖Freq.velocity‖ *
          volume (Metric.closedBall (0 : Space) R) ^
            (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 *
          ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.divergence_free,
          ae_restrict_of_ae hv.sixth_power, ae_matSq_lt_top hv] with σ h1 h2 h3 h4
        exact slice_ball_sq_bound h1 h2 h3 h4 R
    _ = (ENNReal.ofReal ‖Freq.velocity‖ * volume (Metric.closedBall (0 : Space) R) ^
          (1 / (2 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal)) ^ 2 *
          periodLIntegral (fun σ y => matSq (G σ y)) := lintegral_const_mul' _ _ hK
    _ < ⊤ := ENNReal.mul_lt_top hK.lt_top hv.gradient_finite

theorem velocity_locallyIntegrable {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    LocallyIntegrable (fun z : ℝ × Space => v z.1 z.2) volume := by
  have hnorm : LocallyIntegrable (fun z : ℝ × Space => ‖v z.1 z.2‖) volume := by
    intro x
    refine ⟨Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 1,
      prod_mem_nhds (Ioo_mem_nhds (by linarith) (by linarith)) (Metric.ball_mem_nhds _ one_pos), ?_⟩
    refine ⟨hv.measurable_velocity.norm.restrict, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    simp only [enorm_norm]
    have hK : volume (Metric.ball x.2 (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) ≠ ⊤ :=
      ENNReal.rpow_ne_top_of_nonneg (by norm_num) measure_ball_lt_top.ne
    have hper : Function.Periodic (fun σ => ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) 1 := fun σ => by
      simp only [hv.periodic_gradient σ]
    have hΦ : ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1),
        ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ := by
      rw [Cert.Internal.CoerciveBordered.lintegral_Ioc_periodic _ hper]
      exact hv.gradient_finite
    have hfin : ∀ᵐ σ ∂(volume.restrict (Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1))),
        ∫⁻ y, ENNReal.ofReal (matSq (G σ y)) < ⊤ :=
      ae_lt_top' (aemeasurable_matNorm hv.measurable_gradient).restrict hΦ.ne
    calc ∫⁻ z in Set.Ioo (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ), ‖v z.1 z.2‖ₑ
        ≤ ∫⁻ z in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1) ×ˢ Metric.ball x.2 (1 : ℝ), ‖v z.1 z.2‖ₑ :=
          lintegral_mono_set (Set.prod_mono Set.Ioo_subset_Ioc_self subset_rfl)
      _ = ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1), ∫⁻ y in Metric.ball x.2 (1 : ℝ), ‖v σ y‖ₑ := by
          rw [Measure.volume_eq_prod, setLIntegral_prod (fun z : ℝ × Space => ‖v z.1 z.2‖ₑ)
            hv.measurable_velocity.enorm.restrict]
      _ ≤ ∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1),
          ENNReal.ofReal ‖Freq.velocity‖ * (1 + ∫⁻ y, ENNReal.ofReal (matSq (G σ y))) *
            volume (Metric.ball x.2 (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
          refine lintegral_mono_ae ?_
          filter_upwards [ae_restrict_of_ae hv.weak_gradient, ae_restrict_of_ae hv.divergence_free,
            ae_restrict_of_ae hv.sixth_power, hfin] with σ h1 h2 h3 h4
          exact slice_ball_bound h1 h2 h3 h4 x.2
      _ = ENNReal.ofReal ‖Freq.velocity‖ * (∫⁻ σ in Set.Ioc (x.1 - 1 / 2) (x.1 - 1 / 2 + 1),
            (1 + ∫⁻ y, ENNReal.ofReal (matSq (G σ y)))) *
            volume (Metric.ball x.2 (1 : ℝ)) ^ (1 / (1 : ℝ≥0∞).toReal - 1 / (6 : ℝ≥0∞).toReal) := by
          rw [lintegral_mul_const' _ _ hK, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ < ⊤ := by
          refine ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_) hK.lt_top
          rw [lintegral_add_left measurable_const]
          refine ENNReal.add_lt_top.2 ⟨?_, hΦ⟩
          simp
  exact hnorm.mono hv.measurable_velocity (Eventually.of_forall fun z => by simp)

end Internal.PerturbationFacts

open Internal.PerturbationFacts in
theorem perturbationSecondDerivBoundHolds_proof : PerturbationSecondDerivBoundHolds :=
  fun _ _ _ _ _ _ hv => secondDeriv_bound hv

open Internal.PerturbationFacts in
theorem perturbationLocalSquareIntegrabilityHolds_proof : PerturbationLocalSquareIntegrabilityHolds :=
  fun _ _ _ _ _ _ hv R => velocity_localSquare hv R

open Internal.PerturbationFacts in
theorem perturbationLocalIntegrabilityHolds_proof : PerturbationLocalIntegrabilityHolds :=
  fun _ _ _ _ _ _ hv =>
    ⟨velocity_locallyIntegrable hv, gradient_locallyIntegrable hv, secondDeriv_locallyIntegrable hv⟩

end Coercive

end Breakdown
