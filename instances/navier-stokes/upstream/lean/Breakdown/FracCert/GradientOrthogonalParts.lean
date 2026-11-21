import Breakdown.FracCert.StHeldParts
import Breakdown.Uniqueness.CutoffBounds
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Function.ContinuousMapDense

open scoped ContDiff ENNReal Convolution
open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace GradientOrthogonalInternal

def pairShift (ζ Q : Space → Space) (y : Space) : ℝ := ∫ x, inner ℝ (ζ x) (Q (x + y))

private def sq2' {E : Type*} [NormedAddCommGroup E] (f : Space → E) : ℝ :=
  (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))

private def sq2 (f : Space → Space) : ℝ := (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ))

private theorem sq2_nonneg (f : Space → Space) : 0 ≤ sq2 f :=
  Real.rpow_nonneg (integral_nonneg fun _ => Real.rpow_nonneg (norm_nonneg _) _) _

private theorem memLp_shift {b : Space → Space} (hb : MemLp b 2 volume) (y : Space) :
    MemLp (fun x => b (x + y)) 2 volume :=
  hb.comp_measurePreserving (measurePreserving_add_right volume y)

private theorem sq2_shift (b : Space → Space) (y : Space) : sq2 (fun x => b (x + y)) = sq2 b := by
  unfold sq2
  rw [integral_add_right_eq_self (fun x => ‖b x‖ ^ (2 : ℝ)) y]

private theorem integrable_pair {a b : Space → Space} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    Integrable (fun x => inner ℝ (a x) (b x)) volume := by
  have h : Integrable (fun x => ‖a x‖ * ‖b x‖) volume := ha.norm.integrable_mul hb.norm
  refine h.mono' (ha.1.inner hb.1) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs]
  exact abs_real_inner_le_norm _ _

private theorem abs_pair_le {a b : Space → Space} (ha : MemLp a 2 volume) (hb : MemLp b 2 volume) :
    |∫ x, inner ℝ (a x) (b x)| ≤ sq2 a * sq2 b := by
  have h : Integrable (fun x => ‖a x‖ * ‖b x‖) volume := ha.norm.integrable_mul hb.norm
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have ha' : MemLp a (ENNReal.ofReal 2) volume := by simpa using ha
  have hb' : MemLp b (ENNReal.ofReal 2) volume := by simpa using hb
  calc |∫ x, inner ℝ (a x) (b x)| = ‖∫ x, inner ℝ (a x) (b x)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∫ x, ‖a x‖ * ‖b x‖ :=
        norm_integral_le_of_norm_le h (Eventually.of_forall fun x => by
          rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _)
    _ ≤ sq2 a * sq2 b := integral_mul_norm_le_Lp_mul_Lq hpq ha' hb'

private theorem approx {f : Space → Space} (hf : MemLp f 2 volume) {ε : ℝ} (hε : 0 < ε) :
    ∃ g : Space → Space, HasCompactSupport g ∧ Continuous g ∧ MemLp g 2 volume ∧ sq2 (f - g) ≤ ε := by
  obtain ⟨g, hgc, hle, hgcont, hgm⟩ :=
    hf.exists_hasCompactSupport_eLpNorm_sub_le (by norm_num) (ENNReal.ofReal_pos.2 hε).ne'
  refine ⟨g, hgc, hgcont, hgm, ?_⟩
  have hm : MemLp (f - g) 2 volume := hf.sub hgm
  rw [hm.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)] at hle
  have := (ENNReal.ofReal_le_ofReal_iff hε.le).1 hle
  simpa [sq2, one_div] using this

private theorem pair_sub (ζ Q g h : Space → Space) (hζ : MemLp ζ 2 volume) (hQ : MemLp Q 2 volume)
    (hg : MemLp g 2 volume) (hh : MemLp h 2 volume) (y : Space) :
    |pairShift ζ Q y - pairShift g h y| ≤ sq2 (ζ - g) * sq2 Q + sq2 g * sq2 (Q - h) := by
  have e : pairShift ζ Q y - pairShift g h y =
      (∫ x, inner ℝ ((ζ - g) x) (Q (x + y))) + ∫ x, inner ℝ (g x) ((Q - h) (x + y)) := by
    unfold pairShift
    rw [← integral_sub (integrable_pair hζ (memLp_shift hQ y)) (integrable_pair hg (memLp_shift hh y)),
      ← integral_add (integrable_pair (hζ.sub hg) (memLp_shift hQ y))
        (integrable_pair hg (memLp_shift (hQ.sub hh) y))]
    congr 1
    funext x
    simp only [Pi.sub_apply, inner_sub_left, inner_sub_right]
    ring
  rw [e]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · have := abs_pair_le (hζ.sub hg) (memLp_shift hQ y)
    rwa [sq2_shift] at this
  · have := abs_pair_le hg (memLp_shift (hQ.sub hh) y)
    rwa [sq2_shift (Q - h) y] at this

private theorem uniform_approx {ζ Q : Space → Space} (hζ : MemLp ζ 2 volume) (hQ : MemLp Q 2 volume)
    {ε : ℝ} (hε : 0 < ε) : ∃ g h : Space → Space, HasCompactSupport g ∧ Continuous g ∧
      HasCompactSupport h ∧ Continuous h ∧ ∀ y, |pairShift ζ Q y - pairShift g h y| ≤ ε := by
  obtain ⟨g, hgc, hgcont, hgm, hgle⟩ := approx hζ (ε := ε / (2 * (sq2 Q + 1))) (by
    have := sq2_nonneg Q; positivity)
  obtain ⟨h, hhc, hhcont, hhm, hhle⟩ := approx hQ (ε := ε / (2 * (sq2 g + 1))) (by
    have := sq2_nonneg g; positivity)
  refine ⟨g, h, hgc, hgcont, hhc, hhcont, fun y => (pair_sub ζ Q g h hζ hQ hgm hhm y).trans ?_⟩
  have hQ0 := sq2_nonneg Q
  have hg0 := sq2_nonneg g
  have h1 : sq2 (ζ - g) * sq2 Q ≤ ε / 2 := by
    calc sq2 (ζ - g) * sq2 Q ≤ ε / (2 * (sq2 Q + 1)) * (sq2 Q + 1) :=
          mul_le_mul hgle (by linarith) hQ0 (by positivity)
      _ = ε / 2 := by field_simp
  have h2 : sq2 g * sq2 (Q - h) ≤ ε / 2 := by
    calc sq2 g * sq2 (Q - h) ≤ (sq2 g + 1) * (ε / (2 * (sq2 g + 1))) :=
          mul_le_mul (by linarith) hhle (sq2_nonneg _) (by positivity)
      _ = ε / 2 := by field_simp
  linarith

private theorem pairShift_conv (g h : Space → Space) :
    pairShift g h = (fun t => g (-t)) ⋆[innerSL ℝ, volume] h := by
  funext y
  rw [convolution_def, pairShift]
  rw [← integral_neg_eq_self]
  congr 1
  funext x
  rw [innerSL_apply_apply, sub_eq_neg_add]

private theorem approx_cont {g h : Space → Space} (hgc : HasCompactSupport g) (hg : Continuous g)
    (hhc : HasCompactSupport h) (hh : Continuous h) :
    Continuous (pairShift g h) ∧ Tendsto (pairShift g h) (cocompact Space) (𝓝 0) := by
  rw [pairShift_conv]
  have hgc' : HasCompactSupport (fun t => g (-t)) := hgc.comp_homeomorph (Homeomorph.neg Space)
  have hg' : Continuous (fun t => g (-t)) := hg.comp continuous_neg
  exact ⟨hhc.continuous_convolution_right _ hg'.locallyIntegrable hh,
    (hgc'.convolution _ hhc).is_zero_at_infty⟩

theorem continuous_pairShift {ζ Q : Space → Space} (hζ : MemLp ζ 2 volume) (hQ : MemLp Q 2 volume) :
    Continuous (pairShift ζ Q) := by
  have hU : ∀ n : ℕ, ∃ g h : Space → Space, HasCompactSupport g ∧ Continuous g ∧
      HasCompactSupport h ∧ Continuous h ∧ ∀ y, |pairShift ζ Q y - pairShift g h y| ≤ 1 / ((n : ℝ) + 1) :=
    fun n => uniform_approx hζ hQ (by positivity)
  choose g h hgc hg hhc hh hle using hU
  refine TendstoUniformly.continuous (F := fun n => pairShift (g n) (h n)) (p := atTop) ?_
    (Eventually.of_forall fun n => (approx_cont (hgc n) (hg n) (hhc n) (hh n)).1).frequently
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  filter_upwards [eventually_ge_atTop N] with n hn y
  rw [Real.dist_eq]
  refine (hle n y).trans_lt (lt_of_le_of_lt ?_ hN)
  apply one_div_le_one_div_of_le (by positivity)
  have : (N : ℝ) ≤ n := by exact_mod_cast hn
  linarith

theorem tendsto_pairShift {ζ Q : Space → Space} (hζ : MemLp ζ 2 volume) (hQ : MemLp Q 2 volume) :
    Tendsto (pairShift ζ Q) (cocompact Space) (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨g, h, hgc, hg, hhc, hh, hle⟩ := uniform_approx hζ hQ (ε := ε / 2) (by positivity)
  have h2 := (approx_cont hgc hg hhc hh).2
  rw [Metric.tendsto_nhds] at h2
  filter_upwards [h2 (ε / 2) (by positivity)] with y hy
  rw [Real.dist_eq, sub_zero] at hy ⊢
  have := hle y
  calc |pairShift ζ Q y| ≤ |pairShift ζ Q y - pairShift g h y| + |pairShift g h y| := by
        have := abs_add_le (pairShift ζ Q y - pairShift g h y) (pairShift g h y)
        simpa using this
    _ < ε := by linarith

theorem integrable_pair_shift {ζ : Space → Space} (hζ : MemLp ζ 2 volume) (κ : Space → ℝ) (hκ : Continuous κ)
    (hκc : HasCompactSupport κ) (F : Space → ℝ) (hF : MemLp F 2 volume) :
    Integrable (fun x => ‖ζ x‖ * ‖∫ y, κ y * F (x + y)‖) volume := by
  have hFm : AEStronglyMeasurable (fun p : Space × Space => F (p.1 + p.2)) (volume.prod volume) :=
    hF.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_add volume volume)
  have hζm : AEStronglyMeasurable (fun p : Space × Space => ζ p.1) (volume.prod volume) := hζ.1.comp_fst
  have hm : AEStronglyMeasurable (fun p : Space × Space => κ p.2 * F (p.1 + p.2)) (volume.prod volume) :=
    (hκ.comp continuous_snd).aestronglyMeasurable.mul hFm
  have hm2 : AEStronglyMeasurable (fun p : Space × Space => ‖ζ p.1‖ * ‖κ p.2 * F (p.1 + p.2)‖)
      (volume.prod volume) := hζm.norm.mul hm.norm
  have hprod : Integrable (fun p : Space × Space => ‖ζ p.1‖ * ‖κ p.2 * F (p.1 + p.2)‖)
      (volume.prod volume) := by
    rw [integrable_prod_iff' hm2]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · have h1 : Integrable (fun x => ‖ζ x‖ * ‖F (x + y)‖) volume :=
        hζ.norm.integrable_mul (hF.comp_measurePreserving (measurePreserving_add_right volume y)).norm
      refine (h1.const_mul ‖κ y‖).congr (Eventually.of_forall fun x => ?_)
      simp only [norm_mul]
      ring
    · have hb : Integrable (fun y => ‖κ y‖ * (sq2' ζ * sq2' F)) volume :=
        ((hκ.integrable_of_hasCompactSupport hκc).norm).mul_const _
      refine hb.mono' (hm2.norm.prod_swap.integral_prod_right') (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
      have he : (fun x => ‖‖ζ x‖ * ‖κ y * F (x + y)‖‖) = fun x => ‖κ y‖ * (‖ζ x‖ * ‖F (x + y)‖) := by
        funext x
        simp only [norm_mul, norm_norm]
        ring
      rw [he, integral_const_mul]
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
      have ha' : MemLp ζ (ENNReal.ofReal 2) volume := by simpa using hζ
      have hb' : MemLp (fun x => F (x + y)) (ENNReal.ofReal 2) volume := by
        have := hF.comp_measurePreserving (measurePreserving_add_right volume y)
        simpa [Function.comp_def] using this
      calc ∫ x, ‖ζ x‖ * ‖F (x + y)‖ = ∫ x, ‖‖ζ x‖‖ * ‖F (x + y)‖ := by simp only [norm_norm]
        _ ≤ sq2' (fun x => ‖ζ x‖) * sq2' (fun x => F (x + y)) := by
            unfold sq2'
            exact integral_mul_norm_le_Lp_mul_Lq hpq ha'.norm hb'
        _ = sq2' ζ * sq2' F := by
          unfold sq2'
          simp only [norm_norm]
          rw [integral_add_right_eq_self (fun x => ‖F x‖ ^ (2 : ℝ)) y]
  refine hprod.integral_prod_left.mono' (hζ.1.norm.mul (hm.integral_prod_right').norm)
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  show ‖ζ x‖ * ‖∫ y, κ y * F (x + y)‖ ≤ ∫ y, ‖ζ x‖ * ‖κ y * F (x + y)‖
  calc ‖ζ x‖ * ‖∫ y, κ y * F (x + y)‖ ≤ ‖ζ x‖ * ∫ y, ‖κ y * F (x + y)‖ :=
        mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _) (norm_nonneg _)
    _ = ∫ y, ‖ζ x‖ * ‖κ y * F (x + y)‖ := (integral_const_mul _ _).symm

private theorem grad_norm_le (g : Space → ℝ) (x : Space) : ‖gradientAt g x‖ ≤ 3 * ‖fderiv ℝ g x‖ := by
  unfold gradientAt
  refine (norm_sum_le _ _).trans ?_
  have hu : ∀ i : Fin 3, ‖unitVector i‖ = 1 := fun i => by simp [unitVector]
  have : ∀ i : Fin 3, ‖fderiv ℝ g x (unitVector i) • unitVector i‖ ≤ ‖fderiv ℝ g x‖ := by
    intro i
    rw [norm_smul, hu, mul_one]
    calc ‖fderiv ℝ g x (unitVector i)‖ ≤ ‖fderiv ℝ g x‖ * ‖unitVector i‖ := (fderiv ℝ g x).le_opNorm _
      _ = _ := by rw [hu, mul_one]
  calc ∑ i, ‖fderiv ℝ g x (unitVector i) • unitVector i‖ ≤ ∑ _i : Fin 3, ‖fderiv ℝ g x‖ :=
        Finset.sum_le_sum fun i _ => this i
    _ = 3 * ‖fderiv ℝ g x‖ := by simp

private theorem grad_mul {a b : Space → ℝ} {x : Space} (ha : DifferentiableAt ℝ a x)
    (hb : DifferentiableAt ℝ b x) :
    gradientAt (fun y => a y * b y) x = a x • gradientAt b x + b x • gradientAt a x := by
  unfold gradientAt
  have h : HasFDerivAt (fun y => a y * b y) (a x • fderiv ℝ b x + b x • fderiv ℝ a x) x :=
    ha.hasFDerivAt.mul hb.hasFDerivAt
  rw [h.fderiv]
  simp [Finset.sum_add_distrib, Finset.smul_sum, add_smul, mul_smul]

private theorem continuous_grad {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) : Continuous (gradientAt g) := by
  unfold gradientAt
  exact continuous_finsetSum _ fun i _ =>
    ((hg.continuous_fderiv (by simp)).clm_apply continuous_const).smul continuous_const

theorem cut_pair {ζ : Space → Space} (hζ : IsSolenoidalL2 ζ) (f : Space → ℝ) (hf : ContDiff ℝ ∞ f)
    (hf1 : Integrable (fun x => ‖ζ x‖ * ‖f x‖) volume)
    (hd1 : ∀ j : Fin 3, Integrable (fun x => ‖ζ x‖ * ‖fderiv ℝ f x (unitVector j)‖) volume) :
    ∫ x, inner ℝ (ζ x) (gradientAt f x) = 0 := by
  obtain ⟨c, hc⟩ := norm_fderiv_radialCutoff_le
  have hc0 : 0 ≤ c := by
    have := hc 1 one_pos 0
    rw [div_one] at this
    exact (norm_nonneg _).trans this
  have hr : ∀ n : ℕ, (0 : ℝ) < (n : ℝ) + 1 := fun n => by positivity
  have hχs : ∀ n : ℕ, ContDiff ℝ ∞ (radialCutoff ((n : ℝ) + 1)) := fun n => contDiff_radialCutoff (hr n)
  have htest : ∀ n : ℕ, IsTestScalar (fun y => radialCutoff ((n : ℝ) + 1) y * f y) := fun n =>
    ⟨(hχs n).mul hf, (hasCompactSupport_radialCutoff (hr n)).mul_right⟩
  have hzero : ∀ n : ℕ, ∫ x, inner ℝ (ζ x) (gradientAt (fun y => radialCutoff ((n : ℝ) + 1) y * f y) x) = 0 :=
    fun n => hζ.2 _ (htest n)
  have hdf : Differentiable ℝ f := hf.differentiable (by simp)
  have hlim := tendsto_integral_of_dominated_convergence
    (fun x => ∑ j : Fin 3, ‖ζ x‖ * ‖fderiv ℝ f x (unitVector j)‖ + 3 * c * (‖ζ x‖ * ‖f x‖))
    (F := fun (n : ℕ) x => inner ℝ (ζ x) (gradientAt (fun y => radialCutoff ((n : ℝ) + 1) y * f y) x))
    (f := fun x => inner ℝ (ζ x) (gradientAt f x))
    (fun n => hζ.1.1.inner (continuous_grad (htest n).1).aestronglyMeasurable)
    ((integrable_finsetSum _ fun j _ => hd1 j).add (hf1.const_mul _))
    (fun n => Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]
      refine (abs_real_inner_le_norm _ _).trans ?_
      rw [grad_mul ((hχs n).differentiable (by simp) x) (hdf x)]
      have h0 : ‖ζ x‖ * ‖gradientAt f x‖ ≤ ∑ j : Fin 3, ‖ζ x‖ * ‖fderiv ℝ f x (unitVector j)‖ := by
        rw [← Finset.mul_sum]
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        unfold gradientAt
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        congr 1
        funext j
        rw [norm_smul]
        simp [unitVector]
      have h1 : ‖radialCutoff ((n : ℝ) + 1) x • gradientAt f x‖ ≤ ‖gradientAt f x‖ := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (radialCutoff_nonneg _ _)]
        exact mul_le_of_le_one_left (norm_nonneg _) (radialCutoff_le_one _ _)
      have h2 : ‖f x • gradientAt (radialCutoff ((n : ℝ) + 1)) x‖ ≤ 3 * c * ‖f x‖ := by
        rw [norm_smul]
        have hg := grad_norm_le (radialCutoff ((n : ℝ) + 1)) x
        have hb := hc _ (hr n) x
        have hcn : c / ((n : ℝ) + 1) ≤ c := div_le_self hc0 (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)])
        nlinarith [norm_nonneg (f x), norm_nonneg (fderiv ℝ (radialCutoff ((n : ℝ) + 1)) x),
          norm_nonneg (gradientAt (radialCutoff ((n : ℝ) + 1)) x)]
      have h3 := norm_add_le (radialCutoff ((n : ℝ) + 1) x • gradientAt f x)
        (f x • gradientAt (radialCutoff ((n : ℝ) + 1)) x)
      nlinarith [norm_nonneg (ζ x)])
    (Eventually.of_forall fun x => by
      obtain ⟨N, hN⟩ := exists_nat_gt ‖x‖
      apply tendsto_const_nhds.congr'
      rw [EventuallyEq, eventually_atTop]
      refine ⟨N, fun n hn => ?_⟩
      have hnR : (N : ℝ) ≤ n := by exact_mod_cast hn
      have hev : (fun y => radialCutoff ((n : ℝ) + 1) y * f y) =ᶠ[𝓝 x] f := by
        have hb : Metric.ball (0 : Space) ((n : ℝ) + 1) ∈ 𝓝 x :=
          Metric.isOpen_ball.mem_nhds (by rw [Metric.mem_ball, dist_zero_right]; linarith)
        filter_upwards [hb] with y hy
        rw [Metric.mem_ball, dist_zero_right] at hy
        rw [radialCutoff_eq_one (hr n) hy.le, one_mul]
      have hg : gradientAt (fun y => radialCutoff ((n : ℝ) + 1) y * f y) x = gradientAt f x := by
        unfold gradientAt
        rw [hev.fderiv_eq]
      rw [hg])
  have h0 : Tendsto (fun n : ℕ => ∫ x, inner ℝ (ζ x) (gradientAt (fun y => radialCutoff ((n : ℝ) + 1) y * f y) x))
      atTop (𝓝 0) := by
    simp_rw [hzero]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hlim h0

theorem exchange_pair {ζ Q : Space → Space} (hζ : MemLp ζ 2 volume) (hQ : MemLp Q 2 volume)
    (κ : Space → ℝ) (hκ : Continuous κ) (hκc : HasCompactSupport κ) :
    ∫ y, κ y * pairShift ζ Q y = ∫ x, inner ℝ (ζ x) (∫ y, κ y • Q (x + y)) := by
  have hint : ∀ x, Integrable (fun y => κ y • Q (x + y)) volume := fun x =>
    ((hQ.comp_measurePreserving (measurePreserving_add_left volume x)).locallyIntegrable
      (by norm_num)).integrable_smul_left_of_hasCompactSupport hκ hκc
  have hR : ∀ x, inner ℝ (ζ x) (∫ y, κ y • Q (x + y)) = ∫ y, κ y * inner ℝ (ζ x) (Q (x + y)) := by
    intro x
    rw [← integral_inner (hint x)]
    simp [inner_smul_right]
  simp_rw [hR]
  unfold pairShift
  simp_rw [← integral_const_mul]
  have hQm : AEStronglyMeasurable (fun p : Space × Space => Q (p.2 + p.1)) (volume.prod volume) :=
    hQ.1.comp_quasiMeasurePreserving (quasiMeasurePreserving_add_swap volume volume)
  have hm : AEStronglyMeasurable (fun p : Space × Space => κ p.1 * inner ℝ (ζ p.2) (Q (p.2 + p.1)))
      (volume.prod volume) :=
    have hζm : AEStronglyMeasurable (fun p : Space × Space => ζ p.2) (volume.prod volume) :=
      hζ.1.comp_snd
    (hκ.comp continuous_fst).aestronglyMeasurable.mul (hζm.inner (𝕜 := ℝ) hQm)
  have hprod : Integrable (fun p : Space × Space => κ p.1 * inner ℝ (ζ p.2) (Q (p.2 + p.1)))
      (volume.prod volume) := by
    rw [integrable_prod_iff hm]
    refine ⟨Eventually.of_forall fun y => (integrable_pair hζ (memLp_shift hQ y)).const_mul (κ y), ?_⟩
    have hb : Integrable (fun y => |κ y| * (sq2 ζ * sq2 Q)) volume :=
      ((hκ.integrable_of_hasCompactSupport hκc).abs).mul_const _
    refine hb.mono' hm.norm.integral_prod_right' (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]
    simp only [norm_mul, Real.norm_eq_abs]
    rw [integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have h1 : Integrable (fun x => ‖ζ x‖ * ‖Q (x + y)‖) volume :=
      hζ.norm.integrable_mul (memLp_shift hQ y).norm
    have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
    have ha' : MemLp ζ (ENNReal.ofReal 2) volume := by simpa using hζ
    have hb' : MemLp (fun x => Q (x + y)) (ENNReal.ofReal 2) volume := by simpa using memLp_shift hQ y
    calc ∫ x, |inner ℝ (ζ x) (Q (x + y))| ≤ ∫ x, ‖ζ x‖ * ‖Q (x + y)‖ :=
          integral_mono (integrable_pair hζ (memLp_shift hQ y)).abs h1
            (fun x => abs_real_inner_le_norm _ _)
      _ ≤ sq2 ζ * sq2 (fun x => Q (x + y)) := integral_mul_norm_le_Lp_mul_Lq hpq ha' hb'
      _ = sq2 ζ * sq2 Q := by rw [sq2_shift]
  exact integral_integral_swap (f := fun y x => κ y * inner ℝ (ζ x) (Q (x + y))) hprod

private abbrev scalFlip : ℝ →L[ℝ] ℝ →L[ℝ] ℝ :=
  (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] ℝ →L[ℝ] ℝ).flip

private theorem scalFlip_apply (a r : ℝ) : scalFlip a r = r * a := rfl

private theorem shift_conv (F h : Space → ℝ) :
    (fun x => ∫ y, h y * F (x + y)) = F ⋆[scalFlip, volume] (fun u => h (-u)) := by
  funext x
  rw [convolution_def]
  simp only [scalFlip_apply]
  conv_lhs => rw [← integral_sub_right_eq_self (μ := volume) _ x]
  congr 1
  funext t
  rw [neg_sub, add_sub_cancel]

theorem deriv_shift (φ : Space → ℝ) (hφ : IsTestScalar φ) (F : Space → ℝ) (hF : MemLp F 2 volume) :
    ContDiff ℝ ∞ (fun x => ∫ y, φ y * F (x + y)) ∧ ∀ x (j : Fin 3),
      fderiv ℝ (fun x => ∫ y, φ y * F (x + y)) x (unitVector j) =
        -∫ y, fderiv ℝ φ y (unitVector j) * F (x + y) := by
  have hFloc : LocallyIntegrable F volume := hF.locallyIntegrable (by norm_num)
  have hgs : ContDiff ℝ ∞ (fun u : Space => φ (-u)) := hφ.1.comp contDiff_neg
  have hgc : HasCompactSupport (fun u : Space => φ (-u)) := hφ.2.comp_homeomorph (Homeomorph.neg Space)
  refine ⟨by rw [shift_conv F φ]; exact hgc.contDiff_convolution_right scalFlip hFloc hgs, fun x j => ?_⟩
  rw [shift_conv F φ]
  have h1 : ContDiff ℝ 1 (fun u : Space => φ (-u)) := hgs.of_le (by exact_mod_cast le_top)
  rw [(hgc.hasFDerivAt_convolution_right scalFlip hFloc h1 x).fderiv,
    convolution_precompR_apply scalFlip hFloc (hgc.fderiv ℝ) (h1.continuous_fderiv one_ne_zero) x
      (unitVector j)]
  have hgd : (fun a => fderiv ℝ (fun u : Space => φ (-u)) a (unitVector j)) =
      fun a => -(fderiv ℝ φ (-a) (unitVector j)) := by
    funext a
    have : HasFDerivAt (fun u : Space => φ (-u)) ((fderiv ℝ φ (-a)).comp (-ContinuousLinearMap.id ℝ Space)) a :=
      ((hφ.1.differentiable (by simp)).differentiableAt).hasFDerivAt.comp a ((hasFDerivAt_id a).neg)
    rw [this.fderiv]
    simp
  rw [hgd]
  have := congrFun (shift_conv F (fun y => -(fderiv ℝ φ y (unitVector j)))) x
  beta_reduce at this
  rw [← this]
  simp [neg_mul, integral_neg]

private theorem test_dir' {φ : Space → ℝ} (hφ : IsTestScalar φ) (v : Space) :
    Continuous (fun y => fderiv ℝ φ y v) ∧ HasCompactSupport (fun y => fderiv ℝ φ y v) :=
  ⟨(hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const, hφ.2.fderiv_apply (𝕜 := ℝ) v⟩

private theorem curl_shift {Q : Space → Space}
    (hcurl : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j k : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector k) * inner ℝ (Q y) (unitVector j) =
        ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (Q y) (unitVector k))
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (x : Space) (j k : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector k) * inner ℝ (Q (x + y)) (unitVector j) =
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (Q (x + y)) (unitVector k) := by
  have hχ : IsTestScalar (fun z => φ (z - x)) :=
    ⟨hφ.1.comp (contDiff_id.sub contDiff_const), hφ.2.comp_homeomorph (Homeomorph.subRight x)⟩
  have hder : ∀ z v, fderiv ℝ (fun z => φ (z - x)) z v = fderiv ℝ φ (z - x) v := by
    intro z v
    have hψd : DifferentiableAt ℝ φ (z - x) :=
      (hφ.1.differentiable (by simp)).differentiableAt
    have : HasFDerivAt (fun z => φ (z - x))
        ((fderiv ℝ φ (z - x)).comp (ContinuousLinearMap.id ℝ Space - 0)) z :=
      hψd.hasFDerivAt.comp z ((hasFDerivAt_id z).sub (hasFDerivAt_const x z))
    rw [this.fderiv]
    simp
  have h := hcurl _ hχ j k
  simp only [hder] at h
  have t1 := integral_sub_right_eq_self (μ := volume)
    (fun y => fderiv ℝ φ y (unitVector k) * inner ℝ (Q (x + y)) (unitVector j)) x
  have t2 := integral_sub_right_eq_self (μ := volume)
    (fun y => fderiv ℝ φ y (unitVector j) * inner ℝ (Q (x + y)) (unitVector k)) x
  simp only [add_sub_cancel] at t1 t2
  rw [← t1, ← t2]
  exact h

theorem integral_deriv_pairShift {ζ Q : Space → Space} (hζ : IsSolenoidalL2 ζ) (hQ : MemLp Q 2 volume)
    (hcurl : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j k : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector k) * inner ℝ (Q y) (unitVector j) =
        ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (Q y) (unitVector k))
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (k : Fin 3) :
    ∫ y, fderiv ℝ φ y (unitVector k) * pairShift ζ Q y = 0 := by
  obtain ⟨hκ, hκc⟩ := test_dir' hφ (unitVector k)
  rw [exchange_pair hζ.1 hQ _ hκ hκc]
  have hQk : MemLp (fun z => inner ℝ (Q z) (unitVector k)) 2 volume := by
    exact hQ.inner_const (𝕜 := ℝ) (unitVector k)
  obtain ⟨hW, hWd⟩ := deriv_shift φ hφ _ hQk
  have hW1 := integrable_pair_shift hζ.1 φ hφ.1.continuous hφ.2 _ hQk
  have hd1 : ∀ j : Fin 3, Integrable (fun x => ‖ζ x‖ * ‖fderiv ℝ (fun x => ∫ y, φ y * inner ℝ (Q (x + y)) (unitVector k)) x
      (unitVector j)‖) volume := by
    intro j
    simp_rw [hWd, norm_neg]
    exact integrable_pair_shift hζ.1 _ (test_dir' hφ (unitVector j)).1 (test_dir' hφ (unitVector j)).2 _ hQk
  have hcut := cut_pair hζ _ hW hW1 hd1
  have hpt : ∀ x, inner ℝ (ζ x) (∫ y, fderiv ℝ φ y (unitVector k) • Q (x + y)) =
      -inner ℝ (ζ x) (gradientAt (fun x => ∫ y, φ y * inner ℝ (Q (x + y)) (unitVector k)) x) := by
    intro x
    rw [← inner_neg_right]
    congr 1
    have hint : Integrable (fun y => fderiv ℝ φ y (unitVector k) • Q (x + y)) volume :=
      ((hQ.comp_measurePreserving (measurePreserving_add_left volume x)).locallyIntegrable
        (by norm_num)).integrable_smul_left_of_hasCompactSupport hκ hκc
    ext i
    have hcomp : ∀ v : Space, v i = inner ℝ (unitVector i) v := fun v => by
      simp [unitVector, EuclideanSpace.inner_single_left]
    have hg : ∀ (f : Space → ℝ) (z : Space), (gradientAt f z) i = fderiv ℝ f z (unitVector i) := by
      intro f z
      simp [gradientAt, unitVector, Pi.single_apply]
    rw [PiLp.neg_apply, hg, hWd x i, neg_neg, hcomp, ← integral_inner hint,
      ← curl_shift hcurl φ hφ x i k]
    congr 1
    funext y
    rw [inner_smul_right, real_inner_comm]
  simp_rw [hpt, integral_neg, hcut, neg_zero]

end GradientOrthogonalInternal

end SteadyCert

end Breakdown
