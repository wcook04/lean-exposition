import Breakdown.Frac.StSpace
import Breakdown.Frac.OpIntegrable
import Breakdown.Frac.OpCovariance
import Breakdown.Frac.OpNormalizer
import Breakdown.Uniqueness.CutoffBounds

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.SpaceLowerBound.Internal


theorem contDiff_two_of {f : Space → ℝ} (h : ContDiff ℝ ∞ f) : ContDiff ℝ 2 f :=
  h.of_le (WithTop.coe_le_coe.mpr le_top)

theorem unitVector_zero_ne : unitVector 0 ≠ 0 := by
  intro h
  have := congrArg (fun v : Space => v 0) h
  simp [unitVector] at this

theorem norm_unitVector_zero : ‖unitVector 0‖ = 1 := by
  simp [unitVector]

theorem remainder_smul_const (g : Space → ℝ) (hg : ContDiff ℝ 2 g) (e x z : Space) :
    secondOrderRemainder (fun y => g y • e) x z = scalarSecondOrderRemainder g x z • e := by
  set L : ℝ →L[ℝ] Space := (ContinuousLinearMap.id ℝ ℝ).smulRight e with hLdef
  have hL : (fun y => g y • e) = L ∘ g := by
    funext y
    simp [hLdef]
  have h1 : fderiv ℝ (L ∘ g) x = L.comp (fderiv ℝ g x) :=
    (L.hasFDerivAt.comp x ((hg.differentiable (by norm_num)).differentiableAt.hasFDerivAt)).fderiv
  have h2 : iteratedFDeriv ℝ 2 (L ∘ g) x =
      L.compContinuousMultilinearMap (iteratedFDeriv ℝ 2 g x) :=
    L.iteratedFDeriv_comp_left hg.contDiffAt le_rfl
  rw [secondOrderRemainder, scalarSecondOrderRemainder, hL, h1, h2]
  simp [hLdef, sub_smul, mul_smul]

theorem power_smul_const (α : ℝ) (g : Space → ℝ) (hg : ContDiff ℝ 2 g) (e x : Space) :
    fractionalPowerAt α (fun y => g y • e) x = scalarPowerAt α g x • e := by
  simp only [fractionalPowerAt, scalarPowerAt, remainder_smul_const g hg, smul_smul,
    integral_smul_const]

theorem scalar_comp_smul (h4 : CovarianceStatement) (α : ℝ) (g : Space → ℝ) (hg : ContDiff ℝ 2 g)
    (l : ℝ) (hl : 0 < l) (y : Space) :
    scalarPowerAt α (fun x => g (l • x)) y = l ^ (2 * α) * scalarPowerAt α g (l • y) := by
  have hgl : ContDiff ℝ 2 (fun x => g (l • x)) := hg.comp (contDiff_id.const_smul l)
  have key := (h4 α (fun x => g x • unitVector 0) (hg.smul contDiff_const)).1 l hl y
  have e1 := power_smul_const α (fun x => g (l • x)) hgl (unitVector 0) y
  have e2 := power_smul_const α g hg (unitVector 0) (l • y)
  try simp only at key
  rw [e1, e2, smul_smul] at key
  exact smul_left_injective ℝ unitVector_zero_ne key

theorem scalar_bounded (h3 : FracCompactDecayStatement) {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2)
    (g : Space → ℝ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, |scalarPowerAt α g x| ≤ C := by
  obtain ⟨_, C, hC⟩ := h3 α hα1 hα2 (fun y => g y • unitVector 0) (hg.smul contDiff_const)
    hgc.smul_right
  refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
  have h := hC x
  rw [power_smul_const α g (contDiff_two_of hg), norm_smul, norm_unitVector_zero, mul_one,
    Real.norm_eq_abs] at h
  have hp0 : 0 ≤ (1 + ‖x‖) ^ (-(3 + 2 * α)) := Real.rpow_nonneg (by positivity) _
  have hp1 : (1 + ‖x‖) ^ (-(3 + 2 * α)) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg x]) (by linarith)
  calc |scalarPowerAt α g x| ≤ C * (1 + ‖x‖) ^ (-(3 + 2 * α)) := h
    _ ≤ max C 0 * (1 + ‖x‖) ^ (-(3 + 2 * α)) :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hp0
    _ ≤ max C 0 := mul_le_of_le_one_right (le_max_right _ _) hp1

theorem radialCutoff_eq_scale {r : ℝ} (hr : 0 < r) (y : Space) :
    radialCutoff r y = radialCutoff 1 (r⁻¹ • y) := by
  simp only [radialCutoff, norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hr, div_one]
  rw [div_eq_inv_mul]

theorem scalar_term_bound (h3 : FracCompactDecayStatement) (h4 : CovarianceStatement)
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 3 / 2) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ r : ℝ, 1 ≤ r → ∀ x : Space,
      |scalarPowerAt α (fun y => (radialCutoff r y ^ 2) ^ 2) x
        - 2 * radialCutoff r x ^ 2 * scalarPowerAt α (fun y => radialCutoff r y ^ 2) x| ≤ c / r ^ 2 := by
  have hη : ContDiff ℝ ∞ (radialCutoff 1) := contDiff_radialCutoff one_pos
  have hηc : HasCompactSupport (radialCutoff 1) := hasCompactSupport_radialCutoff one_pos
  set g₁ : Space → ℝ := fun y => (radialCutoff 1 y ^ 2) ^ 2 with hg₁
  set g₂ : Space → ℝ := fun y => radialCutoff 1 y ^ 2 with hg₂
  have hg₁s : ContDiff ℝ ∞ g₁ := (hη.pow 2).pow 2
  have hg₂s : ContDiff ℝ ∞ g₂ := hη.pow 2
  have hg₁c : HasCompactSupport g₁ :=
    hηc.comp_left (g := fun t : ℝ => (t ^ 2) ^ 2) (by norm_num)
  have hg₂c : HasCompactSupport g₂ := hηc.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  obtain ⟨C₁, hC₁, hb₁⟩ := scalar_bounded h3 hα1 hα2 g₁ hg₁s hg₁c
  obtain ⟨C₂, hC₂, hb₂⟩ := scalar_bounded h3 hα1 hα2 g₂ hg₂s hg₂c
  refine ⟨C₁ + 2 * C₂, by positivity, fun r hr x => ?_⟩
  have hr0 : 0 < r := by linarith
  have hri : 0 < r⁻¹ := inv_pos.2 hr0
  have hf₁ : (fun y => (radialCutoff r y ^ 2) ^ 2) = fun y => g₁ (r⁻¹ • y) := by
    funext y; simp only [hg₁, radialCutoff_eq_scale hr0 y]
  have hf₂ : (fun y => radialCutoff r y ^ 2) = fun y => g₂ (r⁻¹ • y) := by
    funext y; simp only [hg₂, radialCutoff_eq_scale hr0 y]
  have hx : radialCutoff r x ^ 2 = g₂ (r⁻¹ • x) := by simp only [hg₂, radialCutoff_eq_scale hr0 x]
  rw [hf₁, hf₂, hx, scalar_comp_smul h4 α g₁ (contDiff_two_of hg₁s) r⁻¹ hri,
    scalar_comp_smul h4 α g₂ (contDiff_two_of hg₂s) r⁻¹ hri]
  set y := r⁻¹ • x
  have hq0 : 0 ≤ g₂ y := by simp only [hg₂]; positivity
  have hq1 : g₂ y ≤ 1 := by
    simp only [hg₂]; exact pow_le_one₀ (radialCutoff_nonneg 1 y) (radialCutoff_le_one 1 y)
  have hp : r⁻¹ ^ (2 * α) ≤ 1 / r ^ 2 := by
    have := Real.rpow_le_rpow_of_exponent_ge hri (inv_le_one_of_one_le₀ hr) (by linarith :
      (2 : ℝ) ≤ 2 * α)
    rw [Real.rpow_two, inv_pow] at this
    simpa [one_div] using this
  have hp0 : 0 ≤ r⁻¹ ^ (2 * α) := Real.rpow_nonneg hri.le _
  have he : r⁻¹ ^ (2 * α) * scalarPowerAt α g₁ y - 2 * g₂ y * (r⁻¹ ^ (2 * α) * scalarPowerAt α g₂ y)
      = r⁻¹ ^ (2 * α) * (scalarPowerAt α g₁ y - 2 * g₂ y * scalarPowerAt α g₂ y) := by ring
  rw [he, abs_mul, abs_of_nonneg hp0]
  have hin : |scalarPowerAt α g₁ y - 2 * g₂ y * scalarPowerAt α g₂ y| ≤ C₁ + 2 * C₂ := by
    refine (abs_sub _ _).trans (add_le_add (hb₁ y) ?_)
    rw [abs_mul, abs_mul, abs_of_nonneg hq0, abs_two]
    have := hb₂ y
    nlinarith [abs_nonneg (scalarPowerAt α g₂ y)]
  calc r⁻¹ ^ (2 * α) * |scalarPowerAt α g₁ y - 2 * g₂ y * scalarPowerAt α g₂ y|
      ≤ (1 / r ^ 2) * (C₁ + 2 * C₂) :=
        mul_le_mul hp hin (abs_nonneg _) (by positivity)
    _ = (C₁ + 2 * C₂) / r ^ 2 := by ring


def nearFarKernel (α d : ℝ) : ℝ := if d < 1 then d ^ (-(2 + 4 * (α - 1))) else d ^ (-(1 + 2 * α))

def nearKernel (d : ℝ) : ℝ := if d < 1 then d ^ (-4 : ℝ) else 0

theorem nearFarKernel_nonneg (α d : ℝ) (hd : 0 ≤ d) : 0 ≤ nearFarKernel α d := by
  unfold nearFarKernel; split_ifs <;> exact Real.rpow_nonneg hd _

theorem nearKernel_nonneg (d : ℝ) (hd : 0 ≤ d) : 0 ≤ nearKernel d := by
  unfold nearKernel; split_ifs
  · exact Real.rpow_nonneg hd _
  · exact le_rfl

theorem amgm_step {t X Y Z : ℝ} (hY : 0 < Y) (hXYZ : X ^ 2 = Y * Z) :
    2 * t * X ≤ t ^ 2 * Y + Z := by
  have h : 0 ≤ Y * (t ^ 2 * Y + Z - 2 * t * X) := by nlinarith [sq_nonneg (t * Y - X)]
  have := (mul_nonneg_iff_of_pos_left hY).1 h
  linarith

theorem sq_norm_sub_le (p q : Space) : ‖p - q‖ ^ 2 ≤ 2 * ‖p‖ ^ 2 + 2 * ‖q‖ ^ 2 := by
  have := norm_sub_le p q
  nlinarith [norm_nonneg p, norm_nonneg q, norm_nonneg (p - q), sq_nonneg (‖p‖ - ‖q‖)]

theorem pointwise_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {c : ℝ} (hc0 : 0 ≤ c)
    (hc : ∀ r, 0 < r → ∀ x y, |radialCutoff r x - radialCutoff r y| ≤ c * ‖x - y‖ / r)
    {r : ℝ} (hr : 1 ≤ r) (w : Space → Space) (x y : Space) :
    (radialCutoff r x ^ 2 - radialCutoff r y ^ 2) ^ 2 * ‖w x - w y‖ ^ 2 * ‖x - y‖ ^ (-(3 + 2 * α)) ≤
      (8 * c ^ 2 + 8 * c ^ 4) / r ^ 2 *
        (nearKernel ‖x - y‖ * ‖radialCutoff r x ^ 2 • w x - radialCutoff r y ^ 2 • w y‖ ^ 2
          + nearFarKernel α ‖x - y‖ * (‖w x‖ ^ 2 + ‖w y‖ ^ 2)) := by
  have hr0 : 0 < r := by linarith
  have hδ := hc r hr0 x y
  set d := ‖x - y‖ with hd
  set a₁ := radialCutoff r x with ha₁d
  set a₂ := radialCutoff r y with ha₂d
  set u := w x
  set v := w y
  have ha₁ : 0 ≤ a₁ := radialCutoff_nonneg r x
  have ha₁' : a₁ ≤ 1 := radialCutoff_le_one r x
  have ha₂ : 0 ≤ a₂ := radialCutoff_nonneg r y
  have ha₂' : a₂ ≤ 1 := radialCutoff_le_one r y
  have hK : 0 ≤ (8 * c ^ 2 + 8 * c ^ 4) / r ^ 2 := by positivity
  have hd0 : 0 ≤ d := norm_nonneg _
  rcases eq_or_lt_of_le hd0 with h0 | hpos
  · have hxy : x = y := by
      have : ‖x - y‖ = 0 := h0.symm
      rwa [norm_eq_zero, sub_eq_zero] at this
    have hz : a₁ = a₂ := by simp only [ha₁d, ha₂d, hxy]
    rw [hz, sub_self]
    have : 0 ≤ (8 * c ^ 2 + 8 * c ^ 4) / r ^ 2 *
        (nearKernel d * ‖a₂ ^ 2 • u - a₂ ^ 2 • v‖ ^ 2 + nearFarKernel α d * (‖u‖ ^ 2 + ‖v‖ ^ 2)) :=
      mul_nonneg hK (add_nonneg (mul_nonneg (nearKernel_nonneg d hd0) (by positivity))
        (mul_nonneg (nearFarKernel_nonneg α d hd0) (by positivity)))
    simpa using this
  have hδ2 : (a₁ - a₂) ^ 2 ≤ c ^ 2 * d ^ 2 / r ^ 2 := by
    have h := sq_le_sq' (abs_le.1 hδ).1 (abs_le.1 hδ).2
    calc (a₁ - a₂) ^ 2 ≤ (c * d / r) ^ 2 := h
      _ = c ^ 2 * d ^ 2 / r ^ 2 := by ring
  have hr2 : 1 ≤ r ^ 2 := one_le_pow₀ hr
  have hcd : c ^ 2 * d ^ 2 / r ^ 2 ≤ c ^ 2 * d ^ 2 := div_le_self (by positivity) hr2
  set q := (a₁ ^ 2 - a₂ ^ 2) ^ 2 with hqd
  have hq4 : q ≤ 4 * (c ^ 2 * d ^ 2 / r ^ 2) := by
    have e : q = (a₁ - a₂) ^ 2 * (a₁ + a₂) ^ 2 := by rw [hqd]; ring
    have h2 : (a₁ + a₂) ^ 2 ≤ 4 := by nlinarith
    rw [e]
    nlinarith [sq_nonneg (a₁ - a₂), sq_nonneg (a₁ + a₂)]
  have hq2 : q ≤ 2 * (c ^ 2 * d ^ 2 / r ^ 2) * (a₁ ^ 2 + a₂ ^ 2) := by
    have e : q = (a₁ - a₂) ^ 2 * (a₁ + a₂) ^ 2 := by rw [hqd]; ring
    have h2 : (a₁ + a₂) ^ 2 ≤ 2 * (a₁ ^ 2 + a₂ ^ 2) := by nlinarith [sq_nonneg (a₁ - a₂)]
    rw [e]
    calc (a₁ - a₂) ^ 2 * (a₁ + a₂) ^ 2 ≤ (c ^ 2 * d ^ 2 / r ^ 2) * (2 * (a₁ ^ 2 + a₂ ^ 2)) :=
          mul_le_mul hδ2 h2 (sq_nonneg _) (by positivity)
      _ = _ := by ring
  have hΔ : ‖u - v‖ ^ 2 ≤ 2 * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
    have := sq_norm_sub_le u v; linarith
  set P := d ^ (-(3 + 2 * α)) with hPd
  have hP0 : 0 ≤ P := Real.rpow_nonneg hd0 _
  have hX : P * d ^ 2 = d ^ (-(1 + 2 * α)) := by
    rw [hPd, ← Real.rpow_natCast d 2, ← Real.rpow_add hpos]
    norm_num
    ring_nf
  set X := d ^ (-(1 + 2 * α)) with hXd
  have hX0 : 0 ≤ X := Real.rpow_nonneg hd0 _
  have hN0 : 0 ≤ ‖u‖ ^ 2 + ‖v‖ ^ 2 := by positivity
  by_cases hd1 : d < 1
  · have hnk : nearKernel d = d ^ (-4 : ℝ) := by simp [nearKernel, hd1]
    have hnf : nearFarKernel α d = d ^ (-(2 + 4 * (α - 1))) := by simp [nearFarKernel, hd1]
    rw [hnk, hnf]
    set Y := d ^ (-4 : ℝ) with hYd
    set Z := d ^ (-(2 + 4 * (α - 1))) with hZd
    have hY0 : 0 < Y := Real.rpow_pos_of_pos hpos _
    have hZ0 : 0 ≤ Z := Real.rpow_nonneg hd0 _
    have hXYZ : X ^ 2 = Y * Z := by
      rw [hXd, hYd, hZd, ← Real.rpow_natCast, ← Real.rpow_mul hd0, ← Real.rpow_add hpos]
      congr 1
      push_cast
      ring
    have hYZ : d ^ 2 * Y ≤ Z := by
      have e : d ^ 2 * Y = d ^ (-2 : ℝ) := by
        rw [hYd, ← Real.rpow_natCast d 2, ← Real.rpow_add hpos]
        norm_num
      rw [e, hZd]
      exact Real.rpow_le_rpow_of_exponent_ge hpos hd1.le (by linarith)
    set N := ‖a₁ ^ 2 • u - a₂ ^ 2 • v‖ with hNd
    have hW1 : a₁ ^ 4 * ‖u - v‖ ^ 2 ≤ 2 * N ^ 2 + 2 * q * ‖v‖ ^ 2 := by
      have e : a₁ ^ 2 • (u - v) = (a₁ ^ 2 • u - a₂ ^ 2 • v) - (a₁ ^ 2 - a₂ ^ 2) • v := by
        rw [smul_sub, sub_smul]; abel
      have h := sq_norm_sub_le (a₁ ^ 2 • u - a₂ ^ 2 • v) ((a₁ ^ 2 - a₂ ^ 2) • v)
      rw [← e, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs] at h
      have e2 : (a₁ ^ 2 * ‖u - v‖) ^ 2 = a₁ ^ 4 * ‖u - v‖ ^ 2 := by ring
      have e3 : (|a₁ ^ 2 - a₂ ^ 2| * ‖v‖) ^ 2 = q * ‖v‖ ^ 2 := by rw [mul_pow, sq_abs]
      rw [e2, e3] at h
      linarith
    have hW2 : a₂ ^ 4 * ‖u - v‖ ^ 2 ≤ 2 * N ^ 2 + 2 * q * ‖u‖ ^ 2 := by
      have e : a₂ ^ 2 • (u - v) = (a₁ ^ 2 • u - a₂ ^ 2 • v) - (a₁ ^ 2 - a₂ ^ 2) • u := by
        rw [smul_sub, sub_smul]; abel
      have h := sq_norm_sub_le (a₁ ^ 2 • u - a₂ ^ 2 • v) ((a₁ ^ 2 - a₂ ^ 2) • u)
      rw [← e, norm_smul, norm_smul, Real.norm_of_nonneg (by positivity), Real.norm_eq_abs] at h
      have e2 : (a₂ ^ 2 * ‖u - v‖) ^ 2 = a₂ ^ 4 * ‖u - v‖ ^ 2 := by ring
      have e3 : (|a₁ ^ 2 - a₂ ^ 2| * ‖u‖) ^ 2 = q * ‖u‖ ^ 2 := by rw [mul_pow, sq_abs]
      rw [e2, e3] at h
      linarith
    have hA1 := amgm_step (t := a₁ ^ 2) hY0 hXYZ
    have hA2 := amgm_step (t := a₂ ^ 2) hY0 hXYZ
    have hAM : (a₁ ^ 2 + a₂ ^ 2) * X ≤ (a₁ ^ 4 + a₂ ^ 4) / 2 * Y + Z := by
      have e1 : (a₁ ^ 2) ^ 2 = a₁ ^ 4 := by ring
      have e2 : (a₂ ^ 2) ^ 2 = a₂ ^ 4 := by ring
      rw [e1] at hA1; rw [e2] at hA2
      linarith
    have hqY : q * Y ≤ 4 * c ^ 2 * Z := by
      have h1 : q * Y ≤ 4 * (c ^ 2 * d ^ 2) * Y :=
        mul_le_mul_of_nonneg_right (hq4.trans (by linarith)) hY0.le
      calc q * Y ≤ 4 * (c ^ 2 * d ^ 2) * Y := h1
        _ = 4 * c ^ 2 * (d ^ 2 * Y) := by ring
        _ ≤ 4 * c ^ 2 * Z := mul_le_mul_of_nonneg_left hYZ (by positivity)
    set E := ‖u - v‖ ^ 2 with hEd
    have hE0 : 0 ≤ E := by positivity
    have s1 : q * E * P ≤ 2 * (c ^ 2 / r ^ 2) * ((a₁ ^ 2 + a₂ ^ 2) * X) * E := by
      have : q * E * P ≤ 2 * (c ^ 2 * d ^ 2 / r ^ 2) * (a₁ ^ 2 + a₂ ^ 2) * E * P :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hq2 hE0) hP0
      calc q * E * P ≤ 2 * (c ^ 2 * d ^ 2 / r ^ 2) * (a₁ ^ 2 + a₂ ^ 2) * E * P := this
        _ = 2 * (c ^ 2 / r ^ 2) * ((a₁ ^ 2 + a₂ ^ 2) * (P * d ^ 2)) * E := by ring
        _ = _ := by rw [hX]
    have s2 : ((a₁ ^ 2 + a₂ ^ 2) * X) * E ≤ ((a₁ ^ 4 + a₂ ^ 4) / 2 * Y + Z) * E :=
      mul_le_mul_of_nonneg_right hAM hE0
    have s3 : ((a₁ ^ 4 + a₂ ^ 4) / 2 * Y + Z) * E ≤
        2 * N ^ 2 * Y + (4 * c ^ 2 + 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) * Z := by
      have t1 : (a₁ ^ 4 + a₂ ^ 4) * E ≤ 4 * N ^ 2 + 2 * q * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
        linarith
      have t2 : (a₁ ^ 4 + a₂ ^ 4) / 2 * Y * E ≤ (2 * N ^ 2 + q * (‖u‖ ^ 2 + ‖v‖ ^ 2)) * Y := by
        have := mul_le_mul_of_nonneg_right t1 hY0.le
        linarith
      have t3 : q * (‖u‖ ^ 2 + ‖v‖ ^ 2) * Y ≤ 4 * c ^ 2 * Z * (‖u‖ ^ 2 + ‖v‖ ^ 2) := by
        have := mul_le_mul_of_nonneg_right hqY hN0
        linarith
      have t4 : Z * E ≤ Z * (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := mul_le_mul_of_nonneg_left hΔ hZ0
      linarith
    have hc2 : 0 ≤ c ^ 2 / r ^ 2 := by positivity
    have s4 : 2 * (c ^ 2 / r ^ 2) * (2 * N ^ 2 * Y + (4 * c ^ 2 + 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) * Z) ≤
        (8 * c ^ 2 + 8 * c ^ 4) / r ^ 2 * (Y * N ^ 2 + Z * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
      have hNY : 0 ≤ N ^ 2 * Y := by positivity
      have hNZ : 0 ≤ (‖u‖ ^ 2 + ‖v‖ ^ 2) * Z := by positivity
      have e : (8 * c ^ 2 + 8 * c ^ 4) / r ^ 2 * (Y * N ^ 2 + Z * (‖u‖ ^ 2 + ‖v‖ ^ 2)) =
          2 * (c ^ 2 / r ^ 2) * ((4 + 4 * c ^ 2) * (N ^ 2 * Y) + (4 + 4 * c ^ 2) *
            ((‖u‖ ^ 2 + ‖v‖ ^ 2) * Z)) := by ring
      rw [e]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      linarith [mul_nonneg (sq_nonneg c) hNY, mul_nonneg (sq_nonneg c) hNZ]
    calc q * E * P ≤ 2 * (c ^ 2 / r ^ 2) * ((a₁ ^ 2 + a₂ ^ 2) * X) * E := s1
      _ = 2 * (c ^ 2 / r ^ 2) * (((a₁ ^ 2 + a₂ ^ 2) * X) * E) := by ring
      _ ≤ 2 * (c ^ 2 / r ^ 2) * (2 * N ^ 2 * Y + (4 * c ^ 2 + 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2) * Z) :=
          mul_le_mul_of_nonneg_left (s2.trans s3) (by positivity)
      _ ≤ _ := s4
  · have hnk : nearKernel d = 0 := by simp [nearKernel, hd1]
    have hnf : nearFarKernel α d = X := by simp [nearFarKernel, hd1, hXd]
    rw [hnk, hnf, zero_mul, zero_add]
    have hq' : q ≤ 4 * c ^ 2 * d ^ 2 / r ^ 2 := by
      rw [show 4 * c ^ 2 * d ^ 2 / r ^ 2 = 4 * (c ^ 2 * d ^ 2 / r ^ 2) by ring]; exact hq4
    calc q * ‖u - v‖ ^ 2 * P ≤ (4 * c ^ 2 * d ^ 2 / r ^ 2) * (2 * (‖u‖ ^ 2 + ‖v‖ ^ 2)) * P :=
          mul_le_mul_of_nonneg_right (mul_le_mul hq' hΔ (by positivity) (by positivity)) hP0
      _ = 8 * c ^ 2 / r ^ 2 * ((P * d ^ 2) * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by ring
      _ = 8 * c ^ 2 / r ^ 2 * (X * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by rw [hX]
      _ ≤ (8 * c ^ 2 + 8 * c ^ 4) / r ^ 2 * (X * (‖u‖ ^ 2 + ‖v‖ ^ 2)) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          apply div_le_div_of_nonneg_right _ (by positivity)
          nlinarith [pow_nonneg hc0 4]


theorem sq_integral_le {k : ℝ → ℝ} (hk : Continuous k) :
    (∫ t in (0 : ℝ)..1, k t) ^ 2 ≤ ∫ t in (0 : ℝ)..1, k t ^ 2 := by
  set m := ∫ t in (0 : ℝ)..1, k t with hm
  have hi1 : IntervalIntegrable k volume 0 1 := hk.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (fun t => k t ^ 2) volume 0 1 := (hk.pow 2).intervalIntegrable _ _
  have h0 : 0 ≤ ∫ t in (0 : ℝ)..1, (k t - m) ^ 2 :=
    intervalIntegral.integral_nonneg zero_le_one fun t _ => sq_nonneg _
  have e : (fun t => (k t - m) ^ 2) = fun t => (k t ^ 2 - 2 * m * k t) + m ^ 2 := by
    funext t; ring
  rw [e, intervalIntegral.integral_add (hi2.sub (hi1.const_mul _)) intervalIntegrable_const,
    intervalIntegral.integral_sub hi2 (hi1.const_mul _), intervalIntegral.integral_const_mul,
    intervalIntegral.integral_const, ← hm] at h0
  simp only [sub_zero, smul_eq_mul, one_mul] at h0
  nlinarith

theorem norm_apply_sq_le (L : Space →L[ℝ] Space) (z : Space) :
    ‖L z‖ ^ 2 ≤ ‖z‖ ^ 2 * ∑ i, ‖L (unitVector i)‖ ^ 2 := by
  have hz : z = ∑ i, z i • unitVector i := by
    ext j
    simp [unitVector, Finset.sum_apply, Pi.single_apply]
  have h1 : ‖L z‖ ≤ ∑ i, |z i| * ‖L (unitVector i)‖ := by
    conv_lhs => rw [hz]
    rw [map_sum]
    refine (norm_sum_le _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, norm_smul, Real.norm_eq_abs]
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => |z i|) (fun i => ‖L (unitVector i)‖)
  have hnz : ‖z‖ ^ 2 = ∑ i, |z i| ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp [Real.norm_eq_abs]
  rw [hnz]
  have h0 : 0 ≤ ‖L z‖ := norm_nonneg _
  calc ‖L z‖ ^ 2 ≤ (∑ i, |z i| * ‖L (unitVector i)‖) ^ 2 := pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := h2

theorem pointwise_translation (W : Space → Space) (hW : ContDiff ℝ ∞ W) (x z : Space) :
    ‖W (x + z) - W x‖ ^ 2 ≤
      ‖z‖ ^ 2 * ∫ t in (0 : ℝ)..1, ∑ i, ‖fderiv ℝ W (x + t • z) (unitVector i)‖ ^ 2 := by
  have hd : Differentiable ℝ W := hW.differentiable (by simp)
  have hc : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by simp)
  set h : ℝ → Space := fun t => fderiv ℝ W (x + t • z) z with hh
  have hhc : Continuous h := by
    have : Continuous fun t : ℝ => x + t • z := by fun_prop
    exact (hc.comp this).clm_apply continuous_const
  have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun t : ℝ => W (x + t • z)) (h t) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => x + t • z) z t := by
      simpa using ((hasDerivAt_id t).smul_const z).const_add x
    exact (hd (x + t • z)).hasFDerivAt.comp_hasDerivAt t h1
  have hint := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hhc.intervalIntegrable _ _)
  simp only [one_smul, zero_smul, add_zero] at hint
  rw [← hint]
  have hn : ‖∫ t in (0 : ℝ)..1, h t‖ ≤ ∫ t in (0 : ℝ)..1, ‖h t‖ :=
    intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hj := sq_integral_le hhc.norm
  have hb : ∫ t in (0 : ℝ)..1, ‖h t‖ ^ 2 ≤
      ∫ t in (0 : ℝ)..1, ‖z‖ ^ 2 * ∑ i, ‖fderiv ℝ W (x + t • z) (unitVector i)‖ ^ 2 := by
    refine intervalIntegral.integral_mono_on zero_le_one ((hhc.norm.pow 2).intervalIntegrable _ _)
      ?_ fun t _ => norm_apply_sq_le _ _
    have : Continuous fun t : ℝ => x + t • z := by fun_prop
    exact (continuous_const.mul (continuous_finsetSum _ fun i _ =>
      (((hc.comp this).clm_apply continuous_const).norm.pow 2))).intervalIntegrable _ _
  rw [intervalIntegral.integral_const_mul] at hb
  calc ‖∫ t in (0 : ℝ)..1, h t‖ ^ 2 ≤ (∫ t in (0 : ℝ)..1, ‖h t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hn 2
    _ ≤ ∫ t in (0 : ℝ)..1, ‖h t‖ ^ 2 := hj
    _ ≤ _ := hb

theorem translation_bound (W : Space → Space) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W)
    (z : Space) :
    ∫⁻ x, ENNReal.ofReal (‖W (x + z) - W x‖ ^ 2) ≤
      ENNReal.ofReal (‖z‖ ^ 2 * ∫ x, ∑ i, ‖fderiv ℝ W x (unitVector i)‖ ^ 2) := by
  have hc : Continuous (fderiv ℝ W) := hW.continuous_fderiv (by simp)
  set g : Space → ℝ := fun y => ∑ i, ‖fderiv ℝ W y (unitVector i)‖ ^ 2 with hgd
  have hgc : Continuous g := continuous_finsetSum _ fun i _ => (hc.clm_apply continuous_const).norm.pow 2
  have hg0 : ∀ y, 0 ≤ g y := fun y => Finset.sum_nonneg fun i _ => sq_nonneg _
  have hgs : HasCompactSupport g :=
    (hWc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] Space => ∑ i, ‖L (unitVector i)‖ ^ 2)
      (by simp)
  have hgi : Integrable g := hgc.integrable_of_hasCompactSupport hgs
  have hcomp : ∀ x, Continuous fun t : ℝ => g (x + t • z) := fun x => hgc.comp (by fun_prop)
  have step1 : ∫⁻ x, ENNReal.ofReal (‖W (x + z) - W x‖ ^ 2) ≤
      ∫⁻ x, ENNReal.ofReal (‖z‖ ^ 2) * ∫⁻ t in Ioc (0 : ℝ) 1, ENNReal.ofReal (g (x + t • z)) := by
    refine lintegral_mono fun x => ?_
    refine (ENNReal.ofReal_le_ofReal (pointwise_translation W hW x z)).trans (le_of_eq ?_)
    rw [ENNReal.ofReal_mul (sq_nonneg _), intervalIntegral.integral_of_le zero_le_one,
      ofReal_integral_eq_lintegral_ofReal ((hcomp x).integrableOn_Icc.mono_set Ioc_subset_Icc_self)
        (Filter.Eventually.of_forall fun t => hg0 _)]
  refine step1.trans (le_of_eq ?_)
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hm : AEMeasurable (Function.uncurry fun (x : Space) (t : ℝ) => ENNReal.ofReal (g (x + t • z)))
      (volume.prod (volume.restrict (Ioc (0 : ℝ) 1))) := by
    refine (ENNReal.measurable_ofReal.comp (Continuous.measurable ?_)).aemeasurable
    exact hgc.comp (by fun_prop)
  rw [lintegral_lintegral_swap hm]
  have hin : ∀ t : ℝ, ∫⁻ x, ENNReal.ofReal (g (x + t • z)) = ∫⁻ x, ENNReal.ofReal (g x) :=
    fun t => lintegral_add_right_eq_self (fun y => ENNReal.ofReal (g y)) (t • z)
  simp only [hin]
  rw [setLIntegral_const, Real.volume_Ioc, sub_zero, ENNReal.ofReal_one, mul_one,
    ← ofReal_integral_eq_lintegral_ofReal hgi (Filter.Eventually.of_forall hg0),
    ← ENNReal.ofReal_mul (sq_nonneg _)]

theorem measurable_nearKernel : Measurable nearKernel := by
  unfold nearKernel
  exact Measurable.ite measurableSet_Iio (measurable_id.pow_const _) measurable_const

theorem measurable_nearFarKernel (α : ℝ) : Measurable (nearFarKernel α) := by
  unfold nearFarKernel
  exact Measurable.ite measurableSet_Iio (measurable_id.pow_const _) (measurable_id.pow_const _)

theorem integrable_nearFarKernel {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) :
    Integrable (fun z : Space => nearFarKernel α ‖z‖) := by
  have h1 := (FracInternal.integrableOn_ball_norm_rpow (s := -(2 + 4 * (α - 1)))
    (by linarith)).integrable_indicator Metric.isOpen_ball.measurableSet
  have h2 := (FracInternal.integrableOn_compl_ball_norm_rpow (s := -(1 + 2 * α))
    (by linarith)).integrable_indicator Metric.isOpen_ball.measurableSet.compl
  refine (h1.add h2).congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ < 1
  · have hm : z ∈ Metric.ball (0 : Space) 1 := by simpa using hz
    simp [nearFarKernel, hz, hm]
  · have hm : z ∉ Metric.ball (0 : Space) 1 := by simpa using hz
    simp [nearFarKernel, hz, hm]

theorem integrable_nearKernel_sq :
    Integrable (fun z : Space => nearKernel ‖z‖ * ‖z‖ ^ 2) := by
  have h1 := (FracInternal.integrableOn_ball_norm_rpow (s := -2)
    (by norm_num)).integrable_indicator Metric.isOpen_ball.measurableSet
  refine h1.congr (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : ‖z‖ < 1
  · have hm : z ∈ Metric.ball (0 : Space) 1 := by simpa using hz
    simp only [Set.indicator_of_mem hm, nearKernel, hz, if_true]
    rcases eq_or_lt_of_le (norm_nonneg z) with h0 | hpos
    · rw [← h0, Real.zero_rpow (by norm_num), Real.zero_rpow (by norm_num)]
      ring
    · rw [← Real.rpow_natCast, ← Real.rpow_add hpos]
      norm_num
  · have hm : z ∉ Metric.ball (0 : Space) 1 := by simpa using hz
    simp [nearKernel, hz, hm]

theorem far_term_left {α : ℝ} (w : Space → Space) (hw : Continuous w) {a : ℝ}
    (hwa : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2))
    (hK : Integrable (fun z : Space => nearFarKernel α ‖z‖)) :
    ∫⁻ p : Space × Space, ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2)
        ∂(volume.prod volume) ≤ ENNReal.ofReal ((∫ z : Space, nearFarKernel α ‖z‖) * a ^ 2) := by
  have hm : AEMeasurable (fun p : Space × Space =>
      ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2)) (volume.prod volume) := by
    refine (ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)).aemeasurable
    · exact (measurable_nearFarKernel α).comp (by fun_prop : Continuous fun p : Space × Space => ‖p.1 - p.2‖).measurable
    · exact ((hw.comp continuous_fst).norm.pow 2).measurable
  have hK0 : ∀ z : Space, 0 ≤ nearFarKernel α ‖z‖ := fun z => nearFarKernel_nonneg α _ (norm_nonneg z)
  have hKl : ∫⁻ z : Space, ENNReal.ofReal (nearFarKernel α ‖z‖) =
      ENNReal.ofReal (∫ z : Space, nearFarKernel α ‖z‖) :=
    (ofReal_integral_eq_lintegral_ofReal hK (Filter.Eventually.of_forall hK0)).symm
  rw [lintegral_prod _ hm]
  have hin : ∀ x : Space, ∫⁻ y : Space, ENNReal.ofReal (nearFarKernel α ‖(x, y).1 - (x, y).2‖ *
      ‖w (x, y).1‖ ^ 2) = ENNReal.ofReal (‖w x‖ ^ 2) * ENNReal.ofReal (∫ z : Space, nearFarKernel α ‖z‖) := by
    intro x
    dsimp only
    have e : ∀ y : Space, ENNReal.ofReal (nearFarKernel α ‖x - y‖ * ‖w x‖ ^ 2) =
        ENNReal.ofReal (‖w x‖ ^ 2) * ENNReal.ofReal (nearFarKernel α ‖y - x‖) := by
      intro y
      rw [norm_sub_rev, mul_comm, ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_right_eq_self (fun y : Space => ENNReal.ofReal (nearFarKernel α ‖y‖)) x, hKl]
  simp only [hin]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm,
    ENNReal.ofReal_mul (integral_nonneg hK0)]
  gcongr

theorem far_term_right {α : ℝ} (w : Space → Space) (hw : Continuous w) {a : ℝ}
    (hwa : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2))
    (hK : Integrable (fun z : Space => nearFarKernel α ‖z‖)) :
    ∫⁻ p : Space × Space, ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.2‖ ^ 2)
        ∂(volume.prod volume) ≤ ENNReal.ofReal ((∫ z : Space, nearFarKernel α ‖z‖) * a ^ 2) := by
  have hm : AEMeasurable (fun p : Space × Space =>
      ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.2‖ ^ 2)) (volume.prod volume) := by
    refine (ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)).aemeasurable
    · exact (measurable_nearFarKernel α).comp (by fun_prop : Continuous fun p : Space × Space => ‖p.1 - p.2‖).measurable
    · exact ((hw.comp continuous_snd).norm.pow 2).measurable
  have hK0 : ∀ z : Space, 0 ≤ nearFarKernel α ‖z‖ := fun z => nearFarKernel_nonneg α _ (norm_nonneg z)
  have hKl : ∫⁻ z : Space, ENNReal.ofReal (nearFarKernel α ‖z‖) =
      ENNReal.ofReal (∫ z : Space, nearFarKernel α ‖z‖) :=
    (ofReal_integral_eq_lintegral_ofReal hK (Filter.Eventually.of_forall hK0)).symm
  rw [lintegral_prod_symm _ hm]
  have hin : ∀ y : Space, ∫⁻ x : Space, ENNReal.ofReal (nearFarKernel α ‖(x, y).1 - (x, y).2‖ *
      ‖w (x, y).2‖ ^ 2) = ENNReal.ofReal (‖w y‖ ^ 2) * ENNReal.ofReal (∫ z : Space, nearFarKernel α ‖z‖) := by
    intro y
    dsimp only
    have e : ∀ x : Space, ENNReal.ofReal (nearFarKernel α ‖x - y‖ * ‖w y‖ ^ 2) =
        ENNReal.ofReal (‖w y‖ ^ 2) * ENNReal.ofReal (nearFarKernel α ‖x - y‖) := by
      intro x
      rw [mul_comm, ENNReal.ofReal_mul (sq_nonneg _)]
    simp only [e]
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_sub_right_eq_self (fun x : Space => ENNReal.ofReal (nearFarKernel α ‖x‖)) y, hKl]
  simp only [hin]
  rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top, mul_comm,
    ENNReal.ofReal_mul (integral_nonneg hK0)]
  gcongr

theorem near_term (W : Space → Space) (hW : ContDiff ℝ ∞ W) (hWc : HasCompactSupport W) :
    ∫⁻ p : Space × Space, ENNReal.ofReal (nearKernel ‖p.1 - p.2‖ * ‖W p.1 - W p.2‖ ^ 2)
        ∂(volume.prod volume) ≤
      ENNReal.ofReal ((∫ z : Space, nearKernel ‖z‖ * ‖z‖ ^ 2) *
        ∫ x, ∑ i, ‖fderiv ℝ W x (unitVector i)‖ ^ 2) := by
  have hWcont : Continuous W := hW.continuous
  have hm : AEMeasurable (fun p : Space × Space =>
      ENNReal.ofReal (nearKernel ‖p.1 - p.2‖ * ‖W p.1 - W p.2‖ ^ 2)) (volume.prod volume) := by
    refine (ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)).aemeasurable
    · exact measurable_nearKernel.comp (by fun_prop : Continuous fun p : Space × Space => ‖p.1 - p.2‖).measurable
    · exact (((hWcont.comp continuous_fst).sub (hWcont.comp continuous_snd)).norm.pow 2).measurable
  set G := ∫ x, ∑ i, ‖fderiv ℝ W x (unitVector i)‖ ^ 2 with hGd
  have hG0 : 0 ≤ G := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  rw [lintegral_prod _ hm]
  have hin : ∀ x : Space, ∫⁻ y : Space, ENNReal.ofReal (nearKernel ‖(x, y).1 - (x, y).2‖ *
      ‖W (x, y).1 - W (x, y).2‖ ^ 2) = ∫⁻ z : Space, ENNReal.ofReal (nearKernel ‖z‖ *
        ‖W (x + z) - W x‖ ^ 2) := by
    intro x
    dsimp only
    rw [← lintegral_add_left_eq_self (fun y : Space => ENNReal.ofReal (nearKernel ‖x - y‖ *
      ‖W x - W y‖ ^ 2)) x]
    refine lintegral_congr fun z => ?_
    try dsimp only
    rw [show x - (x + z) = -z by abel, norm_neg, norm_sub_rev]
  simp only [hin]
  have hm2 : AEMeasurable (Function.uncurry fun (x z : Space) =>
      ENNReal.ofReal (nearKernel ‖z‖ * ‖W (x + z) - W x‖ ^ 2)) (volume.prod volume) := by
    refine (ENNReal.measurable_ofReal.comp (Measurable.mul ?_ ?_)).aemeasurable
    · exact measurable_nearKernel.comp continuous_snd.norm.measurable
    · exact (((hWcont.comp (continuous_fst.add continuous_snd)).sub
        (hWcont.comp continuous_fst)).norm.pow 2).measurable
  rw [lintegral_lintegral_swap hm2]
  have hK0 : ∀ z : Space, 0 ≤ nearKernel ‖z‖ := fun z => nearKernel_nonneg _ (norm_nonneg z)
  calc ∫⁻ z : Space, ∫⁻ x : Space, ENNReal.ofReal (nearKernel ‖z‖ * ‖W (x + z) - W x‖ ^ 2)
      = ∫⁻ z : Space, ENNReal.ofReal (nearKernel ‖z‖) *
          ∫⁻ x : Space, ENNReal.ofReal (‖W (x + z) - W x‖ ^ 2) := by
        refine lintegral_congr fun z => ?_
        simp only [ENNReal.ofReal_mul (hK0 z)]
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ z : Space, ENNReal.ofReal (nearKernel ‖z‖) * ENNReal.ofReal (‖z‖ ^ 2 * G) :=
        lintegral_mono fun z => by gcongr; exact translation_bound W hW hWc z
    _ = ∫⁻ z : Space, ENNReal.ofReal (nearKernel ‖z‖ * ‖z‖ ^ 2) * ENNReal.ofReal G := by
        refine lintegral_congr fun z => ?_
        rw [← ENNReal.ofReal_mul (hK0 z), ← ENNReal.ofReal_mul (mul_nonneg (hK0 z) (sq_nonneg _)), mul_assoc]
    _ = ENNReal.ofReal ((∫ z : Space, nearKernel ‖z‖ * ‖z‖ ^ 2) * G) := by
        rw [lintegral_mul_const' _ _ ENNReal.ofReal_ne_top,
          ← ofReal_integral_eq_lintegral_ofReal integrable_nearKernel_sq
            (Filter.Eventually.of_forall fun z => mul_nonneg (hK0 z) (sq_nonneg _)),
          ← ENNReal.ofReal_mul (integral_nonneg fun z => mul_nonneg (hK0 z) (sq_nonneg _))]

theorem pair_term_bound {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) :
    ∃ c : ℝ, 0 ≤ c ∧ ∀ r : ℝ, 1 ≤ r → ∀ w : Space → Space, ContDiff ℝ ∞ w →
      ∀ a : ℝ, 0 ≤ a → ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2) →
      ∫ z : Space × Space, (radialCutoff r z.1 ^ 2 - radialCutoff r z.2 ^ 2) ^ 2 *
          ‖w z.1 - w z.2‖ ^ 2 * ‖z.1 - z.2‖ ^ (-(3 + 2 * α)) ∂(volume.prod volume) ≤
        c / r ^ 2 * (a ^ 2 + ∫ x, ∑ i, ‖fderiv ℝ (fun y => radialCutoff r y ^ 2 • w y) x
          (unitVector i)‖ ^ 2) := by
  obtain ⟨c₀, hc₀⟩ := abs_radialCutoff_sub_le
  set c := max c₀ 0 with hcd
  have hc0 : 0 ≤ c := le_max_right _ _
  have hc : ∀ r, 0 < r → ∀ x y, |radialCutoff r x - radialCutoff r y| ≤ c * ‖x - y‖ / r := by
    intro r hr x y
    refine (hc₀ r hr x y).trans ?_
    apply div_le_div_of_nonneg_right _ hr.le
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  have hKn := integrable_nearFarKernel hα1 hα2
  set Kn := ∫ z : Space, nearFarKernel α ‖z‖ with hKnd
  set Kg := ∫ z : Space, nearKernel ‖z‖ * ‖z‖ ^ 2 with hKgd
  have hKn0 : 0 ≤ Kn := integral_nonneg fun z => nearFarKernel_nonneg α _ (norm_nonneg z)
  have hKg0 : 0 ≤ Kg :=
    integral_nonneg fun z => mul_nonneg (nearKernel_nonneg _ (norm_nonneg z)) (sq_nonneg _)
  set K := 8 * c ^ 2 + 8 * c ^ 4 with hKd
  have hK0 : 0 ≤ K := by positivity
  refine ⟨K * (2 * Kn + Kg), by positivity, fun r hr w hw a ha hwa => ?_⟩
  have hr0 : 0 < r := by linarith
  have hwc : Continuous w := hw.continuous
  set W : Space → Space := fun y => radialCutoff r y ^ 2 • w y with hWd
  have hW : ContDiff ℝ ∞ W := ((contDiff_radialCutoff hr0).pow 2).smul hw
  have hWcont : Continuous W := hW.continuous
  have hWc : HasCompactSupport W :=
    ((hasCompactSupport_radialCutoff hr0).comp_left (g := fun t : ℝ => t ^ 2)
      (by norm_num)).smul_right
  set G := ∫ x, ∑ i, ‖fderiv ℝ W x (unitVector i)‖ ^ 2 with hGd
  have hG0 : 0 ≤ G := integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  set F : Space × Space → ℝ := fun z => (radialCutoff r z.1 ^ 2 - radialCutoff r z.2 ^ 2) ^ 2 *
    ‖w z.1 - w z.2‖ ^ 2 * ‖z.1 - z.2‖ ^ (-(3 + 2 * α)) with hFd
  have hRHS : 0 ≤ K * (2 * Kn + Kg) / r ^ 2 * (a ^ 2 + G) := by positivity
  by_cases hFi : Integrable F (volume.prod volume)
  swap
  · rw [integral_undef hFi]; exact hRHS
  have hF0 : ∀ p, 0 ≤ F p := fun p => by
    simp only [hFd]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg _) _)
  have hpt : ∀ p : Space × Space, ENNReal.ofReal (F p) ≤ ENNReal.ofReal (K / r ^ 2) *
      (ENNReal.ofReal (nearKernel ‖p.1 - p.2‖ * ‖W p.1 - W p.2‖ ^ 2) +
        ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2) +
        ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.2‖ ^ 2)) := by
    intro p
    have h := pointwise_bound hα1 hα2 hc0 hc hr w p.1 p.2
    have n1 : 0 ≤ nearKernel ‖p.1 - p.2‖ * ‖W p.1 - W p.2‖ ^ 2 :=
      mul_nonneg (nearKernel_nonneg _ (norm_nonneg _)) (sq_nonneg _)
    have n2 : 0 ≤ nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2 :=
      mul_nonneg (nearFarKernel_nonneg _ _ (norm_nonneg _)) (sq_nonneg _)
    have n3 : 0 ≤ nearFarKernel α ‖p.1 - p.2‖ * ‖w p.2‖ ^ 2 :=
      mul_nonneg (nearFarKernel_nonneg _ _ (norm_nonneg _)) (sq_nonneg _)
    rw [← ENNReal.ofReal_add n1 n2, ← ENNReal.ofReal_add (add_nonneg n1 n2) n3,
      ← ENNReal.ofReal_mul (by positivity)]
    refine ENNReal.ofReal_le_ofReal (h.trans (le_of_eq ?_))
    simp only [hWd, hKd]
    ring
  have hA : Measurable fun p : Space × Space =>
      ENNReal.ofReal (nearKernel ‖p.1 - p.2‖ * ‖W p.1 - W p.2‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp ((measurable_nearKernel.comp
      (by fun_prop : Continuous fun p : Space × Space => ‖p.1 - p.2‖).measurable).mul
      (by fun_prop : Continuous fun p : Space × Space => ‖W p.1 - W p.2‖ ^ 2).measurable)
  have hB : Measurable fun p : Space × Space =>
      ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2) :=
    ENNReal.measurable_ofReal.comp (((measurable_nearFarKernel α).comp
      (by fun_prop : Continuous fun p : Space × Space => ‖p.1 - p.2‖).measurable).mul
      (by fun_prop : Continuous fun p : Space × Space => ‖w p.1‖ ^ 2).measurable)
  have hlin : ∫⁻ p, ENNReal.ofReal (F p) ∂(volume.prod volume) ≤
      ENNReal.ofReal (K / r ^ 2 * (Kg * G + Kn * a ^ 2 + Kn * a ^ 2)) := by
    refine (lintegral_mono hpt).trans ?_
    have hAB : Measurable fun p : Space × Space =>
        ENNReal.ofReal (nearKernel ‖p.1 - p.2‖ * ‖W p.1 - W p.2‖ ^ 2) +
          ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2) := hA.add hB
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left hAB,
      lintegral_add_left hA]
    have t1 := near_term W hW hWc
    have t2 := far_term_left (α := α) w hwc hwa hKn
    have t3 := far_term_right (α := α) w hwc hwa hKn
    calc ENNReal.ofReal (K / r ^ 2) * (∫⁻ p, ENNReal.ofReal (nearKernel ‖p.1 - p.2‖ *
            ‖W p.1 - W p.2‖ ^ 2) ∂(volume.prod volume) +
          ∫⁻ p, ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.1‖ ^ 2) ∂(volume.prod volume) +
          ∫⁻ p, ENNReal.ofReal (nearFarKernel α ‖p.1 - p.2‖ * ‖w p.2‖ ^ 2) ∂(volume.prod volume))
        ≤ ENNReal.ofReal (K / r ^ 2) * (ENNReal.ofReal (Kg * G) + ENNReal.ofReal (Kn * a ^ 2) +
            ENNReal.ofReal (Kn * a ^ 2)) := by
          gcongr
      _ = ENNReal.ofReal (K / r ^ 2 * (Kg * G + Kn * a ^ 2 + Kn * a ^ 2)) := by
          rw [← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_add (by positivity) (by positivity),
            ← ENNReal.ofReal_mul (by positivity)]
  rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hF0) hFi.aestronglyMeasurable]
  refine ENNReal.toReal_le_of_le_ofReal hRHS (hlin.trans (ENNReal.ofReal_le_ofReal ?_))
  have e : K * (2 * Kn + Kg) / r ^ 2 * (a ^ 2 + G) = K / r ^ 2 * ((2 * Kn + Kg) * (a ^ 2 + G)) := by
    ring
  rw [e]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  nlinarith [mul_nonneg hKn0 hG0, mul_nonneg hKg0 (sq_nonneg a)]

theorem integrable_sq_of_lintegral {w : Space → Space} (hw : Continuous w) {a : ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal (a ^ 2)) :
    Integrable (fun x => ‖w x‖ ^ 2) ∧ ∫ x, ‖w x‖ ^ 2 ≤ a ^ 2 := by
  have hfin : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≠ ⊤ := (h.trans_lt ENNReal.ofReal_lt_top).ne
  have hm : AEMeasurable (fun x => ENNReal.ofReal (‖w x‖ ^ 2)) :=
    (ENNReal.measurable_ofReal.comp (hw.norm.pow 2).measurable).aemeasurable
  have hi := integrable_toReal_of_lintegral_ne_top hm hfin
  have heq : (fun x => (ENNReal.ofReal (‖w x‖ ^ 2)).toReal) = fun x => ‖w x‖ ^ 2 := by
    funext x; exact ENNReal.toReal_ofReal (by positivity)
  rw [heq] at hi
  refine ⟨hi, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖w x‖ ^ 2)
    (Filter.Eventually.of_forall fun x => by positivity)
    (by fun_prop : Continuous fun x => ‖w x‖ ^ 2).aestronglyMeasurable]
  exact ENNReal.toReal_le_of_le_ofReal (by positivity) h

end Breakdown.SpaceLowerBound.Internal

namespace Breakdown

open SpaceLowerBound.Internal

theorem fracCutoffLowerBound_of (h1 : FracLocalizationStatement) (h2 : FracGradientBoundStatement)
    (h3 : FracCompactDecayStatement) (h4 : CovarianceStatement) : FracCutoffLowerBoundStatement := by
  intro α hα1 hα2
  obtain ⟨c₃, hc₃, hS⟩ := scalar_term_bound h3 h4 hα1 (by linarith)
  obtain ⟨c₄, hc₄, hJ⟩ := pair_term_bound hα1 hα2
  have hM : 0 < fractionalNormalizer α := (normalizer α hα1 (by linarith)).2
  set M := fractionalNormalizer α with hMdef
  have hMi : 0 ≤ M⁻¹ := inv_nonneg.2 hM.le
  refine ⟨max 1 (Real.sqrt (M⁻¹ * c₄)), c₃ / 2 + M⁻¹ * c₄ / 2, le_max_left _ _, ?_⟩
  intro w hw a ha hwa r hr
  have hr1 : 1 ≤ r := (le_max_left _ _).trans hr
  have hr0 : 0 < r := by linarith
  have hsq : M⁻¹ * c₄ ≤ r ^ 2 := by
    have h0 : 0 ≤ M⁻¹ * c₄ := mul_nonneg hMi hc₄
    have hs : Real.sqrt (M⁻¹ * c₄) ≤ r := (le_max_right _ _).trans hr
    calc M⁻¹ * c₄ = Real.sqrt (M⁻¹ * c₄) ^ 2 := (Real.sq_sqrt h0).symm
      _ ≤ r ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
  obtain ⟨hwi, hwa'⟩ := integrable_sq_of_lintegral hw.continuous hwa
  have hmem : MemLp w 2 volume :=
    (memLp_two_iff_integrable_sq_norm hw.continuous.aestronglyMeasurable).2 hwi
  set φ : Space → ℝ := fun y => radialCutoff r y ^ 2 with hφdef
  have hφ : ContDiff ℝ ∞ φ := (contDiff_radialCutoff hr0).pow 2
  have hφc : HasCompactSupport φ :=
    (hasCompactSupport_radialCutoff hr0).comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  obtain ⟨_, hloc⟩ := h1 α hα1 (by linarith) w hw hmem φ hφ hφc
  have hfun : (fun y => cutoffPow r y • w y) = fun y => φ y ^ 2 • w y := by
    funext y; simp only [cutoffPow, hφdef, ← pow_mul]
  rw [hfun, hloc]
  set W : Space → Space := fun y => φ y • w y with hWdef
  have hW : ContDiff ℝ ∞ W := hφ.smul hw
  have hWc : HasCompactSupport W := hφc.smul_right
  obtain ⟨hD0, hG⟩ := h2 α hα1 (by linarith) W hW hWc
  have hWa : ∫ x, ‖W x‖ ^ 2 ≤ a ^ 2 := by
    refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => by positivity) hwi
      (Filter.Eventually.of_forall fun x => ?_)) hwa'
    have h0 : 0 ≤ φ x := by positivity
    have h1' : φ x ≤ 1 := by
      simp only [hφdef]
      exact pow_le_one₀ (radialCutoff_nonneg r x) (radialCutoff_le_one r x)
    simp only [hWdef, norm_smul, Real.norm_of_nonneg h0, mul_pow]
    exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ h0 h1')
  have hD : cutoffFracDissipation α r w = ∫ x, inner ℝ (W x) (fractionalPowerAt α W x) := rfl
  set D := ∫ x, inner ℝ (W x) (fractionalPowerAt α W x) with hDdef
  set G := ∫ x, ∑ i, ‖fderiv ℝ W x (unitVector i)‖ ^ 2 with hGdef
  set J := ∫ z : Space × Space, (φ z.1 - φ z.2) ^ 2 * ‖w z.1 - w z.2‖ ^ 2 *
      ‖z.1 - z.2‖ ^ (-(3 + 2 * α)) ∂(volume.prod volume) with hJdef
  set T := ∫ x, (scalarPowerAt α (fun y => φ y ^ 2) x - 2 * φ x * scalarPowerAt α φ x) * ‖w x‖ ^ 2
    with hTdef
  have hJ' : J ≤ c₄ / r ^ 2 * (a ^ 2 + G) := hJ r hr1 w hw a ha hwa
  have hT : -(c₃ / r ^ 2 * a ^ 2) ≤ T := by
    have habs : |T| ≤ c₃ / r ^ 2 * a ^ 2 := by
      refine (abs_integral_le_integral_abs).trans ?_
      refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => abs_nonneg _)
        (hwi.const_mul (c₃ / r ^ 2)) (Filter.Eventually.of_forall fun x => ?_)) ?_
      · dsimp only
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖w x‖ ^ 2)]
        exact mul_le_mul_of_nonneg_right (hS r hr1 x) (by positivity)
      · rw [integral_const_mul]
        exact mul_le_mul_of_nonneg_left hwa' (by positivity)
    exact neg_le_of_abs_le habs
  have hk0 : 0 ≤ M⁻¹ * c₄ / r ^ 2 := by positivity
  have hk1 : M⁻¹ * c₄ / r ^ 2 ≤ 1 := (div_le_one (by positivity)).2 hsq
  have hJk : M⁻¹ / 4 * J ≤ M⁻¹ * c₄ / r ^ 2 / 4 * (2 * a ^ 2 + D) := by
    calc M⁻¹ / 4 * J ≤ M⁻¹ / 4 * (c₄ / r ^ 2 * (a ^ 2 + G)) :=
          mul_le_mul_of_nonneg_left hJ' (by positivity)
      _ = M⁻¹ * c₄ / r ^ 2 / 4 * (a ^ 2 + G) := by ring
      _ ≤ M⁻¹ * c₄ / r ^ 2 / 4 * (2 * a ^ 2 + D) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hkD : M⁻¹ * c₄ / r ^ 2 / 4 * D ≤ D / 4 := by
    have := mul_le_mul_of_nonneg_right hk1 hD0
    linarith
  have hC : (c₃ / 2 + M⁻¹ * c₄ / 2) * a ^ 2 / r ^ 2 =
      c₃ / r ^ 2 * a ^ 2 / 2 + M⁻¹ * c₄ / r ^ 2 / 4 * (2 * a ^ 2) := by ring
  rw [hD, hC]
  nlinarith

end Breakdown
