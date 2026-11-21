import Breakdown.FracCert.StDecay
import Breakdown.Frac.PAxial
import Breakdown.Frac.TorusSelfSimilar

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq Breakdown.SmoothFlow

def HeatDivRegularStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ (β : ℝ) (j : ℕ), 0 ≤ β → β < 3 →
    ∃ C : ℝ, ∀ (F : Space → Fin 3 → Fin 3 → ℝ) (A B : ℝ), ContDiff ℝ j F →
      (∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ A) → (∀ y, (1 + ‖y‖) ^ β * ‖F y‖ ≤ B) →
      (∀ t : ℝ, 0 < t → ContDiff ℝ j (heatDivConv α t F)) ∧
      (∀ k ≤ j, ContinuousOn (fun p : ℝ × Space => iteratedFDeriv ℝ k (heatDivConv α p.1 F) p.2)
        (Ioi 0 ×ˢ univ)) ∧
      ∀ k ≤ j, ∀ t : ℝ, 0 < t → t ≤ 1 → ∀ x,
        ‖iteratedFDeriv ℝ k (heatDivConv α t F) x‖ ≤ C * t ^ (-(1 / (2 * α))) * (A + B)

namespace DecayFarField.Internal

def integrand (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (τ : ℝ) : Space → Space :=
  pushForward (axialRotation (a * τ)) (scaleField α (Real.exp (-τ)) (heatDivConv α (1 - Real.exp (-τ)) F))

theorem integral_contDiff {Φ : ℝ → Space → Space} {w : ℝ → ℝ} (j : ℕ)
    (hΦ : ∀ τ, 0 < τ → ContDiff ℝ j (Φ τ))
    (hm : ∀ k ≤ j, ∀ y, AEStronglyMeasurable (fun τ => iteratedFDeriv ℝ k (Φ τ) y)
      (volume.restrict (Ioi 0)))
    (hb : ∀ k ≤ j, ∀ τ, 0 < τ → ∀ y, ‖iteratedFDeriv ℝ k (Φ τ) y‖ ≤ w τ)
    (hw : IntegrableOn w (Ioi 0)) :
    ContDiff ℝ j (fun y => ∫ τ in Ioi (0 : ℝ), Φ τ y) ∧
      ∀ y, iteratedFDeriv ℝ j (fun y => ∫ τ in Ioi (0 : ℝ), Φ τ y) y =
        ∫ τ in Ioi (0 : ℝ), iteratedFDeriv ℝ j (Φ τ) y := by
  set G := fun y => ∫ τ in Ioi (0 : ℝ), Φ τ y with hG
  have hbae : ∀ k ≤ j, ∀ᵐ τ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ y, ‖iteratedFDeriv ℝ k (Φ τ) y‖ ≤ w τ :=
    fun k hk => (ae_restrict_iff' measurableSet_Ioi).2
      (Filter.Eventually.of_forall fun τ hτ y => hb k hk τ hτ y)
  have hint : ∀ k ≤ j, ∀ y, Integrable (fun τ => iteratedFDeriv ℝ k (Φ τ) y) (volume.restrict (Ioi 0)) :=
    fun k hk y => Integrable.mono' hw (hm k hk y) ((hbae k hk).mono fun τ h => h y)
  have hdiff : ∀ k < j, ∀ y, HasFDerivAt (fun y => ∫ τ in Ioi (0 : ℝ), iteratedFDeriv ℝ k (Φ τ) y)
      (∫ τ in Ioi (0 : ℝ), fderiv ℝ (iteratedFDeriv ℝ k (Φ τ)) y) y := by
    intro k hk y
    have hk1 : k + 1 ≤ j := hk
    refine hasFDerivAt_integral_of_dominated_of_fderiv_le (𝕜 := ℝ) (s := univ)
      (F' := fun x τ => fderiv ℝ (iteratedFDeriv ℝ k (Φ τ)) x) (bound := w) Filter.univ_mem
      (Filter.Eventually.of_forall fun y => hm k hk.le y) (hint k hk.le y) ?_ ?_ hw ?_
    · have : (fun τ => fderiv ℝ (iteratedFDeriv ℝ k (Φ τ)) y) = fun τ =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) Space
            (iteratedFDeriv ℝ (k + 1) (Φ τ) y) := by
        funext τ; rw [fderiv_iteratedFDeriv]; rfl
      rw [this]
      exact (LinearIsometryEquiv.continuous _).comp_aestronglyMeasurable (hm (k + 1) hk1 y)
    · refine (hbae (k + 1) hk1).mono fun τ h x _ => ?_
      rw [fderiv_iteratedFDeriv, Function.comp_apply, LinearIsometryEquiv.norm_map]
      exact h x
    · refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ x _ => ?_)
      exact ((hΦ τ hτ).differentiable_iteratedFDeriv (by exact_mod_cast hk) x).hasFDerivAt
  have heq : ∀ k ≤ j, iteratedFDeriv ℝ k G = fun y => ∫ τ in Ioi (0 : ℝ), iteratedFDeriv ℝ k (Φ τ) y := by
    intro k
    induction k with
    | zero =>
      intro _
      funext y
      rw [iteratedFDeriv_zero_eq_comp]
      simp only [Function.comp_apply, iteratedFDeriv_zero_eq_comp]
      have hc := LinearIsometry.integral_comp_comm (μ := volume.restrict (Ioi (0 : ℝ)))
        (continuousMultilinearCurryFin0 ℝ Space Space).symm.toLinearIsometry (fun τ => Φ τ y)
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hc
      exact hc.symm
    | succ k ih =>
      intro hk
      have hk' : k < j := hk
      funext y
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih hk'.le, (hdiff k hk' y).fderiv]
      have : (fun τ => fderiv ℝ (iteratedFDeriv ℝ k (Φ τ)) y) = fun τ =>
          continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) Space
            (iteratedFDeriv ℝ (k + 1) (Φ τ) y) := by
        funext τ; rw [fderiv_iteratedFDeriv]; rfl
      have hc := LinearIsometry.integral_comp_comm (μ := volume.restrict (Ioi (0 : ℝ)))
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => Space) Space).toLinearIsometry
        (fun τ => iteratedFDeriv ℝ (k + 1) (Φ τ) y)
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at hc
      rw [this, hc, LinearIsometryEquiv.symm_apply_apply]
  have hcont : ∀ k ≤ j, Continuous (fun y => ∫ τ in Ioi (0 : ℝ), iteratedFDeriv ℝ k (Φ τ) y) := by
    intro k hk
    refine continuous_of_dominated (fun y => hm k hk y) (fun y => (hbae k hk).mono fun τ h => h y) hw ?_
    exact (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ =>
      (hΦ τ hτ).continuous_iteratedFDeriv (by exact_mod_cast hk))
  refine ⟨?_, fun y => by rw [heq j le_rfl]⟩
  refine contDiff_iff_continuous_differentiable.2 ⟨fun m hm' => ?_, fun m hm' => ?_⟩
  · have hmj : m ≤ j := by exact_mod_cast hm'
    rw [heq m hmj]; exact hcont m hmj
  · have hmj : m < j := by exact_mod_cast hm'
    rw [heq m hmj.le]; exact fun y => (hdiff m hmj y).differentiableAt

theorem integrand_contDiff (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (j : ℕ) (τ : ℝ)
    (h : ContDiff ℝ j (heatDivConv α (1 - Real.exp (-τ)) F)) :
    ContDiff ℝ j (integrand α a F τ) := by
  unfold integrand pushForward scaleField
  exact (axialRotation (a * τ)).contDiff.comp
    ((h.comp ((axialRotation (a * τ)).symm.contDiff.const_smul (Real.exp (-τ) ^ (1 / (2 * α))))).const_smul
      (Real.exp (-τ) ^ (1 - 1 / (2 * α))))

theorem integrand_norm_le (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (k : ℕ) (τ : ℝ)
    (h : ContDiff ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)) (y : Space) :
    ‖iteratedFDeriv ℝ k (integrand α a F τ) y‖ ≤
      Real.exp (-τ) ^ (1 - 1 / (2 * α)) * (Real.exp (-τ) ^ (1 / (2 * α))) ^ k *
        ‖iteratedFDeriv ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)
          (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)‖ := by
  set R := axialRotation (a * τ)
  set c := Real.exp (-τ) ^ (1 / (2 * α))
  set d := Real.exp (-τ) ^ (1 - 1 / (2 * α))
  set hh := heatDivConv α (1 - Real.exp (-τ)) F
  have hc : 0 ≤ c := Real.rpow_nonneg (Real.exp_pos _).le _
  have hd : 0 ≤ d := Real.rpow_nonneg (Real.exp_pos _).le _
  set L : Space →L[ℝ] Space := c • ContinuousLinearMap.id ℝ Space
  have hfun : integrand α a F τ = R ∘ ((fun z => d • (hh ∘ L) z) ∘ R.symm) := by
    funext z; simp [integrand, pushForward, scaleField, L, R, c, d, hh]
  have hL : ContDiff ℝ k (hh ∘ L) := h.comp L.contDiff
  rw [hfun, LinearIsometryEquiv.norm_iteratedFDeriv_comp_left,
    LinearIsometryEquiv.norm_iteratedFDeriv_comp_right]
  have h1 : iteratedFDeriv ℝ k (fun z => d • (hh ∘ L) z) (R.symm y) =
      d • iteratedFDeriv ℝ k (hh ∘ L) (R.symm y) := by
    have he : (fun z => d • (hh ∘ L) z) = d • (hh ∘ L) := rfl
    rw [he]
    exact iteratedFDeriv_const_smul_apply (hL.contDiffAt)
  rw [h1, norm_smul, Real.norm_eq_abs, abs_of_nonneg hd,
    ContinuousLinearMap.iteratedFDeriv_comp_right L h (R.symm y) le_rfl]
  have hLn : ‖L‖ ≤ c := by
    refine le_trans (norm_smul_le _ _) ?_
    rw [Real.norm_eq_abs, abs_of_nonneg hc]
    exact mul_le_of_le_one_right hc ContinuousLinearMap.norm_id_le
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ k hh (L (R.symm y))) (fun _ : Fin k => L)
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h2
  have h3 : ‖L‖ ^ k ≤ c ^ k := pow_le_pow_left₀ (norm_nonneg _) hLn k
  have hLy : L (R.symm y) = c • R.symm y := rfl
  rw [hLy] at h2
  calc d * ‖(iteratedFDeriv ℝ k hh (c • R.symm y)).compContinuousLinearMap fun _ => L‖
      ≤ d * (‖iteratedFDeriv ℝ k hh (c • R.symm y)‖ * ‖L‖ ^ k) := by gcongr
    _ ≤ d * (‖iteratedFDeriv ℝ k hh (c • R.symm y)‖ * c ^ k) := by gcongr
    _ = _ := by ring

theorem t_pos {τ : ℝ} (hτ : 0 < τ) : 0 < 1 - Real.exp (-τ) := by
  have : Real.exp (-τ) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  linarith

theorem integrableOn_of_abs_le {f G : ℝ → ℝ} {S : Set ℝ} (hS : MeasurableSet S) (hf : ContinuousOn f S)
    (hG : IntegrableOn G S) (h : ∀ τ ∈ S, |f τ| ≤ G τ) : IntegrableOn f S :=
  Integrable.mono' hG (hf.aestronglyMeasurable hS)
    ((ae_restrict_iff' hS).2 (Filter.Eventually.of_forall fun τ hτ => by
      rw [Real.norm_eq_abs]; exact h τ hτ))

theorem tpow_continuousOn (g : ℝ) : ContinuousOn (fun τ : ℝ => (1 - Real.exp (-τ)) ^ (-g)) (Ioi 0) := by
  refine ContinuousOn.rpow_const (by fun_prop) fun τ hτ => Or.inl (t_pos hτ).ne'

theorem tpow_le_near (g : ℝ) (hg0 : 0 ≤ g) {τ : ℝ} (hτ : 0 < τ) (hτ1 : τ ≤ 1) :
    (1 - Real.exp (-τ)) ^ (-g) ≤ Real.exp g * τ ^ (-g) := by
  have h1 : τ * Real.exp (-τ) ≤ 1 - Real.exp (-τ) := by
    have h2 := Real.add_one_le_exp τ
    have h3 : Real.exp τ * Real.exp (-τ) = 1 := by rw [← Real.exp_add]; simp
    nlinarith [Real.exp_pos (-τ)]
  have hpos : 0 < τ * Real.exp (-τ) := mul_pos hτ (Real.exp_pos _)
  refine le_trans (Real.rpow_le_rpow_of_nonpos hpos h1 (by linarith)) ?_
  rw [Real.mul_rpow hτ.le (Real.exp_pos _).le, ← Real.exp_mul, mul_comm]
  gcongr
  nlinarith

theorem tpow_le_far (g : ℝ) (hg0 : 0 ≤ g) {τ : ℝ} (hτ1 : 1 ≤ τ) :
    (1 - Real.exp (-τ)) ^ (-g) ≤ (1 - Real.exp (-1)) ^ (-g) := by
  refine Real.rpow_le_rpow_of_nonpos (t_pos one_pos) ?_ (by linarith)
  have : Real.exp (-τ) ≤ Real.exp (-1) := Real.exp_le_exp.2 (by linarith)
  linarith

theorem tpow_nonneg (g : ℝ) {τ : ℝ} (hτ : 0 < τ) : 0 ≤ (1 - Real.exp (-τ)) ^ (-g) :=
  Real.rpow_nonneg (t_pos hτ).le _

theorem weight_integrable (g c : ℝ) (hg0 : 0 ≤ g) (hg : g < 1) (hc : 0 < c) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(c * τ)) * (1 - Real.exp (-τ)) ^ (-g)) (Ioi 0) := by
  have hcont : ContinuousOn (fun τ : ℝ => Real.exp (-(c * τ)) * (1 - Real.exp (-τ)) ^ (-g)) (Ioi 0) :=
    (by fun_prop : Continuous fun τ : ℝ => Real.exp (-(c * τ))).continuousOn.mul (tpow_continuousOn g)
  rw [← Ioc_union_Ioi_eq_Ioi zero_le_one]
  refine IntegrableOn.union ?_ ?_
  · have hI : IntegrableOn (fun τ : ℝ => Real.exp g * τ ^ (-g)) (Ioc 0 1) :=
      ((intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).1
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))).const_mul _
    refine integrableOn_of_abs_le measurableSet_Ioc (hcont.mono Ioc_subset_Ioi_self) hI fun τ hτ => ?_
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (tpow_nonneg g hτ.1))]
    have h1 : Real.exp (-(c * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hτ.1])
    calc Real.exp (-(c * τ)) * (1 - Real.exp (-τ)) ^ (-g) ≤ 1 * (1 - Real.exp (-τ)) ^ (-g) := by
          gcongr; exact tpow_nonneg g hτ.1
      _ ≤ Real.exp g * τ ^ (-g) := by rw [one_mul]; exact tpow_le_near g hg0 hτ.1 hτ.2
  · have hI : IntegrableOn (fun τ : ℝ => (1 - Real.exp (-1)) ^ (-g) * Real.exp (-c * τ)) (Ioi 1) :=
      (exp_neg_integrableOn_Ioi 1 hc).const_mul _
    refine integrableOn_of_abs_le measurableSet_Ioi (hcont.mono (Ioi_subset_Ioi zero_le_one)) hI
      fun τ hτ => ?_
    have hτ0 : (0 : ℝ) < τ := lt_trans one_pos hτ
    rw [abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (tpow_nonneg g hτ0)), neg_mul,
      mul_comm ((1 - Real.exp (-1)) ^ (-g))]
    exact mul_le_mul_of_nonneg_left (tpow_le_far g hg0 (le_of_lt hτ)) (Real.exp_pos _).le


theorem base_cont (g s b y : ℝ) (hy : 0 ≤ y) : ContinuousOn (fun τ : ℝ => Real.exp (-(g * s * τ)) *
    (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^ (-b)) (Ioi 0) := by
  refine ((by fun_prop : Continuous fun τ : ℝ => Real.exp (-(g * s * τ))).continuousOn.mul
    (tpow_continuousOn g)).mul ?_
  refine ContinuousOn.rpow_const (by fun_prop) fun τ _ => Or.inl ?_
  have := Real.exp_pos (-(g * τ)); positivity

theorem upow_le_one (g b y τ : ℝ) (hb : 0 ≤ b) (hy : 0 ≤ y) : (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤ 1 :=
  Real.rpow_le_one_of_one_le_of_nonpos (by nlinarith [Real.exp_pos (-(g * τ))]) (by linarith)

theorem base_le (g s b y : ℝ) (hb : 0 ≤ b) (hy : 0 ≤ y) {τ : ℝ} (hτ : 0 < τ) :
    Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤
      Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) := by
  have h0 : 0 ≤ Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) :=
    mul_nonneg (Real.exp_pos _).le (tpow_nonneg g hτ)
  exact mul_le_of_le_one_right h0 (upow_le_one g b y τ hb hy)

theorem base_integrable (g s b y : ℝ) (hg0 : 0 < g) (hg : g < 1) (hs : 0 < s) (hb : 0 ≤ b) (hy : 0 ≤ y) :
    IntegrableOn (fun τ : ℝ => Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
        (1 + Real.exp (-(g * τ)) * y) ^ (-b)) (Ioi 0) := by
  refine integrableOn_of_abs_le measurableSet_Ioi (base_cont g s b y hy)
    (weight_integrable g (g * s) hg0.le hg (by positivity)) fun τ hτ => ?_
  have hτ' : (0 : ℝ) < τ := hτ
  rw [abs_of_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (tpow_nonneg g hτ'))
    (Real.rpow_nonneg (by nlinarith [Real.exp_pos (-(g * τ))]) _))]
  exact base_le g s b y hb hy hτ'

def shape (g s b : ℝ) (x : ℝ) : ℝ := Real.exp (-(g * s * x)) * (1 + Real.exp (-(g * x))) ^ (-b)

theorem shape_nonneg (g s b x : ℝ) : 0 ≤ shape g s b x :=
  mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by linarith [Real.exp_pos (-(g * x))]) _)

theorem shape_integrable (g s b : ℝ) (hg0 : 0 < g) (hs : 0 < s) (hbs : s < b) :
    Integrable (shape g s b) := by
  set k := g * min s (b - s) with hk
  have hk0 : 0 < k := mul_pos hg0 (lt_min hs (by linarith))
  have hks : k ≤ g * s := mul_le_mul_of_nonneg_left (min_le_left _ _) hg0.le
  have hkb : k ≤ g * (b - s) := mul_le_mul_of_nonneg_left (min_le_right _ _) hg0.le
  have habs : Integrable (fun x : ℝ => Real.exp (-(k * |x|))) := by
    rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ))]
    refine IntegrableOn.union ?_ ?_
    · refine (integrableOn_exp_mul_Iic hk0 0).congr_fun (fun x hx => ?_) measurableSet_Iic
      simp only [mem_Iic] at hx
      simp only [abs_of_nonpos hx]; ring_nf
    · refine (exp_neg_integrableOn_Ioi 0 hk0).congr_fun (fun x hx => ?_) measurableSet_Ioi
      simp only [mem_Ioi] at hx
      simp only [abs_of_pos hx]; ring_nf
  have hcont : Continuous (shape g s b) := by
    unfold shape
    refine (by fun_prop : Continuous fun x : ℝ => Real.exp (-(g * s * x))).mul ?_
    refine Continuous.rpow_const (by fun_prop) fun x => Or.inl ?_
    have := Real.exp_pos (-(g * x)); positivity
  refine Integrable.mono' habs hcont.aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (shape_nonneg g s b x)]
  unfold shape
  rcases le_or_gt 0 x with hx | hx
  · rw [abs_of_nonneg hx]
    calc Real.exp (-(g * s * x)) * (1 + Real.exp (-(g * x))) ^ (-b) ≤ Real.exp (-(g * s * x)) * 1 := by
          gcongr
          exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [Real.exp_pos (-(g * x))]) (by linarith)
      _ ≤ Real.exp (-(k * x)) := by rw [mul_one]; gcongr
  · rw [abs_of_neg hx]
    have h1 : (1 + Real.exp (-(g * x))) ^ (-b) ≤ Real.exp (g * b * x) := by
      refine le_trans (Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (by linarith) (by linarith)) ?_
      rw [← Real.exp_mul]; apply le_of_eq; ring_nf
    calc Real.exp (-(g * s * x)) * (1 + Real.exp (-(g * x))) ^ (-b)
        ≤ Real.exp (-(g * s * x)) * Real.exp (g * b * x) := by gcongr
      _ = Real.exp (g * (b - s) * x) := by rw [← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(k * -x)) := by gcongr; nlinarith

theorem shape_identity (g s b y τ : ℝ) (hg0 : 0 < g) (hy : 0 < y) :
    Real.exp (-(g * s * τ)) * (1 + Real.exp (-(g * τ)) * y) ^ (-b) =
      y ^ (-s) * shape g s b (τ - Real.log y / g) := by
  unfold shape
  have e1 : Real.exp (-(g * (τ - Real.log y / g))) = Real.exp (-(g * τ)) * y := by
    rw [show -(g * (τ - Real.log y / g)) = -(g * τ) + Real.log y by field_simp; ring, Real.exp_add,
      Real.exp_log hy]
  have e2 : Real.exp (-(g * s * (τ - Real.log y / g))) = Real.exp (-(g * s * τ)) * y ^ s := by
    rw [show -(g * s * (τ - Real.log y / g)) = -(g * s * τ) + Real.log y * s by field_simp; ring,
      Real.exp_add, Real.rpow_def_of_pos hy]
  rw [e1, e2, Real.rpow_neg hy.le]
  have : y ^ s ≠ 0 := (Real.rpow_pos_of_pos hy s).ne'
  field_simp

theorem scalar_bound (g s b : ℝ) (hg0 : 0 < g) (hg : g < 1) (hs : 0 < s) (hb : 0 ≤ b) (hbs : b ≠ s) :
    ∃ K : ℝ, ∀ y : ℝ, 0 ≤ y →
      IntegrableOn (fun τ : ℝ => Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
        (1 + Real.exp (-(g * τ)) * y) ^ (-b)) (Ioi 0) ∧
      (1 + y) ^ (min b s) * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
        (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤ K := by
  set Es := ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) with hEs
  have hEsI := weight_integrable g (g * s) hg0.le hg (by positivity)
  have hEs0 : 0 ≤ Es := setIntegral_nonneg measurableSet_Ioi fun τ hτ =>
    mul_nonneg (Real.exp_pos _).le (tpow_nonneg g hτ)
  rcases lt_or_gt_of_ne hbs with hlt | hgt
  · have hwI := weight_integrable g (g * (s - b)) hg0.le hg (mul_pos hg0 (by linarith))
    refine ⟨∫ τ in Ioi (0 : ℝ), Real.exp (-(g * (s - b) * τ)) * (1 - Real.exp (-τ)) ^ (-g),
      fun y hy => ⟨base_integrable g s b y hg0 hg hs hb hy, ?_⟩⟩
    rw [min_eq_left hlt.le]
    have hy1 : 0 < 1 + y := by linarith
    have hbound : ∀ τ ∈ Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
        (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤
        (1 + y) ^ (-b) * (Real.exp (-(g * (s - b) * τ)) * (1 - Real.exp (-τ)) ^ (-g)) := by
      intro τ hτ
      have hτ' : (0 : ℝ) < τ := hτ
      have he : Real.exp (-(g * τ)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      have hep := Real.exp_pos (-(g * τ))
      have h1 : (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤ Real.exp (g * b * τ) * (1 + y) ^ (-b) := by
        refine le_trans (Real.rpow_le_rpow_of_nonpos (mul_pos hep hy1) (by nlinarith) (by linarith)) ?_
        rw [Real.mul_rpow hep.le hy1.le, ← Real.exp_mul]
        apply le_of_eq; congr 2; ring
      have hq := tpow_nonneg g hτ'
      calc Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^ (-b)
          ≤ Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (Real.exp (g * b * τ) * (1 + y) ^ (-b)) := by
            gcongr
        _ = (1 + y) ^ (-b) * ((Real.exp (-(g * s * τ)) * Real.exp (g * b * τ)) * (1 - Real.exp (-τ)) ^ (-g)) := by
            ring
        _ = _ := by rw [← Real.exp_add]; ring_nf
    have hint := setIntegral_mono_on (base_integrable g s b y hg0 hg hs hb hy) (hwI.const_mul _)
      measurableSet_Ioi hbound
    rw [integral_const_mul] at hint
    have hpb : 0 < (1 + y) ^ b := Real.rpow_pos_of_pos hy1 b
    calc (1 + y) ^ b * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
          (1 + Real.exp (-(g * τ)) * y) ^ (-b)
        ≤ (1 + y) ^ b * ((1 + y) ^ (-b) * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * (s - b) * τ)) *
            (1 - Real.exp (-τ)) ^ (-g)) := by gcongr
      _ = _ := by rw [Real.rpow_neg hy1.le, ← mul_assoc, mul_inv_cancel₀ hpb.ne', one_mul]
  · have hψI := shape_integrable g s b hg0 hs hgt
    set Ψ := ∫ x, shape g s b x with hΨ
    have hΨ0 : 0 ≤ Ψ := integral_nonneg fun x => shape_nonneg g s b x
    set C0 := (1 - Real.exp (-1)) ^ (-g) with hC0
    have hC00 : 0 ≤ C0 := Real.rpow_nonneg (t_pos one_pos).le _
    have h2s : 0 < (2 : ℝ) ^ s := Real.rpow_pos_of_pos two_pos s
    refine ⟨2 ^ s * Es + Real.exp (g * b) * Es + C0 * 2 ^ s * Ψ,
      fun y hy => ⟨base_integrable g s b y hg0 hg hs hb hy, ?_⟩⟩
    rw [min_eq_right hgt.le]
    have hy1 : 0 < 1 + y := by linarith
    have hEb : 0 ≤ Real.exp (g * b) * Es := mul_nonneg (Real.exp_pos _).le hEs0
    have hΨb : 0 ≤ C0 * 2 ^ s * Ψ := mul_nonneg (mul_nonneg hC00 h2s.le) hΨ0
    rcases le_or_gt y 1 with hy1' | hy1'
    · have hint := setIntegral_mono_on (base_integrable g s b y hg0 hg hs hb hy) hEsI measurableSet_Ioi
        fun τ hτ => base_le g s b y hb hy hτ
      have hp : (1 + y) ^ s ≤ 2 ^ s := Real.rpow_le_rpow hy1.le (by linarith) hs.le
      have hI0 : 0 ≤ ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
          (1 + Real.exp (-(g * τ)) * y) ^ (-b) :=
        setIntegral_nonneg measurableSet_Ioi fun τ hτ => by
            have hτ' : (0 : ℝ) < τ := hτ
            exact mul_nonneg (mul_nonneg (Real.exp_pos _).le (tpow_nonneg g hτ'))
              (Real.rpow_nonneg (by nlinarith [Real.exp_pos (-(g * τ))]) _)
      calc (1 + y) ^ s * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
            (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤ 2 ^ s * Es := mul_le_mul hp hint hI0 h2s.le
        _ ≤ _ := by linarith
    · have hy0 : 0 < y := by linarith
      set τ0 := Real.log y / g
      have hys : y ^ (-s) ≤ 2 ^ s * (1 + y) ^ (-s) := by
        have hpy : y ^ s ≠ 0 := (Real.rpow_pos_of_pos hy0 s).ne'
        have hp1 : (1 + y) ^ s ≠ 0 := (Real.rpow_pos_of_pos hy1 s).ne'
        have e1 : y ^ (-s) = ((1 + y) / y) ^ s * (1 + y) ^ (-s) := by
          rw [Real.div_rpow hy1.le hy0.le, Real.rpow_neg hy0.le, Real.rpow_neg hy1.le]
          field_simp
        rw [e1]
        gcongr
        rw [div_le_iff₀ hy0]; linarith
      set G : ℝ → ℝ := fun τ => (1 + y) ^ (-s) * (Real.exp (g * b) *
        (Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g)) + C0 * 2 ^ s * shape g s b (τ - τ0)) with hG
      have hGI : IntegrableOn G (Ioi 0) :=
        (((hEsI.const_mul (Real.exp (g * b)))).add
          ((hψI.comp_sub_right τ0).integrableOn.const_mul (C0 * 2 ^ s))).const_mul _
      have hps : 0 ≤ (1 + y) ^ (-s) := Real.rpow_nonneg hy1.le _
      have hbound : ∀ τ ∈ Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
          (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤ G τ := by
        intro τ hτ
        have hτ' : (0 : ℝ) < τ := hτ
        have hq := tpow_nonneg g hτ'
        have hsh := shape_nonneg g s b (τ - τ0)
        have hep := Real.exp_pos (-(g * τ))
        rcases le_or_gt τ 1 with hτ1 | hτ1
        · have he1 : Real.exp (-g) ≤ Real.exp (-(g * τ)) := Real.exp_le_exp.2 (by nlinarith)
          have he2 : Real.exp (-g) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
          have h1 : (1 + Real.exp (-(g * τ)) * y) ^ (-b) ≤ Real.exp (g * b) * (1 + y) ^ (-s) := by
            refine le_trans (Real.rpow_le_rpow_of_nonpos (mul_pos (Real.exp_pos (-g)) hy1)
              (by nlinarith) (by linarith)) ?_
            rw [Real.mul_rpow (Real.exp_pos _).le hy1.le, ← Real.exp_mul,
              show -g * -b = g * b by ring]
            gcongr; linarith
          calc Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^ (-b)
              ≤ Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (Real.exp (g * b) * (1 + y) ^ (-s)) := by
                gcongr
            _ = (1 + y) ^ (-s) * (Real.exp (g * b) * (Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g)) + 0) := by
                ring
            _ ≤ G τ := by
                simp only [hG]
                exact mul_le_mul_of_nonneg_left (add_le_add_right (mul_nonneg (mul_nonneg hC00 h2s.le) hsh) _) hps
        · have hq1 := tpow_le_far g hg0.le hτ1.le
          have hid := shape_identity g s b y τ hg0 hy0
          calc Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * y) ^ (-b)
              = (1 - Real.exp (-τ)) ^ (-g) * (y ^ (-s) * shape g s b (τ - τ0)) := by rw [← hid]; ring
            _ ≤ C0 * (2 ^ s * (1 + y) ^ (-s) * shape g s b (τ - τ0)) := by gcongr
            _ = (1 + y) ^ (-s) * (0 + C0 * 2 ^ s * shape g s b (τ - τ0)) := by ring
            _ ≤ G τ := by
                simp only [hG]
                exact mul_le_mul_of_nonneg_left (add_le_add_left (mul_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le hq)) _) hps
      have hint := setIntegral_mono_on (base_integrable g s b y hg0 hg hs hb hy) hGI measurableSet_Ioi hbound
      have hsh : ∫ τ in Ioi (0 : ℝ), shape g s b (τ - τ0) ≤ Ψ := by
        refine le_trans (setIntegral_le_integral (hψI.comp_sub_right τ0)
          (Filter.Eventually.of_forall fun x => shape_nonneg g s b _)) (le_of_eq ?_)
        exact integral_sub_right_eq_self (shape g s b) τ0
      have hGint : ∫ τ in Ioi (0 : ℝ), G τ = (1 + y) ^ (-s) * (Real.exp (g * b) * Es +
          C0 * 2 ^ s * ∫ τ in Ioi (0 : ℝ), shape g s b (τ - τ0)) := by
        rw [hG, integral_const_mul, integral_add (hEsI.const_mul _)
          ((hψI.comp_sub_right τ0).integrableOn.const_mul _), integral_const_mul, integral_const_mul]
      have hpb : 0 < (1 + y) ^ s := Real.rpow_pos_of_pos hy1 s
      calc (1 + y) ^ s * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
            (1 + Real.exp (-(g * τ)) * y) ^ (-b)
          ≤ (1 + y) ^ s * ((1 + y) ^ (-s) * (Real.exp (g * b) * Es + C0 * 2 ^ s * Ψ)) := by
            refine mul_le_mul_of_nonneg_left (le_trans hint ?_) hpb.le
            rw [hGint]
            gcongr
        _ = Real.exp (g * b) * Es + C0 * 2 ^ s * Ψ := by
            rw [Real.rpow_neg hy1.le, ← mul_assoc, mul_inv_cancel₀ hpb.ne', one_mul]
        _ ≤ _ := by nlinarith [mul_nonneg h2s.le hEs0]

theorem cont_left {k : ℕ} {S : Set ℝ} {g : ℝ → Space →L[ℝ] Space}
    {q : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) Space}
    (hg : ContinuousOn g S) (hq : ContinuousOn q S) :
    ContinuousOn (fun τ => (g τ).compContinuousMultilinearMap (q τ)) S := by
  have : (fun τ => (g τ).compContinuousMultilinearMap (q τ)) = fun τ =>
      ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Space) Space Space (g τ) (q τ) := rfl
  rw [this]
  exact ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ _ _ _).continuous.comp_continuousOn hg).clm_apply hq

theorem cont_right {k : ℕ} {S : Set ℝ} {L : ℝ → Space →L[ℝ] Space}
    {p : ℝ → ContinuousMultilinearMap ℝ (fun _ : Fin k => Space) Space}
    (hL : ContinuousOn L S) (hp : ContinuousOn p S) :
    ContinuousOn (fun τ => (p τ).compContinuousLinearMap (fun _ => L τ)) S := by
  have : (fun τ => (p τ).compContinuousLinearMap (fun _ => L τ)) = fun τ =>
      ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ (fun _ : Fin k => Space)
        (fun _ : Fin k => Space) Space (fun _ => L τ) (p τ) := by
    funext τ; ext v; simp
  rw [this]
  exact ((ContinuousMultilinearMap.compContinuousLinearMapContinuousMultilinear ℝ _ _ _).cont.comp_continuousOn
    (continuousOn_pi.2 fun _ => hL)).clm_apply hp

theorem rot_clm_cont (a : ℝ) :
    Continuous (fun τ : ℝ => ((axialRotation (a * τ) : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space)) := by
  refine continuous_clm_apply.2 fun v => ?_
  have h := (Breakdown.Periodic.FracSelfSimilar.Internal.rot_contDiff
    Breakdown.axialRotationSpec).continuous
  have e : ∀ τ : ℝ, ((axialRotation (a * τ) : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space) v =
      axialRotation (a * τ) v := fun τ => rfl
  simp only [e]
  have h2 : Continuous (fun τ : ℝ => ((a * τ, v) : ℝ × Space)) :=
    (continuous_const.mul continuous_id).prodMk continuous_const
  exact (h.comp h2).congr fun τ => by simp only [Function.comp_apply]

theorem rot_symm_clm_cont (a : ℝ) :
    Continuous (fun τ : ℝ => (((axialRotation (a * τ)).symm : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space)) := by
  refine continuous_clm_apply.2 fun v => ?_
  have hA := Breakdown.axialRotationSpec
  have h := (Breakdown.Periodic.FracSelfSimilar.Internal.rot_contDiff hA).continuous
  have e : ∀ τ : ℝ, (((axialRotation (a * τ)).symm : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space) v =
      (axialRotation (a * τ)).symm v := fun τ => rfl
  have e2 : ∀ τ : ℝ, (axialRotation (a * τ)).symm v = axialRotation (-(a * τ)) v := by
    intro τ; rw [hA.2.2.2.1]
  simp only [e, e2]
  have h2 : Continuous (fun τ : ℝ => ((-(a * τ), v) : ℝ × Space)) :=
    (continuous_const.mul continuous_id).neg.prodMk continuous_const
  exact (h.comp h2).congr fun τ => by simp only [Function.comp_apply]

theorem integrand_iteratedFDeriv (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (k : ℕ) (τ : ℝ)
    (h : ContDiff ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)) (y : Space) :
    iteratedFDeriv ℝ k (integrand α a F τ) y =
      ((axialRotation (a * τ) : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space).compContinuousMultilinearMap
        ((Real.exp (-τ) ^ (1 - 1 / (2 * α)) •
          (iteratedFDeriv ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)
            (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)).compContinuousLinearMap
              (fun _ => Real.exp (-τ) ^ (1 / (2 * α)) • ContinuousLinearMap.id ℝ Space)).compContinuousLinearMap
          (fun _ => (((axialRotation (a * τ)).symm : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space))) := by
  set R := axialRotation (a * τ)
  set c := Real.exp (-τ) ^ (1 / (2 * α))
  set d := Real.exp (-τ) ^ (1 - 1 / (2 * α))
  set hh := heatDivConv α (1 - Real.exp (-τ)) F
  set L : Space →L[ℝ] Space := c • ContinuousLinearMap.id ℝ Space
  set Rc : Space →L[ℝ] Space := ((R : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space)
  set Rs : Space →L[ℝ] Space := ((R.symm : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space)
  have hfun : integrand α a F τ = Rc ∘ ((d • (hh ∘ L)) ∘ Rs) := by
    funext z; simp [integrand, pushForward, scaleField, L, R, c, d, hh, Rc, Rs]
  have hL : ContDiff ℝ k (hh ∘ L) := h.comp L.contDiff
  have hdL : ContDiff ℝ k (d • (hh ∘ L)) := contDiff_const.smul hL
  rw [hfun, ContinuousLinearMap.iteratedFDeriv_comp_left Rc (hdL.comp Rs.contDiff).contDiffAt le_rfl,
    ContinuousLinearMap.iteratedFDeriv_comp_right Rs hdL y le_rfl,
    iteratedFDeriv_const_smul_apply hL.contDiffAt,
    ContinuousLinearMap.iteratedFDeriv_comp_right L h (Rs y) le_rfl]
  rfl

theorem integrand_aesm (α a : ℝ) (F : Space → Fin 3 → Fin 3 → ℝ) (j : ℕ)
    (hsm : ∀ t : ℝ, 0 < t → ContDiff ℝ j (heatDivConv α t F))
    (hc : ∀ k ≤ j, ContinuousOn (fun p : ℝ × Space => iteratedFDeriv ℝ k (heatDivConv α p.1 F) p.2)
        (Ioi 0 ×ˢ univ)) :
    ∀ k ≤ j, ∀ y, AEStronglyMeasurable (fun τ => iteratedFDeriv ℝ k (integrand α a F τ) y)
      (volume.restrict (Ioi 0)) := by
  intro k hk y
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  have hpos : ∀ τ ∈ Ioi (0 : ℝ), 0 < 1 - Real.exp (-τ) := fun τ hτ => by
    have : Real.exp (-τ) < 1 := Real.exp_lt_one_iff.2 (by simp only [mem_Ioi] at hτ; linarith)
    linarith
  refine ContinuousOn.congr (f := fun τ =>
      ((axialRotation (a * τ) : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space).compContinuousMultilinearMap
        ((Real.exp (-τ) ^ (1 - 1 / (2 * α)) •
          (iteratedFDeriv ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)
            (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)).compContinuousLinearMap
              (fun _ => Real.exp (-τ) ^ (1 / (2 * α)) • ContinuousLinearMap.id ℝ Space)).compContinuousLinearMap
          (fun _ => (((axialRotation (a * τ)).symm : Space ≃ₗᵢ[ℝ] Space) : Space →L[ℝ] Space)))) ?_ ?_
  · have hcexp : ∀ r : ℝ, Continuous (fun τ : ℝ => Real.exp (-τ) ^ r) := fun r =>
      Continuous.rpow_const (by fun_prop) fun τ => Or.inl (Real.exp_pos _).ne'
    have hin : ContinuousOn (fun τ : ℝ => iteratedFDeriv ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)
        (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)) (Ioi 0) := by
      refine (hc k hk).comp (f := fun τ : ℝ => (1 - Real.exp (-τ),
        Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)) ?_ ?_
      · refine Continuous.continuousOn (Continuous.prodMk (by fun_prop) ?_)
        exact (hcexp _).smul ((rot_symm_clm_cont a).clm_apply continuous_const)
      · intro τ hτ
        exact ⟨hpos τ hτ, mem_univ _⟩
    refine cont_left (rot_clm_cont a).continuousOn (cont_right (rot_symm_clm_cont a).continuousOn ?_)
    refine ((hcexp _).continuousOn).smul (cont_right ?_ hin)
    exact ((hcexp _).smul continuous_const).continuousOn
  · intro τ hτ
    exact integrand_iteratedFDeriv α a F k τ ((hsm _ (hpos τ hτ)).of_le (by exact_mod_cast hk)) y

end DecayFarField.Internal

open DecayFarField.Internal

theorem farFieldBound_of (h1 : HeatDivBoundStatement) (h2 : HeatDivRegularStatement) :
    FarFieldBoundStatement := by
  intro α hα1 hα2 a β b j hβ0 hβ3 hb0 hbj hbne
  obtain ⟨C1, hC1⟩ := h1 α hα1 hα2 β b j hβ0 hβ3 hb0 hbj
  obtain ⟨C2, hC2⟩ := h2 α hα1 hα2 β j hβ0 hβ3
  have hαpos : 0 < α := by linarith
  set g : ℝ := 1 / (2 * α) with hg
  have hg0 : 0 < g := by positivity
  have hg1 : g < 1 := by rw [hg, div_lt_one (by positivity)]; linarith
  have hg2 : g * (2 * α) = 1 := by rw [hg]; field_simp
  set s : ℝ := 2 * α - 1 + j with hs
  have hs0 : 0 < s := by have : (0 : ℝ) ≤ j := Nat.cast_nonneg j; rw [hs]; linarith
  obtain ⟨K, hK⟩ := scalar_bound g s b hg0 hg1 hs0 hb0 hbne
  have hwI := weight_integrable g (1 - g) hg0.le hg1 (by linarith)
  refine ⟨max C1 0 * K, ?_⟩
  intro F A B hF hA hB
  have hA0 : 0 ≤ A := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (hA 0)
  have hB0 : 0 ≤ B := le_trans (mul_nonneg (by positivity) (norm_nonneg _)) (hB 0)
  have hA' : ∀ y, ‖iteratedFDeriv ℝ j F y‖ ≤ A := by
    intro y
    have h1y : (1 : ℝ) ≤ (1 + ‖y‖) ^ b := Real.one_le_rpow (by linarith [norm_nonneg y]) hb0
    exact le_trans (le_mul_of_one_le_left (norm_nonneg _) h1y) (hA y)
  obtain ⟨hsm, hct, hbd⟩ := hC2 F A B hF hA' hB
  have ht : ∀ τ : ℝ, 0 < τ → 0 < 1 - Real.exp (-τ) ∧ 1 - Real.exp (-τ) ≤ 1 := by
    intro τ hτ
    have h0 : Real.exp (-τ) < 1 := (Real.exp_lt_exp.2 (by linarith : -τ < 0)).trans_eq Real.exp_zero
    exact ⟨by linarith, by linarith [Real.exp_pos (-τ)]⟩
  have hμ : ∀ τ : ℝ, Real.exp (-τ) ^ (1 - g) = Real.exp (-((1 - g) * τ)) := by
    intro τ; rw [← Real.exp_mul]; ring_nf
  have hμg : ∀ τ : ℝ, Real.exp (-τ) ^ g = Real.exp (-(g * τ)) := by
    intro τ; rw [← Real.exp_mul]; ring_nf
  have hsj : ∀ τ : ℝ, Real.exp (-τ) ^ (1 - g) * (Real.exp (-τ) ^ g) ^ j = Real.exp (-(g * s * τ)) := by
    intro τ
    rw [hμ, hμg, ← Real.exp_nat_mul, ← Real.exp_add]
    congr 1
    have : g * s = g * (2 * α) - g + g * j := by rw [hs]; ring
    rw [this, hg2]; ring
  have hpow : ∀ τ : ℝ, 0 < τ → ∀ k : ℕ, (Real.exp (-τ) ^ g) ^ k ≤ 1 := by
    intro τ hτ k
    rw [hμg]
    exact pow_le_one₀ (Real.exp_pos _).le (Real.exp_le_one_iff.2 (by nlinarith))
  have hbnd : ∀ k ≤ j, ∀ τ, 0 < τ → ∀ y, ‖iteratedFDeriv ℝ k (integrand α a F τ) y‖ ≤
      max C2 0 * (A + B) * (Real.exp (-((1 - g) * τ)) * (1 - Real.exp (-τ)) ^ (-g)) := by
    intro k hk τ hτ y
    have hk' : ContDiff ℝ k (heatDivConv α (1 - Real.exp (-τ)) F) :=
      (hsm _ (ht τ hτ).1).of_le (by exact_mod_cast hk)
    refine le_trans (integrand_norm_le α a F k τ hk' y) ?_
    have h3 := hbd k hk _ (ht τ hτ).1 (ht τ hτ).2 (Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y)
    have hq : 0 ≤ (1 - Real.exp (-τ)) ^ (-g) := Real.rpow_nonneg (ht τ hτ).1.le _
    have h4 : C2 * (1 - Real.exp (-τ)) ^ (-(1 / (2 * α))) * (A + B) ≤
        max C2 0 * (1 - Real.exp (-τ)) ^ (-g) * (A + B) := by
      rw [← hg]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hq) (by linarith)
    have h5 := hpow τ hτ k
    rw [← hg] at h3 ⊢
    have hm0 : 0 ≤ max C2 0 * (1 - Real.exp (-τ)) ^ (-g) * (A + B) :=
      mul_nonneg (mul_nonneg (le_max_right _ _) hq) (by linarith)
    calc Real.exp (-τ) ^ (1 - g) * (Real.exp (-τ) ^ g) ^ k *
          ‖iteratedFDeriv ℝ k (heatDivConv α (1 - Real.exp (-τ)) F)
            (Real.exp (-τ) ^ g • (axialRotation (a * τ)).symm y)‖
        ≤ Real.exp (-τ) ^ (1 - g) * 1 * (max C2 0 * (1 - Real.exp (-τ)) ^ (-g) * (A + B)) := by
          gcongr
          exact le_trans h3 h4
      _ = _ := by rw [hμ]; ring
  have key := integral_contDiff (Φ := integrand α a F) j
    (fun τ hτ => integrand_contDiff α a F j τ (hsm _ (ht τ hτ).1))
    (integrand_aesm α a F j hsm hct) hbnd (hwI.const_mul _)
  have hfun : farFieldOp α a F = fun y => -∫ τ in Ioi (0 : ℝ), integrand α a F τ y := rfl
  rw [hfun]
  refine ⟨key.1.neg, fun y => ?_⟩
  show (1 + ‖y‖) ^ min b s * ‖iteratedFDeriv ℝ j (-(fun y => ∫ τ in Ioi (0 : ℝ), integrand α a F τ y)) y‖ ≤ _
  rw [iteratedFDeriv_neg_apply, norm_neg, key.2 y]
  obtain ⟨hIint, hIK⟩ := hK ‖y‖ (norm_nonneg y)
  have hC1' : 0 ≤ max C1 0 * (A + B) := mul_nonneg (le_max_right _ _) (by linarith)
  have hle : ‖∫ τ in Ioi (0 : ℝ), iteratedFDeriv ℝ j (integrand α a F τ) y‖ ≤
      ∫ τ in Ioi (0 : ℝ), max C1 0 * (A + B) * (Real.exp (-(g * s * τ)) * (1 - Real.exp (-τ)) ^ (-g) *
        (1 + Real.exp (-(g * τ)) * ‖y‖) ^ (-b)) := by
    refine norm_integral_le_of_norm_le (hIint.const_mul _) ?_
    refine (ae_restrict_iff' measurableSet_Ioi).2 (Filter.Eventually.of_forall fun τ hτ => ?_)
    have hτ : (0 : ℝ) < τ := hτ
    have hk' : ContDiff ℝ j (heatDivConv α (1 - Real.exp (-τ)) F) := hsm _ (ht τ hτ).1
    refine le_trans (integrand_norm_le α a F j τ hk' y) ?_
    set x := Real.exp (-τ) ^ (1 / (2 * α)) • (axialRotation (a * τ)).symm y with hx
    have hxn : ‖x‖ = Real.exp (-(g * τ)) * ‖y‖ := by
      rw [hx, norm_smul, LinearIsometryEquiv.norm_map, ← hg, hμg, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    have h3 := hC1 _ (ht τ hτ).1 (ht τ hτ).2 F A B hF hA hB x
    have hw1 : 0 < 1 + ‖x‖ := by linarith [norm_nonneg x]
    have hwb : 0 < (1 + ‖x‖) ^ b := Real.rpow_pos_of_pos hw1 _
    have hq : 0 ≤ (1 - Real.exp (-τ)) ^ (-g) := Real.rpow_nonneg (ht τ hτ).1.le _
    have h4 : ‖iteratedFDeriv ℝ j (heatDivConv α (1 - Real.exp (-τ)) F) x‖ ≤
        max C1 0 * (A + B) * ((1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * ‖y‖) ^ (-b)) := by
      rw [← hxn, Real.rpow_neg hw1.le]
      have h5 : C1 * (1 - Real.exp (-τ)) ^ (-g) * (A + B) ≤ max C1 0 * (A + B) * (1 - Real.exp (-τ)) ^ (-g) := by
        have := mul_le_mul_of_nonneg_right (le_max_left C1 0) hq
        nlinarith
      have h6 : ‖iteratedFDeriv ℝ j (heatDivConv α (1 - Real.exp (-τ)) F) x‖ * (1 + ‖x‖) ^ b ≤
          max C1 0 * (A + B) * (1 - Real.exp (-τ)) ^ (-g) := by linarith
      calc ‖iteratedFDeriv ℝ j (heatDivConv α (1 - Real.exp (-τ)) F) x‖
          = ‖iteratedFDeriv ℝ j (heatDivConv α (1 - Real.exp (-τ)) F) x‖ * (1 + ‖x‖) ^ b *
              ((1 + ‖x‖) ^ b)⁻¹ := by field_simp
        _ ≤ max C1 0 * (A + B) * (1 - Real.exp (-τ)) ^ (-g) * ((1 + ‖x‖) ^ b)⁻¹ := by gcongr
        _ = _ := by ring
    rw [← hg]
    calc Real.exp (-τ) ^ (1 - g) * (Real.exp (-τ) ^ g) ^ j * ‖iteratedFDeriv ℝ j (heatDivConv α (1 - Real.exp (-τ)) F) x‖
        ≤ Real.exp (-τ) ^ (1 - g) * (Real.exp (-τ) ^ g) ^ j * (max C1 0 * (A + B) * ((1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * ‖y‖) ^ (-b))) := by
          gcongr
      _ = _ := by rw [← hsj τ]; ring
  have hm : (1 + ‖y‖) ^ min b s ≥ 0 := by positivity
  calc (1 + ‖y‖) ^ min b (2 * α - 1 + j) * ‖∫ τ in Ioi (0 : ℝ), iteratedFDeriv ℝ j (integrand α a F τ) y‖
      ≤ (1 + ‖y‖) ^ min b s * (max C1 0 * (A + B) * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) *
          (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * ‖y‖) ^ (-b)) := by
        rw [← integral_const_mul]; exact mul_le_mul_of_nonneg_left hle hm
    _ = max C1 0 * (A + B) * ((1 + ‖y‖) ^ min b s * ∫ τ in Ioi (0 : ℝ), Real.exp (-(g * s * τ)) *
          (1 - Real.exp (-τ)) ^ (-g) * (1 + Real.exp (-(g * τ)) * ‖y‖) ^ (-b)) := by ring
    _ ≤ max C1 0 * (A + B) * K := mul_le_mul_of_nonneg_left hIK hC1'
    _ = max C1 0 * K * (A + B) := by ring

end Breakdown.FracCert
