import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoerciveField
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveFrequencySeminorm
import Breakdown.Cert.CoercivePieceFieldCurlWeight

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace PieceField

namespace Internal

def secondDerivPairing (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ψ : ℝ → Space → Space) : ℝ :=
  ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ σ y)

def pieceIntegrand {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ψ : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
    ((∑ β : Fin nE, (Complex.I * ((PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y : ℝ) : ℂ)
        * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re)
      + ∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y : ℝ) : ℂ)
        * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re)

def pieceModeSum {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ψ : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ ι σ y

theorem scalar_pair_bound {α β c cμ E S : ℝ} (hc : 0 < c) (hcμ : 0 < cμ) (hE : 0 ≤ E) :
    α * Real.sqrt E + β * S ≤ Real.sqrt (α ^ 2 / c + β ^ 2 / cμ) * Real.sqrt (c * E + cμ * S ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.le_sqrt_of_sq_le
  have he := Real.sq_sqrt hE
  have he0 := Real.sqrt_nonneg E
  set e := Real.sqrt E
  rw [div_add_div _ _ hc.ne' hcμ.ne', div_mul_eq_mul_div, le_div_iff₀ (by positivity), ← he]
  nlinarith [sq_nonneg (α * cμ * S - β * c * e)]

theorem coef_le {ε ε' r c cμ w₀ T Gr E n : ℝ} (hc : 0 < c) (hcμ : 0 < cμ) (hw₀ : 0 < w₀)
    (hε : 0 ≤ ε) (hε' : 0 ≤ ε') (hr : 0 ≤ r) (hn : 0 ≤ n) (hT0 : 0 ≤ T) (hG0 : 0 ≤ Gr)
    (hT : T ≤ E) (hG : w₀ * Gr ≤ E) :
    Real.sqrt T + (ε * Real.sqrt T + ε' * Real.sqrt Gr + Real.sqrt (r * n))
      ≤ Real.sqrt ((1 + ε + ε' / Real.sqrt w₀) ^ 2 / c + r / cμ) * Real.sqrt (c * E + cμ * n) := by
  have hE : 0 ≤ E := hT0.trans hT
  have hsw := Real.sqrt_pos.2 hw₀
  have h1 : Real.sqrt T ≤ Real.sqrt E := Real.sqrt_le_sqrt hT
  have h2 : Real.sqrt Gr ≤ Real.sqrt E / Real.sqrt w₀ := by
    rw [le_div_iff₀ hsw, ← Real.sqrt_mul hG0, mul_comm]
    exact Real.sqrt_le_sqrt hG
  have key := scalar_pair_bound (α := 1 + ε + ε' / Real.sqrt w₀) (β := Real.sqrt r) (S := Real.sqrt n) hc hcμ hE
  rw [Real.sq_sqrt hr, Real.sq_sqrt hn] at key
  refine le_trans ?_ key
  rw [Real.sqrt_mul hr]
  have h3 : ε' * Real.sqrt Gr ≤ ε' / Real.sqrt w₀ * Real.sqrt E := by
    rw [div_mul_eq_mul_div, mul_div_assoc]
    exact mul_le_mul_of_nonneg_left h2 hε'
  nlinarith [mul_le_mul_of_nonneg_left h1 hε]

theorem periodLIntegral_mono {f g : ℝ → Space → ℝ} (hfg : ∀ σ y, f σ y ≤ g σ y) :
    periodLIntegral f ≤ periodLIntegral g :=
  lintegral_mono fun σ => lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hfg σ y)

theorem periodLIntegral_const_mul {a : ℝ} (ha : 0 ≤ a) (f : ℝ → Space → ℝ) :
    periodLIntegral (fun σ y => a * f σ y) = ENNReal.ofReal a * periodLIntegral f := by
  unfold periodLIntegral
  simp_rw [ENNReal.ofReal_mul ha]
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  congr 1
  funext σ
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

theorem restrict_eq_prod : (volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)
    = (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume := by
  rw [Measure.volume_eq_prod, ← Measure.prod_restrict, Measure.restrict_univ]

theorem periodLIntegral_eq_prod {f : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) volume) :
    periodLIntegral f = ∫⁻ z in Set.Icc (0 : ℝ) 1 ×ˢ Set.univ, ENNReal.ofReal (f z.1 z.2) := by
  rw [restrict_eq_prod, lintegral_prod _ (by rw [← restrict_eq_prod]; exact hf.restrict)]
  rfl

theorem periodLIntegral_add_le {f g : ℝ → Space → ℝ}
    (hf : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2)) volume)
    (hg : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (g z.1 z.2)) volume)
    (hfg : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (f z.1 z.2 + g z.1 z.2)) volume) :
    periodLIntegral (fun σ y => f σ y + g σ y) ≤ periodLIntegral f + periodLIntegral g := by
  have e := periodLIntegral_eq_prod (f := fun σ y => f σ y + g σ y) hfg
  rw [e, periodLIntegral_eq_prod hf, periodLIntegral_eq_prod hg, ← lintegral_add_left' hf.restrict]
  exact lintegral_mono fun z => ENNReal.ofReal_add_le

theorem continuous_secondDerivTrace_sq :
    Continuous (fun K : Space →L[ℝ] Space →L[ℝ] Space => ‖secondDerivTrace K‖ ^ 2) := by
  unfold secondDerivTrace
  fun_prop

theorem continuous_secondDerivTrace :
    Continuous (fun K : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace K) := by
  unfold secondDerivTrace
  fun_prop

theorem continuous_matSq : Continuous (fun K : Space →L[ℝ] Space => matSq K) := by
  unfold matSq
  fun_prop

theorem matSq_nonneg (K : Space →L[ℝ] Space) : 0 ≤ matSq K :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem testField_aesm {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    AEStronglyMeasurable (fun z : ℝ × Space => ψ z.1 z.2) volume :=
  hψ.1.continuous.aestronglyMeasurable

theorem testField_sq_lt_top {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2) < ⊤ := by
  obtain ⟨hs, -, ⟨R, hR⟩, -⟩ := hψ
  have hK : IsCompact (Set.Icc (0 : ℝ) 1 ×ˢ Metric.closedBall (0 : Space) R) :=
    isCompact_Icc.prod (isCompact_closedBall _ _)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hs.continuous.continuousOn
  have hpt : ∀ σ ∈ Set.Icc (0 : ℝ) 1, ∀ y, ENNReal.ofReal (‖ψ σ y‖ ^ 2)
      ≤ (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal (D ^ 2)) y := by
    intro σ hσ y
    by_cases hy : y ∈ Metric.closedBall (0 : Space) R
    · rw [Set.indicator_of_mem hy]
      apply ENNReal.ofReal_le_ofReal
      have h1 : ‖ψ σ y‖ ≤ D := hD (σ, y) ⟨hσ, hy⟩
      have h0 := norm_nonneg (ψ σ y)
      nlinarith
    · have hlt : R < ‖y‖ := by
        simpa [Metric.mem_closedBall, dist_zero_right] using hy
      simp [hR σ y hlt]
  calc periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2)
      ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          (Metric.closedBall (0 : Space) R).indicator (fun _ => ENNReal.ofReal (D ^ 2)) y :=
        setLIntegral_mono' measurableSet_Icc fun σ hσ => lintegral_mono fun y => hpt σ hσ y
    _ = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (D ^ 2) * volume (Metric.closedBall (0 : Space) R) := by
        simp only [lintegral_indicator_const measurableSet_closedBall]
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_Icc]
        exact ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_closedBall_lt_top)
          ENNReal.ofReal_lt_top

theorem integrable_inner_prod {F M : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hM : AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hM2 : periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤) :
    Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (M z.1 z.2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  rw [← restrict_eq_prod]
  have sq : ∀ {X : ℝ → Space → Space}, AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume →
      periodLIntegral (fun σ y => ‖X σ y‖ ^ 2) < ⊤ →
      Integrable (fun z : ℝ × Space => ‖X z.1 z.2‖ ^ 2)
        ((volume : Measure (ℝ × Space)).restrict (Set.Icc (0 : ℝ) 1 ×ˢ Set.univ)) := by
    intro X hX hX2
    refine ⟨(hX.norm.pow 2).restrict, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun z => sq_nonneg _)]
    have e := periodLIntegral_eq_prod (f := fun σ y => ‖X σ y‖ ^ 2) (hX.norm.pow 2).aemeasurable.ennreal_ofReal
    rw [← e]
    exact hX2
  refine Integrable.mono' ((sq hF hF2).add (sq hM hM2)) (hF.inner hM).restrict ?_
  refine Filter.Eventually.of_forall fun z => ?_
  have h1 := abs_real_inner_le_norm (F z.1 z.2) (M z.1 z.2)
  have h2 := norm_nonneg (F z.1 z.2)
  have h3 := norm_nonneg (M z.1 z.2)
  rw [Real.norm_eq_abs, Pi.add_apply]
  nlinarith [sq_nonneg (‖F z.1 z.2‖ - ‖M z.1 z.2‖)]

theorem modeAverage_const_mul {β : Type*} (ι : ℤ × ℤ) (a : ℝ) (f : ℝ → ℝ → β → ℝ) (b : β) :
    modeAverage ι (fun τ φ b => a * f τ φ b) b = (a : ℂ) * modeAverage ι f b := by
  unfold modeAverage
  simp only [Complex.ofReal_mul]
  simp_rw [mul_left_comm _ (a : ℂ), intervalIntegral.integral_const_mul]
  ring

theorem modeVel_smul (ι : ℤ × ℤ) (a : ℝ) (f : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    modeVel ι (fun σ y => a • f σ y) σ y = fun i => (a : ℂ) * modeVel ι f σ y i := by
  funext i
  unfold modeVel
  rw [← modeAverage_const_mul]
  simp only [RotationInternal.axialRot_map_smul, PiLp.smul_apply, smul_eq_mul]

theorem gradField_smul (a : ℝ) (ψ : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    gradField (fun σ y => a • ψ σ y) σ y = a • gradField ψ σ y := by
  unfold gradField
  exact congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := ψ σ) a) y

theorem modeGrad_smul (ι : ℤ × ℤ) (a : ℝ) (ψ : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    modeGrad ι (gradField (fun σ y => a • ψ σ y)) σ y
      = fun ij => (a : ℂ) * modeGrad ι (gradField ψ) σ y ij := by
  funext ij
  unfold modeGrad
  rw [← modeAverage_const_mul]
  simp only [gradField_smul, FunLike.coe_smul, Pi.smul_apply, RotationInternal.axialRot_map_smul,
    PiLp.smul_apply, smul_eq_mul]

theorem curlOfGrad_smul (a : ℝ) (g : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (fun ij => (a : ℂ) * g ij) = fun i => (a : ℂ) * curlOfGrad g i := by
  funext i
  simp only [curlOfGrad, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => by ring

theorem cdot_smul (a : ℝ) (x z : Fin 3 → ℂ) :
    cdot x (fun i => (a : ℂ) * z i) = (a : ℂ) * cdot x z := by
  simp only [cdot, map_mul, Complex.conj_ofReal, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem re_smul_aux (a : ℝ) (s c : ℂ) : (Complex.I * s * ((a : ℂ) * c)).re = a * (Complex.I * s * c).re := by
  rw [show Complex.I * s * ((a : ℂ) * c) = (a : ℂ) * (Complex.I * s * c) by ring, Complex.re_ofReal_mul]

theorem axialRot_continuous : Continuous (fun p : ℝ × Space => axialRot p.1 p.2) := by
  unfold axialRot
  fun_prop

theorem axialRot_comp_continuous {α : Type*} [TopologicalSpace α] {f : α → ℝ} {g : α → Space}
    (hf : Continuous f) (hg : Continuous g) : Continuous (fun a => axialRot (f a) (g a)) := by
  unfold axialRot
  fun_prop

theorem space_apply_continuous (i : Fin 3) : Continuous (fun y : Space => y i) := by
  fun_prop

theorem slice_differentiableAt {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (s : ℝ) (x : Space) :
    DifferentiableAt ℝ (ψ s) x :=
  ((hψ.1.differentiable (by simp)) (s, x)).comp x ((differentiableAt_const s).prodMk differentiableAt_id)

theorem gradField_eq {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (s : ℝ) (x : Space) :
    gradField ψ s x = (fderiv ℝ (fun z : ℝ × Space => ψ z.1 z.2) (s, x)).comp
      (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have hd : DifferentiableAt ℝ (fun z : ℝ × Space => ψ z.1 z.2) (s, x) :=
    (hψ.1.differentiable (by simp)).differentiableAt
  exact (hd.hasFDerivAt.comp x (hasFDerivAt_prodMk_right s x)).fderiv

theorem gradField_continuous {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Continuous (fun z : ℝ × Space => gradField ψ z.1 z.2) := by
  have h := (hψ.1.continuous_fderiv (by simp)).clm_comp
    (continuous_const (y := ContinuousLinearMap.inr ℝ ℝ Space))
  refine h.congr fun z => ?_
  exact (gradField_eq hψ z.1 z.2).symm

theorem gradField_add {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) (s : ℝ) (x : Space) :
    gradField (fun σ y => ψ₁ σ y + ψ₂ σ y) s x = gradField ψ₁ s x + gradField ψ₂ s x := by
  unfold gradField
  exact fderiv_add (slice_differentiableAt h₁ s x) (slice_differentiableAt h₂ s x)

theorem iter_integral_add (E F : ℝ → ℝ → ℂ) (hE : Continuous (fun p : ℝ × ℝ => E p.1 p.2))
    (hF : Continuous (fun p : ℝ × ℝ => F p.1 p.2)) (a b c d : ℝ) :
    (∫ τ in a..b, ∫ φ in c..d, (E τ φ + F τ φ))
      = (∫ τ in a..b, ∫ φ in c..d, E τ φ) + ∫ τ in a..b, ∫ φ in c..d, F τ φ := by
  have hin : ∀ τ, (∫ φ in c..d, (E τ φ + F τ φ)) = (∫ φ in c..d, E τ φ) + ∫ φ in c..d, F τ φ :=
    fun τ => intervalIntegral.integral_add
      ((hE.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
      ((hF.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _)
  simp_rw [hin]
  exact intervalIntegral.integral_add
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := E) hE c d).intervalIntegrable _ _)
    ((intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (f := F) hF c d).intervalIntegrable _ _)

theorem phase_continuous (ι : ℤ × ℤ) : Continuous (fun p : ℝ × ℝ =>
    Complex.exp (-(((2 * Real.pi * ι.1 * p.1 + ι.2 * p.2 : ℝ) : ℂ) * Complex.I))) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp
    ((continuous_const.mul continuous_fst).add (continuous_const.mul continuous_snd))).mul continuous_const).neg

theorem modeAverage_add {β : Type*} (ι : ℤ × ℤ) (f g : ℝ → ℝ → β → ℝ) (b : β)
    (hf : Continuous (fun p : ℝ × ℝ => f p.1 p.2 b)) (hg : Continuous (fun p : ℝ × ℝ => g p.1 p.2 b)) :
    modeAverage ι (fun τ φ b => f τ φ b + g τ φ b) b = modeAverage ι f b + modeAverage ι g b := by
  unfold modeAverage
  rw [← mul_add]
  congr 1
  have hsplit : ∀ (e : ℂ) (x y : ℝ), e * ((x + y : ℝ) : ℂ) = e * (x : ℂ) + e * (y : ℂ) := by
    intro e x y
    push_cast
    ring
  simp only [hsplit]
  exact iter_integral_add
    (fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((f τ φ b : ℝ) : ℂ))
    (fun τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I)) * ((g τ φ b : ℝ) : ℂ))
    ((phase_continuous ι).mul (Complex.continuous_ofReal.comp hf))
    ((phase_continuous ι).mul (Complex.continuous_ofReal.comp hg)) _ _ _ _

theorem vel_integrand_continuous {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (σ : ℝ) (y : Space)
    (i : Fin 3) : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (ψ (σ + p.1) (axialRot p.2 y)) i) := by
  have h1 : Continuous (fun p : ℝ × ℝ => axialRot p.2 y) :=
    axialRot_comp_continuous continuous_snd continuous_const
  have h1a : Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
    (continuous_const.add continuous_fst).prodMk h1
  have h2 : Continuous (fun p : ℝ × ℝ => ψ (σ + p.1) (axialRot p.2 y)) := hψ.1.continuous.comp h1a
  have h4 : Continuous (fun p : ℝ × ℝ => axialRot (-p.2) (ψ (σ + p.1) (axialRot p.2 y))) :=
    axialRot_comp_continuous continuous_snd.neg h2
  exact (space_apply_continuous i).comp h4

theorem grad_integrand_continuous {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) (σ : ℝ) (y : Space)
    (ij : Fin 3 × Fin 3) : Continuous (fun p : ℝ × ℝ =>
      axialRot (-p.2) (gradField ψ (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector ij.2))) ij.1) := by
  have h1 : Continuous (fun p : ℝ × ℝ => axialRot p.2 y) :=
    axialRot_comp_continuous continuous_snd continuous_const
  have h1' : Continuous (fun p : ℝ × ℝ => axialRot p.2 (unitVector ij.2)) :=
    axialRot_comp_continuous continuous_snd continuous_const
  have h1a : Continuous (fun p : ℝ × ℝ => ((σ + p.1, axialRot p.2 y) : ℝ × Space)) :=
    (continuous_const.add continuous_fst).prodMk h1
  have h2 : Continuous (fun p : ℝ × ℝ => gradField ψ (σ + p.1) (axialRot p.2 y)) :=
    (gradField_continuous hψ).comp h1a
  have h2' : Continuous (fun p : ℝ × ℝ =>
      gradField ψ (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector ij.2))) := h2.clm_apply h1'
  have h4 : Continuous (fun p : ℝ × ℝ =>
      axialRot (-p.2) (gradField ψ (σ + p.1) (axialRot p.2 y) (axialRot p.2 (unitVector ij.2)))) :=
    axialRot_comp_continuous continuous_snd.neg h2'
  exact (space_apply_continuous ij.1).comp h4

theorem modeVel_add {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeVel ι (fun σ y => ψ₁ σ y + ψ₂ σ y) σ y = fun i => modeVel ι ψ₁ σ y i + modeVel ι ψ₂ σ y i := by
  funext i
  unfold modeVel
  simp only [RotationInternal.axialRot_map_add, PiLp.add_apply]
  exact modeAverage_add ι _ _ i (vel_integrand_continuous h₁ σ y i) (vel_integrand_continuous h₂ σ y i)

theorem modeGrad_add {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeGrad ι (gradField (fun σ y => ψ₁ σ y + ψ₂ σ y)) σ y
      = fun ij => modeGrad ι (gradField ψ₁) σ y ij + modeGrad ι (gradField ψ₂) σ y ij := by
  funext ij
  unfold modeGrad
  simp only [gradField_add h₁ h₂, add_apply, RotationInternal.axialRot_map_add,
    PiLp.add_apply]
  exact modeAverage_add ι _ _ ij (grad_integrand_continuous h₁ σ y ij) (grad_integrand_continuous h₂ σ y ij)

theorem curlOfGrad_add (g₁ g₂ : Fin 3 × Fin 3 → ℂ) :
    curlOfGrad (fun ij => g₁ ij + g₂ ij) = fun i => curlOfGrad g₁ i + curlOfGrad g₂ i := by
  funext i
  simp only [curlOfGrad, mul_add, Finset.sum_add_distrib]

theorem cdot_add (x z₁ z₂ : Fin 3 → ℂ) : cdot x (fun i => z₁ i + z₂ i) = cdot x z₁ + cdot x z₂ := by
  simp only [cdot, map_add, mul_add, Finset.sum_add_distrib]

theorem re_add_aux (s a b : ℂ) : (Complex.I * s * (a + b)).re = (Complex.I * s * a).re + (Complex.I * s * b).re := by
  rw [mul_add, Complex.add_re]

theorem pieceIntegrand_add {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) {ψ₁ ψ₂ : ℝ → Space → Space} (h₁ : IsPeriodicTestField ψ₁)
    (h₂ : IsPeriodicTestField ψ₂) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pieceIntegrand m v G (fun σ y => ψ₁ σ y + ψ₂ σ y) ι σ y
      = pieceIntegrand m v G ψ₁ ι σ y + pieceIntegrand m v G ψ₂ ι σ y := by
  unfold pieceIntegrand
  rw [modeGrad_add h₁ h₂, modeVel_add h₁ h₂, curlOfGrad_add]
  simp only [cdot_add, re_add_aux, Finset.sum_add_distrib]
  ring

theorem exists_field_of_bounded (L : (ℝ → Space → Space) → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hadd : ∀ ψ₁ ψ₂, IsPeriodicTestField ψ₁ → IsPeriodicTestField ψ₂ → L (ψ₁ + ψ₂) = L ψ₁ + L ψ₂)
    (hsmul : ∀ (a : ℝ) ψ, IsPeriodicTestField ψ → L (a • ψ) = a * L ψ)
    (hbd : ∀ ψ, IsPeriodicTestField ψ → |L ψ| ≤ K * periodNorm ψ) :
    ∃ M : ℝ → Space → Space, AEStronglyMeasurable (fun z : ℝ × Space => M z.1 z.2) volume ∧
      IsTimePeriodic M ∧ periodLIntegral (fun σ y => ‖M σ y‖ ^ 2) < ⊤ ∧
      (∀ q, IsPeriodicTestPotential q →
        ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (gradientAt (q σ) y) = 0) ∧
      (∀ ψ, IsPeriodicTestField ψ → ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (M σ y) (ψ σ y) = L ψ) ∧
      periodNorm M ≤ K :=
  Breakdown.Coercive.Internal.Field.exists_field_of_bounded L hK hadd hsmul hbd

theorem energy_bounds {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {Γ : Set Symmetry} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (hwb : ∃ B, ∀ y, w y ≤ B)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal ≤ weightedEnergy w G H ∧
      w₀ * (periodLIntegral (fun σ y => matSq (G σ y))).toReal ≤ weightedEnergy w G H := by
  obtain ⟨B, hB⟩ := hwb
  have hmT : AEMeasurable (fun z : ℝ × Space => ‖secondDerivTrace (H z.1 z.2)‖ ^ 2) volume :=
    (continuous_secondDerivTrace_sq.comp_aestronglyMeasurable hv.measurable_secondDeriv).aemeasurable
  have hmF : AEMeasurable (fun z : ℝ × Space => matSq (G z.1 z.2)) volume :=
    (continuous_matSq.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable
  have hmw : AEMeasurable (fun z : ℝ × Space => w z.2) volume :=
    (hm.weight_measurable.comp measurable_snd).aemeasurable
  have hmWF : AEMeasurable (fun z : ℝ × Space => w z.2 * matSq (G z.1 z.2)) volume := hmw.mul hmF
  have hsum := periodLIntegral_add_le (f := fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)
    (g := fun σ y => w y * matSq (G σ y)) hmT.ennreal_ofReal hmWF.ennreal_ofReal
    (hmT.add hmWF).ennreal_ofReal
  have hw0 : ∀ y, 0 ≤ w y := fun y => hm.weight_pos.le.trans (hm.weight_lower y)
  have hWF : periodLIntegral (fun σ y => w y * matSq (G σ y))
      ≤ ENNReal.ofReal (max B 0) * periodLIntegral (fun σ y => matSq (G σ y)) := by
    rw [← periodLIntegral_const_mul (le_max_right B 0)]
    exact periodLIntegral_mono fun σ y =>
      mul_le_mul_of_nonneg_right ((hB y).trans (le_max_left B 0)) (matSq_nonneg _)
  have hfin : periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2 + w y * matSq (G σ y)) ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt hsum (ENNReal.add_lt_top.2 ⟨hv.sumSecondPartials_finite, ?_⟩))
    exact lt_of_le_of_lt hWF (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hv.gradient_finite)
  constructor
  · exact ENNReal.toReal_mono hfin (periodLIntegral_mono fun σ y =>
      le_add_of_nonneg_right (mul_nonneg (hw0 y) (matSq_nonneg _)))
  · have e : w₀ * (periodLIntegral (fun σ y => matSq (G σ y))).toReal
        = (periodLIntegral (fun σ y => w₀ * matSq (G σ y))).toReal := by
      rw [periodLIntegral_const_mul hm.weight_pos.le, ENNReal.toReal_mul,
        ENNReal.toReal_ofReal hm.weight_pos.le]
    rw [e]
    exact ENNReal.toReal_mono hfin (periodLIntegral_mono fun σ y =>
      le_add_of_nonneg_of_le (sq_nonneg _)
        (mul_le_mul_of_nonneg_right (hm.weight_lower y) (matSq_nonneg _)))

theorem secondDerivPairing_abs_le {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    |secondDerivPairing H ψ| ≤ Real.sqrt (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal
      * periodNorm ψ := by
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => -secondDerivTrace (H z.1 z.2)) volume :=
    (continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv).neg
  have hF2 : periodLIntegral (fun σ y => ‖-secondDerivTrace (H σ y)‖ ^ 2) < ⊤ := by
    simpa only [norm_neg] using hv.sumSecondPartials_finite
  have key := periodPairing_abs_le hF (testField_aesm hψ) hF2 (testField_sq_lt_top hψ)
  have hn : periodNorm (fun σ y => -secondDerivTrace (H σ y))
      = Real.sqrt (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal := by
    unfold periodNorm
    simp only [norm_neg]
  rw [hn] at key
  exact key

theorem secondDerivPairing_add {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ₁ ψ₂ : ℝ → Space → Space}
    (h₁ : IsPeriodicTestField ψ₁) (h₂ : IsPeriodicTestField ψ₂) :
    secondDerivPairing H (fun σ y => ψ₁ σ y + ψ₂ σ y) = secondDerivPairing H ψ₁ + secondDerivPairing H ψ₂ := by
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => -secondDerivTrace (H z.1 z.2)) volume :=
    (continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv).neg
  have hF2 : periodLIntegral (fun σ y => ‖-secondDerivTrace (H σ y)‖ ^ 2) < ⊤ := by
    simpa only [norm_neg] using hv.sumSecondPartials_finite
  have i1 := integrable_inner_prod hF (testField_aesm h₁) hF2 (testField_sq_lt_top h₁)
  have i2 := integrable_inner_prod hF (testField_aesm h₂) hF2 (testField_sq_lt_top h₂)
  unfold secondDerivPairing
  simp only [inner_add_right]
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ₁ σ y))
      = ∫ z, inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ₁ z.1 z.2)
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := (integral_prod _ i1).symm
  have e2 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, inner ℝ (-secondDerivTrace (H σ y)) (ψ₂ σ y))
      = ∫ z, inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ₂ z.1 z.2)
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := (integral_prod _ i2).symm
  have e12 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, (inner ℝ (-secondDerivTrace (H σ y)) (ψ₁ σ y)
        + inner ℝ (-secondDerivTrace (H σ y)) (ψ₂ σ y)))
      = ∫ z, (inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ₁ z.1 z.2)
          + inner ℝ (-secondDerivTrace (H z.1 z.2)) (ψ₂ z.1 z.2))
        ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := (integral_prod _ (i1.add i2)).symm
  rw [e12, e1, e2, integral_add i1 i2]

theorem secondDerivPairing_smul (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (a : ℝ)
    (ψ : ℝ → Space → Space) :
    secondDerivPairing H (fun σ y => a • ψ σ y) = a * secondDerivPairing H ψ := by
  unfold secondDerivPairing
  simp only [inner_smul_right, integral_const_mul]

theorem weightedFrequency_lt_top (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (hP0 : 0 < P) (wt : Space → ℝ)
    (hwt0 : ∀ y, 0 ≤ wt y) (hwtc : Continuous wt) (hwtB : ∃ B, ∀ y, wt y ≤ B ∧ ‖y‖ ^ 2 * wt y ≤ B) :
    ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * wt y * cnormSq (modeVel ι v σ y)) < ⊤ :=
  FrequencySeminorm.Internal.weightedFrequency_lt_top hP hD hR hv hP0 wt hwt0 hwtc hwtB

theorem frameFreq_abs_le {P a : ℝ} (hP0 : 0 < P) (ι : ℤ × ℤ) :
    |PieceWeights.frameFreq P a ι| ≤ (2 * Real.pi / P + |a|) * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) := by
  unfold PieceWeights.frameFreq
  have e : |2 * Real.pi * (ι.1 : ℝ) / P| = 2 * Real.pi / P * |(ι.1 : ℝ)| := by
    rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hP0]
    ring
  have h1 := abs_add_le (2 * Real.pi * (ι.1 : ℝ) / P) (a * (ι.2 : ℝ))
  rw [e, abs_mul] at h1
  have hp : 0 ≤ 2 * Real.pi / P := by positivity
  nlinarith [abs_nonneg (ι.1 : ℝ), abs_nonneg (ι.2 : ℝ), abs_nonneg a, mul_nonneg hp (abs_nonneg (ι.2 : ℝ)),
    mul_nonneg (abs_nonneg a) (abs_nonneg (ι.1 : ℝ))]

theorem sgn_abs_le (T : Set (ℤ × ℤ)) (ι : ℤ × ℤ) : |PieceWeights.sgn T ι| ≤ 1 := by
  unfold PieceWeights.sgn
  split_ifs <;> simp

theorem cnormSq_nonneg {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cdot_norm_le (x z : Fin 3 → ℂ) :
    ‖cdot x z‖ ≤ Real.sqrt (cnormSq x) * Real.sqrt (cnormSq z) := by
  unfold cdot cnormSq
  calc ‖∑ i, x i * (starRingEnd ℂ) (z i)‖ ≤ ∑ i, ‖x i‖ * ‖z i‖ := by
        refine (norm_sum_le _ _).trans (le_of_eq ?_)
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, Complex.norm_conj]
    _ ≤ _ := Real.sum_mul_le_sqrt_mul_sqrt _ _ _

theorem re_I_mul_le (c : ℝ) (X : ℂ) : |(Complex.I * (c : ℂ) * X).re| ≤ |c| * ‖X‖ := by
  refine (Complex.abs_re_le_norm _).trans (le_of_eq ?_)
  rw [norm_mul, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul]

theorem mu_part_abs_le {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) (y : Space) (X Y : Fin 3 → ℂ) :
    |∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y : ℝ) : ℂ)
        * cdot X Y).re|
      ≤ Real.sqrt (ratio * ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι|
          * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt y)
        * (Real.sqrt (cnormSq X) * Real.sqrt (cnormSq Y)) := by
  have hS0 : 0 ≤ ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * (m.muP β).wt y :=
    Finset.sum_nonneg fun β _ => mul_nonneg (abs_nonneg _) (hm.mu_wt_nonneg β y)
  have hS : ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * (m.muP β).wt y
      ≤ Real.sqrt (ratio * ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι|
          * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt y) :=
    Real.le_sqrt_of_sq_le (hm.mu_ratio y ι)
  calc |∑ β : Fin nM, (Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y : ℝ) : ℂ)
        * cdot X Y).re|
      ≤ ∑ β : Fin nM, |(Complex.I * ((PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y : ℝ) : ℂ)
        * cdot X Y).re| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y| * ‖cdot X Y‖ :=
        Finset.sum_le_sum fun β _ => re_I_mul_le _ _
    _ = (∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι| * (m.muP β).wt y) * ‖cdot X Y‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun β _ => ?_
        rw [abs_mul, abs_of_nonneg (hm.mu_wt_nonneg β y)]
    _ ≤ _ := mul_le_mul hS (cdot_norm_le X Y) (norm_nonneg _) (Real.sqrt_nonneg _)

theorem eps_part_eq {nE : ℕ} (c : Fin nE → ℝ) (X : ℂ) :
    ∑ β : Fin nE, (Complex.I * ((c β : ℝ) : ℂ) * X).re = (Complex.I * ((∑ β : Fin nE, c β : ℝ) : ℂ) * X).re := by
  rw [Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul, Complex.re_sum]

theorem epsCoef_abs_le {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) (y : Space) :
    |∑ β : Fin nE, PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y| ≤ epsSup := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans (le_trans ?_ (hm.eps_sum_le y))
  refine Finset.sum_le_sum fun β _ => ?_
  rw [abs_mul, abs_of_nonneg (hm.eps_wt_nonneg β y)]
  exact mul_le_of_le_one_left (hm.eps_wt_nonneg β y) (sgn_abs_le _ _)

theorem epsCoef_fderiv_le {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) (y : Space)
    (hd : ∀ β, DifferentiableAt ℝ (m.epsP β).wt y) :
    ‖fderiv ℝ (fun x => ∑ β : Fin nE, PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt x) y‖
      ≤ epsGradSup := by
  rw [fderiv_fun_sum (fun β _ => (hd β).const_mul _)]
  refine (norm_sum_le _ _).trans (le_trans ?_ (hm.eps_grad_sum_le y))
  refine Finset.sum_le_sum fun β _ => ?_
  rw [fderiv_const_mul (hd β), norm_smul, Real.norm_eq_abs]
  exact mul_le_of_le_one_left (norm_nonneg _) (sgn_abs_le _ _)

theorem seminormSq_lt_top (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds) (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    m.seminormSq P v < ⊤ := by
  have hP0 := hm.period_pos
  unfold PieceWeights.seminormSq
  refine ENNReal.sum_lt_top.2 fun β _ => ?_
  obtain ⟨K, hK⟩ := hm.mu_increment β
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hC : 0 ≤ 2 * Real.pi / P + |(m.muP β).frame| := by positivity
  have hgen := weightedFrequency_lt_top hP hD hR hv hP0 (m.muP β).wt (hm.mu_wt_nonneg β) hK.continuous
    ⟨B, fun y => ⟨(hB β y).1, (hB β y).2.1⟩⟩
  have hpt : ∀ (ι : ℤ × ℤ) (σ : ℝ) (y : Space),
      ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
        * (m.muP β).wt y * cnormSq (modeVel ι v σ y))
      ≤ ENNReal.ofReal (2 * Real.pi / P + |(m.muP β).frame|)
        * ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by
    intro ι σ y
    rw [← ENNReal.ofReal_mul hC]
    apply ENNReal.ofReal_le_ofReal
    have hs := sgn_abs_le (m.muP β).modes ι
    have hf := frameFreq_abs_le (a := (m.muP β).frame) hP0 ι
    have hw := hm.mu_wt_nonneg β y
    have hc := cnormSq_nonneg (modeVel ι v σ y)
    have hwc : 0 ≤ (m.muP β).wt y * cnormSq (modeVel ι v σ y) := mul_nonneg hw hc
    have hsf : |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
        ≤ (2 * Real.pi / P + |(m.muP β).frame|) * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) := by
      calc _ ≤ 1 * |PieceWeights.frameFreq P (m.muP β).frame ι| :=
            mul_le_mul_of_nonneg_right hs (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hf
    calc |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
          * (m.muP β).wt y * cnormSq (modeVel ι v σ y)
        = (|PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|)
          * ((m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by ring
      _ ≤ ((2 * Real.pi / P + |(m.muP β).frame|) * (|(ι.1 : ℝ)| + |(ι.2 : ℝ)|))
          * ((m.muP β).wt y * cnormSq (modeVel ι v σ y)) := mul_le_mul_of_nonneg_right hsf hwc
      _ = _ := by ring
  calc (∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
          * (m.muP β).wt y * cnormSq (modeVel ι v σ y)))
      ≤ ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal (2 * Real.pi / P + |(m.muP β).frame|)
            * ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) :=
        ENNReal.tsum_le_tsum fun ι => lintegral_mono fun σ => lintegral_mono fun y => hpt ι σ y
    _ = ENNReal.ofReal (2 * Real.pi / P + |(m.muP β).frame|) * ∑' ι : ℤ × ℤ, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ENNReal.ofReal ((|(ι.1 : ℝ)| + |(ι.2 : ℝ)|) * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by
        simp_rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        rw [ENNReal.tsum_mul_left]
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgen


abbrev slabMeasure : Measure (ℝ × Space) := (volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume

def curlTerm (c : ℤ × ℤ → Space → ℝ) (G : ℝ → Space → (Space →L[ℝ] Space)) (ψ : ℝ → Space → Space)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * ((c ι y : ℝ) : ℂ) * cdot (curlOfGrad (modeGrad ι G σ y)) (curlOfGrad (modeGrad ι (gradField ψ) σ y))).re

def velTerm (c : ℤ × ℤ → Space → ℝ) (v : ℝ → Space → Space) (ψ : ℝ → Space → Space)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : ℝ :=
  (Complex.I * ((c ι y : ℝ) : ℂ) * cdot (modeVel ι v σ y) (modeVel ι ψ σ y)).re

theorem curlTerm_aesm {c : ℤ × ℤ → Space → ℝ} (hc : ∀ ι, Continuous (c ι))
    {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2) volume) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => curlTerm c G ψ ι z.1 z.2) slabMeasure := by
  have he := hc ι
  have hΦ : Continuous (fun q : Space × (Fin 3 × Fin 3 → ℂ) × (Fin 3 × Fin 3 → ℂ) =>
      (Complex.I * ((c ι q.1 : ℝ) : ℂ) * cdot (curlOfGrad q.2.1) (curlOfGrad q.2.2)).re) := by
    unfold cdot curlOfGrad
    fun_prop
  have hq : AEMeasurable (fun z : ℝ × Space =>
      (z.2, modeGrad ι G z.1 z.2, modeGrad ι (gradField ψ) z.1 z.2)) slabMeasure :=
    measurable_snd.aemeasurable.prodMk ((Internal.FieldModes.aemeasurable_modeGrad hG ι).prodMk
      (Internal.FieldModes.aemeasurable_modeGrad (gradField_continuous hψ).aestronglyMeasurable ι))
  exact (hΦ.measurable.comp_aemeasurable hq).aestronglyMeasurable

theorem velTerm_aesm {c : ℤ × ℤ → Space → ℝ} (hc : ∀ ι, Continuous (c ι))
    {U : ℝ → Space → Space}
    (hU : AEStronglyMeasurable (fun z : ℝ × Space => U z.1 z.2) volume) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun z : ℝ × Space => velTerm c U ψ ι z.1 z.2) slabMeasure := by
  have he := hc ι
  have hΦ : Continuous (fun q : Space × (Fin 3 → ℂ) × (Fin 3 → ℂ) =>
      (Complex.I * ((c ι q.1 : ℝ) : ℂ) * cdot q.2.1 q.2.2).re) := by
    unfold cdot
    fun_prop
  have hq : AEMeasurable (fun z : ℝ × Space =>
      (z.2, modeVel ι U z.1 z.2, modeVel ι ψ z.1 z.2)) slabMeasure :=
    measurable_snd.aemeasurable.prodMk ((Internal.FieldModes.aemeasurable_modeVel hU ι).prodMk
      (Internal.FieldModes.aemeasurable_modeVel hψ.1.continuous.aestronglyMeasurable ι))
  exact (hΦ.measurable.comp_aemeasurable hq).aestronglyMeasurable

theorem gradField_matSq_lt_top {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    periodLIntegral (fun σ y => matSq (gradField ψ σ y)) < ⊤ := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  have hc : Continuous (fun z : ℝ × Space => matSq (gradField ψ z.1 z.2)) :=
    continuous_matSq.comp (gradField_continuous hψ)
  refine Internal.FieldModes.periodLIntegral_lt_top_of_support hc (R := R) (fun σ y hy => ?_)
  rw [Internal.FieldModes.gradField_eq_zero sR σ y hy]
  simp [matSq]

theorem curlTerm_integrable (hPars : ModeSquareSumHolds) {c : ℤ × ℤ → Space → ℝ}
    (hc : ∀ ι, Continuous (c ι)) {B : ℝ} (hB : ∀ ι y, |c ι y| ≤ B)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => curlTerm c G ψ ι z.1 z.2) slabMeasure := by
  have hA := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hv.measurable_gradient
    hv.periodic_gradient hv.gradient_finite ι
  have hB' := Internal.FieldModes.integrable_cnormSq_modeGrad hPars
    (gradField_continuous hψ).aestronglyMeasurable
    (Internal.FieldModes.gradField_periodic hψ.2.1) (gradField_matSq_lt_top hψ) ι
  refine Integrable.mono' ((hA.add hB').const_mul B) (curlTerm_aesm hc hv.measurable_gradient hψ ι)
    (ae_of_all _ fun z => ?_)
  rw [Real.norm_eq_abs]
  refine (Internal.FieldModes.abs_curlTerm_le _ _ _).trans ?_
  exact mul_le_mul_of_nonneg_right (hB _ _)
    (add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _))

theorem curlTerm_summable (hPars : ModeSquareSumHolds) {c : ℤ × ℤ → Space → ℝ}
    {B : ℝ} (hB : ∀ ι y, |c ι y| ≤ B)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Summable (fun ι : ℤ × ℤ => ∫ z, curlTerm c G ψ ι z.1 z.2 ∂slabMeasure) := by
  have hψg : AEStronglyMeasurable (fun z : ℝ × Space => gradField ψ z.1 z.2) volume :=
    (gradField_continuous hψ).aestronglyMeasurable
  have hψgp := Internal.FieldModes.gradField_periodic hψ.2.1
  have hψg2 := gradField_matSq_lt_top hψ
  refine Summable.of_norm_bounded ((
    (Internal.FieldModes.summable_integral_cnormSq_modeGrad hPars hv.measurable_gradient
      hv.periodic_gradient hv.gradient_finite).add
    (Internal.FieldModes.summable_integral_cnormSq_modeGrad hPars hψg hψgp hψg2)).mul_left B) (fun ι => ?_)
  have hA := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hv.measurable_gradient
    hv.periodic_gradient hv.gradient_finite ι
  have hA' := Internal.FieldModes.integrable_cnormSq_modeGrad hPars hψg hψgp hψg2 ι
  refine (norm_integral_le_of_norm_le ((hA.add hA').const_mul B) (ae_of_all _ fun z => ?_)).trans
    (le_of_eq ?_)
  · rw [Real.norm_eq_abs]
    refine (Internal.FieldModes.abs_curlTerm_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hB _ _)
      (add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _))
  · rw [integral_const_mul]
    congr 1
    exact integral_add hA hA'

theorem velTerm_ballPart (c : ℤ × ℤ → Space → ℝ) (v : ℝ → Space → Space) {ψ : ℝ → Space → Space}
    {R : ℝ} (hs : ∀ σ y, R < ‖y‖ → ψ σ y = 0) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    velTerm c v ψ ι σ y = velTerm c (Internal.FieldModes.ballPart R v) ψ ι σ y := by
  unfold velTerm
  by_cases hy : ‖y‖ ≤ R
  · rw [Internal.FieldModes.modeVel_ballPart v ι σ hy]
  · rw [Internal.FieldModes.modeVel_eq_zero hs ι σ (lt_of_not_ge hy)]
    simp [cdot]

theorem velTerm_integrable (hPars : ModeSquareSumHolds) {c : ℤ × ℤ → Space → ℝ}
    (hc : ∀ ι, Continuous (c ι)) {B : ℝ} (hB : ∀ ι y, |c ι y| ≤ B)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ)
    (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => velTerm c v ψ ι z.1 z.2) slabMeasure := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  have hU := Internal.FieldModes.isSquareField_ballPart perturbationLocalSquareIntegrabilityHolds_proof hv R
  have hX := Internal.FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  have hA := Internal.FieldModes.integrable_cnormSq_modeVel hPars hU ι
  have hA' := Internal.FieldModes.integrable_cnormSq_modeVel hPars hX ι
  have hI : Integrable (fun z : ℝ × Space => velTerm c (Internal.FieldModes.ballPart R v) ψ ι z.1 z.2)
      slabMeasure := by
    refine Integrable.mono' (((hA.add hA').div_const 2).const_mul B)
      (velTerm_aesm hc hU.1 hψ ι) (ae_of_all _ fun z => ?_)
    rw [Real.norm_eq_abs]
    refine (Internal.FieldModes.abs_velTerm_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hB _ _)
      (div_nonneg (add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _))
        zero_le_two)
  refine hI.congr (ae_of_all _ fun z => ?_)
  exact (velTerm_ballPart c v sR ι z.1 z.2).symm

theorem velTerm_summable (hPars : ModeSquareSumHolds) {c : ℤ × ℤ → Space → ℝ}
    {B : ℝ} (hB : ∀ ι y, |c ι y| ≤ B)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space} (hψ : IsPeriodicTestField ψ) :
    Summable (fun ι : ℤ × ℤ => ∫ z, velTerm c v ψ ι z.1 z.2 ∂slabMeasure) := by
  obtain ⟨R, sR⟩ := hψ.2.2.1
  have hU := Internal.FieldModes.isSquareField_ballPart perturbationLocalSquareIntegrabilityHolds_proof hv R
  have hX := Internal.FieldModes.isSquareField_of_continuous hψ.1.continuous hψ.2.1 sR
  refine Summable.of_norm_bounded ((
    ((Internal.FieldModes.summable_integral_cnormSq_modeVel hPars hU).add
      (Internal.FieldModes.summable_integral_cnormSq_modeVel hPars hX)).div_const 2).mul_left B) (fun ι => ?_)
  have hA := Internal.FieldModes.integrable_cnormSq_modeVel hPars hU ι
  have hA' := Internal.FieldModes.integrable_cnormSq_modeVel hPars hX ι
  refine (norm_integral_le_of_norm_le (((hA.add hA').div_const 2).const_mul B)
    (ae_of_all _ fun z => ?_)).trans (le_of_eq ?_)
  · rw [Real.norm_eq_abs, velTerm_ballPart c v sR ι z.1 z.2]
    refine (Internal.FieldModes.abs_velTerm_le _ _ _).trans ?_
    exact mul_le_mul_of_nonneg_right (hB _ _)
      (div_nonneg (add_nonneg (Internal.FieldModes.cnormSq_nonneg _) (Internal.FieldModes.cnormSq_nonneg _))
        zero_le_two)
  · rw [integral_const_mul, integral_div]
    congr 2
    exact integral_add hA hA'

def epsCoefOf {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (β : Fin nE) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y

def muCoefOf {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (β : Fin nM) (ι : ℤ × ℤ) (y : Space) : ℝ :=
  PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y

theorem pieceIntegrand_eq {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ψ : ℝ → Space → Space) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pieceIntegrand m v G ψ ι σ y = (∑ β : Fin nE, curlTerm (epsCoefOf m β) G ψ ι σ y)
      + ∑ β : Fin nM, velTerm (muCoefOf m β) v ψ ι σ y := rfl

theorem epsCoefOf_continuous {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nE) (ι : ℤ × ℤ) :
    Continuous (epsCoefOf m β ι) := by
  obtain ⟨K, hK⟩ := hm.eps_increment β
  exact continuous_const.mul hK.continuous

theorem muCoefOf_continuous {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nM) (ι : ℤ × ℤ) :
    Continuous (muCoefOf m β ι) := by
  obtain ⟨K, hK⟩ := hm.mu_increment β
  exact continuous_const.mul hK.continuous

theorem epsCoefOf_abs_le {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) (β : Fin nE) (ι : ℤ × ℤ) (y : Space) :
    |epsCoefOf m β ι y| ≤ epsSup := by
  unfold epsCoefOf
  rw [abs_mul, abs_of_nonneg (hm.eps_wt_nonneg β y)]
  refine (mul_le_of_le_one_left (hm.eps_wt_nonneg β y) (sgn_abs_le _ _)).trans ?_
  refine le_trans ?_ (hm.eps_sum_le y)
  exact Finset.single_le_sum (f := fun β => (m.epsP β).wt y) (fun β _ => hm.eps_wt_nonneg β y)
    (Finset.mem_univ β)

theorem muCoefOf_abs_le {C : Type} {nE nM : ℕ} {m : PieceWeights C nE nM} {P : ℝ} {h : HarmonicBounds}
    {w : Space → ℝ} {W : ℝ → Space → Space} {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {B : ℝ}
    (hB : ∀ β y, (m.muP β).wt y ≤ B) (β : Fin nM) (ι : ℤ × ℤ) (y : Space) :
    |muCoefOf m β ι y| ≤ B := by
  unfold muCoefOf
  rw [abs_mul, abs_of_nonneg (hm.mu_wt_nonneg β y)]
  exact (mul_le_of_le_one_left (hm.mu_wt_nonneg β y) (sgn_abs_le _ _)).trans (hB β y)

theorem pieceIntegrand_integrable_slab (hP : ModeSquareSumHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    (∀ β : Fin nE, Integrable (fun z : ℝ × Space => curlTerm (epsCoefOf m β) G ψ ι z.1 z.2) slabMeasure) ∧
      ∀ β : Fin nM, Integrable (fun z : ℝ × Space => velTerm (muCoefOf m β) v ψ ι z.1 z.2) slabMeasure := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  exact ⟨fun β => curlTerm_integrable hP (epsCoefOf_continuous hm β) (epsCoefOf_abs_le hm β) hv hψ ι,
    fun β => velTerm_integrable hP (muCoefOf_continuous hm β)
      (muCoefOf_abs_le hm (fun β y => (hB β y).1) β) hv hψ ι⟩

theorem pieceIntegrand_integrable (hP : ModeSquareSumHolds) (_hD : ModeDerivativeHolds)
    (_hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    Integrable (fun z : ℝ × Space => pieceIntegrand m v G ψ ι z.1 z.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  obtain ⟨hE, hM⟩ := pieceIntegrand_integrable_slab hP m P h w Γ W hm hv hψ ι
  simp only [pieceIntegrand_eq]
  exact (integrable_finsetSum _ fun β _ => hE β).add (integrable_finsetSum _ fun β _ => hM β)

theorem pieceIntegral_summable (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    Summable (fun ι : ℤ × ℤ => ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ ι σ y) := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hSE : ∀ β : Fin nE, Summable (fun ι : ℤ × ℤ => ∫ z, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2 ∂slabMeasure) :=
    fun β => curlTerm_summable hP (epsCoefOf_abs_le hm β) hv hψ
  have hSM : ∀ β : Fin nM, Summable (fun ι : ℤ × ℤ => ∫ z, velTerm (muCoefOf m β) v ψ ι z.1 z.2 ∂slabMeasure) :=
    fun β => velTerm_summable hP (muCoefOf_abs_le hm (fun β y => (hB β y).1) β) hv hψ
  refine ((summable_sum (s := Finset.univ) fun β _ => hSE β).add
    (summable_sum (s := Finset.univ) fun β _ => hSM β)).congr (fun ι => ?_)
  obtain ⟨hE, hM⟩ := pieceIntegrand_integrable_slab hP m P h w Γ W hm hv hψ ι
  have hI := pieceIntegrand_integrable hP hD hR m P h w Γ W hm hv hψ ι
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ ι σ y)
      = ∫ z, pieceIntegrand m v G ψ ι z.1 z.2 ∂slabMeasure := (integral_prod _ hI).symm
  rw [e1]
  simp only [pieceIntegrand_eq]
  rw [integral_add (integrable_finsetSum _ fun β _ => hE β) (integrable_finsetSum _ fun β _ => hM β),
    integral_finsetSum _ fun β _ => hE β, integral_finsetSum _ fun β _ => hM β]

def epsModeSum {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (G : ℝ → Space → (Space →L[ℝ] Space))
    (ψ : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ z, (∑ β : Fin nE, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2) ∂slabMeasure

def muModeSum {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (ψ : ℝ → Space → Space) : ℝ :=
  ∑' ι : ℤ × ℤ, ∫ z, (∑ β : Fin nM, velTerm (muCoefOf m β) v ψ ι z.1 z.2) ∂slabMeasure

theorem pieceModeSum_split (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    pieceModeSum m v G ψ = epsModeSum m G ψ + muModeSum m v ψ := by
  obtain ⟨B, hB⟩ := hm.mu_decay
  have hSE : ∀ β : Fin nE, Summable (fun ι : ℤ × ℤ => ∫ z, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2 ∂slabMeasure) :=
    fun β => curlTerm_summable hP (epsCoefOf_abs_le hm β) hv hψ
  have hSM : ∀ β : Fin nM, Summable (fun ι : ℤ × ℤ => ∫ z, velTerm (muCoefOf m β) v ψ ι z.1 z.2 ∂slabMeasure) :=
    fun β => velTerm_summable hP (muCoefOf_abs_le hm (fun β y => (hB β y).1) β) hv hψ
  have sE : Summable (fun ι : ℤ × ℤ =>
      ∫ z, (∑ β : Fin nE, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2) ∂slabMeasure) :=
    (summable_sum (s := Finset.univ) fun β _ => hSE β).congr fun ι =>
      (integral_finsetSum _ fun β _ => (pieceIntegrand_integrable_slab hP m P h w Γ W hm hv hψ ι).1 β).symm
  have sM : Summable (fun ι : ℤ × ℤ =>
      ∫ z, (∑ β : Fin nM, velTerm (muCoefOf m β) v ψ ι z.1 z.2) ∂slabMeasure) :=
    (summable_sum (s := Finset.univ) fun β _ => hSM β).congr fun ι =>
      (integral_finsetSum _ fun β _ => (pieceIntegrand_integrable_slab hP m P h w Γ W hm hv hψ ι).2 β).symm
  unfold epsModeSum muModeSum
  rw [← sE.tsum_add sM]
  unfold pieceModeSum
  refine tsum_congr fun ι => ?_
  obtain ⟨hE, hM⟩ := pieceIntegrand_integrable_slab hP m P h w Γ W hm hv hψ ι
  have hI := pieceIntegrand_integrable hP hD hR m P h w Γ W hm hv hψ ι
  have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ ι σ y)
      = ∫ z, pieceIntegrand m v G ψ ι z.1 z.2 ∂slabMeasure := (integral_prod _ hI).symm
  rw [e1]
  simp only [pieceIntegrand_eq]
  exact integral_add (integrable_finsetSum _ fun β _ => hE β) (integrable_finsetSum _ fun β _ => hM β)

theorem epsMode_abs_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) (ι : ℤ × ℤ) :
    ENNReal.ofReal |∫ z, (∑ β : Fin nE, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2) ∂slabMeasure| ≤
      ∫⁻ z, ENNReal.ofReal ((epsSup * Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
        + epsGradSup * Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))))
        * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) ∂slabMeasure := by
  have e : (∫ z, (∑ β : Fin nE, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2) ∂slabMeasure) =
      ∫ z, (Complex.I * ((∑ β : Fin nE, PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt z.2 : ℝ) : ℂ)
        * cdot (curlOfGrad (modeGrad ι G z.1 z.2)) (curlOfGrad (modeGrad ι (gradField ψ) z.1 z.2))).re
        ∂slabMeasure :=
    integral_congr_ae (ae_of_all _ fun z => eps_part_eq (fun β => epsCoefOf m β ι z.2) _)
  rw [e]
  exact CurlWeight.Internal.curlWeightPairing_abs_le hP hD hR hv hψ ι
    (fun β => PieceWeights.sgn (m.epsP β).modes ι) (fun β => (m.epsP β).wt) hm.eps_increment
    (epsCoef_abs_le hm ι) (fun y hd => epsCoef_fderiv_le hm ι y hd)

theorem curlMode_squareSum_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∑' ι : ℤ × ℤ, ∫⁻ z, ENNReal.ofReal (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) ∂slabMeasure ≤
      periodLIntegral (fun σ y => matSq (G σ y)) := by
  have hcurl : Continuous (fun q : Fin 3 × Fin 3 → ℂ => curlOfGrad q) :=
    continuous_pi fun i => by unfold curlOfGrad; fun_prop
  have hm : ∀ ι, AEMeasurable (fun z : ℝ × Space => cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) slabMeasure :=
    fun ι => (Internal.FieldModes.continuous_cnormSq.comp hcurl).measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι)
  have hmG : ∀ ι, AEMeasurable (fun z : ℝ × Space => cnormSq (modeGrad ι G z.1 z.2)) slabMeasure :=
    fun ι => Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι)
  have hint : ∀ ι, Integrable (fun z : ℝ × Space => cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) slabMeasure :=
    fun ι => ((Internal.FieldModes.integrable_cnormSq_modeGrad hP hv.measurable_gradient hv.periodic_gradient
      hv.gradient_finite ι).const_mul 2).mono' (hm ι).aestronglyMeasurable (ae_of_all _ fun z => by
        rw [Real.norm_eq_abs, abs_of_nonneg (Internal.FieldModes.cnormSq_nonneg _)]
        exact Internal.FieldModes.cnormSq_curlOfGrad_le _)
  have e : ∀ ι, ∫⁻ z, ENNReal.ofReal (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) ∂slabMeasure =
      ENNReal.ofReal (∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂slabMeasure) := fun ι =>
    (ofReal_integral_eq_lintegral_ofReal (hint ι) (ae_of_all _ fun z => Internal.FieldModes.cnormSq_nonneg _)).symm
  have hle : ∀ ι, ∫⁻ z, ENNReal.ofReal (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) ∂slabMeasure ≤
      ENNReal.ofReal 2 * ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (cnormSq (modeGrad ι G σ y)) := by
    intro ι
    rw [← lintegral_prod _ (hmG ι).ennreal_ofReal, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono fun z => ?_
    rw [← ENNReal.ofReal_mul zero_le_two]
    exact ENNReal.ofReal_le_ofReal (Internal.FieldModes.cnormSq_curlOfGrad_le _)
  have hfinE : ∑' ι, ∫⁻ z, ENNReal.ofReal (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) ∂slabMeasure ≠ ⊤ := by
    refine ne_top_of_le_ne_top (ENNReal.mul_ne_top (ENNReal.ofReal_ne_top (r := 2)) hv.gradient_finite.ne) ?_
    rw [hP.2.1 G hv.measurable_gradient hv.periodic_gradient hv.gradient_finite, ← ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum hle
  have hnn : ∀ ι, 0 ≤ ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂slabMeasure := fun ι =>
    integral_nonneg fun z => Internal.FieldModes.cnormSq_nonneg _
  have hsum : Summable (fun ι : ℤ × ℤ => ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂slabMeasure) := by
    refine (ENNReal.summable_toReal hfinE).congr fun ι => ?_
    rw [e ι, ENNReal.toReal_ofReal (hnn ι)]
  have key := Breakdown.Coercive.Internal.Field.curlMode_tsum_le hP hD hR hv
  rw [tsum_congr e, ← ENNReal.ofReal_tsum_of_nonneg hnn hsum]
  calc ENNReal.ofReal (∑' ι, ∫ z, cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)) ∂slabMeasure)
      ≤ ENNReal.ofReal (Breakdown.Coercive.Internal.Field.fieldGradNorm G ^ 2) := ENNReal.ofReal_le_ofReal key
    _ = periodLIntegral (fun σ y => matSq (G σ y)) := by
        unfold Breakdown.Coercive.Internal.Field.fieldGradNorm
        rw [Real.sq_sqrt ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hv.gradient_finite.ne]

theorem mul_le_half_sq {x y t : ℝ} (ht : 0 < t) : x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  have h1 : 0 ≤ (t * x - y) ^ 2 / t := div_nonneg (sq_nonneg _) ht.le
  have e : (t * x - y) ^ 2 / t = t * x ^ 2 - 2 * (x * y) + y ^ 2 / t := by
    field_simp
    ring
  linarith

theorem le_sqrt_mul_of_forall {s X Y : ℝ} (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hs : ∀ t : ℝ, 0 < t → s ≤ (t * X + Y / t) / 2) : s ≤ Real.sqrt X * Real.sqrt Y := by
  by_contra hlt
  rw [not_le] at hlt
  have ha : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
  have hb : 0 ≤ Real.sqrt Y := Real.sqrt_nonneg Y
  have hXa : X = Real.sqrt X ^ 2 := (Real.sq_sqrt hX).symm
  have hYb : Y = Real.sqrt Y ^ 2 := (Real.sq_sqrt hY).symm
  set a := Real.sqrt X
  set b := Real.sqrt Y
  have hd : 0 < s - a * b := by linarith
  have hab1 : 0 < a + b + 1 := by linarith
  set ε := (s - a * b) / (a + b + 1) with hε_def
  have hε : 0 < ε := div_pos hd hab1
  have hεab : ε * (a + b) < s - a * b := by
    rw [hε_def, div_mul_eq_mul_div, div_lt_iff₀ hab1]
    nlinarith
  have hae : 0 < a + ε := by linarith
  have hbe : 0 < b + ε := by linarith
  have ht : 0 < (b + ε) / (a + ε) := div_pos hbe hae
  have h1 : (b + ε) / (a + ε) * X ≤ (b + ε) * a := by
    rw [hXa, div_mul_eq_mul_div, div_le_iff₀ hae]
    nlinarith [mul_nonneg (mul_nonneg hbe.le ha) hε.le]
  have h2 : Y / ((b + ε) / (a + ε)) ≤ b * (a + ε) := by
    rw [hYb, div_div_eq_mul_div, div_le_iff₀ hbe]
    nlinarith [mul_nonneg (mul_nonneg hae.le hb) hε.le]
  have h3 := hs _ ht
  nlinarith

theorem tsum_lintegral_mul_le {f g : ℤ × ℤ → ℝ × Space → ℝ}
    (hfm : ∀ ι, AEMeasurable (f ι) slabMeasure)
    (hF : ∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z ^ 2) ∂slabMeasure ≠ ⊤)
    (hG : ∑' ι, ∫⁻ z, ENNReal.ofReal (g ι z ^ 2) ∂slabMeasure ≠ ⊤) :
    ∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z * g ι z) ∂slabMeasure ≠ ⊤ ∧
    (∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z * g ι z) ∂slabMeasure).toReal ≤
      Real.sqrt (∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z ^ 2) ∂slabMeasure).toReal
        * Real.sqrt (∑' ι, ∫⁻ z, ENNReal.ofReal (g ι z ^ 2) ∂slabMeasure).toReal := by
  have bound : ∀ t : ℝ, 0 < t → ∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z * g ι z) ∂slabMeasure ≤
      ENNReal.ofReal (t / 2) * ∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z ^ 2) ∂slabMeasure
        + ENNReal.ofReal (1 / (2 * t)) * ∑' ι, ∫⁻ z, ENNReal.ofReal (g ι z ^ 2) ∂slabMeasure := by
    intro t ht
    have ha0 : 0 ≤ t / 2 := by positivity
    have hb0 : 0 ≤ 1 / (2 * t) := by positivity
    have hQ : ∀ ι, ∫⁻ z, ENNReal.ofReal (f ι z * g ι z) ∂slabMeasure ≤
        ENNReal.ofReal (t / 2) * ∫⁻ z, ENNReal.ofReal (f ι z ^ 2) ∂slabMeasure
          + ENNReal.ofReal (1 / (2 * t)) * ∫⁻ z, ENNReal.ofReal (g ι z ^ 2) ∂slabMeasure := by
      intro ι
      have hmeas : AEMeasurable (fun z => ENNReal.ofReal (t / 2) * ENNReal.ofReal (f ι z ^ 2)) slabMeasure :=
        ((hfm ι).pow_const 2).ennreal_ofReal.const_mul _
      calc ∫⁻ z, ENNReal.ofReal (f ι z * g ι z) ∂slabMeasure
          ≤ ∫⁻ z, (ENNReal.ofReal (t / 2) * ENNReal.ofReal (f ι z ^ 2)
              + ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal (g ι z ^ 2)) ∂slabMeasure := by
            refine lintegral_mono fun z => ?_
            rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
              ← ENNReal.ofReal_add (mul_nonneg ha0 (sq_nonneg _)) (mul_nonneg hb0 (sq_nonneg _))]
            apply ENNReal.ofReal_le_ofReal
            have hm2 := mul_le_half_sq (x := f ι z) (y := g ι z) ht
            calc f ι z * g ι z ≤ _ := hm2
              _ = _ := by ring
        _ = _ := by
            rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    calc _ ≤ ∑' ι, (ENNReal.ofReal (t / 2) * ∫⁻ z, ENNReal.ofReal (f ι z ^ 2) ∂slabMeasure
          + ENNReal.ofReal (1 / (2 * t)) * ∫⁻ z, ENNReal.ofReal (g ι z ^ 2) ∂slabMeasure) := ENNReal.tsum_le_tsum hQ
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hne : ∀ t : ℝ, ENNReal.ofReal (t / 2) * ∑' ι, ∫⁻ z, ENNReal.ofReal (f ι z ^ 2) ∂slabMeasure
      + ENNReal.ofReal (1 / (2 * t)) * ∑' ι, ∫⁻ z, ENNReal.ofReal (g ι z ^ 2) ∂slabMeasure ≠ ⊤ := fun t =>
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF, ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG⟩
  refine ⟨ne_top_of_le_ne_top (hne 1) (bound 1 one_pos),
    le_sqrt_mul_of_forall ENNReal.toReal_nonneg ENNReal.toReal_nonneg fun t ht => ?_⟩
  have ha0 : 0 ≤ t / 2 := by positivity
  have hb0 : 0 ≤ 1 / (2 * t) := by positivity
  refine (ENNReal.toReal_mono (hne t) (bound t ht)).trans (le_of_eq ?_)
  rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hF) (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hG),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hb0]
  ring

theorem epsModeSum_abs_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    |epsModeSum m G ψ| ≤ (epsSup * Real.sqrt (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal
      + epsGradSup * Real.sqrt (periodLIntegral (fun σ y => matSq (G σ y))).toReal) * periodNorm ψ := by
  have he : 0 ≤ epsSup := le_trans (Finset.sum_nonneg fun β _ => hm.eps_wt_nonneg β 0) (hm.eps_sum_le 0)
  have hg : 0 ≤ epsGradSup := le_trans (Finset.sum_nonneg fun β _ => norm_nonneg _) (hm.eps_grad_sum_le 0)
  have hY := testField_sq_lt_top hψ
  have hTr : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
    continuous_secondDerivTrace.comp_aestronglyMeasurable hv.measurable_secondDeriv
  have hcurl : Continuous (fun q : Fin 3 × Fin 3 → ℂ => curlOfGrad q) :=
    continuous_pi fun i => by unfold curlOfGrad; fun_prop
  let fT : ℤ × ℤ → ℝ × Space → ℝ := fun ι z =>
    Real.sqrt (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2))
  let fO : ℤ × ℤ → ℝ × Space → ℝ := fun ι z => Real.sqrt (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2)))
  let fY : ℤ × ℤ → ℝ × Space → ℝ := fun ι z => Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))
  have hmT : ∀ ι, AEMeasurable (fT ι) slabMeasure := fun ι =>
    (Real.continuous_sqrt.comp Internal.FieldModes.continuous_cnormSq).measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeVel hTr ι)
  have hmO : ∀ ι, AEMeasurable (fO ι) slabMeasure := fun ι =>
    (Real.continuous_sqrt.comp (Internal.FieldModes.continuous_cnormSq.comp hcurl)).measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeGrad hv.measurable_gradient ι)
  have hmY : ∀ ι, AEMeasurable (fY ι) slabMeasure := fun ι =>
    (Real.continuous_sqrt.comp Internal.FieldModes.continuous_cnormSq).measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeVel hψ.1.continuous.aestronglyMeasurable ι)
  have hsq : ∀ (a : ℝ), 0 ≤ a → ENNReal.ofReal (Real.sqrt a ^ 2) = ENNReal.ofReal a := fun a ha => by
    rw [Real.sq_sqrt ha]
  have hT2 : ∑' ι, ∫⁻ z, ENNReal.ofReal (fT ι z ^ 2) ∂slabMeasure
      = periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2) := by
    have e : ∀ ι, ∫⁻ z, ENNReal.ofReal (fT ι z ^ 2) ∂slabMeasure = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (cnormSq (modeVel ι (fun σ y => secondDerivTrace (H σ y)) σ y)) := by
      intro ι
      simp only [fT, hsq _ (Internal.FieldModes.cnormSq_nonneg _)]
      exact lintegral_prod _ (Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
        (Internal.FieldModes.aemeasurable_modeVel hTr ι)).ennreal_ofReal
    rw [tsum_congr e]
    exact (hP.1 (fun σ y => secondDerivTrace (H σ y)) hTr (fun σ y => congrArg secondDerivTrace (hv.periodic_secondDeriv σ y))
      hv.sumSecondPartials_finite).symm
  have hO2 : ∑' ι, ∫⁻ z, ENNReal.ofReal (fO ι z ^ 2) ∂slabMeasure ≤ periodLIntegral (fun σ y => matSq (G σ y)) := by
    have e : ∀ ι, ∫⁻ z, ENNReal.ofReal (fO ι z ^ 2) ∂slabMeasure =
        ∫⁻ z, ENNReal.ofReal (cnormSq (curlOfGrad (modeGrad ι G z.1 z.2))) ∂slabMeasure := by
      intro ι
      simp only [fO, hsq _ (Internal.FieldModes.cnormSq_nonneg _)]
    rw [tsum_congr e]
    exact curlMode_squareSum_le hP hD hR hv
  have hY2 : ∑' ι, ∫⁻ z, ENNReal.ofReal (fY ι z ^ 2) ∂slabMeasure = periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2) := by
    have e : ∀ ι, ∫⁻ z, ENNReal.ofReal (fY ι z ^ 2) ∂slabMeasure = ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (cnormSq (modeVel ι ψ σ y)) := by
      intro ι
      simp only [fY, hsq _ (Internal.FieldModes.cnormSq_nonneg _)]
      exact lintegral_prod _ (Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
        (Internal.FieldModes.aemeasurable_modeVel hψ.1.continuous.aestronglyMeasurable ι)).ennreal_ofReal
    rw [tsum_congr e]
    exact (hP.1 ψ hψ.1.continuous.aestronglyMeasurable hψ.2.1 hY).symm
  have hTfin : ∑' ι, ∫⁻ z, ENNReal.ofReal (fT ι z ^ 2) ∂slabMeasure ≠ ⊤ := by
    rw [hT2]; exact hv.sumSecondPartials_finite.ne
  have hOfin : ∑' ι, ∫⁻ z, ENNReal.ofReal (fO ι z ^ 2) ∂slabMeasure ≠ ⊤ :=
    ne_top_of_le_ne_top hv.gradient_finite.ne hO2
  have hYfin : ∑' ι, ∫⁻ z, ENNReal.ofReal (fY ι z ^ 2) ∂slabMeasure ≠ ⊤ := by
    rw [hY2]; exact hY.ne
  obtain ⟨hTYfin, hTY⟩ := tsum_lintegral_mul_le hmT hTfin hYfin
  obtain ⟨hOYfin, hOY⟩ := tsum_lintegral_mul_le hmO hOfin hYfin
  rw [hT2, hY2] at hTY
  rw [hY2] at hOY
  have hO2r : Real.sqrt (∑' ι, ∫⁻ z, ENNReal.ofReal (fO ι z ^ 2) ∂slabMeasure).toReal
      ≤ Real.sqrt (periodLIntegral (fun σ y => matSq (G σ y))).toReal :=
    Real.sqrt_le_sqrt (ENNReal.toReal_mono hv.gradient_finite.ne hO2)
  let a : ℤ × ℤ → ℝ := fun ι => ∫ z, (∑ β : Fin nE, curlTerm (epsCoefOf m β) G ψ ι z.1 z.2) ∂slabMeasure
  have hQ : ∀ ι, ENNReal.ofReal |a ι| ≤ ENNReal.ofReal epsSup * ∫⁻ z, ENNReal.ofReal (fT ι z * fY ι z) ∂slabMeasure
      + ENNReal.ofReal epsGradSup * ∫⁻ z, ENNReal.ofReal (fO ι z * fY ι z) ∂slabMeasure := by
    intro ι
    refine (epsMode_abs_le hP hD hR m P h w Γ W hm hv hψ ι).trans (le_of_eq ?_)
    have hmeas : AEMeasurable (fun z => ENNReal.ofReal epsSup * ENNReal.ofReal (fT ι z * fY ι z)) slabMeasure :=
      ((hmT ι).mul (hmY ι)).ennreal_ofReal.const_mul _
    have e : ∀ z : ℝ × Space, ENNReal.ofReal ((epsSup * fT ι z + epsGradSup * fO ι z) * fY ι z) =
        ENNReal.ofReal epsSup * ENNReal.ofReal (fT ι z * fY ι z)
          + ENNReal.ofReal epsGradSup * ENNReal.ofReal (fO ι z * fY ι z) := by
      intro z
      have h1 : 0 ≤ fT ι z * fY ι z := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      have h2 : 0 ≤ fO ι z * fY ι z := mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
      rw [← ENNReal.ofReal_mul he, ← ENNReal.ofReal_mul hg,
        ← ENNReal.ofReal_add (mul_nonneg he h1) (mul_nonneg hg h2)]
      congr 1
      ring
    show ∫⁻ z, ENNReal.ofReal ((epsSup * fT ι z + epsGradSup * fO ι z) * fY ι z) ∂slabMeasure = _
    simp_rw [e]
    rw [lintegral_add_left' hmeas, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  have hsum : ∑' ι, ENNReal.ofReal |a ι| ≤ ENNReal.ofReal epsSup * ∑' ι, ∫⁻ z, ENNReal.ofReal (fT ι z * fY ι z) ∂slabMeasure
      + ENNReal.ofReal epsGradSup * ∑' ι, ∫⁻ z, ENNReal.ofReal (fO ι z * fY ι z) ∂slabMeasure := by
    calc _ ≤ _ := ENNReal.tsum_le_tsum hQ
      _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
  have hfin : ENNReal.ofReal epsSup * ∑' ι, ∫⁻ z, ENNReal.ofReal (fT ι z * fY ι z) ∂slabMeasure
      + ENNReal.ofReal epsGradSup * ∑' ι, ∫⁻ z, ENNReal.ofReal (fO ι z * fY ι z) ∂slabMeasure ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTYfin,
      ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOYfin⟩
  have hafin := ne_top_of_le_ne_top hfin hsum
  have has : Summable (fun ι => ‖a ι‖) := by
    refine (ENNReal.summable_toReal hafin).congr fun ι => ?_
    rw [ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
  have hN : 0 ≤ periodNorm ψ := Real.sqrt_nonneg _
  calc |epsModeSum m G ψ| = ‖∑' ι, a ι‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' ι, ‖a ι‖ := norm_tsum_le_tsum_norm has
    _ = (∑' ι, ENNReal.ofReal |a ι|).toReal := by
        rw [ENNReal.tsum_toReal_eq fun ι => ENNReal.ofReal_ne_top]
        exact tsum_congr fun ι => by rw [ENNReal.toReal_ofReal (abs_nonneg _), Real.norm_eq_abs]
    _ ≤ _ := ENNReal.toReal_mono hfin hsum
    _ = epsSup * (∑' ι, ∫⁻ z, ENNReal.ofReal (fT ι z * fY ι z) ∂slabMeasure).toReal
        + epsGradSup * (∑' ι, ∫⁻ z, ENNReal.ofReal (fO ι z * fY ι z) ∂slabMeasure).toReal := by
        rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hTYfin)
          (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hOYfin), ENNReal.toReal_mul, ENNReal.toReal_mul,
          ENNReal.toReal_ofReal he, ENNReal.toReal_ofReal hg]
    _ ≤ epsSup * (Real.sqrt (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal * periodNorm ψ)
        + epsGradSup * (Real.sqrt (periodLIntegral (fun σ y => matSq (G σ y))).toReal * periodNorm ψ) := by
        refine add_le_add (mul_le_mul_of_nonneg_left hTY he) (mul_le_mul_of_nonneg_left (hOY.trans ?_) hg)
        exact mul_le_mul_of_nonneg_right hO2r hN
    _ = _ := by ring

theorem muModeSum_abs_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    |muModeSum m v ψ| ≤ Real.sqrt (ratio * (m.seminormSq P v).toReal) * periodNorm ψ := by
  have hS := seminormSq_lt_top hP hD hR m P h w Γ W hm hv
  have hY := testField_sq_lt_top hψ
  have hr := hm.ratio_nonneg
  let sw : ℤ × ℤ → Space → ℝ := fun ι y => ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι|
    * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt y
  have hsw0 : ∀ ι y, 0 ≤ sw ι y := fun ι y =>
    Finset.sum_nonneg fun β _ => mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (hm.mu_wt_nonneg β y)
  have hwtc : ∀ β : Fin nM, Continuous (m.muP β).wt := fun β => by
    obtain ⟨K, hK⟩ := hm.mu_increment β
    exact hK.continuous
  let F : ℤ × ℤ → ℝ × Space → ℝ := fun ι z => ∑ β : Fin nM, velTerm (muCoefOf m β) v ψ ι z.1 z.2
  have hFpt : ∀ ι z, |F ι z| ≤ Real.sqrt (ratio * sw ι z.2)
      * (Real.sqrt (cnormSq (modeVel ι v z.1 z.2)) * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) :=
    fun ι z => mu_part_abs_le hm ι z.2 _ _
  have hmX : ∀ ι, AEMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι v z.1 z.2)) slabMeasure := fun ι =>
    Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeVel hv.measurable_velocity ι)
  have hmY : ∀ ι, AEMeasurable (fun z : ℝ × Space => cnormSq (modeVel ι ψ z.1 z.2)) slabMeasure := fun ι =>
    Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
      (Internal.FieldModes.aemeasurable_modeVel hψ.1.continuous.aestronglyMeasurable ι)
  have hmT : ∀ (ι : ℤ × ℤ) (β : Fin nM), AEMeasurable (fun z : ℝ × Space =>
      |PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt z.2
        * cnormSq (modeVel ι v z.1 z.2)) slabMeasure := fun ι β =>
    ((continuous_const.mul (hwtc β)).measurable.comp measurable_snd).aemeasurable.mul (hmX ι)
  have hsw_meas : ∀ ι, AEMeasurable (fun z : ℝ × Space => sw ι z.2) slabMeasure := fun ι =>
    ((continuous_finset_sum _ fun β _ => continuous_const.mul (hwtc β)).measurable.comp measurable_snd).aemeasurable
  let A : ℤ × ℤ → ℝ≥0∞ := fun ι => ∫⁻ z, ENNReal.ofReal (sw ι z.2 * cnormSq (modeVel ι v z.1 z.2)) ∂slabMeasure
  let Bψ : ℤ × ℤ → ℝ≥0∞ := fun ι => ∫⁻ z, ENNReal.ofReal (cnormSq (modeVel ι ψ z.1 z.2)) ∂slabMeasure
  have hAsum : ∑' ι, A ι = m.seminormSq P v := by
    have e : ∀ ι, A ι = ∑ β : Fin nM, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι| * |PieceWeights.frameFreq P (m.muP β).frame ι|
          * (m.muP β).wt y * cnormSq (modeVel ι v σ y)) := by
      intro ι
      have e1 : ∀ z : ℝ × Space, ENNReal.ofReal (sw ι z.2 * cnormSq (modeVel ι v z.1 z.2)) =
          ∑ β : Fin nM, ENNReal.ofReal (|PieceWeights.sgn (m.muP β).modes ι|
            * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt z.2 * cnormSq (modeVel ι v z.1 z.2)) := by
        intro z
        rw [show sw ι z.2 * cnormSq (modeVel ι v z.1 z.2) = ∑ β : Fin nM, |PieceWeights.sgn (m.muP β).modes ι|
            * |PieceWeights.frameFreq P (m.muP β).frame ι| * (m.muP β).wt z.2 * cnormSq (modeVel ι v z.1 z.2)
          from Finset.sum_mul _ _ _]
        exact ENNReal.ofReal_sum_of_nonneg fun β _ => mul_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _)
          (abs_nonneg _)) (hm.mu_wt_nonneg β z.2)) (Internal.FieldModes.cnormSq_nonneg _)
      show ∫⁻ z, ENNReal.ofReal (sw ι z.2 * cnormSq (modeVel ι v z.1 z.2)) ∂slabMeasure = _
      simp_rw [e1]
      rw [lintegral_finsetSum' _ fun β _ => (hmT ι β).ennreal_ofReal]
      refine Finset.sum_congr rfl fun β _ => ?_
      exact lintegral_prod _ (hmT ι β).ennreal_ofReal
    simp_rw [e]
    rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
    rfl
  have hBsum : ∑' ι, Bψ ι = periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2) := by
    rw [hP.1 ψ hψ.1.continuous.aestronglyMeasurable hψ.2.1 hY]
    exact tsum_congr fun ι => lintegral_prod _ (hmY ι).ennreal_ofReal
  have key : ∀ t : ℝ, 0 < t → |muModeSum m v ψ| ≤
      (t * (ratio * (m.seminormSq P v).toReal) + (periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2)).toReal / t) / 2 := by
    intro t ht
    have ha0 : 0 ≤ t / 2 * ratio := by positivity
    have hb0 : 0 ≤ 1 / (2 * t) := by positivity
    have hQ : ∀ ι, ∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure
        ≤ ENNReal.ofReal (t / 2 * ratio) * A ι + ENNReal.ofReal (1 / (2 * t)) * Bψ ι := by
      intro ι
      calc ∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure
          ≤ ∫⁻ z, (ENNReal.ofReal (t / 2 * ratio) * ENNReal.ofReal (sw ι z.2 * cnormSq (modeVel ι v z.1 z.2))
              + ENNReal.ofReal (1 / (2 * t)) * ENNReal.ofReal (cnormSq (modeVel ι ψ z.1 z.2))) ∂slabMeasure := by
            refine lintegral_mono fun z => ?_
            have hX0 := Internal.FieldModes.cnormSq_nonneg (modeVel ι v z.1 z.2)
            have hY0 := Internal.FieldModes.cnormSq_nonneg (modeVel ι ψ z.1 z.2)
            have hs0 := hsw0 ι z.2
            rw [← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul hb0,
              ← ENNReal.ofReal_add (mul_nonneg ha0 (mul_nonneg hs0 hX0)) (mul_nonneg hb0 hY0)]
            apply ENNReal.ofReal_le_ofReal
            rw [Real.norm_eq_abs]
            refine (hFpt ι z).trans ?_
            have hm2 := mul_le_half_sq (x := Real.sqrt (ratio * sw ι z.2) * Real.sqrt (cnormSq (modeVel ι v z.1 z.2)))
              (y := Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2))) ht
            rw [mul_pow, Real.sq_sqrt (mul_nonneg hr hs0), Real.sq_sqrt hX0, Real.sq_sqrt hY0] at hm2
            calc Real.sqrt (ratio * sw ι z.2)
                  * (Real.sqrt (cnormSq (modeVel ι v z.1 z.2)) * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)))
                = Real.sqrt (ratio * sw ι z.2) * Real.sqrt (cnormSq (modeVel ι v z.1 z.2))
                  * Real.sqrt (cnormSq (modeVel ι ψ z.1 z.2)) := by ring
              _ ≤ _ := hm2
              _ = _ := by ring
        _ = ENNReal.ofReal (t / 2 * ratio) * A ι + ENNReal.ofReal (1 / (2 * t)) * Bψ ι := by
            have hmeas : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (t / 2 * ratio)
                * ENNReal.ofReal (sw ι z.2 * cnormSq (modeVel ι v z.1 z.2))) slabMeasure :=
              ((hsw_meas ι).mul (hmX ι)).ennreal_ofReal.const_mul _
            rw [lintegral_add_left' hmeas,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    have hsum : ∑' ι, ∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure
        ≤ ENNReal.ofReal (t / 2 * ratio) * m.seminormSq P v
          + ENNReal.ofReal (1 / (2 * t)) * periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2) := by
      calc _ ≤ ∑' ι, (ENNReal.ofReal (t / 2 * ratio) * A ι + ENNReal.ofReal (1 / (2 * t)) * Bψ ι) :=
            ENNReal.tsum_le_tsum hQ
        _ = _ := by rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, hAsum, hBsum]
    have hfin : ENNReal.ofReal (t / 2 * ratio) * m.seminormSq P v
        + ENNReal.ofReal (1 / (2 * t)) * periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2) ≠ ⊤ :=
      ENNReal.add_ne_top.2 ⟨ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.ne,
        ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY.ne⟩
    have hQfin := ne_top_of_le_ne_top hfin hsum
    have hQs : Summable (fun ι => (∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure).toReal) :=
      ENNReal.summable_toReal hQfin
    have hnorm : ∀ ι, ‖∫ z, F ι z ∂slabMeasure‖ ≤ (∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure).toReal :=
      fun ι => norm_integral_le_lintegral_norm _
    have hsn : Summable (fun ι => ‖∫ z, F ι z ∂slabMeasure‖) :=
      Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hQs
    calc |muModeSum m v ψ| = ‖∑' ι, ∫ z, F ι z ∂slabMeasure‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' ι, ‖∫ z, F ι z ∂slabMeasure‖ := norm_tsum_le_tsum_norm hsn
      _ ≤ ∑' ι, (∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure).toReal := hsn.tsum_le_tsum hnorm hQs
      _ = (∑' ι, ∫⁻ z, ENNReal.ofReal ‖F ι z‖ ∂slabMeasure).toReal :=
          (ENNReal.tsum_toReal_eq fun ι => ne_top_of_le_ne_top hQfin (ENNReal.le_tsum ι)).symm
      _ ≤ (ENNReal.ofReal (t / 2 * ratio) * m.seminormSq P v
          + ENNReal.ofReal (1 / (2 * t)) * periodLIntegral (fun σ y => ‖ψ σ y‖ ^ 2)).toReal :=
          ENNReal.toReal_mono hfin hsum
      _ = _ := by
          rw [ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS.ne)
            (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hY.ne), ENNReal.toReal_mul, ENNReal.toReal_mul,
            ENNReal.toReal_ofReal ha0, ENNReal.toReal_ofReal hb0]
          ring
  exact le_sqrt_mul_of_forall (mul_nonneg hr ENNReal.toReal_nonneg) ENNReal.toReal_nonneg key

theorem pieceModeSum_abs_le (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ : ℝ → Space → Space}
    (hψ : IsPeriodicTestField ψ) :
    |pieceModeSum m v G ψ| ≤ (epsSup * Real.sqrt (periodLIntegral (fun σ y => ‖secondDerivTrace (H σ y)‖ ^ 2)).toReal
      + epsGradSup * Real.sqrt (periodLIntegral (fun σ y => matSq (G σ y))).toReal
      + Real.sqrt (ratio * (m.seminormSq P v).toReal)) * periodNorm ψ := by
  rw [pieceModeSum_split hP hD hR m P h w Γ W hm hv hψ]
  have h1 := epsModeSum_abs_le hP hD hR m P h w Γ W hm hv hψ
  have h2 := muModeSum_abs_le hP hD hR m P h w Γ W hm hv hψ
  calc |epsModeSum m G ψ + muModeSum m v ψ| ≤ |epsModeSum m G ψ| + |muModeSum m v ψ| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2
    _ = _ := by ring

theorem pieceModeSum_add (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds)
    {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
    (Γ : Set Symmetry) (W : ℝ → Space → Space) {w₀ epsSup epsGradSup ratio : ℝ}
    (hm : m.IsAdmissible P h w W w₀ epsSup epsGradSup ratio) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) {ψ₁ ψ₂ : ℝ → Space → Space}
    (h₁ : IsPeriodicTestField ψ₁) (h₂ : IsPeriodicTestField ψ₂) :
    pieceModeSum m v G (fun σ y => ψ₁ σ y + ψ₂ σ y) = pieceModeSum m v G ψ₁ + pieceModeSum m v G ψ₂ := by
  have e : ∀ ι : ℤ × ℤ, (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
      pieceIntegrand m v G (fun σ y => ψ₁ σ y + ψ₂ σ y) ι σ y)
      = (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ₁ ι σ y)
        + ∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ₂ ι σ y := by
    intro ι
    have i1 := pieceIntegrand_integrable hP hD hR m P h w Γ W hm hv h₁ ι
    have i2 := pieceIntegrand_integrable hP hD hR m P h w Γ W hm hv h₂ ι
    simp only [pieceIntegrand_add m v G h₁ h₂]
    have e1 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ₁ ι σ y)
        = ∫ z, pieceIntegrand m v G ψ₁ ι z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
      (integral_prod _ i1).symm
    have e2 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y, pieceIntegrand m v G ψ₂ ι σ y)
        = ∫ z, pieceIntegrand m v G ψ₂ ι z.1 z.2 ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
      (integral_prod _ i2).symm
    have e12 : (∫ σ in Set.Icc (0 : ℝ) 1, ∫ y,
        (pieceIntegrand m v G ψ₁ ι σ y + pieceIntegrand m v G ψ₂ ι σ y))
        = ∫ z, (pieceIntegrand m v G ψ₁ ι z.1 z.2 + pieceIntegrand m v G ψ₂ ι z.1 z.2)
          ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
      (integral_prod _ (i1.add i2)).symm
    rw [e12, e1, e2, integral_add i1 i2]
  unfold pieceModeSum
  rw [tsum_congr e]
  exact (pieceIntegral_summable hP hD hR m P h w Γ W hm hv h₁).tsum_add
    (pieceIntegral_summable hP hD hR m P h w Γ W hm hv h₂)

theorem pieceModeSum_smul {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (a : ℝ) (ψ : ℝ → Space → Space) :
    pieceModeSum m v G (fun σ y => a • ψ σ y) = a * pieceModeSum m v G ψ := by
  unfold pieceModeSum pieceIntegrand
  simp only [modeVel_smul, modeGrad_smul, curlOfGrad_smul, cdot_smul, re_smul_aux, ← Finset.mul_sum,
    ← mul_add, integral_const_mul, tsum_mul_left]

end Internal

end PieceField

open PieceField.Internal in
theorem pieceFieldExistsHolds_of (hP : ModeSquareSumHolds) (hD : ModeDerivativeHolds)
    (hR : ModeRotationHolds) : PieceFieldExistsHolds := by
  intro C nE nM m P h w Γ W w₀ epsSup epsGradSup ratio hm hwb v G H g hv
  have hS := seminormSq_lt_top hP hD hR m P h w Γ W hm hv
  refine ⟨hS, ?_⟩
  obtain ⟨hT, hG⟩ := energy_bounds hm hwb hv
  have hε : 0 ≤ epsSup := by
    have := hm.eps_sum_le 0
    exact le_trans (Finset.sum_nonneg fun β _ => hm.eps_wt_nonneg β 0) this
  have hε' : 0 ≤ epsGradSup := by
    have := hm.eps_grad_sum_le 0
    exact le_trans (Finset.sum_nonneg fun β _ => norm_nonneg _) this
  have hcoef := coef_le (ε := epsSup) (ε' := epsGradSup) (r := ratio)
    (n := (m.seminormSq P v).toReal) hm.c_pos hm.cμ_pos hm.weight_pos hε hε' hm.ratio_nonneg
    ENNReal.toReal_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg hT hG
  obtain ⟨M, hMm, hMp, hM2, hMq, hMψ, hMn⟩ :=
    exists_field_of_bounded (fun ψ => secondDerivPairing H ψ + pieceModeSum m v G ψ)
      (K := Real.sqrt ((1 + epsSup + epsGradSup / Real.sqrt w₀) ^ 2 / m.c + ratio / m.cμ)
        * Real.sqrt (m.c * weightedEnergy w G H + m.cμ * (m.seminormSq P v).toReal))
      (by positivity)
      (fun ψ₁ ψ₂ h₁ h₂ => by
        show secondDerivPairing H (fun σ y => ψ₁ σ y + ψ₂ σ y) + pieceModeSum m v G (fun σ y => ψ₁ σ y + ψ₂ σ y) = _
        rw [secondDerivPairing_add hv h₁ h₂, pieceModeSum_add hP hD hR m P h w Γ W hm hv h₁ h₂]
        ring)
      (fun a ψ _ => by
        show secondDerivPairing H (fun σ y => a • ψ σ y) + pieceModeSum m v G (fun σ y => a • ψ σ y) = _
        rw [secondDerivPairing_smul, pieceModeSum_smul m v G a ψ]
        ring)
      (fun ψ hψ => by
        have h1 := secondDerivPairing_abs_le hv hψ
        have h2 := pieceModeSum_abs_le hP hD hR m P h w Γ W hm hv hψ
        have hN : 0 ≤ periodNorm ψ := Real.sqrt_nonneg _
        calc |secondDerivPairing H ψ + pieceModeSum m v G ψ|
            ≤ |secondDerivPairing H ψ| + |pieceModeSum m v G ψ| := abs_add_le _ _
          _ ≤ _ := add_le_add h1 h2
          _ = _ := by ring
          _ ≤ _ := mul_le_mul_of_nonneg_right hcoef hN)
  exact ⟨M, ⟨hMm, hMp, hM2, hMq, hMψ⟩, hMn⟩

end Coercive

end Breakdown
