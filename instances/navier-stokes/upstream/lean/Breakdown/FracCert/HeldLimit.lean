import Breakdown.FracCert.HeldLimitParts
import Breakdown.FracCert.HeldWeakProfileParts
import Breakdown.Frac.OpCovariance

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace HeldLimitInternal

theorem inner_integrable {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    Integrable (fun y => inner ℝ (f y) (g y)) := by
  refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem gradient_neg {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fun y => -Q y) := by
  obtain ⟨q, hq2, hQ2, hQm, hq⟩ := hQ
  refine ⟨fun y => -q y, ?_, ?_, hQm.neg, ?_⟩
  · simpa only [neg_sq] using hq2
  · simpa only [norm_neg] using hQ2
  · intro φ hφ j
    have h := hq φ hφ j
    simp only [mul_neg, inner_neg_left, integral_neg]
    linarith

theorem recover (h4 : SolenoidalSplitStatement) (h5 : GradientOrthogonalStatement) (m : ℕ)
    (F : Space → Space) (hF : MemLp F 2 volume) (hFc : IsClassField m F)
    (hort : ∀ ζ : Space → Space, IsSolenoidalL2 ζ → ∫ y, inner ℝ (F y) (ζ y) = 0) :
    ∃ Q : Space → Space, IsGradientField Q ∧ ∀ᵐ y ∂volume, F y + Q y = 0 := by
  obtain ⟨F₀, Q, hF₀s, -, hQg, hQ2, hsplit⟩ := h4 m F hF hFc
  have h0 := hort F₀ hF₀s
  have h1 := h5 Q F₀ hQg hQ2 hF₀s
  have iF := inner_integrable hF hF₀s.1
  have iQ := inner_integrable hQ2 hF₀s.1
  have hself : ∫ y, inner ℝ (F₀ y) (F₀ y) = 0 := by
    have e : ∫ y, inner ℝ (F₀ y) (F₀ y) = ∫ y, (inner ℝ (F y) (F₀ y) - inner ℝ (Q y) (F₀ y)) := by
      apply integral_congr_ae
      filter_upwards [hsplit] with y hy
      rw [hy, inner_add_left]
      ring
    rw [e, integral_sub iF iQ, h0, h1, sub_zero]
  have iself := inner_integrable hF₀s.1 hF₀s.1
  have hz : (fun y => inner ℝ (F₀ y) (F₀ y)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg (fun y => real_inner_self_nonneg) iself).1 hself
  refine ⟨fun y => -Q y, gradient_neg hQg, ?_⟩
  filter_upwards [hsplit, hz] with y hy hzy
  have hF0 : F₀ y = 0 := inner_self_eq_zero.1 hzy
  rw [hy, hF0, zero_add, add_neg_cancel]

theorem residual_orthogonal (h5 : GradientOrthogonalStatement) (hR : HeldResidualSquareStatement)
    {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N : ℕ} (d : FracCertData k N) (hd : IsFracCert α d)
    {p : Fin k → ℝ} (hp : p ∈ box d.radius) {u : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} {P : Space → Space} {κ : Fin k → ℝ}
    (hsol : d.IsHeldSolution α p u G H P κ) (ζ : Space → Space) (hζ : IsSolenoidalL2 ζ) :
    ∫ y, inner ℝ (d.heldResidual α p u G H P κ y) (ζ y) = 0 := by
  have hres := (hR α hα1 hα2 d hd p hp u G H P hsol.state κ).1
  obtain ⟨Q, hQg, hQ⟩ := hsol.equation
  have hQe : (fun y => -d.heldResidual α p u G H P κ y) =ᵐ[volume] Q := by
    filter_upwards [hQ] with y hy
    exact neg_eq_of_add_eq_zero_right hy
  have hQ2 : MemLp Q 2 volume := hres.neg.ae_eq hQe
  have h0 := h5 Q ζ hQg hQ2 hζ
  have e : ∫ y, inner ℝ (d.heldResidual α p u G H P κ y) (ζ y) = -∫ y, inner ℝ (Q y) (ζ y) := by
    rw [← integral_neg]
    apply integral_congr_ae
    filter_upwards [hQe] with y hy
    rw [← hy, inner_neg_left, neg_neg]
  rw [e, h0, neg_zero]

theorem residual_split {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (y : Space) :
    d.heldResidual α p v G H P κ y = d.heldResidual α p v G H P 0 y + ∑ i, κ i • d.actuator i y := by
  simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField, Pi.zero_apply,
    zero_smul, Finset.sum_const_zero, add_zero]
  abel

theorem residual_pair {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (ζ : Space → Space) (h0 : MemLp (d.heldResidual α p v G H P 0) 2 volume)
    (hζ : MemLp ζ 2 volume) (ha : ∀ i, MemLp (d.actuator i) 2 volume) :
    ∫ y, inner ℝ (d.heldResidual α p v G H P κ y) (ζ y) =
      (∫ y, inner ℝ (d.heldResidual α p v G H P 0 y) (ζ y)) +
        ∑ i, κ i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
  have e : (fun y => inner ℝ (d.heldResidual α p v G H P κ y) (ζ y)) = fun y =>
      inner ℝ (d.heldResidual α p v G H P 0 y) (ζ y) + ∑ i, κ i * inner ℝ (d.actuator i y) (ζ y) := by
    funext y
    rw [residual_split, inner_add_left, sum_inner]
    simp only [real_inner_smul_left]
  have i1 := inner_integrable h0 hζ
  have i2 : Integrable (fun y => ∑ i, κ i * inner ℝ (d.actuator i y) (ζ y)) :=
    integrable_finsetSum _ (fun i _ => (inner_integrable (ha i) hζ).const_mul (κ i))
  rw [e, integral_add i1 i2, integral_finsetSum _ (fun i _ => (inner_integrable (ha i) hζ).const_mul (κ i))]
  simp only [integral_const_mul]

theorem energy_nonneg {k N : ℕ} (d : FracCertData k N) {α : ℝ} (hd : IsFracCert α d)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) : 0 ≤ d.energy G H := by
  unfold FracCertData.energy weightedEnergy
  refine add_nonneg (integral_nonneg fun y => sq_nonneg _) (integral_nonneg fun y => ?_)
  refine mul_nonneg ?_ (Finset.sum_nonneg fun i _ => sq_nonneg _)
  exact le_trans hd.weightMin_pos.le (hd.weight_lower y)

theorem size_sq {k N : ℕ} (d : FracCertData k N) {α : ℝ} (hd : IsFracCert α d)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) :
    d.size G H κ ^ 2 = d.energy G H + d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by
  unfold FracCertData.size sizeNorm
  rw [Real.sq_sqrt]
  · rfl
  · exact add_nonneg (energy_nonneg d hd G H)
      (mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _))

theorem coord_bound {k N : ℕ} (d : FracCertData k N) {α : ℝ} (hd : IsFracCert α d)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ)
    {R : ℝ} (hR : d.size G H κ ≤ R) (i : Fin k) : d.multiplierScale * |κ i| ≤ R := by
  have hμ := hd.multiplierScale_pos
  have h0 : 0 ≤ d.size G H κ := Real.sqrt_nonneg _
  have h1 : (d.multiplierScale * |κ i|) ^ 2 ≤ d.size G H κ ^ 2 := by
    rw [size_sq d hd, mul_pow, sq_abs]
    have : κ i ^ 2 ≤ ∑ j, κ j ^ 2 :=
      Finset.single_le_sum (f := fun j => κ j ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
    nlinarith [energy_nonneg d hd G H, sq_nonneg d.multiplierScale]
  exact ((pow_le_pow_iff_left₀ (mul_nonneg hμ.le (abs_nonneg _)) h0 two_ne_zero).1 h1).trans hR

theorem residual_terms {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) :
    d.heldResidual α p v G H P κ = fun y =>
      driftField α (d.rotationRate p) v G y + driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
        + P y + d.profilePower p y + (d.gradProfile p y + G y) (d.profile p y + v y)
        + ∑ i, (d.multiplier p i + κ i) • d.actuator i y := by
  funext y
  simp only [FracCertData.heldResidual, FracCertData.fullField, FracCertData.localField,
    FracCertData.splitField, FracCertData.defect, symProduct, add_smul, Finset.sum_add_distrib,
    add_apply, map_add, smul_smul]
  norm_num
  abel

def turnLin (m : ℕ) : Space →ₗ[ℝ] Space where
  toFun := turnStep m
  map_add' a b := by
    ext i
    fin_cases i <;> simp [turnStep] <;> ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [turnStep] <;> ring

def mirrorLin : Space →ₗ[ℝ] Space where
  toFun := mirror
  map_add' a b := by
    ext i
    fin_cases i <;> simp [mirror]
    ring
  map_smul' c a := by
    ext i
    fin_cases i <;> simp [mirror]

theorem axial_turn (m : ℕ) (z : Space) : axialTurn (turnLin m z) = turnLin m (axialTurn z) := by
  change axialTurn (turnStep m z) = turnStep m (axialTurn z)
  ext i
  fin_cases i <;> simp [turnStep, axialTurn] <;> ring

theorem axial_mirror (z : Space) : axialTurn (mirrorLin z) = mirrorLin (axialTurn z) := by
  change axialTurn (mirror z) = mirror (axialTurn z)
  ext i
  fin_cases i <;> simp [mirror, axialTurn]

theorem vec_ext {a b : Space} (h : ∀ i : Fin 3, inner ℝ (unitVector i) a = inner ℝ (unitVector i) b) :
    a = b := by
  ext i
  have := h i
  simpa [unitVector, EuclideanSpace.inner_single_left] using this

theorem power_equivariant {α : ℝ} (R : Space ≃ₗᵢ[ℝ] Space) {v P : Space → Space}
    (hv : ∀ᵐ y ∂volume, v (R y) = R (v y)) (hP : IsWeakFractionalPower α v P) :
    ∀ᵐ y ∂volume, P (R y) = R (P y) := by
  have hR := R.measurePreserving
  have hRe := R.toHomeomorph.measurableEmbedding
  set P' : Space → Space := fun y => R.symm (P (R y)) with hP'
  have hpair : ∀ φ : Space → Space, IsTestVectorField φ →
      ∫ y, inner ℝ (P' y) (φ y) = ∫ y, inner ℝ (P y) (φ y) := by
    intro φ hφ
    set ψ : Space → Space := fun x => R (φ (R.symm x)) with hψ
    have hψt : IsTestVectorField ψ := by
      refine ⟨R.contDiff.comp (hφ.1.comp R.symm.contDiff), ?_⟩
      exact (hφ.2.comp_homeomorph R.symm.toHomeomorph).comp_left (map_zero R)
    have e1 : ∫ y, inner ℝ (P' y) (φ y) = ∫ y, inner ℝ (P (R y)) (ψ (R y)) := by
      congr 1
      funext y
      simp only [hP', hψ, LinearIsometryEquiv.symm_apply_apply]
      rw [← LinearIsometryEquiv.inner_map_map R, LinearIsometryEquiv.apply_symm_apply]
    have hA := FracInternal.fractionalPowerAt_comp_isometry α φ (hφ.1.of_le (WithTop.coe_le_coe.mpr le_top)) R
    have c1 := hR.integral_comp hRe (fun x => inner ℝ (P x) (ψ x))
    have c2 := hR.integral_comp hRe (fun x => inner ℝ (v x) (R (fractionalPowerAt α φ (R.symm x))))
    have e2 : ∫ x, inner ℝ (v x) (fractionalPowerAt α ψ x) =
        ∫ y, inner ℝ (v (R y)) (R (fractionalPowerAt α φ (R.symm (R y)))) := by
      rw [c2]
      congr 1
      funext x
      rw [hψ, hA]
    rw [e1, c1, hP.2 ψ hψt, e2, hP.2 φ hφ]
    apply integral_congr_ae
    filter_upwards [hv] with y hy
    simp only [LinearIsometryEquiv.symm_apply_apply, hy, LinearIsometryEquiv.inner_map_map]
  have hP'2 : MemLp P' 2 volume := by
    have h := hP.1.comp_measurePreserving hR
    exact (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp_memLp' h
  have hl' := hP'2.locallyIntegrable (by norm_num)
  have hl := hP.1.locallyIntegrable (by norm_num)
  have hc : ∀ i : Fin 3, ∀ᵐ y ∂volume, inner ℝ (unitVector i) (P' y) = inner ℝ (unitVector i) (P y) := by
    intro i
    have li : ∀ {f : Space → Space}, LocallyIntegrable f volume →
        LocallyIntegrable (fun y => inner ℝ (unitVector i) (f y)) volume := fun {f} h =>
      locallyIntegrable_iff.2 fun K hK => by
        have h2 := (innerSL ℝ (unitVector i)).integrable_comp (locallyIntegrable_iff.1 h K hK)
        simp only [innerSL_apply_apply] at h2
        exact h2
    refine ae_eq_of_integral_contDiff_smul_eq (li hl') (li hl) fun g hg hgc => ?_
    have ht : IsTestVectorField (fun y => g y • unitVector i) :=
      ⟨hg.smul contDiff_const, hgc.smul_right⟩
    have hq := hpair _ ht
    simp only [inner_smul_right, smul_eq_mul] at hq ⊢
    simpa only [real_inner_comm] using hq
  filter_upwards [ae_all_iff.2 hc] with y hy
  have h := vec_ext hy
  rw [hP'] at h
  simp only at h
  rw [← h, LinearIsometryEquiv.apply_symm_apply]

def turnIsom (m : ℕ) : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := turnLin m
      norm_map' := fun y => by
        change ‖turnStep m y‖ = ‖y‖
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp [Fin.sum_univ_three, turnStep, Real.norm_eq_abs, sq_abs]
        linear_combination (y 0 ^ 2 + y 1 ^ 2) * Real.sin_sq_add_cos_sq (2 * Real.pi / m) } rfl

def mirrorIsom : Space ≃ₗᵢ[ℝ] Space :=
  LinearIsometry.toLinearIsometryEquiv
    { toLinearMap := mirrorLin
      norm_map' := fun y => by
        change ‖mirror y‖ = ‖y‖
        rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
        congr 1
        simp [Fin.sum_univ_three, mirror, Real.norm_eq_abs, sq_abs] } rfl

theorem turnIsom_apply (m : ℕ) (y : Space) : turnIsom m y = turnStep m y := rfl

theorem mirrorIsom_apply (y : Space) : mirrorIsom y = mirror y := rfl

theorem sum_unit (w : Space) : w = ∑ j : Fin 3, w j • unitVector j := by
  ext i
  simp [unitVector, Pi.single_apply]

theorem clm_sum {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (L : Space →L[ℝ] F) (w : Space) : L w = ∑ j : Fin 3, w j • L (unitVector j) := by
  conv_lhs => rw [sum_unit w]
  simp only [map_sum, map_smul]

theorem dir_continuous {φ : Space → ℝ} (hφ : IsTestScalar φ) (w : Space) :
    Continuous (fun y => fderiv ℝ φ y w) :=
  (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const

theorem dir_support {φ : Space → ℝ} (hφ : IsTestScalar φ) (w : Space) :
    HasCompactSupport (fun y => fderiv ℝ φ y w) :=
  hφ.2.fderiv_apply (𝕜 := ℝ) w

theorem weak_dir {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} (hvl : LocallyIntegrable v volume)
    (hcol : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume) (hw : IsWeakGradientOf v G)
    (φ : Space → ℝ) (hφ : IsTestScalar φ) (w : Space) :
    ∫ y, (fderiv ℝ φ y w) • v y = -∫ y, φ y • G y w := by
  have i1 : ∀ j : Fin 3, Integrable (fun y => (fderiv ℝ φ y (unitVector j)) • v y) := fun j =>
    hvl.integrable_smul_left_of_hasCompactSupport (dir_continuous hφ _) (dir_support hφ _)
  have i2 : ∀ j : Fin 3, Integrable (fun y => φ y • G y (unitVector j)) := fun j =>
    (hcol j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
  have e1 : (fun y => (fderiv ℝ φ y w) • v y) = fun y => ∑ j : Fin 3, w j • ((fderiv ℝ φ y (unitVector j)) • v y) := by
    funext y
    rw [clm_sum (fderiv ℝ φ y) w]
    simp only [Finset.sum_smul, smul_assoc]
  have e2 : (fun y => φ y • G y w) = fun y => ∑ j : Fin 3, w j • (φ y • G y (unitVector j)) := by
    funext y
    rw [clm_sum (G y) w, Finset.smul_sum]
    simp only [smul_comm (φ y) (w _)]
  rw [e1, e2, integral_finsetSum _ (fun j _ =>
      (show Integrable (fun y => w j • ((fderiv ℝ φ y (unitVector j)) • v y)) from (i1 j).smul (w j))),
    integral_finsetSum _ (fun j _ =>
      (show Integrable (fun y => w j • (φ y • G y (unitVector j))) from (i2 j).smul (w j))),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_smul, integral_smul, hw φ hφ j, smul_neg]

theorem gradient_equivariant (R : Space ≃ₗᵢ[ℝ] Space) {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    (hvl : LocallyIntegrable v volume) (hcol : ∀ i, MemLp (fun y => G y (unitVector i)) 2 volume)
    (hw : IsWeakGradientOf v G) (hvc : ∀ᵐ y ∂volume, v (R y) = R (v y)) :
    ∀ᵐ y ∂volume, ∀ w, G (R y) (R w) = R (G y w) := by
  have hR := R.measurePreserving
  have hRe := R.toHomeomorph.measurableEmbedding
  have hcl : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    (hcol i).locallyIntegrable (by norm_num)
  have hc : ∀ i, ∀ᵐ y ∂volume, R.symm (G (R y) (R (unitVector i))) = G y (unitVector i) := by
    intro i
    have hm : MemLp (fun y => R.symm (G (R y) (R (unitVector i)))) 2 volume := by
      have e : (fun y => R.symm (G (R y) (R (unitVector i)))) = fun y =>
          R.symm (∑ j : Fin 3, (R (unitVector i)) j • G (R y) (unitVector j)) := by
        funext y
        rw [clm_sum (G (R y))]
      rw [e]
      have hs : MemLp (fun y => ∑ j : Fin 3, (R (unitVector i)) j • G (R y) (unitVector j)) 2 volume :=
        memLp_finsetSum _ fun j _ => (show MemLp (fun y => (R (unitVector i)) j • G (R y) (unitVector j)) 2 volume from
          ((hcol j).comp_measurePreserving hR).const_smul ((R (unitVector i)) j))
      exact (R.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp_memLp' hs
    refine ae_eq_of_integral_contDiff_smul_eq (hm.locallyIntegrable (by norm_num)) (hcl i) fun g hg hgc => ?_
    have hgt : IsTestScalar g := ⟨hg, hgc⟩
    set ψ : Space → ℝ := fun x => g (R.symm x) with hψ
    have hψt : IsTestScalar ψ := ⟨hg.comp R.symm.contDiff, hgc.comp_homeomorph R.symm.toHomeomorph⟩
    have hch : ∀ y, fderiv ℝ ψ (R y) (R (unitVector i)) = fderiv ℝ g y (unitVector i) := by
      intro y
      have hgd : DifferentiableAt ℝ g (R.symm.toContinuousLinearEquiv (R y)) :=
        (hg.differentiable (by simp)).differentiableAt
      have h := hgd.hasFDerivAt.comp (R y) (R.symm.toContinuousLinearEquiv.hasFDerivAt)
      rw [show ψ = g ∘ ⇑(R.symm.toContinuousLinearEquiv) from rfl, h.fderiv]
      simp
    have k1 : ∫ y, g y • R.symm (G (R y) (R (unitVector i))) =
        R.symm (∫ y, g y • G (R y) (R (unitVector i))) := by
      have h := R.symm.toLinearIsometry.integral_comp_comm (μ := volume)
        (fun y => g y • G (R y) (R (unitVector i)))
      simp only [LinearIsometryEquiv.coe_toLinearIsometry, map_smul] at h
      exact h
    have c1 := hR.integral_comp hRe (fun x => ψ x • G x (R (unitVector i)))
    have c2 := hR.integral_comp hRe (fun x => fderiv ℝ ψ x (R (unitVector i)) • v x)
    have k2 : ∫ y, g y • G (R y) (R (unitVector i)) = ∫ y, ψ (R y) • G (R y) (R (unitVector i)) := by
      congr 1
      funext y
      simp [hψ]
    have k3 : ∫ y, fderiv ℝ ψ (R y) (R (unitVector i)) • v (R y) =
        R (∫ y, fderiv ℝ g y (unitVector i) • v y) := by
      have h := R.toLinearIsometry.integral_comp_comm (μ := volume)
        (fun y => fderiv ℝ g y (unitVector i) • v y)
      simp only [LinearIsometryEquiv.coe_toLinearIsometry] at h
      rw [← h]
      apply integral_congr_ae
      filter_upwards [hvc] with y hy
      simp [hch y, hy, map_smul]
    have hd := weak_dir hvl hcl hw ψ hψt (R (unitVector i))
    have hg' := hw g hgt i
    have k4 : ∫ x, ψ x • G x (R (unitVector i)) = -∫ x, fderiv ℝ ψ x (R (unitVector i)) • v x := by
      rw [hd, neg_neg]
    rw [k1, k2, c1, k4, ← c2, k3, map_neg, LinearIsometryEquiv.symm_apply_apply, hg', neg_neg]
  filter_upwards [ae_all_iff.2 hc] with y hy w
  have hy' : ∀ i, G (R y) (R (unitVector i)) = R (G y (unitVector i)) := fun i => by
    rw [← hy i, LinearIsometryEquiv.apply_symm_apply]
  conv_lhs => rw [sum_unit w]
  rw [clm_sum (G y) w]
  simp only [map_sum, map_smul, hy']

theorem residual_at {k N : ℕ} (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (v : Space → Space)
    (G : Space → (Space →L[ℝ] Space)) (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (P : Space → Space)
    (κ : Fin k → ℝ) (L : Space →ₗ[ℝ] Space) (hJ : ∀ z, axialTurn (L z) = L (axialTurn z)) (y : Space)
    (h1 : v (L y) = L (v y)) (h2 : P (L y) = L (P y)) (h3 : d.profile p (L y) = L (d.profile p y))
    (h4 : d.profilePower p (L y) = L (d.profilePower p y)) (h5 : ∀ w, G (L y) (L w) = L (G y w))
    (h6 : ∀ w, d.gradProfile p (L y) (L w) = L (d.gradProfile p y w))
    (h7 : ∀ i, d.actuator i (L y) = L (d.actuator i y)) :
    d.heldResidual α p v G H P κ (L y) = L (d.heldResidual α p v G H P κ y) := by
  rw [residual_terms]
  simp only [driftField, add_apply, map_add, map_sub, map_smul, map_sum, h1, h2, h3, h4, h5, h6, h7, hJ]

end HeldLimitInternal

open HeldLimitInternal

theorem weakPowerClass_holds : WeakPowerClassStatement := by
  intro α _ _ m v P _ _ hvc hP
  constructor
  · have h := power_equivariant (turnIsom m) (by simpa only [turnIsom_apply] using hvc.1) hP
    simpa only [turnIsom_apply] using h
  · have h := power_equivariant mirrorIsom (by simpa only [mirrorIsom_apply] using hvc.2) hP
    simpa only [mirrorIsom_apply] using h

theorem gradientClass_holds : GradientClassStatement := by
  intro m v G _ hv6 hGm hGi hw hvc
  have hvl := hv6.locallyIntegrable (by norm_num)
  have hcol : ∀ i, MemLp (fun y => G y (unitVector i)) 2 volume := fun i => by
    have hm : AEStronglyMeasurable (fun y => G y (unitVector i)) volume := hGm.apply_continuousLinearMap _
    refine (memLp_two_iff_integrable_sq_norm hm).2 (hGi.mono' (hm.norm.pow 2) (ae_of_all _ fun y => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => sq_nonneg _)
      (Finset.mem_univ i)
  constructor
  · have h := gradient_equivariant (turnIsom m) hvl hcol hw (by simpa only [turnIsom_apply] using hvc.1)
    simpa only [turnIsom_apply] using h
  · have h := gradient_equivariant mirrorIsom hvl hcol hw (by simpa only [mirrorIsom_apply] using hvc.2)
    simpa only [mirrorIsom_apply] using h

theorem heldResidualClass_of (s1 : ProfileEmbedDataStatement) (s2 : WeakPowerClassStatement)
    (s3 : GradientClassStatement) : HeldResidualClassStatement := by
  intro α hα1 hα2 k N d hd p hp v G H P hst κ
  have hs := hst.second
  obtain ⟨m1, m6, mG, iG, wG, -⟩ := s1 α hα1 hα2 d hd p hp
  have hvc := hs.symmetric
  have hPc := s2 α hα1 hα2 d.order v P hs.measurable_velocity hs.velocity_six hvc hst.power
  have hWc := hd.profile_class p hp
  have hPPc := s2 α hα1 hα2 d.order _ _ m1 m6 hWc (hd.profile_power p hp)
  obtain ⟨hGt, hGm⟩ := s3 d.order v G hs.measurable_velocity hs.velocity_six hs.measurable_gradient
    hs.gradient_two hs.weak_gradient hvc
  obtain ⟨hgt, hgm⟩ := s3 d.order _ _ m1 m6 mG iG wG hWc
  have hAt : ∀ᵐ y ∂volume, ∀ i, d.actuator i (turnStep d.order y) = turnStep d.order (d.actuator i y) :=
    ae_all_iff.2 fun i => (hd.actuator_class i).1
  have hAm : ∀ᵐ y ∂volume, ∀ i, d.actuator i (mirror y) = mirror (d.actuator i y) :=
    ae_all_iff.2 fun i => (hd.actuator_class i).2
  constructor
  · filter_upwards [hvc.1, hPc.1, hWc.1, hPPc.1, hGt, hgt, hAt] with y h1 h2 h3 h4 h5 h6 h7
    exact residual_at d α p v G H P κ (turnLin d.order) (axial_turn d.order) y h1 h2 h3 h4 h5 h6 h7
  · filter_upwards [hvc.2, hPc.2, hWc.2, hPPc.2, hGm, hgm, hAm] with y h1 h2 h3 h4 h5 h6 h7
    exact residual_at d α p v G H P κ mirrorLin axial_mirror y h1 h2 h3 h4 h5 h6 h7

theorem heldResidualSquare_of (s1 : HeldQuadraticL2Statement) (s2 : HeldResidualClassStatement) :
    HeldResidualSquareStatement := by
  intro α hα1 hα2 k N d hd p hp v G H P hst κ
  refine ⟨?_, s2 α hα1 hα2 d hd p hp v G H P hst κ⟩
  rw [residual_terms]
  have hs : MemLp (fun y => ∑ i, (d.multiplier p i + κ i) • d.actuator i y) 2 volume :=
    memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (d.multiplier p i + κ i)
  exact ((((hst.drift.add (hd.profile_drift p hp)).add hst.power.1).add (hd.profile_power p hp).1).add
    (s1 α hα1 hα2 d hd p hp v G H hst.second)).add hs

theorem heldWeakLimit_of (s1 : HeldResidualSquareStatement) (s2 : HeldStateLimitStatement) :
    HeldWeakLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ R hsol hsize
  obtain ⟨φ₁, hφ₁, u₀, G₀, H₀, P₀, hst, hlsc, hG, hres⟩ :=
    s2 α hα1 hα2 d hd p q hp hq hpq u G H P κ R hsol hsize
  have hμ := hd.multiplierScale_pos
  have hbd : ∀ n, κ (φ₁ n) ∈ Metric.closedBall (0 : Fin k → ℝ) (R / d.multiplierScale) := by
    intro n
    rw [Metric.mem_closedBall, dist_zero_right]
    have hR0 : 0 ≤ R := le_trans (Real.sqrt_nonneg _) (hsize (φ₁ n))
    refine (pi_norm_le_iff_of_nonneg (div_nonneg hR0 hμ.le)).2 fun i => ?_
    rw [Real.norm_eq_abs, le_div_iff₀ hμ, mul_comm]
    exact coord_bound d hd _ _ _ (hsize (φ₁ n)) i
  obtain ⟨κ₀, -, φ₂, hφ₂, hκ⟩ := tendsto_subseq_of_bounded Metric.isBounded_closedBall hbd
  have hφ₂t := hφ₂.tendsto_atTop
  refine ⟨φ₁ ∘ φ₂, hφ₁.comp hφ₂, u₀, G₀, H₀, P₀, κ₀, hst, ?_, hκ, ?_, ?_⟩
  · have hR0 : 0 ≤ R := le_trans (Real.sqrt_nonneg _) (hsize 0)
    have hs : Filter.Tendsto (fun n => d.multiplierScale ^ 2 * ∑ i, κ (φ₁ (φ₂ n)) i ^ 2) Filter.atTop
        (nhds (d.multiplierScale ^ 2 * ∑ i, κ₀ i ^ 2)) := by
      refine Filter.Tendsto.const_mul _ (tendsto_finsetSum _ fun i _ => ?_)
      exact ((continuous_apply i).tendsto κ₀).comp hκ |>.pow 2
    have key : ∀ ε : ℝ, 0 < ε → d.energy G₀ H₀ + d.multiplierScale ^ 2 * ∑ i, κ₀ i ^ 2 ≤ R ^ 2 + ε := by
      intro ε hε
      have hev := hφ₂t.eventually (hlsc ε hε)
      refine le_of_tendsto (hs.const_add (d.energy G₀ H₀)) ?_
      filter_upwards [hev] with n hn
      have h1 := size_sq d hd (G (φ₁ (φ₂ n))) (H (φ₁ (φ₂ n))) (κ (φ₁ (φ₂ n)))
      have h2 : d.size (G (φ₁ (φ₂ n))) (H (φ₁ (φ₂ n))) (κ (φ₁ (φ₂ n))) ^ 2 ≤ R ^ 2 :=
        pow_le_pow_left₀ (Real.sqrt_nonneg _) (hsize _) 2
      linarith
    have hx : d.energy G₀ H₀ + d.multiplierScale ^ 2 * ∑ i, κ₀ i ^ 2 ≤ R ^ 2 :=
      le_of_forall_pos_le_add key
    unfold FracCertData.size sizeNorm weightedEnergy
    unfold FracCertData.energy weightedEnergy at hx
    calc Real.sqrt _ ≤ Real.sqrt (R ^ 2) := Real.sqrt_le_sqrt hx
      _ = R := Real.sqrt_sq hR0
  · refine tendsto_pi_nhds.2 fun i => ?_
    exact (hG (d.pin i) (hd.pin_measurable i).1 (hd.pin_two i).1).comp hφ₂t
  · intro ζ hζ
    have hn : ∀ n, MemLp (d.heldResidual α (p n) (u n) (G n) (H n) (P n) 0) 2 volume := fun n =>
      (s1 α hα1 hα2 d hd (p n) (hp n) (u n) (G n) (H n) (P n) (hsol n).state 0).1
    have h0 := (s1 α hα1 hα2 d hd q hq u₀ G₀ H₀ P₀ hst 0).1
    simp only [Function.comp_apply]
    rw [residual_pair d α q u₀ G₀ H₀ P₀ κ₀ ζ h0 hζ.1 hd.actuator_two]
    have e : (fun n => ∫ y, inner ℝ (d.heldResidual α (p (φ₁ (φ₂ n))) (u (φ₁ (φ₂ n))) (G (φ₁ (φ₂ n)))
        (H (φ₁ (φ₂ n))) (P (φ₁ (φ₂ n))) (κ (φ₁ (φ₂ n))) y) (ζ y)) = fun n =>
        (∫ y, inner ℝ (d.heldResidual α (p (φ₁ (φ₂ n))) (u (φ₁ (φ₂ n))) (G (φ₁ (φ₂ n)))
          (H (φ₁ (φ₂ n))) (P (φ₁ (φ₂ n))) 0 y) (ζ y)) +
          ∑ i, κ (φ₁ (φ₂ n)) i * ∫ y, inner ℝ (d.actuator i y) (ζ y) := by
      funext n
      exact residual_pair d α _ _ _ _ _ _ ζ (hn _) hζ.1 hd.actuator_two
    rw [e]
    refine ((hres ζ hζ).comp hφ₂t).add (tendsto_finsetSum _ fun i _ => ?_)
    exact ((((continuous_apply i).tendsto κ₀).comp hκ)).mul_const _

theorem heldLimit_of (h4 : SolenoidalSplitStatement) (h5 : GradientOrthogonalStatement)
    (s1 : HeldResidualSquareStatement) (s2 : HeldWeakLimitStatement) : HeldLimitStatement := by
  intro α hα1 hα2 k N d hd p q hp hq hpq u G H P κ hsol hsize
  obtain ⟨φ, hφ, u₀, G₀, H₀, P₀, κ₀, hst, hsz, hκ, hpins, hconv⟩ :=
    s2 α hα1 hα2 d hd p q hp hq hpq u G H P κ d.heldRadius hsol hsize
  refine ⟨φ, hφ, u₀, G₀, H₀, P₀, κ₀, ⟨hst, ?_, ?_⟩, hsz, hκ⟩
  · obtain ⟨hF, hFc⟩ := s1 α hα1 hα2 d hd q hq u₀ G₀ H₀ P₀ hst κ₀
    refine recover h4 h5 d.order (d.heldResidual α q u₀ G₀ H₀ P₀ κ₀) hF hFc ?_
    intro ζ hζ
    have hz : (fun n => ∫ y, inner ℝ
        (d.heldResidual α (p (φ n)) (u (φ n)) (G (φ n)) (H (φ n)) (P (φ n)) (κ (φ n)) y) (ζ y)) =
        fun _ => (0 : ℝ) := by
      funext n
      exact residual_orthogonal h5 s1 hα1 hα2 d hd (hp (φ n)) (hsol (φ n)) ζ hζ
    have hc := hconv ζ hζ
    rw [hz] at hc
    exact tendsto_nhds_unique hc tendsto_const_nhds
  · have hz : (fun n => d.pins (G (φ n))) = fun _ => (0 : Fin k → ℝ) := by
      funext n i
      exact (hsol (φ n)).pins i
    rw [hz] at hpins
    have h0 := tendsto_nhds_unique hpins tendsto_const_nhds
    intro i
    exact congrFun h0 i

end SteadyCert

end Breakdown
