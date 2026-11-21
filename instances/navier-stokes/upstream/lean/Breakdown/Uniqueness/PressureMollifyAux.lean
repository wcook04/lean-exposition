import Breakdown.Uniqueness.FundSolDecay

open scoped ContDiff ENNReal
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.Internal.PressureMollify

theorem infty_ne_zero : ((⊤ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by simp

theorem two_le_infty : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := 
  WithTop.coe_le_coe.2 le_top

theorem contDiff_fderiv_apply {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (w : Space) :
    ContDiff ℝ ∞ (fun y => fderiv ℝ θ y w) :=
  (contDiff_infty_iff_fderiv.1 hθ).2.clm_apply contDiff_const

theorem hasCompactSupport_fderiv_apply {θ : Space → ℝ} (hc : HasCompactSupport θ) (w : Space) :
    HasCompactSupport (fun y => fderiv ℝ θ y w) :=
  (hc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L w) rfl

theorem integral_mul_fderiv {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (w : Space) :
    ∫ x, f x * fderiv ℝ g x w = -∫ x, fderiv ℝ f x w * g x := by
  have h1 : Continuous (fun x => fderiv ℝ f x w) := (contDiff_fderiv_apply hf w).continuous
  have h2 : Continuous (fun x => fderiv ℝ g x w) := (contDiff_fderiv_apply hg w).continuous
  apply integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
  · exact (h1.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left (f := fun x => fderiv ℝ f x w))
  · exact (hf.continuous.mul h2).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hgc w).mul_left (f := f))
  · exact (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left (f := f))
  · exact fun x _ => (hf.differentiable infty_ne_zero) x
  · exact fun x _ => (hg.differentiable infty_ne_zero) x

theorem secondPartial_eq {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) (x : Space) :
    FundSol.secondPartial θ i j x =
      fderiv ℝ (fun y => fderiv ℝ θ y (unitVector j)) x (unitVector i) := by
  have hd : DifferentiableAt ℝ (fderiv ℝ θ) x :=
    ((contDiff_infty_iff_fderiv.1 hθ).2.differentiable infty_ne_zero) x
  rw [FundSol.secondPartial, iteratedFDeriv_two_apply, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem integral_mul_secondPartial {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (i j : Fin 3) :
    ∫ x, f x * FundSol.secondPartial g i j x = ∫ x, FundSol.secondPartial f j i x * g x := by
  have e1 : (fun x => f x * FundSol.secondPartial g i j x) =
      fun x => f x * fderiv ℝ (fun y => fderiv ℝ g y (unitVector j)) x (unitVector i) := by
    funext x; rw [secondPartial_eq hg]
  have e2 : (fun x => FundSol.secondPartial f j i x * g x) =
      fun x => fderiv ℝ (fun y => fderiv ℝ f y (unitVector i)) x (unitVector j) * g x := by
    funext x; rw [secondPartial_eq hf]
  have h1 := integral_mul_fderiv hf (contDiff_fderiv_apply hg (unitVector j))
    (hasCompactSupport_fderiv_apply hgc (unitVector j)) (unitVector i)
  have h2 := integral_mul_fderiv (contDiff_fderiv_apply hf (unitVector i)) hg hgc (unitVector j)
  rw [e1, e2, h1]
  linarith [h2]

def divergenceMap : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  ∑ i : Fin 3, (EuclideanSpace.proj i : Space →L[ℝ] ℝ).comp
    (ContinuousLinearMap.apply ℝ Space (unitVector i))

theorem divergenceMap_apply (A : Space →L[ℝ] Space) :
    divergenceMap A = ∑ i : Fin 3, A (unitVector i) i := by
  simp [divergenceMap]

theorem divergenceAt_eq_comp (ψ : Space → Space) :
    divergenceAt ψ = divergenceMap ∘ fderiv ℝ ψ := by
  funext x; rw [Function.comp_apply, divergenceMap_apply]; rfl

theorem contDiff_divergenceAt {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞ (divergenceAt ψ) := by
  rw [divergenceAt_eq_comp]; exact divergenceMap.contDiff.comp (contDiff_infty_iff_fderiv.1 hψ).2

theorem hasCompactSupport_divergenceAt {ψ : Space → Space} (hc : HasCompactSupport ψ) :
    HasCompactSupport (divergenceAt ψ) := by
  rw [divergenceAt_eq_comp]; exact (hc.fderiv (𝕜 := ℝ)).comp_left (map_zero _)

theorem inner_gradientAt (p : Space → ℝ) (x y : Space) :
    inner ℝ (gradientAt p x) y = ∑ i : Fin 3, fderiv ℝ p x (unitVector i) * y i := by
  simp [gradientAt, sum_inner, inner_smul_left, unitVector, EuclideanSpace.inner_single_left]

theorem fderiv_component {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (i : Fin 3) (x w : Space) :
    fderiv ℝ (fun y => ψ y i) x w = fderiv ℝ ψ x w i := by
  have h := (EuclideanSpace.proj (𝕜 := ℝ) i).hasFDerivAt.comp x
    ((hψ.differentiable infty_ne_zero) x).hasFDerivAt
  have h' : HasFDerivAt (fun y => ψ y i)
      ((EuclideanSpace.proj (𝕜 := ℝ) i : Space →L[ℝ] ℝ).comp (fderiv ℝ ψ x)) x := h
  rw [h'.fderiv]
  simp

theorem contDiff_component {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (i : Fin 3) :
    ContDiff ℝ ∞ (fun y => ψ y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff.comp hψ

theorem continuous_component {ψ : Space → Space} (hψ : Continuous ψ) (i : Fin 3) :
    Continuous (fun y => ψ y i) :=
  (EuclideanSpace.proj (𝕜 := ℝ) i).continuous.comp hψ

theorem hasCompactSupport_component {ψ : Space → Space} (hc : HasCompactSupport ψ) (i : Fin 3) :
    HasCompactSupport (fun y => ψ y i) :=
  hc.comp_left (g := fun z : Space => z i) (by simp)

theorem integral_inner_gradientAt {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) {ψ : Space → Space}
    (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) :
    ∫ x, inner ℝ (gradientAt p x) (ψ x) = -∫ x, p x * divergenceAt ψ x := by
  have hI : ∀ i : Fin 3, Integrable (fun x => fderiv ℝ p x (unitVector i) * ψ x i) := fun i =>
    ((contDiff_fderiv_apply hp _).continuous.mul (contDiff_component hψ i).continuous
      ).integrable_of_hasCompactSupport
      ((hasCompactSupport_component hc i).mul_left (f := fun x => fderiv ℝ p x (unitVector i)))
  have hJ : ∀ i : Fin 3, Integrable
      (fun x => p x * fderiv ℝ (fun y => ψ y i) x (unitVector i)) := fun i =>
    (hp.continuous.mul (contDiff_fderiv_apply (contDiff_component hψ i) _).continuous
      ).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply (hasCompactSupport_component hc i) _).mul_left (f := p))
  have e1 : (fun x => inner ℝ (gradientAt p x) (ψ x)) =
      fun x => ∑ i : Fin 3, fderiv ℝ p x (unitVector i) * ψ x i := by
    funext x; exact inner_gradientAt p x (ψ x)
  have e2 : (fun x => p x * divergenceAt ψ x) =
      fun x => ∑ i : Fin 3, p x * fderiv ℝ (fun y => ψ y i) x (unitVector i) := by
    funext x; simp only [divergenceAt, Finset.mul_sum, fderiv_component hψ]
  rw [e1, e2, integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i),
    ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := integral_mul_fderiv hp (contDiff_component hψ i) (hasCompactSupport_component hc i)
    (unitVector i)
  rw [h, neg_neg]

theorem integrable_norm_sq {w : Space → Space} (hw : Continuous w) {A : ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal A) :
    Integrable (fun x => ‖w x‖ ^ 2) := by
  refine ⟨(hw.norm.pow 2).aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun x => by positivity)]
  exact h.trans_lt ENNReal.ofReal_lt_top

theorem abs_secondPartial_le (θ : Space → ℝ) (i j : Fin 3) (x : Space) :
    |FundSol.secondPartial θ i j x| ≤ ‖iteratedFDeriv ℝ 2 θ x‖ := by
  have h := (iteratedFDeriv ℝ 2 θ x).le_opNorm ![unitVector i, unitVector j]
  simpa [FundSol.secondPartial, Fin.prod_univ_two, unitVector, PiLp.norm_single] using h

theorem contDiff_secondPartial {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (i j : Fin 3) :
    ContDiff ℝ ∞ (FundSol.secondPartial θ i j) := by
  have e : FundSol.secondPartial θ i j =
      fun x => fderiv ℝ (fun y => fderiv ℝ θ y (unitVector j)) x (unitVector i) := by
    funext x; exact secondPartial_eq hθ i j x
  rw [e]; exact contDiff_fderiv_apply (contDiff_fderiv_apply hθ _) _

theorem hasCompactSupport_secondPartial {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hc : HasCompactSupport θ) (i j : Fin 3) :
    HasCompactSupport (FundSol.secondPartial θ i j) := by
  have e : FundSol.secondPartial θ i j =
      fun x => fderiv ℝ (fun y => fderiv ℝ θ y (unitVector j)) x (unitVector i) := by
    funext x; exact secondPartial_eq hθ i j x
  rw [e]; exact hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply hc _) _

theorem integrable_stress {w : Space → Space} (hw : Continuous w)
    (hE : Integrable (fun x => ‖w x‖ ^ 2)) {θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) {C : ℝ}
    (hb : ∀ x, ‖iteratedFDeriv ℝ 2 θ x‖ ≤ C) (i j : Fin 3) :
    Integrable (fun x => w x i * w x j * FundSol.secondPartial θ i j x) := by
  refine (hE.mul_const C).mono' ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (((continuous_component hw i).mul (continuous_component hw j)).mul
      (contDiff_secondPartial hθ i j).continuous).aestronglyMeasurable
  · have hi : ‖w x i‖ ≤ ‖w x‖ := PiLp.norm_apply_le _ _
    have hj : ‖w x j‖ ≤ ‖w x‖ := PiLp.norm_apply_le _ _
    have hs : ‖FundSol.secondPartial θ i j x‖ ≤ C :=
      (Real.norm_eq_abs _ ▸ abs_secondPartial_le θ i j x).trans (hb x)
    rw [norm_mul, norm_mul, sq]
    gcongr

theorem bound_iteratedFDeriv_two_potential {g : Space → ℝ} (hg : ContDiff ℝ ∞ g)
    (hc : HasCompactSupport g) :
    ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 (FundSol.potential g) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := FundSol.potential_decay hg hc
  refine ⟨|C|, fun x => (hC 2 (by norm_num) x).trans ?_⟩
  have h0 : 0 ≤ (1 + ‖x‖)⁻¹ := by positivity
  have h1 : (1 + ‖x‖)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [norm_nonneg x])
  have h3 : (1 + ‖x‖)⁻¹ ^ (2 + 1) ≤ 1 := pow_le_one₀ h0 h1
  calc C * (1 + ‖x‖)⁻¹ ^ (2 + 1) ≤ |C| * (1 + ‖x‖)⁻¹ ^ (2 + 1) := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * 1 := by gcongr
    _ = |C| := mul_one _

theorem secondPartial_sub {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    (i j : Fin 3) (x : Space) :
    FundSol.secondPartial (f - g) i j x =
      FundSol.secondPartial f i j x - FundSol.secondPartial g i j x := by
  simp only [FundSol.secondPartial]
  rw [iteratedFDeriv_sub_apply (hf.contDiffAt.of_le two_le_infty) (hg.contDiffAt.of_le two_le_infty)]
  rfl

end Breakdown.Internal.PressureMollify
