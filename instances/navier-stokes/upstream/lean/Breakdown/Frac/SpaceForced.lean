import Breakdown.Frac.StSpace
import Breakdown.Uniqueness.PressureMollifyAux2
import Breakdown.Uniqueness.LocalEnergyAuxTime

open scoped ContDiff ENNReal Topology
open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FracInternal.Forced

open Breakdown.Internal.PressureMollify

theorem memLp_of_energy {w : Space → Space} (hw : Continuous w) {A : ℝ}
    (h : ∫⁻ x, ENNReal.ofReal (‖w x‖ ^ 2) ≤ ENNReal.ofReal A) : MemLp w 2 volume :=
  (memLp_two_iff_integrable_sq_norm hw.aestronglyMeasurable).2 (integrable_norm_sq hw h)

theorem contDiff_timeDeriv {T : ℝ} {f : ℝ → Space → Space}
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Space => f z.1 z.2) (Icc 0 T ×ˢ univ)) {t : ℝ}
    (ht : t ∈ Ioo 0 T) : ContDiff ℝ ∞ (fun x => deriv (fun τ => f τ x) t) := by
  have hU : IsOpen (Ioo 0 T ×ˢ (univ : Set Space)) := isOpen_Ioo.prod isOpen_univ
  have h1 : ContDiffOn ℝ ∞ (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2)) (Ioo 0 T ×ˢ univ) :=
    (hf.mono (prod_mono Ioo_subset_Icc_self subset_rfl)).fderiv_of_isOpen hU (by simp)
  have h3 : ContDiffOn ℝ ∞
      ((fderiv ℝ (fun z : ℝ × Space => f z.1 z.2)) ∘ fun x : Space => (t, x)) univ :=
    h1.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun x _ => ⟨ht, mem_univ x⟩)
  have h2 : ContDiff ℝ ∞
      (fun x : Space => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, x) (1, 0)) :=
    (contDiffOn_univ.1 h3).clm_apply contDiff_const
  have e : (fun x => deriv (fun τ => f τ x) t) =
      fun x => fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (t, x) (1, 0) := by
    funext x
    exact (Internal.CutoffEnergy.hasDerivAt_slice_time hf ht x).deriv
  rw [e]
  exact h2

theorem contDiff_gradient {p : Space → ℝ} (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (gradientAt p) := by
  show ContDiff ℝ ∞ (fun x => ∑ i : Fin 3, fderiv ℝ p x (unitVector i) • unitVector i)
  exact ContDiff.sum fun i _ => (contDiff_fderiv_apply hp _).smul contDiff_const

theorem contDiff_advection {w : Space → Space} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (advectionAt w) := by
  show ContDiff ℝ ∞ (fun x => fderiv ℝ w x (w x))
  exact (contDiff_infty_iff_fderiv.1 hw).2.clm_apply hw

theorem integral_inner_gradient_test {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ)
    {ξ : Space → ℝ} (hξ : ContDiff ℝ ∞ ξ) (hc : HasCompactSupport ξ) :
    ∫ x, inner ℝ (ψ x) (gradientAt ξ x) = -∫ x, divergenceAt ψ x * ξ x := by
  have hI : ∀ i : Fin 3, Integrable (fun x => ψ x i * fderiv ℝ ξ x (unitVector i)) := fun i =>
    ((contDiff_component hψ i).continuous.mul (contDiff_fderiv_apply hξ _).continuous
      ).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply hc _).mul_left (f := fun x => ψ x i))
  have hJ : ∀ i : Fin 3, Integrable
      (fun x => fderiv ℝ (fun y => ψ y i) x (unitVector i) * ξ x) := fun i =>
    ((contDiff_fderiv_apply (contDiff_component hψ i) _).continuous.mul hξ.continuous
      ).integrable_of_hasCompactSupport
      (hc.mul_left (f := fun x => fderiv ℝ (fun y => ψ y i) x (unitVector i)))
  have e1 : (fun x => inner ℝ (ψ x) (gradientAt ξ x)) =
      fun x => ∑ i : Fin 3, ψ x i * fderiv ℝ ξ x (unitVector i) := by
    funext x
    rw [real_inner_comm, inner_gradientAt]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have e2 : (fun x => divergenceAt ψ x * ξ x) =
      fun x => ∑ i : Fin 3, fderiv ℝ (fun y => ψ y i) x (unitVector i) * ξ x := by
    funext x
    simp only [divergenceAt, Finset.sum_mul, fderiv_component hψ]
  rw [e1, e2, integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i),
    ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ =>
    integral_mul_fderiv (contDiff_component hψ i) hξ hc (unitVector i)

theorem divergence_eq_zero_of_weak {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ)
    (h : ∀ ξ : Space → ℝ, ContDiff ℝ ∞ ξ → HasCompactSupport ξ →
      ∫ x, inner ℝ (ψ x) (gradientAt ξ x) = 0) (x : Space) : divergenceAt ψ x = 0 := by
  have hcont : Continuous (divergenceAt ψ) := (contDiff_divergenceAt hψ).continuous
  have hae : ∀ᵐ y ∂(volume : Measure Space), divergenceAt ψ y = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hcont.locallyIntegrable
      fun ξ hξ hc => ?_
    have h1 := integral_inner_gradient_test hψ hξ hc
    rw [h ξ hξ hc] at h1
    have e : (fun y => ξ y • divergenceAt ψ y) = fun y => divergenceAt ψ y * ξ y := by
      funext y
      rw [smul_eq_mul, mul_comm]
    rw [e]
    linarith
  have hfun : divergenceAt ψ = fun _ => (0 : ℝ) :=
    (hcont.ae_eq_iff_eq (μ := volume) continuous_const).1 hae
  exact congrFun hfun x

end Breakdown.FracInternal.Forced

namespace Breakdown

open FracInternal.Forced

theorem fracForced_of (h1 : SymmetryCompactStatement) (h2 : FracWeakSolenoidalStatement)
    (h3 : FracWeakContinuityStatement) (h4 : FracMollifyPairingStatement)
    (_h5 : RemainderIntegrableStatement) : FracForcedStatement := by
  intro α hα1 hα2 T v q hs hE
  obtain ⟨A, hA⟩ := hE
  have hsl : ∀ t ∈ Icc 0 T, ContDiff ℝ ∞ (v t) := fun t ht =>
    Internal.CutoffEnergy.contDiff_slice hs.smooth_velocity ht
  have hL : ∀ t ∈ Icc 0 T, MemLp (v t) 2 volume := fun t ht =>
    memLp_of_energy (hsl t ht).continuous (hA t ht)
  have hsym : ∀ t ∈ Icc 0 T, ∀ φ : Space → Space, ContDiff ℝ ∞ φ → HasCompactSupport φ →
      ∫ x, inner ℝ (fractionalPowerAt α (v t) x) (φ x) =
        ∫ x, inner ℝ (v t x) (fractionalPowerAt α φ x) := fun t ht φ hφ hc =>
    (h1 α hα1 hα2 (v t) φ (hsl t ht) (Or.inl (hL t ht)) hφ hc).2.2
  have hF : ∀ t ∈ Ioo 0 T, fractionalPowerAt α (v t) =
      fun x => -gradientAt (q t) x - deriv (fun τ => v τ x) t - advectionAt (v t) x := by
    intro t ht
    funext x
    rw [← hs.momentum t ht x]
    abel
  have hFs : ∀ t ∈ Ioo 0 T, ContDiff ℝ ∞ (fractionalPowerAt α (v t)) := by
    intro t ht
    rw [hF t ht]
    have hq := contDiff_gradient
      (Internal.CutoffEnergy.contDiff_slice hs.smooth_pressure (Ioo_subset_Icc_self ht))
    exact (hq.neg.sub (contDiff_timeDeriv hs.smooth_velocity ht)).sub
      (contDiff_advection (hsl t (Ioo_subset_Icc_self ht)))
  refine ⟨hs.smooth_velocity, hs.smooth_pressure, hs.momentum, hs.incompressible, hFs, ?_, ?_, ?_⟩
  · intro t ht x
    have htc := Ioo_subset_Icc_self ht
    exact divergence_eq_zero_of_weak (hFs t ht) (fun ξ hξ hc =>
      h2 α hα1 hα2 (v t) (hsl t htc) (hL t htc) (hs.incompressible t htc) ξ hξ hc) x
  · intro ϕ hϕ hc
    exact (h3 α hα1 hα2 T v hs.smooth_velocity ⟨A, hA⟩ ϕ hϕ hc).congr fun t ht =>
      hsym t ht ϕ hϕ hc
  · intro ϕ hϕ hc ε hε
    obtain ⟨ρ₀, hρ₀⟩ := h4 α hα1 hα2 ϕ hϕ hc A ε hε
    refine ⟨max ρ₀ 1, fun ρ hρ t ht => ?_⟩
    have hρpos : 0 < ρ := lt_of_lt_of_le one_pos ((le_max_right _ _).trans hρ)
    have htc := Ioo_subset_Icc_self ht
    rw [hsym t htc _ (Internal.PressureMollify.contDiff_mollify ρ hϕ hc)
      (Internal.PressureMollify.hasCompactSupport_mollify hρpos hc)]
    exact hρ₀ ρ ((le_max_left _ _).trans hρ) (v t) (hsl t htc).continuous (hA t htc)

end Breakdown
