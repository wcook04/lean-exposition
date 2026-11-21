import Breakdown.Uniqueness.PressureSumSecondPartials
import Breakdown.Uniqueness.PressureMollifyAux2
import Breakdown.Uniqueness.FundSolByParts
import Breakdown.Uniqueness.Restrict

open scoped ContDiff ENNReal Convolution
open MeasureTheory Set Real
open Breakdown.Internal.PressureMollify

noncomputable section

namespace Breakdown

private theorem integral_sum_sum {f : Fin 3 → Fin 3 → Space → ℝ}
    (hf : ∀ i j, Integrable (f i j)) :
    ∫ x, ∑ i, ∑ j, f i j x = ∑ i, ∑ j, ∫ x, f i j x := by
  rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => hf i j))]
  exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ (fun j _ => hf i j)

private theorem integral_mul_scalarSumSecondPartials {f g : Space → ℝ} (hf : ContDiff ℝ ∞ f)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) :
    ∫ x, f x * FundSol.scalarSumSecondPartials g x = ∫ x, FundSol.scalarSumSecondPartials f x * g x := by
  have hI : ∀ i : Fin 3, Integrable (fun x => f x * FundSol.secondPartial g i i x) := fun i =>
    (hf.continuous.mul (contDiff_secondPartial hg i i).continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_secondPartial hg hgc i i).mul_left (f := f))
  have hJ : ∀ i : Fin 3, Integrable (fun x => FundSol.secondPartial f i i x * g x) := fun i =>
    ((contDiff_secondPartial hf i i).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hgc.mul_left (f := FundSol.secondPartial f i i))
  have e1 : (fun x => f x * FundSol.scalarSumSecondPartials g x) =
      fun x => ∑ i : Fin 3, f x * FundSol.secondPartial g i i x := by
    funext x; simp only [FundSol.scalarSumSecondPartials, Finset.mul_sum]
  have e2 : (fun x => FundSol.scalarSumSecondPartials f x * g x) =
      fun x => ∑ i : Fin 3, FundSol.secondPartial f i i x * g x := by
    funext x; simp only [FundSol.scalarSumSecondPartials, Finset.sum_mul]
  rw [e1, e2, integral_finsetSum _ (fun i _ => hI i), integral_finsetSum _ (fun i _ => hJ i)]
  exact Finset.sum_congr rfl fun i _ => integral_mul_secondPartial hf hg hgc i i

private theorem stress_difference {w : Space → Space} (hw : ContDiff ℝ ∞ w)
    (hwE : Integrable (fun x => ‖w x‖ ^ 2)) {p : Space → ℝ} (hp : ContDiff ℝ ∞ p)
    (hssp : ∀ x, FundSol.scalarSumSecondPartials p x =
      -∑ i, ∑ j, FundSol.secondPartial (fun y => w y i * w y j) i j x)
    {θ Θ : Space → ℝ} (hθ : ContDiff ℝ ∞ θ) (hΘ : ContDiff ℝ ∞ Θ)
    (hθb : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 θ x‖ ≤ C) (hΘb : ∃ C, ∀ x, ‖iteratedFDeriv ℝ 2 Θ x‖ ≤ C)
    (hξc : HasCompactSupport (Θ - θ)) :
    stressPairing w w Θ - stressPairing w w θ = -∫ x, p x * FundSol.scalarSumSecondPartials (Θ - θ) x := by
  obtain ⟨C₁, hC₁⟩ := hθb
  obtain ⟨C₂, hC₂⟩ := hΘb
  have hξ : ContDiff ℝ ∞ (Θ - θ) := hΘ.sub hθ
  have hF : ∀ i j : Fin 3, ContDiff ℝ ∞ (fun y => w y i * w y j) := fun i j =>
    (contDiff_component hw i).mul (contDiff_component hw j)
  have hIθ : ∀ i j : Fin 3, Integrable (fun x => w x i * w x j * FundSol.secondPartial θ i j x) :=
    fun i j => integrable_stress hw.continuous hwE hθ hC₁ i j
  have hIΘ : ∀ i j : Fin 3, Integrable (fun x => w x i * w x j * FundSol.secondPartial Θ i j x) :=
    fun i j => integrable_stress hw.continuous hwE hΘ hC₂ i j
  have hIξ : ∀ i j : Fin 3,
      Integrable (fun x => w x i * w x j * FundSol.secondPartial (Θ - θ) i j x) := fun i j =>
    (((hF i j).continuous).mul (contDiff_secondPartial hξ i j).continuous
      ).integrable_of_hasCompactSupport
      ((hasCompactSupport_secondPartial hξ hξc i j).mul_left (f := fun y => w y i * w y j))
  have hIξ' : ∀ i j : Fin 3,
      Integrable (fun x => FundSol.secondPartial (fun y => w y i * w y j) j i x * (Θ - θ) x) :=
    fun i j => ((contDiff_secondPartial (hF i j) j i).continuous.mul hξ.continuous
      ).integrable_of_hasCompactSupport
      (hξc.mul_left (f := FundSol.secondPartial (fun y => w y i * w y j) j i))
  have h1 : stressPairing w w Θ = ∑ i, ∑ j, ∫ x, w x i * w x j * FundSol.secondPartial Θ i j x :=
    integral_sum_sum (f := fun i j x => w x i * w x j * FundSol.secondPartial Θ i j x) hIΘ
  have h2 : stressPairing w w θ = ∑ i, ∑ j, ∫ x, w x i * w x j * FundSol.secondPartial θ i j x :=
    integral_sum_sum (f := fun i j x => w x i * w x j * FundSol.secondPartial θ i j x) hIθ
  have h3 : ∀ i j : Fin 3, (∫ x, w x i * w x j * FundSol.secondPartial Θ i j x) -
      ∫ x, w x i * w x j * FundSol.secondPartial θ i j x =
      ∫ x, FundSol.secondPartial (fun y => w y i * w y j) j i x * (Θ - θ) x := by
    intro i j
    rw [← integral_sub (hIΘ i j) (hIθ i j)]
    have e : (fun x => w x i * w x j * FundSol.secondPartial Θ i j x -
        w x i * w x j * FundSol.secondPartial θ i j x) =
        fun x => w x i * w x j * FundSol.secondPartial (Θ - θ) i j x := by
      funext x; rw [secondPartial_sub hΘ hθ, mul_sub]
    rw [e]
    exact integral_mul_secondPartial (hF i j) hξ hξc i j
  have h4 : ∫ x, (∑ i, ∑ j, FundSol.secondPartial (fun y => w y i * w y j) j i x) * (Θ - θ) x =
      ∑ i, ∑ j, ∫ x, FundSol.secondPartial (fun y => w y i * w y j) j i x * (Θ - θ) x := by
    rw [← integral_sum_sum (f := fun i j x =>
      FundSol.secondPartial (fun y => w y i * w y j) j i x * (Θ - θ) x) hIξ']
    congr 1; funext x; simp only [Finset.sum_mul]
  have h5 : ∀ x, ∑ i, ∑ j, FundSol.secondPartial (fun y => w y i * w y j) j i x =
      -FundSol.scalarSumSecondPartials p x := by
    intro x
    rw [hssp x, neg_neg, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have e : (fun y => w y j * w y i) = fun y => w y i * w y j := by funext y; ring
    rw [e]
  have h6 := integral_mul_scalarSumSecondPartials hp hξ hξc
  have h7 : ∫ x, (∑ i, ∑ j, FundSol.secondPartial (fun y => w y i * w y j) j i x) * (Θ - θ) x =
      -∫ x, FundSol.scalarSumSecondPartials p x * (Θ - θ) x := by
    rw [← integral_neg]; congr 1; funext x; rw [h5 x, neg_mul]
  rw [h1, h2, ← Finset.sum_sub_distrib]
  simp only [← Finset.sum_sub_distrib, h3]
  rw [← h4, h7, h6]

private theorem pressureDefect_eq_of_hasCompactSupport {T : ℝ} {v : ℝ → Space → Space}
    {q : ℝ → Space → ℝ} (hv : IsSolutionOn T v q) {t : ℝ} (ht : t ∈ Ioo 0 T)
    (hvE : Integrable (fun x => ‖v t x‖ ^ 2)) {ϕ Φ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ)
    (hc : HasCompactSupport ϕ) (hΦ : ContDiff ℝ ∞ Φ) (hΦc : HasCompactSupport Φ)
    (hξc : HasCompactSupport
      (FundSol.potential (divergenceAt Φ) - FundSol.potential (divergenceAt ϕ))) :
    pressureDefect v q t Φ = pressureDefect v q t ϕ := by
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hvt : ContDiff ℝ ∞ (v t) := hv.contDiff_velocity htc
  have hqt : ContDiff ℝ ∞ (q t) := hv.contDiff_pressure htc
  have hζ := contDiff_divergenceAt hϕ
  have hζc := hasCompactSupport_divergenceAt hc
  have hZ := contDiff_divergenceAt hΦ
  have hZc := hasCompactSupport_divergenceAt hΦc
  have hθ := FundSol.contDiff_potential hζ hζc
  have hΘ := FundSol.contDiff_potential hZ hZc
  have hS := stress_difference hvt hvE hqt (fun x => scalarSumSecondPartials_pressure hv ht x) hθ hΘ
    (bound_iteratedFDeriv_two_potential hζ hζc) (bound_iteratedFDeriv_two_potential hZ hZc) hξc
  have hΔ : ∀ x, FundSol.scalarSumSecondPartials
      (FundSol.potential (divergenceAt Φ) - FundSol.potential (divergenceAt ϕ)) x =
      divergenceAt Φ x - divergenceAt ϕ x := by
    intro x
    have h1 := FundSol.scalarSumSecondPartials_potential hZ hZc x
    have h2 := FundSol.scalarSumSecondPartials_potential hζ hζc x
    simp only [FundSol.scalarSumSecondPartials] at h1 h2 ⊢
    simp only [secondPartial_sub hΘ hθ, Finset.sum_sub_distrib, h1, h2]
  have hIZ : Integrable (fun x => q t x * divergenceAt Φ x) :=
    (hqt.continuous.mul hZ.continuous).integrable_of_hasCompactSupport (hZc.mul_left (f := q t))
  have hIζ : Integrable (fun x => q t x * divergenceAt ϕ x) :=
    (hqt.continuous.mul hζ.continuous).integrable_of_hasCompactSupport (hζc.mul_left (f := q t))
  have hsplit : ∫ x, q t x * FundSol.scalarSumSecondPartials
      (FundSol.potential (divergenceAt Φ) - FundSol.potential (divergenceAt ϕ)) x =
      (∫ x, q t x * divergenceAt Φ x) - ∫ x, q t x * divergenceAt ϕ x := by
    rw [← integral_sub hIZ hIζ]
    congr 1; funext x; rw [hΔ x, mul_sub]
  unfold pressureDefect
  rw [integral_inner_gradientAt hqt hΦ hΦc, integral_inner_gradientAt hqt hϕ hc]
  linarith [hS, hsplit]

theorem pressureDefect_mollify {T : ℝ} {v : ℝ → Space → Space} {q : ℝ → Space → ℝ}
    (hv : IsSolutionOn T v q) (hE : EnergyBoundedOn T v) {t : ℝ} (ht : t ∈ Ioo 0 T)
    {ϕ : Space → Space} (hϕ : ContDiff ℝ ∞ ϕ) (hc : HasCompactSupport ϕ) {ρ : ℝ} (hρ : 0 < ρ) :
    pressureDefect v q t (FundSol.mollify ρ ϕ) = pressureDefect v q t ϕ := by
  obtain ⟨A, hA⟩ := hE
  have htc : t ∈ Icc 0 T := Ioo_subset_Icc_self ht
  have hvE := integrable_norm_sq (hv.contDiff_velocity htc).continuous (hA t htc)
  have hξc := hasCompactSupport_potential_sub hρ (contDiff_divergenceAt hϕ)
    (hasCompactSupport_divergenceAt hc)
  rw [← divergenceAt_mollify ρ hϕ hc] at hξc
  exact pressureDefect_eq_of_hasCompactSupport hv ht hvE hϕ hc (contDiff_mollify ρ hϕ hc)
    (hasCompactSupport_mollify hρ hc) hξc

end Breakdown
