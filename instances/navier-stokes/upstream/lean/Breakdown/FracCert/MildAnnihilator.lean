import Breakdown.FracCert.StMildProfile
import Breakdown.Frac.NNicePairing
import Breakdown.Frac.NNiceField
import Breakdown.Frac.NNiceDense
import Breakdown.Frac.RMildOfWeakHeat
import Breakdown.Frac.RHeat
import Breakdown.FreqTr.Realization
import Breakdown.FreqTr.BilinTestFormula
import Breakdown.FreqTr.VelocityExists
import Breakdown.Weak.PairingVelocity

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.FracCert

open Breakdown.Freq

namespace Internal.MildAnnihilator

open Freq.Internal.VelocityInjective in
theorem inner_embed_nice (x : X) {φ : Space → Space} (hφ : IsNiceField φ) :
    inner ℝ x (embedX φ) = ∫ y, inner ℝ ((velocity x : Space → Space) y) (negSsp φ y) := by
  have hN := niceFieldProps (9 / 8) (by norm_num) (by norm_num)
  obtain ⟨-, hφd, hψn, -, -⟩ := hN φ hφ
  obtain ⟨⟨S, hS⟩, -, -, -, -⟩ := hN _ hψn
  have hG : MemLp (negSsp φ) (6 / 5) volume := by rw [← hS]; exact S.memLp (6 / 5) volume
  have hE : PairingEmbed := pairingEmbed embedNormLinear_holds.1 embedNormLinear_holds.2
  have hspec : VelocitySpec velocity :=
    Freq.Internal.BilinTestFormula.velocity_spec velocity_holds
  let P := (innerSL ℝ : Space →L[ℝ] Space →L[ℝ] ℝ).lpPairing (volume : Measure Space) 6 (6 / 5)
  have hpair : ∀ y : X, ∫ z, inner ℝ ((velocity y : Space → Space) z) (negSsp φ z) =
      P (velocity y) (hG.toLp _) :=
    fun y => WeakProfile.Internal.PairingVelocity.pairing_eq_lp φ hG y
  have heq : (fun y : X => inner ℝ y (embedX φ)) = fun y => P (velocity y) (hG.toLp _) := by
    apply Continuous.ext_on testDense_holds.2 (by fun_prop)
      ((P.flip (hG.toLp _)).continuous.comp velocity.continuous)
    intro y hy
    obtain ⟨ψ, hψ, rfl⟩ := testSpan_holds y hy
    show inner ℝ (embedX ψ) (embedX φ) = P (velocity (embedX ψ)) (hG.toLp _)
    have hψd : IsDecayField ψ := Freq.Internal.VelocityExists.isDecayField_of_isTestField hψ
    rw [hE _ _ hψd hφd, nicePairingByParts _ _ hψd hφ, ← hpair]
    unfold fieldPairing
    apply integral_congr_ae
    filter_upwards [(hspec ψ hψ) ▸ Freq.Internal.VelocityInjective.toLp6_test ψ hψ] with z hz
    rw [hz]
  rw [congrFun heq x, ← hpair]

end Internal.MildAnnihilator

open Internal.MildAnnihilator FracInternal.MildWeak in
theorem niceAnnihilator : NiceAnnihilatorStatement := by
  intro z hz
  have hα1 : (1 : ℝ) < 9 / 8 := by norm_num
  have hα2 : (9 / 8 : ℝ) < 3 / 2 := by norm_num
  have hN := niceFieldProps (9 / 8) hα1 hα2
  have h0 : ∀ φ, IsNiceField φ → inner ℝ z (embedX φ) = 0 := by
    intro φ hφ
    rw [inner_embed_nice z hφ]
    exact hz _ (hN φ hφ).2.2.1
  have hD : FracNiceGraphDense (9 / 8) := fracNiceGraphDense (9 / 8) hα1 hα2 niceEmbedSymbol
    (fun m hm => fracPower_niceField (9 / 8) hα1 hα2 m hm)
  have hH := fracHeatSemigroup (9 / 8)
  have h1 : ∀ τ : ℝ, 0 < τ → inner ℝ z (fracHeatX (9 / 8) τ z) = 0 := by
    intro τ hτ
    have hfr := isFracOf_heat (by norm_num) hH hτ z
    have hc : IsClosed {y : X | inner ℝ z y = 0} := isClosed_eq (by fun_prop) continuous_const
    have hcl : fracHeatX (9 / 8) τ z ∈ closure {y : X | inner ℝ z y = 0} := by
      rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨φ, hφ, e1, -⟩ := hD _ _ hfr ε hε
      exact ⟨embedX φ, h0 φ hφ, by rw [dist_comm, dist_eq_norm]; exact e1⟩
    exact hc.closure_subset hcl
  have e : fracHeatX (9 / 8) 0 z = z := by rw [hH.1]; rfl
  have hc : Tendsto (fun τ => fracHeatX (9 / 8) τ z) (𝓝[>] 0) (𝓝 z) := by
    have h := ((hH.2.2.2.1 z 0 self_mem_Ici).mono Ioi_subset_Ici_self).tendsto
    simpa only [e] using h
  have hlim : Tendsto (fun τ => inner ℝ z (fracHeatX (9 / 8) τ z)) (𝓝[>] 0) (𝓝 (inner ℝ z z)) :=
    tendsto_const_nhds.inner hc
  have hev : (fun τ => inner ℝ z (fracHeatX (9 / 8) τ z)) =ᶠ[𝓝[>] 0] fun _ => (0 : ℝ) :=
    eventually_nhdsWithin_of_forall (fun τ hτ => h1 τ hτ)
  have hzz : inner ℝ z z = (0 : ℝ) := tendsto_nhds_unique (hlim.congr' hev) tendsto_const_nhds
  exact inner_self_eq_zero.1 hzz

end Breakdown.FracCert
