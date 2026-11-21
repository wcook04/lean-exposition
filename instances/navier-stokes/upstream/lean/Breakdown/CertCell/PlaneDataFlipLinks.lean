import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.ModeFlip
import Breakdown.CertCell.TailFlipDecay

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.PlaneDataFlip

open CellCert.CellAnalysis.LowEntry.Internal (cylArg)
open TailBand.Internal.FlipDecay (ae_orbit_of_ae cylArg_eq)
open Internal.ModeFlip (ae_flip_gradient ae_joint_flip grad_of_columns secondDeriv_of_columns frameSign_mul_self
  modeVel_flip_of modeGrad_flip_of modeSecondDeriv_flip_of)

theorem flipPoint_planePoint (r z : ℝ) : flipPoint (planePoint (r, z)) = planePoint (r, -z) := by
  ext i
  fin_cases i <;>
    simp [planePoint, CellCert.CellAnalysis.cylPoint, flipPoint, unitVector]

theorem ae_field_flip {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hp : IsPerturbation Γ P v G H g) (hflip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) :
    ∀ᵐ w : ℝ × Space, v w.1 (flipPoint w.2) = flipPoint (v w.1 w.2)
      ∧ (∀ u, G w.1 (flipPoint w.2) u = flipPoint (G w.1 w.2 (flipPoint u)))
      ∧ ∀ u u', H w.1 (flipPoint w.2) u u' = flipPoint (H w.1 w.2 (flipPoint u) (flipPoint u')) := by
  obtain ⟨γ, hγ, hγ1, hγ2⟩ := hflip
  have hinv : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2) := by
    filter_upwards [hp.invariant γ hγ] with z hz
    rw [hγ2, add_zero, hγ1, hγ1] at hz
    exact hz
  have hvs : ∀ᵐ s, ∀ᵐ x, v s (flipPoint x) = flipPoint (v s x) := Measure.ae_ae_of_ae_prod hinv
  have hGs : ∀ᵐ s, ∀ᵐ x, ∀ j, G s (flipPoint x) (unitVector j)
      = frameSign j • flipPoint (G s x (unitVector j)) := by
    filter_upwards [hvs, hp.weak_gradient] with s h1 h2
    filter_upwards [ae_flip_gradient γ.1 hγ1 h2 1 (one_mul 1) (h1.mono fun x hx => by rw [hx, one_smul])]
      with x hx j
    rw [hx j, one_mul]
  have hHs : ∀ᵐ s, ∀ᵐ x, ∀ j l, H s (flipPoint x) (unitVector j) (unitVector l)
      = (frameSign l * frameSign j) • flipPoint (H s x (unitVector j) (unitVector l)) := by
    filter_upwards [hGs, hp.weak_secondDeriv] with s h1 h2
    have hl : ∀ l, ∀ᵐ x, ∀ j, H s (flipPoint x) (unitVector j) (unitVector l)
        = (frameSign l * frameSign j) • flipPoint (H s x (unitVector j) (unitVector l)) := fun l =>
      (ae_flip_gradient γ.1 hγ1 (h2 l) (frameSign l) (frameSign_mul_self l)
        (h1.mono fun x hx => hx l)).mono fun x hx j => hx j
    filter_upwards [ae_all_iff.2 hl] with x hx j l
    exact hx l j
  have hGj : ∀ j, ∀ᵐ z : ℝ × Space, G z.1 (flipPoint z.2) (unitVector j)
      = frameSign j • flipPoint (G z.1 z.2 (unitVector j)) := fun j =>
    ae_joint_flip γ.1 hγ1 (fun s x => G s x (unitVector j))
      ((continuous_id.clm_apply continuous_const).comp_aestronglyMeasurable hp.measurable_gradient)
      (frameSign j) (hGs.mono fun s hs => hs.mono fun x hx => hx j)
  have hHj : ∀ j l, ∀ᵐ z : ℝ × Space, H z.1 (flipPoint z.2) (unitVector j) (unitVector l)
      = (frameSign l * frameSign j) • flipPoint (H z.1 z.2 (unitVector j) (unitVector l)) := fun j l =>
    ae_joint_flip γ.1 hγ1 (fun s x => H s x (unitVector j) (unitVector l))
      (((continuous_id.clm_apply continuous_const).clm_apply continuous_const).comp_aestronglyMeasurable
        hp.measurable_secondDeriv)
      (frameSign l * frameSign j) (hHs.mono fun s hs => hs.mono fun x hx => hx j l)
  filter_upwards [hinv, ae_all_iff.2 hGj, ae_all_iff.2 fun j => ae_all_iff.2 (hHj j)] with w h1 h2 h3
  exact ⟨h1, grad_of_columns γ.1 hγ1 h2, secondDeriv_of_columns γ.1 hγ1 h3⟩

theorem ae_plane_mode_flip {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g)
    (hflip : ∃ γ ∈ Γ, (∀ y, γ.1 y = flipPoint y) ∧ γ.2 = 0) (ξ : ℤ × ℤ) :
    ∀ᵐ r : ℝ, ∀ᵐ z : ℝ,
      modeVel (flipLabel ξ) v 0 (planePoint (r, z))
          = (fun a => (frameSign a : ℂ) * modeVel ξ v 0 (planePoint (r, -z)) a) ∧
      modeGrad (flipLabel ξ) G 0 (planePoint (r, z))
          = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint (r, -z)) ab) ∧
      modeSecondDeriv (flipLabel ξ) H 0 (planePoint (r, z))
          = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
            * modeSecondDeriv ξ H 0 (planePoint (r, -z)) abc) := by
  have horb := ae_orbit_of_ae (ae_field_flip hp hflip)
  have hpt : ∀ᵐ p : ℝ × ℝ,
      modeVel (flipLabel ξ) v 0 (flipPoint (planePoint p))
          = (fun a => (frameSign a : ℂ) * modeVel ξ v 0 (planePoint p) a) ∧
      modeGrad (flipLabel ξ) G 0 (flipPoint (planePoint p))
          = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) ab) ∧
      modeSecondDeriv (flipLabel ξ) H 0 (flipPoint (planePoint p))
          = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
            * modeSecondDeriv ξ H 0 (planePoint p) abc) := by
    filter_upwards [horb] with p hp'
    have hq : ∀ᵐ τ : ℝ, ∀ᵐ φ : ℝ, v (0 + τ) (flipPoint (axialRot φ (planePoint p)))
          = flipPoint (v (0 + τ) (axialRot φ (planePoint p)))
        ∧ (∀ u, G (0 + τ) (flipPoint (axialRot φ (planePoint p))) u
          = flipPoint (G (0 + τ) (axialRot φ (planePoint p)) (flipPoint u)))
        ∧ ∀ u u', H (0 + τ) (flipPoint (axialRot φ (planePoint p))) u u'
          = flipPoint (H (0 + τ) (axialRot φ (planePoint p)) (flipPoint u) (flipPoint u')) := by
      have h1 : ∀ᵐ q ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
          v q.1 (flipPoint (cylArg (p, q.2))) = flipPoint (v q.1 (cylArg (p, q.2)))
          ∧ (∀ u, G q.1 (flipPoint (cylArg (p, q.2))) u = flipPoint (G q.1 (cylArg (p, q.2)) (flipPoint u)))
          ∧ ∀ u u', H q.1 (flipPoint (cylArg (p, q.2))) u u'
            = flipPoint (H q.1 (cylArg (p, q.2)) (flipPoint u) (flipPoint u')) := by
        rw [← Measure.volume_eq_prod]
        exact hp'
      filter_upwards [Measure.ae_ae_of_ae_prod h1] with τ hτ
      filter_upwards [hτ] with φ hφ
      simpa only [zero_add, cylArg_eq] using hφ
    exact ⟨modeVel_flip_of ξ (hq.mono fun τ h => h.mono fun φ h => h.1),
      modeGrad_flip_of ξ (hq.mono fun τ h => h.mono fun φ h => h.2.1),
      modeSecondDeriv_flip_of ξ (hq.mono fun τ h => h.mono fun φ h => h.2.2)⟩
  have hmp : MeasurePreserving (Prod.map (id : ℝ → ℝ) (fun z : ℝ => -z))
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) ((volume : Measure ℝ).prod (volume : Measure ℝ)) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_neg _)
  have hpt' : ∀ᵐ p ∂((volume : Measure ℝ).prod (volume : Measure ℝ)),
      modeVel (flipLabel ξ) v 0 (flipPoint (planePoint p))
          = (fun a => (frameSign a : ℂ) * modeVel ξ v 0 (planePoint p) a) ∧
      modeGrad (flipLabel ξ) G 0 (flipPoint (planePoint p))
          = (fun ab => ((frameSign ab.1 * frameSign ab.2 : ℝ) : ℂ) * modeGrad ξ G 0 (planePoint p) ab) ∧
      modeSecondDeriv (flipLabel ξ) H 0 (flipPoint (planePoint p))
          = (fun abc => ((frameSign abc.1 * frameSign abc.2.1 * frameSign abc.2.2 : ℝ) : ℂ)
            * modeSecondDeriv ξ H 0 (planePoint p) abc) := by
    rw [← Measure.volume_eq_prod]
    exact hpt
  filter_upwards [Measure.ae_ae_of_ae_prod (hmp.quasiMeasurePreserving.ae hpt')] with r hr
  filter_upwards [hr] with z hz
  simp only [Prod.map_apply, id_eq, flipPoint_planePoint, neg_neg] at hz
  exact hz

end Internal.PlaneDataFlip

open Internal.PlaneDataFlip in
theorem planeDataFlip (hF : TraceFlipHolds) (hM : TraceMatchHolds) (hD : ModeHeightDerivHolds)
    (hX : ModeFlipHolds) : PlaneDataFlipHolds := by
  intro Γ P v G H g hp hflip ξ a
  have hD1 := hD Γ P v G H g hp ξ a
  have hpl := ae_plane_mode_flip hp hflip ξ
  filter_upwards [hD1, ae_restrict_of_ae hpl] with r hr hrl h hh
  have w := hr (2 * h) (by positivity)
  have hs2 : frameSign (2 : Fin 3) = -1 := by simp [frameSign]
  have hV : ∀ᵐ z : ℝ, planeVel (flipLabel ξ) v a r z = (frameSign a : ℂ) * planeVel ξ v a r (-z) ∧
      planeVelHeight (flipLabel ξ) G a r z = -((frameSign a : ℂ) * planeVelHeight ξ G a r (-z)) ∧
      planeVelHeight2 (flipLabel ξ) H a r z = (frameSign a : ℂ) * planeVelHeight2 ξ H a r (-z) := by
    filter_upwards [hrl] with z hz
    obtain ⟨e1, e2, e3⟩ := hz
    refine ⟨?_, ?_, ?_⟩
    · simp only [planeVel]
      rw [e1]
    · simp only [planeVelHeight]
      rw [e2]
      dsimp only
      rw [hs2]
      push_cast
      ring
    · simp only [planeVelHeight2]
      rw [e3]
      dsimp only
      rw [hs2]
      push_cast
      ring
  constructor
  · have step : upperTrace (planeVel (flipLabel ξ) v a r) (planeVelHeight (flipLabel ξ) G a r) h
        = upperTrace (fun z => (frameSign a : ℂ) * planeVel ξ v a r (-z))
          (fun z => -((frameSign a : ℂ) * planeVelHeight ξ G a r (-z))) h := by
      unfold upperTrace
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hV] with z hz _
      rw [hz.1, hz.2.1]
    rw [step, hF, hM _ _ h hh w.1]
  · have step : upperTrace (planeVelHeight (flipLabel ξ) G a r) (planeVelHeight2 (flipLabel ξ) H a r) h
        = upperTrace (fun z => (-(frameSign a : ℂ)) * planeVelHeight ξ G a r (-z))
          (fun z => -((-(frameSign a : ℂ)) * planeVelHeight2 ξ H a r (-z))) h := by
      unfold upperTrace
      congr 1
      refine intervalIntegral.integral_congr_ae ?_
      filter_upwards [hV] with z hz _
      rw [hz.2.1, hz.2.2]
      ring
    rw [step, hF, hM _ _ h hh w.2.1]
    ring

end Bridge

end CertCell

end Breakdown
