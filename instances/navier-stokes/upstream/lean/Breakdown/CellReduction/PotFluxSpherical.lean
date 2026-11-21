import Breakdown.FracCell.CylIntegral

open MeasureTheory Real Set

noncomputable section

namespace Breakdown.PotentialShape

open CellCert.Spectral CellCert.Spectral.Internal.CylIntegral

def sphericalPoint (r ϑ φ : ℝ) : Space := cylPoint (r * Real.sin ϑ) φ (r * Real.cos ϑ)

def sphericalBox : Set ((ℝ × ℝ) × ℝ) := (Ioi (0 : ℝ) ×ˢ Ioo 0 π) ×ˢ Ioo (-π) π

namespace Internal.SphericalChange

def turnEquiv : (ℝ × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
  MeasurableEquiv.prodAssoc.trans MeasurableEquiv.prodComm

theorem turnEquiv_apply (a b c : ℝ) : turnEquiv ((a, b), c) = ((b, c), a) := rfl

theorem turnEquiv_mp : MeasurePreserving turnEquiv volume volume :=
  Measure.measurePreserving_swap.comp (measurePreserving_prodAssoc volume volume volume)

theorem turnEquiv_preimage :
    turnEquiv ⁻¹' cylMap.target = ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) ×ˢ Ioo (-π) π := by
  ext ⟨⟨a, b⟩, c⟩
  simp [turnEquiv_apply, cylMap_target, polarCoord_target]

theorem cylMap_symm_pair (p : ℝ × ℝ) (c : ℝ) : cylMap.symm (p, c) = (polarCoord.symm p, c) := rfl

theorem box_measurable : MeasurableSet sphericalBox :=
  (measurableSet_Ioi.prod measurableSet_Ioo).prod measurableSet_Ioo

theorem box_sub : sphericalBox ⊆ cylMap.target := by
  rintro ⟨⟨r, t⟩, s⟩ ⟨⟨hr, ht⟩, hs⟩
  rw [cylMap_target, polarCoord_target]
  exact ⟨⟨hr, by linarith [ht.1, Real.pi_pos], ht.2⟩, mem_univ _⟩

theorem image_box :
    cylMap.symm '' sphericalBox = ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) ×ˢ Ioo (-π) π := by
  ext ⟨⟨a, b⟩, c⟩
  constructor
  · rintro ⟨⟨⟨r, t⟩, s⟩, ⟨⟨hr, ht⟩, hs⟩, he⟩
    rw [cylMap_symm_pair] at he
    simp only [polarCoord_symm_apply, Prod.mk.injEq] at he
    obtain ⟨⟨-, rfl⟩, rfl⟩ := he
    exact ⟨⟨mem_univ _, mul_pos hr (Real.sin_pos_of_pos_of_lt_pi ht.1 ht.2)⟩, hs⟩
  · rintro ⟨⟨-, hb1⟩, hc1⟩
    have hb : (0 : ℝ) < b := hb1
    have hc : c ∈ Ioo (-π) π := hc1
    have hsource : (a, b) ∈ polarCoord.source := by
      rw [polarCoord_source]
      exact Or.inr (ne_of_gt hb)
    have htgt : polarCoord (a, b) ∈ Ioi (0 : ℝ) ×ˢ Ioo (-π) π := by
      rw [← polarCoord_target]
      exact polarCoord.map_source hsource
    have hinv : polarCoord.symm (polarCoord (a, b)) = (a, b) := polarCoord.left_inv hsource
    have hsin : (polarCoord (a, b)).1 * Real.sin (polarCoord (a, b)).2 = b := by
      have := congrArg Prod.snd hinv
      simpa only [polarCoord_symm_apply] using this
    have hpos : 0 < (polarCoord (a, b)).2 := by
      by_contra hneg
      rw [not_lt] at hneg
      have h1 := Real.sin_nonpos_of_nonpos_of_neg_pi_le hneg htgt.2.1.le
      have h2 : (polarCoord (a, b)).1 * Real.sin (polarCoord (a, b)).2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt htgt.1) h1
      linarith
    refine ⟨(polarCoord (a, b), c), ⟨⟨htgt.1, hpos, htgt.2.2⟩, hc⟩, ?_⟩
    rw [cylMap_symm_pair, hinv]

theorem box_value (r t s : ℝ) :
    cylMap.symm (turnEquiv (cylMap.symm ((r, t), s))) =
      ((r * Real.sin t * Real.cos s, r * Real.sin t * Real.sin s), r * Real.cos t) := rfl

theorem toSpace_box (r t s : ℝ) :
    toSpace (cylMap.symm (turnEquiv (cylMap.symm ((r, t), s)))) = sphericalPoint r t s := by
  rw [box_value r t s, toSpace_apply]
  rfl

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_target (g : (ℝ × ℝ) × ℝ → E) :
    ∫ w, g w = ∫ x in cylMap.target, x.1.1 • g (cylMap.symm x) := by
  rw [← setIntegral_univ, ← setIntegral_congr_set image_ae,
    integral_image_eq_integral_abs_det_fderiv_smul volume cylMap.open_target.measurableSet
      (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g]
  refine setIntegral_congr_fun cylMap.open_target.measurableSet fun x hx => ?_
  simp only [abs_det_eq hx]

theorem integrable_target (g : (ℝ × ℝ) × ℝ → E) :
    Integrable g ↔ IntegrableOn (fun x => x.1.1 • g (cylMap.symm x)) cylMap.target := by
  have hset : IntegrableOn g (cylMap.symm '' cylMap.target) ↔ Integrable g :=
    ⟨fun h => integrableOn_univ.mp (h.congr_set_ae image_ae.symm),
      fun h => (integrableOn_univ.mpr h).congr_set_ae image_ae⟩
  rw [← hset, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume
      cylMap.open_target.measurableSet (fun x _ => (hasDeriv x).hasFDerivWithinAt) cylMap.symm.injOn g]
  exact integrableOn_congr_fun (fun x hx => by simp only [abs_det_eq hx])
    cylMap.open_target.measurableSet

theorem integral_turn (H : (ℝ × ℝ) × ℝ → E) :
    ∫ x in cylMap.target, H x =
      ∫ p in sphericalBox, p.1.1 • H (turnEquiv (cylMap.symm p)) := by
  rw [← turnEquiv_mp.setIntegral_preimage_emb turnEquiv.measurableEmbedding H, turnEquiv_preimage,
    ← image_box, integral_image_eq_integral_abs_det_fderiv_smul volume box_measurable
      (fun x _ => (hasDeriv x).hasFDerivWithinAt) (cylMap.symm.injOn.mono box_sub)]
  refine setIntegral_congr_fun box_measurable fun x hx => ?_
  simp only [abs_det_eq (box_sub hx)]

theorem integrable_turn (H : (ℝ × ℝ) × ℝ → E) :
    IntegrableOn H cylMap.target ↔
      IntegrableOn (fun p => p.1.1 • H (turnEquiv (cylMap.symm p))) sphericalBox := by
  rw [← turnEquiv_mp.integrableOn_comp_preimage turnEquiv.measurableEmbedding, turnEquiv_preimage,
    ← image_box, integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume box_measurable
      (fun x _ => (hasDeriv x).hasFDerivWithinAt) (cylMap.symm.injOn.mono box_sub)]
  exact integrableOn_congr_fun (fun x hx => by simp only [abs_det_eq (box_sub hx), Function.comp_apply])
    box_measurable

theorem weight_eq (f : Space → E) (p : (ℝ × ℝ) × ℝ) :
    p.1.1 • ((turnEquiv (cylMap.symm p)).1.1 • f (toSpace (cylMap.symm (turnEquiv (cylMap.symm p))))) =
      (p.1.1 ^ 2 * Real.sin p.1.2) • f (sphericalPoint p.1.1 p.1.2 p.2) := by
  obtain ⟨⟨r, t⟩, s⟩ := p
  rw [toSpace_box, smul_smul]
  congr 1
  show r * (r * Real.sin t) = r ^ 2 * Real.sin t
  ring

theorem swap_preimage_box :
    swapEquiv ⁻¹' sphericalBox = (Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ×ˢ Ioo 0 π := by
  ext ⟨⟨r, s⟩, t⟩
  simp only [mem_preimage, swapEquiv_apply, sphericalBox, mem_prod]
  tauto

end Internal.SphericalChange

open Internal.SphericalChange

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem integral_eq_sphericalBox (f : Space → E) :
    ∫ y, f y = ∫ p in sphericalBox, (p.1.1 ^ 2 * Real.sin p.1.2) • f (sphericalPoint p.1.1 p.1.2 p.2) := by
  rw [← toSpace_mp.integral_comp' f, integral_target, integral_turn]
  exact setIntegral_congr_fun box_measurable fun p _ => weight_eq f p

theorem integrable_iff_sphericalBox (f : Space → E) :
    Integrable f ↔
      IntegrableOn (fun p => (p.1.1 ^ 2 * Real.sin p.1.2) • f (sphericalPoint p.1.1 p.1.2 p.2))
        sphericalBox := by
  rw [← toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding, integrable_target, integrable_turn]
  exact integrableOn_congr_fun (fun p _ => weight_eq f p) box_measurable

theorem integral_eq_spherical_radius_polar_azimuth [CompleteSpace E] (f : Space → E)
    (hf : Integrable f) :
    ∫ y, f y = ∫ r in Ioi (0 : ℝ), ∫ ϑ in Ioo 0 π, ∫ φ in Ioo (-π) π,
      (r ^ 2 * Real.sin ϑ) • f (sphericalPoint r ϑ φ) := by
  have hbox := (integrable_iff_sphericalBox f).mp hf
  unfold sphericalBox at hbox
  have hin : IntegrableOn (fun a : ℝ × ℝ => ∫ φ in Ioo (-π) π,
      (a.1 ^ 2 * Real.sin a.2) • f (sphericalPoint a.1 a.2 φ)) (Ioi (0 : ℝ) ×ˢ Ioo 0 π) := by
    have h : Integrable (fun p : (ℝ × ℝ) × ℝ => (p.1.1 ^ 2 * Real.sin p.1.2) •
        f (sphericalPoint p.1.1 p.1.2 p.2))
        ((volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo 0 π)).prod (volume.restrict (Ioo (-π) π))) := by
      rw [Measure.prod_restrict]
      exact hbox
    exact h.integral_prod_left
  rw [integral_eq_sphericalBox]
  unfold sphericalBox
  refine (setIntegral_prod _ hbox).trans ?_
  exact setIntegral_prod _ hin

theorem integrableOn_spherical_polar_inner (f : Space → E) (hf : Integrable f) :
    IntegrableOn (fun q : (ℝ × ℝ) × ℝ => (q.1.1 ^ 2 * Real.sin q.2) • f (sphericalPoint q.1.1 q.2 q.1.2))
      ((Ioi (0 : ℝ) ×ˢ Ioo (-π) π) ×ˢ Ioo 0 π) := by
  rw [← swap_preimage_box]
  exact (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr
    ((integrable_iff_sphericalBox f).mp hf)

theorem integral_eq_spherical_polar_inner [CompleteSpace E] (f : Space → E) (hf : Integrable f) :
    ∫ y, f y = ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ∫ ϑ in Ioo 0 π,
      (q.1 ^ 2 * Real.sin ϑ) • f (sphericalPoint q.1 ϑ q.2) := by
  rw [integral_eq_sphericalBox]
  refine (swapEquiv_mp.setIntegral_preimage_emb swapEquiv.measurableEmbedding
    (fun p : (ℝ × ℝ) × ℝ => (p.1.1 ^ 2 * Real.sin p.1.2) • f (sphericalPoint p.1.1 p.1.2 p.2))
    sphericalBox).symm.trans ?_
  rw [swap_preimage_box]
  exact setIntegral_prod _ (integrableOn_spherical_polar_inner f hf)

theorem spherical_polar_slice_integrable (f : Space → E) (hf : Integrable f) :
    ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π)),
      IntegrableOn (fun ϑ => (q.1 ^ 2 * Real.sin ϑ) • f (sphericalPoint q.1 ϑ q.2)) (Ioo 0 π) := by
  have h : Integrable (fun q : (ℝ × ℝ) × ℝ => (q.1.1 ^ 2 * Real.sin q.2) • f (sphericalPoint q.1.1 q.2 q.1.2))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π)).prod (volume.restrict (Ioo 0 π))) := by
    rw [Measure.prod_restrict]
    exact integrableOn_spherical_polar_inner f hf
  exact h.prod_right_ae

theorem integral_eq_spherical_polar_interval [CompleteSpace E] (f : Space → E) (hf : Integrable f) :
    ∫ y, f y = ∫ q in Ioi (0 : ℝ) ×ˢ Ioo (-π) π, ∫ ϑ in (0 : ℝ)..π,
      (q.1 ^ 2 * Real.sin ϑ) • f (sphericalPoint q.1 ϑ q.2) := by
  rw [integral_eq_spherical_polar_inner f hf]
  refine setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioo) fun q _ => ?_
  rw [intervalIntegral.integral_of_le Real.pi_pos.le, integral_Ioc_eq_integral_Ioo]

theorem spherical_polar_slice_intervalIntegrable (f : Space → E) (hf : Integrable f) :
    ∀ᵐ q ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-π) π)),
      IntervalIntegrable (fun ϑ => (q.1 ^ 2 * Real.sin ϑ) • f (sphericalPoint q.1 ϑ q.2)) volume 0 π := by
  filter_upwards [spherical_polar_slice_integrable f hf] with q hq
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le Real.pi_pos.le, integrableOn_Ioc_iff_integrableOn_Ioo]
  exact hq

end Breakdown.PotentialShape
