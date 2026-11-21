import Breakdown.CertCell.AssemblyTiedParts
import Breakdown.CertCell.AssemblyFlipAverage
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.Cert.CoerciveFrequencySeminormBoundSub

open MeasureTheory Filter
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal.PressureFlip

open Bridge.Internal.ModeTermFlip (flipIsometryEquiv flipPoint_flipPoint frameSign_mul_self)
open Bridge.Internal.ModeFlip (flipPoint_unitVector flipPoint_apply)
open CertCell.Internal.RowShares (inner_flipPoint flipPoint_add flipPoint_smul)
open Internal.FlipAverageRight (flipConj flipPair flipPoint_sub flipPoint_sum integral_flip fderiv_field_flip
  transportTest transportTest_conj)

theorem flipConj_testVector {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    IsSpaceTimeTestVector (flipConj φ) := by
  refine ⟨?_, ?_⟩
  · exact flipIsometryEquiv.contDiff.comp
      (hφ.1.comp (contDiff_fst.prodMk (flipIsometryEquiv.contDiff.comp contDiff_snd)))
  · have h1 := hφ.2.comp_homeomorph ((Homeomorph.refl ℝ).prodCongr flipIsometryEquiv.toHomeomorph)
    exact h1.comp_left (g := flipIsometryEquiv) (map_zero _)

theorem derivative_pairing_conj {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g)
    (hv : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2))
    {φ : ℝ → Space → Space} (hφ : IsSpaceTimeTestVector φ) :
    ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2)
      = ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (φ z.1 z.2) := by
  rw [← hp.transport _ (flipConj_testVector hφ), ← hp.transport φ hφ]
  have e : (fun z : ℝ × Space => inner ℝ (v z.1 z.2) (transportTest P (flipConj φ) z))
      =ᵐ[volume] fun z => inner ℝ (v (flipPair z).1 (flipPair z).2) (transportTest P φ (flipPair z)) := by
    filter_upwards [hv] with z hz
    rw [transportTest_conj, ← inner_flipPoint, ← hz]
    rfl
  exact (integral_congr_ae e).trans (integral_flip (fun z => inner ℝ (v z.1 z.2) (transportTest P φ z)))

theorem locallyIntegrable_flipPair {f : ℝ × Space → Space} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun z => flipPoint (f (flipPair z))) volume := by
  let e : ℝ × Space ≃ₜ ℝ × Space := (Homeomorph.refl ℝ).prodCongr flipIsometryEquiv.toHomeomorph
  have hM : MeasurePreserving e volume volume :=
    Cert.Internal.ExtendedInvariance.measurePreserving_rot flipIsometryEquiv
  have h1 : LocallyIntegrable (fun z => f (flipPair z)) volume := by
    refine locallyIntegrable_iff.2 fun K hK => ?_
    have h2 : IntegrableOn f (e '' K) volume := hf.integrableOn_isCompact (hK.image e.continuous)
    have h3 := (hM.integrableOn_comp_preimage e.measurableEmbedding).2 h2
    exact h3.mono_set (Set.subset_preimage_image e K)
  refine h1.mono (flipIsometryEquiv.continuous.comp_aestronglyMeasurable h1.aestronglyMeasurable)
    (Eventually.of_forall fun z => ?_)
  exact le_of_eq (flipIsometryEquiv.norm_map _)

theorem derivative_flip {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g)
    (hv : ∀ᵐ z : ℝ × Space, v z.1 (flipPoint z.2) = flipPoint (v z.1 z.2)) :
    ∀ᵐ z : ℝ × Space, g z.1 (flipPoint z.2) = flipPoint (g z.1 z.2) := by
  have hgl := Coercive.FrequencySeminorm.Internal.derivative_locallyIntegrable hp
  have hcl := locallyIntegrable_flipPair hgl
  have hloc : LocallyIntegrable (fun z : ℝ × Space => g z.1 z.2 - flipPoint (g z.1 (flipPoint z.2))) volume :=
    hgl.sub hcl
  have hpair : ∀ φ, IsSpaceTimeTestVector φ →
      ∫ z : ℝ × Space, inner ℝ (g z.1 z.2 - flipPoint (g z.1 (flipPoint z.2))) (φ z.1 z.2) = 0 := by
    intro φ hφ
    have hφc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφ.1.continuous
    have i1 := Coercive.FrequencyBound.Internal.integrable_inner_of_locallyIntegrable hgl hφc hφ.2
    have i2 := Coercive.FrequencyBound.Internal.integrable_inner_of_locallyIntegrable hcl hφc hφ.2
    have e2 : ∫ z : ℝ × Space, inner ℝ (flipPoint (g z.1 (flipPoint z.2))) (φ z.1 z.2)
        = ∫ z : ℝ × Space, inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2) := by
      rw [← integral_flip (fun z => inner ℝ (g z.1 z.2) (flipConj φ z.1 z.2))]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [flipPair, flipConj, flipPoint_flipPoint]
      exact inner_flipPoint _ _
    have i2' : Integrable (fun z : ℝ × Space => inner ℝ (flipPoint (g z.1 (flipPoint z.2))) (φ z.1 z.2)) := i2
    simp only [inner_sub_left]
    rw [integral_sub i1 i2', e2, derivative_pairing_conj hp hv hφ, sub_self]
  have hz : ∀ᵐ z : ℝ × Space, g z.1 z.2 - flipPoint (g z.1 (flipPoint z.2)) = 0 := by
    refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc fun ψ hψ hψc => ?_
    have hint := hloc.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    have hc : ∀ i : Fin 3, inner ℝ (∫ z : ℝ × Space, ψ z • (g z.1 z.2 - flipPoint (g z.1 (flipPoint z.2))))
        (unitVector i) = 0 := by
      intro i
      rw [real_inner_comm, ← integral_inner hint]
      have hφ : IsSpaceTimeTestVector (fun σ y => ψ (σ, y) • unitVector i) :=
        ⟨hψ.smul contDiff_const, hψc.smul_right⟩
      refine Eq.trans (integral_congr_ae (Eventually.of_forall fun z => ?_)) (hpair _ hφ)
      simp only [real_inner_smul_right]
      rw [real_inner_comm]
    ext i
    have h := hc i
    simpa [unitVector, EuclideanSpace.inner_single_right] using h
  filter_upwards [hz] with z hz
  have h := sub_eq_zero.1 hz
  rw [h, flipPoint_flipPoint]

theorem curlVec_conj {A A' : Space →L[ℝ] Space} (h : ∀ u, A' u = flipPoint (A (flipPoint u))) :
    curlVec A' = flipPoint (curlVec A) := by
  have hc : ∀ j l : Fin 3, A' (unitVector j) l = frameSign l * frameSign j * A (unitVector j) l := by
    intro j l
    rw [h, flipPoint_apply, flipPoint_unitVector, map_smul, PiLp.smul_apply, smul_eq_mul]
    ring
  ext i
  rw [flipPoint_apply]
  simp only [curlVec, hc]
  fin_cases i <;> simp [Fin.sum_univ_three, alternatingSymbol, unitVector, frameSign] <;> ring

theorem crossVec_conj (u w : Space) : CellCalculus.crossVec (flipPoint u) (flipPoint w) = flipPoint (CellCalculus.crossVec u w) := by
  ext i
  rw [flipPoint_apply]
  simp only [CellCalculus.crossVec, flipPoint_apply]
  fin_cases i <;> simp [Fin.sum_univ_three, alternatingSymbol, unitVector, frameSign] <;> ring

theorem secondTrace_conj {A A' : Space →L[ℝ] Space →L[ℝ] Space}
    (h : ∀ u u', A' u u' = flipPoint (A (flipPoint u) (flipPoint u'))) :
    secondDerivTrace A' = flipPoint (secondDerivTrace A) := by
  unfold secondDerivTrace
  rw [flipPoint_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [h, flipPoint_unitVector]
  simp only [map_smul, FunLike.coe_smul, Pi.smul_apply, smul_smul, frameSign_mul_self, one_smul]

theorem couplingField_conj {W v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} {σ : ℝ} {y : Space}
    (hW : ∀ σ y, W σ (flipPoint y) = flipPoint (W σ y)) (hv : v σ (flipPoint y) = flipPoint (v σ y))
    (hG : ∀ u, G σ (flipPoint y) u = flipPoint (G σ y (flipPoint u))) :
    CellCalculus.couplingField W v G σ (flipPoint y) = flipPoint (CellCalculus.couplingField W v G σ y) := by
  have hD : ∀ u, fderiv ℝ (W σ) (flipPoint y) u = flipPoint (fderiv ℝ (W σ) y (flipPoint u)) := by
    intro u
    have e := fderiv_field_flip (hW σ) y (flipPoint u)
    rwa [flipPoint_flipPoint] at e
  unfold CellCalculus.couplingField CellCalculus.vorticityOf
  rw [curlVec_conj hG, curlVec_conj hD, hW, hv, crossVec_conj, crossVec_conj, flipPoint_add]

theorem flipAverage_conj (F : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    flipAverage F σ (flipPoint y) = flipPoint (flipAverage F σ y) := by
  unfold flipAverage
  rw [flipPoint_smul, flipPoint_add, flipPoint_flipPoint, flipPoint_flipPoint, add_comm]

end Internal.PressureFlip

open Internal.PressureFlip Internal.FlipAverageRight CertCell.Internal.RowShares in
theorem chosenPressureFlip_holds : ChosenPressureFlipHolds := by
  intro k C nE nM D hD q hq x
  have hvGH := Bridge.Internal.PlaneDataFlip.ae_field_flip x.perturbation hD.mode_class.flip
  have hg := derivative_flip x.perturbation (hvGH.mono fun z hz => hz.1)
  have hb : ∀ i, ∀ᵐ z : ℝ × Space,
      D.cert.actuator i z.1 (flipPoint z.2) = flipPoint (D.cert.actuator i z.1 z.2) := fun i => by
    obtain ⟨S, hS⟩ := hD.actuators i
    exact hS.invariant.mono fun z hz => hz.2
  filter_upwards [hvGH, hg, ae_all_iff.2 hb] with z h1 h2 h3
  obtain ⟨hv, hG, hH⟩ := h1
  unfold chosenPressure
  simp only [flipAverage_conj, h2, secondTrace_conj hH, couplingField_conj hD.flip_model.field_flip hv hG, h3,
    flipPoint_sub, flipPoint_add, flipPoint_sum, flipPoint_smul]

end Assembly

end CertCell

end Breakdown
