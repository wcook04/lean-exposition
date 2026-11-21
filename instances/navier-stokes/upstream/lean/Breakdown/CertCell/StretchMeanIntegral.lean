import Breakdown.CertCell.BridgeStatements
import Breakdown.CertCell.TailFlipDecay
import Breakdown.FracCell.RelTrace
import Breakdown.Cert.CoerciveModeDerivative
import Breakdown.Cert.ProductBound
import Breakdown.Cert.ExtendedCoercivePassageStretch
import Breakdown.Cert.ExtendedCoerciveAbsorbStep

open scoped ENNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

namespace Internal.StretchMeanParts

open CellCert.CellFormula.Internal.RelTrace (cylF region lintegral_cyl measurable_cylF)

theorem flip_flip (y : Space) : flipPoint (flipPoint y) = y := by
  ext i
  fin_cases i <;> simp [flipPoint, unitVector]

theorem flip_two (y : Space) : flipPoint y 2 = -y 2 := by
  simp [flipPoint, unitVector]

theorem cylF_two (x : (ℝ × ℝ) × ℝ) : cylF x 2 = x.1.2 := by
  simp [cylF, CellCert.CellAnalysis.cylPoint]

theorem cylF_eq_rot (x : (ℝ × ℝ) × ℝ) : cylF x = axialRot x.2 (planePoint x.1) :=
  TailBand.Internal.FlipDecay.cylArg_eq x.1 x.2

theorem measurableSet_halfPlane : MeasurableSet CertCell.halfPlane :=
  measurableSet_Ioi.prod measurableSet_Ioi

theorem coord_two_null : (volume : Measure Space) {y | y 2 = 0} = 0 := by
  let L : Space →ₗ[ℝ] ℝ := (EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ)
  have hs : {y : Space | y 2 = 0} = (LinearMap.ker L : Set Space) := by
    ext y
    simp [L]
  rw [hs]
  refine Measure.addHaar_submodule volume _ fun h => ?_
  have : unitVector 2 ∈ LinearMap.ker L := by rw [h]; trivial
  simp [L, unitVector] at this

theorem lintegral_angle_shift (F : ℝ → ℝ≥0∞) (hF : Function.Periodic F (2 * Real.pi)) :
    ∫⁻ θ in Ioo (-Real.pi) Real.pi, F θ = ∫⁻ θ in Ioc 0 (2 * Real.pi), F θ := by
  have hT : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [setLIntegral_congr Ioo_ae_eq_Ioc]
  have h1 := isAddFundamentalDomain_Ioc hT (-Real.pi)
  have h2 := isAddFundamentalDomain_Ioc hT 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h1
  rw [zero_add] at h2
  refine h1.setLIntegral_eq h2 F fun g x => ?_
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.1 g.2
  change F ((g : ℝ) + x) = F x
  rw [← hn, add_comm]
  exact hF.zsmul n x

theorem lintegral_fold (R : Space ≃ₗᵢ[ℝ] Space) (hR : ∀ y, R y = flipPoint y)
    (g : Space → ℝ≥0∞) (hg : Measurable g) (hsym : ∀ᵐ y, g (flipPoint y) = g y) :
    ∫⁻ y, g y = 2 * ∫⁻ p in CertCell.halfPlane, ∫⁻ φ in Ioc 0 (2 * Real.pi),
      ENNReal.ofReal p.1 * g (axialRot φ (planePoint p)) := by
  have hc : Continuous (fun y : Space => y 2) := (EuclideanSpace.proj (2 : Fin 3)).continuous
  set U : Set Space := {y | 0 < y 2} with hUdef
  have hU : MeasurableSet U := measurableSet_lt measurable_const hc.measurable
  have hcompl : (Uᶜ : Set Space) =ᵐ[volume] {y : Space | y 2 < 0} := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (fun y hy => ?_) coord_two_null
      simp only [hUdef, mem_sdiff, mem_compl_iff, mem_ofPred_eq, not_lt] at hy ⊢
      exact le_antisymm hy.1 hy.2
    · refine measure_mono_null (fun y hy => ?_) measure_empty
      simp only [hUdef, mem_sdiff, mem_compl_iff, mem_ofPred_eq, not_lt, not_le] at hy
      exact absurd hy.2 (not_lt.2 hy.1.le)
  have hpre : R ⁻¹' {y : Space | y 2 < 0} = U := by
    ext y
    simp [hR, flip_two, hUdef]
  have hLint : ∫⁻ y in {y : Space | y 2 < 0}, g y = ∫⁻ y in U, g (R y) := by
    rw [← hpre]
    exact (R.measurePreserving.setLIntegral_comp_preimage_emb R.toHomeomorph.measurableEmbedding g _).symm
  have hsplit : ∫⁻ y, g y = 2 * ∫⁻ y in U, g y := by
    rw [← lintegral_add_compl g hU, setLIntegral_congr hcompl, hLint, two_mul]
    congr 1
    refine lintegral_congr_ae (ae_restrict_of_ae ?_)
    filter_upwards [hsym] with y hy
    rw [hR, hy]
  have hm : Measurable (fun x : (ℝ × ℝ) × ℝ => ENNReal.ofReal x.1.1 * U.indicator g (cylF x)) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul ((hg.indicator hU).comp measurable_cylF)
  have hreg : volume.restrict region = (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    rfl
  have hcyl : ∫⁻ y in U, g y = ∫⁻ q in Ioi (0 : ℝ) ×ˢ (univ : Set ℝ), ∫⁻ θ in Ioo (-Real.pi) Real.pi,
      ENNReal.ofReal q.1 * U.indicator g (cylF (q, θ)) := by
    rw [← lintegral_indicator hU, ← lintegral_cyl, hreg]
    exact lintegral_prod _ hm.aemeasurable
  have hinner : ∀ q : ℝ × ℝ, ∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal q.1 * U.indicator g (cylF (q, θ))
      = ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)).indicator (fun q => ∫⁻ θ in Ioc 0 (2 * Real.pi),
          ENNReal.ofReal q.1 * g (axialRot θ (planePoint q))) q := by
    intro q
    by_cases hq : 0 < q.2
    · have hq' : q ∈ ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := ⟨trivial, hq⟩
      rw [indicator_of_mem hq']
      have e1 : ∀ θ, U.indicator g (cylF (q, θ)) = g (axialRot θ (planePoint q)) := fun θ => by
        have hmem : cylF (q, θ) ∈ U := by
          show 0 < cylF (q, θ) 2
          rw [cylF_two]
          exact hq
        rw [indicator_of_mem hmem, cylF_eq_rot]
      simp_rw [e1]
      exact lintegral_angle_shift _ fun θ => by
        simp only [TailBand.Internal.FlipDecay.axialRot_add_period]
    · have hq' : q ∉ ((univ : Set ℝ) ×ˢ Ioi (0 : ℝ)) := fun h => hq h.2
      rw [indicator_of_notMem hq']
      have e0 : ∀ θ, U.indicator g (cylF (q, θ)) = 0 := fun θ => by
        refine indicator_of_notMem (fun h => hq ?_) g
        have h' : 0 < cylF (q, θ) 2 := h
        rwa [cylF_two] at h'
      simp [e0]
  rw [hsplit, hcyl]
  congr 1
  simp_rw [hinner]
  rw [setLIntegral_indicator (MeasurableSet.univ.prod measurableSet_Ioi), Set.prod_inter_prod,
    univ_inter, inter_univ]
  rfl

theorem measurable_orbit :
    Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (w.2.1, axialRot w.2.2 (planePoint w.1))) := by
  have e : (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (w.2.1, axialRot w.2.2 (planePoint w.1)))
      = fun w => (w.2.1, cylF (w.1, w.2.2)) := by
    funext w
    rw [cylF_eq_rot]
  rw [e]
  exact measurable_snd.fst.prodMk (measurable_cylF.comp (measurable_fst.prodMk measurable_snd.snd))

theorem lintegral_spacetime (R : Space ≃ₗᵢ[ℝ] Space) (hR : ∀ y, R y = flipPoint y)
    (h : ℝ × Space → ℝ≥0∞) (hh : Measurable h)
    (hsym : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y, h (σ, flipPoint y) = h (σ, y)) :
    ∫⁻ z, h z ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      = 2 * ∫⁻ w, ENNReal.ofReal w.1.1 * h (w.2.1, axialRot w.2.2 (planePoint w.1))
          ∂((volume.restrict CertCell.halfPlane).prod
            ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
  set F : (ℝ × ℝ) × (ℝ × ℝ) → ℝ≥0∞ :=
    fun w => ENNReal.ofReal w.1.1 * h (w.2.1, axialRot w.2.2 (planePoint w.1)) with hFdef
  have hFm : Measurable F := (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul (hh.comp measurable_orbit)
  have e1 : ∀ p : ℝ × ℝ, ∫⁻ s, F (p, s) ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod
      (volume.restrict (Ioc 0 (2 * Real.pi))))
      = ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ φ in Ioc 0 (2 * Real.pi), F (p, (τ, φ)) := fun p =>
    lintegral_prod _ (hFm.comp measurable_prodMk_left).aemeasurable
  have hsw : Measurable (fun x : (ℝ × ℝ) × ℝ => ∫⁻ φ in Ioc 0 (2 * Real.pi), F (x.1, (x.2, φ))) :=
    (hFm.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))).lintegral_prod_right'
  have hR1 : ∫⁻ w, F w ∂((volume.restrict CertCell.halfPlane).prod
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
      = ∫⁻ τ in Ioc (0 : ℝ) 1, ∫⁻ p in CertCell.halfPlane, ∫⁻ φ in Ioc 0 (2 * Real.pi), F (p, (τ, φ)) := by
    rw [lintegral_prod _ hFm.aemeasurable, lintegral_congr e1, lintegral_lintegral_swap hsw.aemeasurable]
  rw [lintegral_prod _ hh.aemeasurable, hR1,
    Measure.restrict_congr_set (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := 1)),
    ← lintegral_const_mul' _ _ (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)]
  refine lintegral_congr_ae ?_
  filter_upwards [hsym] with σ hσ
  exact lintegral_fold R hR (fun y => h (σ, y)) (hh.comp measurable_prodMk_left) hσ

theorem ae_orbit_pos :
    ∀ᵐ w ∂((volume.restrict CertCell.halfPlane).prod
      ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))),
      0 < w.1.1 ∧ 0 < w.1.2 := by
  rw [ae_iff]
  refine measure_mono_null (t := (CertCell.halfPlane)ᶜ ×ˢ univ) (fun w hw => ⟨fun h => hw h, trivial⟩) ?_
  rw [Measure.prod_prod, Measure.restrict_apply' measurableSet_halfPlane, compl_inter_self, measure_empty,
    zero_mul]

theorem qmp_orbit (R : Space ≃ₗᵢ[ℝ] Space) (hR : ∀ y, R y = flipPoint y) :
    Measure.QuasiMeasurePreserving (fun w : (ℝ × ℝ) × (ℝ × ℝ) => (w.2.1, axialRot w.2.2 (planePoint w.1)))
      ((volume.restrict CertCell.halfPlane).prod
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  refine ⟨measurable_orbit, Measure.AbsolutelyContinuous.mk fun s hs h0 => ?_⟩
  rw [Measure.map_apply measurable_orbit hs]
  have hΦ : MeasurePreserving (Prod.map id R) ((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) :=
    (MeasurePreserving.id (volume.restrict (Icc (0 : ℝ) 1))).prod R.measurePreserving
  have hi : Measurable (s.indicator (1 : ℝ × Space → ℝ≥0∞)) := measurable_one.indicator hs
  set h : ℝ × Space → ℝ≥0∞ := fun z => s.indicator 1 z + s.indicator 1 (Prod.map id R z) with hdef
  have hhm : Measurable h := hi.add (hi.comp hΦ.measurable)
  have hsym : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y, h (σ, flipPoint y) = h (σ, y) :=
    Filter.Eventually.of_forall fun σ => Filter.Eventually.of_forall fun y => by
      simp only [hdef, Prod.map, id, hR, flip_flip]
      rw [add_comm]
  have hzero : ∫⁻ z, h z ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume) = 0 := by
    rw [lintegral_add_left hi, lintegral_indicator_one hs, h0, zero_add,
      hΦ.lintegral_comp hi, lintegral_indicator_one hs, h0]
  rw [lintegral_spacetime R hR h hhm hsym] at hzero
  have hz := (mul_eq_zero.1 hzero).resolve_left two_ne_zero
  have hFm : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) =>
      ENNReal.ofReal w.1.1 * h (w.2.1, axialRot w.2.2 (planePoint w.1))) :=
    (ENNReal.measurable_ofReal.comp measurable_fst.fst).mul (hhm.comp measurable_orbit)
  rw [lintegral_eq_zero_iff hFm] at hz
  rw [measure_eq_zero_iff_ae_notMem]
  filter_upwards [hz, ae_orbit_pos] with w hw hw0 hmem
  rcases mul_eq_zero.1 hw with h1 | h1
  · rw [ENNReal.ofReal_eq_zero] at h1
    linarith [hw0.1]
  · have hm' : (w.2.1, axialRot w.2.2 (planePoint w.1)) ∈ s := hmem
    simp only [hdef, indicator_of_mem hm'] at h1
    simp at h1

theorem integral_spacetime (R : Space ≃ₗᵢ[ℝ] Space) (hR : ∀ y, R y = flipPoint y)
    (f : ℝ × Space → ℝ) (hf : Integrable f ((volume.restrict (Icc (0 : ℝ) 1)).prod volume))
    (hsym : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y, f (σ, flipPoint y) = f (σ, y)) :
    Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 * f (w.2.1, axialRot w.2.2 (planePoint w.1)))
        ((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) ∧
      ∫ z, f z ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
        = 2 * ∫ w, w.1.1 * f (w.2.1, axialRot w.2.2 (planePoint w.1))
          ∂((volume.restrict CertCell.halfPlane).prod
            ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
  have hq := qmp_orbit R hR
  set f' := hf.aestronglyMeasurable.mk f with hf'def
  have hf'm : Measurable f' := hf.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hff' : f =ᵐ[(volume.restrict (Icc (0 : ℝ) 1)).prod volume] f' := hf.aestronglyMeasurable.ae_eq_mk
  have hsym' : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y, f' (σ, flipPoint y) = f' (σ, y) := by
    filter_upwards [Measure.ae_ae_of_ae_prod hff', hsym] with σ h1 h2
    have h3 : ∀ᵐ y, f (σ, flipPoint y) = f' (σ, flipPoint y) := by
      have := R.measurePreserving.quasiMeasurePreserving.ae h1
      simpa only [hR] using this
    filter_upwards [h1, h2, h3] with y a b c
    rw [← a, ← c, b]
  have hKK : (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 * f (w.2.1, axialRot w.2.2 (planePoint w.1)))
      =ᵐ[(volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))]
      (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1))) := by
    filter_upwards [hq.ae hff'] with w hw
    rw [hw]
  have hKm : Measurable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1))) :=
    measurable_fst.fst.mul (hf'm.comp measurable_orbit)
  have hn : ∫⁻ z, ‖f' z‖ₑ ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      = 2 * ∫⁻ w, ENNReal.ofReal w.1.1 * ‖f' (w.2.1, axialRot w.2.2 (planePoint w.1))‖ₑ
        ∂((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) :=
    lintegral_spacetime R hR (fun z => ‖f' z‖ₑ) hf'm.enorm (by
      filter_upwards [hsym'] with σ hσ
      filter_upwards [hσ] with y hy
      rw [hy])
  have hfin : ∫⁻ z, ‖f' z‖ₑ ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume) < ⊤ :=
    (hf.congr hff').hasFiniteIntegral
  have hKi : Integrable (fun w : (ℝ × ℝ) × (ℝ × ℝ) => w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1)))
      ((volume.restrict CertCell.halfPlane).prod
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
    refine ⟨hKm.aestronglyMeasurable, ?_⟩
    show ∫⁻ w : (ℝ × ℝ) × (ℝ × ℝ), ‖w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1))‖ₑ ∂_ < ⊤
    have hnorm : ∫⁻ w : (ℝ × ℝ) × (ℝ × ℝ), ‖w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1))‖ₑ
        ∂((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
        = ∫⁻ w : (ℝ × ℝ) × (ℝ × ℝ), ENNReal.ofReal w.1.1 * ‖f' (w.2.1, axialRot w.2.2 (planePoint w.1))‖ₑ
          ∂((volume.restrict CertCell.halfPlane).prod
            ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
      refine lintegral_congr_ae ?_
      filter_upwards [ae_orbit_pos] with w hw
      rw [enorm_mul, Real.enorm_of_nonneg hw.1.le]
    rw [hnorm]
    rw [hn] at hfin
    exact lt_of_le_of_lt (le_mul_of_one_le_left' (by norm_num)) hfin
  refine ⟨hKi.congr hKK.symm, ?_⟩
  have hsp : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y,
      ENNReal.ofReal (f' (σ, flipPoint y)) = ENNReal.ofReal (f' (σ, y)) := by
    filter_upwards [hsym'] with σ hσ
    filter_upwards [hσ] with y hy
    rw [hy]
  have hsm : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y,
      ENNReal.ofReal (-f' (σ, flipPoint y)) = ENNReal.ofReal (-f' (σ, y)) := by
    filter_upwards [hsym'] with σ hσ
    filter_upwards [hσ] with y hy
    rw [hy]
  have hp : ∫⁻ z, ENNReal.ofReal (f' z) ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      = 2 * ∫⁻ w, ENNReal.ofReal w.1.1 * ENNReal.ofReal (f' (w.2.1, axialRot w.2.2 (planePoint w.1)))
        ∂((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) :=
    lintegral_spacetime R hR (fun z => ENNReal.ofReal (f' z)) (ENNReal.measurable_ofReal.comp hf'm) hsp
  have hm : ∫⁻ z, ENNReal.ofReal (-f' z) ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      = 2 * ∫⁻ w, ENNReal.ofReal w.1.1 * ENNReal.ofReal (-f' (w.2.1, axialRot w.2.2 (planePoint w.1)))
        ∂((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) :=
    lintegral_spacetime R hR (fun z => ENNReal.ofReal (-f' z)) (ENNReal.measurable_ofReal.comp hf'm.neg) hsm
  have ep : ∫⁻ w, ENNReal.ofReal (w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1)))
      ∂((volume.restrict CertCell.halfPlane).prod
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
      = ∫⁻ w, ENNReal.ofReal w.1.1 * ENNReal.ofReal (f' (w.2.1, axialRot w.2.2 (planePoint w.1)))
        ∂((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_orbit_pos] with w hw
    rw [ENNReal.ofReal_mul hw.1.le]
  have em : ∫⁻ w, ENNReal.ofReal (-(w.1.1 * f' (w.2.1, axialRot w.2.2 (planePoint w.1))))
      ∂((volume.restrict CertCell.halfPlane).prod
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))))
      = ∫⁻ w, ENNReal.ofReal w.1.1 * ENNReal.ofReal (-f' (w.2.1, axialRot w.2.2 (planePoint w.1)))
        ∂((volume.restrict CertCell.halfPlane).prod
          ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))) := by
    refine lintegral_congr_ae ?_
    filter_upwards [ae_orbit_pos] with w hw
    rw [← ENNReal.ofReal_mul hw.1.le, mul_neg]
  rw [integral_congr_ae hff', integral_congr_ae hKK,
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part (hf.congr hff'),
    integral_eq_lintegral_pos_part_sub_lintegral_neg_part hKi, hp, hm, ep, em,
    ENNReal.toReal_mul, ENNReal.toReal_mul]
  simp only [ENNReal.toReal_ofNat]
  ring

theorem abs_stretch_le {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW D) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) :
    |CoerciveWeak.stretchFormWith W HW v G σ y|
      ≤ 729 * |D| * (6 * matSq (G σ y) + ‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 6) := by
  have e : CoerciveWeak.stretchFormWith W HW v G σ y
      = Coercive.Internal.PassageCommon.stretchPair (G σ y) (G σ y) (fderiv ℝ (W σ) y) (HW σ y)
        (v σ y) (v σ y) := rfl
  rw [e]
  have hb := Coercive.Internal.PassageCommon.abs_stretchPair_le (G σ y) (G σ y) (fderiv ℝ (W σ) y)
    (HW σ y) (v σ y) (v σ y)
  have h1 := CoerciveWeak.Internal.PassageStretch.norm_fderiv_le_abs hW σ y
  have h2 := (hW.decay σ y).2.2
  have hf := Coercive.Internal.PassageCommon.norm_sq_le_matSq (G σ y)
  set gg := ‖G σ y‖
  set dd := ‖fderiv ℝ (W σ) y‖
  set hh := ‖HW σ y‖
  set vv := ‖v σ y‖
  set r := 1 + ‖y‖ with hr
  have hr0 : 0 < r := by rw [hr]; linarith [norm_nonneg y]
  have g0 : 0 ≤ gg := norm_nonneg _
  have d0 : 0 ≤ dd := norm_nonneg _
  have h0 : 0 ≤ hh := norm_nonneg _
  have v0 : 0 ≤ vv := norm_nonneg _
  have hh3 : hh * r ^ 3 ≤ |D| := ((le_div_iff₀ (by positivity)).1 h2).trans (le_abs_self D)
  set q := vv / r ^ 3 with hq
  have q0 : 0 ≤ q := div_nonneg v0 (by positivity)
  have hvq : vv = q * r ^ 3 := by rw [hq]; field_simp
  have hhv : hh * vv ≤ |D| * q := by
    rw [hvq, show hh * (q * r ^ 3) = (hh * r ^ 3) * q by ring]
    exact mul_le_mul_of_nonneg_right hh3 q0
  have t1 : dd * gg * gg ≤ |D| * (gg * gg) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right h1 (by positivity)
  have t2 : hh * vv * gg ≤ |D| * q * gg := mul_le_mul_of_nonneg_right hhv g0
  have hq2 : q ^ 2 = vv ^ 2 / r ^ 6 := by rw [hq, div_pow, ← pow_mul]
  have hD0 := abs_nonneg D
  have key : 2 * q * gg ≤ gg ^ 2 + q ^ 2 := by nlinarith [sq_nonneg (gg - q)]
  have k2 := mul_le_mul_of_nonneg_left key hD0
  refine hb.trans ?_
  have s1 : 729 * dd * gg * gg + 729 * hh * vv * gg + 729 * hh * gg * vv
      ≤ 729 * |D| * (2 * gg ^ 2 + q ^ 2) := by
    nlinarith [t1, t2, k2]
  refine s1.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  rw [← hq2]
  nlinarith [hf]

theorem sixth_weight_finite {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∫⁻ σ in Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 6) < ⊤ := by
  set K : ℝ≥0∞ := (∫⁻ y : Space, ENNReal.ofReal ((1 + ‖y‖) ^ (-(9 : ℝ)))) ^ (1 / (3 / 2 : ℝ)) with hKdef
  have hK : K < ⊤ := by
    refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
    refine (Integrable.lintegral_lt_top (integrable_one_add_norm ?_)).ne
    rw [finrank_euclideanSpace_fin]
    norm_num
  have hconj : (3 : ℝ).HolderConjugate (3 / 2) := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  have hvm := hv.measurable_velocity
  rw [Measure.volume_eq_prod] at hvm
  have hle : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)),
      ∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 6)
        ≤ (∫⁻ y, ENNReal.ofReal (‖v σ y‖ ^ 6)) ^ (1 / (3 : ℝ)) * K := by
    filter_upwards [ae_restrict_of_ae hvm.prodMk_left] with σ hσ
    have hF : AEMeasurable (fun y => ENNReal.ofReal (‖v σ y‖ ^ 2)) volume :=
      (hσ.norm.aemeasurable.pow_const 2).ennreal_ofReal
    have hc : Continuous (fun y : Space => (1 + ‖y‖) ^ (-(6 : ℝ))) :=
      Continuous.rpow_const (continuous_const.add continuous_norm) fun y =>
        Or.inl (by linarith [norm_nonneg y])
    have hG : AEMeasurable (fun y : Space => ENNReal.ofReal ((1 + ‖y‖) ^ (-(6 : ℝ)))) volume :=
      hc.measurable.ennreal_ofReal.aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq volume hconj hF hG
    have e1 : ∀ y : Space, ENNReal.ofReal (‖v σ y‖ ^ 2 / (1 + ‖y‖) ^ 6)
        = ((fun y => ENNReal.ofReal (‖v σ y‖ ^ 2)) * fun y : Space => ENNReal.ofReal ((1 + ‖y‖) ^ (-(6 : ℝ)))) y := by
      intro y
      have hy : (0 : ℝ) < 1 + ‖y‖ := by linarith [norm_nonneg y]
      simp only [Pi.mul_apply]
      rw [← ENNReal.ofReal_mul (by positivity), Real.rpow_neg hy.le,
        show (6 : ℝ) = ((6 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, div_eq_mul_inv]
    have e2 : ∀ y : Space, ENNReal.ofReal (‖v σ y‖ ^ 2) ^ (3 : ℝ) = ENNReal.ofReal (‖v σ y‖ ^ 6) := by
      intro y
      rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num),
        show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast, ← pow_mul]
    have e3 : ∀ y : Space, ENNReal.ofReal ((1 + ‖y‖) ^ (-(6 : ℝ))) ^ (3 / 2 : ℝ)
        = ENNReal.ofReal ((1 + ‖y‖) ^ (-(9 : ℝ))) := by
      intro y
      have hy : (0 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
      rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hy _) (by norm_num), ← Real.rpow_mul hy]
      norm_num
    rw [lintegral_congr e1]
    refine hH.trans (le_of_eq ?_)
    rw [lintegral_congr e2, lintegral_congr e3]
  refine lt_of_le_of_lt (lintegral_mono_ae hle) ?_
  rw [lintegral_mul_const' _ _ hK.ne]
  exact ENNReal.mul_lt_top (TailBand.velocitySixthSquareIntegral _ _ _ _ _ _ hv) hK

theorem continuous_matSq : Continuous (fun A : Space →L[ℝ] Space => matSq A) := by
  unfold matSq
  fun_prop

theorem enorm_stretch_le {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW D) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (z : ℝ × Space) :
    ‖CoerciveWeak.stretchFormWith W HW v G z.1 z.2‖ₑ
      ≤ ENNReal.ofReal (729 * |D|) * (6 * ENNReal.ofReal (matSq (G z.1 z.2))
        + ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 6)) := by
  have hc0 : 0 ≤ 729 * |D| := by positivity
  have hy : (0 : ℝ) < 1 + ‖z.2‖ := by linarith [norm_nonneg z.2]
  have hfr : 0 ≤ matSq (G z.1 z.2) := by
    unfold matSq
    positivity
  rw [Real.enorm_eq_ofReal_abs]
  refine (ENNReal.ofReal_le_ofReal (abs_stretch_le hW v G z.1 z.2)).trans (le_of_eq ?_)
  rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_add (by positivity) (by positivity),
    ENNReal.ofReal_mul (p := 6) (by norm_num), ENNReal.ofReal_ofNat]

theorem stretch_integrable {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW D) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hv : IsPerturbation Γ P v G H g) :
    Integrable (fun z : ℝ × Space => CoerciveWeak.stretchFormWith W HW v G z.1 z.2)
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
  have hμ : (volume.restrict (Icc (0 : ℝ) 1)).prod (volume : Measure Space)
      = (volume : Measure (ℝ × Space)).restrict (Icc (0 : ℝ) 1 ×ˢ univ) := by
    rw [Measure.restrict_prod_eq_prod_univ, Measure.volume_eq_prod]
  have hm : AEMeasurable (fun z : ℝ × Space => CoerciveWeak.stretchFormWith W HW v G z.1 z.2) volume :=
    CoerciveWeak.Internal.AbsorbStep.aem_stretchFormWith (W := W) (v := v) (G := G) (HW := HW) hW hv.measurable_velocity hv.measurable_gradient
  have hfs := continuous_matSq
  have hA : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (matSq (G z.1 z.2)))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ]
    exact (hfs.comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable.ennreal_ofReal.restrict
  have hB : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 6))
      ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := by
    rw [hμ]
    have hr : Continuous (fun z : ℝ × Space => (1 + ‖z.2‖) ^ 6) := by fun_prop
    exact ((hv.measurable_velocity.norm.aemeasurable.pow_const 2).div hr.aemeasurable).ennreal_ofReal.restrict
  refine ⟨by rw [hμ]; exact hm.aestronglyMeasurable.restrict, ?_⟩
  have hpt := enorm_stretch_le hW v G
  have hfA : ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2)) ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume) < ⊤ := by
    rw [lintegral_prod _ hA]
    exact hv.gradient_finite
  have hfB : ∫⁻ z, ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 6)
      ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume) < ⊤ := by
    rw [lintegral_prod _ hB]
    exact sixth_weight_finite hv
  have hbound : ∫⁻ z, ‖CoerciveWeak.stretchFormWith W HW v G z.1 z.2‖ₑ
      ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
      ≤ ENNReal.ofReal (729 * |D|) * (6 * ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2))
          ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
        + ∫⁻ z, ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 6)
          ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)) := by
    refine (lintegral_mono hpt).trans (le_of_eq ?_)
    rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left' (hA.const_mul 6),
      lintegral_const_mul' (6 : ℝ≥0∞) _ (by simp)]
  have hlt : ENNReal.ofReal (729 * |D|) * (6 * ∫⁻ z, ENNReal.ofReal (matSq (G z.1 z.2))
          ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)
        + ∫⁻ z, ENNReal.ofReal (‖v z.1 z.2‖ ^ 2 / (1 + ‖z.2‖) ^ 6)
          ∂((volume.restrict (Icc (0 : ℝ) 1)).prod volume)) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.add_lt_top.2 ⟨ENNReal.mul_lt_top (by simp) hfA, hfB⟩)
  exact lt_of_le_of_lt hbound hlt

theorem stretch_flip_ae (hF : StretchFlipHolds) {W : ℝ → Space → Space}
    {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ} (hI : IsFlipInvariantModel W HW)
    (hW : CoerciveWeak.IsWeakSecondDerivState W HW D) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (γ : Symmetry) (hγ : γ ∈ Γ)
    (hR : ∀ y, γ.1 y = flipPoint y) (hγ2 : γ.2 = 0) :
    ∀ᵐ σ, ∀ᵐ y, CoerciveWeak.stretchFormWith W HW v G σ (flipPoint y)
      = CoerciveWeak.stretchFormWith W HW v G σ y := by
  have hRs : ∀ x, γ.1.symm x = flipPoint x := fun x => by
    rw [LinearIsometryEquiv.symm_apply_eq, hR, flip_flip]
  have hinv := hv.invariant γ hγ
  rw [Measure.volume_eq_prod] at hinv
  have hvσ := Measure.ae_ae_of_ae_prod hinv
  have hdiff : ∀ σ, Differentiable ℝ (W σ) := fun σ =>
    (hW.smooth.differentiable (by norm_num)).comp ((differentiable_const σ).prodMk differentiable_id)
  filter_upwards [hvσ, hv.weak_gradient] with σ hσv hσG
  have hσv' : ∀ᵐ y, v σ (flipPoint y) = flipPoint (v σ y) := by
    filter_upwards [hσv] with y hy
    simpa [hγ2, hR] using hy
  have hG' : ∀ᵐ y, ∀ a, G σ (flipPoint y) (flipPoint a) = flipPoint (G σ y a) := by
    set g' : Space → (Space →L[ℝ] Space) := fun y =>
      (γ.1.symm.toContinuousLinearEquiv : Space →L[ℝ] Space).comp
        ((G σ (γ.1 y)).comp (γ.1.toContinuousLinearEquiv : Space →L[ℝ] Space)) with hg'
    have hrot : IsWeakGradient (fun y => γ.1.symm (v σ (γ.1 y))) g' :=
      Coercive.ModeDerivative.Internal.weakGradient_rotate hσG γ.1 (fun _ => rfl) (fun _ _ => rfl)
    have hfe : (fun y => γ.1.symm (v σ (γ.1 y))) =ᵐ[volume] v σ := by
      filter_upwards [hσv'] with y hy
      rw [hR, hy, hRs, flip_flip]
    have h2 := Coercive.ModeDerivative.Internal.isWeakGradient_congr_ae hrot hfe Filter.EventuallyEq.rfl
    have hu := Cert.Internal.ProductBound.weakGradient_unique hσG h2
    filter_upwards [hu] with y hy a
    have h3 : G σ y a = g' y a := by rw [hy]
    have h4 : g' y a = flipPoint (G σ (flipPoint y) (flipPoint a)) := by
      show γ.1.symm (G σ (γ.1 y) (γ.1 a)) = _
      rw [hRs, hR, hR]
    rw [h3, h4, flip_flip]
  filter_upwards [hσv', hG'] with y h1 h2
  exact hF W HW hI hdiff v G σ y h1 h2

end Internal.StretchMeanParts

open Internal.StretchMeanParts in
theorem stretchMeanIntegral (hV : VelocitySixthIntegralHolds) (hA : RotationAverageHolds)
    (hF : StretchFlipHolds) : StretchMeanIntegralHolds := by
  intro k C nE nM D D₀ hM hI hW P v G H g hv
  obtain ⟨γ, hγΓ, hγ1, hγ2⟩ := hM.flip
  set f : ℝ × Space → ℝ := fun z => CoerciveWeak.stretchFormWith D.given D.givenHess v G z.1 z.2
    with hfdef
  have hfi : Integrable f ((volume.restrict (Icc (0 : ℝ) 1)).prod volume) := stretch_integrable hW hv
  have hsym : ∀ᵐ σ ∂(volume.restrict (Icc (0 : ℝ) 1)), ∀ᵐ y, f (σ, flipPoint y) = f (σ, y) :=
    ae_restrict_of_ae (stretch_flip_ae hF hI hW hv γ hγΓ hγ1 hγ2)
  obtain ⟨hKi, hKe⟩ := integral_spacetime γ.1 hγ1 f hfi hsym
  have h2pi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hfib : ∀ᵐ p ∂(volume.restrict CertCell.halfPlane),
      ∫ s, (p, s).1.1 * f ((p, s).2.1, axialRot (p, s).2.2 (planePoint (p, s).1))
        ∂((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi))))
        = 2 * Real.pi * (D.meanStretch v G p * p.1) := by
    filter_upwards [hKi.prod_right_ae, ae_restrict_mem measurableSet_halfPlane] with p hp hpP
    have hp1 : 0 < p.1 := hpP.1
    have hint : Integrable (fun s : ℝ × ℝ => f (s.1, axialRot s.2 (planePoint p)))
        ((volume.restrict (Ioc (0 : ℝ) 1)).prod (volume.restrict (Ioc 0 (2 * Real.pi)))) := by
      refine (hp.const_mul (p.1)⁻¹).congr (Filter.Eventually.of_forall fun s => ?_)
      exact inv_mul_cancel_left₀ hp1.ne' _
    have hms : D.meanStretch v G p = (1 / (2 * Real.pi)) *
        ∫ τ in Ioc (0 : ℝ) 1, ∫ φ in Ioc 0 (2 * Real.pi), f (τ, axialRot φ (planePoint p)) := by
      simp only [CellLayerData.meanStretch, intervalIntegral.integral_of_le zero_le_one,
        intervalIntegral.integral_of_le h2pi.le]
      rfl
    rw [integral_const_mul, integral_prod _ hint, hms]
    field_simp
  have hL := hKi.integral_prod_left
  have hI2 : IntegrableOn (fun p => D.meanStretch v G p * p.1) CertCell.halfPlane := by
    refine (hL.const_mul (1 / (2 * Real.pi))).congr ?_
    filter_upwards [hfib] with p hp
    rw [hp]
    field_simp
  refine ⟨hfi, hI2, ?_⟩
  rw [integral_prod f hfi] at hKe
  change (∫ σ in Icc (0 : ℝ) 1, ∫ y, f (σ, y)) = _
  rw [hKe, integral_prod _ hKi, integral_congr_ae hfib, integral_const_mul]
  ring

end Bridge

end CertCell

end Breakdown
