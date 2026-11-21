import Breakdown.Cert.ExtendedCoerciveMinorant
import Breakdown.Cert.ExtendedCoercivePieceDensityEnvelope
import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionParts
import Breakdown.Cert.CoerciveSmoothPieceEpsCompressionSymbolDefs
import Breakdown.Cert.CoercivePieceAbsorbMeasure
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoercivePieceField

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CoerciveWeak

namespace Internal.PieceEpsSymbolBound

open Coercive Coercive.PieceField.Internal

def symbolEntry (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (h : HarmonicBounds) (z : ℝ × Space)
    (τ φ : ℝ) (i j : Fin 3) : ℂ :=
  curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
    + ∑ α ∈ h.harmonics.erase 0, Coercive.Internal.SmoothPieceEpsCompression.torusPhase α τ φ
      * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j)

def symbolNormSq (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (h : HarmonicBounds) (z : ℝ × Space)
    (τ φ : ℝ) (u : Fin 3 → ℂ) : ℝ :=
  cnormSq (fun i => ∑ j, symbolEntry HW h z τ φ i j * u j)

theorem cnormSq_nonneg_of (u : Fin 3 → ℂ) : 0 ≤ cnormSq u :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem eq_zero_of_cnormSq_eq_zero {u : Fin 3 → ℂ} (hu : cnormSq u = 0) : u = 0 := by
  funext b
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun b _ => sq_nonneg ‖u b‖)).1 hu b (Finset.mem_univ b)
  simpa using h

theorem torusPhase_shift (α : ℤ × ℤ) (τ φ : ℝ) (n k : ℤ) :
    Coercive.Internal.SmoothPieceEpsCompression.torusPhase α (τ + n) (φ + k * (2 * Real.pi))
      = Coercive.Internal.SmoothPieceEpsCompression.torusPhase α τ φ := by
  unfold Coercive.Internal.SmoothPieceEpsCompression.torusPhase
  have e : (((2 * Real.pi * α.1 * (τ + n) + α.2 * (φ + k * (2 * Real.pi)) : ℝ) : ℂ) * Complex.I)
      = (((2 * Real.pi * α.1 * τ + α.2 * φ : ℝ) : ℂ) * Complex.I)
        + ((α.1 * n + α.2 * k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem symbolNormSq_shift (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (h : HarmonicBounds)
    (z : ℝ × Space) (τ φ : ℝ) (n k : ℤ) (u : Fin 3 → ℂ) :
    symbolNormSq HW h z (τ + n) (φ + k * (2 * Real.pi)) u = symbolNormSq HW h z τ φ u := by
  unfold symbolNormSq symbolEntry
  simp only [torusPhase_shift]

theorem continuous_symbolNormSq (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (h : HarmonicBounds)
    (z : ℝ × Space) :
    Continuous (fun x : ℝ × ℝ × (Fin 3 → ℂ) => symbolNormSq HW h z x.1 x.2.1 x.2.2) := by
  unfold symbolNormSq symbolEntry Coercive.Internal.SmoothPieceEpsCompression.torusPhase
  refine Coercive.Internal.FieldModes.continuous_cnormSq.comp (continuous_pi fun i => ?_)
  fun_prop

theorem continuous_symbolNormSq_angle (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (h : HarmonicBounds) (z : ℝ × Space) (u : Fin 3 → ℂ) :
    Continuous (fun q : ℝ × ℝ => symbolNormSq HW h z q.1 q.2 u) := by
  unfold symbolNormSq symbolEntry Coercive.Internal.SmoothPieceEpsCompression.torusPhase
  refine Coercive.Internal.FieldModes.continuous_cnormSq.comp (continuous_pi fun i => ?_)
  fun_prop

theorem le_of_ae_box {f : ℝ × ℝ → ℝ} (hf : Continuous f) (c : ℝ)
    (hae : ∀ᵐ q ∂Coercive.Internal.ModeRotation.boxMeasure, f q ≤ c) :
    ∀ q ∈ Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi), f q ≤ c := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set U := {q : ℝ × ℝ | c < f q} ∩ (Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi)) with hUdef
  have hUo : IsOpen U := (isOpen_lt continuous_const hf).inter (isOpen_Ioo.prod isOpen_Ioo)
  have h0 : (volume : Measure (ℝ × ℝ)) U = 0 := by
    have hb : ((volume.restrict (Set.Ioc (0 : ℝ) 1)).prod (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))))
        {q | ¬ f q ≤ c} = 0 := ae_iff.1 hae
    rw [Measure.prod_restrict, Measure.restrict_apply' (measurableSet_Ioc.prod measurableSet_Ioc),
      ← Measure.volume_eq_prod] at hb
    refine measure_mono_null ?_ hb
    rintro q ⟨hq1, hq2⟩
    refine ⟨?_, Set.Ioo_subset_Ioc_self hq2.1, Set.Ioo_subset_Ioc_self hq2.2⟩
    have hq1' : c < f q := hq1
    exact not_le.2 hq1'
  have hU : U = ∅ := (hUo.measure_eq_zero_iff volume).1 h0
  have hin : Set.Ioo (0 : ℝ) 1 ×ˢ Set.Ioo (0 : ℝ) (2 * Real.pi) ⊆ {q | f q ≤ c} := by
    intro q hq
    by_contra hn
    have hqU : q ∈ U := ⟨show c < f q from not_le.1 hn, hq⟩
    rw [hU] at hqU
    exact hqU
  have hcl := closure_minimal hin (isClosed_le hf continuous_const)
  rw [closure_prod_eq, closure_Ioo zero_ne_one, closure_Ioo hpi.ne] at hcl
  exact fun q hq => hcl hq

theorem bddAbove_vortGradMap {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {D : ℝ}
    (hW : IsWeakSecondDerivState W HW D) (y : Space) :
    BddAbove (Set.range fun p : ℝ × ℝ => ‖vortGradMap (HW p.1 (axialRot p.2 y))‖) := by
  refine ⟨81 * (D / (1 + ‖y‖) ^ 3), ?_⟩
  rintro _ ⟨p, rfl⟩
  refine (CoerciveWeak.Internal.PieceDensity.norm_vortGradMap_le _).trans
    (mul_le_mul_of_nonneg_left ?_ (by norm_num))
  have := (hW.decay p.1 (axialRot p.2 y)).2.2
  rwa [Coercive.RotationInternal.axialRot_norm] at this

theorem symbol_le_sup_of_expansion (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (h : HarmonicBounds)
    (z : ℝ × Space)
    (hbdd : BddAbove (Set.range fun p : ℝ × ℝ => ‖vortGradMap (HW p.1 (axialRot p.2 z.2))‖))
    (hz : ∀ᵐ q ∂Coercive.Internal.ModeRotation.boxMeasure, ∀ i j : Fin 3,
      ((axialRot (-q.2) (vortGradMap (HW (z.1 + q.1) (axialRot q.2 z.2)) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
        = curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
          + ∑ α ∈ h.harmonics.erase 0, Complex.exp (((2 * Real.pi * α.1 * q.1 + α.2 * q.2 : ℝ) : ℂ) * Complex.I)
            * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j))
    (τ φ : ℝ) (u : Fin 3 → ℂ) :
    symbolNormSq HW h z τ φ u ≤ vortGradSupWith HW z.2 ^ 2 * cnormSq u := by
  have hcont : Continuous (fun q : ℝ × ℝ => symbolNormSq HW h z q.1 q.2 u) :=
    continuous_symbolNormSq_angle HW h z u
  have hae : ∀ᵐ q ∂Coercive.Internal.ModeRotation.boxMeasure,
      symbolNormSq HW h z q.1 q.2 u ≤ vortGradSupWith HW z.2 ^ 2 * cnormSq u := by
    filter_upwards [hz] with q hq
    have e : symbolNormSq HW h z q.1 q.2 u = cnormSq (fun i => ∑ j,
        ((axialRot (-q.2) (vortGradMap (HW (z.1 + q.1) (axialRot q.2 z.2)) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
          * u j) := by
      unfold symbolNormSq
      congr 1
      funext i
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hq i j]
      rfl
    rw [e]
    refine (Coercive.Internal.SmoothPieceEpsCompressionParts.rot_clm_cnormSq_le _ q.2 u).trans ?_
    refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ 2) (cnormSq_nonneg_of u)
    exact le_ciSup hbdd (z.1 + q.1, q.2)
  have hbox := le_of_ae_box hcont _ hae
  have hp := symbolNormSq_shift HW h z (Int.fract τ) (2 * Real.pi * Int.fract (φ / (2 * Real.pi))) ⌊τ⌋
    ⌊φ / (2 * Real.pi)⌋ u
  have e1 : Int.fract τ + (⌊τ⌋ : ℝ) = τ := Int.fract_add_floor τ
  have e2 : 2 * Real.pi * Int.fract (φ / (2 * Real.pi)) + (⌊φ / (2 * Real.pi)⌋ : ℝ) * (2 * Real.pi) = φ := by
    have hpi : (2 * Real.pi) ≠ 0 := by positivity
    unfold Int.fract
    field_simp
    ring
  rw [e1, e2] at hp
  rw [hp]
  refine hbox (Int.fract τ, 2 * Real.pi * Int.fract (φ / (2 * Real.pi))) ⟨⟨Int.fract_nonneg τ, (Int.fract_lt_one τ).le⟩,
    ⟨by have := Int.fract_nonneg (φ / (2 * Real.pi)); positivity, ?_⟩⟩
  exact mul_le_of_le_one_right (by positivity) (Int.fract_lt_one _).le

theorem aem_symbolNormSq {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hHW : AEStronglyMeasurable (fun z : ℝ × Space => HW z.1 z.2) volume) (h : HarmonicBounds)
    (τ φ : ℝ) (u : Fin 3 → ℂ) :
    AEMeasurable (fun z : ℝ × Space => symbolNormSq HW h z τ φ u) volume := by
  have hc : ∀ α il, AEStronglyMeasurable (fun z : ℝ × Space => curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) il)
      volume := by
    intro α il
    unfold curlGradOfSecondDeriv
    exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun m _ =>
      (Coercive.Internal.PieceAbsorb.aestronglyMeasurable_modeSecondDeriv hHW α (m, il.2, j)).const_mul _
  unfold symbolNormSq symbolEntry
  refine Coercive.Internal.FieldModes.continuous_cnormSq.measurable.comp_aemeasurable
    (aemeasurable_pi_iff.2 fun i => ?_)
  refine AEStronglyMeasurable.aemeasurable ?_
  refine Finset.aestronglyMeasurable_fun_sum _ fun j _ => ?_
  exact ((hc 0 (i, j)).add (Finset.aestronglyMeasurable_fun_sum _ fun α _ => (hc α (i, j)).const_mul _)).mul_const _

theorem slab_ac_volume : (slabMeasure : Measure (ℝ × Space)) ≪ (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact (Measure.absolutelyContinuous_of_le Measure.restrict_le_self).prod Measure.AbsolutelyContinuous.rfl

theorem ae_le_realMinorant_slab {c : Space → ℝ} (hc : ∀ y, 0 ≤ c y) {g : ℝ × Space → ℝ}
    (hg : AEMeasurable g slabMeasure) (hle : ∀ᵐ z ∂slabMeasure, g z ≤ c z.2) :
    ∀ᵐ z ∂slabMeasure, g z ≤ Internal.Minorant.realMinorant volume c z.2 := by
  set k := hg.mk g with hkdef
  have hkm : Measurable k := hg.measurable_mk
  set B : Set (ℝ × Space) := {z | g z ≤ c z.2 ∧ g z = k z} with hBdef
  have hB : ∀ᵐ z ∂slabMeasure, z ∈ B := by
    filter_upwards [hle, hg.ae_eq_mk] with z h1 h2
    exact ⟨h1, h2⟩
  set M : Set (ℝ × Space) := (toMeasurable slabMeasure Bᶜ)ᶜ with hMdef
  have hMm : MeasurableSet M := (measurableSet_toMeasurable _ _).compl
  have hMB : M ⊆ B := by
    intro z hz
    by_contra hn
    exact hz (subset_toMeasurable _ _ hn)
  have hM : ∀ᵐ z ∂slabMeasure, z ∈ M := by
    have h0 : slabMeasure Bᶜ = 0 := ae_iff.1 hB
    rw [ae_iff]
    have e : {z | ¬ z ∈ M} = toMeasurable slabMeasure Bᶜ := by
      ext z
      simp only [hMdef, Set.mem_ofPred_eq, Set.mem_compl_iff, not_not]
    rw [e, measure_toMeasurable]
    exact h0
  set K : ℝ × Space → ℝ := M.indicator k with hKdef
  have hKm : Measurable K := hkm.indicator hMm
  have hKc : ∀ z, K z ≤ c z.2 := by
    intro z
    by_cases hz : z ∈ M
    · rw [hKdef, Set.indicator_of_mem hz]
      obtain ⟨h1, h2⟩ := hMB hz
      rw [← h2]
      exact h1
    · simp only [hKdef, Set.indicator, hz, if_false]
      exact hc _
  have hEm : MeasurableSet {z : ℝ × Space | K z ≤ Internal.Minorant.realMinorant volume c z.2} :=
    measurableSet_le hKm ((Internal.Minorant.measurable_realMinorant volume c).comp measurable_snd)
  have hall : ∀ᵐ z ∂slabMeasure, z ∈ {z : ℝ × Space | K z ≤ Internal.Minorant.realMinorant volume c z.2} :=
    (Measure.ae_prod_mem_iff_ae_ae_mem hEm).2 (Filter.Eventually.of_forall fun t =>
      Internal.Minorant.ae_le_realMinorant volume (hKm.comp measurable_prodMk_left) fun y => hKc (t, y))
  filter_upwards [hM, hall] with z hz1 hz2
  have hk : K z = g z := by
    rw [hKdef, Set.indicator_of_mem hz1]
    exact (hMB hz1).2.symm
  rw [← hk]
  exact hz2

theorem symbolNormSq_bound_of_expansion {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} {h : HarmonicBounds} (hW : IsWeakSecondDerivState W HW D)
    (hE : ∀ᵐ z ∂slabMeasure, ∀ᵐ q ∂Coercive.Internal.ModeRotation.boxMeasure, ∀ i j : Fin 3,
      ((axialRot (-q.2) (vortGradMap (HW (z.1 + q.1) (axialRot q.2 z.2)) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
        = curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
          + ∑ α ∈ h.harmonics.erase 0, Complex.exp (((2 * Real.pi * α.1 * q.1 + α.2 * q.2 : ℝ) : ℂ) * Complex.I)
            * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j)) :
    ∀ᵐ z ∂slabMeasure, ∀ τ φ (u : Fin 3 → ℂ), symbolNormSq HW h z τ φ u
          ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 * cnormSq u := by
  obtain ⟨S, hSc, hSd⟩ := TopologicalSpace.exists_countable_dense (ℝ × ℝ × (Fin 3 → ℂ))
  have hpt : ∀ x : ℝ × ℝ × (Fin 3 → ℂ), ∀ᵐ z ∂slabMeasure,
      Real.sqrt (symbolNormSq HW h z x.1 x.2.1 x.2.2 / cnormSq x.2.2)
        ≤ Internal.Minorant.vortGradSupLower HW z.2 := by
    intro x
    refine ae_le_realMinorant_slab (Internal.Minorant.vortGradSupWith_nonneg HW)
      (Real.continuous_sqrt.measurable.comp_aemeasurable
        (((aem_symbolNormSq hW.secondDeriv_measurable h x.1 x.2.1 x.2.2).div_const _).mono_ac slab_ac_volume)) ?_
    filter_upwards [hE] with z hz
    have hb := symbol_le_sup_of_expansion HW h z (bddAbove_vortGradMap hW z.2) hz x.1 x.2.1 x.2.2
    have hV := Internal.Minorant.vortGradSupWith_nonneg HW z.2
    calc Real.sqrt (symbolNormSq HW h z x.1 x.2.1 x.2.2 / cnormSq x.2.2)
        ≤ Real.sqrt (vortGradSupWith HW z.2 ^ 2) :=
          Real.sqrt_le_sqrt (div_le_of_le_mul₀ (cnormSq_nonneg_of _) (sq_nonneg _) hb)
      _ = vortGradSupWith HW z.2 := Real.sqrt_sq hV
  have hall := (ae_ball_iff hSc).2 fun x _ => hpt x
  filter_upwards [hall] with z hz τ φ u
  have hL := Internal.Minorant.vortGradSupLower_nonneg HW z.2
  have hS : S ⊆ {x : ℝ × ℝ × (Fin 3 → ℂ) | symbolNormSq HW h z x.1 x.2.1 x.2.2
      ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 * cnormSq x.2.2} := by
    intro x hx
    have h1 := hz x hx
    have hQ : 0 ≤ symbolNormSq HW h z x.1 x.2.1 x.2.2 := cnormSq_nonneg_of _
    have hc := cnormSq_nonneg_of x.2.2
    rcases hc.lt_or_eq with hc | hc
    · have h2 : symbolNormSq HW h z x.1 x.2.1 x.2.2 / cnormSq x.2.2
          ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 := by
        rw [← Real.sq_sqrt (div_nonneg hQ hc.le)]
        exact pow_le_pow_left₀ (Real.sqrt_nonneg _) h1 2
      exact (div_le_iff₀ hc).1 h2
    · have hu := eq_zero_of_cnormSq_eq_zero hc.symm
      show symbolNormSq HW h z x.1 x.2.1 x.2.2 ≤ _
      rw [← hc, hu]
      simp [symbolNormSq, cnormSq]
  have hcl : IsClosed {x : ℝ × ℝ × (Fin 3 → ℂ) | symbolNormSq HW h z x.1 x.2.1 x.2.2
      ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 * cnormSq x.2.2} :=
    isClosed_le (continuous_symbolNormSq HW h z)
      (continuous_const.mul (Coercive.Internal.FieldModes.continuous_cnormSq.comp (continuous_snd.comp continuous_snd)))
  have hmem : (τ, φ, u) ∈ closure S := by
    rw [hSd.closure_eq]
    exact Set.mem_univ _
  have hfin := closure_minimal hS hcl hmem
  simpa only [Set.mem_ofPred_eq] using hfin

theorem symbol_bound_of_expansion {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {D : ℝ} {h : HarmonicBounds} (hW : IsWeakSecondDerivState W HW D)
    (hE : ∀ᵐ z ∂slabMeasure, ∀ᵐ q ∂Coercive.Internal.ModeRotation.boxMeasure, ∀ i j : Fin 3,
      ((axialRot (-q.2) (vortGradMap (HW (z.1 + q.1) (axialRot q.2 z.2)) (axialRot q.2 (unitVector j))) i : ℝ) : ℂ)
        = curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
          + ∑ α ∈ h.harmonics.erase 0, Complex.exp (((2 * Real.pi * α.1 * q.1 + α.2 * q.2 : ℝ) : ℂ) * Complex.I)
            * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j)) :
    ∀ᵐ z ∂slabMeasure, ∀ τ φ (u : Fin 3 → ℂ), cnormSq (fun i => ∑ j, (curlGradOfSecondDeriv (modeSecondDeriv 0 HW z.1 z.2) (i, j)
        + ∑ α ∈ h.harmonics.erase 0, Coercive.Internal.SmoothPieceEpsCompression.torusPhase α τ φ
          * curlGradOfSecondDeriv (modeSecondDeriv α HW z.1 z.2) (i, j)) * u j)
          ≤ Internal.Minorant.vortGradSupLower HW z.2 ^ 2 * cnormSq u := by
  filter_upwards [symbolNormSq_bound_of_expansion hW hE] with z hz τ φ u
  have hb := hz τ φ u
  unfold symbolNormSq symbolEntry at hb
  exact hb

end Internal.PieceEpsSymbolBound

end CoerciveWeak

end Breakdown
