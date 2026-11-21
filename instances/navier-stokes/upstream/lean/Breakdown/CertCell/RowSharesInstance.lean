import Breakdown.CertCell.TopStatements
import Breakdown.CertCell.GeneratorFlip
import Breakdown.CertCell.ModeTermFlip
import Breakdown.CertCell.InstanceRegular

open scoped ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Internal.RowShares

open Bridge.Internal.ModeTermFlip (flipIsometryEquiv flipPoint_flipPoint norm_flipPoint)
open CellCert.CellAnalysis (CellBox)

theorem flipPoint_add (a b : Space) : flipPoint (a + b) = flipPoint a + flipPoint b :=
  map_add flipIsometryEquiv a b

theorem flipPoint_smul (c : ℝ) (a : Space) : flipPoint (c • a) = c • flipPoint a :=
  map_smul flipIsometryEquiv c a

theorem inner_flipPoint (a b : Space) : inner ℝ (flipPoint a) b = inner ℝ a (flipPoint b) := by
  have h := flipIsometryEquiv.inner_map_map a (flipPoint b)
  change inner ℝ (flipPoint a) (flipPoint (flipPoint b)) = _ at h
  rwa [flipPoint_flipPoint] at h

theorem flip_measurePreserving : MeasurePreserving flipPoint volume volume :=
  flipIsometryEquiv.measurePreserving

theorem flip_measurableEmbedding : MeasurableEmbedding flipPoint :=
  flipIsometryEquiv.toMeasurableEquiv.measurableEmbedding

theorem plane_null : (volume : Measure Space) {y | y 2 = 0} = 0 := by
  let L : Space →ₗ[ℝ] ℝ := ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ)
  have hs : ({y : Space | y 2 = 0} : Set Space) = (LinearMap.ker L : Set Space) := by
    ext y
    simp [L]
  rw [hs]
  apply Measure.addHaar_submodule
  intro h
  have hmem : (EuclideanSpace.single (2 : Fin 3) (1 : ℝ) : Space) ∈ LinearMap.ker L := h ▸ Submodule.mem_top
  simp [L] at hmem

theorem ae_off_plane : ∀ᵐ y : Space, y 2 ≠ 0 :=
  ae_iff.2 (by simpa using plane_null)

theorem flipAverage_flip (F : ℝ → Space → Space) (σ : ℝ) (y : Space) :
    flipAverage F σ (flipPoint y) = flipPoint (flipAverage F σ y) := by
  unfold flipAverage
  simp only [flipPoint_smul, flipPoint_add, flipPoint_flipPoint]
  rw [add_comm]

theorem flipAverage_periodic {F : ℝ → Space → Space} (hF : IsTimePeriodic F) :
    IsTimePeriodic (flipAverage F) := by
  intro σ y
  unfold flipAverage
  rw [hF σ y, hF σ (flipPoint y)]

theorem norm_sq_average_le (a b : Space) :
    ‖(1 / 2 : ℝ) • (a + flipPoint b)‖ ^ 2 ≤ ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
  have h1 : ‖(1 / 2 : ℝ) • (a + flipPoint b)‖ ≤ (1 / 2) * (‖a‖ + ‖b‖) := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    gcongr
    calc ‖a + flipPoint b‖ ≤ ‖a‖ + ‖flipPoint b‖ := norm_add_le _ _
      _ = ‖a‖ + ‖b‖ := by rw [norm_flipPoint]
  have h0 : 0 ≤ ‖(1 / 2 : ℝ) • (a + flipPoint b)‖ := norm_nonneg _
  have h2 := mul_le_mul h1 h1 h0 (by positivity)
  nlinarith [norm_nonneg a, norm_nonneg b, sq_nonneg (‖a‖ - ‖b‖)]

theorem restrict_prod_measurable {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  rw [Measure.volume_eq_prod] at hF
  exact hF.mono_ac (Measure.AbsolutelyContinuous.prod
    (Measure.absolutelyContinuous_of_le Measure.restrict_le_self) Measure.AbsolutelyContinuous.rfl)

theorem ae_slice_measurable {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), AEStronglyMeasurable (F σ) volume :=
  (restrict_prod_measurable hF).prodMk_left

theorem ae_slice_memLp {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), MemLp (F σ) 2 := by
  have hF' := restrict_prod_measurable hF
  have hm : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (‖F z.1 z.2‖ ^ 2))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) :=
    (hF'.norm.pow 2).aemeasurable.ennreal_ofReal
  have hfin : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) < ⊤ :=
    ae_lt_top' hm.lintegral_prod_right' hF2.ne
  filter_upwards [hF'.prodMk_left, hfin] with σ hσ hσ2
  refine (memLp_two_iff_integrable_sq_norm hσ).2 ⟨hσ.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun y => by positivity)]
  exact hσ2

theorem flipAverage_measurable {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) :
    AEStronglyMeasurable (fun z : ℝ × Space => flipAverage F z.1 z.2) volume := by
  have hmp : MeasurePreserving (Prod.map id flipPoint : ℝ × Space → ℝ × Space) volume volume := by
    rw [Measure.volume_eq_prod]
    exact (MeasurePreserving.id volume).prod flip_measurePreserving
  have h2 : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 (flipPoint z.2)) volume :=
    hF.comp_measurePreserving hmp
  have h3 : AEStronglyMeasurable (fun z : ℝ × Space => flipPoint (F z.1 (flipPoint z.2))) volume :=
    flipIsometryEquiv.continuous.comp_aestronglyMeasurable h2
  exact (hF.add h3).const_smul (1 / 2 : ℝ)

theorem flipAverage_finite {F : ℝ → Space → Space}
    (hF : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) :
    periodLIntegral (fun σ y => ‖flipAverage F σ y‖ ^ 2) < ⊤ := by
  have hle : periodLIntegral (fun σ y => ‖flipAverage F σ y‖ ^ 2)
      ≤ 2 * periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) := by
    unfold periodLIntegral
    rw [← lintegral_const_mul' 2 _ (by simp)]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_slice_measurable hF] with σ hσ
    have hmeas : AEMeasurable (fun y => ENNReal.ofReal (‖F σ y‖ ^ 2)) volume :=
      (hσ.norm.pow 2).aemeasurable.ennreal_ofReal
    have hc : ∫⁻ y, ENNReal.ofReal (‖F σ (flipPoint y)‖ ^ 2) = ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) :=
      flip_measurePreserving.lintegral_comp_emb flip_measurableEmbedding (fun y => ENNReal.ofReal (‖F σ y‖ ^ 2))
    calc ∫⁻ y, ENNReal.ofReal (‖flipAverage F σ y‖ ^ 2)
        ≤ ∫⁻ y, (ENNReal.ofReal (‖F σ y‖ ^ 2) + ENNReal.ofReal (‖F σ (flipPoint y)‖ ^ 2)) := by
          refine lintegral_mono fun y => ?_
          rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
          exact ENNReal.ofReal_le_ofReal (norm_sq_average_le _ _)
      _ = (∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2)) + ∫⁻ y, ENNReal.ofReal (‖F σ (flipPoint y)‖ ^ 2) :=
          lintegral_add_left' hmeas _
      _ = 2 * ∫⁻ y, ENNReal.ofReal (‖F σ y‖ ^ 2) := by
          rw [hc, two_mul]
  exact hle.trans_lt (ENNReal.mul_lt_top (by simp) hF2)

theorem slice_pairing {f g : Space → Space} (hf : MemLp f 2) (hg : MemLp g 2)
    (hflip : ∀ᵐ y, g (flipPoint y) = flipPoint (g y)) :
    ∫ y, inner ℝ ((1 / 2 : ℝ) • (f y + flipPoint (f (flipPoint y)))) (g y) = ∫ y, inner ℝ (f y) (g y) := by
  have hint : Integrable (fun y => inner ℝ (f y) (g y)) := by
    refine (L2.integrable_inner (𝕜 := ℝ) (hf.toLp f) (hg.toLp g)).congr ?_
    filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
    rw [h1, h2]
  have hint2 : Integrable (fun y => inner ℝ (f (flipPoint y)) (g (flipPoint y))) :=
    (MeasureTheory.integrable_comp flipIsometryEquiv (fun y => inner ℝ (f y) (g y))).2 hint
  have hae : (fun y => inner ℝ (flipPoint (f (flipPoint y))) (g y))
      =ᵐ[volume] (fun y => inner ℝ (f (flipPoint y)) (g (flipPoint y))) := by
    filter_upwards [hflip] with y hy
    rw [inner_flipPoint, hy]
  have hint3 : Integrable (fun y => inner ℝ (flipPoint (f (flipPoint y))) (g y)) := hint2.congr hae.symm
  have hsplit : (fun y => inner ℝ ((1 / 2 : ℝ) • (f y + flipPoint (f (flipPoint y)))) (g y))
      = fun y => (1 / 2 : ℝ) * inner ℝ (f y) (g y) + (1 / 2 : ℝ) * inner ℝ (flipPoint (f (flipPoint y))) (g y) := by
    funext y
    rw [real_inner_smul_left, inner_add_left]
    ring
  have hc : ∫ y, inner ℝ (f (flipPoint y)) (g (flipPoint y)) = ∫ y, inner ℝ (f y) (g y) :=
    MeasureTheory.integral_comp flipIsometryEquiv (fun y => inner ℝ (f y) (g y))
  rw [hsplit, integral_add (hint.const_mul _) (hint3.const_mul _), integral_const_mul, integral_const_mul,
    integral_congr_ae hae, hc]
  ring

theorem pairing_flipAverage {F e : ℝ → Space → Space}
    (hF : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), MemLp (F σ) 2)
    (he : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), MemLp (e σ) 2)
    (hflip : ∀ σ, ∀ᵐ y, e σ (flipPoint y) = flipPoint (e σ y)) :
    periodPairing (flipAverage F) e = periodPairing F e := by
  unfold periodPairing flipAverage
  refine integral_congr_ae ?_
  filter_upwards [hF, he] with σ h1 h2
  exact slice_pairing h1 h2 (hflip σ)

theorem generator_labels_flip {count rowCount : ℕ} (R : RowValues count rowCount) (b : Fin rowCount) :
    ∀ K ι, ι ∈ (R.generator b).labels K → labelFlip ι ∈ (R.generator b).labels K := by
  intro K ι h
  simp only [RowValues.generator] at h ⊢
  split_ifs at h ⊢ with hK
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (Internal.GeneratorFlip.labelFlip_involutive _)
  · simp at h

theorem rowField_flip {count rowCount : ℕ} (R : RowValues count rowCount) (box : Fin count → CellBox) (m : ℕ)
    (a : Fin rowCount) (σ : ℝ) :
    ∀ᵐ y, R.rowFieldOf box m a σ (flipPoint y) = flipPoint (R.rowFieldOf box m a σ y) := by
  filter_upwards [ae_off_plane] with y hy
  simp only [RowValues.rowFieldOf]
  change _ = flipIsometryEquiv (∑ b, _)
  rw [map_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_smul]
  congr 1
  exact cellVecField_flip_equivariant (R.generator b) box m (generator_labels_flip R b) σ y hy

theorem rowField_memLp (hreg : Instance.CellVecFieldRegular) {rowCount : ℕ} (M : CellMesh)
    (R : RowValues M.count rowCount) (m : ℕ) (hM : IsCellMesh M) (a : Fin rowCount) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), MemLp (R.rowFieldOf M.box m a σ) 2 := by
  have hgen : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ b, MemLp (R.generatorField M.box m b σ) 2 := by
    rw [Filter.eventually_all]
    intro b
    exact ae_slice_memLp (hreg M (R.generator b) m hM).1 (hreg M (R.generator b) m hM).2.2.2
  filter_upwards [hgen] with σ hσ
  have := memLp_finsetSum Finset.univ (fun b _ => (hσ b).const_smul (R.mix M.box m a b))
  exact this

theorem rowSharesOfInstance_of_regular (hreg : Instance.CellVecFieldRegular) : RowSharesOfInstanceHolds := by
  intro k C nE nM D X hcls hrec _ q _ x
  have hrow := hrec.rows
  have hM : IsCellMesh D.mesh := hrow.values.mesh_valid
  have hFs_meas := flipAverage_measurable x.right_measurable
  have hFs_per := flipAverage_periodic x.right_periodic
  have hFs_fin := flipAverage_finite x.right_measurable x.right_finite
  have hclass := hcls D.mesh D.rows D.azimuthOrder X.rowWeightMax D.coercivity hrow.values hrow.coercivity_pos
    (flipAverage x.F) hFs_meas hFs_per hFs_fin (flipAverage_flip x.F)
  have hrowsEq : D.cert.rows x.F = D.cert.rows (flipAverage x.F) := by
    simp only [ExtendedCertificateData.rows, rowNorm]
    rw [hrow.rowField_eq]
    congr 1
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [pairing_flipAverage (ae_slice_memLp x.right_measurable x.right_finite)
      (rowField_memLp hreg D.mesh D.rows D.azimuthOrder hM a)
      (fun σ => rowField_flip D.rows D.mesh.box D.azimuthOrder a σ)]
  have hrowsForm : D.cert.rows (flipAverage x.F)
      = rowNorm (D.rows.rowFieldOf D.mesh.box D.azimuthOrder) (D.rows.rowWeightOf D.coercivity) (flipAverage x.F) := by
    simp only [ExtendedCertificateData.rows]
    rw [hrow.rowField_eq, hrow.rowWeight_eq]
  rw [hrowsEq, hrowsForm, hclass, mul_div_cancel_left₀ _ (by positivity)]
  rfl

end Internal.RowShares

theorem rowSharesOfInstance : RowSharesOfInstanceHolds :=
  Internal.RowShares.rowSharesOfInstance_of_regular Instance.cellVecFieldRegular

end CertCell

end Breakdown
