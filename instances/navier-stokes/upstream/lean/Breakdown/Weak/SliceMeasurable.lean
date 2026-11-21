import Breakdown.Weak.StatementsTime

open MeasureTheory Set Real Filter Topology
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.WeakProfile

open Freq

private theorem pairing_test_measurable (hp : PairingVelocity) {x : ℝ → X}
    {W : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} {M : ℝ}
    (hc : IsSliceCurve x W G M)
    (hW : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume)
    {φ : Space → Space} (hφ : IsTestField φ) :
    AEStronglyMeasurable (fun s => inner ℝ (x s) (embedX φ)) volume := by
  have hF : AEStronglyMeasurable (fun z : ℝ × Space => inner ℝ (W z.1 z.2) (negSsp φ z.2))
      ((volume : Measure ℝ).prod (volume : Measure Space)) := by
    rw [← Measure.volume_eq_prod]
    exact hW.inner ((isTestField_negSsp hφ).1.continuous.comp continuous_snd).aestronglyMeasurable
  refine hF.integral_prod_right'.congr (ae_of_all _ fun s => ?_)
  simp only
  rw [hp (x s) φ hφ]
  exact integral_congr_ae ((hc.vel s).mono fun y hy => by simp only [hy])

private theorem pairing_measurable (hp : PairingVelocity) {x : ℝ → X}
    {W : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)} {M : ℝ}
    (hc : IsSliceCurve x W G M)
    (hW : AEStronglyMeasurable (fun z : ℝ × Space => W z.1 z.2) volume) (v : X) :
    AEStronglyMeasurable (fun s => inner ℝ (x s) v) volume := by
  have hv : v ∈ closure (testSpan : Set X) := by
    rw [testDense_holds.2.closure_eq]; exact mem_univ v
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.1 hv
  refine aestronglyMeasurable_of_tendsto_ae atTop (f := fun n s => inner ℝ (x s) (u n))
    (fun n => ?_) (ae_of_all _ fun s => ?_)
  · obtain ⟨φ, hφ, he⟩ := testSpan_holds (u n) (hu n)
    rw [← he]
    exact pairing_test_measurable hp hc hW hφ
  · exact ((continuous_const.inner continuous_id).tendsto v).comp hlim

private theorem functional_measurable {x : ℝ → X}
    (hx : ∀ v : X, AEStronglyMeasurable (fun s => inner ℝ (x s) v) volume)
    (ℓ : X →L[ℝ] ℝ) : AEStronglyMeasurable (fun s => ℓ (x s)) volume := by
  refine (hx ((InnerProductSpace.toDual ℝ X).symm ℓ)).congr (ae_of_all _ fun s => ?_)
  simp only
  rw [real_inner_comm, InnerProductSpace.toDual_symm_apply]

private theorem finiteDim_measurable {x : ℝ → X}
    (hx : ∀ ℓ : X →L[ℝ] ℝ, AEStronglyMeasurable (fun s => ℓ (x s)) volume)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (T : X →L[ℝ] F) : AEStronglyMeasurable (fun s => T (x s)) volume := by
  let b := Module.finBasis ℝ F
  have h : (fun s => T (x s)) = fun s => ∑ i, b.repr (T (x s)) i • b i := by
    funext s
    exact (b.sum_repr (T (x s))).symm
  rw [h]
  refine Finset.aestronglyMeasurable_fun_sum _ fun i _ => ?_
  refine AEStronglyMeasurable.smul_const ?_ (b i)
  exact hx ((LinearMap.toContinuousLinearMap (b.coord i)).comp T)

theorem sliceMeasurable_holds : SliceMeasurable := by
  intro hp x W G M hc hW
  have h2 := functional_measurable (pairing_measurable hp hc hW)
  have : IsSeparable (volume : Measure Space) := inferInstance
  have : Fact ((2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞)) := ⟨by norm_num⟩
  have : SecondCountableTopology L2C := MeasureTheory.Lp.SecondCountableTopology
  have : SecondCountableTopology X := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq X
  let U : ℕ → Submodule ℝ X := fun n => Submodule.span ℝ (d '' Iic n)
  have : ∀ n, FiniteDimensional ℝ (U n) := fun n =>
    FiniteDimensional.span_of_finite ℝ ((finite_Iic n).image d)
  have hmono : Monotone U := fun m n h => Submodule.span_mono (image_mono (Iic_subset_Iic.2 h))
  have htop : ⊤ ≤ (⨆ n, U n).topologicalClosure := by
    intro v _
    have hsub : range d ⊆ ((⨆ n, U n : Submodule ℝ X) : Set X) := by
      rintro _ ⟨n, rfl⟩
      exact Submodule.mem_iSup_of_mem n (Submodule.subset_span ⟨n, le_refl n, rfl⟩)
    have hcl := closure_mono hsub
    rw [hd.closure_range] at hcl
    rw [← SetLike.mem_coe, Submodule.topologicalClosure_coe]
    exact hcl (mem_univ v)
  refine aestronglyMeasurable_of_tendsto_ae atTop
    (f := fun n s => (U n).starProjection (x s)) (fun n => ?_)
    (ae_of_all _ fun s => Submodule.starProjection_tendsto_self U hmono (x s) htop)
  have hP := finiteDim_measurable h2 (U n).orthogonalProjectionOnto
  refine (continuous_subtype_val.comp_aestronglyMeasurable hP).congr (ae_of_all _ fun s => ?_)
  rfl

end Breakdown.WeakProfile
