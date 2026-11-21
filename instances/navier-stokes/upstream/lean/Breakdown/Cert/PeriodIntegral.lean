import Mathlib
import Breakdown.Cert.Statement

open MeasureTheory Set

noncomputable section

namespace Breakdown.Cert

open Breakdown

theorem lintegral_Icc_coe (g : AddCircle (1 : ℝ) → ENNReal) (_hg : AEMeasurable g volume) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, g (σ : AddCircle (1 : ℝ)) = ∫⁻ t, g t := by
  have h := AddCircle.lintegral_preimage 1 0 g
  rw [zero_add] at h
  rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]

theorem integral_Icc_coe {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (g : AddCircle (1 : ℝ) → E) :
    ∫ σ in Set.Icc (0 : ℝ) 1, g (σ : AddCircle (1 : ℝ)) = ∫ t, g t := by
  have h := AddCircle.integral_preimage 1 0 g
  rw [zero_add] at h
  rw [← h, Measure.restrict_congr_set Ioc_ae_eq_Icc]

namespace PeriodIntegralInternal

theorem measurePreserving_equivIoc_val :
    MeasurePreserving (fun t : AddCircle (1 : ℝ) => ((AddCircle.equivIoc 1 0 t : Ioc (0 : ℝ) (0 + 1)) : ℝ))
      volume (volume.restrict (Ioc (0 : ℝ) (0 + 1))) :=
  (measurePreserving_subtype_coe measurableSet_Ioc).comp (AddCircle.measurePreserving_equivIoc 1)

theorem coe_equivIoc_val (t : AddCircle (1 : ℝ)) :
    (((AddCircle.equivIoc 1 0 t : Ioc (0 : ℝ) (0 + 1)) : ℝ) : AddCircle (1 : ℝ)) = t :=
  AddCircle.coe_equivIoc

theorem measurePreserving_mk_int (n : ℤ) :
    MeasurePreserving ((↑) : ℝ → AddCircle (1 : ℝ)) (volume.restrict (Ioc (n : ℝ) (n + 1))) :=
  AddCircle.measurePreserving_mk 1 (n : ℝ)

end PeriodIntegralInternal

open PeriodIntegralInternal

theorem ae_coe_iff (p : AddCircle (1 : ℝ) → Prop) :
    (∀ᵐ t : AddCircle (1 : ℝ), p t) ↔ ∀ᵐ σ : ℝ, p (σ : AddCircle (1 : ℝ)) := by
  constructor
  · intro h
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ)), ← iUnion_Ioc_intCast,
      ae_restrict_iUnion_iff]
    intro n
    exact (measurePreserving_mk_int n).quasiMeasurePreserving.ae h
  · intro h
    have h1 := measurePreserving_equivIoc_val.quasiMeasurePreserving.ae (ae_restrict_of_ae h)
    filter_upwards [h1] with t ht
    rwa [coe_equivIoc_val] at ht

theorem exists_lift_of_periodic {β : Type*} (f : ℝ → Space → β) (hf : IsTimePeriodic f) :
    ∃ F : AddCircle (1 : ℝ) → Space → β, ∀ (σ : ℝ) y, F (σ : AddCircle (1 : ℝ)) y = f σ y :=
  ⟨fun t y => Function.Periodic.lift (f := fun σ : ℝ => f σ y) (c := (1 : ℝ)) (fun σ : ℝ => hf σ y) t,
    fun σ y => Function.Periodic.lift_coe (f := fun σ : ℝ => f σ y) (c := (1 : ℝ)) (fun σ : ℝ => hf σ y) σ⟩

theorem aestronglyMeasurable_lift_iff {E : Type*} [TopologicalSpace E] [TopologicalSpace.PseudoMetrizableSpace E]
    (f : ℝ → Space → E) (F : AddCircle (1 : ℝ) → Space → E)
    (hF : ∀ (σ : ℝ) y, F (σ : AddCircle (1 : ℝ)) y = f σ y) :
    AEStronglyMeasurable (fun z : AddCircle (1 : ℝ) × Space => F z.1 z.2) volume ↔
      AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume := by
  rw [Measure.volume_eq_prod, Measure.volume_eq_prod]
  constructor
  · intro h
    rw [← Measure.restrict_univ (μ := (volume : Measure ℝ).prod (volume : Measure Space)),
      ← univ_prod_univ, ← iUnion_Ioc_intCast, iUnion_prod_const, aestronglyMeasurable_iUnion_iff]
    intro n
    rw [← Measure.prod_restrict, Measure.restrict_univ]
    have hmp := (measurePreserving_mk_int n).prod (MeasurePreserving.id (volume : Measure Space))
    have := h.comp_measurePreserving hmp
    refine this.congr (ae_of_all _ fun z => ?_)
    simp [hF]
  · intro h
    have hmp := measurePreserving_equivIoc_val.prod (MeasurePreserving.id (volume : Measure Space))
    have h' : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2)
        ((volume.restrict (Ioc (0 : ℝ) (0 + 1))).prod (volume : Measure Space)) := by
      rw [← Measure.restrict_univ (μ := (volume : Measure Space)), Measure.prod_restrict]
      exact h.restrict
    refine (h'.comp_measurePreserving hmp).congr (ae_of_all _ fun z => ?_)
    simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq]
    rw [← hF, coe_equivIoc_val]

theorem aestronglyMeasurable_lift_of_periodic {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] (f : ℝ → Space → E) (hf : IsTimePeriodic f)
    (hmeas : AEStronglyMeasurable (fun z : ℝ × Space => f z.1 z.2) volume) :
    ∃ F : AddCircle (1 : ℝ) → Space → E, (∀ (σ : ℝ) y, F (σ : AddCircle (1 : ℝ)) y = f σ y) ∧
      AEStronglyMeasurable (fun z : AddCircle (1 : ℝ) × Space => F z.1 z.2) volume := by
  obtain ⟨F, hF⟩ := exists_lift_of_periodic f hf
  exact ⟨F, hF, (aestronglyMeasurable_lift_iff f F hF).2 hmeas⟩

end Breakdown.Cert
