import Breakdown.Cert.Nodes
import Breakdown.Cert.ProductPairing
import Breakdown.Cert.TestPairing
import Breakdown.Cert.PeriodIntegral

open MeasureTheory Filter
open scoped ENNReal

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ProductSub

theorem ae_eq_of_ae_slices {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [TopologicalSpace E] [TopologicalSpace.MetrizableSpace E] {μ : Measure α} {ν : Measure β}
    [SFinite ν] {f g : α × β → E}
    (hf : AEStronglyMeasurable f (μ.prod ν)) (hg : AEStronglyMeasurable g (μ.prod ν))
    (h : ∀ᵐ x ∂μ, ∀ᵐ y ∂ν, f (x, y) = g (x, y)) : ∀ᵐ z ∂(μ.prod ν), f z = g z := by
  have hs : MeasurableSet {z | hf.mk f z = hg.mk g z} :=
    hf.stronglyMeasurable_mk.measurableSet_eq_fun hg.stronglyMeasurable_mk
  have key : ∀ᵐ z ∂(μ.prod ν), z ∈ {z | hf.mk f z = hg.mk g z} := by
    refine (Measure.ae_prod_mem_iff_ae_ae_mem hs).2 ?_
    filter_upwards [Measure.ae_ae_of_ae_prod hf.ae_eq_mk, Measure.ae_ae_of_ae_prod hg.ae_eq_mk, h]
      with x h1 h2 h3
    filter_upwards [h1, h2, h3] with y e1 e2 e3
    show hf.mk f (x, y) = hg.mk g (x, y)
    rw [← e1, ← e2, e3]
  filter_upwards [hf.ae_eq_mk, hg.ae_eq_mk, key] with z e1 e2 e3
  rw [e1, e2]
  exact e3

theorem productSlice_sub (a b : Freq.X) :
    (fun y => productSlice a a y - productSlice b b y) =ᵐ[volume]
      fun y => productSlice (a - b) a y + productSlice b (a - b) y := by
  have hv : (velocity (a - b) : Space → Space) =ᵐ[volume]
      (velocity a : Space → Space) - (velocity b : Space → Space) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have hp : ∀ j : Fin 3, (partialX j (a - b) : Space → Space) =ᵐ[volume]
      (partialX j a : Space → Space) - (partialX j b : Space → Space) := fun j => by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [hv, ae_all_iff.2 hp] with y h1 h2
  simp only [productSlice, h1, fun j => h2 j, Pi.sub_apply, PiLp.sub_apply, sub_smul, smul_sub,
    Finset.sum_sub_distrib]
  abel

theorem productSlice_sub_of_eq {a b c : Freq.X} (hc : c = a - b) :
    (fun y => productSlice a a y - productSlice b b y) =ᵐ[volume]
      fun y => productSlice c a y + productSlice b c y := by
  subst hc
  exact productSlice_sub a b

theorem ae_gradPart_sub (u u' : XX) :
    ∀ᵐ σ : ℝ, gradPart (((u - u' : XX) : TimeCircle → XBar) (σ : TimeCircle)) =
      gradPart ((u : TimeCircle → XBar) (σ : TimeCircle)) -
        gradPart ((u' : TimeCircle → XBar) (σ : TimeCircle)) := by
  have hs : ∀ᵐ σ : ℝ, ((u - u' : XX) : TimeCircle → XBar) (σ : TimeCircle) =
      (u : TimeCircle → XBar) σ - (u' : TimeCircle → XBar) σ :=
    (ae_coe_iff (fun t => ((u - u' : XX) : TimeCircle → XBar) t =
      (u : TimeCircle → XBar) t - (u' : TimeCircle → XBar) t)).1 (Lp.coeFn_sub u u')
  filter_upwards [hs] with σ c
  exact (congrArg gradPart c).trans (map_sub gradPart _ _)

theorem supGrad_eq_gradCLM (v : XX) : supGrad v = eLpNorm (gradCLM v) ⊤ volume :=
  (eLpNorm_congr_ae (ContinuousLinearMap.coeFn_compLpL gradPart v)).symm

theorem supGrad_sub_lt_top {u u' : XX} (hu : supGrad u < ⊤) (hu' : supGrad u' < ⊤) :
    supGrad (u - u') < ⊤ := by
  rw [supGrad_eq_gradCLM] at hu hu' ⊢
  rw [map_sub, eLpNorm_congr_ae (Lp.coeFn_sub _ _)]
  exact (eLpNorm_sub_le (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _) le_top).trans_lt
    (ENNReal.add_lt_top.2 ⟨hu, hu'⟩)

theorem admissible_one : IsAdmissibleWeight (fun _ => (1 : ℝ)) 1 :=
  ⟨one_pos, measurable_const, fun _ => le_rfl, 1, fun _ => le_rfl⟩

theorem ae_slices (h1 : ReadingExistsHolds) (u u' : XX) :
    ∀ᵐ σ : ℝ, (fun y => productField u u σ y - productField u' u' σ y) =ᵐ[volume]
      fun y => productField (u - u') u σ y + productField u' (u - u') σ y := by
  filter_upwards [Internal.ProductPairing.ae_productField_eq h1 u u,
    Internal.ProductPairing.ae_productField_eq h1 u' u',
    Internal.ProductPairing.ae_productField_eq h1 (u - u') u,
    Internal.ProductPairing.ae_productField_eq h1 u' (u - u'), ae_gradPart_sub u u'] with σ hA hB hC hD hs
  filter_upwards [hA, hB, hC, hD, productSlice_sub_of_eq hs] with y e1 e2 e3 e4 e5
  exact (congrArg₂ (· - ·) e1 e2).trans (e5.trans (congrArg₂ (· + ·) e3 e4).symm)

theorem toLpOrZero_sub_eq {f g k l : Space → Space} (hf : MemLp f 2) (hg : MemLp g 2)
    (hk : MemLp k 2) (hl : MemLp l 2)
    (h : (fun y => f y - g y) =ᵐ[volume] fun y => k y + l y) :
    toLpOrZero 2 f - toLpOrZero 2 g = toLpOrZero 2 k + toLpOrZero 2 l := by
  simp only [toLpOrZero, dif_pos hf, dif_pos hg, dif_pos hk, dif_pos hl]
  rw [← MemLp.toLp_sub hf hg, ← MemLp.toLp_add hk hl]
  exact MemLp.toLp_congr _ _ h

theorem physToHH_sub_eq {A B C D : ℝ → Space → Space} (hA : IsPeriodicField A)
    (hB : IsPeriodicField B) (hC : IsPeriodicField C) (hD : IsPeriodicField D)
    (h : ∀ᵐ σ : ℝ, (fun y => A σ y - B σ y) =ᵐ[volume] fun y => C σ y + D σ y) :
    physToHH A - physToHH B = physToHH C + physToHH D := by
  have xA := Internal.TestPairing.exists_curve A hA
  have xB := Internal.TestPairing.exists_curve B hB
  have xC := Internal.TestPairing.exists_curve C hC
  have xD := Internal.TestPairing.exists_curve D hD
  refine xA.elim fun cA pA => xB.elim fun cB pB => xC.elim fun cC pC => xD.elim fun cD pD => ?_
  have hc : ∀ᵐ t : TimeCircle, cA t - cB t = cC t + cD t := by
    refine (ae_coe_iff (fun t => cA t - cB t = cC t + cD t)).2 ?_
    filter_upwards [pA.2, pB.2, pC.2, pD.2, h] with σ qA qB qC qD hσ
    exact (congrArg₂ (· - ·) qA.2 qB.2).symm.trans
      ((toLpOrZero_sub_eq qA.1 qB.1 qC.1 qD.1 hσ).trans (congrArg₂ (· + ·) qC.2 qD.2))
  refine Lp.ext ?_
  filter_upwards [Lp.coeFn_sub (physToHH A) (physToHH B), Lp.coeFn_add (physToHH C) (physToHH D),
    pA.1, pB.1, pC.1, pD.1, hc] with t e1 e2 e3 e4 e5 e6 e7
  exact e1.trans ((congrArg₂ (· - ·) e3 e4).trans (((map_sub solProj _ _).symm.trans
    (congrArg solProj e7)).trans ((map_add solProj _ _).trans
      ((congrArg₂ (· + ·) e5 e6).symm.trans e2.symm))))

end Internal.ProductSub

open Internal.ProductSub

theorem productSubHolds_of (h1 : ReadingExistsHolds) (h2 : ProductBoundHolds) : ProductSubHolds := by
  intro u u' hu hu'
  have hd := supGrad_sub_lt_top hu hu'
  have hA := (h2 _ _ admissible_one u u hu).1
  have hB := (h2 _ _ admissible_one u' u' hu').1
  have hC := (h2 _ _ admissible_one (u - u') u hu).1
  have hD := (h2 _ _ admissible_one u' (u - u') hd).1
  have hs := ae_slices h1 u u'
  refine ⟨?_, ?_⟩
  · exact (congrArg₂ (· - ·) (Internal.ProductPairing.productH_eq_physToHH h1 hA.2.1)
      (Internal.ProductPairing.productH_eq_physToHH h1 hB.2.1)).trans
      ((physToHH_sub_eq hA hB hC hD hs).trans
        (congrArg₂ (· + ·) (Internal.ProductPairing.productH_eq_physToHH h1 hC.2.1)
          (Internal.ProductPairing.productH_eq_physToHH h1 hD.2.1)).symm)
  · exact ae_eq_of_ae_slices (μ := volume) (ν := volume)
      (f := fun z : ℝ × Space => productField u u z.1 z.2 - productField u' u' z.1 z.2)
      (g := fun z : ℝ × Space => productField (u - u') u z.1 z.2 + productField u' (u - u') z.1 z.2)
      (hA.1.sub hB.1) (hC.1.add hD.1) hs

end Breakdown.Cert
