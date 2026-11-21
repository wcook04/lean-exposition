import Breakdown.Cert.ExtendedNodes
import Breakdown.Cert.HeldExistsUnique

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.ExtendedHeldExistsUnique

open Internal.HeldExistsUnique

theorem heldRight_fst {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (u : XX) :
    (d.heldRight q u).1 = -(d.defectH q) - productH u u := rfl

theorem heldRight_snd {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (u : XX) :
    (d.heldRight q u).2 = d.targetGap q := rfl

theorem heldStep_fst {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ)
    (x : XX × (Fin k → ℝ)) :
    (d.heldStep q x).1 =
      freeInv (d.period q) (borderedInv d.toCertificateData q (d.heldRight q x.1)).1 := rfl

theorem heldStep_snd {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ)
    (x : XX × (Fin k → ℝ)) :
    (d.heldStep q x).2 = (borderedInv d.toCertificateData q (d.heldRight q x.1)).2 := rfl

theorem heldStep_mk {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (u : XX)
    (κ : Fin k → ℝ) :
    d.heldStep q (u, κ) =
      (freeInv (d.period q) (borderedInv d.toCertificateData q (d.heldRight q u)).1,
        (borderedInv d.toCertificateData q (d.heldRight q u)).2) := rfl

theorem heldRight_mem {k : ℕ} (d : ExtendedCertificateData k) (hd : IsExtendedCertificate d)
    (h7 : ExtendedInvarianceHolds) (q : Fin k → ℝ) (hq : q ∈ d.params) (u : XX)
    (hu : gradCLM u ∈ invariantHH d.symmetries) :
    (d.heldRight q u).1 ∈ invariantHH d.symmetries := by
  have hI := h7 d hd q hq
  exact Submodule.sub_mem _ (Submodule.neg_mem _ hI.2.2) (hI.1 u hu).2

theorem borderedInv_apply {k : ℕ} (d : ExtendedCertificateData k)
    (hd : IsNormalExtendedCertificate d) (h5 : ExtendedBorderedInvertibleHolds) (q : Fin k → ℝ)
    (hq : q ∈ d.params) (y : HH × (Fin k → ℝ)) (hy : y.1 ∈ invariantHH d.symmetries) :
    (borderedInv d.toCertificateData q y).1 ∈ invariantHH d.symmetries ∧
      bordered d.toCertificateData q (borderedInv d.toCertificateData q y) = y :=
  borderedInv_spec d.toCertificateData q (h5 d hd q hq).1 y hy

theorem fixed_of_solution {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (f : HH)
    (κ : Fin k → ℝ)
    (hB : borderedInv d.toCertificateData q (d.heldRight q (freeInv (d.period q) f)) = (f, κ)) :
    d.heldStep q (freeInv (d.period q) f, κ) = (freeInv (d.period q) f, κ) := by
  have h := congrArg (fun z : HH × (Fin k → ℝ) => (freeInv (d.period q) z.1, z.2)) hB
  exact (heldStep_mk d q _ κ).trans h

theorem bordered_of_solution {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ) (f : HH)
    (κ : Fin k → ℝ) (hsol : d.IsHeldSolution q f κ) :
    bordered d.toCertificateData q (f, κ) = d.heldRight q (freeInv (d.period q) f) := by
  have hs : f + convection d.toCertificateData q (freeInv (d.period q) f)
      + actuatorH d.toCertificateData κ
      - (-(d.defectH q) - productH (freeInv (d.period q) f) (freeInv (d.period q) f)) =
      f + convection d.toCertificateData q (freeInv (d.period q) f)
        + actuatorH d.toCertificateData κ
        + productH (freeInv (d.period q) f) (freeInv (d.period q) f) + d.defectH q := by
    abel
  have h1 := (bordered_fst d.toCertificateData q (f, κ)).trans
    ((sub_eq_zero.mp (hs.trans hsol.equation)).trans (heldRight_fst d q _).symm)
  have h2 := (bordered_snd d.toCertificateData q (f, κ)).trans
    (hsol.pins.trans (heldRight_snd d q (freeInv (d.period q) f)).symm)
  exact Prod.ext h1 h2

theorem zero_mem_heldSet {k : ℕ} (d : ExtendedCertificateData k) (hd : IsExtendedCertificate d) :
    ((0 : XX), (0 : Fin k → ℝ)) ∈ heldSet d.toCertificateData := by
  have h0 : sizeZ d.weightFn (0 : XX) (0 : Fin k → ℝ) = 0 := by
    unfold sizeZ
    rw [energyW_zero]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · change sizeZ d.weightFn (0 : XX) (0 : Fin k → ℝ) ≤ 2 * d.sizeBound
    rw [h0]
    linarith [hd.sizeBound_nonneg]
  · rw [supGrad_zero]
    exact bot_le

theorem solution_of_eqs {k : ℕ} (d : ExtendedCertificateData k) (q : Fin k → ℝ)
    (z : HH × (Fin k → ℝ)) (u : XX) (κ : Fin k → ℝ) (hu : freeInv (d.period q) z.1 = u)
    (hκ : z.2 = κ) (hinv : z.1 ∈ invariantHH d.symmetries)
    (hbord : bordered d.toCertificateData q z = d.heldRight q u)
    (hsz : sizeZ d.weightFn u κ ≤ 2 * d.sizeBound)
    (hsup : supGrad u ≤ ENNReal.ofReal d.supBound) :
    d.IsHeldSolution q z.1 κ := by
  subst hu
  subst hκ
  have h := (bordered_fst d.toCertificateData q z).symm.trans
    ((congrArg Prod.fst hbord).trans (heldRight_fst d q _))
  have h' := (bordered_snd d.toCertificateData q z).symm.trans
    ((congrArg Prod.snd hbord).trans (heldRight_snd d q _))
  exact ⟨hinv, add_eq_zero_aux h, h', hsz, hsup⟩

theorem solution_of_fixed {k : ℕ} (d : ExtendedCertificateData k)
    (hd : IsNormalExtendedCertificate d) (h5 : ExtendedBorderedInvertibleHolds)
    (h7 : ExtendedInvarianceHolds) (q : Fin k → ℝ) (hq : q ∈ d.params) (x : XX × (Fin k → ℝ))
    (hxS : x ∈ heldSet d.toCertificateData) (hfix : d.heldStep q x = x) :
    d.IsHeldSolution q (borderedInv d.toCertificateData q (d.heldRight q x.1)).1 x.2 := by
  have hB := borderedInv_apply d hd h5 q hq (d.heldRight q x.1)
    (heldRight_mem d hd.certificate h7 q hq x.1 hxS.1)
  have hu : freeInv (d.period q) (borderedInv d.toCertificateData q (d.heldRight q x.1)).1 = x.1 :=
    (heldStep_fst d q x).symm.trans (congrArg Prod.fst hfix)
  have hκ : (borderedInv d.toCertificateData q (d.heldRight q x.1)).2 = x.2 :=
    (heldStep_snd d q x).symm.trans (congrArg Prod.snd hfix)
  exact solution_of_eqs d q _ x.1 x.2 hu hκ hB.1 hB.2 hxS.2.1 hxS.2.2

theorem inv_of_solution {k : ℕ} (d : ExtendedCertificateData k)
    (hd : IsNormalExtendedCertificate d) (h5 : ExtendedBorderedInvertibleHolds)
    (h6 : FreeEquivariantHolds) (h7 : ExtendedInvarianceHolds) (q : Fin k → ℝ)
    (hq : q ∈ d.params) (f : HH) (κ : Fin k → ℝ) (hsol : d.IsHeldSolution q f κ) :
    (freeInv (d.period q) f, κ) ∈ heldSet d.toCertificateData ∧
      borderedInv d.toCertificateData q (d.heldRight q (freeInv (d.period q) f)) = (f, κ) := by
  have hg : gradCLM (freeInv (d.period q) f) ∈ invariantHH d.symmetries :=
    h6 d.symmetries (d.period q) (hd.certificate.period_pos q hq) f hsol.invariant
  have hmem : (freeInv (d.period q) f, κ) ∈ heldSet d.toCertificateData :=
    ⟨hg, hsol.size, hsol.sup⟩
  have hB := borderedInv_apply d hd h5 q hq _ (heldRight_mem d hd.certificate h7 q hq _ hg)
  exact ⟨hmem, (h5 d hd q hq).2 _ _ hB.1 hsol.invariant
    (hB.2.trans (bordered_of_solution d q f κ hsol).symm)⟩

end Internal.ExtendedHeldExistsUnique

open Internal.ExtendedHeldExistsUnique in
theorem extendedHeldExistsUniqueHolds_of (h1 : ContractionFixedPointHolds)
    (h2 : ExtendedHeldMetricHolds) (h3 : ExtendedHeldMapsToHolds)
    (h4 : ExtendedHeldContractsHolds) (h5 : ExtendedBorderedInvertibleHolds)
    (h6 : FreeEquivariantHolds) (h7 : ExtendedInvarianceHolds) :
    ExtendedHeldExistsUniqueHolds := by
  intro k d hd q hq
  have hm := h2 d hd.certificate
  have hc := hm.2.1
  have hθ := h4 d hd q hq
  have hfp := h1 (heldSet d.toCertificateData) (heldDist d.toCertificateData) (d.heldStep q)
    hc.choose hθ.choose hm.1 ⟨_, zero_mem_heldSet d hd.certificate⟩ (h3 d hd q hq)
    hc.choose_spec.1 hθ.choose_spec.1 hc.choose_spec.2 hm.2.2.1 hm.2.2.2 hθ.choose_spec.2
  have hx := hfp.choose_spec
  refine ⟨_, _, solution_of_fixed d hd h5 h7 q hq hfp.choose hx.1 hx.2.1, ?_⟩
  intro f' κ' hsol
  have hI := inv_of_solution d hd h5 h6 h7 q hq f' κ' hsol
  have he := hx.2.2 _ hI.1 (fixed_of_solution d q f' κ' hI.2)
  have e1 : freeInv (d.period q) f' = hfp.choose.1 := congrArg Prod.fst he
  have e2 : κ' = hfp.choose.2 := congrArg Prod.snd he
  have e3 : (borderedInv d.toCertificateData q (d.heldRight q (freeInv (d.period q) f'))).1 = f' :=
    congrArg Prod.fst hI.2
  have e4 := congrArg (fun u => (borderedInv d.toCertificateData q (d.heldRight q u)).1) e1
  exact ⟨e3.symm.trans e4, e2⟩

end Breakdown.Cert
