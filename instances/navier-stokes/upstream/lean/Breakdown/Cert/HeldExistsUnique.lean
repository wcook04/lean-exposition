import Breakdown.Cert.Nodes

open scoped ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown.Cert

open Freq

namespace Internal.HeldExistsUnique

theorem borderedInv_spec {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ)
    (h : ∃ T, BorderedInvSpec d p T) : BorderedInvSpec d p (borderedInv d p) := by
  unfold borderedInv
  rw [dif_pos h]
  exact h.choose_spec

theorem bordered_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (z : HH × (Fin k → ℝ)) :
    (bordered d p z).1 = z.1 + convection d p (freeInv (d.period p) z.1) + actuatorH d z.2 := rfl

theorem bordered_snd {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (z : HH × (Fin k → ℝ)) :
    (bordered d p z).2 = pinMap d (freeInv (d.period p) z.1) := rfl

theorem heldRight_snd {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u : XX) :
    (heldRight d p u).2 = targetGap d p := rfl

theorem heldRight_mem {k : ℕ} (d : CertificateData k) (hd : IsCertificate d)
    (h7 : InvarianceHolds) (p : Fin k → ℝ) (hp : p ∈ d.box) (u : XX)
    (hu : gradCLM u ∈ invariantHH d.symmetries) :
    (heldRight d p u).1 ∈ invariantHH d.symmetries := by
  have hI := h7 d hd p hp
  exact Submodule.sub_mem _ (Submodule.neg_mem _ hI.2.2) (hI.1 u hu).2

theorem heldStep_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (x : XX × (Fin k → ℝ)) :
    (heldStep d p x).1 = freeInv (d.period p) (borderedInv d p (heldRight d p x.1)).1 := rfl

theorem heldStep_snd {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (x : XX × (Fin k → ℝ)) :
    (heldStep d p x).2 = (borderedInv d p (heldRight d p x.1)).2 := rfl

theorem heldRight_fst {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u : XX) :
    (heldRight d p u).1 = -(defectH d p) - productH u u := rfl


theorem heldStep_mk {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (u : XX) (κ : Fin k → ℝ) :
    heldStep d p (u, κ) = (freeInv (d.period p) (borderedInv d p (heldRight d p u)).1,
      (borderedInv d p (heldRight d p u)).2) := rfl

theorem borderedInv_apply {k : ℕ} (d : CertificateData k) (hd : IsCertificate d)
    (h5 : BorderedInvertibleHolds) (p : Fin k → ℝ) (hp : p ∈ d.box) (y : HH × (Fin k → ℝ))
    (hy : y.1 ∈ invariantHH d.symmetries) :
    (borderedInv d p y).1 ∈ invariantHH d.symmetries ∧ bordered d p (borderedInv d p y) = y :=
  borderedInv_spec d p (h5 d hd p hp).1 y hy

theorem energyW_eq_zero_of (w : Space → ℝ) (u : XX)
    (hu : ∀ᵐ t, gradPart ((u : TimeCircle → XBar) t) = 0) (h2 : secondCLM u = 0) :
    energyW w u = 0 := by
  have hs : ∀ h : Freq.X, h = 0 → sliceWeightedGrad w h = 0 := by
    intro h hh
    subst hh
    unfold sliceWeightedGrad
    have h0 : (fun y => w y * ∑ j : Fin 3, ‖((partialX j (0 : Freq.X) : L2R) : Space → Space) y‖ ^ 2)
        =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [Lp.coeFn_zero Space 2 (volume : Measure Space)] with y hy
      simp [map_zero]
    rw [integral_congr_ae h0]
    simp
  have hi : ∫ t, sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)) = 0 := by
    have h0 : (fun t => sliceWeightedGrad w (gradPart ((u : TimeCircle → XBar) t)))
        =ᵐ[volume] fun _ => (0 : ℝ) := by
      filter_upwards [hu] with t ht
      exact hs _ ht
    rw [integral_congr_ae h0, integral_zero]
  have h3 : ‖secondCLM u‖ ^ 2 = 0 := by rw [h2, norm_zero]; norm_num
  unfold energyW
  linarith

theorem supGrad_eq_zero_of (u : XX) (hu : ∀ᵐ t, gradPart ((u : TimeCircle → XBar) t) = 0) :
    supGrad u = 0 := by
  unfold supGrad
  rw [eLpNorm_congr_ae (g := fun _ => (0 : Freq.X)) hu]
  exact eLpNorm_zero'

theorem coe_zero_ae : ∀ᵐ t, gradPart (((0 : XX) : TimeCircle → XBar) t) = 0 := by
  filter_upwards [Lp.coeFn_zero XBar 2 (volume : Measure TimeCircle)] with t ht
  rw [ht]
  simp

theorem energyW_zero (w : Space → ℝ) : energyW w 0 = 0 :=
  energyW_eq_zero_of w 0 coe_zero_ae (map_zero _)

theorem supGrad_zero : supGrad 0 = 0 := supGrad_eq_zero_of 0 coe_zero_ae

theorem fixed_of_solution {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (f : HH)
    (κ : Fin k → ℝ) (hB : borderedInv d p (heldRight d p (freeInv (d.period p) f)) = (f, κ)) :
    heldStep d p (freeInv (d.period p) f, κ) = (freeInv (d.period p) f, κ) := by
  have h := congrArg (fun z : HH × (Fin k → ℝ) => (freeInv (d.period p) z.1, z.2)) hB
  exact (heldStep_mk d p _ κ).trans h

theorem bordered_of_solution {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (f : HH)
    (κ : Fin k → ℝ) (hsol : IsHeldSolution d p f κ) :
    bordered d p (f, κ) = heldRight d p (freeInv (d.period p) f) := by
  have hs : f + convection d p (freeInv (d.period p) f) + actuatorH d κ
      - (-(defectH d p) - productH (freeInv (d.period p) f) (freeInv (d.period p) f)) =
      f + convection d p (freeInv (d.period p) f) + actuatorH d κ
        + productH (freeInv (d.period p) f) (freeInv (d.period p) f) + defectH d p := by
    abel
  have h1 := (bordered_fst d p (f, κ)).trans ((sub_eq_zero.mp (hs.trans hsol.equation)).trans
    (heldRight_fst d p _).symm)
  have h2 := (bordered_snd d p (f, κ)).trans (hsol.pins.trans (heldRight_snd d p (freeInv (d.period p) f)).symm)
  exact Prod.ext h1 h2

theorem zero_mem_heldSet {k : ℕ} (d : CertificateData k) (hd : IsCertificate d) :
    ((0 : XX), (0 : Fin k → ℝ)) ∈ heldSet d := by
  have h0 : sizeZ d.weightFn (0 : XX) (0 : Fin k → ℝ) = 0 := by
    unfold sizeZ
    rw [energyW_zero]
    simp
  refine ⟨?_, ?_, ?_⟩
  · rw [map_zero]
    exact Submodule.zero_mem _
  · rw [h0]
    linarith [hd.sizeBound_nonneg]
  · rw [supGrad_zero]
    exact bot_le

theorem add_eq_zero_aux {E : Type*} [AddCommGroup E] {a D P : E} (h : a = -D - P) :
    a + P + D = 0 := by
  rw [h]
  abel

theorem solution_of_eqs {k : ℕ} (d : CertificateData k) (p : Fin k → ℝ) (z : HH × (Fin k → ℝ))
    (u : XX) (κ : Fin k → ℝ) (hu : freeInv (d.period p) z.1 = u) (hκ : z.2 = κ)
    (hinv : z.1 ∈ invariantHH d.symmetries) (hbord : bordered d p z = heldRight d p u)
    (hsz : sizeZ d.weightFn u κ ≤ 2 * d.sizeBound) (hsup : supGrad u ≤ ENNReal.ofReal d.supBound) :
    IsHeldSolution d p z.1 κ := by
  subst hu
  subst hκ
  have h := (bordered_fst d p z).symm.trans ((congrArg Prod.fst hbord).trans (heldRight_fst d p _))
  have h' := (bordered_snd d p z).symm.trans ((congrArg Prod.snd hbord).trans (heldRight_snd d p _))
  exact ⟨hinv, add_eq_zero_aux h, h', hsz, hsup⟩

theorem solution_of_fixed {k : ℕ} (d : CertificateData k) (hd : IsCertificate d)
    (h5 : BorderedInvertibleHolds) (h7 : InvarianceHolds) (p : Fin k → ℝ) (hp : p ∈ d.box)
    (x : XX × (Fin k → ℝ)) (hxS : x ∈ heldSet d) (hfix : heldStep d p x = x) :
    IsHeldSolution d p (borderedInv d p (heldRight d p x.1)).1 x.2 := by
  have hB := borderedInv_apply d hd h5 p hp (heldRight d p x.1) (heldRight_mem d hd h7 p hp x.1 hxS.1)
  have hu : freeInv (d.period p) (borderedInv d p (heldRight d p x.1)).1 = x.1 :=
    (heldStep_fst d p x).symm.trans (congrArg Prod.fst hfix)
  have hκ : (borderedInv d p (heldRight d p x.1)).2 = x.2 :=
    (heldStep_snd d p x).symm.trans (congrArg Prod.snd hfix)
  exact solution_of_eqs d p _ x.1 x.2 hu hκ hB.1 hB.2 hxS.2.1 hxS.2.2

theorem inv_of_solution {k : ℕ} (d : CertificateData k) (hd : IsCertificate d)
    (h5 : BorderedInvertibleHolds) (h6 : FreeEquivariantHolds) (h7 : InvarianceHolds)
    (p : Fin k → ℝ) (hp : p ∈ d.box) (f : HH) (κ : Fin k → ℝ) (hsol : IsHeldSolution d p f κ) :
    (freeInv (d.period p) f, κ) ∈ heldSet d ∧
      borderedInv d p (heldRight d p (freeInv (d.period p) f)) = (f, κ) := by
  have hg : gradCLM (freeInv (d.period p) f) ∈ invariantHH d.symmetries :=
    h6 d.symmetries (d.period p) (hd.period_pos p hp) f hsol.invariant
  have hmem : (freeInv (d.period p) f, κ) ∈ heldSet d := ⟨hg, hsol.size, hsol.sup⟩
  have hB := borderedInv_apply d hd h5 p hp _ (heldRight_mem d hd h7 p hp _ hg)
  exact ⟨hmem, (h5 d hd p hp).2 _ _ hB.1 hsol.invariant
    (hB.2.trans (bordered_of_solution d p f κ hsol).symm)⟩

end Internal.HeldExistsUnique

open Internal.HeldExistsUnique in
theorem heldExistsUniqueHolds_of (h1 : ContractionFixedPointHolds) (h2 : HeldMetricHolds)
    (h3 : HeldMapsToHolds) (h4 : HeldContractsHolds) (h5 : BorderedInvertibleHolds)
    (h6 : FreeEquivariantHolds) (h7 : InvarianceHolds) : HeldExistsUniqueHolds := by
  intro k d hd p hp
  have hm := h2 d hd
  have hc := hm.2.1
  have hθ := h4 d hd p hp
  have hfp := h1 (heldSet d) (heldDist d) (heldStep d p) hc.choose hθ.choose hm.1
    ⟨_, zero_mem_heldSet d hd⟩ (h3 d hd p hp) hc.choose_spec.1 hθ.choose_spec.1
    hc.choose_spec.2 hm.2.2.1 hm.2.2.2 hθ.choose_spec.2
  have hx := hfp.choose_spec
  refine ⟨_, _, solution_of_fixed d hd h5 h7 p hp hfp.choose hx.1 hx.2.1, ?_⟩
  intro f' κ' hsol
  have hI := inv_of_solution d hd h5 h6 h7 p hp f' κ' hsol
  have he := hx.2.2 _ hI.1 (fixed_of_solution d p f' κ' hI.2)
  have e1 : freeInv (d.period p) f' = hfp.choose.1 := congrArg Prod.fst he
  have e2 : κ' = hfp.choose.2 := congrArg Prod.snd he
  have e3 : (borderedInv d p (heldRight d p (freeInv (d.period p) f'))).1 = f' := congrArg Prod.fst hI.2
  have e4 := congrArg (fun u => (borderedInv d p (heldRight d p u)).1) e1
  exact ⟨e3.symm.trans e4, e2⟩

end Breakdown.Cert
