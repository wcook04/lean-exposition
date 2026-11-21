import Breakdown.CertCell.AssemblyPotentialSharpLeaf
import Breakdown.CertCell.AssemblyPotentialModelFrameFacts
import Breakdown.FracCell.SharpCircleStrain

open scoped ComplexConjugate
open Filter Topology Matrix MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

open Bridge Bridge.Internal.MeanStretch Coercive.StretchInternal Coercive.Internal.ModeRotation CellCalculus
  CellCert.CellAnalysis

section Defs

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def otherAt (P : CouplingEntries D R) (K : Fin D.mesh.count) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ) (η : Fin (R.portCount K) → ℂ) : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ :=
  otherProfiles D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) v G

def leafCore (K : Fin D.mesh.count) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (sesq12 ((R.leaves K).localMatrix ι p) (X ι p) (X ι p)).re

def boxCore (K : Fin D.mesh.count) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  p.1 * (R.leaves K).boxPairPenalty ι (strainOfVec (X ι p)) (velOf (X ι p))

def absorbCore (K : Fin D.mesh.count) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  (D.mesh.box K).lineWeight p.1 *
    ((R.leaves K).curlAbsorb ι * curlSq (strainOfVec (X ι p)) + (R.leaves K).strainAbsorb ι * sumSq (strainOfVec (X ι p))
      + (R.leaves K).velocityAbsorb ι * vecSq (velOf (X ι p)))

def chargeTerm (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  if ι ∈ D.mesh.resolved K then 0 else
    (D.labelDensity q v G H ι p
      - TailBand.offModeDensity (D.pieces q) (D.cert.period q) (D.bounds q) D.cert.weightFn (D.charges (some K))
          (R.entryCharges K ι) D.azimuthOrder ι v G H p
      - extraChargeDensity D R K ι v G p) * p.1

def stretchTerm (Hl : Finset (ℤ × ℤ)) (X : ℤ × ℤ → ℝ × ℝ → Fin 12 → ℂ) (ι : ℤ × ℤ) (p : ℝ × ℝ) : ℝ :=
  ∑ α ∈ Hl, p.1 * (sesq12 (trueCoupling D α p) (X ι p) (X (ι - α) p)).re

end Defs

def AbsorbSplitStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) (states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P states → LowTailSplit D R →
    ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ (ζ : Fin k → ℝ) (η : Fin (R.portCount K) → ℂ),
      alAmount D R K (otherAt D R P K v G H Pg κ ζ η)
        = alAmount D R K (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)))
          + alAmount D R K (tailProfiles D R K v G)

def SharpRegularStatement : Prop :=
  ∀ {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D) (A : AssemblyEntry D R)
    (P : CouplingEntries D R) (states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop), AssemblyRegular D R → TrueFieldRegular D → PotentialConditions D R A P states → LowTailSplit D R →
    ∀ K q v G H g κ F Pg, IsCellTuple D K q v G H g κ F Pg → ∀ (ζ : Fin k → ℝ) (η : Fin (R.portCount K) → ℂ),
      (∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect),
        Summable (fun ι => cnormSq (otherAt D R P K v G H Pg κ ζ η ι p)) ∧
        Summable (fun ι => chargeTerm D R K q v G H ι p) ∧
        Summable (fun ι => stretchTerm D (P.potential K).harmonicLabels (otherAt D R P K v G H Pg κ ζ η) ι p)) ∧
      (∀ ι ∈ D.mesh.resolved K,
        IntegrableOn (leafCore D R K (otherAt D R P K v G H Pg κ ζ η) ι) (D.mesh.box K).rect ∧
        IntegrableOn (boxCore D R K (otherAt D R P K v G H Pg κ ζ η) ι) (D.mesh.box K).rect ∧
        IntegrableOn (absorbCore D R K (otherAt D R P K v G H Pg κ ζ η) ι) (D.mesh.box K).rect) ∧
      IntegrableOn (fun p => ∑' ι, chargeTerm D R K q v G H ι p) (D.mesh.box K).rect ∧
      (∫ p in (D.mesh.box K).rect, ∑' ι, chargeTerm D R K q v G H ι p) = stretchChargeAmount D R K q v G H ∧
      IntegrableOn (fun p => ∑' ι, stretchTerm D (P.potential K).harmonicLabels (otherAt D R P K v G H Pg κ ζ η) ι p)
        (D.mesh.box K).rect ∧
      (∫ p in (D.mesh.box K).rect,
          ∑' ι, stretchTerm D (P.potential K).harmonicLabels (otherAt D R P K v G H Pg κ ζ η) ι p)
        = trueStretch D K (P.potential K).harmonicLabels (otherAt D R P K v G H Pg κ ζ η)
            (otherAt D R P K v G H Pg κ ζ η)

theorem sum_core (res : Finset (ℤ × ℤ)) (f leaf charge st : ℤ × ℤ → ℝ) (r : ℝ) (hf : Summable f)
    (hcs : Summable charge) (hleaf : ∀ ι ∈ res, r * f ι ≤ leaf ι)
    (hcharge : ∀ ι, (if ι ∈ res then 0 else r * f ι) ≤ charge ι) (hst : -(r * ∑' ι, f ι) ≤ ∑' ι, st ι) :
    0 ≤ ∑ ι ∈ res, leaf ι + ∑' ι, charge ι + ∑' ι, st ι := by
  classical
  have habs : Summable fun ι => |f ι| := summable_abs_iff.mpr hf
  have hin : Summable fun ι => if ι ∈ res then f ι else 0 :=
    Summable.of_norm_bounded habs fun ι => by split_ifs <;> simp
  have hout : Summable fun ι => if ι ∈ res then 0 else f ι :=
    Summable.of_norm_bounded habs fun ι => by split_ifs <;> simp
  have hsplit : ∑' ι, f ι = ∑ ι ∈ res, f ι + ∑' ι, (if ι ∈ res then 0 else f ι) := by
    have e : ∀ ι, f ι = (if ι ∈ res then f ι else 0) + (if ι ∈ res then 0 else f ι) := by
      intro ι; split_ifs <;> simp
    rw [tsum_congr e, hin.tsum_add hout, tsum_eq_sum (s := res)]
    · refine congrArg (· + _) (Finset.sum_congr rfl fun ι hι => ?_)
      simp [hι]
    · intro ι hι; simp [hι]
  have h1 : r * ∑ ι ∈ res, f ι ≤ ∑ ι ∈ res, leaf ι := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum hleaf
  have h2 : r * ∑' ι, (if ι ∈ res then 0 else f ι) ≤ ∑' ι, charge ι := by
    rw [← tsum_mul_left]
    refine (hout.mul_left r).tsum_le_tsum (fun ι => ?_) hcs
    have := hcharge ι
    split_ifs at this ⊢ with h
    · simpa using this
    · exact this
  have h3 := hst
  rw [hsplit] at h3
  nlinarith [h1, h2, h3]

theorem cylPoint_eq (p : ℝ × ℝ) (φ : ℝ) : cylPoint p.1 φ p.2 = axialRot φ (planePoint p) := by
  ext i
  fin_cases i <;> simp [cylPoint, planePoint, axialRot, unitVector] <;> ring

theorem inner_strainOf (W : ℝ → Space → Space) (τ : ℝ) (x u : Space) :
    inner ℝ (strainOf W τ x u) u = inner ℝ u (gradField W τ x u) := by
  unfold strainOf gradField
  rw [_root_.smul_apply, _root_.add_apply, inner_smul_left, inner_add_left,
    ContinuousLinearMap.adjoint_inner_left, real_inner_comm u]
  simp
  ring

theorem labelGrad_zero_vort {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (p : ℝ × ℝ) :
    (fun a b => labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p (a, b))
      = fun a b => modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (D.givenHess σ y)) 0 (planePoint p) (a, b) := by
  have : labelHarmonic D.azimuthOrder (0, 0) = 0 := by simp [labelHarmonic, labelTime, labelAzimuth]
  unfold labelGrad
  rw [this]
  rfl

theorem other_unresolved {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (P : CouplingEntries D R) (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) (ι : ℤ × ℤ) (hι : ι ∉ D.mesh.resolved K) (p : ℝ × ℝ) :
    otherAt D R P K v G H Pg κ ζ η ι p = bandProfile D ι v G p := by
  unfold otherAt otherProfiles upperProfiles lowAt trueProfiles
  simp [hι]

theorem labelGrad_zero_vort_apply {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (p : ℝ × ℝ)
    (ab : Fin 3 × Fin 3) :
    labelGrad D.azimuthOrder (0, 0) (vorticityGradOf D.givenHess) p ab
      = modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (D.givenHess σ y)) 0 (planePoint p) ab := by
  have : labelHarmonic D.azimuthOrder (0, 0) = 0 := by simp [labelHarmonic, labelTime, labelAzimuth]
  unfold labelGrad
  rw [this]
  rfl

theorem lineWeight_pos (K : CellBox) (p : ℝ × ℝ) (hp : p ∈ K.rect) (hp1 : p.1 ≠ 0) :
    0 < K.lineWeight p.1 := by
  unfold CellBox.lineWeight
  split_ifs with h
  · have h1 : K.r₁ ≤ p.1 := hp.1.1
    rcases lt_or_eq_of_le (h ▸ h1 : (0 : ℝ) ≤ p.1) with h2 | h2
    · exact h2
    · exact absurd h2.symm hp1
  · exact one_pos

theorem point_nonneg {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)
    (A : AssemblyEntry D R) (P : CouplingEntries D R) (hAR : AssemblyRegular D R) {states : ∀ K : Fin D.mesh.count, (CellVars D R K → ℂ) → Prop} (hchk : PotentialConditions D R A P states)
    (K : Fin D.mesh.count) (q : Fin k → ℝ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (g : ℝ → Space → Space) (κ : Fin k → ℝ)
    (F Pg : ℝ → Space → Space) (ht : IsCellTuple D K q v G H g κ F Pg) (ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) (p : ℝ × ℝ) (hp : p ∈ (D.mesh.box K).rect) (hp1 : p.1 ≠ 0)
    (hE2 : ∀ τ φ a b c, ((frameSecondDeriv D.givenHess (planePoint p) τ φ a b c : ℝ) : ℂ)
      = ∑ β ∈ D.givenLabels, phase β τ φ * modeSecondDeriv β D.givenHess 0 (planePoint p) (a, b, c))
    (hsumX : Summable fun ι => cnormSq (otherAt D R P K v G H Pg κ ζ η ι p))
    (hsumC : Summable fun ι => chargeTerm D R K q v G H ι p) :
    0 ≤ ∑ ι ∈ D.mesh.resolved K, (leafCore D R K (otherAt D R P K v G H Pg κ ζ η) ι p
          - boxCore D R K (otherAt D R P K v G H Pg κ ζ η) ι p + absorbCore D R K (otherAt D R P K v G H Pg κ ζ η) ι p)
      + ∑' ι, chargeTerm D R K q v G H ι p
      + ∑' ι, stretchTerm D (P.potential K).harmonicLabels (otherAt D R P K v G H Pg κ ζ η) ι p := by
  set X := otherAt D R P K v G H Pg κ ζ η with hXdef
  set ch := D.charges (some K) with hch
  have hcb := hchk.charges_all K
  have hF := hAR.field
  obtain ⟨B, hWHS⟩ := hF.model_state
  have hbox : IsCellBox (D.mesh.box K) := hchk.mesh_valid.box_valid K
  have hE1 := (frameFacts.given_expansion D.givenLabels D.given D.givenHess B hF.model_harmonics hWHS
    (D.mesh.box K) hbox).1 (planePoint p)
  have hV : ∀ τ φ j l, fibGrad (fun σ y => CoerciveWeak.vortGradMap (D.givenHess σ y)) (planePoint p) τ φ j l
      = curlGradReal (frameSecondDeriv D.givenHess (planePoint p) τ φ) j l := fun τ φ j l =>
    frameFacts.vorticity_grad (D.givenHess τ (axialRot φ (planePoint p))) (hF.hessian_symmetric τ _) φ j l
  set ℓ := ch.length 0 p with hℓdef
  have hℓ : 0 < ℓ := hcb.length_pos 0 p hp
  have hlen : ∀ ι, ch.length ι p = ℓ := fun ι => hcb.length_common ι 0 p hp
  obtain ⟨c, hc⟩ := hAR.charges.bounded K
  have hC : ∀ ι, |ch.curl ι p| ≤ c ∧ ch.product ι p ≤ c ∧ ch.gradient ι p ≤ c := fun ι =>
    ⟨(hc ι p hp).2.2.2.2.1, (le_abs_self _).trans (hc ι p hp).2.2.2.2.2.1,
      (le_abs_self _).trans (hc ι p hp).2.2.2.2.2.2.1⟩
  have hg0 : ∀ ι, 0 ≤ ch.product ι p := fun ι => (hcb.charges_nonneg ι p hp).1
  have hgw : ∀ ι, 0 ≤ ch.gradient ι p := fun ι => (hcb.charges_nonneg ι p hp).2
  have hstrain : ∀ ι τ φ (u : Space), inner ℝ u (gradField D.given τ (axialRot φ (planePoint p)) u)
      ≤ ch.curl ι p * ‖u‖ ^ 2 := by
    intro ι τ φ u
    have h := hcb.strain ι p hp τ φ u
    rwa [cylPoint_eq, inner_strainOf] at h
  have hmean : ∀ ι, opBound (fun a b => modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (D.givenHess σ y)) 0
      (planePoint p) (a, b)) (ch.product ι p) := by
    intro ι
    have h := hcb.mean_gradient ι p hp
    simpa only [labelGrad_zero_vort_apply] using h
  have hwave : ∀ ι τ φ (u : Space), ‖CoerciveWeak.vortGradMap (D.givenHess τ (axialRot φ (planePoint p))) u
      - CellMatField.frameMap φ (fun a b => (modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (D.givenHess σ y)) 0
          (planePoint p) (a, b)).re) u‖ ≤ ch.gradient ι p * ‖u‖ := by
    intro ι τ φ u
    have h := hcb.wave_gradient ι p hp τ φ u
    simp only [labelGrad_zero_vort_apply] at h
    rw [cylPoint_eq] at h
    exact h
  have PB := point_bound D.azimuthOrder hF.azimuth_pos D.givenLabels (P.potential K).harmonicLabels
    (hchk.labels_iff K) D.given D.givenHess (planePoint p) hE1 hE2 hV hF.hessian_symmetric
    (fun ι => ch.curl ι p) (fun ι => ch.product ι p) (fun ι => ch.gradient ι p) ℓ c hℓ hstrain hmean hwave hg0 hgw hC
    (fun ι => X ι p) hsumX
  set f : ℤ × ℤ → ℝ := fun ι => pointLoss (ch.curl ι p) (ch.product ι p) (ch.gradient ι p) ℓ (X ι p) with hfdef
  have hf : Summable f := summable_of_cnorm hsumX f _ fun ι =>
    pointLoss_abs_le _ _ _ ℓ c hℓ (hC ι).1 (hg0 ι) (hC ι).2.1 (hgw ι) (hC ι).2.2 (X ι p)
  have hp0 : 0 ≤ p.1 := le_trans hbox.r_order.1 hp.1.1
  have hlw := lineWeight_pos (D.mesh.box K) p hp hp1
  refine sum_core (D.mesh.resolved K) f _ _ _ p.1 hf hsumC ?_ ?_ ?_
  · intro ι hι
    have h := leaf_point (D.mesh.box K) (D.mesh.resolved K) _ ch (R.leaves K)
      (hchk.cell_conditions.leaves_valid K q ht.param) ι hι p hp hp1 hlw (X ι p)
    rw [hlen ι] at h
    have e : absorbCore D R K X ι p = (D.mesh.box K).lineWeight p.1
        * (R.leaves K).absorbValue ι (strainOfVec (X ι p)) (velOf (X ι p)) := rfl
    simp only [leafCore, boxCore] at *
    rw [e]
    simp only [hfdef]
    linarith
  · intro ι
    by_cases hι : ι ∈ D.mesh.resolved K
    · simp [chargeTerm, hι]
    · simp only [hι, if_false, chargeTerm]
      have h := offmode_point D R K q v G H ι p (hchk.stretch_const K ι hι) (hg0 ι) (hgw ι)
        (hcb.length_pos ι p hp) hp0
      rw [hlen ι, ← other_unresolved D R P K v G H Pg κ ζ η ι hι p] at h
      simp only [hfdef]
      linarith
  · have e1 : ∀ ι, stretchTerm D (P.potential K).harmonicLabels X ι p
        = p.1 * ∑ α ∈ (P.potential K).harmonicLabels,
          (sesq12 (tripleMatrix (modeGrad (labelHarmonic D.azimuthOrder α) (gradField D.given) 0 (planePoint p))
            (modeSecondDeriv (labelHarmonic D.azimuthOrder α) D.givenHess 0 (planePoint p))) (X ι p) (X (ι - α) p)).re := by
      intro ι
      unfold stretchTerm
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun α _ => ?_
      rw [trueCoupling_eq]
      rfl
    rw [tsum_congr e1, tsum_mul_left]
    have := mul_le_mul_of_nonneg_left PB hp0
    linarith

theorem sharpStageHolds_of (hAb : AbsorbSplitStatement) (hReg : SharpRegularStatement) : SharpStageHolds := by
  intro k C nE nM D R A P states hstates hAR hTF _ hchk hLT K q v G H g κ F Pg ht ζ η
  obtain ⟨hae, hloc, hcI, hcE, hsI, hsE⟩ := hReg D R A P states hAR hTF hchk hLT K q v G H g κ F Pg ht ζ η
  have hab := hAb D R A P states hAR hTF hchk hLT K q v G H g κ F Pg ht ζ η
  have hF := hAR.field
  obtain ⟨B, hWHS⟩ := hF.model_state
  have hbox : IsCellBox (D.mesh.box K) := hchk.mesh_valid.box_valid K
  have hst2 := (frameFacts.given_expansion D.givenLabels D.given D.givenHess B hF.model_harmonics hWHS
    (D.mesh.box K) hbox).2
  have hmeas : MeasurableSet (D.mesh.box K).rect := measurableSet_Icc.prod measurableSet_Icc
  set X := otherAt D R P K v G H Pg κ ζ η with hX
  have hΦ : 0 ≤ᵐ[volume.restrict (D.mesh.box K).rect] fun p =>
      ∑ ι ∈ D.mesh.resolved K, (leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p)
        + ∑' ι, chargeTerm D R K q v G H ι p
        + ∑' ι, stretchTerm D (P.potential K).harmonicLabels X ι p := by
    filter_upwards [hae, hst2, SharpCircleStrainParts.fst_ne_ae (D.mesh.box K), ae_restrict_mem hmeas]
      with p h1 h2 h3 h4
    exact point_nonneg D R A P hAR hchk K q v G H g κ F Pg ht ζ η p h4 h3 (fun τ φ a b c => h2 τ φ a b c) h1.1 h1.2.1
  have hI := integral_nonneg_of_ae hΦ
  have hleafI : ∀ ι ∈ D.mesh.resolved K, IntegrableOn
      (fun p => leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p) (D.mesh.box K).rect :=
    fun ι hι => ((hloc ι hι).1.sub (hloc ι hι).2.1).add (hloc ι hι).2.2
  have hsumI : IntegrableOn (fun p => ∑ ι ∈ D.mesh.resolved K,
      (leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p)) (D.mesh.box K).rect :=
    integrable_finsetSum _ hleafI
  have hsplit1 : (∫ p in (D.mesh.box K).rect,
      ∑ ι ∈ D.mesh.resolved K, (leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p)
        + ∑' ι, chargeTerm D R K q v G H ι p
        + ∑' ι, stretchTerm D (P.potential K).harmonicLabels X ι p)
      = (∫ p in (D.mesh.box K).rect,
          ∑ ι ∈ D.mesh.resolved K, (leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p))
        + (∫ p in (D.mesh.box K).rect, ∑' ι, chargeTerm D R K q v G H ι p)
        + ∫ p in (D.mesh.box K).rect, ∑' ι, stretchTerm D (P.potential K).harmonicLabels X ι p := by
    have hA : IntegrableOn (fun p => ∑ ι ∈ D.mesh.resolved K,
        (leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p)
        + ∑' ι, chargeTerm D R K q v G H ι p) (D.mesh.box K).rect := hsumI.add hcI
    have i1 := integral_add hA hsI
    have i2 := integral_add hsumI hcI
    beta_reduce at i1 i2
    rw [i1, i2]
  rw [hsplit1, integral_finsetSum _ hleafI, hcE, hsE] at hI
  have e1 : ∀ ι ∈ D.mesh.resolved K, (∫ p in (D.mesh.box K).rect,
      (leafCore D R K X ι p - boxCore D R K X ι p + absorbCore D R K X ι p))
      = (∫ p in (D.mesh.box K).rect, leafCore D R K X ι p) - (∫ p in (D.mesh.box K).rect, boxCore D R K X ι p)
        + ∫ p in (D.mesh.box K).rect, absorbCore D R K X ι p := by
    intro ι hι
    have hsub : IntegrableOn (fun p => leafCore D R K X ι p - boxCore D R K X ι p) (D.mesh.box K).rect :=
      (hloc ι hι).1.sub (hloc ι hι).2.1
    have i1 := integral_add hsub (hloc ι hι).2.2
    have i2 := integral_sub (hloc ι hι).1 (hloc ι hι).2.1
    beta_reduce at i1 i2
    rw [i1, i2]
  rw [Finset.sum_congr rfl e1, Finset.sum_add_distrib, Finset.sum_sub_distrib] at hI
  have eL : leafPair D R K X X = ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect, leafCore D R K X ι p := rfl
  have eA : alAmount D R K X = ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect, absorbCore D R K X ι p := rfl
  have eB : boxPairAmount D R K (restrictTo (D.mesh.resolved K : Set (ℤ × ℤ)) X)
      = ∑ ι ∈ D.mesh.resolved K, ∫ p in (D.mesh.box K).rect, boxCore D R K X ι p := by
    unfold boxPairAmount
    refine Finset.sum_congr rfl fun ι hι => ?_
    have : ∀ p, restrictTo (D.mesh.resolved K : Set (ℤ × ℤ)) X ι p = X ι p := fun p => by
      simp [restrictTo, hι]
    simp only [this]
    rfl
  have hab' : alAmount D R K X
      = alAmount D R K (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)))
        + alAmount D R K (tailProfiles D R K v G) := hab
  show -alAmount D R K (lowAt D R K (bandPart D R K (P.potential K) (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η)))
        - alAmount D R K (tailProfiles D R K v G)
        + boxPairAmount D R K (restrictTo (D.mesh.resolved K : Set (ℤ × ℤ)) X)
      ≤ leafPair D R K X X + trueStretch D K (P.potential K).harmonicLabels X X + stretchChargeAmount D R K q v G H
  rw [eL, eB]
  linarith [hI, hab', eA]

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown
