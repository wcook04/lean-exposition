import TorusEuler.HierarchyTransverseNorms
import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.Proofs.S53.Library.CopyConstHTN
import TorusEuler.Paper.Proofs.S53.Library.CopyLAC
import TorusEuler.Paper.Proofs.S53.Library.CopyLACaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODEaux
import TorusEuler.Paper.Proofs.S53.Library.CopyODE
import TorusEuler.Paper.Proofs.S53.Library.CopySDB
import TorusEuler.Paper.Proofs.S53.Library.CopyPSJ

/-!
# S53 library: Lemma 5.3 chain: transverse norms

Generated copy (script `s53tools/mkcopy.py`) of the declarations TransverseResult.norm_bound, contDiff_pressureCoefficients of
`TorusEuler/HierarchyTransverseNorms.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

open TorusEuler.HierarchyTwistedProfile
section WordNorm

variable {T : ℝ} {k : Vec3} {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

end WordNorm

section SelectedSolve

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- Copy of the library lemma `TorusEuler.contDiff_pressureCoefficients` (glue), placed in `Paper.Lib.S53`. -/
theorem contDiff_pressureCoefficients {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {M : P → Vec3 →L[ℝ] Vec3} {κ : P → Vec3}
    (hM : ContDiff ℝ ∞ M) (hκ : ContDiff ℝ ∞ κ) (hn : ∀ p, κ p ≠ 0) :
    ContDiff ℝ ∞ (fun p => hierarchyRelayPressureAmplitudeCoefficient (M p) (κ p)) ∧
      ContDiff ℝ ∞ (fun p => hierarchyRelayPressureSourceCoefficient (κ p)) := by
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hL : ContDiff ℝ ∞ (fun p => L (κ p)) := L.contDiff.comp hκ
  have hInv : ContDiff ℝ ∞ (fun p => (‖κ p‖ ^ 2)⁻¹) :=
    (hκ.norm_sq ℝ).inv fun p => pow_ne_zero _ (norm_ne_zero_iff.mpr (hn p))
  exact ⟨((contDiff_const (c := (-2 : ℝ))).mul hInv).smul (hL.clm_comp hM), hInv.smul hL⟩

set_option maxHeartbeats 1800000 in
/-- The actual selected velocity and pressure satisfy the quantitative
inverse estimate in the measured active-slab seminorm. The positive
coefficient-word bound enters only through its dimensionless budget. -/
theorem TransverseResult.norm_bound
    {U : Type} [NormedAddCommGroup U] [NormedSpace ℝ U] [FiniteDimensional ℝ U]
    {hT : 0 < T} {G M : MP} {κ F : VP} (r : TransverseResult hT G M κ F)
    (d : TransverseCoefficients M κ)
    (hFavg : (twistedHierarchyOperators hT G M κ).average F = 0) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ < T)
    {S : Set Vec3} (hS : IsClosed S)
    (hF : ∀ t ∈ Icc 0 T, ∀ a s, t < t₀ ∨ a ∉ S → F.val.val.val (t,a,s) = 0)
    {γ dγ : ℝ → ℝ} (hγ : ContinuousOn γ (Icc t₀ T))
    (hγ₀ : ∀ t ∈ Icc t₀ T, 0 < γ t)
    (hγt : ∀ t ∈ Icc t₀ T, HasDerivWithinAt γ (dγ t) (Icc t₀ T) t)
    (hdγ : ContinuousOn dγ (Icc t₀ T))
    {J : ℝ → Vec3 → U →L[ℝ] Vec3} {R : ℝ → Vec3 → Vec3 →L[ℝ] U}
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (Icc t₀ T ×ˢ univ))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (Icc t₀ T ×ˢ univ))
    (hJt : ∀ a t, t ∈ Icc t₀ T →
      HasDerivWithinAt (fun u => J u a) ((d.strain t a).comp (J t a)) (Icc t₀ T) t)
    (hRJ : ∀ a t, t ∈ Icc t₀ T → (R t a).comp (J t a) = .id ℝ U)
    (hJR : ∀ a t, t ∈ Icc t₀ T →
      (J t a).comp (R t a) = oscillatoryTransverseProjection (d.covector t a))
    {ℓ h freq K C Ccomm CJ CR CA CB : ℝ} {n : ℕ}
    (hfreq : 0 < freq) (hℓ : 0 < ℓ) (hh : 0 < h) (hK : 0 ≤ K) (hC : 0 ≤ C) (hbudget : K * (T - t₀) * C ≤ Ccomm)
    (hκne : ∀ a t, t ∈ Icc t₀ T → d.covector t a ≠ 0)
    (hJB : HierarchyRelayWordBound ℓ h n CJ (fun (t : Icc t₀ T) p => J t p.1))
    (hRB : HierarchyRelayWordBound ℓ h n CR (fun (t : Icc t₀ T) p => R t p.1))
    (hCAB : HierarchyRelayWordBound ℓ h n CA (fun (t : Icc t₀ T) p =>
      hierarchyRelayPressureAmplitudeCoefficient (d.strain t p.1) (freq⁻¹ • d.covector t p.1)))
    (hCBB : HierarchyRelayWordBound ℓ h n CB (fun (t : Icc t₀ T) p =>
      hierarchyRelayPressureSourceCoefficient (freq⁻¹ • d.covector t p.1))) :
    let A (t : ℝ) (p : Vec3 × ℝ) := fixedTransverseGenerator (d.strain t p.1) (J t p.1) (R t p.1)
    let Wv := amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT.le γ hγ hγ₀
    let Wp := amplitudeSeminorm (E := ℝ) (k := k) False ℓ h n hT ht₀ htT.le γ hγ hγ₀
    (∀ p : Vec3 × ℝ, p.1 ∈ S → ∀ y : ℝ → U,
      (∀ u ∈ Icc t₀ T, HasDerivWithinAt y (A u p (y u)) (Icc t₀ T) u) →
      ∀ u ∈ Icc t₀ T, ∀ v ∈ Icc u T, ‖y v‖ / γ v ≤ K * (‖y u‖ / γ u)) →
    (∀ w ∈ hierarchyAdmissibleWords (Fin 4) n, w ≠ [] → ∀ p : Vec3 × ℝ, p.1 ∈ S →
      ∀ t ∈ Icc t₀ T, ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A t) p‖ ≤ C) →
    Wv r.output.V + freq * Wp r.output.p ≤
      transverseSolveNormConstant n (T - t₀) K Ccomm CJ CR CA CB * Wv F := by
  let I := Icc t₀ T
  let V (t : ℝ) (p : Vec3 × ℝ) := r.output.V.val.val.val (t,p)
  let Q (t : ℝ) (p : Vec3 × ℝ) := r.output.p.val.val.val (t,p)
  let f (t : ℝ) (p : Vec3 × ℝ) := F.val.val.val (t,p)
  let q (t : ℝ) (p : Vec3 × ℝ) := deriv (fun s => Q t (p.1,s)) p.2
  let κn (t : ℝ) (a : Vec3) := freq⁻¹ • d.covector t a
  let Wv := amplitudeSeminorm (E := Vec3) (k := k) False ℓ h n hT ht₀ htT.le γ hγ hγ₀
  let H := Wv F
  let VC := transverseVelocityWordConstant n (T - t₀) K Ccomm CJ CR
  let PC := 2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
    ((2 : ℝ) ^ n * CA * VC + (2 : ℝ) ^ n * CB))
  have hI : I ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hS' : IsClosed (S ×ˢ (univ : Set ℝ)) := hS.prod isClosed_univ
  dsimp only
  intro hStable hCoeff
  have hvS : ContDiffOn ℝ ∞ (Function.uncurry V) (I ×ˢ univ) :=
    (HierarchySmoothProfile.smooth r.output.V.val.val).mono (prod_mono hI le_rfl)
  have hfS : ContDiffOn ℝ ∞ (Function.uncurry f) (I ×ˢ univ) :=
    (HierarchySmoothProfile.smooth F.val.val).mono (prod_mono hI le_rfl)
  have hMc := d.strain_smooth.mono (prod_mono hI (Subset.rfl : (univ : Set Vec3) ⊆ univ))
  have hzeroV : V t₀ = 0 := by
    funext p
    rcases ht₀.eq_or_lt with h0 | h0
    · exact (congrArg (fun t : ℝ => V t p) h0).symm.trans (r.velocity_initial p.1 p.2)
    · have hz := r.inactive t₀ S hF
      have hz' : EqOn r.output.V.val.val.val 0 (hierarchyInactiveRegion T t₀ S) :=
        fun x hx => (hz x.1 hx.1.1 x.2.1 x.2.2 hx.2).1
      exact HierarchySmoothProfile.eq_zero_at_activation r.output.V.val.val h0 htT.le hz' p.1 p.2
  have hvEq (p : Vec3 × ℝ) (t : ℝ) (ht : t ∈ I) :
      HasDerivWithinAt (fun u => V u p) (f t p - d.strain t p.1 (V t p) -
        q t p • d.covector t p.1) I t := by
    have he := (r.velocity_equation t (hI ht) p.1 p.2).mono hI
    rw [d.strain_value _ ⟨hI ht, mem_univ _⟩, d.covector_value _ ⟨hI ht, mem_univ _⟩] at he
    exact he
  have hvκ (p : Vec3 × ℝ) (t : ℝ) (ht : t ∈ I) :
      ⟪d.covector t p.1, V t p⟫_ℝ = 0 := by
    have he := r.transverse t (hI ht) p.1 p.2
    rwa [d.covector_value _ ⟨hI ht, mem_univ _⟩] at he
  have hfOff (p : Vec3 × ℝ) (hp : p ∉ S ×ˢ (univ : Set ℝ)) (t : ℝ) (ht : t ∈ I) : f t p = 0 :=
    hF t (hI ht) p.1 p.2 (Or.inr fun ha => hp ⟨ha, mem_univ _⟩)
  have hFB : HierarchyRelayWordBound ℓ h n H (fun (t : I) p => (γ t)⁻¹ • f t p) :=
    wordBound_of_amplitudeSeminorm hT ht₀ htT.le hγ hγ₀ ℓ h n F
  have hvB' := oscillatoryVelocity_weightedWordBound
    (J := J) (R := R) (M := d.strain) (κ := d.covector) (V := V) (f := f) (q := q)
    (S := S ×ˢ (univ : Set ℝ)) n htT hK hC hbudget hS' hJ hR hMc hfS hvS hzeroV
    hJt hRJ hJR hvEq hvκ hfOff hγ₀ hγt hdγ hJB hRB hFB
    (fun p hp => hStable p hp.1) (fun w hw hn p hp => hCoeff w hw hn p hp.1)
  have hvB : HierarchyRelayWordBound ℓ h n (VC * H) (fun (t : I) p => (γ t)⁻¹ • V t p) := by
    convert hvB' using 1
    unfold VC transverseVelocityWordConstant
    ring
  have hVnorm := amplitudeSeminorm_le_of_wordBound hT ht₀ htT.le hγ hγ₀
    (f := r.output.V) hvB
  let pA (t : I) (p : Vec3 × ℝ) :=
    hierarchyRelayPressureAmplitudeCoefficient (d.strain t p.1) (κn t p.1)
  let pB (t : I) (p : Vec3 × ℝ) := hierarchyRelayPressureSourceCoefficient (κn t p.1)
  have hCs (t : I) : ContDiff ℝ ∞ (pA t) ∧ ContDiff ℝ ∞ (pB t) := by
    have hms : ContDiff ℝ ∞ (d.strain t) := contDiffOn_univ.mp
      (hMc.comp (contDiff_const.prodMk contDiff_id).contDiffOn (fun _ _ => ⟨t.property, mem_univ _⟩))
    have hks : ContDiff ℝ ∞ (d.covector t) := contDiffOn_univ.mp
      (d.covector_smooth.comp (contDiff_const.prodMk contDiff_id).contDiffOn
        (fun _ _ => ⟨hI t.property, mem_univ _⟩))
    exact contDiff_pressureCoefficients (hms.comp contDiff_fst) ((hks.comp contDiff_fst).const_smul _)
      (fun p => smul_ne_zero (inv_ne_zero hfreq.ne') (hκne p.1 t t.property))
  have hFslice (t : I) : ContDiff ℝ ∞ (f t) := HierarchySmoothProfile.contDiff_labelPhase_slice F.val.val (hI t.property)
  have hVslice (t : I) : ContDiff ℝ ∞ (V t) :=
    HierarchySmoothProfile.contDiff_labelPhase_slice r.output.V.val.val (hI t.property)
  have hVmean (t : I) (a : Vec3) : phaseMean (fun s => V t (a,s)) = 0 := by
    have he := congrArg (fun v : VP => v.val.val.val (t,a,0)) r.output.average_V
    change (HierarchySmoothProfile.profilePhaseAverage hT r.output.V.val.val).val (t,a,0) = 0 at he
    rwa [HierarchySmoothProfile.profilePhaseAverage_apply hT _ ⟨hI t.property, mem_univ _⟩] at he
  have hFmean (t : I) (a : Vec3) : phaseMean (fun s => f t (a,s)) = 0 := by
    have he := congrArg (fun v : VP => v.val.val.val (t,a,0)) hFavg
    change (HierarchySmoothProfile.profilePhaseAverage hT F.val.val).val (t,a,0) = 0 at he
    rwa [HierarchySmoothProfile.profilePhaseAverage_apply hT _ ⟨hI t.property, mem_univ _⟩] at he
  have hpB := oscillatoryPhasePressure_weightedWordBound
    (T := I) (M := fun t => d.strain t) (κ := fun t => κn t) (V := fun t => V t) (f := fun t => f t)
    (g := fun t => γ t) hfreq hℓ hh hVslice hFslice (fun t a => HierarchyPeriodicProfile.phasePeriodic r.output.V.val t a)
    (fun t a => HierarchyPeriodicProfile.phasePeriodic F.val t a) hVmean hFmean (fun t => (hCs t).1) (fun t => (hCs t).2)
    hCAB hCBB hvB hFB
  have hPressureEq (t : I) (p : Vec3 × ℝ) :
      Q t p = oscillatoryPhasePressure (d.strain t p.1) (freq • κn t p.1)
        (fun s => f t (p.1,s)) (fun s => V t (p.1,s)) p.2 := by
    have hq := r.pressure_value t (hI t.property) p.1 p.2
    rw [d.strain_value _ ⟨hI t.property, mem_univ _⟩, d.covector_value _ ⟨hI t.property, mem_univ _⟩] at hq
    simpa only [κn, smul_smul, mul_inv_cancel₀ hfreq.ne', one_smul] using hq
  have hpB' : HierarchyRelayWordBound ℓ h n (PC * H)
      (fun (t : I) p => (γ t)⁻¹ • freq • Q t p) := by
    convert hpB using 1
    · unfold PC
      ring
    · funext t p
      rw [hPressureEq]
  have hnormP := freq_mul_amplitudeSeminorm_le_of_wordBound hT ht₀ htT.le hγ hγ₀
    (f := r.output.p) hfreq.le hpB'
  refine (add_le_add hVnorm hnormP).trans_eq ?_
  unfold transverseSolveNormConstant
  dsimp only [VC, PC, H, Wv]
  ring

end SelectedSolve

section PhysicalCoframe

variable {T : ℝ} {k : Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3
local notation "MP" => HierarchyTwistedProfile T k (Vec3 →L[ℝ] Vec3)
local notation "Plane" => transversePlane k

end PhysicalCoframe

end TorusEuler.Paper.Lib.S53.HierarchyTwistedProfile

