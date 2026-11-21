import TorusEuler.OscillatoryDerivativeEstimates
import TorusEuler.Paper.Proofs.S53.Library.Leaves
import TorusEuler.Paper.Proofs.S53.Library.CopyODEaux
import TorusEuler.Paper.Proofs.S53.Library.CopyLAC

/-!
# S53 library: Lemma 5.3 chain: oscillatory word estimates

Generated copy (script `s53tools/mkcopy.py`) of the declarations oscillatoryVelocity_weightedWordBound_of_initial, linearODE_weightedHierarchyWordBound_of_initial, oscillatoryPhasePressure_weightedWordBound, oscillatoryVelocity_weightedWordBound of
`TorusEuler/OscillatoryDerivativeEstimates.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ContDiff InnerProductSpace Interval Topology

namespace TorusEuler.Paper.Lib.S53

open TorusEuler
section WordDerivative

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

end WordDerivative

section LinearODE

variable {ι P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

end LinearODE

section FiniteNorm

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

set_option maxHeartbeats 900000 in
/-- The weighted derivative estimate applies to localized initial data
and forcing on the active interval. Stability and positive-order
coefficient estimates are used on their common closed support. -/
theorem linearODE_weightedHierarchyWordBound_of_initial
    {A : ℝ → (Vec3 × ℝ) → E →L[ℝ] E} {f x : ℝ → (Vec3 × ℝ) → E}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm B H ℓ h : ℝ} (N : ℕ)
    (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hx : ContDiffOn ℝ ∞ (Function.uncurry x) (Icc l r ×ˢ univ))
    (hx₀ : ∀ p ∉ S, x l p = 0)
    (hxt : ∀ p t, t ∈ Icc l r →
      HasDerivWithinAt (fun s => x s p) (A t p (x t p) + f t p) (Icc l r) t)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hStable : ∀ p ∈ S, ∀ y : ℝ → E,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u))
    (hinit : HierarchyRelayWordBound ℓ h N B
      (fun (_ : Icc l r) p => (g l)⁻¹ • x l p))
    (hsource : HierarchyRelayWordBound ℓ h N H
      (fun (u : Icc l r) p => (g u)⁻¹ • f u p))
    (hcoeff : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) :
    HierarchyRelayWordBound ℓ h N (linearODEWordFactor Ccomm N * (K * (B + (r - l) * H)))
      (fun (u : Icc l r) p => (g u)⁻¹ • x u p) := by
  let d (i : Fin 4) : Vec3 × ℝ := hierarchyMixedDirection ℓ h i 0
  have hd : (fun i (_ : Vec3 × ℝ) => d i) = hierarchyMixedDirection ℓ h := rfl
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr.le⟩
  have hT : 0 ≤ r - l := sub_nonneg.mpr hlr.le
  have hα : 0 ≤ K * (r - l) * C := by positivity
  have hB : 0 ≤ linearODEWordFactor Ccomm N * (K * (B + (r - l) * H)) := by
    exact mul_nonneg (linearODEWordFactor_nonneg (hα.trans hcomm) N)
      (mul_nonneg hK (add_nonneg hinit.1 (mul_nonneg hT hsource.1)))
  have hs (w : List (Fin 4)) (hw : w.length ≤ N) :
      w.mergeSort ∈ hierarchyAdmissibleWords (Fin 4) N :=
    mem_hierarchyAdmissibleWords.mpr
      ⟨(List.mergeSort_perm _ _).length_eq.le.trans hw, List.pairwise_mergeSort' _ _⟩
  have hsource' (w : List (Fin 4)) (hw : w.length ≤ N) (p : Vec3 × ℝ) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖phaseOperatorWord (fun i _ => d i) w (f u) p‖ / g u ≤ H := by
    have hfu := contDiff_slabSlice hf hu
    rw [← phaseOperatorWord_constantDirections_perm d hfu (List.mergeSort_perm w _),
      ← norm_word_inv_smul hfu (hg₀ u hu), hd]
    exact hsource.2 (w.mergeSort) (hs w hw) ⟨u, hu⟩ p
  have hcoeff' (w : List (Fin 4)) (hw : w.length ≤ N) (hn : w ≠ [])
      (p : Vec3 × ℝ) (hp : p ∈ S) (u : ℝ) (hu : u ∈ Icc l r) :
      ‖phaseOperatorWord (fun i _ => d i) w (A u) p‖ ≤ C := by
    have hperm : w.mergeSort.Perm w := List.mergeSort_perm _ _
    have hnil : w.mergeSort ≠ [] := fun h => hn (List.Perm.nil_eq (h ▸ hperm)).symm
    rw [← phaseOperatorWord_constantDirections_perm d (contDiff_slabSlice hA hu) hperm, hd]
    exact hcoeff (w.mergeSort) (hs w hw) hnil p hp u hu
  have hinitial (w : List (Fin 4)) (hw : w.length ≤ N) (p : Vec3 × ℝ) :
      ‖phaseOperatorWord (fun i _ => d i) w (x l) p‖ / g l ≤ B := by
    have hxl := contDiff_slabSlice hx hl
    rw [← phaseOperatorWord_constantDirections_perm d hxl (List.mergeSort_perm w _),
      ← norm_word_inv_smul hxl (hg₀ l hl), hd]
    exact hinit.2 (w.mergeSort) (hs w hw) ⟨l, hl⟩ p
  have hwords := linearODE_wordBounds_Icc d N (S := S) hlr hK hC hinit.1 hsource.1
    hA hf hx hxt hg₀ hg hdg hStable (fun w hw p _ => hinitial w hw p)
    (fun w hw p _ => hsource' w hw p) hcoeff'
  have hxOutside (p : Vec3 × ℝ) (hp : p ∉ S) (u : ℝ) (hu : u ∈ Icc l r) : x u p = 0 := by
    have hAp : ContinuousOn (fun t => A t p) (Icc l r) :=
      hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun _ ht => ⟨ht, mem_univ p⟩)
    have hXp (t : ℝ) (ht : t ∈ Icc l r) :
        HasDerivWithinAt (fun s => x s p) (A t p (x t p)) (Icc l r) t := by
      simpa only [hfs p hp t ht, add_zero] using hxt p t ht
    exact linearODE_unique_of_mem (y := fun _ => (0 : E)) ordConnected_Icc hl hAp hXp
      (fun t _ => by simpa only [map_zero] using hasDerivWithinAt_const t (Icc l r) (0 : E))
      (hx₀ p hp) hu
  refine ⟨hB, fun w hw u p => ?_⟩
  rw [← hd, norm_word_inv_smul (contDiff_slabSlice hx u.property) (hg₀ u u.property)]
  by_cases hp : p ∈ S
  · refine (hwords w (mem_hierarchyAdmissibleWords.mp hw).1 p hp u u.property).trans ?_
    exact mul_le_mul_of_nonneg_right (linearODEWordFactor_mono hα hcomm N)
      (mul_nonneg hK (add_nonneg hinit.1 (mul_nonneg hT hsource.1)))
  · have hN : ∀ᶠ q in 𝓝 p, q ∈ Sᶜ := hS.isOpen_compl.mem_nhds hp
    have heq : x u =ᶠ[𝓝 p] (0 : Vec3 × ℝ → E) :=
      hN.mono fun q hq => hxOutside q hq u u.property
    rw [(phaseOperatorWord_eventuallyEq (D := fun i _ => d i) heq w).eq_of_nhds,
      phaseOperatorWord_zero, Pi.zero_apply, norm_zero, zero_div]
    exact hB

end FiniteNorm

section FixedCoordinates

variable {E F : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

end FixedCoordinates

set_option maxHeartbeats 1300000 in
/-- The finite weighted norm of the physical transverse velocity follows
from the fixed-plane forward estimate and the word bounds of the two
coframes. The force is measured in physical coordinates. -/
theorem oscillatoryVelocity_weightedWordBound_of_initial
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : ℝ → Vec3 → F →L[ℝ] Vec3} {R : ℝ → Vec3 → Vec3 →L[ℝ] F}
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {V f : ℝ → (Vec3 × ℝ) → Vec3} {q : ℝ → (Vec3 × ℝ) → ℝ}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm CJ CR B H ℓ h : ℝ}
    (N : ℕ) (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (Icc l r ×ˢ univ))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (Icc l r ×ˢ univ))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc l r ×ˢ univ))
    (hV₀ : ∀ p ∉ S, V l p = 0)
    (hJt : ∀ a t, t ∈ Icc l r → HasDerivWithinAt (fun u => J u a) ((M t a).comp (J t a)) (Icc l r) t)
    (hRJ : ∀ a t, t ∈ Icc l r → (R t a).comp (J t a) = .id ℝ F)
    (hJR : ∀ a t, t ∈ Icc l r → (J t a).comp (R t a) = oscillatoryTransverseProjection (κ t a))
    (hVt : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (fun u => V u p)
      (f t p - M t p.1 (V t p) - q t p • κ t p.1) (Icc l r) t)
    (hVκ : ∀ p t, t ∈ Icc l r → ⟪κ t p.1, V t p⟫_ℝ = 0)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hJN : HierarchyRelayWordBound ℓ h N CJ (fun (u : Icc l r) p => J u p.1))
    (hRN : HierarchyRelayWordBound ℓ h N CR (fun (u : Icc l r) p => R u p.1))
    (hInit : HierarchyRelayWordBound ℓ h N B (fun (_ : Icc l r) p => (g l)⁻¹ • V l p))
    (hfN : HierarchyRelayWordBound ℓ h N H (fun (u : Icc l r) p => (g u)⁻¹ • f u p)) :
    let A (t : ℝ) (p : Vec3 × ℝ) := (-2 : ℝ) • (R t p.1).comp ((M t p.1).comp (J t p.1))
    (∀ p ∈ S, ∀ y : ℝ → F,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u)) →
    (∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) →
    HierarchyRelayWordBound ℓ h N
      ((2 : ℝ) ^ N * CJ * (linearODEWordFactor Ccomm N *
        (K * ((2 : ℝ) ^ N * CR * B + (r - l) * ((2 : ℝ) ^ N * CR * H)))))
      (fun (u : Icc l r) p => (g u)⁻¹ • V u p) := by
  let A (t : ℝ) (p : Vec3 × ℝ) := (-2 : ℝ) • (R t p.1).comp ((M t p.1).comp (J t p.1))
  let X (t : ℝ) (p : Vec3 × ℝ) := R t p.1 (V t p)
  let fR (t : ℝ) (p : Vec3 × ℝ) := R t p.1 (f t p)
  let D := Icc l r ×ˢ (univ : Set (Vec3 × ℝ))
  dsimp only
  intro hStable hcoeff
  have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (Vec3 × ℝ) => (z.1, z.2.1)) D :=
    contDiffOn_fst.prodMk contDiffOn_snd.fst
  have hm : MapsTo (fun z : ℝ × (Vec3 × ℝ) => (z.1, z.2.1)) D
      (Icc l r ×ˢ (univ : Set Vec3)) := fun z hz => ⟨hz.1, mem_univ z.2.1⟩
  have hJ' : ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : Vec3 × ℝ) => J t p.1)) D :=
    hJ.comp hproj hm
  have hR' : ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : Vec3 × ℝ) => R t p.1)) D :=
    hR.comp hproj hm
  have hM' : ContDiffOn ℝ ∞ (Function.uncurry (fun t (p : Vec3 × ℝ) => M t p.1)) D :=
    hM.comp hproj hm
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) D :=
    (contDiffOn_const (c := (-2 : ℝ))).smul (hR'.clm_comp (hM'.clm_comp hJ'))
  have hX : ContDiffOn ℝ ∞ (Function.uncurry X) D := hR'.clm_apply hV
  have hfR : ContDiffOn ℝ ∞ (Function.uncurry fR) D := hR'.clm_apply hf
  have hX₀ (p : Vec3 × ℝ) (hp : p ∉ S) : X l p = 0 := by simp [X, hV₀ p hp]
  have hXode (p : Vec3 × ℝ) (t : ℝ) (ht : t ∈ Icc l r) :
      HasDerivWithinAt (fun u => X u p) (A t p (X t p) + fR t p) (Icc l r) t := by
    have hRc : ContDiffOn ℝ ∞ (fun u => R u p.1) (Icc l r) :=
      hR.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun _ hu => ⟨hu, mem_univ p.1⟩)
    have hRd : HasDerivWithinAt (fun u => R u p.1)
        (derivWithin (fun u => R u p.1) (Icc l r) t) (Icc l r) t :=
      (hRc.differentiableOn (by simp) t ht).hasDerivWithinAt
    have hd := hasDerivWithinAt_oscillatory_fixedCoordinates
      (J := fun u => J u p.1) (R := fun u => R u p.1) (V := fun u => V u p)
      (M := M t p.1) (κ := κ t p.1) (f := f t p) (q := q t p) ht (uniqueDiffOn_Icc hlr t ht)
      (hRJ p.1) (hJR p.1 t ht) (hJt p.1 t ht) hRd (hVt p t ht) (hVκ p t ht)
    exact hd
  let ForceBound := (2 : ℝ) ^ N * CR * H
  have hfRN : HierarchyRelayWordBound ℓ h N ForceBound
      (fun (u : Icc l r) p => (g u)⁻¹ • fR u p) := by
    have hfRW := HierarchyRelayWordBound.clm_apply
      (f := fun (u : Icc l r) p => R u p.1) (g := fun u p => (g u)⁻¹ • f u p)
      (fun u => contDiff_slabSlice hR' u.property)
      (fun u => (contDiff_slabSlice hf u.property).const_smul _) hRN hfN
    simpa only [fR, map_smul] using hfRW
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr.le⟩
  have hInitial : HierarchyRelayWordBound ℓ h N ((2 : ℝ) ^ N * CR * B)
      (fun (_ : Icc l r) p => (g l)⁻¹ • X l p) := by
    have hRead : HierarchyRelayWordBound ℓ h N CR (fun (_ : Icc l r) p => R l p.1) :=
      ⟨hRN.1, fun w hw _ p => hRN.2 w hw ⟨l, hl⟩ p⟩
    have hProd := HierarchyRelayWordBound.clm_apply
      (f := fun (_ : Icc l r) p => R l p.1) (g := fun _ p => (g l)⁻¹ • V l p)
      (fun _ => contDiff_slabSlice hR' hl)
      (fun _ => (contDiff_slabSlice hV hl).const_smul _) hRead hInit
    simpa only [X, map_smul] using hProd
  have hXN := linearODE_weightedHierarchyWordBound_of_initial N
    (A := A) (f := fR) (x := X) (S := S) hlr hK hC hcomm hS
    hA hfR hX hX₀ hXode (fun p hp u hu => by simp [fR, hfs p hp u hu])
    hg₀ hg hdg hStable hInitial hfRN hcoeff
  have hLift := HierarchyRelayWordBound.clm_apply
    (f := fun (u : Icc l r) p => J u p.1) (g := fun u p => (g u)⁻¹ • X u p)
    (fun u => contDiff_slabSlice hJ' u.property)
    (fun u => (contDiff_slabSlice hX u.property).const_smul _) hJN hXN
  have heq (u : Icc l r) (p : Vec3 × ℝ) : J u p.1 ((g u)⁻¹ • X u p) = (g u)⁻¹ • V u p := by
    rw [map_smul]
    congr 1
    change ((J u p.1).comp (R u p.1)) (V u p) = _
    rw [hJR p.1 u u.property, oscillatoryTransverseProjection_apply, hVκ p u u.property,
      zero_div, zero_smul, sub_zero]
  simpa only [heq, ForceBound] using hLift

/-- Zero-start version of the weighted estimate for the transverse velocity. -/
theorem oscillatoryVelocity_weightedWordBound
    {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    {J : ℝ → Vec3 → F →L[ℝ] Vec3} {R : ℝ → Vec3 → Vec3 →L[ℝ] F}
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {V f : ℝ → (Vec3 × ℝ) → Vec3} {q : ℝ → (Vec3 × ℝ) → ℝ}
    {g dg : ℝ → ℝ} {S : Set (Vec3 × ℝ)} {l r K C Ccomm CJ CR H ℓ h : ℝ}
    (N : ℕ) (hlr : l < r) (hK : 0 ≤ K) (hC : 0 ≤ C) (hcomm : K * (r - l) * C ≤ Ccomm)
    (hS : IsClosed S)
    (hJ : ContDiffOn ℝ ∞ (Function.uncurry J) (Icc l r ×ˢ univ))
    (hR : ContDiffOn ℝ ∞ (Function.uncurry R) (Icc l r ×ˢ univ))
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc l r ×ˢ univ))
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc l r ×ˢ univ))
    (hV : ContDiffOn ℝ ∞ (Function.uncurry V) (Icc l r ×ˢ univ))
    (hV₀ : V l = 0)
    (hJt : ∀ a t, t ∈ Icc l r → HasDerivWithinAt (fun u => J u a) ((M t a).comp (J t a)) (Icc l r) t)
    (hRJ : ∀ a t, t ∈ Icc l r → (R t a).comp (J t a) = .id ℝ F)
    (hJR : ∀ a t, t ∈ Icc l r → (J t a).comp (R t a) = oscillatoryTransverseProjection (κ t a))
    (hVt : ∀ p t, t ∈ Icc l r → HasDerivWithinAt (fun u => V u p)
      (f t p - M t p.1 (V t p) - q t p • κ t p.1) (Icc l r) t)
    (hVκ : ∀ p t, t ∈ Icc l r → ⟪κ t p.1, V t p⟫_ℝ = 0)
    (hfs : ∀ p ∉ S, ∀ u ∈ Icc l r, f u p = 0)
    (hg₀ : ∀ u ∈ Icc l r, 0 < g u)
    (hg : ∀ u ∈ Icc l r, HasDerivWithinAt g (dg u) (Icc l r) u)
    (hdg : ContinuousOn dg (Icc l r))
    (hJN : HierarchyRelayWordBound ℓ h N CJ (fun (u : Icc l r) p => J u p.1))
    (hRN : HierarchyRelayWordBound ℓ h N CR (fun (u : Icc l r) p => R u p.1))
    (hfN : HierarchyRelayWordBound ℓ h N H (fun (u : Icc l r) p => (g u)⁻¹ • f u p)) :
    let A (t : ℝ) (p : Vec3 × ℝ) := (-2 : ℝ) • (R t p.1).comp ((M t p.1).comp (J t p.1))
    (∀ p ∈ S, ∀ y : ℝ → F,
      (∀ u ∈ Icc l r, HasDerivWithinAt y (A u p (y u)) (Icc l r) u) →
      ∀ u ∈ Icc l r, ∀ v ∈ Icc u r, ‖y v‖ / g v ≤ K * (‖y u‖ / g u)) →
    (∀ w ∈ hierarchyAdmissibleWords (Fin 4) N, w ≠ [] → ∀ p ∈ S, ∀ u ∈ Icc l r,
      ‖phaseOperatorWord (hierarchyMixedDirection ℓ h) w (A u) p‖ ≤ C) →
    HierarchyRelayWordBound ℓ h N
      ((2 : ℝ) ^ N * CJ * (linearODEWordFactor Ccomm N * (K * ((r - l) * ((2 : ℝ) ^ N * CR * H)))))
      (fun (u : Icc l r) p => (g u)⁻¹ • V u p) := by
  dsimp only
  intro hStable hcoeff
  have hInit : HierarchyRelayWordBound ℓ h N 0
      (fun (_ : Icc l r) p => (g l)⁻¹ • V l p) := by
    refine ⟨le_rfl, fun w _ _ p => ?_⟩
    simp only [hV₀, Pi.zero_apply, smul_zero]
    change ‖phaseOperatorWord (fun i (_ : Vec3 × ℝ) => hierarchyMixedDirection ℓ h i 0)
      w (0 : Vec3 × ℝ → Vec3) p‖ ≤ 0
    rw [phaseOperatorWord_zero, Pi.zero_apply, norm_zero]
  simpa only [mul_zero, zero_add] using
    oscillatoryVelocity_weightedWordBound_of_initial (S := S) N hlr hK hC hcomm hS hJ hR hM hf hV
      (fun p _ => by simp [hV₀]) hJt hRJ hJR hVt hVκ hfs hg₀ hg hdg hJN hRN hInit hfN hStable hcoeff

section Pressure

variable {T : Type}

/-- The actual normalized pressure has one inverse factor of the carrier at
every order, with the remaining constants given by the normalized covector
and strain coefficient bounds. -/
theorem oscillatoryPhasePressure_weightedWordBound
    {M : T → Vec3 → Vec3 →L[ℝ] Vec3} {κ : T → Vec3 → Vec3}
    {V f : T → (Vec3 × ℝ) → Vec3} {g : T → ℝ}
    {freq ℓ h A B V₀ F₀ : ℝ} {n : ℕ} (hfreq : 0 < freq) (hℓ : 0 < ℓ) (hh : 0 < h)
    (hV : ∀ t, ContDiff ℝ ∞ (V t)) (hf : ∀ t, ContDiff ℝ ∞ (f t))
    (hVp : ∀ t a, Function.Periodic (fun s => V t (a,s)) 1)
    (hfp : ∀ t a, Function.Periodic (fun s => f t (a,s)) 1)
    (hVz : ∀ t a, phaseMean (fun s => V t (a,s)) = 0)
    (hfz : ∀ t a, phaseMean (fun s => f t (a,s)) = 0)
    (ha : ∀ t, ContDiff ℝ ∞ (fun p : Vec3 × ℝ =>
      hierarchyRelayPressureAmplitudeCoefficient (M t p.1) (κ t p.1)))
    (hb : ∀ t, ContDiff ℝ ∞ (fun p : Vec3 × ℝ => hierarchyRelayPressureSourceCoefficient (κ t p.1)))
    (haN : HierarchyRelayWordBound ℓ h n A
      (fun t p => hierarchyRelayPressureAmplitudeCoefficient (M t p.1) (κ t p.1)))
    (hbN : HierarchyRelayWordBound ℓ h n B (fun t p => hierarchyRelayPressureSourceCoefficient (κ t p.1)))
    (hVN : HierarchyRelayWordBound ℓ h n V₀ (fun t p => (g t)⁻¹ • V t p))
    (hfN : HierarchyRelayWordBound ℓ h n F₀ (fun t p => (g t)⁻¹ • f t p)) :
    HierarchyRelayWordBound ℓ h n
      (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
        ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀)))
      (fun t p => (g t)⁻¹ • freq • oscillatoryPhasePressure (M t p.1) (freq • κ t p.1)
        (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2) := by
  let a (t : T) (x : Vec3) := hierarchyRelayPressureAmplitudeCoefficient (M t x) (κ t x)
  let b (t : T) (x : Vec3) := hierarchyRelayPressureSourceCoefficient (κ t x)
  let V' (t : T) (p : Vec3 × ℝ) := (g t)⁻¹ • V t p
  let f' (t : T) (p : Vec3 × ℝ) := (g t)⁻¹ • f t p
  have hV' (t : T) : ContDiff ℝ ∞ (V' t) := (hV t).const_smul _
  have hf' (t : T) : ContDiff ℝ ∞ (f' t) := (hf t).const_smul _
  have hVp' (t : T) (x : Vec3) : Function.Periodic (fun s => V' t (x,s)) 1 :=
    fun s => congrArg ((g t)⁻¹ • ·) (hVp t x s)
  have hfp' (t : T) (x : Vec3) : Function.Periodic (fun s => f' t (x,s)) 1 :=
    fun s => congrArg ((g t)⁻¹ • ·) (hfp t x s)
  have hVz' (t : T) (x : Vec3) : phaseMean (fun s => V' t (x,s)) = 0 := by
    change phaseMean (fun s => (g t)⁻¹ • V t (x,s)) = _
    rw [phaseMean_const_smul, hVz, smul_zero]
  have hfz' (t : T) (x : Vec3) : phaseMean (fun s => f' t (x,s)) = 0 := by
    change phaseMean (fun s => (g t)⁻¹ • f t (x,s)) = _
    rw [phaseMean_const_smul, hfz, smul_zero]
  let Q (t : T) (p : Vec3 × ℝ) :=
    phasePrimitive (fun s => a t p.1 (V' t (p.1,s)) + b t p.1 (f' t (p.1,s))) p.2
  have hP : HierarchyRelayWordBound ℓ h n
      (2 * ((hierarchyAdmissibleWords (Fin 4) n).card *
        ((2 : ℝ) ^ n * A * V₀ + (2 : ℝ) ^ n * B * F₀))) Q :=
    (hierarchyRelayWordBound_linearPrimitive (a := a) (b := b) (V := V') (f := f')
      hℓ hh ha hb hV' hf' hVp' hfp' hVz' hfz' haN hbN hVN hfN).2
  have heq (t : T) (p : Vec3 × ℝ) :
      (g t)⁻¹ • freq • oscillatoryPhasePressure (M t p.1) (freq • κ t p.1)
        (fun s => f t (p.1, s)) (fun s => V t (p.1, s)) p.2 = Q t p := by
    rw [oscillatoryPhasePressure_frequency_scale hfreq, smul_smul freq freq⁻¹,
      mul_inv_cancel₀ hfreq.ne', one_smul]
    unfold Q oscillatoryPhasePressure
    rw [← phasePrimitive_const_smul]
    congr 1
    funext s
    simp only [V', f', map_smul, ← smul_add, a, b, oscillatoryPressureSlope_eq_coefficients]
  simpa only [heq] using hP

end Pressure

end TorusEuler.Paper.Lib.S53

