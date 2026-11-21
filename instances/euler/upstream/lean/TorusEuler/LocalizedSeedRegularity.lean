import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import TorusEuler.ChildFlowDeformation
import TorusEuler.CoframeDerivativeBounds
import TorusEuler.EulerLimitClosure
import TorusEuler.FirstWaveLocalized
import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.LocalizedPhaseBounds
import TorusEuler.OscillatoryJointRegularity

/-! Smooth activation and spatial parity for the selected localized seed. -/

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace NNReal Topology

namespace TorusEuler

/-- The already selected labelwise linear trajectory is jointly smooth on
the closed physical time slab if its coefficient and initial profile are smooth. -/
theorem contDiffOn_selected_linearTrajectory {P E : Type}
    [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {a b : ℝ} (hab : a < b) {A : ℝ → P → E →L[ℝ] E} {X : ℝ → P → E}
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc a b ×ˢ (univ : Set P)))
    (hX₀ : ContDiff ℝ ∞ (X a))
    (hXt : ∀ p t, t ∈ Icc a b →
      HasDerivWithinAt (fun u => X u p) (A t p (X t p)) (Icc a b) t) :
    ContDiffOn ℝ ∞ (Function.uncurry X) (Icc a b ×ˢ (univ : Set P)) := by
  let T := b - a
  have hT : 0 < T := sub_pos.mpr hab
  let S : Set (ℝ × P) := Icc 0 T ×ˢ univ
  let B (t : ℝ) (p : P) := A (t + a) p
  have hforward : MapsTo (fun t : ℝ => t + a) (Icc 0 T) (Icc a b) := by
    intro t ht
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hback : MapsTo (fun t : ℝ => t - a) (Icc a b) (Icc 0 T) := by
    intro t ht
    exact ⟨sub_nonneg.mpr ht.1, sub_le_sub_right ht.2 a⟩
  have hB : ContDiffOn ℝ ∞ (Function.uncurry B) S :=
    hA.comp (((contDiff_fst.add contDiff_const).prodMk contDiff_snd).contDiffOn)
      (fun z hz => ⟨hforward hz.1, mem_univ _⟩)
  obtain ⟨x, hx, hx₀, hODE⟩ := exists_contDiff_parameterized_linearODE hT.le
    (contDiff_currySlab_of_contDiffOn hT hB)
    (contDiff_const (c := (0 : C(Icc (0 : ℝ) T, E)))) hX₀
  let V (t : ℝ) (p : P) := x p (projIcc 0 T hT.le t)
  have h0 : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, hT.le⟩
  have hV₀ : V 0 = X a := by
    funext p
    change x p (projIcc 0 T hT.le 0) = X a p
    rw [projIcc_of_mem hT.le h0]
    exact hx₀ p
  have hprojTime : Continuous (fun z : ℝ × P => projIcc 0 T hT.le z.1) :=
    continuous_projIcc.comp continuous_fst
  have hVc : Continuous (Function.uncurry V) :=
    continuous_eval.comp ((hx.continuous.comp continuous_snd).prodMk hprojTime)
  have hVt (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => V u p) (B t p (V t p)) (Icc 0 T) t := by
    have h := hODE p t ht
    change HasDerivWithinAt (fun u => V u p) (B t p (x p ⟨t, ht⟩) + (0 : E)) (Icc 0 T) t at h
    have heq : V t p = x p ⟨t, ht⟩ := by
      change x p (projIcc 0 T hT.le t) = _
      rw [projIcc_of_mem hT.le ht]
    rwa [← heq, add_zero] at h
  let Y (t : ℝ) (p : P) := (V t p, p)
  let W (t : ℝ) (z : E × P) := (B t z.2 z.1, (0 : P))
  have hW : ContDiffOn ℝ ∞ (Function.uncurry W) (Icc 0 T ×ˢ (univ : Set (E × P))) := by
    have hproj : ContDiffOn ℝ ∞ (fun z : ℝ × (E × P) => (z.1, z.2.2))
        (Icc 0 T ×ˢ (univ : Set (E × P))) := contDiffOn_fst.prodMk contDiffOn_snd.snd
    have hm : MapsTo (fun z : ℝ × (E × P) => (z.1, z.2.2))
        (Icc 0 T ×ˢ (univ : Set (E × P))) S := fun z hz => ⟨hz.1, mem_univ _⟩
    exact ((hB.comp hproj hm).clm_apply contDiffOn_snd.fst).prodMk contDiffOn_const
  have hY₀ : ContDiff ℝ ∞ (Y 0) := by
    change ContDiff ℝ ∞ (fun p => (V 0 p, p))
    rw [hV₀]
    exact hX₀.prodMk contDiff_id
  have hY : ContDiffOn ℝ ∞ (Function.uncurry Y) S :=
    trajectoryFamily_joint_contDiff (f := W) hT hW (hVc.continuousOn.prodMk continuousOn_snd)
      (fun p t ht => by
        simpa only [Y, W] using (hVt p t ht).prodMk (hasDerivWithinAt_const t (Icc 0 T) p)) hY₀
  have hshift (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivWithinAt (fun u => X (u + a) p) (B t p (X (t + a) p)) (Icc 0 T) t := by
    simpa only [Function.comp_def, B, one_smul, id_eq] using
      (hXt p (t + a) (hforward ht)).scomp t
        ((hasDerivWithinAt_id t (Icc 0 T)).add_const a) hforward
  have hEq (p : P) (t : ℝ) (ht : t ∈ Icc 0 T) : V t p = X (t + a) p := by
    have hBc : ContinuousOn (fun u => B u p) (Icc 0 T) :=
      hB.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun u hu => ⟨hu, mem_univ _⟩)
    have hstart : V 0 p = X (0 + a) p := by rw [hV₀, zero_add]
    exact linearODE_unique_of_mem ordConnected_Icc h0 hBc (hVt p) (hshift p) hstart ht
  have hV : ContDiffOn ℝ ∞ (Function.uncurry V) S := hY.fst
  refine (hV.comp
    (((contDiff_fst.sub contDiff_const).prodMk contDiff_snd).contDiffOn)
    (fun z hz => ⟨hback hz.1, mem_univ _⟩)).congr ?_
  intro z hz
  change X z.1 z.2 = V (z.1 - a) z.2
  exact ((hEq z.2 (z.1 - a) (hback hz.1)).trans
    (congrArg (fun t => X t z.2) (sub_add_cancel z.1 a))).symm

section ParentCoframeRegularity

variable {U : Velocity} {X : ℝ → Velocity} {T : ℝ}

/-- The actual forward flow is jointly smooth in time and label on the closed slab. -/
theorem IsLabelFlowOn.contDiffOn_forwardLabelFlow
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) :
    ContDiffOn ℝ ∞ (Function.uncurry (X 0)) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hinitial : X 0 0 = id := funext fun a => hX.initial 0 h₀ a
  exact trajectoryFamily_joint_contDiff hT hU (hX.continuousOn_time_label hK h₀)
    (fun a => hX.trajectory 0 h₀ a) (hinitial.symm ▸ contDiff_id)

/-- The forward deformation has joint closed-slab regularity. -/
theorem IsLabelFlowOn.contDiffOn_forwardLabelDerivative
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (X 0 z.1) z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
  contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT)
    (by simpa using hX.contDiffOn_forwardLabelFlow hT hU hper)

/-- The actual inverse deformation along the forward flow is jointly smooth.
The flow inverse identities identify it with the inverse of the forward deformation. -/
theorem IsLabelFlowOn.contDiffOn_inverseLabelDerivative
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (X z.1 0) (X 0 z.1 z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  let S := Icc (0 : ℝ) T ×ˢ (univ : Set Vec3)
  let F (z : ℝ × Vec3) := fderiv ℝ (X 0 z.1) z.2
  let G (z : ℝ × Vec3) := fderiv ℝ (X z.1 0) (X 0 z.1 z.2)
  have hF : ContDiffOn ℝ ∞ F S := hX.contDiffOn_forwardLabelDerivative hT hU hper
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hu (z : ℝ × Vec3) (hz : z ∈ S) :
      ∃ u : (Vec3 →L[ℝ] Vec3)ˣ, (u : Vec3 →L[ℝ] Vec3) = F z ∧
        Ring.inverse (F z) = G z := by
    obtain ⟨hGF, hFG⟩ := hX.labelDerivative_inverse hT (hU.of_le (by simp)) hper h₀ hz.1 z.2
    let u : (Vec3 →L[ℝ] Vec3)ˣ := ⟨F z, G z, hFG, hGF⟩
    exact ⟨u, rfl, Ring.inverse_unit u⟩
  have hFinv : ContDiffOn ℝ ∞ (Ring.inverse ∘ F) S := by
    intro z hz
    obtain ⟨u, hu, _⟩ := hu z hz
    have hi : ContDiffAt ℝ ∞ Ring.inverse (F z) := hu ▸ contDiffAt_ringInverse ℝ u
    exact hi.comp_contDiffWithinAt z (hF z hz)
  exact hFinv.congr fun z hz => (hu z hz).choose_spec.2.symm

/-- The velocity gradient evaluated along the actual parent flow is jointly smooth. -/
theorem IsLabelFlowOn.contDiffOn_materialGradient
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (U z.1) (X 0 z.1 z.2))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  have hDU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => fderiv ℝ (U z.1) z.2)
      (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    contDiffOn_spatialDerivative_of_joint_contDiff (uniqueDiffOn_Icc hT) (by simpa using hU)
  exact hDU.comp (contDiffOn_fst.prodMk (hX.contDiffOn_forwardLabelFlow hT hU hper))
    (fun z hz => ⟨hz.1, mem_univ _⟩)

/-- A fixed initial covector produces a jointly smooth transported covector. -/
theorem IsLabelFlowOn.contDiffOn_transportedCovector
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) (k : Vec3) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => labelWaveVector X 0 z.2 k z.1)
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  let A := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  exact (A.toContinuousLinearEquiv.contDiff.comp_contDiffOn
    (hX.contDiffOn_inverseLabelDerivative hT hU hper)).clm_apply contDiffOn_const

end ParentCoframeRegularity

theorem even_fderiv_of_odd {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : Function.Odd f) : Function.Even (fderiv ℝ f) := by
  intro x
  let N : E ≃L[ℝ] E := (LinearIsometryEquiv.neg ℝ : E ≃ₗᵢ[ℝ] E).toContinuousLinearEquiv
  have hfun : f ∘ N = -f := funext hf
  have h := N.comp_right_fderiv (f := f) (x := x)
  rw [hfun, fderiv_neg] at h
  ext v
  have hv := DFunLike.congr_fun h v
  change -(fderiv ℝ f x v) = fderiv ℝ f (-x) (-v) at hv
  rw [map_neg] at hv
  exact (neg_injective hv).symm

/-- The material velocity gradient and transported covector of an odd parent
are even functions of the label at each pair of flow times. -/
theorem IsLabelFlowOn.even_materialGradient_and_labelWaveVector
    {U : Velocity} {X : ℝ → Velocity} {l r s t : ℝ} {K : ℝ≥0}
    (hX : IsLabelFlowOn U X (Icc l r)) (hLip : ∀ u ∈ Icc l r, LipschitzWith K (U u))
    (hodd : ∀ u ∈ Icc l r, Function.Odd (U u))
    (hs : s ∈ Icc l r) (ht : t ∈ Icc l r) (k : Vec3) :
    Function.Even (fun a => fderiv ℝ (U t) (X s t a)) ∧
    Function.Even (fun a => labelWaveVector X s a k t) := by
  have hforward := hX.odd hLip hodd hs ht
  have hback := even_fderiv_of_odd (hX.odd hLip hodd ht hs)
  have hgrad := even_fderiv_of_odd (hodd t ht)
  constructor
  · intro a
    change fderiv ℝ (U t) (X s t (-a)) = fderiv ℝ (U t) (X s t a)
    rw [hforward a, hgrad (X s t a)]
  · intro a
    change (fderiv ℝ (X t s) (X s t (-a))).adjoint k =
      (fderiv ℝ (X t s) (X s t a)).adjoint k
    rw [hforward a, hback (X s t a)]

section PhaseTwistedPeriodization

variable {E : Type*}

/-- Extend a profile by shifting its phase with its lattice translation. -/
noncomputable def phaseTwistedPeriodizeCentered
    (k : Vec3) (f : ℝ → Vec3 → ℝ → E) (t : ℝ) (a : Vec3) (s : ℝ) : E :=
  f t (centeredLabel a) (s - ⟪k, a⟫_ℝ + ⟪k, centeredLabel a⟫_ℝ)

theorem phaseTwistedPeriodizeCentered_translate
    (k : Vec3) (f : ℝ → Vec3 → ℝ → E) (t : ℝ) (a : Vec3) (s : ℝ) (n : Fin 3 → ℤ) :
    phaseTwistedPeriodizeCentered k f t (a + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ) =
      phaseTwistedPeriodizeCentered k f t a s := by
  unfold phaseTwistedPeriodizeCentered
  rw [spatiallyPeriodic_centeredLabel n a, inner_add_right]
  congr 1
  ring

theorem phaseTwistedPeriodizeCentered_phase_periodic
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {t : ℝ} {period : ℝ}
    (hf : ∀ a, Function.Periodic (f t a) period) (a : Vec3) :
    Function.Periodic (phaseTwistedPeriodizeCentered k f t a) period := by
  intro s
  have harg : s + period - ⟪k, a⟫_ℝ + ⟪k, centeredLabel a⟫_ℝ =
      (s - ⟪k, a⟫_ℝ + ⟪k, centeredLabel a⟫_ℝ) + period := by ring
  exact (congrArg _ harg).trans (hf (centeredLabel a) _)

/-- On the phase graph the twisted extension is exactly the usual
periodized graph evaluation composed with the inverse label map. -/
theorem phaseTwistedPeriodizeCentered_on_graph
    (A : Velocity) (k : Vec3) (f : ℝ → Vec3 → ℝ → E) (t : ℝ) (x : Vec3) :
    phaseTwistedPeriodizeCentered k f t (A t x) ⟪k, A t x⟫_ℝ =
      localizedTransportedProfile A k f t x := by
  simp only [phaseTwistedPeriodizeCentered, localizedTransportedProfile, periodizeCentered,
    Function.comp_apply, sub_self, zero_add]

variable [Zero E]

/-- The extension agrees with the profile on the entire closed cell. -/
theorem phaseTwistedPeriodizeCentered_eq_on_centeredCell
    {δ : ℝ} (hδ : 0 < δ) {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {t : ℝ}
    (hf : ∀ a, (∃ i : Fin 3, 1 / 2 - δ < |a i|) → ∀ s, f t a s = 0)
    {a : Vec3} (ha : a ∈ centeredCell) (s : ℝ) :
    phaseTwistedPeriodizeCentered k f t a s = f t a s := by
  let g := fun (b : Vec3) (q : ℝ) => f t b (q + ⟪k, b⟫_ℝ)
  have h := periodizeCentered_eq_on_centeredCell (f := g) hδ
    (fun b hb => funext fun q => hf b hb _) ha
  have hq := congrFun h (s - ⟪k, a⟫_ℝ)
  simpa only [g, phaseTwistedPeriodizeCentered, periodizeCentered, Function.comp_apply,
    sub_add_cancel] using hq

/-- Reflection of the label and phase commutes with the extension when
the profile vanishes at the walls. -/
theorem phaseTwistedPeriodizeCentered_neg_equivariant
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {t : ℝ} {L : E → E}
    (hL : L 0 = 0) (hneg : ∀ a s, f t (-a) (-s) = L (f t a s))
    (hwall : ∀ a, (∃ i : Fin 3, a i = -(1 / 2 : ℝ)) → ∀ s, f t a s = 0)
    (a : Vec3) (s : ℝ) :
    phaseTwistedPeriodizeCentered k f t (-a) (-s) =
      L (phaseTwistedPeriodizeCentered k f t a s) := by
  let g := fun (b : Vec3) (q : ℝ) => f t b (q + ⟪k, b⟫_ℝ)
  let L' := fun (u : ℝ → E) (q : ℝ) => L (u (-q))
  have hL' : L' 0 = 0 := funext fun _ => hL
  have hg (b : Vec3) : g (-b) = L' (g b) := by
    funext q
    change f t (-b) (q + ⟪k,-b⟫_ℝ) = L (f t b (-q + ⟪k,b⟫_ℝ))
    rw [← hneg b (-q + ⟪k,b⟫_ℝ), inner_neg_right, neg_add_rev, neg_neg, add_comm]
  have hgwall (b : Vec3) (hb : ∃ i : Fin 3, b i = -(1 / 2 : ℝ)) : g b = 0 :=
    funext fun q => hwall b hb _
  have h := congrFun (periodizeCentered_neg_equivariant hL' hg hgwall a)
    (-(s - ⟪k, a⟫_ℝ))
  simp only [g, L', periodizeCentered, Function.comp_apply, neg_neg] at h
  simpa [phaseTwistedPeriodizeCentered, inner_neg_right, neg_sub, sub_neg_eq_add,
    sub_eq_add_neg, add_comm] using h

end PhaseTwistedPeriodization

section SmoothExtension

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem exists_smooth_centeredLabel_proxy
    {r : ℝ} (hr : 0 < r) (hcell : 2 * r < 1 / 2) :
    ∃ proxy : Vec3 → Vec3,
      ContDiff ℝ ∞ (periodizeCentered (radialEnvelope r)) ∧
      ContDiff ℝ ∞ proxy ∧
      ∀ a, periodizeCentered (radialEnvelope r) a ≠ 0 → proxy a = centeredLabel a := by
  let R : ℝ := (2 * r + 1 / 2) / 2
  let δ : ℝ := 1 / 2 - R
  have hRin : 2 * r < R := by dsimp only [R]; linarith
  have hRout : R < 1 / 2 := by dsimp only [R]; linarith
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hδ' : δ ≤ 1 / 2 := by dsimp only [δ]; linarith
  let b : ContDiffBump (0 : Vec3) := ⟨2 * r, R, by positivity, hRin⟩
  let proxy := periodizeCentered (fun a => b a • a)
  have hcollar (a : Vec3) (ha : ∃ i : Fin 3, 1 / 2 - δ < |a i|) : R < ‖a‖ := by
    obtain ⟨i, hi⟩ := ha
    have hi' : |a i| ≤ ‖a‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le a i
    dsimp only [δ] at hi
    linarith
  refine ⟨proxy, contDiff_periodizeCentered hδ hδ' (contDiff_radialEnvelope hr) ?_, ?_, ?_⟩
  · intro a ha
    exact radialEnvelope_eq_zero hr (hRin.le.trans (hcollar a ha).le)
  · apply contDiff_periodizeCentered hδ hδ' (b.contDiff.smul contDiff_id)
    intro a ha
    have hb : b a = 0 := b.zero_of_le_dist (by
      simpa only [dist_zero_right, b] using (hcollar a ha).le)
    change b a • a = 0
    rw [hb, zero_smul]
  · intro a ha
    have hinside : ‖centeredLabel a‖ ≤ 2 * r := by
      by_contra! hfar
      exact ha (radialEnvelope_eq_zero hr hfar.le)
    have hb : b (centeredLabel a) = 1 := b.one_of_mem_closedBall (by
      simpa only [Metric.mem_closedBall, dist_zero_right, b] using hinside)
    change b (centeredLabel a) • centeredLabel a = centeredLabel a
    rw [hb, one_smul]

/-- A supported phase profile extends smoothly across all label-cell walls
on the stated time set. -/
theorem contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {ℓ : ℝ} {I : Set ℝ}
    (hℓ : 0 < ℓ) (hcell : 2 * ℓ < 1 / 2)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => f p.1 p.2.1 p.2.2) (I ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ =>
      phaseTwistedPeriodizeCentered k (fun t a s => radialEnvelope ℓ a • f t a s)
        p.1 p.2.1 p.2.2) (I ×ˢ univ) := by
  obtain ⟨proxy, hg, hproxy, hsupport⟩ := exists_smooth_centeredLabel_proxy hℓ hcell
  let label : (ℝ × Vec3 × ℝ) → Vec3 := fun p => proxy p.2.1
  have hlabel : ContDiff ℝ ∞ label := hproxy.comp contDiff_snd.fst
  let phase : (ℝ × Vec3 × ℝ) → ℝ :=
    fun p => p.2.2 - ⟪k, p.2.1⟫_ℝ + ⟪k, label p⟫_ℝ
  have hphase : ContDiff ℝ ∞ phase :=
    (contDiff_snd.snd.sub ((innerSL ℝ k).contDiff.comp contDiff_snd.fst)).add
      ((innerSL ℝ k).contDiff.comp hlabel)
  let args : (ℝ × Vec3 × ℝ) → ℝ × Vec3 × ℝ := fun p => (p.1, label p, phase p)
  have hargs : ContDiff ℝ ∞ args := contDiff_fst.prodMk (hlabel.prodMk hphase)
  have hmaps : MapsTo args (I ×ˢ (univ : Set (Vec3 × ℝ))) (I ×ˢ univ) :=
    fun _ hp => ⟨hp.1, mem_univ _⟩
  have hcomp := hf.comp hargs.contDiffOn hmaps
  have hm := (hg.comp (contDiff_snd.fst : ContDiff ℝ ∞
    (fun p : ℝ × Vec3 × ℝ => p.2.1))).contDiffOn.smul hcomp
  refine hm.congr fun p _ => ?_
  change radialEnvelope ℓ (centeredLabel p.2.1) •
      f p.1 (centeredLabel p.2.1)
        (p.2.2 - ⟪k, p.2.1⟫_ℝ + ⟪k, centeredLabel p.2.1⟫_ℝ) =
    periodizeCentered (radialEnvelope ℓ) p.2.1 • f p.1 (label p) (phase p)
  by_cases h : periodizeCentered (radialEnvelope ℓ) p.2.1 = 0
  · change radialEnvelope ℓ (centeredLabel p.2.1) = 0 at h
    rw [h, zero_smul, show periodizeCentered (radialEnvelope ℓ) p.2.1 = 0 from h, zero_smul]
  · have heq : label p = centeredLabel p.2.1 := hsupport p.2.1 h
    simp only [phase, heq]
    rfl

/-- A switch which vanishes up to launch gives an extension smooth on the
whole preterminal time slab, including the instant of activation. -/
theorem contDiffOn_phaseTwistedPeriodizeCentered_flatActivation
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {χ : ℝ → ℝ} {ℓ a b : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hcell : 2 * ℓ < 1 / 2)
    (hχ : ContDiff ℝ ∞ χ) (hflat : ∀ t ≤ a, χ t = 0)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => f p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ =>
      phaseTwistedPeriodizeCentered k (fun t x s => χ t • (radialEnvelope ℓ x • f t x s))
        p.1 p.2.1 p.2.2) (Iic b ×ˢ univ) :=
  contDiffOn_flatActivation_smul hab hχ hflat
    (contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope hℓ hcell hf)

/-- Evaluate the supported flat profile along any jointly smooth inverse
label map on the closed time slab. -/
theorem contDiffOn_localizedTransportedProfile_flatActivation
    {A : Velocity} {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {χ : ℝ → ℝ} {ℓ a b : ℝ}
    (hab : a < b) (hℓ : 0 < ℓ) (hcell : 2 * ℓ < 1 / 2)
    (hχ : ContDiff ℝ ∞ χ) (hflat : ∀ t ≤ a, χ t = 0)
    (hf : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => f p.1 p.2.1 p.2.2)
      (Icc a b ×ˢ univ))
    (hA : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 => A p.1 p.2) (Icc 0 b ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 =>
      localizedTransportedProfile A k (fun t x s => χ t • (radialEnvelope ℓ x • f t x s))
        p.1 p.2) (Icc 0 b ×ˢ univ) := by
  let graph (p : ℝ × Vec3) : ℝ × Vec3 × ℝ := (p.1, A p.1 p.2, ⟪k, A p.1 p.2⟫_ℝ)
  have hg : ContDiffOn ℝ ∞ graph (Icc 0 b ×ˢ univ) :=
    contDiff_fst.contDiffOn.prodMk (hA.prodMk ((innerSL ℝ k).contDiff.comp_contDiffOn hA))
  have hmaps : MapsTo graph (Icc 0 b ×ˢ univ) (Iic b ×ˢ univ) :=
    fun _ hp => ⟨hp.1.2, mem_univ _⟩
  have hp := (contDiffOn_phaseTwistedPeriodizeCentered_flatActivation (k := k)
    hab hℓ hcell hχ hflat hf).comp hg hmaps
  refine hp.congr fun p _ => ?_
  exact (phaseTwistedPeriodizeCentered_on_graph A k
    (fun t x s => χ t • (radialEnvelope ℓ x • f t x s)) p.1 p.2).symm

end SmoothExtension

section RadialSymmetry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- For a supported radial envelope, the twisted extension preserves any
linear reflection parity of the profile. -/
theorem phaseTwistedPeriodizeCentered_radialEnvelope_neg_equivariant
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {t ℓ : ℝ} {L : E →L[ℝ] E}
    (hℓ : 0 < ℓ) (hcell : 2 * ℓ ≤ 1 / 2)
    (hneg : ∀ a s, f t (-a) (-s) = L (f t a s)) (a : Vec3) (s : ℝ) :
    phaseTwistedPeriodizeCentered k (fun u x q => radialEnvelope ℓ x • f u x q) t (-a) (-s) =
      L (phaseTwistedPeriodizeCentered k (fun u x q => radialEnvelope ℓ x • f u x q) t a s) := by
  refine phaseTwistedPeriodizeCentered_neg_equivariant (map_zero L) ?_ ?_ a s
  · intro x q
    simp only [radialEnvelope_neg, hneg, map_smul]
  · rintro x ⟨i, hi⟩ q
    have hnorm : (1 / 2 : ℝ) ≤ ‖x‖ := by
      have hn := PiLp.norm_apply_le x i
      rw [hi, Real.norm_eq_abs, abs_neg, abs_of_nonneg (by norm_num)] at hn
      exact hn
    rw [radialEnvelope_eq_zero hℓ (hcell.trans hnorm), zero_smul]

/-- The supported extension agrees on the entire closed label cell. -/
theorem phaseTwistedPeriodizeCentered_radialEnvelope_eq_on_centeredCell
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {t ℓ : ℝ}
    (hℓ : 0 < ℓ) (hcell : 2 * ℓ < 1 / 2) {a : Vec3}
    (ha : a ∈ centeredCell) (s : ℝ) :
    phaseTwistedPeriodizeCentered k (fun u x q => radialEnvelope ℓ x • f u x q) t a s =
      radialEnvelope ℓ a • f t a s := by
  have hδ : 0 < 1 / 2 - 2 * ℓ := sub_pos.mpr hcell
  refine phaseTwistedPeriodizeCentered_eq_on_centeredCell hδ ?_ ha s
  rintro x ⟨i, hi⟩ q
  have hn : |x i| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le x i
  have hr : 2 * ℓ ≤ ‖x‖ := by linarith
  rw [radialEnvelope_eq_zero hℓ hr, zero_smul]

/-- The envelope confines the extension to the translates of its original
support ball. -/
theorem phaseTwistedPeriodizeCentered_radialEnvelope_eq_zero_of_separation
    {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {a : Vec3} (hsep : ∀ n : Fin 3 → ℤ, 2 * ℓ ≤ ‖a - latticeVector n‖)
    (t s : ℝ) :
    phaseTwistedPeriodizeCentered k (fun u x q => radialEnvelope ℓ x • f u x q) t a s = 0 := by
  let n : Fin 3 → ℤ := fun i => ⌊a i + 1 / 2⌋
  have hc : centeredLabel a = a - latticeVector n := by
    apply PiLp.ext
    intro i
    change Int.fract (a i + 1 / 2) - 1 / 2 = a i - (⌊a i + 1 / 2⌋ : ℤ)
    rw [Int.fract]
    ring
  have hz : radialEnvelope ℓ (centeredLabel a) = 0 := radialEnvelope_eq_zero hℓ
    (show 2 * ℓ ≤ ‖centeredLabel a‖ from hc.symm ▸ hsep n)
  simp only [phaseTwistedPeriodizeCentered, hz, zero_smul]

/-- The Eulerian phase graph preserves the simultaneous reflection of the
label and phase when the inverse parent flow is odd. -/
theorem localizedTransportedProfile_radialEnvelope_neg_equivariant
    {A : Velocity} {k : Vec3} {f : ℝ → Vec3 → ℝ → E} {t ℓ : ℝ} {L : E →L[ℝ] E}
    (hℓ : 0 < ℓ) (hcell : 2 * ℓ ≤ 1 / 2) (hA : Function.Odd (A t))
    (hneg : ∀ a s, f t (-a) (-s) = L (f t a s)) (x : Vec3) :
    localizedTransportedProfile A k (fun u a s => radialEnvelope ℓ a • f u a s) t (-x) =
      L (localizedTransportedProfile A k (fun u a s => radialEnvelope ℓ a • f u a s) t x) := by
  rw [← phaseTwistedPeriodizeCentered_on_graph, ← phaseTwistedPeriodizeCentered_on_graph]
  rw [hA x, inner_neg_right]
  exact phaseTwistedPeriodizeCentered_radialEnvelope_neg_equivariant hℓ hcell hneg
    (A t x) ⟪k, A t x⟫_ℝ

end RadialSymmetry

section InverseLabelRegularity

private theorem contDiffOn_localInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {F G : E → E} {s : Set E} (hs : UniqueDiffOn ℝ s)
    (hF : ContDiffOn ℝ ∞ F s) (hG : ContinuousOn G s)
    (hmap : MapsTo G s s) (hInv : EqOn (F ∘ G) id s)
    (hUnit : ∀ x ∈ s, IsUnit (fderivWithin ℝ F s x)) :
    ContDiffOn ℝ ∞ G s := by
  let DG (x : E) := Ring.inverse (fderivWithin ℝ F s x)
  have hDG : ContDiffOn ℝ ∞ DG s := by
    have hDF := hF.fderivWithin (m := ∞) hs (by simp)
    intro x hx
    obtain ⟨u, hu⟩ := hUnit x hx
    have hi : ContDiffAt ℝ ∞ Ring.inverse (fderivWithin ℝ F s x) :=
      hu ▸ contDiffAt_ringInverse ℝ u
    exact hi.comp_contDiffWithinAt x (hDF x hx)
  have hD (x : E) (hx : x ∈ s) : HasFDerivWithinAt G (DG (G x)) s x := by
    have hF' := (hF.differentiableOn (by simp) _ (hmap hx)).hasFDerivWithinAt
    have hg := (hG x hx).tendsto_nhdsWithin hmap
    have hInv' : F ∘ G =ᶠ[𝓝[s] x] id := by
      filter_upwards [self_mem_nhdsWithin (s := s)] with y hy using hInv hy
    have hlin : Function.LeftInverse (DG (G x)) (fderivWithin ℝ F s (G x)) := by
      obtain ⟨u, hu⟩ := hUnit (G x) (hmap hx)
      dsimp only [DG]
      rw [← hu, Ring.inverse_unit]
      intro d
      exact DFunLike.congr_fun u.inv_val d
    simpa only [ContinuousLinearMap.comp_id] using
      HasFDerivWithinAt.of_comp_of_leftInverse hg hF' (hasFDerivWithinAt_id x s) hInv' hlin hx
  apply contDiffOn_infty.2
  intro n
  induction n with
  | zero =>
      simpa only [Nat.cast_zero, contDiffOn_zero] using hG
  | succ n ih =>
      rw [Nat.cast_succ, contDiffOn_succ_iff_fderivWithin hs]
      refine ⟨fun x hx => (hD x hx).differentiableWithinAt, ?_, ?_⟩
      · intro h
        simp at h
      · exact ((hDG.of_le (by simp)).comp ih hmap).congr
          (fun x hx => (hD x hx).fderivWithin (hs x hx))

/-- The actual inverse label map is jointly smooth on the closed parent slab.
The time-preserving inverse acts on the same slab as the forward map. -/
theorem IsLabelFlowOn.contDiffOn_inverseLabelFlow
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ}
    (hX : IsLabelFlowOn U X (Icc 0 T)) (hT : 0 < T)
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec3 => X z.1 0 z.2) (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  let S := Icc (0 : ℝ) T ×ˢ (univ : Set Vec3)
  let F (z : ℝ × Vec3) := (z.1, X 0 z.1 z.2)
  let G (z : ℝ × Vec3) := (z.1, X z.1 0 z.2)
  have hS : UniqueDiffOn ℝ S := (uniqueDiffOn_Icc hT).prod uniqueDiffOn_univ
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) S := hU.of_le (by simp)
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU₂.of_le (by norm_num)) hper
  have hinit : X 0 0 = id := funext fun a => hX.initial 0 h₀ a
  have hForward : ContDiffOn ℝ ∞ (Function.uncurry (X 0)) S :=
    trajectoryFamily_joint_contDiff hT hU (hX.continuousOn_time_label hK h₀)
      (fun a => hX.trajectory 0 h₀ a) (hinit.symm ▸ contDiff_id)
  have hF : ContDiffOn ℝ ∞ F S := contDiffOn_fst.prodMk hForward
  have hGc : ContinuousOn (fun z : ℝ × Vec3 => X z.1 0 z.2) S :=
    continuousOn_prod_of_continuousOn_lipschitzOnWith'
      _ (Real.toNNReal (Real.exp (K * (T - 0))))
      (fun t ht => (hX.lipschitzWith_labels hK ht h₀).lipschitzOnWith)
      (fun x _ => HasDerivWithinAt.continuousOn fun t ht =>
        hX.hasDerivWithinAt_inverseLabel hT hU₂ hper h₀ ht x)
  have hG : ContinuousOn G S := continuous_fst.continuousOn.prodMk hGc
  have hMaps : MapsTo G S S := fun z hz => ⟨hz.1, mem_univ _⟩
  have hInv : EqOn (F ∘ G) id S := by
    intro z hz
    exact Prod.ext rfl ((hX.inverse hK h₀ hz.1).2 z.2)
  have hUnit (z : ℝ × Vec3) (hz : z ∈ S) : IsUnit (fderivWithin ℝ F S z) := by
    let H := fderiv ℝ (X 0 z.1) z.2
    let R := fderiv ℝ (X z.1 0) (X 0 z.1 z.2)
    let v := U z.1 (X 0 z.1 z.2)
    let fst := ContinuousLinearMap.fst ℝ ℝ Vec3
    let snd := ContinuousLinearMap.snd ℝ ℝ Vec3
    let D := fst.prod ((toSpanSingleton ℝ v).coprod H)
    let E := fst.prod (R.comp (snd - fst.smulRight v))
    obtain ⟨hRH, hHR⟩ := hX.labelDerivative_inverse hT hU₂ hper h₀ hz.1 z.2
    have hrh (x : Vec3) : R (H x) = x := DFunLike.congr_fun hRH x
    have hhr (x : Vec3) : H (R x) = x := DFunLike.congr_fun hHR x
    have hD : HasFDerivWithinAt F D S z :=
      hasFDerivWithinAt_fst.prodMk
        (hX.hasFDerivWithinAt_time_label_of_contDiffOn_periodic hT hU₂ hper h₀ hz.1)
    have hDE : D * E = 1 := by
      apply ContinuousLinearMap.ext
      rintro ⟨r, x⟩
      refine Prod.ext rfl ?_
      change r • v + H (R (x - r • v)) = x
      rw [hhr, add_comm, sub_add_cancel]
    have hED : E * D = 1 := by
      apply ContinuousLinearMap.ext
      rintro ⟨r, x⟩
      refine Prod.ext rfl ?_
      change R (r • v + H x - r • v) = x
      rw [add_comm, add_sub_cancel_right, hrh]
    rw [hD.fderivWithin (hS z hz)]
    exact ⟨⟨D, E, hDE, hED⟩, rfl⟩
  exact (contDiffOn_localInverse hS hF hG hMaps hInv hUnit).snd

end InverseLabelRegularity

end TorusEuler

namespace TorusEuler.LocalizedAmplitude

private theorem contDiffOn_seed_coefficients
    {M : ℝ × Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ × Vec3 → Vec3} {S : Set (ℝ × Vec3)}
    (hM : ContDiffOn ℝ ∞ M S) (hκ : ContDiffOn ℝ ∞ κ S) (hκ₀ : ∀ p ∈ S, κ p ≠ 0) :
    ContDiffOn ℝ ∞ (fun p => affineWaveAmplitudeOperator (M p) (κ p)) S ∧
      ContDiffOn ℝ ∞ (fun p => oscillatoryTransverseProjection (κ p)) S := by
  let L : Vec3 →L[ℝ] Vec3 →L[ℝ] ℝ := innerSL ℝ
  have hInner := L.contDiff.comp_contDiffOn hκ
  have hRank : ContDiffOn ℝ ∞ (fun p => InnerProductSpace.rankOne ℝ (κ p) (κ p)) S :=
    (isBoundedBilinearMap_smulRight (𝕜 := ℝ) (E := Vec3) (F := Vec3)).contDiff.comp_contDiffOn
      (hInner.prodMk hκ)
  have hn : ContDiffOn ℝ ∞ (fun p => ‖κ p‖ ^ 2) S := hκ.norm_sq ℝ
  have hn₀ (p : ℝ × Vec3) (hp : p ∈ S) : ‖κ p‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ p hp))
  have ht := (contDiffOn_const (c := (2 : ℝ))).div hn hn₀
  have hp := hn.inv hn₀
  exact ⟨hM.neg.add (ht.smul (hRank.clm_comp hM)), contDiffOn_const.sub (hp.smul hRank)⟩

/-- The selected projected seed is jointly smooth whenever its actual
coefficient fields are jointly smooth on the closed activation slab. -/
theorem SeedOn.contDiffOn_amplitude
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3} {center : ℝ → Vec3}
    {t₀ T ell D C : ℝ} (w : SeedOn M κ center t₀ T ell D C) (ht₀T : t₀ < T)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ₀ : ∀ t ∈ Icc t₀ T, ∀ a, κ t a ≠ 0) :
    ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3)) := by
  obtain ⟨hA, hP⟩ := contDiffOn_seed_coefficients hM hκ (fun p hp => hκ₀ p.1 hp.1 p.2)
  let J : Set (ℝ × Vec3) := Icc t₀ T ×ˢ univ
  let g : ℝ × Vec3 → Vec3 →L[ℝ] Vec3 :=
    fun p => oscillatoryTransverseProjection (κ p.1 p.2)
  let s : Vec3 → ℝ × Vec3 := fun a => (t₀, a)
  have hp : ContDiffOn ℝ ∞ g J := hP
  have hs : ContDiff ℝ ∞ s := contDiff_const.prodMk contDiff_id
  have hm (a : Vec3) : s a ∈ J := ⟨left_mem_Icc.mpr ht₀T.le, mem_univ a⟩
  have hP₀' : ContDiff ℝ ∞ (g ∘ s) :=
    ContDiffOn.comp_contDiff (s := J) (g := g) (f := s) hp hs hm
  have hP₀ : ContDiff ℝ ∞ (fun a => oscillatoryTransverseProjection (κ t₀ a)) := hP₀'
  have hInit : ContDiff ℝ ∞ (w.amplitude t₀) := by
    rw [show w.amplitude t₀ = fun a => oscillatoryTransverseProjection (κ t₀ a) (center t₀) from
      funext w.activation]
    exact hP₀.clm_apply contDiff_const
  exact contDiffOn_selected_linearTrajectory
    (A := fun t a => affineWaveAmplitudeOperator (M t a) (κ t a))
    ht₀T hA hInit w.equation

/-- The projected initial seed and the coefficient have the same label parity.
Uniqueness preserves it throughout the closed active slab. -/
theorem SeedOn.even_amplitude
    {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3} {center : ℝ → Vec3}
    {t₀ T ell D C : ℝ} (seed : SeedOn M κ center t₀ T ell D C) (hT : t₀ ≤ T)
    (hM : ∀ a, ContinuousOn (fun t => M t a) (Icc t₀ T))
    (hκ : ∀ a, ContinuousOn (fun t => κ t a) (Icc t₀ T))
    (hκne : ∀ a t, t ∈ Icc t₀ T → κ t a ≠ 0)
    (hMeven : ∀ t ∈ Icc t₀ T, Function.Even (M t))
    (hκeven : ∀ t ∈ Icc t₀ T, Function.Even (κ t)) :
    ∀ t ∈ Icc t₀ T, Function.Even (seed.amplitude t) := by
  intro t ht a
  have h₀ : t₀ ∈ Icc t₀ T := ⟨le_rfl, hT⟩
  let A (u : ℝ) := affineWaveAmplitudeOperator (M u a) (κ u a)
  have hA : ContinuousOn A (Icc t₀ T) :=
    continuousOn_affineWaveAmplitudeOperator (hM a) (hκ a) (hκne a)
  refine linearODE_unique_of_mem ordConnected_Icc h₀ hA
    (x := fun u => seed.amplitude u (-a)) (y := fun u => seed.amplitude u a)
    (fun u hu => ?_) (seed.equation a) ?_ ht
  · simpa only [A, hMeven u hu a, hκeven u hu a] using seed.equation (-a) u hu
  · simp only [seed.activation, hκeven t₀ h₀ a]

/-- The actual coframe has no zero transported covector for a nonzero
launch. -/
theorem transportedCovector_ne_zero_of_parent
    {U : Velocity} {X : ℝ → Velocity} {T : ℝ} {k : Vec3}
    (hT : 0 < T) (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) (hk : k ≠ 0)
    (t : ℝ) (ht : t ∈ Icc 0 T) (a : Vec3) :
    labelWaveVector X 0 a k t ≠ 0 := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hGF := (hX.labelDerivative_inverse hT (hU.of_le (by simp)) hper h₀ ht a).1
  exact (coframe_covector_nonzero_and_norm_le k hk hGF le_rfl).1

private theorem continuousOn_apply_label
    {F : Type*} [TopologicalSpace F] {f : ℝ → Vec3 → F} {J : Set ℝ}
    (hf : ContinuousOn (Function.uncurry f) (J ×ˢ (univ : Set Vec3))) (a : Vec3) :
    ContinuousOn (fun t => f t a) J := by
  let e : ℝ → ℝ × Vec3 := fun t => (t, a)
  have hce : Continuous e := continuous_id.prodMk continuous_const
  have he : MapsTo e J (J ×ˢ (univ : Set Vec3)) := fun t ht =>
    mem_prod.mpr ⟨ht, mem_univ a⟩
  exact hf.comp hce.continuousOn he

set_option maxHeartbeats 450000 in
/-- The actual odd parent supplies joint smoothness and even label parity of
the same selected seed on the whole closed activation slab. -/
theorem SeedOn.regularity_of_parent
    {U : Velocity} {X : ℝ → Velocity} {center : ℝ → Vec3} {k : Vec3}
    {t₀ T ell D C : ℝ} (ht₀ : 0 ≤ t₀) (ht₀T : t₀ < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) (hk : k ≠ 0)
    (w : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C) :
    ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t) := by
  let M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 := fun t a => fderiv ℝ (U t) (X 0 t a)
  let κ : ℝ → Vec3 → Vec3 := fun t a => labelWaveVector X 0 a k t
  let J : Set ℝ := Icc t₀ T
  let S : Set (ℝ × Vec3) := J ×ˢ univ
  let seed : SeedOn M κ center t₀ T ell D C := w
  have hT : 0 < T := ht₀.trans_lt ht₀T
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hsub : J ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hsubS : S ⊆ Icc 0 T ×ˢ (univ : Set Vec3) := fun _ hp =>
    mem_prod.mpr ⟨hsub hp.1, hp.2⟩
  have hMwhole : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hX.contDiffOn_materialGradient hT hU hper
  have hκwhole : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hX.contDiffOn_transportedCovector hT hU hper k
  have hM : ContDiffOn ℝ ∞ (Function.uncurry M) S := hMwhole.mono hsubS
  have hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) S := hκwhole.mono hsubS
  have hκ₀ (t : ℝ) (ht : t ∈ J) (a : Vec3) : κ t a ≠ 0 :=
    transportedCovector_ne_zero_of_parent hT hX hU hper hk t (hsub ht) a
  have hSmooth : ContDiffOn ℝ ∞ (Function.uncurry seed.amplitude) S :=
    SeedOn.contDiffOn_amplitude seed ht₀T hM hκ hκ₀
  have hU₁ : ContDiffOn ℝ 1 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  obtain ⟨L, hL⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT hU₁ hper
  have hEven (t : ℝ) (ht : t ∈ J) : Function.Even (M t) ∧ Function.Even (κ t) :=
    hX.even_materialGradient_and_labelWaveVector hL hodd h₀ (hsub ht) k
  have hMc (a : Vec3) : ContinuousOn (fun t => M t a) J :=
    continuousOn_apply_label (f := M) (J := J) hM.continuousOn a
  have hκc (a : Vec3) : ContinuousOn (fun t => κ t a) J :=
    continuousOn_apply_label (f := κ) (J := J) hκ.continuousOn a
  have hParity : ∀ t ∈ J, Function.Even (seed.amplitude t) :=
    SeedOn.even_amplitude seed ht₀T.le hMc hκc (fun a t ht => hκ₀ t ht a)
      (fun t ht => (hEven t ht).1) (fun t ht => (hEven t ht).2)
  exact ⟨hSmooth, hParity⟩

section LeadingProfiles

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C : ℝ}

/-- The leading oscillation before switching on the wave. -/
noncomputable def SeedOn.leading (w : SeedOn M κ center t₀ T ell D C) (h : ℝ)
    (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  (radialEnvelope ell a * waveProfile h s) • w.amplitude t a

/-- The leading oscillation with the actual flat switch. -/
noncomputable def SeedOn.switchedLeading (w : SeedOn M κ center t₀ T ell D C) (r h : ℝ)
    (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  waveSwitch t₀ r t • w.leading h t a s

/-- The smooth leading pressure before application of the flat switch. -/
noncomputable def SeedOn.leadingPressure (w : SeedOn M κ center t₀ T ell D C) (h : ℝ)
    (t : ℝ) (a : Vec3) (s : ℝ) : ℝ :=
  -wavePressureCoefficient (radialEnvelope ell a) (κ t a) (w.amplitude t a) (M t a) *
    wavePressurePrimitive h s

theorem SeedOn.leadingPressure_eq_phasePressure (w : SeedOn M κ center t₀ T ell D C)
    (h t : ℝ) (a : Vec3) :
    w.leadingPressure h t a =
      oscillatoryPhasePressure (M t a) (κ t a) (fun _ => 0) (w.leading h t a) :=
  (oscillatoryPhasePressure_primary_eq h (radialEnvelope ell a) (κ t a)
    (w.amplitude t a) (M t a)).symm

/-- The pressure profile with the actual flat switch. -/
noncomputable def SeedOn.switchedPressure (w : SeedOn M κ center t₀ T ell D C) (r h : ℝ)
    (t : ℝ) (a : Vec3) (s : ℝ) : ℝ :=
  waveSwitch t₀ r t * w.leadingPressure h t a s

/-- The envelope and the phase profile preserve joint smoothness on the
activation slab. -/
theorem SeedOn.contDiffOn_leading (w : SeedOn M κ center t₀ T ell D C)
    {h : ℝ} (hEll : 0 < ell) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude)
      (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.leading h p.1 p.2.1 p.2.2)
      (Icc t₀ T ×ˢ univ) := by
  have hproj : ContDiff ℝ ∞ (fun p : ℝ × Vec3 × ℝ => (p.1, p.2.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst
  have hAmp : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.amplitude p.1 p.2.1)
      (Icc t₀ T ×ˢ univ) :=
    hw.comp hproj.contDiffOn (fun _ hp => mem_prod.mpr ⟨hp.1, mem_univ _⟩)
  exact (((contDiff_radialEnvelope hEll).comp contDiff_snd.fst).mul
    ((contDiff_waveProfile hh hh₁).comp contDiff_snd.snd)).contDiffOn.smul hAmp

/-- The flat switch extends the actual leading profile smoothly, including
the seam at activation. -/
theorem SeedOn.contDiffOn_switchedLeading (w : SeedOn M κ center t₀ T ell D C)
    {r h : ℝ} (hT : t₀ < T) (hr : 0 ≤ r) (hEll : 0 < ell) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude)
      (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.switchedLeading r h p.1 p.2.1 p.2.2)
      (Iic T ×ˢ univ) :=
  contDiffOn_flatActivation_smul hT (contDiff_waveSwitch t₀ r)
    (fun _ ht => waveSwitch_eq_zero_of_le hr ht) (w.contDiffOn_leading hEll hh hh₁ hw)

/-- The normalized pressure coefficient and its phase primitive are smooth on
the active slab for the same selected seed. -/
theorem SeedOn.contDiffOn_leadingPressure (w : SeedOn M κ center t₀ T ell D C)
    {h : ℝ} (hEll : 0 < ell) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ₀ : ∀ t ∈ Icc t₀ T, ∀ a, κ t a ≠ 0)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude)
      (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.leadingPressure h p.1 p.2.1 p.2.2)
      (Icc t₀ T ×ˢ univ) := by
  let S := Icc t₀ T ×ˢ (univ : Set (Vec3 × ℝ))
  have hproj : ContDiff ℝ ∞ (fun p : ℝ × Vec3 × ℝ => (p.1, p.2.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst
  have hmap : MapsTo (fun p : ℝ × Vec3 × ℝ => (p.1, p.2.1)) S
      (Icc t₀ T ×ˢ (univ : Set Vec3)) := fun p hp => mem_prod.mpr ⟨hp.1, mem_univ _⟩
  have hK : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => κ p.1 p.2.1) S :=
    hκ.comp hproj.contDiffOn hmap
  have hV : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => M p.1 p.2.1 (w.amplitude p.1 p.2.1)) S :=
    (hM.comp hproj.contDiffOn hmap).clm_apply (hw.comp hproj.contDiffOn hmap)
  have hE : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => radialEnvelope ell p.2.1) S :=
    ((contDiff_radialEnvelope hEll).comp contDiff_snd.fst).contDiffOn
  have hn (p : ℝ × Vec3 × ℝ) (hp : p ∈ S) : ‖κ p.1 p.2.1‖ ^ 2 ≠ 0 :=
    pow_ne_zero _ (norm_ne_zero_iff.mpr (hκ₀ p.1 hp.1 p.2.1))
  have hDot := hK.inner ℝ hV
  have hCoef := (((contDiffOn_const (c := (2 : ℝ))).mul hE).mul hDot).div (hK.norm_sq ℝ) hn
  exact hCoef.neg.mul (((contDiff_wavePressurePrimitive hh hh₁).comp contDiff_snd.snd).contDiffOn)

theorem SeedOn.contDiffOn_switchedPressure (w : SeedOn M κ center t₀ T ell D C)
    {r h : ℝ} (hT : t₀ < T) (hr : 0 ≤ r) (hEll : 0 < ell) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hM : ContDiffOn ℝ ∞ (Function.uncurry M) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ : ContDiffOn ℝ ∞ (Function.uncurry κ) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hκ₀ : ∀ t ∈ Icc t₀ T, ∀ a, κ t a ≠ 0)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude)
      (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.switchedPressure r h p.1 p.2.1 p.2.2)
      (Iic T ×ˢ univ) :=
  contDiffOn_flatActivation_smul hT (contDiff_waveSwitch t₀ r)
    (fun _ ht => waveSwitch_eq_zero_of_le hr ht)
    (w.contDiffOn_leadingPressure hEll hh hh₁ hM hκ hκ₀ hw)

theorem SeedOn.switchedLeading_eq_zero_before_activation
    (w : SeedOn M κ center t₀ T ell D C) {r h t : ℝ} (hr : 0 ≤ r)
    (ht : t ≤ t₀) (a : Vec3) (s : ℝ) : w.switchedLeading r h t a s = 0 := by
  simp only [SeedOn.switchedLeading, waveSwitch_eq_zero_of_le hr ht, zero_smul]

theorem SeedOn.switchedLeading_eq_zero_outside_envelope
    (w : SeedOn M κ center t₀ T ell D C) {r h t : ℝ} (hEll : 0 < ell)
    {a : Vec3} (ha : 2 * ell ≤ ‖a‖) (s : ℝ) : w.switchedLeading r h t a s = 0 := by
  simp only [SeedOn.switchedLeading, SeedOn.leading, radialEnvelope_eq_zero hEll ha,
    zero_mul, zero_smul, smul_zero]

theorem SeedOn.switchedLeading_periodic_phase
    (w : SeedOn M κ center t₀ T ell D C) {r h t : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (a : Vec3) : Function.Periodic (w.switchedLeading r h t a) 1 := by
  intro s
  simp only [SeedOn.switchedLeading, SeedOn.leading, periodic_waveProfile hh hh₁ s]

/-- The leading oscillation is odd under simultaneous label and phase
reflection. The inactive part is identically zero. -/
theorem SeedOn.switchedLeading_neg_label_phase
    (w : SeedOn M κ center t₀ T ell D C) {r h t : ℝ}
    (ht : t ≤ T) (hr : 0 ≤ r) (hh : 0 < h) (hh₁ : h ≤ 1)
    (hwEven : ∀ u ∈ Icc t₀ T, Function.Even (w.amplitude u)) (a : Vec3) (s : ℝ) :
    w.switchedLeading r h t (-a) (-s) = -w.switchedLeading r h t a s := by
  rcases le_total t t₀ with ht₀ | h₀t
  · rw [w.switchedLeading_eq_zero_before_activation hr ht₀,
      w.switchedLeading_eq_zero_before_activation hr ht₀, neg_zero]
  · simp only [SeedOn.switchedLeading, SeedOn.leading, radialEnvelope_neg,
      odd_waveProfile hh hh₁ s, mul_neg, neg_smul, smul_neg, hwEven t ⟨h₀t, ht⟩ a]

end LeadingProfiles


/-- The later-wave leading velocity and pressure both extend smoothly across
activation, and the leading velocity has the required reflection symmetry. -/
theorem SeedOn.switched_profiles_of_parent
    {U : Velocity} {X : ℝ → Velocity} {center : ℝ → Vec3} {k : Vec3}
    {t₀ T ell D C r h : ℝ} (ht₀ : 0 ≤ t₀) (ht₀T : t₀ < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) (hk : k ≠ 0)
    (w : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C)
    (hr : 0 ≤ r) (hEll : 0 < ell) (hh : 0 < h) (hh₁ : h ≤ 1) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.switchedLeading r h p.1 p.2.1 p.2.2) (Iic T ×ˢ univ) ∧
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.switchedPressure r h p.1 p.2.1 p.2.2) (Iic T ×ˢ univ) ∧
    ∀ t ≤ T, ∀ a s, w.switchedLeading r h t (-a) (-s) = -w.switchedLeading r h t a s := by
  obtain ⟨hSmooth, hEven⟩ := SeedOn.regularity_of_parent ht₀ ht₀T hX hU hper hodd hk w
  have hT : 0 < T := ht₀.trans_lt ht₀T
  have hsub : Icc t₀ T ⊆ Icc 0 T := Icc_subset_Icc_left ht₀
  have hsub' : (Icc t₀ T ×ˢ (univ : Set Vec3)) ⊆ Icc 0 T ×ˢ univ :=
    fun _ hp => mem_prod.mpr ⟨hsub hp.1, hp.2⟩
  have hM := (hX.contDiffOn_materialGradient hT hU hper).mono hsub'
  have hK := (hX.contDiffOn_transportedCovector hT hU hper k).mono hsub'
  exact ⟨w.contDiffOn_switchedLeading ht₀T hr hEll hh hh₁ hSmooth,
    w.contDiffOn_switchedPressure ht₀T hr hEll hh hh₁ hM hK
      (fun t ht a => transportedCovector_ne_zero_of_parent hT hX hU hper hk t (hsub ht) a) hSmooth,
    fun _ ht a s => w.switchedLeading_neg_label_phase ht hr hh hh₁ hEven a s⟩


section SpatialGluing

variable {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
  {center : ℝ → Vec3} {t₀ T ell D C : ℝ}

private theorem SeedOn.contDiffOn_unenvelopedLeading (w : SeedOn M κ center t₀ T ell D C)
    {h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => waveProfile h p.2.2 • w.amplitude p.1 p.2.1)
      (Icc t₀ T ×ˢ univ) := by
  have hproj : ContDiff ℝ ∞ (fun p : ℝ × Vec3 × ℝ => (p.1, p.2.1)) :=
    contDiff_fst.prodMk contDiff_snd.fst
  have hAmp : ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ => w.amplitude p.1 p.2.1)
      (Icc t₀ T ×ˢ univ) :=
    hw.comp hproj.contDiffOn (fun _ hp => mem_prod.mpr ⟨hp.1, mem_univ _⟩)
  exact ((contDiff_waveProfile hh hh₁).comp contDiff_snd.snd).contDiffOn.smul hAmp

private theorem SeedOn.switchedLeading_eq_profile_product (w : SeedOn M κ center t₀ T ell D C)
    (r h : ℝ) :
    w.switchedLeading r h =
      fun t a s => waveSwitch t₀ r t • (radialEnvelope ell a • (waveProfile h s • w.amplitude t a)) := by
  funext t a s
  simp only [SeedOn.switchedLeading, SeedOn.leading, smul_smul]

/-- The actual switched leading wave extends through the label cell by the
phase shift dictated by the launch covector. -/
theorem SeedOn.contDiffOn_twistedSwitchedLeading
    (w : SeedOn M κ center t₀ T ell D C) {r h : ℝ} (k : Vec3)
    (ht₀T : t₀ < T) (hr : 0 ≤ r) (hEll : 0 < ell) (hcell : 2 * ell < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (fun p : ℝ × Vec3 × ℝ =>
      phaseTwistedPeriodizeCentered k (w.switchedLeading r h) p.1 p.2.1 p.2.2) (Iic T ×ˢ univ) := by
  rw [w.switchedLeading_eq_profile_product]
  exact contDiffOn_phaseTwistedPeriodizeCentered_flatActivation ht₀T hEll hcell
    (contDiff_waveSwitch t₀ r) (fun _ ht => waveSwitch_eq_zero_of_le hr ht)
    (w.contDiffOn_unenvelopedLeading hh hh₁ hw)

/-- On the closed label cell, the twisted extension agrees with the actual
switched seed profile. It has the same reflection symmetry everywhere. -/
theorem SeedOn.twistedSwitchedLeading_agreement_and_reflection
    (w : SeedOn M κ center t₀ T ell D C) {r h : ℝ} (k : Vec3)
    (hr : 0 ≤ r) (hEll : 0 < ell) (hcell : 2 * ell < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (hwEven : ∀ t ∈ Icc t₀ T, Function.Even (w.amplitude t)) :
    (∀ t, ∀ a ∈ centeredCell, ∀ s,
      phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t a s = w.switchedLeading r h t a s) ∧
    ∀ t ≤ T, ∀ a s,
      phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t (-a) (-s) =
        -phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t a s := by
  constructor
  · intro t a ha s
    let δ : ℝ := 1 / 2 - 2 * ell
    have hδ : 0 < δ := sub_pos.mpr hcell
    refine phaseTwistedPeriodizeCentered_eq_on_centeredCell hδ ?_ ha s
    intro b hb q
    obtain ⟨i, hi⟩ := hb
    have hnorm : |b i| ≤ ‖b‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
    have hsize : 2 * ell ≤ ‖b‖ := by
      dsimp only [δ] at hi
      linarith
    exact w.switchedLeading_eq_zero_outside_envelope hEll hsize q
  · intro t ht a s
    refine phaseTwistedPeriodizeCentered_neg_equivariant (L := fun x : Vec3 => -x) (neg_zero)
      (w.switchedLeading_neg_label_phase ht hr hh hh₁ hwEven) ?_ a s
    intro b hb q
    obtain ⟨i, hi⟩ := hb
    have hnorm : |b i| ≤ ‖b‖ := by
      simpa only [Real.norm_eq_abs] using PiLp.norm_apply_le b i
    have hsize : 2 * ell ≤ ‖b‖ := by
      rw [hi, abs_neg, abs_of_nonneg (by norm_num)] at hnorm
      exact hcell.le.trans hnorm
    exact w.switchedLeading_eq_zero_outside_envelope hEll hsize q

/-- Evaluating the actual switched and supported wave on the Eulerian phase
graph preserves joint smoothness for a smooth inverse label map. -/
theorem SeedOn.contDiffOn_transportedSwitchedLeading
    (w : SeedOn M κ center t₀ T ell D C) {r h : ℝ} (k : Vec3) {A : Velocity}
    (ht₀T : t₀ < T) (hr : 0 ≤ r) (hEll : 0 < ell) (hcell : 2 * ell < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3)))
    (hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set Vec3))) :
    ContDiffOn ℝ ∞ (Function.uncurry (localizedTransportedProfile A k (w.switchedLeading r h)))
      (Icc 0 T ×ˢ (univ : Set Vec3)) := by
  rw [w.switchedLeading_eq_profile_product]
  exact contDiffOn_localizedTransportedProfile_flatActivation ht₀T hEll hcell
    (contDiff_waveSwitch t₀ r) (fun _ ht => waveSwitch_eq_zero_of_le hr ht)
    (w.contDiffOn_unenvelopedLeading hh hh₁ hw) hA

end SpatialGluing


set_option maxHeartbeats 500000 in
/-- The Eulerian leading wave built from the selected seed is jointly smooth
through activation, periodic and odd on the actual parent slab. -/
theorem SeedOn.transportedSwitchedLeading_of_parent
    {U : Velocity} {X : ℝ → Velocity} {center : ℝ → Vec3} {k : Vec3}
    {t₀ T ell D C r h : ℝ} (ht₀ : 0 ≤ t₀) (ht₀T : t₀ < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t))
    (hodd : ∀ t ∈ Icc 0 T, Function.Odd (U t)) (hk : k ≠ 0)
    (w : SeedOn (fun t a => fderiv ℝ (U t) (X 0 t a))
      (fun t a => labelWaveVector X 0 a k t) center t₀ T ell D C)
    (hr : 0 ≤ r) (hEll : 0 < ell) (hcell : 2 * ell < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) :
    let W := localizedTransportedProfile (fun t => X t 0) k (w.switchedLeading r h)
    ContDiffOn ℝ ∞ (Function.uncurry W) (Icc 0 T ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc 0 T, SpatiallyPeriodic (W t) ∧ Function.Odd (W t) := by
  obtain ⟨hSmooth, hEven⟩ := SeedOn.regularity_of_parent ht₀ ht₀T hX hU hper hodd hk w
  have hT : 0 < T := ht₀.trans_lt ht₀T
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  let A : Velocity := fun t => X t 0
  let W := localizedTransportedProfile A k (w.switchedLeading r h)
  have hA : ContDiffOn ℝ ∞ (Function.uncurry A) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hX.contDiffOn_inverseLabelFlow hT hU hper
  obtain ⟨K, hK⟩ := exists_lipschitzWith_of_contDiffOn_periodic hT (hU.of_le (by simp)) hper
  have hReflect := (w.twistedSwitchedLeading_agreement_and_reflection k hr hEll hcell hh hh₁ hEven).2
  refine ⟨w.contDiffOn_transportedSwitchedLeading k ht₀T hr hEll hcell hh hh₁ hSmooth hA,
    fun t ht => ?_⟩
  refine ⟨spatiallyPeriodic_localizedTransportedProfile
    (A := A) (hX.add_latticeVector hK hper ht h₀) k (w.switchedLeading r h), ?_⟩
  have hAodd : Function.Odd (A t) := hX.odd hK hodd ht h₀
  show Function.Odd (W t)
  intro x
  calc
    W t (-x) = phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t
        (A t (-x)) ⟪k, A t (-x)⟫_ℝ :=
      (phaseTwistedPeriodizeCentered_on_graph A k (w.switchedLeading r h) t (-x)).symm
    _ = phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t
        (-A t x) (-⟪k, A t x⟫_ℝ) := by rw [hAodd x, inner_neg_right]
    _ = -phaseTwistedPeriodizeCentered k (w.switchedLeading r h) t (A t x) ⟪k, A t x⟫_ℝ :=
      hReflect t ht.2 (A t x) ⟪k, A t x⟫_ℝ
    _ = -W t x := congrArg Neg.neg
      (phaseTwistedPeriodizeCentered_on_graph A k (w.switchedLeading r h) t x)

end TorusEuler.LocalizedAmplitude
