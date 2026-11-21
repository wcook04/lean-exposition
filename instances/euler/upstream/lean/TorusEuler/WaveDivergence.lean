import TorusEuler.TransportedPhase
import TorusEuler.WaveCompletion
import TorusEuler.WaveCurl
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

open ContinuousLinearMap Filter Set
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The differential of a joint label-phase profile is the sum of its partial differentials. -/
theorem hasFDerivAt_profile_partials {f : Vec3 × ℝ → E} {a : Vec3} {s : ℝ}
    (hf : DifferentiableAt ℝ f (a, s)) :
    HasFDerivAt f
      ((fderiv ℝ (fun b => f (b, s)) a).coprod
        (toSpanSingleton ℝ (deriv (fun r => f (a, r)) s))) (a, s) := by
  have ha := (hf.hasFDerivAt.comp a (hasFDerivAt_prodMk_left (𝕜 := ℝ) a s)).fderiv
  have hs := (hf.hasFDerivAt.comp s (hasFDerivAt_prodMk_right (𝕜 := ℝ) a s)).hasDerivAt
  change fderiv ℝ (fun b => f (b, s)) a = _ at ha
  change HasDerivAt (fun r => f (a, r)) _ s at hs
  refine hf.hasFDerivAt.congr_fderiv ?_
  apply ContinuousLinearMap.ext
  intro p
  rw [coprod_apply, ha, hs.deriv]
  simp only [comp_apply, inl_apply, toSpanSingleton_apply, inr_apply]
  rw [← map_smul, Prod.smul_mk, smul_zero, smul_eq_mul, mul_one, ← map_add]
  simp

theorem curlOfDerivative_add (F G : Vec3 →L[ℝ] Vec3) :
    curlOfDerivative (F + G) = curlOfDerivative F + curlOfDerivative G := by
  ext i
  fin_cases i <;> simp [curlOfDerivative] <;> abel

/-- The Eulerian curl of a modulated vector profile has slow curl and fast cross-product terms. -/
theorem curl_transportedProfile {A : Velocity} {k x : Vec3} {t : ℝ}
    {Q : ℝ → Vec3 → ℝ → Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    (hA : HasFDerivAt (A t) Ax x)
    (hQ : DifferentiableAt ℝ (fun p : Vec3 × ℝ => Q t p.1 p.2) (A t x, ⟪k, A t x⟫_ℝ)) :
    let a := A t x
    let s := ⟪k, a⟫_ℝ
    curl (transportedProfile A k Q t) x =
      curlOfDerivative ((fderiv ℝ (fun b => Q t b s) a).comp Ax) +
        cross3 (Ax.adjoint k) (deriv (Q t a) s) := by
  rw [curl, (hasFDerivAt_transportedProfile hA (hasFDerivAt_profile_partials hQ)).fderiv,
    curlOfDerivative_add]
  congr 1
  exact coordinateCurl_rankOne _ _

/-- Apply the exact fast curl inverse of (3.5) at the transported phase.
The slow curl is taken in the label at fixed phase, then pulled back through the inverse flow. -/
theorem curl_transportedWavePotential {A : Velocity} {k x : Vec3} {t : ℝ}
    {V : ℝ → Vec3 → ℝ → Vec3} {κ : ℝ → Vec3 → Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    (hA : HasFDerivAt (A t) Ax x) (hκ : κ t (A t x) = Ax.adjoint k)
    (hk : κ t (A t x) ≠ 0) (hV : Continuous (V t (A t x)))
    (htrans : ∀ s, ⟪κ t (A t x), V t (A t x) s⟫_ℝ = 0)
    (hQ : DifferentiableAt ℝ
      (fun p : Vec3 × ℝ => wavePotential (κ t p.1) (V t p.1) p.2) (A t x, ⟪k, A t x⟫_ℝ)) :
    let Q := fun τ b => wavePotential (κ τ b) (V τ b)
    let a := A t x
    let s := ⟪k, a⟫_ℝ
    curl (transportedProfile A k Q t) x =
      V t a s + curlOfDerivative ((fderiv ℝ (fun b => Q t b s) a).comp Ax) := by
  let Q := fun τ b => wavePotential (κ τ b) (V τ b)
  change curl (transportedProfile A k Q t) x = _
  rw [curl_transportedProfile (k := k) hA hQ, ← hκ]
  change _ + cross3 (κ t (A t x)) (deriv (wavePotential (κ t (A t x)) (V t (A t x)))
    ⟪k, A t x⟫_ℝ) = _
  rw [wavePotential_fast_curl hk hV htrans, add_comm]

/-- The slow curl in the completion is the ordinary Eulerian curl taken with the phase held fixed. -/
theorem curl_transportedWavePotential_eq_add_slowCurl {A : Velocity} {k x : Vec3} {t : ℝ}
    {V : ℝ → Vec3 → ℝ → Vec3} {κ : ℝ → Vec3 → Vec3} {Ax : Vec3 →L[ℝ] Vec3}
    (hA : HasFDerivAt (A t) Ax x) (hκ : κ t (A t x) = Ax.adjoint k)
    (hk : κ t (A t x) ≠ 0) (hV : Continuous (V t (A t x)))
    (htrans : ∀ s, ⟪κ t (A t x), V t (A t x) s⟫_ℝ = 0)
    (hQ : DifferentiableAt ℝ
      (fun p : Vec3 × ℝ => wavePotential (κ t p.1) (V t p.1) p.2) (A t x, ⟪k, A t x⟫_ℝ)) :
    let Q := fun τ b => wavePotential (κ τ b) (V τ b)
    let s := ⟪k, A t x⟫_ℝ
    curl (transportedProfile A k Q t) x =
      transportedProfile A k V t x + curl (fun y => Q t (A t y) s) x := by
  let Q := fun τ b => wavePotential (κ τ b) (V τ b)
  let s := ⟪k, A t x⟫_ℝ
  have hd := hQ.hasFDerivAt.comp (A t x) (hasFDerivAt_prodMk_left (𝕜 := ℝ) (A t x) s)
  have hpartial : DifferentiableAt ℝ (fun b => Q t b s) (A t x) := hd.differentiableAt
  change curl (transportedProfile A k Q t) x =
    transportedProfile A k V t x + curl (fun y => Q t (A t y) s) x
  rw [curl_transportedWavePotential (k := k) hA hκ hk hV htrans hQ]
  change _ = transportedProfile A k V t x + curlOfDerivative (fderiv ℝ (fun y => Q t (A t y) s) x)
  have hfixed := (hpartial.hasFDerivAt.comp x hA).fderiv
  change fderiv ℝ (fun y => Q t (A t y) s) x = _ at hfixed
  rw [hfixed]
  rfl

private noncomputable def curlDerivativeLinear : (Vec3 →L[ℝ] Vec3) →ₗ[ℝ] Vec3 where
  toFun := curlOfDerivative
  map_add' := curlOfDerivative_add
  map_smul' := curlOfDerivative_smul

/-- Spatial divergence of the curl of a twice differentiable potential vanishes. -/
theorem divergence_curl {Q : Vec3 → Vec3} {x : Vec3} (hQ : ContDiffAt ℝ 2 Q x) :
    divergence (curl Q) x = 0 := by
  let L := curlDerivativeLinear.toContinuousLinearMap
  let H := fderiv ℝ (fderiv ℝ Q) x
  have hH : HasFDerivAt (fderiv ℝ Q) H x :=
    (hQ.fderiv_right (m := 1) (by norm_num)).differentiableAt_one.hasFDerivAt
  have hcurl : fderiv ℝ (curl Q) x = L.comp H := (L.hasFDerivAt.comp x hH).fderiv
  let e (i : Fin 3) := EuclideanSpace.single i (1 : ℝ)
  have hs (i j k : Fin 3) : (H (e i) (e j)) k = (H (e j) (e i)) k :=
    congrArg (fun v : Vec3 => v k) ((hQ.isSymmSndFDerivAt (by simp)).eq (e i) (e j))
  rw [divergence, hcurl, Fin.sum_univ_three]
  change (H (e 0) (e 1) 2 - H (e 0) (e 2) 1) +
      (H (e 1) (e 2) 0 - H (e 1) (e 0) 2) +
      (H (e 2) (e 0) 1 - H (e 2) (e 1) 0) = 0
  rw [hs 0 1 2, hs 1 2 0, hs 2 0 1]
  abel

/-- The localized completed wave is divergence free on any open chart where the
inverse label and the potential have the stated regularity. -/
theorem divergence_completedWaveOn {U : Set Vec3} {A : Velocity} {k x : Vec3} {t : ℝ}
    {V : ℝ → Vec3 → ℝ → Vec3} {κ : ℝ → Vec3 → Vec3}
    (hU : IsOpen U) (hx : x ∈ U)
    (hA : ∀ y ∈ U, ContDiffAt ℝ 2 (A t) y)
    (hκ : ∀ y ∈ U, κ t (A t y) = (fderiv ℝ (A t) y).adjoint k)
    (hk : ∀ y ∈ U, κ t (A t y) ≠ 0)
    (hV : ∀ y ∈ U, Continuous (V t (A t y)))
    (htrans : ∀ y ∈ U, ∀ s, ⟪κ t (A t y), V t (A t y) s⟫_ℝ = 0)
    (hQ : ∀ y ∈ U, ContDiffAt ℝ 2
      (fun p : Vec3 × ℝ => wavePotential (κ t p.1) (V t p.1) p.2) (A t y, ⟪k, A t y⟫_ℝ)) :
    let Q := fun τ b => wavePotential (κ τ b) (V τ b)
    divergence
      (fun y => transportedProfile A k V t y +
        curl (fun z => Q t (A t z) ⟪k, A t y⟫_ℝ) y) x = 0 := by
  let Q := fun τ b => wavePotential (κ τ b) (V τ b)
  have heq : (fun y => transportedProfile A k V t y +
        curl (fun z => Q t (A t z) ⟪k, A t y⟫_ℝ) y) =ᶠ[𝓝 x]
      curl (transportedProfile A k Q t) := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact (curl_transportedWavePotential_eq_add_slowCurl (k := k)
      ((hA y hy).differentiableAt (by simp)).hasFDerivAt (hκ y hy) (hk y hy) (hV y hy)
        (htrans y hy) ((hQ y hy).differentiableAt (by simp))).symm
  have hphase : ContDiffAt ℝ 2 (fun y => ⟪k, A t y⟫_ℝ) x :=
    (innerSL ℝ k).contDiff.contDiffAt.comp x (hA x hx)
  have hcomp := (hQ x hx).comp x ((hA x hx).prodMk hphase)
  have hQeval : ContDiffAt ℝ 2 (transportedProfile A k Q t) x := hcomp
  change divergence (fun y => transportedProfile A k V t y +
    curl (fun z => Q t (A t z) ⟪k, A t y⟫_ℝ) y) x = 0
  unfold divergence
  rw [heq.fderiv_eq]
  exact divergence_curl hQeval

/-- The representative with each coordinate in the half-open centered label cell. -/
noncomputable def centeredLabel (x : Vec3) : Vec3 :=
  WithLp.toLp 2 (fun i => Int.fract (x i + 1 / 2) - 1 / 2)

theorem spatiallyPeriodic_centeredLabel : SpatiallyPeriodic centeredLabel := by
  intro n x
  apply PiLp.ext
  intro i
  change Int.fract (x i + (n i : ℝ) + 1 / 2) - 1 / 2 = Int.fract (x i + 1 / 2) - 1 / 2
  rw [add_right_comm, Int.fract_add_intCast]

/-- Extend a label profile periodically using its values on the centered cell. -/
noncomputable def periodizeCentered {F : Type*} (f : Vec3 → F) : Vec3 → F :=
  f ∘ centeredLabel

theorem spatiallyPeriodic_periodizeCentered {F : Type*} (f : Vec3 → F) :
    SpatiallyPeriodic (periodizeCentered f) := by
  intro n x
  exact congrArg f (spatiallyPeriodic_centeredLabel n x)

private theorem centeredLabel_eq_of_mem {x : Vec3}
    (hx : ∀ i : Fin 3, -(1 / 2 : ℝ) ≤ x i ∧ x i < 1 / 2) :
    centeredLabel x = x := by
  apply PiLp.ext
  intro i
  have hz : ⌊x i + 1 / 2⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨by linarith [(hx i).1],
    by linarith [(hx i).2]⟩
  change Int.fract (x i + 1 / 2) - 1 / 2 = x i
  rw [Int.fract, hz, Int.cast_zero, sub_zero, add_sub_cancel_right]

/-- The periodic extension agrees on the whole closed cell when the profile vanishes near
its boundary. -/
theorem periodizeCentered_eq_on_centeredCell {F : Type*} [Zero F] {f : Vec3 → F} {δ : ℝ}
    (hδ : 0 < δ)
    (hf : ∀ x, (∃ i : Fin 3, 1 / 2 - δ < |x i|) → f x = 0) :
    EqOn (periodizeCentered f) f centeredCell := by
  intro x hx
  change f (centeredLabel x) = f x
  by_cases h : ∀ i : Fin 3, x i < 1 / 2
  · rw [centeredLabel_eq_of_mem (fun i => ⟨(hx i).1, h i⟩)]
  · push Not at h
    obtain ⟨i, hi⟩ := h
    have hxi : x i = 1 / 2 := le_antisymm (hx i).2 hi
    have hyi : centeredLabel x i = -(1 / 2 : ℝ) := by
      change Int.fract (x i + 1 / 2) - 1 / 2 = _
      norm_num [hxi]
    rw [hf _ ⟨i, by rw [hyi, abs_neg, abs_of_nonneg (by norm_num)]; linarith⟩,
      hf _ ⟨i, by rw [hxi, abs_of_nonneg (by norm_num)]; linarith⟩]

private theorem centeredLabel_eventuallyEq_translate {x : Vec3}
    (hx : ∀ i : Fin 3, 0 < Int.fract (x i + 1 / 2)) :
    centeredLabel =ᶠ[𝓝 x] fun y => y - latticeVector (fun i => ⌊x i + 1 / 2⌋) := by
  have hcoord (i : Fin 3) :
      ∀ᶠ y in 𝓝 x, ⌊y i + (1 / 2 : ℝ)⌋ = ⌊x i + 1 / 2⌋ := by
    let n : ℤ := ⌊x i + (1 / 2 : ℝ)⌋
    have hlt₁ : (n : ℝ) < x i + 1 / 2 := sub_pos.mp (hx i)
    have hlt₂ : x i + 1 / 2 < (n : ℝ) + 1 := Int.lt_floor_add_one _
    have hcont : Continuous (fun y : Vec3 => y i + (1 / 2 : ℝ)) :=
      (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).add continuous_const
    filter_upwards [hcont.continuousAt.eventually (Ioo_mem_nhds hlt₁ hlt₂)] with y hy
    exact Int.floor_eq_iff.mpr ⟨hy.1.le, hy.2⟩
  filter_upwards [eventually_all.mpr hcoord] with y hy
  apply PiLp.ext
  intro i
  change Int.fract (y i + 1 / 2) - 1 / 2 = y i - (⌊x i + 1 / 2⌋ : ℤ)
  rw [Int.fract, hy i]
  ring

private theorem centeredLabel_eventually_in_collar {x : Vec3} {i : Fin 3} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hx : Int.fract (x i + 1 / 2) = 0) :
    ∀ᶠ y in 𝓝 x, 1 / 2 - δ < |centeredLabel y i| := by
  let n : ℤ := ⌊x i + (1 / 2 : ℝ)⌋
  have hcenter : x i + 1 / 2 - (n : ℝ) = 0 := hx
  have hcont : Continuous (fun y : Vec3 => y i + 1 / 2 - (n : ℝ)) :=
    ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) i).add continuous_const).sub continuous_const
  have hnear : -(δ : ℝ) < x i + 1 / 2 - (n : ℝ) ∧ x i + 1 / 2 - (n : ℝ) < δ := by
    rw [hcenter]
    exact ⟨neg_lt_zero.mpr hδ, hδ⟩
  filter_upwards [hcont.continuousAt.eventually (Ioo_mem_nhds hnear.1 hnear.2)] with y hy
  let u := y i + (1 / 2 : ℝ) - (n : ℝ)
  change -(δ : ℝ) < u ∧ u < δ at hy
  change 1 / 2 - δ < |Int.fract (y i + 1 / 2) - 1 / 2|
  have hfract : Int.fract (y i + 1 / 2) = Int.fract u := by
    rw [← Int.fract_add_intCast u n]
    congr 1
    exact (sub_add_cancel _ _).symm
  rw [hfract]
  by_cases hu : 0 ≤ u
  · have hfloor : ⌊u⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hu, by linarith [hy.2]⟩
    rw [Int.fract, hfloor, Int.cast_zero, sub_zero, abs_of_nonpos (by linarith [hy.2])]
    linarith [hy.2]
  · have hfloor : ⌊u⌋ = -1 := Int.floor_eq_iff.mpr ⟨by norm_num; linarith [hy.1],
      by norm_num; exact lt_of_not_ge hu⟩
    rw [Int.fract, hfloor, Int.cast_neg, Int.cast_one, abs_of_nonneg (by linarith [hy.1])]
    linarith [hy.1]

/-- A smooth label profile that vanishes in a collar of the cell boundary extends smoothly
and periodically, even if its phase is defined using a nonlattice wave vector. -/
theorem contDiff_periodizeCentered {f : Vec3 → E} {m : WithTop ℕ∞} {δ : ℝ}
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) (hreg : ContDiff ℝ m f)
    (hf : ∀ x, (∃ i : Fin 3, 1 / 2 - δ < |x i|) → f x = 0) :
    ContDiff ℝ m (periodizeCentered f) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : ∀ i : Fin 3, 0 < Int.fract (x i + 1 / 2)
  · have htranslate : ContDiff ℝ m (fun y => f (y - latticeVector (fun i => ⌊x i + 1 / 2⌋))) :=
      hreg.comp (contDiff_id.sub contDiff_const)
    exact htranslate.contDiffAt.congr_of_eventuallyEq
      ((centeredLabel_eventuallyEq_translate hx).mono fun y hy => congrArg f hy)
  · push Not at hx
    obtain ⟨i, hi⟩ := hx
    have hboundary : Int.fract (x i + 1 / 2) = 0 := le_antisymm hi (Int.fract_nonneg _)
    apply (contDiffAt_const (c := (0 : E))).congr_of_eventuallyEq
    filter_upwards [centeredLabel_eventually_in_collar hδ hδ' hboundary] with y hy
    exact hf _ ⟨i, hy⟩

/-- The label-cell evaluation and its extension, composed with the inverse flow. -/
noncomputable def localizedTransportedProfile {F : Type*} (A : Velocity) (k : Vec3)
    (f : ℝ → Vec3 → ℝ → F) (t : ℝ) : Vec3 → F :=
  (periodizeCentered (fun a => f t a ⟪k, a⟫_ℝ)) ∘ A t

theorem spatiallyPeriodic_localizedTransportedProfile {F : Type*} {A : Velocity} {t : ℝ}
    (hA : ∀ (n : Fin 3 → ℤ) (x : Vec3), A t (x + latticeVector n) = A t x + latticeVector n)
    (k : Vec3) (f : ℝ → Vec3 → ℝ → F) :
    SpatiallyPeriodic (localizedTransportedProfile A k f t) := by
  intro n x
  let f₀ := fun a => f t a ⟪k, a⟫_ℝ
  change periodizeCentered f₀ (A t (x + latticeVector n)) = periodizeCentered f₀ (A t x)
  rw [hA]
  exact spatiallyPeriodic_periodizeCentered _ n (A t x)

theorem contDiff_localizedTransportedProfile {A : Velocity} {k : Vec3} {t : ℝ}
    {f : ℝ → Vec3 → ℝ → E} {m : WithTop ℕ∞} {δ : ℝ}
    (hA : ContDiff ℝ m (A t)) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hreg : ContDiff ℝ m (fun a => f t a ⟪k, a⟫_ℝ))
    (hf : ∀ a : Vec3, (∃ i : Fin 3, 1 / 2 - δ < |a i|) → f t a ⟪k, a⟫_ℝ = 0) :
    ContDiff ℝ m (localizedTransportedProfile A k f t) :=
  (contDiff_periodizeCentered hδ hδ' hreg hf).comp hA

theorem localizedTransportedProfile_eventuallyEq {F : Type*} [Zero F]
    {A : Velocity} {k x : Vec3} {t δ : ℝ} {f : ℝ → Vec3 → ℝ → F}
    (hA : ContinuousAt (A t) x) (hx : A t x ∈ interior centeredCell) (hδ : 0 < δ)
    (hf : ∀ a : Vec3, (∃ i : Fin 3, 1 / 2 - δ < |a i|) → f t a ⟪k, a⟫_ℝ = 0) :
    localizedTransportedProfile A k f t =ᶠ[𝓝 x] transportedProfile A k f t := by
  filter_upwards [hA.eventually (interior_mem_nhds.mp (isOpen_interior.mem_nhds hx))] with y hy
  exact periodizeCentered_eq_on_centeredCell hδ hf hy

theorem spatiallyPeriodic_curl {Q : Vec3 → Vec3} (hQ : SpatiallyPeriodic Q) :
    SpatiallyPeriodic (curl Q) := by
  intro n x
  have hshift : (fun y => Q (y + latticeVector n)) = Q := funext (hQ n)
  simp only [curl, ← fderiv_comp_add_right (latticeVector n), hshift]

theorem contDiff_curl {Q : Vec3 → Vec3} {m : WithTop ℕ∞}
    (hQ : ContDiff ℝ (m + 1) Q) : ContDiff ℝ m (curl Q) :=
  curlDerivativeLinear.toContinuousLinearMap.contDiff.comp (hQ.fderiv_right le_rfl)

/-- A completed wave made from a smooth periodized potential is smooth, periodic
and divergence free. Its cell formula is the original evaluated curl at every interior label. -/
theorem localizedCurl_properties {A : Velocity} {k : Vec3} {t δ : ℝ}
    {Q : ℝ → Vec3 → ℝ → Vec3}
    (hA : ContDiff ℝ ∞ (A t))
    (hperiod : ∀ (n : Fin 3 → ℤ) (x : Vec3), A t (x + latticeVector n) = A t x + latticeVector n)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hreg : ContDiff ℝ ∞ (fun a => Q t a ⟪k, a⟫_ℝ))
    (hQ : ∀ a : Vec3, (∃ i : Fin 3, 1 / 2 - δ < |a i|) → Q t a ⟪k, a⟫_ℝ = 0) :
    let P := localizedTransportedProfile A k Q t
    ContDiff ℝ ∞ (curl P) ∧ SpatiallyPeriodic (curl P) ∧
      (∀ x, divergence (curl P) x = 0) ∧
      ∀ x, A t x ∈ interior centeredCell →
        curl P x = curl (transportedProfile A k Q t) x := by
  have hP := contDiff_localizedTransportedProfile hA hδ hδ' hreg hQ
  refine ⟨contDiff_curl (by simpa using hP),
    spatiallyPeriodic_curl (spatiallyPeriodic_localizedTransportedProfile hperiod k Q),
    fun x => divergence_curl ((hP.of_le (by simp)).contDiffAt), fun x hx => ?_⟩
  exact congrArg curlOfDerivative
    (localizedTransportedProfile_eventuallyEq hA.continuous.continuousAt hx hδ hQ).fderiv_eq

theorem wavePotential_zero_of_profile_zero {κ : Vec3} {V : ℝ → Vec3}
    (hV : ∀ s, V s = 0) (s : ℝ) : wavePotential κ V s = 0 := by
  have hcross : cross3 κ 0 = 0 := by simp [cross3]
  simp [wavePotential, phasePrimitive, phaseOscillation, phaseMean, hV, hcross]

/-- The centered-cell construction of (3.5) gives a smooth periodic divergence-free
wave, with its exact slow and fast parts on the lifted label chart. -/
theorem localizedCompletedWave_properties {A : Velocity} {k : Vec3} {t δ : ℝ}
    {V : ℝ → Vec3 → ℝ → Vec3} {κ : ℝ → Vec3 → Vec3}
    (hA : ContDiff ℝ ∞ (A t))
    (hperiod : ∀ (n : Fin 3 → ℤ) (x : Vec3), A t (x + latticeVector n) = A t x + latticeVector n)
    (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hQ : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => wavePotential (κ t p.1) (V t p.1) p.2))
    (hzero : ∀ a : Vec3, (∃ i : Fin 3, 1 / 2 - δ < |a i|) → ∀ s, V t a s = 0)
    (hκ : ∀ x, A t x ∈ interior centeredCell →
      κ t (A t x) = (fderiv ℝ (A t) x).adjoint k)
    (hk : ∀ x, A t x ∈ interior centeredCell → κ t (A t x) ≠ 0)
    (hV : ∀ x, A t x ∈ interior centeredCell → Continuous (V t (A t x)))
    (htrans : ∀ x, A t x ∈ interior centeredCell → ∀ s, ⟪κ t (A t x), V t (A t x) s⟫_ℝ = 0) :
    let Q := fun τ a => wavePotential (κ τ a) (V τ a)
    let W := curl (localizedTransportedProfile A k Q t)
    ContDiff ℝ ∞ W ∧ SpatiallyPeriodic W ∧
      (∀ x, divergence W x = 0) ∧
      ∀ x, A t x ∈ interior centeredCell →
        W x = transportedProfile A k V t x + curl (fun y => Q t (A t y) ⟪k, A t x⟫_ℝ) x := by
  let Q := fun τ a => wavePotential (κ τ a) (V τ a)
  have hcomp := hQ.comp (contDiff_id.prodMk (innerSL ℝ k).contDiff)
  have hreg : ContDiff ℝ ∞ (fun a => Q t a ⟪k, a⟫_ℝ) := hcomp
  have hQzero (a : Vec3) (ha : ∃ i : Fin 3, 1 / 2 - δ < |a i|) : Q t a ⟪k, a⟫_ℝ = 0 :=
    wavePotential_zero_of_profile_zero (hzero a ha) _
  obtain ⟨hsmooth, hper, hsol, hcell⟩ := localizedCurl_properties hA hperiod hδ hδ' hreg hQzero
  refine ⟨hsmooth, hper, hsol, fun x hx => ?_⟩
  exact (hcell x hx).trans (curl_transportedWavePotential_eq_add_slowCurl
    (k := k) (hA.differentiable (by simp) x).hasFDerivAt (hκ x hx) (hk x hx)
      (hV x hx) (htrans x hx) (hQ.differentiable (by simp) _))

end TorusEuler
