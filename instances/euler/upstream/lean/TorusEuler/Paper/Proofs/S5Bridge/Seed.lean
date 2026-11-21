import TorusEuler.Paper.Proofs.S5Bridge.Parent
import TorusEuler.LinearFlow
import TorusEuler.AffinePropagation
import TorusEuler.LaterWaveHierarchyInput

/-!
# S5 bridge: the seed of §5.1

Glue between the seed of the Section 5 statements (`S5.IsSeed`, a predicate) and the
library seed structure `SeedOn` with its regularity record `SeedOn.HierarchyRegularity`.

* `SeedOn` carries, besides the defining equations of the seed (which are exactly those
  of `S5.IsSeed`), the quantitative field `near`, named `SeedNear` here and absent from
  `S5.IsSeed`. For `|a| ≤ 2ℓ` it contains the two bounds (5.19)
  (`|𝐚(t,a)| ≤ 2|𝐚(t,0)|`, `κ·M𝐚 > 0`) and in addition a label-Lipschitz bound
  `|𝐚(t,a) - 𝐚(t,0)| ≤ C|a||𝐚(t,0)|`, the lower size bound `|𝐚(t,0)|/2 ≤ |𝐚(t,a)|` and
  the two coupling bounds `(2𝖣)⁻¹|κ(t,0)||𝐚(t,0)| ≤ κ·M𝐚` and
  `(8𝖣)⁻¹ ≤ κ·M𝐚/(|κ||𝐚|)`. It is strictly stronger than the (5.19) conjunct of
  `Statement.lemma_5_3`, which therefore cannot supply it.
* The library lemma `exists_seedOn_of_coframe_bounds` constructs a `SeedOn` and proves
  `near` by the variation-of-constants argument of the proof of Lemma 5.3, which is the
  argument proving (5.19). It is mathematical content of Lemma 5.3 even though the ledger
  does not list it, and only the proof of Lemma 5.3 itself may use it: there `near` is
  rebuilt from the label-Lipschitz bounds of the coefficients implied by (D.6) of
  `Statement.proposition_5_1`, the seed is identified with the library amplitude by
  `IsSeed.eqOn_amplitude` (no smoothness of that amplitude is needed), and `near` passes
  to the seed by `seedNear_of_eqOn`. Every
  other row takes (5.19) from its hypothesis `h5_3` (if it cites 5.3) and works with
  library lemmas stated over `S5.IsSeed` and the two bounds of (5.19), not over `SeedOn`
  (copies of its own content lemmas, with these bounds as hypotheses in place of the
  `SeedOn` argument). Given `SeedNear`, `seedOnOfIsSeed` packages an `S5.IsSeed` as a
  `SeedOn` with the same amplitude (definitionally).
* Conversely every `SeedOn` over the parent coefficients with a smooth amplitude is an
  `S5.IsSeed` (`isSeed_of_seedOn`).
* The seed is unique: two solutions of (3.2) with the initial data (5.4) agree on
  `[t₀,T] × ℝ³` (linear ODE uniqueness at each label, `IsSeed.eqOn`).
* `hierarchyRegularity_of_isSeed` gives the library regularity record of a `SeedOn`
  whose amplitude is an `S5.IsSeed`, for the envelope radius `ℓ_*` and width `h` of
  §5.1 (`radius_fits`, `width_pos`, `width_le_one`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Bridge

open HierarchyTwistedProfile LocalizedAmplitude

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {t₀ : ℝ} {center : ℝ → Vec3}

/-- The seed coefficient `M(t,a)` of the parent, as a function of `(t,a)`. -/
abbrev seedStrain (U : Velocity) (X : ℝ → Velocity) : ℝ → Vec3 → Vec3 →L[ℝ] Vec3 :=
  fun t a => S5.strainField U X t a

/-- The seed coefficient `κ(t,a)` of the parent, as a function of `(t,a)`. -/
abbrev seedCovector (X : ℝ → Velocity) (k : Vec3) : ℝ → Vec3 → Vec3 :=
  fun t a => S5.waveVector X k t a

/-- The quantitative field `near` of the library `SeedOn` for an amplitude `amp`, for
labels `|a| ≤ 2ℓ`: a label-Lipschitz bound with constant `C`, the two-sided size bound
(whose upper half is the first bound of (5.19)), the lower coupling bound, the positivity
`κ·M𝐚 > 0` of (5.19) and the coupling ratio bound. It is not part of `S5.IsSeed`, and it
is strictly stronger than (5.19) as stated in `Statement.lemma_5_3`. Only the proof of
Lemma 5.3 can establish it (through `exists_seedOn_of_coframe_bounds`, see the module
docstring); other rows use the two bounds of (5.19) from `h5_3` instead. -/
def SeedNear (M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3) (κ : ℝ → Vec3 → Vec3) (center : ℝ → Vec3)
    (t₀ T ell D C : ℝ) (amp : ℝ → Vec3 → Vec3) : Prop :=
  ∀ a, ‖a‖ ≤ 2 * ell → ∀ t ∈ Icc t₀ T,
    ‖amp t a - center t‖ ≤ C * ‖a‖ * ‖center t‖ ∧
    (‖center t‖ / 2 ≤ ‖amp t a‖ ∧ ‖amp t a‖ ≤ 2 * ‖center t‖) ∧
    (2 * D)⁻¹ * (‖κ t 0‖ * ‖center t‖) ≤ ⟪κ t a, M t a (amp t a)⟫_ℝ ∧
    0 < ⟪κ t a, M t a (amp t a)⟫_ℝ ∧
    (8 * D)⁻¹ ≤ ⟪κ t a, M t a (amp t a)⟫_ℝ / (‖κ t a‖ * ‖amp t a‖)

/-- The field `near` of a library seed, as `SeedNear` of its amplitude. -/
theorem seedOn_seedNear {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {ell D C : ℝ} (w : SeedOn M κ center t₀ T ell D C) :
    SeedNear M κ center t₀ T ell D C w.amplitude :=
  w.near

/-- `SeedNear` only depends on the amplitude on `[t₀,T] × ℝ³`. -/
theorem seedNear_of_eqOn {M : ℝ → Vec3 → Vec3 →L[ℝ] Vec3} {κ : ℝ → Vec3 → Vec3}
    {ell D C : ℝ} {amp amp' : ℝ → Vec3 → Vec3} (h : SeedNear M κ center t₀ T ell D C amp)
    (heq : ∀ t ∈ Icc t₀ T, ∀ a, amp' t a = amp t a) :
    SeedNear M κ center t₀ T ell D C amp' := by
  intro a ha t ht
  rw [heq t ht a]
  exact h a ha t ht

/-- An `S5.IsSeed` together with the bounds `SeedNear` is a library seed `SeedOn` over
the parent coefficients, with the same amplitude. -/
def seedOnOfIsSeed {amp : ℝ → Vec3 → Vec3} (h : S5.IsSeed U X k t₀ T center amp)
    {ell D C : ℝ} (hnear : SeedNear (seedStrain U X) (seedCovector X k) center t₀ T ell D C amp) :
    SeedOn (seedStrain U X) (seedCovector X k) center t₀ T ell D C where
  amplitude := amp
  at_center := fun t ht => h.at_origin t ht
  activation := h.start
  equation := fun a t ht => h.equation a t ht
  transverse := fun a t ht => h.transverse a t ht
  near := hnear

/-- The amplitude of `seedOnOfIsSeed h hnear` is the seed `amp` itself. -/
@[simp] theorem seedOnOfIsSeed_amplitude {amp : ℝ → Vec3 → Vec3}
    (h : S5.IsSeed U X k t₀ T center amp) {ell D C : ℝ}
    (hnear : SeedNear (seedStrain U X) (seedCovector X k) center t₀ T ell D C amp) :
    (seedOnOfIsSeed h hnear).amplitude = amp := rfl

/-- A library seed over the parent coefficients with a jointly smooth amplitude is an
`S5.IsSeed`. -/
theorem isSeed_of_seedOn {ell D C : ℝ}
    (w : SeedOn (seedStrain U X) (seedCovector X k) center t₀ T ell D C)
    (hsmooth : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    S5.IsSeed U X k t₀ T center w.amplitude where
  at_origin := fun _ ht => w.at_center ht
  start := w.activation
  equation := fun a t ht => w.equation a t ht
  transverse := fun a t ht => w.transverse a t ht
  smooth := hsmooth

/-- A library seed over the parent coefficients with its regularity record is an
`S5.IsSeed`. -/
theorem isSeed_of_hierarchyRegularity {ell D C r h : ℝ}
    {w : SeedOn (seedStrain U X) (seedCovector X k) center t₀ T ell D C}
    (reg : w.HierarchyRegularity r h) : S5.IsSeed U X k t₀ T center w.amplitude :=
  isSeed_of_seedOn w reg.amplitude_smooth

section Unique

variable {pU : Pressure} {D lam : ℝ}

/-- A jointly continuous field of `(t,a)` is continuous in `t` at a fixed label. -/
theorem continuousOn_slice {F : Type*} [TopologicalSpace F] {f : ℝ → Vec3 → F} {J : Set ℝ}
    {S : Set (ℝ × Vec3)} (hf : ContinuousOn (Function.uncurry f) S) (a : Vec3)
    (hJ : ∀ r ∈ J, (r, a) ∈ S) : ContinuousOn (fun r => f r a) J :=
  hf.comp (continuous_id.prodMk continuous_const).continuousOn hJ

/-- `t ↦ M(t,a)` is continuous on `[t₀,T]`. -/
theorem strainField_continuousOn (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    (a : Vec3) : ContinuousOn (fun r => S5.strainField U X r a) (Icc t₀ T) :=
  continuousOn_slice (f := S5.strainField U X)
    (Parent.strainField_smooth (Launch.end_pos hL) hP).continuousOn a
    (fun _ hr => ⟨Launch.active_subset hL hr, mem_univ a⟩)

/-- `t ↦ κ(t,a)` is continuous on `[t₀,T]`. -/
theorem waveVector_continuousOn (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    (a : Vec3) : ContinuousOn (fun r => S5.waveVector X k r a) (Icc t₀ T) :=
  continuousOn_slice (f := S5.waveVector X k)
    (Parent.waveVector_smooth (Launch.end_pos hL) hP).continuousOn a
    (fun _ hr => ⟨Launch.active_subset hL hr, mem_univ a⟩)

/-- The seed operator `t ↦ -(Id - 2P_κ)M` at a label is continuous on `[t₀,T]`. -/
theorem seedOperator_continuousOn (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) (a : Vec3) :
    ContinuousOn (fun r => affineWaveAmplitudeOperator (S5.strainField U X r a)
      (S5.waveVector X k r a)) (Icc t₀ T) :=
  continuousOn_affineWaveAmplitudeOperator (strainField_continuousOn hP hL a)
    (waveVector_continuousOn hP hL a) fun _ hr =>
      Parent.waveVector_ne_zero (Launch.end_pos hL) hP hL.carrier_ne_zero
        (Launch.active_subset hL hr) a

/-- Uniqueness of the seed: two solutions of (3.2) with the initial data (5.4) agree on
`[t₀,T] × ℝ³` (linear ODE uniqueness at each label). -/
theorem IsSeed.eqOn (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {amp amp' : ℝ → Vec3 → Vec3} (h : S5.IsSeed U X k t₀ T center amp)
    (h' : S5.IsSeed U X k t₀ T center amp') : ∀ t ∈ Icc t₀ T, ∀ a, amp t a = amp' t a := by
  intro t ht a
  exact linearODE_unique_of_mem ordConnected_Icc (left_mem_Icc.mpr hL.start_lt.le)
    (seedOperator_continuousOn hP hL a) (fun r hr => h.equation a r hr)
    (fun r hr => h'.equation a r hr) ((h.start a).trans (h'.start a).symm) ht

/-- Every `S5.IsSeed` agrees on `[t₀,T] × ℝ³` with the amplitude of any library seed over
the parent coefficients whose amplitude is smooth. -/
theorem IsSeed.eqOn_seedOn (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (h : S5.IsSeed U X k t₀ T center amp) {ell D' C : ℝ}
    (w : SeedOn (seedStrain U X) (seedCovector X k) center t₀ T ell D' C)
    (hw : ContDiffOn ℝ ∞ (Function.uncurry w.amplitude) (Icc t₀ T ×ˢ (univ : Set Vec3))) :
    ∀ t ∈ Icc t₀ T, ∀ a, amp t a = w.amplitude t a :=
  IsSeed.eqOn hP hL h (isSeed_of_seedOn w hw)

/-- Every `S5.IsSeed` agrees on `[t₀,T] × ℝ³` with the amplitude of any library seed over
the parent coefficients, with no regularity assumption on the library amplitude (linear
ODE uniqueness at each label uses only the equation and the initial data). This identifies
the seed with the `SeedOn` of `exists_seedOn_of_coframe_bounds`, which records no
smoothness, in the proof of Lemma 5.3. -/
theorem IsSeed.eqOn_amplitude (hP : S5.Parent T U X pU D lam) (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (h : S5.IsSeed U X k t₀ T center amp) {ell D' C : ℝ}
    (w : SeedOn (seedStrain U X) (seedCovector X k) center t₀ T ell D' C) :
    ∀ t ∈ Icc t₀ T, ∀ a, amp t a = w.amplitude t a := by
  intro t ht a
  exact linearODE_unique_of_mem ordConnected_Icc (left_mem_Icc.mpr hL.start_lt.le)
    (seedOperator_continuousOn hP hL a) (fun r hr => h.equation a r hr)
    (fun r hr => w.equation a r hr) ((h.start a).trans (w.activation a).symm) ht

/-- The regularity record of the library seed built from an `S5.IsSeed` (or of any
library seed whose amplitude is an `S5.IsSeed`), for an envelope radius `ell` that fits in
the cell, a width `0 < h ≤ 1` and a rate `r ≥ 0`. -/
theorem hierarchyRegularity_of_isSeed (hP : S5.Parent T U X pU D lam)
    (hL : S5.Launch T X k lam t₀) {ell D' C : ℝ}
    (w : SeedOn (seedStrain U X) (seedCovector X k) center t₀ T ell D' C)
    (hw : S5.IsSeed U X k t₀ T center w.amplitude) {r h : ℝ} (hr : 0 ≤ r) (hell : 0 < ell)
    (hfit : 2 * ell < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) : w.HierarchyRegularity r h where
  nonneg_start := hL.start_nonneg
  start_lt_end := hL.start_lt
  rate_nonneg := hr
  envelope_pos := hell
  envelope_fits := hfit
  phase_pos := hh
  phase_le_one := hh₁
  strain_smooth := (Parent.strainField_smooth (Launch.end_pos hL) hP).mono
    (prod_mono (Launch.active_subset hL) subset_rfl)
  covector_smooth := (Parent.waveVector_smooth (Launch.end_pos hL) hP).mono
    (prod_mono (Launch.active_subset hL) subset_rfl)
  covector_nonzero := fun _ ht a =>
    Parent.waveVector_ne_zero (Launch.end_pos hL) hP hL.carrier_ne_zero (Launch.active_subset hL ht) a
  amplitude_smooth := hw.smooth

end Unique

/-- The envelope `ℓ_* = 𝖣^{-a}` fits in the label cell, `2ℓ_* < 1/2`, once `𝖣 ≥ 2` and
`a ≥ 3`. -/
theorem radius_fits {D : ℝ} (hD : 2 ≤ D) {a : ℕ} (ha : 3 ≤ a) : 2 * S5.radius D a < 1 / 2 := by
  have h8 : (8 : ℝ) ≤ D ^ a :=
    calc (8 : ℝ) = 2 ^ 3 := by norm_num
      _ ≤ D ^ 3 := pow_le_pow_left₀ (by norm_num) hD 3
      _ ≤ D ^ a := pow_le_pow_right₀ (by linarith) ha
  have hinv : (D ^ a)⁻¹ ≤ (8 : ℝ)⁻¹ := inv_anti₀ (by norm_num) h8
  unfold S5.radius
  linarith

end

end TorusEuler.Paper.Bridge
