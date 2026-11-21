import TorusEuler.Paper.Proofs.S5b.Lemma58B
import TorusEuler.Paper.Proofs.S5Bridge.Leading
import TorusEuler.PaperGenericSwitchCompletion

/-!
# Lemma 5.8, third part: a twisted profile of `A₁` on `[0,T]` and its curl correction

For the bound of `R_χ̃^♮` (`sections/08_exact_wave.tex:137-143`) the proof of Lemma 5.8 applies
(5.45) "at each time `t`" to the field `A₁ + C[A₁]`, of which `R_χ̃ = S + C[S]` is the multiple
`χ̃'(t)`. Lemma 5.7 is stated for twisted profiles on `[0,T]`, while `A₁ = g𝐚F_h` is given on
`[t₀,T]` only. Here the seed is extended smoothly in time (the library Seeley extension
`exists_smoothExtensionOfClosedTimeSlab`), which gives a twisted profile `extLeading` on
`[0,T]` equal to the twisted extension of `A₁` on `[t₀,T]` (`extLeading_active_eval`), vanishing
at labels outside `supp g` (`extLeading_eq_zero_off_support`), with zero phase mean
(`extLeading_average`) and transverse to `κ` on `[t₀,T]` (`extLeading_transverse`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile LocalizedAmplitude Lib.S5Bridge

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {t₀ : ℝ} {center : ℝ → Vec3}
  {pU : Pressure} {D lam : ℝ}

/-- The seed extends to a jointly smooth field on `ℝ × ℝ³` that agrees with it on
`[t₀,T] × ℝ³` (library Seeley extension in time). -/
theorem exists_seed_extension (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) :
    ∃ ampE : ℝ → Vec3 → Vec3, ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)) ∧
      ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a := by
  obtain ⟨g, hg, hEq⟩ := exists_smoothExtensionOfClosedTimeSlab hL.start_lt isOpen_univ hamp.smooth
  exact ⟨fun t a => g (t, a), hg, fun t ht a => hEq ⟨ht, mem_univ a⟩⟩

/-- The raw leading field `g(a) F_h(s) 𝐚(t,a)` for a field `𝐚` on all times. -/
def rawLeading (ℓ h : ℝ) (amp : ℝ → Vec3 → Vec3) (t : ℝ) (a : Vec3) (s : ℝ) : Vec3 :=
  radialEnvelope ℓ a • (waveProfile h s • amp t a)

/-- The raw leading term agrees with the leading term of Lemma 5.8. -/
theorem rawLeading_eq_leading (ℓ h : ℝ) (amp : ℝ → Vec3 → Vec3) (t : ℝ) (a : Vec3) (s : ℝ) :
    rawLeading ℓ h amp t a s = S5.leading ℓ h amp t a s := by
  simp only [rawLeading, S5.leading, smul_smul]

/-- The twisted profile on `[0,T]` of the leading field of an extended seed `ampE`. -/
def extLeading (k : Vec3) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3))) :
    HierarchyTwistedProfile T k Vec3 :=
  wrapProfile k (f := rawLeading ℓ h ampE)
    (contDiffOn_phaseTwistedPeriodizeCentered_radialEnvelope (k := k)
      (f := fun t a s => waveProfile h s • ampE t a) (I := Icc 0 T) hℓ hfit
      (leadingBare_smooth (t₀ := 0) (T := T) (hE.mono (prod_mono (subset_univ _) subset_rfl))
        hh hh₁))
    (fun t a s => by simp only [rawLeading, periodic_waveProfile hh hh₁ s])

/-- Evaluation of the extended leading term. -/
theorem extLeading_eval (k : Vec3) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h)
    (hh₁ : h ≤ 1) {ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) (s : ℝ) :
    (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k (rawLeading ℓ h ampE) t a s :=
  wrapProfile_eval k _ _ ht a s

/-- On `[t₀,T]` the extended leading profile is the twisted extension of `A₁`. -/
theorem extLeading_active_eval (k : Vec3) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1) {amp ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    (hEq : ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a) (ht₀ : 0 ≤ t₀)
    {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, a, s) =
      phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) t a s := by
  rw [extLeading_eval k hℓ hfit hh hh₁ hE ⟨ht₀.trans ht.1, ht.2⟩]
  simp only [phaseTwistedPeriodizeCentered, rawLeading, hEq t ht]

/-- The twisted extension of a field with the envelope factor vanishes at labels outside
`supp g`. -/
theorem ptpc_eq_zero_off_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (k : Vec3) {ℓ : ℝ} {f : ℝ → Vec3 → ℝ → E} {a : Vec3} (ha : a ∉ S5.envelopeSupport ℓ)
    (t s : ℝ) :
    phaseTwistedPeriodizeCentered k (fun u x q => radialEnvelope ℓ x • f u x q) t a s = 0 := by
  have h0 : periodizeCentered (radialEnvelope ℓ) a = 0 := image_eq_zero_of_notMem_tsupport ha
  change radialEnvelope ℓ (centeredLabel a) • _ = 0
  rw [show radialEnvelope ℓ (centeredLabel a) = 0 from h0, zero_smul]

/-- The extended leading profile vanishes at labels outside `supp g`. -/
theorem extLeading_eq_zero_off_support (k : Vec3) {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2)
    (hh : 0 < h) (hh₁ : h ≤ 1) {ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∉ S5.envelopeSupport ℓ) (s : ℝ) :
    (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, a, s) = 0 := by
  rw [extLeading_eval k hℓ hfit hh hh₁ hE ht]
  exact ptpc_eq_zero_off_support k (f := fun u x q => waveProfile h q • ampE u x) ha t s

/-- The extended leading profile has zero phase mean (`F_h` has zero mean). -/
theorem extLeading_average (hT : 0 < T) (d : ParentGeometry hT U X k) {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3))) :
    (S5.ops d).average (extLeading (T := T) k hℓ hfit hh hh₁ hE) = 0 := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  rw [Bridge.ops_average_eval d _ hx]
  have hfun : (fun z => (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (x.1, x.2.1, z)) =
      phaseTwistedPeriodizeCentered k (rawLeading ℓ h ampE) x.1 x.2.1 :=
    funext fun z => extLeading_eval k hℓ hfit hh hh₁ hE hx.1 _ _
  rw [hfun]
  refine phaseMean_wrapped_shift k x.2.1 (fun b q => ?_) (fun b => ?_)
  · simp only [rawLeading, periodic_waveProfile hh hh₁ q]
  · have he : rawLeading ℓ h ampE x.1 b =
        fun q => radialEnvelope ℓ b • ContinuousLinearMap.toSpanSingleton ℝ (ampE x.1 b)
          (waveProfile h q) := by
      funext q
      simp only [rawLeading, ContinuousLinearMap.toSpanSingleton_apply]
    rw [he, phaseMean_const_smul, phaseMean,
      (ContinuousLinearMap.toSpanSingleton ℝ (ampE x.1 b)).intervalIntegral_comp_comm
        ((contDiff_waveProfile hh hh₁).continuous.intervalIntegrable 0 1),
      ← phaseMean, phaseMean_waveProfile hh hh₁, map_zero, smul_zero]

/-- On `[t₀,T]` the extended leading profile is transverse to `κ` (the seed is). -/
theorem extLeading_transverse (hT : 0 < T) (d : ParentGeometry hT U X k)
    (hL : S5.Launch T X k lam t₀) {amp : ℝ → Vec3 → Vec3}
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hℓ : 0 < ℓ)
    (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    (hEq : ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a) :
    ∀ t ∈ Icc t₀ T, ∀ a s, ⟪S5.waveVector X k t a,
      (extLeading (T := T) k hℓ hfit hh hh₁ hE).val.val.val (t, a, s)⟫_ℝ = 0 := by
  let V := extLeading (T := T) k hℓ hfit hh hh₁ hE
  have hall := forall_of_centeredCell (T := T) k
    (Q := fun x => t₀ ≤ x.1 → ⟪d.covector.val.val.val x, V.val.val.val x⟫_ℝ = 0)
    (fun t a s n hq => by simpa only [HierarchyTwistedProfile.twistedSlice] using hq)
    (fun t ht a ha s hact => by
      have hκ : d.covector.val.val.val (t, a, s) = S5.waveVector X k t a :=
        d.covector_value (t, a, s) ⟨ht, mem_univ _⟩
      change ⟪d.covector.val.val.val (t, a, s), V.val.val.val (t, a, s)⟫_ℝ = 0
      rw [hκ, extLeading_active_eval k hℓ hfit hh hh₁ hE hEq hL.start_nonneg ⟨hact, ht.2⟩,
        wrapped_eq_on_cell k ha s hfit
          (fun b hb q => by simp only [rawLeading, radialEnvelope_eq_zero hℓ hb, zero_smul])]
      simp only [rawLeading, real_inner_smul_right, hamp.transverse a t ⟨hact, ht.2⟩, mul_zero])
  intro t ht a s
  have h := hall (t, a, s) ⟨Bridge.Launch.active_subset hL ht, mem_univ _⟩ ht.1
  have hκ : d.covector.val.val.val (t, a, s) = S5.waveVector X k t a :=
    d.covector_value (t, a, s) ⟨Bridge.Launch.active_subset hL ht, mem_univ _⟩
  change ⟪d.covector.val.val.val (t, a, s), V.val.val.val (t, a, s)⟫_ℝ = 0 at h
  rw [hκ] at h
  exact h

end

end TorusEuler.Paper.S5b
