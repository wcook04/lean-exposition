import TorusEuler.Paper.Proofs.S5b.Lemma58C

/-!
# Lemma 5.8, third part (continued): the activation term at a fixed time

For an expansion with activation term `S = χ̃'A₁` (`S5.IsExpansion.activation`):

* `activation_eval`: `S(t,a,s) = χ̃'(t) · (twisted extension of A₁)(t,a,s)` on the slab;
* `activation_average`: `⟨S⟩ = 0`;
* `curlCorrection_activation_eval`: at `t ∈ [t₀,T]`,
  `C[S](t,·) = χ̃'(t) · C[V₀](t,·)` for the extended leading profile `V₀ = extLeading …`
  (`C[·]` acts at fixed time: the library `complete_smul_wrapped_eval`);
* `curlCorrection_extLeading_eq_zero_off_support`: `C[V₀]` vanishes at labels outside `supp g`.

These are the identities behind "at each time `t`, `R_χ̃` is `χ̃'(t)` times this field"
(`sections/08_exact_wave.tex:139-140`).
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile LocalizedAmplitude Lib.S5Bridge

noncomputable section

variable {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {k : Vec3} {t₀ : ℝ} {center : ℝ → Vec3}
  {pU : Pressure} {D lam : ℝ}

/-- Pulling a time factor out of the twisted extension. -/
theorem ptpc_smul_time (k : Vec3) (c : ℝ → ℝ) (f : ℝ → Vec3 → ℝ → Vec3) (t : ℝ) (a : Vec3)
    (s : ℝ) :
    phaseTwistedPeriodizeCentered k (fun u x q => c u • f u x q) t a s =
      c t • phaseTwistedPeriodizeCentered k f t a s := rfl

/-- **The activation term on the slab**: `S = χ̃' · (twisted extension of A₁)`. -/
theorem activation_eval {hT : 0 < T} (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T}
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) {amp : ℝ → Vec3 → Vec3} {P : ℕ}
    {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) :
    ∀ x ∈ hierarchyProfileSlab T, S.val.val.val x =
      χ.derivative x.1 • phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) x.1 x.2.1 x.2.2 := by
  refine forall_of_centeredCell (T := T) k
    (Q := fun x => S.val.val.val x =
      χ.derivative x.1 • phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) x.1 x.2.1 x.2.2)
    (fun t a s n hq => ?_) (fun t ht a ha s => ?_)
  · change S.val.val.val (t, a + latticeVector n, s + ⟪k, latticeVector n⟫_ℝ) =
      χ.derivative t • phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) t
        (a + latticeVector n) (s + ⟪k, latticeVector n⟫_ℝ)
    rw [HierarchyTwistedProfile.twistedSlice, phaseTwistedPeriodizeCentered_translate]
    exact hq
  · change S.val.val.val (t, a, s) =
      χ.derivative t • phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) t a s
    rw [hu.activation t ht a ha s, wrapped_eq_on_cell k ha s hfit
      (fun b hb q => by simp only [rawLeading, radialEnvelope_eq_zero hℓ hb, zero_smul]),
      rawLeading_eq_leading]

/-- The activation term has zero phase mean. -/
theorem activation_average {hT : 0 < T} (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T}
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) : (S5.ops d).average S = 0 := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  rw [Bridge.ops_average_eval d _ hx]
  have hfun : (fun z => S.val.val.val (x.1, x.2.1, z)) =
      fun z => χ.derivative x.1 • phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) x.1 x.2.1 z :=
    funext fun z => activation_eval d hℓ hfit hu (x.1, x.2.1, z) ⟨hx.1, mem_univ _⟩
  rw [hfun, phaseMean_const_smul]
  have h0 : phaseMean (phaseTwistedPeriodizeCentered k (rawLeading ℓ h amp) x.1 x.2.1) = 0 := by
    refine phaseMean_wrapped_shift k x.2.1 (fun b q => ?_) (fun b => ?_)
    · simp only [rawLeading, periodic_waveProfile hh hh₁ q]
    · have he : rawLeading ℓ h amp x.1 b =
          fun q => radialEnvelope ℓ b • ContinuousLinearMap.toSpanSingleton ℝ (amp x.1 b)
            (waveProfile h q) := by
        funext q
        simp only [rawLeading, ContinuousLinearMap.toSpanSingleton_apply]
      rw [he, phaseMean_const_smul, phaseMean,
        (ContinuousLinearMap.toSpanSingleton ℝ (amp x.1 b)).intervalIntegral_comp_comm
          ((contDiff_waveProfile hh hh₁).continuous.intervalIntegrable 0 1),
        ← phaseMean, phaseMean_waveProfile hh hh₁, map_zero, smul_zero]
  rw [h0, smul_zero]
  rfl

/-- **`C[·]` acts at fixed time**: at `t ∈ [t₀,T]`, `C[S](t,·) = χ̃'(t) C[V₀](t,·)` for the
extended leading profile `V₀` (library `complete_smul_wrapped_eval`). -/
theorem curlCorrection_activation_eval {hT : 0 < T} (d : ParentGeometry hT U X k)
    (hL : S5.Launch T X k lam t₀) {χ : PaperWaveCutoff t₀ T}
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {amp ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    (hEq : ∀ t ∈ Icc t₀ T, ∀ a, ampE t a = amp t a)
    {P : ℕ} {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    (S5.curlCorrection d S).val.val.val (t, a, s) =
      χ.derivative t • (S5.curlCorrection d (extLeading (T := T) k hℓ hfit hh hh₁ hE)).val.val.val
        (t, a, s) := by
  have ht' : t ∈ Icc 0 T := Bridge.Launch.active_subset hL ht
  have hκ : ∀ x ∈ hierarchyProfileSlab T, d.covector.val.val.val x = S5.waveVector X k x.1 x.2.1 :=
    fun x hx => d.covector_value x hx
  have hS := complete_smul_wrapped_eval hT d.inverse d.covector S
    d.oscillation.covector_independent d.oscillation.covector_ne_zero hκ
    (by exact activation_average d hℓ hfit hh hh₁ hu) ht'
    (c := χ.derivative) (raw := rawLeading ℓ h amp)
    (fun b q => activation_eval d hℓ hfit hu (t, b, q) ⟨ht', mem_univ _⟩) a s
  have hV := complete_smul_wrapped_eval hT d.inverse d.covector
    (extLeading (T := T) k hℓ hfit hh hh₁ hE)
    d.oscillation.covector_independent d.oscillation.covector_ne_zero hκ
    (by exact extLeading_average hT d hℓ hfit hh hh₁ hE) ht'
    (c := fun _ => 1) (raw := rawLeading ℓ h amp)
    (fun b q => by
      rw [extLeading_active_eval k hℓ hfit hh hh₁ hE hEq hL.start_nonneg ht b q, one_smul]) a s
  change (complete hT d.inverse d.covector _ _ S).val.val.val (t, a, s) =
    χ.derivative t • (complete hT d.inverse d.covector _ _
      (extLeading (T := T) k hℓ hfit hh hh₁ hE)).val.val.val (t, a, s)
  rw [hS, hV, one_smul]

/-- The wave potential of the zero profile vanishes. -/
theorem wavePotential_zero (K : Vec3) (s : ℝ) : wavePotential K (fun _ => (0 : Vec3)) s = 0 := by
  have h0 : (fun q : ℝ => (-(‖K‖ ^ 2)⁻¹) • cross3 K ((fun _ => (0 : Vec3)) q)) = fun _ => 0 := by
    funext q
    change (-(‖K‖ ^ 2)⁻¹) • cross3Left K 0 = 0
    rw [map_zero, smul_zero]
  unfold wavePotential
  rw [h0]
  simp [phasePrimitive, phaseOscillation, phaseMean]

/-- **`C[V₀]` vanishes at labels outside `supp g`** (it is a label derivative of the wave
potential of `V₀`, which vanishes on the open complement of `supp g`). -/
theorem curlCorrection_extLeading_eq_zero_off_support {hT : 0 < T} (d : ParentGeometry hT U X k)
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1)
    {ampE : ℝ → Vec3 → Vec3}
    (hE : ContDiffOn ℝ ∞ (Function.uncurry ampE) (univ ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) {a : Vec3} (ha : a ∉ S5.envelopeSupport ℓ) (s : ℝ) :
    (S5.curlCorrection d (extLeading (T := T) k hℓ hfit hh hh₁ hE)).val.val.val (t, a, s) = 0 := by
  have hκ : ∀ x ∈ hierarchyProfileSlab T, d.covector.val.val.val x = S5.waveVector X k x.1 x.2.1 :=
    fun x hx => d.covector_value x hx
  have hV := complete_smul_wrapped_eval hT d.inverse d.covector
    (extLeading (T := T) k hℓ hfit hh hh₁ hE)
    d.oscillation.covector_independent d.oscillation.covector_ne_zero hκ
    (by exact extLeading_average hT d hℓ hfit hh hh₁ hE) ht
    (c := fun _ => 1) (raw := rawLeading ℓ h ampE)
    (fun b q => by rw [extLeading_eval k hℓ hfit hh hh₁ hE ht b q, one_smul]) a s
  have hopen : IsOpen (S5.envelopeSupport ℓ)ᶜ := (isClosed_tsupport _).isOpen_compl
  have hev : (fun b => wavePotential (S5.waveVector X k t b)
      (phaseTwistedPeriodizeCentered k (rawLeading ℓ h ampE) t b) s) =ᶠ[𝓝 a] fun _ => 0 := by
    filter_upwards [hopen.mem_nhds ha] with b hb
    have hz : phaseTwistedPeriodizeCentered k (rawLeading ℓ h ampE) t b = fun _ => 0 :=
      funext fun q => ptpc_eq_zero_off_support k (f := fun u x q => waveProfile h q • ampE u x) hb t q
    rw [hz]
    exact wavePotential_zero _ s
  change (complete hT d.inverse d.covector _ _ (extLeading (T := T) k hℓ hfit hh hh₁ hE)).val.val.val
    (t, a, s) = 0
  rw [hV, hev.fderiv_eq, fderiv_const_apply, ContinuousLinearMap.zero_comp, one_smul]
  ext i
  fin_cases i <;> simp [curlOfDerivative]

end

end TorusEuler.Paper.S5b
