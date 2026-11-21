import TorusEuler.Paper.Proofs.S5b.T56Level1

/-!
# Theorem 5.6, glue: elementary properties of the expansion

Zero phase mean of the sources, level-one facts and the vanishing of the operators before `t₀`.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.S5b

open AppendixD HierarchyTwistedProfile

noncomputable section

section Facts

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam t₀ : ℝ} {center : ℝ → Vec3}

local notation "VP" => HierarchyTwistedProfile T k Vec3

/-- `⟨κ∂_s q⟩ = 0` for every pressure profile (the phase derivative of a periodic function has
mean zero, and `κ` does not depend on the phase). -/
theorem average_phaseGrad_zero (d : ParentGeometry hT U X k) (q : HierarchyTwistedProfile T k ℝ) :
    (S5.ops d).average ((S5.ops d).phaseGrad q) = 0 := by
  apply HierarchyTwistedProfile.ext
  intro x hx
  rw [Bridge.ops_average_eval d _ hx]
  have hfun : (fun z => ((S5.ops d).phaseGrad q).val.val.val (x.1, x.2.1, z)) =
      fun z => deriv (fun r => q.val.val.val (x.1, x.2.1, r)) z • S5.waveVector X k x.1 x.2.1 :=
    funext fun z => Bridge.ops_phaseGrad_eval d q ⟨hx.1, mem_univ _⟩
  have hsm : ContDiff ℝ ∞ (fun r => q.val.val.val (x.1, x.2.1, r)) := by
    have hι : ContDiffOn ℝ ∞ (fun r : ℝ => ((x.1, x.2.1, r) : HierarchyProfilePoint)) univ :=
      (contDiff_const.prodMk (contDiff_const.prodMk contDiff_id)).contDiffOn
    exact contDiffOn_univ.mp ((HierarchySmoothProfile.smooth q.val.val).comp hι
      (fun r _ => ⟨hx.1, mem_univ _⟩))
  have hmean : phaseMean (fun z => deriv (fun r => q.val.val.val (x.1, x.2.1, r)) z) = 0 :=
    phaseMean_deriv (fun z => (hsm.differentiable (by simp) z).hasDerivAt)
      (hsm.continuous_deriv (by simp)) (HierarchyPeriodicProfile.phasePeriodic q.val x.1 x.2.1)
  rw [hfun]
  unfold phaseMean at hmean ⊢
  rw [intervalIntegral.integral_smul_const, hmean, zero_smul]
  rfl

/-- `⟨(∂_t+M)V⟩ = 0` when `⟨V⟩ = 0`. -/
theorem average_material_zero (d : ParentGeometry hT U X k) {V : VP}
    (hV : (S5.ops d).average V = 0) : (S5.ops d).average ((S5.ops d).material V) = 0 :=
  average_material_centered hT d.inverse d.strain d.covector V (PhysicalApproximationData.parentStrain_phaseIndependent (d := d))
    hV

/-- A solution of the transverse equation (5.15) has a source of zero phase mean: `f = (∂_t+M)V +
κ∂_s𝗉` with `⟨V⟩ = 0`. -/
theorem transverse_average_source (d : ParentGeometry hT U X k) {f V : VP}
    {q : HierarchyTwistedProfile T k ℝ} (hs : S5.TransverseSolution d f V q) :
    (S5.ops d).average f = 0 := by
  rw [← hs.momentum, map_add, average_material_zero d hs.mean_zero, average_phaseGrad_zero, add_zero]

/-- `⟨u.C i⟩ = 0` for the corrections of an expansion (`C_{p+1} = C[V_p]`; `C₁ = 0`). -/
theorem expansion_average_C (d : ParentGeometry hT U X k) {χ : PaperWaveCutoff t₀ T} {ℓ h : ℝ}
    {amp : ℝ → Vec3 → Vec3} {P : ℕ} {R S : VP}
    {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) {i : ℕ} (hi : i ≤ P) :
    (S5.ops d).average (u.C i) = 0 := by
  rcases Nat.eq_zero_or_pos i with rfl | hpos
  · have h0 : u.C 0 = 0 := hu.first_correction
    rw [h0, map_zero]
  · have h := hu.correction i (Finset.mem_Icc.mpr ⟨hpos, hi⟩)
    change u.C i = _ at h
    rw [h]
    exact Bridge.ops_average_curlCorrection d _

/-- `V₁ = χ̃A₁` is transverse: `κ·V₁ = 0` on the slab. -/
theorem V1_transverse (d : ParentGeometry hT U X k) (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp) {χ : PaperWaveCutoff t₀ T}
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {P : ℕ}
    {R S : VP} {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) :
    ∀ t ∈ Icc 0 T, ∀ a s, ⟪S5.waveVector X k t a, (u.V 1).val.val.val (t, a, s)⟫_ℝ = 0 := by
  have heq : u.V 1 =
      Bridge.leadingVelocityProfile hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before :=
    Lib.S5Bridge.eq_of_centeredCell fun t ht a ha s => by
      rw [hu.leading_velocity t ht a ha s, Bridge.leadingVelocityProfile_cell_eval hL hamp hℓ
        hfit hh hh₁ χ.value χ.smooth χ.zero_before ht ha s]
  rw [heq]
  exact Bridge.leadingVelocityProfile_transverse d hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
    χ.zero_before

/-- `𝗉₁ = χ̃𝗉[A₁]` has zero phase mean (`P_h` has zero mean). -/
theorem p1_phaseMean (hP : S5.Parent T U X pU D lam) (d : ParentGeometry hT U X k)
    (hL : S5.Launch T X k lam t₀)
    {amp : ℝ → Vec3 → Vec3} (hamp : S5.IsSeed U X k t₀ T center amp) {χ : PaperWaveCutoff t₀ T}
    {ℓ h : ℝ} (hℓ : 0 < ℓ) (hfit : 2 * ℓ < 1 / 2) (hh : 0 < h) (hh₁ : h ≤ 1) {P : ℕ}
    {R S : VP} {u : HierarchyProfiles VP (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) :
    ∀ t ∈ Icc 0 T, ∀ a, phaseMean (fun r => (u.p 1).val.val.val (t, a, r)) = 0 := by
  have heq : u.p 1 =
      Bridge.leadingPressureProfile hP hL hamp hℓ hfit hh hh₁ χ.value χ.smooth χ.zero_before :=
    Lib.S5Bridge.eq_of_centeredCell fun t ht a ha s => by
      rw [hu.leading_pressure t ht a ha s, Bridge.leadingPressureProfile_cell_eval hP hL hamp hℓ
        hfit hh hh₁ χ.value χ.smooth χ.zero_before ht ha s]
  intro t ht a
  rw [heq]
  have hfun : (fun r => (Bridge.leadingPressureProfile hP hL hamp hℓ hfit hh hh₁ χ.value χ.smooth
      χ.zero_before).val.val.val (t, a, r)) = phaseTwistedPeriodizeCentered k
        (fun t a s => radialEnvelope ℓ a • Bridge.pressureCore U X k h amp χ.value t a s) t a :=
    funext fun r => Bridge.leadingPressureProfile_eval hP hL hamp hℓ hfit hh hh₁ _ _ _ ht a r
  rw [hfun]
  refine Lib.S5Bridge.phaseMean_wrapped_shift k a (fun b q => ?_) (fun b => ?_)
  · simp only [Bridge.pressureCore, periodic_wavePressurePrimitive hh hh₁ q]
  · have he : (fun q => radialEnvelope ℓ b • Bridge.pressureCore U X k h amp χ.value t b q) =
        fun q => (radialEnvelope ℓ b * χ.value t * (-wavePressureCoefficient 1
          (S5.waveVector X k t b) (amp t b) (S5.strainField U X t b))) •
            wavePressurePrimitive h q := by
      funext q
      simp only [Bridge.pressureCore, smul_eq_mul]
      ring
    rw [he, phaseMean_const_smul, phaseMean_wavePressurePrimitive hh hh₁, smul_zero]

/-- **The linear term vanishes before `t₀`**: if `C` and `p` vanish at all times `< t₀`, so does
`(∂_t+M)C + 𝐝p`. -/
theorem relay_vanish_before (d : ParentGeometry hT U X k) {C : VP}
    {p : HierarchyTwistedProfile T k ℝ}
    (hC : ∀ r ∈ Icc 0 T, r < t₀ → ∀ x s, C.val.val.val (r, x, s) = 0)
    (hp : ∀ r ∈ Icc 0 T, r < t₀ → ∀ x s, p.val.val.val (r, x, s) = 0) {t : ℝ} (ht : t ∈ Icc 0 T)
    (hpre : t < t₀) (a : Vec3) (s : ℝ) :
    ((S5.ops d).material C + (S5.ops d).labelGrad p).val.val.val (t, a, s) = 0 := by
  have hx : (t, a, s) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  rw [eval_add, Bridge.ops_material_eval d C hx, ops_labelGrad_eval hT d p hx]
  have hd : HasDerivWithinAt (fun r => C.val.val.val (r, a, s)) (0 : Vec3) (Icc 0 T) t := by
    apply (hasDerivWithinAt_inter (Iio_mem_nhds hpre)).mp
    exact (hasDerivWithinAt_const t (Icc 0 T ∩ Iio t₀) (0 : Vec3)).congr
      (fun r hr => hC r hr.1 hr.2 a s) (hC t ht hpre a s)
  have hnhds : {z : HierarchyProfilePoint | z.1 < t₀} ∈ 𝓝 ((t, a, s) : HierarchyProfilePoint) :=
    continuous_fst.continuousAt.preimage_mem_nhds (Iio_mem_nhds hpre)
  have hz : HasFDerivWithinAt p.val.val.val (0 : HierarchyProfilePoint →L[ℝ] ℝ)
      (hierarchyProfileSlab T) (t, a, s) := by
    apply (hasFDerivWithinAt_inter hnhds).mp
    exact (hasFDerivWithinAt_const (0 : ℝ) ((t, a, s) : HierarchyProfilePoint)
      (hierarchyProfileSlab T ∩ {z | z.1 < t₀})).congr
      (fun z hz => hp z.1 hz.1.1 hz.2 z.2.1 z.2.2) (hp t ht hpre a s)
  rw [hd.derivWithin (uniqueDiffOn_Icc hT t ht), hz.fderivWithin (uniqueDiffOn_hierarchyProfileSlab hT _ hx),
    hC t ht hpre a s]
  simp

/-- (5.39), second line, in the unweighted norm on `[0,T]`:
`‖(f·κ)∂_s g‖_{[n]} ≤ c_n (c_n N_κ ‖f‖_{[n]}) (h⁻¹ ‖g‖_{[n+1]})`. -/
theorem uNorm_phaseAdv {ℓ h : ℝ} {γ : ℝ → ℝ} (hD_1 : Statement.lemma_D_1)
    (st : NormSetting T ℓ h t₀ γ) (d : ParentGeometry hT U X k) {NG Nk : ℕ → ℝ}
    (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) (f g : VP) :
    S5.uNorm ℓ h n ((S5.ops d).phaseAdv f g) ≤
      productConst n * (productConst n * Nk n * S5.uNorm ℓ h n f) *
        (h⁻¹ * S5.uNorm ℓ h (n + 1) g) := by
  have hg : FieldNormFinite ℓ h (n + 1)
      (weighted (fun _ : Icc 0 T => (1 : ℝ)) (Bridge.slices (Icc 0 T) g)) := by
    rw [weighted_one]; exact st.finU (n + 1) g
  have h1 := fastAdv_right hD_1 st.hℓ st.hh (γ := fun _ : Icc 0 T => (1 : ℝ)) (fun _ => one_pos)
    n (hc _ subset_rfl n).2.1 (hc _ subset_rfl n).2.2 (st.finU n f) hg
  simp only [weightedFieldNorm, weighted_one] at h1
  rw [Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm, Bridge.uNorm_eq_fieldNorm,
    slices_phaseAdv d subset_rfl]
  exact h1.2

/-- `‖(f·κ)∂_s g‖_{[n]} ≤ Λ'_n ‖f‖_{[n]} ‖g‖_{[n+1]}` on `[0,T]`, `Λ'_n = c_n² N_κ h⁻¹`. -/
theorem term_fastU {ℓ h : ℝ} {γ : ℝ → ℝ} (hD_1 : Statement.lemma_D_1)
    (st : NormSetting T ℓ h t₀ γ) (d : ParentGeometry hT U X k) {NG Nk : ℕ → ℝ}
    (hc : CoefBounds T ℓ h X k NG Nk) (n : ℕ) (f g : VP) :
    S5.uNorm ℓ h n ((S5.ops d).phaseAdv f g) ≤
      phaseConst h Nk n * (S5.uNorm ℓ h n f * S5.uNorm ℓ h (n + 1) g) := by
  refine (uNorm_phaseAdv hD_1 st d hc n f g).trans (le_of_eq ?_)
  unfold phaseConst
  ring

end Facts

end

end TorusEuler.Paper.S5b
