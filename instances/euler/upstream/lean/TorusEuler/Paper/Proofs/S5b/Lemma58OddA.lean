import TorusEuler.Paper.S5.Vocabulary
import TorusEuler.Paper.Proofs.S5Bridge.Operators
import TorusEuler.HierarchyTwistedCompletion

/-!
# Lemma 5.8, oddness of `W^♮` (part 1): the operators of §5.5 commute with the reflection

The symmetry `(a,s) ↦ (-a,-s)` of the construction of §5.5 (`sections/08_exact_wave.tex:121-123`)
acts on velocity profiles by `ϱf(t,a,s) = -f(t,-a,-s)` (`vrefl`) and on pressure profiles by
`f(t,a,s) ↦ f(t,-a,-s)` (the library `reflection`). For an odd parent the coefficient profiles
`(D_aX)⁻¹`, `M`, `κ` are even, and the operators of `S5.ops d` and the divergence correction
`C[·]` of (3.5) commute with the symmetry:

* `material_vrefl`, `labelGrad_reflection`, `phaseGrad_reflection`, `labelAdv_vrefl`,
  `phaseAdv_vrefl`, `average_vrefl`: from the library parity lemmas
  (`material_reflectionParity`, …), which hold for profiles of a fixed parity, by splitting a
  profile into its even and odd parts (`reflection_split`);
* `curlCorrection_vrefl`: `C[ϱV] = ϱC[V]` for `⟨V⟩ = 0`, directly from the formula
  `C[V] = 𝐝 × Q[V]` and the reflection identity of the phase primitive
  (`wavePotential_neg_reflected`).
-/

open Set
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.S5b

open HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3}

/-! ## Splitting into even and odd parts -/

/-- **Splitting.** An additive map `M` that agrees with `L` on reflection-even profiles and
with `-L` on reflection-odd profiles is `L ∘ reflection`. -/
theorem reflection_split {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {G : Type*} [AddCommGroup G]
    (M L : HierarchyTwistedProfile T k E → G)
    (hM : ∀ f g, M (f + g) = M f + M g) (hL : ∀ f g, L (f - g) = L f - L g)
    (hplus : ∀ f, reflection f = f → M f = L f)
    (hminus : ∀ f, reflection f = -f → M f = -L f) (f : HierarchyTwistedProfile T k E) :
    M f = L (reflection f) := by
  have hrp : reflection ((2⁻¹ : ℝ) • (f + reflection f)) = (2⁻¹ : ℝ) • (f + reflection f) := by
    rw [map_smul, map_add, reflection_involutive]
    module
  have hrm : reflection ((2⁻¹ : ℝ) • (f - reflection f)) = -((2⁻¹ : ℝ) • (f - reflection f)) := by
    rw [map_smul, map_sub, reflection_involutive]
    module
  have hf : f = (2⁻¹ : ℝ) • (f + reflection f) + (2⁻¹ : ℝ) • (f - reflection f) := by module
  have hr : reflection f = (2⁻¹ : ℝ) • (f + reflection f) - (2⁻¹ : ℝ) • (f - reflection f) := by
    module
  calc M f = M ((2⁻¹ : ℝ) • (f + reflection f)) + M ((2⁻¹ : ℝ) • (f - reflection f)) := by
        rw [← hM, ← hf]
    _ = L ((2⁻¹ : ℝ) • (f + reflection f)) - L ((2⁻¹ : ℝ) • (f - reflection f)) := by
        rw [hplus _ hrp, hminus _ hrm, ← sub_eq_add_neg]
    _ = L (reflection f) := by rw [← hL, ← hr]

/-- A reflection-even profile has parity `1`. -/
theorem parity_of_even {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} (h : reflection f = f) :
    HierarchyProfileReflectionParity 1 f.val.val.val :=
  (reflection_eq_smul_iff 1 f).mp (by rw [one_smul]; exact h)

/-- A reflection-odd profile has parity `-1`. -/
theorem parity_of_odd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} (h : reflection f = -f) :
    HierarchyProfileReflectionParity (-1) f.val.val.val :=
  (reflection_eq_smul_iff (-1) f).mp (by rw [neg_one_smul]; exact h)

/-- The reflection of a profile of parity `σ` is `σ` times the profile. -/
theorem reflection_of_parity {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f : HierarchyTwistedProfile T k E} {σ : ℝ} (h : HierarchyProfileReflectionParity σ f.val.val.val) :
    reflection f = σ • f :=
  (reflection_eq_smul_iff σ f).mpr h

/-! ## The velocity symmetry `ϱ` -/

/-- The symmetry of the construction on velocity profiles: `ϱf(t,a,s) = -f(t,-a,-s)`. -/
def vrefl : HierarchyTwistedProfile T k Vec3 →ₗ[ℝ] HierarchyTwistedProfile T k Vec3 :=
  -reflection

/-- Unfolding of the vector reflection `vrefl` (negated reflection). -/
theorem vrefl_apply (f : HierarchyTwistedProfile T k Vec3) : vrefl f = -reflection f := rfl

/-- Evaluation formula for `vrefl`. -/
@[simp] theorem vrefl_eval (f : HierarchyTwistedProfile T k Vec3) (x : HierarchyProfilePoint) :
    (vrefl f).val.val.val x = -f.val.val.val (hierarchyProfileReflection x) := rfl

/-- `vrefl` is an involution. -/
theorem vrefl_vrefl (f : HierarchyTwistedProfile T k Vec3) : vrefl (vrefl f) = f := by
  rw [vrefl_apply, vrefl_apply, map_neg, neg_neg, reflection_involutive]

/-! ## Equivariance of the operators for even coefficients -/

section Operators

variable {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} (d : ParentGeometry hT U X k)

/-- The parities of the coefficient profiles of an odd parent: `(D_aX)⁻¹`, `M`, `κ` are even. -/
structure EvenGeometry : Prop where
  inverse : HierarchyProfileReflectionParity 1 d.inverse.val.val.val
  strain : HierarchyProfileReflectionParity 1 d.strain.val.val.val
  covector : HierarchyProfileReflectionParity 1 d.covector.val.val.val

variable {d}

/-- `(∂_t + M)` commutes with the reflection. -/
theorem material_reflection (hd : EvenGeometry d) (f : HierarchyTwistedProfile T k Vec3) :
    reflection ((S5.ops d).material f) = (S5.ops d).material (reflection f) := by
  refine reflection_split (fun g => reflection ((S5.ops d).material g)) (S5.ops d).material
    (fun g g' => by simp only [map_add]) (fun g g' => map_sub _ g g') (fun g hg => ?_)
    (fun g hg => ?_) f
  · have h : HierarchyProfileReflectionParity 1 ((S5.ops d).material g).val.val.val :=
      material_reflectionParity hT d.inverse d.strain d.covector g 1 hd.strain (parity_of_even hg)
    rw [reflection_of_parity h, one_smul]
  · have h : HierarchyProfileReflectionParity (-1) ((S5.ops d).material g).val.val.val :=
      material_reflectionParity hT d.inverse d.strain d.covector g (-1) hd.strain
        (parity_of_odd hg)
    rw [reflection_of_parity h, neg_one_smul]

/-- `(∂_t + M)ϱf = ϱ(∂_t + M)f`. -/
theorem material_vrefl (hd : EvenGeometry d) (f : HierarchyTwistedProfile T k Vec3) :
    (S5.ops d).material (vrefl f) = vrefl ((S5.ops d).material f) := by
  rw [vrefl_apply, vrefl_apply, map_neg, material_reflection hd]

/-- `𝐝(q ∘ reflection) = ϱ 𝐝q`. -/
theorem labelGrad_reflection (hd : EvenGeometry d) (q : HierarchyTwistedProfile T k ℝ) :
    (S5.ops d).labelGrad (reflection q) = vrefl ((S5.ops d).labelGrad q) := by
  refine (reflection_split (fun g => -reflection ((S5.ops d).labelGrad g)) (S5.ops d).labelGrad
    (fun g g' => by simp only [map_add, neg_add]) (fun g g' => map_sub _ g g') (fun g hg => ?_)
    (fun g hg => ?_) q).symm
  · have h : HierarchyProfileReflectionParity (-1) ((S5.ops d).labelGrad g).val.val.val :=
      labelGrad_reflectionParity hT d.inverse d.strain d.covector g 1 hd.inverse (parity_of_even hg)
    rw [reflection_of_parity h, neg_one_smul, neg_neg]
  · have h : HierarchyProfileReflectionParity (-(-1)) ((S5.ops d).labelGrad g).val.val.val :=
      labelGrad_reflectionParity hT d.inverse d.strain d.covector g (-1) hd.inverse
        (parity_of_odd hg)
    rw [reflection_of_parity h, neg_neg, one_smul]

/-- `κ∂_s(q ∘ reflection) = ϱ κ∂_s q`. -/
theorem phaseGrad_reflection (hd : EvenGeometry d) (q : HierarchyTwistedProfile T k ℝ) :
    (S5.ops d).phaseGrad (reflection q) = vrefl ((S5.ops d).phaseGrad q) := by
  refine (reflection_split (fun g => -reflection ((S5.ops d).phaseGrad g)) (S5.ops d).phaseGrad
    (fun g g' => by simp only [map_add, neg_add]) (fun g g' => map_sub _ g g') (fun g hg => ?_)
    (fun g hg => ?_) q).symm
  · have h : HierarchyProfileReflectionParity (-1) ((S5.ops d).phaseGrad g).val.val.val :=
      phaseGrad_reflectionParity hT d.inverse d.strain d.covector g 1 hd.covector
        (parity_of_even hg)
    rw [reflection_of_parity h, neg_one_smul, neg_neg]
  · have h : HierarchyProfileReflectionParity (-(-1)) ((S5.ops d).phaseGrad g).val.val.val :=
      phaseGrad_reflectionParity hT d.inverse d.strain d.covector g (-1) hd.covector
        (parity_of_odd hg)
    rw [reflection_of_parity h, neg_neg, one_smul]

/-- The splitting argument for a bilinear map, over an abstract module with an involution `r`:
if `r(B f g) = -σ(f)σ(g) B f g` whenever `r f = σ(f) f`, `r g = σ(g) g` with `σ = ±1`, then
`r(B f g) = -B(r f)(r g)`. -/
theorem bilinear_abstract {V : Type*} [AddCommGroup V] [Module ℝ V] (r : V →ₗ[ℝ] V)
    (hr : ∀ f, r (r f) = f) (B : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (hB : ∀ (f g : V) (sF sG : ℝ), r f = sF • f → r g = sG • g →
      r (B f g) = (-(sF * sG)) • B f g)
    (f g : V) : r (B f g) = -B (r f) (r g) := by
  have hsplit (x : V) : ∃ xp xm : V, r xp = (1 : ℝ) • xp ∧ r xm = (-1 : ℝ) • xm ∧
      x = xp + xm ∧ r x = xp - xm := by
    refine ⟨(2⁻¹ : ℝ) • (x + r x), (2⁻¹ : ℝ) • (x - r x), ?_, ?_, by module, by module⟩
    · rw [map_smul, map_add, hr]; module
    · rw [map_smul, map_sub, hr]; module
  obtain ⟨fp, fm, hfp, hfm, hf, hrf⟩ := hsplit f
  obtain ⟨gp, gm, hgp, hgm, hg, hrg⟩ := hsplit g
  have e1 := hB fp gp 1 1 hfp hgp
  have e2 := hB fp gm 1 (-1) hfp hgm
  have e3 := hB fm gp (-1) 1 hfm hgp
  have e4 := hB fm gm (-1) (-1) hfm hgm
  calc r (B f g) = r (B fp gp) + r (B fp gm) + (r (B fm gp) + r (B fm gm)) := by
        rw [hf, hg]; simp only [map_add, LinearMap.add_apply]; abel
    _ = -B (fp - fm) (gp - gm) := by
        rw [e1, e2, e3, e4]; simp only [map_sub, LinearMap.sub_apply]; module
    _ = -B (r f) (r g) := by rw [hrf, hrg]

/-- A bilinear map is even under `(f,g) ↦ (-f,-g)`. -/
theorem bilinear_neg_neg {V : Type*} [AddCommGroup V] [Module ℝ V] (B : V →ₗ[ℝ] V →ₗ[ℝ] V)
    (x y : V) : B (-x) (-y) = B x y := by
  simp only [map_neg, LinearMap.neg_apply, neg_neg]

set_option maxHeartbeats 1000000 in
/-- `(ϱZ·𝐝)ϱZ' = ϱ((Z·𝐝)Z')`. -/
theorem labelAdv_vrefl (hd : EvenGeometry d) (f g : HierarchyTwistedProfile T k Vec3) :
    (S5.ops d).labelAdv (vrefl f) (vrefl g) = vrefl ((S5.ops d).labelAdv f g) := by
  have h := bilinear_abstract (V := HierarchyTwistedProfile T k Vec3) reflection
    reflection_involutive (S5.ops d).labelAdv
    (fun f g sF sG hf hg => reflection_of_parity
      (labelAdv_reflectionParity hT d.inverse d.strain d.covector f g sF sG hd.inverse
        ((reflection_eq_smul_iff sF f).mp hf) ((reflection_eq_smul_iff sG g).mp hg))) f g
  rw [vrefl_apply, vrefl_apply, vrefl_apply, bilinear_neg_neg, h, neg_neg]

set_option maxHeartbeats 1000000 in
/-- `(ϱZ·κ)∂_sϱY = ϱ((Z·κ)∂_sY)`. -/
theorem phaseAdv_vrefl (hd : EvenGeometry d) (f g : HierarchyTwistedProfile T k Vec3) :
    (S5.ops d).phaseAdv (vrefl f) (vrefl g) = vrefl ((S5.ops d).phaseAdv f g) := by
  have h := bilinear_abstract (V := HierarchyTwistedProfile T k Vec3) reflection
    reflection_involutive (S5.ops d).phaseAdv
    (fun f g sF sG hf hg => reflection_of_parity
      (phaseAdv_reflectionParity hT d.inverse d.strain d.covector f g sF sG hd.covector
        ((reflection_eq_smul_iff sF f).mp hf) ((reflection_eq_smul_iff sG g).mp hg))) f g
  rw [vrefl_apply, vrefl_apply, vrefl_apply, bilinear_neg_neg, h, neg_neg]

/-- The phase average commutes with the reflection. -/
theorem average_reflection (f : HierarchyTwistedProfile T k Vec3) :
    reflection ((S5.ops d).average f) = (S5.ops d).average (reflection f) := by
  refine reflection_split (fun g => reflection ((S5.ops d).average g)) (S5.ops d).average
    (fun g g' => by simp only [map_add]) (fun g g' => map_sub _ g g') (fun g hg => ?_)
    (fun g hg => ?_) f
  · have h : HierarchyProfileReflectionParity 1 ((S5.ops d).average g).val.val.val :=
      average_reflectionParity hT g 1 (parity_of_even hg)
    rw [reflection_of_parity h, one_smul]
  · have h : HierarchyProfileReflectionParity (-1) ((S5.ops d).average g).val.val.val :=
      average_reflectionParity hT g (-1) (parity_of_odd hg)
    rw [reflection_of_parity h, neg_one_smul]

/-- `⟨ϱf⟩ = ϱ⟨f⟩`. -/
theorem average_vrefl (f : HierarchyTwistedProfile T k Vec3) :
    (S5.ops d).average (vrefl f) = vrefl ((S5.ops d).average f) := by
  rw [vrefl_apply, vrefl_apply, map_neg, average_reflection]

/-- The derivative of `b ↦ f(-b)` (no differentiability needed). -/
theorem fderiv_comp_neg' {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (f : Vec3 → F)
    (a : Vec3) : fderiv ℝ (fun b => f (-b)) a = -fderiv ℝ f (-a) := by
  let N : Vec3 ≃L[ℝ] Vec3 := (LinearIsometryEquiv.neg ℝ : Vec3 ≃ₗᵢ[ℝ] Vec3).toContinuousLinearEquiv
  have h := N.comp_right_fderiv (f := f) (x := a)
  change fderiv ℝ (f ∘ N) a = _
  rw [h]
  ext v
  change fderiv ℝ f (-a) (-v) = -(fderiv ℝ f (-a) v)
  rw [map_neg]

/-! ## The divergence correction -/

/-- The phase slices of a twisted profile are continuous. -/
theorem continuous_phase_slice' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : HierarchyTwistedProfile T k E) {t : ℝ} (ht : t ∈ Icc 0 T) (a : Vec3) :
    Continuous (fun s => f.val.val.val (t, a, s)) :=
  (HierarchySmoothProfile.contDiff_labelPhase_slice f.val.val ht).continuous.comp
    (continuous_const.prodMk continuous_id)

set_option maxHeartbeats 1000000 in
/-- **`C[ϱV] = ϱC[V]`** for `⟨V⟩ = 0` (even coframe and wave vector): the phase primitive of
`-V(t,-a,-s)` is `Q[V](t,-a,-s)` (`wavePotential_neg_reflected`), and the slow curl of a
reflected potential is minus the reflected slow curl. -/
theorem curlCorrection_vrefl (hd : EvenGeometry d) (V : HierarchyTwistedProfile T k Vec3)
    (hV : (S5.ops d).average V = 0) :
    S5.curlCorrection d (vrefl V) = vrefl (S5.curlCorrection d V) := by
  have hVr : (S5.ops d).average (vrefl V) = 0 := by rw [average_vrefl, hV, map_zero]
  have hκ := d.oscillation.covector_ne_zero
  have hcV := complete_val_val_of_phaseMean_zero hT d.inverse d.covector
    d.oscillation.covector_independent hκ V hV
  have hcVr := complete_val_val_of_phaseMean_zero hT d.inverse d.covector
    d.oscillation.covector_independent hκ (vrefl V) hVr
  apply HierarchyTwistedProfile.ext
  rintro ⟨t, a, s⟩ hx
  have ht : t ∈ Icc 0 T := hx.1
  rw [vrefl_eval]
  change (complete hT d.inverse d.covector _ hκ (vrefl V)).val.val.val (t, a, s) =
    -(complete hT d.inverse d.covector _ hκ V).val.val.val (hierarchyProfileReflection (t, a, s))
  rw [hcV, hcVr]
  simp only [hierarchyProfileReflection_apply, HierarchySmoothProfile.profileCompletion]
  rw [HierarchySmoothProfile.profileSlowCurl_apply hT _ _ ht,
    HierarchySmoothProfile.profileSlowCurl_apply hT _ _ ht]
  -- the potential of the reflected field is the reflected potential
  have hmean (b : Vec3) : phaseMean (fun r => V.val.val.val (t, b, r)) = 0 := by
    have hb : (t, b, (0 : ℝ)) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
    rw [← Bridge.ops_average_eval d V hb, hV]
    rfl
  have hQ : (fun b => (HierarchySmoothProfile.profileWavePotential hT d.covector.val.val hκ
        (vrefl V).val.val).val (t, b, s)) =
      fun b => (HierarchySmoothProfile.profileWavePotential hT d.covector.val.val hκ
        V.val.val).val (t, -b, -s) := by
    funext b
    rw [HierarchySmoothProfile.profileWavePotential_apply hT _ hκ _ ht,
      HierarchySmoothProfile.profileWavePotential_apply hT _ hκ _ ht]
    have hk : d.covector.val.val.val (t, b, 0) = d.covector.val.val.val (t, -b, 0) := by
      have := hd.covector (t, b, 0)
      simp only [hierarchyProfileReflection_apply, neg_zero, one_smul] at this
      exact this.symm
    have hfun : (fun σ => (vrefl V).val.val.val (t, b, σ)) =
        fun σ => -V.val.val.val (t, -b, -σ) := by
      funext σ
      simp only [vrefl_eval, hierarchyProfileReflection_apply]
    change wavePotential (d.covector.val.val.val (t, b, 0)) (fun σ => (vrefl V).val.val.val (t, b, σ)) s =
      wavePotential (d.covector.val.val.val (t, -b, 0)) (fun σ => V.val.val.val (t, -b, σ)) (-s)
    rw [hk, hfun, wavePotential_neg_reflected _ (continuous_phase_slice' V ht (-b))
      (HierarchyPeriodicProfile.phasePeriodic V.val t (-b)) (hmean (-b))]
  rw [hQ]
  have hG : d.inverse.val.val.val (t, a, s) = d.inverse.val.val.val (t, -a, -s) := by
    have := hd.inverse (t, a, s)
    simp only [hierarchyProfileReflection_apply, one_smul] at this
    exact this.symm
  change curlOfDerivative ((fderiv ℝ (fun b => (HierarchySmoothProfile.profileWavePotential hT
      d.covector.val.val hκ V.val.val).val (t, -b, -s)) a).comp (d.inverse.val.val.val (t, a, s))) =
    -curlOfDerivative ((fderiv ℝ (fun b => (HierarchySmoothProfile.profileWavePotential hT
      d.covector.val.val hκ V.val.val).val (t, b, -s)) (-a)).comp
        (d.inverse.val.val.val (t, -a, -s)))
  rw [hG, fderiv_comp_neg' (fun b => (HierarchySmoothProfile.profileWavePotential hT
      d.covector.val.val hκ V.val.val).val (t, b, -s)), ContinuousLinearMap.neg_comp]
  change curlOfDerivativeCLM (-_) = -curlOfDerivativeCLM _
  rw [map_neg]

end Operators

end

end TorusEuler.Paper.S5b
