import TorusEuler.Paper.Proofs.S5a.Library.Leading
import TorusEuler.Paper.Proofs.S5Bridge.Leading

/-!
# S5a library: the leading switch of Proposition 5.4

For an expansion of Proposition 5.4 the first level is `V₁ = χ̃A₁`, `𝗉₁ = χ̃𝗉[A₁]` on the label cell
and `S = χ̃'A₁` (3.7), (3.8). `leadingSwitch` proves
`(∂_t + M)V₁ + κ∂_s𝗉₁ = S` (`sections/06c_finite_hierarchy.tex:355-358`): by the product rule it is
`χ̃'A₁ + χ̃ ((∂_t+M)A₁ + κ∂_s𝗉[A₁])`, and the bracket vanishes on `[t₀,T]` by the leading
equation (3.4) (the seed equation (3.2); glue, ledger decision D6); before `t₀` all terms vanish.
-/

open Set Filter
open scoped ContDiff InnerProductSpace Topology

namespace TorusEuler.Paper.Lib.S5a

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

variable {T : ℝ} {hT : 0 < T} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {k : Vec3}
  {D lam t₀ : ℝ} {center : ℝ → Vec3} {amp : ℝ → Vec3 → Vec3}

/-- The time derivative of the leading oscillation `A₁` of a seed on `[t₀,T]`: by the seed
equation (3.2), `∂_tA₁ = -MA₁ - ∂_s𝗉[A₁] κ` (the step of `leading_homogeneous`, kept as a
derivative statement). -/
theorem hasDerivWithinAt_leading (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hh : 0 < h)
    (hh₁ : h ≤ 1) {t : ℝ} (ht : t ∈ Icc t₀ T) (a : Vec3) (s : ℝ) :
    HasDerivWithinAt (fun u => S5.leading ℓ h amp u a s)
      (-S5.strainField U X t a (S5.leading ℓ h amp t a s) -
        deriv (S5.leadingPressure U X k ℓ h amp t a) s • S5.waveVector X k t a) (Icc t₀ T) t := by
  let c := radialEnvelope ℓ a * waveProfile h s
  have hAmp := (hamp.equation a t ht).const_smul c
  have hOp := affineWaveAmplitudeOperator_add_transverseProjection (S5.strainField U X t a)
    (S5.waveVector X k t a) 0 (amp t a)
  simp only [map_zero, add_zero, zero_sub] at hOp
  apply hAmp.congr_deriv
  rw [hOp, deriv_leadingPressure hh hh₁]
  simp only [c, S5.leading, map_smul, smul_sub, smul_neg, smul_smul]

set_option maxHeartbeats 1600000 in
/-- **The leading switch** `(∂_t + M)V₁ + κ∂_s𝗉₁ = χ̃'A₁` of an expansion
(`06c_finite_hierarchy.tex:355-358`, from (3.4) and (3.7)). -/
theorem leadingSwitch {hT : 0 < T} (d : ParentGeometry hT U X k) (hL : S5.Launch T X k lam t₀)
    (hamp : S5.IsSeed U X k t₀ T center amp) {ℓ h : ℝ} (hh : 0 < h) (hh₁ : h ≤ 1)
    {χ : PaperWaveCutoff t₀ T} {P : ℕ} {R S : HierarchyTwistedProfile T k Vec3}
    {u : HierarchyProfiles (HierarchyTwistedProfile T k Vec3) (HierarchyTwistedProfile T k ℝ)}
    (hu : S5.IsExpansion d pU χ ℓ h amp P R S u) :
    (S5.ops d).material (u.V 1) + (S5.ops d).phaseGrad (u.p 1) = S := by
  refine Lib.S5Bridge.eq_of_centeredCell fun t ht a ha s => ?_
  have hx : ((t, a, s) : HierarchyProfilePoint) ∈ hierarchyProfileSlab T := ⟨ht, mem_univ _⟩
  have hsub : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  have hI : t₀ < T := hL.start_lt
  change ((S5.ops d).material (u.V 1)).val.val.val (t, a, s) +
    ((S5.ops d).phaseGrad (u.p 1)).val.val.val (t, a, s) = S.val.val.val (t, a, s)
  rw [Bridge.ops_material_eval d _ hx, Bridge.ops_phaseGrad_eval d _ hx, hu.activation t ht a ha s]
  have hV : ∀ r ∈ Icc 0 T, (u.V 1).val.val.val (r, a, s) = χ.value r • S5.leading ℓ h amp r a s :=
    fun r hr => hu.leading_velocity r hr a ha s
  have hpz : (fun z => (u.p 1).val.val.val (t, a, z)) =
      fun z => χ.value t * S5.leadingPressure U X k ℓ h amp t a z :=
    funext fun z => hu.leading_pressure t ht a ha z
  change derivWithin (fun r => (u.V 1).val.val.val (r, a, s)) (Icc 0 T) t +
      S5.strainField U X t a ((u.V 1).val.val.val (t, a, s)) +
      deriv (fun z => (u.p 1).val.val.val (t, a, z)) s • S5.waveVector X k t a =
    χ.derivative t • S5.leading ℓ h amp t a s
  rw [hpz, deriv_const_mul_field', hV t ht]
  rcases lt_or_ge t t₀ with hlt | hge
  · have hχ0 : χ.value t = 0 := χ.zero_before t ht hlt
    have hχ' : χ.derivative t = 0 := χ.derivative_zero_before (Bridge.Launch.end_pos hL) ht hlt
    have hmem : Iio t₀ ∩ Icc 0 T ∈ 𝓝[Icc 0 T] t :=
      mem_nhdsWithin.mpr ⟨Iio t₀, isOpen_Iio, hlt, subset_rfl⟩
    have hev : (fun r => (u.V 1).val.val.val (r, a, s)) =ᶠ[𝓝[Icc 0 T] t] fun _ => (0 : Vec3) := by
      filter_upwards [hmem] with r hr
      simp only [hV r hr.2, χ.zero_before r hr.2 hr.1, zero_smul]
    have hd : derivWithin (fun r => (u.V 1).val.val.val (r, a, s)) (Icc 0 T) t = 0 :=
      ((hasDerivWithinAt_const t (Icc 0 T) (0 : Vec3)).congr_of_eventuallyEq hev
        (by rw [hV t ht, hχ0, zero_smul])).derivWithin (uniqueDiffOn_Icc hT t ht)
    rw [hd, hχ0, hχ']
    simp
  · have ht0 : t ∈ Icc t₀ T := ⟨hge, ht.2⟩
    have hA := hasDerivWithinAt_leading (ℓ := ℓ) hamp hh hh₁ ht0 a s
    have hχd : HasDerivWithinAt χ.value (χ.derivative t) (Icc t₀ T) t :=
      ((χ.smooth.differentiableOn (by simp) t ht).hasDerivWithinAt).mono hsub
    have hprod := hχd.smul hA
    have hdiff : DifferentiableWithinAt ℝ (fun r => (u.V 1).val.val.val (r, a, s)) (Icc 0 T) t :=
      (((HierarchySmoothProfile.smooth (u.V 1).val.val).comp
        (contDiffOn_id.prodMk (contDiffOn_const.prodMk contDiffOn_const))
        (fun r hr => ⟨hr, mem_univ _⟩)).differentiableOn (by simp)) t ht
    have h2 := hdiff.hasDerivWithinAt.mono hsub
    have h3 := hprod.congr (fun r hr => hV r (hsub hr)) (hV t ht)
    rw [UniqueDiffWithinAt.eq_deriv _ (uniqueDiffOn_Icc hI t ht0) h2 h3, map_smul]
    module

end

end TorusEuler.Paper.Lib.S5a
