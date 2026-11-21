import TorusEuler.Paper.Proofs.S5a.Lemma55Main
import TorusEuler.Paper.Proofs.S5a.Library.Leading
import TorusEuler.Paper.Proofs.S5Bridge.Seed

/-!
# Proof of Lemma 5.5 from Proposition 5.1 and Lemma D.1

The estimates (5.31), (5.32) are `Lib.S5a.lemma55_main`. The last clause ("for the leading
oscillation `V = A₁` on `[t₀,T]` the source in this estimate is `f = 0`",
`sections/06c_finite_hierarchy.tex:412-413`) represents `A₁`, `𝗉[A₁]` by twisted profiles
(`Lib.S5a.exists_leading_representatives`), checks (3.4) for them on `[t₀,T]`
(`Lib.S5a.leading_homogeneous`) and applies (5.32) with `f = 0`.
-/

open Set Function
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

open HierarchyTwistedProfile LocalizedAmplitude

namespace Lib.S5a

/-- The weighted norm of the zero profile vanishes. -/
theorem wNorm_zero {T : ℝ} {k : Vec3} {ℓ h t₀ : ℝ} {γ : ℝ → ℝ} (n : ℕ) :
    S5.wNorm ℓ h t₀ γ n (0 : HierarchyTwistedProfile T k Vec3) = 0 := by
  have hz (w : List (Fin 4)) :
      phaseOperatorWord (hierarchyMixedDirection ℓ h) w (fun _ : Vec3 × ℝ => (0 : Vec3)) =
        fun _ => 0 := by
    induction w with
    | nil => rfl
    | cons i w ih =>
      funext x
      simp only [phaseOperatorWord, phaseDirectionalDerivative, ih]
      simp
  unfold S5.wNorm S5.fieldNorm hierarchyFiniteWordNorm
  refine Finset.sum_eq_zero fun w _ => ?_
  have hf : (fun (t : Icc t₀ T) (x : Vec3 × ℝ) =>
      (γ t)⁻¹ • (0 : HierarchyTwistedProfile T k Vec3).val.val.val (t, x)) = fun _ _ => 0 := by
    funext t x
    exact smul_zero _
  rw [hf]
  have hs : hierarchyJetValues False (hierarchyMixedDirection ℓ h) w
      (fun (_ : Icc t₀ T) (_ : Vec3 × ℝ) => (0 : Vec3)) = {0} := by
    ext r
    simp only [hierarchyJetValues, hz, norm_zero, false_and, or_false, Set.mem_singleton_iff]
    constructor
    · rintro (hr | ⟨_, _, hr⟩)
      · exact hr
      · exact hr.symm
    · exact Or.inl
  rw [hs, csSup_singleton]

end Lib.S5a

set_option maxHeartbeats 8000000 in
/-- Proof of **Lemma 5.5** (`cc:uf:hier:lem:relay`), following
`sections/06c_finite_hierarchy.tex:415-447`.

* `h5_1` (Proposition 5.1) enters through its bound (5.8) for the coefficients
  `(D_aX)⁻¹`, `M`, `κ/λ`, `λ²/|κ|²` (TeX line 422, "(5.8) give (5.31)"), in
  `Lib.S5a.lemma55_main`; the envelope exponent is `a₀ = max(C_{5.1}, 3)`, so that
  `ℓ_* ≤ 𝖣^{-C}` as (5.8) requires and `2ℓ_* < 1/2`.
* `hD_1` (Lemma D.1) enters through the product rule (D.4) for every product of these
  coefficients with fixed maps and `ℓ_*⁻¹` (TeX lines 420-421; `Lib.S5a.relayBudget`) and
  through the primitive estimate (D.5) for `∂_s^{-1}` in `Q[V]` and in (5.33) (TeX lines 417,
  444-445; `Lib.S5a.relayWordBound_phasePrimitive_of_D1`), in `Lib.S5a.lemma55_main`.
* The leading clause (TeX lines 412-413) uses the seed equation (3.2) through
  `Lib.S5a.leading_homogeneous` and then (5.32) with `f = 0`.

Equations: (5.31), (5.32), (5.33), (3.4), (3.5), (5.8), (D.3)–(D.5). -/
theorem Proof.lemma_5_5_of (h5_1 : Statement.proposition_5_1) (hD_1 : Statement.lemma_D_1) :
    Statement.lemma_5_5 := by
  obtain ⟨a₀, hmain⟩ := Lib.S5a.lemma55_main h5_1 hD_1
  refine ⟨max a₀ 3, fun a ha => ?_⟩
  obtain ⟨C, K, hCK⟩ := hmain a (le_of_max_le_left ha)
  refine ⟨C, K, ?_⟩
  intro T hT U X pU k D lam t₀ center d hP hL hO ℓ h γ A κ
  have hM := hCK hT d hP hL hO
  refine ⟨fun n V hV htrans => hM n V hV htrans, fun amp hamp => ?_⟩
  have hℓ : 0 < ℓ := Bridge.radius_pos hP a
  have hfit : 2 * ℓ < 1 / 2 := Bridge.radius_fits hP.scale_ge_two (le_of_max_le_right ha)
  have hh : 0 < h := Bridge.width_pos hP
  have hh₁ : h ≤ 1 := Bridge.width_le_one hP
  have hI : Icc t₀ T ⊆ Icc 0 T := Bridge.Launch.active_subset hL
  obtain ⟨V, p, hVmean, hpMean, hEval⟩ :=
    Lib.S5a.exists_leading_representatives hP hL hamp hℓ hfit hh hh₁
  -- the values of the representatives on the label cell are `A₁`, `𝗉[A₁]`
  have hV (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (hx : x ∈ centeredCell) (s : ℝ) :
      V.val.val.val (t, x, s) = S5.leading ℓ h amp t x s := by
    rw [(hEval t ht x s).1]
    apply Lib.S5a.wrapped_eq_on_cell hx s hfit
    intro b hb q
    simp only [S5.leading, radialEnvelope_eq_zero hℓ hb, zero_mul, zero_smul]
  have hp (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (hx : x ∈ centeredCell) (s : ℝ) :
      p.val.val.val (t, x, s) = S5.leadingPressure U X k ℓ h amp t x s := by
    rw [(hEval t ht x s).2]
    apply Lib.S5a.wrapped_eq_on_cell hx s hfit
    intro b hb q
    simp only [S5.leadingPressure, wavePressureCoefficient, radialEnvelope_eq_zero hℓ hb,
      mul_zero, zero_mul, zero_div, neg_zero]
  -- (3.4) and transversality on the label cell, from the seed equation
  let R := A.material V + A.phaseGrad p
  have hCell (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (hx : x ∈ centeredCell) (s : ℝ) :
      ⟪d.covector.val.val.val (t, x, s), V.val.val.val (t, x, s)⟫_ℝ = 0 ∧
        R.val.val.val (t, x, s) = 0 := by
    have hz : (t, x, s) ∈ hierarchyProfileSlab T := ⟨hI ht, mem_univ _⟩
    have hlead := Lib.S5a.leading_homogeneous (ℓ := ℓ) hamp hL.start_lt hh hh₁ ht x s
    constructor
    · rw [d.covector_value _ hz, hV t ht x hx s]
      exact hlead.2.1
    · have hQ : (fun q => p.val.val.val (t, x, q)) = S5.leadingPressure U X k ℓ h amp t x :=
        funext (hp t ht x hx)
      have hv₀ := (HierarchySmoothProfile.hasDerivWithinAt_profileTime V.val.val (hI ht) x s).mono hI
      have hv := hv₀.derivWithin (uniqueDiffOn_Icc hL.start_lt t ht)
      have hVFun : EqOn (fun u => V.val.val.val (u, x, s)) (fun u => S5.leading ℓ h amp u x s)
          (Icc t₀ T) := fun u hu => hV u hu x hx s
      rw [derivWithin_congr hVFun (hVFun ht)] at hv
      have hp' := (HierarchySmoothProfile.hasDerivAt_profilePhase p.val.val (hI ht) x s).deriv
      rw [hQ] at hp'
      let ops := HierarchySmoothProfile.hierarchyConcreteOperators hT d.inverse.val.val
        d.strain.val.val d.covector.val.val
      change (ops.material V.val.val).val (t, x, s) +
        (HierarchySmoothProfile.phaseGradient hT d.covector.val.val p.val.val).val (t, x, s) = 0
      rw [HierarchySmoothProfile.hierarchyConcreteOperators_material_apply hT _ _ _ _ hz,
        HierarchySmoothProfile.phaseGradient_apply hT _ _ hz, ← hv, ← hp',
        d.covector_value _ hz, d.strain_value _ hz, hV t ht x hx s]
      exact hlead.1
  -- and at every label, by the lattice twist
  have hAll (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (s : ℝ) :
      ⟪d.covector.val.val.val (t, x, s), V.val.val.val (t, x, s)⟫_ℝ = 0 ∧
        R.val.val.val (t, x, s) = 0 := by
    obtain ⟨m, hm⟩ := exists_sub_latticeVector_mem_centeredCell x
    have hShift {Y : Type} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
        (f : HierarchyTwistedProfile T k Y) : f.val.val.val (t, x, s) =
        f.val.val.val (t, x - latticeVector m, s - ⟪k, latticeVector m⟫_ℝ) := by
      simpa only [sub_add_cancel] using
        twistedSlice f t (x - latticeVector m) (s - ⟪k, latticeVector m⟫_ℝ) m
    rw [hShift d.covector, hShift V, hShift R]
    exact hCell t ht _ hm _
  have hTrans (t : ℝ) (ht : t ∈ Icc t₀ T) (x : Vec3) (s : ℝ) :
      ⟪κ t x, V.val.val.val (t, x, s)⟫_ℝ = 0 := by
    have hc := d.oscillation.covector_independent (t, x, 0) ⟨hI ht, mem_univ _⟩ s
    change d.covector.val.val.val (t, x, s) = d.covector.val.val.val (t, x, 0) at hc
    have h0 := (hAll t ht x s).1
    rw [hc, d.covector_value (t, x, 0) ⟨hI ht, mem_univ _⟩] at h0
    exact h0
  have hAvg : A.average V = 0 := hVmean
  have hpM : ∀ t ∈ Icc t₀ T, ∀ x, phaseMean (fun s => p.val.val.val (t, x, s)) = 0 :=
    fun t ht x => hpMean t (hI ht) x
  refine ⟨V, p, fun t ht x hx s => ⟨hV t ht x hx s, hp t ht x hx s⟩, hAvg, hTrans, hpM,
    fun t ht x s => (hAll t ht x s).2, fun n => ?_⟩
  -- (5.32) with the source `f = 0`
  have h0 : A.average (0 : HierarchyTwistedProfile T k Vec3) = 0 := map_zero _
  have hb := (hM n V hAvg hTrans).2 0 p h0 hpM (fun t ht x s => by
    rw [(hAll t ht x s).2]
    rfl)
  rw [Lib.S5a.wNorm_zero, add_zero] at hb
  exact hb

end

end TorusEuler.Paper
