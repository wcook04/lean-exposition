import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.SBD.Library.Fields

/-! # Proof of Lemma D.1 (derivatives, products and phase operators in the finite norms)

Conditional proof `Paper.Proof.lemma_D_1` of `Paper.Statement.lemma_D_1`
(`cc:uf:trunc:lem:fields`, sections/appD_finite_norms.tex:42-79 of the latest
manuscript). Lemma D.1 is a leaf of the proof spine: its TeX proof cites no
other numbered result, so the Lean proof has no hypotheses. In particular it
does not use display (D.2) (`Statement.Text.eq_D_2`, whose content is
`paperAppendixD_holderComparison`): the half-Hölder product estimate comes
from the product inequality in `C^{0,1/2}` directly. -/

open MeasureTheory Set
open scoped ContDiff Pointwise

namespace TorusEuler.Paper

open AppendixD Lib.SBD

/-- Proof of **Lemma D.1** (`cc:uf:trunc:lem:fields`), following
sections/appD_finite_norms.tex:66-78. The TeX proof cites no numbered result,
so this leaf has no hypotheses. The weighted norm (D.1) `‖f‖_{[n],γ}` is the
norm of `f/γ`; since `γ` depends only on time, every label or phase derivative
commutes with the division by `γ`, so each weighted estimate is the
unweighted estimate applied to `f/γ`.

* appD:67-69, (D.3) `cc:uf:trunc:eq:deriv`: each label derivative of order
  `m + 1` occurs at most three times in the sum over `i`, and the phase
  derivative shifts `j` by one: `paperLemmaD1_derivatives` (own content of
  D.1) applied to `f/γ`, after `∂(f/γ) = (∂f)/γ`. Finiteness of the left
  sides: `Lib.SBD.jetValues_bdd_dirDeriv` (from
  `hierarchyFiniteWordNorm_constDerivative_le`, own content of D.1).
* appD:69-71, (D.4) `cc:uf:trunc:eq:product`: Leibniz' rule for `f (g/γ)`,
  using that `γ` depends only on time: `paperLemmaD1_product` with
  `holder = False` (own content of D.1); finiteness from
  `Lib.SBD.hierarchyJetValues_bdd_bilinear'`.
* appD:71-72, Hölder version (`γ ≡ 1`): the product inequality in
  `C^{0,1/2}`, `paperLemmaD1_product` with `holder = True` in the label
  directions.
* appD:74-78, (D.5) `cc:uf:trunc:eq:phase-ops`: phase averaging has supremum
  norm at most one and commutes with the derivatives
  (`paperLemmaD1_phaseAverage`, own content of D.1, applied to `f/γ`, with
  `⟨f/γ⟩ = ⟨f⟩/γ`; finiteness by `Lib.SBD.phaseAverage_jetValues_bdd` and,
  for `f − ⟨f⟩`, `Lib.SBD.jetValues_bdd_add`); the zero-mean periodic
  primitive has supremum at most `2 sup |f|` and commutes with the derivatives
  (`hierarchyFiniteWordNorm_phasePrimitive_le`, own content of D.1, applied to
  `f/γ`, with `∂_s^{-1}(f/γ) = (∂_s^{-1} f)/γ`). -/
theorem Proof.lemma_D_1 : Statement.lemma_D_1 := by
  intro I ℓ h hℓ hh γ hγ n
  have hsm {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : I → Vec3 × ℝ → E}
      (hf : ∀ t, ContDiff ℝ ∞ (weighted γ f t)) (t : I) : ContDiff ℝ ∞ (f t) := by
    have := (hf t).const_smul (γ t)
    convert this using 1
    funext x
    simp [weighted, smul_smul, mul_inv_cancel₀ (hγ t).ne']
  have hMixed : ∀ i, ContDiff ℝ ∞ (hierarchyMixedDirection ℓ h i) := fun i => contDiff_const
  -- the mixed directions as weighted constant directions
  let q (i : Fin 4) : Vec3 × ℝ := Fin.lastCases (phaseCoordinateDirection (.inr ()))
    (fun j => phaseCoordinateDirection (.inl j)) i
  let sw (i : Fin 4) : ℝ := Fin.lastCases h (fun _ : Fin 3 => ℓ) i
  have hQ : (fun j (_ : Vec3 × ℝ) => sw j • q j) = hierarchyMixedDirection ℓ h := by
    funext j x
    refine Fin.lastCases (motive := fun i => sw i • q i = hierarchyMixedDirection ℓ h i x)
      ?_ (fun i => ?_) j
    · simp only [q, sw, hierarchyMixedDirection, Fin.lastCases_last]
    · simp only [q, sw, hierarchyMixedDirection, Fin.lastCases_castSucc]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (D.3)
    intro E _ _ f hf
    have hcomm (v : Vec3 × ℝ) :
        weighted γ (fun t => phaseDirectionalDerivative (fun _ => v) (f t)) =
          fun t => phaseDirectionalDerivative (fun _ => v) (weighted γ f t) := by
      funext t x
      change (γ t)⁻¹ • fderiv ℝ (f t) x v = fderiv ℝ (fun y => (γ t)⁻¹ • f t y) x v
      have hd : HasFDerivAt (fun y => (γ t)⁻¹ • f t y) ((γ t)⁻¹ • fderiv ℝ (f t) x) x :=
        (((hsm hf.1) t).differentiable (by simp) x).hasFDerivAt.const_smul (γ t)⁻¹
      rw [hd.fderiv]
      rfl
    have hb' : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) (n + 1),
        BddAbove (hierarchyJetValues False (fun j _ => sw j • q j) w (weighted γ f)) := by
      rw [hQ]; exact hf.2
    have hfin (i : Fin 4) (hi : 0 < sw i) :
        FieldNormFinite ℓ h n
          (fun t => phaseDirectionalDerivative (fun _ => q i) (weighted γ f t)) := by
      obtain ⟨h1, h2⟩ := jetValues_bdd_dirDeriv False q sw i hi n hf.1 hb'
      refine ⟨h1, ?_⟩
      rw [← hQ]; exact h2
    have hD := paperLemmaD1_derivatives ℓ h hℓ hh n (f := weighted γ f) hf.1 hf.2
    simp only at hD
    refine ⟨fun i => ?_, ?_, ?_, ?_⟩
    · unfold labelPartial
      rw [hcomm]
      simpa only [q, Fin.lastCases_castSucc] using
        hfin i.castSucc (by simpa only [sw, Fin.lastCases_castSucc] using hℓ)
    · unfold phasePartial
      rw [hcomm]
      simpa only [q, Fin.lastCases_last] using
        hfin (Fin.last 3) (by simpa only [sw, Fin.lastCases_last] using hh)
    · have e : ∀ i, weightedFieldNorm ℓ h γ n (labelPartial i f) =
          hierarchyFiniteWordNorm False (hierarchyMixedDirection ℓ h) n (fun t =>
            phaseDirectionalDerivative (fun _ => phaseCoordinateDirection (.inl i))
              (weighted γ f t)) :=
        fun i => by unfold weightedFieldNorm fieldNorm labelPartial; rw [hcomm]
      simp only [e]
      exact hD.1
    · unfold weightedFieldNorm fieldNorm phasePartial
      rw [hcomm]
      exact hD.2
  · -- (D.4)
    intro E F G _ _ _ _ _ _ B f g hf hg
    have hprod : weighted γ (fun t x => B (f t x) (g t x)) =
        fun t x => B (f t x) (weighted γ g t x) := by
      funext t x
      simp [weighted, map_smul]
    refine ⟨?_, paperLemmaD1_product B False hMixed n γ hf.1 (hsm hg.1) hf.2 hg.2⟩
    rw [hprod]
    exact ⟨fun t => ((B.contDiff.comp (hf.1 t)).clm_apply (hg.1 t)),
      hierarchyJetValues_bdd_bilinear' B False hMixed n hf.1 hg.1 hf.2 hg.2⟩
  · -- (D.5)
    intro E _ _ _ f hf hper
    let d : Fin 4 → Vec3 × ℝ := fun i => hierarchyMixedDirection ℓ h i 0
    have hperW : ∀ t a, Function.Periodic (fun s => weighted γ f t (a, s)) 1 := by
      intro t a s
      simp only [weighted]
      rw [show f t (a, s + 1) = f t (a, s) from hper t a s]
    have hb : ∀ w ∈ hierarchyAdmissibleWords (Fin 4) n,
        BddAbove (hierarchyJetValues False (fun i _ => d i) w (weighted γ f)) := hf.2
    have hA := paperLemmaD1_phaseAverage d n (f := weighted γ f) hf.1 hperW hb
    have havg : (fun t (x : Vec3 × ℝ) => phaseMean (fun s => weighted γ f t (x.1, s))) =
        weighted γ (phaseAverage f) := by
      funext t x
      simp only [weighted, phaseAverage]
      exact phaseMean_const_smul _ _
    have hsub : weighted γ f - weighted γ (phaseAverage f) =
        weighted γ (f - phaseAverage f) := by
      funext t x
      simp [weighted, smul_sub]
    simp only at hA
    rw [havg, hsub] at hA
    obtain ⟨hAs, hAb⟩ := phaseAverage_jetValues_bdd d n (f := weighted γ f) hf.1 hperW hb
    rw [havg] at hAb
    have hAs : ∀ t, ContDiff ℝ ∞ (weighted γ (phaseAverage f) t) := by
      rw [← havg]; exact hAs
    have hAvgFin : FieldNormFinite ℓ h n (weighted γ (phaseAverage f)) := ⟨hAs, hAb⟩
    have hSubFin : FieldNormFinite ℓ h n (weighted γ (f - phaseAverage f)) := by
      rw [← hsub, sub_eq_add_neg, ← neg_one_smul ℝ (weighted γ (phaseAverage f))]
      refine ⟨fun t => (hf.1 t).add ((hAs t).const_smul (-1 : ℝ)), fun w hw => ?_⟩
      exact jetValues_bdd_add hMixed w hf.1 (fun t => (hAs t).const_smul (-1 : ℝ)) (hf.2 w hw)
        (jetValues_bdd_smul False hMixed w hAs (-1) (hAb w hw))
    refine ⟨hAvgFin, hSubFin, hA.1, hA.2, ?_⟩
    intro hzero
    have hzW : ∀ t a, phaseMean (fun s => weighted γ f t (a, s)) = 0 := by
      intro t a
      simp only [weighted]
      rw [phaseMean_const_smul, hzero, smul_zero]
    have hP :=
      hierarchyFiniteWordNorm_phasePrimitive_le d n (f := weighted γ f) hf.1 hperW hzW hb
    have hprim :
        (fun t (x : Vec3 × ℝ) => phasePrimitive (fun s => weighted γ f t (x.1, s)) x.2) =
          weighted γ (phaseInverse f) := by
      funext t x
      simp only [weighted, phaseInverse, phasePrimitive, phaseOscillation,
        intervalIntegral.integral_smul]
      rw [phaseMean_const_smul, smul_sub]
    simp only at hP
    rw [hprim] at hP
    refine ⟨⟨fun t => ?_, hP.1⟩, hP.2⟩
    have hS := contDiffOn_phasePrimitive (P := Vec3) (S := univ) convex_univ uniqueDiffOn_univ
      (f := fun a s => weighted γ f t (a, s))
      (by
        rw [univ_prod_univ, contDiffOn_univ]
        exact hf.1 t)
    rw [univ_prod_univ, contDiffOn_univ] at hS
    rw [← hprim]
    exact hS
  · -- (D.4) in `‖·‖_{[n],1/2}` for phase-independent fields, `γ ≡ 1`
    intro E F G _ _ _ _ _ _ B c d hc hd
    have hL : ∀ i, ContDiff ℝ ∞ (hierarchyLabelDirection ℓ i) := fun i => contDiff_const
    have h1 : (fun t x => ((fun _ : I => (1 : ℝ)) t)⁻¹ • d t x) = d := by
      funext t x; simp
    have hP := paperLemmaD1_product B True hL n (fun _ => (1 : ℝ)) hc.1 hd.1 hc.2
      (by rw [h1]; exact hd.2)
    rw [h1] at hP
    refine ⟨⟨fun t => ((B.contDiff.comp (hc.1 t)).clm_apply (hd.1 t)),
      hierarchyJetValues_bdd_bilinear' B True hL n hc.1 hd.1 hc.2 hd.2⟩, ?_⟩
    simpa [holderFieldNorm] using hP

end TorusEuler.Paper
