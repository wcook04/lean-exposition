import TorusEuler.Paper.Proofs.S5c.Library.CutoffStage

/-!
# Library copies for Proposition 5.11: the cutoff estimates from (B.2) and (5.59)

The library estimates of the truncation (`TruncatedChildStage.exists_cutoffBounds`,
`TruncatedChildStage.lean:555`) read the tail bound (B.2) of the real vector and tensor
cutoffs from library lemmas listed as content of Lemma B.1
(`spatialHolderHalfNorm_realVectorCutoffTail`, `spatialHolderHalfNorm_cutoffTail`,
`spatialHolderHalfNorm_realTensorCutoffTail`) and the product inequality (5.59) from
`spatialHolderHalf_bilinear`, glue by decision D3, the proof of the display (5.59). In the proof of
Proposition 5.11 (`sections/08_exact_wave.tex:420-445`) these are cited: "The tail bound
(B.2) at the order `P` gives `‖v_Λ‖_{C^{s,1/2}} ≤ C_{2,P} Λ^{s-P} ‖V‖_{C^{P,1/2}}`", then
(5.59) for the three quadratic tensors of (5.58). The copies take (B.2) for the real cutoff
and for the complex cutoff (the tensor cutoff is `R ∘ S_Λ ∘ J`) as hypotheses whose statements
are the (B.2) clauses of `Paper.Statement.lemma_B_1` (`CutTail`, `CutTailComplex`), and the
product inequality as a hypothesis whose statement is `Paper.Statement.Text.eq_5_59` with
chosen constants (`ProductBound`). The constants of the library (the Schwartz kernel tail
constant `cutoffHolderTailUniformConstant`, the bilinear constant `3(m+1)2^m‖B‖`) are replaced
by those of the hypotheses (`Ct M`, `Cm m ‖B‖`); the proofs are otherwise the library proofs.

| original | copy | change |
|---|---|---|
| `spatialLevel_nonneg`, `spatialHolderHalfNorm_nonneg'`, `spatialHolderHalf_mono`, `spatialHolderHalf_neg` (private, `TruncatedParentResidual.lean:21,32,85,118`) | same names | none |
| `spatialHolderHalfNorm_realTensorCutoffTail` (`:330`) | `realTensorCutoffTail` | the complex (B.2) is the hypothesis `CutTailComplex` (constant `Ct M`) |
| `spatialHolderHalf_realVectorCutoff` (private, `:369`) | `spatialHolderHalf_realVectorCutoff` | the real (B.2) at `s = M` is the hypothesis `CutTail` |
| `truncatedParentProjectedResidual_holder_bound` (`:415`) | `truncatedParentProjectedResidual_holder_bound` | (B.2) from `CutTail`, `CutTailComplex`; (5.59) from `ProductBound`; constants `Ct`, `Cm` |
| `truncatedEulerProjectedResidual_holder_bound` (`:649`) | `truncatedEulerProjectedResidual_holder_bound` | as above, specialized to the momentum tensor |
| `spatialHolderHalfNorm_cutoffVelocityDifference` (`TruncatedChildStage.lean:161`) | `cutoffVelocityDifference` | (B.2) from `CutTail` |
| `spatialHolderHalfNorm_cutoffPressureTailProduct` (`:180`) | `cutoffPressureTailProduct` | (B.2) from `CutTail` |
| `TruncatedChildStage.contDiff_slice` (private, `:280`) | `contDiff_slice` | none |
| `TruncatedChildStage.exists_cutoffBounds` (`:555`) | `exists_cutoffBounds` | hypotheses `CutTail`, `CutTailComplex` at each `Λ`, `ProductBound`; constants from them |
-/

open MeasureTheory Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S5c

noncomputable section

local notation "Labels" => UnitAddTorus (Fin 3)

/-! ## Hypotheses: (B.2) and (5.59) -/

/-- (B.2) of Lemma B.1 for the real vector cutoff at the frequency `Λ`, with the
constants `Ct`. -/
def CutTail (ψ : Vec3 → ℝ) (Λ : ℝ) (Ct : ℕ → ℝ) : Prop :=
  ∀ (M s : ℕ), s ≤ M → ∀ g : C(Labels, Vec3),
    SpatialHolderHalf M (fun x => g (toUnitTorus x)) →
    SpatialHolderHalf s
        (fun x => g (toUnitTorus x) - realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ∧
      spatialHolderHalfNorm s
          (fun x => g (toUnitTorus x) - realVectorFourierCutoff ψ Λ g (toUnitTorus x)) ≤
        Ct M * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M (fun x => g (toUnitTorus x))

/-- (B.2) of Lemma B.1 for the complex cutoff `smoothFourierCutoff ψ Λ` of fields with
values in the complex Banach space `E`, with the constants `Ct`. -/
def CutTailComplex (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (ψ : Vec3 → ℝ) (Λ : ℝ) (Ct : ℕ → ℝ) : Prop :=
  ∀ (M s : ℕ), s ≤ M → ∀ g : C(Labels, E),
    SpatialHolderHalf M (fun x => g (toUnitTorus x)) →
    SpatialHolderHalf s
        (fun x => g (toUnitTorus x) - smoothFourierCutoff ψ Λ g (toUnitTorus x)) ∧
      spatialHolderHalfNorm s
          (fun x => g (toUnitTorus x) - smoothFourierCutoff ψ Λ g (toUnitTorus x)) ≤
        Ct M * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M (fun x => g (toUnitTorus x))

/-- The product inequality (5.59) with the constants `Cm` (the statement
`Paper.Statement.Text.eq_5_59` with its constants chosen). -/
def ProductBound (Cm : ℕ → ℝ) : Prop :=
  ∀ m : ℕ, 0 ≤ Cm m ∧
    ∀ {E F G : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
      [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
      (B : E →L[ℝ] F →L[ℝ] G) (f : Vec3 → E) (g : Vec3 → F),
      SpatialHolderHalf m f → SpatialHolderHalf m g →
        SpatialHolderHalf m (fun x => B (f x) (g x)) ∧
          spatialHolderHalfNorm m (fun x => B (f x) (g x)) ≤
            Cm m * ‖B‖ * spatialHolderHalfNorm m f * spatialHolderHalfNorm m g

/-! ## Copied Hölder glue -/

section HolderCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Copy of the private `spatialLevel_nonneg`. -/
theorem spatialLevel_nonneg {f : Vec3 → E} {m j : ℕ}
    (hf : SpatialHolderHalf m f) (hj : j ≤ m) :
    0 ≤ spatialSupNorm (iteratedFDeriv ℝ j f) +
      spatialHolderHalfSeminorm (iteratedFDeriv ℝ j f) := by
  apply add_nonneg
  · exact (norm_nonneg _).trans (norm_le_spatialSupNorm (hf.2 j hj).1 0)
  · have h := le_ciSup (hf.2 j hj).2 ((0 : Vec3), (0 : Vec3))
    rw [show spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) (0, 0) = 0 by
      simp [spatialHolderHalfQuotient]] at h
    exact h

/-- Copy of the private `spatialHolderHalfNorm_nonneg'`. -/
theorem spatialHolderHalfNorm_nonneg' {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) : 0 ≤ spatialHolderHalfNorm m f :=
  Finset.sum_nonneg fun j hj => spatialLevel_nonneg hf (by simpa using hj)

/-- Copy of the private `spatialHolderHalf_mono`. -/
theorem spatialHolderHalf_mono {f : Vec3 → E} {m n : ℕ}
    (h : n ≤ m) (hf : SpatialHolderHalf m f) : SpatialHolderHalf n f ∧
      spatialHolderHalfNorm n f ≤ spatialHolderHalfNorm m f := by
  refine ⟨⟨hf.1.of_le (by exact_mod_cast h), fun j hj => hf.2 j (hj.trans h)⟩, ?_⟩
  unfold spatialHolderHalfNorm
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.add_le_add_right h 1))
  exact fun j hj _ => spatialLevel_nonneg hf (by simpa using hj)

/-- Copy of the private `spatialHolderHalf_neg`. -/
theorem spatialHolderHalf_neg {f : Vec3 → E} {m : ℕ}
    (hf : SpatialHolderHalf m f) : SpatialHolderHalf m (-f) ∧
      spatialHolderHalfNorm m (-f) = spatialHolderHalfNorm m f := by
  have hsup (j : ℕ) : (fun x => ‖iteratedFDeriv ℝ j (-f) x‖) =
      fun x => ‖iteratedFDeriv ℝ j f x‖ := by
    rw [iteratedFDeriv_neg]
    simp only [Pi.neg_apply, norm_neg]
  have hq (j : ℕ) : spatialHolderHalfQuotient (iteratedFDeriv ℝ j (-f)) =
      spatialHolderHalfQuotient (iteratedFDeriv ℝ j f) := by
    rw [iteratedFDeriv_neg]
    funext p
    simp only [spatialHolderHalfQuotient, Pi.neg_apply, neg_sub_neg]
    rw [norm_sub_rev]
  refine ⟨⟨hf.1.neg, fun j hj => ?_⟩, ?_⟩
  · rw [hsup j, hq j]
    exact hf.2 j hj
  · unfold spatialHolderHalfNorm
    apply Finset.sum_congr rfl
    intro j _
    simp only [spatialSupNorm, spatialHolderHalfSeminorm, hsup j, hq j]

end HolderCalculus

/-! ## The quantitative residual (5.58) -/

section QuantitativeResidual

variable {Q Qc : Type} [NormedAddCommGroup Q] [NormedSpace ℝ Q]
  [NormedAddCommGroup Qc] [NormedSpace ℂ Qc] [CompleteSpace Qc]

/-- Copy of `spatialHolderHalfNorm_realTensorCutoffTail`: the tail of the real tensor
cutoff `R ∘ S_Λ ∘ J` from the complex (B.2) (hypothesis `htc`, Lemma B.1) by
contraction. -/
theorem realTensorCutoffTail (J : Q →L[ℝ] Qc) (R : Qc →L[ℝ] Q)
    (hRJ : ∀ q, R (J q) = q) {ψ : Vec3 → ℝ} {Λ : ℝ} {Ct : ℕ → ℝ}
    (htc : CutTailComplex Qc ψ Λ Ct) (hCt : ∀ M, 0 ≤ Ct M) (hΛ : 0 < Λ)
    (g : C(UnitAddTorus (Fin 3), Q)) {M s : ℕ} (hsM : s ≤ M)
    (hg : SpatialHolderHalf M (fun x => g (toUnitTorus x))) :
    let f : Vec3 → Q := fun x => g (toUnitTorus x)
    let r : Vec3 → Q := f - fun x => realTensorFourierCutoff J R ψ Λ g (toUnitTorus x)
    SpatialHolderHalf s r ∧ spatialHolderHalfNorm s r ≤
      (‖R‖ * ‖J‖ * Ct M) * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M f := by
  let f := fun x => g (toUnitTorus x)
  let gc : C(UnitAddTorus (Fin 3), Qc) := ⟨fun a => J (g a), J.continuous.comp g.continuous⟩
  let rc := (fun x => gc (toUnitTorus x)) -
    fun x => smoothFourierCutoff ψ Λ gc (toUnitTorus x)
  have hJ := spatialHolderHalf_comp_clm J hg
  change SpatialHolderHalf M (fun x => gc (toUnitTorus x)) ∧
    spatialHolderHalfNorm M (fun x => gc (toUnitTorus x)) ≤ ‖J‖ * spatialHolderHalfNorm M f at hJ
  have ht := htc M s hsM gc hJ.1
  change SpatialHolderHalf s rc ∧ spatialHolderHalfNorm s rc ≤ _ at ht
  have hR := spatialHolderHalf_comp_clm R ht.1
  have heq : R ∘ rc = f - fun x => realTensorFourierCutoff J R ψ Λ g (toUnitTorus x) := by
    funext x
    change R (J (f x) - smoothFourierCutoff ψ Λ gc (toUnitTorus x)) = _
    rw [map_sub, hRJ]
    rfl
  rw [heq] at hR
  refine ⟨hR.1, hR.2.trans ?_⟩
  have hC := hCt M
  have hp : 0 ≤ Λ ^ ((s : ℤ) - M) := zpow_nonneg hΛ.le _
  calc
    _ ≤ ‖R‖ * (Ct M * Λ ^ ((s : ℤ) - M) * spatialHolderHalfNorm M (fun x => gc (toUnitTorus x))) :=
      mul_le_mul_of_nonneg_left ht.2 (norm_nonneg _)
    _ ≤ ‖R‖ * (Ct M * Λ ^ ((s : ℤ) - M) * (‖J‖ * spatialHolderHalfNorm M f)) := by
      gcongr
      exact hJ.2
    _ = _ := by ring

/-- Copy of the private `spatialHolderHalf_realVectorCutoff`: the real cutoff is bounded on
`C^{m,1/2}`, from (B.2) at `s = M = m` (hypothesis `hvt`, Lemma B.1). -/
theorem spatialHolderHalf_realVectorCutoff {ψ : Vec3 → ℝ} {Λ : ℝ} {Ct : ℕ → ℝ}
    (hvt : CutTail ψ Λ Ct)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {m : ℕ}
    (hg : SpatialHolderHalf m (fun x => g (toUnitTorus x))) :
    let u := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf m u ∧ spatialHolderHalfNorm m u ≤
      (2 * (m + 1) * (1 + Ct m)) * spatialHolderHalfNorm m (fun x => g (toUnitTorus x)) := by
  let f := fun x => g (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
  have ht := hvt m m le_rfl g hg
  change SpatialHolderHalf m (f - u) ∧ spatialHolderHalfNorm m (f - u) ≤ _ at ht
  have hneg := spatialHolderHalf_neg ht.1
  have h := spatialHolderHalf_add hg hneg.1
  rw [show f + -(f - u) = u by abel, hneg.2] at h
  refine ⟨h.1, h.2.trans ?_⟩
  have hΛ0 : Λ ^ ((m : ℤ) - m) = 1 := by rw [sub_self, zpow_zero]
  have htail : spatialHolderHalfNorm m (f - u) ≤ Ct m * spatialHolderHalfNorm m f := by
    have h2 := ht.2
    rw [hΛ0, mul_one] at h2
    exact h2
  calc
    _ ≤ (2 * (m + 1) : ℝ) * (spatialHolderHalfNorm m f + Ct m * spatialHolderHalfNorm m f) := by
      gcongr
    _ = _ := by ring

/-- Copy of `truncatedParentProjectedResidual_holder_bound`: the estimate of (5.58). The
tail bounds (B.2) are the hypotheses `hvt`, `htc` (Lemma B.1) and the product inequality
(5.59) is `hprod`; the constants are `Ct`, `Cm` in place of the library constants. -/
theorem truncatedParentProjectedResidual_holder_bound
    (J : Q →L[ℝ] Qc) (R : Qc →L[ℝ] Q) (hRJ : ∀ q, R (J q) = q)
    (B : Vec3 →L[ℝ] Vec3 →L[ℝ] Q) (D : (Vec3 →L[ℝ] Q) →L[ℝ] Vec3)
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) {Cproj : ℝ} (hCproj : 0 ≤ Cproj)
    (hproj : ∀ f : Vec3 → Vec3, SpatiallyPeriodic f → SpatialHolderHalf 1 f →
      SpatialHolderHalf 1 (proj f) ∧ spatialHolderHalfNorm 1 (proj f) ≤ Cproj * spatialHolderHalfNorm 1 f)
    {ψ : Vec3 → ℝ} {Ct Cm : ℕ → ℝ} (hCt : ∀ M, 0 ≤ Ct M) (hprod : ProductBound Cm)
    (P : ℕ) (hP : 2 ≤ P) :
    let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) * (1 + Ct 1))
    ∃ Kt : ℝ, 0 ≤ Kt ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → CutTail ψ Λ Ct → CutTailComplex Qc ψ Λ Ct →
      ∀ gV gRV : C(UnitAddTorus (Fin 3), Vec3),
      SpatialHolderHalf P (fun x => gV (toUnitTorus x)) →
      SpatialHolderHalf 1 (fun x => gRV (toUnitTorus x)) →
      let V := fun x => gV (toUnitTorus x)
      let v := (fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)) - V
      let res := truncatedParentProjectedResidual J R B D proj ψ Λ gV gRV
      let ε := Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P V)^2
      SpatialHolderHalf 2 v ∧ spatialHolderHalfNorm 2 v ≤ Kt * ε ∧
      SpatialHolderHalf 1 res ∧
        spatialHolderHalfNorm 1 res ≤
          Cr * spatialHolderHalfNorm 1 (fun x => gRV (toUnitTorus x)) + Kt * ε := by
  let C (m : ℕ) := Ct m
  let Bc (m : ℕ) := Cm m * ‖B‖
  let Sc (m : ℕ) := 2 * (m + 1) * (1 + C m)
  let Ct₀ := 36 * (Bc 2 * C P * Sc 2 + Bc 2 * C P + (‖R‖ * ‖J‖ * C P) * Bc P)
  let Cr := 4 * Cproj * Sc 1
  let Kt := C P + 4 * Cproj * ‖D‖ * Ct₀
  have hC (m : ℕ) : 0 ≤ C m := hCt m
  have hBc (m : ℕ) : 0 ≤ Bc m := mul_nonneg (hprod m).1 (ContinuousLinearMap.opNorm_nonneg B)
  have hSc (m : ℕ) : 0 ≤ Sc m := mul_nonneg (by positivity) (by linarith [hC m])
  have h1 := mul_nonneg (mul_nonneg (hBc 2) (hC P)) (hSc 2)
  have h2 := mul_nonneg (hBc 2) (hC P)
  have hQR : 0 ≤ ‖R‖ * ‖J‖ * C P := mul_nonneg (by positivity) (hC P)
  have hCt₀ : 0 ≤ Ct₀ := mul_nonneg (by norm_num)
    (add_nonneg (add_nonneg h1 h2) (mul_nonneg hQR (hBc P)))
  have hrem : 0 ≤ 4 * Cproj * ‖D‖ * Ct₀ := by positivity
  have hKt : 0 ≤ Kt := add_nonneg (hC P) hrem
  refine ⟨Kt, hKt, ?_⟩
  intro Λ hΛ hvt htc gV gRV hV hRV
  let V := fun x => gV (toUnitTorus x)
  let u := fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)
  let v := u - V
  let RV := fun x => gRV (toUnitTorus x)
  let cutRV := fun x => realVectorFourierCutoff ψ Λ gRV (toUnitTorus x)
  let gVV : C(UnitAddTorus (Fin 3), Q) :=
    ⟨fun z => B (gV z) (gV z), (B.continuous.comp gV.continuous).clm_apply gV.continuous⟩
  let VV := fun x => gVV (toUnitTorus x)
  let tailVV := VV - fun x => realTensorFourierCutoff J R ψ Λ gVV (toUnitTorus x)
  let vu := fun x => B (v x) (u x)
  let Vv := fun x => B (V x) (v x)
  let E := vu + Vv + tailVV
  let W := cutRV + D ∘ fderiv ℝ E
  let τ := Λ ^ ((2 : ℤ) - P)
  let M := spatialHolderHalfNorm P V
  let ε := τ * (1 + M)^2
  have hτ : 0 ≤ τ := zpow_nonneg (by linarith) _
  have hM : 0 ≤ M := spatialHolderHalfNorm_nonneg' hV
  have hε : 0 ≤ ε := by dsimp only [ε]; positivity
  have hΛ' : 0 < Λ := by linarith
  have hV₂ := spatialHolderHalf_mono hP hV
  have htail := hvt P 2 hP gV hV
  change SpatialHolderHalf 2 (V - u) ∧ spatialHolderHalfNorm 2 (V - u) ≤ C P * τ * M at htail
  have hv := spatialHolderHalf_neg htail.1
  rw [neg_sub] at hv
  change SpatialHolderHalf 2 v ∧ _ at hv
  have hvN : spatialHolderHalfNorm 2 v ≤ C P * τ * M := hv.2.le.trans htail.2
  have hu := spatialHolderHalf_realVectorCutoff hvt gV hV₂.1
  change SpatialHolderHalf 2 u ∧ spatialHolderHalfNorm 2 u ≤ Sc 2 * spatialHolderHalfNorm 2 V at hu
  have huN := hu.2.trans (mul_le_mul_of_nonneg_left hV₂.2 (hSc 2))
  have hcut := spatialHolderHalf_realVectorCutoff hvt gRV hRV
  change SpatialHolderHalf 1 cutRV ∧
    spatialHolderHalfNorm 1 cutRV ≤ Sc 1 * spatialHolderHalfNorm 1 RV at hcut
  have hVV := (hprod P).2 B V V hV hV
  change SpatialHolderHalf P VV ∧ spatialHolderHalfNorm P VV ≤ Bc P * M * M at hVV
  have htailVV := realTensorCutoffTail J R hRJ htc hCt hΛ' gVV hP hVV.1
  change SpatialHolderHalf 2 tailVV ∧ spatialHolderHalfNorm 2 tailVV ≤
    (‖R‖ * ‖J‖ * C P) * τ * spatialHolderHalfNorm P VV at htailVV
  have h₁ := (hprod 2).2 B v u hv.1 hu.1
  change SpatialHolderHalf 2 vu ∧ spatialHolderHalfNorm 2 vu ≤
    Bc 2 * spatialHolderHalfNorm 2 v * spatialHolderHalfNorm 2 u at h₁
  have h₂ := (hprod 2).2 B V v hV₂.1 hv.1
  change SpatialHolderHalf 2 Vv ∧ spatialHolderHalfNorm 2 Vv ≤
    Bc 2 * spatialHolderHalfNorm 2 V * spatialHolderHalfNorm 2 v at h₂
  have h₁N : spatialHolderHalfNorm 2 vu ≤ Bc 2 * (C P * τ * M) * (Sc 2 * M) :=
    h₁.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hvN (hBc 2)) huN
      (spatialHolderHalfNorm_nonneg' hu.1)
      (mul_nonneg (hBc 2) (mul_nonneg (mul_nonneg (hC P) hτ) hM)))
  have h₂N : spatialHolderHalfNorm 2 Vv ≤ Bc 2 * M * (C P * τ * M) :=
    h₂.2.trans (mul_le_mul (mul_le_mul_of_nonneg_left hV₂.2 (hBc 2)) hvN
      (spatialHolderHalfNorm_nonneg' hv.1) (mul_nonneg (hBc 2) hM))
  have h₃N : spatialHolderHalfNorm 2 tailVV ≤ (‖R‖ * ‖J‖ * C P) * τ * (Bc P * M * M) :=
    htailVV.2.trans (mul_le_mul_of_nonneg_left hVV.2 (mul_nonneg hQR hτ))
  have hsum := spatialHolderHalf_add h₁.1 h₂.1
  have hE := spatialHolderHalf_add hsum.1 htailVV.1
  have hE₀ : SpatialHolderHalf 2 E := hE.1
  have hEN : spatialHolderHalfNorm 2 E ≤ Ct₀ * (τ * M^2) := by
    have h₃ := spatialHolderHalfNorm_nonneg' htailVV.1
    change spatialHolderHalfNorm 2 E ≤ _
    have htmp := hE.2
    norm_num at hsum htmp
    dsimp only [Ct₀]
    nlinarith only [htmp, hsum.2, h₁N, h₂N, h₃N, h₃]
  have hdiv := spatialHolderHalf_contraction_fderiv D hE₀
  have hsumW := spatialHolderHalf_add hcut.1 hdiv.1
  have hW : SpatialHolderHalf 1 W := hsumW.1
  have hdivN : spatialHolderHalfNorm 1 (D ∘ fderiv ℝ E) ≤ ‖D‖ * (Ct₀ * (τ * M^2)) :=
    hdiv.2.trans (mul_le_mul_of_nonneg_left hEN (norm_nonneg D))
  have hsumWN : spatialHolderHalfNorm 1 W ≤
      4 * (spatialHolderHalfNorm 1 cutRV + spatialHolderHalfNorm 1 (D ∘ fderiv ℝ E)) := by
    norm_num at hsumW
    exact hsumW.2
  have hWN : spatialHolderHalfNorm 1 W ≤
      4 * (Sc 1 * spatialHolderHalfNorm 1 RV + ‖D‖ * (Ct₀ * (τ * M^2))) :=
    hsumWN.trans (mul_le_mul_of_nonneg_left (add_le_add hcut.2 hdivN) (by norm_num))
  have hWper : SpatiallyPeriodic W := by
    intro n x
    have hx (y : Vec3) : toUnitTorus (y + latticeVector n) = toUnitTorus y :=
      (toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩
    have he (y : Vec3) : E (y + latticeVector n) = E y := by
      simp only [E, vu, Vv, v, V, u, tailVV, VV, Pi.add_apply, Pi.sub_apply, hx]
    have hd : fderiv ℝ E (x + latticeVector n) = fderiv ℝ E x := by
      rw [← fderiv_comp_add_right]
      exact congrArg (fun f : Vec3 → Q => fderiv ℝ f x) (funext he)
    simp only [W, cutRV, Pi.add_apply, Function.comp_apply, hx, hd]
  have hL := hproj W hWper hW
  have hMε : τ * M^2 ≤ ε := mul_le_mul_of_nonneg_left (by nlinarith only [hM]) hτ
  have hMleε : τ * M ≤ ε := mul_le_mul_of_nonneg_left (by nlinarith only [hM, sq_nonneg M]) hτ
  refine ⟨hv.1, hvN.trans ?_, hL.1, hL.2.trans ?_⟩
  · calc
      _ = C P * (τ * M) := by ring
      _ ≤ C P * ε := mul_le_mul_of_nonneg_left hMleε (hC P)
      _ ≤ Kt * ε := by
        apply mul_le_mul_of_nonneg_right _ hε
        exact le_add_of_nonneg_right hrem
  · calc
      _ ≤ Cproj * (4 * (Sc 1 * spatialHolderHalfNorm 1 RV + ‖D‖ * (Ct₀ * (τ * M^2)))) :=
        mul_le_mul_of_nonneg_left hWN hCproj
      _ = Cr * spatialHolderHalfNorm 1 RV + (4 * Cproj * ‖D‖ * Ct₀) * (τ * M^2) := by
        dsimp only [Cr]; ring
      _ ≤ Cr * spatialHolderHalfNorm 1 RV + Kt * ε := by
        refine add_le_add le_rfl ?_
        calc
          _ ≤ (4 * Cproj * ‖D‖ * Ct₀) * ε := mul_le_mul_of_nonneg_left hMε hrem
          _ ≤ Kt * ε := mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (hC P)) hε

end QuantitativeResidual

/-- The complexification of the columns of a momentum tensor (the library's private
`momentumTensorComplexify`, `TruncatedParentResidual.lean:631`). -/
abbrev tensorComplexify : MomentumTensor →L[ℝ] (Fin 3 → ComplexEuclideanVec3) :=
  ContinuousLinearMap.piMap fun _ => periodicComplexifyVector

/-- The real part of the columns (the library's private `momentumTensorRealPart`). -/
abbrev tensorRealPart : (Fin 3 → ComplexEuclideanVec3) →L[ℝ] MomentumTensor :=
  ContinuousLinearMap.piMap fun _ => periodicRealPartVector

/-- Copy of the private `momentumTensorRealPart_complexify`. -/
theorem tensorRealPart_complexify (q : MomentumTensor) :
    tensorRealPart (tensorComplexify q) = q :=
  funext fun i => periodicRealPartVector_complexifyVector (q i)

/-- Copy of `truncatedEulerProjectedResidual_holder_bound` (the velocity tail and (5.58)
in physical Hölder norms), from the copy `truncatedParentProjectedResidual_holder_bound`
with the momentum tensor; the B.1 tails and (5.59) are hypotheses. -/
theorem truncatedEulerProjectedResidual_holder_bound
    (proj : (Vec3 → Vec3) → (Vec3 → Vec3)) {Cproj : ℝ} (hCproj : 0 ≤ Cproj)
    (hproj : ∀ f : Vec3 → Vec3, SpatiallyPeriodic f → SpatialHolderHalf 1 f →
      SpatialHolderHalf 1 (proj f) ∧ spatialHolderHalfNorm 1 (proj f) ≤ Cproj * spatialHolderHalfNorm 1 f)
    {ψ : Vec3 → ℝ} {Ct Cm : ℕ → ℝ} (hCt : ∀ M, 0 ≤ Ct M) (hprod : ProductBound Cm)
    (P : ℕ) (hP : 2 ≤ P) :
    let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) * (1 + Ct 1))
    ∃ Kt : ℝ, 0 ≤ Kt ∧
      ∀ (Λ : ℝ), 1 ≤ Λ → CutTail ψ Λ Ct → CutTailComplex (Fin 3 → ComplexEuclideanVec3) ψ Λ Ct →
      ∀ gV gRV : C(UnitAddTorus (Fin 3), Vec3),
      SpatialHolderHalf P (fun x => gV (toUnitTorus x)) →
      SpatialHolderHalf 1 (fun x => gRV (toUnitTorus x)) →
      let V := fun x => gV (toUnitTorus x)
      let v := (fun x => realVectorFourierCutoff ψ Λ gV (toUnitTorus x)) - V
      let res := truncatedEulerProjectedResidual proj ψ Λ gV gRV
      let ε := Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P V)^2
      SpatialHolderHalf 2 v ∧ spatialHolderHalfNorm 2 v ≤ Kt * ε ∧
      SpatialHolderHalf 1 res ∧
        spatialHolderHalfNorm 1 res ≤
          Cr * spatialHolderHalfNorm 1 (fun x => gRV (toUnitTorus x)) + Kt * ε :=
  truncatedParentProjectedResidual_holder_bound tensorComplexify tensorRealPart
    tensorRealPart_complexify momentumTensor momentumTensorDivergence proj hCproj hproj
    hCt hprod P hP

/-- Copy of `spatialHolderHalfNorm_cutoffVelocityDifference`, with (B.2) from `hvt`. -/
theorem cutoffVelocityDifference {ψ : Vec3 → ℝ} {Λ : ℝ} {Ct : ℕ → ℝ}
    (hvt : CutTail ψ Λ Ct)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {P m : ℕ} (hm : m ≤ P)
    (hg : SpatialHolderHalf P (fun x => g (toUnitTorus x))) :
    let V : Vec3 → Vec3 := fun x => g (toUnitTorus x)
    let u : Vec3 → Vec3 := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    SpatialHolderHalf m (u - V) ∧ spatialHolderHalfNorm m (u - V) ≤
      Ct P * Λ ^ ((m : ℤ) - P) * spatialHolderHalfNorm P V := by
  intro V u
  have h := hvt P m hm g hg
  change SpatialHolderHalf m (V - u) ∧ _ at h
  have hNeg := spatialHolderHalf_neg h.1
  rw [neg_sub] at hNeg
  exact ⟨hNeg.1, hNeg.2.trans_le h.2⟩

/-- Copy of `spatialHolderHalfNorm_cutoffPressureTailProduct`, with (B.2) from `hvt`. -/
theorem cutoffPressureTailProduct {ψ : Vec3 → ℝ} {Λ : ℝ} {Ct : ℕ → ℝ}
    (hvt : CutTail ψ Λ Ct) (hCt : ∀ M, 0 ≤ Ct M) (hΛ : 1 ≤ Λ)
    (g : C(UnitAddTorus (Fin 3), Vec3)) {P : ℕ} (hP : 2 ≤ P)
    (hg : SpatialHolderHalf P (fun x => g (toUnitTorus x))) :
    let V : Vec3 → Vec3 := fun x => g (toUnitTorus x)
    let u : Vec3 → Vec3 := fun x => realVectorFourierCutoff ψ Λ g (toUnitTorus x)
    let C := Ct P
    spatialHolderHalfNorm 1 (u - V) * (spatialHolderHalfNorm 1 u + spatialHolderHalfNorm 1 V) ≤
      C * (2 + C) * (Λ ^ ((2 : ℤ) - P) * (1 + spatialHolderHalfNorm P V)^2) := by
  intro V u C
  let M := spatialHolderHalfNorm P V
  have hM : 0 ≤ M := spatialHolderHalfNorm_nonneg' hg
  have hC : 0 ≤ C := hCt P
  have hv := spatialHolderHalf_mono (one_le_two.trans hP) hg
  have ht := cutoffVelocityDifference hvt g (show 1 ≤ P from one_le_two.trans hP) hg
  change SpatialHolderHalf 1 (u - V) ∧
    spatialHolderHalfNorm 1 (u - V) ≤ C * Λ ^ ((1 : ℤ) - P) * M at ht
  have htNonneg : 0 ≤ spatialHolderHalfNorm 1 (u - V) := spatialHolderHalfNorm_nonneg' ht.1
  have hpow (n : ℤ) (hn : (1 : ℤ) - P ≤ n) : Λ ^ ((1 : ℤ) - P) ≤ Λ ^ n :=
    zpow_le_zpow_right₀ hΛ hn
  have htSmall : spatialHolderHalfNorm 1 (u - V) ≤ C * M := by
    calc
      _ ≤ C * Λ ^ ((1 : ℤ) - P) * M := ht.2
      _ ≤ C * Λ ^ (0 : ℤ) * M :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpow 0 (by omega)) hC) hM
      _ = C * M := by rw [zpow_zero, mul_one]
  have htDepth : spatialHolderHalfNorm 1 (u - V) ≤ C * Λ ^ ((2 : ℤ) - P) * M :=
    ht.2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hpow ((2 : ℤ) - P) (by omega)) hC) hM)
  have hu : spatialHolderHalfNorm 1 u ≤ (1 + C) * M := by
    calc
      _ = spatialHolderHalfNorm 1 ((u - V) + V) := by rw [sub_add_cancel]
      _ ≤ spatialHolderHalfNorm 1 (u - V) + spatialHolderHalfNorm 1 V :=
        (spatialHolderHalf_add_exact ht.1 hv.1).2
      _ ≤ C * M + M := add_le_add htSmall hv.2
      _ = (1 + C) * M := by ring
  calc
    _ ≤ spatialHolderHalfNorm 1 (u - V) * ((1 + C) * M + M) :=
      mul_le_mul_of_nonneg_left (add_le_add hu hv.2) htNonneg
    _ ≤ (C * Λ ^ ((2 : ℤ) - P) * M) * ((1 + C) * M + M) :=
      mul_le_mul_of_nonneg_right htDepth (by positivity)
    _ = C * (2 + C) * (Λ ^ ((2 : ℤ) - P) * M ^ 2) := by ring
    _ ≤ _ := by gcongr; linarith

/-- Copy of the private `TruncatedChildStage.contDiff_slice`. -/
theorem contDiff_slice {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {T : ℝ}
    {f : ℝ → Vec3 → E}
    (hf : ContDiffOn ℝ ∞ (Function.uncurry f) (Icc 0 T ×ˢ (univ : Set Vec3)))
    {t : ℝ} (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (f t) :=
  contDiffOn_univ.mp (hf.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

/-- Copy of `TruncatedChildStage.exists_cutoffBounds`: the cutoff estimates of (5.56),
with constants uniform over all smooth approximate stages on a closed slab. The tails
(B.2) are the hypotheses `CutTail`, `CutTailComplex` at the frequency `Λ` of the stage
(Lemma B.1, constants `Ct`), and the product inequality (5.59) is `hprod`. -/
theorem exists_cutoffBounds {ψ : Vec3 → ℝ} {Ct Cm : ℕ → ℝ} (hCt : ∀ M, 0 ≤ Ct M)
    (hprod : ProductBound Cm) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ P : ℕ, 2 ≤ P → ∃ K : ℝ, 0 ≤ K ∧
      ∀ {T Λ : ℝ}, 0 < T → 1 ≤ Λ → CutTail ψ Λ Ct →
      CutTailComplex (Fin 3 → ComplexEuclideanVec3) ψ Λ Ct → ∀ {V RV : Velocity}
      (s : TruncatedChildStage T Λ ψ V RV) (approximatePressure : ℝ → EndpointSmoothPotential),
      ContDiffOn ℝ ∞ (Function.uncurry V) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      ContDiffOn ℝ ∞ (Function.uncurry RV) (Icc 0 T ×ˢ (univ : Set Vec3)) →
      (∀ t ∈ Icc 0 T, ∀ x, divergence (V t) x = 0) →
      (∀ t ∈ Icc 0 T, ∀ x, derivWithin (fun r => V r x) (Icc 0 T) t +
        fderiv ℝ (V t) x (V t x) + gradient (approximatePressure t).lift x = RV t x) →
      s.CutoffBounds approximatePressure P C K := by
  let Cproj := 2 * Real.sqrt 2 * ‖endpointStrongSpatialLeray‖
  have hCproj : 0 ≤ Cproj := by dsimp only [Cproj]; positivity
  let Cr := 4 * Cproj * (2 * (((1 : ℕ) : ℝ) + 1) * (1 + Ct 1))
  let Cp := 24 * ‖pressureHessianMultiplier‖
  have hCp : 0 ≤ Cp := by dsimp only [Cp]; positivity
  let C := max Cr Cp
  refine ⟨C, hCp.trans (le_max_right _ _), fun P hP => ?_⟩
  obtain ⟨Kres, hKres, hres⟩ := truncatedEulerProjectedResidual_holder_bound (ψ := ψ)
    periodicLerayHolderLift hCproj periodicLerayHolderLift_holder_one hCt hprod P hP
  let Kp := Ct P
  have hKp : 0 ≤ Kp := hCt P
  let K := max Kp (max Kres (Cp * Kp * (2 + Kp)))
  have hTailK : Kp ≤ K := le_max_left _ _
  have hResK : Kres ≤ K := (le_max_left _ _).trans (le_max_right _ _)
  have hPressureK : Cp * Kp * (2 + Kp) ≤ K := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨K, hKp.trans hTailK, ?_⟩
  intro T Λ hT hΛ hvt htc V RV s approximatePressure hV hRV hdivV hMom
  have hVrep (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun x => s.approximateTorus t (toUnitTorus x)) = V t := funext (s.approximate_rep t ht)
  have hRVrep (t : ℝ) (ht : t ∈ Icc 0 T) :
      (fun x => s.approximateResidualTorus t (toUnitTorus x)) = RV t :=
    funext (s.approximateResidual_rep t ht)
  have hVper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (V t) := by
    rw [← hVrep t ht]
    exact fun n x => congrArg (s.approximateTorus t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hRVper (t : ℝ) (ht : t ∈ Icc 0 T) : SpatiallyPeriodic (RV t) := by
    rw [← hRVrep t ht]
    exact fun n x =>
      congrArg (s.approximateResidualTorus t) ((toUnitTorus_eq_iff _ _).mpr ⟨n, rfl⟩)
  have hVholder (t : ℝ) (ht : t ∈ Icc 0 T) : SpatialHolderHalf P (V t) :=
    spatialHolderHalf_of_contDiff_periodic (contDiff_slice hV ht) (hVper t ht) P
  have hRVholder (t : ℝ) (ht : t ∈ Icc 0 T) : SpatialHolderHalf 1 (RV t) :=
    spatialHolderHalf_of_contDiff_periodic (contDiff_slice hRV ht) (hRVper t ht) 1
  have hRV₀ (t : ℝ) (ht : t ∈ Icc 0 T) : 0 ≤ spatialHolderHalfNorm 1 (RV t) :=
    spatialHolderHalfNorm_nonneg' (hRVholder t ht)
  have hε (t : ℝ) : 0 ≤ s.truncationError P t := by
    unfold TruncatedChildStage.truncationError
    have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
    positivity
  have hQuant (t : ℝ) (ht : t ∈ Icc 0 T) :
      spatialHolderHalfNorm 2 (s.velocity t - V t) ≤ Kres * s.truncationError P t ∧
      SpatialHolderHalf 1 (s.residual t) ∧ spatialHolderHalfNorm 1 (s.residual t) ≤
        Cr * spatialHolderHalfNorm 1 (RV t) + Kres * s.truncationError P t := by
    have hgV : SpatialHolderHalf P (fun x => s.approximateTorus t (toUnitTorus x)) :=
      (hVrep t ht).symm ▸ hVholder t ht
    have hgRV : SpatialHolderHalf 1 (fun x => s.approximateResidualTorus t (toUnitTorus x)) :=
      (hRVrep t ht).symm ▸ hRVholder t ht
    have h := hres Λ hΛ hvt htc (s.approximateTorus t) (s.approximateResidualTorus t) hgV hgRV
    have hR : s.residual t = truncatedEulerProjectedResidual periodicLerayHolderLift ψ Λ
        (s.approximateTorus t) (s.approximateResidualTorus t) := s.residual_cutoff t ht
    dsimp only at h
    simpa only [← s.velocity_eq_cutoff t, ← hR, hVrep t ht, hRVrep t ht,
      TruncatedChildStage.truncationError] using h.2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m hm t ht
    have hg : SpatialHolderHalf P (fun x => s.approximateTorus t (toUnitTorus x)) :=
      (hVrep t ht).symm ▸ hVholder t ht
    have h := cutoffVelocityDifference hvt (s.approximateTorus t) hm hg
    dsimp only at h
    rw [← s.velocity_eq_cutoff t, hVrep t ht] at h
    have hV₀ : 0 ≤ spatialHolderHalfNorm P (V t) := spatialHolderHalfNorm_nonneg' (hVholder t ht)
    refine ⟨h.1, h.2.trans ?_⟩
    have hΛ₀ : 0 ≤ Λ := zero_le_one.trans hΛ
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTailK (by positivity)) hV₀
  · intro t ht
    exact (hQuant t ht).1.trans (mul_le_mul_of_nonneg_right hResK (hε t))
  · intro t ht
    have h := (hQuant t ht).2
    exact ⟨h.1, h.2.trans (add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) (hRV₀ t ht))
      (mul_le_mul_of_nonneg_right hResK (hε t)))⟩
  · intro t ht
    let w : Velocity := fun r x => derivWithin (fun q => V q x) (Icc 0 T) r
    have hw : ContDiffOn ℝ ∞ (Function.uncurry w) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
      contDiffOn_sliceTimeDerivWithin_Icc hT hV
    have hDivW : ∀ x, divergence (w t) x = 0 :=
      divergence_slabVelocityTimeDerivative hT ht (hV.of_le (by simp)) hdivV
    have hH := spatialHolderHalfNorm_cutoffPressureHessian_of_residual_le
      (contDiff_slice (f := s.velocity) s.smooth_velocity ht) (contDiff_slice hV ht)
      (contDiff_slice hRV ht) (contDiff_slice s.smooth_pressure ht) (approximatePressure t).smooth
      (s.periodic_velocity t) (hVper t ht) (hRVper t ht) (s.periodic_pressure t ht)
      (approximatePressure t).periodic (hdivV t ht)
      ((contDiff_slice hw ht).differentiable (by simp)) hDivW (s.poisson t ht) (hMom t ht)
    have hg : SpatialHolderHalf P (fun x => s.approximateTorus t (toUnitTorus x)) :=
      (hVrep t ht).symm ▸ hVholder t ht
    have hProduct := cutoffPressureTailProduct hvt hCt hΛ (s.approximateTorus t) hP hg
    dsimp only at hProduct
    rw [← s.velocity_eq_cutoff t, hVrep t ht] at hProduct
    calc
      _ ≤ Cp * (spatialHolderHalfNorm 1 (s.velocity t - V t) *
          (spatialHolderHalfNorm 1 (s.velocity t) + spatialHolderHalfNorm 1 (V t)) +
          spatialHolderHalfNorm 1 (RV t)) := hH
      _ ≤ Cp * ((Kp * (2 + Kp)) * s.truncationError P t + spatialHolderHalfNorm 1 (RV t)) :=
        mul_le_mul_of_nonneg_left (add_le_add_left hProduct _) hCp
      _ = Cp * spatialHolderHalfNorm 1 (RV t) +
          (Cp * Kp * (2 + Kp)) * s.truncationError P t := by ring
      _ ≤ C * spatialHolderHalfNorm 1 (RV t) + K * s.truncationError P t :=
        add_le_add (mul_le_mul_of_nonneg_right (le_max_right _ _) (hRV₀ t ht))
          (mul_le_mul_of_nonneg_right hPressureK (hε t))

end

end TorusEuler.Paper.Lib.S5c
