import TorusEuler.LocalizedAmplitudeComparison
import TorusEuler.Paper.Proofs.S53.Library.Leaf51
import TorusEuler.Paper.Proofs.S53.Library.CopyLACaux
import TorusEuler.Paper.Proofs.S53.Library.Leaves

/-!
# S53 library: Lemma 5.3 chain: scaled wave-phase jets, switched leading profile and label-Lipschitz bounds

Generated copy (script `s53tools/mkcopy.py`) of the declarations exists_parent_coefficient_label_lipschitz, exists_switchedLeadingProfile_scaledJetBounds, exists_scaled_wavePhaseJetBounds, exists_scaled_deriv_waveProfile_bound of
`TorusEuler/LocalizedAmplitudeComparison.lean`, placed in `TorusEuler.Paper.Lib.S53` so that the calls of the leaf results of
Lemmas 3.1, D.1 and D.3 resolve to the hypotheses carried by `Leaves`; the bounds of Lemma D.2 come from
`Leaves.d2` (`mul_of_D2`, `rescale_of_D2`) and the jets of Proposition 5.1 enter through the hypothesis
`Leaf2` / `Lib.S5a.LeafBounds`.
-/
noncomputable section

variable [TorusEuler.Paper.Lib.S53.Leaves]

open ContinuousLinearMap Set MeasureTheory
open scoped ContDiff InnerProductSpace
open NormedSpace (normalize)

namespace TorusEuler.Paper.Lib.S53

open TorusEuler
section LocalizedDuhamel

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

end LocalizedDuhamel

section NearLabelContraction

variable {E : Type} [NormedAddCommGroup E]

variable [InnerProductSpace ℝ E]

end NearLabelContraction

section FixedTransverse

variable {E S : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup S] [NormedSpace ℝ S]

end FixedTransverse

open NormedSpace (normalize)
open MovingWaveVector

namespace MovingWaveVector.PhysicalAmplification

open MovingWaveVector.PhysicalAmplification
end MovingWaveVector.PhysicalAmplification

/-- The scaled derivatives of the wave profile are bounded by `C h` (Lemma 3.1 through
`waveProfile_bounds`, replacing the original constants `1/2` and the library bounds). -/
private theorem exists_scaled_deriv_waveProfile_bound (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ h, 0 < h → h ≤ 1 → ∀ s,
      h ^ j * ‖iteratedDeriv j (waveProfile h) s‖ ≤ C * h := by
  obtain ⟨C0, hC0, hd0, hj0⟩ := waveProfile_bounds
  cases j with
  | zero =>
      refine ⟨C0, hC0, fun h hh h₁ s => ?_⟩
      simpa only [pow_zero, one_mul, iteratedDeriv_zero] using (hd0 h hh h₁ s).2.2
  | succ j =>
      cases j with
      | zero =>
          refine ⟨max C0 1, lt_max_of_lt_right zero_lt_one, fun h hh h₁ s => ?_⟩
          have ho := hd0 h hh h₁ s
          have hC1 : C0 * h ≤ max C0 1 := by
            nlinarith [le_max_left C0 1]
          have hnorm : ‖deriv (waveProfile h) s‖ ≤ max C0 1 := by
            rw [Real.norm_eq_abs, abs_le]
            exact ⟨by linarith [ho.1], ho.2.1.trans (le_max_right _ _)⟩
          have hmul := mul_le_mul_of_nonneg_left hnorm hh.le
          simp only [Nat.zero_add, pow_one, iteratedDeriv_one]
          linarith
      | succ j =>
          obtain ⟨C, hC, h⟩ := hj0 (j + 1 + 1) (by omega)
          refine ⟨C, hC, fun h₀ hh h₁ s => ?_⟩
          calc
            _ ≤ h₀ ^ (j + 1 + 1) * (C * h₀ ^ (1 - ((j + 1 + 1 : ℕ) : ℤ))) :=
              mul_le_mul_of_nonneg_left (h h₀ hh h₁ s) (by positivity)
            _ = _ := by
              rw [mul_left_comm, ← zpow_natCast h₀ (j + 1 + 1), ← zpow_add₀ hh.ne']
              congr 1
              have he : (((j + 1 + 1 : ℕ) : ℤ) + (1 - ((j + 1 + 1 : ℕ) : ℤ))) = 1 := by omega
              rw [he, zpow_one]

/-- Scaling the phase variable by the profile width gives uniform finite
derivative bounds for the wave and its pressure primitive. -/
theorem exists_scaled_wavePhaseJetBounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ h, 0 < h → h ≤ 1 →
      PhaseJetBound n (C * h) (fun p : Vec3 × ℝ => waveProfile h (h * p.2)) ∧
      PhaseJetBound n (C * h) (fun p : Vec3 × ℝ => wavePressurePrimitive h (h * p.2)) := by
  classical
  choose B hB hBD using exists_scaled_deriv_waveProfile_bound
  obtain ⟨C0, hC0, hd0, -⟩ := waveProfile_bounds
  let C := 1 + 2 * C0 + ∑ j ∈ Finset.range (n + 1), B j
  have hC : 1 ≤ C := by
    dsimp only [C]
    have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), B j := Finset.sum_nonneg fun j _ => (hB j).le
    linarith
  have hLe (j : ℕ) (hj : j ≤ n) : B j ≤ C := by
    have hmem : j ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
    have hsum := Finset.single_le_sum (f := B) (fun k _ => (hB k).le) hmem
    have htotal : (∑ k ∈ Finset.range (n + 1), B k) ≤ C := by
      dsimp only [C]
      linarith
    exact hsum.trans htotal
  refine ⟨C, hC, fun h hh h₁ => ?_⟩
  have hw (j : ℕ) (hj : j ≤ n) (s : ℝ) :
      h ^ j * ‖iteratedDeriv j (waveProfile h) s‖ ≤ C * h :=
    (hBD j h hh h₁ s).trans (mul_le_mul_of_nonneg_right (hLe j hj) hh.le)
  refine ⟨phaseJetBound_scaledPhaseOnly (contDiff_waveProfile hh h₁) hh hw,
    phaseJetBound_scaledPhaseOnly (contDiff_wavePressurePrimitive hh h₁) hh ?_⟩
  intro j hj s
  cases j with
  | zero =>
      rw [pow_zero, one_mul, iteratedDeriv_zero]
      unfold wavePressurePrimitive
      have hp := norm_phasePrimitive_le (contDiff_waveProfile hh h₁).continuous
        (periodic_waveProfile hh h₁) (phaseMean_waveProfile hh h₁)
        (fun σ _ => (hd0 h hh h₁ σ).2.2) s
      have h2 : ‖phasePrimitive (waveProfile h) s‖ ≤ C * h := by
        have : 2 * C0 ≤ C := by
          have hsum : 0 ≤ ∑ j ∈ Finset.range (n + 1), B j := Finset.sum_nonneg fun j _ => (hB j).le
          dsimp only [C]
          linarith
        nlinarith
      simpa only [one_mul] using h2
  | succ j =>
      have heq : deriv (wavePressurePrimitive h) = waveProfile h :=
        funext fun x => (hasDerivAt_wavePressurePrimitive hh h₁ x).deriv
      rw [iteratedDeriv_succ', heq, pow_succ, mul_comm (h ^ j), mul_assoc]
      exact (mul_le_mul_of_nonneg_left (hw j (by omega) s) hh.le).trans
        (mul_le_of_le_one_left (by positivity) h₁)


/-- The finite-order leading profile and pressure bounds follow from the
corresponding slow-factor bounds. The pressure slow factor includes the
frequency normalization in (5.22). -/
theorem exists_switchedLeadingProfile_scaledJetBounds (n : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {freq ell χ γ U Q : ℝ} {a κ : Vec3 → Vec3}
      {M : Vec3 → (Vec3 →L[ℝ] Vec3)},
      1 ≤ freq → 0 ≤ γ → 0 ≤ U → 0 ≤ Q →
      let h := freq ^ (-1 / 2 : ℝ)
      let F (p : Vec3 × ℝ) := (χ * radialEnvelope ell (ell • p.1)) • a (ell • p.1)
      let P (p : Vec3 × ℝ) := freq * -wavePressureCoefficient
        (χ * radialEnvelope ell (ell • p.1)) (κ (ell • p.1)) (a (ell • p.1)) (M (ell • p.1))
      ContDiff ℝ ∞ F → ContDiff ℝ ∞ P →
      PhaseJetBound n (U * γ * freq ^ (-3 / 4 : ℝ)) F →
      PhaseJetBound n (Q * γ * freq ^ (-3 / 4 : ℝ)) P →
      PhaseJetBound n (γ * (C * U * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ell h
          (fun x s => ((χ * radialEnvelope ell x) * waveProfile h s) • a x)) ∧
      PhaseJetBound n (γ * (C * Q * freq ^ (-5 / 4 : ℝ)))
        (scaledPhaseProfile ell h (fun x s =>
          freq * oscillatoryPhasePressure (M x) (κ x) (fun _ => 0)
            (fun σ => ((χ * radialEnvelope ell x) * waveProfile h σ) • a x) s)) := by
  obtain ⟨C, hC, hBase⟩ := exists_scaled_wavePhaseJetBounds n
  let B := (2 : ℝ) ^ n * C
  have hB : 1 ≤ B := by
    dsimp only [B]
    nlinarith [one_le_pow₀ (show (1 : ℝ) ≤ 2 by norm_num) (n := n)]
  refine ⟨B, hB, ?_⟩
  intro freq ell χ γ U Q a κ M hf hγ hU hQ h F P hF hP hFU hPQ
  have hwidth : (0 < h ∧ h ≤ 1) ∧ freq ^ (-3 / 4 : ℝ) * h = freq ^ (-5 / 4 : ℝ) :=
    profileWidth_and_seedScale hf
  obtain ⟨hWave, hPrim⟩ := hBase h hwidth.1.1 hwidth.1.2
  let L : (Vec3 × ℝ) →L[ℝ] ℝ := h • ContinuousLinearMap.snd ℝ Vec3 ℝ
  have hw : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => waveProfile h (h * p.2)) :=
    (contDiff_waveProfile hwidth.1.1 hwidth.1.2).comp L.contDiff
  have hp : ContDiff ℝ ∞ (fun p : Vec3 × ℝ => wavePressurePrimitive h (h * p.2)) :=
    (contDiff_wavePressurePrimitive hwidth.1.1 hwidth.1.2).comp L.contDiff
  have hV' := phaseJetBound_smul_localized hw hF (by positivity) (by positivity) hWave hFU
  have hP' := phaseJetBound_smul_localized hp hP (by positivity) (by positivity) hPrim hPQ
  have hvEq :
      scaledPhaseProfile ell h (fun x s => ((χ * radialEnvelope ell x) * waveProfile h s) • a x) =
        fun p => waveProfile h (h * p.2) • F p := by
    funext p
    simp only [scaledPhaseProfile, Function.comp_def, labelPhaseScale_apply, Function.uncurry,
      F, smul_smul]
    rw [mul_comm (waveProfile h (h * p.2))]
  have hpEq :
      scaledPhaseProfile ell h (fun x s => freq * oscillatoryPhasePressure (M x) (κ x)
        (fun _ => 0) (fun σ => ((χ * radialEnvelope ell x) * waveProfile h σ) • a x) s) =
      fun p => wavePressurePrimitive h (h * p.2) • P p := by
    funext p
    simp only [scaledPhaseProfile, Function.comp_def, labelPhaseScale_apply, Function.uncurry,
      P, oscillatoryPhasePressure_primary_eq, smul_eq_mul]
    ring
  have hs (A : ℝ) : (2 : ℝ) ^ n * (C * h) * (A * γ * freq ^ (-3 / 4 : ℝ)) =
      γ * (B * A * freq ^ (-5 / 4 : ℝ)) := by
    rw [← hwidth.2]
    dsimp only [B]
    ring
  exact ⟨by rw [hvEq, ← hs]; exact hV', by rw [hpEq, ← hs]; exact hP'⟩

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- The actual first parent coframe jets supply the label Lipschitz estimates
for the flow Jacobians, material gradient and transverse projection. The
transported wave-vector comparison is relative to the reference label. -/
theorem exists_parent_coefficient_label_lipschitz (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        ∀ (k : Vec3) {Λ t₀ : ℝ}, 0 < Λ → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = Λ → Lib.S5a.LeafBounds B U X T D k Λ →
          ∀ t ∈ Icc 0 T, ∀ a b : Vec3,
          let F := fderiv ℝ (X 0 t)
          let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
          let M (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
          let κ (x : Vec3) := labelWaveVector X 0 x k t
          ‖F a - F b‖ ≤ C * D ^ 6 * ‖a - b‖ ∧
          ‖G a - G b‖ ≤ C * D ^ 8 * ‖a - b‖ ∧
          ‖M a - M b‖ ≤ C * D ^ 7 * ‖a - b‖ ∧
          ‖κ a - κ b‖ ≤ C * D ^ 11 * ‖a - b‖ * ‖κ b‖ ∧
          ‖oscillatoryTransverseProjection (κ a) - oscillatoryTransverseProjection (κ b)‖ ≤
            C * D ^ 24 * ‖a - b‖ := by
  let C := B
  have hC := hB
  refine ⟨C 1, hC 1, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG k Λ t₀ hΛ ht₀ hcenter hLeaf t ht a b
  dsimp only
  let F := fderiv ℝ (X 0 t)
  let G (x : Vec3) := fderiv ℝ (X t 0) (X 0 t x)
  let M (x : Vec3) := fderiv ℝ (U t) (X 0 t x)
  let κ (x : Vec3) := labelWaveVector X 0 x k t
  let κN (x : Vec3) := Λ⁻¹ • κ x
  let P (x : Vec3) := (‖κ x‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ x) (κ x)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have hFlow : ContDiff ℝ 2 (X 0 t) := (hX.labelJets_evolve 2 hT hU hper).1 t ht
  have hFd : ContDiff ℝ 1 F := hFlow.fderiv_right (by norm_num)
  have hGd : ContDiff ℝ 1 G :=
    hX.contDiff_inverseLabelDerivative hT hU₂ hper h₀ ht (n := 1) hFlow
  have hU' : ContDiff ℝ ∞ (U t) :=
    contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
      (fun x _ => ⟨ht, mem_univ x⟩))
  have hGrad : ContDiff ℝ 1 (fderiv ℝ (U t)) :=
    ((contDiff_infty_iff_fderiv.mp hU').2).of_le (by simp)
  have hMd : ContDiff ℝ 1 M := hGrad.comp (hFlow.of_le (by norm_num))
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  have hκd : ContDiff ℝ 1 κ := (J.toContinuousLinearEquiv.contDiff.comp hGd).clm_apply contDiff_const
  have hκNd : ContDiff ℝ 1 κN := by
    change ContDiff ℝ 1 (fun x => Λ⁻¹ • κ x)
    exact (contDiff_const (c := Λ⁻¹)).smul hκd
  have hLower (x : Vec3) : (D ^ 2)⁻¹ ≤ ‖κN x‖ :=
    (hX.norm_normalizedLabelWaveVector_bounds hT hU₂ hper ht₀ ht x k hD hΛ hcenter
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t ht x) (hG t ht x)).2.1
  have hκnz (x : Vec3) : κ x ≠ 0 := by
    intro hzero
    have h := hLower x
    simp only [κN, hzero, smul_zero, norm_zero] at h
    exact (not_le_of_gt (show 0 < (D ^ 2)⁻¹ by positivity)) h
  have hQ : ContDiff ℝ 1 (fun x => ‖κ x‖ ^ 2) := by
    simp_rw [← real_inner_self_eq_norm_sq]
    exact ((innerSL ℝ (E := Vec3)).contDiff.comp hκd).clm_apply hκd
  let A : Vec3 →L[ℝ] (Vec3 →L[ℝ] (Vec3 →L[ℝ] Vec3)) := InnerProductSpace.rankOne ℝ
  have hPRank : ContDiff ℝ 1 (fun x => InnerProductSpace.rankOne ℝ (κ x) (κ x)) := by
    change ContDiff ℝ 1 (fun x => A (κ x) (κ x))
    exact (A.contDiff.comp hκd).clm_apply hκd
  have hPd : ContDiff ℝ 1 P :=
    (hQ.inv fun x => pow_ne_zero 2 (norm_ne_zero_iff.mpr (hκnz x))).smul hPRank
  have hJet (x : Vec3) := hLeaf 1 t ht x
  have hFdiff := norm_label_difference_le_of_first_jet (hFd.differentiable (by norm_num))
    (fun x => (hJet x).1) a b
  have hGdiff := norm_label_difference_le_of_first_jet (hGd.differentiable (by norm_num))
    (fun x => (hJet x).2.1) a b
  have hMdiff := norm_label_difference_le_of_first_jet (hMd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.1) a b
  have hκNdiff := norm_label_difference_le_of_first_jet (hκNd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.2.1) a b
  have hPdiff := norm_label_difference_le_of_first_jet (hPd.differentiable (by norm_num))
    (fun x => (hJet x).2.2.2.2.2.2) a b
  have hNorm (v : Vec3) : ‖Λ⁻¹ • v‖ = ‖v‖ / Λ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), div_eq_mul_inv, mul_comm]
  have hκAbs : ‖κ a - κ b‖ ≤ C 1 * D ^ 9 * ‖a - b‖ * Λ := by
    change ‖Λ⁻¹ • κ a - Λ⁻¹ • κ b‖ ≤ C 1 * D ^ 9 * ‖a - b‖ at hκNdiff
    rw [← smul_sub, hNorm] at hκNdiff
    exact (div_le_iff₀ hΛ).mp hκNdiff
  have hΛbound : Λ ≤ D ^ 2 * ‖κ b‖ := by
    have hx := hLower b
    change (D ^ 2)⁻¹ ≤ ‖Λ⁻¹ • κ b‖ at hx
    rw [hNorm, ← one_div (D ^ 2)] at hx
    have hl := (div_le_div_iff₀ (by positivity : 0 < D ^ 2) hΛ).mp hx
    simpa only [one_mul, mul_one, mul_comm] using hl
  have hκdiff : ‖κ a - κ b‖ ≤ C 1 * D ^ 11 * ‖a - b‖ * ‖κ b‖ := by
    calc
      _ ≤ C 1 * D ^ 9 * ‖a - b‖ * Λ := hκAbs
      _ ≤ C 1 * D ^ 9 * ‖a - b‖ * (D ^ 2 * ‖κ b‖) :=
        mul_le_mul_of_nonneg_left hΛbound
          (mul_nonneg (mul_nonneg (hC 1) (by positivity)) (norm_nonneg _))
      _ = _ := by ring
  have hQdiff :
      ‖oscillatoryTransverseProjection (κ a) - oscillatoryTransverseProjection (κ b)‖ =
        ‖P a - P b‖ := by
    change ‖(.id ℝ Vec3 - P a) - (.id ℝ Vec3 - P b)‖ = _
    rw [sub_sub_sub_cancel_left, norm_sub_rev]
  exact ⟨hFdiff, hGdiff, hMdiff, hκdiff, hQdiff.trans_le hPdiff⟩

end TorusEuler.Paper.Lib.S53

namespace TorusEuler.Paper.Lib.S53.LocalizedAmplitude

open TorusEuler.LocalizedAmplitude
end TorusEuler.Paper.Lib.S53.LocalizedAmplitude

