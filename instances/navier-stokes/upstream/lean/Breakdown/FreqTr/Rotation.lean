import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff

noncomputable section

namespace Breakdown.Freq

namespace Internal.Rotation

theorem rotC_apply (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) (i : Fin 3) :
    rotC R z i = ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) * z j := rfl

theorem apply_eq_sum (R : Space ≃ₗᵢ[ℝ] Space) (η : Space) (i : Fin 3) :
    R η i = ∑ j : Fin 3, R (unitVector j) i * η j := by
  have hη : η = ∑ j : Fin 3, η j • unitVector j := by
    ext k; simp [unitVector, Pi.single_apply]
  conv_lhs => rw [hη]
  simp [map_sum, map_smul, mul_comm]

theorem symm_unit (R : Space ≃ₗᵢ[ℝ] Space) (i j : Fin 3) :
    R.symm (unitVector i) j = R (unitVector j) i := by
  have h1 : R.symm (unitVector i) j = inner ℝ (unitVector j) (R.symm (unitVector i)) := by
    simp [unitVector, EuclideanSpace.inner_single_left]
  have h2 : R (unitVector j) i = inner ℝ (unitVector i) (R (unitVector j)) := by
    simp [unitVector, EuclideanSpace.inner_single_left]
  rw [h1, h2, ← R.inner_map_eq_flip, real_inner_comm]

theorem rotC_rotC_symm (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : rotC R (rotC R.symm z) = z := by
  ext i
  simp only [rotC_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hk : ∀ k : Fin 3, ∑ j : Fin 3, ((R (unitVector j) i : ℝ) : ℂ) *
      (((R.symm (unitVector k) j : ℝ) : ℂ) * z k) = ((R (R.symm (unitVector k)) i : ℝ) : ℂ) * z k := by
    intro k
    rw [apply_eq_sum R (R.symm (unitVector k)) i]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  simp only [hk, LinearIsometryEquiv.apply_symm_apply]
  rw [Finset.sum_eq_single i]
  · simp [unitVector]
  · intro b _ hb
    simp [unitVector, Ne.symm hb]
  · simp

theorem rotC_inner (R : Space ≃ₗᵢ[ℝ] Space) (w z : CSpace) :
    inner ℂ (rotC R w) z = inner ℂ w (rotC R.symm z) := by
  simp only [PiLp.inner_apply, rotC_apply, RCLike.inner_apply, map_sum, map_mul, Complex.conj_ofReal,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => ?_))
  rw [symm_unit]
  ring

theorem norm_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : ‖rotC R z‖ = ‖z‖ := by
  have h : ‖rotC R z‖ ^ 2 = ‖z‖ ^ 2 := by
    have := rotC_inner R z (rotC R z)
    have h2 : rotC R.symm (rotC R z) = z := by
      simpa using rotC_rotC_symm R.symm z
    rw [h2] at this
    have h3 := congrArg Complex.re this
    rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h3
    exact_mod_cast h3
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 h

theorem rotC_freqVec (R : Space ≃ₗᵢ[ℝ] Space) (η : Space) : rotC R (freqVec η) = freqVec (R η) := by
  ext i
  rw [rotC_apply]
  have h : (freqVec (R η)) i = ((R η i : ℝ) : ℂ) := rfl
  rw [h, apply_eq_sum R η i]
  push_cast
  rfl

theorem rotC_smul (R : Space ≃ₗᵢ[ℝ] Space) (c : ℂ) (z : CSpace) : rotC R (c • z) = c • rotC R z := by
  ext i
  simp only [rotC_apply, PiLp.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem inner_freqVec_rotC (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) (z : CSpace) :
    inner ℂ (freqVec ξ) (rotC R z) = inner ℂ (freqVec (R.symm ξ)) z := by
  have := rotC_inner R.symm (freqVec ξ) z
  simp only [LinearIsometryEquiv.symm_symm] at this
  rw [← this, rotC_freqVec]

theorem longitudinal_rotC (R : Space ≃ₗᵢ[ℝ] Space) (ξ : Space) (z : CSpace) :
    longitudinal ξ (rotC R z) = rotC R (longitudinal (R.symm ξ) z) := by
  simp only [longitudinal, smul_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, map_smul, rotC_smul, rotC_freqVec,
    LinearIsometryEquiv.apply_symm_apply, LinearIsometryEquiv.norm_map, inner_freqVec_rotC]

theorem conjVec_rotC (R : Space ≃ₗᵢ[ℝ] Space) (z : CSpace) : conjVec (rotC R z) = rotC R (conjVec z) := by
  ext i
  simp [conjVec, rotC_apply, map_sum]

theorem ae_comp {f g : Space → CSpace} {A : Space → Space}
    (hA : Measure.QuasiMeasurePreserving A volume volume) (h : f =ᵐ[volume] g) :
    (fun ξ => f (A ξ)) =ᵐ[volume] fun ξ => g (A ξ) :=
  h.comp_tendsto hA.tendsto_ae

theorem qmp_liso (S : Space ≃ₗᵢ[ℝ] Space) : Measure.QuasiMeasurePreserving (fun ξ => S ξ) volume volume :=
  S.measurePreserving.quasiMeasurePreserving

theorem qmp_neg : Measure.QuasiMeasurePreserving (fun ξ : Space => -ξ) volume volume :=
  (Measure.measurePreserving_neg volume).quasiMeasurePreserving

theorem qmp_smul {c : ℝ} (hc : c ≠ 0) :
    Measure.QuasiMeasurePreserving (fun ξ : Space => c • ξ) volume volume :=
  Measure.quasiMeasurePreserving_smul volume hc

theorem fieldOp_cases (A : Space → Space) (F : Space → CSpace →L[ℝ] CSpace) :
    fieldOp A F = 0 ∨ IsRealizedBy (fieldOp A F) A F := by
  unfold fieldOp
  split_ifs with h
  · exact Or.inr h.choose_spec
  · exact Or.inl rfl

theorem rotL2_realized (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) :
    IsRealizedBy (rotL2 R) (fun ξ => R.symm ξ) (fun _ => rotC R) :=
  h1 R.symm.toContinuousLinearEquiv (fun _ => rotC R) ‖rotC R‖ aestronglyMeasurable_const (fun _ => le_rfl)

theorem reflConj_realized (h1 : FieldOpRealized) :
    IsRealizedBy reflConj (fun ξ => -ξ) (fun _ => conjVec) :=
  h1 (ContinuousLinearEquiv.neg ℝ) (fun _ => conjVec) ‖conjVec‖ aestronglyMeasurable_const (fun _ => le_rfl)

theorem norm_rotL2 (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (f : L2C) : ‖rotL2 R f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (rotL2_realized h1 R f)]
  have h : eLpNorm (fun ξ => rotC R (f (R.symm ξ))) 2 volume = eLpNorm (fun ξ => f (R.symm ξ)) 2 volume :=
    eLpNorm_congr_norm_ae (Filter.Eventually.of_forall (fun ξ => norm_rotC R _))
  rw [h]
  exact congrArg ENNReal.toReal
    (eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f) R.symm.measurePreserving)

theorem rotL2_rotL2_symm (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (g : L2C) :
    rotL2 R (rotL2 R.symm g) = g := by
  apply Lp.ext
  filter_upwards [rotL2_realized h1 R (rotL2 R.symm g),
    ae_comp (qmp_liso R.symm) (rotL2_realized h1 R.symm g)] with ξ a b
  rw [a, b]
  simp [rotC_rotC_symm]

theorem rot_mem_sig (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) {f : L2C} (hf : f ∈ Sig) :
    rotL2 R f ∈ Sig := by
  simp only [Sig, Submodule.mem_inf, LinearMap.mem_ker, ContinuousLinearMap.coe_coe,
    sub_apply, ContinuousLinearMap.id_apply, sub_eq_zero] at hf ⊢
  obtain ⟨hr, hl⟩ := hf
  have hR := rotL2_realized h1 R
  have hC := reflConj_realized h1
  refine ⟨?_, ?_⟩
  · have hf1 := hC f
    rw [hr] at hf1
    apply Lp.ext
    filter_upwards [hC (rotL2 R f), ae_comp qmp_neg (hR f), hR f, ae_comp (qmp_liso R.symm) hf1]
      with ξ a b c d
    rw [a, b, c, d, conjVec_rotC, map_neg]
  · rcases fieldOp_cases id longitudinal with h | h
    · rw [h]; rfl
    · have hl1 := h f
      rw [hl] at hl1
      apply Lp.ext
      filter_upwards [h (rotL2 R f), hR f, ae_comp (qmp_liso R.symm) (hl1.symm.trans (Lp.coeFn_zero _ _ _)),
        Lp.coeFn_zero CSpace 2 (volume : Measure Space)] with ξ a b c d
      rw [a, d]
      simp only [id] at c ⊢
      rw [b, longitudinal_rotC, c]
      simp

def rotSig (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) : X →ₗ[ℝ] X :=
  LinearMap.codRestrict Sig ((rotL2 R : L2C →ₗ[ℝ] L2C) ∘ₗ Sig.subtype) (fun x => rot_mem_sig h1 R x.2)

def rotIso (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) : X →ₗᵢ[ℝ] X :=
  { rotSig h1 R with norm_map' := fun x => norm_rotL2 h1 R x }

def rotEquiv (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) : X ≃ₗᵢ[ℝ] X :=
  LinearIsometryEquiv.ofSurjective (rotIso h1 R)
    (fun y => ⟨rotSig h1 R.symm y, Subtype.ext (rotL2_rotL2_symm h1 R y)⟩)

theorem rotEquiv_apply (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (x : X) :
    (rotEquiv h1 R x : L2C) = rotL2 R x := rfl

theorem rotX_coe (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (x : X) :
    (rotX R x : L2C) = rotL2 R x := by
  have h : ∃ E : X ≃ₗᵢ[ℝ] X, ∀ x, (E x : L2C) = rotL2 R x := ⟨rotEquiv h1 R, rotEquiv_apply h1 R⟩
  unfold rotX
  rw [dif_pos h]
  exact h.choose_spec x

theorem rotL2_heatL2 (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) (t : ℝ) (y : L2C) :
    rotL2 R (heatL2 t y) = heatL2 t (rotL2 R y) := by
  have hR := rotL2_realized h1 R
  rcases fieldOp_cases id (fun ξ => heatFactor t ξ • ContinuousLinearMap.id ℝ CSpace) with h | h
  · simp only [heatL2, h, zero_apply, map_zero]
  · change IsRealizedBy (heatL2 t) _ _ at h
    apply Lp.ext
    filter_upwards [hR (heatL2 t y), ae_comp (qmp_liso R.symm) (h y), h (rotL2 R y), hR y]
      with ξ a b c d
    simp only [id] at b c
    rw [a, b, c, d]
    simp [heatFactor, map_smul]

theorem rotL2_dilL2 (h1 : FieldOpRealized) (R : Space ≃ₗᵢ[ℝ] Space) {μ : ℝ} (hμ : 0 < μ) (y : L2C) :
    rotL2 R (dilL2 μ y) = dilL2 μ (rotL2 R y) := by
  have hR := rotL2_realized h1 R
  have hc : (Real.sqrt μ)⁻¹ ≠ 0 := inv_ne_zero (Real.sqrt_pos.2 hμ).ne'
  rcases fieldOp_cases (fun ξ => (Real.sqrt μ)⁻¹ • ξ)
      (fun _ => (Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ CSpace) with h | h
  · simp only [dilL2, h, zero_apply, map_zero]
  · change IsRealizedBy (dilL2 μ) _ _ at h
    apply Lp.ext
    filter_upwards [hR (dilL2 μ y), ae_comp (qmp_liso R.symm) (h y), h (rotL2 R y),
      ae_comp (qmp_smul hc) (hR y)] with ξ a b c d
    rw [a, b, c, d]
    simp [map_smul]

end Internal.Rotation

open Internal.Rotation in
theorem rotationAlgebra (h1 : FieldOpRealized) (h2 : DilationAlgebra) (h3 : HeatSemigroup) :
    RotationAlgebra := by
  intro R
  refine ⟨rotX_coe h1 R, fun t x => ?_, fun μ x => ?_⟩
  · apply Subtype.ext
    rw [rotX_coe h1, h3.2.2.2.2.2, h3.2.2.2.2.2, rotX_coe h1, rotL2_heatL2 h1]
  · by_cases hμ : 0 < μ
    · apply Subtype.ext
      rw [rotX_coe h1, h2.2.2.2.2 μ hμ, h2.2.2.2.2 μ hμ, rotX_coe h1, rotL2_dilL2 h1 R hμ]
    · simp [dilX, hμ]

end Breakdown.Freq
