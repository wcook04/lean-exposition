import TorusEuler.Paper.Proofs.S53.Library.D2Bridge
import TorusEuler.SeedDerivativeBudgets

/-!
# S53 library: the coframe coefficients through Lemma D.2(a)

`transverseCoframe_jetPower` is the power bound (D.6) of the coefficients of the transverse coframe
of Lemma 5.3 (06c_finite_hierarchy.tex:92-95): the products of the 3 x 3 matrix coefficients `G Q` and
`(G Q)(M F)` of the parent flow satisfy (D.6) by Lemma D.2(a), taken from `Leaves.d2` through
`mul_of_D2`. The fixed contractions (restriction to the transverse plane, projection) are glue. The
fields `A_perp` and `A_perp^dagger` of the manuscript are fixed contractions of these products
(`A_perp = F iota`, `A_perp^dagger = pi G Q`, generator `-M_perp = pi (-2 (G Q)(M F)) iota`, see the proof of `Lemma 5.3`), so
D.2(a) is applied in the fixed value space `Vec3 →L Vec3`, which keeps the constants independent of the
covector `k`.
-/
open Set ContinuousLinearMap
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper.Lib.S53

open TorusEuler TorusEuler.LocalizedAmplitude

noncomputable section

section JetGlue

variable {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- Larger constants. -/
theorem JetPower.mono_const {C C' : ℕ → ℝ} {D : ℝ} {a : ℕ} {f : Vec3 → X} (hD : 1 ≤ D)
    (h : JetPower C D a f) (hle : ∀ m, C m ≤ C' m) : JetPower C' D a f :=
  ⟨h.1, fun m x => (h.2 m x).trans
    (mul_le_mul_of_nonneg_right (hle m) (pow_nonneg (zero_le_one.trans hD) _))⟩

/-- A larger exponent. -/
theorem JetPower.mono_exp {C : ℕ → ℝ} {D : ℝ} {a b : ℕ} {f : Vec3 → X} (hD : 1 ≤ D)
    (hC : ∀ m, 0 ≤ C m) (h : JetPower C D a f) (hab : a ≤ b) : JetPower C D b f :=
  ⟨h.1, fun m x => (h.2 m x).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_right₀ hD (Nat.mul_le_mul_right _ hab)) (hC m))⟩

/-- A fixed contraction applied on the left preserves the power bound. -/
theorem JetPower.comp_left {C : ℕ → ℝ} {D : ℝ} {a : ℕ} {f : Vec3 → X} (L : X →L[ℝ] Y)
    (hL : ‖L‖ ≤ 1) (h : JetPower C D a f) : JetPower C D a (fun x => L (f x)) := by
  refine ⟨L.contDiff.comp h.1, fun m x => ?_⟩
  have hf : ContDiffAt ℝ m f x := (h.1.of_le (by simp)).contDiffAt
  have hb := L.norm_iteratedFDeriv_comp_left hf le_rfl
  exact (hb.trans (mul_le_of_le_one_left (norm_nonneg _) hL)).trans (h.2 m x)

/-- A constant factor. -/
theorem JetPower.const_smul {C : ℕ → ℝ} {D : ℝ} {a : ℕ} {f : Vec3 → X} (c : ℝ)
    (h : JetPower C D a f) : JetPower (fun m => ‖c‖ * C m) D a (fun x => c • f x) := by
  refine ⟨h.1.const_smul c, fun m x => ?_⟩
  have hf : ContDiffAt ℝ m f x := (h.1.of_le (by simp)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hf, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.2 m x) (norm_nonneg _)

end JetGlue

section Coframe

/-- The coefficients of the transverse coframe through Lemma D.2(a): `G Q` has the power bound with
the exponent `32` and `-2 (G Q)(M F)` with the exponent `64`, where `Q = id - P` is the projection
orthogonal to the covector `G^T k`. The constants do not depend on `k`. -/
theorem transverseCoframe_jetPower [L : Leaves] (W : ℕ → ℝ) (hW : ∀ n, 0 ≤ W n) :
    ∃ C₁ C₂ : ℕ → ℝ, (∀ n, 0 ≤ C₁ n) ∧ (∀ n, 0 ≤ C₂ n) ∧
      ∀ (k : Vec3) {D : ℝ} {F G M : Vec3 → Vec3 →L[ℝ] Vec3}, 1 ≤ D →
        JetPower W D 16 F → JetPower W D 16 G → JetPower W D 16 M →
        JetPower W D 16 (fun b => (‖(G b).adjoint k‖ ^ 2)⁻¹ •
          InnerProductSpace.rankOne ℝ ((G b).adjoint k) ((G b).adjoint k)) →
        JetPower C₁ D 32 (fun b => (G b).comp (oscillatoryTransverseProjection ((G b).adjoint k))) ∧
        JetPower C₂ D 64 (fun b => (-2 : ℝ) •
          ((G b).comp (oscillatoryTransverseProjection ((G b).adjoint k))).comp ((M b).comp (F b))) := by
  let W1 (m : ℕ) : ℝ := 1 + W m
  have hW1 (m : ℕ) : 0 ≤ W1 m := add_nonneg zero_le_one (hW m)
  obtain ⟨C₁, hC₁, hmul₁⟩ := mul_of_D2 (X := Vec3 →L[ℝ] Vec3) (Y := Vec3 →L[ℝ] Vec3)
    (Z := Vec3 →L[ℝ] Vec3) W1 W1 hW1 hW1 16 16
  obtain ⟨C₃, hC₃, hmul₃⟩ := mul_of_D2 (X := Vec3 →L[ℝ] Vec3) (Y := Vec3 →L[ℝ] Vec3)
    (Z := Vec3 →L[ℝ] Vec3) (fun m => C₁ m) (fun m => C₁ m) hC₁ hC₁ (2 * max 16 16) (2 * max 16 16)
  refine ⟨fun m => C₁ m, fun m => ‖(-2 : ℝ)‖ * C₃ m, hC₁, fun m => mul_nonneg (norm_nonneg _) (hC₃ m), ?_⟩
  intro k D F G M hD hF hG hM hP
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hW1le (m : ℕ) : W m ≤ W1 m := by dsimp only [W1]; linarith
  have hF1 := hF.mono_const hD hW1le
  have hG1 := hG.mono_const hD hW1le
  have hM1 := hM.mono_const hD hW1le
  have hQ : JetPower W1 D 16 (fun b => oscillatoryTransverseProjection ((G b).adjoint k)) := by
    refine ⟨(contDiff_const (c := ContinuousLinearMap.id ℝ Vec3)).sub hP.1, fun i x => ?_⟩
    have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := i) (x := x)
      (contDiffAt_const (c := ContinuousLinearMap.id ℝ Vec3))
      ((hP.1.of_le (by simp)).contDiffAt)
    change iteratedFDeriv ℝ i (fun b => ContinuousLinearMap.id ℝ Vec3 - _) x = _ at hsub
    have hId : ‖iteratedFDeriv ℝ i (fun _ : Vec3 => ContinuousLinearMap.id ℝ Vec3) x‖ ≤ 1 := by
      cases i with
      | zero => simpa only [norm_iteratedFDeriv_zero] using (norm_id_le (𝕜 := ℝ) (E := Vec3))
      | succ i =>
        rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero i), Pi.zero_apply, norm_zero]
        exact zero_le_one
    have hpow : 1 ≤ D ^ (16 * (i + 1)) := one_le_pow₀ hD
    change ‖iteratedFDeriv ℝ i (fun b => ContinuousLinearMap.id ℝ Vec3 - _) x‖ ≤ _
    rw [hsub]
    calc _ ≤ ‖iteratedFDeriv ℝ i (fun _ : Vec3 => ContinuousLinearMap.id ℝ Vec3) x‖ +
          ‖iteratedFDeriv ℝ i _ x‖ := norm_sub_le _ _
      _ ≤ D ^ (16 * (i + 1)) + W i * D ^ (16 * (i + 1)) :=
        add_le_add (hId.trans hpow) (hP.2 i x)
      _ = W1 i * D ^ (16 * (i + 1)) := by dsimp only [W1]; ring
  have hcomp : ‖compL ℝ Vec3 Vec3 Vec3‖ ≤ 1 := norm_compL_le ℝ Vec3 Vec3 Vec3
  have hGQ := hmul₁ (compL ℝ Vec3 Vec3 Vec3) hcomp hD hG1 hQ
  have hMF := hmul₁ (compL ℝ Vec3 Vec3 Vec3) hcomp hD hM1 hF1
  have hAt := hmul₃ (compL ℝ Vec3 Vec3 Vec3) hcomp hD hGQ hMF
  have e32 : 2 * max 16 16 = 32 := by norm_num
  have e64 : 2 * max (2 * max 16 16) (2 * max 16 16) = 64 := by norm_num
  rw [e32] at hGQ
  rw [e64] at hAt
  refine ⟨?_, ?_⟩
  · simpa only [compL_apply] using hGQ
  · simpa only [compL_apply] using hAt.const_smul (-2 : ℝ)

end Coframe

section Contractions

variable {P : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]

/-- A fixed contraction does not increase the jets. -/
theorem norm_iteratedFDeriv_clm_le {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (L : X →L[ℝ] Y) (hL : ‖L‖ ≤ 1) {g : P → X} (hg : ContDiff ℝ ∞ g) (m : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ m (fun x => L (g x)) a‖ ≤ ‖iteratedFDeriv ℝ m g a‖ := by
  have hf : ContDiffAt ℝ m g a := (hg.of_le (by simp)).contDiffAt
  exact (L.norm_iteratedFDeriv_comp_left hf le_rfl).trans
    (mul_le_of_le_one_left (norm_nonneg _) hL)

/-- The lift `F ↦ F ι` to the transverse plane is smooth. -/
theorem contDiff_coframeLift' (k : Vec3) {g : P → Vec3 →L[ℝ] Vec3} {N : ℕ∞ω} (hg : ContDiff ℝ N g) :
    ContDiff ℝ N (fun x => coframeLift k (g x)) :=
  contDiffOn_univ.mp (contDiffOn_coframeLift k hg.contDiffOn)

/-- The lift `F ↦ F ι` to the transverse plane does not increase the jets. -/
theorem norm_iteratedFDeriv_coframeLift_le (k : Vec3) {g : P → Vec3 →L[ℝ] Vec3}
    (hg : ContDiff ℝ ∞ g) (m : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ m (fun x => coframeLift k (g x)) a‖ ≤ ‖iteratedFDeriv ℝ m g a‖ := by
  let L := (compL ℝ (transversePlane k) Vec3 Vec3).flip (transversePlane k).subtypeL
  have hL : ‖L‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun S => ?_
    change ‖coframeLift k S‖ ≤ 1 * ‖S‖
    rw [one_mul]
    exact norm_coframeLift_le k S
  exact norm_iteratedFDeriv_clm_le L hL hg m a

/-- The projection onto the transverse plane applied on the left does not increase the jets of a
field with values in `Vec3 →L Vec3`. -/
theorem norm_iteratedFDeriv_projLeft_le (k : Vec3) {g : P → Vec3 →L[ℝ] Vec3}
    (hg : ContDiff ℝ ∞ g) (m : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ m (fun x => (transversePlane k).orthogonalProjectionOnto.comp (g x)) a‖ ≤
      ‖iteratedFDeriv ℝ m g a‖ := by
  let L := compL ℝ Vec3 Vec3 (transversePlane k) (transversePlane k).orthogonalProjectionOnto
  have hL : ‖L‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun S => ?_
    change ‖(transversePlane k).orthogonalProjectionOnto.comp S‖ ≤ 1 * ‖S‖
    rw [one_mul]
    exact (((transversePlane k).orthogonalProjectionOnto).opNorm_comp_le S).trans
      (mul_le_of_le_one_left (norm_nonneg _) (transversePlane k).orthogonalProjectionOnto_norm_le)
  exact norm_iteratedFDeriv_clm_le L hL hg m a

/-- The projection onto the transverse plane applied on the left does not increase the jets of a
field with values in `S →L Vec3`. -/
theorem norm_iteratedFDeriv_projLeft'_le (k : Vec3) {g : P → transversePlane k →L[ℝ] Vec3}
    (hg : ContDiff ℝ ∞ g) (m : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ m (fun x => (transversePlane k).orthogonalProjectionOnto.comp (g x)) a‖ ≤
      ‖iteratedFDeriv ℝ m g a‖ := by
  let L := compL ℝ (transversePlane k) Vec3 (transversePlane k)
    (transversePlane k).orthogonalProjectionOnto
  have hL : ‖L‖ ≤ 1 := by
    refine opNorm_le_bound _ zero_le_one fun S => ?_
    change ‖(transversePlane k).orthogonalProjectionOnto.comp S‖ ≤ 1 * ‖S‖
    rw [one_mul]
    exact (((transversePlane k).orthogonalProjectionOnto).opNorm_comp_le S).trans
      (mul_le_of_le_one_left (norm_nonneg _) (transversePlane k).orthogonalProjectionOnto_norm_le)
  exact norm_iteratedFDeriv_clm_le L hL hg m a

/-- The compression `π E ι` of a smooth field does not increase the jets. -/
theorem norm_iteratedFDeriv_generator_le (k : Vec3) {g : P → Vec3 →L[ℝ] Vec3}
    (hg : ContDiff ℝ ∞ g) (m : ℕ) (a : P) :
    ‖iteratedFDeriv ℝ m (fun x => (transversePlane k).orthogonalProjectionOnto.comp
        (coframeLift k (g x))) a‖ ≤ ‖iteratedFDeriv ℝ m g a‖ :=
  (norm_iteratedFDeriv_projLeft'_le k (contDiff_coframeLift' k hg) m a).trans
    (norm_iteratedFDeriv_coframeLift_le k hg m a)

/-- The fixed transverse generator is the compression `π (-2 (G Q)(M F)) ι`. -/
theorem fixedTransverseGenerator_eq (k : Vec3) (F G M : Vec3 →L[ℝ] Vec3) :
    fixedTransverseGenerator M (coframeLift k F) (coframePullback k G) =
      (transversePlane k).orthogonalProjectionOnto.comp (coframeLift k
        ((-2 : ℝ) • (G.comp (oscillatoryTransverseProjection (G.adjoint k))).comp (M.comp F))) := by
  ext z
  simp [fixedTransverseGenerator, coframePullback, coframeLift]

end Contractions


section Rescaled

variable [L : Leaves]

omit [TorusEuler.Paper.Lib.S53.Leaves] in
/-- A constant bounding the finitely many rescaling constants `R m`, `m ≤ N`. -/
theorem exists_const_ge (N : ℕ) (R : ℕ → ℝ) (hR : ∀ m, 0 ≤ R m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m ≤ N, R m ≤ C := by
  refine ⟨1 + ∑ m ∈ Finset.range (N + 1), R m, ?_, fun m hm => ?_⟩
  · linarith [Finset.sum_nonneg (fun m (_ : m ∈ Finset.range (N + 1)) => hR m)]
  · have := Finset.single_le_sum (f := R) (fun m _ => hR m) (Finset.mem_range.mpr (Nat.lt_succ_of_le hm))
    linarith

/-- The rescaled jets of the lift `J`, the pullback `R` and the generator `A` of the transverse
coframe, by Lemma D.2(c) (`rescale_of_D2`) applied to the ambient coefficients `F`, `G Q` and
`-2 (G Q)(M F)` at the base scale `D₀` with `D₀ ^ d2Scale ≤ D`, and the fixed contractions. -/
theorem rescaled_coframe_jets (N : ℕ) (Kf Kg Ka : ℕ → ℝ) (hKf : ∀ m, 0 ≤ Kf m)
    (hKg : ∀ m, 0 ≤ Kg m) (hKa : ∀ m, 0 ≤ Ka m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (k : Vec3) {F G M : Vec3 → Vec3 →L[ℝ] Vec3} {ℓ D D₀ : ℝ},
      0 < ℓ → 1 ≤ D → 1 ≤ D₀ → D₀ ^ d2Scale ≤ D → ℓ * D ^ 30 ≤ 1 →
      JetPower Kf D₀ 16 F →
      JetPower Kg D₀ 32 (fun b => (G b).comp (oscillatoryTransverseProjection ((G b).adjoint k))) →
      JetPower Ka D₀ 64 (fun b => (-2 : ℝ) •
        ((G b).comp (oscillatoryTransverseProjection ((G b).adjoint k))).comp
          ((M b).comp (F b))) →
      PhaseJetBound N (C * D) (fun a => coframeLift k (F (ℓ • a))) ∧
      PhaseJetBound N (C * D ^ 9) (fun a => coframePullback k (G (ℓ • a))) ∧
      ∀ m ≤ N, 0 < m → ∀ a, ‖iteratedFDeriv ℝ m (fun b => fixedTransverseGenerator (M (ℓ • b))
        (coframeLift k (F (ℓ • b))) (coframePullback k (G (ℓ • b)))) a‖ ≤ C * ℓ * D ^ 27 := by
  obtain ⟨RF, hRF, hRFb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) Kf hKf 16
  obtain ⟨RG, hRG, hRGb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) Kg hKg 32
  obtain ⟨RA, hRA, hRAb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) Ka hKa 64
  obtain ⟨C, hC, hRC⟩ := exists_const_ge N (fun m => RF m + RG m + RA m)
    fun m => add_nonneg (add_nonneg (hRF m) (hRG m)) (hRA m)
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, hC, ?_⟩
  intro k F G M ℓ D D₀ hℓ hD hDb hpow h30 hFj hGQj hAtj
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hpow64 : D₀ ^ 64 ≤ D := hpow
  have hsD (a : ℕ) (ha : a ≤ 64) : ℓ * D₀ ^ a ≤ 1 := by
    calc ℓ * D₀ ^ a ≤ ℓ * D₀ ^ 64 := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hDb ha) hℓ.le
      _ ≤ ℓ * D := mul_le_mul_of_nonneg_left hpow64 hℓ.le
      _ ≤ ℓ * D ^ 30 := mul_le_mul_of_nonneg_left (le_self_pow₀ hD (by norm_num)) hℓ.le
      _ ≤ 1 := h30
  have hDpow (a e : ℕ) (hae : a ≤ 64) (he : 1 ≤ e) : D₀ ^ a ≤ D ^ e :=
    (pow_le_pow_right₀ hDb hae).trans (hpow64.trans (le_self_pow₀ hD (by omega)))
  have hscaleS : ContDiff ℝ ∞ (fun a : Vec3 => ℓ • a) := contDiff_id.const_smul _
  have hm1 (m : ℕ) (hm : m ≤ N) : RF m ≤ C ∧ RG m ≤ C ∧ RA m ≤ C := by
    have := hRC m hm
    have := hRF m
    have := hRG m
    have := hRA m
    refine ⟨by linarith, by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m hm a
    have hg : ContDiff ℝ ∞ (fun y => F (ℓ • y)) := hFj.1.comp hscaleS
    refine (norm_iteratedFDeriv_coframeLift_le k hg m a).trans ?_
    refine ((hRFb hDb hℓ (hsD 16 (by norm_num)) hFj m a).1).trans ?_
    rw [← pow_one D]
    exact mul_le_mul (hm1 m hm).1 (hDpow 16 1 (by norm_num) le_rfl) (pow_nonneg (by linarith) _) hC₀
  · intro m hm a
    have hg : ContDiff ℝ ∞ (fun y => (G (ℓ • y)).comp
        (oscillatoryTransverseProjection ((G (ℓ • y)).adjoint k))) := hGQj.1.comp hscaleS
    refine (norm_iteratedFDeriv_projLeft_le k hg m a).trans ?_
    refine ((hRGb hDb hℓ (hsD 32 (by norm_num)) hGQj m a).1).trans ?_
    exact mul_le_mul (hm1 m hm).2.1 (hDpow 32 9 (by norm_num) (by norm_num))
      (pow_nonneg (by linarith) _) hC₀
  · intro m hm hm₀ a
    have hg : ContDiff ℝ ∞ (fun y => (-2 : ℝ) •
        ((G (ℓ • y)).comp (oscillatoryTransverseProjection ((G (ℓ • y)).adjoint k))).comp
          ((M (ℓ • y)).comp (F (ℓ • y)))) := hAtj.1.comp hscaleS
    have hAeq : (fun b => fixedTransverseGenerator (M (ℓ • b)) (coframeLift k (F (ℓ • b)))
        (coframePullback k (G (ℓ • b)))) = fun b => (transversePlane k).orthogonalProjectionOnto.comp
        (coframeLift k ((-2 : ℝ) • ((G (ℓ • b)).comp
          (oscillatoryTransverseProjection ((G (ℓ • b)).adjoint k))).comp
            ((M (ℓ • b)).comp (F (ℓ • b))))) := by
      funext b
      exact fixedTransverseGenerator_eq k _ _ _
    rw [hAeq]
    refine (norm_iteratedFDeriv_generator_le k hg m a).trans ?_
    refine ((hRAb hDb hℓ (hsD 64 le_rfl) hAtj m a).2 hm₀).trans ?_
    have h2 : D₀ ^ (2 * 64) ≤ D ^ 27 := by
      rw [pow_mul']
      exact (pow_le_pow_left₀ (pow_nonneg (by linarith) _) hpow64 2).trans
        (pow_le_pow_right₀ hD (by norm_num))
    exact mul_le_mul (mul_le_mul_of_nonneg_right (hm1 m hm).2.2 hℓ.le) h2
      (pow_nonneg (by linarith) _) (mul_nonneg hC₀ hℓ.le)

/-- The rescaled jets of the coefficients `M`, `κ/λ` and `λ²/|κ|²` of the pressure operators, by
Lemma D.2(c) (`rescale_of_D2`) at the base scale `D₀` with `D₀ ^ d2Scale ≤ D`. -/
theorem rescaled_pressure_jets (N : ℕ) (W : ℕ → ℝ) (hW : ∀ m, 0 ≤ W m) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {M : Vec3 → Vec3 →L[ℝ] Vec3} {κ : Vec3 → Vec3} {freq ℓ D D₀ : ℝ},
      0 < ℓ → 1 ≤ D → 1 ≤ D₀ → D₀ ^ d2Scale ≤ D → ℓ * D ^ 16 ≤ 1 →
      JetPower W D₀ 16 M → JetPower W D₀ 16 (fun b => freq⁻¹ • κ b) →
      JetPower W D₀ 16 (fun b => freq ^ 2 / ‖κ b‖ ^ 2) →
      PhaseJetBound N (C * D) (fun a => M (ℓ • a)) ∧
      PhaseJetBound N (C * D ^ 2) (fun a => freq⁻¹ • κ (ℓ • a)) ∧
      PhaseJetBound N (C * D ^ 4) (fun a => freq ^ 2 / ‖κ (ℓ • a)‖ ^ 2) := by
  obtain ⟨RM, hRM, hRMb⟩ := rescale_of_D2 (X := Vec3 →L[ℝ] Vec3) W hW 16
  obtain ⟨RK, hRK, hRKb⟩ := rescale_of_D2 (X := Vec3) W hW 16
  obtain ⟨RQ, hRQ, hRQb⟩ := rescale_of_D2 (X := ℝ) W hW 16
  obtain ⟨C, hC, hRC⟩ := exists_const_ge N (fun m => RM m + RK m + RQ m)
    fun m => add_nonneg (add_nonneg (hRM m) (hRK m)) (hRQ m)
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  refine ⟨C, hC, ?_⟩
  intro M κ freq ℓ D D₀ hℓ hD hDb hpow hR hMj hKj hQj
  have hpow64 : D₀ ^ 64 ≤ D := hpow
  have hs16 : ℓ * D₀ ^ 16 ≤ 1 :=
    (mul_le_mul_of_nonneg_left ((pow_le_pow_right₀ hDb (by norm_num : 16 ≤ 64)).trans
      (hpow64.trans (le_self_pow₀ hD (by norm_num)))) hℓ.le).trans hR
  have hDpow (e : ℕ) (he : 1 ≤ e) : D₀ ^ 16 ≤ D ^ e :=
    (pow_le_pow_right₀ hDb (by norm_num : 16 ≤ 64)).trans (hpow64.trans (le_self_pow₀ hD (by omega)))
  have hm1 (m : ℕ) (hm : m ≤ N) : RM m ≤ C ∧ RK m ≤ C ∧ RQ m ≤ C := by
    have := hRC m hm
    have := hRM m
    have := hRK m
    have := hRQ m
    refine ⟨by linarith, by linarith, by linarith⟩
  refine ⟨?_, ?_, ?_⟩
  · intro m hm a
    have h := ((hRMb hDb hℓ hs16 hMj m a).1).trans (mul_le_mul (hm1 m hm).1 (hDpow 1 le_rfl)
      (pow_nonneg (by linarith) _) hC₀)
    simpa only [pow_one] using h
  · exact fun m hm a => ((hRKb hDb hℓ hs16 hKj m a).1).trans (mul_le_mul (hm1 m hm).2.1
      (hDpow 2 (by norm_num)) (pow_nonneg (by linarith) _) hC₀)
  · exact fun m hm a => ((hRQb hDb hℓ hs16 hQj m a).1).trans (mul_le_mul (hm1 m hm).2.2
      (hDpow 4 (by norm_num)) (pow_nonneg (by linarith) _) hC₀)

end Rescaled

end

end TorusEuler.Paper.Lib.S53
