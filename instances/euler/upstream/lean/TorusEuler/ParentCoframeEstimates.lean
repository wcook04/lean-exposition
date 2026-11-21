import TorusEuler.CoframeDerivativeBounds
import TorusEuler.FlowHigherVariations

/-! The label-derivative coefficient bounds of Proposition 5.1. -/

open ContinuousLinearMap Set
open scoped BigOperators ContDiff

namespace TorusEuler

/-- Transport commutes with scalar multiplication of the launch covector. -/
theorem labelWaveVector_smul (X : ℝ → Velocity) (s t : ℝ) (a k : Vec3) (c : ℝ) :
    labelWaveVector X s a (c • k) t = c • labelWaveVector X s a k t :=
  map_smul _ _ _

/-- A prescribed nonzero length at activation and the two-sided deformation
bounds imply the normalized covector bounds in (5.3). -/
theorem IsLabelFlowOn.norm_normalizedLabelWaveVector_bounds
    {U : Velocity} {X : ℝ → Velocity} {T t₀ t D Λ : ℝ} (hT : 0 < T)
    (hX : IsLabelFlowOn U X (Icc 0 T))
    (hU : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (hper : ∀ s ∈ Icc 0 T, SpatiallyPeriodic (U s))
    (ht₀ : t₀ ∈ Icc 0 T) (ht : t ∈ Icc 0 T) (a k : Vec3)
    (hD : 1 ≤ D) (hΛ : 0 < Λ)
    (hcenter : ‖labelWaveVector X 0 0 k t₀‖ = Λ)
    (hF₀ : ‖fderiv ℝ (X 0 t₀) 0‖ ≤ D)
    (hG₀ : ‖fderiv ℝ (X t₀ 0) (X 0 t₀ 0)‖ ≤ D)
    (hF : ‖fderiv ℝ (X 0 t) a‖ ≤ D)
    (hG : ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) :
    ‖k‖ / Λ ≤ D ∧
      (D ^ 2)⁻¹ ≤ ‖Λ⁻¹ • labelWaveVector X 0 a k t‖ ∧
      ‖Λ⁻¹ • labelWaveVector X 0 a k t‖ ≤ D ^ 2 := by
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hc := hX.norm_labelWaveVector_bounds hT hU hper h₀ ht₀ 0 k hDpos hF₀ hG₀
  have hn := hX.norm_labelWaveVector_bounds hT hU hper h₀ ht a k hDpos hF hG
  rw [hcenter] at hc
  have hk₁ : ‖k‖ ≤ D * Λ := by
    rw [mul_comm]
    exact (div_le_iff₀ hDpos).mp hc.1
  have hk₂ : Λ ≤ D * ‖k‖ := hc.2
  have hscale :
      ‖Λ⁻¹ • labelWaveVector X 0 a k t‖ = ‖labelWaveVector X 0 a k t‖ / Λ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ), div_eq_mul_inv, mul_comm]
  refine ⟨(div_le_iff₀ hΛ).mpr hk₁, ?_, ?_⟩
  · rw [hscale, le_div_iff₀ hΛ]
    have hkl : ‖k‖ ≤ D * ‖labelWaveVector X 0 a k t‖ := by
      rw [mul_comm]
      exact (div_le_iff₀ hDpos).mp hn.1
    have hΛl : Λ ≤ D ^ 2 * ‖labelWaveVector X 0 a k t‖ := by
      calc
        _ ≤ D * ‖k‖ := hk₂
        _ ≤ D * (D * ‖labelWaveVector X 0 a k t‖) :=
          mul_le_mul_of_nonneg_left hkl hDpos.le
        _ = _ := by rw [pow_two, mul_assoc]
    have hdiv : Λ / (D ^ 2) ≤ ‖labelWaveVector X 0 a k t‖ :=
      (div_le_iff₀ (sq_pos_of_pos hDpos)).mpr (by simpa only [mul_comm] using hΛl)
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  · rw [hscale, div_le_iff₀ hΛ]
    calc
      _ ≤ D * ‖k‖ := hn.2
      _ ≤ D * (D * Λ) := mul_le_mul_of_nonneg_left hk₁ hDpos.le
      _ = _ := by rw [pow_two, mul_assoc]

section NormScaling

variable {V : Type*} [NormedAddCommGroup V]

/-- The lower covector bound implies the reciprocal bound used in
Proposition 5.1. -/
theorem normalizedWaveNorm_ne_zero_and_inv_sq_le {κ : V} {D : ℝ}
    (hD : 0 < D) (hlower : (D ^ 2)⁻¹ ≤ ‖κ‖) :
    κ ≠ 0 ∧ (‖κ‖ ^ 2)⁻¹ ≤ D ^ 4 := by
  have hpos : 0 < (D ^ 2)⁻¹ := inv_pos.mpr (sq_pos_of_pos hD)
  have hκ : 0 < ‖κ‖ := hpos.trans_le hlower
  refine ⟨norm_pos_iff.mp hκ, ?_⟩
  calc
    (‖κ‖ ^ 2)⁻¹ ≤ (((D ^ 2)⁻¹) ^ 2)⁻¹ :=
      (inv_le_inv₀ (sq_pos_of_pos hκ) (sq_pos_of_pos hpos)).mpr
        (pow_le_pow_left₀ hpos.le hlower 2)
    _ = D ^ 4 := by rw [inv_pow, inv_inv, ← pow_mul]

variable [NormedSpace ℝ V]

/-- The reciprocal squared norm of the normalized vector is the coefficient
of Proposition 5.1. -/
theorem inv_sq_norm_inv_smul (Λ : ℝ) (κ : V) :
    (‖Λ⁻¹ • κ‖ ^ 2)⁻¹ = Λ ^ 2 / ‖κ‖ ^ 2 := by
  rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, inv_pow, mul_inv_rev, inv_inv,
    div_eq_mul_inv, mul_comm]

end NormScaling

/-- The longitudinal rank-one projection is invariant under nonzero real
rescaling of its direction. -/
theorem rankOne_directionProjection_smul {V : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] (κ : V) {c : ℝ} (hc : c ≠ 0) :
    (‖c • κ‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (c • κ) (c • κ) =
      (‖κ‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ κ κ := by
  have hRank : InnerProductSpace.rankOne ℝ (c • κ) (c • κ) =
      c ^ 2 • InnerProductSpace.rankOne ℝ κ κ := by
    ext w : 1
    simp only [InnerProductSpace.rankOne_apply, real_inner_smul_left, _root_.smul_apply, smul_smul]
    congr 1
    ring
  rw [hRank, smul_smul, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, mul_inv_rev,
    mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hc), mul_one]

private theorem one_le_finsetJetConstant (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n) (n : ℕ) :
    1 ≤ 1 + ∑ j ∈ Finset.range (n + 1), C j :=
  le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => hC j)

private theorem le_finsetJetConstant (C : ℕ → ℝ) (hC : ∀ n, 0 ≤ C n)
    {i n : ℕ} (hi : i ≤ n) : C i ≤ 1 + ∑ j ∈ Finset.range (n + 1), C j := by
  have hmem : i ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  exact (Finset.single_le_sum (fun j _ => hC j) hmem).trans
    (le_add_of_nonneg_left zero_le_one)

private theorem contDiff_velocitySlice {U : Velocity} {T t : ℝ}
    (hU : ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)))
    (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (U t) :=
  contDiffOn_univ.mp (hU.comp (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun x _ => ⟨ht, mem_univ x⟩))

set_option maxHeartbeats 850000 in
/-- The actual coefficient fields of Proposition 5.1 have uniform
Fréchet jet bounds. The normalized covector uses the actual frequency
`Λ` prescribed by the central covector length at activation. The
velocity bounds are supplied through order `n + 1` for the order-`n`
material gradient. -/
theorem exists_parent_coefficientJetBounds (R : ℕ → ℝ) (hR : ∀ n, 0 ≤ R n) :
    ∃ C : ℕ → ℝ, (∀ n, 0 ≤ C n) ∧
      ∀ {U : Velocity} {X : ℝ → Velocity} {T D : ℝ}, 0 < T → T ≤ 1 → 1 ≤ D →
        IsLabelFlowOn U X (Icc 0 T) →
        ContDiffOn ℝ ∞ (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) →
        (∀ t ∈ Icc 0 T, SpatiallyPeriodic (U t)) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X 0 t) a‖ ≤ D) →
        (∀ t ∈ Icc 0 T, ∀ a, ‖fderiv ℝ (X t 0) (X 0 t a)‖ ≤ D) →
        (∀ n k : ℕ, 1 ≤ k → k ≤ n → ∀ t ∈ Icc 0 T, ∀ x,
          ‖iteratedFDeriv ℝ k (U t) x‖ ≤ R n * D ^ k) →
        ∀ (k : Vec3) {Λ t₀ : ℝ}, 0 < Λ → t₀ ∈ Icc 0 T →
          ‖labelWaveVector X 0 0 k t₀‖ = Λ → ∀ n : ℕ, ∀ t ∈ Icc 0 T, ∀ a : Vec3,
          let F := fderiv ℝ (X 0 t)
          let G (b : Vec3) := fderiv ℝ (X t 0) (X 0 t b)
          let M (b : Vec3) := fderiv ℝ (U t) (X 0 t b)
          let κ (b : Vec3) := labelWaveVector X 0 b k t
          ‖iteratedFDeriv ℝ n F a‖ ≤ C n * D ^ (5 * n + 1) ∧
          ‖iteratedFDeriv ℝ n G a‖ ≤ C n * D ^ (7 * n + 1) ∧
          ‖iteratedFDeriv ℝ n (fun b => (G b).adjoint) a‖ ≤ C n * D ^ (7 * n + 1) ∧
          ‖iteratedFDeriv ℝ n M a‖ ≤ C n * D ^ (6 * n + 1) ∧
          ‖iteratedFDeriv ℝ n (fun b => Λ⁻¹ • κ b) a‖ ≤ C n * D ^ (7 * n + 2) ∧
          ‖iteratedFDeriv ℝ n (fun b => Λ ^ 2 / ‖κ b‖ ^ 2) a‖ ≤ C n * D ^ (16 * n + 4) ∧
          ‖iteratedFDeriv ℝ n
            (fun b => (‖κ b‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ b) (κ b)) a‖ ≤
              C n * D ^ (16 * n + 8) := by
  obtain ⟨Cf, hCf, hFlowJet⟩ := exists_forward_flowJetBounds R hR
  let A (n : ℕ) := 1 + ∑ j ∈ Finset.range (n + 2), Cf j
  let I (n : ℕ) := (n.factorial : ℝ) ^ 2 * (A n) ^ n
  let L (n : ℕ) := 1 + ∑ j ∈ Finset.range (n + 1), I j
  let B (n : ℕ) := (2 : ℝ) ^ n * (L n * L n)
  let Q (n : ℕ) := (n.factorial : ℝ) ^ 2 * (B n) ^ n
  let P (n : ℕ) := (2 : ℝ) ^ n * (Q n * B n)
  let Mbound (n : ℕ) := (n.factorial : ℝ) * R (n + 1) * (A n) ^ n
  let C (n : ℕ) := Cf (n + 1) + I n + Mbound n + Q n + P n
  have hA (n : ℕ) : 1 ≤ A n := one_le_finsetJetConstant Cf hCf (n + 1)
  have hA₀ (n : ℕ) : 0 ≤ A n := zero_le_one.trans (hA n)
  have hI (n : ℕ) : 0 ≤ I n := mul_nonneg (sq_nonneg _) (pow_nonneg (hA₀ n) n)
  have hL (n : ℕ) : 1 ≤ L n := one_le_finsetJetConstant I hI n
  have hL₀ (n : ℕ) : 0 ≤ L n := zero_le_one.trans (hL n)
  have hB (n : ℕ) : 0 ≤ B n := mul_nonneg (by positivity) (mul_self_nonneg _)
  have hQ (n : ℕ) : 0 ≤ Q n := mul_nonneg (sq_nonneg _) (pow_nonneg (hB n) n)
  have hP (n : ℕ) : 0 ≤ P n := mul_nonneg (by positivity) (mul_nonneg (hQ n) (hB n))
  have hM (n : ℕ) : 0 ≤ Mbound n :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hR _)) (pow_nonneg (hA₀ n) n)
  have hconst (n : ℕ) :
      0 ≤ C n ∧ Cf (n + 1) ≤ C n ∧ I n ≤ C n ∧ Mbound n ≤ C n ∧ Q n ≤ C n ∧ P n ≤ C n := by
    dsimp only [C]
    have hf := hCf (n + 1)
    have hi := hI n
    have hm := hM n
    have hq := hQ n
    have hp := hP n
    exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith, by linarith⟩
  refine ⟨C, fun n => (hconst n).1, ?_⟩
  intro U X T D hT hT₁ hD hX hU hper hF hG hUjet k Λ t₀ hΛ ht₀ hcenter n t ht a
  dsimp only
  have hDpos : 0 < D := zero_lt_one.trans_le hD
  have hD₀ : 0 ≤ D := hDpos.le
  have hU₂ : ContDiffOn ℝ 2 (Function.uncurry U) (Icc 0 T ×ˢ (univ : Set Vec3)) :=
    hU.of_le (by simp)
  have h₀ : (0 : ℝ) ∈ Icc 0 T := left_mem_Icc.mpr hT.le
  have hNorm (b : Vec3) :=
    hX.norm_normalizedLabelWaveVector_bounds hT hU₂ hper ht₀ ht b k hD hΛ hcenter
      (hF t₀ ht₀ 0) (hG t₀ ht₀ 0) (hF t ht b) (hG t ht b)
  let kNorm := Λ⁻¹ • k
  have hk₂ : ‖kNorm‖ ≤ D := by
    rw [show ‖kNorm‖ = ‖k‖ / Λ by
      simp only [kNorm, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hΛ),
        div_eq_mul_inv, mul_comm]]
    exact (hNorm a).1
  have hFlow (j : ℕ) : ContDiff ℝ j (X 0 t) := (hX.labelJets_evolve j hT hU hper).1 t ht
  have hFlowAt (j : ℕ) (hj : 1 ≤ j) (b : Vec3) :
      ‖iteratedFDeriv ℝ j (X 0 t) b‖ ≤ Cf j * D ^ (5 * j - 4) :=
    hFlowJet hT hT₁ hD hX hU hper hF hG
      (fun j _ i hi hij => hUjet j i (by omega) hij) j hj t ht b
  have hFlowAt' (j : ℕ) (hj : 1 ≤ j) (hjn : j ≤ n + 1) (b : Vec3) :
      ‖iteratedFDeriv ℝ j (X 0 t) b‖ ≤ A n * D ^ (5 * j - 4) :=
    (hFlowAt j hj b).trans (mul_le_mul_of_nonneg_right (le_finsetJetConstant Cf hCf hjn)
      (pow_nonneg hD₀ _))
  have hJac : ‖iteratedFDeriv ℝ n (fderiv ℝ (X 0 t)) a‖ ≤ Cf (n + 1) * D ^ (5 * n + 1) :=
    norm_iteratedFDeriv_labelJacobian_le_of_flowJets n (hFlowAt _ (by omega) a)
  let G (b : Vec3) := fderiv ℝ (X t 0) (X 0 t b)
  have hJacJets (j : ℕ) (b : Vec3) (i : ℕ) (_ : 1 ≤ i) (hij : i ≤ j) :
      ‖iteratedFDeriv ℝ (i + 1) (X 0 t) b‖ ≤ A j * D ^ (5 * i + 1) := by
    have hh := hFlowAt (i + 1) (by omega) b
    have e : 5 * (i + 1) - 4 = 5 * i + 1 := by omega
    rw [e] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_finsetJetConstant Cf hCf (by omega : i + 1 ≤ j + 1))
      (pow_nonneg hD₀ _))
  have hInv (j : ℕ) (b : Vec3) : ‖iteratedFDeriv ℝ j G b‖ ≤ I j * D ^ (7 * j + 1) :=
    hX.norm_iteratedFDeriv_inverseLabelDerivative_le hT hU₂ hper h₀ ht (hFlow (j + 1))
      b hD (hA j) (hG t ht b) (hJacJets j b)
  have hCoframe : ‖iteratedFDeriv ℝ n (fun b => (G b).adjoint) a‖ ≤ I n * D ^ (7 * n + 1) := by
    let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
    change ‖iteratedFDeriv ℝ n (J ∘ G) a‖ ≤ _
    rw [J.norm_iteratedFDeriv_comp_left G a n]
    exact hInv n a
  let κ (b : Vec3) := labelWaveVector X 0 b kNorm t
  have hκeq : κ = fun b => Λ⁻¹ • labelWaveVector X 0 b k t :=
    funext fun b => labelWaveVector_smul X 0 t b k Λ⁻¹
  have hκdiff : ContDiff ℝ n κ := by
    let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
    have hGc : ContDiff ℝ n G :=
      hX.contDiff_inverseLabelDerivative hT hU₂ hper h₀ ht (hFlow (n + 1))
    exact (J.toContinuousLinearEquiv.contDiff.comp hGc).clm_apply contDiff_const
  have hκbound (j : ℕ) (b : Vec3) : ‖iteratedFDeriv ℝ j κ b‖ ≤ I j * D ^ (7 * j + 2) := by
    have hκj := hX.norm_iteratedFDeriv_labelWaveVector_le hT hU₂ hper h₀ ht (hFlow (j + 1))
      b kNorm hD (hA j) (hG t ht b) (hJacJets j b)
    calc
      _ ≤ ‖kNorm‖ * (I j * D ^ (7 * j + 1)) := hκj
      _ ≤ D * (I j * D ^ (7 * j + 1)) :=
        mul_le_mul_of_nonneg_right hk₂ (mul_nonneg (hI j) (pow_nonneg hD₀ _))
      _ = _ := by rw [show 7 * j + 2 = (7 * j + 1) + 1 by omega, pow_add, pow_one]; ring
  have hκlower (b : Vec3) : (D ^ 2)⁻¹ ≤ ‖κ b‖ := by
    rw [hκeq]
    exact (hNorm b).2.1
  have hκnz (b : Vec3) : κ b ≠ 0 :=
    (normalizedWaveNorm_ne_zero_and_inv_sq_le hDpos (hκlower b)).1
  have hRecip₀ : (‖κ a‖ ^ 2)⁻¹ ≤ D ^ 4 :=
    (normalizedWaveNorm_ne_zero_and_inv_sq_le hDpos (hκlower a)).2
  have hκj (i : ℕ) (hi : i ≤ n) : ‖iteratedFDeriv ℝ i κ a‖ ≤ L n * D ^ (7 * i + 2) :=
    (hκbound i a).trans (mul_le_mul_of_nonneg_right (le_finsetJetConstant I hI hi) (pow_nonneg hD₀ _))
  obtain ⟨hRecip, hProj⟩ := norm_iteratedFDeriv_waveCoefficients_le hκdiff
    hκnz a hD (hL n) hRecip₀ hκj
  let grad := fderiv ℝ (U t)
  let M (b : Vec3) := grad (X 0 t b)
  have hgradSmooth : ContDiff ℝ n grad :=
    ((contDiff_infty_iff_fderiv.mp (contDiff_velocitySlice hU ht)).2).of_le (by simp)
  have hGrad (i : ℕ) (hi : i ≤ n) :
      ‖iteratedFDeriv ℝ i grad (X 0 t a)‖ ≤ R (n + 1) * D * D ^ i := by
    rw [norm_iteratedFDeriv_fderiv]
    have h := hUjet (n + 1) (i + 1) (by omega) (by omega) t ht (X 0 t a)
    exact h.trans_eq (by rw [pow_succ]; ring)
  have hMaterial : ‖iteratedFDeriv ℝ n M a‖ ≤ Mbound n * D ^ (6 * n + 1) := by
    have h := norm_iteratedFDeriv_parentComposition_le hgradSmooth (hFlow n) a
      hD (hA n) (hR (n + 1)) hD₀ (fun i hi hin =>
        (hFlowAt' i hi (by omega) a).trans
          (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hD (by omega)) (hA₀ n))) hGrad
    refine h.trans_eq ?_
    rw [pow_succ]
    dsimp only [Mbound]
    ring
  rcases hconst n with ⟨_, hcF, hcI, hcM, hcQ, hcP⟩
  refine ⟨hJac.trans (mul_le_mul_of_nonneg_right hcF (pow_nonneg hD₀ _)),
    (hInv n a).trans (mul_le_mul_of_nonneg_right hcI (pow_nonneg hD₀ _)),
    hCoframe.trans (mul_le_mul_of_nonneg_right hcI (pow_nonneg hD₀ _)),
    hMaterial.trans (mul_le_mul_of_nonneg_right hcM (pow_nonneg hD₀ _)),
    ?_, ?_, ?_⟩
  · rw [← hκeq]
    exact (hκbound n a).trans (mul_le_mul_of_nonneg_right hcI (pow_nonneg hD₀ _))
  · have heq : (fun b => (‖κ b‖ ^ 2)⁻¹) =
        (fun b => Λ ^ 2 / ‖labelWaveVector X 0 b k t‖ ^ 2) := by
      rw [hκeq]
      exact funext fun b => inv_sq_norm_inv_smul Λ (labelWaveVector X 0 b k t)
    rw [← heq]
    exact hRecip.trans (mul_le_mul_of_nonneg_right hcQ (pow_nonneg hD₀ _))
  · have heq : (fun b => (‖κ b‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ (κ b) (κ b)) =
        (fun b => (‖labelWaveVector X 0 b k t‖ ^ 2)⁻¹ • InnerProductSpace.rankOne ℝ
          (labelWaveVector X 0 b k t) (labelWaveVector X 0 b k t)) := by
      rw [hκeq]
      exact funext fun b => rankOne_directionProjection_smul (labelWaveVector X 0 b k t)
        (inv_ne_zero hΛ.ne')
    rw [← heq]
    exact hProj.trans (mul_le_mul_of_nonneg_right hcP (pow_nonneg hD₀ _))

/-- Weighting each spatial derivative by the envelope radius removes the
order-dependent power of the scale in the finite sum. The parameter `A`
can supply the remaining fixed power for a coefficient or the amplitude
of a composed field. -/
theorem sum_weighted_labelJets_le_of_power
    {v C : ℕ → ℝ} {A D ℓ : ℝ} {n p : ℕ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hℓ : 0 ≤ ℓ) (hscale : ℓ * D ^ p ≤ 1)
    (hC : ∀ j ≤ n, 0 ≤ C j) (hv : ∀ j ≤ n, v j ≤ C j * A * D ^ (p * j)) :
    ∑ j ∈ Finset.range (n + 1), ℓ ^ j * v j ≤ (∑ j ∈ Finset.range (n + 1), C j) * A := by
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j hj => ?_
  have hn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hprod : 0 ≤ ℓ * D ^ p := mul_nonneg hℓ (pow_nonneg hD _)
  calc
    _ ≤ ℓ ^ j * (C j * A * D ^ (p * j)) :=
      mul_le_mul_of_nonneg_left (hv j hn) (pow_nonneg hℓ _)
    _ = (ℓ * D ^ p) ^ j * (C j * A) := by rw [mul_pow, ← pow_mul]; ring
    _ ≤ _ := mul_le_of_le_one_left (mul_nonneg (hC j hn) hA) (pow_le_one₀ hprod hscale)

end TorusEuler
