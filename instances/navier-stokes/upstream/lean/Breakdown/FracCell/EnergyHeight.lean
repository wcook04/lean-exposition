import Breakdown.FracCell.EnergyHeightRows

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

namespace EnergyHeightInternal

theorem side_lw (K : CellBox) (hK : IsCellBox K) (t₀ : ℝ → ℝ) (h : Continuous t₀) :
    0 < K.r₁ ∨ ∃ t₁ : ℝ → ℝ, Continuous t₁ ∧ ∀ r, K.lineWeight r * t₀ r = r * t₁ r := by
  by_cases h0 : K.r₁ = 0
  · exact Or.inr ⟨t₀, h, fun r => by simp [CellBox.lineWeight, h0]⟩
  · exact Or.inl (lt_of_le_of_ne hK.r_order.1 (Ne.symm h0))

theorem comb_mul (C : Fin 3 → Fin 3 → ℂ) (X : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (t s : ℝ → ℝ) :
    (fun p : ℝ × ℝ => ((t p.1 * s p.2 : ℝ) : ℂ) * ∑ a, ∑ b, C a b * X a b p)
      = fun p => ∑ a, ∑ b, C a b * (((t p.1 * s p.2 : ℝ) : ℂ) * X a b p) := by
  funext p
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))

theorem comb_integrable (S : Set (ℝ × ℝ)) (C : Fin 3 → Fin 3 → ℂ) (Y : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (h : ∀ a b, IntegrableOn (Y a b) S) : IntegrableOn (fun p => ∑ a, ∑ b, C a b * Y a b p) S :=
  integrable_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => (h a b).const_mul _))

theorem comb_integral (S : Set (ℝ × ℝ)) (C : Fin 3 → Fin 3 → ℂ) (Y : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (h : ∀ a b, IntegrableOn (Y a b) S) :
    ∫ p in S, ∑ a, ∑ b, C a b * Y a b p = ∑ a, ∑ b, C a b * ∫ p in S, Y a b p := by
  rw [integral_finsetSum]
  · refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [integral_finsetSum]
    · exact Finset.sum_congr rfl (fun b _ => integral_const_mul _ _)
    · intro b _; exact (h a b).const_mul _
  · intro a _; exact integrable_finsetSum _ (fun b _ => (h a b).const_mul _)

theorem pair_comb (K : CellBox) (C : Fin 3 → Fin 3 → ℂ) (F dF : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (h : ∀ a b, HeightWeakPair K (F a b) (dF a b)) :
    HeightWeakPair K (fun p => ∑ a, ∑ b, C a b * F a b p) (fun p => ∑ a, ∑ b, C a b * dF a b p) := by
  intro t s ht hs hside
  have hI := fun a b => h a b t s ht hs hside
  refine ⟨?_, ?_, ?_⟩
  · rw [comb_mul C F t s]
    exact comb_integrable _ C _ (fun a b => (hI a b).1)
  · rw [comb_mul C dF t s]
    exact comb_integrable _ C _ (fun a b => (hI a b).2.1)
  · intro hs1 hz1 hz2
    have hd := fun a b => h a b t (deriv s) ht (hs1.continuous_deriv le_rfl) hside
    rw [comb_mul C dF t s, comb_mul C F t (deriv s), comb_integral _ C _ (fun a b => (hI a b).2.1),
      comb_integral _ C _ (fun a b => (hd a b).1)]
    simp only [fun a b => (hI a b).2.2 hs1 hz1 hz2, mul_neg, Finset.sum_neg_distrib]

theorem continuous_radialPoly (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) :=
  HeightProj.continuous_triPoly B.radialCoef j

theorem continuous_heightPoly (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) :=
  HeightProj.continuous_triPoly B.heightCoef l

theorem differentiable_heightPoly (B : CellBases) (l : ℕ) : Differentiable ℝ (B.heightPoly l) := by
  unfold CellBases.heightPoly; fun_prop

theorem contDiff_heightPoly (B : CellBases) (l : ℕ) : ContDiff ℝ 1 (B.heightPoly l) := by
  unfold CellBases.heightPoly; fun_prop

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}

theorem lowRow_value (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hK : IsCellBox K)
    (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (u : D → ℂ) (hrep : Represents K B I m v G H u)
    (n : modes) (C : Fin 3 → Fin 3 → ℂ)
    (hpair : ∀ a b, HeightWeakPair K (gradMode m n G a b) (heightGradMode m n H a b)) (j l : Fin (Q + 1)) :
    rowApply (lowRow I n C j l) u = B.coef K (strainField m n G C) j l := by
  have h1 : rowApply (lowRow I n C j l) u = ∑ a, ∑ b, C a b * u (I.strainSlot n a b j l) := by
    simp only [rowApply, lowRow, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    simp [mul_ite, ite_mul]
  rw [h1]
  simp only [hrep.strain]
  unfold CellBases.coef strainField
  have hint : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode m n G a b p *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    intro a b
    have h := (hpair a b (fun r => K.lineWeight r * B.radialPoly j r) (B.heightPoly l)
      ((HeightProj.continuous_lineWeight K).mul (continuous_radialPoly B j)) (continuous_heightPoly B l)
      (side_lw K hK _ (continuous_radialPoly B j))).1
    refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    push_cast; ring
  have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * (∑ a, ∑ b, C a b * gradMode m n G a b p) *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = fun p => ∑ a, ∑ b, C a b *
      ((K.lineWeight p.1 : ℂ) * gradMode m n G a b p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
    funext p
    simp only [Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
  rw [e, comb_integral _ C _ hint]

theorem slope_basis (B : CellBases) (j l : ℕ) :
    heightSlope (basisFn B j l) = fun p => B.radialPoly j p.1 * deriv (B.heightPoly l) p.2 := by
  funext p
  unfold heightSlope basisFn
  show deriv (fun z => B.radialPoly j p.1 * B.heightPoly l z) p.2 = _
  exact deriv_const_mul _ ((differentiable_heightPoly B l) p.2)

theorem heightDeriv_comb (B : CellBases) (Q : ℕ) (c : Fin (Q + 1) → Fin (Q + 1) → ℂ) :
    CellBox.heightDeriv (fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l * ((basisFn B j l p : ℝ) : ℂ))
      = fun p => ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), c j l *
          ((B.radialPoly j p.1 * deriv (B.heightPoly l) p.2 : ℝ) : ℂ) := by
  funext p
  unfold CellBox.heightDeriv
  apply HasDerivAt.deriv
  refine HasDerivAt.fun_sum (fun j _ => HasDerivAt.fun_sum (fun l _ => ?_))
  refine HasDerivAt.const_mul _ ?_
  have h := (((differentiable_heightPoly B l) p.2).hasDerivAt).const_mul (B.radialPoly j p.1)
  exact h.ofReal_comp

theorem face_comb (K : CellBox) (hK : IsCellBox K) (C : Fin 3 → Fin 3 → ℂ) (F dF : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (h : ∀ a b, HeightWeakPair K (F a b) (dF a b)) (e : Fin 2) (t : ℝ → ℝ) (ht : Continuous t) :
    ∑ a, ∑ b, C a b * heightFaceMoment K (F a b) (dF a b) e t
      = heightFaceMoment K (fun p => ∑ a, ∑ b, C a b * F a b p) (fun p => ∑ a, ∑ b, C a b * dF a b p) e t := by
  have key : ∀ (cz oz : ℝ), min cz oz = K.z₁ → max cz oz = K.z₂ →
      ∑ a, ∑ b, C a b * heightStripMoment cz oz K.r₁ K.r₂ (fun r => r) (F a b) (dF a b) t
        = heightStripMoment cz oz K.r₁ K.r₂ (fun r => r) (fun p => ∑ a, ∑ b, C a b * F a b p)
            (fun p => ∑ a, ∑ b, C a b * dF a b p) t := by
    intro cz oz hmin hmax
    unfold heightStripMoment
    rw [hmin, hmax]
    have hS : Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc K.z₁ K.z₂ = K.rect := rfl
    rw [hS]
    have hYi : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => ((((1 / (cz - oz) : ℝ)) : ℂ) * F a b p
        + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * dF a b p) * ((p.1 * t p.1 : ℝ) : ℂ)) K.rect := by
      intro a b
      have side : 0 < K.r₁ ∨ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ r, r * t r = r * t₀ r :=
        Or.inr ⟨t, ht, fun r => rfl⟩
      have h1 := (h a b (fun r => r * t r) (fun _ => 1 / (cz - oz)) (by fun_prop) continuous_const side).1
      have h2 := (h a b (fun r => r * t r) (fun z => (z - oz) / (cz - oz)) (by fun_prop) (by fun_prop) side).2.1
      refine (h1.add h2).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      simp only [Pi.add_apply]; push_cast; ring
    have e1 : (fun p : ℝ × ℝ => ((((1 / (cz - oz) : ℝ)) : ℂ) * (∑ a, ∑ b, C a b * F a b p)
        + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * (∑ a, ∑ b, C a b * dF a b p)) * ((p.1 * t p.1 : ℝ) : ℂ))
        = fun p => ∑ a, ∑ b, C a b * (((((1 / (cz - oz) : ℝ)) : ℂ) * F a b p
          + (((p.2 - oz) / (cz - oz) : ℝ) : ℂ) * dF a b p) * ((p.1 * t p.1 : ℝ) : ℂ)) := by
      funext p
      simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ => by ring))
    rw [e1, comb_integral _ C _ hYi, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun b _ => by ring)
  unfold heightFaceMoment
  split_ifs
  · exact key _ _ (min_eq_right hK.z_order.2.le) (max_eq_left hK.z_order.2.le)
  · exact key _ _ (min_eq_left hK.z_order.2.le) (max_eq_right hK.z_order.2.le)

theorem continuous_refZ (K : CellBox) : Continuous K.refZ := by
  unfold CellBox.refZ; fun_prop

theorem refZ_sq_le (K : CellBox) (hK : IsCellBox K) {z : ℝ} (hz : z ∈ Set.Icc K.z₁ K.z₂) : K.refZ z ^ 2 ≤ 1 := by
  have hd : 0 < K.z₂ - K.z₁ := by linarith [hK.z_order.2]
  rw [CellBox.refZ, div_pow, div_le_one (by positivity)]
  nlinarith [hz.1, hz.2]

theorem refZ_sq_lt (K : CellBox) (hK : IsCellBox K) {z : ℝ} (hz : z ∈ Set.Ioo K.z₁ K.z₂) : K.refZ z ^ 2 < 1 := by
  have hd : 0 < K.z₂ - K.z₁ := by linarith [hK.z_order.2]
  rw [CellBox.refZ, div_pow, div_lt_one (by positivity)]
  nlinarith [hz.1, hz.2]

theorem proj_value (K : CellBox) (B : CellBases) (I : LowIndex D modes Q q) (hK : IsCellBox K)
    (hB : IsCellBases K B) (n : modes) (C : Fin 3 → Fin 3 → ℂ) (F dF : ℝ × ℝ → ℂ)
    (hpair : HeightWeakPair K F dF) (u : D → ℂ)
    (hrow : ∀ j l : Fin (Q + 1), rowApply (lowRow I n C j l) u = B.coef K F j l) :
    quadFormValue (heightProjForm K B I n C) u =
      K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
        (CellBox.heightDeriv (K.proj Q Q F)) := by
  have hF : ∀ t s : ℝ → ℝ, Continuous t → Continuous s →
      IntegrableOn (fun p => ((K.lineWeight p.1 * t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect := by
    intro t s ht hs
    exact (hpair (fun r => K.lineWeight r * t r) s ((HeightProj.continuous_lineWeight K).mul ht) hs
      (side_lw K hK t ht)).1
  rw [HeightProj.proj_eq_basis K B hB Q F hF, heightDeriv_comb]
  set P : Fin (Q + 1) × Fin (Q + 1) → ℝ × ℝ → ℝ :=
    fun i p => B.radialPoly i.1 p.1 * deriv (B.heightPoly i.2) p.2 with hP
  set w : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2) with hw
  have hPc : ∀ i, Continuous (P i) := fun i =>
    ((continuous_radialPoly B _).comp continuous_fst).mul
      (((contDiff_heightPoly B _).continuous_deriv le_rfl).comp continuous_snd)
  have hwc : Continuous w :=
    ((HeightProj.continuous_lineWeight K).comp continuous_fst).mul
      (continuous_const.sub (((continuous_refZ K).comp continuous_snd).pow 2))
  have hint : ∀ i i', IntegrableOn (fun p => w p * P i p * P i' p) K.rect := fun i i' =>
    ((hwc.mul (hPc i)).mul (hPc i')).continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hM : heightProjForm K B I n C = formOfRows (fun jl : Fin (Q + 1) × Fin (Q + 1) => lowRow I n C jl.1 jl.2)
      ((K.innerRadius : ℂ) • testInnerMatrix K w P) := by
    unfold heightProjForm
    congr 1
    ext i i'
    simp only [slope_basis, Matrix.smul_apply, testInnerMatrix, smul_eq_mul, Complex.ofReal_mul, hP, hw,
      rectIntegral]
  rw [hM, RadialForm.value_formOfRows, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, Complex.re_ofReal_mul,
    RadialForm.pairing_value K w P hint]
  unfold CellBox.normSqOn
  congr 2
  funext p
  simp only [hrow, Fintype.sum_prod_type, hP, hw]

end EnergyHeightInternal

open EnergyHeightInternal in
theorem componentHeight (hw : HeightModeWeakStatement) : ComponentHeightStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u hs n C
  have hK := hs.box
  have hB := hs.bases
  have hdeg := hs.scalars.degrees
  have hQ : Q = S.degHigh := hs.degHigh_eq
  have hq : q = S.degLow := hs.degLow_eq
  have hpa : ∀ a b, HeightWeakPair K (gradMode c.order n G a b) (heightGradMode c.order n H a b) :=
    fun a b => hw c.order v G H hs.field K hK n a b
  have hpair : HeightWeakPair K (strainField c.order n G C) (heightField c.order n H C) :=
    pair_comb K C _ _ hpa
  have hrow := lowRow_value K B I hK c.order v G H u hs.represents n C hpa
  have hface : ∀ (e : Fin 2) (j : Fin (q + 1)), rowApply (heightFaceComp I n C e j) u =
      heightFaceMoment K (strainField c.order n G C) (heightField c.order n H C) e (B.radialPoly j) := by
    intro e j
    have h1 : rowApply (heightFaceComp I n C e j) u = ∑ a, ∑ b, C a b * rowApply (I.heightFaceRow n e a b j) u := by
      simp only [rowApply, heightFaceComp, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl (fun a _ => ?_)
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun b _ => Finset.sum_congr rfl (fun _ _ => by ring))
    rw [h1]
    simp only [hs.represents.height_face]
    exact face_comb K hK C _ _ hpa e _ (continuous_radialPoly B j)
  have hrect : ∀ p ∈ K.rect, K.r₁ ≤ p.1 ∧ K.refZ p.2 ^ 2 ≤ 1 := fun p hp =>
    ⟨hp.1.1, refZ_sq_le K hK hp.2⟩
  have h3 : quadFormValue (heightOuterForm K B I n C) u =
      K.testSupremum (fun p => p.1) (polyFn q Q) (fun p => (K.refZ p.2 : ℂ) * heightField c.order n H C p) := by
    symm
    unfold heightOuterForm
    refine HeightParts.testSup_polyFn K hK (fun p => p.1) continuous_fst
      (fun p hp => le_trans hK.r_order.1 (hrect p hp).1)
      (fun p hp => lt_of_le_of_lt hK.r_order.1 hp.1.1) q Q _ _ u (fun i => ?_) (fun i => ?_)
    · have h := (hpair (fun r => r * r ^ (i.1 : ℕ)) (fun z => K.refZ z * z ^ (i.2 : ℕ)) (by fun_prop)
        ((continuous_refZ K).mul (continuous_pow _)) (Or.inr ⟨fun r => r ^ (i.1 : ℕ), by fun_prop, fun r => rfl⟩)).2.1
      refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
      simp only [monomial]; push_cast; ring
    · exact HeightRows.outer_rows K B I hK hB (by omega) n C _ _ hpair u hrow hface i
  have h2 : quadFormValue (if K.r₁ = 0 then 0 else heightInnerForm K B I n C) u =
      (if K.r₁ = 0 then 0 else
        K.testSupremum (fun p => (p.1 - K.r₁) * (1 - K.refZ p.2 ^ 2)) (polyFn (Q - 1) (Q - 1))
          (heightField c.order n H C)) := by
    split_ifs with h0
    · exact RadialForm.value_zero u
    · have hr : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
      obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 1 := ⟨Q - 1, by omega⟩
      simp only [Nat.add_sub_cancel]
      symm
      unfold heightInnerForm
      refine HeightParts.testSup_polyFn K hK (heightInnerWeight K) ?_ ?_ ?_ Q' Q' _ _ u (fun i => ?_) (fun i => ?_)
      · unfold heightInnerWeight; exact (continuous_fst.sub continuous_const).mul
          (continuous_const.sub (((continuous_refZ K).comp continuous_snd).pow 2))
      · intro p hp
        unfold heightInnerWeight
        exact mul_nonneg (by linarith [(hrect p hp).1]) (by linarith [(hrect p hp).2])
      · intro p hp
        unfold heightInnerWeight
        exact mul_pos (by linarith [hp.1.1]) (by linarith [refZ_sq_lt K hK hp.2])
      · have h := (hpair (fun r => (r - K.r₁) * r ^ (i.1 : ℕ)) (fun z => (1 - K.refZ z ^ 2) * z ^ (i.2 : ℕ))
          (by fun_prop) ((continuous_const.sub ((continuous_refZ K).pow 2)).mul (continuous_pow _))
          (Or.inl hr)).2.1
        refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp only [monomial, heightInnerWeight]; push_cast; ring
      · exact HeightRows.inner_rows K B I hK hB hr n C _ _ hpair u hrow i
  rw [RadialForm.value_add, RadialForm.value_add, proj_value K B I hK hB n C _ _ hpair u hrow, h2, h3]
  rfl

end Breakdown.CellCert.CellEnergy
