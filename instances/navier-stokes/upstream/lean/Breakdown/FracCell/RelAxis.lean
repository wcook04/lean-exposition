import Breakdown.FracCell.StCoordsProof

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis

def AxisModeIntegrableStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
      ∀ (R z₁ z₂ : ℝ) (n : ℤ) (a b : Fin 3),
        IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p) (Set.Icc 0 R ×ˢ Set.Icc z₁ z₂)

def AxisFluxStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
      ∀ (R z₁ z₂ : ℝ), 0 < R → z₁ < z₂ → ∀ (t : ℝ → ℝ), Continuous t → ∀ (i : ℕ) (σ : Fin 2),
        ((R * R ^ i : ℝ) : ℂ) * radialStripMoment R 0 z₁ z₂
            (fun p => modeVec m 0 v p.1 p.2 (if σ = 0 then 0 else 1))
            (gradMode m 0 G (if σ = 0 then 0 else 1) 0) t
          = (∫ p in Set.Icc 0 R ×ˢ Set.Icc z₁ z₂, ((p.1 * (((i : ℝ) + 1) * p.1 ^ i) * t p.2 : ℝ) : ℂ) *
              (if σ = 0 then gradMode m 0 G 1 1 p else -gradMode m 0 G 0 1 p))
            + ∫ p in Set.Icc 0 R ×ˢ Set.Icc z₁ z₂, ((p.1 * p.1 ^ i * t p.2 : ℝ) : ℂ) *
              gradMode m 0 G (if σ = 0 then 0 else 1) 0 p

namespace RelAxisInternal

lemma radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  fun_prop

lemma heightPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.heightPoly j) := by
  unfold CellBases.heightPoly
  fun_prop

lemma pow_mem_span (B : CellBases) (hlead : ∀ j, 0 < B.radialCoef j j) (i : ℕ) :
    (fun r : ℝ => r ^ i) ∈ Submodule.span ℝ ((fun j => B.radialPoly j) '' Set.Iic i) := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    have hne : B.radialCoef i i ≠ 0 := (hlead i).ne'
    have e : (fun r : ℝ => r ^ i) = (B.radialCoef i i)⁻¹ •
        (B.radialPoly i - ∑ k ∈ Finset.range i, B.radialCoef i k • (fun r : ℝ => r ^ k)) := by
      funext r
      simp only [CellBases.radialPoly, Finset.sum_range_succ, Pi.smul_apply, Pi.sub_apply,
        Finset.sum_apply, smul_eq_mul]
      field_simp
      ring
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.subset_span ⟨i, le_refl i, rfl⟩
    · refine Submodule.sum_mem _ (fun k hk => Submodule.smul_mem _ _ ?_)
      have hk' : k < i := Finset.mem_range.1 hk
      exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hk'.le)) (ih k hk')

lemma lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

lemma expand_span (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ) (g : ℝ → ℝ)
    (hg : g ∈ Submodule.span ℝ ((fun j => B.radialPoly j) '' Set.Iic Q)) :
    Continuous g ∧ g = ∑ j ∈ Finset.range (Q + 1),
      (∫ s in Set.Icc K.r₁ K.r₂, K.lineWeight s * g s * B.radialPoly j s) • B.radialPoly j := by
  have hint : ∀ (f : ℝ → ℝ), Continuous f → ∀ j,
      IntegrableOn (fun s => K.lineWeight s * f s * B.radialPoly j s) (Set.Icc K.r₁ K.r₂) := by
    intro f hf j
    exact ((lineWeight_continuous K).mul hf |>.mul (radialPoly_continuous B j)).integrableOn_Icc
  induction hg using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk, rfl⟩ := hx
    refine ⟨radialPoly_continuous B k, ?_⟩
    have hk' : k ∈ Finset.range (Q + 1) := Finset.mem_range.2 (Nat.lt_succ_of_le hk)
    simp only [hB.radial_orthonormal, ite_smul, one_smul, zero_smul]
    rw [Finset.sum_ite_eq]
    simp [hk']
  | zero =>
    refine ⟨continuous_const, ?_⟩
    simp
  | add x y _ _ hx hy =>
    refine ⟨hx.1.add hy.1, ?_⟩
    have e : ∀ j, (∫ s in Set.Icc K.r₁ K.r₂, K.lineWeight s * (x + y) s * B.radialPoly j s) =
        (∫ s in Set.Icc K.r₁ K.r₂, K.lineWeight s * x s * B.radialPoly j s) +
          ∫ s in Set.Icc K.r₁ K.r₂, K.lineWeight s * y s * B.radialPoly j s := by
      intro j
      rw [← integral_add (hint x hx.1 j) (hint y hy.1 j)]
      congr 1
      funext s
      simp only [Pi.add_apply]
      ring
    simp_rw [e, add_smul, Finset.sum_add_distrib]
    rw [← hx.2, ← hy.2]
  | smul c x _ hx =>
    refine ⟨hx.1.const_smul c, ?_⟩
    have e : ∀ j, (∫ s in Set.Icc K.r₁ K.r₂, K.lineWeight s * (c • x) s * B.radialPoly j s) =
        c * ∫ s in Set.Icc K.r₁ K.r₂, K.lineWeight s * x s * B.radialPoly j s := by
      intro j
      rw [← integral_const_mul]
      congr 1
      funext s
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    simp_rw [e, mul_smul]
    rw [← Finset.smul_sum, ← hx.2]

lemma pow_expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (hK : K.r₁ = 0) (Q i : ℕ)
    (hi : i ≤ Q) (r : ℝ) :
    ∑ j ∈ Finset.range (Q + 1),
      (∫ s in Set.Icc K.r₁ K.r₂, s * s ^ i * B.radialPoly j s) * B.radialPoly j r = r ^ i := by
  have h := (expand_span K B hB Q (fun r : ℝ => r ^ i)
    (Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hi))
      (pow_mem_span B hB.radial_leading i))).2
  have hlw : ∀ s, K.lineWeight s = s := by intro s; simp [CellBox.lineWeight, hK]
  have h2 := congrFun h r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hlw] at h2
  exact h2.symm

end RelAxisInternal


namespace RelAxisInternal

lemma coef_expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (hK : K.r₁ = 0) (Q i : ℕ)
    (hi : i ≤ Q) (F : ℝ × ℝ → ℂ) (hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) K.rect) (l : ℕ) :
    ∑ j ∈ Finset.range (Q + 1),
        ((∫ r in Set.Icc K.r₁ K.r₂, r * r ^ i * B.radialPoly j r : ℝ) : ℂ) * B.coef K F j l
      = ∫ p in K.rect, ((p.1 * p.1 ^ i * B.heightPoly l p.2 : ℝ) : ℂ) * F p := by
  have hlw : ∀ s, K.lineWeight s = s := by intro s; simp [CellBox.lineWeight, hK]
  have hcpt : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hterm : ∀ j, IntegrableOn (fun p : ℝ × ℝ =>
      (K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) K.rect := by
    intro j
    have hc : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
      have h1 := radialPoly_continuous B j
      have h2 := heightPoly_continuous B l
      fun_prop
    have := hF.mul_continuousOn hc.continuousOn hcpt
    simpa [hlw] using this
  simp only [CellBases.coef]
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum _ (fun j _ => (hterm j).const_mul _)]
  refine setIntegral_congr_fun (hcpt.isClosed.measurableSet) (fun p _ => ?_)
  rw [← pow_expand K B hB hK Q i hi p.1]
  push_cast
  rw [hlw]
  simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

lemma deriv_rpow_succ (i : ℕ) (r : ℝ) : deriv (fun r : ℝ => r * r ^ i) r = ((i : ℝ) + 1) * r ^ i := by
  have e : (fun r : ℝ => r * r ^ i) = fun r => r ^ (i + 1) := by funext r; ring
  rw [e, (hasDerivAt_pow (i + 1) r).deriv]
  push_cast
  simp

variable (L : CellLayout)

lemma ev_unit (T : L.Datum → ℂ) (d0 : L.Datum) : ∑ d, L.unitAt d0 d * T d = T d0 := by
  simp [CellLayout.unitAt, Pi.single_apply]

lemma ev_sub (T : L.Datum → ℂ) (f g : L.Datum → ℂ) :
    ∑ d, (f - g) d * T d = ∑ d, f d * T d - ∑ d, g d * T d := by
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma ev_neg (T : L.Datum → ℂ) (f : L.Datum → ℂ) : ∑ d, (-f) d * T d = -∑ d, f d * T d := by
  simp only [Pi.neg_apply, neg_mul, Finset.sum_neg_distrib]

lemma ev_smul (T : L.Datum → ℂ) (c : ℂ) (f : L.Datum → ℂ) :
    ∑ d, (c • f) d * T d = c * ∑ d, f d * T d := by
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  rw [Finset.mul_sum]

lemma ev_sum {ι : Type*} (T : L.Datum → ℂ) (s : Finset ι) (f : ι → L.Datum → ℂ) :
    ∑ d, (∑ j ∈ s, f j) d * T d = ∑ j ∈ s, ∑ d, f j d * T d := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

lemma ev_strain {k : ℕ} (x : FieldTuple k) (n : L.modes) (a b : Fin 3) (j l : ℕ)
    (hj : j < L.degCoef + 1) (hl : l < L.degCoef + 1) :
    ∑ d, L.strainAt n a b j l d * L.trueData x d = L.bases.coef L.box (L.gradModeOf n x a b) j l := by
  simp only [CellLayout.strainAt, dif_pos (And.intro hj hl)]
  rw [ev_unit]
  rfl

lemma ev_extra {k : ℕ} (x : FieldTuple k) (n : L.modes) (e : Fin 4) (a : Fin 3) (l : ℕ)
    (hl : l < L.degCoef + 1) :
    ∑ d, L.extraAt n e a l d * L.trueData x d = L.extraValue n x e a l := by
  simp only [CellLayout.extraAt, dif_pos hl]
  rw [ev_unit]
  rfl

lemma zeroMode_val (n0 : L.modes) (h : L.zeroMode = some n0) : (n0 : ℤ) = 0 := by
  unfold CellLayout.zeroMode at h
  split_ifs at h with h0
  cases h
  rfl

end RelAxisInternal

namespace RelAxisInternal

lemma hbase (L : CellLayout) (hB : IsCellBases L.box L.bases) (hK : L.box.r₁ = 0) (i l : ℕ)
    (hi : i ≤ L.degCoef) (F1 F2 : ℝ × ℝ → ℂ)
    (hF1 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F1 p) L.box.rect)
    (hF2 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F2 p) L.box.rect) (E : ℂ)
    (hflux : ((L.box.r₂ * L.box.r₂ ^ i : ℝ) : ℂ) * E =
      (∫ p in L.box.rect, ((p.1 * (((i : ℝ) + 1) * p.1 ^ i) * L.bases.heightPoly l p.2 : ℝ) : ℂ) * F1 p)
        + ∫ p in L.box.rect, ((p.1 * p.1 ^ i * L.bases.heightPoly l p.2 : ℝ) : ℂ) * F2 p) :
    ((L.box.r₂ * L.box.r₂ ^ i : ℝ) : ℂ) * E
      - ∑ j ∈ Finset.range (L.degCoef + 1),
          ((L.radialInt (fun r => r * deriv (fun r => r * r ^ i) r * L.bases.radialPoly j r) : ℝ) : ℂ)
            * L.bases.coef L.box F1 j l
      - ∑ j ∈ Finset.range (L.degCoef + 1),
          ((L.radialInt (fun r => r * r ^ i * L.bases.radialPoly j r) : ℝ) : ℂ) * L.bases.coef L.box F2 j l
      = 0 := by
  have h1 := coef_expand L.box L.bases hB hK L.degCoef i hi F1 hF1 l
  have h2 := coef_expand L.box L.bases hB hK L.degCoef i hi F2 hF2 l
  have e1 : ∀ j, L.radialInt (fun r => r * deriv (fun r => r * r ^ i) r * L.bases.radialPoly j r) =
      ((i : ℝ) + 1) * ∫ r in Set.Icc L.box.r₁ L.box.r₂, r * r ^ i * L.bases.radialPoly j r := by
    intro j
    unfold CellLayout.radialInt
    rw [← integral_const_mul]
    congr 1
    funext r
    dsimp only
    rw [deriv_rpow_succ]
    ring
  have e1' : (∫ p in L.box.rect, ((p.1 * (((i : ℝ) + 1) * p.1 ^ i) * L.bases.heightPoly l p.2 : ℝ) : ℂ) * F1 p)
      = ((i : ℂ) + 1) * ∫ p in L.box.rect, ((p.1 * p.1 ^ i * L.bases.heightPoly l p.2 : ℝ) : ℂ) * F1 p := by
    rw [← integral_const_mul]
    congr 1
    funext p
    push_cast
    ring
  have s1 : ∑ j ∈ Finset.range (L.degCoef + 1),
      ((L.radialInt (fun r => r * deriv (fun r => r * r ^ i) r * L.bases.radialPoly j r) : ℝ) : ℂ)
        * L.bases.coef L.box F1 j l
      = ((i : ℂ) + 1) * ∫ p in L.box.rect, ((p.1 * p.1 ^ i * L.bases.heightPoly l p.2 : ℝ) : ℂ) * F1 p := by
    rw [← h1, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [e1]
    push_cast
    ring
  have s2 : ∑ j ∈ Finset.range (L.degCoef + 1),
      ((L.radialInt (fun r => r * r ^ i * L.bases.radialPoly j r) : ℝ) : ℂ) * L.bases.coef L.box F2 j l
      = ∫ p in L.box.rect, ((p.1 * p.1 ^ i * L.bases.heightPoly l p.2 : ℝ) : ℂ) * F2 p := h2
  rw [s1, s2, hflux, e1']
  ring

end RelAxisInternal

namespace RelAxisInternal

variable (L : CellLayout)

lemma ev_strain_sum {k : ℕ} (x : FieldTuple k) (n : L.modes) (a b : Fin 3) (l : ℕ)
    (hl : l < L.degCoef + 1) (c : ℕ → ℂ) :
    ∑ j ∈ Finset.range (L.degCoef + 1), ∑ d, (c j • L.strainAt n a b j l) d * L.trueData x d =
      ∑ j ∈ Finset.range (L.degCoef + 1), c j * L.bases.coef L.box (L.gradModeOf n x a b) j l := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [ev_smul, ev_strain L x n a b j l (Finset.mem_range.1 hj) hl]

lemma ev_negstrain_sum {k : ℕ} (x : FieldTuple k) (n : L.modes) (a b : Fin 3) (l : ℕ)
    (hl : l < L.degCoef + 1) (c : ℕ → ℂ) :
    ∑ j ∈ Finset.range (L.degCoef + 1), ∑ d, (c j • -L.strainAt n a b j l) d * L.trueData x d =
      ∑ j ∈ Finset.range (L.degCoef + 1),
        c j * L.bases.coef L.box (fun p => -L.gradModeOf n x a b p) j l := by
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [ev_smul, ev_neg, ev_strain L x n a b j l (Finset.mem_range.1 hj) hl]
  simp only [CellBases.coef, mul_neg, neg_mul, integral_neg]

end RelAxisInternal

namespace RelAxisInternal

theorem relAxis_main (hI : AxisModeIntegrableStatement) (hF : AxisFluxStatement) {k N : ℕ}
    (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases) (L : CellLayout)
    (hL : IsCellLayout c K S B L) (x : FieldTuple k) (hx : IsAdmissible c x)
    (ρ : Fin 2 × Fin (L.degCoef + 1) × Fin (L.degCoef + 1)) :
    (∑ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr (Sum.inr
      (Sum.inl ρ)))))))) d * L.trueData x d) = 0 := by
  obtain ⟨σ, l, i⟩ := ρ
  have hB : IsCellBases L.box L.bases := by rw [hL.box_eq, hL.bases_eq]; exact hL.bases_valid
  have hbox : IsCellBox L.box := by rw [hL.box_eq]; exact hL.box_valid
  have hsec : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := by rw [hL.order_eq]; exact hx.1
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  rcases hz : L.zeroMode with _ | n0
  · simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  have hn0 := zeroMode_val L n0 hz
  dsimp only
  by_cases hK : L.box.r₁ = 0
  swap
  · simp only [if_pos hK, Pi.zero_apply, zero_mul, Finset.sum_const_zero]
  rw [if_neg (not_not.mpr hK)]
  have hl : (l : ℕ) < L.degCoef + 1 := l.2
  have hi : (i : ℕ) ≤ L.degCoef := Nat.lt_succ_iff.1 i.2
  have hr : 0 < L.box.r₂ := by have := hbox.r_order; linarith
  have hz' : L.box.z₁ < L.box.z₂ := hbox.z_order.2
  have hψ := heightPoly_continuous L.bases l
  have hflux := hF L.order x.1 x.2.1 x.2.2.1 hsec L.box.r₂ L.box.z₁ L.box.z₂ hr hz' _ hψ i σ
  have hrect : L.box.rect = Set.Icc 0 L.box.r₂ ×ˢ Set.Icc L.box.z₁ L.box.z₂ := by
    simp [CellBox.rect, hK]
  rw [← hrect] at hflux
  have hint : ∀ a b : Fin 3,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode L.order 0 x.2.1 a b p) L.box.rect := by
    intro a b
    rw [hrect]
    exact hI L.order x.1 x.2.1 x.2.2.1 hsec L.box.r₂ L.box.z₁ L.box.z₂ 0 a b
  rw [ev_sub, ev_sub, ev_smul, ev_extra _ _ _ _ _ _ hl, ev_sum, ev_sum]
  have hext : L.extraValue (n0 : ℤ) x 1 (if σ = 0 then 0 else 1) l =
      radialStripMoment L.box.r₂ 0 L.box.z₁ L.box.z₂
        (fun p => modeVec L.order 0 x.1 p.1 p.2 (if σ = 0 then 0 else 1))
        (gradMode L.order 0 x.2.1 (if σ = 0 then 0 else 1) 0) (L.bases.heightPoly l) := by
    simp [CellLayout.extraValue, CellLayout.sideTest, CellLayout.gradModeOf, hK, hn0]
    rfl
  rw [hext]
  by_cases hσ : σ = 0
  · simp only [hσ, if_true] at hflux ⊢
    rw [ev_strain_sum L x n0 1 1 l hl, ev_strain_sum L x n0 0 0 l hl]
    simp only [CellLayout.gradModeOf, hn0]
    exact hbase L hB hK i l hi _ _ (hint 1 1) (hint 0 0) _ hflux
  · simp only [hσ, if_false] at hflux ⊢
    rw [ev_negstrain_sum L x n0 0 1 l hl, ev_strain_sum L x n0 1 0 l hl]
    simp only [CellLayout.gradModeOf, hn0]
    refine hbase L hB hK i l hi _ _ ?_ (hint 1 0) _ hflux
    simpa [mul_neg] using (hint 0 1).neg

end RelAxisInternal

theorem relAxis_of (hI : AxisModeIntegrableStatement) (hF : AxisFluxStatement) : RelAxisStatement :=
  fun c K S B L hL x hx ρ => RelAxisInternal.relAxis_main hI hF c K S B L hL x hx ρ

end Breakdown.CellCert.CellFormula
