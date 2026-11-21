import Breakdown.FracCell.StAngularMode

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

private lemma pair_sub {ι : Type*} [Fintype ι] (f g t : ι → ℂ) :
    ∑ d, (f - g) d * t d = ∑ d, f d * t d - ∑ d, g d * t d := by
  simp only [Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

private lemma pair_add {ι : Type*} [Fintype ι] (f g t : ι → ℂ) :
    ∑ d, (f + g) d * t d = ∑ d, f d * t d + ∑ d, g d * t d := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

private lemma pair_smul {ι : Type*} [Fintype ι] (c : ℂ) (f t : ι → ℂ) :
    ∑ d, (c • f) d * t d = c * ∑ d, f d * t d := by
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

private lemma pair_sum {ι κ : Type*} [Fintype ι] (s : Finset κ) (f : κ → ι → ℂ) (t : ι → ℂ) :
    ∑ d, (∑ i ∈ s, f i) d * t d = ∑ i ∈ s, ∑ d, f i d * t d := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

private lemma pair_single {ι : Type*} [Fintype ι] [DecidableEq ι] (d0 : ι) (t : ι → ℂ) :
    ∑ d, (Pi.single d0 (1 : ℂ) : ι → ℂ) d * t d = t d0 := by
  simp [Pi.single_apply]

private lemma pair_strain (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (a b : Fin 3) (i l : ℕ)
    (hi : i < L.degCoef + 1) (hl : l < L.degCoef + 1) :
    ∑ d, L.strainAt n a b i l d * L.trueData x d = L.bases.coef L.box (L.gradModeOf n x a b) i l := by
  rw [CellLayout.strainAt, dif_pos ⟨hi, hl⟩, CellLayout.unitAt, pair_single]
  rfl

private lemma pair_velocity (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (a : Fin 3) (j l : ℕ)
    (hj : j < L.degCoef) (hl : l < L.degCoef) :
    ∑ d, L.velocityAt n a j l d * L.trueData x d = L.bases.coef L.box (L.velMode n x a) j l := by
  rw [CellLayout.velocityAt, dif_pos ⟨hj, hl⟩, CellLayout.unitAt, pair_single]
  rfl

private lemma mono_mem (B : CellBases) (hB : ∀ j, B.radialCoef j j ≠ 0) (Q : ℕ) :
    ∀ d, d ≤ Q → (fun r : ℝ => r ^ d) ∈
      Submodule.span ℝ (Set.range (fun i : Fin (Q + 1) => B.radialPoly (i : ℕ))) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro hd
    have key : (fun r : ℝ => r ^ d) = (B.radialCoef d d)⁻¹ •
        (B.radialPoly d - ∑ i ∈ Finset.range d, B.radialCoef d i • (fun r : ℝ => r ^ i)) := by
      funext r
      simp only [Pi.smul_apply, Pi.sub_apply, Finset.sum_apply, smul_eq_mul, CellBases.radialPoly,
        Finset.sum_range_succ]
      rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ (hB d), one_mul]
    rw [key]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · exact Submodule.subset_span ⟨⟨d, by omega⟩, rfl⟩
    · exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
        (ih i (Finset.mem_range.mp hi) (by have := Finset.mem_range.mp hi; omega)))

private lemma shift_expand (B : CellBases) (hB : ∀ j, B.radialCoef j j ≠ 0) (Q j : ℕ) (hj : j + 1 ≤ Q) :
    ∃ β : Fin (Q + 1) → ℝ, ∀ r, r * B.radialPoly j r = ∑ i, β i * B.radialPoly i r := by
  have hmem : (fun r : ℝ => r * B.radialPoly j r) ∈
      Submodule.span ℝ (Set.range (fun i : Fin (Q + 1) => B.radialPoly (i : ℕ))) := by
    have e : (fun r : ℝ => r * B.radialPoly j r) =
        ∑ i ∈ Finset.range (j + 1), B.radialCoef j i • (fun r : ℝ => r ^ (i + 1)) := by
      funext r
      simp only [CellBases.radialPoly, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
      (mono_mem B hB Q (i + 1) (by have := Finset.mem_range.mp hi; omega)))
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨β, fun r => ?_⟩
  have h := congrFun hβ r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

private lemma radialPoly_cont (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  fun_prop

private lemma heightPoly_cont (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  fun_prop

private lemma lineWeight_cont (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  by_cases h : K.r₁ = 0
  · simp only [h, if_true]
    fun_prop
  · simp only [h, if_false]
    fun_prop

private lemma shift_eq (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q j : ℕ) (β : Fin (Q + 1) → ℝ)
    (hβ : ∀ r, r * B.radialPoly j r = ∑ i, β i * B.radialPoly i r) (i : Fin (Q + 1)) :
    ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r = β i := by
  have h1 : ∀ r, K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r =
      ∑ k, β k * (K.lineWeight r * B.radialPoly k r * B.radialPoly i r) := by
    intro r
    rw [show K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r =
      K.lineWeight r * B.radialPoly i r * (r * B.radialPoly j r) by ring, hβ, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  simp_rw [h1]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, hB.radial_orthonormal]
    simp [Fin.val_inj]
  · intro k _
    exact (((lineWeight_cont K).mul (radialPoly_cont B k)).mul (radialPoly_cont B i)).integrableOn_Icc.const_mul _

private lemma rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

private lemma basis_cont (B : CellBases) (i l : ℕ) :
    Continuous (fun p : ℝ × ℝ => ((B.radialPoly i p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (((radialPoly_cont B i).comp continuous_fst).mul
    ((heightPoly_cont B l).comp continuous_snd))

private lemma axis_null : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

private lemma coef_shift (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (Q j l : ℕ)
    (hj : j + 1 ≤ Q) (F V : ℝ × ℝ → ℂ)
    (hF : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hFV : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * F p = V p) :
    ∑ i ∈ Finset.range (Q + 1),
        ((∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r : ℝ) : ℂ) *
          B.coef K F i l = B.coef K V j l := by
  obtain ⟨β, hβ⟩ := shift_expand B (fun j => (hB.radial_leading j).ne') Q j hj
  rw [Finset.sum_range (fun i => ((∫ r in Set.Icc K.r₁ K.r₂,
    K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r : ℝ) : ℂ) * B.coef K F i l)]
  rw [Finset.sum_congr rfl (fun i _ => by rw [shift_eq K B hB Q j β hβ i])]
  unfold CellBases.coef
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
    filter_upwards [hFV, axis_null] with p hp hp0 hmem
    have hr : 0 < p.1 :=
      lt_of_le_of_ne (le_trans hK.r_order.1 (Set.mem_prod.mp hmem).1.1) (Ne.symm hp0)
    rw [← hp hr]
    have e : ((p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) =
        ∑ i, (β i : ℂ) * ((B.radialPoly i p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
      rw [hβ p.1]
      push_cast
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    calc ∑ i, (β i : ℂ) * ((K.lineWeight p.1 : ℂ) * F p * ((B.radialPoly i p.1 * B.heightPoly l p.2 : ℝ) : ℂ))
        = (K.lineWeight p.1 : ℂ) * F p *
            ∑ i, (β i : ℂ) * ((B.radialPoly i p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun i _ => by ring)
      _ = (K.lineWeight p.1 : ℂ) * F p * ((p.1 * B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
          rw [e]
      _ = (K.lineWeight p.1 : ℂ) * ((p.1 : ℂ) * F p) * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) := by
          push_cast
          ring
  · intro i _
    exact (hF.mul_continuousOn (basis_cont B i l).continuousOn (rect_compact K)).const_mul _

private lemma coef_lin (K : CellBox) (B : CellBases) (j l : ℕ) (c s : ℂ) (V₁ V₂ : ℝ × ℝ → ℂ)
    (h₁ : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * V₁ p) K.rect)
    (h₂ : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * V₂ p) K.rect) :
    B.coef K (fun p => c * V₁ p + s * V₂ p) j l = c * B.coef K V₁ j l + s * B.coef K V₂ j l := by
  unfold CellBases.coef
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · congr 1
    funext p
    ring
  · exact (h₁.mul_continuousOn (basis_cont B j l).continuousOn (rect_compact K)).const_mul _
  · exact (h₂.mul_continuousOn (basis_cont B j l).continuousOn (rect_compact K)).const_mul _

theorem relTurn_of (hI : ModeIntegrableStatement) (hA : AngularModeStatement) : RelTurnStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, j, l⟩ := ρ
  have hsec : IsSecondOrderField L.order x.1 x.2.1 x.2.2.1 := hL.order_eq ▸ hx.1
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have hB : IsCellBases L.box L.bases := by
    rw [hL.box_eq, hL.bases_eq]
    exact hL.bases_valid
  have hj : (j : ℕ) + 1 ≤ L.degCoef := j.2
  have hj' : (j : ℕ) < L.degCoef := j.2
  have hl' : (l : ℕ) < L.degCoef := l.2
  have hl : (l : ℕ) < L.degCoef + 1 := by omega
  simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
  rw [pair_sub, pair_sum, sub_eq_zero]
  simp_rw [pair_smul]
  rw [Finset.sum_congr rfl (fun i hi => by rw [pair_strain L x n a 1 i l (Finset.mem_range.mp hi) hl])]
  simp only [CellLayout.radialShift, CellLayout.radialInt]
  have hI' := hI L.order x.1 x.2.1 x.2.2.1 hsec L.box hK n
  have hA' := hA L.order x.1 x.2.1 x.2.2.1 hsec n
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · rw [coef_shift L.box hK L.bases hB L.degCoef j l hj (L.gradModeOf n x 0 1)
      (fun p => ((azimuth L.order n : ℂ) * Complex.I) * L.velMode n x 0 p + (-1) * L.velMode n x 1 p)
      ((hI' 0).2 1) ?_]
    · rw [coef_lin L.box L.bases j l _ _ (L.velMode n x 0) (L.velMode n x 1) (hI' 0).1 (hI' 1).1]
      simp only [CellLayout.turnRow, if_true]
      rw [pair_sub, pair_smul, pair_velocity L x n 0 j l hj' hl', pair_velocity L x n 1 j l hj' hl']
      ring
    · filter_upwards [hA'] with p hp hr
      simp only [CellLayout.velMode, CellLayout.gradModeOf]
      rw [(hp hr).1]
      ring
  · rw [coef_shift L.box hK L.bases hB L.degCoef j l hj (L.gradModeOf n x 1 1)
      (fun p => ((azimuth L.order n : ℂ) * Complex.I) * L.velMode n x 1 p + 1 * L.velMode n x 0 p)
      ((hI' 1).2 1) ?_]
    · rw [coef_lin L.box L.bases j l _ _ (L.velMode n x 1) (L.velMode n x 0) (hI' 1).1 (hI' 0).1]
      simp only [CellLayout.turnRow, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true]
      rw [pair_add, pair_smul, pair_velocity L x n 1 j l hj' hl', pair_velocity L x n 0 j l hj' hl']
      simp
    · filter_upwards [hA'] with p hp hr
      simp only [CellLayout.velMode, CellLayout.gradModeOf]
      rw [(hp hr).2.1]
      ring
  · rw [coef_shift L.box hK L.bases hB L.degCoef j l hj (L.gradModeOf n x 2 1)
      (fun p => ((azimuth L.order n : ℂ) * Complex.I) * L.velMode n x 2 p + 0 * L.velMode n x 0 p)
      ((hI' 2).2 1) ?_]
    · rw [coef_lin L.box L.bases j l _ _ (L.velMode n x 2) (L.velMode n x 0) (hI' 2).1 (hI' 0).1]
      simp only [CellLayout.turnRow, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
      rw [pair_smul, pair_velocity L x n 2 j l hj' hl']
      simp
    · filter_upwards [hA'] with p hp hr
      simp only [CellLayout.velMode, CellLayout.gradModeOf]
      rw [(hp hr).2.2]
      ring

end CellFormula

end CellCert

end Breakdown
