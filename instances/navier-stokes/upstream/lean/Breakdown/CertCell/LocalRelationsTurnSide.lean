import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.RelTurn
import Breakdown.FracCell.RelRadialSide
import Breakdown.FracCell.RelHeightSide

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

namespace Internal

open CellCert.CellFormula.RadialSide.Internal

theorem turn_pair_add {ι : Type*} [Fintype ι] (f g t : ι → ℂ) :
    ∑ d, (f + g) d * t d = ∑ d, f d * t d + ∑ d, g d * t d := by
  simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem turn_shift_expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q j : ℕ) (hj : j + 1 ≤ Q) :
    ∃ β : Fin (Q + 1) → ℝ, ∀ r, r * B.radialPoly j r = ∑ i, β i * B.radialPoly i r := by
  have hmem : (fun r : ℝ => r * B.radialPoly j r) ∈ polySpan B (Q + 1) := by
    have e : (fun r : ℝ => r * B.radialPoly j r) =
        ∑ i ∈ Finset.range (j + 1), B.radialCoef j i • (fun r : ℝ => r ^ (i + 1)) := by
      funext r
      simp only [CellBases.radialPoly, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e]
    exact Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
      (pow_mem K B hB (i + 1) (Q + 1) (by have := Finset.mem_range.mp hi; omega)))
  obtain ⟨β, hβ⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hmem
  refine ⟨β, fun r => ?_⟩
  have h := congrFun hβ r
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  exact h.symm

theorem turn_shift_eq (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q j : ℕ) (β : Fin (Q + 1) → ℝ)
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
    exact (((lineWeight_continuous K).mul (radialPoly_continuous B k)).mul
      (radialPoly_continuous B i)).integrableOn_Icc.const_mul _

theorem turn_basis_cont (B : CellBases) (i l : ℕ) :
    Continuous (fun p : ℝ × ℝ => ((B.radialPoly i p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) :=
  Complex.continuous_ofReal.comp (((radialPoly_continuous B i).comp continuous_fst).mul
    ((heightPoly_continuous B l).comp continuous_snd))

theorem turn_axis_null : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
  have h : ∀ᵐ r : ℝ ∂volume, r ≠ 0 := by
    rw [ae_iff]
    simp
  exact (Measure.quasiMeasurePreserving_fst (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))).ae h

theorem turn_coef_shift (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (Q j l : ℕ)
    (hj : j + 1 ≤ Q) (F V : ℝ × ℝ → ℂ)
    (hF : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hFV : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 → (p.1 : ℂ) * F p = V p) :
    ∑ i ∈ Finset.range (Q + 1),
        ((∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r : ℝ) : ℂ) *
          B.coef K F i l = B.coef K V j l := by
  obtain ⟨β, hβ⟩ := turn_shift_expand K B hB Q j hj
  rw [Finset.sum_range (fun i => ((∫ r in Set.Icc K.r₁ K.r₂,
    K.lineWeight r * r * B.radialPoly i r * B.radialPoly j r : ℝ) : ℂ) * B.coef K F i l)]
  rw [Finset.sum_congr rfl (fun i _ => by rw [turn_shift_eq K B hB Q j β hβ i])]
  unfold CellBases.coef
  simp_rw [← integral_const_mul]
  rw [← integral_finsetSum]
  · refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
    filter_upwards [hFV, turn_axis_null] with p hp hp0 hmem
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
    exact (hF.mul_continuousOn (turn_basis_cont B i l).continuousOn (rect_compact K)).const_mul _

theorem turn_coef_lin (K : CellBox) (B : CellBases) (j l : ℕ) (c s : ℂ) (V₁ V₂ : ℝ × ℝ → ℂ)
    (h₁ : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * V₁ p) K.rect)
    (h₂ : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * V₂ p) K.rect) :
    B.coef K (fun p => c * V₁ p + s * V₂ p) j l = c * B.coef K V₁ j l + s * B.coef K V₂ j l := by
  unfold CellBases.coef
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add]
  · congr 1
    funext p
    ring
  · exact (h₁.mul_continuousOn (turn_basis_cont B j l).continuousOn (rect_compact K)).const_mul _
  · exact (h₂.mul_continuousOn (turn_basis_cont B j l).continuousOn (rect_compact K)).const_mul _

end Internal

open CellCert.CellFormula.RadialSide.Internal Internal in
theorem localRelTurn_of (hI : LocalModeIntegrableStatement) (hA : LocalAngularModeStatement) :
    LocalRelTurnStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, j, l⟩ := ρ
  have hsec : IsLocalSecondOrderField x.1 x.2.1 x.2.2.1 := hx.1
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have hB : IsCellBases L.box L.bases := by
    rw [hL.box_eq, hL.bases_eq]
    exact hL.bases_valid
  have hj : (j : ℕ) + 1 ≤ L.degCoef := j.2
  have hj' : (j : ℕ) ∈ Finset.range L.degCoef := Finset.mem_range.mpr j.2
  have hl' : (l : ℕ) < L.degCoef := l.2
  have hl : (l : ℕ) < L.degCoef + 1 := by omega
  simp only [CellLayout.relationRow, Sum.elim_inl, Sum.elim_inr]
  rw [pair_sub, pair_sum, sub_eq_zero]
  simp_rw [pair_smul]
  rw [Finset.sum_congr rfl (fun i hi => by rw [pair_strain L x n a 1 i l hi hl])]
  simp only [CellLayout.radialShift, CellLayout.radialInt]
  have hI' := hI L.order x.1 x.2.1 x.2.2.1 hsec L.box hK n
  have hA' := hA L.order x.1 x.2.1 x.2.2.1 hsec n
  obtain rfl | rfl | rfl : a = 0 ∨ a = 1 ∨ a = 2 := by fin_cases a <;> simp
  · rw [turn_coef_shift L.box hK L.bases hB L.degCoef j l hj (L.gradModeOf n x 0 1)
      (fun p => ((azimuth L.order n : ℂ) * Complex.I) * L.velMode n x 0 p + (-1) * L.velMode n x 1 p)
      ((hI' 0).2 1) ?_]
    · rw [turn_coef_lin L.box L.bases j l _ _ (L.velMode n x 0) (L.velMode n x 1) (hI' 0).1 (hI' 1).1]
      simp only [CellLayout.turnRow, if_true]
      rw [pair_sub, pair_smul, pair_velocity L x n 0 j l hj' hl', pair_velocity L x n 1 j l hj' hl']
      ring
    · filter_upwards [hA'] with p hp hr
      simp only [CellLayout.velMode, CellLayout.gradModeOf]
      rw [(hp hr).1]
      ring
  · rw [turn_coef_shift L.box hK L.bases hB L.degCoef j l hj (L.gradModeOf n x 1 1)
      (fun p => ((azimuth L.order n : ℂ) * Complex.I) * L.velMode n x 1 p + 1 * L.velMode n x 0 p)
      ((hI' 1).2 1) ?_]
    · rw [turn_coef_lin L.box L.bases j l _ _ (L.velMode n x 1) (L.velMode n x 0) (hI' 1).1 (hI' 0).1]
      simp only [CellLayout.turnRow, show (1 : Fin 3) ≠ 0 by decide, if_false, if_true]
      rw [turn_pair_add, pair_smul, pair_velocity L x n 1 j l hj' hl', pair_velocity L x n 0 j l hj' hl']
      simp
    · filter_upwards [hA'] with p hp hr
      simp only [CellLayout.velMode, CellLayout.gradModeOf]
      rw [(hp hr).2.1]
      ring
  · rw [turn_coef_shift L.box hK L.bases hB L.degCoef j l hj (L.gradModeOf n x 2 1)
      (fun p => ((azimuth L.order n : ℂ) * Complex.I) * L.velMode n x 2 p + 0 * L.velMode n x 0 p)
      ((hI' 2).2 1) ?_]
    · rw [turn_coef_lin L.box L.bases j l _ _ (L.velMode n x 2) (L.velMode n x 0) (hI' 2).1 (hI' 0).1]
      simp only [CellLayout.turnRow, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide, if_false]
      rw [pair_smul, pair_velocity L x n 2 j l hj' hl']
      simp
    · filter_upwards [hA'] with p hp hr
      simp only [CellLayout.velMode, CellLayout.gradModeOf]
      rw [(hp hr).2.2]
      ring

open CellCert.CellFormula.RelHeightSideInternal in
theorem localHeightParts_of (hIbp : LocalHeightModeIbpStatement) (hI : LocalModeIntegrableStatement) :
    LocalSideHeightPartsStatement := by
  intro k N c x hx L hord K hK n a
  have hsec := hx.1
  have hIv := (hI c.order x.1 x.2.1 x.2.2.1 hsec K hK n a).1
  obtain ⟨hIg, hparts⟩ := hIbp c.order n x.1 x.2.1 x.2.2.1 hsec K hK a
  have e1 : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * L.velMode n x a p) =
      fun p => (K.lineWeight p.1 : ℂ) * modeVec c.order n x.1 p.1 p.2 a := by
    funext p
    simp only [CellLayout.velMode, hord]
  have e2 : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p) =
      fun p => (K.lineWeight p.1 : ℂ) * gradMode c.order n x.2.1 a 2 p := by
    funext p
    simp only [CellLayout.gradModeOf, hord]
  refine ⟨e1 ▸ hIv, e2 ▸ hIg, ?_⟩
  intro s φ φ' hs hφ' hd h1 h2
  have hdφ : deriv φ = φ' := funext fun z => (hd z).deriv
  have hcd : ContDiff ℝ 1 φ :=
    contDiff_one_iff_deriv.mpr ⟨fun z => (hd z).differentiableAt, hdφ ▸ hφ'⟩
  have e := hparts s φ hs hcd h1 h2
  rw [hdφ] at e
  have i1 : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * modeVec c.order n x.1 p.1 p.2 a *
      ((s p.1 * φ' p.2 : ℝ) : ℂ)) K.rect :=
    term_int hIv (by fun_prop)
  have i2 : IntegrableOn (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) * gradMode c.order n x.2.1 a 2 p *
      ((s p.1 * φ p.2 : ℝ) : ℂ)) K.rect :=
    term_int hIg (by fun_prop)
  simp only [CellLayout.velMode, CellLayout.gradModeOf, hord]
  rw [integral_add i1 i2, e]
  ring

namespace Internal

open CellCert.CellFormula.RelHeightSideInternal in
theorem height_side_of_parts (hP : LocalSideHeightPartsStatement) : LocalRelHeightSideStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, j, m⟩ := ρ
  have hK : IsCellBox L.box := by rw [hL.box_eq]; exact hL.box_valid
  have hB : IsCellBases L.box L.bases := by rw [hL.box_eq, hL.bases_eq]; exact hL.bases_valid
  have hQ1 : 1 ≤ L.degCoef := by have := hL.degSide_pos; have := hL.degSide_le; omega
  obtain ⟨hFi, hGi, hby⟩ := hP c x hx L hL.order_eq L.box hK n a
  have hz : L.box.z₁ < L.box.z₂ := hK.z_order.2
  have hh : L.box.z₂ - L.box.z₁ ≠ 0 := sub_ne_zero.mpr hz.ne'
  have hRc : Continuous (L.bases.radialPoly (j : ℕ)) := radial_cont _ _
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl, pair_sub, pair_smul, pair_sum]
  rw [pair_extra L x n 3 a j (by omega), pair_extra L x n 2 a j (by omega), sum_vel L x n a j j.2,
    sum_strain L x n a j (by omega), extra_three, extra_two,
    strip_top L.box hz _ _ _ hRc hFi hGi, strip_bottom L.box hz _ _ _ hRc hFi hGi]
  have hlead := hB.height_leading
  obtain ⟨D, hD⟩ : ∃ D, L.degCoef = D + 1 := ⟨L.degCoef - 1, by omega⟩
  have hm : (m : ℕ) ≤ L.degCoef := Nat.lt_succ_iff.mp m.2
  have hexpB : ∀ z, ∑ l ∈ Finset.range (L.degCoef + 1),
      L.heightInt (fun z => z ^ (m : ℕ) * L.bases.heightPoly l z) * L.bases.heightPoly l z = z ^ (m : ℕ) :=
    (proj_span L.box L.bases hB L.degCoef _ (pow_mem L.bases hlead m L.degCoef hm)).2
  have hexpA : ∀ z, ∑ l ∈ Finset.range L.degCoef,
      L.heightInt (fun z => deriv (fun z => z ^ (m : ℕ)) z * L.bases.heightPoly l z) * L.bases.heightPoly l z =
        deriv (fun z => z ^ (m : ℕ)) z := by
    intro z
    have hmem : (fun z : ℝ => deriv (fun z : ℝ => z ^ (m : ℕ)) z) ∈
        Submodule.span ℝ {g | ∃ l ≤ D, g = L.bases.heightPoly l} := by
      rw [deriv_pow_eq]
      exact Submodule.smul_mem _ _ (pow_mem L.bases hlead _ D (by omega))
    have := (proj_span L.box L.bases hB D _ hmem).2 z
    have hr : Finset.range L.degCoef = Finset.range (D + 1) := by rw [hD]
    rw [hr]
    exact this
  have hdc : Continuous (fun z : ℝ => deriv (fun z : ℝ => z ^ (m : ℕ)) z) := by
    rw [deriv_pow_eq]
    exact continuous_const.smul (continuous_pow _)
  have hA : ∑ l ∈ Finset.range L.degCoef,
      ((L.heightInt (fun z => deriv (fun z => z ^ (m : ℕ)) z * L.bases.heightPoly l z) : ℝ) : ℂ) *
        L.bases.coef L.box (L.velMode n x a) j l =
      J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.velMode n x a p)
        (fun p => L.bases.radialPoly j p.1 * deriv (fun z => z ^ (m : ℕ)) p.2) := by
    refine (Finset.sum_congr rfl (fun l _ => (J_smul L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.velMode n x a p)
      (L.heightInt (fun z => deriv (fun z => z ^ (m : ℕ)) z * L.bases.heightPoly l z))
      (fun p => L.bases.radialPoly j p.1 * L.bases.heightPoly l p.2)).symm)).trans ?_
    rw [← J_sum hFi (Finset.range L.degCoef)
      (fun l p => L.heightInt (fun z => deriv (fun z => z ^ (m : ℕ)) z * L.bases.heightPoly l z) *
        (L.bases.radialPoly j p.1 * L.bases.heightPoly l p.2))
      (fun l => continuous_const.mul ((hRc.comp continuous_fst).mul ((height_cont _ l).comp continuous_snd)))]
    congr 1
    funext p
    rw [← hexpA p.2, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  have hBs : ∑ l ∈ Finset.range (L.degCoef + 1),
      ((L.heightInt (fun z => z ^ (m : ℕ) * L.bases.heightPoly l z) : ℝ) : ℂ) *
        L.bases.coef L.box (L.gradModeOf n x a 2) j l =
      J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
        (fun p => L.bases.radialPoly j p.1 * p.2 ^ (m : ℕ)) := by
    refine (Finset.sum_congr rfl (fun l _ => (J_smul L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
      (L.heightInt (fun z => z ^ (m : ℕ) * L.bases.heightPoly l z))
      (fun p => L.bases.radialPoly j p.1 * L.bases.heightPoly l p.2)).symm)).trans ?_
    rw [← J_sum hGi (Finset.range (L.degCoef + 1))
      (fun l p => L.heightInt (fun z => z ^ (m : ℕ) * L.bases.heightPoly l z) *
        (L.bases.radialPoly j p.1 * L.bases.heightPoly l p.2))
      (fun l => continuous_const.mul ((hRc.comp continuous_fst).mul ((height_cont _ l).comp continuous_snd)))]
    congr 1
    funext p
    rw [← hexpB p.2, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [hA, hBs]
  have hφd : ∀ z : ℝ, HasDerivAt (fun z : ℝ => z ^ (m : ℕ) -
      ((L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁) * z +
        (L.box.z₁ ^ (m : ℕ) * L.box.z₂ - L.box.z₂ ^ (m : ℕ) * L.box.z₁) / (L.box.z₂ - L.box.z₁)))
      (deriv (fun z : ℝ => z ^ (m : ℕ)) z - (L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁)) z := by
    intro z
    rw [(hasDerivAt_pow (m : ℕ) z).deriv]
    have := (hasDerivAt_pow (m : ℕ) z).sub (((hasDerivAt_id' (x := z)).const_mul
      ((L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁))).add_const
      ((L.box.z₁ ^ (m : ℕ) * L.box.z₂ - L.box.z₂ ^ (m : ℕ) * L.box.z₁) / (L.box.z₂ - L.box.z₁)))
    exact this.congr_deriv (by ring)
  have hφ1 : L.box.z₁ ^ (m : ℕ) -
      ((L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁) * L.box.z₁ +
        (L.box.z₁ ^ (m : ℕ) * L.box.z₂ - L.box.z₂ ^ (m : ℕ) * L.box.z₁) / (L.box.z₂ - L.box.z₁)) = 0 := by
    field_simp
    ring
  have hφ2 : L.box.z₂ ^ (m : ℕ) -
      ((L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁) * L.box.z₂ +
        (L.box.z₁ ^ (m : ℕ) * L.box.z₂ - L.box.z₂ ^ (m : ℕ) * L.box.z₁) / (L.box.z₂ - L.box.z₁)) = 0 := by
    field_simp
    ring
  have key := hby (L.bases.radialPoly j) _ _ hRc (hdc.sub continuous_const) hφd hφ1 hφ2
  have key' : J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.velMode n x a p)
      (fun p => L.bases.radialPoly j p.1 * (deriv (fun z : ℝ => z ^ (m : ℕ)) p.2 -
        (L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁)))
      + J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
      (fun p => L.bases.radialPoly j p.1 * (p.2 ^ (m : ℕ) -
        ((L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁) * p.2 +
          (L.box.z₁ ^ (m : ℕ) * L.box.z₂ - L.box.z₂ ^ (m : ℕ) * L.box.z₁) / (L.box.z₂ - L.box.z₁)))) = 0 := by
    unfold J
    rw [← integral_add (term_int hFi (by fun_prop)) (term_int hGi (by fun_prop))]
    exact key
  have lF : J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.velMode n x a p)
      (fun p => L.bases.radialPoly j p.1 * (deriv (fun z : ℝ => z ^ (m : ℕ)) p.2 -
        (L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁))) =
      ((1 : ℝ) : ℂ) * J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.velMode n x a p)
        (fun p => L.bases.radialPoly j p.1 * deriv (fun z => z ^ (m : ℕ)) p.2)
      + ((-(L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) : ℝ) : ℂ) *
        J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.velMode n x a p)
          (fun p => L.bases.radialPoly j p.1 / (L.box.z₂ - L.box.z₁)) := by
    rw [← J_lin hFi (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    ring
  have lG : J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
      (fun p => L.bases.radialPoly j p.1 * (p.2 ^ (m : ℕ) -
        ((L.box.z₂ ^ (m : ℕ) - L.box.z₁ ^ (m : ℕ)) / (L.box.z₂ - L.box.z₁) * p.2 +
          (L.box.z₁ ^ (m : ℕ) * L.box.z₂ - L.box.z₂ ^ (m : ℕ) * L.box.z₁) / (L.box.z₂ - L.box.z₁)))) =
      ((1 : ℝ) : ℂ) * J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
        (fun p => L.bases.radialPoly j p.1 * p.2 ^ (m : ℕ))
      + ((-(L.box.z₂ ^ (m : ℕ)) : ℝ) : ℂ) * J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
          (fun p => L.bases.radialPoly j p.1 * (p.2 - L.box.z₁) / (L.box.z₂ - L.box.z₁))
      + ((L.box.z₁ ^ (m : ℕ) : ℝ) : ℂ) * J L.box (fun p => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p)
          (fun p => L.bases.radialPoly j p.1 * (p.2 - L.box.z₂) / (L.box.z₂ - L.box.z₁)) := by
    rw [← J_lin3 hGi (by fun_prop) (by fun_prop) (by fun_prop)]
    congr 1
    funext p
    field_simp
    ring
  push_cast at lF lG ⊢
  linear_combination (-1 : ℂ) * key' + lF + lG

end Internal

theorem localRelHeightSide_of (hIbp : LocalHeightModeIbpStatement) (hI : LocalModeIntegrableStatement) :
    LocalRelHeightSideStatement :=
  Internal.height_side_of_parts (localHeightParts_of hIbp hI)

end Breakdown.CertCell.LocalField
