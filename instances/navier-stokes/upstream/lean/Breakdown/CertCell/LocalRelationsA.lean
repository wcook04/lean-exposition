import Breakdown.CertCell.LocalFieldDefs
import Breakdown.FracCell.RelRadialCoef
import Breakdown.FracCell.ModeRadialPartsF
import Breakdown.FracCell.RelHeightCoef
import Breakdown.FracCell.RelTrace
import Breakdown.FracCell.RelZeroMode
import Breakdown.FracCell.RelRadialSide

open MeasureTheory Polynomial Set Filter

noncomputable section

namespace Breakdown.CertCell.LocalField

open SteadyCert CellCert CellCert.Assembly CellCert.CellAnalysis CellCert.CellFormula

open CellCert.CellFormula.Internal.RelRadialCoef in
theorem localRelRadialCoef : LocalRelRadialCoefStatement := by
  have h : CellFormula.ModeRadialPartsStatement := CellFormula.modeRadialParts
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, j, l⟩ := ρ
  have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
  have hB : IsCellBases L.box L.bases := by
    rw [hL.box_eq, hL.bases_eq]
    exact hL.bases_valid
  simp only [CellLayout.relationRow, Sum.elim_inl]
  split_ifs with hj0
  · simp
  · obtain ⟨hI, hP⟩ := h L.order x.1 x.2.1 hx.1.measurable_velocity hx.1.velocity_six
      hx.1.measurable_gradient hx.1.gradient_two hx.1.weak_gradient n a L.box.r₁ L.box.r₂ L.box.z₁ L.box.z₂
      hK.r_order.1 hK.r_order.2 hK.z_order.2
    have hq : Continuous (L.bases.heightPoly l) := by
      unfold CellBases.heightPoly
      fun_prop
    have hint : ∀ i, IntegrableOn (fun p : ℝ × ℝ => (L.box.lineWeight p.1 : ℂ) * L.gradModeOf n x a 0 p *
        ((L.bases.radialPoly i p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ)) L.box.rect := by
      intro i
      by_cases h0 : L.box.r₁ = 0
      · have := hI (L.bases.radialPoly i) (L.bases.heightPoly l)
          (by rw [poly_fun]; exact (Polynomial.continuous _).continuousOn) hq
        refine this.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        simp only [CellBox.lineWeight, h0, if_true, CellLayout.gradModeOf]
        push_cast
        ring
      · have hpos : 0 < L.box.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)
        have := hI (fun r => L.bases.radialPoly i r / r) (L.bases.heightPoly l)
          (by
            rw [poly_fun]
            exact ContinuousOn.div (Polynomial.continuous _).continuousOn continuousOn_id
              (fun r hr => (lt_of_lt_of_le hpos hr.1).ne')) hq
        refine this.congr_fun (fun p hp => ?_) (measurableSet_Icc.prod measurableSet_Icc)
        have hp1 : p.1 ≠ 0 := (lt_of_lt_of_le hpos hp.1.1).ne'
        have hp1' : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp1
        simp only [CellBox.lineWeight, h0, if_false, CellLayout.gradModeOf]
        push_cast
        field_simp
        try ring
    have hparts : ∀ ψ : ℝ → ℝ, ContDiff ℝ 1 ψ → ψ L.box.r₁ = 0 → ψ L.box.r₂ = 0 →
        ∫ p in L.box.rect, ((ψ p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * L.gradModeOf n x a 0 p =
          -∫ p in L.box.rect, ((deriv ψ p.1 * L.bases.heightPoly l p.2 : ℝ) : ℂ) * L.velMode n x a p :=
      fun ψ hψ h1 h2 => hP ψ (L.bases.heightPoly l) hψ hq h1 h2
    have hkey := key L hK hB j l (fun h' => hj0 h') j.isLt (L.velMode n x a) (L.gradModeOf n x a 0) hint hparts
    have hv : ∑ d, L.velocityAt n a j l d * L.trueData x d = L.bases.coef L.box (L.velMode n x a) j l := by
      unfold CellLayout.velocityAt
      rw [dif_pos ⟨j.isLt, l.isLt⟩, sum_unit]
      rfl
    have hs : ∀ i ∈ Finset.range (L.degCoef + 1), ∑ d, L.strainAt n a 0 i l d * L.trueData x d =
        L.bases.coef L.box (L.gradModeOf n x a 0) i l := by
      intro i hi
      unfold CellLayout.strainAt
      rw [dif_pos ⟨Finset.mem_range.1 hi, by omega⟩, sum_unit]
      rfl
    have hsplit : ∀ d, (L.velocityAt n a j l - ∑ i ∈ Finset.range (L.degCoef + 1),
        (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) • L.strainAt n a 0 i l) d * L.trueData x d =
        L.velocityAt n a j l d * L.trueData x d - ∑ i ∈ Finset.range (L.degCoef + 1),
          (((L.radialStiff j i / radialEigen L.box j : ℝ)) : ℂ) * (L.strainAt n a 0 i l d * L.trueData x d) := by
      intro d
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, sub_mul, Finset.sum_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => by ring)
    rw [Finset.sum_congr rfl (fun d _ => hsplit d), Finset.sum_sub_distrib, Finset.sum_comm]
    simp_rw [← Finset.mul_sum]
    rw [hv, Finset.sum_congr rfl (fun i hi => by rw [hs i hi]), hkey, sub_self]

namespace Internal

open CellCert.CellFormula.Internal.RelHeightCoef in
theorem coef_height_local (hIbp : LocalHeightModeIbpStatement) {m : ℕ} {n : ℤ} {v : Space → Space}
    {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsLocalSecondOrderField v G H) {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B)
    (a : Fin 3) (j : ℕ) {l Q : ℕ} (hl : 1 ≤ l) (hlQ : l + 1 ≤ Q) :
    B.coef K (fun p => modeVec m n v p.1 p.2 a) j l =
      ∑ i ∈ Finset.range (Q + 1),
        (((∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) /
          heightEigen K l : ℝ) : ℂ) * B.coef K (gradMode m n G a 2) j i := by
  have hlead : ∀ l, B.heightCoef l l ≠ 0 := fun l => (hB.height_leading l).ne'
  have hz : K.z₁ < K.z₂ := hK.z_order.2
  have hpe : ∀ l z, (hp B.heightCoef l).eval z = B.heightPoly l z := by
    intro l z
    rw [hp_eval]
    rfl
  have hpf : ∀ l, B.heightPoly l = fun z => (hp B.heightCoef l).eval z := fun l => funext fun z => (hpe l z).symm
  have horth : ∀ l l', ∫ z in K.z₁..K.z₂, (hp B.heightCoef l).eval z * (hp B.heightCoef l').eval z =
      if l = l' then 1 else 0 := by
    intro l l'
    simp only [hpe]
    rw [intervalIntegral.integral_of_le hz.le, ← integral_Icc_eq_integral_Ioc]
    exact hB.height_orthonormal l l'
  have hstiff : ∀ i, ∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z =
      ∫ z in K.z₁..K.z₂, (gp B.heightCoef K.z₁ K.z₂ l).eval z * (hp B.heightCoef i).eval z := by
    intro i
    rw [intervalIntegral.integral_of_le hz.le, ← integral_Icc_eq_integral_Ioc]
    refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
    rw [hpf l, Polynomial.deriv, ← hpe i]
    simp only [gp, eval_mul, zp_eval, CellBox.refZ]
  have hR : Continuous (B.radialPoly j) := by
    unfold CellBases.radialPoly
    fun_prop
  have hH : ∀ i, Continuous (B.heightPoly i) := fun i => by
    rw [hpf i]
    exact (hp B.heightCoef i).continuous
  set g : ℝ → ℝ := fun z => (gp B.heightCoef K.z₁ K.z₂ l).eval z with hgdef
  have hgz1 : g K.z₁ = 0 := by simp [g, gp, zp_left hz]
  have hgz2 : g K.z₂ = 0 := by simp [g, gp, zp_right hz]
  have hderiv : ∀ z, deriv g z = (derivative (gp B.heightCoef K.z₁ K.z₂ l)).eval z := fun z => Polynomial.deriv _
  have hg1 : ContDiff ℝ 1 g := contDiff_one_iff_deriv.2 ⟨(gp B.heightCoef K.z₁ K.z₂ l).differentiable, by
    rw [show deriv g = fun z => (derivative (gp B.heightCoef K.z₁ K.z₂ l)).eval z from funext hderiv]
    exact Polynomial.continuous _⟩
  obtain ⟨hint, hibp⟩ := hIbp m n v G H hv K hK a
  have key := hibp (B.radialPoly j) g hR hg1 hgz1 hgz2
  have heig : heightEigen K l = (l : ℝ) * (l + 1) * (2 / (K.z₂ - K.z₁)) ^ 2 := rfl
  have e1 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
      ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) =
      ((-(1 / heightEigen K l) : ℝ) : ℂ) * ((K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a *
        ((B.radialPoly j p.1 * deriv g p.2 : ℝ) : ℂ)) := by
    intro p
    rw [← hpe, hp_of_gp hlead horth hz hl, hderiv, heig]
    push_cast
    ring
  have hexp : ∀ z, g z = ∑ i ∈ Finset.range (Q + 1),
      (∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) *
        B.heightPoly i z := by
    intro z
    show (gp B.heightCoef K.z₁ K.z₂ l).eval z = _
    rw [gp_expand hlead horth hlQ z]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [hstiff i, hpe]
  have e2 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((B.radialPoly j p.1 * g p.2 : ℝ) : ℂ) =
      ∑ i ∈ Finset.range (Q + 1),
        (((∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) : ℝ) : ℂ) *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((B.radialPoly j p.1 * B.heightPoly i p.2 : ℝ) : ℂ)) := by
    intro p
    rw [hexp p.2, Finset.mul_sum]
    push_cast
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hintI : ∀ i ∈ Finset.range (Q + 1), Integrable (fun p : ℝ × ℝ =>
      (((∫ z in Set.Icc K.z₁ K.z₂, (1 - K.refZ z ^ 2) * deriv (B.heightPoly l) z * B.heightPoly i z) : ℝ) : ℂ) *
          ((K.lineWeight p.1 : ℂ) * gradMode m n G a 2 p * ((B.radialPoly j p.1 * B.heightPoly i p.2 : ℝ) : ℂ)))
        (volume.restrict K.rect) := by
    intro i _
    refine Integrable.const_mul ?_ _
    have hc : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly i p.2 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((hR.comp continuous_fst).mul ((hH i).comp continuous_snd))
    exact hint.mul_continuousOn hc.continuousOn hcomp
  unfold CellBases.coef
  rw [integral_congr_ae (ae_of_all _ e1), integral_const_mul, key, integral_congr_ae (ae_of_all _ e2),
    integral_finsetSum _ hintI, mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [integral_const_mul]
  push_cast
  ring

open CellCert.CellFormula.Internal.RelHeightCoef in
theorem height_row_local (hIbp : LocalHeightModeIbpStatement) {k N : ℕ} (c : FracCellData k N) (K : CellBox)
    (S : CellScalars) (B : CellBases) (L : CellLayout) (hL : IsCellLayout c K S B L) (x : FieldTuple k)
    (hx : IsLocalAdmissible x) (ρ : L.modes × Fin 3 × Fin L.degCoef × Fin L.degCoef) :
    (∑ d, L.relationRow (Sum.inr (Sum.inl ρ)) d * L.trueData x d) = 0 := by
  obtain ⟨n, a, j, l⟩ := ρ
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  split_ifs with hl0
  · simp
  have hj := j.isLt
  have hl := l.isLt
  rw [pair_sub]
  have hv : L.velocityAt n a j l = L.unitAt (CellDatum.lowVelocity n a ⟨j, hj⟩ ⟨l, hl⟩) := by
    unfold CellLayout.velocityAt
    rw [dif_pos ⟨hj, hl⟩]
  have hs : ∀ i ∈ Finset.range (L.degCoef + 1), ∑ d, L.strainAt n a 2 j i d * L.trueData x d =
      L.bases.coef L.box (L.gradModeOf n x a 2) j i := by
    intro i hi
    unfold CellLayout.strainAt
    rw [dif_pos ⟨by omega, Finset.mem_range.1 hi⟩, pair_unit]
    rfl
  rw [hv, pair_unit, Finset.sum_congr rfl (fun i hi => by rw [hs i hi])]
  have hT : L.trueData x (CellDatum.lowVelocity n a ⟨j, hj⟩ ⟨l, hl⟩) =
      L.bases.coef L.box (fun p => modeVec L.order n x.1 p.1 p.2 a) j l := rfl
  rw [hT, sub_eq_zero]
  rw [coef_height_local hIbp (m := L.order) hx.1 (hL.box_eq ▸ hL.box_valid)
    (hL.box_eq ▸ hL.bases_eq ▸ hL.bases_valid) a j
    (Nat.one_le_iff_ne_zero.2 hl0) (by omega : (l : ℕ) + 1 ≤ L.degCoef)]
  rfl

theorem ae_first_ne_zero : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
  rw [ae_iff]
  have hs : {p : ℝ × ℝ | ¬ p.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (univ : Set ℝ) := by
    ext p; simp
  rw [hs, Measure.volume_eq_prod, Measure.prod_prod]
  simp

end Internal

theorem localRelHeightCoef_of (hIbp : LocalHeightModeIbpStatement) : LocalRelHeightCoefStatement :=
  fun c K S B L hL x hx ρ => Internal.height_row_local hIbp c K S B L hL x hx ρ

theorem localRelTrace : LocalRelTraceStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, j, l⟩ := ρ
  have hrow : ∀ d, L.relationRow (Sum.inr (Sum.inr (Sum.inr (Sum.inl (n, j, l))))) d =
      ∑ a : Fin 3, L.unitAt (CellDatum.lowStrain n a a j l) d := by
    intro d
    simp only [CellLayout.relationRow, CellLayout.strainAt, Sum.elim_inr, Sum.elim_inl, j.isLt, l.isLt, and_self,
      dif_pos, Fin.eta, Finset.sum_apply]
  simp only [hrow, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [CellLayout.unitAt, Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  simp only [CellLayout.trueData, CellDatum.lowStrain, Sum.elim_inl, CellLayout.gradModeOf]
  have hK : IsCellBox L.box := by rw [hL.box_eq]; exact hL.box_valid
  exact CellCert.CellFormula.Internal.RelTrace.trace_coef L.order n x.2.1 hx.1.measurable_gradient
    hx.1.gradient_two hx.1.divergence L.box hK L.bases j l

open CellCert.CellFormula.Internal.RelZeroMode in
theorem localRelZeroMode : LocalRelZeroModeStatement := by
  intro k N c K S B L hL x hx ρ
  have hsec := hx.1
  have hr0 : 0 ≤ L.box.r₁ := by rw [hL.box_eq]; exact hL.box_valid.r_order.1
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  cases hz : L.zeroMode with
  | none => simp
  | some n0 =>
    have hn0 : (n0 : ℤ) = 0 := by
      unfold CellLayout.zeroMode at hz
      split_ifs at hz with hm
      rw [← Option.some.inj hz]
    simp only [CellLayout.strainAt, dif_pos (And.intro ρ.1.isLt ρ.2.isLt), CellLayout.unitAt,
      Pi.single_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    simp only [CellLayout.trueData, CellDatum.lowStrain, Sum.elim_inl, CellBases.coef,
      CellLayout.gradModeOf, gradMode, hn0]
    refine integral_eq_zero_of_ae ?_
    rw [EventuallyEq]
    refine (ae_restrict_iff' (measurableSet_Icc.prod measurableSet_Icc : MeasurableSet L.box.rect)).mpr ?_
    filter_upwards [mode_zero hsec.velocity_six hsec.measurable_gradient hsec.gradient_two hsec.weak_gradient
      L.order, Internal.ae_first_ne_zero] with p hp hne hpr
    have hpos : 0 < p.1 := lt_of_le_of_ne (hr0.trans hpr.1.1) (Ne.symm hne)
    simp [hp hpos]

open CellCert.CellFormula.RadialSide.Internal in
theorem localRelRadialSide_of (h : LocalModeRadialWeakStatement) : LocalRelRadialSideStatement := by
  intro k N c K S B L hL x hx ρ
  obtain ⟨n, a, l, i⟩ := ρ
  simp only [CellLayout.relationRow, Sum.elim_inr, Sum.elim_inl]
  split_ifs with hax
  · simp
  · have hK : IsCellBox L.box := hL.box_eq ▸ hL.box_valid
    have hB : IsCellBases L.box L.bases := by
      rw [hL.box_eq, hL.bases_eq]
      exact hL.bases_valid
    obtain ⟨hF, hdF, hcore⟩ := h L.box hK L.order x.1 x.2.1 x.2.2.1 hx.1 n a
    have hl := l.isLt
    have hil := i.isLt
    simp only [pair_sub, pair_smul, pair_sum]
    rw [pair_extra L x n 1 a l (by omega), pair_extra L x n 0 a l (by omega), extra_one, extra_zero]
    have hv : ∀ (cf : ℕ → ℂ), ∑ j ∈ Finset.range L.degCoef, cf j * ∑ u, L.velocityAt n a j l u * L.trueData x u =
        ∑ j ∈ Finset.range L.degCoef, cf j * L.bases.coef L.box (L.velMode n x a) j l :=
      fun cf => Finset.sum_congr rfl (fun j hj => by rw [pair_velocity L x n a j l hj hl])
    have hs : ∀ (cf : ℕ → ℂ), ∑ j ∈ Finset.range (L.degCoef + 1),
        cf j * ∑ u, L.strainAt n a 0 j l u * L.trueData x u =
        ∑ j ∈ Finset.range (L.degCoef + 1), cf j * L.bases.coef L.box (L.gradModeOf n x a 0) j l :=
      fun cf => Finset.sum_congr rfl (fun j hj => by rw [pair_strain L x n a 0 j l hj (by omega)])
    rw [hv, hs]
    simp only [CellLayout.radialInt]
    by_cases h0 : L.box.r₁ = 0
    · have hi : (i : ℕ) < L.degCoef := by
        have : (i : ℕ) ≠ L.degCoef := fun hh => hax ⟨h0, hh⟩
        omega
      have hβ : L.radialBeta i = fun r => r ^ ((i : ℕ) + 2) := by
        funext r
        simp [CellLayout.radialBeta, h0]
      have hw : ∀ r, L.box.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
      have hm1 : (fun r : ℝ => ((i : ℝ) + 2) * r ^ (i : ℕ)) ∈ polySpan L.bases L.degCoef := by
        have := Submodule.smul_mem (polySpan L.bases L.degCoef) ((i : ℝ) + 2)
          (pow_mem L.box L.bases hB i L.degCoef hi)
        convert this using 1
        funext r
        simp [smul_eq_mul]
      exact key L.box hK L.bases hB (L.velMode n x a) (L.gradModeOf n x a 0) hF hdF hcore
        (L.radialBeta i) (by rw [hβ]; fun_prop) L.degCoef (L.degCoef + 1)
        (fun r => ((i : ℝ) + 2) * r ^ (i : ℕ)) (fun r => r ^ ((i : ℕ) + 1))
        hm1 (pow_mem L.box L.bases hB _ _ (by omega)) (by fun_prop)
        (fun r => by
          rw [hβ, hw, (hasDerivAt_pow ((i : ℕ) + 2) r).deriv, show (i : ℕ) + 2 - 1 = (i : ℕ) + 1 by omega]
          push_cast
          ring)
        (fun r => by
          rw [hβ, hw]
          ring) l
    · have hβ : L.radialBeta i = fun r => r ^ (i : ℕ) := by
        funext r
        simp [CellLayout.radialBeta, h0]
      have hw : ∀ r, L.box.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
      have hm1 : (fun r : ℝ => (i : ℝ) * r ^ ((i : ℕ) - 1)) ∈ polySpan L.bases L.degCoef := by
        have := Submodule.smul_mem (polySpan L.bases L.degCoef) (i : ℝ)
          (pow_mem L.box L.bases hB ((i : ℕ) - 1) L.degCoef (by omega))
        convert this using 1
        funext r
        simp [smul_eq_mul]
      exact key L.box hK L.bases hB (L.velMode n x a) (L.gradModeOf n x a 0) hF hdF hcore
        (L.radialBeta i) (by rw [hβ]; fun_prop) L.degCoef (L.degCoef + 1)
        (fun r => (i : ℝ) * r ^ ((i : ℕ) - 1)) (fun r => r ^ (i : ℕ))
        hm1 (pow_mem L.box L.bases hB _ _ (by omega)) (by fun_prop)
        (fun r => by
          rw [hβ, hw, (hasDerivAt_pow (i : ℕ) r).deriv]
          ring)
        (fun r => by
          rw [hβ, hw]
          ring) l

end Breakdown.CertCell.LocalField
