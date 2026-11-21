import Breakdown.FracCell.StCoordsProof
import Breakdown.FracCell.StHeightModeIbp
import Breakdown.FracCell.StAngularMode

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis

namespace RelHeightSideInternal

def J (K : CellBox) (Fw : ℝ × ℝ → ℂ) (U : ℝ × ℝ → ℝ) : ℂ := ∫ p in K.rect, Fw p * ((U p : ℝ) : ℂ)

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem term_int {K : CellBox} {Fw : ℝ × ℝ → ℂ} (hF : IntegrableOn Fw K.rect) {U : ℝ × ℝ → ℝ}
    (hU : Continuous U) : IntegrableOn (fun p => Fw p * ((U p : ℝ) : ℂ)) K.rect :=
  hF.mul_continuousOn (Complex.continuous_ofReal.comp hU).continuousOn (rect_compact K)

def HeightPartsStatement : Prop :=
  ∀ {k N : ℕ} (c : FracCellData k N) (x : FieldTuple k), IsAdmissible c x →
    ∀ (L : CellLayout), L.order = c.order → ∀ (K : CellBox), IsCellBox K → ∀ (n : ℤ) (a : Fin 3),
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * L.velMode n x a p) K.rect ∧
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p) K.rect ∧
      ∀ (s φ φ' : ℝ → ℝ), Continuous s → Continuous φ' → (∀ z, HasDerivAt φ (φ' z) z) →
        φ K.z₁ = 0 → φ K.z₂ = 0 →
        ∫ p in K.rect, ((K.lineWeight p.1 : ℂ) * L.velMode n x a p * ((s p.1 * φ' p.2 : ℝ) : ℂ)
          + (K.lineWeight p.1 : ℂ) * L.gradModeOf n x a 2 p * ((s p.1 * φ p.2 : ℝ) : ℂ)) = 0

theorem heightParts_of (hIbp : HeightModeIbpStatement) (hI : ModeIntegrableStatement) : HeightPartsStatement := by
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


theorem J_add {K : CellBox} {Fw : ℝ × ℝ → ℂ} (hF : IntegrableOn Fw K.rect) {U V : ℝ × ℝ → ℝ}
    (hU : Continuous U) (hV : Continuous V) : J K Fw (fun p => U p + V p) = J K Fw U + J K Fw V := by
  unfold J
  rw [← integral_add (term_int hF hU) (term_int hF hV)]
  congr 1
  funext p
  push_cast
  ring

theorem J_smul (K : CellBox) (Fw : ℝ × ℝ → ℂ) (c : ℝ) (U : ℝ × ℝ → ℝ) :
    J K Fw (fun p => c * U p) = (c : ℂ) * J K Fw U := by
  unfold J
  rw [← integral_const_mul]
  congr 1
  funext p
  push_cast
  ring

theorem J_lin {K : CellBox} {Fw : ℝ × ℝ → ℂ} (hF : IntegrableOn Fw K.rect) {U V : ℝ × ℝ → ℝ}
    (hU : Continuous U) (hV : Continuous V) (a b : ℝ) :
    J K Fw (fun p => a * U p + b * V p) = (a : ℂ) * J K Fw U + (b : ℂ) * J K Fw V := by
  rw [J_add (U := fun p => a * U p) (V := fun p => b * V p) hF (continuous_const.mul hU)
    (continuous_const.mul hV), J_smul, J_smul]

theorem J_lin3 {K : CellBox} {Fw : ℝ × ℝ → ℂ} (hF : IntegrableOn Fw K.rect) {U V W : ℝ × ℝ → ℝ}
    (hU : Continuous U) (hV : Continuous V) (hW : Continuous W) (a b c : ℝ) :
    J K Fw (fun p => a * U p + b * V p + c * W p) =
      (a : ℂ) * J K Fw U + (b : ℂ) * J K Fw V + (c : ℂ) * J K Fw W := by
  rw [J_add (U := fun p => a * U p + b * V p) (V := fun p => c * W p) hF
    ((continuous_const.mul hU).add (continuous_const.mul hV)) (continuous_const.mul hW), J_lin hF hU hV, J_smul]

theorem J_sum {K : CellBox} {Fw : ℝ × ℝ → ℂ} (hF : IntegrableOn Fw K.rect) (s : Finset ℕ)
    (U : ℕ → ℝ × ℝ → ℝ) (hU : ∀ i, Continuous (U i)) :
    J K Fw (fun p => ∑ i ∈ s, U i p) = ∑ i ∈ s, J K Fw (U i) := by
  unfold J
  rw [← integral_finsetSum s (fun i _ => term_int hF (hU i))]
  congr 1
  funext p
  push_cast
  rw [Finset.mul_sum]

theorem radial_cont (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  fun_prop

theorem height_cont (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  fun_prop

def proj (B : CellBases) (z₁ z₂ : ℝ) (D : ℕ) (f : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ l ∈ Finset.range (D + 1), (∫ u in Set.Icc z₁ z₂, f u * B.heightPoly l u) * B.heightPoly l z

theorem proj_span (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (D : ℕ) (f : ℝ → ℝ)
    (hf : f ∈ Submodule.span ℝ {g | ∃ l ≤ D, g = B.heightPoly l}) :
    Continuous f ∧ ∀ z, proj B K.z₁ K.z₂ D f z = f z := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨l, hl, rfl⟩ := hg
    refine ⟨height_cont B l, fun z => ?_⟩
    unfold proj
    simp_rw [hB.height_orthonormal]
    simp [ite_mul, Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_of_le hl]
  | zero => exact ⟨continuous_const, fun z => by simp [proj]⟩
  | add f g _ _ hf hg =>
    refine ⟨hf.1.add hg.1, fun z => ?_⟩
    have key : ∀ l, (∫ u in Set.Icc K.z₁ K.z₂, (f u * B.heightPoly l u + g u * B.heightPoly l u)) =
        (∫ u in Set.Icc K.z₁ K.z₂, f u * B.heightPoly l u) + ∫ u in Set.Icc K.z₁ K.z₂, g u * B.heightPoly l u := by
      intro l
      exact integral_add ((hf.1.mul (height_cont B l)).integrableOn_Icc)
        ((hg.1.mul (height_cont B l)).integrableOn_Icc)
    have hfz := hf.2 z
    have hgz := hg.2 z
    unfold proj at hfz hgz ⊢
    simp only [Pi.add_apply, add_mul, key, Finset.sum_add_distrib]
    rw [hfz, hgz]
  | smul c f _ hf =>
    refine ⟨continuous_const.mul hf.1, fun z => ?_⟩
    have key : ∀ l, (∫ u in Set.Icc K.z₁ K.z₂, c * f u * B.heightPoly l u) =
        c * ∫ u in Set.Icc K.z₁ K.z₂, f u * B.heightPoly l u := by
      intro l
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    have hfz := hf.2 z
    unfold proj at hfz ⊢
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← hfz, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun l _ => by rw [key l]; ring)

theorem pow_mem (B : CellBases) (hlead : ∀ l, 0 < B.heightCoef l l) (m : ℕ) :
    ∀ D, m ≤ D → (fun z : ℝ => z ^ m) ∈ Submodule.span ℝ {g | ∃ l ≤ D, g = B.heightPoly l} := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro D hmD
    have hc : B.heightCoef m m ≠ 0 := (hlead m).ne'
    have hpoly : B.heightPoly m ∈ Submodule.span ℝ {g | ∃ l ≤ D, g = B.heightPoly l} :=
      Submodule.subset_span ⟨m, hmD, rfl⟩
    have hlow : (∑ i ∈ Finset.range m, B.heightCoef m i • (fun z : ℝ => z ^ i)) ∈
        Submodule.span ℝ {g | ∃ l ≤ D, g = B.heightPoly l} :=
      Submodule.sum_mem _ (fun i hi => Submodule.smul_mem _ _
        (ih i (Finset.mem_range.mp hi) D (by have := Finset.mem_range.mp hi; omega)))
    have e : (fun z : ℝ => z ^ m) = (B.heightCoef m m)⁻¹ •
        (B.heightPoly m - ∑ i ∈ Finset.range m, B.heightCoef m i • (fun z : ℝ => z ^ i)) := by
      funext z
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, CellBases.heightPoly, Finset.sum_range_succ,
        Finset.sum_apply]
      field_simp
      ring
    rw [e]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hpoly hlow)

theorem deriv_pow_eq (m : ℕ) : (fun z : ℝ => deriv (fun z : ℝ => z ^ m) z) = (m : ℝ) • (fun z : ℝ => z ^ (m - 1)) := by
  funext z
  rw [(hasDerivAt_pow m z).deriv]
  simp

theorem pair_sub (L : CellLayout) (f g T : L.Datum → ℂ) :
    ∑ d, (f - g) d * T d = ∑ d, f d * T d - ∑ d, g d * T d := by
  simp [sub_mul, Finset.sum_sub_distrib]

theorem pair_smul (L : CellLayout) (c : ℂ) (f T : L.Datum → ℂ) :
    ∑ d, (c • f) d * T d = c * ∑ d, f d * T d := by
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

theorem pair_sum (L : CellLayout) (s : Finset ℕ) (f : ℕ → L.Datum → ℂ) (T : L.Datum → ℂ) :
    ∑ d, (∑ i ∈ s, f i) d * T d = ∑ i ∈ s, ∑ d, f i d * T d := by
  simp only [Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

theorem pair_unit (L : CellLayout) (d₀ : L.Datum) (T : L.Datum → ℂ) :
    ∑ d, L.unitAt d₀ d * T d = T d₀ := by
  simp [CellLayout.unitAt, Pi.single_apply]

theorem pair_extra (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (e : Fin 4) (a : Fin 3) (d : ℕ)
    (hd : d < L.degCoef + 1) :
    ∑ d', L.extraAt n e a d d' * L.trueData x d' = L.extraValue n x e a d := by
  unfold CellLayout.extraAt
  rw [dif_pos hd, pair_unit]
  rfl

theorem sum_vel (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (a : Fin 3) (j : ℕ)
    (hj : j < L.degCoef) (A : ℕ → ℂ) :
    ∑ l ∈ Finset.range L.degCoef, A l * ∑ d, L.velocityAt n a j l d * L.trueData x d =
      ∑ l ∈ Finset.range L.degCoef, A l * L.bases.coef L.box (L.velMode n x a) j l := by
  refine Finset.sum_congr rfl (fun l hl => ?_)
  unfold CellLayout.velocityAt
  rw [dif_pos ⟨hj, Finset.mem_range.mp hl⟩, pair_unit]
  rfl

theorem sum_strain (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : L.modes) (a : Fin 3) (j : ℕ)
    (hj : j < L.degCoef + 1) (A : ℕ → ℂ) :
    ∑ l ∈ Finset.range (L.degCoef + 1), A l * ∑ d, L.strainAt n a 2 j l d * L.trueData x d =
      ∑ l ∈ Finset.range (L.degCoef + 1), A l * L.bases.coef L.box (L.gradModeOf n x a 2) j l := by
  refine Finset.sum_congr rfl (fun l hl => ?_)
  unfold CellLayout.strainAt
  rw [dif_pos ⟨hj, Finset.mem_range.mp hl⟩, pair_unit]
  rfl

theorem extra_three (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : ℤ) (a : Fin 3) (d : ℕ) :
    L.extraValue n x 3 a d = heightStripMoment L.box.z₂ L.box.z₁ L.box.r₁ L.box.r₂ (fun _ => 1)
      (L.velMode n x a) (L.gradModeOf n x a 2)
      (fun r => (if L.box.r₁ = 0 then r else 1) * L.bases.radialPoly d r) := by
  unfold CellLayout.extraValue CellLayout.sideTest
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), if_neg (by decide)]

theorem extra_two (L : CellLayout) {k : ℕ} (x : FieldTuple k) (n : ℤ) (a : Fin 3) (d : ℕ) :
    L.extraValue n x 2 a d = heightStripMoment L.box.z₁ L.box.z₂ L.box.r₁ L.box.r₂ (fun _ => 1)
      (L.velMode n x a) (L.gradModeOf n x a 2)
      (fun r => (if L.box.r₁ = 0 then r else 1) * L.bases.radialPoly d r) := by
  unfold CellLayout.extraValue CellLayout.sideTest
  rw [if_neg (by decide), if_neg (by decide), if_pos (by decide), if_neg (by decide)]

theorem weight_eq (K : CellBox) (r : ℝ) : (if K.r₁ = 0 then r else 1) = K.lineWeight r := by
  unfold CellBox.lineWeight
  split_ifs <;> rfl

theorem strip_top (K : CellBox) (hz : K.z₁ < K.z₂) (F dF : ℝ × ℝ → ℂ) (R : ℝ → ℝ) (hR : Continuous R)
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hG : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect) :
    heightStripMoment K.z₂ K.z₁ K.r₁ K.r₂ (fun _ => 1) F dF (fun r => (if K.r₁ = 0 then r else 1) * R r) =
      J K (fun p => (K.lineWeight p.1 : ℂ) * F p) (fun p => R p.1 / (K.z₂ - K.z₁))
        + J K (fun p => (K.lineWeight p.1 : ℂ) * dF p) (fun p => R p.1 * (p.2 - K.z₁) / (K.z₂ - K.z₁)) := by
  unfold heightStripMoment edgeSign
  rw [if_pos hz, min_eq_right hz.le, max_eq_left hz.le, one_mul]
  unfold J
  rw [← integral_add (term_int hF (by fun_prop)) (term_int hG (by fun_prop))]
  unfold CellBox.rect
  congr 1
  funext p
  simp only [weight_eq]
  push_cast
  ring

theorem strip_bottom (K : CellBox) (hz : K.z₁ < K.z₂) (F dF : ℝ × ℝ → ℂ) (R : ℝ → ℝ) (hR : Continuous R)
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hG : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * dF p) K.rect) :
    heightStripMoment K.z₁ K.z₂ K.r₁ K.r₂ (fun _ => 1) F dF (fun r => (if K.r₁ = 0 then r else 1) * R r) =
      J K (fun p => (K.lineWeight p.1 : ℂ) * F p) (fun p => R p.1 / (K.z₂ - K.z₁))
        + J K (fun p => (K.lineWeight p.1 : ℂ) * dF p) (fun p => R p.1 * (p.2 - K.z₂) / (K.z₂ - K.z₁)) := by
  unfold heightStripMoment edgeSign
  rw [if_neg (not_lt.mpr hz.le), min_eq_left hz.le, max_eq_right hz.le]
  unfold J
  rw [← integral_add (term_int hF (by fun_prop)) (term_int hG (by fun_prop)), ← integral_const_mul]
  unfold CellBox.rect
  congr 1
  funext p
  simp only [weight_eq]
  have c1 : (1 / (K.z₁ - K.z₂) : ℝ) = -(1 / (K.z₂ - K.z₁)) := by
    rw [show K.z₁ - K.z₂ = -(K.z₂ - K.z₁) by ring, div_neg]
  have c2 : ((p.2 - K.z₂) / (K.z₁ - K.z₂) : ℝ) = -((p.2 - K.z₂) / (K.z₂ - K.z₁)) := by
    rw [show K.z₁ - K.z₂ = -(K.z₂ - K.z₁) by ring, div_neg]
  rw [c1, c2]
  push_cast
  ring

end RelHeightSideInternal

open RelHeightSideInternal in
private theorem relHeightSide_of_parts (hP : HeightPartsStatement) : RelHeightSideStatement := by
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


open RelHeightSideInternal in
theorem relHeightSide_of (hIbp : HeightModeIbpStatement) (hI : ModeIntegrableStatement) : RelHeightSideStatement :=
  relHeightSide_of_parts (heightParts_of hIbp hI)

end CellFormula

end CellCert

end Breakdown
