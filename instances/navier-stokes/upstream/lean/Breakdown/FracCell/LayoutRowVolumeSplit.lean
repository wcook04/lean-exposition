import Breakdown.FracCell.LowVelocityExpansion
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.CellDensityModesWeak
import Breakdown.FracCell.LayoutRowValueParts

open MeasureTheory Finset

noncomputable section

namespace Breakdown.FracInternal.LayoutRowVolumeSplit

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly CellCert.CellEnergy.TopFormInternal CellCert.CellEnergy.LowVelocityExpansion.Internal
  LayoutRowParts FracInternal.CellDensityModesMirror FracInternal.CellDensityModesWeak

private theorem basisVal_eq (B : CellBases) (j l : ℕ) (p : ℝ × ℝ) : basisVal B j l p = basisC B j l p := rfl

private theorem weight_mul {K : CellBox} {X P : ℝ × ℝ → ℂ} {p : ℝ × ℝ}
    (h : ((rHat K p : ℝ) : ℂ) * X p = P p) : (p.1 : ℂ) * X p = (K.lineWeight p.1 : ℂ) * P p := by
  rw [← h]
  by_cases hw : K.lineWeight p.1 = 0
  · have h0 : p.1 = 0 := by
      unfold CellBox.lineWeight at hw
      split_ifs at hw with h1
      · exact hw
      · exact absurd hw one_ne_zero
    have hw0 : K.lineWeight 0 = 0 := h0 ▸ hw
    simp [h0, hw0]
  · unfold rHat
    push_cast
    have hw' : (K.lineWeight p.1 : ℂ) ≠ 0 := by exact_mod_cast hw
    field_simp

private theorem poly_conj {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') :
    (fun p => (starRingEnd ℂ) (P p)) ∈ polyFn d d' := by
  obtain ⟨c, hc⟩ := hP
  refine ⟨fun j l => (starRingEnd ℂ) (c j l), fun p => ?_⟩
  show (starRingEnd ℂ) (P p) = _
  rw [hc p]
  simp only [map_sum, map_mul, map_pow, Complex.conj_ofReal]

private theorem poly_pairing {K : CellBox} {B : CellBases} (hB : IsCellBases K B) {d : ℕ} {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hX : ∃ P ∈ polyFn d d, ∀ p ∈ K.rect, ((rHat K p : ℝ) : ℂ) * X p = P p) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * F p * X p := by
  obtain ⟨P, hP, hPX⟩ := hX
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  set Q : ℝ × ℝ → ℂ := fun p => (starRingEnd ℂ) (P p) with hQdef
  have hQ : Q ∈ polyFn d d := poly_conj hP
  have e1 : ∀ j l : ℕ, (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) =
      (starRingEnd ℂ) (K.pairOn K.lineWeightFn Q (basisC B j l)) := by
    intro j l
    rw [pair_def, ← integral_conj]
    refine setIntegral_congr_fun hrm fun p hp => ?_
    have h := weight_mul (hPX p hp)
    simp only [hQdef, basisVal_eq, basisC, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination ((CellEnergy.basisFn B j l p : ℝ) : ℂ) * h
  have e2 : (∫ p in K.rect, (p.1 : ℂ) * F p * X p) = K.pairOn K.lineWeightFn F Q := by
    rw [pair_def]
    refine setIntegral_congr_fun hrm fun p hp => ?_
    have h := weight_mul (hPX p hp)
    simp only [hQdef, Complex.conj_conj]
    linear_combination F p * h
  have hrec := poly_recon K hB hQ
  have hQf : Q = fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p := funext hrec
  have hcont : ∀ i ∈ range (d + 1), Continuous (fun p => ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p) := fun i _ =>
    continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k)
  rw [e2, hQf, pair_sum_right K _ hF hcont]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_sum_right K _ hF (g := fun k p => K.pairOn K.lineWeightFn Q (basisC B j k) * basisC B j k p)
    (fun k _ => continuous_const.mul (basisC_cont B j k))]
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pair_smul_right, e1, coef_eq, coef_eq]

private theorem proj_pairing {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (d : ℕ) {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) (hX : IntegrableOn X K.rect) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * K.proj d d F p * X p := by
  have hint : ∀ j l : ℕ, IntegrableOn (fun p => (p.1 : ℂ) * basisVal B j l p * X p) K.rect := by
    intro j l
    have hc : Continuous (fun p : ℝ × ℝ => (p.1 : ℂ) * basisVal B j l p) :=
      (Complex.continuous_ofReal.comp continuous_fst).mul (basisC_cont B j l)
    exact hX.continuousOn_mul hc.continuousOn (rect_compact K)
  have e : ∀ p, (p.1 : ℂ) * K.proj d d F p * X p = ∑ j ∈ range (d + 1), ∑ l ∈ range (d + 1),
      B.coef K F j l * ((p.1 : ℂ) * basisVal B j l p * X p) := by
    intro p
    rw [proj_expand K hB hF d d p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [basisVal_eq]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (hint j l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint _ l).const_mul _, integral_const_mul]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring


private theorem rim_null_rect (K : CellBox) :
    volume (K.rect \ (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂)) = 0 := by
  have hs : K.rect \ (Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) ⊆
      ({K.r₁, K.r₂} ×ˢ (Set.univ : Set ℝ)) ∪ ((Set.univ : Set ℝ) ×ˢ {K.z₁, K.z₂}) := by
    rintro ⟨r, z⟩ ⟨⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩, hn⟩
    simp only [Set.mem_prod, Set.mem_Ioo, not_and_or, not_lt] at hn
    simp only [Set.mem_union, Set.mem_prod, Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_univ, and_true,
      true_and]
    rcases hn with (h | h) | (h | h)
    · exact Or.inl (Or.inl (le_antisymm h hr1))
    · exact Or.inl (Or.inr (le_antisymm hr2 h))
    · exact Or.inr (Or.inl (le_antisymm h hz1))
    · exact Or.inr (Or.inr (le_antisymm hz2 h))
  refine measure_mono_null hs (measure_union_null ?_ ?_)
  · rw [Measure.volume_eq_prod, Measure.prod_prod, (Set.toFinite {K.r₁, K.r₂}).measure_zero, zero_mul]
  · rw [Measure.volume_eq_prod, Measure.prod_prod, (Set.toFinite {K.z₁, K.z₂}).measure_zero, mul_zero]

private theorem poly_pairing_open {K : CellBox} (hK : IsCellBox K) {B : CellBases} (hB : IsCellBases K B) {d : ℕ} {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hX : ∃ P ∈ polyFn d d, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((rHat K p : ℝ) : ℂ) * X p = P p) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * F p * X p := by
  obtain ⟨P, hP, hPX⟩ := hX
  have hrm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ K.rect → p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
    refine measure_mono_null ?_ (rim_null_rect K)
    intro q hq
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Classical.not_imp] at hq
    exact hq
  have hPX' : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p ∈ K.rect → ((rHat K p : ℝ) : ℂ) * X p = P p := by
    filter_upwards [hae] with p hp hpr
    exact hPX p (hp hpr) (lt_of_le_of_lt hK.r_order.1 (hp hpr).1.1).ne'
  set Q : ℝ × ℝ → ℂ := fun p => (starRingEnd ℂ) (P p) with hQdef
  have hQ : Q ∈ polyFn d d := poly_conj hP
  have e1 : ∀ j l : ℕ, (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) =
      (starRingEnd ℂ) (K.pairOn K.lineWeightFn Q (basisC B j l)) := by
    intro j l
    rw [pair_def, ← integral_conj]
    refine setIntegral_congr_ae hrm ?_
    filter_upwards [hPX'] with p hp0 hp
    have h := weight_mul (hp0 hp)
    simp only [hQdef, basisVal_eq, basisC, map_mul, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination ((CellEnergy.basisFn B j l p : ℝ) : ℂ) * h
  have e2 : (∫ p in K.rect, (p.1 : ℂ) * F p * X p) = K.pairOn K.lineWeightFn F Q := by
    rw [pair_def]
    refine setIntegral_congr_ae hrm ?_
    filter_upwards [hPX'] with p hp0 hp
    have h := weight_mul (hp0 hp)
    simp only [hQdef, Complex.conj_conj]
    linear_combination F p * h
  have hrec := poly_recon K hB hQ
  have hQf : Q = fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p := funext hrec
  have hcont : ∀ i ∈ range (d + 1), Continuous (fun p => ∑ k ∈ range (d + 1),
      K.pairOn K.lineWeightFn Q (basisC B i k) * basisC B i k p) := fun i _ =>
    continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k)
  rw [e2, hQf, pair_sum_right K _ hF hcont]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [pair_sum_right K _ hF (g := fun k p => K.pairOn K.lineWeightFn Q (basisC B j k) * basisC B j k p)
    (fun k _ => continuous_const.mul (basisC_cont B j k))]
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [pair_smul_right, e1, coef_eq, coef_eq]

private def openCore (K : CellBox) : Set Space :=
  {y | K.r₁ < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < |cylHeight y| ∧ |cylHeight y| < K.z₂}

private theorem openCore_open (K : CellBox) : IsOpen (openCore K) := by
  have hR : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hH : Continuous (fun y => |cylHeight y|) := by unfold cylHeight; fun_prop
  exact ((isOpen_lt continuous_const hR).inter ((isOpen_lt hR continuous_const).inter
    ((isOpen_lt continuous_const hH).inter (isOpen_lt hH continuous_const))))

private theorem openCore_sub (K : CellBox) : openCore K ⊆ K.solid := fun y hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.le⟩

private theorem upper_nhds (K : CellBox) {y : Space} (hy : y ∈ openCore K) (hh : 0 < cylHeight y) :
    K.solid ∩ {z | 0 ≤ cylHeight z} ∈ nhds y := by
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  refine Filter.mem_of_superset (((openCore_open K).inter (isOpen_lt continuous_const hH)).mem_nhds ⟨hy, hh⟩) ?_
  exact fun z hz => ⟨openCore_sub K hz.1, show 0 ≤ cylHeight z from le_of_lt hz.2⟩

private theorem lower_eq_near {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} {a : Fin N} (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) {y : Space}
    (hy : y ∈ openCore K) (hh : cylHeight y < 0) :
    c.row a =ᶠ[nhds y] fun z => mirror (c.row a (mirror z)) := by
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  exact Filter.mem_of_superset (((openCore_open K).inter (isOpen_lt hH continuous_const)).mem_nhds ⟨hy, hh⟩)
    fun z hz => hR.row_mirror a ha z (openCore_sub K hz.1) hz.2

private theorem lower_fderiv {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} {a : Fin N} (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) {y : Space}
    (hy : y ∈ openCore K) (hh : cylHeight y < 0) (u : Space) :
    fderiv ℝ (c.row a) y u = mirror (fderiv ℝ (c.row a) (mirror y) (mirror u)) := by
  set E : Space ≃L[ℝ] Space := LinearSolveCore.mirrorIsometry.toContinuousLinearEquiv with hE
  have hEf : (⇑E : Space → Space) = mirror := mirror_coe
  have hg : (fun z => mirror (c.row a (mirror z))) = ⇑E ∘ (c.row a ∘ ⇑E) := by
    funext z
    rw [hEf]
    rfl
  rw [(lower_eq_near hR ha hy hh).fderiv_eq, hg, E.comp_fderiv, E.comp_right_fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe, hEf]

private theorem upper_bound {k N : ℕ} {c : FracCellData k N} {K : CellBox} {a : Fin N} {L : NNReal}
    (hL : LipschitzOnWith L (c.row a) (K.solid ∩ {y | 0 ≤ cylHeight y})) {y : Space}
    (hy : y ∈ openCore K) (hh : 0 < cylHeight y) : ‖fderiv ℝ (c.row a) y‖ ≤ L :=
  norm_fderiv_le_of_lipschitzOn ℝ (upper_nhds K hy hh) hL

section

open Filter Topology

private theorem path_radial (r θ z : ℝ) : HasDerivAt (fun s => cylPoint s θ z) (radialUnit θ) r := by
  have e : (fun s => cylPoint s θ z) = fun s => s • radialUnit θ + EuclideanSpace.single 2 z := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, radialUnit]
  rw [e]
  have h := ((hasDerivAt_id r).smul_const (radialUnit θ)).add_const (EuclideanSpace.single 2 z : Space)
  simpa using h

private theorem path_height (r θ z : ℝ) : HasDerivAt (fun s => cylPoint r θ s) axialUnit z := by
  have e : (fun s => cylPoint r θ s) = fun s => s • axialUnit + cylPoint r θ 0 := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, axialUnit]
  rw [e]
  have h := ((hasDerivAt_id z).smul_const axialUnit).add_const (cylPoint r θ 0)
  simpa using h

private theorem path_radialUnit (θ : ℝ) : HasDerivAt (fun t => radialUnit t) (angularUnit θ) θ := by
  have e : (fun t => radialUnit t) = fun t => Real.cos t • (EuclideanSpace.single 0 1 : Space)
      + Real.sin t • (EuclideanSpace.single 1 1 : Space) := by
    funext t; ext j; fin_cases j <;> simp [radialUnit]
  rw [e]
  have h := ((Real.hasDerivAt_cos θ).smul_const (EuclideanSpace.single 0 1 : Space)).add
    ((Real.hasDerivAt_sin θ).smul_const (EuclideanSpace.single 1 1 : Space))
  have e2 : angularUnit θ = (-Real.sin θ) • (EuclideanSpace.single 0 1 : Space)
      + Real.cos θ • (EuclideanSpace.single 1 1 : Space) := by
    ext j; fin_cases j <;> simp [angularUnit]
  rw [e2]
  exact h

private theorem path_angularUnit (θ : ℝ) : HasDerivAt (fun t => angularUnit t) (-radialUnit θ) θ := by
  have e : (fun t => angularUnit t) = fun t => (-Real.sin t) • (EuclideanSpace.single 0 1 : Space)
      + Real.cos t • (EuclideanSpace.single 1 1 : Space) := by
    funext t; ext j; fin_cases j <;> simp [angularUnit]
  rw [e]
  have h := ((Real.hasDerivAt_sin θ).neg.smul_const (EuclideanSpace.single 0 1 : Space)).add
    ((Real.hasDerivAt_cos θ).smul_const (EuclideanSpace.single 1 1 : Space))
  have e2 : -radialUnit θ = (-Real.cos θ) • (EuclideanSpace.single 0 1 : Space)
      + (-Real.sin θ) • (EuclideanSpace.single 1 1 : Space) := by
    ext j; fin_cases j <;> simp [radialUnit]
  rw [e2]
  exact h

private theorem path_angle (r θ z : ℝ) : HasDerivAt (fun t => cylPoint r t z) (r • angularUnit θ) θ := by
  have e : (fun t => cylPoint r t z) = fun t => r • radialUnit t + EuclideanSpace.single 2 z := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, radialUnit]
  rw [e]
  exact ((path_radialUnit θ).const_smul r).add_const _

private theorem path_unit (θ : ℝ) (a : Fin 3) :
    HasDerivAt (fun t => frameUnit t a) (![angularUnit θ, -radialUnit θ, 0] a) θ := by
  fin_cases a
  · exact path_radialUnit θ
  · exact path_angularUnit θ
  · exact hasDerivAt_const θ axialUnit

private theorem frame_radial_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun s => frameVec θ (g (cylPoint s θ z)) a) (frameMat θ D a 0) r := by
  have e : (fun s => frameVec θ (g (cylPoint s θ z)) a) = fun s => inner ℝ (g (cylPoint s θ z)) (frameUnit θ a) :=
    funext fun s => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt r (path_radial r θ z)).inner ℝ (hasDerivAt_const r (frameUnit θ a))
  refine h.congr_deriv ?_
  simp only [inner_zero_right, zero_add]
  rfl

private theorem frame_height_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun s => frameVec θ (g (cylPoint r θ s)) a) (frameMat θ D a 2) z := by
  have e : (fun s => frameVec θ (g (cylPoint r θ s)) a) = fun s => inner ℝ (g (cylPoint r θ s)) (frameUnit θ a) :=
    funext fun s => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt z (path_height r θ z)).inner ℝ (hasDerivAt_const z (frameUnit θ a))
  refine h.congr_deriv ?_
  simp only [inner_zero_right, zero_add]
  rfl

private theorem frame_angle_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun t => frameVec t (g (cylPoint r t z)) a)
      (r * frameMat θ D a 1 + ![frameVec θ (g (cylPoint r θ z)) 1, -frameVec θ (g (cylPoint r θ z)) 0, 0] a) θ := by
  have e : (fun t => frameVec t (g (cylPoint r t z)) a) = fun t => inner ℝ (g (cylPoint r t z)) (frameUnit t a) :=
    funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt θ (path_angle r θ z)).inner ℝ (path_unit θ a)
  refine h.congr_deriv ?_
  simp only [Function.comp_apply, map_smul, real_inner_smul_left]
  have e1 : frameMat θ D a 1 = inner ℝ (D (angularUnit θ)) (frameUnit θ a) := rfl
  rw [e1, add_comm]
  congr 1
  fin_cases a
  · rfl
  · show inner ℝ (g (cylPoint r θ z)) (-radialUnit θ) = -frameVec θ (g (cylPoint r θ z)) 0
    rw [inner_neg_right]; rfl
  · show inner ℝ (g (cylPoint r θ z)) 0 = 0
    exact inner_zero_right _

private theorem frameMat_abs_le (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : |frameMat θ M a b| ≤ ‖M‖ := by
  have ha := LowEntry.Internal.unit_norm θ a
  have hb := LowEntry.Internal.unit_norm θ b
  unfold frameMat
  rw [← Real.norm_eq_abs]
  calc ‖inner ℝ (M (![radialUnit θ, angularUnit θ, axialUnit] b)) (![radialUnit θ, angularUnit θ, axialUnit] a)‖
      ≤ ‖M (![radialUnit θ, angularUnit θ, axialUnit] b)‖ * ‖![radialUnit θ, angularUnit θ, axialUnit] a‖ :=
        norm_inner_le_norm _ _
    _ ≤ (‖M‖ * 1) * 1 := by
        gcongr
        exact (M.le_opNorm _).trans (by gcongr)
    _ = ‖M‖ := by ring

private theorem param_mode_zero {F F' : ℝ → ℝ → ℝ} {x₀ C k : ℝ} {s : Set ℝ} (hs : s ∈ 𝓝 x₀)
    (hFc : ∀ x ∈ s, Continuous (F x)) (hF'c : Continuous (F' x₀)) (hb : ∀ x ∈ s, ∀ t, |F' x t| ≤ C)
    (hd : ∀ x ∈ s, ∀ t, HasDerivAt (fun x => F x t) (F' x t) x)
    (hz : ∀ x ∈ s, ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ) = 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(k * t : ℝ) * Complex.I) * (F' x₀ t : ℂ) = 0 := by
  have hec : Continuous (fun t : ℝ => Complex.exp (-(k * t : ℝ) * Complex.I)) := by fun_prop
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-(k * t : ℝ) * Complex.I)‖ = 1 := fun t => by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
    (a := 0) (b := 2 * Real.pi) (bound := fun _ => C)
    (F := fun x t => Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ))
    (F' := fun x t => Complex.exp (-(k * t : ℝ) * Complex.I) * (F' x t : ℂ)) hs
    (Filter.eventually_of_mem hs fun x hx =>
      (hec.mul (Complex.continuous_ofReal.comp (hFc x hx))).aestronglyMeasurable)
    ((hec.mul (Complex.continuous_ofReal.comp (hFc x₀ (mem_of_mem_nhds hs)))).intervalIntegrable _ _)
    ((hec.mul (Complex.continuous_ofReal.comp hF'c)).aestronglyMeasurable)
    (ae_of_all _ fun t _ x hx => by
      rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]; exact hb x hx t)
    intervalIntegrable_const
    (ae_of_all _ fun t _ x hx => ((hd x hx t).ofReal_comp).const_mul _)
  have h0 : HasDerivAt (fun x => ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(k * t : ℝ) * Complex.I) * (F x t : ℂ)) 0 x₀ :=
    (hasDerivAt_const x₀ (0 : ℂ)).congr_of_eventuallyEq (Filter.eventually_of_mem hs fun x hx => hz x hx)
  exact key.2.unique h0

private theorem mode_of_deriv {Φ Φ' : ℝ → ℝ} (m : ℕ) (k : ℤ) (hd : ∀ t, HasDerivAt Φ (Φ' t) t) (hc : Continuous Φ')
    (hper : Φ (2 * Real.pi) = Φ 0) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m k * t : ℝ) * Complex.I) * (Φ' t : ℂ) =
      ((azimuth m k : ℂ) * Complex.I) *
        ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m k * t : ℝ) * Complex.I) * (Φ t : ℂ) := by
  set w : ℝ := azimuth m k with hw
  have hu : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(w * t : ℝ) * Complex.I))
      (Complex.exp (-(w * t : ℝ) * Complex.I) * (-((w * 1 : ℝ) : ℂ) * Complex.I)) t := fun t =>
    ((((hasDerivAt_id t).const_mul w).ofReal_comp.neg).mul_const Complex.I).cexp
  have hv : ∀ t : ℝ, HasDerivAt (fun t : ℝ => (Φ t : ℂ)) (Φ' t : ℂ) t := fun t => (hd t).ofReal_comp
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := 0) (b := 2 * Real.pi)
    (fun t _ => hu t) (fun t _ => hv t)
    ((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-(w * t : ℝ) * Complex.I) *
      (-((w * 1 : ℝ) : ℂ) * Complex.I))).intervalIntegrable _ _)
    ((Complex.continuous_ofReal.comp hc).intervalIntegrable _ _)
  beta_reduce at hibp
  rw [hibp]
  have h2 : Complex.exp (-(w * (2 * Real.pi) : ℝ) * Complex.I) = 1 := by
    have : -(((w * (2 * Real.pi) : ℝ)) : ℂ) * Complex.I = ((-(k * m) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
      rw [hw]; unfold azimuth; push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  have h0 : Complex.exp (-(w * 0 : ℝ) * Complex.I) = 1 := by simp
  rw [h2, h0, hper]
  have e : (fun t : ℝ => Complex.exp (-(w * t : ℝ) * Complex.I) * (-((w * 1 : ℝ) : ℂ) * Complex.I) * (Φ t : ℂ)) =
      fun t => (-((w : ℂ) * Complex.I)) * (Complex.exp (-(w * t : ℝ) * Complex.I) * (Φ t : ℂ)) := by
    funext t; push_cast; ring
  rw [e, intervalIntegral.integral_const_mul]
  ring


end

open Filter Topology in
private theorem grad_mode_zero {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet)
    {n : ℤ} (hn0 : ∀ q ∈ K.rect, CellScalars.rowMode c a n q = 0)
    {p : ℝ × ℝ} (hp : p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂) (i j : Fin 3) :
    rowModeGrad c a n p i j = 0 := by
  obtain ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩ := hp
  have hK := hD.box
  have hr0 : 0 < p.1 := lt_of_le_of_lt hK.r_order.1 hr1
  obtain ⟨f, hf, hfeq⟩ := hR.row_smooth a ha (p.1 / 2) (by positivity)
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  set lo : ℝ := max K.r₁ (p.1 / 2) with hlo
  have hRc : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hHc : Continuous cylHeight := by unfold cylHeight; fun_prop
  set V : Set Space := {y | lo < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < cylHeight y ∧ cylHeight y < K.z₂}
    with hV
  have hVo : IsOpen V := (isOpen_lt continuous_const hRc).inter ((isOpen_lt hRc continuous_const).inter
    ((isOpen_lt continuous_const hHc).inter (isOpen_lt hHc continuous_const)))
  have hVcore : ∀ y ∈ V, y ∈ openCore K ∧ 0 < cylHeight y := by
    intro y hy
    have h0 : 0 < cylHeight y := lt_of_le_of_lt hK.z_order.1 hy.2.2.1
    refine ⟨⟨lt_of_le_of_lt (le_max_left _ _) hy.1, hy.2.1, ?_, ?_⟩, h0⟩
    · rw [abs_of_pos h0]; exact hy.2.2.1
    · rw [abs_of_pos h0]; exact hy.2.2.2
  have hVeq : ∀ y ∈ V, c.row a =ᶠ[𝓝 y] f := by
    intro y hy
    refine Filter.eventually_of_mem (hVo.mem_nhds hy) fun w hw => ?_
    obtain ⟨hwc, hw0⟩ := hVcore w hw
    exact hfeq w (openCore_sub K hwc) hw0.le (le_trans (le_max_right _ _) hw.1.le)
  have hder : ∀ y ∈ V, HasFDerivAt (c.row a) (fderiv ℝ (c.row a) y) y := by
    intro y hy
    have h1 : HasFDerivAt f (fderiv ℝ f y) y := (hf.differentiable (by norm_num) y).hasFDerivAt
    rw [(hVeq y hy).fderiv_eq]
    exact h1.congr_of_eventuallyEq (hVeq y hy)
  have hcont : ContinuousOn (fderiv ℝ (c.row a)) V :=
    (hf.continuous_fderiv (by norm_num)).continuousOn.congr fun y hy => (hVeq y hy).fderiv_eq
  have hbd : ∀ y ∈ V, ‖fderiv ℝ (c.row a) y‖ ≤ L := fun y hy =>
    upper_bound hL (hVcore y hy).1 (hVcore y hy).2
  have hmem : ∀ x t z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → cylPoint x t z' ∈ V := by
    intro x t z' h1 h2 h3 h4
    have hx0 : 0 ≤ x := le_trans (le_trans hK.r_order.1 (le_max_left _ _)) h1.le
    show lo < cylRadius (cylPoint x t z') ∧ cylRadius (cylPoint x t z') < K.r₂ ∧
      K.z₁ < cylHeight (cylPoint x t z') ∧ cylHeight (cylPoint x t z') < K.z₂
    rw [CellDensityModesSolid.cyl_radius hx0, CellDensityModesSolid.cyl_height]
    exact ⟨h1, h2, h3, h4⟩
  have hlop : lo < p.1 := max_lt hr1 (by linarith)
  have hpV : ∀ t, cylPoint p.1 t p.2 ∈ V := fun t => hmem _ _ _ hlop hr2 hz1 hz2
  have hpath : ∀ x z', Continuous (fun t => cylPoint x t z') := fun x z' =>
    continuous_iff_continuousAt.2 fun t => (path_angle x t z').continuousAt
  have hFc : ∀ x z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ∀ b,
      Continuous (fun t => frameVec t (c.row a (cylPoint x t z')) b) := by
    intro x z' h1 h2 h3 h4 b
    have hg : Continuous (fun t => c.row a (cylPoint x t z')) :=
      continuous_iff_continuousAt.2 fun t =>
        (hder _ (hmem x t z' h1 h2 h3 h4)).continuousAt.comp (f := fun t => cylPoint x t z') (path_angle x t z').continuousAt
    have e : (fun t => frameVec t (c.row a (cylPoint x t z')) b) =
        fun t => inner ℝ (c.row a (cylPoint x t z')) (frameUnit t b) :=
      funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
    rw [e]
    exact hg.inner (ModeVelSquareInternal.frameUnit_cont b)
  have hMc : ∀ a' b', Continuous (fun t => frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) a' b') := by
    intro a' b'
    have hD' : Continuous (fun t => fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) :=
      hcont.comp_continuous (hpath p.1 p.2) hpV
    show Continuous fun t => inner ℝ ((fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) (frameUnit t b')) (frameUnit t a')
    exact (hD'.clm_apply (ModeVelSquareInternal.frameUnit_cont b')).inner (ModeVelSquareInternal.frameUnit_cont a')
  have hrect : ∀ x z', K.r₁ < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ((x, z') : ℝ × ℝ) ∈ K.rect :=
    fun x z' h1 h2 h3 h4 => ⟨⟨h1.le, h2.le⟩, ⟨h3.le, h4.le⟩⟩
  have hang : ∀ t', HasDerivAt (fun t => frameVec t (c.row a (cylPoint p.1 t p.2)) i)
      (p.1 * frameMat t' (fderiv ℝ (c.row a) (cylPoint p.1 t' p.2)) i 1 +
        ![frameVec t' (c.row a (cylPoint p.1 t' p.2)) 1, -frameVec t' (c.row a (cylPoint p.1 t' p.2)) 0, 0] i) t' :=
    fun t' => frame_angle_deriv (hder _ (hpV t')) i
  have hq : p ∈ K.rect := ⟨⟨hr1.le, hr2.le⟩, ⟨hz1.le, hz2.le⟩⟩
  have hrm : ∀ q ∈ K.rect, ∀ b, ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (frameVec t (c.row a (cylPoint q.1 t q.2)) b : ℂ) = 0 := by
    intro q hq' b
    have h : (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (frameVec t (c.row a (cylPoint q.1 t q.2)) b : ℂ) = 0 :=
      congrFun (hn0 q hq') b
    have h2 : (1 / (2 * Real.pi) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < 2 * Real.pi := by positivity
      exact one_div_ne_zero (by exact_mod_cast this.ne')
    exact (mul_eq_zero.1 h).resolve_left h2
  have hec : ∀ n : ℤ, Continuous (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)) :=
    fun n => by fun_prop
  suffices H : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
      (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i j : ℂ) = 0 by
    simp only [rowModeGrad, modeMat, H, mul_zero]
  fin_cases j
  · exact param_mode_zero (F := fun x t => frameVec t (c.row a (cylPoint x t p.2)) i)
      (F' := fun x t => frameMat t (fderiv ℝ (c.row a) (cylPoint x t p.2)) i 0) (C := L)
      (Ioo_mem_nhds hlop hr2)
      (fun x hx => hFc x p.2 hx.1 hx.2 hz1 hz2 i) (hMc i 0)
      (fun x hx t => (frameMat_abs_le _ _ _ _).trans (hbd _ (hmem x t p.2 hx.1 hx.2 hz1 hz2)))
      (fun x hx t => frame_radial_deriv (hder _ (hmem x t p.2 hx.1 hx.2 hz1 hz2)) i)
      (fun x hx => hrm (x, p.2) (hrect x p.2 (lt_of_le_of_lt (le_max_left _ _) hx.1) hx.2 hz1 hz2) i)
  · have hEc : Continuous (fun t => ![frameVec t (c.row a (cylPoint p.1 t p.2)) 1,
        -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i) := by
      fin_cases i
      · exact hFc p.1 p.2 hlop hr2 hz1 hz2 1
      · exact (hFc p.1 p.2 hlop hr2 hz1 hz2 0).neg
      · exact continuous_const
    have h2pi : frameVec (2 * Real.pi) (c.row a (cylPoint p.1 (2 * Real.pi) p.2)) i =
        frameVec 0 (c.row a (cylPoint p.1 0 p.2)) i := by
      have e1 : cylPoint p.1 (2 * Real.pi) p.2 = cylPoint p.1 0 p.2 := by simp [cylPoint]
      rw [e1]
      fin_cases i <;> simp [frameVec, radialUnit, angularUnit]
    have hibp := mode_of_deriv c.order n hang ((continuous_const.mul (hMc i 1)).add hEc) h2pi
    beta_reduce at hibp
    rw [hrm p hq i, mul_zero] at hibp
    have hE0 : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ) = 0 := by
      fin_cases i
      · exact hrm p hq 1
      · refine Eq.trans (intervalIntegral.integral_congr (g := fun t => -(Complex.exp (-(azimuth c.order n * t : ℝ) *
            Complex.I) * (frameVec t (c.row a (cylPoint p.1 t p.2)) 0 : ℂ))) fun t _ => ?_) ?_
        · show _ * (((-frameVec t (c.row a (cylPoint p.1 t p.2)) 0 : ℝ)) : ℂ) = _
          push_cast; ring
        · rw [intervalIntegral.integral_neg, hrm p hq 0, neg_zero]
      · show ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (((0 : ℝ)) : ℂ) = 0
        simp
    have hi1 : IntervalIntegrable (fun t : ℝ => (p.1 : ℂ) * (Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 : ℂ))) volume 0 (2 * Real.pi) :=
      (continuous_const.mul ((hec n).mul (Complex.continuous_ofReal.comp (hMc i 1)))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ))
        volume 0 (2 * Real.pi) :=
      ((hec n).mul (Complex.continuous_ofReal.comp hEc)).intervalIntegrable _ _
    have hsplit : (∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        ((p.1 * frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 +
          ![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ)) =
        (p.1 : ℂ) * (∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
          (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 : ℂ)) +
        ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
          ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ) := by
      rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add hi1 hi2]
      congr 1
      funext t
      push_cast
      ring
    rw [hsplit, hE0, add_zero] at hibp
    exact (mul_eq_zero.1 hibp).resolve_left (by exact_mod_cast hr0.ne')
  · exact param_mode_zero (F := fun z' t => frameVec t (c.row a (cylPoint p.1 t z')) i)
      (F' := fun z' t => frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t z')) i 2) (C := L)
      (Ioo_mem_nhds hz1 hz2)
      (fun z' hz => hFc p.1 z' hlop hr2 hz.1 hz.2 i) (hMc i 2)
      (fun z' hz t => (frameMat_abs_le _ _ _ _).trans (hbd _ (hmem p.1 t z' hlop hr2 hz.1 hz.2)))
      (fun z' hz t => frame_height_deriv (hder _ (hmem p.1 t z' hlop hr2 hz.1 hz.2)) i)
      (fun z' hz => hrm (p.1, z') (hrect p.1 z' hr1 hr2 hz.1 hz.2) i)

private theorem proj_cont' (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : Continuous (K.proj d d' F) := by
  unfold CellBox.proj
  split_ifs with h
  · exact LowEntry.Internal.poly_cont h.choose_spec.1
  · exact continuous_const

private theorem solid_meas' (K : CellBox) : MeasurableSet K.solid := by
  have h0 : Continuous cylRadius := by unfold cylRadius; fun_prop
  have h2 : Continuous (fun y : Space => |cylHeight y|) := by unfold cylHeight; fun_prop
  have he : K.solid = ({y | K.r₁ ≤ cylRadius y} ∩ {y | cylRadius y ≤ K.r₂}) ∩
      ({y | K.z₁ ≤ |cylHeight y|} ∩ {y | |cylHeight y| ≤ K.z₂}) := by
    ext y; simp only [CellBox.solid, Set.mem_ofPred_eq, Set.mem_inter_iff]; tauto
  rw [he]
  exact (((measurableSet_le measurable_const h0.measurable).inter (measurableSet_le h0.measurable measurable_const)).inter
    ((measurableSet_le measurable_const h2.measurable).inter (measurableSet_le h2.measurable measurable_const)))

private theorem cyl_in_solid {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hp.1.1
  have hz : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
  show K.r₁ ≤ cylRadius (cylPoint p.1 θ p.2) ∧ cylRadius (cylPoint p.1 θ p.2) ≤ K.r₂ ∧
    K.z₁ ≤ |cylHeight (cylPoint p.1 θ p.2)| ∧ |cylHeight (cylPoint p.1 θ p.2)| ≤ K.z₂
  rw [CellDensityModesSolid.cyl_radius h0, CellDensityModesSolid.cyl_height, abs_of_nonneg hz]
  exact ⟨hp.1.1, hp.1.2, hp.2.1, hp.2.2⟩

private theorem modeVec_int_on {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) {v : Space → Space}
    (hvm : AEStronglyMeasurable v volume) (hvi : IntegrableOn (fun y => ‖v y‖) K.solid) (a : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeVec m n v p.1 p.2 a) K.rect := by
  have hI : Integrable (K.solid.indicator v) := by
    rw [integrable_indicator_iff (solid_meas' K)]
    exact (integrable_norm_iff hvm.restrict).1 hvi
  have h := LowEntry.Internal.mode_int K hK hI.locallyIntegrable (LowEntry.Internal.velKernel m n a)
    (LowEntry.Internal.velKernel_cont m n a) (LowEntry.Internal.velKernel_bound m n a)
  refine IntegrableOn.congr_fun (h.const_mul (1 / (2 * Real.pi) : ℂ)) (fun p hp => ?_) (LowEntry.Internal.rect_meas K)
  rw [LowEntry.Internal.modeVec_eq]
  have e : ∫ θ in Set.Ioo (-Real.pi) Real.pi, LowEntry.Internal.velKernel m n a θ
      (K.solid.indicator v (cylPoint p.1 θ p.2)) =
      ∫ θ in Set.Ioo (-Real.pi) Real.pi, LowEntry.Internal.velKernel m n a θ (v (cylPoint p.1 θ p.2)) := by
    congr 1
    funext θ
    rw [Set.indicator_of_mem (cyl_in_solid hK hp θ)]
  rw [e]
  ring

private theorem weight_eq_rect {K : CellBox} (hK : IsCellBox K) {X P : ℝ × ℝ → ℂ}
    (hX : ∀ p ∈ K.rect, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * X p = P p) {p : ℝ × ℝ} (hp : p ∈ K.rect) :
    (p.1 : ℂ) * X p = (K.lineWeight p.1 : ℂ) * P p := by
  by_cases h : p.1 = 0
  · have hr : K.r₁ = 0 := le_antisymm (h ▸ hp.1.1) hK.r_order.1
    simp [h, CellBox.lineWeight, hr]
  · exact weight_mul (hX p hp h)

private theorem open_ae (K : CellBox) :
    ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂ := by
  rw [ae_restrict_iff' (LowEntry.Internal.rect_meas K)]
  refine measure_mono_null ?_ (rim_null_rect K)
  intro q hq
  simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Classical.not_imp] at hq
  exact hq

private theorem conj_weight {r w : ℝ} {X P : ℂ} (h : (r : ℂ) * X = (w : ℂ) * P) :
    (r : ℂ) * (starRingEnd ℂ) X = (w : ℂ) * (starRingEnd ℂ) P := by
  have := congrArg (starRingEnd ℂ) h
  simpa only [map_mul, Complex.conj_ofReal] using this

private theorem re_int {K : CellBox} {f : ℝ × ℝ → ℂ} (h : IntegrableOn (fun p => (p.1 : ℂ) * f p) K.rect) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (f p).re) K.rect := by
  refine (Complex.reCLM.integrable_comp h).congr ?_
  filter_upwards with p
  simp

theorem volume_lhs_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑ n ∈ R.rowModes,
        pairC (modeVec c.order n (lowTransport c K S α x) p.1 p.2) (rowModeVec c a n p)).re) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')).re) K.rect := by
  have hK : IsCellBox K := hD.box
  have hrm := LowEntry.Internal.rect_meas K
  have hcpt := LowEntry.Internal.rect_compact K
  constructor
  · choose P hP hPX using hR.row_low_velocity a ha
    obtain ⟨hTm, hTi⟩ := lowTransport_on hc hD hx
    refine re_int ?_
    have hI : IntegrableOn (fun p => ∑ n ∈ R.rowModes, ∑ i : Fin 3,
        (K.lineWeight p.1 : ℂ) * modeVec c.order n (lowTransport c K S α x) p.1 p.2 i *
          (starRingEnd ℂ) (P n i p)) K.rect :=
      integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun i _ =>
        (modeVec_int_on hK c.order n hTm hTi i).mul_continuousOn
          (Complex.continuous_conj.comp (LowEntry.Internal.poly_cont (hP n i))).continuousOn hcpt
    refine hI.congr_fun (fun p hp => ?_) hrm
    simp only [pairC, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => ?_
    have h := conj_weight (weight_eq_rect hK (X := fun q => rowModeVec c a n q i) (P := P n i) (hPX n i) hp)
    linear_combination (-modeVec c.order n (lowTransport c K S α x) p.1 p.2 i) * h
  · choose P hP hPX using hR.row_low_gradient a ha
    refine re_int ?_
    have hI : IntegrableOn (fun p => ∑ n ∈ R.rowModes, ∑ a' : Fin 3, ∑ b' : Fin 3,
        (K.lineWeight p.1 : ℂ) * gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (P n a' b' p)) K.rect :=
      integrable_finsetSum _ fun n _ => integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        (LowEntry.Internal.gradMode_int K hK c.order n hx.1.measurable_gradient hx.1.gradient_two i j).mul_continuousOn
          (Complex.continuous_conj.comp (LowEntry.Internal.poly_cont (hP n i j))).continuousOn hcpt
    refine Integrable.congr hI ?_
    filter_upwards [open_ae K] with p hp
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have h := conj_weight (weight_mul (X := fun q => rowModeGrad c a n q i j) (P := P n i j) (hPX n i j p hp (lt_of_le_of_lt hK.r_order.1 hp.1.1).ne'))
    linear_combination (-gradMode c.order n x.2.1 i j p) * h

def volumeDensity {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (α ν : ℝ) (x : FieldTuple k)
    (m : ℤ) (X : Fin 3 → ℂ) (Y : Fin 3 → Fin 3 → ℂ) (p : ℝ × ℝ) : ℂ :=
  (∑ a : Fin 3, ∑ b : Fin 3, gradMode c.order m x.2.1 a b p *
      (((1 / (2 * α) : ℝ) : ℂ) * frameY p b * (starRingEnd ℂ) (X a)
        + (c.modelRate : ℂ) * frameTurnY p b * (starRingEnd ℂ) (X a) + (ν : ℂ) * (starRingEnd ℂ) (Y a b)))
  + ∑ a : Fin 3, modeVec c.order m x.1 p.1 p.2 a *
      (((1 - 1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (X a) - (c.modelRate : ℂ) * pairC (turnC (Pi.single a 1)) X)
  + ∑ n ∈ S.resolved, ((∑ a' : Fin 3, ∑ b' : Fin 3, K.lowStrain c.order n S.degHigh x.2.1 a' b' p *
        pairC (crossC (fun i => (permSign i b' a' : ℂ)) (modeVec c.order (m - n) c.modelVelocity p.1 p.2)) X)
      + ∑ a' : Fin 3, K.lowVelocity c.order n S.degHigh x.1 a' p *
        pairC (crossC (modeVec c.order (m - n) c.modelCurl p.1 p.2) (Pi.single a' 1)) X)



private theorem proj_pairing' {K : CellBox} {B : CellBases} (hB : IsCellBases K B) (d : ℕ) {F X : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hX : IntegrableOn (fun p => (p.1 : ℂ) * X p) K.rect) :
    ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l =
      ∫ p in K.rect, (p.1 : ℂ) * K.proj d d F p * X p := by
  have hint : ∀ j l : ℕ, IntegrableOn (fun p => (p.1 : ℂ) * basisVal B j l p * X p) K.rect := by
    intro j l
    exact IntegrableOn.congr_fun (hX.continuousOn_mul (basisC_cont B j l).continuousOn
      (LowEntry.Internal.rect_compact K)) (fun p _ => by rw [basisVal_eq]; ring) (LowEntry.Internal.rect_meas K)
  have e : ∀ p, (p.1 : ℂ) * K.proj d d F p * X p = ∑ j ∈ range (d + 1), ∑ l ∈ range (d + 1),
      B.coef K F j l * ((p.1 : ℂ) * basisVal B j l p * X p) := by
    intro p
    rw [proj_expand K hB hF d d p, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [basisVal_eq]
    ring
  simp_rw [e]
  rw [integral_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (hint j l).const_mul _]
  simp_rw [integral_finsetSum _ fun l _ => (hint _ l).const_mul _, integral_const_mul]
  rw [← Finset.sum_range (fun j => ∑ l : Fin (d + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) *
    B.coef K F j l)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_range (fun l => (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * X p) * B.coef K F j l)]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

private theorem gen_term {K : CellBox} (hK : IsCellBox K) {B : CellBases} (hB : IsCellBases K B) (Q D : ℕ)
    (hQD : D = Q + 1) (s : Finset ℤ) (n : ℤ) {F : ℝ × ℝ → ℂ} (Dm Cm : ℤ → ℝ × ℝ → ℂ)
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hD : ∀ m, ∃ P ∈ polyFn Q Q, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((rHat K p : ℝ) : ℂ) * Dm m p = P p)
    (hC : ∀ m, IntegrableOn (fun p => (p.1 : ℂ) * Cm m p) K.rect) :
    ∑ j : Fin D, ∑ l : Fin D, (∑ m ∈ s, ∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p *
      ((if m = n then Dm m p else 0) + Cm m p)) * B.coef K F j l =
    ∑ m ∈ s, ((if m = n then ∫ p in K.rect, (p.1 : ℂ) * F p * Dm m p else 0) +
      ∫ p in K.rect, (p.1 : ℂ) * K.proj Q Q F p * Cm m p) := by
  subst hQD
  have hcpt := LowEntry.Internal.rect_compact K
  have hrm := LowEntry.Internal.rect_meas K
  have hbc : ∀ j l : ℕ, Continuous (basisVal B j l) := fun j l => basisC_cont B j l
  have hDi : ∀ m (j l : ℕ), IntegrableOn (fun p => (p.1 : ℂ) * basisVal B j l p * Dm m p) K.rect := by
    intro m j l
    obtain ⟨P, hP, hPX⟩ := hD m
    have h1 : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * basisVal B j l p * P p) K.rect :=
      (((LowEntry.Internal.weight_cont K).mul (hbc j l)).mul (LowEntry.Internal.poly_cont hP)).continuousOn.integrableOn_compact hcpt
    refine Integrable.congr h1 ?_
    filter_upwards [open_ae K] with p hp
    have h := weight_mul (X := Dm m) (P := P) (hPX p hp (lt_of_le_of_lt hK.r_order.1 hp.1.1).ne')
    linear_combination (-basisVal B j l p) * h
  have hCi : ∀ m (j l : ℕ), IntegrableOn (fun p => (p.1 : ℂ) * basisVal B j l p * Cm m p) K.rect := by
    intro m j l
    exact IntegrableOn.congr_fun ((hC m).continuousOn_mul (hbc j l).continuousOn hcpt) (fun p _ => by ring) hrm
  have hsplit : ∀ (j l : ℕ) m, (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * ((if m = n then Dm m p else 0) + Cm m p)) =
      (if m = n then ∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * Dm m p else 0) +
        ∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p * Cm m p := by
    intro j l m
    by_cases h : m = n
    · simp only [h, if_pos, mul_add]
      exact integral_add (hDi n j l) (hCi n j l)
    · simp only [h, if_false, mul_zero, zero_add]
  have key : ∀ m, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), (∫ p in K.rect, (p.1 : ℂ) * basisVal B j l p *
      ((if m = n then Dm m p else 0) + Cm m p)) * B.coef K F j l =
      (if m = n then ∫ p in K.rect, (p.1 : ℂ) * F p * Dm m p else 0) +
        ∫ p in K.rect, (p.1 : ℂ) * K.proj Q Q F p * Cm m p := by
    intro m
    simp only [hsplit, add_mul, Finset.sum_add_distrib]
    congr 1
    · by_cases h : m = n
      · simp only [h, if_pos]
        exact poly_pairing_open hK hB hF (hD n)
      · simp only [h, if_false, zero_mul, Finset.sum_const_zero]
    · exact proj_pairing' hB Q hF (hC m)
  rw [← Finset.sum_congr rfl fun m _ => key m]
  simp only [Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_comm]

private def strainDiag {k N : ℕ} (c : FracCellData k N) (α : ℝ) (a : Fin N) (m : ℤ) (i j : Fin 3)
    (p : ℝ × ℝ) : ℂ :=
  ((1 / (2 * α) : ℝ) : ℂ) * frameY p j * (starRingEnd ℂ) (rowModeVec c a m p i)
    + (c.modelRate : ℂ) * frameTurnY p j * (starRingEnd ℂ) (rowModeVec c a m p i)
    + (c.splitVisc : ℂ) * (starRingEnd ℂ) (rowModeGrad c a m p i j)

private def velDiag {k N : ℕ} (c : FracCellData k N) (α : ℝ) (a : Fin N) (m : ℤ) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  ((1 - 1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (rowModeVec c a m p i)
    - (c.modelRate : ℂ) * pairC (turnC (Pi.single i 1)) (rowModeVec c a m p)

private def strainCross {k N : ℕ} (c : FracCellData k N) (a : Fin N) (m n : ℤ) (i j : Fin 3) (p : ℝ × ℝ) : ℂ :=
  pairC (crossC (fun l => (permSign l j i : ℂ)) (modeVec c.order (m - n) c.modelVelocity p.1 p.2))
    (rowModeVec c a m p)

private def velCross {k N : ℕ} (c : FracCellData k N) (a : Fin N) (m n : ℤ) (i : Fin 3) (p : ℝ × ℝ) : ℂ :=
  pairC (crossC (modeVec c.order (m - n) c.modelCurl p.1 p.2) (Pi.single i 1)) (rowModeVec c a m p)

private theorem frameY_conj (p : ℝ × ℝ) (j : Fin 3) : (starRingEnd ℂ) (frameY p j) = frameY p j := by
  fin_cases j <;> simp [frameY]

private theorem frameTurnY_conj (p : ℝ × ℝ) (j : Fin 3) : (starRingEnd ℂ) (frameTurnY p j) = frameTurnY p j := by
  fin_cases j <;> simp [frameTurnY]

private theorem conj_rhat {K : CellBox} {p : ℝ × ℝ} {Z P : ℂ} (h : ((rHat K p : ℝ) : ℂ) * Z = P) :
    ((rHat K p : ℝ) : ℂ) * (starRingEnd ℂ) Z = (starRingEnd ℂ) P := by
  rw [← h, map_mul, Complex.conj_ofReal]

private theorem strainDiag_poly {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} (hR : IsRowShape c K S R) {a : Fin N} (ha : a ∈ R.rowSet) (m : ℤ) (i j : Fin 3) :
    ∃ P ∈ polyFn S.degHigh S.degHigh, ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((rHat K p : ℝ) : ℂ) * strainDiag c α a m i j p = P p := by
  obtain ⟨P1, h1, hP1⟩ := hR.row_low_position a ha m i j
  obtain ⟨P2, h2, hP2⟩ := hR.row_low_turn a ha m i j
  obtain ⟨P3, h3, hP3⟩ := hR.row_low_gradient a ha m i j
  refine ⟨fun p => ((1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (P1 p) + (c.modelRate : ℂ) * (starRingEnd ℂ) (P2 p)
    + (c.splitVisc : ℂ) * (starRingEnd ℂ) (P3 p),
    LowEntry.Internal.poly_add (LowEntry.Internal.poly_add (LowEntry.Internal.poly_smul _ (poly_conj h1))
      (LowEntry.Internal.poly_smul _ (poly_conj h2))) (LowEntry.Internal.poly_smul _ (poly_conj h3)),
    fun p hp hp0 => ?_⟩
  have hpr : p ∈ K.rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have e1 := conj_rhat (hP1 p hpr hp0)
  have e2 := conj_rhat (hP2 p hpr hp0)
  have e3 := conj_rhat (hP3 p hp hp0)
  simp only [map_mul, frameY_conj, frameTurnY_conj] at e1 e2
  simp only [strainDiag]
  linear_combination ((1 / (2 * α) : ℝ) : ℂ) * e1 + (c.modelRate : ℂ) * e2 + (c.splitVisc : ℂ) * e3

private theorem velDiag_poly {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {R : CellRows N slots k} (hR : IsRowShape c K S R) {a : Fin N} (ha : a ∈ R.rowSet) (m : ℤ) (i : Fin 3) :
    ∃ P ∈ polyFn (S.degHigh - 1) (S.degHigh - 1), ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((rHat K p : ℝ) : ℂ) * velDiag c α a m i p = P p := by
  choose P hP hPX using hR.row_low_velocity a ha
  refine ⟨fun p => ((1 - 1 / (2 * α) : ℝ) : ℂ) * (starRingEnd ℂ) (P m i p)
    + (-(c.modelRate : ℂ)) * ∑ l : Fin 3, turnC (Pi.single i 1) l * (starRingEnd ℂ) (P m l p),
    LowEntry.Internal.poly_add (LowEntry.Internal.poly_smul _ (poly_conj (hP m i)))
      (LowEntry.Internal.poly_smul _ (LowEntry.Internal.poly_sum _ _ fun l _ =>
        LowEntry.Internal.poly_smul _ (poly_conj (hP m l)))),
    fun p hp hp0 => ?_⟩
  have hpr : p ∈ K.rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
  have ei := conj_rhat (hPX m i p hpr hp0)
  have e0 := conj_rhat (hPX m 0 p hpr hp0)
  have e1 := conj_rhat (hPX m 1 p hpr hp0)
  have e2 := conj_rhat (hPX m 2 p hpr hp0)
  simp only [velDiag, pairC, Fin.sum_univ_three]
  linear_combination ((1 - 1 / (2 * α) : ℝ) : ℂ) * ei - (c.modelRate : ℂ) * (turnC (Pi.single i 1) 0 * e0
    + turnC (Pi.single i 1) 1 * e1 + turnC (Pi.single i 1) 2 * e2)

private theorem int_poly {K : CellBox} (hK : IsCellBox K) {d d' : ℕ} {F E : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect)
    (hE : ∃ P ∈ polyFn d d', ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, p.1 ≠ 0 →
      ((rHat K p : ℝ) : ℂ) * E p = P p) :
    IntegrableOn (fun p => (p.1 : ℂ) * F p * E p) K.rect := by
  obtain ⟨P, hP, hPX⟩ := hE
  refine Integrable.congr (hF.mul_continuousOn (LowEntry.Internal.poly_cont hP).continuousOn
    (LowEntry.Internal.rect_compact K)) ?_
  filter_upwards [open_ae K] with p hp
  have h := weight_mul (X := E) (P := P) (hPX p hp (lt_of_le_of_lt hK.r_order.1 hp.1.1).ne')
  linear_combination (-F p) * h

private theorem int_pair {K : CellBox} (hK : IsCellBox K) {d : ℕ} {U X : ℝ × ℝ → Fin 3 → ℂ}
    (hU : ∀ i, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * U p i) K.rect)
    (hX : ∀ i, ∃ P ∈ polyFn d d, ∀ p ∈ K.rect, p.1 ≠ 0 → ((rHat K p : ℝ) : ℂ) * X p i = P p) :
    IntegrableOn (fun p => (p.1 : ℂ) * pairC (U p) (X p)) K.rect := by
  choose P hP hPX using hX
  have hI : IntegrableOn (fun p => ∑ i : Fin 3, (K.lineWeight p.1 : ℂ) * U p i * (starRingEnd ℂ) (P i p)) K.rect :=
    integrable_finsetSum _ fun i _ => (hU i).mul_continuousOn
      (Complex.continuous_conj.comp (LowEntry.Internal.poly_cont (hP i))).continuousOn (LowEntry.Internal.rect_compact K)
  refine hI.congr_fun (fun p hp => ?_) (LowEntry.Internal.rect_meas K)
  simp only [pairC, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := conj_weight (weight_eq_rect hK (X := fun q => X q i) (P := P i) (hPX i) hp)
  linear_combination (-U p i) * h

private theorem cross_left_int {K : CellBox} {u : ℝ × ℝ → Fin 3 → ℂ} (w : Fin 3 → ℂ)
    (hu : ∀ i, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * u p i) K.rect) (i : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * crossC w (u p) i) K.rect := by
  have hm := LowEntry.Internal.rect_meas K
  fin_cases i
  · exact IntegrableOn.congr_fun (((hu 2).const_mul (w 1)).sub ((hu 1).const_mul (w 2)))
      (fun p _ => by simp [crossC] <;> ring) hm
  · exact IntegrableOn.congr_fun (((hu 0).const_mul (w 2)).sub ((hu 2).const_mul (w 0)))
      (fun p _ => by simp [crossC] <;> ring) hm
  · exact IntegrableOn.congr_fun (((hu 1).const_mul (w 0)).sub ((hu 0).const_mul (w 1)))
      (fun p _ => by simp [crossC] <;> ring) hm

private theorem cross_right_int {K : CellBox} {u : ℝ × ℝ → Fin 3 → ℂ} (w : Fin 3 → ℂ)
    (hu : ∀ i, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * u p i) K.rect) (i : Fin 3) :
    IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * crossC (u p) w i) K.rect := by
  have hm := LowEntry.Internal.rect_meas K
  fin_cases i
  · exact IntegrableOn.congr_fun (((hu 1).const_mul (w 2)).sub ((hu 2).const_mul (w 1)))
      (fun p _ => by simp [crossC] <;> ring) hm
  · exact IntegrableOn.congr_fun (((hu 2).const_mul (w 0)).sub ((hu 0).const_mul (w 2)))
      (fun p _ => by simp [crossC] <;> ring) hm
  · exact IntegrableOn.congr_fun (((hu 0).const_mul (w 1)).sub ((hu 1).const_mul (w 0)))
      (fun p _ => by simp [crossC] <;> ring) hm

private theorem sum_algebra (RM res : Finset ℤ) (Ig : ℤ → Fin 3 → Fin 3 → ℂ) (Iv : ℤ → Fin 3 → ℂ)
    (Jg : ℤ → ℤ → Fin 3 → Fin 3 → ℂ) (Jv : ℤ → ℤ → Fin 3 → ℂ)
    (h : ∀ m ∈ RM, m ∉ res → (∀ i j, Ig m i j = 0) ∧ ∀ i, Iv m i = 0) :
    ∑ m ∈ RM, (∑ i, ∑ j, Ig m i j + ∑ i, Iv m i + ∑ n ∈ res, (∑ i, ∑ j, Jg m n i j + ∑ i, Jv m n i)) =
    ∑ n ∈ res, ∑ i, ∑ j, ∑ m ∈ RM, ((if m = n then Ig m i j else 0) + Jg m n i j) +
    ∑ n ∈ res, ∑ i, ∑ m ∈ RM, ((if m = n then Iv m i else 0) + Jv m n i) := by
  have hG : ∑ m ∈ RM, ∑ i, ∑ j, Ig m i j = ∑ n ∈ res, ∑ i, ∑ j, ∑ m ∈ RM, (if m = n then Ig m i j else 0) := by
    have e1 : ∑ m ∈ RM, ∑ i, ∑ j, Ig m i j = ∑ m ∈ RM, (if m ∈ res then ∑ i, ∑ j, Ig m i j else 0) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      by_cases hr : m ∈ res
      · rw [if_pos hr]
      · rw [if_neg hr]; simp [(h m hm hr).1]
    have e2 : ∀ n, ∑ i, ∑ j, ∑ m ∈ RM, (if m = n then Ig m i j else 0) = if n ∈ RM then ∑ i, ∑ j, Ig n i j else 0 := by
      intro n
      simp only [Finset.sum_ite_eq']
      split_ifs <;> simp
    rw [e1, Finset.sum_congr rfl fun n _ => e2 n, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_comm]
  have hV : ∑ m ∈ RM, ∑ i, Iv m i = ∑ n ∈ res, ∑ i, ∑ m ∈ RM, (if m = n then Iv m i else 0) := by
    have e1 : ∑ m ∈ RM, ∑ i, Iv m i = ∑ m ∈ RM, (if m ∈ res then ∑ i, Iv m i else 0) := by
      refine Finset.sum_congr rfl fun m hm => ?_
      by_cases hr : m ∈ res
      · rw [if_pos hr]
      · rw [if_neg hr]; simp [(h m hm hr).2]
    have e2 : ∀ n, ∑ i, ∑ m ∈ RM, (if m = n then Iv m i else 0) = if n ∈ RM then ∑ i, Iv n i else 0 := by
      intro n
      simp only [Finset.sum_ite_eq']
      split_ifs <;> simp
    rw [e1, Finset.sum_congr rfl fun n _ => e2 n, Finset.sum_ite_mem, Finset.sum_ite_mem, Finset.inter_comm]
  have hJg : ∑ m ∈ RM, ∑ n ∈ res, ∑ i, ∑ j, Jg m n i j = ∑ n ∈ res, ∑ i, ∑ j, ∑ m ∈ RM, Jg m n i j := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
  have hJv : ∑ m ∈ RM, ∑ n ∈ res, ∑ i, Jv m n i = ∑ n ∈ res, ∑ i, ∑ m ∈ RM, Jv m n i := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_comm]
  simp only [Finset.sum_add_distrib]
  rw [hG, hV, hJg, hJv]
  ring


private theorem int_sum4 {μ : Measure (ℝ × ℝ)} (s : Finset ℤ) (f1 : Fin 3 → Fin 3 → ℝ × ℝ → ℂ)
    (f2 : Fin 3 → ℝ × ℝ → ℂ) (g1 : ℤ → Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (g2 : ℤ → Fin 3 → ℝ × ℝ → ℂ)
    (h1 : ∀ i j, Integrable (f1 i j) μ) (h2 : ∀ i, Integrable (f2 i) μ)
    (h3 : ∀ n i j, Integrable (g1 n i j) μ) (h4 : ∀ n i, Integrable (g2 n i) μ) :
    ∫ p, (∑ i, ∑ j, f1 i j p + ∑ i, f2 i p + ∑ n ∈ s, (∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p)) ∂μ =
      ∑ i, ∑ j, ∫ p, f1 i j p ∂μ + ∑ i, ∫ p, f2 i p ∂μ +
        ∑ n ∈ s, (∑ i, ∑ j, ∫ p, g1 n i j p ∂μ + ∑ i, ∫ p, g2 n i p ∂μ) := by
  have i1 : Integrable (fun p => ∑ i, ∑ j, f1 i j p) μ :=
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j
  have i2 : Integrable (fun p => ∑ i, f2 i p) μ := integrable_finsetSum _ fun i _ => h2 i
  have i3 : ∀ n, Integrable (fun p => ∑ i, ∑ j, g1 n i j p) μ := fun n =>
    integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h3 n i j
  have i4 : ∀ n, Integrable (fun p => ∑ i, g2 n i p) μ := fun n => integrable_finsetSum _ fun i _ => h4 n i
  have i12 : Integrable (fun p => ∑ i, ∑ j, f1 i j p + ∑ i, f2 i p) μ := i1.add i2
  have i34 : ∀ n, Integrable (fun p => ∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p) μ := fun n => (i3 n).add (i4 n)
  have iS : Integrable (fun p => ∑ n ∈ s, (∑ i, ∑ j, g1 n i j p + ∑ i, g2 n i p)) μ :=
    integrable_finsetSum _ fun n _ => i34 n
  rw [integral_add i12 iS, integral_add i1 i2, integral_finsetSum _ fun n _ => i34 n,
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h1 i j, integral_finsetSum _ fun i _ => h2 i]
  congr 1
  · congr 1
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => h1 i j
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_add (i3 n) (i4 n), integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => h3 n i j,
      integral_finsetSum _ fun i _ => h4 n i]
    congr 1
    exact Finset.sum_congr rfl fun i _ => integral_finsetSum _ fun j _ => h3 n i j

theorem volume_sum_identity {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) :
    (∫ p in K.rect, p.1 * (∑ m ∈ R.rowModes,
        volumeDensity c K S α c.splitVisc x m (rowModeVec c a m p) (rowModeGrad c a m p) p).re) =
      (strainSum c α L R a x + velocitySum c α L R a x).re := by
  have hK : IsCellBox K := hD.box
  have hB : IsCellBases K B := hL.layout.bases_valid
  have hcpt := LowEntry.Internal.rect_compact K
  have hrm := LowEntry.Internal.rect_meas K
  have hdeg2 : 2 ≤ S.degHigh := by
    have h1 := hL.layout.degSide_pos; have h2 := hL.layout.degSide_le; have h3 := hL.layout.degCoef_eq; omega
  have hGw : ∀ n i j, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * gradMode c.order n x.2.1 i j p) K.rect :=
    fun n i j => LowEntry.Internal.gradMode_int K hK c.order n hx.1.measurable_gradient hx.1.gradient_two i j
  have hVw : ∀ n i, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * modeVec c.order n x.1 p.1 p.2 i) K.rect :=
    fun n i => LowEntry.Internal.modeVec_int K hK c.order n hx.1.velocity_six i
  obtain ⟨CM, hCM⟩ := hc.model_bounded
  have hfin : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hfin.ne
  have hMV : IntegrableOn (fun y => ‖c.modelVelocity y‖) K.solid :=
    Integrable.mono' (integrable_const CM) hc.model_measurable.1.norm.restrict
      ((ae_restrict_iff' (solid_meas' K)).2 (ae_of_all _ fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact (hCM y (hD.solid_in_region hy)).1))
  have hMW : IntegrableOn (fun y => ‖c.modelCurl y‖) K.solid :=
    Integrable.mono' (integrable_const CM) hc.model_measurable.2.1.norm.restrict
      ((ae_restrict_iff' (solid_meas' K)).2 (ae_of_all _ fun y hy => by
        rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]; exact (hCM y (hD.solid_in_region hy)).2.1))
  have hXp := hR.row_low_velocity a ha
  have hSC : ∀ m n i j, IntegrableOn (fun p => (p.1 : ℂ) * strainCross c a m n i j p) K.rect := fun m n i j =>
    int_pair hK (U := fun p => crossC (fun l => (permSign l j i : ℂ)) (modeVec c.order (m - n) c.modelVelocity p.1 p.2))
      (X := fun p => rowModeVec c a m p)
      (cross_left_int _ (fun l => modeVec_int_on hK c.order (m - n) hc.model_measurable.1 hMV l)) (hXp m)
  have hVC : ∀ m n i, IntegrableOn (fun p => (p.1 : ℂ) * velCross c a m n i p) K.rect := fun m n i =>
    int_pair hK (U := fun p => crossC (modeVec c.order (m - n) c.modelCurl p.1 p.2) (Pi.single i 1))
      (X := fun p => rowModeVec c a m p)
      (cross_right_int _ (fun l => modeVec_int_on hK c.order (m - n) hc.model_measurable.2.1 hMW l)) (hXp m)
  have hSD := strainDiag_poly (α := α) hR ha
  have hVD := velDiag_poly (α := α) hR ha
  have iG : ∀ m i j, IntegrableOn (fun p => (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p)
      K.rect := fun m i j => int_poly hK (hGw m i j) (hSD m i j)
  have iV : ∀ m i, IntegrableOn (fun p => (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p)
      K.rect := fun m i => int_poly hK (F := fun p => modeVec c.order m x.1 p.1 p.2 i) (hVw m i) (hVD m i)
  have iJg : ∀ m n i j, IntegrableOn (fun p => (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p *
      strainCross c a m n i j p) K.rect := fun m n i j =>
    IntegrableOn.congr_fun ((hSC m n i j).continuousOn_mul (proj_cont' K _ _ _).continuousOn hcpt)
      (fun p _ => by ring) hrm
  have iJv : ∀ m n i, IntegrableOn (fun p => (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1)
      (fun q => modeVec c.order n x.1 q.1 q.2 i) p * velCross c a m n i p) K.rect := fun m n i =>
    IntegrableOn.congr_fun ((hVC m n i).continuousOn_mul (proj_cont' K _ _ _).continuousOn hcpt)
      (fun p _ => by ring) hrm
  have hzero : ∀ m ∈ R.rowModes, m ∉ S.resolved →
      (∀ i j, ∫ p in K.rect, (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p = 0) ∧
      ∀ i, ∫ p in K.rect, (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p = 0 := by
    intro m _ hmr
    have hres := hD.row_mode_resolved a ha
    have h1 : m ≠ R.rowModeOf a := fun h => hmr (h ▸ hres)
    have h2 : m ≠ -R.rowModeOf a := fun h => hmr (h ▸ (hD.scalars.resolved_symm _).1 hres)
    have hX0 : ∀ q ∈ K.rect, CellScalars.rowMode c a m q = 0 := hD.row_mode_of a ha m h1 h2
    have hX0' : ∀ q ∈ K.rect, ∀ i, rowModeVec c a m q i = 0 := fun q hq i => congrFun (hX0 q hq) i
    constructor
    · intro i j
      refine integral_eq_zero_of_ae ?_
      filter_upwards [open_ae K] with p hp
      have hpr : p ∈ K.rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
      simp only [strainDiag, hX0' p hpr, grad_mode_zero hc hD hR ha hX0 hp, map_zero, mul_zero, add_zero,
        Pi.zero_apply]
    · intro i
      refine integral_eq_zero_of_ae ?_
      filter_upwards [open_ae K] with p hp
      have hpr : p ∈ K.rect := ⟨⟨hp.1.1.le, hp.1.2.le⟩, ⟨hp.2.1.le, hp.2.2.le⟩⟩
      have e : rowModeVec c a m p = 0 := funext (hX0' p hpr)
      simp only [velDiag, e, hX0' p hpr, pairC, Pi.zero_apply, map_zero, mul_zero, Finset.sum_const_zero, sub_zero]
  have hRHS : strainSum c α L R a x + velocitySum c α L R a x =
      ∑ n ∈ S.resolved, ∑ i, ∑ j, ∑ m ∈ R.rowModes,
        ((if m = n then ∫ p in K.rect, (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p else 0) +
          ∫ p in K.rect, (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p *
            strainCross c a m n i j p) +
      ∑ n ∈ S.resolved, ∑ i, ∑ m ∈ R.rowModes,
        ((if m = n then ∫ p in K.rect, (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p else 0) +
          ∫ p in K.rect, (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1)
            (fun q => modeVec c.order n x.1 q.1 q.2 i) p * velCross c a m n i p) := by
    have hord := hL.layout.order_eq
    have hbox := hL.layout.box_eq
    have hbas := hL.layout.bases_eq
    have hmod := hL.layout.modes_eq
    have hdeg := hL.layout.degCoef_eq
    rcases L with ⟨order, box, bases, modes, degCoef, degSide, segCount, segment, presCount, presSegment,
      cornerCount, corner, cornerOther, segEnd, cellCorner, sideSegments, gauge, gaugeDeleted⟩
    dsimp only at hord hbox hbas hmod hdeg
    subst hord hbox hbas hmod hdeg
    simp only [strainSum, velocitySum, CellLayout.gradModeOf, CellLayout.velMode, Fintype.sum_prod_type]
    congr 1
    · rw [← Finset.sum_coe_sort S.resolved]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      refine (gen_term hK hB S.degHigh (S.degHigh + 1) rfl R.rowModes n (F := gradMode c.order n x.2.1 i j)
        (fun m p => strainDiag c α a m i j p) (fun m p => strainCross c a m n i j p) (hGw n i j)
        (fun m => hSD m i j) (fun m => hSC m n i j)).trans ?_
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : m = (n : ℤ)
      · subst h; rfl
      · simp only [h, if_false]
    · rw [← Finset.sum_coe_sort S.resolved]
      refine Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun i _ => ?_
      refine (gen_term hK hB (S.degHigh - 1) S.degHigh (by omega) R.rowModes n
        (F := fun p => modeVec c.order n x.1 p.1 p.2 i) (fun m p => velDiag c α a m i p)
        (fun m p => velCross c a m n i p) (hVw n i) (fun m => hVD m i) (fun m => hVC m n i)).trans ?_
      refine Finset.sum_congr rfl fun m _ => ?_
      by_cases h : m = (n : ℤ)
      · subst h; rfl
      · simp only [h, if_false]
  have hpt : ∀ p : ℝ × ℝ, (p.1 : ℂ) * ∑ m ∈ R.rowModes,
      volumeDensity c K S α c.splitVisc x m (rowModeVec c a m p) (rowModeGrad c a m p) p =
      ∑ m ∈ R.rowModes, (∑ i, ∑ j, (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p
        + ∑ i, (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p
        + ∑ n ∈ S.resolved, (∑ i, ∑ j, (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p *
            strainCross c a m n i j p
          + ∑ i, (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1)
            (fun q => modeVec c.order n x.1 q.1 q.2 i) p * velCross c a m n i p)) := by
    intro p
    simp only [volumeDensity, strainDiag, velDiag, strainCross, velCross, CellBox.lowStrain, CellBox.lowVelocity,
      Finset.mul_sum, mul_add, mul_assoc]
  have hIm : ∀ m, IntegrableOn (fun p : ℝ × ℝ =>
      ∑ i, ∑ j, (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p
        + ∑ i, (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p
        + ∑ n ∈ S.resolved, (∑ i, ∑ j, (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p *
            strainCross c a m n i j p
          + ∑ i, (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1)
            (fun q => modeVec c.order n x.1 q.1 q.2 i) p * velCross c a m n i p)) K.rect := fun m =>
    ((integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => iG m i j).add
      (integrable_finsetSum _ fun i _ => iV m i)).add
      (integrable_finsetSum _ fun n _ => (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ =>
        iJg m n i j).add (integrable_finsetSum _ fun i _ => iJv m n i))
  have hIc := integrable_finsetSum R.rowModes fun m _ => hIm m
  have e1 : (∫ p in K.rect, p.1 * (∑ m ∈ R.rowModes,
      volumeDensity c K S α c.splitVisc x m (rowModeVec c a m p) (rowModeGrad c a m p) p).re) =
      (∫ p in K.rect, ∑ m ∈ R.rowModes, (∑ i, ∑ j, (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p
        + ∑ i, (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p
        + ∑ n ∈ S.resolved, (∑ i, ∑ j, (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p *
            strainCross c a m n i j p
          + ∑ i, (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1)
            (fun q => modeVec c.order n x.1 q.1 q.2 i) p * velCross c a m n i p))).re := by
    have h := integral_re hIc
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine setIntegral_congr_fun hrm fun p _ => ?_
    rw [← hpt p]
    simp
  rw [e1, hRHS, integral_finsetSum _ fun m _ => hIm m]
  congr 1
  rw [← sum_algebra R.rowModes S.resolved
    (fun m i j => ∫ p in K.rect, (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p)
    (fun m i => ∫ p in K.rect, (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p)
    (fun m n i j => ∫ p in K.rect, (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p *
            strainCross c a m n i j p)
    (fun m n i => ∫ p in K.rect, (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1)
            (fun q => modeVec c.order n x.1 q.1 q.2 i) p * velCross c a m n i p) hzero]
  refine Finset.sum_congr rfl fun m _ => ?_
  exact int_sum4 S.resolved
    (fun i j p => (p.1 : ℂ) * gradMode c.order m x.2.1 i j p * strainDiag c α a m i j p)
    (fun i p => (p.1 : ℂ) * modeVec c.order m x.1 p.1 p.2 i * velDiag c α a m i p)
    (fun n i j p => (p.1 : ℂ) * K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 i j) p * strainCross c a m n i j p)
    (fun n i p => (p.1 : ℂ) * K.proj (S.degHigh - 1) (S.degHigh - 1) (fun q => modeVec c.order n x.1 q.1 q.2 i) p *
      velCross c a m n i p)
    (fun i j => iG m i j) (fun i => iV m i) (fun n i j => iJg m n i j) (fun n i => iJv m n i)
end Breakdown.FracInternal.LayoutRowVolumeSplit
