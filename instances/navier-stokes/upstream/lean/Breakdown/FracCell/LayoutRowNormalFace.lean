import Breakdown.FracCell.LayoutRowViscousSides

open MeasureTheory Set Matrix

noncomputable section

namespace Breakdown.FracInternal.LayoutRowNormalFace

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly LayoutRowParts LayoutRowViscousSides

theorem range_sum_fin {m l : ℕ} (hl : l < m) (g : ℕ → ℂ) :
    ∑ i : Fin m, (if (i : ℕ) ≤ l then g i else 0) = ∑ i ∈ Finset.range (l + 1), g i := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i ≤ l then g i else 0) m, ← Finset.sum_filter]
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

theorem poly_span {m : ℕ} {coef : ℕ → ℕ → ℝ} (hlead : ∀ l, coef l l ≠ 0) {p : ℕ → ℝ → ℝ}
    (hp : ∀ l u, p l u = ∑ i ∈ Finset.range (l + 1), coef l i * u ^ i) (cf : Fin m → ℂ) :
    ∃ β : Fin m → ℂ, ∀ u : ℝ, ∑ d : Fin m, cf d * (u : ℂ) ^ (d : ℕ) = ∑ l : Fin m, β l * ((p l u : ℝ) : ℂ) := by
  classical
  obtain ⟨M, hMe⟩ : ∃ M : Matrix (Fin m) (Fin m) ℂ, ∀ i l, M i l = if (i : ℕ) ≤ l then (coef l i : ℂ) else 0 :=
    ⟨fun i l => if (i : ℕ) ≤ l then (coef l i : ℂ) else 0, fun _ _ => rfl⟩
  have hM : M.BlockTriangular id := by
    intro i j hij
    have : ¬ ((i : ℕ) ≤ j) := fun h => absurd (Fin.le_def.2 h) (not_le.mpr hij)
    rw [hMe, if_neg this]
  have hdet : IsUnit M.det := by
    rw [Matrix.det_of_upperTriangular hM, isUnit_iff_ne_zero, Finset.prod_ne_zero_iff]
    intro i _
    rw [hMe, if_pos le_rfl]
    exact_mod_cast hlead i
  obtain ⟨β, hβ⟩ : ∃ β, M *ᵥ β = cf :=
    ⟨M⁻¹ *ᵥ cf, by rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hdet, Matrix.one_mulVec]⟩
  refine ⟨β, fun u => ?_⟩
  rw [← hβ]
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hp]
  push_cast
  rw [Finset.mul_sum, ← range_sum_fin l.isLt]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [hMe]
  split_ifs <;> ring

theorem poly_expand {m : ℕ} {coef : ℕ → ℕ → ℝ} (hlead : ∀ l, coef l l ≠ 0) {p : ℕ → ℝ → ℝ}
    (hp : ∀ l u, p l u = ∑ i ∈ Finset.range (l + 1), coef l i * u ^ i) {a b : ℝ} {w : ℝ → ℝ}
    (hw : ContinuousOn w (Icc a b))
    (horth : ∀ l l', l < m → l' < m → ∫ u in Icc a b, w u * p l u * p l' u = if l = l' then 1 else 0)
    (cf : Fin m → ℂ) (t : ℝ) :
    ∑ d : Fin m, cf d * (t : ℂ) ^ (d : ℕ) =
      ∑ l : Fin m, (∫ u in Icc a b, ((w u * p l u : ℝ) : ℂ) * ∑ d : Fin m, cf d * (u : ℂ) ^ (d : ℕ)) *
        ((p l t : ℝ) : ℂ) := by
  obtain ⟨β, hβ⟩ := poly_span hlead hp cf
  have hpc : ∀ l, Continuous (p l) := fun l => by
    have : p l = fun u => ∑ i ∈ Finset.range (l + 1), coef l i * u ^ i := funext (hp l)
    rw [this]; fun_prop
  have hcoef : ∀ l : Fin m, ∫ u in Icc a b, ((w u * p l u : ℝ) : ℂ) * ∑ d : Fin m, cf d * (u : ℂ) ^ (d : ℕ) =
      β l := by
    intro l
    have hfun : (fun u => ((w u * p l u : ℝ) : ℂ) * ∑ d : Fin m, cf d * (u : ℂ) ^ (d : ℕ)) =
        fun u => ∑ l' : Fin m, β l' * ((w u * p l u * p l' u : ℝ) : ℂ) := by
      funext u
      rw [hβ u, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l' _ => ?_)
      push_cast; ring
    rw [hfun, integral_finsetSum]
    · have hterm : ∀ l' : Fin m, ∫ u in Icc a b, β l' * ((w u * p l u * p l' u : ℝ) : ℂ) =
          if l' = l then β l else 0 := by
        intro l'
        rw [integral_const_mul, integral_complex_ofReal, horth l l' l.isLt l'.isLt]
        by_cases h : l' = l
        · subst h; simp
        · have h' : (l : ℕ) ≠ l' := fun e => h (Fin.ext e.symm)
          simp [h, h']
      simp_rw [hterm]
      simp
    · intro l' _
      exact ContinuousOn.integrableOn_compact isCompact_Icc
        (continuousOn_const.mul (Complex.continuous_ofReal.comp_continuousOn
          ((hw.mul (hpc l).continuousOn).mul (hpc l').continuousOn)))
  rw [hβ t]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hcoef l]


def gradSideNormalSum {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (a : Fin N) (x : FieldTuple k) : ℂ :=
  ∑ i : L.modes × Fin L.segCount × Fin 3 × Fin (L.degSide + 1),
    (if i.2.2.1 = segmentNormal L i.2.1 then gradSideRowCoef c L a i.1.1 i.2.1 i.2.2.1 i.2.2.2 *
      (if (L.segment i.2.1).radial then
        (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 0)
          (L.secondModeOf i.1 x i.2.2.1 0 0) (L.secondModeOf i.1 x i.2.2.1 0 2) i.2.2.2
      else (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 2)
          (L.secondModeOf i.1 x i.2.2.1 2 0) (L.secondModeOf i.1 x i.2.2.1 2 2) i.2.2.2) else 0)

def gradSideTangentSum {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (a : Fin N) (x : FieldTuple k) : ℂ :=
  ∑ i : L.modes × Fin L.segCount × Fin 3 × Fin (L.degSide + 1),
    (if i.2.2.1 = segmentNormal L i.2.1 then 0 else gradSideRowCoef c L a i.1.1 i.2.1 i.2.2.1 i.2.2.2) *
      (if (L.segment i.2.1).radial then
        (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 0)
          (L.secondModeOf i.1 x i.2.2.1 0 0) (L.secondModeOf i.1 x i.2.2.1 0 2) i.2.2.2
      else (L.segment i.2.1).moment true (L.gradModeOf i.1 x i.2.2.1 2)
          (L.secondModeOf i.1 x i.2.2.1 2 0) (L.secondModeOf i.1 x i.2.2.1 2 2) i.2.2.2)

theorem gradSide_split {k N : ℕ} (c : FracCellData k N) (L : CellLayout) (a : Fin N) (x : FieldTuple k) :
    gradSideSum c L a x = gradSideTangentSum c L a x + gradSideNormalSum c L a x := by
  unfold gradSideSum gradSideTangentSum gradSideNormalSum
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  split_ifs <;> ring

private theorem edge_alg (ν E v X I : ℂ) (h : E * E = 1) : -ν * ((v * X) * I) = -ν * E * v * (X * (E * I)) := by
  linear_combination (ν * v * X * I) * h

private theorem edge_alg' (ν E X I : ℂ) (h : E * E = 1) : -ν * (X * I) = -ν * E * (X * (E * I)) := by
  linear_combination (ν * X * I) * h

theorem radial_face {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1))
    (n : ℤ) {v o : ℝ} (hv : v = K.r₂ ∨ (v = K.r₁ ∧ K.r₁ ≠ 0)) (ho : o = K.r₁ + K.r₂ - v)
    (Pl : ℝ → ℂ) (cfl : Fin (L.degSide + 1) → ℂ) (hPl : ∀ t, Pl t = ∑ d, cfl d * (t : ℂ) ^ (d : ℕ))
    (hrow : ∀ z ∈ Icc K.z₁ K.z₂, rowModeVec c a n (v, z) 0 = Pl z) :
    ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
      ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
        (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d =
    -(c.splitVisc : ℂ) * edgeSign v o * (v : ℂ) * ∑ l : Fin (L.degSide + 1),
      (starRingEnd ℂ) (∫ z in Icc K.z₁ K.z₂, rowModeVec c a n (v, z) 0 * ((L.bases.heightPoly l z : ℝ) : ℂ)) *
        radialStripMoment v o K.z₁ K.z₂ (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.bases.heightPoly l) := by
  have hK := hD.box
  have hr := hK.r_order
  have hz := hK.z_order
  have hB : IsCellBases K L.bases := by rw [hL.layout.bases_eq]; exact hL.layout.bases_valid
  have hord : L.order = c.order := hL.layout.order_eq
  have hW := modes_radial_pair_gradient c x hx L hord n 0
  have hvmem : v ∈ Icc K.r₁ K.r₂ := by
    rcases hv with h | ⟨h, _⟩ <;> rw [h] <;> constructor <;> linarith
  have hvo : v ≠ o ∧ min v o = K.r₁ ∧ max v o = K.r₂ := by
    rw [ho]
    rcases hv with h | ⟨h, _⟩ <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> simp [min_def, max_def] <;> intros <;> linarith
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  choose P hPcf hPtr using fun s => hseg a ha s n 0
  choose cf hcf using hPcf
  have hcoef : ∀ s (d : Fin (L.degSide + 1)), gradSideRowCoef c L a n s 0 d =
      -(c.splitVisc : ℂ) * edgeSign (L.segment s).level (L.segment s).other *
        (if (L.segment s).radial then ((L.segment s).level : ℂ) else 1) * (starRingEnd ℂ) (cf s d) := by
    intro s d
    unfold gradSideRowCoef
    rw [trace_coef hα1 hα2 hc hD hR hL hx ha n s 0 (P s) (hPtr s) d]
    have hP : P s = fun t => ∑ d', cf s d' * (((L.segment s).test d' t : ℝ) : ℂ) := funext (hcf s)
    rw [hP, coef_of_trace (L.segment s) (L.degSide + 1)
      (fun d d' hd hd' => hL.layout.segment_orthonormal s d d' (by omega) (by omega)) (cf s) d]
  obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n 0
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hC.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (K.r₁, K.z₁) ⟨⟨le_rfl, hr.2.le⟩, le_rfl, hz.2.le⟩)
  have hRb : ∀ p ∈ K.rect, |p.1| ≤ K.r₂ := fun p hp => by
    rw [abs_of_nonneg (hr.1.trans hp.1.1)]; exact hp.1.2
  have hGL := lp_coord_slope hC hRb hM (hr.1.trans hr.2.le) hM0
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun q => (q.1 : ℂ) * (starRingEnd ℂ) (rowModeVec c a n q 0) := ⟨_, rfl⟩
  rw [← hGdef] at hGL
  have hGc : ContinuousOn G K.rect := hGL.continuousOn
  have hGv : ∀ s, (L.segment s).radial = true → (L.segment s).level = v → ∀ z ∈ Icc K.z₁ K.z₂,
      G (v, z) = (v : ℂ) * ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) * ((L.segment s).test d z : ℂ) := by
    intro s hrad hlev z hz'
    have h := (hPtr s (v, z) ⟨hvmem, hz'⟩).1 hrad hlev.symm
    rw [hGdef]
    try simp only
    rw [h, hcf s, map_sum]
    simp [map_mul, Complex.conj_ofReal]
  have hside := radial_side_sum (dFz := L.secondModeOf n x 0 0 2) hK hL hW hGc cf hv ho hGv
  have hL1 : ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
      ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
        (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d =
      -(c.splitVisc : ℂ) * ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
        ∑ d : Fin (L.degSide + 1), edgeSign (L.segment s).level (L.segment s).other *
          ((L.segment s).level : ℂ) * (starRingEnd ℂ) (cf s d) *
            (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hrad : (L.segment s).radial = true := (Finset.mem_filter.1 hs).2.1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hcoef s d, if_pos hrad]
    ring
  rw [hL1, ← hside]
  have hexp : ∀ z : ℝ, Pl z = ∑ l : Fin (L.degSide + 1),
      (∫ u in Icc K.z₁ K.z₂, rowModeVec c a n (v, u) 0 * ((L.bases.heightPoly l u : ℝ) : ℂ)) *
        ((L.bases.heightPoly l z : ℝ) : ℂ) := by
    intro z
    have h := poly_expand (m := L.degSide + 1) (coef := L.bases.heightCoef) (fun l => (hB.height_leading l).ne')
      (p := L.bases.heightPoly) (fun l u => rfl) (a := K.z₁) (b := K.z₂) (w := fun _ => 1) continuousOn_const
      (fun l l' _ _ => by simpa using hB.height_orthonormal l l') cfl z
    rw [hPl z, h]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    try simp only
    rw [hrow u hu, ← hPl u]
    push_cast
    ring
  have hGexp : ∀ p ∈ K.rect, G (v, p.2) = ∑ l : Fin (L.degSide + 1), ((v : ℂ) * (starRingEnd ℂ)
      (∫ u in Icc K.z₁ K.z₂, rowModeVec c a n (v, u) 0 * ((L.bases.heightPoly l u : ℝ) : ℂ))) *
        ((L.bases.heightPoly l p.2 : ℝ) : ℂ) := by
    intro p hp
    rw [hGdef]
    try simp only
    rw [hrow p.2 hp.2, hexp p.2, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
    ring
  have hF : IntegrableOn (L.gradModeOf n x 0 0) K.rect :=
    (hW.1 K.r₂ (|K.z₁| + |K.z₂|)).1.mono_set (prod_mono (Icc_subset_Icc_left hr.1) (lp_box_sub _ _))
  have hdFt : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p) K.rect := by
    rcases hr.1.lt_or_eq with h0 | h0
    · have hd : IntegrableOn (L.secondModeOf n x 0 0 0) K.rect :=
        (hW.2.1 K.r₁ K.r₂ (|K.z₁| + |K.z₂|) h0).mono_set (prod_mono subset_rfl (lp_box_sub _ _))
      exact IntegrableOn.continuousOn_mul (by fun_prop) hd hcomp
    · have ho0 : o = 0 := by
        rcases hv with h | ⟨_, h⟩
        · rw [ho, h, ← h0]; ring
        · exact absurd h0.symm h
      have hrd : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x 0 0 0 p) K.rect :=
        (hW.1 K.r₂ (|K.z₁| + |K.z₂|)).2.mono_set (prod_mono (Icc_subset_Icc_left hr.1) (lp_box_sub _ _))
      refine IntegrableOn.congr_fun (hrd.const_mul (((1 / (v - o) : ℝ)) : ℂ)) (fun p _ => ?_) hmeas
      simp only [ho0, sub_zero]; push_cast; ring
  have hWint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 0 0 p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p)) K.rect := (hF.const_mul _).add hdFt
  have hpoly : ∀ l, Continuous (L.bases.heightPoly l) := fun l => by
    unfold CellBases.heightPoly; fun_prop
  have hint : ∀ l : Fin (L.degSide + 1), IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 0 0 p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p) *
      ((L.bases.heightPoly l p.2 : ℝ) : ℂ)) K.rect := fun l =>
    hWint.mul_continuousOn (Complex.continuous_ofReal.comp ((hpoly l).comp continuous_snd)).continuousOn hcomp
  have hI : ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 0 0 p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p) * G (v, p.2) =
      ∑ l : Fin (L.degSide + 1), ((v : ℂ) * (starRingEnd ℂ)
        (∫ u in Icc K.z₁ K.z₂, rowModeVec c a n (v, u) 0 * ((L.bases.heightPoly l u : ℝ) : ℂ))) *
        ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 0 0 p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p) * ((L.bases.heightPoly l p.2 : ℝ) : ℂ) := by
    rw [setIntegral_congr_fun hmeas (g := fun p => ∑ l : Fin (L.degSide + 1), ((v : ℂ) * (starRingEnd ℂ)
        (∫ u in Icc K.z₁ K.z₂, rowModeVec c a n (v, u) 0 * ((L.bases.heightPoly l u : ℝ) : ℂ))) *
        (((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 0 0 p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p) * ((L.bases.heightPoly l p.2 : ℝ) : ℂ))) (fun p hp => ?_)]
    · rw [integral_finsetSum _ (fun l _ => (hint l).const_mul _)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul]
    · try simp only
      rw [hGexp p hp, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
  have hstrip : ∀ l : Fin (L.degSide + 1),
      radialStripMoment v o K.z₁ K.z₂ (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.bases.heightPoly l) =
        edgeSign v o * ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 0 0 p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 0 0 0 p) * ((L.bases.heightPoly l p.2 : ℝ) : ℂ) := by
    intro l
    unfold radialStripMoment
    rw [hvo.2.1, hvo.2.2, ← hrect]
  rw [hI, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hstrip l]
  exact edge_alg _ _ _ _ _ (lp_edge_sq v o)

theorem height_face {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1))
    (n : ℤ) {v o : ℝ} (hv : v = K.z₁ ∨ v = K.z₂) (ho : o = K.z₁ + K.z₂ - v)
    (Pl : ℝ → ℂ) (cfl : Fin (L.degSide + 1) → ℂ) (hPl : ∀ t, Pl t = ∑ d, cfl d * (t : ℂ) ^ (d : ℕ))
    (hrow : ∀ r ∈ Icc K.r₁ K.r₂, rowModeVec c a n (r, v) 2 = Pl r) :
    ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
      ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
        (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d =
    -(c.splitVisc : ℂ) * edgeSign v o * ∑ l : Fin (L.degSide + 1),
      (starRingEnd ℂ) (∫ r in Icc K.r₁ K.r₂, ((K.lineWeight r * L.bases.radialPoly l r : ℝ) : ℂ) *
        rowModeVec c a n (r, v) 2) *
        heightStripMoment v o K.r₁ K.r₂ (fun r => r) (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2)
          (L.bases.radialPoly l) := by
  have hK := hD.box
  have hr := hK.r_order
  have hz := hK.z_order
  have hB : IsCellBases K L.bases := by rw [hL.layout.bases_eq]; exact hL.layout.bases_valid
  have hord : L.order = c.order := hL.layout.order_eq
  have hW := modes_height_pair_gradient c x hx L hord n 2
  have hvmem : v ∈ Icc K.z₁ K.z₂ := by
    rcases hv with h | h <;> rw [h] <;> constructor <;> linarith
  have hvo : v ≠ o ∧ min v o = K.z₁ ∧ max v o = K.z₂ := by
    rw [ho]
    rcases hv with h | h <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> simp [min_def, max_def] <;> intros <;> linarith
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  choose P hPcf hPtr using fun s => hseg a ha s n 2
  choose cf hcf using hPcf
  have hcoef : ∀ s (d : Fin (L.degSide + 1)), gradSideRowCoef c L a n s 2 d =
      -(c.splitVisc : ℂ) * edgeSign (L.segment s).level (L.segment s).other *
        (if (L.segment s).radial then ((L.segment s).level : ℂ) else 1) * (starRingEnd ℂ) (cf s d) := by
    intro s d
    unfold gradSideRowCoef
    rw [trace_coef hα1 hα2 hc hD hR hL hx ha n s 2 (P s) (hPtr s) d]
    have hP : P s = fun t => ∑ d', cf s d' * (((L.segment s).test d' t : ℝ) : ℂ) := funext (hcf s)
    rw [hP, coef_of_trace (L.segment s) (L.degSide + 1)
      (fun d d' hd hd' => hL.layout.segment_orthonormal s d d' (by omega) (by omega)) (cf s) d]
  obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n 2
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun q => (starRingEnd ℂ) (rowModeVec c a n q 2) := ⟨_, rfl⟩
  have hGL : LipschitzOnWith C G K.rect := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [hGdef]
    try simp only
    rw [Complex.dist_conj_conj]
    exact hC.dist_le_mul p hp q hq
  have hGc : ContinuousOn G K.rect := hGL.continuousOn
  have hGv : ∀ s, (L.segment s).radial = false → (L.segment s).level = v → ∀ r ∈ Icc K.r₁ K.r₂,
      G (r, v) = ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) * ((L.segment s).test d r : ℂ) := by
    intro s hrad hlev r hr'
    have h := (hPtr s (r, v) ⟨hr', hvmem⟩).2 (by simp [hrad]) hlev.symm
    rw [hGdef]
    try simp only
    rw [h, hcf s, map_sum]
    simp [map_mul, Complex.conj_ofReal]
  have hside := height_side_sum (dFr := L.secondModeOf n x 2 2 0) hK hL hW hGc cf hv ho hGv
  have hL1 : ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
      ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
        (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d =
      -(c.splitVisc : ℂ) * ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
        ∑ d : Fin (L.degSide + 1), edgeSign (L.segment s).level (L.segment s).other * (starRingEnd ℂ) (cf s d) *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun s hs => ?_)
    have hrad : (L.segment s).radial = false := (Finset.mem_filter.1 hs).2.1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [hcoef s d, if_neg (by simp [hrad])]
    ring
  rw [hL1, ← hside]
  have hwc : ContinuousOn K.lineWeight (Icc K.r₁ K.r₂) := by
    by_cases h0 : K.r₁ = 0
    · have e : K.lineWeight = fun r => r := by funext r; simp [CellBox.lineWeight, h0]
      rw [e]; exact continuousOn_id
    · have e : K.lineWeight = fun _ => 1 := by funext r; simp [CellBox.lineWeight, h0]
      rw [e]; exact continuousOn_const
  have hexp : ∀ r : ℝ, Pl r = ∑ l : Fin (L.degSide + 1),
      (∫ u in Icc K.r₁ K.r₂, ((K.lineWeight u * L.bases.radialPoly l u : ℝ) : ℂ) * rowModeVec c a n (u, v) 2) *
        ((L.bases.radialPoly l r : ℝ) : ℂ) := by
    intro r
    have h := poly_expand (m := L.degSide + 1) (coef := L.bases.radialCoef) (fun l => (hB.radial_leading l).ne')
      (p := L.bases.radialPoly) (fun l u => rfl) hwc (fun l l' _ _ => hB.radial_orthonormal l l') cfl r
    rw [hPl r, h]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    congr 1
    refine setIntegral_congr_fun measurableSet_Icc (fun u hu => ?_)
    try simp only
    rw [hrow u hu, ← hPl u]
  have hGexp : ∀ p ∈ K.rect, G (p.1, v) = ∑ l : Fin (L.degSide + 1), (starRingEnd ℂ)
      (∫ u in Icc K.r₁ K.r₂, ((K.lineWeight u * L.bases.radialPoly l u : ℝ) : ℂ) * rowModeVec c a n (u, v) 2) *
        ((L.bases.radialPoly l p.1 : ℝ) : ℂ) := by
    intro p hp
    rw [hGdef]
    try simp only
    rw [hrow p.1 hp.1, hexp p.1, map_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [map_mul, Complex.conj_ofReal]
  have hbox : K.rect ⊆ Icc (-(|K.r₁| + |K.r₂|)) (|K.r₁| + |K.r₂|) ×ˢ Icc (-(|K.z₁| + |K.z₂|)) (|K.z₁| + |K.z₂|) :=
    prod_mono (lp_box_sub _ _) (lp_box_sub _ _)
  have hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.gradModeOf n x 2 2 p) K.rect := (hW.1 _ _).1.mono_set hbox
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x 2 2 2 p) K.rect := (hW.1 _ _).2.mono_set hbox
  have hpoly : ∀ l, Continuous (L.bases.radialPoly l) := fun l => by
    unfold CellBases.radialPoly; fun_prop
  have hint : ∀ l : Fin (L.degSide + 1), IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 2 2 p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 2 2 2 p) *
      ((p.1 : ℂ) * ((L.bases.radialPoly l p.1 : ℝ) : ℂ))) K.rect := by
    intro l
    have h1 : IntegrableOn (fun p : ℝ × ℝ => (((((1 / (v - o) : ℝ)) : ℂ) * ((p.1 : ℂ) * L.gradModeOf n x 2 2 p)) +
        (((p.2 - o) / (v - o) : ℝ) : ℂ) * ((p.1 : ℂ) * L.secondModeOf n x 2 2 2 p)) *
          ((L.bases.radialPoly l p.1 : ℝ) : ℂ)) K.rect :=
      IntegrableOn.mul_continuousOn ((hF.const_mul _).add (IntegrableOn.continuousOn_mul
        (show Continuous fun p : ℝ × ℝ => ((((p.2 - o) / (v - o) : ℝ)) : ℂ) by fun_prop).continuousOn hdF hcomp))
        (Complex.continuous_ofReal.comp ((hpoly l).comp continuous_fst)).continuousOn hcomp
    exact h1.congr_fun (fun p _ => by ring) hmeas
  have hI : ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 2 2 p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 2 2 2 p) * ((p.1 : ℂ) * G (p.1, v)) =
      ∑ l : Fin (L.degSide + 1), (starRingEnd ℂ)
        (∫ u in Icc K.r₁ K.r₂, ((K.lineWeight u * L.bases.radialPoly l u : ℝ) : ℂ) * rowModeVec c a n (u, v) 2) *
        ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 2 2 p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 2 2 2 p) * ((p.1 : ℂ) * ((L.bases.radialPoly l p.1 : ℝ) : ℂ)) := by
    rw [setIntegral_congr_fun hmeas (g := fun p => ∑ l : Fin (L.degSide + 1), (starRingEnd ℂ)
        (∫ u in Icc K.r₁ K.r₂, ((K.lineWeight u * L.bases.radialPoly l u : ℝ) : ℂ) * rowModeVec c a n (u, v) 2) *
        (((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 2 2 p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 2 2 2 p) * ((p.1 : ℂ) * ((L.bases.radialPoly l p.1 : ℝ) : ℂ)))) (fun p hp => ?_)]
    · rw [integral_finsetSum _ (fun l _ => (hint l).const_mul _)]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      rw [integral_const_mul]
    · try simp only
      rw [hGexp p hp, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      ring
  have hstrip : ∀ l : Fin (L.degSide + 1),
      heightStripMoment v o K.r₁ K.r₂ (fun r => r) (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 2)
        (L.bases.radialPoly l) =
        edgeSign v o * ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * L.gradModeOf n x 2 2 p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * L.secondModeOf n x 2 2 2 p) * ((p.1 : ℂ) * ((L.bases.radialPoly l p.1 : ℝ) : ℂ)) := by
    intro l
    unfold heightStripMoment
    rw [hvo.2.1, hvo.2.2, ← hrect]
    congr 1
    refine setIntegral_congr_fun hmeas (fun p _ => ?_)
    push_cast
    ring
  rw [hI, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [hstrip l]
  exact edge_alg' _ _ _ _ (lp_edge_sq v o)


theorem mode_normal {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1))
    (hface : ∀ a ∈ R.rowSet, ∀ (n : ℤ) (e : Fin 4), ¬ (e.val = 0 ∧ K.r₁ = 0) → ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * (t : ℂ) ^ (d : ℕ)) ∧
      ∀ p ∈ K.rect, (e.val < 2 → p.1 = faceLevel L e → rowModeVec c a n p 0 = Pl p.2) ∧
        (2 ≤ e.val → p.2 = faceLevel L e → rowModeVec c a n p 2 = Pl p.1))
    (n : ℤ) :
    ∑ s : Fin L.segCount, (if (L.segment s).radial then
        ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
          (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d
      else ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d) =
    ∑ e : Fin 4, ∑ l : Fin (L.degSide + 1), (if e.val = 0 ∧ L.box.r₁ = 0 then 0 else
      -(c.splitVisc : ℂ) * edgeSign (faceLevel L e) (faceOther L e) * (if e.val < 2 then (faceLevel L e : ℂ) else 1) *
        (starRingEnd ℂ) (faceRowCoef c L a n e l) * L.strainFaceValue n x e (sideNormal e) (sideNormal e) l) := by
  have hK := hD.box
  have hr := hK.r_order
  have hz := hK.z_order
  have hbox : L.box = K := hL.layout.box_eq
  have hr12 : K.r₁ ≠ K.r₂ := hr.2.ne
  have hz12 : K.z₁ ≠ K.z₂ := hz.2.ne
  have hsplit : ∑ s : Fin L.segCount, (if (L.segment s).radial then
        ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
          (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d
      else ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d) =
      (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = K.r₁), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
          (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d) +
      (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = K.r₂), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
          (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d) +
      (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = K.z₁), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d) +
      (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = K.z₂), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d) := by
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rcases hL.layout.segment_on_side s with ⟨hrad, hlev, _, _, _⟩ | ⟨hnr, hlev, _, _⟩
    · have hrad' : (L.segment s).radial = true := hrad
      rcases hlev with h | h
      · simp [hrad', h, hr12]
      · simp [hrad', h, hr12.symm]
    · have hnr' : (L.segment s).radial = false := by simpa using hnr
      rcases hlev with h | h
      · simp [hnr', h, hz12]
      · simp [hnr', h, hz12.symm]
  have h0' : (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = K.r₁), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
          (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d) = ∑ l : Fin (L.degSide + 1), (if (0 : Fin 4).val = 0 ∧ L.box.r₁ = 0 then 0 else
      -(c.splitVisc : ℂ) * edgeSign (faceLevel L 0) (faceOther L 0) * (if (0 : Fin 4).val < 2 then (faceLevel L 0 : ℂ) else 1) *
        (starRingEnd ℂ) (faceRowCoef c L a n 0 l) * L.strainFaceValue n x 0 (sideNormal 0) (sideNormal 0) l) := by
    by_cases h0 : K.r₁ = 0
    · rw [Finset.sum_eq_zero]
      · symm
        simp [hbox, h0]
      · intro s hs
        obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
        rcases hL.layout.segment_on_side s with ⟨_, _, _, _, hne⟩ | ⟨hnr, _⟩
        · exact absurd (hlev.trans h0) hne
        · exact absurd hrad hnr
    · obtain ⟨Pl, ⟨cfl, hcfl⟩, hPt⟩ := hface a ha n 0 (by simp [h0])
      rw [radial_face hα1 hα2 hc hD hR hL hx ha hseg n (v := K.r₁) (o := K.r₂) (Or.inr ⟨rfl, h0⟩) (by ring) Pl cfl hcfl
        (fun z hz' => (hPt (K.r₁, z) ⟨⟨le_rfl, hr.2.le⟩, hz'⟩).1 (by decide) (by simp [faceLevel, hbox]))]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun l _ => ?_)
      simp [faceLevel, faceOther, sideNormal, faceRowCoef, CellLayout.strainFaceValue, radialFaceMoment,
        CellLayout.sideRadialIndex, hbox, h0]
      ring
  have h1' : (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = K.r₂), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 0 d *
          (L.segment s).moment true (L.gradModeOf n x 0 0) (L.secondModeOf n x 0 0 0) (L.secondModeOf n x 0 0 2) d) = ∑ l : Fin (L.degSide + 1), (if (1 : Fin 4).val = 0 ∧ L.box.r₁ = 0 then 0 else
      -(c.splitVisc : ℂ) * edgeSign (faceLevel L 1) (faceOther L 1) * (if (1 : Fin 4).val < 2 then (faceLevel L 1 : ℂ) else 1) *
        (starRingEnd ℂ) (faceRowCoef c L a n 1 l) * L.strainFaceValue n x 1 (sideNormal 1) (sideNormal 1) l) := by
    obtain ⟨Pl, ⟨cfl, hcfl⟩, hPt⟩ := hface a ha n 1 (by simp)
    rw [radial_face hα1 hα2 hc hD hR hL hx ha hseg n (v := K.r₂) (o := K.r₁) (Or.inl rfl) (by ring) Pl cfl hcfl
      (fun z hz' => (hPt (K.r₂, z) ⟨⟨hr.2.le, le_rfl⟩, hz'⟩).1 (by decide) (by simp [faceLevel, hbox]))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [faceLevel, faceOther, sideNormal, faceRowCoef, CellLayout.strainFaceValue, radialFaceMoment,
        CellLayout.sideRadialIndex, hbox]
    ring
  have h2' : (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = K.z₁), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d) = ∑ l : Fin (L.degSide + 1), (if (2 : Fin 4).val = 0 ∧ L.box.r₁ = 0 then 0 else
      -(c.splitVisc : ℂ) * edgeSign (faceLevel L 2) (faceOther L 2) * (if (2 : Fin 4).val < 2 then (faceLevel L 2 : ℂ) else 1) *
        (starRingEnd ℂ) (faceRowCoef c L a n 2 l) * L.strainFaceValue n x 2 (sideNormal 2) (sideNormal 2) l) := by
    obtain ⟨Pl, ⟨cfl, hcfl⟩, hPt⟩ := hface a ha n 2 (by simp)
    rw [height_face hα1 hα2 hc hD hR hL hx ha hseg n (v := K.z₁) (o := K.z₂) (Or.inl rfl) (by ring) Pl cfl hcfl
      (fun r hr' => (hPt (r, K.z₁) ⟨hr', ⟨le_rfl, hz.2.le⟩⟩).2 (by decide) (by simp [faceLevel, hbox]))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [faceLevel, faceOther, sideNormal, faceRowCoef, CellLayout.strainFaceValue, heightFaceMoment,
        CellLayout.sideHeightIndex, hbox]
    ring
  have h3' : (∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = K.z₂), ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s 2 d *
          (L.segment s).moment true (L.gradModeOf n x 2 2) (L.secondModeOf n x 2 2 0) (L.secondModeOf n x 2 2 2) d) = ∑ l : Fin (L.degSide + 1), (if (3 : Fin 4).val = 0 ∧ L.box.r₁ = 0 then 0 else
      -(c.splitVisc : ℂ) * edgeSign (faceLevel L 3) (faceOther L 3) * (if (3 : Fin 4).val < 2 then (faceLevel L 3 : ℂ) else 1) *
        (starRingEnd ℂ) (faceRowCoef c L a n 3 l) * L.strainFaceValue n x 3 (sideNormal 3) (sideNormal 3) l) := by
    obtain ⟨Pl, ⟨cfl, hcfl⟩, hPt⟩ := hface a ha n 3 (by simp)
    rw [height_face hα1 hα2 hc hD hR hL hx ha hseg n (v := K.z₂) (o := K.z₁) (Or.inr rfl) (by ring) Pl cfl hcfl
      (fun r hr' => (hPt (r, K.z₂) ⟨hr', ⟨hz.2.le, le_rfl⟩⟩).2 (by decide) (by simp [faceLevel, hbox]))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    simp [faceLevel, faceOther, sideNormal, faceRowCoef, CellLayout.strainFaceValue, heightFaceMoment,
        CellLayout.sideHeightIndex, hbox]
    ring
  rw [hsplit, Fin.sum_univ_four, h0', h1', h2', h3']

theorem normal_face_sum {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1))
    (hface : ∀ a ∈ R.rowSet, ∀ (n : ℤ) (e : Fin 4), ¬ (e.val = 0 ∧ K.r₁ = 0) → ∃ Pl : ℝ → ℂ,
      (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, Pl t = ∑ d, cf d * (t : ℂ) ^ (d : ℕ)) ∧
      ∀ p ∈ K.rect, (e.val < 2 → p.1 = faceLevel L e → rowModeVec c a n p 0 = Pl p.2) ∧
        (2 ≤ e.val → p.2 = faceLevel L e → rowModeVec c a n p 2 = Pl p.1))
    (hSF : StrainFaceStatement) :
    gradSideNormalSum c L a x = ∑ d : L.Datum, normalFaceRowData c L a d * L.trueData x d := by
  have hbox : L.box = K := hL.layout.box_eq
  have hRHS : ∑ d : L.Datum, normalFaceRowData c L a d * L.trueData x d = ∑ n : L.modes, ∑ e : Fin 4,
      ∑ l : Fin (L.degSide + 1), (if e.val = 0 ∧ L.box.r₁ = 0 then 0 else
        -(c.splitVisc : ℂ) * edgeSign (faceLevel L e) (faceOther L e) * (if e.val < 2 then (faceLevel L e : ℂ) else 1) *
          (starRingEnd ℂ) (faceRowCoef c L a n e l) * L.strainFaceValue n x e (sideNormal e) (sideNormal e) l) := by
    unfold normalFaceRowData
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun e _ => ?_)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    by_cases h : e.val = 0 ∧ L.box.r₁ = 0
    · simp only [if_pos h, zero_mul, Finset.sum_const_zero]
    · simp only [if_neg h]
      have hl : (l : ℕ) ≤ L.degSide := Nat.lt_succ_iff.mp l.isLt
      rw [hSF c K S B L hL.layout x hx n e (sideNormal e) (sideNormal e) l hl
        (fun h0 h1 => h ⟨h0, by rw [hbox]; exact h1⟩), Finset.mul_sum]
      refine Finset.sum_congr rfl (fun d _ => ?_)
      ring
  rw [hRHS]
  unfold gradSideNormalSum
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun n _ => ?_)
  rw [← mode_normal hα1 hα2 hc hD hR hL hx ha hseg hface n]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [Fin.sum_univ_three]
  by_cases hrad : (L.segment s).radial = true
  · simp [segmentNormal, hrad]
  · have hrad' : (L.segment s).radial = false := by simpa using hrad
    simp [segmentNormal, hrad']

end Breakdown.FracInternal.LayoutRowNormalFace
