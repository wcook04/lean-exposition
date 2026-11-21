import Breakdown.FracCell.LayoutRowValueParts
import Breakdown.FracCell.AngularFrame
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.LayoutRowValuePressure
import Breakdown.FracCell.LayoutRowPressureBoundaryParts
import Breakdown.FracCell.SegmentModesGradient
import Breakdown.FracCell.SegmentModesHeight

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown.FracInternal.LayoutRowViscousSides

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly LayoutRowPressureSideCore LayoutRowPressureBoundaryParts

private theorem lp_cyl_sub (r r' θ z z' : ℝ) : cylPoint r θ z - cylPoint r' θ z' = cylPoint (r - r') θ (z - z') := by
  ext i
  fin_cases i <;> simp [cylPoint] <;> ring

private theorem lp_cyl_radius (r θ z : ℝ) (hr : 0 ≤ r) : CellAnalysis.cylRadius (cylPoint r θ z) = r := by
  unfold CellAnalysis.cylRadius
  simp [cylPoint]
  rw [show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by nlinarith [Real.sin_sq_add_cos_sq θ]]
  exact Real.sqrt_sq hr

private theorem lp_cyl_height (r θ z : ℝ) : cylHeight (cylPoint r θ z) = z := by
  simp [cylHeight, cylPoint]

private theorem lp_cyl_mem {K : CellBox} (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid ∩ {y | 0 ≤ cylHeight y} := by
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hp
  have hr0 : 0 ≤ p.1 := le_trans hK.r_order.1 h1
  have hz0 : 0 ≤ p.2 := le_trans hK.z_order.1 h3
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [lp_cyl_radius _ _ _ hr0]; exact h1
  · rw [lp_cyl_radius _ _ _ hr0]; exact h2
  · rw [lp_cyl_height, abs_of_nonneg hz0]; exact h3
  · rw [lp_cyl_height, abs_of_nonneg hz0]; exact h4
  · show 0 ≤ cylHeight (cylPoint p.1 θ p.2)
    rw [lp_cyl_height]; exact hz0

private theorem lp_cyl_dist (r r' θ z z' : ℝ) :
    ‖cylPoint r θ z - cylPoint r' θ z'‖ ≤ 2 * dist (r, z) (r', z') := by
  rw [lp_cyl_sub, ModeVelSquareInternal.cylPoint_norm, Prod.dist_eq, Real.dist_eq, Real.dist_eq]
  have ha := le_max_left |r - r'| |z - z'|
  have hb := le_max_right |r - r'| |z - z'|
  rw [Real.sqrt_le_left (by positivity)]
  nlinarith [sq_abs (r - r'), sq_abs (z - z'), abs_nonneg (r - r'), abs_nonneg (z - z')]

private theorem lp_cyl_cont (r z : ℝ) : Continuous fun θ : ℝ => cylPoint r θ z := by
  unfold cylPoint
  exact (((ModeVelSquareInternal.single_cont 0).comp (continuous_const.mul Real.continuous_cos)).add
    ((ModeVelSquareInternal.single_cont 1).comp (continuous_const.mul Real.continuous_sin))).add continuous_const

private theorem lp_integrand_cont {v : Space → Space} {s : Set Space} (hv : ContinuousOn v s) {r z : ℝ}
    (hs : ∀ θ, cylPoint r θ z ∈ s) (w : ℝ) (i : Fin 3) :
    Continuous (fun θ : ℝ => Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) i : ℂ)) := by
  have hc1 : Continuous (fun θ : ℝ => v (cylPoint r θ z)) := hv.comp_continuous (lp_cyl_cont r z) hs
  have hc2 : Continuous (fun θ : ℝ => frameVec θ (v (cylPoint r θ z)) i) := by
    simp_rw [ModeVelSquareInternal.frameVec_eq]
    exact hc1.inner (ModeVelSquareInternal.frameUnit_cont i)
  have hc3 : Continuous (fun θ : ℝ => Complex.exp (-(w * θ : ℝ) * Complex.I)) := by fun_prop
  exact hc3.mul (Complex.continuous_ofReal.comp hc2)

private theorem lp_integrand_diff {v : Space → Space} {s : Set Space} {L₀ : NNReal} (hv : LipschitzOnWith L₀ v s)
    {r z r' z' : ℝ} (hs : ∀ θ, cylPoint r θ z ∈ s) (hs' : ∀ θ, cylPoint r' θ z' ∈ s) (w : ℝ) (i : Fin 3) (θ : ℝ) :
    ‖Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r θ z)) i : ℂ) -
      Complex.exp (-(w * θ : ℝ) * Complex.I) * (frameVec θ (v (cylPoint r' θ z')) i : ℂ)‖ ≤
        (2 * L₀ : ℝ) * dist (r, z) (r', z') := by
  rw [← mul_sub, norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  have hlin : frameVec θ (v (cylPoint r θ z)) i - frameVec θ (v (cylPoint r' θ z')) i =
      frameVec θ (v (cylPoint r θ z) - v (cylPoint r' θ z')) i := by
    simp only [ModeVelSquareInternal.frameVec_eq, inner_sub_left]
  rw [hlin]
  refine (ModeVelSquareInternal.frameVec_abs _ _ _).trans ?_
  rw [← dist_eq_norm]
  refine (hv.dist_le_mul _ (hs θ) _ (hs' θ)).trans ?_
  rw [dist_eq_norm]
  have := lp_cyl_dist r r' θ z z'
  have hL : (0 : ℝ) ≤ L₀ := L₀.2
  calc (L₀ : ℝ) * ‖cylPoint r θ z - cylPoint r' θ z'‖ ≤ L₀ * (2 * dist (r, z) (r', z')) :=
        mul_le_mul_of_nonneg_left this hL
    _ = (2 * L₀ : ℝ) * dist (r, z) (r', z') := by ring

private theorem lp_mode_slope {v : Space → Space} {s : Set Space} {L₀ : NNReal} (hv : LipschitzOnWith L₀ v s)
    {T : Set (ℝ × ℝ)} (hT : ∀ p ∈ T, ∀ θ, cylPoint p.1 θ p.2 ∈ s) (m : ℕ) (n : ℤ) (i : Fin 3) :
    LipschitzOnWith (2 * L₀) (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 i) T := by
  refine LipschitzOnWith.of_dist_le_mul (fun p hp q hq => ?_)
  rw [dist_eq_norm]
  unfold modeVec
  rw [← mul_sub, ← intervalIntegral.integral_sub
    ((lp_integrand_cont hv.continuousOn (hT p hp) (azimuth m n) i).intervalIntegrable _ _)
    ((lp_integrand_cont hv.continuousOn (hT q hq) (azimuth m n) i).intervalIntegrable _ _), norm_mul]
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi)
    (fun θ _ => lp_integrand_diff hv (hT p hp) (hT q hq) (azimuth m n) i θ)
  have hpi : 0 < Real.pi := Real.pi_pos
  have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [sub_zero, abs_of_pos (by positivity)] at hI
  rw [h2]
  have hd : dist (p.1, p.2) (q.1, q.2) = dist p q := rfl
  rw [hd] at hI
  calc 1 / (2 * Real.pi) * ‖_‖ ≤ 1 / (2 * Real.pi) * ((2 * L₀ : ℝ) * dist p q * (2 * Real.pi)) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = ((2 * L₀ : NNReal) : ℝ) * dist p q := by push_cast; field_simp

theorem lp_row_slope {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {a : Fin N}
    (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3) :
    ∃ C : NNReal, LipschitzOnWith C (fun p => rowModeVec c a n p i) K.rect := by
  obtain ⟨L₀, hL₀⟩ := hR.row_slope a ha
  exact ⟨2 * L₀, lp_mode_slope hL₀ (fun p hp θ => lp_cyl_mem hD.box hp θ) c.order n i⟩

theorem lp_coord_slope {u : ℝ × ℝ → ℂ} {C : NNReal} {T : Set (ℝ × ℝ)} (hu : LipschitzOnWith C u T)
    {Rb M : ℝ} (hRb : ∀ p ∈ T, |p.1| ≤ Rb) (hM : ∀ p ∈ T, ‖u p‖ ≤ M) (hRb0 : 0 ≤ Rb) (hM0 : 0 ≤ M) :
    LipschitzOnWith (Real.toNNReal (Rb * C + M)) (fun p : ℝ × ℝ => (p.1 : ℂ) * (starRingEnd ℂ) (u p)) T := by
  refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
  rw [Real.coe_toNNReal _ (by positivity), dist_eq_norm]
  have e : (p.1 : ℂ) * (starRingEnd ℂ) (u p) - (q.1 : ℂ) * (starRingEnd ℂ) (u q) =
      (p.1 : ℂ) * (starRingEnd ℂ) (u p - u q) + ((p.1 - q.1 : ℝ) : ℂ) * (starRingEnd ℂ) (u q) := by
    rw [map_sub]; push_cast; ring
  rw [e]
  have h1 : ‖u p - u q‖ ≤ C * dist p q := by rw [← dist_eq_norm]; exact hu.dist_le_mul p hp q hq
  have h2 : |p.1 - q.1| ≤ dist p q := by
    rw [Prod.dist_eq, ← Real.dist_eq]; exact le_max_left _ _
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_conj, Complex.norm_conj,
    Real.norm_eq_abs, Real.norm_eq_abs]
  have hd : 0 ≤ dist p q := dist_nonneg
  calc |p.1| * ‖u p - u q‖ + |p.1 - q.1| * ‖u q‖ ≤ Rb * (C * dist p q) + dist p q * M :=
        add_le_add (mul_le_mul (hRb p hp) h1 (norm_nonneg _) hRb0) (mul_le_mul h2 (hM q hq) (norm_nonneg _) hd)
    _ = (Rb * C + M) * dist p q := by ring

theorem lp_test_cont (F : FaceSegment) (d : ℕ) : Continuous (F.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

theorem lp_edge_sq (c o : ℝ) : edgeSign c o * edgeSign c o = 1 := by
  unfold edgeSign; split_ifs <;> norm_num

theorem lp_box_sub (a b : ℝ) : Icc a b ⊆ Icc (-(|a| + |b|)) (|a| + |b|) := by
  intro s hs
  constructor
  · linarith [neg_abs_le a, abs_nonneg b, hs.1]
  · linarith [le_abs_self b, abs_nonneg a, hs.2]

private theorem seg_side_of {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsCellLayout c K S B L) (e : Fin 4) (s : Fin L.segCount)
    (hrad : ((L.segment s).radial ↔ e.val < 2))
    (hlev : (L.segment s).level = (if e.val = 0 then K.r₁ else if e.val = 1 then K.r₂ else if e.val = 2 then K.z₁ else K.z₂)) :
    s ∈ L.sideSegments e := by
  have hr := hK.r_order
  have hz := hK.z_order
  obtain ⟨e', he'⟩ := hL.segments_on_sides s
  obtain ⟨h1, h2⟩ := hL.sideSegments_spec e' s he'
  have hee : e' = e := by
    fin_cases e <;> fin_cases e' <;> simp_all
  rw [← hee]; exact he'

private theorem seg_cover_gen {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsCellLayout c K S B L) (e : Fin 4) (hnz : e.val = 0 → K.r₁ ≠ 0)
    (b : Bool) (hb : (b = true ↔ e.val < 2)) {v lo hi : ℝ}
    (hv : v = (if e.val = 0 then K.r₁ else if e.val = 1 then K.r₂ else if e.val = 2 then K.z₁ else K.z₂))
    (hlohi : (if e.val < 2 then K.z₁ else K.r₁) = lo ∧ (if e.val < 2 then K.z₂ else K.r₂) = hi)
    (hin0 : ∀ s, (L.segment s).radial = b → lo ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ hi) :
    (∀ u ∈ Icc lo hi, ∃ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = b ∧ (L.segment s).level = v),
        (L.segment s).lo ≤ u ∧ u ≤ (L.segment s).hi) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = b ∧ (L.segment s).level = v),
        lo ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ hi) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = b ∧ (L.segment s).level = v),
      ∀ s' ∈ Finset.univ.filter (fun s => (L.segment s).radial = b ∧ (L.segment s).level = v), s ≠ s' →
        (L.segment s).hi ≤ (L.segment s').lo ∨ (L.segment s').hi ≤ (L.segment s).lo) := by
  have hmem : ∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = b ∧ (L.segment s).level = v),
      s ∈ L.sideSegments e := by
    intro s hs
    obtain ⟨_, hr, hl⟩ := Finset.mem_filter.1 hs
    refine seg_side_of hK hL e s ?_ (hl.trans hv)
    rw [hr]; exact hb
  refine ⟨fun u hu => ?_, fun s hs => hin0 s (Finset.mem_filter.1 hs).2.1, fun s hs s' hs' hne =>
    hL.sideSegments_disjoint e s (hmem s hs) s' (hmem s' hs') hne⟩
  have hu' : (if e.val < 2 then K.z₁ ≤ u ∧ u ≤ K.z₂ else K.r₁ ≤ u ∧ u ≤ K.r₂) := by
    obtain ⟨h1, h2⟩ := hlohi
    split_ifs at h1 h2 ⊢ <;> subst h1 h2 <;> exact hu
  obtain ⟨s, hs, h3, h4⟩ := hL.sideSegments_cover e hnz u hu'
  obtain ⟨hsr, hsl⟩ := hL.sideSegments_spec e s hs
  refine ⟨s, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_, hsl.trans hv.symm⟩, h3, h4⟩
  cases hbb : b
  · cases hx : (L.segment s).radial
    · rfl
    · exact absurd (hb.2 (hsr.1 hx)) (by simp [hbb])
  · exact hb.1 hbb |> hsr.2

private theorem seg_radial_cover {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsCellLayout c K S B L) {v : ℝ} (hv : v = K.r₂ ∨ (v = K.r₁ ∧ K.r₁ ≠ 0)) :
    (∀ u ∈ Icc K.z₁ K.z₂, ∃ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
        (L.segment s).lo ≤ u ∧ u ≤ (L.segment s).hi) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
        K.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.z₂) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
      ∀ s' ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v), s ≠ s' →
        (L.segment s).hi ≤ (L.segment s').lo ∨ (L.segment s').hi ≤ (L.segment s).lo) := by
  have hin0 : ∀ s, (L.segment s).radial = true → K.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.z₂ := by
    intro s hs
    rcases hL.segment_on_side s with ⟨_, _, h1, h2, _⟩ | ⟨h, _⟩
    · exact ⟨h1, h2⟩
    · exact absurd hs h
  rcases hv with h | ⟨h, h0⟩
  · exact seg_cover_gen hK hL 1 (fun h => absurd h (by decide)) true (by simp) (by simp [h]) (by simp) hin0
  · exact seg_cover_gen hK hL 0 (fun _ => h0) true (by simp) (by simp [h]) (by simp) hin0

private theorem seg_height_cover {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsCellLayout c K S B L) {v : ℝ} (hv : v = K.z₁ ∨ v = K.z₂) :
    (∀ u ∈ Icc K.r₁ K.r₂, ∃ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
        (L.segment s).lo ≤ u ∧ u ≤ (L.segment s).hi) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
        K.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.r₂) ∧
    (∀ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
      ∀ s' ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v), s ≠ s' →
        (L.segment s).hi ≤ (L.segment s').lo ∨ (L.segment s').hi ≤ (L.segment s).lo) := by
  have hin0 : ∀ s, (L.segment s).radial = false → K.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.r₂ := by
    intro s hs
    rcases hL.segment_on_side s with ⟨h, _⟩ | ⟨_, _, h1, h2⟩
    · rw [hs] at h; exact absurd h (by decide)
    · exact ⟨h1, h2⟩
  rcases hv with h | h
  · exact seg_cover_gen hK hL 2 (fun h => absurd h (by decide)) false (by simp) (by simp [h]) (by simp) hin0
  · exact seg_cover_gen hK hL 3 (fun h => absurd h (by decide)) false (by simp) (by simp [h]) (by simp) hin0

theorem radial_side_sum {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsPressureLayout c K S B L) {F dF dFz : ℝ × ℝ → ℂ}
    (hW : IsRadialWeakPair F dF) {G : ℝ × ℝ → ℂ} (hGc : ContinuousOn G K.rect)
    (cf : Fin L.segCount → Fin (L.degSide + 1) → ℂ) {v o : ℝ} (hv : v = K.r₂ ∨ (v = K.r₁ ∧ K.r₁ ≠ 0))
    (ho : o = K.r₁ + K.r₂ - v)
    (hGv : ∀ s, (L.segment s).radial = true → (L.segment s).level = v → ∀ z ∈ Icc K.z₁ K.z₂,
      G (v, z) = (v : ℂ) * ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) * ((L.segment s).test d z : ℂ)) :
    ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) * G (v, p.2) =
      ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = v),
        ∑ d : Fin (L.degSide + 1), edgeSign (L.segment s).level (L.segment s).other *
          ((L.segment s).level : ℂ) * (starRingEnd ℂ) (cf s d) * (L.segment s).moment true F dF dFz d := by
  have hr := hK.r_order
  have hvo : v ≠ o ∧ min v o = K.r₁ ∧ max v o = K.r₂ := by
    rw [ho]
    rcases hv with h | ⟨h, _⟩ <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> simp [min_def, max_def] <;> intros <;> linarith
  have hvmem : v ∈ Icc K.r₁ K.r₂ := by
    rcases hv with h | ⟨h, _⟩ <;> rw [h] <;> constructor <;> linarith
  set Z := |K.z₁| + |K.z₂| with hZ
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hF : IntegrableOn F K.rect :=
    (hW.1 K.r₂ Z).1.mono_set (prod_mono (Icc_subset_Icc_left hr.1) (lp_box_sub _ _))
  have hdFt : IntegrableOn (fun p : ℝ × ℝ => (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) K.rect := by
    rcases hr.1.lt_or_eq with h0 | h0
    · have hd : IntegrableOn dF K.rect := (hW.2.1 K.r₁ K.r₂ Z h0).mono_set (prod_mono subset_rfl (lp_box_sub _ _))
      exact IntegrableOn.continuousOn_mul (by fun_prop) hd hcomp
    · have ho0 : o = 0 := by
        rcases hv with h | ⟨_, h⟩
        · rw [ho, h, ← h0]; ring
        · exact absurd h0.symm h
      have hrd : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) K.rect :=
        (hW.1 K.r₂ Z).2.mono_set (prod_mono (Icc_subset_Icc_left hr.1) (lp_box_sub _ _))
      refine IntegrableOn.congr_fun (hrd.const_mul (((1 / (v - o) : ℝ)) : ℂ)) (fun p _ => ?_) hmeas
      simp only [ho0, sub_zero]; push_cast; ring
  have hWint : IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p))
      K.rect := (hF.const_mul _).add hdFt
  have hGvc : ContinuousOn (fun p : ℝ × ℝ => G (v, p.2)) K.rect :=
    hGc.comp (continuous_const.prodMk continuous_snd).continuousOn (fun p hp => ⟨hvmem, hp.2⟩)
  have hfull := hWint.mul_continuousOn hGvc hcomp
  obtain ⟨hcov, hin, hdis⟩ := seg_radial_cover hK hL.layout hv
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect] at hfull hWint ⊢
  rw [strip_partition _ (fun s => (L.segment s).lo) (fun s => (L.segment s).hi) hcov hin hdis
    measurableSet_Icc hfull]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
  have hoth : (L.segment s).other = o := by
    rw [(hL.layout.segment_other_in_box s).1 hrad, hlev, ho]
  have hsub : Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi ⊆ Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ :=
    prod_mono subset_rfl (Icc_subset_Icc (hin s hs).1 (hin s hs).2)
  have hsm : MeasurableSet (Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hint_d : ∀ d : Fin (L.degSide + 1), IntegrableOn (fun p : ℝ × ℝ =>
      ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        (((L.segment s).test d p.2 : ℝ) : ℂ)) (Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi) :=
    fun d => (hWint.mono_set hsub).mul_continuousOn
      (Complex.continuous_ofReal.comp ((lp_test_cont _ d).comp continuous_snd)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)
  have hmom : ∀ d : Fin (L.degSide + 1), (L.segment s).moment true F dF dFz d = edgeSign v o *
      ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          (((L.segment s).test d p.2 : ℝ) : ℂ) := by
    intro d
    simp only [FaceSegment.moment, hrad, ↓reduceIte, radialStripMoment, hlev, hoth, hvo.2.1, hvo.2.2]
  rw [setIntegral_congr_fun hsm (g := fun p => ∑ d : Fin (L.degSide + 1), ((v : ℂ) * (starRingEnd ℂ) (cf s d)) *
      (((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        (((L.segment s).test d p.2 : ℝ) : ℂ))) (fun p hp => ?_)]
  · rw [integral_finsetSum _ (fun d _ => (hint_d d).const_mul _)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [integral_const_mul, hmom d, hlev, hoth]
    linear_combination (-(v : ℂ) * (starRingEnd ℂ) (cf s d) *
      ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          (((L.segment s).test d p.2 : ℝ) : ℂ)) * lp_edge_sq v o
  · simp only
    rw [hGv s hrad hlev p.2 (Icc_subset_Icc (hin s hs).1 (hin s hs).2 hp.2), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring

theorem height_side_sum {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsPressureLayout c K S B L) {F dF dFr : ℝ × ℝ → ℂ}
    (hW : IsHeightWeakPair (fun r => r) F dF) {G : ℝ × ℝ → ℂ} (hGc : ContinuousOn G K.rect)
    (cf : Fin L.segCount → Fin (L.degSide + 1) → ℂ) {v o : ℝ} (hv : v = K.z₁ ∨ v = K.z₂)
    (ho : o = K.z₁ + K.z₂ - v)
    (hGv : ∀ s, (L.segment s).radial = false → (L.segment s).level = v → ∀ r ∈ Icc K.r₁ K.r₂,
      G (r, v) = ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) * ((L.segment s).test d r : ℂ)) :
    ∫ p in K.rect, ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) * ((p.1 : ℂ) * G (p.1, v)) =
      ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = false ∧ (L.segment s).level = v),
        ∑ d : Fin (L.degSide + 1), edgeSign (L.segment s).level (L.segment s).other *
          (starRingEnd ℂ) (cf s d) * (L.segment s).moment true F dFr dF d := by
  have hr := hK.r_order
  have hz := hK.z_order
  have hvo : v ≠ o ∧ min v o = K.z₁ ∧ max v o = K.z₂ := by
    rw [ho]
    rcases hv with h | h <;> rw [h] <;> refine ⟨?_, ?_, ?_⟩ <;> simp [min_def, max_def] <;> intros <;> linarith
  have hvmem : v ∈ Icc K.z₁ K.z₂ := by
    rcases hv with h | h <;> rw [h] <;> constructor <;> linarith
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hbox : K.rect ⊆ Icc (-(|K.r₁| + |K.r₂|)) (|K.r₁| + |K.r₂|) ×ˢ Icc (-(|K.z₁| + |K.z₂|)) (|K.z₁| + |K.z₂|) :=
    prod_mono (lp_box_sub _ _) (lp_box_sub _ _)
  have hF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * F p) K.rect := (hW.1 _ _).1.mono_set hbox
  have hdF : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * dF p) K.rect := (hW.1 _ _).2.mono_set hbox
  have hWint : ∀ g : ℝ × ℝ → ℂ, ContinuousOn g K.rect → ∀ T ⊆ K.rect, MeasurableSet T → IsCompact T →
      IntegrableOn (fun p : ℝ × ℝ => ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * g p)) T := by
    intro g hg T hT hTm hTc
    have h1 : IntegrableOn (fun p : ℝ × ℝ => (((((1 / (v - o) : ℝ)) : ℂ) * ((p.1 : ℂ) * F p)) +
        (((p.2 - o) / (v - o) : ℝ) : ℂ) * ((p.1 : ℂ) * dF p)) * g p) T :=
      IntegrableOn.mul_continuousOn (((hF.mono_set hT).const_mul _).add (IntegrableOn.continuousOn_mul
        (show Continuous fun p : ℝ × ℝ => ((((p.2 - o) / (v - o) : ℝ)) : ℂ) by fun_prop).continuousOn (hdF.mono_set hT) hTc))
        (hg.mono hT) hTc
    exact h1.congr_fun (fun p _ => by ring) hTm
  have hGvc : ContinuousOn (fun p : ℝ × ℝ => G (p.1, v)) K.rect :=
    hGc.comp (continuous_fst.prodMk continuous_const).continuousOn (fun p hp => ⟨hp.1, hvmem⟩)
  have hfull := hWint _ hGvc K.rect subset_rfl hmeas hcomp
  obtain ⟨hcov, hin, hdis⟩ := seg_height_cover hK hL.layout hv
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  rw [hrect] at hfull ⊢
  rw [strip_partition_fst _ (fun s => (L.segment s).lo) (fun s => (L.segment s).hi) hcov hin hdis
    measurableSet_Icc hfull]
  refine Finset.sum_congr rfl (fun s hs => ?_)
  obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
  have hnr : ¬ (L.segment s).radial := by simp [hrad]
  have hoth : (L.segment s).other = o := by
    rw [(hL.layout.segment_other_in_box s).2 hnr, hlev, ho]
  have hsub : Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂ ⊆ K.rect :=
    prod_mono (Icc_subset_Icc (hin s hs).1 (hin s hs).2) subset_rfl
  have hsm : MeasurableSet (Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂) :=
    measurableSet_Icc.prod measurableSet_Icc
  have hsc : IsCompact (Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂) :=
    isCompact_Icc.prod isCompact_Icc
  have hint_d : ∀ d : Fin (L.degSide + 1), IntegrableOn (fun p : ℝ × ℝ =>
      ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * (((L.segment s).test d p.1 : ℝ) : ℂ))) (Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂) :=
    fun d => hWint _ (Complex.continuous_ofReal.comp ((lp_test_cont _ d).comp continuous_fst)).continuousOn _ hsub hsm hsc
  have hmom : ∀ d : Fin (L.degSide + 1), (L.segment s).moment true F dFr dF d = edgeSign v o *
      ∫ p in Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          ((p.1 : ℂ) * (((L.segment s).test d p.1 : ℝ) : ℂ)) := by
    intro d
    simp only [FaceSegment.moment, hrad, Bool.false_eq_true, ↓reduceIte, heightStripMoment, hlev, hoth, hvo.2.1,
      hvo.2.2, Complex.ofReal_mul]
  rw [setIntegral_congr_fun hsm (g := fun p => ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) *
      (((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
        ((p.1 : ℂ) * (((L.segment s).test d p.1 : ℝ) : ℂ)))) (fun p hp => ?_)]
  · rw [integral_finsetSum _ (fun d _ => (hint_d d).const_mul _)]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [integral_const_mul, hmom d, hlev, hoth]
    linear_combination (-(starRingEnd ℂ) (cf s d) *
      ∫ p in Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂,
        ((((1 / (v - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (v - o) : ℝ) : ℂ) * dF p) *
          ((p.1 : ℂ) * (((L.segment s).test d p.1 : ℝ) : ℂ))) * lp_edge_sq v o
  · simp only
    rw [hGv s hrad hlev p.1 (Icc_subset_Icc (hin s hs).1 (hin s hs).2 hp.1), Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    ring


private theorem deriv_int {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (a b : ℝ) :
    IntervalIntegrable (deriv u) volume a b :=
  (intervalIntegrable_const (c := (C : ℝ))).mono_fun' (measurable_deriv u).aestronglyMeasurable
    (ae_of_all _ fun _ => norm_deriv_le_of_lipschitz hu)

private theorem part_ftc (L : ℂ →L[ℝ] ℝ) {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (A o a b : ℝ) :
    L (∫ r in a..b, (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r)) =
      ((b - o) * A) * L (u b) - ((a - o) * A) * L (u a) := by
  have hcont : Continuous u := hu.continuous
  have hF : IntervalIntegrable (fun r => (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r)) volume a b := by
    refine IntervalIntegrable.add ?_ ?_
    · exact (continuous_const.mul hcont).intervalIntegrable _ _
    · exact (deriv_int hu a b).continuousOn_mul (by fun_prop)
  rw [← L.intervalIntegral_comp_comm hF]
  have hw : LipschitzWith ‖A‖₊ (fun r : ℝ => (r - o) * A) := by
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Real.dist_eq, Real.dist_eq, coe_nnnorm, Real.norm_eq_abs, ← sub_mul, abs_mul, mul_comm]
    ring_nf
    rfl
  have hLu : LipschitzWith (‖L‖₊ * C) (fun r => L (u r)) := L.lipschitz.comp hu
  have key := AbsolutelyContinuousOnInterval.integral_deriv_mul_eq_sub
    (hw.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
    (hLu.lipschitzOnWith.absolutelyContinuousOnInterval (a := a) (b := b))
  rw [← key]
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hu.ae_differentiableAt_real] with r hr _
  have h1 : deriv (fun r => L (u r)) r = L (deriv u r) :=
    (L.hasFDerivAt.comp_hasDerivAt r hr.hasDerivAt).deriv
  have h2 : deriv (fun r : ℝ => (r - o) * A) r = A := by
    have : HasDerivAt (fun r : ℝ => (r - o) * A) (1 * A) r :=
      ((hasDerivAt_id' r).sub_const o).mul_const A
    rw [this.deriv]; ring
  rw [h1, h2]
  simp only [map_add]
  rw [show (((A : ℝ) : ℂ) * u r) = A • u r from (Complex.real_smul).symm,
    show ((((r - o) * A : ℝ) : ℂ) * deriv u r) = ((r - o) * A) • deriv u r from (Complex.real_smul).symm,
    map_smul, map_smul, smul_eq_mul, smul_eq_mul]

private theorem slice_ftc {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (A o a b : ℝ) :
    ∫ r in a..b, (((A : ℝ) : ℂ) * u r + (((r - o) * A : ℝ) : ℂ) * deriv u r) =
      ((((b - o) * A : ℝ)) : ℂ) * u b - ((((a - o) * A : ℝ)) : ℂ) * u a := by
  apply Complex.ext
  · have := part_ftc Complex.reCLM hu A o a b
    simp only [Complex.reCLM_apply] at this
    rw [this]; simp
  · have := part_ftc Complex.imCLM hu A o a b
    simp only [Complex.imCLM_apply] at this
    rw [this]; simp

private theorem slice_ftc' {u : ℝ → ℂ} {C : NNReal} (hu : LipschitzWith C u) (c o a b : ℝ) :
    ∫ r in a..b, ((((1 / (c - o) : ℝ)) : ℂ) * u r + (((r - o) / (c - o) : ℝ) : ℂ) * deriv u r) =
      ((((b - o) / (c - o) : ℝ)) : ℂ) * u b - ((((a - o) / (c - o) : ℝ)) : ℂ) * u a := by
  have h : ∀ r : ℝ, (r - o) / (c - o) = (r - o) * (1 / (c - o)) := fun r => by ring
  simp_rw [h]
  exact slice_ftc hu (1 / (c - o)) o a b

private theorem radial_strip_trace {f : ℝ × ℝ → ℂ} {c o lo hi : ℝ} {C : NNReal} (hco : c ≠ o)
    (hf : LipschitzOnWith C f (Icc (min c o) (max c o) ×ˢ Icc lo hi)) {t : ℝ → ℝ} (ht : Continuous t) :
    radialStripMoment c o lo hi f (CellBox.radialDeriv f) t = ∫ z in Icc lo hi, f (c, z) * (t z : ℂ) := by
  unfold radialStripMoment
  rcases lt_or_ge hi lo with hlh | hlh
  · simp [Icc_eq_empty_of_lt hlh]
  set m := min c o with hm
  set M := max c o with hM
  have hmM : m ≤ M := min_le_max
  let P : ℝ × ℝ → ℝ × ℝ := fun p => ((projIcc m M hmM p.1 : ℝ), (projIcc lo hi hlh p.2 : ℝ))
  have hPmem : ∀ p, P p ∈ Icc m M ×ˢ Icc lo hi := fun p => ⟨(projIcc m M hmM p.1).2, (projIcc lo hi hlh p.2).2⟩
  have hPid : ∀ p ∈ Icc m M ×ˢ Icc lo hi, P p = p := fun p hp =>
    Prod.ext (by simp [P, projIcc_of_mem hmM hp.1]) (by simp [P, projIcc_of_mem hlh hp.2])
  have hPd : ∀ p q, dist (P p) (P q) ≤ dist p q := by
    intro p q
    rw [Prod.dist_eq, Prod.dist_eq]
    have h1 := (LipschitzWith.projIcc hmM).dist_le_mul p.1 q.1
    have h2 := (LipschitzWith.projIcc hlh).dist_le_mul p.2 q.2
    simp only [NNReal.coe_one, one_mul, Subtype.dist_eq] at h1 h2
    exact max_le_max h1 h2
  set g : ℝ × ℝ → ℂ := fun p => f (P p) with hgdef
  have hg : LipschitzWith C g := LipschitzWith.of_dist_le_mul fun p q =>
    (hf.dist_le_mul _ (hPmem p) _ (hPmem q)).trans (mul_le_mul_of_nonneg_left (hPd p q) C.2)
  have hfg : ∀ p ∈ Icc m M ×ˢ Icc lo hi, f p = g p := fun p hp => by simp only [hgdef, hPid p hp]
  have hnull : ∀ x : ℝ, (volume : Measure (ℝ × ℝ)) ({x} ×ˢ univ) = 0 := by
    intro x; rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
  have hS1 : ∫ p in Icc m M ×ˢ Icc lo hi, (((1 / (c - o) : ℝ) : ℂ) * f p +
        (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv f p) * ((t p.2 : ℝ) : ℂ) =
      ∫ p in Icc m M ×ˢ Icc lo hi, (((1 / (c - o) : ℝ) : ℂ) * g p +
        (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv g p) * ((t p.2 : ℝ) : ℂ) := by
    refine setIntegral_congr_ae (measurableSet_Icc.prod measurableSet_Icc) ?_
    have h1 := compl_mem_ae_iff.mpr (hnull m)
    have h2 := compl_mem_ae_iff.mpr (hnull M)
    filter_upwards [h1, h2] with p hp1 hp2 hp
    have hpm : p.1 ≠ m := fun e => hp1 ⟨e, mem_univ _⟩
    have hpM : p.1 ≠ M := fun e => hp2 ⟨e, mem_univ _⟩
    have hio : p.1 ∈ Ioo m M := ⟨lt_of_le_of_ne hp.1.1 (Ne.symm hpm), lt_of_le_of_ne hp.1.2 hpM⟩
    have hd : CellBox.radialDeriv f p = CellBox.radialDeriv g p := by
      unfold CellBox.radialDeriv
      refine Filter.EventuallyEq.deriv_eq ?_
      filter_upwards [Icc_mem_nhds hio.1 hio.2] with r hr
      exact hfg (r, p.2) ⟨hr, hp.2⟩
    rw [hfg p hp, hd]
  rw [hS1]
  have hmeasD : Measurable (fun q : ℝ × ℝ => deriv (fun r => g (r, q.1)) q.2) := by
    refine measurable_deriv_with_param (f := fun z r => g (r, z)) ?_
    change Continuous (fun q : ℝ × ℝ => g (q.2, q.1))
    exact hg.continuous.comp continuous_swap
  obtain ⟨Bg, hBg⟩ := (isCompact_Icc.prod isCompact_Icc).exists_bound_of_continuousOn hf.continuousOn
  obtain ⟨Bt, hBt⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc lo hi) ht.continuousOn
  have hwc : Continuous (fun r : ℝ => (r - o) / (c - o)) := by fun_prop
  obtain ⟨Bw, hBw⟩ := isCompact_Icc.exists_bound_of_continuousOn (s := Icc m M) hwc.continuousOn
  have hgb : ∀ p, ‖g p‖ ≤ Bg := fun p => hBg _ (hPmem p)
  have hdb : ∀ z r, ‖deriv (fun r => g (r, z)) r‖ ≤ C := fun z r => by
    have hl : LipschitzWith (C * 1) (fun r => g (r, z)) := hg.comp (LipschitzWith.prodMk_right z)
    have := norm_deriv_le_of_lipschitz (x₀ := r) hl
    simpa using this
  have hInt : IntegrableOn (fun q : ℝ × ℝ => (((1 / (c - o) : ℝ) : ℂ) * g q.swap +
        (((q.swap.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv g q.swap) * ((t q.swap.2 : ℝ) : ℂ))
      (Icc lo hi ×ˢ Icc m M) (volume.prod volume) := by
    refine Measure.integrableOn_of_bounded (M := (‖(1 / (c - o) : ℝ)‖ * Bg + Bw * C) * Bt) ?_ ?_ ?_
    · rw [Measure.prod_prod]
      exact ENNReal.mul_ne_top measure_Icc_lt_top.ne measure_Icc_lt_top.ne
    · have hm1 : Measurable fun q : ℝ × ℝ => g q.swap := (hg.continuous.comp continuous_swap).measurable
      have hm2 : Measurable fun q : ℝ × ℝ => CellBox.radialDeriv g q.swap := hmeasD
      have hm3 : Measurable fun q : ℝ × ℝ => (((q.swap.1 - o) / (c - o) : ℝ) : ℂ) := by
        exact Complex.measurable_ofReal.comp (hwc.measurable.comp measurable_snd)
      have hm4 : Measurable fun q : ℝ × ℝ => ((t q.swap.2 : ℝ) : ℂ) :=
        Complex.measurable_ofReal.comp (ht.measurable.comp measurable_fst)
      exact (((measurable_const.mul hm1).add (hm3.mul hm2)).mul hm4).aestronglyMeasurable
    · refine ae_restrict_of_forall_mem (measurableSet_Icc.prod measurableSet_Icc) (fun q hq => ?_)
      have hw := hBw q.2 hq.2
      have ht' := hBt q.1 hq.1
      rw [norm_mul]
      refine mul_le_mul ?_ ?_ (norm_nonneg _) ?_
      · refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [norm_mul, Complex.norm_real]
          exact mul_le_mul_of_nonneg_left (hgb _) (norm_nonneg _)
        · rw [norm_mul, Complex.norm_real]
          exact mul_le_mul hw (hdb _ _) (norm_nonneg _) ((norm_nonneg _).trans hw)
      · rw [Complex.norm_real]; exact ht'
      · exact add_nonneg (mul_nonneg (norm_nonneg _) ((norm_nonneg _).trans (hgb 0)))
          (mul_nonneg ((norm_nonneg _).trans (hBw m ⟨le_rfl, hmM⟩)) C.2)
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, setIntegral_prod _ hInt, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc (fun z hz => ?_)
  simp only [Prod.swap_prod_mk]
  rw [integral_mul_const, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hmM]
  have hu : LipschitzWith (C * 1) (fun r => g (r, z)) := hg.comp (LipschitzWith.prodMk_right z)
  have hftc := slice_ftc' hu c o m M
  unfold CellBox.radialDeriv
  simp only
  rw [hftc]
  have hcm : (c, z) ∈ Icc m M ×ˢ Icc lo hi := ⟨⟨min_le_left _ _, le_max_left _ _⟩, hz⟩
  have hne : c - o ≠ 0 := sub_ne_zero.mpr hco
  rcases lt_or_gt_of_ne hco with h | h
  · have e1 : m = c := by rw [hm]; exact min_eq_left h.le
    have e2 : M = o := by rw [hM]; exact max_eq_right h.le
    rw [e1, e2, ← hfg _ hcm]
    simp only [edgeSign, if_neg (not_lt.mpr h.le), sub_self, zero_div, div_self hne]
    push_cast
    ring
  · have e1 : m = o := by rw [hm]; exact min_eq_right h.le
    have e2 : M = c := by rw [hM]; exact max_eq_left h.le
    rw [e1, e2, ← hfg _ hcm]
    simp only [edgeSign, if_pos h, sub_self, zero_div, div_self hne]
    push_cast
    ring

private theorem height_strip_trace {f : ℝ × ℝ → ℂ} {c o lo hi : ℝ} {C : NNReal} (hco : c ≠ o)
    (hf : LipschitzOnWith C f (Icc lo hi ×ˢ Icc (min c o) (max c o))) {t : ℝ → ℝ} (ht : Continuous t) :
    heightStripMoment c o lo hi (fun _ => 1) f (CellBox.heightDeriv f) t = ∫ r in Icc lo hi, f (r, c) * (t r : ℂ) := by
  have hs : ∀ a b : ℝ × ℝ, dist a.swap b.swap = dist a b := fun a b => by
    simp [Prod.dist_eq, max_comm]
  have hf' : LipschitzOnWith C (fun q : ℝ × ℝ => f q.swap) (Icc (min c o) (max c o) ×ˢ Icc lo hi) := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    have := hf.dist_le_mul p.swap ⟨hp.2, hp.1⟩ q.swap ⟨hq.2, hq.1⟩
    rwa [hs] at this
  have key := radial_strip_trace hco hf' ht
  unfold radialStripMoment at key
  unfold heightStripMoment
  rw [Measure.volume_eq_prod, ← setIntegral_prod_swap, ← Measure.volume_eq_prod]
  simp only [one_mul, Prod.fst_swap, Prod.snd_swap]
  exact key


section

open Spectral.Internal.CylIntegral CellAnalysis.ModeVelSquareInternal

private theorem vi_mem_solid {K : CellBox} (hK : IsCellBox K) {q : ℝ × ℝ} (hq : q ∈ K.rect) (θ : ℝ) :
    cylPoint q.1 θ q.2 ∈ K.solid := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hq
  have hr : 0 ≤ q.1 := hK.r_order.1.trans h1
  have hz : 0 ≤ q.2 := hK.z_order.1.trans h3
  simp only [CellBox.solid, Set.mem_ofPred_eq, CellDensityModesSolid.cyl_radius hr,
    CellDensityModesSolid.cyl_height, abs_of_nonneg hz]
  exact ⟨h1, h2, h3, h4⟩

private theorem vi_cyl_fun_eq (r z θ : ℝ) : toSpace (cylMap.symm (swapEquiv ((r, z), θ))) = cylPoint r θ z := by
  rw [swapEquiv_apply, symm_apply, toSpace_apply]
  rfl

private theorem vi_joint_meas {F : Space → Space} (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (fun x : (ℝ × ℝ) × ℝ => F (cylPoint x.1.1 x.2 x.1.2))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← swapEquiv_preimage]
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hv : AEStronglyMeasurable (fun x => F (toSpace (cylMap.symm x))) (volume.restrict cylMap.target) :=
    hF.comp_quasiMeasurePreserving (toSpace_mp.quasiMeasurePreserving.comp symm_qmp)
  refine (hv.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply]
  rw [vi_cyl_fun_eq]

private theorem vi_joint_int {f : Space → ℝ} (hf : Integrable f) :
    Integrable (fun x : (ℝ × ℝ) × ℝ => x.1.1 * f (cylPoint x.1.1 x.2 x.1.2))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hg : Integrable (fun w => f (toSpace w)) := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hf
  have hH := change_integrable hg
  have hσ := (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  rw [swapEquiv_preimage] at hσ
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine hσ.congr_fun (fun x _ => ?_) ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply]
  rw [vi_cyl_fun_eq, swapEquiv_apply]



private theorem vi_kern_meas_gen {v : Space → Space} (hv : AEStronglyMeasurable v volume) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    AEStronglyMeasurable (kern m n v a)
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
        (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hset : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi =ᵐ[volume]
      swapEquiv ⁻¹' cylMap.target := by
    rw [swapEquiv_preimage]
    exact Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Ioc.symm
  rw [Measure.restrict_congr_set hset]
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hΨ : Continuous fun q : ℝ × Space =>
      Complex.exp (-(azimuth m n * q.1 : ℝ) * Complex.I) * (frameVec q.1 q.2 a : ℂ) := by
    have := frameVec_cont a
    fun_prop
  have hvc : AEStronglyMeasurable (fun x => v (toSpace (cylMap.symm x))) (volume.restrict cylMap.target) :=
    hv.comp_quasiMeasurePreserving (toSpace_mp.quasiMeasurePreserving.comp symm_qmp)
  have hk := hΨ.comp_aestronglyMeasurable
      ((continuous_snd.comp continuous_fst).aestronglyMeasurable.prodMk hvc)
  refine (hk.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply, swapEquiv_apply, kern]
  rw [symm_apply, toSpace_apply]
  rfl

private theorem vi_mode_meas_gen {v : Space → Space} (hv : AEStronglyMeasurable v volume) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have h := (vi_kern_meas_gen hv m n a).integral_prod_right'
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p =>
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (p, θ) :=
    funext (mode_eq m n v a)
  rw [e]
  exact h.const_mul _

private theorem vi_kern_norm_le (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (x : (ℝ × ℝ) × ℝ) :
    ‖kern m n v a x‖ ≤ ‖v (cylPoint x.1.1 x.2 x.1.2)‖ := by
  unfold kern
  rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact frameVec_abs _ _ _

private theorem vi_mode_r_integrable {K : CellBox} (hK : IsCellBox K) {v : Space → Space}
    (hv : AEStronglyMeasurable v volume) (hvi : IntegrableOn (fun y => ‖v y‖) K.solid) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖) K.rect := by
  have hp := Real.pi_pos
  have hsm : MeasurableSet K.solid := CellDensityModesSolid.solid_closed K
  have hF : Integrable (K.solid.indicator (fun y => ‖v y‖)) := hvi.integrable_indicator hsm
  have h3 := vi_joint_int hF
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h3
  have hB := h3.integral_prod_left
  have hsl := h3.prod_right_ae
  have hks := (vi_kern_meas_gen hv m n a).prodMk_left
  have hT : MeasurableSet ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) :=
    (measurableSet_Ioi.prod MeasurableSet.univ).inter (measurableSet_Icc.prod measurableSet_Icc)
  have hsub : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    inter_subset_left
  have hhalf : IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖)
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) := by
    have hB' : IntegrableOn (fun q : ℝ × ℝ => ∫ θ in Ioc (-Real.pi) Real.pi,
        q.1 * K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2))
        ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) :=
      IntegrableOn.mono_set hB hsub
    refine (hB'.const_mul (1 / (2 * Real.pi))).mono'
      (continuous_fst.aestronglyMeasurable.mul
        ((vi_mode_meas_gen hv m n a).mono_measure (Measure.restrict_mono hsub le_rfl)).norm) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsl,
      ae_restrict_of_ae_restrict_of_subset hsub hks, ae_restrict_mem hT] with q hq hk hqS
    have hpos : 0 < q.1 := hqS.1.1
    have hgi : Integrable (fun θ => K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2))
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
      refine (hq.const_mul (q.1⁻¹)).congr (ae_of_all _ fun θ => ?_)
      simp only []
      field_simp
    have hkb : ∀ θ, ‖kern m n v a (q, θ)‖ ≤ K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2) := by
      intro θ
      rw [Set.indicator_of_mem (vi_mem_solid hK hqS.2 θ)]
      exact vi_kern_norm_le m n v a (q, θ)
    have hI := norm_integral_le_of_norm_le hgi (ae_of_all _ hkb)
    have e1 : ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2) =
        q.1 * ∫ θ in Ioc (-Real.pi) Real.pi, K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2) :=
      integral_const_mul _ _
    have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    show ‖q.1 * ‖modeVec m n v q.1 q.2 a‖‖ ≤
      1 / (2 * Real.pi) * ∫ θ in Ioc (-Real.pi) Real.pi,
        q.1 * K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2)
    rw [e1, Real.norm_of_nonneg (by positivity), mode_eq, norm_mul, hn]
    calc q.1 * (1 / (2 * Real.pi) * ‖∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (q, θ)‖)
        ≤ q.1 * (1 / (2 * Real.pi) *
            ∫ θ in Ioc (-Real.pi) Real.pi, K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2)) := by
          gcongr
      _ = 1 / (2 * Real.pi) * (q.1 * ∫ θ in Ioc (-Real.pi) Real.pi,
            K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2)) := by ring
  refine hhalf.of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
  have h1 : K.r₁ ≤ p.1 := hp.1.1.1
  have h2 : ¬ (0 < p.1) := fun h => hp.2 ⟨⟨h, trivial⟩, hp.1⟩
  have h3 : p.1 = 0 := le_antisymm (not_lt.mp h2) (le_trans hK.r_order.1 h1)
  simp [h3]

private theorem vi_mode_norm_le {v : Space → Space} {C : ℝ} (hC : ∀ y, ‖v y‖ ≤ C) (m : ℕ) (n : ℤ) (r z : ℝ)
    (a : Fin 3) : ‖modeVec m n v r z a‖ ≤ C := by
  have hp := Real.pi_pos
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold modeVec
  rw [norm_mul]
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hI : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (v (cylPoint r θ z)) a : ℂ)‖ ≤ C * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact (frameVec_abs _ _ _).trans (hC _)
  rw [hn, sub_zero, abs_of_pos (by positivity)] at *
  calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (frameVec θ (v (cylPoint r θ z)) a : ℂ)‖ ≤ 1 / (2 * Real.pi) * (C * (2 * Real.pi)) := by gcongr
    _ = C := by field_simp

private theorem vi_pair_integrable {K : CellBox} (hK : IsCellBox K) {Q row : Space → Space}
    (hQ : AEStronglyMeasurable Q volume) (hQi : IntegrableOn (fun y => ‖Q y‖) K.solid)
    (hr : AEStronglyMeasurable row volume) {C : ℝ} (hC : ∀ y, ‖row y‖ ≤ C) (m : ℕ) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * pairC (modeVec m n Q p.1 p.2) (modeVec m n row p.1 p.2))
      K.rect := by
  have hmQ : ∀ i : Fin 3, AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 i)
      (volume.restrict K.rect) := fun i => (vi_mode_meas_gen hQ m n i).mono_measure (rect_ae_le K hK)
  have hmr : ∀ i : Fin 3, AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n row p.1 p.2 i)
      (volume.restrict K.rect) := fun i => (vi_mode_meas_gen hr m n i).mono_measure (rect_ae_le K hK)
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 : ℂ) * pairC (modeVec m n Q p.1 p.2) (modeVec m n row p.1 p.2))
      (volume.restrict K.rect) := by
    unfold pairC
    refine (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul ?_
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => (hmQ i).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hmr i)))
    refine h.congr (ae_of_all _ fun p => ?_)
    simp [Finset.sum_apply]
  refine Integrable.mono' (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    fun i _ => (vi_mode_r_integrable hK hQ hQi m n i).const_mul C) hmeas ?_
  filter_upwards [ae_restrict_mem (CellDensityModesSolid.rect_meas K)] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  unfold pairC
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  calc p.1 * ‖∑ i : Fin 3, modeVec m n Q p.1 p.2 i * (starRingEnd ℂ) (modeVec m n row p.1 p.2 i)‖
      ≤ p.1 * ∑ i : Fin 3, ‖modeVec m n Q p.1 p.2 i * (starRingEnd ℂ) (modeVec m n row p.1 p.2 i)‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ p.1 * ∑ i : Fin 3, ‖modeVec m n Q p.1 p.2 i‖ * C := by
        gcongr with i
        rw [norm_mul, Complex.norm_conj]
        gcongr
        exact vi_mode_norm_le hC m n p.1 p.2 i
    _ = ∑ i : Fin 3, C * (p.1 * ‖modeVec m n Q p.1 p.2 i‖) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

private theorem vi_mirror_norm (v : Space) : ‖mirror v‖ = ‖v‖ :=
  LinearSolveCore.mirrorIsometry.norm_map v

private theorem vi_row_bound {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} (hc : IsFormData α c)
    (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) {a : Fin N} (ha : a ∈ R.rowSet) :
    ∃ C, ∀ y, ‖c.row a y‖ ≤ C := by
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  have hTb : Bornology.IsBounded (K.solid ∩ {y : Space | 0 ≤ cylHeight y}) :=
    hc.cellRegion_bounded.subset (fun y hy => hD.solid_in_region hy.1)
  obtain ⟨C, hC⟩ : ∃ C, ∀ y ∈ K.solid ∩ {y : Space | 0 ≤ cylHeight y}, ‖c.row a y‖ ≤ C := by
    rcases (K.solid ∩ {y : Space | 0 ≤ cylHeight y}).eq_empty_or_nonempty with hT | ⟨y₀, hy₀⟩
    · exact ⟨0, fun y hy => by rw [hT] at hy; exact absurd hy (Set.notMem_empty y)⟩
    · obtain ⟨ρ, hρ⟩ := hTb.subset_closedBall y₀
      refine ⟨‖c.row a y₀‖ + L * ρ, fun y hy => ?_⟩
      have h1 := hL.dist_le_mul y hy y₀ hy₀
      have h2 : dist y y₀ ≤ ρ := Metric.mem_closedBall.mp (hρ hy)
      have h3 : ‖c.row a y‖ - ‖c.row a y₀‖ ≤ dist (c.row a y) (c.row a y₀) := by
        rw [dist_eq_norm]; exact norm_sub_norm_le _ _
      have h4 : (L : ℝ) * dist y y₀ ≤ L * ρ := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
      linarith
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ K.solid
  · by_cases hz : 0 ≤ cylHeight y
    · exact (hC y ⟨hy, hz⟩).trans (le_max_left _ _)
    · have hneg : cylHeight y < 0 := not_le.mp hz
      have hm : mirror y ∈ K.solid ∩ {y : Space | 0 ≤ cylHeight y} := by
        refine ⟨?_, ?_⟩
        · have hy' := hy
          simp only [CellBox.solid, Set.mem_ofPred_eq] at hy' ⊢
          rw [CellDensityModesSolid.mirror_radius, CellDensityModesSolid.mirror_height]
          exact hy'
        · show 0 ≤ cylHeight (mirror y)
          have h5 : cylHeight (mirror y) = -cylHeight y := by simp [cylHeight, mirror]
          rw [h5]
          linarith
      rw [hR.row_mirror a ha y hy hneg, vi_mirror_norm]
      exact (hC _ hm).trans (le_max_left _ _)
  · rw [hD.rows_in_cell a ha y hy, norm_zero]
    exact le_max_right _ _

end

theorem grad_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3, gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')) K.rect := by
  have hs := hx.1
  obtain ⟨_, hG, _⟩ := MeshDataAffineModes.secondOrder_modes_integrable c.order x.1 x.2.1 x.2.2.1 hs n
    K.r₁ K.r₂ K.z₁ K.z₂
  choose P hPmem hP using fun (i b : Fin 3) => hR.row_low_gradient a ha n i b
  have hPc : ∀ i b, Continuous (P i b) := by
    intro i b
    obtain ⟨cc, hcc⟩ := hPmem i b
    rw [funext hcc]
    fun_prop
  have hwc : Continuous (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) := by
    unfold CellBox.lineWeight
    split_ifs <;> fun_prop
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hmeas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hint : IntegrableOn (fun p : ℝ × ℝ => ∑ i : Fin 3, ∑ b : Fin 3,
      gradMode c.order n x.2.1 i b p * (starRingEnd ℂ) (((K.lineWeight p.1 : ℝ) : ℂ) * P i b p)) K.rect := by
    refine integrable_finset_sum _ fun i _ => integrable_finset_sum _ fun b _ => ?_
    exact (hG i b).mul_continuousOn ((Complex.continuous_conj.comp (hwc.mul (hPc i b))).continuousOn) hcomp
  have hset : (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hax : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    have h0 : volume ({0} ×ˢ univ : Set (ℝ × ℝ)) = 0 := by
      rw [Measure.volume_eq_prod, Measure.prod_prod]; simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp h0] with p hp
    exact fun e => hp ⟨e, mem_univ _⟩
  have hio : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ := by
    rw [← Measure.restrict_congr_set hset]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  refine hint.congr_fun_ae ?_
  filter_upwards [hio, ae_restrict_of_ae hax] with p hp hp0
  have hw : K.lineWeight p.1 ≠ 0 := by
    unfold CellBox.lineWeight
    split_ifs
    · exact hp0
    · exact one_ne_zero
  have key : ∀ i b, (p.1 : ℂ) * rowModeGrad c a n p i b = ((K.lineWeight p.1 : ℝ) : ℂ) * P i b p := by
    intro i b
    rw [← hP i b p hp hp0]
    unfold rHat
    push_cast
    have hw' : ((K.lineWeight p.1 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
    field_simp
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun b _ => ?_
  rw [← key i b, map_mul, Complex.conj_ofReal]
  ring

theorem volume_integrable {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)) K.rect ∧ IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3, gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')) K.rect := by
  refine ⟨?_, grad_integrable hα1 hα2 hc hD hR hL hx ha n⟩
  have hs := hx.1
  have hTf : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have htc : Continuous (fun H : Space →L[ℝ] Space →L[ℝ] Space => secondTrace H) := by
    unfold secondTrace; fun_prop
  have hQ : AEStronglyMeasurable (fun y => secondTrace (x.2.2.1 y)) volume :=
    htc.comp_aestronglyMeasurable hs.measurable_second
  have hQi : IntegrableOn (fun y => ‖secondTrace (x.2.2.1 y)‖) K.solid := by
    have hg : IntegrableOn (fun y => (3 : ℝ) + ∑ i : Fin 3, ∑ j : Fin 3, ‖x.2.2.1 y (unitVector i) (unitVector j)‖ ^ 2)
        K.solid :=
      (integrableOn_const hTf.ne).add hs.second_two.integrableOn
    refine hg.mono' hQ.norm.restrict (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_norm]
    unfold secondTrace
    refine (norm_sum_le _ _).trans ?_
    have hd : ∀ j : Fin 3, ‖x.2.2.1 y (unitVector j) (unitVector j)‖ ≤
        1 + ‖x.2.2.1 y (unitVector j) (unitVector j)‖ ^ 2 := fun j => by
      nlinarith [sq_nonneg (‖x.2.2.1 y (unitVector j) (unitVector j)‖ - 1), norm_nonneg (x.2.2.1 y (unitVector j) (unitVector j))]
    have hsq : ∀ j : Fin 3, ‖x.2.2.1 y (unitVector j) (unitVector j)‖ ^ 2 ≤
        ∑ i' : Fin 3, ‖x.2.2.1 y (unitVector j) (unitVector i')‖ ^ 2 := fun j =>
      Finset.single_le_sum (f := fun i' => ‖x.2.2.1 y (unitVector j) (unitVector i')‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ j)
    simp only [Fin.sum_univ_three] at hd hsq ⊢
    linarith [hd 0, hd 1, hd 2, hsq 0, hsq 1, hsq 2]
  obtain ⟨C, hC⟩ := vi_row_bound hc hD hR ha
  exact vi_pair_integrable hD.box hQ hQi (hc.base.row_two a).aestronglyMeasurable hC c.order n

section

open Filter Topology

private def vd_openCore (K : CellBox) : Set Space :=
  {y | K.r₁ < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < |cylHeight y| ∧ |cylHeight y| < K.z₂}

private theorem vd_openCore_open (K : CellBox) : IsOpen (vd_openCore K) := by
  have hR : Continuous cylRadius := by unfold cylRadius; fun_prop
  have hH : Continuous (fun y => |cylHeight y|) := by unfold cylHeight; fun_prop
  exact ((isOpen_lt continuous_const hR).inter ((isOpen_lt hR continuous_const).inter
    ((isOpen_lt continuous_const hH).inter (isOpen_lt hH continuous_const))))

private theorem vd_openCore_sub (K : CellBox) : vd_openCore K ⊆ K.solid := fun y hy =>
  ⟨hy.1.le, hy.2.1.le, hy.2.2.1.le, hy.2.2.2.le⟩

private theorem vd_upper_nhds (K : CellBox) {y : Space} (hy : y ∈ vd_openCore K) (hh : 0 < cylHeight y) :
    K.solid ∩ {z | 0 ≤ cylHeight z} ∈ nhds y := by
  have hH : Continuous cylHeight := by unfold cylHeight; fun_prop
  refine Filter.mem_of_superset (((vd_openCore_open K).inter (isOpen_lt continuous_const hH)).mem_nhds ⟨hy, hh⟩) ?_
  exact fun z hz => ⟨vd_openCore_sub K hz.1, show 0 ≤ cylHeight z from le_of_lt hz.2⟩

private theorem vd_upper_bound {k N : ℕ} {c : FracCellData k N} {K : CellBox} {a : Fin N} {L : NNReal}
    (hL : LipschitzOnWith L (c.row a) (K.solid ∩ {y | 0 ≤ cylHeight y})) {y : Space}
    (hy : y ∈ vd_openCore K) (hh : 0 < cylHeight y) : ‖fderiv ℝ (c.row a) y‖ ≤ L :=
  norm_fderiv_le_of_lipschitzOn ℝ (vd_upper_nhds K hy hh) hL

private theorem vd_path_radial (r θ z : ℝ) : HasDerivAt (fun s => cylPoint s θ z) (radialUnit θ) r := by
  have e : (fun s => cylPoint s θ z) = fun s => s • radialUnit θ + EuclideanSpace.single 2 z := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, radialUnit]
  rw [e]
  have h := ((hasDerivAt_id r).smul_const (radialUnit θ)).add_const (EuclideanSpace.single 2 z : Space)
  simpa using h

private theorem vd_path_height (r θ z : ℝ) : HasDerivAt (fun s => cylPoint r θ s) axialUnit z := by
  have e : (fun s => cylPoint r θ s) = fun s => s • axialUnit + cylPoint r θ 0 := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, axialUnit]
  rw [e]
  have h := ((hasDerivAt_id z).smul_const axialUnit).add_const (cylPoint r θ 0)
  simpa using h

private theorem vd_path_radialUnit (θ : ℝ) : HasDerivAt (fun t => radialUnit t) (angularUnit θ) θ := by
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

private theorem vd_path_angularUnit (θ : ℝ) : HasDerivAt (fun t => angularUnit t) (-radialUnit θ) θ := by
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

private theorem vd_path_angle (r θ z : ℝ) : HasDerivAt (fun t => cylPoint r t z) (r • angularUnit θ) θ := by
  have e : (fun t => cylPoint r t z) = fun t => r • radialUnit t + EuclideanSpace.single 2 z := by
    funext s; ext j; fin_cases j <;> simp [cylPoint, radialUnit]
  rw [e]
  exact ((vd_path_radialUnit θ).const_smul r).add_const _

private theorem vd_path_unit (θ : ℝ) (a : Fin 3) :
    HasDerivAt (fun t => frameUnit t a) (![angularUnit θ, -radialUnit θ, 0] a) θ := by
  fin_cases a
  · exact vd_path_radialUnit θ
  · exact vd_path_angularUnit θ
  · exact hasDerivAt_const θ axialUnit

private theorem vd_frame_radial_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun s => frameVec θ (g (cylPoint s θ z)) a) (frameMat θ D a 0) r := by
  have e : (fun s => frameVec θ (g (cylPoint s θ z)) a) = fun s => inner ℝ (g (cylPoint s θ z)) (frameUnit θ a) :=
    funext fun s => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt r (vd_path_radial r θ z)).inner ℝ (hasDerivAt_const r (frameUnit θ a))
  refine h.congr_deriv ?_
  simp only [inner_zero_right, zero_add]
  rfl

private theorem vd_frame_height_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun s => frameVec θ (g (cylPoint r θ s)) a) (frameMat θ D a 2) z := by
  have e : (fun s => frameVec θ (g (cylPoint r θ s)) a) = fun s => inner ℝ (g (cylPoint r θ s)) (frameUnit θ a) :=
    funext fun s => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt z (vd_path_height r θ z)).inner ℝ (hasDerivAt_const z (frameUnit θ a))
  refine h.congr_deriv ?_
  simp only [inner_zero_right, zero_add]
  rfl

private theorem vd_frame_angle_deriv {g : Space → Space} {D : Space →L[ℝ] Space} {r θ z : ℝ}
    (hg : HasFDerivAt g D (cylPoint r θ z)) (a : Fin 3) :
    HasDerivAt (fun t => frameVec t (g (cylPoint r t z)) a)
      (r * frameMat θ D a 1 + ![frameVec θ (g (cylPoint r θ z)) 1, -frameVec θ (g (cylPoint r θ z)) 0, 0] a) θ := by
  have e : (fun t => frameVec t (g (cylPoint r t z)) a) = fun t => inner ℝ (g (cylPoint r t z)) (frameUnit t a) :=
    funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
  rw [e]
  have h := (hg.comp_hasDerivAt θ (vd_path_angle r θ z)).inner ℝ (vd_path_unit θ a)
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

private theorem vd_frameMat_abs_le (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : |frameMat θ M a b| ≤ ‖M‖ := by
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

private theorem vd_mode_of_deriv {Φ Φ' : ℝ → ℝ} (m : ℕ) (k : ℤ) (hd : ∀ t, HasDerivAt Φ (Φ' t) t) (hc : Continuous Φ')
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

section

open Breakdown.CellCert.CellEnergy.Internal.AngularFrame

private theorem ts_vec (v : Space) : v = ∑ i : Fin 3, v i • unitVector i := by
  ext j
  fin_cases j <;> simp [unitVector, Fin.sum_univ_three]

private theorem ts_bilin (Hy : Space →L[ℝ] Space →L[ℝ] Space) (u : Space) :
    Hy u u = ∑ j : Fin 3, ∑ l : Fin 3, (u j * u l) • Hy (unitVector j) (unitVector l) := by
  conv_lhs => rw [ts_vec u]
  simp only [map_sum, map_smul, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, Finset.smul_sum,
    smul_smul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  rw [mul_comm]

private theorem ts_third (θ : ℝ) (Hy : Space →L[ℝ] Space →L[ℝ] Space) (i b : Fin 3) :
    frameThird θ Hy i b b = ∑ j : Fin 3, ∑ l : Fin 3,
      (frameUnit θ b j * frameUnit θ b l) * frameVec θ (Hy (unitVector j) (unitVector l)) i := by
  rw [frameThird, ts_bilin, sum_inner]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [real_inner_smul_left, ModeVelSquareInternal.frameVec_eq]

private theorem ts_orth (θ : ℝ) (j l : Fin 3) :
    ∑ b : Fin 3, frameUnit θ b j * frameUnit θ b l = if j = l then 1 else 0 := by
  have h := Real.sin_sq_add_cos_sq θ
  fin_cases j <;> fin_cases l <;>
    simp [Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit] <;> nlinarith [h]

private theorem ts_trace (θ : ℝ) (Hy : Space →L[ℝ] Space →L[ℝ] Space) (i : Fin 3) :
    ∑ b : Fin 3, frameThird θ Hy i b b = frameVec θ (secondTrace Hy) i := by
  simp only [ts_third]
  rw [Finset.sum_comm]
  have e : ∀ j : Fin 3, ∑ b : Fin 3, ∑ l : Fin 3,
      (frameUnit θ b j * frameUnit θ b l) * frameVec θ (Hy (unitVector j) (unitVector l)) i =
      frameVec θ (Hy (unitVector j) (unitVector j)) i := by
    intro j
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_mul, ts_orth]
    simp
  simp_rw [e]
  unfold secondTrace
  simp only [ModeVelSquareInternal.frameVec_eq, sum_inner]

end

theorem trace_split {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ i : Fin 3,
      modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2 i = ∑ b : Fin 3, modeThird c.order n x.2.2.1 i b b p := by
  have hs := hx.1
  have hK := hD.box
  have hTf : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have hev : ∀ j l : Fin 3, Continuous (fun Hy : Space →L[ℝ] Space →L[ℝ] Space => Hy (unitVector j) (unitVector l)) :=
    fun j l => by fun_prop
  have hF : ∀ j l : Fin 3, AEStronglyMeasurable (fun y => x.2.2.1 y (unitVector j) (unitVector l)) volume :=
    fun j l => (hev j l).comp_aestronglyMeasurable hs.measurable_second
  have hFi : ∀ j l : Fin 3, IntegrableOn (fun y => ‖x.2.2.1 y (unitVector j) (unitVector l)‖) K.solid := by
    intro j l
    have hg : IntegrableOn (fun y => (1 : ℝ) + ∑ i : Fin 3, ∑ j : Fin 3, ‖x.2.2.1 y (unitVector i) (unitVector j)‖ ^ 2)
        K.solid := (integrableOn_const hTf.ne).add hs.second_two.integrableOn
    refine hg.mono' (hF j l).norm.restrict (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_norm]
    have h1 : ‖x.2.2.1 y (unitVector j) (unitVector l)‖ ≤ 1 + ‖x.2.2.1 y (unitVector j) (unitVector l)‖ ^ 2 := by
      nlinarith [sq_nonneg (‖x.2.2.1 y (unitVector j) (unitVector l)‖ - 1)]
    have h2 : ‖x.2.2.1 y (unitVector j) (unitVector l)‖ ^ 2 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, ‖x.2.2.1 y (unitVector i) (unitVector j)‖ ^ 2 :=
      (Finset.single_le_sum (f := fun l' => ‖x.2.2.1 y (unitVector j) (unitVector l')‖ ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ l)).trans
        (Finset.single_le_sum (f := fun j' => ∑ l' : Fin 3, ‖x.2.2.1 y (unitVector j') (unitVector l')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.mem_univ j))
    linarith
  have hci := fun j l => LayoutRowPressure.circle_integrable hK (hF j l) (hFi j l)
  filter_upwards [Filter.eventually_all.2 fun j => Filter.eventually_all.2 fun l => hci j l] with p hp
  intro i
  have hec : Continuous (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)) := by fun_prop
  have hfc : ∀ b c' : Fin 3, Continuous (fun t : ℝ => frameUnit t b c') := fun b c' => by
    fin_cases b <;> fin_cases c' <;> simp [frameUnit, radialUnit, angularUnit, axialUnit] <;> fun_prop
  have hII : ∀ b : Fin 3, IntervalIntegrable (fun θ => Complex.exp (-(azimuth c.order n * θ : ℝ) * Complex.I) *
      (frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) i b b : ℂ)) volume 0 (2 * Real.pi) := by
    intro b
    have e : (fun θ => Complex.exp (-(azimuth c.order n * θ : ℝ) * Complex.I) *
        (frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) i b b : ℂ)) = fun θ => ∑ j : Fin 3, ∑ l : Fin 3,
          (Complex.exp (-(azimuth c.order n * θ : ℝ) * Complex.I) * ((frameUnit θ b j * frameUnit θ b l : ℝ) : ℂ)) *
            (frameVec θ (x.2.2.1 (cylPoint p.1 θ p.2) (unitVector j) (unitVector l)) i : ℂ) := by
      funext θ
      rw [ts_third, Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.ofReal_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun l _ => ?_
      push_cast
      ring
    rw [e]
    exact Breakdown.CellCert.CellEnergy.Internal.AngularFrame.ii_sum2 fun j l =>
      Breakdown.CellCert.CellEnergy.Internal.AngularFrame.ii_cmul (hp j l i)
      (hec.mul (Complex.continuous_ofReal.comp ((hfc b j).mul (hfc b l))))
  have e1 : ∀ b : Fin 3, modeThird c.order n x.2.2.1 i b b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * θ : ℝ) * Complex.I) *
        (frameThird θ (x.2.2.1 (cylPoint p.1 θ p.2)) i b b : ℂ) := fun b => rfl
  simp only [e1]
  rw [← Finset.mul_sum, ← intervalIntegral.integral_finsetSum fun b _ => hII b]
  show (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * θ : ℝ) * Complex.I) *
      (frameVec θ (secondTrace (x.2.2.1 (cylPoint p.1 θ p.2))) i : ℂ) = _
  congr 1
  refine intervalIntegral.integral_congr fun θ _ => ?_
  rw [← Finset.mul_sum, ← Complex.ofReal_sum, ts_trace]

theorem row_mode_derivs {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ i : Fin 3,
      CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q i) p =
          rowModeVec c a n p i + (p.1 : ℂ) * rowModeGrad c a n p i 0 ∧
        CellBox.heightDeriv (fun q => rowModeVec c a n q i) p = rowModeGrad c a n p i 2 := by
  have hK := hD.box
  have hset : (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hio : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ := by
    rw [← Measure.restrict_congr_set hset]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hio] with p hp
  obtain ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩ := hp
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
  have hVcore : ∀ y ∈ V, y ∈ vd_openCore K ∧ 0 < cylHeight y := by
    intro y hy
    have h0 : 0 < cylHeight y := lt_of_le_of_lt hK.z_order.1 hy.2.2.1
    refine ⟨⟨lt_of_le_of_lt (le_max_left _ _) hy.1, hy.2.1, ?_, ?_⟩, h0⟩
    · rw [abs_of_pos h0]; exact hy.2.2.1
    · rw [abs_of_pos h0]; exact hy.2.2.2
  have hVeq : ∀ y ∈ V, c.row a =ᶠ[nhds y] f := by
    intro y hy
    refine Filter.eventually_of_mem (hVo.mem_nhds hy) fun w hw => ?_
    obtain ⟨hwc, hw0⟩ := hVcore w hw
    exact hfeq w (vd_openCore_sub K hwc) hw0.le (le_trans (le_max_right _ _) hw.1.le)
  have hder : ∀ y ∈ V, HasFDerivAt (c.row a) (fderiv ℝ (c.row a) y) y := by
    intro y hy
    have h1 : HasFDerivAt f (fderiv ℝ f y) y := (hf.differentiable (by norm_num) y).hasFDerivAt
    rw [(hVeq y hy).fderiv_eq]
    exact h1.congr_of_eventuallyEq (hVeq y hy)
  have hcont : ContinuousOn (fderiv ℝ (c.row a)) V :=
    (hf.continuous_fderiv (by norm_num)).continuousOn.congr fun y hy => (hVeq y hy).fderiv_eq
  have hbd : ∀ y ∈ V, ‖fderiv ℝ (c.row a) y‖ ≤ L := fun y hy =>
    vd_upper_bound hL (hVcore y hy).1 (hVcore y hy).2
  have hmem : ∀ x t z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → cylPoint x t z' ∈ V := by
    intro x t z' h1 h2 h3 h4
    have hx0 : 0 ≤ x := le_trans (le_trans hK.r_order.1 (le_max_left _ _)) h1.le
    show lo < cylRadius (cylPoint x t z') ∧ cylRadius (cylPoint x t z') < K.r₂ ∧
      K.z₁ < cylHeight (cylPoint x t z') ∧ cylHeight (cylPoint x t z') < K.z₂
    rw [CellDensityModesSolid.cyl_radius hx0, CellDensityModesSolid.cyl_height]
    exact ⟨h1, h2, h3, h4⟩
  have hlop : lo < p.1 := max_lt hr1 (by linarith)
  have hpath : ∀ x z', Continuous (fun t => cylPoint x t z') := fun x z' =>
    continuous_iff_continuousAt.2 fun t => (vd_path_angle x t z').continuousAt
  have hFc : ∀ x z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ∀ b,
      Continuous (fun t => frameVec t (c.row a (cylPoint x t z')) b) := by
    intro x z' h1 h2 h3 h4 b
    have hg : Continuous (fun t => c.row a (cylPoint x t z')) :=
      continuous_iff_continuousAt.2 fun t =>
        (hder _ (hmem x t z' h1 h2 h3 h4)).continuousAt.comp (f := fun t => cylPoint x t z')
          (vd_path_angle x t z').continuousAt
    have e : (fun t => frameVec t (c.row a (cylPoint x t z')) b) =
        fun t => inner ℝ (c.row a (cylPoint x t z')) (frameUnit t b) :=
      funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
    rw [e]
    exact hg.inner (ModeVelSquareInternal.frameUnit_cont b)
  have hMc : ∀ x z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ∀ a' b',
      Continuous (fun t => frameMat t (fderiv ℝ (c.row a) (cylPoint x t z')) a' b') := by
    intro x z' h1 h2 h3 h4 a' b'
    have hD' : Continuous (fun t => fderiv ℝ (c.row a) (cylPoint x t z')) :=
      hcont.comp_continuous (hpath x z') fun t => hmem x t z' h1 h2 h3 h4
    show Continuous fun t => inner ℝ ((fderiv ℝ (c.row a) (cylPoint x t z')) (frameUnit t b')) (frameUnit t a')
    exact (hD'.clm_apply (ModeVelSquareInternal.frameUnit_cont b')).inner (ModeVelSquareInternal.frameUnit_cont a')
  have hec : Continuous (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)) := by fun_prop
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)‖ = 1 := fun t => by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  intro i
  have hRd : HasDerivAt (fun s => rowModeVec c a n (s, p.2) i) (rowModeGrad c a n p i 0) p.1 := by
    have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (a := 0) (b := 2 * Real.pi) (bound := fun _ => (L : ℝ))
      (F := fun s t => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameVec t (c.row a (cylPoint s t p.2)) i : ℂ))
      (F' := fun s t => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint s t p.2)) i 0 : ℂ)) (Ioo_mem_nhds hlop hr2)
      (Filter.eventually_of_mem (Ioo_mem_nhds hlop hr2) fun s hs =>
        (hec.mul (Complex.continuous_ofReal.comp (hFc s p.2 hs.1 hs.2 hz1 hz2 i))).aestronglyMeasurable)
      ((hec.mul (Complex.continuous_ofReal.comp (hFc p.1 p.2 hlop hr2 hz1 hz2 i))).intervalIntegrable _ _)
      ((hec.mul (Complex.continuous_ofReal.comp (hMc p.1 p.2 hlop hr2 hz1 hz2 i 0))).aestronglyMeasurable)
      (ae_of_all _ fun t _ s hs => by
        rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (vd_frameMat_abs_le _ _ _ _).trans (hbd _ (hmem s t p.2 hs.1 hs.2 hz1 hz2)))
      intervalIntegrable_const
      (ae_of_all _ fun t _ s hs =>
        ((vd_frame_radial_deriv (hder _ (hmem s t p.2 hs.1 hs.2 hz1 hz2)) i).ofReal_comp).const_mul _)
    exact key.2.const_mul _
  have hHd : HasDerivAt (fun s => rowModeVec c a n (p.1, s) i) (rowModeGrad c a n p i 2) p.2 := by
    have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume)
      (a := 0) (b := 2 * Real.pi) (bound := fun _ => (L : ℝ))
      (F := fun s t => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameVec t (c.row a (cylPoint p.1 t s)) i : ℂ))
      (F' := fun s t => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t s)) i 2 : ℂ)) (Ioo_mem_nhds hz1 hz2)
      (Filter.eventually_of_mem (Ioo_mem_nhds hz1 hz2) fun s hs =>
        (hec.mul (Complex.continuous_ofReal.comp (hFc p.1 s hlop hr2 hs.1 hs.2 i))).aestronglyMeasurable)
      ((hec.mul (Complex.continuous_ofReal.comp (hFc p.1 p.2 hlop hr2 hz1 hz2 i))).intervalIntegrable _ _)
      ((hec.mul (Complex.continuous_ofReal.comp (hMc p.1 p.2 hlop hr2 hz1 hz2 i 2))).aestronglyMeasurable)
      (ae_of_all _ fun t _ s hs => by
        rw [norm_mul, hnorm, one_mul, Complex.norm_real, Real.norm_eq_abs]
        exact (vd_frameMat_abs_le _ _ _ _).trans (hbd _ (hmem p.1 t s hlop hr2 hs.1 hs.2)))
      intervalIntegrable_const
      (ae_of_all _ fun t _ s hs =>
        ((vd_frame_height_deriv (hder _ (hmem p.1 t s hlop hr2 hs.1 hs.2)) i).ofReal_comp).const_mul _)
    exact key.2.const_mul _
  refine ⟨?_, hHd.deriv⟩
  unfold CellBox.radialDeriv
  have h : HasDerivAt (fun s : ℝ => ((s : ℝ) : ℂ) * rowModeVec c a n (s, p.2) i)
      (((1 : ℝ) : ℂ) * rowModeVec c a n (p.1, p.2) i + ((p.1 : ℝ) : ℂ) * rowModeGrad c a n p i 0) p.1 :=
    ((hasDerivAt_id p.1).ofReal_comp).mul hRd
  show deriv (fun s : ℝ => ((s : ℝ) : ℂ) * rowModeVec c a n (s, p.2) i) p.1 = _
  rw [h.deriv]
  simp

section

open Breakdown.CellCert.CellEnergy Breakdown.CellCert.CellEnergy.Internal.AngularFrame

theorem second_angular {K : CellBox} (hK : IsCellBox K) {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hF : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3) :
    ∀ᵐ p ∂(volume.restrict K.rect), angularGradMode m n H a b p =
      ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b' * gradMode m n G a' b' p := by
  have hC := circleWeak
  have locG : ∀ i, LocallyIntegrable (fun y => G y (unitVector i)) volume := fun i =>
    locInt_vec (meas_G hF.measurable_gradient i) hF.gradient_two fun y => G_sq_le (G y) i
  have locH : ∀ j i, LocallyIntegrable (fun y => H y (unitVector j) (unitVector i)) volume := fun j i =>
    locInt_vec (meas_H hF.measurable_second j i) hF.second_two fun y => H_sq_le (H y) j i
  have locf : ∀ i l, LocallyIntegrable (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) volume :=
    fun i l => locInt_sq ((meas_G hF.measurable_gradient i).inner aestronglyMeasurable_const)
      hF.gradient_two fun y => (inner_sq_le _ l).trans (G_sq_le (G y) i)
  have locs : ∀ j i l, LocallyIntegrable (fun y => inner ℝ (H y (unitVector j) (unitVector i)) (unitVector l))
      volume := fun j i l => locInt_sq ((meas_H hF.measurable_second j i).inner aestronglyMeasurable_const)
      hF.second_two fun y => (inner_sq_le _ l).trans (H_sq_le (H y) j i)
  have locg : ∀ i l, LocallyIntegrable (fun y => gv (H y) i l) volume := by
    intro i l
    unfold gv
    refine locallyIntegrable_finsetSum Finset.univ fun j _ => ?_
    exact locallyIntegrable_iff.2 fun K hK => ((locs j i l).integrableOn_isCompact hK).smul_const _
  have hweak : ∀ i l, ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l) =
        -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
    intro i l φ hφ j
    have hw := hF.weak_second φ hφ i j
    have hcont : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have hsupp : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.2.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) (by simp)
    have hi1 := (locG i).integrable_smul_left_of_hasCompactSupport hcont hsupp
    have hi2 := (locH j i).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    set L : Space →L[ℝ] ℝ := innerSL ℝ (unitVector l)
    calc ∫ y, fderiv ℝ φ y (unitVector j) * inner ℝ (G y (unitVector i)) (unitVector l)
        = ∫ y, L (fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := by
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp [L, innerSL_apply_apply, real_inner_comm]
      _ = L (∫ y, fderiv ℝ φ y (unitVector j) • G y (unitVector i)) := L.integral_comp_comm hi1
      _ = -L (∫ y, φ y • H y (unitVector j) (unitVector i)) := by rw [hw, map_neg]
      _ = -∫ y, L (φ y • H y (unitVector j) (unitVector i)) := by rw [L.integral_comp_comm hi2]
      _ = -∫ y, φ y * inner ℝ (gv (H y) i l) (unitVector j) := by
          congr 1
          refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [gv_inner]
          simp [L, innerSL_apply_apply, real_inner_comm]
  have hKer := fun i l => hC (fun y => inner ℝ (G y (unitVector i)) (unitVector l)) (fun y => gv (H y) i l)
    (locf i l) (locg i l) (hweak i l)
  have hk : azimuth m n = ((n * m : ℤ) : ℝ) := by
    simp [azimuth]
  have hint := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l => (hKer i l).1
  have hid := Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun l =>
    (hKer i l).2 (wgt (azimuth m n) a b i l) (wgt_smooth _ a b i l) (hk ▸ wgt_periodic _ a b i l)
  have h0 : ∀ᵐ p : ℝ × ℝ ∂volume, p.1 ≠ 0 := by
    have hnull : volume ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = 0 := by
      rw [show ((Prod.fst ⁻¹' ({0} : Set ℝ)) : Set (ℝ × ℝ)) = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) by
        ext p; simp, Measure.volume_eq_prod, Measure.prod_prod]
      simp
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 hnull] with p hp
    simpa using hp
  have hrect : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  rw [ae_restrict_iff' hrect]
  filter_upwards [hint, hid, h0] with p h1 h2 h3 hp
  have hr : 0 < p.1 := lt_of_le_of_ne (hK.r_order.1.trans hp.1.1) (Ne.symm h3)
  obtain ⟨r, z⟩ := p
  exact point m n G H a b r z (fun i l => (h1 i l hr).1) (fun i l => (h1 i l hr).2)
    (fun i l => h2 i l hr)


end

theorem row_angular {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      (p.1 : ℂ) * rowModeGrad c a n p 0 1 =
          ((azimuth c.order n : ℂ) * Complex.I) * rowModeVec c a n p 0 - rowModeVec c a n p 1 ∧
        (p.1 : ℂ) * rowModeGrad c a n p 1 1 =
          ((azimuth c.order n : ℂ) * Complex.I) * rowModeVec c a n p 1 + rowModeVec c a n p 0 ∧
        (p.1 : ℂ) * rowModeGrad c a n p 2 1 = ((azimuth c.order n : ℂ) * Complex.I) * rowModeVec c a n p 2 := by
  have hK := hD.box
  have hset : (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ : Set (ℝ × ℝ)) =ᵐ[volume] K.rect := by
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  have hio : ∀ᵐ p ∂(volume.restrict K.rect), p ∈ Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ := by
    rw [← Measure.restrict_congr_set hset]
    exact ae_restrict_mem (measurableSet_Ioo.prod measurableSet_Ioo)
  filter_upwards [hio] with p hp
  obtain ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩ := hp
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
  have hVcore : ∀ y ∈ V, y ∈ vd_openCore K ∧ 0 < cylHeight y := by
    intro y hy
    have h0 : 0 < cylHeight y := lt_of_le_of_lt hK.z_order.1 hy.2.2.1
    refine ⟨⟨lt_of_le_of_lt (le_max_left _ _) hy.1, hy.2.1, ?_, ?_⟩, h0⟩
    · rw [abs_of_pos h0]; exact hy.2.2.1
    · rw [abs_of_pos h0]; exact hy.2.2.2
  have hVeq : ∀ y ∈ V, c.row a =ᶠ[nhds y] f := by
    intro y hy
    refine Filter.eventually_of_mem (hVo.mem_nhds hy) fun w hw => ?_
    obtain ⟨hwc, hw0⟩ := hVcore w hw
    exact hfeq w (vd_openCore_sub K hwc) hw0.le (le_trans (le_max_right _ _) hw.1.le)
  have hder : ∀ y ∈ V, HasFDerivAt (c.row a) (fderiv ℝ (c.row a) y) y := by
    intro y hy
    have h1 : HasFDerivAt f (fderiv ℝ f y) y := (hf.differentiable (by norm_num) y).hasFDerivAt
    rw [(hVeq y hy).fderiv_eq]
    exact h1.congr_of_eventuallyEq (hVeq y hy)
  have hcont : ContinuousOn (fderiv ℝ (c.row a)) V :=
    (hf.continuous_fderiv (by norm_num)).continuousOn.congr fun y hy => (hVeq y hy).fderiv_eq
  have hbd : ∀ y ∈ V, ‖fderiv ℝ (c.row a) y‖ ≤ L := fun y hy =>
    vd_upper_bound hL (hVcore y hy).1 (hVcore y hy).2
  have hmem : ∀ x t z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → cylPoint x t z' ∈ V := by
    intro x t z' h1 h2 h3 h4
    have hx0 : 0 ≤ x := le_trans (le_trans hK.r_order.1 (le_max_left _ _)) h1.le
    show lo < cylRadius (cylPoint x t z') ∧ cylRadius (cylPoint x t z') < K.r₂ ∧
      K.z₁ < cylHeight (cylPoint x t z') ∧ cylHeight (cylPoint x t z') < K.z₂
    rw [CellDensityModesSolid.cyl_radius hx0, CellDensityModesSolid.cyl_height]
    exact ⟨h1, h2, h3, h4⟩
  have hlop : lo < p.1 := max_lt hr1 (by linarith)
  have hpath : ∀ x z', Continuous (fun t => cylPoint x t z') := fun x z' =>
    continuous_iff_continuousAt.2 fun t => (vd_path_angle x t z').continuousAt
  have hFc : ∀ x z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ∀ b,
      Continuous (fun t => frameVec t (c.row a (cylPoint x t z')) b) := by
    intro x z' h1 h2 h3 h4 b
    have hg : Continuous (fun t => c.row a (cylPoint x t z')) :=
      continuous_iff_continuousAt.2 fun t =>
        (hder _ (hmem x t z' h1 h2 h3 h4)).continuousAt.comp (f := fun t => cylPoint x t z')
          (vd_path_angle x t z').continuousAt
    have e : (fun t => frameVec t (c.row a (cylPoint x t z')) b) =
        fun t => inner ℝ (c.row a (cylPoint x t z')) (frameUnit t b) :=
      funext fun t => ModeVelSquareInternal.frameVec_eq _ _ _
    rw [e]
    exact hg.inner (ModeVelSquareInternal.frameUnit_cont b)
  have hMc : ∀ x z', lo < x → x < K.r₂ → K.z₁ < z' → z' < K.z₂ → ∀ a' b',
      Continuous (fun t => frameMat t (fderiv ℝ (c.row a) (cylPoint x t z')) a' b') := by
    intro x z' h1 h2 h3 h4 a' b'
    have hD' : Continuous (fun t => fderiv ℝ (c.row a) (cylPoint x t z')) :=
      hcont.comp_continuous (hpath x z') fun t => hmem x t z' h1 h2 h3 h4
    show Continuous fun t => inner ℝ ((fderiv ℝ (c.row a) (cylPoint x t z')) (frameUnit t b')) (frameUnit t a')
    exact (hD'.clm_apply (ModeVelSquareInternal.frameUnit_cont b')).inner (ModeVelSquareInternal.frameUnit_cont a')
  have hec : Continuous (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)) := by fun_prop
  have hnorm : ∀ t : ℝ, ‖Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I)‖ = 1 := fun t => by
    rw [← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I]
  have hpV : ∀ t, cylPoint p.1 t p.2 ∈ V := fun t => hmem _ _ _ hlop hr2 hz1 hz2
  have key : ∀ i : Fin 3, (p.1 : ℂ) * (∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 : ℂ)) +
      (∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ)) =
      ((azimuth c.order n : ℂ) * Complex.I) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) * (frameVec t (c.row a (cylPoint p.1 t p.2)) i : ℂ) := by
    intro i
    have hang : ∀ t', HasDerivAt (fun t => frameVec t (c.row a (cylPoint p.1 t p.2)) i)
        (p.1 * frameMat t' (fderiv ℝ (c.row a) (cylPoint p.1 t' p.2)) i 1 +
          ![frameVec t' (c.row a (cylPoint p.1 t' p.2)) 1, -frameVec t' (c.row a (cylPoint p.1 t' p.2)) 0, 0] i) t' :=
      fun t' => vd_frame_angle_deriv (hder _ (hpV t')) i
    have hEc : Continuous (fun t => ![frameVec t (c.row a (cylPoint p.1 t p.2)) 1,
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
    have hibp := vd_mode_of_deriv c.order n hang
      ((continuous_const.mul (hMc p.1 p.2 hlop hr2 hz1 hz2 i 1)).add hEc) h2pi
    rw [← hibp]
    have hi1 : IntervalIntegrable (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i 1 : ℂ)) volume 0 (2 * Real.pi) :=
      (hec.mul (Complex.continuous_ofReal.comp (hMc p.1 p.2 hlop hr2 hz1 hz2 i 1))).intervalIntegrable _ _
    have hi2 : IntervalIntegrable (fun t : ℝ => Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] i : ℝ) : ℂ))
        volume 0 (2 * Real.pi) :=
      (hec.mul (Complex.continuous_ofReal.comp hEc)).intervalIntegrable _ _
    rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add (hi1.const_mul _) hi2]
    refine intervalIntegral.integral_congr fun t _ => ?_
    push_cast
    ring
  have k0 := key 0
  have k1 := key 1
  have k2 := key 2
  have j0 : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
      ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] 0 : ℝ) : ℂ) =
      ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameVec t (c.row a (cylPoint p.1 t p.2)) 1 : ℂ) := rfl
  have j1 : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
      ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] 1 : ℝ) : ℂ) =
      -∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameVec t (c.row a (cylPoint p.1 t p.2)) 0 : ℂ) := by
    rw [← intervalIntegral.integral_neg]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [Matrix.cons_val_one]
    push_cast
    ring
  have j2 : ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
      ((![frameVec t (c.row a (cylPoint p.1 t p.2)) 1, -frameVec t (c.row a (cylPoint p.1 t p.2)) 0, (0 : ℝ)] 2 : ℝ) : ℂ) = 0 := by
    simp
  rw [j0] at k0
  rw [j1] at k1
  rw [j2] at k2
  have e : ∀ i j, rowModeGrad c a n p i j = (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameMat t (fderiv ℝ (c.row a) (cylPoint p.1 t p.2)) i j : ℂ) := fun i j => rfl
  have f : ∀ i, rowModeVec c a n p i = (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (frameVec t (c.row a (cylPoint p.1 t p.2)) i : ℂ) := fun i => rfl
  rw [e, e, e, f, f, f]
  refine ⟨?_, ?_, ?_⟩
  · linear_combination (1 / (2 * Real.pi) : ℂ) * k0
  · linear_combination (1 / (2 * Real.pi) : ℂ) * k1
  · linear_combination (1 / (2 * Real.pi) : ℂ) * k2

theorem angular_cancel {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect),
      ∑ i : Fin 3, ((p.1 : ℂ) * modeThird c.order n x.2.2.1 i 1 1 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        (p.1 : ℂ) * gradMode c.order n x.2.1 i 1 p * (starRingEnd ℂ) (rowModeGrad c a n p i 1)) =
      ∑ i : Fin 3, gradMode c.order n x.2.1 i 0 p * (starRingEnd ℂ) (rowModeVec c a n p i) := by
  have hB := fun i => second_angular hD.box hx.1 n i 1
  filter_upwards [Filter.eventually_all.2 hB, row_angular hα1 hα2 hc hD hR hL hx ha n] with p hB hA
  obtain ⟨hA0, hA1, hA2⟩ := hA
  have hB0 := hB 0
  have hB1 := hB 1
  have hB2 := hB 2
  simp only [angularGradMode, Breakdown.CellCert.CellEnergy.angularComb, Breakdown.CellCert.CellEnergy.frameTurn,
    Fin.sum_univ_three] at hB0 hB1 hB2
  simp at hB0 hB1 hB2
  have c0 := congrArg (starRingEnd ℂ) hA0
  have c1 := congrArg (starRingEnd ℂ) hA1
  have c2 := congrArg (starRingEnd ℂ) hA2
  simp only [map_mul, map_sub, map_add, Complex.conj_ofReal, Complex.conj_I] at c0 c1 c2
  simp only [Fin.sum_univ_three]
  linear_combination (starRingEnd ℂ) (rowModeVec c a n p 0) * hB0 + (starRingEnd ℂ) (rowModeVec c a n p 1) * hB1 +
    (starRingEnd ℂ) (rowModeVec c a n p 2) * hB2 + gradMode c.order n x.2.1 0 1 p * c0 +
    gradMode c.order n x.2.1 1 1 p * c1 + gradMode c.order n x.2.1 2 1 p * c2

theorem pointwise_split {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) :
    ∀ᵐ p ∂(volume.restrict K.rect), (p.1 : ℂ) * pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p) + (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3, gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b') =
      ∑ i : Fin 3, (((p.1 : ℂ) * L.secondModeOf n x i 0 0 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 0 p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q i) p)) + ((p.1 : ℂ) * L.secondModeOf n x i 2 2 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 2 p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q i) p))) := by
  have hord : L.order = c.order := hL.layout.order_eq
  filter_upwards [trace_split hα1 hα2 hc hD hR hL hx ha n, row_mode_derivs hα1 hα2 hc hD hR hL hx ha n,
    angular_cancel hα1 hα2 hc hD hR hL hx ha n] with p hT hRD hA
  have h1 := fun i => (hRD i).1
  have h2 := fun i => (hRD i).2
  simp only [CellLayout.secondModeOf, CellLayout.gradModeOf, hord, h1, h2]
  unfold pairC
  simp only [hT, Fin.sum_univ_three] at hA ⊢
  simp only [map_add, map_mul, Complex.conj_ofReal]
  linear_combination hA

theorem radial_side {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3) (cf : Fin L.segCount → Fin (L.degSide + 1) → ℂ)
    (hcf : ∀ s, ∀ p ∈ K.rect,
      ((L.segment s).radial → p.1 = (L.segment s).level →
          rowModeVec c a n p i = ∑ d, cf s d * ((L.segment s).test d p.2 : ℂ)) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level →
          rowModeVec c a n p i = ∑ d, cf s d * ((L.segment s).test d p.1 : ℂ))) :
    IntegrableOn (fun p : ℝ × ℝ => ((p.1 : ℂ) * L.secondModeOf n x i 0 0 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 0 p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q i) p))) K.rect ∧
    ∫ p in K.rect, ((p.1 : ℂ) * L.secondModeOf n x i 0 0 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 0 p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q i) p)) =
      ∑ s : Fin L.segCount, ∑ d : Fin (L.degSide + 1), (if (L.segment s).radial then
        edgeSign (L.segment s).level (L.segment s).other * ((L.segment s).level : ℂ) * (starRingEnd ℂ) (cf s d) *
          (L.segment s).moment true (L.gradModeOf n x i 0) (L.secondModeOf n x i 0 0) (L.secondModeOf n x i 0 2) d else 0) := by
  have hK := hD.box
  have hr := hK.r_order
  have hord : L.order = c.order := hL.layout.order_eq
  have hW := modes_radial_pair_gradient c x hx L hord n i
  obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n i
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨M, hM⟩ := hcomp.exists_bound_of_continuousOn hC.continuousOn
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM (K.r₁, K.z₁) ⟨⟨le_rfl, hr.2.le⟩, le_rfl, hK.z_order.2.le⟩)
  have hRb : ∀ p ∈ K.rect, |p.1| ≤ K.r₂ := fun p hp => by
    rw [abs_of_nonneg (hr.1.trans hp.1.1)]; exact hp.1.2
  have hGL := lp_coord_slope hC hRb hM (hr.1.trans hr.2.le) hM0
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun q => (q.1 : ℂ) * (starRingEnd ℂ) (rowModeVec c a n q i) := ⟨_, rfl⟩
  rw [← hGdef] at hGL
  have hfun : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x i 0 0 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 0 p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q i) p)) =
      fun p => L.secondModeOf n x i 0 0 p * G p + L.gradModeOf n x i 0 p * CellBox.radialDeriv G p := by
    funext p
    rw [← radialDeriv_conj]
    have e : (fun q : ℝ × ℝ => (starRingEnd ℂ) ((q.1 : ℂ) * rowModeVec c a n q i)) = G := by
      rw [hGdef]; funext q; simp [map_mul, Complex.conj_ofReal]
    rw [e, hGdef]
    ring
  have hGa : K.r₁ = 0 → ∀ z ∈ Icc K.z₁ K.z₂, G (K.r₁, z) = 0 := by
    intro h0 z _; rw [hGdef]; simp [h0]
  obtain ⟨hI, hE⟩ := radial_slope_parts hW hr.1 hr.2 hGL hGa
  rw [hfun]
  refine ⟨hI, ?_⟩
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  have hGv : ∀ v ∈ Icc K.r₁ K.r₂, ∀ s, (L.segment s).radial = true → (L.segment s).level = v →
      ∀ z ∈ Icc K.z₁ K.z₂,
      G (v, z) = (v : ℂ) * ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) * ((L.segment s).test d z : ℂ) := by
    intro v hv s hrad hlev z hz
    have h := (hcf s (v, z) ⟨hv, hz⟩).1 hrad hlev.symm
    rw [hGdef]
    simp only
    rw [h, map_sum]
    simp [map_mul, Complex.conj_ofReal]
  have hGc : ContinuousOn G K.rect := hGL.continuousOn
  have h2 := radial_side_sum (dFz := L.secondModeOf n x i 0 2) hK hL hW hGc cf (v := K.r₂) (o := K.r₁) (Or.inl rfl)
    (by ring) (hGv K.r₂ ⟨hr.2.le, le_rfl⟩)
  rw [hrect] at h2
  rw [hrect, hE, h2]
  have h1 : (∫ p in Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂,
        ((((1 / (K.r₁ - K.r₂) : ℝ)) : ℂ) * L.gradModeOf n x i 0 p + (((p.1 - K.r₂) / (K.r₁ - K.r₂) : ℝ) : ℂ) *
          L.secondModeOf n x i 0 0 p) * G (K.r₁, p.2)) =
      ∑ s ∈ Finset.univ.filter (fun s => (L.segment s).radial = true ∧ (L.segment s).level = K.r₁),
        ∑ d : Fin (L.degSide + 1), edgeSign (L.segment s).level (L.segment s).other *
          ((L.segment s).level : ℂ) * (starRingEnd ℂ) (cf s d) *
          (L.segment s).moment true (L.gradModeOf n x i 0) (L.secondModeOf n x i 0 0) (L.secondModeOf n x i 0 2) d := by
    by_cases h0 : K.r₁ = 0
    · rw [Finset.sum_eq_zero]
      · rw [hGdef]; simp [h0]
      · intro s hs
        obtain ⟨_, hrad, hlev⟩ := Finset.mem_filter.1 hs
        rcases hL.layout.segment_on_side s with ⟨_, _, _, _, hne⟩ | ⟨hnr, _⟩
        · exact absurd (hlev.trans h0) hne
        · exact absurd hrad hnr
    · have h := radial_side_sum (dFz := L.secondModeOf n x i 0 2) hK hL hW hGc cf (v := K.r₁) (o := K.r₂)
        (Or.inr ⟨rfl, h0⟩) (by ring) (hGv K.r₁ ⟨le_rfl, hr.2.le⟩)
      rw [hrect] at h
      exact h
  rw [h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rcases hL.layout.segment_on_side s with ⟨hrad, hlev, _, _, _⟩ | ⟨hnr, _⟩
  · have hrad' : (L.segment s).radial = true := hrad
    rcases hlev with h | h
    · simp [hrad', h, hr.2.ne]
    · simp [hrad', h, hr.2.ne']
  · have hnr' : (L.segment s).radial = false := by simpa using hnr
    simp [hnr']


theorem height_side {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) (i : Fin 3) (cf : Fin L.segCount → Fin (L.degSide + 1) → ℂ)
    (hcf : ∀ s, ∀ p ∈ K.rect,
      ((L.segment s).radial → p.1 = (L.segment s).level →
          rowModeVec c a n p i = ∑ d, cf s d * ((L.segment s).test d p.2 : ℂ)) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level →
          rowModeVec c a n p i = ∑ d, cf s d * ((L.segment s).test d p.1 : ℂ))) :
    IntegrableOn (fun p : ℝ × ℝ => ((p.1 : ℂ) * L.secondModeOf n x i 2 2 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 2 p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q i) p))) K.rect ∧
    ∫ p in K.rect, ((p.1 : ℂ) * L.secondModeOf n x i 2 2 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 2 p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q i) p)) =
      ∑ s : Fin L.segCount, ∑ d : Fin (L.degSide + 1), (if (L.segment s).radial then 0 else
        edgeSign (L.segment s).level (L.segment s).other * (starRingEnd ℂ) (cf s d) * (L.segment s).moment true (L.gradModeOf n x i 2) (L.secondModeOf n x i 2 0) (L.secondModeOf n x i 2 2) d) := by
  have hK := hD.box
  have hr := hK.r_order
  have hz := hK.z_order
  have hord : L.order = c.order := hL.layout.order_eq
  have hW := modes_height_pair_gradient c x hx L hord n i
  obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n i
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ × ℝ → ℂ, G = fun q => (starRingEnd ℂ) (rowModeVec c a n q i) := ⟨_, rfl⟩
  have hGL : LipschitzOnWith C G K.rect := by
    refine LipschitzOnWith.of_dist_le_mul fun p hp q hq => ?_
    rw [hGdef]
    simp only
    rw [Complex.dist_conj_conj]
    exact hC.dist_le_mul p hp q hq
  have hfun : (fun p : ℝ × ℝ => (p.1 : ℂ) * L.secondModeOf n x i 2 2 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 2 p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q i) p)) =
      fun p => (p.1 : ℂ) * (L.secondModeOf n x i 2 2 p * G p + L.gradModeOf n x i 2 p * CellBox.heightDeriv G p) := by
    funext p
    have e : CellBox.heightDeriv G p = (starRingEnd ℂ) (CellBox.heightDeriv (fun q => rowModeVec c a n q i) p) := by
      rw [hGdef]; exact heightDeriv_conj _ p
    rw [e, hGdef, map_mul, Complex.conj_ofReal]
    ring
  obtain ⟨hI, hE⟩ := height_slope_parts hW hr.1 hz.2 hGL
  rw [hfun]
  refine ⟨hI, ?_⟩
  have hrect : K.rect = Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂ := rfl
  have hGv : ∀ v ∈ Icc K.z₁ K.z₂, ∀ s, (L.segment s).radial = false → (L.segment s).level = v →
      ∀ r ∈ Icc K.r₁ K.r₂,
      G (r, v) = ∑ d : Fin (L.degSide + 1), (starRingEnd ℂ) (cf s d) * ((L.segment s).test d r : ℂ) := by
    intro v hv s hrad hlev r hr'
    have h := (hcf s (r, v) ⟨hr', hv⟩).2 (by simp [hrad]) hlev.symm
    rw [hGdef]
    simp only
    rw [h, map_sum]
    simp [map_mul, Complex.conj_ofReal]
  have hGc : ContinuousOn G K.rect := hGL.continuousOn
  have h2 := height_side_sum (dFr := L.secondModeOf n x i 2 0) hK hL hW hGc cf (v := K.z₂) (o := K.z₁) (Or.inr rfl)
    (by ring) (hGv K.z₂ ⟨hz.2.le, le_rfl⟩)
  have h1 := height_side_sum (dFr := L.secondModeOf n x i 2 0) hK hL hW hGc cf (v := K.z₁) (o := K.z₂) (Or.inl rfl)
    (by ring) (hGv K.z₁ ⟨le_rfl, hz.2.le⟩)
  rw [hrect] at h1 h2
  rw [hrect, hE, h2, h1, Finset.sum_filter, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rcases hL.layout.segment_on_side s with ⟨hrad, _⟩ | ⟨hnr, hlev, _, _⟩
  · have hrad' : (L.segment s).radial = true := hrad
    simp [hrad']
  · have hnr' : (L.segment s).radial = false := by simpa using hnr
    rcases hlev with h | h
    · simp [hnr', h, hz.2.ne]
    · simp [hnr', h, hz.2.ne']


theorem trace_coef {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet) (n : ℤ) (s : Fin L.segCount) (i : Fin 3) (g : ℝ → ℂ)
    (hg : ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = g p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = g p.1))
    (d : ℕ) :
    segmentTrace (L.segment s) (fun p => rowModeVec c a n p i) d =
      ∫ t in Set.Icc (L.segment s).lo (L.segment s).hi, g t * (((L.segment s).test d t : ℝ) : ℂ) := by
  have hbox := hD.box
  have hr := hbox.r_order
  have hz := hbox.z_order
  have hoth := hL.layout.segment_other_in_box s
  unfold segmentTrace FaceSegment.moment
  rcases hL.layout.segment_on_side s with ⟨hrad, hlev, hlo, hhi, _⟩ | ⟨hrad, hlev, hlo, hhi⟩
  · have ho := hoth.1 hrad
    simp only [hrad, if_true]
    obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n i
    have hmm : min (L.segment s).level (L.segment s).other = K.r₁ ∧
        max (L.segment s).level (L.segment s).other = K.r₂ := by
      rw [ho]
      rcases hlev with h | h <;> rw [h] <;> constructor <;> simp [min_def, max_def] <;> intros <;> linarith
    have hsub : Icc (min (L.segment s).level (L.segment s).other)
        (max (L.segment s).level (L.segment s).other) ×ˢ
        Icc (L.segment s).lo (L.segment s).hi ⊆ K.rect := by
      rw [hmm.1, hmm.2]
      exact prod_mono subset_rfl (Icc_subset_Icc hlo hhi)
    have hne : (L.segment s).level ≠ (L.segment s).other := by
      rw [ho]; rcases hlev with h | h <;> rw [h] <;> intro e <;> linarith
    rw [radial_strip_trace hne (hC.mono hsub) (lp_test_cont _ d)]
    refine setIntegral_congr_fun measurableSet_Icc (fun z hz' => ?_)
    have hp : ((L.segment s).level, z) ∈ K.rect := by
      refine ⟨?_, Icc_subset_Icc hlo hhi hz'⟩
      rcases hlev with h | h <;> rw [h] <;> constructor <;> linarith
    rw [(hg _ hp).1 hrad rfl]
  · have ho := hoth.2 hrad
    simp only [hrad, if_false, Bool.false_eq_true]
    obtain ⟨C, hC⟩ := lp_row_slope hD hR ha n i
    have hmm : min (L.segment s).level (L.segment s).other = K.z₁ ∧
        max (L.segment s).level (L.segment s).other = K.z₂ := by
      rw [ho]
      rcases hlev with h | h <;> rw [h] <;> constructor <;> simp [min_def, max_def] <;> intros <;> linarith
    have hsub : Icc (L.segment s).lo (L.segment s).hi ×ˢ
        Icc (min (L.segment s).level (L.segment s).other)
          (max (L.segment s).level (L.segment s).other) ⊆ K.rect := by
      rw [hmm.1, hmm.2]
      exact prod_mono (Icc_subset_Icc hlo hhi) subset_rfl
    have hne : (L.segment s).level ≠ (L.segment s).other := by
      rw [ho]; rcases hlev with h | h <;> rw [h] <;> intro e <;> linarith
    rw [height_strip_trace hne (hC.mono hsub) (lp_test_cont _ d)]
    refine setIntegral_congr_fun measurableSet_Icc (fun r hr' => ?_)
    have hp : (r, (L.segment s).level) ∈ K.rect := by
      refine ⟨Icc_subset_Icc hlo hhi hr', ?_⟩
      rcases hlev with h | h <;> rw [h] <;> constructor <;> linarith
    rw [(hg _ hp).2 hrad rfl]

private theorem test_cont (F : FaceSegment) (d : ℕ) : Continuous (F.test d) := by
  unfold FaceSegment.test
  exact continuous_finsetSum _ (fun i _ => by fun_prop)

theorem coef_of_trace (F : FaceSegment) (m : ℕ)
    (horth : ∀ d d', d < m → d' < m →
      ∫ u in Set.Icc F.lo F.hi, F.test d u * F.test d' u = if d = d' then 1 else 0)
    (cf : Fin m → ℂ) (d : Fin m) :
    ∫ t in Set.Icc F.lo F.hi, (∑ d', cf d' * ((F.test d' t : ℝ) : ℂ)) * ((F.test d t : ℝ) : ℂ) = cf d := by
  have hI : ∀ d' : Fin m, IntegrableOn (fun t => cf d' * (((F.test d' t * F.test d t : ℝ)) : ℂ))
      (Set.Icc F.lo F.hi) volume := fun d' =>
    ContinuousOn.integrableOn_compact isCompact_Icc
      (continuous_const.mul (Complex.continuous_ofReal.comp ((test_cont F d').mul (test_cont F d)))).continuousOn
  have hsplit : (fun t => (∑ d', cf d' * ((F.test d' t : ℝ) : ℂ)) * ((F.test d t : ℝ) : ℂ)) =
      fun t => ∑ d', cf d' * (((F.test d' t * F.test d t : ℝ)) : ℂ) := by
    funext t
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun d' _ => ?_)
    push_cast
    ring
  rw [hsplit, integral_finsetSum _ (fun d' _ => hI d')]
  have hterm : ∀ d' : Fin m, ∫ t in Set.Icc F.lo F.hi, cf d' * (((F.test d' t * F.test d t : ℝ)) : ℂ) =
      if d' = d then cf d else 0 := by
    intro d'
    rw [integral_const_mul, integral_complex_ofReal, horth d' d d'.isLt d.isLt]
    by_cases h : d' = d
    · subst h; simp
    · have h' : (d' : ℕ) ≠ d := fun e => h (Fin.ext e)
      simp [h, h']
  simp_rw [hterm]
  simp

theorem mode_parts_identity {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hseg : ∀ a ∈ R.rowSet, ∀ s n i, ∃ P : ℝ → ℂ, (∃ cf : Fin (L.degSide + 1) → ℂ, ∀ t, P t = ∑ d, cf d * ((L.segment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.segment s).radial → p.1 = (L.segment s).level → rowModeVec c a n p i = P p.2) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level → rowModeVec c a n p i = P p.1))
    (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) *
        pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')) K.rect ∧
    -((c.splitVisc : ℂ) * ∫ p in K.rect, (p.1 : ℂ) *
        pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)) =
      (c.splitVisc : ℂ) * (∫ p in K.rect, (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3,
        gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')) +
      ∑ s : Fin L.segCount, ∑ a' : Fin 3, ∑ d : Fin (L.degSide + 1), gradSideRowCoef c L a n s a' d *
        (if (L.segment s).radial then
          (L.segment s).moment true (L.gradModeOf n x a' 0) (L.secondModeOf n x a' 0 0) (L.secondModeOf n x a' 0 2) d
        else (L.segment s).moment true (L.gradModeOf n x a' 2) (L.secondModeOf n x a' 2 0) (L.secondModeOf n x a' 2 2) d) := by
  choose P hPcf hPtr using fun s (i : Fin 3) => hseg a ha s n i
  choose cf hcf using hPcf
  have htr : ∀ i : Fin 3, ∀ s, ∀ p ∈ K.rect,
      ((L.segment s).radial → p.1 = (L.segment s).level →
          rowModeVec c a n p i = ∑ d, cf s i d * ((L.segment s).test d p.2 : ℂ)) ∧
        (¬ (L.segment s).radial → p.2 = (L.segment s).level →
          rowModeVec c a n p i = ∑ d, cf s i d * ((L.segment s).test d p.1 : ℂ)) := by
    intro i s p hp
    refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩
    · rw [(hPtr s i p hp).1 h1 h2, hcf s i]
    · rw [(hPtr s i p hp).2 h1 h2, hcf s i]
  have hcoef : ∀ s i (d : Fin (L.degSide + 1)), gradSideRowCoef c L a n s i d =
      -(c.splitVisc : ℂ) * edgeSign (L.segment s).level (L.segment s).other *
        (if (L.segment s).radial then ((L.segment s).level : ℂ) else 1) * (starRingEnd ℂ) (cf s i d) := by
    intro s i d
    unfold gradSideRowCoef
    rw [trace_coef hα1 hα2 hc hD hR hL hx ha n s i (P s i) (hPtr s i) d]
    have hP : P s i = fun t => ∑ d', cf s i d' * (((L.segment s).test d' t : ℝ) : ℂ) := funext (hcf s i)
    rw [hP, coef_of_trace (L.segment s) (L.degSide + 1)
      (fun d d' hd hd' => hL.layout.segment_orthonormal s d d' (by omega) (by omega)) (cf s i) d]
  obtain ⟨hI0, hI1⟩ := volume_integrable hα1 hα2 hc hD hR hL hx ha n
  have hrad := fun i => radial_side hα1 hα2 hc hD hR hL hx ha n i (fun s => cf s i) (htr i)
  have hht := fun i => height_side hα1 hα2 hc hD hR hL hx ha n i (fun s => cf s i) (htr i)
  have hpt := pointwise_split hα1 hα2 hc hD hR hL hx ha n
  refine ⟨hI0, hI1, ?_⟩
  have hsum : (∫ p in K.rect, (p.1 : ℂ) * pairC (modeVec c.order n (fun y => secondTrace (x.2.2.1 y)) p.1 p.2) (rowModeVec c a n p)) + (∫ p in K.rect, (p.1 : ℂ) * ∑ a' : Fin 3, ∑ b' : Fin 3, gradMode c.order n x.2.1 a' b' p * (starRingEnd ℂ) (rowModeGrad c a n p a' b')) =
      ∑ i : Fin 3, ((∑ s : Fin L.segCount, ∑ d : Fin (L.degSide + 1), (if (L.segment s).radial then
        edgeSign (L.segment s).level (L.segment s).other * ((L.segment s).level : ℂ) * (starRingEnd ℂ) (cf s i d) *
          (L.segment s).moment true (L.gradModeOf n x i 0) (L.secondModeOf n x i 0 0) (L.secondModeOf n x i 0 2) d else 0)) +
        ∑ s : Fin L.segCount, ∑ d : Fin (L.degSide + 1), (if (L.segment s).radial then 0 else
        edgeSign (L.segment s).level (L.segment s).other * (starRingEnd ℂ) (cf s i d) * (L.segment s).moment true (L.gradModeOf n x i 2) (L.secondModeOf n x i 2 0) (L.secondModeOf n x i 2 2) d)) := by
    have hi : ∀ i ∈ (Finset.univ : Finset (Fin 3)), Integrable (fun p : ℝ × ℝ => ((p.1 : ℂ) * L.secondModeOf n x i 0 0 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 0 p * (starRingEnd ℂ) (CellBox.radialDeriv (fun q => (q.1 : ℂ) * rowModeVec c a n q i) p)) + ((p.1 : ℂ) * L.secondModeOf n x i 2 2 p * (starRingEnd ℂ) (rowModeVec c a n p i) +
        L.gradModeOf n x i 2 p * (starRingEnd ℂ) ((p.1 : ℂ) * CellBox.heightDeriv (fun q => rowModeVec c a n q i) p)))
        (volume.restrict K.rect) := fun i _ => (hrad i).1.add (hht i).1
    rw [← integral_add hI0 hI1, integral_congr_ae hpt, integral_finsetSum _ hi]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_add (hrad i).1 (hht i).1, (hrad i).2, (hht i).2]
  simp_rw [hcoef]
  have hB : ∑ s : Fin L.segCount, ∑ i : Fin 3, ∑ d : Fin (L.degSide + 1),
      -(c.splitVisc : ℂ) * edgeSign (L.segment s).level (L.segment s).other *
        (if (L.segment s).radial then ((L.segment s).level : ℂ) else 1) * (starRingEnd ℂ) (cf s i d) *
        (if (L.segment s).radial then (L.segment s).moment true (L.gradModeOf n x i 0) (L.secondModeOf n x i 0 0) (L.secondModeOf n x i 0 2) d else (L.segment s).moment true (L.gradModeOf n x i 2) (L.secondModeOf n x i 2 0) (L.secondModeOf n x i 2 2) d) =
      -(c.splitVisc : ℂ) * ∑ i : Fin 3, ((∑ s : Fin L.segCount, ∑ d : Fin (L.degSide + 1), (if (L.segment s).radial then
        edgeSign (L.segment s).level (L.segment s).other * ((L.segment s).level : ℂ) * (starRingEnd ℂ) (cf s i d) *
          (L.segment s).moment true (L.gradModeOf n x i 0) (L.secondModeOf n x i 0 0) (L.secondModeOf n x i 0 2) d else 0)) +
        ∑ s : Fin L.segCount, ∑ d : Fin (L.degSide + 1), (if (L.segment s).radial then 0 else
        edgeSign (L.segment s).level (L.segment s).other * (starRingEnd ℂ) (cf s i d) * (L.segment s).moment true (L.gradModeOf n x i 2) (L.secondModeOf n x i 2 0) (L.secondModeOf n x i 2 2) d)) := by
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    split_ifs <;> ring
  rw [hB, ← hsum]
  ring

theorem trace_of_zero {k N : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars} {B : CellBases}
    {L : CellLayout} (hK : IsCellBox K) (hL : IsCellLayout c K S B L) {f : ℝ × ℝ → ℂ}
    (hf : ∀ p ∈ K.rect, f p = 0) (s : Fin L.segCount) (d : ℕ) :
    segmentTrace (L.segment s) f d = 0 := by
  have hr := hK.r_order
  have hz := hK.z_order
  have hoth := hL.segment_other_in_box s
  have hIoo : ∀ p : ℝ × ℝ, p.1 ∈ Ioo K.r₁ K.r₂ → p.2 ∈ Ioo K.z₁ K.z₂ →
      f p = 0 ∧ CellBox.radialDeriv f p = 0 ∧ CellBox.heightDeriv f p = 0 := by
    intro p h1 h2
    refine ⟨hf p ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self h2⟩, ?_, ?_⟩
    · unfold CellBox.radialDeriv
      have hev : (fun r : ℝ => f (r, p.2)) =ᶠ[nhds p.1] fun _ => (0 : ℂ) := by
        filter_upwards [Ioo_mem_nhds h1.1 h1.2] with r hr'
        exact hf _ ⟨Ioo_subset_Icc_self hr', Ioo_subset_Icc_self h2⟩
      rw [hev.deriv_eq]
      simp
    · unfold CellBox.heightDeriv
      have hev : (fun z : ℝ => f (p.1, z)) =ᶠ[nhds p.2] fun _ => (0 : ℂ) := by
        filter_upwards [Ioo_mem_nhds h2.1 h2.2] with z hz'
        exact hf _ ⟨Ioo_subset_Icc_self h1, Ioo_subset_Icc_self hz'⟩
      rw [hev.deriv_eq]
      simp
  have hnull : ∀ a b c' d' : ℝ, (Ioo a b ×ˢ Ioo c' d' : Set (ℝ × ℝ)) =ᵐ[volume] Icc a b ×ˢ Icc c' d' := by
    intro a b c' d'
    rw [Measure.volume_eq_prod]
    exact Measure.set_prod_ae_eq Ioo_ae_eq_Icc Ioo_ae_eq_Icc
  unfold segmentTrace FaceSegment.moment
  rcases hL.segment_on_side s with ⟨hrad, hlev, hlo, hhi, _⟩ | ⟨hrad, hlev, hlo, hhi⟩
  · have ho := hoth.1 hrad
    have hmm : min (L.segment s).level (L.segment s).other = K.r₁ ∧
        max (L.segment s).level (L.segment s).other = K.r₂ := by
      rw [ho]
      rcases hlev with h | h <;> rw [h] <;> constructor <;> simp [min_def, max_def] <;> intros <;> linarith
    simp only [hrad, if_true, radialStripMoment, hmm.1, hmm.2]
    rw [← setIntegral_congr_set (hnull _ _ _ _), setIntegral_eq_zero_of_forall_eq_zero (fun p hp => ?_), mul_zero]
    obtain ⟨h0, h1, _⟩ := hIoo p hp.1 ⟨lt_of_le_of_lt hlo hp.2.1, lt_of_lt_of_le hp.2.2 hhi⟩
    rw [h0, h1]
    simp
  · have ho := hoth.2 hrad
    have hmm : min (L.segment s).level (L.segment s).other = K.z₁ ∧
        max (L.segment s).level (L.segment s).other = K.z₂ := by
      rw [ho]
      rcases hlev with h | h <;> rw [h] <;> constructor <;> simp [min_def, max_def] <;> intros <;> linarith
    simp only [hrad, Bool.false_eq_true, if_false, heightStripMoment, hmm.1, hmm.2]
    rw [← setIntegral_congr_set (hnull _ _ _ _), setIntegral_eq_zero_of_forall_eq_zero (fun p hp => ?_), mul_zero]
    obtain ⟨h0, _, h2⟩ := hIoo p ⟨lt_of_le_of_lt hlo hp.1.1, lt_of_lt_of_le hp.1.2 hhi⟩ hp.2
    rw [h0, h2]
    simp

end Breakdown.FracInternal.LayoutRowViscousSides
