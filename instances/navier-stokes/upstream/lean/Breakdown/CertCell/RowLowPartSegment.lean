import Breakdown.CertCell.RowLowPartLift
import Breakdown.FracCell.LayoutRowPressureBoundaryParts

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

def radialIntegrand (c o : ℝ) (F dF : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * dF p

def heightIntegrand (c o : ℝ) (F dF : ℝ × ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * dF p

theorem radialStripMoment_eq (c o lo hi : ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    radialStripMoment c o lo hi F dF t =
      edgeSign c o * ∫ p in Icc (min c o) (max c o) ×ˢ Icc lo hi, radialIntegrand c o F dF p * (t p.2 : ℂ) := rfl

theorem heightStripMoment_eq (c o lo hi : ℝ) (wt : ℝ → ℝ) (F dF : ℝ × ℝ → ℂ) (t : ℝ → ℝ) :
    heightStripMoment c o lo hi wt F dF t =
      edgeSign c o * ∫ p in Icc lo hi ×ˢ Icc (min c o) (max c o),
        heightIntegrand c o F dF p * ((wt p.1 * t p.1 : ℝ) : ℂ) := rfl

theorem edgeSign_sq (c o : ℝ) : edgeSign c o * edgeSign c o = 1 := by
  unfold edgeSign
  split_ifs <;> norm_num

theorem grad_seg_radial (hexp : SegmentTestExpansionStatement) {S : FaceSegment} (hS : IsFaceSegment S)
    (hrad : S.radial = true) {M N : ℕ}
    (horth : ∀ d d', d < N → d' < N → ∫ u in Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    {φa : ℝ × ℝ → ℂ} (hφa : IsBivariatePoly M N φa) {F dF dF' : ℝ × ℝ → ℂ}
    (hint : IntegrableOn (radialIntegrand S.level S.other F dF)
      (Icc (min S.level S.other) (max S.level S.other) ×ˢ Icc S.lo S.hi)) :
    ∑ d ∈ Finset.range N, (starRingEnd ℂ) (sideTestMoment S φa d) * S.moment true F dF dF' d
      = edgeSign S.level S.other * ∫ p in Icc (min S.level S.other) (max S.level S.other) ×ˢ Icc S.lo S.hi,
          radialIntegrand S.level S.other F dF p * (starRingEnd ℂ) (φa (S.level, p.2)) := by
  have hco : S.level ≠ S.other := fun h => hS.other_ne h.symm
  have hst : ∀ d, sideTestMoment S φa d = ∫ w in Icc S.lo S.hi, φa (S.level, w) * (S.test d w : ℂ) := by
    intro d
    unfold sideTestMoment FaceSegment.moment
    rw [if_pos hrad]
    exact radialStrip_of_smooth (bi_contDiff hφa) hco (test_cont S d)
  have hmo : ∀ d, S.moment true F dF dF' d = edgeSign S.level S.other *
      ∫ p in Icc (min S.level S.other) (max S.level S.other) ×ˢ Icc S.lo S.hi,
        radialIntegrand S.level S.other F dF p * (S.test d p.2 : ℂ) := by
    intro d
    unfold FaceSegment.moment
    rw [if_pos hrad]
    rfl
  simp_rw [hst, hmo]
  rw [← seg_expand_snd hexp hS.test_leading horth (bi_slice_snd hφa S.level) hint, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

theorem grad_seg_height (hexp : SegmentTestExpansionStatement) {S : FaceSegment} (hS : IsFaceSegment S)
    (hrad : S.radial = false) {M N : ℕ}
    (horth : ∀ d d', d < M → d' < M → ∫ u in Icc S.lo S.hi, S.test d u * S.test d' u = if d = d' then 1 else 0)
    {φa : ℝ × ℝ → ℂ} (hφa : IsBivariatePoly M N φa) {F dF dF' : ℝ × ℝ → ℂ}
    (hint : IntegrableOn (fun p => heightIntegrand S.level S.other F dF p * (p.1 : ℂ))
      (Icc S.lo S.hi ×ˢ Icc (min S.level S.other) (max S.level S.other))) :
    ∑ d ∈ Finset.range M, (starRingEnd ℂ) (sideTestMoment S φa d) * S.moment true F dF' dF d
      = edgeSign S.level S.other * ∫ p in Icc S.lo S.hi ×ˢ Icc (min S.level S.other) (max S.level S.other),
          heightIntegrand S.level S.other F dF p * (p.1 : ℂ) * (starRingEnd ℂ) (φa (p.1, S.level)) := by
  have hco : S.level ≠ S.other := fun h => hS.other_ne h.symm
  have hst : ∀ d, sideTestMoment S φa d = ∫ w in Icc S.lo S.hi, φa (w, S.level) * (S.test d w : ℂ) := by
    intro d
    unfold sideTestMoment FaceSegment.moment
    rw [if_neg (by simp [hrad])]
    have hw : (fun r : ℝ => if false = true then r else 1) = fun _ => 1 := by funext r; simp
    rw [hw, heightStrip_of_smooth (bi_contDiff hφa) hco continuous_const (test_cont S d)]
    refine setIntegral_congr_fun measurableSet_Icc (fun w _ => ?_)
    simp
  have hmo : ∀ d, S.moment true F dF' dF d = edgeSign S.level S.other *
      ∫ p in Icc S.lo S.hi ×ˢ Icc (min S.level S.other) (max S.level S.other),
        heightIntegrand S.level S.other F dF p * (p.1 : ℂ) * (S.test d p.1 : ℂ) := by
    intro d
    unfold FaceSegment.moment
    rw [if_neg (by simp [hrad]), heightStripMoment_eq]
    congr 1
    refine setIntegral_congr_fun (measurableSet_Icc.prod measurableSet_Icc) (fun p _ => ?_)
    simp only [if_true]
    push_cast
    ring
  simp_rw [hst, hmo]
  rw [← seg_expand_fst hexp hS.test_leading horth (bi_slice_fst hφa S.level) hint, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  ring

theorem int_div_fst {K : CellBox} (hK : IsCellBox K) (h0 : 0 < K.r₁) {f : ℝ × ℝ → ℂ}
    (hf : IntegrableOn (fun p => (p.1 : ℂ) * f p) K.rect) : IntegrableOn f K.rect := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => ((1 / p.1 : ℝ) : ℂ)) K.rect := by
    refine Complex.continuous_ofReal.comp_continuousOn ?_
    refine continuousOn_const.div continuous_fst.continuousOn (fun p hp => ?_)
    exact (lt_of_lt_of_le h0 hp.1.1).ne'
  refine (hf.mul_continuousOn hc (rect_compact K)).congr_fun (fun p hp => ?_) (rect_meas K)
  have : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (lt_of_lt_of_le h0 hp.1.1).ne'
  push_cast
  field_simp

theorem radialIntegrand_int {K : CellBox} (hK : IsCellBox K) {c o : ℝ} (ho : o = 0 ∨ 0 < K.r₁)
    {F dF : ℝ × ℝ → ℂ} (hF : IntegrableOn F K.rect) (hdF : IntegrableOn (fun p => (p.1 : ℂ) * dF p) K.rect) :
    IntegrableOn (radialIntegrand c o F dF) K.rect := by
  unfold radialIntegrand
  refine (hF.const_mul _).add ?_
  rcases ho with ho | ho
  · subst ho
    refine IntegrableOn.congr_fun (Integrable.const_mul hdF (((1 / c : ℝ)) : ℂ)) (fun p _ => ?_) (rect_meas K)
    push_cast
    ring
  · have hc : ContinuousOn (fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ)) K.rect :=
      (Complex.continuous_ofReal.comp ((continuous_fst.sub continuous_const).div_const _)).continuousOn
    exact ((int_div_fst hK ho hdF).continuousOn_mul hc (rect_compact K))

theorem heightIntegrand_w_int {K : CellBox} {c o : ℝ} {F dF : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (p.1 : ℂ) * F p) K.rect) (hdF : IntegrableOn (fun p => (p.1 : ℂ) * dF p) K.rect) :
    IntegrableOn (fun p => heightIntegrand c o F dF p * (p.1 : ℂ)) K.rect := by
  have hc : ContinuousOn (fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ)) K.rect :=
    (Complex.continuous_ofReal.comp ((continuous_snd.sub continuous_const).div_const _)).continuousOn
  refine IntegrableOn.congr_fun (Integrable.add (Integrable.const_mul hF (((1 / (c - o) : ℝ)) : ℂ))
    (hdF.continuousOn_mul hc (rect_compact K))) (fun p _ => ?_) (rect_meas K)
  unfold heightIntegrand
  simp only [Pi.add_apply]
  ring

theorem trace_radial {K : CellBox} {c o : ℝ} (hmin : min c o = K.r₁) (hmax : max c o = K.r₂)
    {F dF : ℝ × ℝ → ℂ} (hint : IntegrableOn (radialIntegrand c o F dF) K.rect) {w : ℝ → ℂ} (hw : Continuous w) :
    IntegrableOn (fun z => radialStripTrace c o F dF z * w z) (Icc K.z₁ K.z₂) ∧
    ∫ z in Icc K.z₁ K.z₂, radialStripTrace c o F dF z * w z =
      edgeSign c o * ∫ p in K.rect, radialIntegrand c o F dF p * w p.2 := by
  have hf : IntegrableOn (fun p : ℝ × ℝ => radialIntegrand c o F dF p * w p.2) K.rect :=
    hint.mul_continuousOn (hw.comp continuous_snd).continuousOn (rect_compact K)
  have htr : ∀ z, radialStripTrace c o F dF z * w z =
      edgeSign c o * ∫ r in Icc K.r₁ K.r₂, radialIntegrand c o F dF (r, z) * w (r, z).2 := by
    intro z
    unfold radialStripTrace
    rw [hmin, hmax, mul_assoc, ← integral_mul_const]
    rfl
  have hf' := hf
  rw [IntegrableOn, CellBox.rect, rect_restrict] at hf'
  refine ⟨?_, ?_⟩
  · simp_rw [htr]
    exact (hf'.integral_prod_right).const_mul _
  · simp_rw [htr]
    rw [integral_const_mul, CellBox.rect, rect_iter_snd hf]

theorem trace_height {K : CellBox} {c o : ℝ} (hmin : min c o = K.z₁) (hmax : max c o = K.z₂)
    {F dF : ℝ × ℝ → ℂ} (hint : IntegrableOn (fun p => heightIntegrand c o F dF p * (p.1 : ℂ)) K.rect)
    {w : ℝ → ℂ} (hw : Continuous w) :
    IntegrableOn (fun r : ℝ => (r : ℂ) * heightStripTrace c o F dF r * w r) (Icc K.r₁ K.r₂) ∧
    ∫ r : ℝ in Icc K.r₁ K.r₂, (r : ℂ) * heightStripTrace c o F dF r * w r =
      edgeSign c o * ∫ p in K.rect, heightIntegrand c o F dF p * (p.1 : ℂ) * w p.1 := by
  have hf : IntegrableOn (fun p : ℝ × ℝ => heightIntegrand c o F dF p * (p.1 : ℂ) * w p.1) K.rect :=
    hint.mul_continuousOn (hw.comp continuous_fst).continuousOn (rect_compact K)
  have htr : ∀ r : ℝ, (r : ℂ) * heightStripTrace c o F dF r * w r =
      edgeSign c o * ∫ z in Icc K.z₁ K.z₂, heightIntegrand c o F dF (r, z) * ((r, z).1 : ℂ) * w (r, z).1 := by
    intro r
    unfold heightStripTrace
    rw [hmin, hmax]
    have : ∫ z in Icc K.z₁ K.z₂, heightIntegrand c o F dF (r, z) * ((r, z).1 : ℂ) * w (r, z).1 =
        (∫ z in Icc K.z₁ K.z₂, heightIntegrand c o F dF (r, z)) * ((r : ℂ) * w r) := by
      rw [← integral_mul_const]
      refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
      simp only
      ring
    rw [this]
    unfold heightIntegrand
    ring
  have hf' := hf
  rw [IntegrableOn, CellBox.rect, rect_restrict] at hf'
  refine ⟨?_, ?_⟩
  · simp_rw [htr]
    exact (hf'.integral_prod_left).const_mul _
  · simp_rw [htr]
    rw [integral_const_mul, CellBox.rect, rect_iter_fst hf]

def segSide (K : CellBox) (S : FaceSegment) : Fin 4 :=
  if S.radial then (if S.level = K.r₁ then 0 else 1) else (if S.level = K.z₁ then 2 else 3)

section Layout

variable {k N' : ℕ} {c0 : FracCellData k N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

theorem segSide_of_mem (hL : IsCellLayout c0 K S0 B L) {e : Fin 4} {s : Fin L.segCount}
    (hs : s ∈ L.sideSegments e) : segSide K (L.segment s) = e := by
  have hspec := hL.sideSegments_spec e s hs
  have hr := hL.box_valid.r_order.2
  have hz := hL.box_valid.z_order.2
  unfold segSide
  fin_cases e
  · simp at hspec
    simp [hspec]
  · simp at hspec
    simp [hspec, hr.ne']
  · simp at hspec
    simp [hspec]
  · simp at hspec
    simp [hspec, hz.ne']

theorem segSide_fiber (hL : IsCellLayout c0 K S0 B L) (e : Fin 4) :
    Finset.univ.filter (fun s => segSide K (L.segment s) = e) = L.sideSegments e := by
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    obtain ⟨e', he'⟩ := hL.segments_on_sides s
    rw [segSide_of_mem hL he'] at h
    rw [← h]
    exact he'
  · exact segSide_of_mem hL

theorem seg_radial_facts (hL : IsCellLayout c0 K S0 B L) {e : Fin 4} (he : e.val < 2) {s : Fin L.segCount}
    (hs : s ∈ L.sideSegments e) :
    (L.segment s).radial = true ∧ (L.segment s).level = (if e.val = 0 then K.r₁ else K.r₂) ∧
      (L.segment s).other = K.r₁ + K.r₂ - (L.segment s).level ∧
      K.z₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.z₂ ∧ (L.segment s).level ≠ 0 := by
  have hspec := hL.sideSegments_spec e s hs
  have hrad : (L.segment s).radial = true := hspec.1.2 he
  refine ⟨hrad, ?_, (hL.segment_other_in_box s).1 hrad, ?_⟩
  · rw [hspec.2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rcases hL.segment_on_side s with ⟨_, _, h1, h2, h3⟩ | ⟨h, _⟩
    · exact ⟨h1, h2, h3⟩
    · exact absurd hrad h

theorem seg_height_facts (hL : IsCellLayout c0 K S0 B L) {e : Fin 4} (he : 2 ≤ e.val) {s : Fin L.segCount}
    (hs : s ∈ L.sideSegments e) :
    (L.segment s).radial = false ∧ (L.segment s).level = (if e.val = 2 then K.z₁ else K.z₂) ∧
      (L.segment s).other = K.z₁ + K.z₂ - (L.segment s).level ∧
      K.r₁ ≤ (L.segment s).lo ∧ (L.segment s).hi ≤ K.r₂ := by
  have hspec := hL.sideSegments_spec e s hs
  have hrad : (L.segment s).radial = false := by
    have := hspec.1
    cases h : (L.segment s).radial
    · rfl
    · rw [h] at this; have := this.1 rfl; omega
  refine ⟨hrad, ?_, (hL.segment_other_in_box s).2 (by simp [hrad]), ?_⟩
  · rw [hspec.2]
    split_ifs <;> first | rfl | (exfalso; omega)
  · rcases hL.segment_on_side s with ⟨h, _⟩ | ⟨_, _, h1, h2⟩
    · rw [hrad] at h; exact absurd h (by decide)
    · exact ⟨h1, h2⟩

end Layout

section Layout

variable {k N' : ℕ} {c0 : FracCellData k N'} {K : CellBox} {S0 : CellScalars} {B : CellBases} {L : CellLayout}

theorem minmax_of {x y c : ℝ} (hxy : x < y) (hc : c = x ∨ c = y) :
    min c (x + y - c) = x ∧ max c (x + y - c) = y := by
  rcases hc with rfl | rfl
  · have : c + y - c = y := by ring
    rw [this]; exact ⟨min_eq_left hxy.le, max_eq_right hxy.le⟩
  · have : x + c - c = x := by ring
    rw [this]; exact ⟨min_eq_right hxy.le, max_eq_left hxy.le⟩

theorem grad_radial_side (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L) {e : Fin 4}
    (he : e.val < 2) {c : ℝ} (hc : c = if e.val = 0 then K.r₁ else K.r₂) (φ : Fin 3 → CellPoly)
    (hφ : ∀ a, IsBivariatePoly (L.degSide + 1) (L.degSide + 1) (fun p => (φ a).eval K p))
    (F dF X : Fin 3 → ℝ × ℝ → ℂ)
    (hint : c ≠ 0 → ∀ a, IntegrableOn (radialIntegrand c (K.r₁ + K.r₂ - c) (F a) (dF a)) K.rect) :
    ∑ s ∈ L.sideSegments e, ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1),
        sideGradRow L φ s a d * (L.segment s).moment true (F a) (dF a) (X a) d
      = -(c : ℂ) * ∑ a : Fin 3, ∫ p in K.rect,
          radialIntegrand c (K.r₁ + K.r₂ - c) (F a) (dF a) p * (starRingEnd ℂ) ((φ a).eval K (c, p.2)) := by
  have hr := hL.box_valid.r_order.2
  by_cases hc0 : c = 0
  · rw [Finset.sum_eq_zero, hc0]
    · simp
    · intro s hs
      obtain ⟨_, hlev, _, _, _, hne⟩ := seg_radial_facts hL he hs
      rw [← hc, hc0] at hlev
      exact absurd hlev hne
  have hcx : c = K.r₁ ∨ c = K.r₂ := by rw [hc]; split_ifs <;> simp
  obtain ⟨hmin, hmax⟩ := minmax_of hr hcx
  have hper : ∀ s ∈ L.sideSegments e, ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1),
      sideGradRow L φ s a d * (L.segment s).moment true (F a) (dF a) (X a) d
      = -(c : ℂ) * ∑ a : Fin 3, ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi,
          radialIntegrand c (K.r₁ + K.r₂ - c) (F a) (dF a) p * (starRingEnd ℂ) ((φ a).eval K (c, p.2)) := by
    intro s hs
    obtain ⟨hrad, hlev, hoth, hlo, hhi, _⟩ := seg_radial_facts hL he hs
    rw [← hc] at hlev
    rw [hlev] at hoth
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hseg := grad_seg_radial (M := L.degSide + 1) (N := L.degSide + 1) hexp (hL.segment_valid s) hrad
      (fun d d' hd hd' => hL.segment_orthonormal s d d' (by omega) (by omega)) (hφ a)
      (F := F a) (dF := dF a) (dF' := X a) (by
        rw [hlev, hoth, hmin, hmax]
        exact (hint hc0 a).mono_set (prod_mono subset_rfl (Icc_subset_Icc hlo hhi)))
    rw [hlev, hoth, hmin, hmax] at hseg
    unfold sideGradRow
    simp only [hrad, if_true, hlev, hoth, hL.box_eq]
    rw [Fin.sum_univ_eq_sum_range (fun d => -edgeSign c (K.r₁ + K.r₂ - c) * (c : ℂ) *
        (starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval K p) d) *
          (L.segment s).moment true (F a) (dF a) (X a) d) (L.degSide + 1)]
    have : ∀ d ∈ Finset.range (L.degSide + 1), -edgeSign c (K.r₁ + K.r₂ - c) * (c : ℂ) *
        (starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval K p) d) *
          (L.segment s).moment true (F a) (dF a) (X a) d =
        (-edgeSign c (K.r₁ + K.r₂ - c) * (c : ℂ)) *
          ((starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval K p) d) *
          (L.segment s).moment true (F a) (dF a) (X a) d) := fun d _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hseg]
    have h2 := edgeSign_sq c (K.r₁ + K.r₂ - c)
    linear_combination (-(c : ℂ) * ∫ p in Icc K.r₁ K.r₂ ×ˢ Icc (L.segment s).lo (L.segment s).hi,
          radialIntegrand c (K.r₁ + K.r₂ - c) (F a) (dF a) p * (starRingEnd ℂ) ((φ a).eval K (c, p.2))) * h2
  rw [Finset.sum_congr rfl hper, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hf : IntegrableOn (fun p => radialIntegrand c (K.r₁ + K.r₂ - c) (F a) (dF a) p *
      (starRingEnd ℂ) ((φ a).eval K (c, p.2))) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    (hint hc0 a).mul_continuousOn
      ((Complex.continuous_conj.comp ((bi_contDiff (hφ a)).continuous.comp
        (continuous_const.prodMk continuous_snd))).continuousOn) (rect_compact K)
  symm
  refine Breakdown.FracInternal.LayoutRowPressureBoundaryParts.strip_partition (L.sideSegments e)
    (fun s => (L.segment s).lo) (fun s => (L.segment s).hi) ?_ ?_ ?_ measurableSet_Icc hf
  · intro u hu
    have h0 : e.val = 0 → K.r₁ ≠ 0 := by
      intro h0 h1; apply hc0; rw [hc, if_pos h0, h1]
    obtain ⟨s, hs, h1, h2⟩ := hL.sideSegments_cover e h0 u (by rw [if_pos he]; exact hu)
    exact ⟨s, hs, h1, h2⟩
  · intro s hs
    obtain ⟨_, _, _, hlo, hhi, _⟩ := seg_radial_facts hL he hs
    exact ⟨hlo, hhi⟩
  · exact hL.sideSegments_disjoint e

theorem grad_height_side (hexp : SegmentTestExpansionStatement) (hL : IsCellLayout c0 K S0 B L) {e : Fin 4}
    (he : 2 ≤ e.val) {c : ℝ} (hc : c = if e.val = 2 then K.z₁ else K.z₂) (φ : Fin 3 → CellPoly)
    (hφ : ∀ a, IsBivariatePoly (L.degSide + 1) (L.degSide + 1) (fun p => (φ a).eval K p))
    (F dF Y : Fin 3 → ℝ × ℝ → ℂ)
    (hint : ∀ a, IntegrableOn (fun p => heightIntegrand c (K.z₁ + K.z₂ - c) (F a) (dF a) p * (p.1 : ℂ)) K.rect) :
    ∑ s ∈ L.sideSegments e, ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1),
        sideGradRow L φ s a d * (L.segment s).moment true (F a) (Y a) (dF a) d
      = -∑ a : Fin 3, ∫ p in K.rect,
          heightIntegrand c (K.z₁ + K.z₂ - c) (F a) (dF a) p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ a).eval K (p.1, c)) := by
  have hz := hL.box_valid.z_order.2
  have hcx : c = K.z₁ ∨ c = K.z₂ := by rw [hc]; split_ifs <;> simp
  obtain ⟨hmin, hmax⟩ := minmax_of hz hcx
  have hper : ∀ s ∈ L.sideSegments e, ∑ a : Fin 3, ∑ d : Fin (L.degSide + 1),
      sideGradRow L φ s a d * (L.segment s).moment true (F a) (Y a) (dF a) d
      = -∑ a : Fin 3, ∫ p in Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂,
          heightIntegrand c (K.z₁ + K.z₂ - c) (F a) (dF a) p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ a).eval K (p.1, c)) := by
    intro s hs
    obtain ⟨hrad, hlev, hoth, hlo, hhi⟩ := seg_height_facts hL he hs
    rw [← hc] at hlev
    rw [hlev] at hoth
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hseg := grad_seg_height (M := L.degSide + 1) (N := L.degSide + 1) hexp (hL.segment_valid s) hrad
      (fun d d' hd hd' => hL.segment_orthonormal s d d' (by omega) (by omega)) (hφ a)
      (F := F a) (dF := dF a) (dF' := Y a) (by
        rw [hlev, hoth, hmin, hmax]
        exact (hint a).mono_set (prod_mono (Icc_subset_Icc hlo hhi) subset_rfl))
    rw [hlev, hoth, hmin, hmax] at hseg
    unfold sideGradRow
    simp only [hrad, Bool.false_eq_true, if_false, hlev, hoth, hL.box_eq, mul_one]
    rw [Fin.sum_univ_eq_sum_range (fun d => -edgeSign c (K.z₁ + K.z₂ - c) *
        (starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval K p) d) *
          (L.segment s).moment true (F a) (Y a) (dF a) d) (L.degSide + 1)]
    have : ∀ d ∈ Finset.range (L.degSide + 1), -edgeSign c (K.z₁ + K.z₂ - c) *
        (starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval K p) d) *
          (L.segment s).moment true (F a) (Y a) (dF a) d =
        (-edgeSign c (K.z₁ + K.z₂ - c)) *
          ((starRingEnd ℂ) (sideTestMoment (L.segment s) (fun p => (φ a).eval K p) d) *
          (L.segment s).moment true (F a) (Y a) (dF a) d) := fun d _ => by ring
    rw [Finset.sum_congr rfl this, ← Finset.mul_sum, hseg]
    have h2 := edgeSign_sq c (K.z₁ + K.z₂ - c)
    linear_combination (-∫ p in Icc (L.segment s).lo (L.segment s).hi ×ˢ Icc K.z₁ K.z₂,
          heightIntegrand c (K.z₁ + K.z₂ - c) (F a) (dF a) p * (p.1 : ℂ) *
            (starRingEnd ℂ) ((φ a).eval K (p.1, c))) * h2
  rw [Finset.sum_congr rfl hper, Finset.sum_neg_distrib, Finset.sum_comm]
  congr 1
  refine Finset.sum_congr rfl (fun a _ => ?_)
  have hf : IntegrableOn (fun p => heightIntegrand c (K.z₁ + K.z₂ - c) (F a) (dF a) p * (p.1 : ℂ) *
      (starRingEnd ℂ) ((φ a).eval K (p.1, c))) (Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂) :=
    (hint a).mul_continuousOn
      ((Complex.continuous_conj.comp ((bi_contDiff (hφ a)).continuous.comp
        (continuous_fst.prodMk continuous_const))).continuousOn) (rect_compact K)
  symm
  refine Breakdown.FracInternal.LayoutRowPressureBoundaryParts.strip_partition_fst (L.sideSegments e)
    (fun s => (L.segment s).lo) (fun s => (L.segment s).hi) ?_ ?_ ?_ measurableSet_Icc hf
  · intro u hu
    obtain ⟨s, hs, h1, h2⟩ := hL.sideSegments_cover e (fun h => by omega) u
      (by rw [if_neg (by omega)]; exact hu)
    exact ⟨s, hs, h1, h2⟩
  · intro s hs
    obtain ⟨_, _, _, hlo, hhi⟩ := seg_height_facts hL he hs
    exact ⟨hlo, hhi⟩
  · exact hL.sideSegments_disjoint e

end Layout

end Breakdown.CertCell.CellCalculus.RowLow.Internal
