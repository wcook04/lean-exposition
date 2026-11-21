import Breakdown.FracCell.GaugeFluxParts

open MeasureTheory Matrix

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

section TraceSide

open Set

private theorem null_vert (x : ℝ) : volume {p : ℝ × ℝ | p.1 = x} = 0 := by
  have e : {p : ℝ × ℝ | p.1 = x} = {x} ×ˢ (univ : Set ℝ) := by ext p; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]; simp

private theorem null_horiz (x : ℝ) : volume {p : ℝ × ℝ | p.2 = x} = 0 := by
  have e : {p : ℝ × ℝ | p.2 = x} = (univ : Set ℝ) ×ˢ {x} := by ext p; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod]; simp

private theorem ftc_line {c o : ℝ} (hco : c ≠ o) {g g' : ℝ → ℂ}
    (hgc : ContinuousOn g (Icc (min c o) (max c o))) (hg'c : ContinuousOn g' (Icc (min c o) (max c o)))
    (hgd : ∀ r ∈ Ioo (min c o) (max c o), HasDerivAt g (g' r) r) :
    edgeSign c o * ∫ r in Icc (min c o) (max c o), (((1 / (c - o) : ℝ) : ℂ) * g r + (((r - o) / (c - o) : ℝ) : ℂ) * g' r)
      = g c := by
  have hab : min c o < max c o := min_lt_max.2 hco
  have hco' : (c - o) ≠ 0 := sub_ne_zero.2 hco
  set ψ : ℝ → ℂ := fun r => (((r - o) / (c - o) : ℝ) : ℂ) * g r with hψ
  have hwc : Continuous fun r : ℝ => (((r - o) / (c - o) : ℝ) : ℂ) := by fun_prop
  have hψc : ContinuousOn ψ (Icc (min c o) (max c o)) := hwc.continuousOn.mul hgc
  have hψd : ∀ r ∈ Ioo (min c o) (max c o), HasDerivAt ψ
      ((((1 / (c - o) : ℝ) : ℂ) * g r + (((r - o) / (c - o) : ℝ) : ℂ) * g' r)) r := by
    intro r hr
    have h1 : HasDerivAt (fun r : ℝ => (r - o) / (c - o)) (1 / (c - o)) r := by
      simpa using ((hasDerivAt_id r).sub_const o).div_const (c - o)
    have h3 := h1.smul (hgd r hr)
    have e1 : ψ = fun y : ℝ => ((y - o) / (c - o)) • g y := funext fun y => (Complex.real_smul ..).symm
    rw [e1]
    convert h3 using 1
    all_goals first | rfl | (simp only [Complex.real_smul]; ring)
  have hint : IntervalIntegrable (fun r => (((1 / (c - o) : ℝ) : ℂ) * g r + (((r - o) / (c - o) : ℝ) : ℂ) * g' r))
      volume (min c o) (max c o) := by
    apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hab.le]
    exact (continuousOn_const.mul hgc).add (hwc.continuousOn.mul hg'c)
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab.le,
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le hψc hψd hint]
  rcases lt_or_gt_of_ne hco with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    simp only [edgeSign, if_neg (not_lt.2 h.le), hψ, sub_self, zero_div, Complex.ofReal_zero, zero_mul]
    rw [div_self hco']; simp
  · rw [min_eq_right h.le, max_eq_left h.le]
    simp only [edgeSign, if_pos h, hψ, sub_self, zero_div, Complex.ofReal_zero, zero_mul, sub_zero]
    rw [div_self hco']; simp

private theorem radial_strip {c o lo hi : ℝ} (hco : c ≠ o) {F G Gr : ℝ × ℝ → ℂ} {t : ℝ → ℝ}
    (ht : Continuous t)
    (hGc : ContinuousOn G (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (hGrc : ContinuousOn Gr (Icc (min c o) (max c o) ×ˢ Icc lo hi))
    (hGd : ∀ r ∈ Ioo (min c o) (max c o), ∀ z ∈ Icc lo hi, HasDerivAt (fun s => G (s, z)) (Gr (r, z)) r)
    (hF : ∀ᵐ p ∂(volume.restrict (Icc (min c o) (max c o) ×ˢ Icc lo hi)),
      F p = G p ∧ CellBox.radialDeriv F p = Gr p) :
    radialStripMoment c o lo hi F (CellBox.radialDeriv F) t = ∫ z in Icc lo hi, G (c, z) * ((t z : ℝ) : ℂ) := by
  unfold radialStripMoment
  have e1 : ∫ p in Icc (min c o) (max c o) ×ˢ Icc lo hi,
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * CellBox.radialDeriv F p) * ((t p.2 : ℝ) : ℂ)
      = ∫ p in Icc (min c o) (max c o) ×ˢ Icc lo hi,
      ((((1 / (c - o) : ℝ)) : ℂ) * G p + (((p.1 - o) / (c - o) : ℝ) : ℂ) * Gr p) * ((t p.2 : ℝ) : ℂ) :=
    integral_congr_ae (hF.mono fun p hp => by simp only [hp.1, hp.2])
  have hw : Continuous fun p : ℝ × ℝ => (((p.1 - o) / (c - o) : ℝ) : ℂ) := by fun_prop
  have htc : Continuous fun p : ℝ × ℝ => ((t p.2 : ℝ) : ℂ) := by fun_prop
  have hHc : ContinuousOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * G p
      + (((p.1 - o) / (c - o) : ℝ) : ℂ) * Gr p) * ((t p.2 : ℝ) : ℂ)) (Icc (min c o) (max c o) ×ˢ Icc lo hi) :=
    ((continuousOn_const.mul hGc).add (hw.continuousOn.mul hGrc)).mul htc.continuousOn
  have hHi := hHc.integrableOn_compact (μ := (volume : Measure ℝ).prod (volume : Measure ℝ)) (isCompact_Icc.prod isCompact_Icc)
  rw [e1, Measure.volume_eq_prod, setIntegral_prod _ hHi, integral_integral_swap, ← integral_const_mul]
  · refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
    simp only
    rw [integral_mul_const, ← mul_assoc]
    congr 1
    have hm : MapsTo (fun s : ℝ => (s, z)) (Icc (min c o) (max c o)) (Icc (min c o) (max c o) ×ˢ Icc lo hi) :=
      fun s hs => ⟨hs, hz⟩
    have hpc : Continuous fun s : ℝ => (s, z) := by fun_prop
    exact ftc_line hco (g := fun s => G (s, z)) (g' := fun s => Gr (s, z)) (hGc.comp hpc.continuousOn hm)
      (hGrc.comp hpc.continuousOn hm) fun r hr => hGd r hr z hz
  · rw [Measure.prod_restrict]
    exact hHi

private theorem height_strip {c o lo hi : ℝ} (hco : c ≠ o) {F G Gz : ℝ × ℝ → ℂ} {wt t : ℝ → ℝ}
    (ht : Continuous fun r => wt r * t r)
    (hGc : ContinuousOn G (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (hGzc : ContinuousOn Gz (Icc lo hi ×ˢ Icc (min c o) (max c o)))
    (hGd : ∀ r ∈ Icc lo hi, ∀ z ∈ Ioo (min c o) (max c o), HasDerivAt (fun s => G (r, s)) (Gz (r, z)) z)
    (hF : ∀ᵐ p ∂(volume.restrict (Icc lo hi ×ˢ Icc (min c o) (max c o))),
      F p = G p ∧ CellBox.heightDeriv F p = Gz p) :
    heightStripMoment c o lo hi wt F (CellBox.heightDeriv F) t
      = ∫ r in Icc lo hi, G (r, c) * ((wt r * t r : ℝ) : ℂ) := by
  unfold heightStripMoment
  have e1 : ∫ p in Icc lo hi ×ˢ Icc (min c o) (max c o),
      ((((1 / (c - o) : ℝ)) : ℂ) * F p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * CellBox.heightDeriv F p)
        * ((wt p.1 * t p.1 : ℝ) : ℂ)
      = ∫ p in Icc lo hi ×ˢ Icc (min c o) (max c o),
      ((((1 / (c - o) : ℝ)) : ℂ) * G p + (((p.2 - o) / (c - o) : ℝ) : ℂ) * Gz p) * ((wt p.1 * t p.1 : ℝ) : ℂ) :=
    integral_congr_ae (hF.mono fun p hp => by simp only [hp.1, hp.2])
  have hw : Continuous fun p : ℝ × ℝ => (((p.2 - o) / (c - o) : ℝ) : ℂ) := by fun_prop
  have htc : Continuous fun p : ℝ × ℝ => ((wt p.1 * t p.1 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (ht.comp continuous_fst)
  have hHc : ContinuousOn (fun p : ℝ × ℝ => ((((1 / (c - o) : ℝ)) : ℂ) * G p
      + (((p.2 - o) / (c - o) : ℝ) : ℂ) * Gz p) * ((wt p.1 * t p.1 : ℝ) : ℂ)) (Icc lo hi ×ˢ Icc (min c o) (max c o)) :=
    ((continuousOn_const.mul hGc).add (hw.continuousOn.mul hGzc)).mul htc.continuousOn
  have hHi := hHc.integrableOn_compact (μ := (volume : Measure ℝ).prod (volume : Measure ℝ)) (isCompact_Icc.prod isCompact_Icc)
  rw [e1, Measure.volume_eq_prod, setIntegral_prod _ hHi, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only
  rw [integral_mul_const, ← mul_assoc]
  congr 1
  have hm : MapsTo (fun s : ℝ => (r, s)) (Icc (min c o) (max c o)) (Icc lo hi ×ˢ Icc (min c o) (max c o)) :=
    fun s hs => ⟨hr, hs⟩
  have hpc : Continuous fun s : ℝ => (r, s) := by fun_prop
  exact ftc_line hco (g := fun s => G (r, s)) (g' := fun s => Gz (r, s)) (hGc.comp hpc.continuousOn hm)
    (hGzc.comp hpc.continuousOn hm) fun z hz => hGd r hr z hz


private theorem poly_contDiff {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') : ContDiff ℝ 1 P := by
  obtain ⟨cf, hcf⟩ := hP
  rw [show P = fun p : ℝ × ℝ => ∑ j, ∑ l, cf j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) from funext hcf]
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  exact ContDiff.sum fun j _ => ContDiff.sum fun l _ => (contDiff_const.mul (h1.pow _)).mul (h2.pow _)

private theorem low_fn {K : CellBox} (hK : IsCellBox K) {F P : ℝ × ℝ → ℂ} {d d' : ℕ} (hP : P ∈ polyFn d d')
    (hFP : ∀ p ∈ K.rect, p.1 ≠ 0 → ((CellScalars.rHat K p : ℝ) : ℂ) * F p = P p) :
    ∃ G : ℝ × ℝ → ℂ, ∃ U : Set (ℝ × ℝ), IsOpen U ∧ K.rect ⊆ U ∧ ContDiffOn ℝ 1 G U ∧
      ∀ p ∈ K.rect, p.1 ≠ 0 → F p = G p := by
  classical
  set ρ : ℝ → ℝ := fun r => if K.r₁ = 0 then 1 else r with hρ
  have hρc : ContDiff ℝ 1 ρ := by
    by_cases h : K.r₁ = 0
    · simp only [hρ, h, if_true]; exact contDiff_const
    · simp only [hρ, h, if_false]; exact contDiff_id
  refine ⟨fun p => P p * (((ρ p.1)⁻¹ : ℝ) : ℂ), {p | ρ p.1 ≠ 0}, ?_, ?_, ?_, ?_⟩
  · exact isOpen_ne_fun (hρc.continuous.comp continuous_fst) continuous_const
  · intro p hp
    simp only [Set.mem_ofPred_eq, hρ]
    split_ifs with h
    · exact one_ne_zero
    · have := hK.r_order.1
      have h1 := hp.1.1
      have h2 : 0 < K.r₁ := lt_of_le_of_ne this (Ne.symm h)
      linarith
  · have hinv : ContDiffOn ℝ 1 (fun p : ℝ × ℝ => (ρ p.1)⁻¹) {p | ρ p.1 ≠ 0} :=
      (hρc.comp contDiff_fst).contDiffOn.inv fun p hp => hp
    exact (poly_contDiff hP).contDiffOn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hinv)
  · intro p hp h0
    have hr : CellScalars.rHat K p = ρ p.1 := by
      simp only [CellScalars.rHat, CellBox.lineWeight, hρ]
      split_ifs
      · exact div_self h0
      · exact div_one _
    have hne : ρ p.1 ≠ 0 := by
      simp only [hρ]; split_ifs
      · exact one_ne_zero
      · exact h0
    have := hFP p hp h0
    rw [hr] at this
    show F p = P p * (((ρ p.1)⁻¹ : ℝ) : ℂ)
    rw [← this, Complex.ofReal_inv]
    field_simp [Complex.ofReal_ne_zero.2 hne]

private theorem line_r {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {p : ℝ × ℝ}
    (hp : p ∈ U) : HasDerivAt (fun s => G (s, p.2)) (fderiv ℝ G p (1, 0)) p.1 := by
  have hd : DifferentiableAt ℝ G p := (hG.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hpath : HasDerivAt (fun s : ℝ => (s, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact hd.hasFDerivAt.comp_hasDerivAt p.1 hpath

private theorem line_z {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U) {p : ℝ × ℝ}
    (hp : p ∈ U) : HasDerivAt (fun s => G (p.1, s)) (fderiv ℝ G p (0, 1)) p.2 := by
  have hd : DifferentiableAt ℝ G p := (hG.differentiableOn one_ne_zero).differentiableAt (hU.mem_nhds hp)
  have hpath : HasDerivAt (fun s : ℝ => (p.1, s)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact hd.hasFDerivAt.comp_hasDerivAt p.2 hpath

private theorem fderiv_cont {G : ℝ × ℝ → ℂ} {U : Set (ℝ × ℝ)} (hU : IsOpen U) (hG : ContDiffOn ℝ 1 G U)
    (v : ℝ × ℝ) : ContinuousOn (fun p => fderiv ℝ G p v) U :=
  (hG.continuousOn_fderiv_of_isOpen hU le_rfl).clm_apply continuousOn_const

theorem presSide_trace {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N slots : ℕ} {c : FracCellData k N}
    (hc : IsFormData α c) {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {L : CellLayout}
    (hL : IsPressureLayout c K S B L) {a : Fin N} (ha : a ∈ R.rowSet) (s : Fin L.presCount) (Pl : ℝ → ℂ)
    (hPl : ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a 0 p 0 = Pl p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a 0 p 2 = Pl p.1))
    (d : ℕ) :
    segmentTrace (L.presSegment s) (fun p => rowModeVec c a 0 p (if (L.presSegment s).radial then 0 else 2)) d =
      ∫ u in Set.Icc (L.presSegment s).lo (L.presSegment s).hi, Pl u * ((L.presSegment s).test d u : ℂ) := by
  classical
  have hK : IsCellBox K := hL.layout.box_valid
  have hr0 := hK.r_order
  have hz0 := hK.z_order
  have hnull : ∀ x : ℝ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ x := fun x =>
    (measure_eq_zero_iff_ae_notMem.1 (null_vert x)).mono fun p hp => hp
  have hnullz : ∀ x : ℝ, ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.2 ≠ x := fun x =>
    (measure_eq_zero_iff_ae_notMem.1 (null_horiz x)).mono fun p hp => hp
  have htc : Continuous ((L.presSegment s).test d) := by unfold FaceSegment.test; fun_prop
  have hco : (L.presSegment s).level ≠ (L.presSegment s).other := (hL.layout.presSegment_valid s).other_ne.symm
  rcases hL.presSegment_on_side s with ⟨hrad, hlev, hlo, hhi, hne⟩ | ⟨hrad, hlev, hlo, hhi⟩
  · have hoth := (hL.presSegment_other_in_box s).1 hrad
    obtain ⟨P, hP, hFP⟩ := hsh.row_low_velocity a ha 0 0
    obtain ⟨G, U, hU, hRU, hG, hFG⟩ := low_fn hK hP hFP
    have hab : min (L.presSegment s).level (L.presSegment s).other = K.r₁ ∧
        max (L.presSegment s).level (L.presSegment s).other = K.r₂ := by
      rcases hlev with h | h
      · rw [hoth, h, show K.r₁ + K.r₂ - K.r₁ = K.r₂ by ring]
        exact ⟨min_eq_left hr0.2.le, max_eq_right hr0.2.le⟩
      · rw [hoth, h, show K.r₁ + K.r₂ - K.r₂ = K.r₁ by ring]
        exact ⟨min_eq_right hr0.2.le, max_eq_left hr0.2.le⟩
    have hlevI : (L.presSegment s).level ∈ Icc K.r₁ K.r₂ := by
      rcases hlev with h | h <;> rw [h] <;> constructor <;> linarith
    have hstrip : Icc (min (L.presSegment s).level (L.presSegment s).other)
        (max (L.presSegment s).level (L.presSegment s).other) ×ˢ Icc (L.presSegment s).lo (L.presSegment s).hi
        ⊆ K.rect := by
      rw [hab.1, hab.2]; exact prod_mono subset_rfl (Icc_subset_Icc hlo hhi)
    unfold segmentTrace FaceSegment.moment
    simp only [hrad, if_true]
    rw [radial_strip hco (G := G) (Gr := fun p => fderiv ℝ G p (1, 0)) htc (hG.continuousOn.mono (hstrip.trans hRU))
      ((fderiv_cont hU hG _).mono (hstrip.trans hRU))
      (fun r hr z hz => line_r hU hG (p := (r, z)) (hRU (hstrip ⟨Ioo_subset_Icc_self hr, hz⟩)))]
    · refine setIntegral_congr_fun measurableSet_Icc fun z hz => ?_
      have hmem : ((L.presSegment s).level, z) ∈ K.rect := ⟨hlevI, ⟨hlo.trans hz.1, hz.2.trans hhi⟩⟩
      rw [← hFG _ hmem hne, (hPl _ hmem).1 hrad rfl]
    · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc),
        ae_restrict_of_ae (hnull (min (L.presSegment s).level (L.presSegment s).other)),
        ae_restrict_of_ae (hnull (max (L.presSegment s).level (L.presSegment s).other)),
        ae_restrict_of_ae (hnull 0)] with p hp h1 h2 h3
      have hpR := hstrip hp
      refine ⟨hFG p hpR h3, ?_⟩
      have hIoo : p.1 ∈ Ioo (min (L.presSegment s).level (L.presSegment s).other)
          (max (L.presSegment s).level (L.presSegment s).other) :=
        ⟨lt_of_le_of_ne hp.1.1 (Ne.symm h1), lt_of_le_of_ne hp.1.2 h2⟩
      have hev : (fun s' => rowModeVec c a 0 (s', p.2) 0) =ᶠ[nhds p.1] fun s' => G (s', p.2) := by
        have hn : Ioo (min (L.presSegment s).level (L.presSegment s).other)
            (max (L.presSegment s).level (L.presSegment s).other) ∩ {0}ᶜ ∈ nhds p.1 :=
          (isOpen_Ioo.inter isOpen_compl_singleton).mem_nhds ⟨hIoo, h3⟩
        filter_upwards [hn] with s' hs
        exact hFG (s', p.2) (hstrip ⟨Ioo_subset_Icc_self hs.1, hp.2⟩) hs.2
      unfold CellBox.radialDeriv
      rw [hev.deriv_eq]
      exact (line_r hU hG (hRU hpR)).deriv
  · have hoth := (hL.presSegment_other_in_box s).2 hrad
    have hrad' : (L.presSegment s).radial = false := by simpa using hrad
    obtain ⟨P, hP, hFP⟩ := hsh.row_low_velocity a ha 0 2
    obtain ⟨G, U, hU, hRU, hG, hFG⟩ := low_fn hK hP hFP
    have hab : min (L.presSegment s).level (L.presSegment s).other = K.z₁ ∧
        max (L.presSegment s).level (L.presSegment s).other = K.z₂ := by
      rcases hlev with h | h
      · rw [hoth, h, show K.z₁ + K.z₂ - K.z₁ = K.z₂ by ring]
        exact ⟨min_eq_left hz0.2.le, max_eq_right hz0.2.le⟩
      · rw [hoth, h, show K.z₁ + K.z₂ - K.z₂ = K.z₁ by ring]
        exact ⟨min_eq_right hz0.2.le, max_eq_left hz0.2.le⟩
    have hlevI : (L.presSegment s).level ∈ Icc K.z₁ K.z₂ := by
      rcases hlev with h | h <;> rw [h] <;> constructor <;> linarith
    have hstrip : Icc (L.presSegment s).lo (L.presSegment s).hi ×ˢ Icc (min (L.presSegment s).level (L.presSegment s).other)
        (max (L.presSegment s).level (L.presSegment s).other) ⊆ K.rect := by
      rw [hab.1, hab.2]; exact prod_mono (Icc_subset_Icc hlo hhi) subset_rfl
    unfold segmentTrace FaceSegment.moment
    simp only [hrad', Bool.false_eq_true, if_false]
    rw [height_strip hco (G := G) (Gz := fun p => fderiv ℝ G p (0, 1)) (by simpa using htc)
      (hG.continuousOn.mono (hstrip.trans hRU))
      ((fderiv_cont hU hG _).mono (hstrip.trans hRU))
      (fun r hr z hz => line_z hU hG (p := (r, z)) (hRU (hstrip ⟨hr, Ioo_subset_Icc_self hz⟩)))]
    · have h0 : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 :=
        (measure_eq_zero_iff_ae_notMem.1 (Real.volume_singleton (a := 0))).mono fun r h => by simpa using h
      refine setIntegral_congr_ae measurableSet_Icc (h0.mono fun r hr0 hr => ?_)
      have hmem : (r, (L.presSegment s).level) ∈ K.rect := ⟨⟨hlo.trans hr.1, hr.2.trans hhi⟩, hlevI⟩
      rw [← hFG _ hmem hr0, (hPl _ hmem).2 hrad rfl, one_mul]
    · filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc),
        ae_restrict_of_ae (hnullz (min (L.presSegment s).level (L.presSegment s).other)),
        ae_restrict_of_ae (hnullz (max (L.presSegment s).level (L.presSegment s).other)),
        ae_restrict_of_ae (hnull 0)] with p hp h1 h2 h3
      have hpR := hstrip hp
      refine ⟨hFG p hpR h3, ?_⟩
      have hIoo : p.2 ∈ Ioo (min (L.presSegment s).level (L.presSegment s).other)
          (max (L.presSegment s).level (L.presSegment s).other) :=
        ⟨lt_of_le_of_ne hp.2.1 (Ne.symm h1), lt_of_le_of_ne hp.2.2 h2⟩
      have hev : (fun s' => rowModeVec c a 0 (p.1, s') 2) =ᶠ[nhds p.2] fun s' => G (p.1, s') := by
        filter_upwards [isOpen_Ioo.mem_nhds hIoo] with s' hs
        exact hFG (p.1, s') (hstrip ⟨hp.1, Ioo_subset_Icc_self hs⟩) h3
      unfold CellBox.heightDeriv
      rw [hev.deriv_eq]
      exact (line_z hU hG (hRU hpR)).deriv

end TraceSide

theorem presSide_flux {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {k N slots : ℕ} {c : FracCellData k N}
    (hc : IsFormData α c) {K : CellBox} {S : CellScalars} {B : CellBases} {Cl : CellClasses}
    {R : CellRows N slots k} (hR : IsCellData α c K S B Cl R) (hsh : IsRowShape c K S R) {L : CellLayout}
    (hL : IsPressureLayout c K S B L) {a : Fin N} (ha : a ∈ R.rowSet) (P₁ P₂ : ℝ → ℂ)
    (hp₁ : ∃ s : Fin L.presCount, ∃ cf : Fin L.degSide → ℂ, ∀ t, P₁ t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (hp₂ : ∃ s : Fin L.presCount, ∃ cf : Fin L.degSide → ℂ, ∀ t, P₂ t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ))
    (h₁ : ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₁) 2 = P₁ r)
    (h₂ : ∀ r ∈ Set.Icc K.r₁ K.r₂, rowModeVec c a 0 (r, K.z₂) 2 = P₂ r) (x : ℝ) (hx : x ∈ Set.Icc K.r₁ K.r₂) :
    (x : ℂ) * (∫ z in K.z₁..K.z₂, (starRingEnd ℂ) (rowModeVec c a 0 (x, z) 0))
      + (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * (starRingEnd ℂ) (P₂ ρ)) - (∫ ρ in (0 : ℝ)..x, (ρ : ℂ) * (starRingEnd ℂ) (P₁ ρ)) = 0 := by
  exact presSide_flux_of_calc hR hsh hL ha (fun x hx z hz => rowMode_zero_calc hc hR hsh ha x z hx hz) P₁ P₂ hp₁ hp₂ h₁ h₂ x hx

private theorem tile_aux {ι : Type} (lo hi : ι → ℝ) (a : ℝ) (H : ℝ → ℂ) (T : Finset ι) :
    ∀ b : ℝ, (∀ i ∈ T, lo i < hi i) → (∀ i ∈ T, a ≤ lo i ∧ hi i ≤ b) →
    (∀ i ∈ T, ∀ j ∈ T, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i) →
    (∀ u, a ≤ u → u ≤ b → ∃ i ∈ T, lo i ≤ u ∧ u ≤ hi i) → a < b →
    ∑ i ∈ T, (H (hi i) - H (lo i)) = H b - H a := by
  classical
  induction T using Finset.strongInduction with
  | H T ih =>
  intro b hlt hin hdis hcov hab
  obtain ⟨i, hiT, hli, hbi⟩ := hcov b hab.le le_rfl
  have hib : hi i = b := le_antisymm (hin i hiT).2 hbi
  have hT' : ∀ j ∈ T.erase i, hi j ≤ lo i := by
    intro j hj
    obtain ⟨hji, hjT⟩ := Finset.mem_erase.mp hj
    rcases hdis i hiT j hjT (Ne.symm hji) with h | h
    · have h1 := hlt j hjT
      have h2 := (hin j hjT).2
      linarith
    · exact h
  rw [← Finset.add_sum_erase T _ hiT, hib]
  rcases (hin i hiT).1.lt_or_eq with hai | hai
  · have hcov' : ∀ u, a ≤ u → u ≤ lo i → ∃ j ∈ T.erase i, lo j ≤ u ∧ u ≤ hi j := by
      intro u hu1 hu2
      rcases hu2.lt_or_eq with hu | hu
      · obtain ⟨j, hjT, h1, h2⟩ := hcov u hu1 (by linarith [(hin i hiT).2, hlt i hiT])
        have hji : j ≠ i := by
          rintro rfl
          linarith
        exact ⟨j, Finset.mem_erase.mpr ⟨hji, hjT⟩, h1, h2⟩
      · by_contra hne
        push_neg at hne
        have hlt' : ∀ j ∈ T.erase i, hi j < lo i := by
          intro j hj
          have h1 := hT' j hj
          have h2 := hlt j (Finset.mem_of_mem_erase hj)
          have h3 := hne j hj (by linarith)
          linarith
        have hm : (insert a ((T.erase i).image hi)).max' (Finset.insert_nonempty _ _) < lo i := by
          rw [Finset.max'_lt_iff]
          intro y hy
          rcases Finset.mem_insert.mp hy with hy | hy
          · rw [hy]; exact hai
          · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hy
            exact hlt' j hj
        have ham : a ≤ (insert a ((T.erase i).image hi)).max' (Finset.insert_nonempty _ _) :=
          Finset.le_max' _ _ (Finset.mem_insert_self _ _)
        obtain ⟨j, hjT, h1, h2⟩ := hcov (((insert a ((T.erase i).image hi)).max' (Finset.insert_nonempty _ _) + lo i) / 2)
          (by linarith) (by linarith [(hin i hiT).2, hlt i hiT])
        by_cases hji : j = i
        · rw [hji] at h1
          linarith
        · have hjm : hi j ≤ (insert a ((T.erase i).image hi)).max' (Finset.insert_nonempty _ _) :=
            Finset.le_max' _ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hji, hjT⟩)))
          linarith
    have e := ih (T.erase i) (Finset.erase_ssubset hiT) (lo i) (fun j hj => hlt j (Finset.mem_of_mem_erase hj))
      (fun j hj => ⟨(hin j (Finset.mem_of_mem_erase hj)).1, hT' j hj⟩)
      (fun j hj j' hj' hne => hdis j (Finset.mem_of_mem_erase hj) j' (Finset.mem_of_mem_erase hj') hne) hcov' hai
    rw [e]
    ring
  · have he : T.erase i = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro j hj
      have h1 := hT' j hj
      have h2 := (hin j (Finset.mem_of_mem_erase hj)).1
      have h3 := hlt j (Finset.mem_of_mem_erase hj)
      linarith
    rw [he, Finset.sum_empty, ← hai]
    ring

theorem tiling_telescope {ι : Type} (T : Finset ι) (lo hi : ι → ℝ) (a b : ℝ) (H : ℝ → ℂ)
    (hlt : ∀ i ∈ T, lo i < hi i) (hin : ∀ i ∈ T, a ≤ lo i ∧ hi i ≤ b)
    (hdis : ∀ i ∈ T, ∀ j ∈ T, i ≠ j → hi i ≤ lo j ∨ hi j ≤ lo i)
    (hcov : ∀ u, a ≤ u → u ≤ b → ∃ i ∈ T, lo i ≤ u ∧ u ≤ hi i) (hab : a < b) :
    ∑ i ∈ T, (H (hi i) - H (lo i)) = H b - H a :=
  tile_aux lo hi a H T b hlt hin hdis hcov hab

end CellFormula

end CellCert

end Breakdown
