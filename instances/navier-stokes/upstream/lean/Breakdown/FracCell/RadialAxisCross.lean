import Breakdown.FracCell.MeshFluxRadial
import Breakdown.FracCell.ModeStripIntegrable
import Breakdown.FracCell.ModeRadialLine
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.AngularMode
import Breakdown.FracCell.CircleWeak
import Breakdown.FracCell.CellDensityModesWeak
import Breakdown.FracCell.CellDensityModesMirror
import Breakdown.FracCell.ModeRadialWeakProof

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellCoordinates

open SteadyCert Assembly CellAnalysis CellFormula

def AxisPrimitiveStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ (A z₁ z₂ : ℝ), 0 < A → z₁ < z₂ →
      ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc 0 A)),
        modeVec m 0 v r z 0 = ∫ t in (0 : ℝ)..r, gradMode m 0 G 0 0 (t, z)

namespace RadialAxisCrossInternal

theorem half_turn (h : ℝ → ℂ) (hp : Function.Periodic h (2 * Real.pi)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), h (θ + Real.pi) = ∫ θ in (0 : ℝ)..(2 * Real.pi), h θ := by
  rw [intervalIntegral.integral_comp_add_right h Real.pi, zero_add]
  have e := hp.intervalIntegral_add_eq Real.pi 0
  rw [zero_add] at e
  rw [show 2 * Real.pi + Real.pi = Real.pi + 2 * Real.pi by ring, e]

theorem cylPoint_half (r θ z : ℝ) : cylPoint (-r) θ z = cylPoint r (θ + Real.pi) z := by
  simp only [cylPoint, Real.cos_add_pi, Real.sin_add_pi, mul_neg, neg_mul]

theorem cylPoint_full (r θ z : ℝ) : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
  simp only [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem radialUnit_half (θ : ℝ) : radialUnit (θ + Real.pi) = -radialUnit θ := by
  ext i
  fin_cases i <;> simp [radialUnit, Real.cos_add_pi, Real.sin_add_pi]

theorem radialUnit_full (θ : ℝ) : radialUnit (θ + 2 * Real.pi) = radialUnit θ := by
  simp only [radialUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem modeVec_neg (m : ℕ) (v : Space → Space) (r z : ℝ) :
    modeVec m 0 v (-r) z 0 = -modeVec m 0 v r z 0 := by
  have key : ∀ θ, ((frameVec θ (v (cylPoint (-r) θ z)) 0 : ℝ) : ℂ) =
      -((frameVec (θ + Real.pi) (v (cylPoint r (θ + Real.pi) z)) 0 : ℝ) : ℂ) := by
    intro θ
    rw [cylPoint_half]
    simp only [frameVec, Matrix.cons_val_zero]
    rw [radialUnit_half, inner_neg_right]
    push_cast
    ring
  have hp : Function.Periodic (fun θ => ((frameVec θ (v (cylPoint r θ z)) 0 : ℝ) : ℂ)) (2 * Real.pi) := by
    intro θ
    simp only [frameVec, Matrix.cons_val_zero, cylPoint_full, radialUnit_full]
  unfold modeVec
  simp only [azimuth, Int.cast_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
  simp_rw [key]
  rw [intervalIntegral.integral_neg, half_turn _ hp]
  ring

theorem gradMode_neg (m : ℕ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) :
    gradMode m 0 G 0 0 (-r, z) = gradMode m 0 G 0 0 (r, z) := by
  have key : ∀ θ, ((frameMat θ (G (cylPoint (-r) θ z)) 0 0 : ℝ) : ℂ) =
      ((frameMat (θ + Real.pi) (G (cylPoint r (θ + Real.pi) z)) 0 0 : ℝ) : ℂ) := by
    intro θ
    rw [cylPoint_half]
    simp only [frameMat, Matrix.cons_val_zero]
    rw [radialUnit_half, map_neg, inner_neg_neg]
  have hp : Function.Periodic (fun θ => ((frameMat θ (G (cylPoint r θ z)) 0 0 : ℝ) : ℂ)) (2 * Real.pi) := by
    intro θ
    simp only [frameMat, Matrix.cons_val_zero, cylPoint_full, radialUnit_full]
  unfold gradMode modeMat
  simp only [azimuth, Int.cast_zero, zero_mul, Complex.ofReal_zero, neg_zero, Complex.exp_zero, one_mul]
  simp_rw [key]
  rw [half_turn _ hp]

theorem rect_measure (a b c d : ℝ) :
    volume.restrict (Icc a b ×ˢ Icc c d) = (volume.restrict (Icc a b)).prod (volume.restrict (Icc c d)) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

theorem slice {a b c d : ℝ} {f : ℝ × ℝ → ℂ} (hf : IntegrableOn f (Icc a b ×ˢ Icc c d)) :
    ∀ᵐ z ∂(volume.restrict (Icc c d)), IntegrableOn (fun r => f (r, z)) (Icc a b) := by
  rw [IntegrableOn, rect_measure] at hf
  exact hf.prod_left_ae

theorem reflect {f : ℝ × ℝ → ℂ} {a : ℝ} {T : Set ℝ} (hf : IntegrableOn f (Icc 0 a ×ˢ T)) :
    IntegrableOn (fun p => f (-p.1, p.2)) (Icc (-a) 0 ×ˢ T) := by
  have hmp : MeasurePreserving (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ))
      (volume : Measure (ℝ × ℝ)) volume := by
    rw [Measure.volume_eq_prod]
    exact (Measure.measurePreserving_neg volume).prod (MeasurePreserving.id volume)
  have he : MeasurableEmbedding (Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ)) :=
    (Homeomorph.neg ℝ).measurableEmbedding.prodMap MeasurableEmbedding.id
  have hpre : Prod.map (Neg.neg : ℝ → ℝ) (id : ℝ → ℝ) ⁻¹' (Icc 0 a ×ˢ T) = Icc (-a) 0 ×ˢ T := by
    ext p
    simp only [mem_preimage, Prod.map_fst, Prod.map_snd, mem_prod, mem_Icc, id]
    constructor
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
    · rintro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨⟨by linarith, by linarith⟩, h3⟩
  have h := (hmp.integrableOn_comp_preimage he).2 hf
  rw [hpre] at h
  exact h

theorem weight_swap {o R : ℝ} {d : ℝ → ℂ} (hd : IntegrableOn d (Icc o R)) :
    ∫ r in Icc o R, ((r - o : ℝ) : ℂ) * d r = ∫ s in Icc o R, ∫ r in Icc s R, d r := by
  have hdI : Integrable d (volume.restrict (Icc o R)) := hd
  have h1 : Integrable (fun q : ℝ × ℝ => d q.2)
      ((volume.restrict (Icc o R)).prod (volume.restrict (Icc o R))) := by
    exact hdI.comp_snd (volume.restrict (Icc o R))
  have h2 : Integrable (Function.uncurry (fun s r : ℝ => if s ≤ r then d r else 0))
      ((volume.restrict (Icc o R)).prod (volume.restrict (Icc o R))) := by
    have := h1.indicator (measurableSet_le measurable_fst measurable_snd)
    refine this.congr (Filter.Eventually.of_forall fun q => ?_)
    simp only [Function.uncurry, Set.indicator_apply, mem_ofPred_eq]
  have sw := integral_integral_swap h2
  have lhs : ∀ r ∈ Icc o R, ∫ s in Icc o R, (if s ≤ r then d r else 0) = ((r - o : ℝ) : ℂ) * d r := by
    intro r hr
    have e : (fun s : ℝ => if s ≤ r then d r else 0) = (Iic r).indicator (fun _ => d r) := by
      funext s
      simp only [Set.indicator_apply, mem_Iic]
    rw [e, integral_indicator measurableSet_Iic, Measure.restrict_restrict measurableSet_Iic,
      setIntegral_const]
    have hs : Iic r ∩ Icc o R = Icc o r := by
      ext s
      simp only [mem_inter_iff, mem_Iic, mem_Icc]
      constructor
      · rintro ⟨h1, h2, _⟩
        exact ⟨h2, h1⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h2, h1, h2.trans hr.2⟩
    rw [hs]
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hr.1), Complex.real_smul]
  have rhs : ∀ s ∈ Icc o R, ∫ r in Icc o R, (if s ≤ r then d r else 0) = ∫ r in Icc s R, d r := by
    intro s hs
    have e : (fun r : ℝ => if s ≤ r then d r else 0) = (Ici s).indicator d := by
      funext r
      simp only [Set.indicator_apply, mem_Ici]
    rw [e, integral_indicator measurableSet_Ici, Measure.restrict_restrict measurableSet_Ici]
    have hs' : Ici s ∩ Icc o R = Icc s R := by
      ext r
      simp only [mem_inter_iff, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨h1, _, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, hs.1.trans h1, h2⟩
    rw [hs']
  rw [← setIntegral_congr_fun measurableSet_Icc lhs, ← setIntegral_congr_fun measurableSet_Icc rhs]
  exact sw.symm

theorem line_eq {o R : ℝ} (ho : o ≤ 0) (hR : 0 ≤ R) (hoR : o < R) {d u : ℝ → ℂ}
    (hd : IntegrableOn d (Icc o R))
    (hu : ∀ᵐ r ∂(volume.restrict (Icc o R)), u r = ∫ t in (0 : ℝ)..r, d t) :
    ∫ r in Icc o R, (((1 / (R - o) : ℝ) : ℂ) * u r + (((r - o) / (R - o) : ℝ) : ℂ) * d r) * ((1 : ℝ) : ℂ)
      = ∫ t in (0 : ℝ)..R, d t := by
  have hi : IntervalIntegrable d volume o R := (intervalIntegrable_iff_integrableOn_Icc_of_le hoR.le).2 hd
  have hfc : ContinuousOn (fun r => ∫ t in (0 : ℝ)..r, d t) (Icc o R) := by
    have h := intervalIntegral.continuousOn_primitive_interval' hi (by rw [uIcc_of_le hoR.le]; exact ⟨ho, hR⟩)
    rwa [uIcc_of_le hoR.le] at h
  have hfi : IntegrableOn (fun r => ∫ t in (0 : ℝ)..r, d t) (Icc o R) := hfc.integrableOn_compact isCompact_Icc
  have hdi : ∀ x ∈ Icc o R, ∀ y ∈ Icc o R, IntervalIntegrable d volume x y := fun x hx y hy =>
    (hd.mono_set (uIcc_subset_Icc hx hy)).intervalIntegrable
  have h0 : (0 : ℝ) ∈ Icc o R := ⟨ho, hR⟩
  have hsub : ∀ s ∈ Icc o R, ∫ r in Icc s R, d r =
      (∫ t in (0 : ℝ)..R, d t) - ∫ t in (0 : ℝ)..s, d t := by
    intro s hs
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs.2,
      intervalIntegral.integral_interval_sub_left (hdi 0 h0 R ⟨hoR.le, le_rfl⟩) (hdi 0 h0 s hs)]
  have hw : ∫ r in Icc o R, ((r - o : ℝ) : ℂ) * d r =
      ((R - o : ℝ) : ℂ) * (∫ t in (0 : ℝ)..R, d t) - ∫ r in Icc o R, ∫ t in (0 : ℝ)..r, d t := by
    rw [weight_swap hd, setIntegral_congr_fun measurableSet_Icc hsub,
      integral_sub (continuousOn_const.integrableOn_compact isCompact_Icc) hfi, setIntegral_const]
    simp [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (sub_nonneg.2 hoR.le), Complex.real_smul]
  have hL : ∫ r in Icc o R, (((1 / (R - o) : ℝ) : ℂ) * u r + (((r - o) / (R - o) : ℝ) : ℂ) * d r) * ((1 : ℝ) : ℂ)
      = ∫ r in Icc o R, ((1 / (R - o) : ℝ) : ℂ) *
          ((∫ t in (0 : ℝ)..r, d t) + ((r - o : ℝ) : ℂ) * d r) := by
    refine setIntegral_congr_ae measurableSet_Icc ?_
    filter_upwards [(ae_restrict_iff' measurableSet_Icc).1 hu] with r hr hrI
    rw [hr hrI]
    push_cast
    ring
  have hwi : IntegrableOn (fun r : ℝ => ((r - o : ℝ) : ℂ) * d r) (Icc o R) :=
    hd.continuousOn_mul (g := fun r : ℝ => ((r - o : ℝ) : ℂ)) (Continuous.continuousOn (by fun_prop)) isCompact_Icc
  rw [hL, integral_const_mul, integral_add hfi hwi, hw]
  have hne : (R : ℂ) - (o : ℂ) ≠ 0 := by
    have : ((R - o : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.2 hoR).ne'
    simpa using this
  push_cast
  field_simp
  ring

theorem strip_eq {o R z₁ z₂ : ℝ} (ho : o ≤ 0) (hR : 0 ≤ R) (hoR : o < R) {F D : ℝ × ℝ → ℂ}
    (hF : IntegrableOn F (Icc o R ×ˢ Icc z₁ z₂)) (hD : IntegrableOn D (Icc o R ×ˢ Icc z₁ z₂))
    (hp : ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc o R)),
      F (r, z) = ∫ t in (0 : ℝ)..r, D (t, z)) :
    ∫ p in Icc o R ×ˢ Icc z₁ z₂,
        (((1 / (R - o) : ℝ) : ℂ) * F p + (((p.1 - o) / (R - o) : ℝ) : ℂ) * D p) * ((1 : ℝ) : ℂ)
      = ∫ z in Icc z₁ z₂, ∫ t in (0 : ℝ)..R, D (t, z) := by
  have hint : IntegrableOn (fun p : ℝ × ℝ =>
      (((1 / (R - o) : ℝ) : ℂ) * F p + (((p.1 - o) / (R - o) : ℝ) : ℂ) * D p) * ((1 : ℝ) : ℂ))
      (Icc o R ×ˢ Icc z₁ z₂) := by
    refine Integrable.mul_const ?_ _
    exact (hF.const_mul _).add (hD.continuousOn_mul (g := fun p : ℝ × ℝ => (((p.1 - o) / (R - o) : ℝ) : ℂ))
      (Continuous.continuousOn (by fun_prop)) (isCompact_Icc.prod isCompact_Icc))
  rw [IntegrableOn, rect_measure] at hint
  rw [rect_measure, integral_prod_symm _ hint]
  refine integral_congr_ae ?_
  filter_upwards [hp, slice hD] with z hz hDz
  exact line_eq (u := fun r => F (r, z)) (d := fun r => D (r, z)) ho hR hoR hDz hz

theorem cross_generic {R o z₁ z₂ : ℝ} (hR : 0 < R) (ho : o < 0) {F D : ℝ × ℝ → ℂ}
    (hodd : ∀ r z, F (-r, z) = -F (r, z)) (heven : ∀ r z, D (-r, z) = D (r, z))
    (hF0 : ∀ A, IntegrableOn F (Icc 0 A ×ˢ Icc z₁ z₂)) (hD0 : ∀ A, IntegrableOn D (Icc 0 A ×ˢ Icc z₁ z₂))
    (hP : ∀ A, 0 < A → ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc 0 A)),
      F (r, z) = ∫ t in (0 : ℝ)..r, D (t, z)) :
    radialStripMoment R o z₁ z₂ F D (fun _ => 1) = radialStripMoment R 0 z₁ z₂ F D (fun _ => 1) := by
  set A : ℝ := max R (-o) with hAdef
  have hA0 : 0 < A := lt_max_of_lt_left hR
  have hRA : R ≤ A := le_max_left _ _
  have hoA : -A ≤ o := by have := le_max_right R (-o); linarith
  have hms : MeasurableSet (Icc (-A) 0 ×ˢ Icc z₁ z₂) := measurableSet_Icc.prod measurableSet_Icc
  have hFn : IntegrableOn F (Icc (-A) 0 ×ˢ Icc z₁ z₂) := by
    refine (reflect (hF0 A)).neg.congr_fun (fun p _ => ?_) hms
    simp only [Pi.neg_apply]
    rw [hodd, neg_neg]
  have hDn : IntegrableOn D (Icc (-A) 0 ×ˢ Icc z₁ z₂) := by
    refine (reflect (hD0 A)).congr_fun (fun p _ => ?_) hms
    simp only
    rw [heven]
  have hsplit : Icc (-A) A ×ˢ Icc z₁ z₂ = Icc (-A) 0 ×ˢ Icc z₁ z₂ ∪ Icc 0 A ×ˢ Icc z₁ z₂ := by
    rw [← union_prod, Icc_union_Icc_eq_Icc (by linarith) hA0.le]
  have hFA : IntegrableOn F (Icc (-A) A ×ˢ Icc z₁ z₂) := by
    rw [hsplit]; exact hFn.union (hF0 A)
  have hDA : IntegrableOn D (Icc (-A) A ×ˢ Icc z₁ z₂) := by
    rw [hsplit]; exact hDn.union (hD0 A)
  have hPA : ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc (-A) A)),
      F (r, z) = ∫ t in (0 : ℝ)..r, D (t, z) := by
    filter_upwards [hP A hA0] with z hz
    rw [ae_restrict_iff' measurableSet_Icc] at hz ⊢
    have hz' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hz
    filter_upwards [hz, hz'] with r h1 h2 hr
    rcases le_total 0 r with h0 | h0
    · exact h1 ⟨h0, hr.2⟩
    · have h3 := h2 ⟨by linarith, by linarith [hr.1]⟩
      have e2 : ∫ t in (0 : ℝ)..r, D (t, z) = -∫ t in (0 : ℝ)..(-r), D (t, z) := by
        have e3 : ∫ t in (0 : ℝ)..r, D (t, z) = ∫ t in (0 : ℝ)..r, D (-t, z) := by
          congr 1
          funext t
          rw [heven]
        have e4 := intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := r) (f := fun t => D (t, z))
        simp only [neg_zero] at e4
        rw [e3, e4, intervalIntegral.integral_symm]
      have e1 : F (r, z) = -F (-r, z) := by rw [hodd, neg_neg]
      rw [e1, h3, e2]
  have hsubO : Icc o R ×ˢ Icc z₁ z₂ ⊆ Icc (-A) A ×ˢ Icc z₁ z₂ := prod_mono (Icc_subset_Icc hoA hRA) le_rfl
  have hsub0 : Icc 0 R ×ˢ Icc z₁ z₂ ⊆ Icc (-A) A ×ˢ Icc z₁ z₂ :=
    prod_mono (Icc_subset_Icc (by linarith) hRA) le_rfl
  have hPo : ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc o R)),
      F (r, z) = ∫ t in (0 : ℝ)..r, D (t, z) := by
    filter_upwards [hPA] with z hz
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc hoA hRA) hz
  have hP0 : ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc 0 R)),
      F (r, z) = ∫ t in (0 : ℝ)..r, D (t, z) := by
    filter_upwards [hPA] with z hz
    exact ae_restrict_of_ae_restrict_of_subset (Icc_subset_Icc (by linarith) hRA) hz
  have e1 : edgeSign R o = 1 := by simp [edgeSign, show o < R by linarith]
  have e0 : edgeSign R 0 = 1 := by simp [edgeSign, hR]
  unfold radialStripMoment
  rw [e1, e0, min_eq_right (by linarith : o ≤ R), max_eq_left (by linarith : o ≤ R),
    min_eq_right hR.le, max_eq_left hR.le, one_mul, one_mul]
  rw [strip_eq ho.le hR.le (by linarith) (hFA.mono_set hsubO) (hDA.mono_set hsubO) hPo,
    strip_eq le_rfl hR.le hR (hFA.mono_set hsub0) (hDA.mono_set hsub0) hP0]

theorem axis_zero {A : ℝ} (hA : 0 < A) {u d T f : ℝ → ℂ}
    (hftc : ∀ x ∈ Ioc 0 A, ∀ y ∈ Ioc 0 A, f y = f x + ∫ t in x..y, d t)
    (hd : IntegrableOn d (Icc 0 A)) (hT : IntegrableOn T (Icc 0 A))
    (huf : u =ᵐ[volume.restrict (Icc 0 A)] f)
    (hang : ∀ᵐ (r : ℝ) ∂(volume.restrict (Icc 0 A)), 0 < r → ((r : ℝ) : ℂ) * T r = u r) :
    ∀ᵐ r ∂(volume.restrict (Icc 0 A)), u r = ∫ t in (0 : ℝ)..r, d t := by
  have hdi : IntervalIntegrable d volume 0 A := (intervalIntegrable_iff_integrableOn_Icc_of_le hA.le).2 hd
  have hdi' : ∀ x ∈ Icc 0 A, IntervalIntegrable d volume 0 x := fun x hx =>
    (hd.mono_set (uIcc_subset_Icc ⟨le_rfl, hA.le⟩ hx)).intervalIntegrable
  have hfL : ∀ x ∈ Ioc 0 A, f x = (f A - ∫ t in (0 : ℝ)..A, d t) + ∫ t in (0 : ℝ)..x, d t := by
    intro x hx
    have h1 := hftc x hx A ⟨hA, le_rfl⟩
    have h2 := intervalIntegral.integral_interval_sub_left (hdi' A ⟨hA.le, le_rfl⟩) (hdi' x ⟨hx.1.le, hx.2⟩)
    linear_combination -h1 + h2
  have hL0 : f A - ∫ t in (0 : ℝ)..A, d t = 0 := by
    by_contra hL
    set L := f A - ∫ t in (0 : ℝ)..A, d t with hLdef
    have hLpos : 0 < ‖L‖ := norm_pos_iff.2 hL
    have hgc := intervalIntegral.continuousOn_primitive_interval' hdi
      (by rw [uIcc_of_le hA.le]; exact ⟨le_rfl, hA.le⟩)
    rw [uIcc_of_le hA.le] at hgc
    obtain ⟨δ, hδ, hδg⟩ := Metric.continuousWithinAt_iff.1 (hgc 0 ⟨le_rfl, hA.le⟩) (‖L‖ / 2) (by positivity)
    have he : 0 < min (δ / 2) A := lt_min (by positivity) hA
    have hsub : Ioc 0 (min (δ / 2) A) ⊆ Icc 0 A := fun r hr => ⟨hr.1.le, hr.2.trans (min_le_right _ _)⟩
    have hTi : IntegrableOn T (Ioc 0 (min (δ / 2) A)) := hT.mono_set hsub
    have hbound : ∀ᵐ r ∂(volume.restrict (Ioc 0 (min (δ / 2) A))), ‖(r⁻¹ : ℝ)‖ ≤ 2 / ‖L‖ * ‖T r‖ := by
      filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub huf,
        ae_restrict_of_ae_restrict_of_subset hsub hang, ae_restrict_mem measurableSet_Ioc] with r h1 h2 hr
      have hrA : r ∈ Ioc 0 A := ⟨hr.1, hr.2.trans (min_le_right _ _)⟩
      have hrd : dist r 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]
        linarith [hr.2, min_le_left (δ / 2) A]
      have hg := hδg ⟨hr.1.le, hrA.2⟩ hrd
      rw [intervalIntegral.integral_same, dist_zero_right] at hg
      have hu : ‖L‖ ≤ 2 * ‖u r‖ := by
        rw [h1, hfL r hrA]
        have := norm_sub_le (L + ∫ t in (0 : ℝ)..r, d t) (∫ t in (0 : ℝ)..r, d t)
        rw [add_sub_cancel_right] at this
        linarith
      have hrT : ‖u r‖ = r * ‖T r‖ := by
        rw [← h2 hr.1, norm_mul, Complex.norm_real, Real.norm_of_nonneg hr.1.le]
      rw [Real.norm_of_nonneg (inv_nonneg.2 hr.1.le),
        show 2 / ‖L‖ * ‖T r‖ = (2 * ‖T r‖) / ‖L‖ by ring, le_div_iff₀ hLpos, inv_mul_le_iff₀ hr.1]
      nlinarith [hu, hrT]
    have hInt : IntegrableOn (fun r : ℝ => r⁻¹) (Ioc 0 (min (δ / 2) A)) :=
      Integrable.mono' (hTi.norm.const_mul (2 / ‖L‖)) measurable_inv.aestronglyMeasurable hbound
    have hII := (intervalIntegrable_iff_integrableOn_Ioc_of_le he.le).2 hInt
    rw [intervalIntegrable_inv_iff] at hII
    rcases hII with h | h
    · linarith
    · exact h (by rw [uIcc_of_le he.le]; exact ⟨le_rfl, he.le⟩)
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := (0 : ℝ)))] with r hr
    exact hr
  filter_upwards [huf, ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne] with r h1 hr hr0
  rw [h1, hfL r ⟨lt_of_le_of_ne hr.1 (Ne.symm hr0), hr.2⟩, hL0, zero_add]

theorem axisPrimitive_upper (hL : ModeRadialLineStatement) (hA : AngularModeStatement) {m : ℕ}
    {v : Space → Space} {G : Space → (Space →L[ℝ] Space)} {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsSecondOrderField m v G H) {A z₁ z₂ : ℝ} (hA0 : 0 < A) (hz1 : 0 ≤ z₁) (hz : z₁ < z₂) :
    ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), ∀ᵐ r ∂(volume.restrict (Icc 0 A)),
      modeVec m 0 v r z 0 = ∫ t in (0 : ℝ)..r, gradMode m 0 G 0 0 (t, z) := by
  have hK : IsCellBox ⟨0, A, z₁, z₂⟩ := ⟨⟨le_rfl, hA0⟩, ⟨hz1, hz⟩⟩
  have hline := hL ⟨0, A, z₁, z₂⟩ hK m v G H hs 0 0
  obtain ⟨_, hgI⟩ := modeStripIntegrable m v G H hs 0 A z₁ z₂
  have hang2 : ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      (p.1 : ℂ) * gradMode m 0 G 1 1 p = modeVec m 0 v p.1 p.2 0 := by
    filter_upwards [hA m v G H hs 0] with p hp h0
    obtain ⟨-, h11, -⟩ := hp h0
    rw [h11]
    simp [azimuth]
  have hang3 : ∀ᵐ (z : ℝ) ∂(volume : Measure ℝ), ∀ᵐ (r : ℝ) ∂(volume : Measure ℝ),
      0 < r → ((r : ℝ) : ℂ) * gradMode m 0 G 1 1 (r, z) = modeVec m 0 v r z 0 := by
    rw [Measure.volume_eq_prod] at hang2
    have h := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).quasiMeasurePreserving.ae hang2
    exact Measure.ae_ae_of_ae_prod h
  filter_upwards [hline, slice (hgI 0 0), slice (hgI 1 1), ae_restrict_of_ae hang3] with z hz hD hT hang
  obtain ⟨f, hftc, -, -, -, -, huf⟩ := hz
  exact axis_zero hA0 hftc hD hT huf (ae_restrict_of_ae hang)

theorem swap_ae {P : ℝ × ℝ → Prop} (h : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), P p) :
    ∀ᵐ (z : ℝ) ∂(volume : Measure ℝ), ∀ᵐ (r : ℝ) ∂(volume : Measure ℝ), P (r, z) := by
  rw [Measure.volume_eq_prod] at h
  have h' := (Measure.measurePreserving_swap (μ := (volume : Measure ℝ)) (ν := volume)).quasiMeasurePreserving.ae h
  exact Measure.ae_ae_of_ae_prod h'

theorem inner_mirror_left (u w : Space) : inner ℝ (mirror u) w = inner ℝ u (mirror w) := by
  simp only [FracInternal.CellDensityModesMirror.inner_eq, FracInternal.CellDensityModesMirror.mirror_apply]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem cylPoint_mirror (r θ z : ℝ) : cylPoint r θ (-z) = mirror (cylPoint r θ z) := by
  ext i
  rw [FracInternal.CellDensityModesMirror.mirror_apply]
  fin_cases i <;> simp [cylPoint, FracInternal.CellDensityModesMirror.sgn]

theorem radialUnit_mirror (θ : ℝ) : mirror (radialUnit θ) = radialUnit θ := by
  ext i
  rw [FracInternal.CellDensityModesMirror.mirror_apply]
  fin_cases i <;> simp [radialUnit, FracInternal.CellDensityModesMirror.sgn]

theorem mode_mirror {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) :
    ∀ᵐ p : ℝ × ℝ ∂volume, 0 < p.1 →
      modeVec m 0 v p.1 (-p.2) 0 = modeVec m 0 v p.1 p.2 0 ∧
        gradMode m 0 G 0 0 (p.1, -p.2) = gradMode m 0 G 0 0 p := by
  have hE : ∀ᵐ y ∂volume, v (mirror y) = mirror (v y) ∧ ∀ u, G (mirror y) u = mirror (G y (mirror u)) := by
    filter_upwards [hs.symmetric.2, gradientMirror m v G H hs] with y h1 h2
    exact ⟨h1, h2.1⟩
  have h1 := LowEntry.Internal.qmp.ae hE
  rw [LowEntry.Internal.muU_def] at h1
  have h2 := Measure.ae_ae_of_ae_prod h1
  rw [ae_restrict_iff' (measurableSet_Ioi.prod MeasurableSet.univ)] at h2
  filter_upwards [h2] with p hp hp0
  have hp' := (ae_restrict_iff' measurableSet_Ioo).1 (hp ⟨hp0, mem_univ _⟩)
  constructor
  · have e1 := LowEntry.Internal.modeVec_eq m 0 v 0 (p.1, -p.2)
    have e2 := LowEntry.Internal.modeVec_eq m 0 v 0 p
    simp only at e1
    rw [e1, e2]
    congr 1
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hp'] with θ hθ hθI
    obtain ⟨hv, -⟩ := hθ hθI
    simp only [LowEntry.Internal.cylArg] at hv
    simp only [LowEntry.Internal.velKernel, frameVec, Matrix.cons_val_zero]
    rw [cylPoint_mirror, hv, inner_mirror_left, radialUnit_mirror]
  · have e1 := LowEntry.Internal.gradMode_eq m 0 G 0 0 (p.1, -p.2)
    have e2 := LowEntry.Internal.gradMode_eq m 0 G 0 0 p
    simp only at e1
    rw [e1, e2]
    congr 1
    refine setIntegral_congr_ae measurableSet_Ioo ?_
    filter_upwards [hp'] with θ hθ hθI
    obtain ⟨-, hG⟩ := hθ hθI
    simp only [LowEntry.Internal.cylArg] at hG
    simp only [LowEntry.Internal.gradKernel, frameMat, Matrix.cons_val_zero]
    rw [cylPoint_mirror, hG, radialUnit_mirror, inner_mirror_left, radialUnit_mirror]

theorem axisPrimitive_of_weak (hW : ModeRadialWeakStatement) : AxisPrimitiveStatement := by
  intro m v G H hs A z₁ z₂ hA hz
  have hZ : 0 < |z₁| + |z₂| + 1 := by positivity
  have hup := axisPrimitive_upper (modeRadialLine_of hW modeGradSquare modeVelSquare)
    (angularMode CellEnergy.circleWeak) hs (z₁ := 0) (z₂ := |z₁| + |z₂| + 1) hA le_rfl hZ
  rw [ae_restrict_iff' measurableSet_Icc] at hup ⊢
  have hneg := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae hup
  have hmir := swap_ae (mode_mirror hs)
  have hne : ∀ᵐ r ∂(volume : Measure ℝ), r ≠ 0 := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := (0 : ℝ)))] with r hr
    exact hr
  filter_upwards [hup, hneg, hmir] with z h1 h2 h3 hzI
  rcases le_total 0 z with h0 | h0
  · exact h1 ⟨h0, by linarith [hzI.2, le_abs_self z₂, abs_nonneg z₁]⟩
  · have hP := h2 ⟨by linarith, by linarith [hzI.1, neg_abs_le z₁, abs_nonneg z₂]⟩
    filter_upwards [hP, ae_restrict_of_ae h3, ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae hne]
      with r hr1 hr3 hrI hr0
    have hrpos : 0 < r := lt_of_le_of_ne hrI.1 (Ne.symm hr0)
    rw [← (hr3 hrpos).1, hr1]
    refine intervalIntegral.integral_congr_ae ?_
    filter_upwards [h3] with t ht htI
    rw [uIoc_of_le hrpos.le] at htI
    exact (ht htI.1).2

end RadialAxisCrossInternal

open RadialAxisCrossInternal

theorem radialAxisCross_of (hS : AxisPrimitiveStatement) : RadialAxisCrossStatement := by
  intro m v G H hs R o z₁ z₂ hR ho hz
  exact cross_generic hR ho (fun r z => modeVec_neg m v r z) (fun r z => gradMode_neg m G r z)
    (fun A => (modeStripIntegrable m v G H hs 0 A z₁ z₂).1 0)
    (fun A => (modeStripIntegrable m v G H hs 0 A z₁ z₂).2 0 0)
    (fun A hA => hS m v G H hs A z₁ z₂ hA hz)

theorem radialAxisCross_of_weak (hW : ModeRadialWeakStatement) : RadialAxisCrossStatement :=
  radialAxisCross_of (axisPrimitive_of_weak hW)

theorem radialAxisCross : RadialAxisCrossStatement :=
  radialAxisCross_of_weak modeRadialWeak

end CellCoordinates

end CellCert

end Breakdown
