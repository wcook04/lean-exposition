import Breakdown.CellReduction.PotScalarOriginParts

open scoped ContDiff Topology
open Filter

noncomputable section

namespace Breakdown

namespace PotentialShape

namespace ScalarOrigin

namespace Internal

open CertCell CertCell.GivenShape
open CellCert.GivenFields (Spline heightRatio weightPoly planePhase_contDiff planePhase_fderiv_localSlope)

section Angular

def planeOfPoint (v : Space) : ℂ := ((v 0 : ℝ) : ℂ) + ((v 1 : ℝ) : ℂ) * Complex.I

def planeConj (v : Space) : ℂ := ((v 0 : ℝ) : ℂ) - ((v 1 : ℝ) : ℂ) * Complex.I

def angular (M : ℤ) (ws : Bool) (ap : ℕ) (v : Space) : ℂ :=
  Complex.exp ((((M : ℝ) * pointAngle v : ℝ) : ℂ) * Complex.I) *
    (((1 - heightRatio v ^ 2) ^ ap * (if ws then polarSine v else 1) : ℝ) : ℂ)

def phaseRing (j : ℤ) (w : ℂ) : ℂ :=
  ((‖w‖ ^ 2 : ℝ) : ℂ) * Complex.exp ((((j : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I)

theorem pointAngle_eq (v : Space) : pointAngle v = Complex.arg (planeOfPoint v) := rfl

theorem ofReal_contDiffAt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {g : E → ℝ} {p : E}
    (h : ContDiffAt ℝ 2 g p) : ContDiffAt ℝ 2 (fun q => ((g q : ℝ) : ℂ)) p :=
  Complex.ofRealCLM.contDiff.contDiffAt.comp p h

theorem planeOfPoint_contDiff : ContDiff ℝ 2 planeOfPoint := by
  have h0 : ContDiff ℝ 2 (fun y : Space => ((y 0 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ 2 (fun y : Space => ((y 1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  exact h0.add (h1.mul contDiff_const)

theorem planeConj_contDiff : ContDiff ℝ 2 planeConj := by
  have h0 : ContDiff ℝ 2 (fun y : Space => ((y 0 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  have h1 : ContDiff ℝ 2 (fun y : Space => ((y 1 : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (1 : Fin 3) : Space →L[ℝ] ℝ).contDiff
  exact h0.sub (h1.mul contDiff_const)

theorem planeConj_eq (v : Space) :
    planeConj v = (‖planeOfPoint v‖ : ℂ) * Complex.exp (((-Complex.arg (planeOfPoint v) : ℝ) : ℂ) * Complex.I) := by
  have h := congrArg (starRingEnd ℂ) (Complex.norm_mul_exp_arg_mul_I (planeOfPoint v))
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I] at h
  have hc : starRingEnd ℂ (planeOfPoint v) = planeConj v := by
    simp only [planeOfPoint, planeConj, map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc] at h
  rw [← h]
  congr 2
  push_cast
  ring

theorem norm_sq_split (v : Space) : ‖v‖ ^ 2 = ‖planeOfPoint v‖ ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three, Complex.sq_norm, planeOfPoint, Complex.normSq_add_mul_I]
  simp [Real.norm_eq_abs, sq_abs]

theorem one_sub_height {v : Space} (hv : v ≠ 0) :
    1 - heightRatio v ^ 2 = ‖planeOfPoint v‖ ^ 2 / ‖v‖ ^ 2 := by
  have hn : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.2 hv)
  rw [eq_div_iff hn, sub_mul, one_mul, heightRatio, div_pow, div_mul_cancel₀ _ hn, norm_sq_split v]
  ring

theorem polarSine_eq {v : Space} (hv : v ≠ 0) : polarSine v = ‖planeOfPoint v‖ / ‖v‖ := by
  rw [polarSine, one_sub_height hv, ← div_pow, Real.sqrt_sq (div_nonneg (norm_nonneg _) (norm_nonneg _))]

theorem heightRatio_contDiffAt {v : Space} (hv : v ≠ 0) : ContDiffAt ℝ 2 heightRatio v :=
  ((EuclideanSpace.proj (2 : Fin 3) : Space →L[ℝ] ℝ).contDiff.contDiffAt (x := v)).div
    (contDiffAt_norm ℝ hv) (norm_ne_zero_iff.2 hv)

theorem heightRatio_axis {v : Space} (hv : v ≠ 0) (hw : planeOfPoint v = 0) :
    heightRatio v = 1 ∨ heightRatio v = -1 := by
  have h := one_sub_height hv
  rw [hw, norm_zero] at h
  have h2 : (heightRatio v - 1) * (heightRatio v + 1) = 0 := by
    have : heightRatio v ^ 2 = 1 := by
      have : (0 : ℝ) ^ 2 / ‖v‖ ^ 2 = 0 := by simp
      linarith
    linear_combination this
  rcases mul_eq_zero.1 h2 with h3 | h3
  · left
    linarith
  · right
    linarith

theorem heightRatio_smul {s : ℝ} (hs : 0 < s) (v : Space) : heightRatio (s • v) = heightRatio v := by
  simp only [heightRatio, PiLp.smul_apply, smul_eq_mul, norm_smul, Real.norm_of_nonneg hs.le]
  exact mul_div_mul_left _ _ hs.ne'

theorem pointAngle_smul {s : ℝ} (hs : 0 < s) (v : Space) : pointAngle (s • v) = pointAngle v := by
  simp only [pointAngle, PiLp.smul_apply, smul_eq_mul]
  rw [show (((s * v 0 : ℝ) : ℂ) + ((s * v 1 : ℝ) : ℂ) * Complex.I) =
      (s : ℂ) * (((v 0 : ℝ) : ℂ) + ((v 1 : ℝ) : ℂ) * Complex.I) by push_cast; ring]
  exact Complex.arg_real_mul _ hs

theorem polarSine_smul {s : ℝ} (hs : 0 < s) (v : Space) : polarSine (s • v) = polarSine v := by
  rw [polarSine, polarSine, heightRatio_smul hs]

theorem phaseRing_tame (j : ℤ) (w0 : ℂ) : TameNear (phaseRing j) w0 := by
  obtain ⟨K, t, ht, hK⟩ := planePhase_fderiv_localSlope j w0
  have e : phaseRing j = fun w : ℂ => ((‖w‖ ^ 2 : ℝ) : ℂ) *
      Complex.exp (Complex.I * (((j : ℝ) * Complex.arg w : ℝ) : ℂ)) := by
    funext w
    simp only [phaseRing, mul_comm Complex.I]
  rw [e]
  exact ⟨t, ht, fun q _ => ((planePhase_contDiff j).differentiable (by norm_num)) q, K, hK⟩

theorem normSq_pow_contDiffAt (k : ℕ) (w0 : ℂ) :
    ContDiffAt ℝ 2 (fun w : ℂ => (((‖w‖ ^ 2) ^ k : ℝ) : ℂ)) w0 :=
  ofReal_contDiffAt (((contDiff_norm_sq ℝ).contDiffAt).pow k)

theorem angular_tame_flat (ap : ℕ) {v0 : Space} (hv0 : v0 ≠ 0) : TameNear (angular 0 false ap) v0 := by
  have e : angular 0 false ap = fun v => (((1 - heightRatio v ^ 2) ^ ap : ℝ) : ℂ) := by
    funext v
    simp [angular]
  rw [e]
  exact tameNear_of_contDiffAt (ofReal_contDiffAt ((contDiffAt_const.sub ((heightRatio_contDiffAt hv0).pow 2)).pow ap))

theorem angular_tame_sine (M : ℤ) (hM : M = 1 ∨ M = -1) (ap : ℕ) {v0 : Space} (hv0 : v0 ≠ 0) :
    TameNear (angular M true ap) v0 := by
  have hq : ContDiffAt ℝ 2 (fun v => (((1 - heightRatio v ^ 2) ^ ap : ℝ) : ℂ)) v0 :=
    ofReal_contDiffAt ((contDiffAt_const.sub ((heightRatio_contDiffAt hv0).pow 2)).pow ap)
  have hr : ContDiffAt ℝ 2 (fun v : Space => ((‖v‖⁻¹ : ℝ) : ℂ)) v0 :=
    ofReal_contDiffAt ((contDiffAt_norm ℝ hv0).inv (norm_ne_zero_iff.2 hv0))
  rcases hM with rfl | rfl
  · refine tameNear_congr (tameNear_of_contDiffAt (hq.mul (planeOfPoint_contDiff.contDiffAt.mul hr))) ?_
    filter_upwards [isOpen_ne.mem_nhds hv0] with v hv
    have hw := Complex.norm_mul_exp_arg_mul_I (planeOfPoint v)
    simp only [angular, polarSine_eq hv, pointAngle_eq, Int.cast_one, one_mul]
    conv_rhs => rw [← hw]
    push_cast
    ring
  · refine tameNear_congr (tameNear_of_contDiffAt (hq.mul (planeConj_contDiff.contDiffAt.mul hr))) ?_
    filter_upwards [isOpen_ne.mem_nhds hv0] with v hv
    simp only [angular, polarSine_eq hv, pointAngle_eq, Int.cast_neg, Int.cast_one, neg_one_mul,
      planeConj_eq v]
    push_cast
    ring

theorem angular_tame_even (M : ℤ) {ap : ℕ} (hap : 1 ≤ ap) {v0 : Space} (hv0 : v0 ≠ 0) :
    TameNear (angular M false ap) v0 := by
  obtain ⟨k, rfl⟩ : ∃ k, ap = k + 1 := ⟨ap - 1, by omega⟩
  have hr : ContDiffAt ℝ 2 (fun v : Space => (((‖v‖ ^ (2 * (k + 1)))⁻¹ : ℝ) : ℂ)) v0 :=
    ofReal_contDiffAt (((contDiffAt_norm ℝ hv0).pow _).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hv0)))
  have hc : TameNear (fun w : ℂ => (((‖w‖ ^ 2) ^ k : ℝ) : ℂ) * phaseRing M w) (planeOfPoint v0) :=
    tameNear_mul (tameNear_of_contDiffAt (normSq_pow_contDiffAt k _)) (phaseRing_tame M _)
  have hcv := tameNear_comp hc (tameNear_of_contDiffAt (planeOfPoint_contDiff.contDiffAt (x := v0)))
  refine tameNear_congr (tameNear_mul (tameNear_of_contDiffAt hr) hcv) ?_
  filter_upwards [isOpen_ne.mem_nhds hv0] with v hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  simp only [angular, Bool.false_eq_true, if_false, mul_one, one_sub_height hv, phaseRing, pointAngle_eq]
  push_cast
  field_simp
  ring

theorem phaseRing_mul_plane (j : ℤ) (w : ℂ) :
    phaseRing (j - 1) w * w = ((‖w‖ ^ 3 : ℝ) : ℂ) * Complex.exp ((((j : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) := by
  calc phaseRing (j - 1) w * w = phaseRing (j - 1) w * ((‖w‖ : ℂ) * Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by
        rw [Complex.norm_mul_exp_arg_mul_I]
    _ = ((‖w‖ ^ 3 : ℝ) : ℂ) * (Complex.exp (((((j - 1 : ℤ) : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) *
          Complex.exp ((Complex.arg w : ℂ) * Complex.I)) := by
        simp only [phaseRing]
        push_cast
        ring
    _ = ((‖w‖ ^ 3 : ℝ) : ℂ) * Complex.exp ((((j : ℝ) * Complex.arg w : ℝ) : ℂ) * Complex.I) := by
        rw [← Complex.exp_add]
        congr 2
        push_cast
        ring

theorem angular_tame_odd (M : ℤ) {ap : ℕ} (hap : 1 ≤ ap) {v0 : Space} (hv0 : v0 ≠ 0) :
    TameNear (angular M true ap) v0 := by
  obtain ⟨k, rfl⟩ : ∃ k, ap = k + 1 := ⟨ap - 1, by omega⟩
  have hr : ContDiffAt ℝ 2 (fun v : Space => (((‖v‖ ^ (2 * (k + 1) + 1))⁻¹ : ℝ) : ℂ)) v0 :=
    ofReal_contDiffAt (((contDiffAt_norm ℝ hv0).pow _).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hv0)))
  have hc : TameNear (fun w : ℂ => (((‖w‖ ^ 2) ^ k : ℝ) : ℂ) * (phaseRing (M - 1) w * w)) (planeOfPoint v0) :=
    tameNear_mul (tameNear_of_contDiffAt (normSq_pow_contDiffAt k _))
      (tameNear_mul (phaseRing_tame (M - 1) _) (tameNear_of_contDiffAt contDiffAt_id))
  have hcv := tameNear_comp hc (tameNear_of_contDiffAt (planeOfPoint_contDiff.contDiffAt (x := v0)))
  refine tameNear_congr (tameNear_mul (tameNear_of_contDiffAt hr) hcv) ?_
  filter_upwards [isOpen_ne.mem_nhds hv0] with v hv
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  simp only [angular, one_sub_height hv, polarSine_eq hv, pointAngle_eq, phaseRing_mul_plane]
  push_cast
  field_simp
  ring

theorem angular_tame_off (M : ℤ) (ws : Bool) (ap : ℕ) {v0 : Space} (hw0 : planeOfPoint v0 ≠ 0) :
    TameNear (angular M ws ap) v0 := by
  have hv0 : v0 ≠ 0 := by
    rintro rfl
    exact hw0 (by simp [planeOfPoint])
  have hpc : ContinuousAt planeOfPoint v0 := planeOfPoint_contDiff.continuous.continuousAt
  have hwn : ContDiffAt ℝ 2 (fun v : Space => ‖planeOfPoint v‖) v0 :=
    (contDiffAt_norm ℝ hw0).comp v0 planeOfPoint_contDiff.contDiffAt
  have hinv : ContDiffAt ℝ 2 (fun v : Space => (((‖planeOfPoint v‖ ^ 2)⁻¹ : ℝ) : ℂ)) v0 :=
    ofReal_contDiffAt ((hwn.pow 2).inv (pow_ne_zero _ (norm_ne_zero_iff.2 hw0)))
  have hph := tameNear_comp (phaseRing_tame M (planeOfPoint v0))
    (tameNear_of_contDiffAt (planeOfPoint_contDiff.contDiffAt (x := v0)))
  have hq : ContDiffAt ℝ 2 (fun v => ((1 - heightRatio v ^ 2) ^ ap *
      (if ws then ‖planeOfPoint v‖ / ‖v‖ else 1) : ℝ)) v0 := by
    refine ((contDiffAt_const.sub ((heightRatio_contDiffAt hv0).pow 2)).pow ap).mul ?_
    cases ws
    · exact contDiffAt_const
    · exact hwn.div (contDiffAt_norm ℝ hv0) (norm_ne_zero_iff.2 hv0)
  refine tameNear_congr (tameNear_mul (tameNear_mul (tameNear_of_contDiffAt hinv) hph)
    (tameNear_of_contDiffAt (ofReal_contDiffAt hq))) ?_
  filter_upwards [hpc.eventually (isOpen_ne.mem_nhds hw0)] with v hv
  have hvv : v ≠ 0 := by
    rintro rfl
    exact hv (by simp [planeOfPoint])
  have hn : ‖planeOfPoint v‖ ≠ 0 := norm_ne_zero_iff.2 hv
  have hs : (if ws then polarSine v else 1) = (if ws then ‖planeOfPoint v‖ / ‖v‖ else 1) := by
    rw [polarSine_eq hvv]
  have hn' : ((‖planeOfPoint v‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  simp only [angular, phaseRing, hs, pointAngle_eq]
  push_cast
  field_simp

theorem angular_prod_tame {M : ℤ} {ws : Bool} {S : PotScalar} (hadm : AxisAdmissible M ws S)
    {Gf : ℝ × Space → ℂ} {p0 : ℝ × Space} (hv0 : p0.2 ≠ 0) (hG : TameNear Gf p0)
    (hvan : AxisCellsVanish S.amp → planeOfPoint p0.2 = 0 → Gf =ᶠ[𝓝 p0] 0) :
    TameNear (fun p => angular M ws S.axisPower p.2 * Gf p) p0 := by
  have lift : TameNear (angular M ws S.axisPower) p0.2 →
      TameNear (fun p => angular M ws S.axisPower p.2 * Gf p) p0 := fun hA =>
    tameNear_mul (tameNear_comp hA (tameNear_of_contDiffAt contDiffAt_snd)) hG
  by_cases hw : planeOfPoint p0.2 = 0
  · by_cases hap : 1 ≤ S.axisPower
    · apply lift
      cases ws
      · exact angular_tame_even M hap hv0
      · exact angular_tame_odd M hap hv0
    · by_cases hax : AxisCellsVanish S.amp
      · refine tameNear_congr (tameNear_of_contDiffAt (contDiffAt_const (c := (0 : ℂ)))) ?_
        filter_upwards [hvan hax hw] with p hp
        simp only [Pi.zero_apply] at hp
        simp [hp]
      · obtain ⟨h1, h2⟩ := hadm
        cases ws
        · have hM : M = 0 := by
            by_contra hM
            rcases h1 hM rfl with h | h
            · exact hap h
            · exact hax h
          subst hM
          exact lift (angular_tame_flat _ hv0)
        · have hM : M = 1 ∨ M = -1 := by
            by_contra hM
            have hM' : |M| ≠ 1 := fun h => hM ((abs_eq zero_le_one).1 h)
            rcases h2 rfl hM' with h | h
            · exact hap h
            · exact hax h
          exact lift (angular_tame_sine M hM _ hv0)
  · exact lift (angular_tame_off M ws S.axisPower hw)

end Angular

end Internal

end ScalarOrigin

end PotentialShape

end Breakdown
