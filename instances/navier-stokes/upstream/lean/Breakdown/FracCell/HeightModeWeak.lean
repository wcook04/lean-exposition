import Breakdown.FracCell.EnergyHeightParts
import Breakdown.FracCell.ModeHeightLine
import Breakdown.FracCell.CylModeWeak
import Breakdown.FracCell.LowEntry
import Breakdown.FracCell.ModeHeightAxis

open scoped ContDiff
open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.HeightModeWeak

open Breakdown.CellCert.CellAnalysis.Internal.ModeHeightLine

theorem tsupp_bound {χ : ℝ → ℝ} (h : HasCompactSupport χ) : ∃ R : ℝ, 0 < R ∧ tsupport χ ⊆ Ioo (-R) R := by
  obtain ⟨R, hR⟩ := h.isCompact.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun z hz => ?_⟩
  have h1 := hR hz
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := abs_le.mp (h1.trans (le_abs_self R))
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem interval_int {B : ℝ → ℂ} (hB : LocallyIntegrable B volume) (a b : ℝ) :
    IntervalIntegrable B volume a b :=
  (hB.integrableOn_isCompact isCompact_uIcc).intervalIntegrable

theorem cont_csupp_int {X : ℝ → ℂ} (hX : LocallyIntegrable X volume) {g : ℝ → ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) : Integrable (fun z => g z • X z) :=
  hX.integrable_smul_left_of_hasCompactSupport hg hgc

theorem prim_ibp {B : ℝ → ℂ} (hB : LocallyIntegrable B volume) {χ : ℝ → ℝ} (hχ : ContDiff ℝ ∞ χ)
    (hc : HasCompactSupport χ) :
    ∫ z, deriv χ z • (∫ u in (0 : ℝ)..z, B u) = -∫ z, χ z • B z := by
  obtain ⟨R, hR0, hR⟩ := tsupp_bound hc
  have hχ0 : ∀ z, z ∉ Ioo (-R) R → χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hR h))
  have hd0 : ∀ z, z ∉ Icc (-R) R → deriv χ z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (Ioo_subset_Icc_self (hR (tsupport_deriv_subset h))))
  have hC1 : ContDiff ℝ 1 χ := hχ.of_le (by exact_mod_cast le_top)
  have hdc : Continuous (deriv χ) := hC1.continuous_deriv le_rfl
  have L1 : ∫ z, deriv χ z • (∫ u in (0 : ℝ)..z, B u) = ∫ z in Icc (-R) R, deriv χ z • (∫ u in (0 : ℝ)..z, B u) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by simp [hd0 z hz])).symm
  have L2 : ∫ z, χ z • B z = ∫ z in Icc (-R) R, χ z • B z :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun z hz => by simp [hχ0 z (fun h => hz (Ioo_subset_Icc_self h))])).symm
  rw [L1, L2]
  have hBI : IntegrableOn B (Icc (-R) R) := hB.integrableOn_isCompact isCompact_Icc
  have hR' : -R ≤ R := by linarith
  have hPc : Continuous (fun z => ∫ u in (-R)..z, B u) := intervalIntegral.continuous_primitive (interval_int hB) _
  have e : ∀ z, deriv χ z • (∫ u in (0 : ℝ)..z, B u) =
      (∫ u in (-R)..z, B u) * ((deriv χ z : ℝ) : ℂ) - (∫ u in (-R)..0, B u) * ((deriv χ z : ℝ) : ℂ) := by
    intro z
    rw [← intervalIntegral.integral_interval_sub_left (interval_int hB _ _) (interval_int hB _ _), Complex.real_smul]
    ring
  simp_rw [e]
  have hdC : Continuous (fun z => ((deriv χ z : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hdc
  have j1 : IntegrableOn (fun z => (∫ u in (-R)..z, B u) * ((deriv χ z : ℝ) : ℂ)) (Icc (-R) R) :=
    (hPc.mul hdC).continuousOn.integrableOn_compact isCompact_Icc
  have j2 : IntegrableOn (fun z => (∫ u in (-R)..0, B u) * ((deriv χ z : ℝ) : ℂ)) (Icc (-R) R) :=
    (continuous_const.mul hdC).continuousOn.integrableOn_compact isCompact_Icc
  rw [integral_sub j1 j2,
    primitive_ibp_real hR' hBI hC1 (hχ0 R (fun h => lt_irrefl _ h.2)), integral_const_mul]
  have hz : ∫ z in Icc (-R) R, ((deriv χ z : ℝ) : ℂ) = 0 := by
    rw [integral_complex_ofReal, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hR',
      intervalIntegral.integral_deriv_eq_sub' χ rfl (fun x _ => (hC1.differentiable one_ne_zero).differentiableAt)
        hdc.continuousOn, hχ0 R (fun h => lt_irrefl _ h.2), hχ0 (-R) (fun h => lt_irrefl _ h.1)]
    simp
  rw [hz, mul_zero, sub_zero]
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
  rw [Complex.real_smul, mul_comm]

theorem one_dim {B C : ℝ → ℂ} (hB : LocallyIntegrable B volume) (hC : LocallyIntegrable C volume)
    (hyp : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ z, deriv χ z • C z = -∫ z, χ z • B z)
    {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) (s : ℝ → ℝ) (hs : ContDiff ℝ 1 s) (hs1 : s z₁ = 0) (hs2 : s z₂ = 0) :
    ∫ z in Icc z₁ z₂, (s z • B z + deriv s z • C z) = 0 := by
  set P : ℝ → ℂ := fun z => ∫ u in (0 : ℝ)..z, B u with hP
  have hPc : Continuous P := intervalIntegral.continuous_primitive (interval_int hB) 0
  have hX : LocallyIntegrable (fun z => C z - P z) volume := hC.sub hPc.locallyIntegrable
  have hE : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ → ∫ z, deriv χ z • (C z - P z) = 0 := by
    intro χ hχ hc
    have hdc : Continuous (deriv χ) := hχ.continuous_deriv (by exact_mod_cast le_top)
    have hdcs : HasCompactSupport (deriv χ) := hc.deriv
    simp_rw [smul_sub]
    rw [integral_sub (cont_csupp_int hC hdc hdcs) (cont_csupp_int hPc.locallyIntegrable hdc hdcs), hyp χ hχ hc,
      prim_ibp hB hχ hc]
    ring
  let η : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, one_lt_two⟩
  set e : ℝ → ℝ := η.normed volume with he_def
  have he : ContDiff ℝ ∞ e := η.contDiff_normed
  have hec : HasCompactSupport e := η.hasCompactSupport_normed
  have he1 : ∫ z, e z = 1 := η.integral_normed
  set c : ℂ := ∫ z, e z • (C z - P z) with hc_def
  have hloc : LocallyIntegrable (fun z => C z - P z - c) volume := hX.sub (locallyIntegrable_const c)
  have hae := ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · have hCe : ∀ᵐ z ∂(volume.restrict (Icc z₁ z₂)), s z • B z + deriv s z • C z =
        (s z • B z + deriv s z • (∫ u in z₁..z, B u)) + deriv s z • ((∫ u in (0 : ℝ)..z₁, B u) + c) := by
      refine ae_restrict_of_ae (hae.mono fun z hz => ?_)
      have h1 : C z = P z + c := by linear_combination hz
      rw [h1, hP]
      simp only
      rw [← intervalIntegral.integral_add_adjacent_intervals (interval_int hB 0 z₁) (interval_int hB z₁ z)]
      simp only [smul_add]
      ring
    rw [integral_congr_ae hCe]
    have hBI : IntegrableOn B (Icc z₁ z₂) := hB.integrableOn_isCompact isCompact_Icc
    have hsc : Continuous s := hs.continuous
    have hdsc : Continuous (deriv s) := hs.continuous_deriv le_rfl
    have hPc1 : Continuous (fun z => ∫ u in z₁..z, B u) := intervalIntegral.continuous_primitive (interval_int hB) _
    have iA : IntegrableOn (fun z => s z • B z) (Icc z₁ z₂) := by
      simp_rw [Complex.real_smul]
      exact hBI.continuousOn_mul (Complex.continuous_ofReal.comp hsc).continuousOn isCompact_Icc
    have iB : IntegrableOn (fun z => deriv s z • (∫ u in z₁..z, B u)) (Icc z₁ z₂) :=
      (hdsc.smul hPc1).continuousOn.integrableOn_compact isCompact_Icc
    have iC : IntegrableOn (fun z => deriv s z • ((∫ u in (0 : ℝ)..z₁, B u) + c)) (Icc z₁ z₂) :=
      (hdsc.smul continuous_const).continuousOn.integrableOn_compact isCompact_Icc
    have iAB : IntegrableOn (fun z => s z • B z + deriv s z • (∫ u in z₁..z, B u)) (Icc z₁ z₂) := iA.add iB
    rw [integral_add iAB iC, integral_add iA iB, integral_smul_const]
    have hds : ∫ z in Icc z₁ z₂, deriv s z = 0 := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hz,
        intervalIntegral.integral_deriv_eq_sub' s rfl (fun x _ => (hs.differentiable one_ne_zero).differentiableAt)
          hdsc.continuousOn, hs1, hs2, sub_zero]
    have hpr := primitive_ibp_real hz hBI hs hs2
    have e2 : ∫ z in Icc z₁ z₂, deriv s z • (∫ u in z₁..z, B u) =
        ∫ z in Icc z₁ z₂, (∫ u in z₁..z, B u) * ((deriv s z : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
      rw [Complex.real_smul, mul_comm]
    have e1 : ∫ z in Icc z₁ z₂, s z • B z = ∫ z in Icc z₁ z₂, B z * ((s z : ℝ) : ℂ) := by
      refine setIntegral_congr_fun measurableSet_Icc (fun z _ => ?_)
      rw [Complex.real_smul, mul_comm]
    rw [hds, zero_smul, add_zero, e2, hpr, e1]
    ring
  intro g hg hgc
  set mg : ℝ := ∫ z, g z with hmg
  set q : ℝ → ℝ := fun z => g z - mg * e z with hq_def
  have hq : ContDiff ℝ ∞ q := hg.sub (contDiff_const.mul he)
  have hqc : HasCompactSupport q := hgc.sub (hec.mul_left)
  obtain ⟨R, hR0, hR⟩ := tsupp_bound hqc
  have hq0 : ∀ z, z ∉ Ioo (-R) R → q z = 0 := fun z hz =>
    image_eq_zero_of_notMem_tsupport (fun h => hz (hR h))
  set h : ℝ → ℝ := fun z => ∫ u in (-R)..z, q u with hh_def
  have hder : ∀ z, HasDerivAt h (q z) z := fun z =>
    (hq.continuous.integral_hasStrictDerivAt (-R) z).hasDerivAt
  have hderiv : deriv h = q := funext fun z => (hder z).deriv
  have hhs : ContDiff ℝ ∞ h :=
    contDiff_infty_iff_deriv.2 ⟨fun z => (hder z).differentiableAt, by rw [hderiv]; exact hq⟩
  have hgI : Integrable g := hg.continuous.integrable_of_hasCompactSupport hgc
  have heI : Integrable e := he.continuous.integrable_of_hasCompactSupport hec
  have hqint : ∫ z, q z = 0 := by
    rw [integral_sub hgI (heI.const_mul mg), integral_const_mul, he1]
    ring
  have hhc : HasCompactSupport h := by
    refine HasCompactSupport.intro (isCompact_Icc (a := -R) (b := R)) (fun z hz => ?_)
    simp only [mem_Icc, not_and_or, not_le] at hz
    rcases hz with hz | hz
    · show ∫ u in (-R)..z, q u = 0
      rw [intervalIntegral.integral_symm, intervalIntegral.integral_of_le hz.le, neg_eq_zero]
      rw [setIntegral_congr_fun measurableSet_Ioc (g := fun _ => (0 : ℝ))
        (fun u hu => hq0 u (fun h' => by linarith [hu.2, h'.1]))]
      simp
    · show ∫ u in (-R)..z, q u = 0
      rw [intervalIntegral.integral_of_le (by linarith),
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun u hu => hq0 u (fun h' => hu (show u ∈ Ioc (-R) z from ⟨h'.1, by linarith [h'.2]⟩))),
        hqint]
  have key := hE h hhs hhc
  rw [hderiv] at key
  have iG : Integrable (fun z => g z • (C z - P z)) := cont_csupp_int hX hg.continuous hgc
  have iE : Integrable (fun z => e z • (C z - P z)) := cont_csupp_int hX he.continuous hec
  have k2 : ∫ z, q z • (C z - P z) = (∫ z, g z • (C z - P z)) - mg • c := by
    simp_rw [hq_def, sub_smul, mul_smul]
    have iE' : Integrable (fun z => mg • (e z • (C z - P z))) := iE.smul mg
    rw [integral_sub iG iE', integral_smul]
  rw [k2, sub_eq_zero] at key
  have iGc : Integrable (fun z => g z • c) := hgI.smul_const c
  rw [show (fun z => g z • (C z - P z - c)) = fun z => g z • (C z - P z) - g z • c from
    funext fun z => smul_sub _ _ _, integral_sub iG iGc, key, integral_smul_const, sub_self]

end Breakdown.FracInternal.HeightModeWeak

namespace Breakdown.FracInternal.HeightModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert

theorem restrict_prod_eq (A B : Set ℝ) :
    volume.restrict (A ×ˢ B) = (volume.restrict A).prod (volume.restrict B) := by
  rw [Measure.volume_eq_prod, Measure.prod_restrict]

theorem iter_z {f : ℝ × ℝ → ℂ} {A B : Set ℝ} (hf : IntegrableOn f (A ×ˢ B)) :
    ∫ p in A ×ˢ B, f p = ∫ z in B, ∫ r in A, f (r, z) := by
  unfold IntegrableOn at hf
  rw [restrict_prod_eq] at hf ⊢
  exact integral_prod_symm f hf

theorem iter_r {f : ℝ × ℝ → ℂ} {A B : Set ℝ} (hf : IntegrableOn f (A ×ˢ B)) :
    ∫ p in A ×ˢ B, f p = ∫ r in A, ∫ z in B, f (r, z) := by
  unfold IntegrableOn at hf
  rw [restrict_prod_eq] at hf ⊢
  exact integral_prod f hf

theorem slice_int {f : ℝ × ℝ → ℂ} {A B : Set ℝ} (hf : IntegrableOn f (A ×ˢ B)) :
    IntegrableOn (fun r => ∫ z in B, f (r, z)) A := by
  unfold IntegrableOn at hf
  rw [restrict_prod_eq] at hf
  exact hf.integral_prod_left

theorem slice_int' {f : ℝ × ℝ → ℂ} {A B : Set ℝ} (hf : IntegrableOn f (A ×ˢ B)) :
    IntegrableOn (fun z => ∫ r in A, f (r, z)) B := by
  unfold IntegrableOn at hf
  rw [restrict_prod_eq] at hf
  exact hf.integral_prod_right

theorem box_mul {F : ℝ × ℝ → ℂ} {A B : Set ℝ} (hA : IsCompact A) (hB : IsCompact B)
    (hF : IntegrableOn F (A ×ˢ B)) {k : ℝ × ℝ → ℝ} (hk : Continuous k) :
    IntegrableOn (fun p => ((k p : ℝ) : ℂ) * F p) (A ×ˢ B) :=
  hF.continuousOn_mul (Complex.continuous_ofReal.comp hk).continuousOn (hA.prod hB)

theorem bounded_box {k : Set ℝ} (hk : IsCompact k) : ∃ R : ℝ, 0 < R ∧ k ⊆ Icc (-R) R := by
  obtain ⟨R, hR⟩ := hk.isBounded.subset_closedBall 0
  refine ⟨|R| + 1, by positivity, fun z hz => ?_⟩
  have h1 := hR hz
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h1
  have h2 := abs_le.mp (h1.trans (le_abs_self R))
  exact ⟨by linarith [h2.1], by linarith [h2.2]⟩

theorem slice_zero {Fw Dw : ℝ × ℝ → ℂ} (hF : ∀ R Z : ℝ, IntegrableOn Fw (Icc 0 R ×ˢ Icc (-Z) Z))
    (hD : ∀ R Z : ℝ, IntegrableOn Dw (Icc 0 R ×ˢ Icc (-Z) Z))
    (hw : ∀ φ χ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ p, ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = -∫ p, ((φ p.1 * χ p.2 : ℝ) : ℂ) * Dw p)
    {z₁ z₂ : ℝ} (hz : z₁ ≤ z₂) (s : ℝ → ℝ) (hs : ContDiff ℝ 1 s) (hs1 : s z₁ = 0) (hs2 : s z₂ = 0) :
    ∀ᵐ r, r ∈ Ioi (0 : ℝ) →
      ∫ z in Icc z₁ z₂, (((s z : ℝ) : ℂ) * Dw (r, z) + ((deriv s z : ℝ) : ℂ) * Fw (r, z)) = 0 := by
  have hsc : Continuous s := hs.continuous
  have hdsc : Continuous (deriv s) := hs.continuous_deriv le_rfl
  set Z₀ : ℝ := |z₁| + |z₂| with hZ₀
  have hI : Icc z₁ z₂ ⊆ Icc (-Z₀) Z₀ := fun z hz' => by
    constructor <;> linarith [hz'.1, hz'.2, abs_nonneg z₁, abs_nonneg z₂, neg_abs_le z₁, le_abs_self z₂]
  set Gf : ℝ × ℝ → ℂ := fun p => ((s p.2 : ℝ) : ℂ) * Dw p + ((deriv s p.2 : ℝ) : ℂ) * Fw p with hGf
  have hGbox : ∀ R, IntegrableOn Gf (Icc 0 R ×ˢ Icc z₁ z₂) := by
    intro R
    have hsub : Icc 0 R ×ˢ Icc z₁ z₂ ⊆ Icc 0 R ×ˢ Icc (-Z₀) Z₀ := prod_mono le_rfl hI
    exact (box_mul isCompact_Icc isCompact_Icc ((hD R Z₀).mono_set hsub) (hsc.comp continuous_snd)).add
      (box_mul isCompact_Icc isCompact_Icc ((hF R Z₀).mono_set hsub) (hdsc.comp continuous_snd))
  set Φ : ℝ → ℂ := fun r => ∫ z in Icc z₁ z₂, Gf (r, z) with hΦ
  have hΦint : ∀ R, IntegrableOn Φ (Icc 0 R) := fun R => slice_int (hGbox R)
  have hloc : LocallyIntegrableOn Φ (Ioi 0) := by
    refine (locallyIntegrableOn_iff isOpen_Ioi.isLocallyClosed).2 fun k hk hkc => ?_
    obtain ⟨R, _, hR⟩ := bounded_box hkc
    exact (hΦint R).mono_set fun r hr => ⟨le_of_lt (hk hr), (hR hr).2⟩
  have := isOpen_Ioi.ae_eq_zero_of_integral_contDiff_smul_eq_zero hloc ?_
  · exact this
  intro g hg hgc hgs
  obtain ⟨R, _, hR⟩ := bounded_box hgc.isCompact
  have hg0 : ∀ r, r ∉ Icc 0 R → g r = 0 := fun r hr => image_eq_zero_of_notMem_tsupport (fun h' =>
    hr ⟨le_of_lt (hgs h'), (hR h').2⟩)
  have hgcC : Continuous (fun r => ((g r : ℝ) : ℂ)) := Complex.continuous_ofReal.comp hg.continuous
  set Cg : ℝ → ℂ := fun z => ∫ r in Icc 0 R, ((g r : ℝ) : ℂ) * Fw (r, z) with hCg
  set Bg : ℝ → ℂ := fun z => ∫ r in Icc 0 R, ((g r : ℝ) : ℂ) * Dw (r, z) with hBg
  have hCl : LocallyIntegrable Cg volume := by
    refine (locallyIntegrable_iff).2 fun k hk => ?_
    obtain ⟨Z, _, hZ⟩ := bounded_box hk
    exact (slice_int' (f := fun p => ((g p.1 : ℝ) : ℂ) * Fw p)
      (box_mul isCompact_Icc isCompact_Icc (hF R Z) (hg.continuous.comp continuous_fst))).mono_set hZ
  have hBl : LocallyIntegrable Bg volume := by
    refine (locallyIntegrable_iff).2 fun k hk => ?_
    obtain ⟨Z, _, hZ⟩ := bounded_box hk
    exact (slice_int' (f := fun p => ((g p.1 : ℝ) : ℂ) * Dw p)
      (box_mul isCompact_Icc isCompact_Icc (hD R Z) (hg.continuous.comp continuous_fst))).mono_set hZ
  have hyp : ∀ χ : ℝ → ℝ, ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ z, deriv χ z • Cg z = -∫ z, χ z • Bg z := by
    intro χ hχ hχc
    obtain ⟨Z, _, hZ⟩ := bounded_box hχc.isCompact
    have hχ0 : ∀ z, z ∉ Icc (-Z) Z → χ z = 0 := fun z hz' => image_eq_zero_of_notMem_tsupport (fun h' => hz' (hZ h'))
    have hd0 : ∀ z, z ∉ Icc (-Z) Z → deriv χ z = 0 := fun z hz' =>
      image_eq_zero_of_notMem_tsupport (fun h' => hz' (hZ (tsupport_deriv_subset h')))
    have hdχ : Continuous (deriv χ) := hχ.continuous_deriv (by exact_mod_cast le_top)
    have key := hw g χ hg hgc hgs hχ hχc
    have e1 : ∫ p, ((g p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = ∫ z, deriv χ z • Cg z := by
      have hout : ∀ p, p ∉ Icc 0 R ×ˢ Icc (-Z) Z → ((g p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = 0 := by
        intro p hp
        rcases not_and_or.1 hp with h' | h'
        · simp [hg0 _ h']
        · simp [hd0 _ h']
      have hint : IntegrableOn (fun p => ((g p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p) (Icc 0 R ×ˢ Icc (-Z) Z) :=
        box_mul isCompact_Icc isCompact_Icc (hF R Z) ((hg.continuous.comp continuous_fst).mul (hdχ.comp continuous_snd))
      have L : ∫ z, deriv χ z • Cg z = ∫ z in Icc (-Z) Z, deriv χ z • Cg z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz' => by simp [hd0 z hz'])).symm
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, iter_z hint, L]
      refine setIntegral_congr_fun measurableSet_Icc fun z _ => ?_
      simp only [hCg, Complex.real_smul]
      rw [← integral_const_mul]
      congr 1
      funext r
      push_cast
      ring
    have e2 : ∫ p, ((g p.1 * χ p.2 : ℝ) : ℂ) * Dw p = ∫ z, χ z • Bg z := by
      have hout : ∀ p, p ∉ Icc 0 R ×ˢ Icc (-Z) Z → ((g p.1 * χ p.2 : ℝ) : ℂ) * Dw p = 0 := by
        intro p hp
        rcases not_and_or.1 hp with h' | h'
        · simp [hg0 _ h']
        · simp [hχ0 _ h']
      have hint : IntegrableOn (fun p => ((g p.1 * χ p.2 : ℝ) : ℂ) * Dw p) (Icc 0 R ×ˢ Icc (-Z) Z) :=
        box_mul isCompact_Icc isCompact_Icc (hD R Z) ((hg.continuous.comp continuous_fst).mul (hχ.continuous.comp continuous_snd))
      have L : ∫ z, χ z • Bg z = ∫ z in Icc (-Z) Z, χ z • Bg z :=
        (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz' => by simp [hχ0 z hz'])).symm
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout, iter_z hint, L]
      refine setIntegral_congr_fun measurableSet_Icc fun z _ => ?_
      simp only [hBg, Complex.real_smul]
      rw [← integral_const_mul]
      congr 1
      funext r
      push_cast
      ring
    rw [← e1, ← e2]
    exact key
  have h1 := one_dim hBl hCl hyp hz s hs hs1 hs2
  have hout : ∀ r, r ∉ Icc 0 R → g r • Φ r = 0 := fun r hr => by simp [hg0 r hr]
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hout]
  have hsub : Icc 0 R ×ˢ Icc z₁ z₂ ⊆ Icc 0 R ×ˢ Icc (-Z₀) Z₀ := prod_mono le_rfl hI
  have iD : IntegrableOn (fun p => ((g p.1 * s p.2 : ℝ) : ℂ) * Dw p) (Icc 0 R ×ˢ Icc z₁ z₂) :=
    box_mul isCompact_Icc isCompact_Icc ((hD R Z₀).mono_set hsub) ((hg.continuous.comp continuous_fst).mul (hsc.comp continuous_snd))
  have iF : IntegrableOn (fun p => ((g p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) (Icc 0 R ×ˢ Icc z₁ z₂) :=
    box_mul isCompact_Icc isCompact_Icc ((hF R Z₀).mono_set hsub) ((hg.continuous.comp continuous_fst).mul (hdsc.comp continuous_snd))
  have e3 : ∫ r in Icc 0 R, g r • Φ r =
      ∫ p in Icc 0 R ×ˢ Icc z₁ z₂, (((g p.1 * s p.2 : ℝ) : ℂ) * Dw p + ((g p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) := by
    have iDF : IntegrableOn (fun p => ((g p.1 * s p.2 : ℝ) : ℂ) * Dw p + ((g p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p)
        (Icc 0 R ×ˢ Icc z₁ z₂) := iD.add iF
    rw [iter_r iDF]
    refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
    simp only [hΦ, hGf, Complex.real_smul]
    rw [← integral_const_mul]
    congr 1
    funext z
    push_cast
    ring
  rw [e3, integral_add iD iF, iter_z iD, iter_z iF, ← h1, ← integral_add]
  · refine setIntegral_congr_fun measurableSet_Icc fun z _ => ?_
    simp only [hBg, hCg, Complex.real_smul]
    rw [← integral_const_mul, ← integral_const_mul]
    congr 1 <;> (congr 1; funext r; push_cast; ring)
  · exact slice_int' iD
  · exact slice_int' iF

end Breakdown.FracInternal.HeightModeWeak

namespace Breakdown.FracInternal.HeightModeWeak

open Breakdown.CellCert Breakdown.CellCert.CellAnalysis Breakdown.SteadyCert Breakdown.CellCert.CellFormula

def unitAt (q : ℝ × ℝ) : Fin 3 → Space :=
  ![EuclideanSpace.single 0 q.1 + EuclideanSpace.single 1 q.2,
    EuclideanSpace.single 0 (-q.2) + EuclideanSpace.single 1 q.1, axialUnit]

theorem unitAt_circle (θ : ℝ) : unitAt (Real.cos θ, Real.sin θ) = frameUnit θ := rfl

def angQ (a : Fin 3) (q : ℝ × ℝ) : Space →L[ℝ] ℝ :=
  ∑ k : Fin 3, unitAt q a k • EuclideanSpace.proj k

theorem angQ_circle (a : Fin 3) (θ : ℝ) (u : Space) :
    angQ a (Real.cos θ, Real.sin θ) u = inner ℝ u (frameUnit θ a) := by
  simp [angQ, unitAt_circle, PiLp.inner_apply, Fin.sum_univ_three, mul_comm]

theorem unitAt_coord_smooth (a k : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a k) := by
  fin_cases a <;> fin_cases k <;>
    simp [unitAt, axialUnit] <;>
    first | exact contDiff_const | exact contDiff_fst | exact contDiff_snd | exact contDiff_snd.neg

theorem unitAt_smooth (a : Fin 3) : ContDiff ℝ ∞ (fun q : ℝ × ℝ => unitAt q a) :=
  (contDiff_piLp 2).2 fun k => unitAt_coord_smooth a k

theorem angQ_smooth (a : Fin 3) : ContDiff ℝ ∞ (angQ a) := by
  unfold angQ
  exact ContDiff.sum fun k _ => (unitAt_coord_smooth a k).smul contDiff_const

def colQ (a b : Fin 3) (q : ℝ × ℝ) : (Space →L[ℝ] Space) →L[ℝ] ℝ :=
  (angQ a q).comp (ContinuousLinearMap.apply ℝ Space (unitAt q b))

theorem colQ_smooth (a b : Fin 3) : ContDiff ℝ ∞ (colQ a b) :=
  (angQ_smooth a).clm_comp ((ContinuousLinearMap.apply ℝ Space).contDiff.comp (unitAt_smooth b))

theorem colQ_circle (a b : Fin 3) (θ : ℝ) (M : Space →L[ℝ] Space) :
    colQ a b (Real.cos θ, Real.sin θ) M = inner ℝ (M (frameUnit θ b)) (frameUnit θ a) := by
  simp only [colQ, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply]
  rw [angQ_circle, unitAt_circle]

theorem vec_expand (u : Space) : u = ∑ j : Fin 3, u j • unitVector j := by
  ext i; fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem norm_le_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (A : Space →L[ℝ] E) :
    ‖A‖ ≤ ∑ i : Fin 3, ‖A (unitVector i)‖ := by
  refine A.opNorm_le_bound (Finset.sum_nonneg fun _ _ => norm_nonneg _) fun u => ?_
  conv_lhs => rw [vec_expand u]
  rw [map_sum, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [map_smul, norm_smul, mul_comm]
  exact mul_le_mul_of_nonneg_left (PiLp.norm_apply_le u i) (norm_nonneg _)

theorem loc_norm {E : Type} [NormedAddCommGroup E] {f : Space → E} (hf : LocallyIntegrable f volume) :
    LocallyIntegrable (fun y => ‖f y‖) volume :=
  hf.mono hf.aestronglyMeasurable.norm (Filter.Eventually.of_forall fun y => by simp)

theorem loc_of_cols {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {A : Space → (Space →L[ℝ] E)} (hm : AEStronglyMeasurable A volume)
    (hc : ∀ i, LocallyIntegrable (fun y => A y (unitVector i)) volume) : LocallyIntegrable A volume := by
  have hs : LocallyIntegrable (fun y => ∑ i : Fin 3, ‖A y (unitVector i)‖) volume := by
    simp only [Fin.sum_univ_three]
    exact ((loc_norm (hc 0)).add (loc_norm (hc 1))).add (loc_norm (hc 2))
  refine hs.mono hm (Filter.Eventually.of_forall fun y => ?_)
  refine (norm_le_cols (A y)).trans (le_of_eq ?_)
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)]

theorem memLp_col {G : Space → (Space →L[ℝ] Space)} (hm : AEStronglyMeasurable G volume)
    (hi : Integrable (fun y => entrySq (G y))) (j : Fin 3) : MemLp (fun y => G y (unitVector j)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => G y (unitVector j)) volume :=
    hm.apply_continuousLinearMap (unitVector j)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  unfold entrySq
  exact Finset.single_le_sum (f := fun i => ‖G y (unitVector i)‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ j)

theorem memLp_col2 {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hm : AEStronglyMeasurable H volume)
    (hi : Integrable (fun y => ∑ i : Fin 3, ∑ j : Fin 3, ‖H y (unitVector i) (unitVector j)‖ ^ 2)) (j i : Fin 3) :
    MemLp (fun y => H y (unitVector j) (unitVector i)) 2 volume := by
  have hmj : AEStronglyMeasurable (fun y => H y (unitVector j) (unitVector i)) volume :=
    (hm.apply_continuousLinearMap (unitVector j)).apply_continuousLinearMap (unitVector i)
  refine (memLp_two_iff_integrable_sq_norm hmj).2 (hi.mono' (hmj.norm.pow 2) (Filter.Eventually.of_forall fun y => ?_))
  simp only [Real.norm_eq_abs, abs_pow, sq_abs]
  calc ‖H y (unitVector j) (unitVector i)‖ ^ 2 ≤ ∑ i' : Fin 3, ‖H y (unitVector j) (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun i' => ‖H y (unitVector j) (unitVector i')‖ ^ 2) (fun _ _ => by positivity)
          (Finset.mem_univ i)
    _ ≤ ∑ j' : Fin 3, ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2 :=
        Finset.single_le_sum (f := fun j' => ∑ i' : Fin 3, ‖H y (unitVector j') (unitVector i')‖ ^ 2)
          (fun _ _ => Finset.sum_nonneg fun _ _ => by positivity) (Finset.mem_univ j)

theorem scale {A B c d : ℝ × ℝ → ℂ} (k : ℂ) (h : ∫ p, c p * A p = -∫ p, d p * B p) :
    ∫ p, c p * (k * A p) = -∫ p, d p * (k * B p) := by
  have e1 : (fun p => c p * (k * A p)) = fun p => k * (c p * A p) := funext fun p => by ring
  have e2 : (fun p => d p * (k * B p)) = fun p => k * (d p * B p) := funext fun p => by ring
  rw [e1, e2, integral_const_mul, integral_const_mul, h, mul_neg]

theorem weak_smooth {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (ψ : ℝ × ℝ → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hc : HasCompactSupport ψ) (hpos : ∀ p ∈ tsupport ψ, 0 < p.1) :
    ∫ p, ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p =
      -∫ p, (ψ p : ℂ) * modeThird m n H a b 2 p := by
  have hGc : ∀ j, LocallyIntegrable (fun y => G y (unitVector j)) volume := fun j =>
    (memLp_col hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)
  have hG : LocallyIntegrable G volume := loc_of_cols hs.measurable_gradient hGc
  have hHc : ∀ j, LocallyIntegrable (fun y => H y (unitVector j)) volume := fun j =>
    loc_of_cols (hs.measurable_second.apply_continuousLinearMap (unitVector j)) fun i =>
      (memLp_col2 hs.measurable_second hs.second_two j i).locallyIntegrable (by norm_num)
  have hweakG : ∀ φ : Space → ℝ, IsTestScalar φ → ∀ j : Fin 3,
      ∫ y, fderiv ℝ φ y (unitVector j) • G y = -∫ y, φ y • H y (unitVector j) := by
    intro φ hφ j
    have hd : Continuous (fun y => fderiv ℝ φ y (unitVector j)) :=
      (hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const
    have i1 : Integrable (fun y => fderiv ℝ φ y (unitVector j) • G y) volume :=
      hG.integrable_smul_left_of_hasCompactSupport hd (hφ.2.fderiv_apply (𝕜 := ℝ) _)
    have i2 : Integrable (fun y => φ y • H y (unitVector j)) volume :=
      (hHc j).integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2
    have key : ∀ i, (∫ y, fderiv ℝ φ y (unitVector j) • G y) (unitVector i) =
        (-∫ y, φ y • H y (unitVector j)) (unitVector i) := by
      intro i
      rw [neg_apply, ContinuousLinearMap.integral_apply i1, ContinuousLinearMap.integral_apply i2]
      simpa using hs.weak_second φ hφ i j
    refine ContinuousLinearMap.ext fun u => ?_
    rw [vec_expand u]
    simp only [map_sum, map_smul, key]
  have hgm : ∀ p : ℝ × ℝ, gradMode m n G a b p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (colQ a b (Real.cos θ, Real.sin θ) (G (cylPoint p.1 θ p.2)) : ℂ) := by
    intro p
    simp only [gradMode, modeMat, colQ_circle]
    rfl
  have hth : ∀ p : ℝ × ℝ, modeThird m n H a b 2 p = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (colQ a b (Real.cos θ, Real.sin θ) (H (cylPoint p.1 θ p.2) axialUnit) : ℂ) := by
    intro p
    simp only [modeThird, colQ_circle]
    rfl
  simp only [hth, hgm]
  exact scale _ (cylModeWeak (Space →L[ℝ] Space) G H hG hHc hweakG (colQ a b) (colQ_smooth a b) m n ψ
    hψ hc hpos).2

theorem weighted_modes {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (R Z : ℝ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p) (Icc 0 R ×ˢ Icc (-Z) Z) ∧
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b 2 p) (Icc 0 R ×ˢ Icc (-Z) Z) := by
  have hGl : LocallyIntegrable G volume := loc_of_cols hs.measurable_gradient fun j =>
    (memLp_col hs.measurable_gradient hs.gradient_two j).locallyIntegrable (by norm_num)
  have hHl : LocallyIntegrable (fun y => H y axialUnit) volume :=
    loc_of_cols (hs.measurable_second.apply_continuousLinearMap (unitVector 2)) fun i =>
      (memLp_col2 hs.measurable_second hs.second_two 2 i).locallyIntegrable (by norm_num)
  have w1 := FracInternal.ModeHeightAxis.weighted_int R Z hGl (LowEntry.Internal.gradKernel m n a b)
    (LowEntry.Internal.gradKernel_cont m n a b) (LowEntry.Internal.gradKernel_bound m n a b)
  have w2 := FracInternal.ModeHeightAxis.weighted_int R Z hHl (LowEntry.Internal.gradKernel m n a b)
    (LowEntry.Internal.gradKernel_cont m n a b) (LowEntry.Internal.gradKernel_bound m n a b)
  have hthird : ∀ p, modeThird m n H a b 2 p = gradMode m n (fun y => H y axialUnit) a b p := fun p => rfl
  constructor
  · have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * gradMode m n G a b p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi, LowEntry.Internal.gradKernel m n a b θ (G (cylPoint p.1 θ p.2))) := by
      funext p; rw [LowEntry.Internal.gradMode_eq]; ring
    rw [e]
    exact w1.const_mul _
  · have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * modeThird m n H a b 2 p) = fun p => (1 / (2 * Real.pi) : ℂ) *
        ((p.1 : ℂ) * ∫ θ in Ioo (-Real.pi) Real.pi,
          LowEntry.Internal.gradKernel m n a b θ (H (cylPoint p.1 θ p.2) axialUnit)) := by
      funext p; rw [hthird, LowEntry.Internal.gradMode_eq]; ring
    rw [e]
    exact w2.const_mul _

theorem prod_fderiv {u χ : ℝ → ℝ} (hu : ContDiff ℝ ∞ u) (hχ : ContDiff ℝ ∞ χ) (p : ℝ × ℝ) :
    fderiv ℝ (fun q : ℝ × ℝ => u q.1 * χ q.2) p (0, 1) = u p.1 * deriv χ p.2 := by
  have h1 : HasFDerivAt (fun q : ℝ × ℝ => u q.1) ((fderiv ℝ u p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p :=
    ((hu.differentiable (by simp)) p.1).hasFDerivAt.comp p hasFDerivAt_fst
  have h2 : HasFDerivAt (fun q : ℝ × ℝ => χ q.2) ((fderiv ℝ χ p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) p :=
    ((hχ.differentiable (by simp)) p.2).hasFDerivAt.comp p hasFDerivAt_snd
  have h3 : HasFDerivAt (fun q : ℝ × ℝ => u q.1 * χ q.2)
      (u p.1 • (fderiv ℝ χ p.2).comp (ContinuousLinearMap.snd ℝ ℝ ℝ) +
        χ p.2 • (fderiv ℝ u p.1).comp (ContinuousLinearMap.fst ℝ ℝ ℝ)) p := h1.mul h2
  rw [h3.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', map_zero, smul_eq_mul, mul_zero, add_zero]
  rfl

theorem prod_weak {m : ℕ} {v : Space → Space} {G : Space → (Space →L[ℝ] Space)}
    {H : Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsSecondOrderField m v G H) (n : ℤ) (a b : Fin 3)
    (φ χ : ℝ → ℝ) (hφ : ContDiff ℝ ∞ φ) (hφc : HasCompactSupport φ) (hφs : tsupport φ ⊆ Ioi 0)
    (hχ : ContDiff ℝ ∞ χ) (hχc : HasCompactSupport χ) :
    ∫ p, ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * gradMode m n G a b p) =
      -∫ p, ((φ p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a b 2 p) := by
  set u : ℝ → ℝ := fun r => φ r * r with hu_def
  have hu : ContDiff ℝ ∞ u := hφ.mul contDiff_id
  have hus : tsupport u ⊆ tsupport φ := tsupport_mul_subset_left
  have huc : HasCompactSupport u := hφc.mul_right
  set ψ : ℝ × ℝ → ℝ := fun q => u q.1 * χ q.2 with hψ_def
  have hψ : ContDiff ℝ ∞ ψ := (hu.comp contDiff_fst).mul (hχ.comp contDiff_snd)
  have hψsub : tsupport ψ ⊆ tsupport u ×ˢ tsupport χ := by
    refine closure_minimal (fun q hq => ?_) ((isClosed_tsupport _).prod (isClosed_tsupport _))
    have hq' : u q.1 * χ q.2 ≠ 0 := hq
    exact ⟨subset_tsupport _ (left_ne_zero_of_mul hq'), subset_tsupport _ (right_ne_zero_of_mul hq')⟩
  have hψc : HasCompactSupport ψ := by
    refine HasCompactSupport.intro (huc.isCompact.prod hχc.isCompact) (fun q hq => ?_)
    by_contra hne
    exact hq (hψsub (subset_tsupport _ hne))
  have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p hp => hφs (hus (hψsub hp).1)
  have key := weak_smooth hs n a b ψ hψ hψc hpos
  have e1 : (fun p : ℝ × ℝ => ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * gradMode m n G a b p)) =
      fun p => ((fderiv ℝ ψ p (0, 1) : ℝ) : ℂ) * gradMode m n G a b p := by
    funext p
    rw [hψ_def, prod_fderiv hu hχ p, hu_def]
    push_cast
    ring
  have e2 : (fun p : ℝ × ℝ => ((φ p.1 * χ p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * modeThird m n H a b 2 p)) =
      fun p => (ψ p : ℂ) * modeThird m n H a b 2 p := by
    funext p
    simp only [hψ_def, hu_def]
    push_cast
    ring
  rw [e1, e2]
  exact key

theorem weight_split (K : CellBox) (t : ℝ → ℝ) (ht : Continuous t)
    (hax : 0 < K.r₁ ∨ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ r, t r = r * t₀ r) :
    ∃ T : ℝ → ℝ, Continuous T ∧ ∀ r ∈ Icc K.r₁ K.r₂, t r = r * T r := by
  rcases hax with h | ⟨t₀, h0, h1⟩
  · refine ⟨fun r => t r / max r K.r₁, ht.div (continuous_id.max continuous_const)
      (fun r => (lt_of_lt_of_le h (le_max_right _ _)).ne'), fun r hr => ?_⟩
    have hr0 : r ≠ 0 := (lt_of_lt_of_le h hr.1).ne'
    simp only
    rw [max_eq_left hr.1]
    field_simp
  · exact ⟨t₀, h0, fun r _ => h1 r⟩

end Breakdown.FracInternal.HeightModeWeak

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis SteadyCert FracInternal.HeightModeWeak

theorem heightModeWeak : HeightModeWeakStatement := by
  intro m v G H hs K hK n a b t s ht hsc hax
  obtain ⟨T, hT, hTt⟩ := weight_split K t ht hax
  set Fw : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * gradMode m n G a b p with hFw
  set Dw : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * heightGradMode m n H a b p with hDw
  have hF : ∀ R Z : ℝ, IntegrableOn Fw (Icc 0 R ×ˢ Icc (-Z) Z) := fun R Z => (weighted_modes hs n a b R Z).1
  have hD : ∀ R Z : ℝ, IntegrableOn Dw (Icc 0 R ×ˢ Icc (-Z) Z) := fun R Z => (weighted_modes hs n a b R Z).2
  have hrect : K.rect ⊆ Icc 0 K.r₂ ×ˢ Icc (-K.z₂) K.z₂ := fun p hp => by
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := (hp : p ∈ Icc K.r₁ K.r₂ ×ˢ Icc K.z₁ K.z₂)
    exact ⟨⟨hK.r_order.1.trans h1, h2⟩, ⟨by linarith [hK.z_order.1], h4⟩⟩
  have hRc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hRm : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc
  have hFr : IntegrableOn Fw K.rect := (hF _ _).mono_set hrect
  have hDr : IntegrableOn Dw K.rect := (hD _ _).mono_set hrect
  have conv : ∀ (k : ℝ → ℝ) (W : ℝ × ℝ → ℂ), Set.EqOn (fun p : ℝ × ℝ => ((t p.1 * k p.2 : ℝ) : ℂ) * W p)
      (fun p => ((T p.1 * k p.2 : ℝ) : ℂ) * ((p.1 : ℂ) * W p)) K.rect := by
    intro k W p hp
    simp only
    rw [hTt p.1 hp.1]
    push_cast
    ring
  have int_of : ∀ (k : ℝ → ℝ), Continuous k → ∀ W : ℝ × ℝ → ℂ,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * W p) K.rect →
      IntegrableOn (fun p : ℝ × ℝ => ((t p.1 * k p.2 : ℝ) : ℂ) * W p) K.rect := by
    intro k hk W hW
    refine (hW.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hT.comp continuous_fst).mul (hk.comp continuous_snd))).continuousOn hRc).congr_fun ?_ hRm
    intro p hp
    exact (conv k W hp).symm
  refine ⟨int_of s hsc _ hFr, int_of s hsc _ hDr, fun hs1 hs0 hs2 => ?_⟩
  have hdsc : Continuous (deriv s) := hs1.continuous_deriv le_rfl
  have hw : ∀ φ χ : ℝ → ℝ, ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ Ioi 0 →
      ContDiff ℝ ∞ χ → HasCompactSupport χ →
      ∫ p, ((φ p.1 * deriv χ p.2 : ℝ) : ℂ) * Fw p = -∫ p, ((φ p.1 * χ p.2 : ℝ) : ℂ) * Dw p :=
    fun φ χ h1 h2 h3 h4 h5 => prod_weak hs n a b φ χ h1 h2 h3 h4 h5
  have hz := slice_zero hF hD hw hK.z_order.2.le s hs1 hs0 hs2
  have iD : IntegrableOn (fun p : ℝ × ℝ => ((T p.1 * s p.2 : ℝ) : ℂ) * Dw p) K.rect :=
    hDr.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hT.comp continuous_fst).mul (hsc.comp continuous_snd))).continuousOn hRc
  have iF : IntegrableOn (fun p : ℝ × ℝ => ((T p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) K.rect :=
    hFr.continuousOn_mul (Complex.continuous_ofReal.comp
      ((hT.comp continuous_fst).mul (hdsc.comp continuous_snd))).continuousOn hRc
  rw [setIntegral_congr_fun hRm (conv s _), setIntegral_congr_fun hRm (conv (deriv s) _)]
  apply eq_neg_of_add_eq_zero_left
  have iDF : IntegrableOn (fun p : ℝ × ℝ => ((T p.1 * s p.2 : ℝ) : ℂ) * Dw p +
      ((T p.1 * deriv s p.2 : ℝ) : ℂ) * Fw p) K.rect := iD.add iF
  rw [← integral_add iD iF, CellBox.rect, iter_r iDF]
  have hae : ∀ᵐ r ∂(volume.restrict (Ioc K.r₁ K.r₂)),
      (∫ z in Icc K.z₁ K.z₂, (((T r * s z : ℝ) : ℂ) * Dw (r, z) + ((T r * deriv s z : ℝ) : ℂ) * Fw (r, z))) = 0 := by
    rw [ae_restrict_iff' measurableSet_Ioc]
    filter_upwards [hz] with r hr hmem
    have h0 := hr (lt_of_le_of_lt hK.r_order.1 hmem.1)
    have e : (fun z => ((T r * s z : ℝ) : ℂ) * Dw (r, z) + ((T r * deriv s z : ℝ) : ℂ) * Fw (r, z)) =
        fun z => (T r : ℂ) * (((s z : ℝ) : ℂ) * Dw (r, z) + ((deriv s z : ℝ) : ℂ) * Fw (r, z)) := by
      funext z; push_cast; ring
    rw [e, integral_const_mul, h0, mul_zero]
  rw [integral_Icc_eq_integral_Ioc]
  exact integral_eq_zero_of_ae hae

end Breakdown.CellCert.CellEnergy
