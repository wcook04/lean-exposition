import Breakdown.FracCell.ResolvedEnergySt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace ResolvedEnergyInternal

variable (K : CellBox)

theorem rect_meas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem normSq_nonneg {m : ℝ × ℝ → ℝ} (hm : ∀ p ∈ K.rect, 0 ≤ m p) (g : ℝ × ℝ → ℂ) :
    0 ≤ K.normSqOn m g :=
  setIntegral_nonneg (rect_meas K) (fun p hp => mul_nonneg (hm p hp) (sq_nonneg _))

theorem cross_integrable {m : ℝ × ℝ → ℝ} (hm : ∀ p ∈ K.rect, 0 ≤ m p)
    (hmm : AEStronglyMeasurable m (volume.restrict K.rect)) {g P : ℝ × ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect)) (hP : AEStronglyMeasurable P (volume.restrict K.rect))
    (hgi : IntegrableOn (fun p => m p * ‖g p‖ ^ 2) K.rect) (hPi : IntegrableOn (fun p => m p * ‖P p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => (m p : ℂ) * g p * (starRingEnd ℂ) (P p)) K.rect := by
  refine Integrable.mono' (hgi.add hPi) ?_ ?_
  · exact ((Complex.continuous_ofReal.comp_aestronglyMeasurable hmm).mul hg).mul
      (Complex.continuous_conj.comp_aestronglyMeasurable hP)
  · refine (ae_restrict_iff' (rect_meas K)).2 (ae_of_all _ (fun p hp => ?_))
    have h0 := hm p hp
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg h0, Complex.norm_conj, Pi.add_apply]
    nlinarith [sq_nonneg (‖g p‖ - ‖P p‖), norm_nonneg (g p), norm_nonneg (P p)]

theorem pair_sq_le {m : ℝ × ℝ → ℝ} (hm : ∀ p ∈ K.rect, 0 ≤ m p)
    (hmm : AEStronglyMeasurable m (volume.restrict K.rect)) {g P : ℝ × ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect)) (hP : AEStronglyMeasurable P (volume.restrict K.rect))
    (hgi : IntegrableOn (fun p => m p * ‖g p‖ ^ 2) K.rect) (hPi : IntegrableOn (fun p => m p * ‖P p‖ ^ 2) K.rect) :
    ‖K.pairOn m g P‖ ^ 2 ≤ K.normSqOn m g * K.normSqOn m P := by
  have hXi : IntegrableOn (fun p => m p * (‖g p‖ * ‖P p‖)) K.rect := by
    refine Integrable.mono' (hgi.add hPi) ?_ ?_
    · exact hmm.mul (hg.norm.mul hP.norm)
    · refine (ae_restrict_iff' (rect_meas K)).2 (ae_of_all _ (fun p hp => ?_))
      have h0 := hm p hp
      simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0, abs_norm, Pi.add_apply]
      nlinarith [sq_nonneg (‖g p‖ - ‖P p‖), norm_nonneg (g p), norm_nonneg (P p), mul_nonneg h0 (sq_nonneg (‖g p‖ - ‖P p‖))]
  set X := ∫ p in K.rect, m p * (‖g p‖ * ‖P p‖)
  have hle : ‖K.pairOn m g P‖ ≤ X := by
    refine norm_integral_le_of_norm_le hXi ((ae_restrict_iff' (rect_meas K)).2 (ae_of_all _ (fun p hp => ?_)))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hm p hp), Complex.norm_conj]
    ring_nf
    exact le_refl _
  have hquad : ∀ s : ℝ, 0 ≤ K.normSqOn m P * (s * s) + (-2 * X) * s + K.normSqOn m g := by
    intro s
    have h1 : 0 ≤ ∫ p in K.rect, m p * (‖g p‖ - s * ‖P p‖) ^ 2 :=
      setIntegral_nonneg (rect_meas K) (fun p hp => mul_nonneg (hm p hp) (sq_nonneg _))
    have h2 : ∫ p in K.rect, m p * (‖g p‖ - s * ‖P p‖) ^ 2
        = K.normSqOn m g - 2 * s * X + s * s * K.normSqOn m P := by
      have e : ∀ p, m p * (‖g p‖ - s * ‖P p‖) ^ 2
          = m p * ‖g p‖ ^ 2 - (2 * s) * (m p * (‖g p‖ * ‖P p‖)) + (s * s) * (m p * ‖P p‖ ^ 2) := fun p => by ring
      simp only [e]
      rw [integral_add, integral_sub, integral_const_mul, integral_const_mul]
      · rfl
      · exact hgi
      · exact hXi.const_mul _
      · exact hgi.sub (hXi.const_mul _)
      · exact hPi.const_mul _
    linarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hX0 : 0 ≤ ‖K.pairOn m g P‖ := norm_nonneg _
  nlinarith

theorem testSup_le {m : ℝ × ℝ → ℝ} (hm : ∀ p ∈ K.rect, 0 ≤ m p)
    (hmm : AEStronglyMeasurable m (volume.restrict K.rect)) {V : Set (ℝ × ℝ → ℂ)} {g : ℝ × ℝ → ℂ}
    (hg : AEStronglyMeasurable g (volume.restrict K.rect))
    (hgi : IntegrableOn (fun p => m p * ‖g p‖ ^ 2) K.rect)
    (hV : ∀ P ∈ V, AEStronglyMeasurable P (volume.restrict K.rect) ∧ IntegrableOn (fun p => m p * ‖P p‖ ^ 2) K.rect) :
    K.testSupremum m V g ≤ K.normSqOn m g := by
  refine Real.sSup_le ?_ (normSq_nonneg K hm g)
  rintro t ⟨P, hPV, hpos, rfl⟩
  rw [div_le_iff₀ hpos]
  exact pair_sq_le K hm hmm hg (hV P hPV).1 hgi (hV P hPV).2

theorem sub_sq_integrable {m : ℝ × ℝ → ℝ} (hm : ∀ p ∈ K.rect, 0 ≤ m p)
    (hmm : AEStronglyMeasurable m (volume.restrict K.rect)) {a b : ℝ × ℝ → ℂ}
    (ha : AEStronglyMeasurable a (volume.restrict K.rect)) (hb : AEStronglyMeasurable b (volume.restrict K.rect))
    (hai : IntegrableOn (fun p => m p * ‖a p‖ ^ 2) K.rect) (hbi : IntegrableOn (fun p => m p * ‖b p‖ ^ 2) K.rect) :
    IntegrableOn (fun p => m p * ‖a p - b p‖ ^ 2) K.rect := by
  refine Integrable.mono' ((hai.const_mul 2).add (hbi.const_mul 2)) ?_ ?_
  · exact hmm.mul ((ha.sub hb).norm.pow 2)
  · refine (ae_restrict_iff' (rect_meas K)).2 (ae_of_all _ (fun p hp => ?_))
    have h0 := hm p hp
    have h1 : ‖a p - b p‖ ≤ ‖a p‖ + ‖b p‖ := norm_sub_le _ _
    have h2 : ‖a p - b p‖ ^ 2 ≤ 2 * ‖a p‖ ^ 2 + 2 * ‖b p‖ ^ 2 := by
      nlinarith [norm_nonneg (a p - b p), norm_nonneg (a p), norm_nonneg (b p), sq_nonneg (‖a p‖ - ‖b p‖)]
    simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg h0, abs_pow, abs_norm, Pi.add_apply]
    nlinarith [mul_le_mul_of_nonneg_left h2 h0]

theorem orth_split {m : ℝ × ℝ → ℝ} (hm : ∀ p ∈ K.rect, 0 ≤ m p)
    (hmm : AEStronglyMeasurable m (volume.restrict K.rect)) {a b : ℝ × ℝ → ℂ}
    (ha : AEStronglyMeasurable a (volume.restrict K.rect)) (hb : AEStronglyMeasurable b (volume.restrict K.rect))
    (hai : IntegrableOn (fun p => m p * ‖a p‖ ^ 2) K.rect) (hbi : IntegrableOn (fun p => m p * ‖b p‖ ^ 2) K.rect)
    (hc : K.pairOn m (fun p => a p - b p) b = 0) :
    K.normSqOn m a = K.normSqOn m b + K.normSqOn m (fun p => a p - b p) := by
  have hdi := sub_sq_integrable K hm hmm ha hb hai hbi
  have hci : IntegrableOn (fun p => (m p : ℂ) * (a p - b p) * (starRingEnd ℂ) (b p)) K.rect :=
    cross_integrable K hm hmm (ha.sub hb) hb hdi hbi
  have e : ∀ p, m p * ‖a p‖ ^ 2 = m p * ‖b p‖ ^ 2 + m p * ‖a p - b p‖ ^ 2
      + 2 * RCLike.re ((m p : ℂ) * (a p - b p) * (starRingEnd ℂ) (b p)) := fun p => by
    have h := Complex.normSq_add (a p - b p) (b p)
    rw [sub_add_cancel] at h
    rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm, h, mul_assoc, RCLike.re_to_complex, Complex.re_ofReal_mul]
    ring
  have hre : ∫ p in K.rect, RCLike.re ((m p : ℂ) * (a p - b p) * (starRingEnd ℂ) (b p)) = 0 := by
    rw [integral_re hci]
    unfold CellBox.pairOn at hc
    rw [hc]
    simp
  unfold CellBox.normSqOn
  simp only [e]
  rw [integral_add, integral_add, integral_const_mul, hre]
  · ring
  · exact hbi
  · exact hdi
  · exact hbi.add hdi
  · exact (hci.re).const_mul 2

theorem poly_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') : Continuous P := by
  obtain ⟨c, hc⟩ := hP
  have : P = fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) :=
    funext hc
  rw [this]
  fun_prop

theorem scaled_cont {f : ℝ × ℝ → ℝ} (hf : Continuous f) {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ scaledPolyFn f d d') :
    Continuous P := by
  obtain ⟨P₀, h₀, hc⟩ := hP
  have : P = fun p => (f p : ℂ) * P₀ p := funext hc
  rw [this]
  exact (Complex.continuous_ofReal.comp hf).mul (poly_cont h₀)

theorem zero_mem (d d' : ℕ) : (0 : ℝ × ℝ → ℂ) ∈ polyFn d d' := ⟨fun _ _ => 0, fun p => by simp⟩

theorem proj_mem (d d' : ℕ) (F : ℝ × ℝ → ℂ) : K.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact zero_mem d d'

theorem proj_orth (d d' : ℕ) (F : ℝ × ℝ → ℂ) :
    K.pairOn K.lineWeightFn (fun p => F p - K.proj d d' F p) (K.proj d d' F) = 0 := by
  by_cases h : ∃ P ∈ polyFn d d', ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0
  · have e : K.proj d d' F = h.choose := by unfold CellBox.proj; rw [dif_pos h]
    rw [e]
    exact h.choose_spec.2 _ h.choose_spec.1
  · have e : K.proj d d' F = 0 := by unfold CellBox.proj; rw [dif_neg h]
    rw [e]
    simp [CellBox.pairOn]

theorem radialDeriv_formula {d d' : ℕ} (c : Fin (d + 1) → Fin (d' + 1) → ℂ) (p : ℝ × ℝ) :
    CellBox.radialDeriv (fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
        c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ))) p
      = ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
        c j l * (((j : ℕ) : ℂ) * (p.1 : ℂ) ^ ((j : ℕ) - 1)) * ((p.2 : ℂ) ^ (l : ℕ)) := by
  unfold CellBox.radialDeriv
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum (fun j _ => HasDerivAt.fun_sum (fun l _ => ?_))
  show HasDerivAt (fun r : ℝ => c j l * (r : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ)) _ p.1
  exact (((hasDerivAt_pow (j : ℕ) (p.1 : ℂ)).comp_ofReal).const_mul (c j l)).mul_const _

theorem heightDeriv_formula {d d' : ℕ} (c : Fin (d + 1) → Fin (d' + 1) → ℂ) (p : ℝ × ℝ) :
    CellBox.heightDeriv (fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
        c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ))) p
      = ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1),
        c j l * ((p.1 : ℂ) ^ (j : ℕ)) * (((l : ℕ) : ℂ) * (p.2 : ℂ) ^ ((l : ℕ) - 1)) := by
  unfold CellBox.heightDeriv
  refine HasDerivAt.deriv ?_
  refine HasDerivAt.fun_sum (fun j _ => HasDerivAt.fun_sum (fun l _ => ?_))
  show HasDerivAt (fun z : ℝ => c j l * (p.1 : ℂ) ^ (j : ℕ) * (z : ℂ) ^ (l : ℕ)) _ p.2
  exact ((hasDerivAt_pow (l : ℕ) (p.2 : ℂ)).comp_ofReal).const_mul _

theorem radialDeriv_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') :
    Continuous (CellBox.radialDeriv P) := by
  obtain ⟨c, hc⟩ := hP
  have : P = fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) :=
    funext hc
  rw [this]
  have e := funext (radialDeriv_formula c)
  rw [e]
  fun_prop

theorem heightDeriv_cont {d d' : ℕ} {P : ℝ × ℝ → ℂ} (hP : P ∈ polyFn d d') :
    Continuous (CellBox.heightDeriv P) := by
  obtain ⟨c, hc⟩ := hP
  have : P = fun p : ℝ × ℝ => ∑ j : Fin (d + 1), ∑ l : Fin (d' + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) :=
    funext hc
  rw [this]
  have e := funext (heightDeriv_formula c)
  rw [e]
  fun_prop

theorem cont_integrable {m : ℝ × ℝ → ℝ} (hm : ContinuousOn m K.rect) {P : ℝ × ℝ → ℂ} (hP : Continuous P) :
    AEStronglyMeasurable P (volume.restrict K.rect) ∧ IntegrableOn (fun p => m p * ‖P p‖ ^ 2) K.rect :=
  ⟨hP.aestronglyMeasurable, (hm.mul (hP.norm.pow 2).continuousOn).integrableOn_compact (isCompact_Icc.prod isCompact_Icc)⟩

theorem piece (iR : ℝ) (w m2 x : ℝ × ℝ → ℝ) (g D : ℝ × ℝ → ℂ) (e2 e3 : ℝ)
    (hw : ∀ p ∈ K.rect, 0 ≤ w p) (hwm : AEStronglyMeasurable w (volume.restrict K.rect))
    (hg : AEStronglyMeasurable g (volume.restrict K.rect)) (hD : AEStronglyMeasurable D (volume.restrict K.rect))
    (hgw : IntegrableOn (fun p => w p * ‖g p‖ ^ 2) K.rect) (hDw : IntegrableOn (fun p => w p * ‖D p‖ ^ 2) K.rect)
    (hm2i : IntegrableOn (fun p => m2 p * ‖g p‖ ^ 2) K.rect)
    (hxi : IntegrableOn (fun p => p.1 * ‖(x p : ℂ) * g p‖ ^ 2) K.rect)
    (hcross : K.pairOn w (fun p => g p - D p) D = 0)
    (he2 : e2 ≤ ∫ p in K.rect, m2 p * ‖g p‖ ^ 2) (he3 : e3 ≤ ∫ p in K.rect, p.1 * ‖(x p : ℂ) * g p‖ ^ 2)
    (hsplit : ∀ p ∈ K.rect, iR * w p + m2 p + p.1 * x p ^ 2 = p.1) :
    iR * K.normSqOn w D + e2 + e3 + iR * K.normSqOn w (fun p => g p - D p) ≤ ∫ p in K.rect, p.1 * ‖g p‖ ^ 2 := by
  have hp := orth_split K hw hwm hg hD hgw hDw hcross
  have hsum : ∫ p in K.rect, p.1 * ‖g p‖ ^ 2
      = iR * K.normSqOn w g + (∫ p in K.rect, m2 p * ‖g p‖ ^ 2) + ∫ p in K.rect, p.1 * ‖(x p : ℂ) * g p‖ ^ 2 := by
    unfold CellBox.normSqOn
    have h1 : IntegrableOn (fun p => iR * (w p * ‖g p‖ ^ 2) + m2 p * ‖g p‖ ^ 2) K.rect := (hgw.const_mul iR).add hm2i
    rw [← integral_const_mul, ← integral_add (hgw.const_mul _) hm2i, ← integral_add h1 hxi]
    refine setIntegral_congr_fun (rect_meas K) (fun p hp => ?_)
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    linear_combination (-(‖g p‖ ^ 2)) * hsplit p hp
  rw [hsum, hp]
  nlinarith

theorem refR_sq_le (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : K.refR p.1 ^ 2 ≤ 1 := by
  obtain ⟨⟨h1, h2⟩, -⟩ := hp
  have hd : 0 < K.r₂ - K.r₁ := by linarith [hK.r_order.2]
  unfold CellBox.refR
  rw [div_pow, div_le_one (by positivity)]
  nlinarith

theorem refZ_sq_le (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : K.refZ p.2 ^ 2 ≤ 1 := by
  obtain ⟨-, ⟨h1, h2⟩⟩ := hp
  have hd : 0 < K.z₂ - K.z₁ := by linarith [hK.z_order.2]
  unfold CellBox.refZ
  rw [div_pow, div_le_one (by positivity)]
  nlinarith

theorem fst_nonneg (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) : 0 ≤ p.1 := by
  linarith [hp.1.1, hK.r_order.1]

theorem lw_cont : Continuous (fun r => K.lineWeight r) := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem refR_cont : Continuous K.refR := by
  unfold CellBox.refR
  fun_prop

theorem refZ_cont : Continuous K.refZ := by
  unfold CellBox.refZ
  fun_prop

theorem wcont {f : ℝ × ℝ → ℝ} (hf : Continuous f) : AEStronglyMeasurable f (volume.restrict K.rect) :=
  hf.aestronglyMeasurable

theorem mono_int {f b : ℝ × ℝ → ℝ} (hf : AEStronglyMeasurable f (volume.restrict K.rect))
    (hb : IntegrableOn b K.rect) (h : ∀ p ∈ K.rect, 0 ≤ f p ∧ f p ≤ b p) : IntegrableOn f K.rect := by
  refine Integrable.mono' hb hf ((ae_restrict_iff' (rect_meas K)).2 (ae_of_all _ (fun p hp => ?_)))
  rw [Real.norm_eq_abs, abs_of_nonneg (h p hp).1]
  exact (h p hp).2

theorem iR_pos (hK : IsCellBox K) : 0 < K.innerRadius := by
  unfold CellBox.innerRadius
  split_ifs with h
  · exact one_pos
  · exact lt_of_le_of_ne hK.r_order.1 (Ne.symm h)

theorem dir_part (hK : IsCellBox K) (y : ℝ × ℝ → ℝ) (hyc : Continuous y) (hy : ∀ p ∈ K.rect, y p ^ 2 ≤ 1)
    (V₂ V₃ : Set (ℝ × ℝ → ℂ)) (hV₂ : ∀ P ∈ V₂, Continuous P) (hV₃ : ∀ P ∈ V₃, Continuous P)
    (g D : ℝ × ℝ → ℂ) (hg : AEStronglyMeasurable g (volume.restrict K.rect)) (hDc : Continuous D)
    (hgi : IntegrableOn (fun p => p.1 * ‖g p‖ ^ 2) K.rect)
    (hcross : K.pairOn (fun p => K.lineWeight p.1 * (1 - y p ^ 2)) (fun p => g p - D p) D = 0) :
    K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - y p ^ 2)) D
      + (if K.r₁ = 0 then 0 else K.testSupremum (fun p => (p.1 - K.r₁) * (1 - y p ^ 2)) V₂ g)
      + K.testSupremum (fun p => p.1) V₃ (fun p => (y p : ℂ) * g p)
      + K.innerRadius * K.normSqOn (fun p => K.lineWeight p.1 * (1 - y p ^ 2)) (fun p => g p - D p)
      ≤ ∫ p in K.rect, p.1 * ‖g p‖ ^ 2 := by
  have hiR := iR_pos K hK
  set iR := K.innerRadius with hiR_def
  set w : ℝ × ℝ → ℝ := fun p => K.lineWeight p.1 * (1 - y p ^ 2) with hw_def
  set m2 : ℝ × ℝ → ℝ := fun p => if K.r₁ = 0 then 0 else (p.1 - K.r₁) * (1 - y p ^ 2) with hm2_def
  have hr0 : ∀ p ∈ K.rect, 0 ≤ p.1 := fun p hp => fst_nonneg K hK hp
  have hwc : Continuous w := ((lw_cont K).comp continuous_fst).mul (continuous_const.sub (hyc.pow 2))
  have hm2c : ∀ p ∈ K.rect, 0 ≤ m2 p := by
    intro p hp
    simp only [hm2_def]
    split_ifs
    · exact le_refl _
    · exact mul_nonneg (by linarith [hp.1.1]) (by linarith [hy p hp])
  have hwn : ∀ p ∈ K.rect, 0 ≤ w p := by
    intro p hp
    simp only [hw_def, CellBox.lineWeight]
    split_ifs
    · exact mul_nonneg (hr0 p hp) (by linarith [hy p hp])
    · exact mul_nonneg zero_le_one (by linarith [hy p hp])
  have hsplit : ∀ p ∈ K.rect, iR * w p + m2 p + p.1 * y p ^ 2 = p.1 := by
    intro p hp
    simp only [hiR_def, hw_def, hm2_def, CellBox.innerRadius, CellBox.lineWeight]
    split_ifs <;> ring
  have hwb : ∀ p ∈ K.rect, iR * w p ≤ p.1 := by
    intro p hp
    have := hsplit p hp
    nlinarith [hm2c p hp, mul_nonneg (hr0 p hp) (sq_nonneg (y p))]
  have hm2b : ∀ p ∈ K.rect, m2 p ≤ p.1 := by
    intro p hp
    have := hsplit p hp
    nlinarith [mul_nonneg hiR.le (hwn p hp), mul_nonneg (hr0 p hp) (sq_nonneg (y p))]
  have hgw : IntegrableOn (fun p => w p * ‖g p‖ ^ 2) K.rect := by
    refine mono_int K ((wcont K hwc).mul (hg.norm.pow 2)) (hgi.const_mul iR⁻¹) (fun p hp => ⟨?_, ?_⟩)
    · exact mul_nonneg (hwn p hp) (sq_nonneg _)
    · have h1 : w p ≤ iR⁻¹ * p.1 := by rw [le_inv_mul_iff₀ hiR]; exact hwb p hp
      calc w p * ‖g p‖ ^ 2 ≤ (iR⁻¹ * p.1) * ‖g p‖ ^ 2 := mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
        _ = iR⁻¹ * (p.1 * ‖g p‖ ^ 2) := by ring
  have hm2m : AEStronglyMeasurable m2 (volume.restrict K.rect) := by
    simp only [hm2_def]
    split_ifs
    · exact aestronglyMeasurable_const
    · exact wcont K ((continuous_fst.sub continuous_const).mul (continuous_const.sub (hyc.pow 2)))
  have hm2i : IntegrableOn (fun p => m2 p * ‖g p‖ ^ 2) K.rect := by
    refine mono_int K (hm2m.mul (hg.norm.pow 2)) hgi (fun p hp => ⟨mul_nonneg (hm2c p hp) (sq_nonneg _), ?_⟩)
    exact mul_le_mul_of_nonneg_right (hm2b p hp) (sq_nonneg _)
  have hyg : AEStronglyMeasurable (fun p => (y p : ℂ) * g p) (volume.restrict K.rect) :=
    ((Complex.continuous_ofReal.comp hyc).aestronglyMeasurable).mul hg
  have hxi : IntegrableOn (fun p => p.1 * ‖(y p : ℂ) * g p‖ ^ 2) K.rect := by
    refine mono_int K ((wcont K continuous_fst).mul (hyg.norm.pow 2)) hgi
      (fun p hp => ⟨mul_nonneg (hr0 p hp) (sq_nonneg _), ?_⟩)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have := hy p hp
    nlinarith [mul_nonneg (hr0 p hp) (sq_nonneg ‖g p‖)]
  refine piece K iR w m2 y g D _ _ hwn (wcont K hwc) hg hDc.aestronglyMeasurable hgw
    (cont_integrable K hwc.continuousOn hDc).2 hm2i hxi hcross ?_ ?_ hsplit
  · by_cases h : K.r₁ = 0
    · simp only [h, if_true, hm2_def, zero_mul, integral_zero, le_refl]
    · have e : (fun p => m2 p * ‖g p‖ ^ 2) = fun p => (p.1 - K.r₁) * (1 - y p ^ 2) * ‖g p‖ ^ 2 := by
        funext p; simp only [hm2_def, if_neg h]
      rw [if_neg h, e]
      have hmc : Continuous (fun p : ℝ × ℝ => (p.1 - K.r₁) * (1 - y p ^ 2)) :=
        (continuous_fst.sub continuous_const).mul (continuous_const.sub (hyc.pow 2))
      refine testSup_le K (fun p hp => ?_) (wcont K hmc) hg ?_ (fun P hP => cont_integrable K hmc.continuousOn (hV₂ P hP))
      · have := hm2c p hp; simpa only [hm2_def, if_neg h] using this
      · rw [← e]; exact hm2i
  · exact testSup_le K hr0 (wcont K continuous_fst) hyg hxi
      (fun P hP => cont_integrable K continuous_fst.continuousOn (hV₃ P hP))

theorem ang_part (hK : IsCellBox K) (Q : ℕ) (n : ℤ) (hn : K.IsAxis → n = 0) (h : ℝ × ℝ → ℂ)
    (hh : AEStronglyMeasurable h (volume.restrict K.rect)) (hhi : IntegrableOn (fun p => p.1 * ‖h p‖ ^ 2) K.rect) :
    K.angularEnergy Q (fun p => (p.1 : ℂ) * h p) + K.angularWeight n * K.tailNormSq Q (fun p => (p.1 : ℂ) * h p)
      ≤ ∫ p in K.rect, p.1 * ‖h p‖ ^ 2 := by
  have hr0 : ∀ p ∈ K.rect, 0 ≤ p.1 := fun p hp => fst_nonneg K hK hp
  by_cases hax : K.r₁ = 0
  · have hn0 : n = 0 := hn hax
    have hw : K.angularWeight n = 0 := by
      unfold CellBox.angularWeight; rw [if_pos hax, if_pos hn0]
    have key : ∀ P : ℝ × ℝ → ℂ, K.pairOn (fun p => p.1) (fun p => (p.1 : ℂ) * h p / (p.1 : ℂ)) P
        = K.pairOn (fun p => p.1) h P := by
      intro P
      unfold CellBox.pairOn
      refine integral_congr_ae (ae_of_all _ (fun p => ?_))
      show (p.1 : ℂ) * ((p.1 : ℂ) * h p / (p.1 : ℂ)) * (starRingEnd ℂ) (P p) = (p.1 : ℂ) * h p * (starRingEnd ℂ) (P p)
      by_cases h0 : p.1 = 0
      · simp [h0]
      · have : (p.1 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 h0
        field_simp
    have he : K.angularEnergy Q (fun p => (p.1 : ℂ) * h p)
        = K.testSupremum (fun p => p.1) (scaledPolyFn (fun p => p.1) Q Q) h := by
      unfold CellBox.angularEnergy CellBox.testSupremum
      rw [if_pos hax]
      simp only [key]
    rw [he, hw, zero_mul, add_zero]
    exact testSup_le K hr0 (wcont K continuous_fst) hh hhi
      (fun P hP => cont_integrable K continuous_fst.continuousOn (scaled_cont continuous_fst hP))
  · have hr1 : 0 < K.r₁ := lt_of_le_of_ne hK.r_order.1 (Ne.symm hax)
    have hr2 : 0 < K.r₂ := by linarith [hK.r_order.2]
    have hpos : ∀ p ∈ K.rect, 0 < p.1 := fun p hp => by linarith [hp.1.1]
    have hle2 : ∀ p ∈ K.rect, p.1 ≤ K.r₂ := fun p hp => hp.1.2
    have hw : K.angularWeight n = K.r₂⁻¹ := by
      unfold CellBox.angularWeight; rw [if_neg hax]
    have hlw : K.lineWeightFn = fun _ => 1 := by
      funext p; simp [CellBox.lineWeightFn, CellBox.lineWeight, hax]
    set F : ℝ × ℝ → ℂ := fun p => (p.1 : ℂ) * h p with hF_def
    set P := K.proj Q Q F with hP_def
    have hFm : AEStronglyMeasurable F (volume.restrict K.rect) :=
      ((Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable).mul hh
    have hnF : ∀ p, ‖F p‖ ^ 2 = p.1 ^ 2 * ‖h p‖ ^ 2 := fun p => by
      simp only [hF_def, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
    have hFi : IntegrableOn (fun p => (1 : ℝ) * ‖F p‖ ^ 2) K.rect := by
      refine mono_int K (aestronglyMeasurable_const.mul (hFm.norm.pow 2)) (hhi.const_mul K.r₂)
        (fun p hp => ⟨mul_nonneg zero_le_one (sq_nonneg _), ?_⟩)
      rw [one_mul, hnF]
      have ha := hle2 p hp
      have hb := hr0 p hp
      nlinarith [mul_nonneg (mul_nonneg hb (sq_nonneg ‖h p‖)) (sub_nonneg.2 ha)]
    have hPc : Continuous P := poly_cont (proj_mem K Q Q F)
    have horth : K.pairOn (fun _ => 1) (fun p => F p - P p) P = 0 := by
      have := proj_orth K Q Q F
      rw [hlw] at this
      exact this
    have hpy := orth_split K (fun p _ => zero_le_one) aestronglyMeasurable_const hFm hPc.aestronglyMeasurable hFi
      (cont_integrable K continuousOn_const hPc).2 horth
    set mθ : ℝ × ℝ → ℝ := fun p => (K.r₂ - p.1) / (p.1 * K.r₂) with hm_def
    have hmc : ContinuousOn mθ K.rect :=
      (continuousOn_const.sub continuousOn_fst).div (continuousOn_fst.mul continuousOn_const)
        (fun p hp => (mul_pos (hpos p hp) hr2).ne')
    have hm0 : ∀ p ∈ K.rect, 0 ≤ mθ p := fun p hp =>
      div_nonneg (by linarith [hle2 p hp]) (mul_pos (hpos p hp) hr2).le
    have hmF : ∀ p ∈ K.rect, mθ p * ‖F p‖ ^ 2 = (K.r₂ - p.1) * p.1 / K.r₂ * ‖h p‖ ^ 2 := by
      intro p hp
      rw [hnF]
      simp only [hm_def]
      have := (hpos p hp).ne'
      field_simp
    have hmi : IntegrableOn (fun p => mθ p * ‖F p‖ ^ 2) K.rect := by
      refine mono_int K ((hmc.aestronglyMeasurable (rect_meas K)).mul (hFm.norm.pow 2)) hhi
        (fun p hp => ⟨mul_nonneg (hm0 p hp) (sq_nonneg _), ?_⟩)
      rw [hmF p hp]
      have h1 : (K.r₂ - p.1) * p.1 / K.r₂ ≤ p.1 := by
        rw [div_le_iff₀ hr2]; nlinarith [hr0 p hp]
      exact mul_le_mul_of_nonneg_right h1 (sq_nonneg _)
    have hts := testSup_le K (V := scaledPolyFn (fun p => p.1) (Q - 1) Q) hm0 (hmc.aestronglyMeasurable (rect_meas K)) hFm hmi
      (fun P hP => cont_integrable K hmc (scaled_cont continuous_fst hP))
    have hang : K.angularEnergy Q F = K.r₂⁻¹ * K.normSqOn (fun _ => 1) P
        + K.testSupremum mθ (scaledPolyFn (fun p => p.1) (Q - 1) Q) F := by
      unfold CellBox.angularEnergy; rw [if_neg hax]
    have htail : K.tailNormSq Q F = K.normSqOn (fun _ => 1) (fun p => F p - P p) := by
      unfold CellBox.tailNormSq; rw [hlw]
    have hsum : ∫ p in K.rect, p.1 * ‖h p‖ ^ 2
        = K.r₂⁻¹ * K.normSqOn (fun _ => 1) F + K.normSqOn mθ F := by
      unfold CellBox.normSqOn
      rw [← integral_const_mul, ← integral_add (hFi.const_mul _) hmi]
      refine setIntegral_congr_fun (rect_meas K) (fun p hp => ?_)
      show p.1 * ‖h p‖ ^ 2 = K.r₂⁻¹ * (1 * ‖F p‖ ^ 2) + mθ p * ‖F p‖ ^ 2
      rw [hmF p hp, one_mul, hnF]
      have := (hpos p hp).ne'
      field_simp
      ring
    rw [hang, htail, hw, hsum, hpy]
    nlinarith [hts, inv_pos.2 hr2]

end ResolvedEnergyInternal

open ResolvedEnergyInternal in
theorem resolvedComponent_of (hr : RadialCrossStatement) (hz : HeightCrossStatement) :
    ResolvedComponentStatement := by
  intro K hK Q q n hn F Fr Fz h hF hFr hFz hh hFi hFri hFzi hhi hrp hzp
  have hPm := proj_mem K Q Q F
  have hlwc : Continuous K.lineWeightFn := (lw_cont K).comp continuous_fst
  have R := dir_part K hK (fun p => K.refR p.1) ((refR_cont K).comp continuous_fst) (fun p hp => refR_sq_le K hK hp)
    (polyFn (Q - 2) Q) (scaledPolyFn K.lineWeightFn (Q - 1) q) (fun P hP => poly_cont hP)
    (fun P hP => scaled_cont hlwc hP) Fr (CellBox.radialDeriv (K.proj Q Q F)) hFr (radialDeriv_cont hPm) hFri
    (hr K hK Q F Fr hF hFr hFi hFri hrp)
  have Z := dir_part K hK (fun p => K.refZ p.2) ((refZ_cont K).comp continuous_snd) (fun p hp => refZ_sq_le K hK hp)
    (polyFn (Q - 1) (Q - 1)) (polyFn q Q) (fun P hP => poly_cont hP)
    (fun P hP => poly_cont hP) Fz (CellBox.heightDeriv (K.proj Q Q F)) hFz (heightDeriv_cont hPm) hFzi
    (hz K hK Q F Fz hF hFz hFi hFzi hzp)
  have A := ang_part K hK Q n hn h hh hhi
  have hsum : ∫ p in K.rect, p.1 * (‖Fr p‖ ^ 2 + ‖h p‖ ^ 2 + ‖Fz p‖ ^ 2)
      = (∫ p in K.rect, p.1 * ‖Fr p‖ ^ 2) + (∫ p in K.rect, p.1 * ‖h p‖ ^ 2) + ∫ p in K.rect, p.1 * ‖Fz p‖ ^ 2 := by
    have h1 : IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖Fr p‖ ^ 2 + p.1 * ‖h p‖ ^ 2) K.rect := hFri.add hhi
    rw [← integral_add hFri hhi, ← integral_add h1 hFzi]
    refine setIntegral_congr_fun (rect_meas K) (fun p _ => ?_)
    show p.1 * (‖Fr p‖ ^ 2 + ‖h p‖ ^ 2 + ‖Fz p‖ ^ 2) = p.1 * ‖Fr p‖ ^ 2 + p.1 * ‖h p‖ ^ 2 + p.1 * ‖Fz p‖ ^ 2
    ring
  rw [hsum]
  unfold CellBox.radialEnergy CellBox.heightEnergy CellBox.tailGradWeight
  linarith

end CellAnalysis

end CellCert

end Breakdown
