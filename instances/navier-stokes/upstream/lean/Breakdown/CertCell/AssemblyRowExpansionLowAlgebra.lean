import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.RowCouplingLow
import Breakdown.CertCell.CellRowFormula

open scoped ENNReal NNReal
open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.Assembly.Internal.RowIdentity

open Breakdown Breakdown.CertCell CellCalculus CellCert CellCert.CellAnalysis CellCert.CellFormula

theorem pairVec_sum_mul (s S : Fin 3 → Fin 3 → ℂ) (u U : Fin 3 → ℂ) :
    ∑ j : Fin 12, pairVec s u j * pairVec S U j = (∑ a : Fin 3, ∑ b : Fin 3, s a b * S a b) + ∑ a : Fin 3, u a * U a := by
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.sum_univ_three, pairVec]
  norm_num
  have h2 : (⟨2, by omega⟩ : Fin 3) = 2 := rfl
  simp only [h2]
  ring

theorem conj_pairVec (s : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) (j : Fin 12) :
    (starRingEnd ℂ) (pairVec s u j) = pairVec (fun a b => (starRingEnd ℂ) (s a b)) (fun a => (starRingEnd ℂ) (u a)) j := by
  unfold pairVec
  split_ifs <;> rfl

theorem cross_pairing (s : Fin 3 → Fin 3 → ℂ) (u W Ω φ : Fin 3 → ℂ) :
    ∑ j : Fin 12, pairVec s u j * (starRingEnd ℂ) (crossTest W Ω φ j)
      = cdot3 (fun a => ∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol a j l : ℂ) * (curlComp s j * W l + Ω j * u l)) φ := by
  have e : ∀ j, (starRingEnd ℂ) (crossTest W Ω φ j) = pairVec
      (fun a b => ∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
        ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol i j' l' : ℂ) * W j' * (starRingEnd ℂ) (φ l'))
      (fun a => ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol a j' l' : ℂ) * (starRingEnd ℂ) (φ j') * Ω l') j := by
    intro j
    unfold crossTest
    rw [conj_pairVec]
    simp only [Complex.conj_conj]
  simp only [e, pairVec_sum_mul]
  have h := Internal.RowCouplingLow.low_expand 1 s u W Ω (fun a => (starRingEnd ℂ) (φ a))
  simp only [one_mul] at h
  rw [← h]
  simp only [cdot3]

theorem crossTest_add (W₁ W₂ Ω₁ Ω₂ φ : Fin 3 → ℂ) :
    crossTest (W₁ + W₂) (Ω₁ + Ω₂) φ = crossTest W₁ Ω₁ φ + crossTest W₂ Ω₂ φ := by
  funext j
  simp only [crossTest, pairVec, Pi.add_apply]
  split_ifs
  · simp only [mul_add, add_mul, Finset.sum_add_distrib, map_add]
  · simp only [mul_add, add_mul, Finset.sum_add_distrib, map_add]

theorem crossTest_zero (φ : Fin 3 → ℂ) : crossTest 0 0 φ = 0 := by
  funext j
  simp only [crossTest, pairVec, Pi.zero_apply]
  split_ifs <;> simp

open Internal.RowForm in
theorem rowVolume_integrable {K : CellBox} (hK : IsCellBox K) {k : ℝ} {R : RowProfile} (hR : IsRowProfile K k R)
    {φ : Fin 3 → CellPoly} (hreg : IsAxisRegularTest K k φ) (freq : ℝ) :
    IntegrableOn (fun p => (p.1 : ℂ) *
      ((∑ a : Fin 3, ∑ b : Fin 3, R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
        + cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p))) K.rect ∧
    IntegrableOn (fun p => (p.1 : ℂ) * cdot3 (R.vel p) (testValue K φ p)) K.rect := by
  obtain ⟨hmv, hmg, hml, hmp⟩ := hR.measurable
  have hF := hR.integrable
  have hsg : ∀ p, 0 ≤ ∑ a : Fin 3, cnormSq (R.grad p a) := fun p => Finset.sum_nonneg fun a _ => cnormSq_nonneg _
  have hvI := vec_int hK _ hF hmv fun p _ => by
    linarith [cnormSq_nonneg (R.lap p), cnormSq_nonneg (R.presGrad p), hsg p]
  have hgI : ∀ a, ∀ b, IntegrableOn (fun p => p.1 * ‖R.grad p a b‖ ^ 2) K.rect := fun a =>
    vec_int hK _ hF ((continuous_apply a).comp_aestronglyMeasurable hmg) fun p _ => by
      have := Finset.single_le_sum (f := fun a => cnormSq (R.grad p a))
        (fun _ _ => cnormSq_nonneg _) (Finset.mem_univ a)
      linarith [cnormSq_nonneg (R.lap p), cnormSq_nonneg (R.vel p), cnormSq_nonneg (R.presGrad p)]
  have hmg2 : ∀ a b, AEStronglyMeasurable (fun p => R.grad p a b) (volume.restrict K.rect) := fun a b =>
    (continuous_apply b).comp_aestronglyMeasurable ((continuous_apply a).comp_aestronglyMeasurable hmg)
  have hmv2 : ∀ a, AEStronglyMeasurable (fun p => R.vel p a) (volume.restrict K.rect) := fun a =>
    (continuous_apply a).comp_aestronglyMeasurable hmv
  have IS : IntegrableOn (fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
      R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b)) K.rect := by
    have e : (fun p => (p.1 : ℂ) * ∑ a : Fin 3, ∑ b : Fin 3,
        R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
        = fun p => ∑ a : Fin 3, ∑ b : Fin 3,
          (p.1 : ℂ) * R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b) := by
      funext p
      simp only [Finset.mul_sum, mul_assoc]
    rw [e]
    refine integrable_finsetSum _ fun a _ => integrable_finsetSum _ fun b _ => ?_
    obtain ⟨M, hM⟩ := testGrad_bound hK k hreg a b
    exact weighted_int hK (hmg2 a b) (hgI a b) (testGrad_meas K k φ a b) hM
  have IA : IntegrableOn (fun p => (p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
      + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p)) K.rect := by
    have e : (fun p => (p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
        + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p))
        = fun p => ∑ a : Fin 3, ((p.1 : ℂ) * R.vel p a
            * (((freq : ℂ) * Complex.I + 1 / 2) * (starRingEnd ℂ) ((φ a).eval K p))
          + (p.1 : ℂ) * R.grad p a 0 * ((1 / 2 : ℂ) * (p.1 : ℂ) * (starRingEnd ℂ) ((φ a).eval K p))
          + (p.1 : ℂ) * R.grad p a 2 * ((1 / 2 : ℂ) * (p.2 : ℂ) * (starRingEnd ℂ) ((φ a).eval K p))) := by
      funext p
      simp only [cdot3, testValue, Fin.sum_univ_three]
      ring
    rw [e]
    refine integrable_finsetSum _ fun a _ => ?_
    have hcj := Complex.continuous_conj.comp (eval_cont K (φ a))
    refine ((weighted_int_cont hK (hmv2 a) (hvI a) (continuous_const.mul hcj)).add
      (weighted_int_cont hK (hmg2 a 0) (hgI a 0) ?_)).add
      (weighted_int_cont hK (hmg2 a 2) (hgI a 2) ?_)
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_fst)).mul hcj
    · exact (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)).mul hcj
  refine ⟨?_, pair_int hK φ hmv hvI⟩
  have e2 : (fun p => (p.1 : ℂ) *
      ((∑ a : Fin 3, ∑ b : Fin 3, R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
        + cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p)))
      = fun p => (p.1 : ℂ) * (∑ a : Fin 3, ∑ b : Fin 3, R.grad p a b * (starRingEnd ℂ) (testGrad K k φ p a b))
        + (p.1 : ℂ) * cdot3 (fun a => ((freq : ℂ) * Complex.I + 1 / 2) * R.vel p a
          + (1 / 2 : ℂ) * ((p.1 : ℂ) * R.grad p a 0 + (p.2 : ℂ) * R.grad p a 2)) (testValue K φ p) := by
    funext p; ring
  rw [e2]
  exact IS.add IA

theorem rowVolume_freq_shift {K : CellBox} (hK : IsCellBox K) {k : ℝ} {R : RowProfile} (hR : IsRowProfile K k R)
    {φ : Fin 3 → CellPoly} (hreg : IsAxisRegularTest K k φ) (f f' : ℝ) :
    rowVolume K k f R φ = rowVolume K k f' R φ
      + ((f - f' : ℝ) : ℂ) * Complex.I * ∫ p in K.rect, (p.1 : ℂ) * cdot3 (R.vel p) (testValue K φ p) := by
  obtain ⟨h1, h2⟩ := rowVolume_integrable hK hR hreg f'
  unfold rowVolume
  rw [← integral_const_mul, ← integral_add h1 (h2.const_mul _)]
  refine setIntegral_congr_fun (Internal.RowForm.rect_meas K) fun p _ => ?_
  simp only [cdot3, Fin.sum_univ_three, Complex.ofReal_sub]
  ring

def RectSquare (K : CellBox) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict K.rect) ∧ IntegrableOn (fun p => p.1 * ‖f p‖ ^ 2) K.rect

theorem rectSquare_add {K : CellBox} (hK : IsCellBox K) {f g : ℝ × ℝ → ℂ} (hf : RectSquare K f)
    (hg : RectSquare K g) : RectSquare K (fun p => f p + g p) := by
  refine ⟨hf.1.add hg.1, ?_⟩
  refine Integrable.mono' ((hf.2.const_mul 2).add (hg.2.const_mul 2))
    (continuous_fst.aestronglyMeasurable.mul ((hf.1.add hg.1).norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (Internal.RowForm.rect_meas K)] with p hp
  have h0 := Internal.RowForm.fst_nonneg hK hp
  have h1 : ‖f p + g p‖ ≤ ‖f p‖ + ‖g p‖ := norm_add_le _ _
  have h2 : ‖f p + g p‖ ^ 2 ≤ 2 * ‖f p‖ ^ 2 + 2 * ‖g p‖ ^ 2 := by
    nlinarith [norm_nonneg (f p + g p), norm_nonneg (f p), norm_nonneg (g p), sq_nonneg (‖f p‖ - ‖g p‖)]
  rw [Real.norm_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  simp only [Pi.add_apply]
  nlinarith [mul_le_mul_of_nonneg_left h2 h0]

theorem rectSquare_mul {K : CellBox} (hK : IsCellBox K) {f c : ℝ × ℝ → ℂ} (hf : RectSquare K f)
    (hc : AEStronglyMeasurable c (volume.restrict K.rect)) {M : ℝ} (hM : ∀ p ∈ K.rect, ‖c p‖ ≤ M) :
    RectSquare K (fun p => c p * f p) := by
  refine ⟨hc.mul hf.1, ?_⟩
  refine Integrable.mono' (hf.2.const_mul (M ^ 2))
    (continuous_fst.aestronglyMeasurable.mul ((hc.mul hf.1).norm.pow 2)) ?_
  filter_upwards [ae_restrict_mem (Internal.RowForm.rect_meas K)] with p hp
  have h0 := Internal.RowForm.fst_nonneg hK hp
  have hc0 := norm_nonneg (c p)
  have hcM := hM p hp
  rw [Real.norm_of_nonneg (mul_nonneg h0 (sq_nonneg _)), norm_mul, mul_pow]
  have : ‖c p‖ ^ 2 ≤ M ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right this (mul_nonneg h0 (sq_nonneg ‖f p‖))]

theorem rectSquare_bounded {K : CellBox} (hK : IsCellBox K) {f : ℝ × ℝ → ℂ}
    (hf : AEStronglyMeasurable f (volume.restrict K.rect)) {M : ℝ} (hM : ∀ p ∈ K.rect, ‖f p‖ ≤ M) :
    RectSquare K f := by
  have h1 : IntegrableOn (fun p : ℝ × ℝ => p.1) K.rect :=
    continuous_fst.continuousOn.integrableOn_compact (Internal.RowForm.rect_cpt K)
  refine ⟨hf, Integrable.mono' (h1.const_mul (M ^ 2))
    (continuous_fst.aestronglyMeasurable.mul (hf.norm.pow 2)) ?_⟩
  filter_upwards [ae_restrict_mem (Internal.RowForm.rect_meas K)] with p hp
  have h0 := Internal.RowForm.fst_nonneg hK hp
  have hfM := hM p hp
  rw [Real.norm_of_nonneg (mul_nonneg h0 (sq_nonneg _))]
  have : ‖f p‖ ^ 2 ≤ M ^ 2 := by nlinarith [norm_nonneg (f p)]
  nlinarith [mul_le_mul_of_nonneg_left this h0]

theorem rectSquare_const_mul {K : CellBox} (hK : IsCellBox K) {f : ℝ × ℝ → ℂ} (hf : RectSquare K f) (c : ℂ) :
    RectSquare K (fun p => c * f p) :=
  rectSquare_mul hK hf aestronglyMeasurable_const (M := ‖c‖) fun _ _ => le_rfl

theorem rectSquare_sum {K : CellBox} (hK : IsCellBox K) {ι' : Type*} (s : Finset ι') {f : ι' → ℝ × ℝ → ℂ}
    (hf : ∀ i ∈ s, RectSquare K (f i)) : RectSquare K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact rectSquare_bounded hK aestronglyMeasurable_const (M := 0) fun _ _ => by simp
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact rectSquare_add hK (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

theorem rectSquare_pairing {K : CellBox} (hK : IsCellBox K) {f t : ℝ × ℝ → ℂ} (hf : RectSquare K f)
    (ht : AEStronglyMeasurable t (volume.restrict K.rect)) {M : ℝ} (hM : ∀ p ∈ K.rect, ‖t p‖ ≤ M) :
    IntegrableOn (fun p => (p.1 : ℂ) * f p * t p) K.rect :=
  Internal.RowForm.weighted_int hK hf.1 hf.2 ht hM

theorem continuous_axialRot_pair : Continuous (fun q : ℝ × Space => axialRot q.1 q.2) := by
  unfold axialRot
  fun_prop

theorem continuous_axialRot_of {Y : Type*} [TopologicalSpace Y] {a : Y → ℝ} {w : Y → Space}
    (ha : Continuous a) (hw : Continuous w) : Continuous (fun y => axialRot (a y) (w y)) := by
  unfold axialRot
  fun_prop

theorem continuous_planePoint : Continuous (fun p : ℝ × ℝ => planePoint p) := by
  have e : (fun p : ℝ × ℝ => planePoint p) = fun p => p.1 • unitVector 0 + p.2 • unitVector 2 := by
    funext p
    ext i
    fin_cases i <;> simp [planePoint, cylPoint, unitVector]
  rw [e]
  fun_prop

theorem continuous_double_integral {Y : Type*} [TopologicalSpace Y] {F : Y → ℝ → ℝ → ℂ}
    (hF : Continuous (fun q : (Y × ℝ) × ℝ => F q.1.1 q.1.2 q.2)) :
    Continuous (fun y => ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ) := by
  have h1 : Continuous (Function.uncurry fun (x : Y × ℝ) (φ : ℝ) => F x.1 x.2 φ) := hF
  have h2 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) h1 0
    (2 * Real.pi)
  have h3 : Continuous (Function.uncurry fun (y : Y) (τ : ℝ) =>
      ∫ φ in (0 : ℝ)..(2 * Real.pi), F y τ φ) := h2
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume) h3 0 1

theorem continuous_modeAverage {Y β : Type*} [TopologicalSpace Y] (ι : ℤ × ℤ) (g : Y → ℝ → ℝ → β → ℝ) (b : β)
    (hg : Continuous (fun q : (Y × ℝ) × ℝ => g q.1.1 q.1.2 q.2 b)) :
    Continuous (fun y => modeAverage ι (g y) b) := by
  unfold modeAverage
  refine continuous_const.mul (continuous_double_integral
    (F := fun y τ φ => Complex.exp (-(((2 * Real.pi * ι.1 * τ + ι.2 * φ : ℝ) : ℂ) * Complex.I))
      * ((g y τ φ b : ℝ) : ℂ)) ?_)
  have hr : Continuous (fun q : (Y × ℝ) × ℝ => 2 * Real.pi * (ι.1 : ℝ) * q.1.2 + (ι.2 : ℝ) * q.2) := by
    fun_prop
  exact (Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp hr).mul continuous_const).neg).mul
    (Complex.continuous_ofReal.comp hg)

theorem continuous_labelVel {X : ℝ → Space → Space} (hX : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (m : ℕ) (ι : ℤ × ℤ) (a : Fin 3) : Continuous (fun p : ℝ × ℝ => labelVel m ι X p a) := by
  have hp : Continuous (fun q : ((ℝ × ℝ) × ℝ) × ℝ => planePoint q.1.1) :=
    continuous_planePoint.comp (continuous_fst.comp continuous_fst)
  have h1 : Continuous (fun q : ((ℝ × ℝ) × ℝ) × ℝ => axialRot q.2 (planePoint q.1.1)) :=
    continuous_axialRot_of continuous_snd hp
  have h2 : Continuous (fun q : ((ℝ × ℝ) × ℝ) × ℝ => X (0 + q.1.2) (axialRot q.2 (planePoint q.1.1))) :=
    hX.comp ((continuous_const.add continuous_fst.snd).prodMk h1)
  have h3 : Continuous (fun q : ((ℝ × ℝ) × ℝ) × ℝ =>
      axialRot (-q.2) (X (0 + q.1.2) (axialRot q.2 (planePoint q.1.1))) a) :=
    (EuclideanSpace.proj a : Space →L[ℝ] ℝ).continuous.comp (continuous_axialRot_of continuous_snd.neg h2)
  exact continuous_modeAverage (labelHarmonic m ι)
    (fun (p : ℝ × ℝ) τ φ i => axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p))) i) a h3

theorem continuous_crossTest_comp {W Ω φ : ℝ × ℝ → Fin 3 → ℂ} (hW : ∀ a, Continuous fun p => W p a)
    (hΩ : ∀ a, Continuous fun p => Ω p a) (hφ : ∀ a, Continuous fun p => φ p a) (j : Fin 12) :
    Continuous (fun p => crossTest (W p) (Ω p) (φ p) j) := by
  unfold crossTest pairVec
  split_ifs
  · refine Complex.continuous_conj.comp ?_
    refine continuous_finsetSum _ fun i _ => continuous_const.mul ?_
    refine continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l' _ => ?_
    exact (continuous_const.mul (hW j')).mul (Complex.continuous_conj.comp (hφ l'))
  · refine Complex.continuous_conj.comp ?_
    refine continuous_finsetSum _ fun j' _ => continuous_finsetSum _ fun l' _ => ?_
    exact (continuous_const.mul (Complex.continuous_conj.comp (hφ j'))).mul (hΩ l')

theorem rect_regular_of_eqOn {K : CellBox} {f f' : ℝ × ℝ → ℂ} (hf' : Continuous f')
    (h : ∀ p ∈ K.rect, f p = f' p) :
    AEStronglyMeasurable f (volume.restrict K.rect) ∧ ∃ M : ℝ, ∀ p ∈ K.rect, ‖f p‖ ≤ M := by
  refine ⟨hf'.aestronglyMeasurable.congr ?_, ?_⟩
  · filter_upwards [ae_restrict_mem (Internal.RowForm.rect_meas K)] with p hp
    exact (h p hp).symm
  · obtain ⟨M, hM⟩ := (Internal.RowForm.rect_cpt K).exists_bound_of_continuousOn hf'.continuousOn
    exact ⟨M, fun p hp => (h p hp) ▸ hM p hp⟩

end Breakdown.CertCell.Assembly.Internal.RowIdentity
