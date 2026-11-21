import Breakdown.FracCell.EnergyPair
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.ModelFormParts

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.EnergyPairIntegrable

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellEnergy Assembly
open CellCert.CellAnalysis.LowEntry.Internal CellCert.CellAnalysis.ModeGradSquare.Internal CellCert.ModelFormInternal

def Bdd (K : CellBox) (f : ℝ × ℝ → ℂ) : Prop :=
  AEStronglyMeasurable f (volume.restrict K.rect) ∧ ∃ C : ℝ, ∀ p ∈ K.rect, ‖f p‖ ≤ C

theorem bdd_const (K : CellBox) (z : ℂ) : Bdd K (fun _ => z) :=
  ⟨aestronglyMeasurable_const, ‖z‖, fun _ _ => le_rfl⟩

theorem bdd_add {K : CellBox} {f g : ℝ × ℝ → ℂ} (hf : Bdd K f) (hg : Bdd K g) :
    Bdd K (fun p => f p + g p) := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  exact ⟨hf.add hg, C + D, fun p hp => (norm_add_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

theorem bdd_sub {K : CellBox} {f g : ℝ × ℝ → ℂ} (hf : Bdd K f) (hg : Bdd K g) :
    Bdd K (fun p => f p - g p) := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  exact ⟨hf.sub hg, C + D, fun p hp => (norm_sub_le _ _).trans (add_le_add (hC p hp) (hD p hp))⟩

theorem bdd_neg {K : CellBox} {f : ℝ × ℝ → ℂ} (hf : Bdd K f) : Bdd K (fun p => -f p) := by
  obtain ⟨hf, C, hC⟩ := hf
  exact ⟨hf.neg, C, fun p hp => by rw [norm_neg]; exact hC p hp⟩

theorem bdd_mul {K : CellBox} {f g : ℝ × ℝ → ℂ} (hf : Bdd K f) (hg : Bdd K g) :
    Bdd K (fun p => f p * g p) := by
  obtain ⟨hf, C, hC⟩ := hf
  obtain ⟨hg, D, hD⟩ := hg
  refine ⟨hf.mul hg, |C| * |D|, fun p hp => ?_⟩
  rw [norm_mul]
  exact mul_le_mul ((hC p hp).trans (le_abs_self C)) ((hD p hp).trans (le_abs_self D)) (norm_nonneg _)
    (abs_nonneg _)

theorem bdd_conj {K : CellBox} {f : ℝ × ℝ → ℂ} (hf : Bdd K f) : Bdd K (fun p => (starRingEnd ℂ) (f p)) := by
  obtain ⟨hf, C, hC⟩ := hf
  exact ⟨Complex.continuous_conj.comp_aestronglyMeasurable hf, C, fun p hp => by
    rw [Complex.norm_conj]; exact hC p hp⟩

theorem bdd_sum {K : CellBox} {ι : Type*} (s : Finset ι) {f : ι → ℝ × ℝ → ℂ} (hf : ∀ i ∈ s, Bdd K (f i)) :
    Bdd K (fun p => ∑ i ∈ s, f i p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bdd_const K 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact bdd_add (hf i (Finset.mem_insert_self i s)) (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem bdd_cont (K : CellBox) {f : ℝ × ℝ → ℂ} (hf : Continuous f) : Bdd K f := by
  obtain ⟨C, hC⟩ := (rect_compact K).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨hf.aestronglyMeasurable, C, hC⟩

theorem Bdd.integrableOn {K : CellBox} {f : ℝ × ℝ → ℂ} (hf : Bdd K f) : IntegrableOn f K.rect := by
  obtain ⟨hm, C, hC⟩ := hf
  refine ⟨hm, HasFiniteIntegral.restrict_of_bounded (C := C) (rect_compact K).measure_lt_top ?_⟩
  filter_upwards [ae_restrict_mem (measurableSet_Icc.prod measurableSet_Icc)] with p hp
  exact hC p hp

theorem bdd_basis (K : CellBox) (B : CellBases) (j l : ℕ) : Bdd K (fun p => ((basisFn B j l p : ℝ) : ℂ)) := by
  refine bdd_cont K ?_
  simp only [basisFn, CellBases.radialPoly, CellBases.heightPoly]
  fun_prop

theorem bdd_slot_fst (K : CellBox) (B : CellBases) {Q : ℕ} (τ : LowSlot Q) (a b : Fin 3) :
    Bdd K (fun p => (slotValue B τ p).1 a b) := by
  cases τ with
  | strain a' b' j l =>
    by_cases h : a = a' ∧ b = b'
    · simp only [slotValue, if_pos h]
      exact bdd_basis K B j l
    · simp only [slotValue, if_neg h]
      exact bdd_const K 0
  | velocity a' j l =>
    simp only [slotValue]
    exact bdd_const K 0

theorem bdd_slot_snd (K : CellBox) (B : CellBases) {Q : ℕ} (τ : LowSlot Q) (a : Fin 3) :
    Bdd K (fun p => (slotValue B τ p).2 a) := by
  cases τ with
  | strain a' b' j l =>
    simp only [slotValue]
    exact bdd_const K 0
  | velocity a' j l =>
    by_cases h : a = a'
    · simp only [slotValue, if_pos h]
      exact bdd_basis K B j l
    · simp only [slotValue, if_neg h]
      exact bdd_const K 0

theorem bdd_mode {K : CellBox} (hK : IsCellBox K) (m : ℕ) (n : ℤ) {G : Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable G volume) (C : ℝ) (hC : ∀ y, ‖G y‖ ≤ C) (a b : Fin 3) :
    Bdd K (fun p => modeMat m n G p.1 p.2 a b) := by
  refine ⟨gm_meas K hK m n hG a b, C, fun p _ => ?_⟩
  have e := gradMode_eq m n G a b p
  unfold gradMode at e
  show ‖modeMat m n G p.1 p.2 a b‖ ≤ C
  rw [e, norm_mul]
  have hi : ‖∫ θ in Ioo (-Real.pi) Real.pi, gradKernel m n a b θ (G (cylPoint p.1 θ p.2))‖ ≤
      C * volume.real (Ioo (-Real.pi) Real.pi) :=
    norm_setIntegral_le_of_norm_le_const measure_Ioo_lt_top
      (fun θ _ => (gradKernel_bound m n a b θ _).trans (hC _))
  rw [Real.volume_real_Ioo] at hi
  have hp := Real.pi_pos
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  rw [hn]
  rw [max_eq_left (by linarith)] at hi
  calc 1 / (2 * Real.pi) * ‖∫ θ in Ioo (-Real.pi) Real.pi, gradKernel m n a b θ (G (cylPoint p.1 θ p.2))‖
      ≤ 1 / (2 * Real.pi) * (C * (Real.pi - -Real.pi)) := by gcongr
    _ = C := by field_simp; ring

theorem bdd_curl {K : CellBox} {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} (hs : ∀ a b, Bdd K (fun p => s p a b))
    (i : Fin 3) : Bdd K (fun p => curlComp (s p) i) := by
  simp only [curlComp]
  exact bdd_sum _ fun j _ => bdd_sum _ fun l _ => bdd_mul (bdd_const _ _) (hs l j)

theorem bdd_coupling {K : CellBox} {M : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hM : ∀ a b, Bdd K (fun p => M p a b)) (hv : ∀ a, Bdd K (fun p => v p a)) (i l : Fin 3) :
    Bdd K (fun p => couplingMap (M p) (v p) i l) := by
  simp only [couplingMap, bracketMat]
  exact bdd_add (bdd_neg (bdd_sum _ fun j _ => bdd_mul (bdd_const _ _)
      (bdd_sum _ fun b _ => bdd_mul (hM j b) (hv b))))
    (bdd_mul (bdd_const _ _) (bdd_sum _ fun q _ => bdd_mul
      (bdd_sum _ fun j _ => bdd_mul (bdd_const _ _) (hv j)) (hM l q)))

theorem bdd_wave {K : CellBox} {Sm Gm Gm' s s' : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v v' : ℝ × ℝ → Fin 3 → ℂ}
    (hSm : ∀ a b, Bdd K (fun p => Sm p a b)) (hGm : ∀ a b, Bdd K (fun p => Gm p a b))
    (hGm' : ∀ a b, Bdd K (fun p => Gm' p a b)) (hs : ∀ a b, Bdd K (fun p => s p a b))
    (hs' : ∀ a b, Bdd K (fun p => s' p a b)) (hv : ∀ a, Bdd K (fun p => v p a))
    (hv' : ∀ a, Bdd K (fun p => v' p a)) :
    Bdd K (fun p => waveForm (Sm p) (Gm p) (Gm' p) (s p) (v p) (s' p) (v' p)) := by
  have hc := bdd_curl hs
  have hc' := bdd_curl hs'
  have hk := bdd_coupling hGm hv'
  have hk' := bdd_coupling hGm' hv
  simp only [waveForm, entryPairing]
  exact bdd_add (bdd_add (bdd_neg (bdd_sum _ fun a _ => bdd_mul (bdd_conj (hc a))
      (bdd_sum _ fun b _ => bdd_mul (hSm a b) (hc' b))))
    (bdd_mul (bdd_const _ _) (bdd_sum _ fun a _ => bdd_sum _ fun b _ => bdd_mul (hk a b) (bdd_conj (hs a b)))))
    (bdd_mul (bdd_const _ _) (bdd_sum _ fun a _ => bdd_sum _ fun b _ => bdd_mul (hs' a b) (bdd_conj (hk' a b))))

theorem bdd_pairVec {K : CellBox} {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hs : ∀ a b, Bdd K (fun p => s p a b)) (hv : ∀ a, Bdd K (fun p => v p a)) (i : Fin 12) :
    Bdd K (fun p => pairVec (s p) (v p) i) := by
  by_cases h : i.val < 9
  · simp only [pairVec, dif_pos h]
    exact hs _ _
  · simp only [pairVec, dif_neg h]
    exact hv _

theorem bdd_msesq {K : CellBox} {A : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} {U U' : ℝ × ℝ → Fin 12 → ℂ}
    (hA : ∀ i j, Bdd K (fun p => A p i j)) (hU : ∀ i, Bdd K (fun p => U p i)) (hU' : ∀ i, Bdd K (fun p => U' p i)) :
    Bdd K (fun p => matrixSesq (A p) (U p) (U' p)) := by
  simp only [matrixSesq]
  exact bdd_sum _ fun i _ => bdd_sum _ fun j _ => bdd_mul (bdd_mul (bdd_conj (hU i)) (hA i j)) (hU' j)

theorem weight_eq (K : CellBox) (p : ℝ × ℝ) : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs
  · by_cases h : p.1 = 0
    · rw [h]; simp
    · field_simp
  · simp

end Breakdown.FracInternal.EnergyPairIntegrable

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly
open Breakdown.FracInternal.EnergyPairIntegrable CellCert.ModelFormInternal

theorem pairIntegrable_holds : PairIntegrableStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u h n n' τ τ'
  obtain ⟨hm, -, -, hK, -, hsc, -, -, hf⟩ := h
  subst hm
  obtain ⟨C, hC⟩ := hf.model_bounded
  obtain ⟨Cc, hCc⟩ := hf.centre_bounds
  have hCc0 := centre_nonneg hCc
  have hSb : ∀ y, ‖c.modelStrain y‖ ≤ max C Cc := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · exact (hC y hy).2.2.1.trans (le_max_left _ _)
    · rw [(hf.model_outside y hy).1]
      exact ((norm_symPart_le _).trans ((hCc y).2.1.trans
        (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 2 (by norm_num))))).trans (le_max_right _ _)
  have hGb : ∀ y, ‖c.modelCurlGrad y‖ ≤ max C (81 * Cc) := by
    intro y
    by_cases hy : y ∈ c.cellRegion
    · exact (hC y hy).2.2.2.trans (le_max_left _ _)
    · rw [(hf.model_outside y hy).2]
      refine ((norm_curlGradMatrix_le _).trans ?_).trans (le_max_right _ _)
      have := (hCc y).2.2.trans (mul_le_of_le_one_right hCc0 (rpow_neg_le_one y 3 (by norm_num)))
      linarith
  have hSm : ∀ (β : ℤ) (a b : Fin 3), Bdd K (fun p => CellScalars.strainMode c β p a b) :=
    fun β a b => bdd_mode hK c.order β hf.model_measurable.2.2.1 _ hSb a b
  have hGm : ∀ (β : ℤ) (a b : Fin 3), Bdd K (fun p => CellScalars.curlGradMode c β p a b) :=
    fun β a b => bdd_mode hK c.order β hf.model_measurable.2.2.2 _ hGb a b
  have hw : Bdd K (fun p => ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ)) := by
    have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ)) = fun p => ((p.1 : ℝ) : ℂ) :=
      funext fun p => by rw [weight_eq]
    rw [e]
    exact bdd_cont K (by fun_prop)
  refine Bdd.integrableOn (bdd_mul hw ?_)
  simp only [pairSesq]
  refine bdd_add (bdd_wave (hSm _) (hGm _) (hGm _) (bdd_slot_fst K B τ) (bdd_slot_fst K B τ')
    (bdd_slot_snd K B τ) (bdd_slot_snd K B τ')) ?_
  by_cases hnn : (n : ℤ) = n'
  · simp only [if_pos hnn]
    obtain ⟨hlm, CL, hCL⟩ := hsc.data_regular.1 n n.2
    refine bdd_msesq (fun i j => ⟨(hlm i j).aestronglyMeasurable, CL, fun p hp => hCL p hp i j⟩)
      (bdd_pairVec (bdd_slot_fst K B τ) (bdd_slot_snd K B τ))
      (bdd_pairVec (bdd_slot_fst K B τ') (bdd_slot_snd K B τ'))
  · simp only [if_neg hnn]
    exact bdd_const K 0

end Breakdown.CellCert.CellEnergy
