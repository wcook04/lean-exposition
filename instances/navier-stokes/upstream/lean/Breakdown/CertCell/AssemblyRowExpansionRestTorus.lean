import Breakdown.CertCell.AssemblyRowExpansionRestTests
import Breakdown.CertCell.AssemblyPotentialModelTorusMeanFacts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation TorusMean CellCert.CellAnalysis CellCert.CellFormula
  CellCalculus

def coefOf (m : ℕ) (ℓ : ℤ × ℤ) (h : ℝ → ℝ → ℂ) : ℂ :=
  torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m ℓ τ φ) * h τ φ)

theorem labelPhase_continuous (m : ℕ) (α : ℤ × ℤ) : Continuous (fun z : ℝ × ℝ => labelPhase m α z.1 z.2) := by
  unfold labelPhase
  fun_prop

theorem norm_labelPhase (m : ℕ) (α : ℤ × ℤ) (τ φ : ℝ) : ‖labelPhase m α τ φ‖ = 1 := by
  unfold labelPhase
  rw [Complex.norm_exp_ofReal_mul_I]

theorem torusIntegrable_of_continuous {f : ℝ → ℝ → ℂ} (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2))
    (hb : ∃ C : ℝ, ∀ τ φ, ‖f τ φ‖ ≤ C) : IsTorusIntegrable f := by
  obtain ⟨C, hC⟩ := hb
  exact bounded_integrable f hf.aestronglyMeasurable ⟨C, fun τ φ _ _ _ _ => hC τ φ⟩

theorem torusIntegrable_phase_mul (m : ℕ) (α : ℤ × ℤ) {h : ℝ → ℝ → ℂ} (hh : IsTorusIntegrable h) :
    IsTorusIntegrable (fun τ φ => labelPhase m α τ φ * h τ φ) := by
  unfold IsTorusIntegrable at hh ⊢
  refine hh.norm.mono' ((labelPhase_continuous m α).aestronglyMeasurable.mul hh.1)
    (Filter.Eventually.of_forall fun z => ?_)
  rw [norm_mul, norm_labelPhase, one_mul]

theorem phase_mul_conj (m : ℕ) (α β : ℤ × ℤ) (τ φ : ℝ) :
    labelPhase m α τ φ * (starRingEnd ℂ) (labelPhase m β τ φ) = (starRingEnd ℂ) (labelPhase m (β - α) τ φ) := by
  rw [conj_labelPhase_sub]
  ring

theorem torusMean_phase_conj (m : ℕ) (hm : 1 ≤ m) (α β : ℤ × ℤ) :
    torusMean (fun τ φ => labelPhase m α τ φ * (starRingEnd ℂ) (labelPhase m β τ φ)) = if α = β then 1 else 0 := by
  simp only [phase_mul_conj]
  rw [torusMean_label m hm]
  by_cases h : α = β
  · rw [if_pos (by rw [h, sub_self]), if_pos h]
  · rw [if_neg (fun e => h (sub_eq_zero.mp e).symm), if_neg h]

theorem coefOf_phase_mul (m : ℕ) (ℓ α : ℤ × ℤ) (h : ℝ → ℝ → ℂ) :
    coefOf m ℓ (fun τ φ => labelPhase m α τ φ * h τ φ) = coefOf m (ℓ - α) h := by
  unfold coefOf
  congr 1
  funext τ φ
  rw [conj_labelPhase_sub]
  ring

theorem torusIntegrable_const (c : ℂ) : IsTorusIntegrable (fun _ _ => c) :=
  torusIntegrable_of_continuous continuous_const ⟨‖c‖, fun _ _ => le_rfl⟩

theorem coefOf_trig (m : ℕ) (hm : 1 ≤ m) (ℓ : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → ℂ) :
    coefOf m ℓ (fun τ φ => ∑ α ∈ S, x α * labelPhase m α τ φ) = if ℓ ∈ S then x ℓ else 0 := by
  unfold coefOf
  have e : (fun τ φ => (starRingEnd ℂ) (labelPhase m ℓ τ φ) * ∑ α ∈ S, x α * labelPhase m α τ φ)
      = fun τ φ => ∑ α ∈ S, x α * (labelPhase m α τ φ * (starRingEnd ℂ) (labelPhase m ℓ τ φ)) := by
    funext τ φ
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun α _ => ?_)
    ring
  rw [e, torusMean_sum S _ (fun α _ => ?_)]
  · simp only [torusMean_const_mul, torusMean_phase_conj m hm]
    simp only [mul_ite, mul_one, mul_zero]
    rw [Finset.sum_ite_eq']
  · exact (torusIntegrable_phase_mul m α (torusIntegrable_of_continuous
      (f := fun τ φ => (starRingEnd ℂ) (labelPhase m ℓ τ φ))
      (Complex.continuous_conj.comp (labelPhase_continuous m ℓ))
      ⟨1, fun τ φ => by rw [Complex.norm_conj, norm_labelPhase]⟩)).const_mul (x α)

theorem trig_continuous (m : ℕ) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → ℂ) :
    Continuous (fun z : ℝ × ℝ => ∑ α ∈ S, x α * labelPhase m α z.1 z.2) :=
  continuous_finsetSum S (fun α _ => continuous_const.mul (labelPhase_continuous m α))

theorem norm_trig_le (m : ℕ) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → ℂ) (τ φ : ℝ) :
    ‖∑ α ∈ S, x α * labelPhase m α τ φ‖ ≤ ∑ α ∈ S, ‖x α‖ := by
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum (fun α _ => ?_))
  rw [norm_mul, norm_labelPhase, mul_one]

theorem trig_integrable (m : ℕ) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → ℂ) :
    IsTorusIntegrable (fun τ φ => ∑ α ∈ S, x α * labelPhase m α τ φ) :=
  torusIntegrable_of_continuous (trig_continuous m S x) ⟨_, norm_trig_le m S x⟩

theorem torusMean_trig_sq (m : ℕ) (hm : 1 ≤ m) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → ℂ) :
    torusMean (fun τ φ => (∑ α ∈ S, x α * labelPhase m α τ φ) * (starRingEnd ℂ) (∑ α ∈ S, x α * labelPhase m α τ φ))
      = ∑ α ∈ S, ((‖x α‖ ^ 2 : ℝ) : ℂ) := by
  have e : (fun τ φ => (∑ α ∈ S, x α * labelPhase m α τ φ) * (starRingEnd ℂ) (∑ α ∈ S, x α * labelPhase m α τ φ))
      = fun τ φ => ∑ β ∈ S, (starRingEnd ℂ) (x β) * ((starRingEnd ℂ) (labelPhase m β τ φ) *
          ∑ α ∈ S, x α * labelPhase m α τ φ) := by
    funext τ φ
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun β _ => ?_)
    rw [map_mul]
    ring
  rw [e, torusMean_sum S _ (fun β _ => ?_)]
  · refine Finset.sum_congr rfl (fun β hβ => ?_)
    have h1 : torusMean (fun τ φ => (starRingEnd ℂ) (x β) * ((starRingEnd ℂ) (labelPhase m β τ φ) *
        ∑ α ∈ S, x α * labelPhase m α τ φ))
        = (starRingEnd ℂ) (x β) * coefOf m β (fun τ φ => ∑ α ∈ S, x α * labelPhase m α τ φ) :=
      torusMean_const_mul _ _
    rw [h1, coefOf_trig m hm β S x, if_pos hβ, Complex.conj_mul', Complex.ofReal_pow]
  · have h := isTorusIntegrable_conj_label_mul m β (trig_integrable m S x)
    unfold IsTorusIntegrable at h ⊢
    exact h.const_mul ((starRingEnd ℂ) (x β))

theorem re_two_mul_conj_sub_le (f u : ℂ) :
    (2 * (f * (starRingEnd ℂ) u) + (-1) * (u * (starRingEnd ℂ) u)).re ≤ ((‖f‖ ^ 2 : ℝ) : ℂ).re := by
  rw [Complex.ofReal_re, Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.mul_im]
  norm_num
  nlinarith [sq_nonneg (f.re - u.re), sq_nonneg (f.im - u.im)]

theorem coef_sq_sum_le (m : ℕ) (hm : 1 ≤ m) (S : Finset (ℤ × ℤ)) (h : ℝ → ℝ → ℂ)
    (hh : IsTorusIntegrable h) (hh2 : IsTorusIntegrable (fun τ φ => ((‖h τ φ‖ ^ 2 : ℝ) : ℂ))) :
    ∑ ℓ ∈ S, ‖coefOf m ℓ h‖ ^ 2 ≤ (torusMean (fun τ φ => ((‖h τ φ‖ ^ 2 : ℝ) : ℂ))).re := by
  set c : ℤ × ℤ → ℂ := fun ℓ => coefOf m ℓ h with hc
  set P : ℝ → ℝ → ℂ := fun τ φ => ∑ ℓ ∈ S, c ℓ * labelPhase m ℓ τ φ with hP
  have hPi : IsTorusIntegrable P := trig_integrable m S c
  have hA : torusMean (fun τ φ => h τ φ * (starRingEnd ℂ) (P τ φ)) = ∑ ℓ ∈ S, ((‖c ℓ‖ ^ 2 : ℝ) : ℂ) := by
    have e : (fun τ φ => h τ φ * (starRingEnd ℂ) (P τ φ))
        = fun τ φ => ∑ ℓ ∈ S, (starRingEnd ℂ) (c ℓ) * ((starRingEnd ℂ) (labelPhase m ℓ τ φ) * h τ φ) := by
      funext τ φ
      rw [hP, map_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      rw [map_mul]
      ring
    rw [e, torusMean_sum S _ (fun ℓ _ => ?_)]
    · refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      have h1 : torusMean (fun τ φ => (starRingEnd ℂ) (c ℓ) * ((starRingEnd ℂ) (labelPhase m ℓ τ φ) * h τ φ))
          = (starRingEnd ℂ) (c ℓ) * c ℓ := torusMean_const_mul _ _
      rw [h1, Complex.conj_mul', Complex.ofReal_pow]
    · have h2 := isTorusIntegrable_conj_label_mul m ℓ hh
      unfold IsTorusIntegrable at h2 ⊢
      exact h2.const_mul ((starRingEnd ℂ) (c ℓ))
  have hB : torusMean (fun τ φ => P τ φ * (starRingEnd ℂ) (P τ φ)) = ∑ ℓ ∈ S, ((‖c ℓ‖ ^ 2 : ℝ) : ℂ) :=
    torusMean_trig_sq m hm S c
  have hAi : IsTorusIntegrable (fun τ φ => h τ φ * (starRingEnd ℂ) (P τ φ)) := by
    unfold IsTorusIntegrable at hh ⊢
    have hcP : Continuous (fun z : ℝ × ℝ => (starRingEnd ℂ) (P z.1 z.2)) :=
      Complex.continuous_conj.comp (trig_continuous m S c)
    refine (hh.norm.const_mul (∑ ℓ ∈ S, ‖c ℓ‖)).mono' (hh.1.mul hcP.aestronglyMeasurable)
      (Filter.Eventually.of_forall (fun z => ?_))
    rw [norm_mul, Complex.norm_conj, mul_comm]
    exact mul_le_mul_of_nonneg_right (norm_trig_le m S c z.1 z.2) (norm_nonneg _)
  have hBi : IsTorusIntegrable (fun τ φ => P τ φ * (starRingEnd ℂ) (P τ φ)) :=
    torusIntegrable_of_continuous ((trig_continuous m S c).mul (Complex.continuous_conj.comp (trig_continuous m S c)))
      ⟨(∑ ℓ ∈ S, ‖c ℓ‖) * (∑ ℓ ∈ S, ‖c ℓ‖), fun τ φ => by
        rw [norm_mul, Complex.norm_conj]
        exact mul_le_mul (norm_trig_le m S c τ φ) (norm_trig_le m S c τ φ) (norm_nonneg _)
          (Finset.sum_nonneg (fun _ _ => norm_nonneg _))⟩
  have hF : IsTorusIntegrable (fun τ φ => 2 * (h τ φ * (starRingEnd ℂ) (P τ φ)) + (-1) * (P τ φ * (starRingEnd ℂ) (P τ φ))) := by
    unfold IsTorusIntegrable at hAi hBi ⊢
    exact (hAi.const_mul 2).add (hBi.const_mul (-1))
  have hmono := torusMean_re_mono _ _ hF hh2 (fun τ φ _ _ _ _ => re_two_mul_conj_sub_le (h τ φ) (P τ φ))
  have hval : torusMean (fun τ φ => 2 * (h τ φ * (starRingEnd ℂ) (P τ φ)) + (-1) * (P τ φ * (starRingEnd ℂ) (P τ φ)))
      = ∑ ℓ ∈ S, ((‖c ℓ‖ ^ 2 : ℝ) : ℂ) := by
    have hAi2 : IsTorusIntegrable (fun τ φ => 2 * (h τ φ * (starRingEnd ℂ) (P τ φ))) := by
      unfold IsTorusIntegrable at hAi ⊢; exact hAi.const_mul 2
    have hBi2 : IsTorusIntegrable (fun τ φ => (-1) * (P τ φ * (starRingEnd ℂ) (P τ φ))) := by
      unfold IsTorusIntegrable at hBi ⊢; exact hBi.const_mul (-1)
    rw [torusMean_add _ _ hAi2 hBi2, torusMean_const_mul, torusMean_const_mul, hA, hB]
    ring
  rw [hval, Complex.re_sum] at hmono
  simp only [Complex.ofReal_re] at hmono
  exact hmono

def crossC (a b : Fin 3 → ℂ) : Fin 3 → ℂ :=
  ![a 1 * b 2 - a 2 * b 1, a 2 * b 0 - a 0 * b 2, a 0 * b 1 - a 1 * b 0]

theorem crossC_norm_le (a b : Fin 3 → ℂ) :
    ∑ c, ‖crossC a b c‖ ^ 2 ≤ (∑ i, ‖a i‖ ^ 2) * (∑ i, ‖b i‖ ^ 2) := by
  simp only [Fin.sum_univ_three, crossC, Complex.sq_norm, Complex.normSq_apply, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im]
  nlinarith [sq_nonneg ((a 0).re * (b 0).re + (a 0).im * (b 0).im + (a 1).re * (b 1).re + (a 1).im * (b 1).im
      + (a 2).re * (b 2).re + (a 2).im * (b 2).im),
    sq_nonneg ((a 0).im * (b 0).re - (a 0).re * (b 0).im + (a 1).im * (b 1).re - (a 1).re * (b 1).im
      + (a 2).im * (b 2).re - (a 2).re * (b 2).im)]

def curlOfU (U : Fin 12 → ℂ) : Fin 3 → ℂ := fun i => curlComp (fun a b => U ⟨3 * a.val + b.val, by omega⟩) i

def velOfU (U : Fin 12 → ℂ) : Fin 3 → ℂ := fun a => U ⟨9 + a.val, by omega⟩

def crossVec (U : Fin 12 → ℂ) (W Ω : Fin 3 → ℂ) : Fin 3 → ℂ := fun c => crossC (curlOfU U) W c + crossC Ω (velOfU U) c

theorem alternatingSymbol_cast_eq (i j l : Fin 3) :
    ((alternatingSymbol i j l : ℝ) : ℂ) = ((CellCert.permSign i j l : ℝ) : ℂ) := by
  congr 1
  fin_cases i <;> fin_cases j <;> fin_cases l <;> norm_num [alternatingSymbol, CellCert.permSign]

theorem crossTest_pairing (U : Fin 12 → ℂ) (W Ω φ : Fin 3 → ℂ) :
    ∑ j, U j * (starRingEnd ℂ) (crossTest W Ω φ j) = ∑ c, crossVec U W Ω c * (starRingEnd ℂ) (φ c) := by
  simp only [crossTest, alternatingSymbol_cast_eq]
  simp [pairVec, crossVec, crossC, curlOfU, velOfU, curlComp, Fin.sum_univ_succ, CellCert.permSign]
  ring

theorem norm_add_sq_le_two (x y : ℂ) : ‖x + y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h := norm_add_le x y
  have h2 : ‖x + y‖ ^ 2 ≤ (‖x‖ + ‖y‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
  nlinarith [sq_nonneg (‖x‖ - ‖y‖)]

theorem crossVec_norm_le (U : Fin 12 → ℂ) (W Ω : Fin 3 → ℂ) :
    ∑ c, ‖crossVec U W Ω c‖ ^ 2
      ≤ 2 * ((∑ i, ‖curlOfU U i‖ ^ 2) * (∑ i, ‖W i‖ ^ 2)) + 2 * ((∑ i, ‖Ω i‖ ^ 2) * (∑ i, ‖velOfU U i‖ ^ 2)) := by
  have h1 := crossC_norm_le (curlOfU U) W
  have h2 := crossC_norm_le Ω (velOfU U)
  have h3 : ∑ c, ‖crossVec U W Ω c‖ ^ 2 ≤ ∑ c, (2 * ‖crossC (curlOfU U) W c‖ ^ 2 + 2 * ‖crossC Ω (velOfU U) c‖ ^ 2) :=
    Finset.sum_le_sum (fun c _ => norm_add_sq_le_two _ _)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h3
  nlinarith

theorem curlOfU_explicit (U : Fin 12 → ℂ) :
    curlOfU U 0 = U 7 - U 5 ∧ curlOfU U 1 = U 2 - U 6 ∧ curlOfU U 2 = U 3 - U 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [curlOfU, curlComp, Fin.sum_univ_three, CellCert.permSign] <;> ring_nf

theorem crossVec_expand_U (U : Fin 12 → ℂ) (W Ω : Fin 3 → ℂ) (c : Fin 3) :
    crossVec U W Ω c = ∑ J, U J * crossVec (Pi.single J 1) W Ω c := by
  have e1 := curlOfU_explicit U
  have hs : ∀ J : Fin 12, curlOfU (Pi.single J 1) 0 = (Pi.single J 1 : Fin 12 → ℂ) 7 - (Pi.single J 1 : Fin 12 → ℂ) 5 ∧
      curlOfU (Pi.single J 1) 1 = (Pi.single J 1 : Fin 12 → ℂ) 2 - (Pi.single J 1 : Fin 12 → ℂ) 6 ∧
      curlOfU (Pi.single J 1) 2 = (Pi.single J 1 : Fin 12 → ℂ) 3 - (Pi.single J 1 : Fin 12 → ℂ) 1 :=
    fun J => curlOfU_explicit _
  fin_cases c <;>
  · simp only [crossVec, crossC, velOfU, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk]
    simp only [e1.1, e1.2.1, e1.2.2, (hs _).1, (hs _).2.1, (hs _).2.2]
    simp [Fin.sum_univ_succ, Pi.single_apply]
    ring

theorem crossVec_expand_WΩ (U : Fin 12 → ℂ) (W Ω : Fin 3 → ℂ) (c : Fin 3) :
    crossVec U W Ω c = ∑ j, crossVec U (Pi.single j 1) 0 c * W j + ∑ l, crossVec U 0 (Pi.single l 1) c * Ω l := by
  fin_cases c <;> simp [crossVec, crossC, Fin.sum_univ_three, Pi.single_apply] <;> ring

theorem coefOf_lin (m : ℕ) (β : ℤ × ℤ) (A B : Fin 3 → ℂ) (F G : Fin 3 → ℝ → ℝ → ℂ)
    (hF : ∀ j, IsTorusIntegrable (F j)) (hG : ∀ j, IsTorusIntegrable (G j)) :
    coefOf m β (fun τ φ => ∑ j, A j * F j τ φ + ∑ l, B l * G l τ φ)
      = ∑ j, A j * coefOf m β (F j) + ∑ l, B l * coefOf m β (G l) := by
  unfold coefOf
  have e : (fun τ φ => (starRingEnd ℂ) (labelPhase m β τ φ) * (∑ j, A j * F j τ φ + ∑ l, B l * G l τ φ))
      = fun τ φ => (∑ j, A j * ((starRingEnd ℂ) (labelPhase m β τ φ) * F j τ φ))
        + ∑ l, B l * ((starRingEnd ℂ) (labelPhase m β τ φ) * G l τ φ) := by
    funext τ φ
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl (fun j _ => ?_) <;> ring
  have hF' : ∀ j, IsTorusIntegrable (fun τ φ => A j * ((starRingEnd ℂ) (labelPhase m β τ φ) * F j τ φ)) := by
    intro j
    have h := isTorusIntegrable_conj_label_mul m β (hF j)
    unfold IsTorusIntegrable at h ⊢
    exact h.const_mul (A j)
  have hG' : ∀ j, IsTorusIntegrable (fun τ φ => B j * ((starRingEnd ℂ) (labelPhase m β τ φ) * G j τ φ)) := by
    intro j
    have h := isTorusIntegrable_conj_label_mul m β (hG j)
    unfold IsTorusIntegrable at h ⊢
    exact h.const_mul (B j)
  rw [e, torusMean_add _ _ (isTorusIntegrable_sum _ _ (fun j _ => hF' j)) (isTorusIntegrable_sum _ _ (fun j _ => hG' j)),
    torusMean_sum _ _ (fun j _ => hF' j), torusMean_sum _ _ (fun j _ => hG' j)]
  simp only [torusMean_const_mul]

theorem coefOf_sum_phase (m : ℕ) (ℓ : ℤ × ℤ) (S : Finset (ℤ × ℤ)) (g : ℤ × ℤ → ℝ → ℝ → ℂ)
    (hg : ∀ ι, IsTorusIntegrable (g ι)) :
    coefOf m ℓ (fun τ φ => ∑ ι ∈ S, labelPhase m ι τ φ * g ι τ φ) = ∑ ι ∈ S, coefOf m (ℓ - ι) (g ι) := by
  have e : coefOf m ℓ (fun τ φ => ∑ ι ∈ S, labelPhase m ι τ φ * g ι τ φ)
      = torusMean (fun τ φ => ∑ ι ∈ S, (starRingEnd ℂ) (labelPhase m ℓ τ φ) * (labelPhase m ι τ φ * g ι τ φ)) := by
    unfold coefOf
    congr 1
    funext τ φ
    rw [Finset.mul_sum]
  rw [e, torusMean_sum _ _ (fun ι _ => isTorusIntegrable_conj_label_mul m ℓ (torusIntegrable_phase_mul m ι (hg ι)))]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  exact coefOf_phase_mul m ℓ ι (g ι)

theorem crossVec_sum_U (S : Finset (ℤ × ℤ)) (e : ℤ × ℤ → ℂ) (U : ℤ × ℤ → Fin 12 → ℂ) (W Ω : Fin 3 → ℂ) (c : Fin 3) :
    crossVec (fun J => ∑ ι ∈ S, e ι * U ι J) W Ω c = ∑ ι ∈ S, e ι * crossVec (U ι) W Ω c := by
  rw [crossVec_expand_U]
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  rw [crossVec_expand_U (U ι), Finset.mul_sum]
  refine Finset.sum_congr rfl (fun J _ => ?_)
  ring

theorem curlOfU_sum (S : Finset (ℤ × ℤ)) (e : ℤ × ℤ → ℂ) (U : ℤ × ℤ → Fin 12 → ℂ) (i : Fin 3) :
    curlOfU (fun J => ∑ ι ∈ S, e ι * U ι J) i = ∑ ι ∈ S, curlOfU (U ι) i * e ι := by
  have h := curlOfU_explicit (fun J => ∑ ι ∈ S, e ι * U ι J)
  have hU := fun ι => curlOfU_explicit (U ι)
  fin_cases i
  · simp only [Fin.zero_eta, Fin.isValue] at h ⊢
    rw [h.1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [(hU ι).1]; ring
  · simp only [Fin.mk_one, Fin.isValue] at h ⊢
    rw [h.2.1, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [(hU ι).2.1]; ring
  · simp only [Fin.reduceFinMk, Fin.isValue] at h ⊢
    rw [h.2.2, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [(hU ι).2.2]; ring

theorem velOfU_sum (S : Finset (ℤ × ℤ)) (e : ℤ × ℤ → ℂ) (U : ℤ × ℤ → Fin 12 → ℂ) (i : Fin 3) :
    velOfU (fun J => ∑ ι ∈ S, e ι * U ι J) i = ∑ ι ∈ S, velOfU (U ι) i * e ι := by
  unfold velOfU
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  ring

theorem mean_trig_normSq (m : ℕ) (hm : 1 ≤ m) (S : Finset (ℤ × ℤ)) (x : ℤ × ℤ → ℂ) :
    torusMean (fun τ φ => ((‖∑ α ∈ S, x α * labelPhase m α τ φ‖ ^ 2 : ℝ) : ℂ)) = ∑ α ∈ S, ((‖x α‖ ^ 2 : ℝ) : ℂ) := by
  rw [← torusMean_trig_sq m hm S x]
  congr 1
  funext τ φ
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem torusIntegrable_normSq_of_bound {h : ℝ → ℝ → ℂ} (hh : IsTorusIntegrable h) (C : ℝ)
    (hC : ∀ τ φ, ‖h τ φ‖ ^ 2 ≤ C) : IsTorusIntegrable (fun τ φ => ((‖h τ φ‖ ^ 2 : ℝ) : ℂ)) := by
  refine bounded_integrable _ ?_ ⟨C, fun τ φ _ _ _ _ => ?_⟩
  · have hm : AEStronglyMeasurable (fun z : ℝ × ℝ => h z.1 z.2) boxMeasure := hh.1
    exact Complex.continuous_ofReal.comp_aestronglyMeasurable (hm.norm.pow 2)
  · rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    exact hC τ φ

theorem cross_coef_sum_le (m : ℕ) (hm : 1 ≤ m) (S T : Finset (ℤ × ℤ)) (U : ℤ × ℤ → Fin 12 → ℂ)
    (EW EΩ : ℝ → ℝ → Fin 3 → ℂ) (hW : ∀ a, IsTorusIntegrable (fun τ φ => EW τ φ a))
    (hΩ : ∀ a, IsTorusIntegrable (fun τ φ => EΩ τ φ a)) (bW bΩ : ℝ)
    (hbW : ∀ τ φ, ∑ a, ‖EW τ φ a‖ ^ 2 ≤ bW) (hbΩ : ∀ τ φ, ∑ a, ‖EΩ τ φ a‖ ^ 2 ≤ bΩ) :
    ∑ ℓ ∈ T, ∑ c, ‖∑ ι ∈ S, crossVec (U ι) (fun a => coefOf m (ℓ - ι) (fun τ φ => EW τ φ a))
        (fun a => coefOf m (ℓ - ι) (fun τ φ => EΩ τ φ a)) c‖ ^ 2
      ≤ 2 * bW * ∑ ι ∈ S, ∑ i, ‖curlOfU (U ι) i‖ ^ 2 + 2 * bΩ * ∑ ι ∈ S, ∑ a, ‖velOfU (U ι) a‖ ^ 2 := by
  have hbW0 : 0 ≤ bW := le_trans (Finset.sum_nonneg (fun a _ => by positivity)) (hbW 0 0)
  have hbΩ0 : 0 ≤ bΩ := le_trans (Finset.sum_nonneg (fun a _ => by positivity)) (hbΩ 0 0)
  set X : ℝ → ℝ → Fin 12 → ℂ := fun τ φ J => ∑ ι ∈ S, labelPhase m ι τ φ * U ι J with hX
  set Y : Fin 3 → ℝ → ℝ → ℂ := fun c τ φ => crossVec (X τ φ) (EW τ φ) (EΩ τ φ) c with hY
  have hg : ∀ ι c, IsTorusIntegrable (fun τ φ => crossVec (U ι) (EW τ φ) (EΩ τ φ) c) := by
    intro ι c
    have e : (fun τ φ => crossVec (U ι) (EW τ φ) (EΩ τ φ) c) = fun τ φ =>
        ∑ j, crossVec (U ι) (Pi.single j 1) 0 c * EW τ φ j + ∑ l, crossVec (U ι) 0 (Pi.single l 1) c * EΩ τ φ l := by
      funext τ φ
      exact crossVec_expand_WΩ _ _ _ c
    rw [e]
    have h1 : ∀ j, IsTorusIntegrable (fun τ φ => crossVec (U ι) (Pi.single j 1) 0 c * EW τ φ j) := by
      intro j; have h := hW j; unfold IsTorusIntegrable at h ⊢; exact h.const_mul _
    have h2 : ∀ j, IsTorusIntegrable (fun τ φ => crossVec (U ι) 0 (Pi.single j 1) c * EΩ τ φ j) := by
      intro j; have h := hΩ j; unfold IsTorusIntegrable at h ⊢; exact h.const_mul _
    exact isTorusIntegrable_add (isTorusIntegrable_sum _ _ (fun j _ => h1 j)) (isTorusIntegrable_sum _ _ (fun j _ => h2 j))
  have hYs : ∀ c, Y c = fun τ φ => ∑ ι ∈ S, labelPhase m ι τ φ * crossVec (U ι) (EW τ φ) (EΩ τ φ) c := by
    intro c
    funext τ φ
    exact crossVec_sum_U S (fun ι => labelPhase m ι τ φ) U (EW τ φ) (EΩ τ φ) c
  have hYi : ∀ c, IsTorusIntegrable (Y c) := by
    intro c
    rw [hYs c]
    exact isTorusIntegrable_sum _ _ (fun ι _ => torusIntegrable_phase_mul m ι (hg ι c))
  have hcoef : ∀ ℓ c, coefOf m ℓ (Y c) = ∑ ι ∈ S, crossVec (U ι) (fun a => coefOf m (ℓ - ι) (fun τ φ => EW τ φ a))
      (fun a => coefOf m (ℓ - ι) (fun τ φ => EΩ τ φ a)) c := by
    intro ℓ c
    rw [hYs c, coefOf_sum_phase m ℓ S _ (fun ι => hg ι c)]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    have e : (fun τ φ => crossVec (U ι) (EW τ φ) (EΩ τ φ) c) = fun τ φ =>
        ∑ j, crossVec (U ι) (Pi.single j 1) 0 c * EW τ φ j + ∑ l, crossVec (U ι) 0 (Pi.single l 1) c * EΩ τ φ l := by
      funext τ φ
      exact crossVec_expand_WΩ _ _ _ c
    rw [e, coefOf_lin m (ℓ - ι) _ _ (fun j τ φ => EW τ φ j) (fun j τ φ => EΩ τ φ j) hW hΩ, crossVec_expand_WΩ]
  have hcurlX : ∀ τ φ i, curlOfU (X τ φ) i = ∑ ι ∈ S, curlOfU (U ι) i * labelPhase m ι τ φ :=
    fun τ φ i => curlOfU_sum S (fun ι => labelPhase m ι τ φ) U i
  have hvelX : ∀ τ φ i, velOfU (X τ φ) i = ∑ ι ∈ S, velOfU (U ι) i * labelPhase m ι τ φ :=
    fun τ φ i => velOfU_sum S (fun ι => labelPhase m ι τ φ) U i
  set Bd : ℝ → ℝ → ℝ := fun τ φ => ∑ i, 2 * bW * ‖∑ ι ∈ S, curlOfU (U ι) i * labelPhase m ι τ φ‖ ^ 2
      + ∑ a, 2 * bΩ * ‖∑ ι ∈ S, velOfU (U ι) a * labelPhase m ι τ φ‖ ^ 2 with hBd
  have hpt : ∀ τ φ, ∑ c, ‖Y c τ φ‖ ^ 2 ≤ Bd τ φ := by
    intro τ φ
    have h := crossVec_norm_le (X τ φ) (EW τ φ) (EΩ τ φ)
    have h1 := hbW τ φ
    have h2 := hbΩ τ φ
    have hc0 : 0 ≤ ∑ i, ‖curlOfU (X τ φ) i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have hv0 : 0 ≤ ∑ i, ‖velOfU (X τ φ) i‖ ^ 2 := Finset.sum_nonneg (fun _ _ => by positivity)
    have hBd' : Bd τ φ = 2 * bW * ∑ i, ‖curlOfU (X τ φ) i‖ ^ 2 + 2 * bΩ * ∑ i, ‖velOfU (X τ φ) i‖ ^ 2 := by
      simp only [hBd, hcurlX, hvelX, Finset.mul_sum]
    rw [hBd']
    show ∑ c, ‖crossVec (X τ φ) (EW τ φ) (EΩ τ φ) c‖ ^ 2 ≤ _
    nlinarith [mul_le_mul_of_nonneg_left h1 hc0, mul_le_mul_of_nonneg_left h2 hv0]
  have hBcont : Continuous (fun z : ℝ × ℝ => Bd z.1 z.2) := by
    simp only [hBd]
    refine continuous_finsetSum _ (fun i _ => continuous_const.mul ((trig_continuous m S _).norm.pow 2)) |>.add
      (continuous_finsetSum _ (fun a _ => continuous_const.mul ((trig_continuous m S _).norm.pow 2)))
  have hBbd : ∃ C, ∀ τ φ, Bd τ φ ≤ C := by
    refine ⟨∑ i, 2 * bW * (∑ ι ∈ S, ‖curlOfU (U ι) i‖) ^ 2 + ∑ a, 2 * bΩ * (∑ ι ∈ S, ‖velOfU (U ι) a‖) ^ 2,
      fun τ φ => ?_⟩
    simp only [hBd]
    refine add_le_add (Finset.sum_le_sum (fun i _ => ?_)) (Finset.sum_le_sum (fun a _ => ?_))
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_trig_le m S _ τ φ) 2) (by positivity)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (norm_trig_le m S _ τ φ) 2) (by positivity)
  obtain ⟨CB, hCB⟩ := hBbd
  have hYn : ∀ c, IsTorusIntegrable (fun τ φ => ((‖Y c τ φ‖ ^ 2 : ℝ) : ℂ)) := by
    intro c
    refine torusIntegrable_normSq_of_bound (hYi c) CB (fun τ φ => ?_)
    have h1 := hpt τ φ
    have h2 : ‖Y c τ φ‖ ^ 2 ≤ ∑ c', ‖Y c' τ φ‖ ^ 2 :=
      Finset.single_le_sum (f := fun c' => ‖Y c' τ φ‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ c)
    linarith [hCB τ φ]
  have hsumYn : IsTorusIntegrable (fun τ φ => ((∑ c, ‖Y c τ φ‖ ^ 2 : ℝ) : ℂ)) := by
    have h := isTorusIntegrable_sum Finset.univ _ (fun c _ => hYn c)
    unfold IsTorusIntegrable at h ⊢
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Complex.ofReal_sum]
  have hBi : IsTorusIntegrable (fun τ φ => ((Bd τ φ : ℝ) : ℂ)) :=
    torusIntegrable_of_continuous (Complex.continuous_ofReal.comp hBcont)
      ⟨CB, fun τ φ => by
        have hB0 : 0 ≤ Bd τ φ := by simp only [hBd]; positivity
        rw [Complex.norm_real, Real.norm_of_nonneg hB0]
        exact hCB τ φ⟩
  have hmeanB : (torusMean (fun τ φ => ((Bd τ φ : ℝ) : ℂ))).re
      = 2 * bW * ∑ ι ∈ S, ∑ i, ‖curlOfU (U ι) i‖ ^ 2 + 2 * bΩ * ∑ ι ∈ S, ∑ a, ‖velOfU (U ι) a‖ ^ 2 := by
    have hterm : ∀ (b : ℝ) (x : ℤ × ℤ → ℂ), IsTorusIntegrable
        (fun τ φ => ((b : ℝ) : ℂ) * ((‖∑ ι ∈ S, x ι * labelPhase m ι τ φ‖ ^ 2 : ℝ) : ℂ)) := by
      intro b x
      have h := torusIntegrable_normSq_of_bound (trig_integrable m S x) ((∑ ι ∈ S, ‖x ι‖) ^ 2)
        (fun τ φ => pow_le_pow_left₀ (norm_nonneg _) (norm_trig_le m S x τ φ) 2)
      unfold IsTorusIntegrable at h ⊢
      exact h.const_mul _
    have e : (fun τ φ => ((Bd τ φ : ℝ) : ℂ)) = fun τ φ =>
        (∑ i, ((2 * bW : ℝ) : ℂ) * ((‖∑ ι ∈ S, curlOfU (U ι) i * labelPhase m ι τ φ‖ ^ 2 : ℝ) : ℂ))
        + ∑ a, ((2 * bΩ : ℝ) : ℂ) * ((‖∑ ι ∈ S, velOfU (U ι) a * labelPhase m ι τ φ‖ ^ 2 : ℝ) : ℂ) := by
      funext τ φ
      simp only [hBd]
      push_cast
      ring
    rw [e, torusMean_add _ _ (isTorusIntegrable_sum _ _ (fun i _ => hterm _ _))
      (isTorusIntegrable_sum _ _ (fun a _ => hterm _ _)),
      torusMean_sum _ _ (fun i _ => hterm _ _), torusMean_sum _ _ (fun a _ => hterm _ _)]
    simp only [torusMean_const_mul, mean_trig_normSq m hm, Complex.add_re, Complex.re_sum, Complex.re_ofReal_mul,
      Complex.ofReal_re]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_comm (s := Finset.univ) (t := S),
      Finset.sum_comm (s := Finset.univ) (t := S)]
  calc ∑ ℓ ∈ T, ∑ c, ‖∑ ι ∈ S, crossVec (U ι) (fun a => coefOf m (ℓ - ι) (fun τ φ => EW τ φ a))
        (fun a => coefOf m (ℓ - ι) (fun τ φ => EΩ τ φ a)) c‖ ^ 2
        = ∑ c, ∑ ℓ ∈ T, ‖coefOf m ℓ (Y c)‖ ^ 2 := by
          simp only [hcoef]
          exact Finset.sum_comm
    _ ≤ ∑ c, (torusMean (fun τ φ => ((‖Y c τ φ‖ ^ 2 : ℝ) : ℂ))).re :=
          Finset.sum_le_sum (fun c _ => coef_sq_sum_le m hm T (Y c) (hYi c) (hYn c))
    _ = (torusMean (fun τ φ => ((∑ c, ‖Y c τ φ‖ ^ 2 : ℝ) : ℂ))).re := by
          rw [← Complex.re_sum, ← torusMean_sum _ _ (fun c _ => hYn c)]
          congr 2
          funext τ φ
          push_cast
          rfl
    _ ≤ (torusMean (fun τ φ => ((Bd τ φ : ℝ) : ℂ))).re :=
          torusMean_re_mono _ _ hsumYn hBi (fun τ φ _ _ _ _ => by
            rw [Complex.ofReal_re, Complex.ofReal_re]
            exact hpt τ φ)
    _ = _ := hmeanB

end Internal

end Assembly

end CertCell

end Breakdown
