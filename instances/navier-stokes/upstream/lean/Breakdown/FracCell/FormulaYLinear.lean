import Breakdown.FracCell.StFormulaProof
import Breakdown.FracCert.WeakRegular

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellFormula

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars

namespace FormulaYLinearInternal

variable {μ : Measure (ℝ × ℝ)}

theorem bd_add {f g : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun p => f p + g p) ⊤ μ := hf.add hg

theorem bd_sub {f g : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun p => f p - g p) ⊤ μ := hf.sub hg

theorem bd_neg {f : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) : MemLp (fun p => -f p) ⊤ μ := hf.neg

theorem bd_mul {f g : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun p => f p * g p) ⊤ μ := hg.mul' hf

theorem bd_const (c : ℂ) : MemLp (fun _ : ℝ × ℝ => c) ⊤ μ := memLp_top_const c

theorem bd_sum {ι : Type} (s : Finset ι) (f : ι → ℝ × ℝ → ℂ) (h : ∀ i, MemLp (f i) ⊤ μ) :
    MemLp (fun p => ∑ i ∈ s, f i p) ⊤ μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have e : (fun p => ∑ i ∈ insert a s, f i p) = fun p => f a p + ∑ i ∈ s, f i p := by
      funext p; rw [Finset.sum_insert ha]
    rw [e]; exact bd_add (h a) ih

theorem bd_conj {f : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) : MemLp (fun p => (starRingEnd ℂ) (f p)) ⊤ μ :=
  hf.of_le (Complex.continuous_conj.comp_aestronglyMeasurable hf.1) (ae_of_all _ fun p => by simp)

theorem bd_ite {P : Prop} [Decidable P] {f g : ℝ × ℝ → ℂ} (hf : MemLp f ⊤ μ) (hg : MemLp g ⊤ μ) :
    MemLp (fun p => if P then f p else g p) ⊤ μ := by
  by_cases h : P
  · simpa [h] using hf
  · simpa [h] using hg

theorem bd_vec3 {f₀ f₁ f₂ : ℝ × ℝ → ℂ} (h₀ : MemLp f₀ ⊤ μ) (h₁ : MemLp f₁ ⊤ μ) (h₂ : MemLp f₂ ⊤ μ) (a : Fin 3) :
    MemLp (fun p => (![f₀ p, f₁ p, f₂ p] : Fin 3 → ℂ) a) ⊤ μ := by
  fin_cases a
  · simpa using h₀
  · simpa using h₁
  · simpa using h₂

theorem bd_pairVec {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hs : ∀ a b, MemLp (fun p => s p a b) ⊤ μ) (hv : ∀ a, MemLp (fun p => v p a) ⊤ μ) (j : Fin 12) :
    MemLp (fun p => pairVec (s p) (v p) j) ⊤ μ := by
  by_cases h : j.val < 9
  · simpa [pairVec, h] using hs ⟨j.val / 3, by omega⟩ ⟨j.val % 3, Nat.mod_lt _ (by norm_num)⟩
  · simpa [pairVec, h] using hv ⟨j.val - 9, by omega⟩

theorem bd_wave {Sβ Gβ s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hS : ∀ a b, MemLp (fun p => Sβ p a b) ⊤ μ) (hG : ∀ a b, MemLp (fun p => Gβ p a b) ⊤ μ)
    (hs : ∀ a b, MemLp (fun p => s p a b) ⊤ μ) (hv : ∀ a, MemLp (fun p => v p a) ⊤ μ) (a b : Fin 3) :
    MemLp (fun p => waveActionStrain (Sβ p) (Gβ p) (s p) (v p) a b) ⊤ μ := by
  simp only [waveActionStrain, curlAdj, matVec, curlComp, couplingMap, bracketMat]
  repeat' (first | (intro _) | apply hS | apply hG | apply hs | apply hv | apply bd_sum | exact bd_const _ | apply bd_neg | apply bd_mul | apply bd_add)

theorem bd_waveVel {Gβ s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ}
    (hG : ∀ a b, MemLp (fun p => Gβ p a b) ⊤ μ)
    (hs : ∀ a b, MemLp (fun p => s p a b) ⊤ μ) (b : Fin 3) :
    MemLp (fun p => waveActionVelocity (Gβ p) (s p) b) ⊤ μ := by
  simp only [waveActionVelocity, couplingAdj]
  repeat' (first | (intro _) | apply hG | apply hs | apply bd_sum | exact bd_const _ | apply bd_conj | apply bd_neg | apply bd_mul | apply bd_add)

theorem bd_local {A : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ} {s : ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {v : ℝ × ℝ → Fin 3 → ℂ}
    (hA : ∀ i j, MemLp (fun p => A p i j) ⊤ μ)
    (hs : ∀ a b, MemLp (fun p => s p a b) ⊤ μ) (hv : ∀ a, MemLp (fun p => v p a) ⊤ μ) (i : Fin 12) :
    MemLp (fun p => matAct (A p) (pairVec (s p) (v p)) i) ⊤ μ := by
  simp only [matAct]
  exact bd_sum _ _ fun j => bd_mul (hA i j) (bd_pairVec hs hv j)


section Main

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (B : CellBases)

theorem rect_compact : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_meas : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem rect_finite : IsFiniteMeasure (volume.restrict K.rect) :=
  ⟨by rw [Measure.restrict_apply_univ]; exact (rect_compact K).measure_lt_top⟩

theorem bd_cont {f : ℝ × ℝ → ℂ} (hf : Continuous f) : MemLp f ⊤ (volume.restrict K.rect) := by
  obtain ⟨C, hC⟩ := (rect_compact K).exists_bound_of_continuousOn hf.continuousOn
  exact memLp_top_of_bound hf.aestronglyMeasurable C (ae_restrict_of_forall_mem (rect_meas K) hC)

theorem bd_poly (j l : ℕ) :
    MemLp (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) ⊤ (volume.restrict K.rect) := by
  apply bd_cont
  unfold CellBases.radialPoly CellBases.heightPoly
  fun_prop

theorem bd_fst : MemLp (fun p : ℝ × ℝ => ((p.1 : ℝ) : ℂ)) ⊤ (volume.restrict K.rect) :=
  bd_cont K (by fun_prop)

theorem bd_lw : MemLp (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) ⊤ (volume.restrict K.rect) := by
  by_cases h : K.r₁ = 0
  · have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) = fun p => ((p.1 : ℝ) : ℂ) := by
      funext p; simp [CellBox.lineWeight, h]
    rw [e]; exact bd_fst K
  · have e : (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) = fun _ => (1 : ℂ) := by
      funext p; simp [CellBox.lineWeight, h]
    rw [e]; exact bd_const _

theorem bd_rHat : MemLp (fun p : ℝ × ℝ => ((rHat K p : ℝ) : ℂ)) ⊤ (volume.restrict K.rect) := by
  by_cases h : K.r₁ = 0
  · have e : (fun p : ℝ × ℝ => ((rHat K p : ℝ) : ℂ)) = fun p => ((p.1 / p.1 : ℝ) : ℂ) := by
      funext p; simp [rHat, CellBox.lineWeight, h]
    rw [e]
    refine memLp_top_of_bound (Complex.measurable_ofReal.comp (measurable_fst.div measurable_fst)).aestronglyMeasurable 1 (ae_of_all _ fun p => ?_)
    by_cases hp : p.1 = 0
    · simp [hp]
    · simp [hp]
  · have e : (fun p : ℝ × ℝ => ((rHat K p : ℝ) : ℂ)) = fun p => ((p.1 : ℝ) : ℂ) := by
      funext p; simp [rHat, CellBox.lineWeight, h]
    rw [e]; exact bd_fst K

theorem lw_rHat (p : ℝ × ℝ) : K.lineWeight p.1 * rHat K p = p.1 := by
  by_cases h : K.r₁ = 0
  · simp only [rHat, CellBox.lineWeight, h, if_true]
    by_cases hp : p.1 = 0
    · simp [hp]
    · field_simp
  · simp [rHat, CellBox.lineWeight, h]

theorem bd_synthStrain (U : Aug S k → ℂ) (n : ℤ) (a b : Fin 3) :
    MemLp (fun p => synthStrain S B U n p a b) ⊤ (volume.restrict K.rect) := by
  simp only [synthStrain, unitStrain]
  refine bd_sum _ _ fun i => bd_mul (bd_const _) (bd_ite ?_ (bd_const _))
  exact bd_poly K B _ _

theorem bd_synthVelocity (U : Aug S k → ℂ) (n : ℤ) (a : Fin 3) :
    MemLp (fun p => synthVelocity S B U n p a) ⊤ (volume.restrict K.rect) := by
  simp only [synthVelocity, unitVelocity]
  refine bd_sum _ _ fun i => bd_mul (bd_const _) (bd_ite ?_ (bd_const _))
  exact bd_poly K B _ _

variable {c K S}

theorem bd_yVel {sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ}
    (hG : ∀ β a b, MemLp (fun p => curlGradMode c β p a b) ⊤ (volume.restrict K.rect))
    (hs : ∀ n a b, MemLp (fun p => sAt n p a b) ⊤ (volume.restrict K.rect))
    (hv : ∀ n a, MemLp (fun p => vAt n p a) ⊤ (volume.restrict K.rect))
    (n : ℤ) (hL : n ∈ S.resolved → ∀ i j, MemLp (fun p => S.localMatrix n p i j) ⊤ (volume.restrict K.rect))
    (b : Fin 3) :
    MemLp (fun p => yVelocityOf c K S sAt vAt n p b) ⊤ (volume.restrict K.rect) := by
  have hr := bd_rHat K
  have hW : MemLp (fun p => ∑ n' ∈ S.resolved, waveActionVelocity (curlGradMode c (n' - n) p) (sAt n' p) b) ⊤
      (volume.restrict K.rect) := bd_sum _ _ fun n' => bd_waveVel (hG _) (hs n') b
  by_cases h1 : n ∈ S.resolved ∪ S.band <;> by_cases h2 : n ∈ S.resolved <;>
    simp only [yVelocityOf, h1, h2, if_true, if_false, splitVelocity, add_zero, zero_add, mul_zero]
  · exact bd_mul hr (bd_add hW (bd_local (hL h2) (hs n) (hv n) _))
  · exact bd_mul hr hW
  · exact bd_mul hr (bd_local (hL h2) (hs n) (hv n) _)
  · exact bd_const _


theorem bd_yStrain0 {sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ}
    (hS : ∀ β a b, MemLp (fun p => strainMode c β p a b) ⊤ (volume.restrict K.rect))
    (hG : ∀ β a b, MemLp (fun p => curlGradMode c β p a b) ⊤ (volume.restrict K.rect))
    (hs : ∀ n a b, MemLp (fun p => sAt n p a b) ⊤ (volume.restrict K.rect))
    (hv : ∀ n a, MemLp (fun p => vAt n p a) ⊤ (volume.restrict K.rect))
    (n : ℤ) (hL : n ∈ S.resolved → ∀ i j, MemLp (fun p => S.localMatrix n p i j) ⊤ (volume.restrict K.rect))
    (a b : Fin 3) :
    MemLp (fun p => yStrainOf c K S sAt vAt 0 0 n p a b) ⊤ (volume.restrict K.rect) := by
  have hr := bd_rHat K
  have hW : MemLp (fun p => ∑ n' ∈ S.resolved,
      waveActionStrain (strainMode c (n - n') p) (curlGradMode c (n - n') p) (sAt n' p) (vAt n' p) a b) ⊤
      (volume.restrict K.rect) := bd_sum _ _ fun n' => bd_wave (hS _) (hG _) (hs n') (hv n') a b
  by_cases h1 : n ∈ S.resolved ∪ S.band <;> by_cases h2 : n ∈ S.resolved <;>
    simp only [yStrainOf, h1, h2, if_true, if_false, splitStrain, Pi.zero_apply, zero_div, zero_mul, add_zero,
      zero_add, mul_zero, Finset.sum_const_zero]
  · exact bd_mul hr (bd_add hW (bd_local (hL h2) (hs n) (hv n) _))
  · exact bd_mul hr hW
  · exact bd_mul hr (bd_local (hL h2) (hs n) (hv n) _)
  · exact bd_const _

theorem yStrain_split (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ) (κ ζ : Fin k → ℂ)
    (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yStrainOf c K S sAt vAt κ ζ n p a b = yStrainOf c K S sAt vAt 0 0 n p a b +
      ((rHat K p : ℝ) : ℂ) * ∑ i : Fin k, ((κ i / 2) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ζ i * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) := by
  simp only [yStrainOf, Pi.zero_apply, zero_div, zero_mul, add_zero, Finset.sum_const_zero]
  ring

theorem yFold_split (sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ) (κ ζ : Fin k → ℂ)
    (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yFoldedOf c K S sAt vAt κ ζ n p a b = yFoldedOf c K S sAt vAt 0 0 n p a b +
      ((rHat K p : ℝ) : ℂ) * ∑ i : Fin k, ((κ i / 2) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ζ i * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) := by
  by_cases hn : n ∈ S.resolved
  · simp only [yFoldedOf, hn, if_true]
    exact yStrain_split sAt vAt κ ζ n p a b
  · simp only [yFoldedOf, hn, if_false, foldVelocity]
    rw [yStrain_split sAt vAt κ ζ n p a b]
    ring

theorem bd_yFold0 {sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ}
    (hS : ∀ β a b, MemLp (fun p => strainMode c β p a b) ⊤ (volume.restrict K.rect))
    (hG : ∀ β a b, MemLp (fun p => curlGradMode c β p a b) ⊤ (volume.restrict K.rect))
    (hs : ∀ n a b, MemLp (fun p => sAt n p a b) ⊤ (volume.restrict K.rect))
    (hv : ∀ n a, MemLp (fun p => vAt n p a) ⊤ (volume.restrict K.rect))
    (n : ℤ) (hL : n ∈ S.resolved → ∀ i j, MemLp (fun p => S.localMatrix n p i j) ⊤ (volume.restrict K.rect))
    (a b : Fin 3) :
    MemLp (fun p => yFoldedOf c K S sAt vAt 0 0 n p a b) ⊤ (volume.restrict K.rect) := by
  have h0 := bd_yStrain0 hS hG hs hv n hL a b
  have hyv := bd_yVel hG hs hv n hL
  by_cases hn : n ∈ S.resolved
  · simpa only [yFoldedOf, hn, if_true] using h0
  · simp only [yFoldedOf, hn, if_false, foldVelocity, turnAdjInv]
    refine bd_add h0 (bd_ite (bd_mul (bd_fst K) (bd_vec3 ?_ ?_ ?_ a)) (bd_const _))
    all_goals
      repeat' (first | exact hyv _ | exact bd_const _ | apply bd_sub | apply bd_mul)

theorem int_yFold {sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ} (κ ζ : Fin k → ℂ)
    (hS : ∀ β a b, MemLp (fun p => strainMode c β p a b) ⊤ (volume.restrict K.rect))
    (hG : ∀ β a b, MemLp (fun p => curlGradMode c β p a b) ⊤ (volume.restrict K.rect))
    (hs : ∀ n a b, MemLp (fun p => sAt n p a b) ⊤ (volume.restrict K.rect))
    (hv : ∀ n a, MemLp (fun p => vAt n p a) ⊤ (volume.restrict K.rect))
    (n : ℤ) (hL : n ∈ S.resolved → ∀ i j, MemLp (fun p => S.localMatrix n p i j) ⊤ (volume.restrict K.rect))
    (a b : Fin 3)
    (hA : ∀ i, Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
      (volume.restrict K.rect))
    (hP : ∀ i, Integrable (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b)
      (volume.restrict K.rect))
    {P : ℝ × ℝ → ℂ} (hPb : MemLp P ⊤ (volume.restrict K.rect)) :
    Integrable (fun p => (K.lineWeight p.1 : ℂ) * yFoldedOf c K S sAt vAt κ ζ n p a b * P p)
      (volume.restrict K.rect) := by
  have := rect_finite K
  have e : (fun p => (K.lineWeight p.1 : ℂ) * yFoldedOf c K S sAt vAt κ ζ n p a b * P p) =
      fun p => (K.lineWeight p.1 : ℂ) * yFoldedOf c K S sAt vAt 0 0 n p a b * P p +
        (∑ i : Fin k, ((κ i / 2) * ((p.1 : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
          + ζ i * ((p.1 : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b))) * P p := by
    funext p
    rw [yFold_split]
    have h : ((K.lineWeight p.1 : ℝ) : ℂ) * ((rHat K p : ℝ) : ℂ) = (p.1 : ℂ) := by
      rw [← Complex.ofReal_mul, lw_rHat]
    have h2 : (∑ i : Fin k, ((κ i / 2) * ((p.1 : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
          + ζ i * ((p.1 : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b))) =
        (p.1 : ℂ) * ∑ i : Fin k, ((κ i / 2) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b
          + ζ i * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h2, ← h]
    ring
  rw [e]
  refine Integrable.add ?_ ?_
  · exact (bd_mul (bd_mul (bd_lw K) (bd_yFold0 hS hG hs hv n hL a b)) hPb).integrable le_top
  · refine Integrable.mul_of_top_left ?_ hPb
    exact integrable_finsetSum _ fun i _ => ((hA i).const_mul _).add ((hP i).const_mul _)

theorem int_yVel {sAt : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ} {vAt : ℤ → ℝ × ℝ → Fin 3 → ℂ}
    (hG : ∀ β a b, MemLp (fun p => curlGradMode c β p a b) ⊤ (volume.restrict K.rect))
    (hs : ∀ n a b, MemLp (fun p => sAt n p a b) ⊤ (volume.restrict K.rect))
    (hv : ∀ n a, MemLp (fun p => vAt n p a) ⊤ (volume.restrict K.rect))
    (n : ℤ) (hL : n ∈ S.resolved → ∀ i j, MemLp (fun p => S.localMatrix n p i j) ⊤ (volume.restrict K.rect))
    (a : Fin 3) {P : ℝ × ℝ → ℂ} (hPb : MemLp P ⊤ (volume.restrict K.rect)) :
    Integrable (fun p => (K.lineWeight p.1 : ℂ) * yVelocityOf c K S sAt vAt n p a * P p)
      (volume.restrict K.rect) := by
  have := rect_finite K
  exact (bd_mul (bd_mul (bd_lw K) (bd_yVel hG hs hv n hL a)) hPb).integrable le_top


theorem pairVec_add (x y : Fin 3 → Fin 3 → ℂ) (u w : Fin 3 → ℂ) :
    pairVec (x + y) (u + w) = pairVec x u + pairVec y w := by
  funext j
  simp only [pairVec, Pi.add_apply]
  split_ifs <;> rfl

theorem pairVec_smul (t : ℂ) (x : Fin 3 → Fin 3 → ℂ) (u : Fin 3 → ℂ) :
    pairVec (t • x) (t • u) = t • pairVec x u := by
  funext j
  simp only [pairVec, Pi.smul_apply]
  split_ifs <;> rfl

theorem wave_add (Sβ Gβ s₁ s₂ : Fin 3 → Fin 3 → ℂ) (v₁ v₂ : Fin 3 → ℂ) :
    waveActionStrain Sβ Gβ (s₁ + s₂) (v₁ + v₂) = waveActionStrain Sβ Gβ s₁ v₁ + waveActionStrain Sβ Gβ s₂ v₂ := by
  funext a b
  simp only [waveActionStrain, curlAdj, matVec, curlComp, couplingMap, bracketMat, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem wave_smul (t : ℂ) (Sβ Gβ s₁ : Fin 3 → Fin 3 → ℂ) (v₁ : Fin 3 → ℂ) :
    waveActionStrain Sβ Gβ (t • s₁) (t • v₁) = t • waveActionStrain Sβ Gβ s₁ v₁ := by
  funext a b
  simp only [waveActionStrain, curlAdj, matVec, curlComp, couplingMap, bracketMat, Pi.smul_apply, smul_eq_mul,
    Fin.sum_univ_three]
  ring

theorem waveVel_add (Gβ s₁ s₂ : Fin 3 → Fin 3 → ℂ) :
    waveActionVelocity Gβ (s₁ + s₂) = waveActionVelocity Gβ s₁ + waveActionVelocity Gβ s₂ := by
  funext b
  simp only [waveActionVelocity, couplingAdj, Pi.add_apply, Fin.sum_univ_three]
  ring

theorem waveVel_smul (t : ℂ) (Gβ s₁ : Fin 3 → Fin 3 → ℂ) :
    waveActionVelocity Gβ (t • s₁) = t • waveActionVelocity Gβ s₁ := by
  funext b
  simp only [waveActionVelocity, couplingAdj, Pi.smul_apply, smul_eq_mul, Fin.sum_univ_three]
  ring

theorem matAct_add (A : Matrix (Fin 12) (Fin 12) ℂ) (x y : Fin 12 → ℂ) :
    matAct A (x + y) = matAct A x + matAct A y := by
  funext i
  simp only [matAct, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem matAct_smul (t : ℂ) (A : Matrix (Fin 12) (Fin 12) ℂ) (x : Fin 12 → ℂ) :
    matAct A (t • x) = t • matAct A x := by
  funext i
  simp only [matAct, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem splitStrain_add (x y : Fin 12 → ℂ) : splitStrain (x + y) = splitStrain x + splitStrain y := rfl

theorem splitStrain_smul (t : ℂ) (x : Fin 12 → ℂ) : splitStrain (t • x) = t • splitStrain x := rfl

theorem splitVelocity_add (x y : Fin 12 → ℂ) : splitVelocity (x + y) = splitVelocity x + splitVelocity y := rfl

theorem splitVelocity_smul (t : ℂ) (x : Fin 12 → ℂ) : splitVelocity (t • x) = t • splitVelocity x := rfl

theorem turnAdjInv_add (q : ℝ) (x y : Fin 3 → ℂ) : turnAdjInv q (x + y) = turnAdjInv q x + turnAdjInv q y := by
  funext a
  fin_cases a <;> simp [turnAdjInv] <;> ring

theorem turnAdjInv_smul (t : ℂ) (q : ℝ) (x : Fin 3 → ℂ) : turnAdjInv q (t • x) = t • turnAdjInv q x := by
  funext a
  fin_cases a <;> simp [turnAdjInv] <;> ring

theorem yStrainOf_add (s₁ s₂ : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v₁ v₂ : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yStrainOf c K S (s₁ + s₂) (v₁ + v₂) 0 0 n p a b =
      yStrainOf c K S s₁ v₁ 0 0 n p a b + yStrainOf c K S s₂ v₂ 0 0 n p a b := by
  by_cases h1 : n ∈ S.resolved ∪ S.band <;> by_cases h2 : n ∈ S.resolved <;>
    simp only [yStrainOf, h1, h2, if_true, if_false, Pi.add_apply, wave_add, pairVec_add, matAct_add,
      splitStrain_add, Finset.sum_add_distrib, Pi.zero_apply, zero_div, zero_mul, add_zero, zero_add,
      Finset.sum_const_zero] <;> ring

theorem yStrainOf_smul (t : ℂ) (s₁ : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v₁ : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yStrainOf c K S (t • s₁) (t • v₁) 0 0 n p a b = t * yStrainOf c K S s₁ v₁ 0 0 n p a b := by
  by_cases h1 : n ∈ S.resolved ∪ S.band <;> by_cases h2 : n ∈ S.resolved <;>
    simp only [yStrainOf, h1, h2, if_true, if_false, Pi.smul_apply, wave_smul, pairVec_smul, matAct_smul,
      splitStrain_smul, smul_eq_mul, ← Finset.mul_sum, Pi.zero_apply, zero_div, zero_mul, add_zero, zero_add,
      Finset.sum_const_zero] <;> ring

theorem yVelocityOf_add (s₁ s₂ : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v₁ v₂ : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (n : ℤ) (p : ℝ × ℝ) :
    yVelocityOf c K S (s₁ + s₂) (v₁ + v₂) n p = yVelocityOf c K S s₁ v₁ n p + yVelocityOf c K S s₂ v₂ n p := by
  funext b
  by_cases h1 : n ∈ S.resolved ∪ S.band <;> by_cases h2 : n ∈ S.resolved <;>
    simp only [yVelocityOf, h1, h2, if_true, if_false, Pi.add_apply, waveVel_add, pairVec_add, matAct_add,
      splitVelocity_add, Finset.sum_add_distrib, add_zero, zero_add] <;> ring

theorem yVelocityOf_smul (t : ℂ) (s₁ : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v₁ : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (n : ℤ) (p : ℝ × ℝ) :
    yVelocityOf c K S (t • s₁) (t • v₁) n p = t • yVelocityOf c K S s₁ v₁ n p := by
  funext b
  by_cases h1 : n ∈ S.resolved ∪ S.band <;> by_cases h2 : n ∈ S.resolved <;>
    simp only [yVelocityOf, h1, h2, if_true, if_false, Pi.smul_apply, waveVel_smul, pairVec_smul, matAct_smul,
      splitVelocity_smul, smul_eq_mul, ← Finset.mul_sum, add_zero, zero_add] <;> ring

theorem yFold0_add (s₁ s₂ : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v₁ v₂ : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yFoldedOf c K S (s₁ + s₂) (v₁ + v₂) 0 0 n p a b =
      yFoldedOf c K S s₁ v₁ 0 0 n p a b + yFoldedOf c K S s₂ v₂ 0 0 n p a b := by
  by_cases hn : n ∈ S.resolved
  · simp only [yFoldedOf, hn, if_true]
    exact yStrainOf_add s₁ s₂ v₁ v₂ n p a b
  · simp only [yFoldedOf, hn, if_false, foldVelocity, yVelocityOf_add, turnAdjInv_add, Pi.add_apply]
    rw [yStrainOf_add]
    split_ifs <;> ring

theorem yFold0_smul (t : ℂ) (s₁ : ℤ → ℝ × ℝ → Fin 3 → Fin 3 → ℂ) (v₁ : ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yFoldedOf c K S (t • s₁) (t • v₁) 0 0 n p a b = t * yFoldedOf c K S s₁ v₁ 0 0 n p a b := by
  by_cases hn : n ∈ S.resolved
  · simp only [yFoldedOf, hn, if_true]
    exact yStrainOf_smul t s₁ v₁ n p a b
  · simp only [yFoldedOf, hn, if_false, foldVelocity, yVelocityOf_smul, turnAdjInv_smul, Pi.smul_apply,
      smul_eq_mul]
    rw [yStrainOf_smul]
    split_ifs <;> ring

theorem synthStrain_add (U V : Aug S k → ℂ) :
    synthStrain S B (U + V) = synthStrain S B U + synthStrain S B V := by
  funext n p a b
  simp only [synthStrain, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem synthStrain_smul (t : ℂ) (U : Aug S k → ℂ) : synthStrain S B (t • U) = t • synthStrain S B U := by
  funext n p a b
  simp only [synthStrain, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem synthVelocity_add (U V : Aug S k → ℂ) :
    synthVelocity S B (U + V) = synthVelocity S B U + synthVelocity S B V := by
  funext n p a
  simp only [synthVelocity, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem synthVelocity_smul (t : ℂ) (U : Aug S k → ℂ) : synthVelocity S B (t • U) = t • synthVelocity S B U := by
  funext n p a
  simp only [synthVelocity, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem lin_repr {ι : Type} [Fintype ι] [DecidableEq ι] (f : (ι → ℂ) → ℂ) (hadd : ∀ U V, f (U + V) = f U + f V)
    (hsmul : ∀ (t : ℂ) U, f (t • U) = t * f U) (U : ι → ℂ) : f U = ∑ e, U e * f (Pi.single e 1) := by
  let L : (ι → ℂ) →ₗ[ℂ] ℂ := { toFun := f, map_add' := hadd, map_smul' := fun t U => by simpa using hsmul t U }
  have hU : U = ∑ e, U e • (Pi.single e 1 : ι → ℂ) := by
    ext x; simp [Finset.sum_apply, Pi.single_apply]
  change L U = _
  conv_lhs => rw [hU]
  rw [map_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [L.map_smul, smul_eq_mul]
  rfl

open Classical in
theorem fold_linear (U : Aug S k → ℂ) (n : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    yFoldedOf c K S (synthStrain S B U) (synthVelocity S B U) (kappaPart S U) (pinPart S U) n p a b =
      ∑ e, U e * yFoldedOf c K S (synthStrain S B (Pi.single e 1)) (synthVelocity S B (Pi.single e 1))
        (kappaPart S (Pi.single e 1)) (pinPart S (Pi.single e 1)) n p a b := by
  refine lin_repr (fun U => yFoldedOf c K S (synthStrain S B U) (synthVelocity S B U) (kappaPart S U)
    (pinPart S U) n p a b) (fun U V => ?_) (fun t U => ?_) U
  · simp only [yFold_split _ _ (kappaPart S _), synthStrain_add, synthVelocity_add, yFold0_add, kappaPart, pinPart,
      Pi.add_apply, add_div, add_mul, Finset.sum_add_distrib]
    ring
  · simp only [yFold_split _ _ (kappaPart S _), synthStrain_smul, synthVelocity_smul, yFold0_smul, kappaPart, pinPart,
      Pi.smul_apply, smul_eq_mul, mul_add]
    congr 1
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

open Classical in
theorem vel_linear (U : Aug S k → ℂ) (n : ℤ) (p : ℝ × ℝ) (a : Fin 3) :
    yVelocityOf c K S (synthStrain S B U) (synthVelocity S B U) n p a =
      ∑ e, U e * yVelocityOf c K S (synthStrain S B (Pi.single e 1)) (synthVelocity S B (Pi.single e 1)) n p a := by
  refine lin_repr (fun U => yVelocityOf c K S (synthStrain S B U) (synthVelocity S B U) n p a)
    (fun U V => ?_) (fun t U => ?_) U
  · simp only [synthStrain_add, synthVelocity_add, yVelocityOf_add, Pi.add_apply]
  · simp only [synthStrain_smul, synthVelocity_smul, yVelocityOf_smul, Pi.smul_apply, smul_eq_mul]

end Main

end FormulaYLinearInternal

def ModeRegularity {k N : ℕ} (c : FracCellData k N) (K : CellBox) : Prop :=
  ∀ (n : ℤ) (a b : Fin 3),
    MemLp (fun p : ℝ × ℝ => strainMode c n p a b) ⊤ (volume.restrict K.rect) ∧
    MemLp (fun p : ℝ × ℝ => curlGradMode c n p a b) ⊤ (volume.restrict K.rect) ∧
    ∀ i : Fin k,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b) K.rect ∧
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat c.order n (c.modelPinField i) p.1 p.2 a b) K.rect

def ModeRegularityStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N slots : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) (R : CellRows N slots k),
    IsCellData α c K S B Cl R → ModeRegularity c K

open FormulaYLinearInternal Classical in
theorem yCoefLinear_of_modes (hm : ModeRegularityStatement) : YCoefLinearStatement := by
  intro α hα1 hα2 k N slots c hc K S B Cl R hd U n j l
  have hM := hm α hα1 hα2 c hc K S B Cl R hd
  have hS : ∀ β a b, MemLp (fun p => strainMode c β p a b) ⊤ (volume.restrict K.rect) :=
    fun β a b => (hM β a b).1
  have hG : ∀ β a b, MemLp (fun p => curlGradMode c β p a b) ⊤ (volume.restrict K.rect) :=
    fun β a b => (hM β a b).2.1
  have hL : n ∈ S.resolved → ∀ i j, MemLp (fun p => S.localMatrix n p i j) ⊤ (volume.restrict K.rect) := by
    intro hn i j
    obtain ⟨hmeas, C, hC⟩ := hd.scalars.data_regular.1 n hn
    exact memLp_top_of_bound (hmeas i j).aestronglyMeasurable C
      (ae_restrict_of_forall_mem (rect_meas K) fun p hp => hC p hp i j)
  have hP := bd_poly K B j l
  constructor
  · intro a b
    have hint : ∀ V : Aug S k → ℂ, Integrable (fun p => (K.lineWeight p.1 : ℂ) *
        yFoldedOf c K S (synthStrain S B V) (synthVelocity S B V) (kappaPart S V) (pinPart S V) n p a b *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) (volume.restrict K.rect) :=
      fun V => int_yFold (kappaPart S V) (pinPart S V) hS hG (bd_synthStrain K S B V) (bd_synthVelocity K S B V)
        n hL a b (fun i => ((hM n a b).2.2 i).1) (fun i => ((hM n a b).2.2 i).2) hP
    simp only [yCoef, yVec, CellBases.coef]
    have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) *
        yFoldedOf c K S (synthStrain S B U) (synthVelocity S B U) (kappaPart S U) (pinPart S U) n p a b *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = fun p => ∑ e, U e * ((K.lineWeight p.1 : ℂ) *
        yFoldedOf c K S (synthStrain S B (Pi.single e 1)) (synthVelocity S B (Pi.single e 1))
          (kappaPart S (Pi.single e 1)) (pinPart S (Pi.single e 1)) n p a b *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
      funext p
      rw [fold_linear, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e, integral_finsetSum _ fun e _ => (hint _).const_mul (U e)]
    exact Finset.sum_congr rfl fun e _ => integral_const_mul _ _
  · intro a
    have hint : ∀ V : Aug S k → ℂ, Integrable (fun p => (K.lineWeight p.1 : ℂ) *
        yVelocityOf c K S (synthStrain S B V) (synthVelocity S B V) n p a *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) (volume.restrict K.rect) :=
      fun V => int_yVel hG (bd_synthStrain K S B V) (bd_synthVelocity K S B V) n hL a hP
    simp only [yVelCoef, velVec, CellBases.coef]
    have e : (fun p : ℝ × ℝ => (K.lineWeight p.1 : ℂ) *
        yVelocityOf c K S (synthStrain S B U) (synthVelocity S B U) n p a *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) = fun p => ∑ e, U e * ((K.lineWeight p.1 : ℂ) *
        yVelocityOf c K S (synthStrain S B (Pi.single e 1)) (synthVelocity S B (Pi.single e 1)) n p a *
          ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
      funext p
      rw [vel_linear, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun e _ => by ring
    rw [e, integral_finsetSum _ fun e _ => (hint _).const_mul (U e)]
    exact Finset.sum_congr rfl fun e _ => integral_const_mul _ _

end Breakdown.CellCert.CellFormula

open Set

namespace Breakdown.CellCert.CellFormula.FormulaYLinearInternal

open CellAnalysis

def toSp : (ℝ × ℝ) × ℝ ≃ᵐ Space :=
  ((MeasurableEquiv.prodComm.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.finTwoArrow.symm)).trans
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm).trans
    (MeasurableEquiv.toLp 2 (Fin 3 → ℝ))

theorem toSp_mp : MeasurePreserving toSp volume volume :=
  (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin 3)).symm.comp
    ((volume_preserving_piFinSuccAbove (fun _ : Fin 3 => ℝ) 2).symm.comp
      (((MeasurePreserving.id volume).prod (volume_preserving_finTwoArrow ℝ).symm).comp
        Measure.measurePreserving_swap))

theorem toSp_apply (r θ z : ℝ) : toSp ((r * Real.cos θ, r * Real.sin θ), z) = cylPoint r θ z := by
  ext i
  fin_cases i <;> simp [cylPoint] <;> rfl

def cylM : OpenPartialHomeomorph ((ℝ × ℝ) × ℝ) ((ℝ × ℝ) × ℝ) :=
  polarCoord.prod (OpenPartialHomeomorph.refl ℝ)

def cylD (x : (ℝ × ℝ) × ℝ) : (ℝ × ℝ) × ℝ →L[ℝ] (ℝ × ℝ) × ℝ :=
  (fderivPolarCoordSymm x.1).prodMap (ContinuousLinearMap.id ℝ ℝ)

theorem cylD_has (x : (ℝ × ℝ) × ℝ) : HasFDerivAt cylM.symm (cylD x) x :=
  (hasFDerivAt_polarCoord_symm x.1).prodMap x (hasFDerivAt_id x.2)

theorem cylD_det (x : (ℝ × ℝ) × ℝ) : (cylD x).det = x.1.1 := by
  have : (cylD x).toLinearMap =
      LinearMap.prodMap (fderivPolarCoordSymm x.1).toLinearMap LinearMap.id := rfl
  rw [ContinuousLinearMap.det, this, LinearMap.det_prodMap, LinearMap.det_id, mul_one,
    ← ContinuousLinearMap.det, det_fderivPolarCoordSymm]

theorem cylM_image_ae : cylM.symm '' cylM.target =ᵐ[volume] (univ : Set ((ℝ × ℝ) × ℝ)) := by
  rw [← Set.univ_prod_univ, cylM.symm_image_target_eq_source]
  exact Measure.set_prod_ae_eq polarCoord_source_ae_eq_univ .rfl

theorem cyl_change {g : (ℝ × ℝ) × ℝ → ℂ} (hg : Integrable g) :
    IntegrableOn (fun x => x.1.1 • g (cylM.symm x)) cylM.target := by
  have : Measure.IsAddHaarMeasure (volume : Measure ((ℝ × ℝ) × ℝ)) := Measure.prod.instIsAddHaarMeasure _ _
  have h1 : IntegrableOn g (cylM.symm '' cylM.target) :=
    (integrableOn_univ.mpr hg).congr_set_ae cylM_image_ae
  rw [integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume cylM.open_target.measurableSet
      (fun x _ => (cylD_has x).hasFDerivWithinAt) cylM.symm.injOn g] at h1
  refine h1.congr_fun (fun x hx => ?_) cylM.open_target.measurableSet
  show |(cylD x).det| • g (cylM.symm x) = x.1.1 • g (cylM.symm x)
  rw [cylD_det, abs_of_pos hx.1.1]

def swapE : (ℝ × ℝ) × ℝ ≃ᵐ (ℝ × ℝ) × ℝ :=
  (MeasurableEquiv.prodAssoc.trans
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) MeasurableEquiv.prodComm)).trans
    MeasurableEquiv.prodAssoc.symm

theorem swapE_mp : MeasurePreserving swapE volume volume :=
  (measurePreserving_prodAssoc volume volume volume).symm.comp
    (((MeasurePreserving.id volume).prod Measure.measurePreserving_swap).comp
      (measurePreserving_prodAssoc volume volume volume))

theorem swapE_apply (r z θ : ℝ) : swapE ((r, z), θ) = ((r, θ), z) := rfl

theorem swapE_preimage :
    swapE ⁻¹' cylM.target = (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-Real.pi) Real.pi := by
  ext ⟨⟨r, z⟩, θ⟩
  simp [swapE_apply, cylM, polarCoord_target]

theorem fiber_int {f : Space → ℂ} (hf : Integrable f) :
    IntegrableOn (fun q : ℝ × ℝ => (q.1 : ℂ) * ∫ θ in (-Real.pi)..Real.pi, f (cylPoint q.1 θ q.2))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := by
  set g : (ℝ × ℝ) × ℝ → ℂ := fun w => f (toSp w) with hg_def
  have hg : Integrable g := (toSp_mp.integrable_comp_emb toSp.measurableEmbedding).mpr hf
  have hH := cyl_change hg
  set H : (ℝ × ℝ) × ℝ → ℂ := fun x => x.1.1 • g (cylM.symm x) with hH_def
  have hHσ : IntegrableOn (H ∘ swapE) ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioo (-Real.pi) Real.pi) := by
    rw [← swapE_preimage]
    exact (swapE_mp.integrableOn_comp_preimage swapE.measurableEmbedding).mpr hH
  have hprod : Integrable (H ∘ swapE)
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]; exact hHσ
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  refine hprod.integral_prod_left.congr (Filter.Eventually.of_forall fun q => ?_)
  show (∫ θ in Ioo (-Real.pi) Real.pi, (H ∘ swapE) (q, θ)) =
    (q.1 : ℂ) * ∫ θ in (-Real.pi)..Real.pi, f (cylPoint q.1 θ q.2)
  rw [intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo, ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ _ => ?_
  obtain ⟨r, z⟩ := q
  simp only [Function.comp_apply, swapE_apply, hH_def, hg_def, Complex.real_smul]
  rw [← toSp_apply]
  rfl

def angOf (y : Space) : ℝ := Complex.arg ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I)

def liftMat (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (y : Space) : ℂ :=
  Complex.exp (-(azimuth m n * angOf y : ℝ) * Complex.I) * (frameMat (angOf y) (G y) a b : ℂ)

theorem cyl0 (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ := by simp [cylPoint]
theorem cyl1 (r θ z : ℝ) : cylPoint r θ z 1 = r * Real.sin θ := by simp [cylPoint]
theorem cyl2 (r θ z : ℝ) : cylPoint r θ z 2 = z := by simp [cylPoint]

theorem angOf_cyl {r θ z : ℝ} (hr : 0 < r) (hθ : θ ∈ Ioo (-Real.pi) Real.pi) : angOf (cylPoint r θ z) = θ := by
  unfold angOf
  rw [cyl0, cyl1]
  push_cast
  rw [show (r : ℂ) * Complex.cos θ + r * Complex.sin θ * Complex.I = r * (Complex.cos θ + Complex.sin θ * Complex.I) by
    ring, Complex.arg_real_mul _ hr, Complex.arg_cos_add_sin_mul_I ⟨hθ.1, hθ.2.le⟩]

theorem frame_norm (θ : ℝ) (b : Fin 3) : ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b‖ ≤ 1 := by
  fin_cases b <;> simp [radialUnit, angularUnit, axialUnit, EuclideanSpace.norm_eq, Fin.sum_univ_three]

theorem frame_le (θ : ℝ) (M : Space →L[ℝ] Space) (a b : Fin 3) : |frameMat θ M a b| ≤ ‖M‖ := by
  unfold frameMat
  refine (abs_real_inner_le_norm _ _).trans ?_
  calc ‖M ((![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b)‖ *
        ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) a‖
      ≤ (‖M‖ * 1) * 1 := by
        gcongr
        · exact (M.le_opNorm _).trans (mul_le_mul_of_nonneg_left (frame_norm θ b) (norm_nonneg _))
        · exact frame_norm θ a
    _ = ‖M‖ := by ring

theorem exp_norm (x : ℝ) : ‖Complex.exp (-(x : ℂ) * Complex.I)‖ = 1 := by
  rw [show -(x : ℂ) * Complex.I = ((-x : ℝ) : ℂ) * Complex.I by push_cast; ring, Complex.norm_exp_ofReal_mul_I]

theorem liftMat_norm (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3) (y : Space) :
    ‖liftMat m n G a b y‖ ≤ ‖G y‖ := by
  unfold liftMat
  rw [norm_mul, exp_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
  exact frame_le _ _ _ _

theorem single_cont (i : Fin 3) : Continuous (fun c : ℝ => (EuclideanSpace.single i c : Space)) := by
  have e : (fun c : ℝ => (EuclideanSpace.single i c : Space)) = fun c => c • (EuclideanSpace.single i (1 : ℝ) : Space) := by
    funext c
    ext j
    by_cases h : j = i <;> simp [h]
  rw [e]
  fun_prop

theorem frame_cont (b : Fin 3) : Continuous (fun θ => (![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b) := by
  have h0 := single_cont 0
  have h1 := single_cont 1
  fin_cases b
  · exact (h0.comp Real.continuous_cos).add (h1.comp Real.continuous_sin)
  · exact (h0.comp Real.continuous_sin.neg).add (h1.comp Real.continuous_cos)
  · exact continuous_const

theorem frameMat_cont (a b : Fin 3) : Continuous fun q : ℝ × (Space →L[ℝ] Space) => frameMat q.1 q.2 a b := by
  have ha := frame_cont a
  have hb := frame_cont b
  unfold frameMat
  exact (continuous_snd.clm_apply (hb.comp continuous_fst)).inner (ha.comp continuous_fst)

theorem coord_cont (i : Fin 3) : Continuous fun y : Space => y i := by fun_prop

theorem angOf_meas : Measurable angOf := by
  unfold angOf
  exact Complex.measurable_arg.comp ((Complex.continuous_ofReal.comp (coord_cont 0)).add
      ((Complex.continuous_ofReal.comp (coord_cont 1)).mul continuous_const)).measurable

theorem phase_cont (x : ℝ) : Continuous fun q : ℝ × (Space →L[ℝ] Space) =>
    Complex.exp (-((x * q.1 : ℝ) : ℂ) * Complex.I) := by
  fun_prop

theorem liftFun_cont (m : ℕ) (n : ℤ) (a b : Fin 3) : Continuous (fun q : ℝ × (Space →L[ℝ] Space) =>
    Complex.exp (-(azimuth m n * q.1 : ℝ) * Complex.I) * (frameMat q.1 q.2 a b : ℂ)) :=
  (phase_cont (azimuth m n)).mul (Complex.continuous_ofReal.comp (frameMat_cont a b))

theorem pair_meas {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume) :
    AEStronglyMeasurable (fun y => (angOf y, G y)) volume :=
  AEStronglyMeasurable.prodMk angOf_meas.aestronglyMeasurable hG

theorem liftMat_meas (m : ℕ) (n : ℤ) {G : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (a b : Fin 3) : AEStronglyMeasurable (liftMat m n G a b) volume := by
  have h3 := (liftFun_cont m n a b).comp_aestronglyMeasurable (pair_meas hG)
  unfold liftMat
  exact h3

theorem mode_periodic (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    Function.Periodic (fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameMat θ (G (cylPoint r θ z)) a b : ℂ)) (2 * Real.pi) := by
  intro θ
  have h1 : cylPoint r (θ + 2 * Real.pi) z = cylPoint r θ z := by
    simp only [cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have h2 : frameMat (θ + 2 * Real.pi) = frameMat θ := by
    funext M a b
    simp only [frameMat, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]
  have h3 : -(((azimuth m n * (θ + 2 * Real.pi) : ℝ)) : ℂ) * Complex.I =
      -((azimuth m n * θ : ℝ) : ℂ) * Complex.I + ((-(n * m) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    simp only [azimuth]; push_cast; ring
  simp only
  rw [h1, h2, h3, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem modeMat_sym (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (r z : ℝ) (a b : Fin 3) :
    modeMat m n G r z a b = (1 / (2 * Real.pi) : ℂ) * ∫ θ in (-Real.pi)..Real.pi,
      Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameMat θ (G (cylPoint r θ z)) a b : ℂ) := by
  unfold modeMat
  congr 1
  have := (mode_periodic m n G r z a b).intervalIntegral_add_eq 0 (-Real.pi)
  rw [zero_add, show -Real.pi + 2 * Real.pi = Real.pi by ring] at this
  exact this

theorem mode_fiber (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) {r : ℝ} (hr : 0 < r) (z : ℝ) (a b : Fin 3) :
    modeMat m n G r z a b = (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (-Real.pi)..Real.pi, liftMat m n G a b (cylPoint r θ z) := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  rw [modeMat_sym]
  congr 1
  rw [intervalIntegral.integral_of_le hpi, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo,
    integral_Ioc_eq_integral_Ioo]
  refine setIntegral_congr_fun measurableSet_Ioo fun θ hθ => ?_
  simp only [liftMat, angOf_cyl hr hθ]

theorem rect_ae (K : CellBox) (hK : 0 ≤ K.r₁) :
    K.rect =ᵐ[volume] (K.rect ∩ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) : Set (ℝ × ℝ)) := by
  refine ae_eq_set.2 ⟨?_, by rw [Set.sdiff_eq_empty.2 Set.inter_subset_left, measure_empty]⟩
  refine measure_mono_null (t := ({0} : Set ℝ) ×ˢ (univ : Set ℝ)) ?_ ?_
  · intro p hp
    simp only [mem_sdiff, mem_inter_iff, mem_prod, mem_Ioi, mem_univ, and_true, not_and, not_lt] at hp
    have h1 : K.r₁ ≤ p.1 := hp.1.1.1
    exact ⟨le_antisymm (hp.2 hp.1) (hK.trans h1), trivial⟩
  · rw [Measure.volume_eq_prod, Measure.prod_prod]; simp

theorem mode_int (K : CellBox) (hK : 0 ≤ K.r₁) (m : ℕ) (n : ℤ) (G : Space → (Space →L[ℝ] Space)) (a b : Fin 3)
    {f : Space → ℂ} (hf : Integrable f)
    (hfe : ∀ p ∈ K.rect, 0 < p.1 → ∀ θ ∈ Ioo (-Real.pi) Real.pi, f (cylPoint p.1 θ p.2) = liftMat m n G a b (cylPoint p.1 θ p.2)) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat m n G p.1 p.2 a b) K.rect := by
  have hpi : -Real.pi ≤ Real.pi := by linarith [Real.pi_pos]
  have h1 : IntegrableOn (fun x : ℝ × ℝ => (1 / (2 * Real.pi) : ℂ) * ((x.1 : ℂ) *
      ∫ θ in (-Real.pi)..Real.pi, f (cylPoint x.1 θ x.2))) (K.rect ∩ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) :=
    ((fiber_int hf).mono_set inter_subset_right).const_mul _
  have h2 : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * modeMat m n G p.1 p.2 a b)
      (K.rect ∩ (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
    refine IntegrableOn.congr_fun h1 (fun p hp => ?_) ((rect_meas K).inter (measurableSet_Ioi.prod MeasurableSet.univ))
    have hp1 : 0 < p.1 := hp.2.1
    rw [mode_fiber m n G hp1]
    rw [intervalIntegral.integral_of_le hpi, intervalIntegral.integral_of_le hpi, integral_Ioc_eq_integral_Ioo,
      integral_Ioc_eq_integral_Ioo, setIntegral_congr_fun measurableSet_Ioo fun θ hθ => hfe p hp.1 hp1 θ hθ]
    ring
  exact h2.congr_set_ae (rect_ae K hK)

theorem norm_le_sq (M : Space →L[ℝ] Space) : ‖M‖ ≤ 3 + ∑ i : Fin 3, ‖M (unitVector i)‖ ^ 2 := by
  refine (FracCert.WeakRegularInternal.opNorm_le_sum_basis M).trans ?_
  have e : (3 : ℝ) + ∑ i : Fin 3, ‖M (unitVector i)‖ ^ 2 = ∑ i : Fin 3, (1 + ‖M (unitVector i)‖ ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin]; norm_num
  rw [e]
  exact Finset.sum_le_sum fun i _ => by nlinarith [sq_nonneg (‖M (unitVector i)‖ - 1)]

theorem act_int {G : Space → (Space →L[ℝ] Space)} {Ω : Set Space} (hGm : AEStronglyMeasurable G volume)
    (hG2 : Integrable (fun y => ∑ i : Fin 3, ‖G y (unitVector i)‖ ^ 2)) (hz : ∀ y ∉ Ω, G y = 0)
    (hΩ : Bornology.IsBounded Ω) (m : ℕ) (n : ℤ) (a b : Fin 3) : Integrable (liftMat m n G a b) := by
  obtain ⟨R, hR⟩ := hΩ.subset_closedBall (0 : Space)
  have hb0 : IntegrableOn (fun _ : Space => (3 : ℝ)) (Metric.closedBall (0 : Space) R) := by
    refine (integrableOn_const_iff ?_).2 (Or.inr measure_closedBall_lt_top)
    simp
  have hb : Integrable ((Metric.closedBall (0 : Space) R).indicator (fun _ => (3 : ℝ))) :=
    hb0.integrable_indicator measurableSet_closedBall
  refine Integrable.mono' (hb.add hG2) (liftMat_meas m n hGm a b) (ae_of_all _ fun y => ?_)
  by_cases hy : y ∈ Ω
  · have h1 := liftMat_norm m n G a b y
    have h2 := norm_le_sq (G y)
    simp only [Pi.add_apply, indicator_of_mem (hR hy)]
    linarith
  · have hl : liftMat m n G a b y = 0 := by simp [liftMat, hz y hy, frameMat]
    rw [hl, norm_zero]
    exact add_nonneg (indicator_nonneg (fun _ _ => by norm_num) _) (Finset.sum_nonneg fun _ _ => sq_nonneg _)

theorem cyl_solid (K : CellBox) (hK : IsCellBox K) {p : ℝ × ℝ} (hp : p ∈ K.rect) (θ : ℝ) :
    cylPoint p.1 θ p.2 ∈ K.solid := by
  have hr : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have hz : 0 ≤ p.2 := hK.z_order.1.trans hp.2.1
  have hrad : cylRadius (cylPoint p.1 θ p.2) = p.1 := by
    unfold cylRadius
    rw [cyl0, cyl1, show (p.1 * Real.cos θ) ^ 2 + (p.1 * Real.sin θ) ^ 2 = p.1 ^ 2 by
      linear_combination p.1 ^ 2 * Real.cos_sq_add_sin_sq θ, Real.sqrt_sq hr]
  have hh : |cylHeight (cylPoint p.1 θ p.2)| = p.2 := by
    unfold cylHeight; rw [cyl2, abs_of_nonneg hz]
  exact ⟨by rw [hrad]; exact hp.1.1, by rw [hrad]; exact hp.1.2, by rw [hh]; exact hp.2.1, by rw [hh]; exact hp.2.2⟩

theorem solid_meas (K : CellBox) : MeasurableSet K.solid := by
  have h1 : Continuous cylRadius := by
    unfold cylRadius; exact (((coord_cont 0).pow 2).add ((coord_cont 1).pow 2)).sqrt
  have h2 : Continuous fun y => |cylHeight y| := by unfold cylHeight; exact (coord_cont 2).abs
  exact (measurableSet_le measurable_const h1.measurable).inter ((measurableSet_le h1.measurable measurable_const).inter
    ((measurableSet_le measurable_const h2.measurable).inter (measurableSet_le h2.measurable measurable_const)))

theorem bdd_mode (K : CellBox) (hK : IsCellBox K) {G : Space → (Space →L[ℝ] Space)} (hGm : AEStronglyMeasurable G volume)
    (C : ℝ) (hC : ∀ y ∈ K.solid, ‖G y‖ ≤ C) (hfin : volume K.solid < ⊤) (m : ℕ) (n : ℤ) (a b : Fin 3) :
    MemLp (fun p : ℝ × ℝ => modeMat m n G p.1 p.2 a b) ⊤ (volume.restrict K.rect) := by
  have hf : Integrable (K.solid.indicator (liftMat m n G a b)) := by
    have hc0 : IntegrableOn (fun _ : Space => C) K.solid := by
      refine (integrableOn_const_iff ?_).2 (Or.inr hfin)
      simp
    refine Integrable.mono' (hc0.integrable_indicator (solid_meas K))
      ((liftMat_meas m n hGm a b).indicator (solid_meas K)) (ae_of_all _ fun y => ?_)
    by_cases hy : y ∈ K.solid
    · rw [indicator_of_mem hy, indicator_of_mem hy]; exact (liftMat_norm m n G a b y).trans (hC y hy)
    · rw [indicator_of_notMem hy, indicator_of_notMem hy, norm_zero]
  have hint := mode_int K hK.r_order.1 m n G a b hf (fun p hp _ θ _ => indicator_of_mem (cyl_solid K hK hp θ) _)
  have h1 : AEStronglyMeasurable (fun p : ℝ × ℝ => ((p.1 : ℂ))⁻¹ * ((p.1 : ℂ) * modeMat m n G p.1 p.2 a b))
      (volume.restrict K.rect) :=
    (Complex.measurable_ofReal.comp measurable_fst).inv.aestronglyMeasurable.mul hint.1
  have hae : AEStronglyMeasurable (fun p : ℝ × ℝ => modeMat m n G p.1 p.2 a b) (volume.restrict K.rect) := by
    refine h1.congr ?_
    rw [Filter.EventuallyEq, Measure.restrict_congr_set (rect_ae K hK.r_order.1)]
    refine ae_restrict_of_forall_mem ((rect_meas K).inter (measurableSet_Ioi.prod MeasurableSet.univ)) fun p hp => ?_
    have : (p.1 : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hp.2.1)
    field_simp
  refine memLp_top_of_bound hae C (ae_restrict_of_forall_mem (rect_meas K) fun p hp => ?_)
  unfold modeMat
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := 2 * Real.pi) (C := C)
    (f := fun θ => Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ))
    (fun θ _ => by
      rw [norm_mul, exp_norm, one_mul, Complex.norm_real, Real.norm_eq_abs]
      exact (frame_le _ _ _ _).trans (hC _ (cyl_solid K hK hp θ)))
  rw [norm_mul]
  have hpi := Real.pi_pos
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hn]
  calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..2 * Real.pi, Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (frameMat θ (G (cylPoint p.1 θ p.2)) a b : ℂ)‖ ≤ 1 / (2 * Real.pi) * (C * |2 * Real.pi - 0|) :=
        mul_le_mul_of_nonneg_left hI (by positivity)
    _ = C := by rw [sub_zero, abs_of_pos (by positivity)]; field_simp

theorem modeRegularity : ModeRegularityStatement := by
  intro α _ _ k N slots c hc K S B Cl R hd n a b
  have hK := hd.box
  have hsub : K.solid ⊆ c.cellRegion := hd.solid_in_region
  have hfin : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hsub).measure_lt_top
  obtain ⟨C, hC⟩ := hc.model_bounded
  refine ⟨bdd_mode K hK hc.model_measurable.2.2.1 C (fun y hy => (hC y (hsub hy)).2.2.1) hfin c.order n a b,
    bdd_mode K hK hc.model_measurable.2.2.2 C (fun y hy => (hC y (hsub hy)).2.2.2) hfin c.order n a b, fun i => ⟨?_, ?_⟩⟩
  · exact mode_int K hK.r_order.1 c.order n (c.modelActuatorGrad i) a b
      (act_int (hc.modelActuatorGrad_data i).1 (hc.modelActuatorGrad_data i).2.1 (hc.modelActuatorGrad_data i).2.2
        hc.cellRegion_bounded c.order n a b) (fun _ _ _ _ _ => rfl)
  · exact mode_int K hK.r_order.1 c.order n (c.modelPinField i) a b
      (act_int (hc.modelPin_data i).1 (hc.modelPin_data i).2.1 (hc.modelPin_data i).2.2
        hc.cellRegion_bounded c.order n a b) (fun _ _ _ _ _ => rfl)

end Breakdown.CellCert.CellFormula.FormulaYLinearInternal

namespace Breakdown.CellCert.CellFormula

theorem yCoefLinear : YCoefLinearStatement :=
  yCoefLinear_of_modes FormulaYLinearInternal.modeRegularity

end Breakdown.CellCert.CellFormula
