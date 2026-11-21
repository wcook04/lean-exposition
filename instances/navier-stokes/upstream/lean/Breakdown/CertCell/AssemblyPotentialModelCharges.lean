import Breakdown.CertCell.AssemblyPotentialModelAlgebra

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge

theorem cnormSq_star_vec {β : Type*} [Fintype β] (z : β → ℂ) : cnormSq (star z) = cnormSq z := by
  simp [cnormSq]

theorem curlOfGrad_star_grad (g : Fin 3 × Fin 3 → ℂ) : curlOfGrad (star g) = star (curlOfGrad g) := by
  funext i
  simp [curlOfGrad, alternatingSymbol]

theorem two_sqrt_mul_le (x y c : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : 0 < c) :
    2 * (Real.sqrt x * Real.sqrt y) ≤ c * x + y / c := by
  have hsx := Real.sq_sqrt hx
  have hsy := Real.sq_sqrt hy
  have h0 : 0 ≤ (c * Real.sqrt x - Real.sqrt y) ^ 2 := sq_nonneg _
  have h1 : 2 * (Real.sqrt x * Real.sqrt y) * c ≤ c * x * c + y := by
    have e : (c * Real.sqrt x - Real.sqrt y) ^ 2 = c * x * c + y - 2 * (Real.sqrt x * Real.sqrt y) * c := by
      ring_nf
      rw [hsx, hsy]
    linarith
  have : c * x + y / c = (c * x * c + y) / c := by field_simp
  rw [this, le_div_iff₀ hc]
  linarith

theorem modelTriple_pair_norm_le (S Gω : Fin 3 → Fin 3 → ℂ) (σc γc ℓ β : ℝ) (hσ : 0 ≤ σc) (hγ : 0 ≤ γc)
    (hℓ : 0 < ℓ) (hβ : 0 < β)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ σc ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ γc ^ 2 * cnormSq u)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) (a' : Fin 3 → ℂ) (g' : Fin 3 × Fin 3 → ℂ) :
    2 * ‖modelTriple S Gω a g (star a') (star g')‖
      ≤ β * crossCharge σc γc ℓ a g + β⁻¹ * crossCharge σc γc ℓ a' g' := by
  have hc : ∀ j l, curlGradOfSecondDeriv (curlGradPreimage Gω) (j, l) = Gω j l := curlGradOfSecondDeriv_preimage Gω
  rw [modelTriple_eq_stretchTriple]
  have hB := stretchTripleBound (fun ij => S ij.1 ij.2) (curlGradPreimage Gω) σc γc hσ hγ (fun u => hS u)
    (fun u => by simpa only [hc] using hG u) a g (star a') (star g')
  rw [curlOfGrad_star_grad, cnormSq_star_vec, cnormSq_star_vec, cnormSq_star_vec] at hB
  have hk : 0 ≤ 3 / (2 * Real.sqrt 2) * γc := by positivity
  have e1 := two_sqrt_mul_le (cnormSq (curlOfGrad g)) (cnormSq (curlOfGrad g')) β
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) hβ
  have e2 := two_sqrt_mul_le (cnormSq a) (cnormSq g') (β / ℓ)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (div_pos hβ hℓ)
  have e3 := two_sqrt_mul_le (cnormSq g) (cnormSq a') (β * ℓ)
    (Finset.sum_nonneg fun _ _ => sq_nonneg _) (Finset.sum_nonneg fun _ _ => sq_nonneg _) (mul_pos hβ hℓ)
  have e3' : 2 * (Real.sqrt (cnormSq a') * Real.sqrt (cnormSq g)) ≤ β * ℓ * cnormSq g + cnormSq a' / (β * ℓ) := by
    rw [mul_comm (Real.sqrt _)]; exact e3
  have f2 : cnormSq g' / (β / ℓ) = β⁻¹ * (ℓ * cnormSq g') := by field_simp
  have f2' : β / ℓ * cnormSq a = β * (cnormSq a / ℓ) := by field_simp
  have f3 : cnormSq a' / (β * ℓ) = β⁻¹ * (cnormSq a' / ℓ) := by field_simp
  have f1 : cnormSq (curlOfGrad g') / β = β⁻¹ * cnormSq (curlOfGrad g') := by field_simp
  rw [f2, f2'] at e2
  rw [f3] at e3'
  rw [f1] at e1
  unfold crossCharge
  have m1 := mul_le_mul_of_nonneg_left e1 hσ
  have m2 := mul_le_mul_of_nonneg_left (add_le_add e2 e3') hk
  nlinarith [hB]

theorem modelTriple_self_norm_le (S Gω : Fin 3 → Fin 3 → ℂ) (σc γc ℓ : ℝ) (hσ : 0 ≤ σc) (hγ : 0 ≤ γc)
    (hℓ : 0 < ℓ)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ σc ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ γc ^ 2 * cnormSq u)
    (a : Fin 3 → ℂ) (g : Fin 3 × Fin 3 → ℂ) :
    ‖modelTriple S Gω a g (star a) (star g)‖ ≤ crossCharge σc γc ℓ a g := by
  have h := modelTriple_pair_norm_le S Gω σc γc ℓ 1 hσ hγ hℓ one_pos hS hG a g a g
  simp only [one_mul, inv_one] at h
  linarith




section Base

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

theorem torusIntegrable_bdd_mul {f : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) {g : ℝ → ℝ → ℂ}
    (hg : Continuous (fun z : ℝ × ℝ => g z.1 z.2)) (c : ℝ) (hc : ∀ τ φ, ‖g τ φ‖ ≤ c) :
    IsTorusIntegrable (fun τ φ => g τ φ * f τ φ) :=
  Integrable.bdd_mul (c := c) hf hg.aestronglyMeasurable (Filter.Eventually.of_forall fun z => hc z.1 z.2)

theorem waveSum_continuous (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) (j : Fin 12) :
    Continuous (fun z : ℝ × ℝ => waveSum m S X z.1 z.2 j) := by
  unfold waveSum
  exact continuous_finsetSum _ fun ι _ => (labelPhase_continuous_pair m ι).mul continuous_const

theorem waveSum_norm_le (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) (j : Fin 12) :
    ‖waveSum m S X τ φ j‖ ≤ ∑ ι ∈ S, ‖X ι j‖ := by
  unfold waveSum
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
  rw [norm_mul, labelPhase_norm_one, one_mul]

theorem pairSesq_wave_integrable (m : ℕ) {M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : ∀ i j, IsTorusIntegrable (fun τ φ => M τ φ i j)) (S T : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → Fin 12 → ℂ) :
    IsTorusIntegrable (fun τ φ => pairSesq (M τ φ) (waveSum m S X τ φ) (waveSum m T Y τ φ)) := by
  unfold pairSesq
  refine torusIntegrable_finsum _ _ fun i _ => torusIntegrable_finsum _ _ fun j _ => ?_
  have h := torusIntegrable_bdd_mul (hM i j)
    (g := fun τ φ => (starRingEnd ℂ) (waveSum m S X τ φ i) * waveSum m T Y τ φ j)
    ((Complex.continuous_conj.comp (waveSum_continuous m S X i)).mul (waveSum_continuous m T Y j))
    ((∑ ι ∈ S, ‖X ι i‖) * ∑ ι ∈ T, ‖Y ι j‖) fun τ φ => by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_mul (waveSum_norm_le m S X τ φ i) (waveSum_norm_le m T Y τ φ j) (norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
  refine (h : Integrable _ _).congr (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

theorem torusMean_add' (hT : TorusFacts) {f g : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g) :
    torusMean (fun τ φ => f τ φ + g τ φ) = torusMean f + torusMean g := hT.add f g hf hg

theorem torusMean_sub (hT : TorusFacts) {f g : ℝ → ℝ → ℂ} (hf : IsTorusIntegrable f) (hg : IsTorusIntegrable g) :
    torusMean (fun τ φ => f τ φ - g τ φ) = torusMean f - torusMean g := by
  have hg' : IsTorusIntegrable (fun τ φ => (-1 : ℂ) * g τ φ) := by
    unfold IsTorusIntegrable at *
    exact hg.const_mul (-1)
  have h := hT.add f (fun τ φ => (-1 : ℂ) * g τ φ) hf hg'
  rw [torusMean_const_mul] at h
  have e : (fun τ φ => f τ φ - g τ φ) = (fun τ φ => f τ φ + (-1 : ℂ) * g τ φ) := by
    funext τ φ
    ring
  rw [e, h]
  ring

theorem torusCoef_sub (hT : TorusFacts) (m : ℕ) {M M' : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : ∀ i j, IsTorusIntegrable (fun τ φ => M τ φ i j)) (hM' : ∀ i j, IsTorusIntegrable (fun τ φ => M' τ φ i j))
    (α : ℤ × ℤ) :
    torusCoef m (fun τ φ => M τ φ - M' τ φ) α = torusCoef m M α - torusCoef m M' α := by
  ext i j
  simp only [torusCoef, Matrix.sub_apply, mul_sub]
  have h1 := torusIntegrable_bdd_mul (hM i j) (g := fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)) (Complex.continuous_conj.comp (labelPhase_continuous_pair m α)) 1
    fun τ φ => by rw [Complex.norm_conj, labelPhase_norm_one]
  have h2 := torusIntegrable_bdd_mul (hM' i j) (g := fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)) (Complex.continuous_conj.comp (labelPhase_continuous_pair m α)) 1
    fun τ φ => by rw [Complex.norm_conj, labelPhase_norm_one]
  exact torusMean_sub hT h1 h2

theorem tripleMatrix_sub (S S' Gω Gω' : Fin 3 → Fin 3 → ℂ) :
    tripleMatrix (S - S') (Gω - Gω') = tripleMatrix S Gω - tripleMatrix S' Gω' := by
  ext i j
  simp only [tripleMatrix, Matrix.sub_apply, modelTriple_eq_coef, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
  ring

theorem torusCoef_tripleMatrix (hT : TorusFacts) (m : ℕ) (S Gω : ℝ → ℝ → Fin 3 → Fin 3 → ℂ)
    (hS : ∀ a b, IsTorusIntegrable (fun τ φ => S τ φ a b)) (hG : ∀ a b, IsTorusIntegrable (fun τ φ => Gω τ φ a b))
    (α : ℤ × ℤ) :
    torusCoef m (fun τ φ => tripleMatrix (S τ φ) (Gω τ φ)) α
      = tripleMatrix (fun a b => torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * S τ φ a b))
          (fun a b => torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * Gω τ φ a b)) := by
  have hcS : ∀ a b, IsTorusIntegrable (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * S τ φ a b) := fun a b =>
    torusIntegrable_bdd_mul (hS a b) (g := fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)) (Complex.continuous_conj.comp (labelPhase_continuous_pair m α)) 1
      fun τ φ => by rw [Complex.norm_conj, labelPhase_norm_one]
  have hcG : ∀ a b, IsTorusIntegrable (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * Gω τ φ a b) := fun a b =>
    torusIntegrable_bdd_mul (hG a b) (g := fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)) (Complex.continuous_conj.comp (labelPhase_continuous_pair m α)) 1
      fun τ φ => by rw [Complex.norm_conj, labelPhase_norm_one]
  ext i j
  simp only [torusCoef, tripleMatrix, modelTriple_eq_coef, mul_add, Finset.mul_sum]
  set e : ℝ → ℝ → ℂ := fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ)
  have hA : ∀ a b, IsTorusIntegrable (fun τ φ => e τ φ * (S τ φ a b * coefS (velOf (Pi.single j 1))
      (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b)) := by
    intro a b
    have := (hcS a b).mul_const (coefS (velOf (Pi.single j 1))
      (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [e]
    ring
  have hB : ∀ a b, IsTorusIntegrable (fun τ φ => e τ φ * (Gω τ φ a b * coefG (velOf (Pi.single j 1))
      (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b)) := by
    intro a b
    have := (hcG a b).mul_const (coefG (velOf (Pi.single j 1))
      (gradOf (Pi.single j 1)) (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b)
    refine this.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [e]
    ring
  rw [hT.add _ _ (torusIntegrable_finsum _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => hA a b)
    (torusIntegrable_finsum _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => hB a b)]
  rw [torusMean_finsum hT _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => hA a b,
    torusMean_finsum hT _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => hB a b]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [torusMean_finsum hT _ _ fun b _ => hA a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 : (fun τ φ => e τ φ * (S τ φ a b * coefS (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
        (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b))
        = fun τ φ => coefS (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
          (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b * (e τ φ * S τ φ a b) := by
      funext τ φ
      ring
    rw [e1, torusMean_const_mul]
    ring
  · refine Finset.sum_congr rfl fun a _ => ?_
    rw [torusMean_finsum hT _ _ fun b _ => hB a b]
    refine Finset.sum_congr rfl fun b _ => ?_
    have e1 : (fun τ φ => e τ φ * (Gω τ φ a b * coefG (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
        (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b))
        = fun τ φ => coefG (velOf (Pi.single j 1)) (gradOf (Pi.single j 1))
          (star (velOf (Pi.single i 1))) (star (gradOf (Pi.single i 1))) a b * (e τ φ * Gω τ φ a b) := by
      funext τ φ
      ring
    rw [e1, torusMean_const_mul]
    ring

end Base


section Charges

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation CellCert.CellAnalysis

def chargeForm (c₁ c₂ c₃ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  c₁ * cnormSq (curlOfGrad (gradOf U)) + c₂ * cnormSq (gradOf U) + c₃ * cnormSq (velOf U)

theorem crossCharge_eq_chargeForm (σc γc ℓ : ℝ) (U : Fin 12 → ℂ) :
    Bridge.crossCharge σc γc ℓ (velOf U) (gradOf U)
      = chargeForm σc (3 / (2 * Real.sqrt 2) * γc * ℓ) (3 / (2 * Real.sqrt 2) * γc / ℓ) U := by
  unfold Bridge.crossCharge chargeForm
  ring

theorem curlComp_strainOfVec (U : Fin 12 → ℂ) (i : Fin 3) :
    curlComp (strainOfVec U) i = curlOfGrad (gradOf U) i := by
  fin_cases i <;> simp [curlComp, curlOfGrad, strainOfVec, Fin.sum_univ_three, CellCert.permSign, alternatingSymbol] <;>
    norm_num

theorem curlSq_strainOfVec (U : Fin 12 → ℂ) : curlSq (strainOfVec U) = cnormSq (curlOfGrad (gradOf U)) := by
  simp only [curlSq, cnormSq, curlComp_strainOfVec]

theorem sumSq_strainOfVec (U : Fin 12 → ℂ) : sumSq (strainOfVec U) = cnormSq (gradOf U) := by
  simp only [sumSq, cnormSq, strainOfVec, Fintype.sum_prod_type]

theorem vecSq_velOf (U : Fin 12 → ℂ) : vecSq (velOf U) = cnormSq (velOf U) := rfl

theorem highOwnCharge_eq {V : Type} (P : PotentialData V) (U : Fin 12 → ℂ) :
    highOwnCharge P U = chargeForm (P.youngCurl * P.highStrain) (3 / (2 * Real.sqrt 2) * P.highGrad * P.youngStrain)
      (3 / (2 * Real.sqrt 2) * P.highGrad * P.youngVel) U := by
  unfold highOwnCharge chargeForm
  rw [curlSq_strainOfVec, sumSq_strainOfVec, vecSq_velOf]
  ring

theorem highPartnerCharge_eq {V : Type} (P : PotentialData V) (U : Fin 12 → ℂ) :
    highPartnerCharge P U = chargeForm (P.highStrain / P.youngCurl) (3 / (2 * Real.sqrt 2) * P.highGrad / P.youngVel)
      (3 / (2 * Real.sqrt 2) * P.highGrad / P.youngStrain) U := by
  unfold highPartnerCharge chargeForm
  rw [curlSq_strainOfVec, sumSq_strainOfVec, vecSq_velOf]
  ring

theorem curlOfGrad_wave (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → ℂ) (g : ℤ × ℤ → Fin 3 × Fin 3 → ℂ) (i : Fin 3) :
    curlOfGrad (fun ab => ∑ ι ∈ S, c ι * g ι ab) i = ∑ ι ∈ S, c ι * curlOfGrad (g ι) i := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [curlOfGrad]
  | insert a S ha ih =>
    have e : (fun ab => ∑ ι ∈ insert a S, c ι * g ι ab) = c a • g a + (fun ab => ∑ ι ∈ S, c ι * g ι ab) := by
      funext ab
      simp [Finset.sum_insert ha]
    rw [e, curlOfGrad_add_fn, curlOfGrad_smul_fn, ih, Finset.sum_insert ha]

theorem torusMean_cnormSq_wave (hT : TorusFacts) {m : ℕ} (hm : 1 ≤ m) {κ : Type*} [Fintype κ]
    (S : Finset (ℤ × ℤ)) (c : ℤ × ℤ → κ → ℂ) :
    torusMean (fun τ φ => ((cnormSq (fun k => ∑ ι ∈ S, labelPhase m ι τ φ * c ι k) : ℝ) : ℂ))
      = ∑ ι ∈ S, ((cnormSq (c ι) : ℝ) : ℂ) := by
  have hint : ∀ k, IsTorusIntegrable (fun τ φ => (((‖∑ ι ∈ S, labelPhase m ι τ φ * c ι k‖ ^ 2 : ℝ)) : ℂ)) := by
    intro k
    refine torusIntegrable_of_continuous hT ?_ ((∑ ι ∈ S, ‖c ι k‖) ^ 2) fun τ φ => ?_
    · have h1 : Continuous (fun z : ℝ × ℝ => ∑ ι ∈ S, labelPhase m ι z.1 z.2 * c ι k) :=
        continuous_finsetSum _ fun ι _ => (labelPhase_continuous_pair m ι).mul continuous_const
      exact Complex.continuous_ofReal.comp (h1.norm.pow 2)
    · rw [Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
      have h2 : ‖∑ ι ∈ S, labelPhase m ι τ φ * c ι k‖ ≤ ∑ ι ∈ S, ‖c ι k‖ := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
        rw [norm_mul, labelPhase_norm_one, one_mul]
      exact pow_le_pow_left₀ (norm_nonneg _) h2 2
  have e : (fun τ φ => ((cnormSq (fun k => ∑ ι ∈ S, labelPhase m ι τ φ * c ι k) : ℝ) : ℂ))
      = fun τ φ => ∑ k : κ, (((‖∑ ι ∈ S, labelPhase m ι τ φ * c ι k‖ ^ 2 : ℝ)) : ℂ) := by
    funext τ φ
    simp only [cnormSq, Complex.ofReal_sum]
  rw [e, torusMean_finsum hT _ _ fun k _ => hint k]
  simp only [torusMean_wave_normSq hT hm, cnormSq, Complex.ofReal_sum]
  exact Finset.sum_comm

theorem chargeForm_wave (c₁ c₂ c₃ : ℝ) (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) :
    chargeForm c₁ c₂ c₃ (waveSum m S X τ φ)
      = c₁ * cnormSq (fun i => ∑ ι ∈ S, labelPhase m ι τ φ * curlOfGrad (gradOf (X ι)) i)
        + c₂ * cnormSq (fun ab => ∑ ι ∈ S, labelPhase m ι τ φ * gradOf (X ι) ab)
        + c₃ * cnormSq (fun a => ∑ ι ∈ S, labelPhase m ι τ φ * velOf (X ι) a) := by
  unfold chargeForm
  have e : (fun i => curlOfGrad (gradOf (waveSum m S X τ φ)) i)
      = fun i => ∑ ι ∈ S, labelPhase m ι τ φ * curlOfGrad (gradOf (X ι)) i := by
    funext i
    exact curlOfGrad_wave S (fun ι => labelPhase m ι τ φ) (fun ι => gradOf (X ι)) i
  have e' : curlOfGrad (gradOf (waveSum m S X τ φ)) = fun i => curlOfGrad (gradOf (waveSum m S X τ φ)) i := rfl
  rw [e', e]
  rfl

theorem chargeForm_wave_continuous (c₁ c₂ c₃ : ℝ) (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) :
    Continuous (fun z : ℝ × ℝ => chargeForm c₁ c₂ c₃ (waveSum m S X z.1 z.2)) := by
  unfold chargeForm cnormSq
  have hw : ∀ j, Continuous (fun z : ℝ × ℝ => waveSum m S X z.1 z.2 j) := waveSum_continuous m S X
  have hg : ∀ ab : Fin 3 × Fin 3, Continuous (fun z : ℝ × ℝ => gradOf (waveSum m S X z.1 z.2) ab) := fun ab => hw _
  have hv : ∀ a : Fin 3, Continuous (fun z : ℝ × ℝ => velOf (waveSum m S X z.1 z.2) a) := fun a => hw _
  have hc : ∀ i : Fin 3, Continuous (fun z : ℝ × ℝ => curlOfGrad (gradOf (waveSum m S X z.1 z.2)) i) := by
    intro i
    unfold curlOfGrad
    exact continuous_finsetSum _ fun j _ => continuous_finsetSum _ fun l _ => continuous_const.mul (hg (l, j))
  refine ((continuous_const.mul (continuous_finsetSum _ fun i _ => (hc i).norm.pow 2)).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => (hg i).norm.pow 2))).add
    (continuous_const.mul (continuous_finsetSum _ fun i _ => (hv i).norm.pow 2))

theorem torusMean_chargeForm_wave (hT : TorusFacts) {m : ℕ} (hm : 1 ≤ m) (c₁ c₂ c₃ : ℝ) (S : Finset (ℤ × ℤ))
    (X : ℤ × ℤ → Fin 12 → ℂ) :
    torusMean (fun τ φ => ((chargeForm c₁ c₂ c₃ (waveSum m S X τ φ) : ℝ) : ℂ))
      = ∑ ι ∈ S, ((chargeForm c₁ c₂ c₃ (X ι) : ℝ) : ℂ) := by
  simp only [chargeForm_wave]
  have i1 : IsTorusIntegrable (fun τ φ => ((cnormSq (fun i => ∑ ι ∈ S, labelPhase m ι τ φ *
      curlOfGrad (gradOf (X ι)) i) : ℝ) : ℂ)) := by
    have h := chargeForm_wave_continuous 1 0 0 m S X
    refine torusIntegrable_of_continuous hT ?_ (∑ i : Fin 3, (∑ ι ∈ S, ‖curlOfGrad (gradOf (X ι)) i‖) ^ 2)
      fun τ φ => ?_
    · have e : (fun z : ℝ × ℝ => ((cnormSq (fun i => ∑ ι ∈ S, labelPhase m ι z.1 z.2 *
          curlOfGrad (gradOf (X ι)) i) : ℝ) : ℂ))
          = fun z => ((chargeForm 1 0 0 (waveSum m S X z.1 z.2) : ℝ) : ℂ) := by
        funext z
        rw [chargeForm_wave]
        ring
      rw [e]
      exact Complex.continuous_ofReal.comp h
    · rw [Complex.norm_real]
      simp only [cnormSq]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
      rw [norm_mul, labelPhase_norm_one, one_mul]
  have i2 : IsTorusIntegrable (fun τ φ => ((cnormSq (fun ab => ∑ ι ∈ S, labelPhase m ι τ φ *
      gradOf (X ι) ab) : ℝ) : ℂ)) := by
    have h := chargeForm_wave_continuous 0 1 0 m S X
    refine torusIntegrable_of_continuous hT ?_ (∑ ab : Fin 3 × Fin 3, (∑ ι ∈ S, ‖gradOf (X ι) ab‖) ^ 2)
      fun τ φ => ?_
    · have e : (fun z : ℝ × ℝ => ((cnormSq (fun ab => ∑ ι ∈ S, labelPhase m ι z.1 z.2 *
          gradOf (X ι) ab) : ℝ) : ℂ))
          = fun z => ((chargeForm 0 1 0 (waveSum m S X z.1 z.2) : ℝ) : ℂ) := by
        funext z
        rw [chargeForm_wave]
        ring
      rw [e]
      exact Complex.continuous_ofReal.comp h
    · rw [Complex.norm_real]
      simp only [cnormSq]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
      rw [norm_mul, labelPhase_norm_one, one_mul]
  have i3 : IsTorusIntegrable (fun τ φ => ((cnormSq (fun a => ∑ ι ∈ S, labelPhase m ι τ φ *
      velOf (X ι) a) : ℝ) : ℂ)) := by
    have h := chargeForm_wave_continuous 0 0 1 m S X
    refine torusIntegrable_of_continuous hT ?_ (∑ a : Fin 3, (∑ ι ∈ S, ‖velOf (X ι) a‖) ^ 2)
      fun τ φ => ?_
    · have e : (fun z : ℝ × ℝ => ((cnormSq (fun a => ∑ ι ∈ S, labelPhase m ι z.1 z.2 *
          velOf (X ι) a) : ℝ) : ℂ))
          = fun z => ((chargeForm 0 0 1 (waveSum m S X z.1 z.2) : ℝ) : ℂ) := by
        funext z
        rw [chargeForm_wave]
        ring
      rw [e]
      exact Complex.continuous_ofReal.comp h
    · rw [Complex.norm_real]
      simp only [cnormSq]
      rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
      refine Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (norm_nonneg _) ?_ 2
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun ι _ => ?_)
      rw [norm_mul, labelPhase_norm_one, one_mul]
  have e : (fun τ φ => ((c₁ * cnormSq (fun i => ∑ ι ∈ S, labelPhase m ι τ φ * curlOfGrad (gradOf (X ι)) i)
        + c₂ * cnormSq (fun ab => ∑ ι ∈ S, labelPhase m ι τ φ * gradOf (X ι) ab)
        + c₃ * cnormSq (fun a => ∑ ι ∈ S, labelPhase m ι τ φ * velOf (X ι) a) : ℝ) : ℂ))
      = fun τ φ => ((c₁ : ℂ) * ((cnormSq (fun i => ∑ ι ∈ S, labelPhase m ι τ φ * curlOfGrad (gradOf (X ι)) i) : ℝ) : ℂ)
        + (c₂ : ℂ) * ((cnormSq (fun ab => ∑ ι ∈ S, labelPhase m ι τ φ * gradOf (X ι) ab) : ℝ) : ℂ))
        + (c₃ : ℂ) * ((cnormSq (fun a => ∑ ι ∈ S, labelPhase m ι τ φ * velOf (X ι) a) : ℝ) : ℂ) := by
    funext τ φ
    push_cast
    ring
  rw [e]
  have j1 : IsTorusIntegrable (fun τ φ => (c₁ : ℂ) * ((cnormSq (fun i => ∑ ι ∈ S, labelPhase m ι τ φ *
      curlOfGrad (gradOf (X ι)) i) : ℝ) : ℂ)) := Integrable.const_mul i1 _
  have j2 : IsTorusIntegrable (fun τ φ => (c₂ : ℂ) * ((cnormSq (fun ab => ∑ ι ∈ S, labelPhase m ι τ φ *
      gradOf (X ι) ab) : ℝ) : ℂ)) := Integrable.const_mul i2 _
  have j3 : IsTorusIntegrable (fun τ φ => (c₃ : ℂ) * ((cnormSq (fun a => ∑ ι ∈ S, labelPhase m ι τ φ *
      velOf (X ι) a) : ℝ) : ℂ)) := Integrable.const_mul i3 _
  rw [hT.add _ _ (torusIntegrable_add j1 j2) j3, hT.add _ _ j1 j2, torusMean_const_mul, torusMean_const_mul,
    torusMean_const_mul, torusMean_cnormSq_wave hT hm, torusMean_cnormSq_wave hT hm, torusMean_cnormSq_wave hT hm]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  simp only [chargeForm]
  push_cast
  rfl

end Charges

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
