import Breakdown.CertCell.AssemblyPotentialSharpSymbol

open scoped ComplexConjugate
open Filter Topology Matrix

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace Sharp

open Bridge Bridge.Internal.MeanStretch Coercive.StretchInternal Coercive.Internal.ModeRotation CellCalculus

theorem labelHarmonic_zero_iff (m : ℕ) (hm : 1 ≤ m) (α : ℤ × ℤ) : labelHarmonic m α = 0 ↔ α = 0 := by
  constructor
  · intro h
    have h1 : labelTime α = 0 := congrArg Prod.fst h
    have h2 : labelAzimuth m α = 0 := congrArg Prod.snd h
    unfold labelTime at h1
    unfold labelAzimuth at h2
    have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
    have ha : α.1 = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact h
      · exact absurd h hm'
    ext
    · exact ha
    · simp only [Prod.snd_zero]; omega
  · rintro rfl
    simp [labelHarmonic, labelTime, labelAzimuth]

theorem sum_drop_zero (S : Finset (ℤ × ℤ)) (w c : ℤ × ℤ → ℂ) :
    ∑ β ∈ S, w β * (if β = 0 then 0 else c β) = ∑ β ∈ S, w β * c β - (if (0 : ℤ × ℤ) ∈ S then w 0 * c 0 else 0) := by
  have e : ∑ β ∈ S, w β * c β
      = ∑ β ∈ S, w β * (if β = 0 then 0 else c β) + ∑ β ∈ S, (if β = 0 then w β * c β else 0) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun β _ => ?_
    split_ifs <;> ring
  rw [e, Finset.sum_ite_eq' S (0 : ℤ × ℤ) (fun β => w β * c β)]
  ring

theorem loss_bound (M : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) :
    |(sesq12 M U U).re| ≤ 2 * (∑ i, ∑ j, ‖M i j‖) * cnormSq U := by
  have h := re_sesq_le M U U
  linarith

theorem curl_le (U : Fin 12 → ℂ) : cnormSq (curlOfGrad (gradOf U)) ≤ 2 * (∑ i, ∑ j, ‖curlPairMatrix i j‖) * cnormSq U := by
  rw [← re_sesq12_curlPairMatrix]
  exact (le_abs_self _).trans (loss_bound _ _)

theorem grad_le (U : Fin 12 → ℂ) : cnormSq (gradOf U) ≤ 2 * (∑ i, ∑ j, ‖gradDiag i j‖) * cnormSq U := by
  rw [← re_sesq12_gradDiag]
  exact (le_abs_self _).trans (loss_bound _ _)

theorem vel_le (U : Fin 12 → ℂ) : cnormSq (velOf U) ≤ 2 * (∑ i, ∑ j, ‖velDiag i j‖) * cnormSq U := by
  rw [← re_sesq12_velDiag]
  exact (le_abs_self _).trans (loss_bound _ _)

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

def meanSecondDeriv (S : Finset (ℤ × ℤ)) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y0 : Space) :
    Fin 3 → Fin 3 → Fin 3 → ℝ :=
  fun a b c => if (0 : ℤ × ℤ) ∈ S then (modeSecondDeriv 0 HW 0 y0 (a, b, c)).re else 0

def waveSecondDeriv (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (β : ℤ × ℤ) (y0 : Space) :
    Fin 3 × Fin 3 × Fin 3 → ℂ :=
  if β = 0 then 0 else modeSecondDeriv β HW 0 y0

def waveSymbol (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))
    (y0 : Space) : ℤ × ℤ → Matrix (Fin 12) (Fin 12) ℂ :=
  fun β => tripleMatrix (modeGrad β (gradField W) 0 y0) (waveSecondDeriv HW β y0)

theorem symbol_point (S : Finset (ℤ × ℤ)) (W : ℝ → Space → Space)
    (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y0 : Space)
    (hE1 : ∀ τ φ a b, ((fibGrad (gradField W) y0 τ φ a b : ℝ) : ℂ)
      = ∑ β ∈ S, phase β τ φ * modeGrad β (gradField W) 0 y0 (a, b))
    (hE2 : ∀ τ φ a b c, ((frameSecondDeriv HW y0 τ φ a b c : ℝ) : ℂ) = ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (a, b, c))
    (hV : ∀ τ φ j l, fibGrad (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) y0 τ φ j l
      = curlGradReal (frameSecondDeriv HW y0 τ φ) j l)
    (hsym : ∀ σ y u w, HW σ y u w = HW σ y w u) (x0 : Fin 3 → Fin 3 → ℝ)
    (hx0 : ∀ a c, x0 a c = curlGradReal (meanSecondDeriv S HW y0) a c) (lamS KS ℓ : ℝ) (hℓ : 0 < ℓ) (hKS0 : 0 ≤ KS)
    (hstrain : ∀ τ φ (u : Space), inner ℝ u (gradField W τ (axialRot φ y0) u) ≤ lamS * ‖u‖ ^ 2)
    (hwave : ∀ τ φ (u : Space), ‖CoerciveWeak.vortGradMap (HW τ (axialRot φ y0)) u
      - CellMatField.frameMap φ x0 u‖ ≤ KS * ‖u‖)
    (σ θ : ℝ) (U : Fin 12 → ℂ) :
    -(sesq12 (lossMatrix lamS ((1 / 2) * Real.sqrt (7 / 2) * KS * ℓ) ((1 / 2) * Real.sqrt (7 / 2) * KS / ℓ)) U U).re
      ≤ (sesq12 (symbolAt S (waveSymbol W HW y0) σ θ) U U).re := by
  unfold symbolAt waveSymbol
  refine symbol_lower S (fun β => wavePhase β σ θ) (fun β => modeGrad β (gradField W) 0 y0) (fun β => waveSecondDeriv HW β y0)
    (fibGrad (gradField W) y0 σ θ) (fun a b c => frameSecondDeriv HW y0 σ θ a b c - meanSecondDeriv S HW y0 a b c)
    ?_ ?_ lamS KS ℓ ?_ ?_ hKS0 ?_ hℓ U
  · funext ij
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hE1 σ θ ij.1 ij.2]
    rfl
  · funext ijl
    rw [Finset.sum_apply]
    simp only [Pi.smul_apply, smul_eq_mul, waveSecondDeriv]
    have e : ∀ β, (if β = 0 then (0 : Fin 3 × Fin 3 × Fin 3 → ℂ) else modeSecondDeriv β HW 0 y0) ijl
        = if β = 0 then 0 else modeSecondDeriv β HW 0 y0 ijl := by
      intro β; split_ifs <;> rfl
    simp only [e]
    rw [sum_drop_zero S (fun β => wavePhase β σ θ) (fun β => modeSecondDeriv β HW 0 y0 ijl)]
    have e2 : ∑ β ∈ S, wavePhase β σ θ * modeSecondDeriv β HW 0 y0 ijl
        = ((frameSecondDeriv HW y0 σ θ ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ) := by
      rw [hE2 σ θ ijl.1 ijl.2.1 ijl.2.2]
      rfl
    rw [e2, wavePhase_zero, one_mul]
    unfold meanSecondDeriv
    split_ifs with h0
    · rw [modeSecondDeriv_zero_real HW y0 ijl.1 ijl.2.1 ijl.2.2]
      simp only [Complex.ofReal_re]
      push_cast
      ring
    · push_cast
      ring
  · exact strain_frame _ θ lamS (hstrain σ θ)
  · refine curlGradReal_trace _ fun b k a => ?_
    simp only [meanSecondDeriv]
    rw [frameSecondDeriv_symm HW hsym, modeSecondDeriv_symm 0 HW hsym]
  · intro x
    have e : curlGradReal (fun a b c => frameSecondDeriv HW y0 σ θ a b c - meanSecondDeriv S HW y0 a b c)
        = fun a c => axialRot (-θ) (CoerciveWeak.vortGradMap (HW σ (axialRot θ y0)) (axialRot θ (unitVector c))) a
          - x0 a c := by
      funext a c
      rw [curlGradReal_sub, hx0, ← hV]
      rfl
    rw [e]
    exact wave_frame _ θ KS x0 hKS0 (hwave σ θ) x

def pointLoss (lam g0 gw ℓ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  lam * cnormSq (curlOfGrad (gradOf U))
    + Real.sqrt (7 / 2) * g0 * Real.sqrt (cnormSq (gradOf U)) * Real.sqrt (cnormSq (velOf U))
    + (1 / 2) * Real.sqrt (7 / 2) * gw * (ℓ * cnormSq (gradOf U) + cnormSq (velOf U) / ℓ)

theorem summable_of_cnorm {X : ℤ × ℤ → Fin 12 → ℂ} (hX : Summable fun ι => cnormSq (X ι)) (f : ℤ × ℤ → ℝ) (C : ℝ)
    (hf : ∀ ι, |f ι| ≤ C * cnormSq (X ι)) : Summable f :=
  Summable.of_norm_bounded (hX.mul_left C) fun ι => by rw [Real.norm_eq_abs]; exact hf ι

theorem summable_shift_sesq {X : ℤ × ℤ → Fin 12 → ℂ} (hX : Summable fun ι => cnormSq (X ι))
    (M : Matrix (Fin 12) (Fin 12) ℂ) (α : ℤ × ℤ) :
    Summable fun ι => (sesq12 M (X ι) (X (ι - α))).re := by
  have hXs : Summable fun ι => cnormSq (X (ι - α)) := by
    have h := hX.comp_injective (sub_left_injective (b := α))
    exact h
  refine Summable.of_norm_bounded ((hX.add hXs).mul_left (∑ i, ∑ j, ‖M i j‖)) fun ι => ?_
  rw [Real.norm_eq_abs]
  exact re_sesq_le _ _ _

theorem tripleMatrix_zero_zero : tripleMatrix 0 0 = 0 := by
  ext i j
  show (pairForm 0 0 (slotL (Pi.single j 1)) (slotL (Pi.single i 1))
      + pairForm 0 0 (slotL (Pi.single i 1)) (slotL (Pi.single j 1))) / 2 = 0
  rw [pairForm_zero_W, pairForm_zero_W]
  simp

theorem sesq12_zero_matrix (U U' : Fin 12 → ℂ) : sesq12 0 U U' = 0 := by
  simp [sesq12]

theorem mean_real (S : Finset (ℤ × ℤ)) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y0 : Space)
    (hE2 : ∀ τ φ a b c, ((frameSecondDeriv HW y0 τ φ a b c : ℝ) : ℂ) = ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (a, b, c))
    (hV : ∀ τ φ j l, fibGrad (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) y0 τ φ j l
      = curlGradReal (frameSecondDeriv HW y0 τ φ) j l) (a c : Fin 3) :
    modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) 0 y0 (a, c)
      = ((curlGradReal (meanSecondDeriv S HW y0) a c : ℝ) : ℂ) := by
  rw [mean_vort_identity S HW y0 hE2 hV a c]
  unfold curlGradReal meanSecondDeriv
  push_cast
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun b _ => ?_
  split_ifs
  · rw [← modeSecondDeriv_zero_real]
  · simp

theorem point_bound (m : ℕ) (hm : 1 ≤ m) (S H : Finset (ℤ × ℤ)) (hH : ∀ α, α ∈ H ↔ labelHarmonic m α ∈ S)
    (W : ℝ → Space → Space) (HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (y0 : Space)
    (hE1 : ∀ τ φ a b, ((fibGrad (gradField W) y0 τ φ a b : ℝ) : ℂ)
      = ∑ β ∈ S, phase β τ φ * modeGrad β (gradField W) 0 y0 (a, b))
    (hE2 : ∀ τ φ a b c, ((frameSecondDeriv HW y0 τ φ a b c : ℝ) : ℂ) = ∑ β ∈ S, phase β τ φ * modeSecondDeriv β HW 0 y0 (a, b, c))
    (hV : ∀ τ φ j l, fibGrad (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) y0 τ φ j l
      = curlGradReal (frameSecondDeriv HW y0 τ φ) j l)
    (hsym : ∀ σ y u w, HW σ y u w = HW σ y w u)
    (lamι g0ι gwι : ℤ × ℤ → ℝ) (ℓ C : ℝ) (hℓ : 0 < ℓ)
    (hstrain : ∀ ι τ φ (u : Space), inner ℝ u (gradField W τ (axialRot φ y0) u) ≤ lamι ι * ‖u‖ ^ 2)
    (hmean : ∀ ι, opBound (fun a b => modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) 0 y0 (a, b)) (g0ι ι))
    (hwave : ∀ ι τ φ (u : Space), ‖CoerciveWeak.vortGradMap (HW τ (axialRot φ y0)) u
      - CellMatField.frameMap φ (fun a b => (modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) 0 y0 (a, b)).re) u‖
        ≤ gwι ι * ‖u‖)
    (hg0 : ∀ ι, 0 ≤ g0ι ι) (hgw : ∀ ι, 0 ≤ gwι ι) (hC : ∀ ι, |lamι ι| ≤ C ∧ g0ι ι ≤ C ∧ gwι ι ≤ C)
    (X : ℤ × ℤ → Fin 12 → ℂ) (hX : Summable fun ι => cnormSq (X ι)) :
    -(∑' ι, pointLoss (lamι ι) (g0ι ι) (gwι ι) ℓ (X ι))
      ≤ ∑' ι, ∑ α ∈ H, (sesq12 (tripleMatrix (modeGrad (labelHarmonic m α) (gradField W) 0 y0)
          (modeSecondDeriv (labelHarmonic m α) HW 0 y0)) (X ι) (X (ι - α))).re := by
  set x0 : Fin 3 → Fin 3 → ℝ := fun a b => (modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) 0 y0 (a, b)).re
    with hx0def
  have hreal : ∀ a c, modeGrad 0 (fun σ y => CoerciveWeak.vortGradMap (HW σ y)) 0 y0 (a, c) = ((x0 a c : ℝ) : ℂ) := by
    intro a c
    rw [hx0def]
    simp only
    rw [mean_real S HW y0 hE2 hV a c, Complex.ofReal_re]
  have hx0 : ∀ a c, x0 a c = curlGradReal (meanSecondDeriv S HW y0) a c := by
    intro a c
    rw [hx0def]
    simp only
    rw [mean_real S HW y0 hE2 hV a c, Complex.ofReal_re]
  set lamS := ⨅ ι, lamι ι with hlamS
  set KS := ⨅ ι, gwι ι with hKS
  have hKS0 : 0 ≤ KS := le_ciInf hgw
  have hlamle : ∀ ι, lamS ≤ lamι ι := fun ι =>
    ciInf_le ⟨-C, by rintro _ ⟨j, rfl⟩; exact neg_le_of_abs_le (hC j).1⟩ ι
  have hKle : ∀ ι, KS ≤ gwι ι := fun ι => ciInf_le ⟨0, by rintro _ ⟨j, rfl⟩; exact hgw j⟩ ι
  have hpt := fun σ θ U => symbol_point S W HW y0 hE1 hE2 hV hsym x0 hx0 lamS KS ℓ hℓ hKS0
    (fun τ φ u => le_iInf_mul (sq_nonneg _) fun ι => hstrain ι τ φ u)
    (fun τ φ u => le_iInf_mul (norm_nonneg _) fun ι => hwave ι τ φ u) σ θ U
  have h0 : ∀ α, α ∈ ({0} : Finset (ℤ × ℤ)) ↔ labelHarmonic m α ∈ ({0} : Finset (ℤ × ℤ)) := by
    intro α
    simp only [Finset.mem_singleton]
    exact (labelHarmonic_zero_iff m hm α).symm
  set N := lossMatrix lamS ((1 / 2) * Real.sqrt (7 / 2) * KS * ℓ) ((1 / 2) * Real.sqrt (7 / 2) * KS / ℓ) with hN
  have T := symbolForm_lower m S H hH h0 (waveSymbol W HW y0) N hpt X hX
  set A : ℤ × ℤ → ℝ := fun ι => ∑ α ∈ H, (sesq12 (waveSymbol W HW y0 (labelHarmonic m α)) (X ι) (X (ι - α))).re
    with hA
  set Bm : ℤ × ℤ → ℝ := fun ι => if (0 : ℤ × ℤ) ∈ H then
    (sesq12 (tripleMatrix 0 (modeSecondDeriv 0 HW 0 y0)) (X ι) (X ι)).re else 0 with hBm
  have hsplit : ∀ ι, ∑ α ∈ H, (sesq12 (tripleMatrix (modeGrad (labelHarmonic m α) (gradField W) 0 y0)
      (modeSecondDeriv (labelHarmonic m α) HW 0 y0)) (X ι) (X (ι - α))).re = A ι + Bm ι := by
    intro ι
    have e1 : ∀ α, tripleMatrix (modeGrad (labelHarmonic m α) (gradField W) 0 y0) (modeSecondDeriv (labelHarmonic m α) HW 0 y0)
        = waveSymbol W HW y0 (labelHarmonic m α)
          + tripleMatrix 0 (if α = 0 then modeSecondDeriv 0 HW 0 y0 else 0) := by
      intro α
      unfold waveSymbol
      rw [← tripleMatrix_split]
      congr 1
      unfold waveSecondDeriv
      by_cases hα : α = 0
      · subst hα
        have : labelHarmonic m 0 = 0 := (labelHarmonic_zero_iff m hm 0).mpr rfl
        simp [this]
      · have : labelHarmonic m α ≠ 0 := fun h => hα ((labelHarmonic_zero_iff m hm α).mp h)
        simp [this, hα]
    simp only [e1, sesq12_add, Complex.add_re, Finset.sum_add_distrib]
    congr 1
    rw [hBm]
    simp only
    have e2 : ∀ α ∈ H, (sesq12 (tripleMatrix 0 (if α = 0 then modeSecondDeriv 0 HW 0 y0 else 0)) (X ι) (X (ι - α))).re
        = if α = 0 then (sesq12 (tripleMatrix 0 (modeSecondDeriv 0 HW 0 y0)) (X ι) (X ι)).re else 0 := by
      intro α _
      by_cases hα : α = 0
      · subst hα; simp
      · simp [hα, tripleMatrix_zero_zero, sesq12_zero_matrix]
    rw [Finset.sum_congr rfl e2, Finset.sum_ite_eq' H (0 : ℤ × ℤ)]
  have hAs : Summable A := summable_sum fun α _ => summable_shift_sesq hX _ α
  have hBs : Summable Bm := by
    rw [hBm]
    by_cases h0H : (0 : ℤ × ℤ) ∈ H
    · simp only [h0H, if_true]
      have := summable_shift_sesq hX (tripleMatrix 0 (modeSecondDeriv 0 HW 0 y0)) 0
      simpa using this
    · simp only [h0H, if_false]
      exact summable_zero
  rw [tsum_congr hsplit, hAs.tsum_add hBs]
  set c1 := 2 * (∑ i, ∑ j, ‖curlPairMatrix i j‖)
  set c2 := 2 * (∑ i, ∑ j, ‖gradDiag i j‖)
  set c3 := 2 * (∑ i, ∑ j, ‖velDiag i j‖)
  have hc1 : 0 ≤ c1 := by positivity
  have hc2 : 0 ≤ c2 := by positivity
  have hc3 : 0 ≤ c3 := by positivity
  set L1 : ℤ × ℤ → ℝ := fun ι => lamι ι * cnormSq (curlOfGrad (gradOf (X ι)))
    + (1 / 2) * Real.sqrt (7 / 2) * gwι ι * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ) with hL1
  set L2 : ℤ × ℤ → ℝ := fun ι => Real.sqrt (7 / 2) * g0ι ι * Real.sqrt (cnormSq (gradOf (X ι)))
    * Real.sqrt (cnormSq (velOf (X ι))) with hL2
  have hsq7 : 0 ≤ Real.sqrt (7 / 2) := Real.sqrt_nonneg _
  have hCnn : 0 ≤ C := (abs_nonneg _).trans (hC 0).1
  have hL2nn : ∀ ι, 0 ≤ L2 ι := fun ι => by
    simp only [hL2]
    have := hg0 ι
    positivity
  have hL2le : ∀ ι, L2 ι ≤ Real.sqrt (7 / 2) * C * ((1 / 2) * (c2 + c3)) * cnormSq (X ι) := by
    intro ι
    simp only [hL2]
    have hs := sqrt_mul_le_split (cnormSq (velOf (X ι))) (cnormSq (gradOf (X ι))) 1
      (cnormSq_nonneg' _) (cnormSq_nonneg' _) one_pos
    have hg := grad_le (X ι)
    have hv := vel_le (X ι)
    have hX0 := cnormSq_nonneg' (X ι)
    have hsq : Real.sqrt (cnormSq (gradOf (X ι))) * Real.sqrt (cnormSq (velOf (X ι)))
        ≤ (1 / 2) * (c2 + c3) * cnormSq (X ι) := by
      rw [mul_comm]
      refine hs.trans ?_
      simp only [one_mul, div_one]
      nlinarith
    have h1 : Real.sqrt (7 / 2) * g0ι ι ≤ Real.sqrt (7 / 2) * C := mul_le_mul_of_nonneg_left (hC ι).2.1 hsq7
    have h2 : 0 ≤ Real.sqrt (cnormSq (gradOf (X ι))) * Real.sqrt (cnormSq (velOf (X ι))) := by positivity
    have h3 : 0 ≤ Real.sqrt (7 / 2) * g0ι ι := mul_nonneg hsq7 (hg0 ι)
    calc Real.sqrt (7 / 2) * g0ι ι * Real.sqrt (cnormSq (gradOf (X ι))) * Real.sqrt (cnormSq (velOf (X ι)))
        = (Real.sqrt (7 / 2) * g0ι ι) * (Real.sqrt (cnormSq (gradOf (X ι))) * Real.sqrt (cnormSq (velOf (X ι)))) := by
          ring
      _ ≤ (Real.sqrt (7 / 2) * C) * ((1 / 2) * (c2 + c3) * cnormSq (X ι)) := mul_le_mul h1 hsq h2 (by positivity)
      _ = _ := by ring
  have hL2s : Summable L2 := summable_of_cnorm hX L2 _ fun ι => by
    rw [abs_of_nonneg (hL2nn ι)]; exact hL2le ι
  have hL1s : Summable L1 := by
    refine summable_of_cnorm hX L1 (C * c1 + (1 / 2) * Real.sqrt (7 / 2) * C * (ℓ * c2 + c3 / ℓ)) fun ι => ?_
    simp only [hL1]
    have hcu := curl_le (X ι)
    have hg := grad_le (X ι)
    have hv := vel_le (X ι)
    have hX0 := cnormSq_nonneg' (X ι)
    have hcn := cnormSq_nonneg' (curlOfGrad (gradOf (X ι)))
    have hgn := cnormSq_nonneg' (gradOf (X ι))
    have hvn := cnormSq_nonneg' (velOf (X ι))
    have hw := hgw ι
    have hwC := (hC ι).2.2
    have hlC := (hC ι).1
    have t1 : |lamι ι * cnormSq (curlOfGrad (gradOf (X ι)))| ≤ C * c1 * cnormSq (X ι) := by
      rw [abs_mul, abs_of_nonneg hcn]
      calc |lamι ι| * cnormSq (curlOfGrad (gradOf (X ι))) ≤ C * (c1 * cnormSq (X ι)) :=
            mul_le_mul hlC hcu hcn hCnn
        _ = C * c1 * cnormSq (X ι) := by ring
    have t2n : 0 ≤ (1 / 2) * Real.sqrt (7 / 2) * gwι ι * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ) := by
      positivity
    have t2 : (1 / 2) * Real.sqrt (7 / 2) * gwι ι * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ)
        ≤ (1 / 2) * Real.sqrt (7 / 2) * C * (ℓ * c2 + c3 / ℓ) * cnormSq (X ι) := by
      have i1 : ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ ≤ (ℓ * c2 + c3 / ℓ) * cnormSq (X ι) := by
        have := mul_le_mul_of_nonneg_left hg hℓ.le
        have := div_le_div_of_nonneg_right hv hℓ.le
        have e : (ℓ * c2 + c3 / ℓ) * cnormSq (X ι) = ℓ * (c2 * cnormSq (X ι)) + c3 * cnormSq (X ι) / ℓ := by ring
        rw [e]; linarith
      have i2 : (1 / 2) * Real.sqrt (7 / 2) * gwι ι ≤ (1 / 2) * Real.sqrt (7 / 2) * C :=
        mul_le_mul_of_nonneg_left hwC (by positivity)
      calc (1 / 2) * Real.sqrt (7 / 2) * gwι ι * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ)
          ≤ (1 / 2) * Real.sqrt (7 / 2) * C * ((ℓ * c2 + c3 / ℓ) * cnormSq (X ι)) :=
            mul_le_mul i2 i1 (by positivity) (by positivity)
        _ = _ := by ring
    calc |lamι ι * cnormSq (curlOfGrad (gradOf (X ι)))
          + (1 / 2) * Real.sqrt (7 / 2) * gwι ι * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ)|
        ≤ |lamι ι * cnormSq (curlOfGrad (gradOf (X ι)))|
          + |(1 / 2) * Real.sqrt (7 / 2) * gwι ι * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ)| :=
          abs_add_le _ _
      _ ≤ C * c1 * cnormSq (X ι) + (1 / 2) * Real.sqrt (7 / 2) * C * (ℓ * c2 + c3 / ℓ) * cnormSq (X ι) := by
          rw [abs_of_nonneg t2n]; linarith
      _ = _ := by ring
  have hLsplit : ∀ ι, pointLoss (lamι ι) (g0ι ι) (gwι ι) ℓ (X ι) = L1 ι + L2 ι := by
    intro ι; simp only [pointLoss, hL1, hL2]; ring
  rw [tsum_congr hLsplit, hL1s.tsum_add hL2s]
  have hNs : Summable fun ι => (sesq12 N (X ι) (X ι)).re := by
    have := summable_shift_sesq hX N 0
    simpa using this
  have hNL : ∑' ι, (sesq12 N (X ι) (X ι)).re ≤ ∑' ι, L1 ι := by
    refine hNs.tsum_le_tsum (fun ι => ?_) hL1s
    rw [hN, re_sesq12_lossMatrix]
    simp only [hL1]
    have hcn := cnormSq_nonneg' (curlOfGrad (gradOf (X ι)))
    have hgn := cnormSq_nonneg' (gradOf (X ι))
    have hvn := cnormSq_nonneg' (velOf (X ι))
    have a1 := mul_le_mul_of_nonneg_right (hlamle ι) hcn
    have a2 : (1 / 2) * Real.sqrt (7 / 2) * KS ≤ (1 / 2) * Real.sqrt (7 / 2) * gwι ι :=
      mul_le_mul_of_nonneg_left (hKle ι) (by positivity)
    have a3 : 0 ≤ ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ := by positivity
    have a4 := mul_le_mul_of_nonneg_right a2 a3
    have e : (1 / 2) * Real.sqrt (7 / 2) * KS * ℓ * cnormSq (gradOf (X ι))
        + (1 / 2) * Real.sqrt (7 / 2) * KS / ℓ * cnormSq (velOf (X ι))
        = (1 / 2) * Real.sqrt (7 / 2) * KS * (ℓ * cnormSq (gradOf (X ι)) + cnormSq (velOf (X ι)) / ℓ) := by
      field_simp
    linarith
  have hBL : -(∑' ι, L2 ι) ≤ ∑' ι, Bm ι := by
    rw [← tsum_neg]
    refine hL2s.neg.tsum_le_tsum (fun ι => ?_) hBs
    rw [hBm]
    simp only
    split_ifs with h0H
    · have h0S : (0 : ℤ × ℤ) ∈ S := by
        have := (hH 0).mp h0H
        rwa [(labelHarmonic_zero_iff m hm 0).mpr rfl] at this
      have hh : modeSecondDeriv 0 HW 0 y0 = fun ijl => ((meanSecondDeriv S HW y0 ijl.1 ijl.2.1 ijl.2.2 : ℝ) : ℂ) := by
        funext ijl
        simp only [meanSecondDeriv, h0S, if_true]
        exact modeSecondDeriv_zero_real HW y0 ijl.1 ijl.2.1 ijl.2.2
      have htr := curlGradReal_trace (meanSecondDeriv S HW y0) fun b k a => by
        simp only [meanSecondDeriv]; rw [modeSecondDeriv_symm 0 HW hsym]
      have hK : ∀ x : Fin 3 → ℝ, ∑ j : Fin 3, matVec (curlGradReal (meanSecondDeriv S HW y0)) x j ^ 2
          ≤ g0ι ι ^ 2 * ∑ m : Fin 3, x m ^ 2 := by
        intro x
        have hop := hmean ι (fun b => ((x b : ℝ) : ℂ))
        simp only [hreal] at hop
        have e1 : ∀ a, ‖∑ b : Fin 3, ((x0 a b : ℝ) : ℂ) * ((x b : ℝ) : ℂ)‖ ^ 2
            = matVec (curlGradReal (meanSecondDeriv S HW y0)) x a ^ 2 := by
          intro a
          have : ∑ b : Fin 3, ((x0 a b : ℝ) : ℂ) * ((x b : ℝ) : ℂ) = ((matVec x0 x a : ℝ) : ℂ) := by
            unfold matVec; push_cast; rfl
          rw [this, Complex.norm_real, Real.norm_eq_abs, sq_abs]
          congr 2
          funext a' c'
          exact hx0 a' c'
        have e2 : ∀ b, ‖((x b : ℝ) : ℂ)‖ ^ 2 = x b ^ 2 := fun b => by
          rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
        simp only [e1, e2] at hop
        exact hop
      have hml := mean_lower (modeSecondDeriv 0 HW 0 y0) (meanSecondDeriv S HW y0) hh (g0ι ι) htr (hg0 ι) hK (X ι)
      simp only [hL2]
      linarith [mul_comm (Real.sqrt (cnormSq (velOf (X ι)))) (Real.sqrt (cnormSq (gradOf (X ι))))]
    · have := hL2nn ι
      linarith
  linarith [T, hNL, hBL]

end Sharp

end Internal

end Assembly

end CertCell

end Breakdown
