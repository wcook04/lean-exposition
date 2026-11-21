import Breakdown.FracCell.SharpSupremumRegular

open MeasureTheory

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpWaveSumBound.Internal

open SteadyCert Assembly SharpParts SharpSupremumParts ComplexConjugate

def coefAt (m : ℕ) (φ : ℝ → ℂ) (β : ℤ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * φ θ

def Good (F : ℤ → ℤ → ℂ) (K : ℝ) : Prop :=
  (∀ n, Summable (F n)) ∧ Summable (fun n => ∑' n', F n n') ∧ ‖∑' n, ∑' n', F n n'‖ ≤ K

theorem good_mono {F : ℤ → ℤ → ℂ} {K L : ℝ} (h : Good F K) (hKL : K ≤ L) : Good F L :=
  ⟨h.1, h.2.1, h.2.2.trans hKL⟩

theorem good_congr {F G : ℤ → ℤ → ℂ} {K : ℝ} (h : Good F K) (e : ∀ n n', F n n' = G n n') : Good G K := by
  have : F = G := funext fun n => funext fun n' => e n n'
  exact this ▸ h

theorem good_add {F G : ℤ → ℤ → ℂ} {K L : ℝ} (hF : Good F K) (hG : Good G L) :
    Good (fun n n' => F n n' + G n n') (K + L) := by
  have e : ∀ n, ∑' n', (F n n' + G n n') = ∑' n', F n n' + ∑' n', G n n' :=
    fun n => (hF.1 n).tsum_add (hG.1 n)
  refine ⟨fun n => (hF.1 n).add (hG.1 n), ?_, ?_⟩
  · simp_rw [e]; exact hF.2.1.add hG.2.1
  · simp_rw [e]; rw [hF.2.1.tsum_add hG.2.1]
    exact (norm_add_le _ _).trans (add_le_add hF.2.2 hG.2.2)

theorem good_mul {F : ℤ → ℤ → ℂ} {K r : ℝ} (w : ℂ) (hF : Good F K) (hw : ‖w‖ ≤ r) :
    Good (fun n n' => w * F n n') (r * K) := by
  have e : ∀ n, ∑' n', w * F n n' = w * ∑' n', F n n' := fun n => tsum_mul_left
  have hK : 0 ≤ K := (norm_nonneg _).trans hF.2.2
  refine ⟨fun n => (hF.1 n).mul_left w, ?_, ?_⟩
  · simp_rw [e]; exact hF.2.1.mul_left w
  · simp_rw [e]; rw [tsum_mul_left, norm_mul]
    exact mul_le_mul hw hF.2.2 (norm_nonneg _) ((norm_nonneg _).trans hw)

theorem good_sum3 {F : Fin 3 → ℤ → ℤ → ℂ} {K : ℝ} (h : ∀ i, Good (F i) K) :
    Good (fun n n' => ∑ i : Fin 3, F i n n') (3 * K) := by
  have := good_add (good_add (h 0) (h 1)) (h 2)
  refine good_congr (good_mono this (by ring_nf; rfl)) ?_
  intro n n'; simp [Fin.sum_univ_three]

theorem coef_norm_le {m : ℕ} {φ : ℝ → ℂ} {M : ℝ} (hφ : ∀ θ, ‖φ θ‖ ≤ M) (β : ℤ) : ‖coefAt m φ β‖ ≤ M := by
  unfold coefAt
  have hpi := Real.pi_pos
  have h1 : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * φ θ‖ ≤
      M * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    have he : ‖Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I)‖ = 1 := by rw [Complex.norm_exp]; simp
    rw [norm_mul, he, one_mul]; exact hφ θ
  rw [norm_mul]
  have h2 : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpi]
  rw [h2]
  calc 1 / (2 * Real.pi) * _ ≤ 1 / (2 * Real.pi) * (M * |2 * Real.pi - 0|) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = M := by rw [sub_zero, abs_of_pos (by positivity)]; field_simp

theorem coef_conj_neg (m : ℕ) (φ : ℝ → ℝ) (β : ℤ) :
    conj (coefAt m (fun θ => (φ θ : ℂ)) (-β)) = coefAt m (fun θ => (φ θ : ℂ)) β := by
  unfold coefAt
  rw [map_mul, intervalIntegral.integral_of_le (by positivity), intervalIntegral.integral_of_le (by positivity),
    ← integral_conj]
  congr 1
  · simp [map_ofNat]
  · congr 1; funext θ
    rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    congr 2
    simp only [azimuth, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I]
    push_cast; ring


theorem permSign_abs (i j l : Fin 3) : |CellCert.permSign i j l| ≤ 1 := by
  unfold CellCert.permSign; split_ifs <;> norm_num

theorem permSign_norm (i j l : Fin 3) (t : ℂ) (ht : ‖t‖ ≤ 1) : ‖t * (CellCert.permSign i j l : ℂ)‖ ≤ 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_one₀ ht (abs_nonneg _) (permSign_abs i j l)

theorem wave_split (Sβ Gβ Gmβ : Fin 3 → Fin 3 → ℂ) (hG : ∀ j b, conj (Gmβ j b) = Gβ j b)
    (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    waveForm Sβ Gβ Gmβ s v s' v' =
      (∑ a : Fin 3, ∑ b : Fin 3, (-1 : ℂ) * (conj (curlComp s a) * Sβ a b * curlComp s' b))
      + (∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
          (-(1 / 2) * (CellCert.permSign i l j : ℂ)) * (conj (s i l) * Gβ j b * v' b))
      + (∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3,
          ((1 / 4) * (CellCert.permSign i q j : ℂ)) * (conj (s i l) * Gβ l q * v' j))
      + (∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
          (-(1 / 2) * (CellCert.permSign i l j : ℂ)) * (conj (v b) * Gβ j b * s' i l))
      + (∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3,
          ((1 / 4) * (CellCert.permSign i q j : ℂ)) * (conj (v j) * Gβ l q * s' i l)) := by
  unfold waveForm entryPairing couplingMap bracketMat
  simp only [map_sum, map_mul, map_neg, map_add, Complex.conj_ofReal, hG, map_one, map_div₀, map_ofNat]
  simp only [Fin.sum_univ_three]
  ring

theorem entry_sq_le (s : Fin 3 → Fin 3 → ℂ) (i l : Fin 3) : ‖s i l‖ ^ 2 ≤ sumSq s := by
  unfold sumSq
  have h1 : ‖s i l‖ ^ 2 ≤ ∑ b : Fin 3, ‖s i b‖ ^ 2 :=
    Finset.single_le_sum (f := fun b => ‖s i b‖ ^ 2) (fun b _ => sq_nonneg _) (Finset.mem_univ l)
  exact h1.trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, ‖s a b‖ ^ 2)
    (fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _) (Finset.mem_univ i))

theorem vec_sq_le (v : Fin 3 → ℂ) (b : Fin 3) : ‖v b‖ ^ 2 ≤ vecSq v :=
  Finset.single_le_sum (f := fun a => ‖v a‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ b)

theorem sumSq_nonneg' (s : Fin 3 → Fin 3 → ℂ) : 0 ≤ sumSq s :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem vecSq_nonneg' (v : Fin 3 → ℂ) : 0 ≤ vecSq v := Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem curl_sq_le (s : Fin 3 → Fin 3 → ℂ) (a : Fin 3) : ‖curlComp s a‖ ^ 2 ≤ 81 * sumSq s := by
  have hq := sumSq_nonneg' s
  have he : ∀ j l, ‖(CellCert.permSign a j l : ℂ) * s l j‖ ≤ Real.sqrt (sumSq s) := by
    intro j l
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |CellCert.permSign a j l| * ‖s l j‖ ≤ 1 * ‖s l j‖ :=
          mul_le_mul_of_nonneg_right (permSign_abs a j l) (norm_nonneg _)
      _ ≤ Real.sqrt (sumSq s) := by
          rw [one_mul]; exact Real.le_sqrt_of_sq_le (entry_sq_le s l j)
  have h1 : ‖curlComp s a‖ ≤ 9 * Real.sqrt (sumSq s) := by
    unfold curlComp
    refine (norm_sum_le _ _).trans ?_
    calc ∑ j : Fin 3, ‖∑ l : Fin 3, (CellCert.permSign a j l : ℂ) * s l j‖
        ≤ ∑ j : Fin 3, ∑ l : Fin 3, Real.sqrt (sumSq s) :=
          Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => he j l)
      _ = 9 * Real.sqrt (sumSq s) := by simp; ring
  calc ‖curlComp s a‖ ^ 2 ≤ (9 * Real.sqrt (sumSq s)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = 81 * sumSq s := by rw [mul_pow, Real.sq_sqrt hq]; norm_num


theorem unit_le (θ : ℝ) (b : Fin 3) : ‖(![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b‖ ≤ 1 := by
  fin_cases b <;> simp [radialUnit, angularUnit, axialUnit, EuclideanSpace.norm_eq, Fin.sum_univ_three]

theorem frame_bound (θ : ℝ) (L : Space →L[ℝ] Space) (a b : Fin 3) : |frameMat θ L a b| ≤ ‖L‖ := by
  unfold frameMat
  refine (abs_real_inner_le_norm _ _).trans ?_
  have h1 := L.le_opNorm ((![radialUnit θ, angularUnit θ, axialUnit] : Fin 3 → Space) b)
  have h2 := unit_le θ a
  have h3 := unit_le θ b
  have h4 : ‖L (![radialUnit θ, angularUnit θ, axialUnit] b)‖ ≤ ‖L‖ :=
    h1.trans (by simpa using mul_le_mul_of_nonneg_left h3 (norm_nonneg L))
  calc _ ≤ ‖L‖ * 1 := mul_le_mul h4 h2 (norm_nonneg _) (norm_nonneg _)
    _ = ‖L‖ := mul_one _

theorem symPart_norm (G : Space →L[ℝ] Space) : ‖symPart G‖ ≤ ‖G‖ := by
  unfold symPart
  rw [norm_smul]
  have : ‖G + ContinuousLinearMap.adjoint G‖ ≤ ‖G‖ + ‖G‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [LinearIsometryEquiv.norm_map]
  rw [Real.norm_eq_abs, abs_of_pos (by norm_num : (0:ℝ) < 1 / 2)]
  linarith

theorem unitVector_norm (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem curlGrad_norm (H : Space →L[ℝ] Space →L[ℝ] Space) : ‖curlGradMatrix H‖ ≤ 81 * ‖H‖ := by
  unfold curlGradMatrix
  have hcoef : ∀ j l : Fin 3, ‖∑ b : Fin 3, ∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q‖ ≤ 9 * ‖H‖ := by
    intro j l
    refine (norm_sum_le _ _).trans ?_
    have : ∀ b q : Fin 3, ‖permSign j b q * H (unitVector l) (unitVector b) q‖ ≤ ‖H‖ := by
      intro b q
      rw [norm_mul, Real.norm_eq_abs]
      have e1 : ‖H (unitVector l) (unitVector b) q‖ ≤ ‖H (unitVector l) (unitVector b)‖ := PiLp.norm_apply_le _ _
      have e2 : ‖H (unitVector l) (unitVector b)‖ ≤ ‖H‖ := by
        have := H.le_opNorm₂ (unitVector l) (unitVector b)
        simpa [unitVector_norm] using this
      calc _ ≤ 1 * ‖H‖ := mul_le_mul (permSign_abs j b q) (e1.trans e2) (norm_nonneg _) zero_le_one
        _ = ‖H‖ := one_mul _
    calc ∑ b : Fin 3, ‖∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q‖
        ≤ ∑ b : Fin 3, ∑ q : Fin 3, ‖H‖ :=
          Finset.sum_le_sum fun b _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => this b q)
      _ = 9 * ‖H‖ := by simp; ring
  have hsr : ∀ j l : Fin 3, ‖(innerSL ℝ (unitVector l)).smulRight (unitVector j)‖ ≤ 1 := by
    intro j l
    rw [ContinuousLinearMap.norm_smulRight_apply, innerSL_apply_norm, unitVector_norm, unitVector_norm, mul_one]
  refine (norm_sum_le _ _).trans ?_
  calc ∑ j : Fin 3, ‖∑ l : Fin 3, (∑ b : Fin 3, ∑ q : Fin 3, permSign j b q * H (unitVector l) (unitVector b) q) •
        (innerSL ℝ (unitVector l)).smulRight (unitVector j)‖
      ≤ ∑ j : Fin 3, ∑ l : Fin 3, 9 * ‖H‖ := by
        refine Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
        rw [norm_smul]
        calc _ ≤ 9 * ‖H‖ * 1 := mul_le_mul (hcoef j l) (hsr j l) (norm_nonneg _) (by positivity)
          _ = 9 * ‖H‖ := mul_one _
    _ = 81 * ‖H‖ := by simp; ring

theorem decay_le {C t : ℝ} {y : Space} (h : t ≤ C * (1 + ‖y‖) ^ (-(2:ℝ)) ∨ t ≤ C * (1 + ‖y‖) ^ (-(3:ℝ))) :
    t ≤ max C 0 := by
  have hy : 1 ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
  have h2 : (1 + ‖y‖) ^ (-(2:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  have h3 : (1 + ‖y‖) ^ (-(3:ℝ)) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hy (by norm_num)
  have p2 : 0 ≤ (1 + ‖y‖) ^ (-(2:ℝ)) := Real.rpow_nonneg (by linarith) _
  have p3 : 0 ≤ (1 + ‖y‖) ^ (-(3:ℝ)) := Real.rpow_nonneg (by linarith) _
  have hm : C ≤ max C 0 := le_max_left _ _
  have hm0 : 0 ≤ max C 0 := le_max_right _ _
  rcases h with h | h
  · exact h.trans ((mul_le_mul_of_nonneg_right hm p2).trans (by nlinarith))
  · exact h.trans ((mul_le_mul_of_nonneg_right hm p3).trans (by nlinarith))

theorem symbol_bound {α : ℝ} {k N : ℕ} (c : FracCellData k N) (hc : IsFormData α c) :
    ∃ M : ℝ, ∀ y, ‖c.modelStrain y‖ ≤ M ∧ ‖c.modelCurlGrad y‖ ≤ M := by
  obtain ⟨C1, h1⟩ := hc.model_bounded
  obtain ⟨C2, h2⟩ := hc.centre_bounds
  refine ⟨max C1 (81 * max C2 0), fun y => ?_⟩
  by_cases hy : y ∈ c.cellRegion
  · exact ⟨(h1 y hy).2.2.1.trans (le_max_left _ _), (h1 y hy).2.2.2.trans (le_max_left _ _)⟩
  · obtain ⟨e1, e2⟩ := hc.model_outside y hy
    have g1 : ‖c.centreGrad y‖ ≤ max C2 0 := decay_le (Or.inl (h2 y).2.1)
    have g2 : ‖c.centreSecond y‖ ≤ max C2 0 := decay_le (Or.inr (h2 y).2.2)
    have hm0 : 0 ≤ max C2 0 := le_max_right _ _
    refine ⟨?_, ?_⟩
    · rw [e1]
      exact (symPart_norm _).trans (g1.trans (by
        refine le_trans ?_ (le_max_right _ _); nlinarith))
    · rw [e2]
      exact (curlGrad_norm _).trans ((by nlinarith : 81 * ‖c.centreSecond y‖ ≤ 81 * max C2 0).trans (le_max_right _ _))

theorem order_zero_vanish {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)
    (p : ℝ × ℝ) (h0 : c.order = 0) (hs : Summable (fun n : ℤ => sumSq (sharpGrad c K S x n p)))
    (hv : Summable (fun n : ℤ => vecSq (sharpVel c K S x n p))) :
    ∀ n ∉ S.resolved, sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p) = 0 := by
  have hconst : ∀ n ∉ S.resolved, sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p) =
      sumSq (fun a b => gradMode c.order 0 x.2.1 a b p) + vecSq (fun a => modeVec c.order 0 x.1 p.1 p.2 a) := by
    intro n hn
    have eG : sharpGrad c K S x n p = fun a b => gradMode c.order 0 x.2.1 a b p := by
      funext a b
      simp only [sharpGrad, lowGrad, if_neg hn, Pi.zero_apply, sub_zero, gradMode, modeMat, azimuth, h0]
      simp
    have eV : sharpVel c K S x n p = fun a => modeVec c.order 0 x.1 p.1 p.2 a := by
      funext a
      simp only [sharpVel, lowVel, if_neg hn, Pi.zero_apply, sub_zero, modeVec, azimuth, h0]
      simp
    rw [eG, eV]
  have hsum := (hs.add hv).subtype ((S.resolved : Set ℤ)ᶜ)
  have hinf : Infinite ((S.resolved : Set ℤ)ᶜ : Set ℤ) := (S.resolved.finite_toSet.infinite_compl).to_subtype
  have hc' : Summable (fun _ : ((S.resolved : Set ℤ)ᶜ : Set ℤ) =>
      sumSq (fun a b => gradMode c.order 0 x.2.1 a b p) + vecSq (fun a => modeVec c.order 0 x.1 p.1 p.2 a)) := by
    refine hsum.congr fun n => ?_
    exact hconst n.1 n.2
  have hz := tendsto_const_nhds_iff.mp hc'.tendsto_cofinite_zero
  intro n hn
  rw [hconst n hn]
  exact hz

theorem good_base_fin {m : ℕ} {φ : ℝ → ℂ} {M : ℝ} (hφ : ∀ θ, ‖φ θ‖ ≤ M) {Q : ℤ → ℝ}
    (hQ0 : ∀ n, 0 ≤ Q n) (hQ : Summable Q) (R : Finset ℤ) (hR : ∀ n ∉ R, Q n = 0) {A B : ℤ → ℂ}
    (hA : ∀ n, ‖A n‖ ^ 2 ≤ Q n) (hB : ∀ n, ‖B n‖ ^ 2 ≤ Q n) :
    Good (fun n n' => conj (A n) * coefAt m φ (n - n') * B n') (M * R.card * ∑' n, Q n) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  have z : ∀ {X : ℤ → ℂ}, (∀ n, ‖X n‖ ^ 2 ≤ Q n) → ∀ n ∉ R, X n = 0 := by
    intro X hX n hn
    have h := hX n
    rw [hR n hn] at h
    have : ‖X n‖ = 0 := by nlinarith [norm_nonneg (X n)]
    exact norm_eq_zero.mp this
  have hin : ∀ n, ∀ n' ∉ R, conj (A n) * coefAt m φ (n - n') * B n' = 0 := by
    intro n n' hn'; rw [z hB n' hn', mul_zero]
  have hin' : ∀ n, ∑' n', conj (A n) * coefAt m φ (n - n') * B n' =
      ∑ n' ∈ R, conj (A n) * coefAt m φ (n - n') * B n' := fun n => tsum_eq_sum (hin n)
  have hout : ∀ n ∉ R, ∑' n', conj (A n) * coefAt m φ (n - n') * B n' = 0 := by
    intro n hn; rw [hin' n, z hA n hn]; simp
  refine ⟨fun n => summable_of_ne_finset_zero (hin n), summable_of_ne_finset_zero hout, ?_⟩
  rw [tsum_eq_sum hout]
  simp_rw [hin']
  have hterm : ∀ n n', ‖conj (A n) * coefAt m φ (n - n') * B n'‖ ≤ M * ((Q n + Q n') / 2) := by
    intro n n'
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have hc := coef_norm_le (m := m) hφ (n - n')
    have h1 : ‖A n‖ * ‖B n'‖ ≤ (Q n + Q n') / 2 := by
      nlinarith [hA n, hB n', sq_nonneg (‖A n‖ - ‖B n'‖)]
    calc ‖A n‖ * ‖coefAt m φ (n - n')‖ * ‖B n'‖ = ‖coefAt m φ (n - n')‖ * (‖A n‖ * ‖B n'‖) := by ring
      _ ≤ M * ((Q n + Q n') / 2) :=
        mul_le_mul hc h1 (by positivity) hM
  have hsum : ∑ n ∈ R, ∑ n' ∈ R, M * ((Q n + Q n') / 2) = M * R.card * ∑ n ∈ R, Q n := by
    simp only [mul_add, add_div, Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum,
      ← Finset.sum_div]
    ring
  calc ‖∑ n ∈ R, ∑ n' ∈ R, conj (A n) * coefAt m φ (n - n') * B n'‖
      ≤ ∑ n ∈ R, ∑ n' ∈ R, M * ((Q n + Q n') / 2) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => (norm_sum_le _ _).trans
          (Finset.sum_le_sum fun n' _ => hterm n n'))
    _ = M * R.card * ∑ n ∈ R, Q n := hsum
    _ ≤ M * R.card * ∑' n, Q n := by
        gcongr
        exact hQ.sum_le_tsum R (fun n _ => hQ0 n)

theorem exp_split (m : ℕ) (n n' : ℤ) (θ : ℝ) :
    Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) =
      conj (Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)) * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, azimuth]
  push_cast; ring

theorem int_exp (m : ℕ) (hm : 0 < m) (β : ℤ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) =
      if β = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  split_ifs with hβ
  · subst hβ; simp [azimuth]
  · have ha : azimuth m β ≠ 0 := by
      unfold azimuth; exact mul_ne_zero (Int.cast_ne_zero.mpr hβ) (Nat.cast_ne_zero.mpr hm.ne')
    have hc : (-(azimuth m β : ℂ) * Complex.I) ≠ 0 := by simp [ha, Complex.I_ne_zero]
    have e : ∀ θ : ℝ, Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) =
        Complex.exp ((-(azimuth m β : ℂ) * Complex.I) * θ) := by
      intro θ; congr 1; push_cast; ring
    simp_rw [e]
    have h1 : Complex.exp ((-(azimuth m β : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      have : (-(azimuth m β : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
          ((-(β * m) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        simp only [azimuth]; push_cast; ring
      rw [this, Complex.exp_int_mul_two_pi_mul_I]
    rw [integral_exp_mul_complex hc, h1]
    simp

theorem coef_one (m : ℕ) (hm : 0 < m) (β : ℤ) : coefAt m (fun _ => 1) β = if β = 0 then 1 else 0 := by
  unfold coefAt
  simp_rw [mul_one]
  rw [int_exp m hm β]
  have hpi := Real.pi_pos
  split_ifs
  · push_cast; field_simp
  · simp

def wavePoly (m : ℕ) (T : Finset ℤ) (a : ℤ → ℂ) (θ : ℝ) : ℂ :=
  ∑ n ∈ T, a n * Complex.exp ((azimuth m n * θ : ℝ) * Complex.I)

theorem wavePoly_cont (m : ℕ) (T : Finset ℤ) (a : ℤ → ℂ) : Continuous (wavePoly m T a) := by
  unfold wavePoly; fun_prop

theorem fin_identity (m : ℕ) {φ : ℝ → ℂ} (hφ : IntervalIntegrable φ volume 0 (2 * Real.pi)) (T : Finset ℤ)
    (a b : ℤ → ℂ) :
    ∑ n ∈ T, ∑ n' ∈ T, conj (a n) * coefAt m φ (n - n') * b n' =
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in (0 : ℝ)..(2 * Real.pi),
        conj (wavePoly m T a θ) * wavePoly m T b θ * φ θ := by
  have hint : ∀ n n' : ℤ, IntervalIntegrable (fun θ => conj (a n) * b n' *
      (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * φ θ)) volume 0 (2 * Real.pi) := by
    intro n n'
    have hc : Continuous (fun θ : ℝ => Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I)) := by fun_prop
    exact (hφ.continuousOn_mul hc.continuousOn).const_mul _
  have e : ∀ θ, conj (wavePoly m T a θ) * wavePoly m T b θ * φ θ = ∑ n ∈ T, ∑ n' ∈ T,
      conj (a n) * b n' * (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * φ θ) := by
    intro θ
    simp only [wavePoly, map_sum, map_mul]
    rw [Finset.sum_mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n' _ => ?_
    rw [exp_split]; ring
  simp_rw [e]
  have hsumi : ∀ n : ℤ, IntervalIntegrable (fun θ => ∑ n' ∈ T, conj (a n) * b n' *
      (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * φ θ)) volume 0 (2 * Real.pi) := by
    intro n
    have := IntervalIntegrable.sum T (fun n' _ => hint n n')
    rw [Finset.sum_fn] at this
    exact this
  rw [intervalIntegral.integral_finsetSum (fun n _ => hsumi n)]
  have hin : ∀ n : ℤ, ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ n' ∈ T, conj (a n) * b n' *
      (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * φ θ) = ∑ n' ∈ T, ∫ θ in (0 : ℝ)..(2 * Real.pi),
      conj (a n) * b n' * (Complex.exp (-(azimuth m (n - n') * θ : ℝ) * Complex.I) * φ θ) :=
    fun n => intervalIntegral.integral_finsetSum (fun n' _ => hint n n')
  simp_rw [hin, intervalIntegral.integral_const_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n' _ => ?_
  unfold coefAt; ring

theorem amgm {x y t : ℝ} (ht : 0 < t) : x * y ≤ (t * x ^ 2 + y ^ 2 / t) / 2 := by
  have h : 0 ≤ (t * x - y) ^ 2 / t := by positivity
  have e : (t * x - y) ^ 2 / t = t * x ^ 2 + y ^ 2 / t - 2 * (x * y) := by field_simp; ring
  linarith

theorem poly_sq (m : ℕ) (hm : 0 < m) (T : Finset ℤ) (a : ℤ → ℂ) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), ‖wavePoly m T a θ‖ ^ 2 = 2 * Real.pi * ∑ n ∈ T, ‖a n‖ ^ 2 := by
  have h := fin_identity m (φ := fun _ => 1) intervalIntegrable_const T a a
  have hl : ∑ n ∈ T, ∑ n' ∈ T, conj (a n) * coefAt m (fun _ => 1) (n - n') * a n' =
      ((∑ n ∈ T, ‖a n‖ ^ 2 : ℝ) : ℂ) := by
    push_cast
    refine Finset.sum_congr rfl fun n hn => ?_
    simp_rw [coef_one m hm, sub_eq_zero]
    simp only [mul_ite, ite_mul, mul_one, mul_zero, zero_mul]
    rw [Finset.sum_ite_eq T n (fun n' => conj (a n) * a n'), if_pos hn, Complex.conj_mul']
  have hr : (∫ θ in (0 : ℝ)..(2 * Real.pi), conj (wavePoly m T a θ) * wavePoly m T a θ * (fun _ => (1 : ℂ)) θ) =
      ((∫ θ in (0 : ℝ)..(2 * Real.pi), ‖wavePoly m T a θ‖ ^ 2 : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    congr 1; funext θ
    rw [mul_one, Complex.conj_mul']; push_cast; ring
  rw [hl, hr] at h
  have hpi := Real.pi_pos
  have h2 := congrArg (fun z => (2 * (Real.pi : ℂ)) * z) h
  have hne : (2 * (Real.pi : ℂ)) ≠ 0 := by
    have : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hpi.ne'
    exact mul_ne_zero two_ne_zero this
  rw [← mul_assoc, mul_one_div_cancel hne, one_mul] at h2
  exact_mod_cast h2.symm

theorem fin_bound (m : ℕ) (hm : 0 < m) {φ : ℝ → ℂ} {M : ℝ} (hφ : ∀ θ, ‖φ θ‖ ≤ M)
    (hφi : IntervalIntegrable φ volume 0 (2 * Real.pi)) (T : Finset ℤ) (a b : ℤ → ℂ) {t : ℝ} (ht : 0 < t) :
    ‖∑ n ∈ T, ∑ n' ∈ T, conj (a n) * coefAt m φ (n - n') * b n'‖ ≤
      M / 2 * (t * ∑ n ∈ T, ‖a n‖ ^ 2 + 1 / t * ∑ n ∈ T, ‖b n‖ ^ 2) := by
  have hpi := Real.pi_pos
  have hM : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  rw [fin_identity m hφi T a b]
  set P := wavePoly m T a
  set R := wavePoly m T b
  have hP := wavePoly_cont m T a
  have hR := wavePoly_cont m T b
  have hfi : IntervalIntegrable (fun θ => conj (P θ) * R θ * φ θ) volume 0 (2 * Real.pi) :=
    hφi.continuousOn_mul (by fun_prop : Continuous fun θ => conj (P θ) * R θ).continuousOn
  have hg : Continuous (fun θ => M / 2 * (t * ‖P θ‖ ^ 2 + 1 / t * ‖R θ‖ ^ 2)) := by fun_prop
  have hpt : ∀ θ, ‖conj (P θ) * R θ * φ θ‖ ≤ M / 2 * (t * ‖P θ‖ ^ 2 + 1 / t * ‖R θ‖ ^ 2) := by
    intro θ
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h1 := amgm (x := ‖P θ‖) (y := ‖R θ‖) ht
    have h2 := hφ θ
    have : ‖P θ‖ * ‖R θ‖ * ‖φ θ‖ ≤ ‖P θ‖ * ‖R θ‖ * M :=
      mul_le_mul_of_nonneg_left h2 (by positivity)
    have e : 1 / t * ‖R θ‖ ^ 2 = ‖R θ‖ ^ 2 / t := by ring
    rw [e]; nlinarith
  have hint : ∫ θ in (0 : ℝ)..(2 * Real.pi), M / 2 * (t * ‖P θ‖ ^ 2 + 1 / t * ‖R θ‖ ^ 2) =
      2 * Real.pi * (M / 2 * (t * ∑ n ∈ T, ‖a n‖ ^ 2 + 1 / t * ∑ n ∈ T, ‖b n‖ ^ 2)) := by
    have i1 : IntervalIntegrable (fun θ => t * ‖P θ‖ ^ 2) volume 0 (2 * Real.pi) :=
      (by fun_prop : Continuous fun θ => t * ‖P θ‖ ^ 2).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun θ => 1 / t * ‖R θ‖ ^ 2) volume 0 (2 * Real.pi) :=
      (by fun_prop : Continuous fun θ => 1 / t * ‖R θ‖ ^ 2).intervalIntegrable _ _
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add i1 i2,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, poly_sq m hm T a, poly_sq m hm T b]
    ring
  have hnorm : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [norm_div, norm_one, Complex.norm_mul, Complex.norm_ofNat, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hpi]
  rw [norm_mul, hnorm]
  have hle : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), conj (P θ) * R θ * φ θ‖ ≤
      ∫ θ in (0 : ℝ)..(2 * Real.pi), M / 2 * (t * ‖P θ‖ ^ 2 + 1 / t * ‖R θ‖ ^ 2) := by
    refine (intervalIntegral.norm_integral_le_integral_norm (by positivity)).trans ?_
    exact intervalIntegral.integral_mono_on (by positivity) hfi.norm (hg.intervalIntegrable _ _)
      (fun θ _ => hpt θ)
  rw [hint] at hle
  calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi), conj (P θ) * R θ * φ θ‖
      ≤ 1 / (2 * Real.pi) * (2 * Real.pi * (M / 2 * (t * ∑ n ∈ T, ‖a n‖ ^ 2 + 1 / t * ∑ n ∈ T, ‖b n‖ ^ 2))) :=
        mul_le_mul_of_nonneg_left hle (by positivity)
    _ = _ := by field_simp

theorem ind_sum (T G : Finset ℤ) (hG : G ⊆ T) (f : ℤ → ℝ) :
    ∑ n ∈ T, (if n ∈ G then f n else 0) = ∑ n ∈ G, f n := by
  rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hG]

theorem col_bound (m : ℕ) (hm : 0 < m) {φ : ℝ → ℂ} {M : ℝ} (hφ : ∀ θ, ‖φ θ‖ ≤ M)
    (hφi : IntervalIntegrable φ volume 0 (2 * Real.pi)) (n : ℤ) (G : Finset ℤ) :
    ∑ k ∈ G, ‖coefAt m φ (n - k)‖ ^ 2 ≤ (M + 1) ^ 2 := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  set T := insert n G
  set X := ∑ k ∈ T, ‖coefAt m φ (n - k)‖ ^ 2 with hXdef
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hGX : ∑ k ∈ G, ‖coefAt m φ (n - k)‖ ^ 2 ≤ X :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_insert _ _) (fun _ _ _ => sq_nonneg _)
  have ht : 0 < M + 1 := by linarith
  have h := fin_bound m hm hφ hφi T (fun k => if k = n then 1 else 0) (fun k => conj (coefAt m φ (n - k))) ht
  have hl : ∑ k ∈ T, ∑ k' ∈ T, conj (if k = n then (1 : ℂ) else 0) * coefAt m φ (k - k') *
      conj (coefAt m φ (n - k')) = ((X : ℝ) : ℂ) := by
    have e : ∀ k k', conj (if k = n then (1 : ℂ) else 0) * coefAt m φ (k - k') * conj (coefAt m φ (n - k')) =
        if k = n then coefAt m φ (n - k') * conj (coefAt m φ (n - k')) else 0 := by
      intro k k'; split_ifs with hk <;> simp [hk]
    simp_rw [e]
    rw [Finset.sum_comm]
    simp only [Finset.sum_ite_eq', Finset.mem_insert_self, if_true, T]
    rw [hXdef]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Complex.mul_conj']
  rw [hl, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hX0] at h
  have ha : ∑ k ∈ T, ‖(if k = n then (1 : ℂ) else 0)‖ ^ 2 = 1 := by
    have e : ∀ k, ‖(if k = n then (1 : ℂ) else 0)‖ ^ 2 = if k = n then 1 else 0 := by
      intro k; split_ifs <;> simp
    simp_rw [e]; simp [T]
  have hb : ∑ k ∈ T, ‖conj (coefAt m φ (n - k))‖ ^ 2 = X := by simp_rw [Complex.norm_conj]; rfl
  rw [ha, hb] at h
  have h2 : X * (M + 1) ≤ M / 2 * ((M + 1) ^ 2 + X) := by
    have e : M / 2 * ((M + 1) * 1 + 1 / (M + 1) * X) * (M + 1) = M / 2 * ((M + 1) ^ 2 + X) := by
      field_simp
    calc X * (M + 1) ≤ M / 2 * ((M + 1) * 1 + 1 / (M + 1) * X) * (M + 1) := mul_le_mul_of_nonneg_right h ht.le
      _ = _ := e
  have h3 : X ≤ (M + 1) ^ 2 := by nlinarith
  exact hGX.trans h3

theorem finite_pair (m : ℕ) (hm : 0 < m) {φ : ℝ → ℂ} {M : ℝ} (hφ : ∀ θ, ‖φ θ‖ ≤ M)
    (hφi : IntervalIntegrable φ volume 0 (2 * Real.pi)) (a b : ℤ → ℂ) (F0 G : Finset ℤ) {t : ℝ} (ht : 0 < t) :
    ‖∑ n ∈ F0, ∑ n' ∈ G, conj (a n) * coefAt m φ (n - n') * b n'‖ ≤
      M / 2 * (t * ∑ n ∈ F0, ‖a n‖ ^ 2 + 1 / t * ∑ n ∈ G, ‖b n‖ ^ 2) := by
  set T := F0 ∪ G
  have h := fin_bound m hm hφ hφi T (fun n => if n ∈ F0 then a n else 0) (fun n => if n ∈ G then b n else 0) ht
  have hl : ∑ n ∈ T, ∑ n' ∈ T, conj (if n ∈ F0 then a n else 0) * coefAt m φ (n - n') *
      (if n' ∈ G then b n' else 0) = ∑ n ∈ F0, ∑ n' ∈ G, conj (a n) * coefAt m φ (n - n') * b n' := by
    have e : ∀ n n', conj (if n ∈ F0 then a n else 0) * coefAt m φ (n - n') * (if n' ∈ G then b n' else 0) =
        if n ∈ F0 then (if n' ∈ G then conj (a n) * coefAt m φ (n - n') * b n' else 0) else 0 := by
      intro n n'; split_ifs <;> simp
    simp_rw [e]
    have e3 : ∀ x : ℤ, ∑ x_1 ∈ T, (if x ∈ F0 then (if x_1 ∈ G then conj (a x) * coefAt m φ (x - x_1) * b x_1 else 0)
        else 0) = if x ∈ F0 then ∑ x_1 ∈ T, (if x_1 ∈ G then conj (a x) * coefAt m φ (x - x_1) * b x_1 else 0)
        else 0 := by
      intro x; split_ifs <;> simp
    rw [Finset.sum_congr rfl (fun x _ => e3 x), Finset.sum_ite_mem,
      Finset.inter_eq_right.mpr Finset.subset_union_left]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_ite_mem, Finset.inter_eq_right.mpr Finset.subset_union_right]
  have e1 : ∑ n ∈ T, ‖(if n ∈ F0 then a n else 0)‖ ^ 2 = ∑ n ∈ F0, ‖a n‖ ^ 2 := by
    rw [← ind_sum T F0 Finset.subset_union_left]
    refine Finset.sum_congr rfl fun n _ => ?_; split_ifs <;> simp
  have e2 : ∑ n ∈ T, ‖(if n ∈ G then b n else 0)‖ ^ 2 = ∑ n ∈ G, ‖b n‖ ^ 2 := by
    rw [← ind_sum T G Finset.subset_union_right]
    refine Finset.sum_congr rfl fun n _ => ?_; split_ifs <;> simp
  rw [hl, e1, e2] at h
  exact h

theorem good_base_pos {m : ℕ} (hm : 0 < m) {φ : ℝ → ℂ} {M : ℝ} (hφ : ∀ θ, ‖φ θ‖ ≤ M) {Q : ℤ → ℝ}
    (hQ0 : ∀ n, 0 ≤ Q n) (hQ : Summable Q) {A B : ℤ → ℂ} (hA : ∀ n, ‖A n‖ ^ 2 ≤ Q n)
    (hB : ∀ n, ‖B n‖ ^ 2 ≤ Q n) :
    Good (fun n n' => conj (A n) * coefAt m φ (n - n') * B n') (M * ∑' n, Q n) := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hφ 0)
  have hQt0 : 0 ≤ ∑' n, Q n := tsum_nonneg hQ0
  by_cases hφi : IntervalIntegrable φ volume 0 (2 * Real.pi)
  swap
  · have hz : ∀ β, coefAt m φ β = 0 := by
      intro β; unfold coefAt
      rw [intervalIntegral.integral_undef, mul_zero]
      intro hi
      apply hφi
      have hc : Continuous (fun θ : ℝ => Complex.exp ((azimuth m β * θ : ℝ) * Complex.I)) := by fun_prop
      have h2 := hi.continuousOn_mul hc.continuousOn
      have e : (fun θ => Complex.exp ((azimuth m β * θ : ℝ) * Complex.I) *
          (Complex.exp (-(azimuth m β * θ : ℝ) * Complex.I) * φ θ)) = φ := by
        funext θ
        rw [← mul_assoc, ← Complex.exp_add]
        have : ((azimuth m β * θ : ℝ) : ℂ) * Complex.I + -((azimuth m β * θ : ℝ) : ℂ) * Complex.I = 0 := by ring
        rw [this, Complex.exp_zero, one_mul]
      rw [e] at h2
      exact h2
    refine ⟨fun n => by simp [hz], by simp [hz], ?_⟩
    simp only [hz, mul_zero, zero_mul, tsum_zero, norm_zero]
    positivity
  have hAs : Summable (fun n => ‖A n‖ ^ 2) := Summable.of_nonneg_of_le (fun n => sq_nonneg _) hA hQ
  have hBs : Summable (fun n => ‖B n‖ ^ 2) := Summable.of_nonneg_of_le (fun n => sq_nonneg _) hB hQ
  have hcol : ∀ n, Summable (fun k => ‖coefAt m φ (n - k)‖ ^ 2) := fun n =>
    summable_of_sum_le (fun k => sq_nonneg _) (col_bound m hm hφ hφi n)
  have hu_s : ∀ n, Summable (fun n' => coefAt m φ (n - n') * B n') := by
    intro n
    refine Summable.of_norm_bounded (((hcol n).add hBs).mul_left (1 / 2)) (fun n' => ?_)
    rw [norm_mul]
    nlinarith [sq_nonneg (‖coefAt m φ (n - n')‖ - ‖B n'‖)]
  have hinner : ∀ n, Summable (fun n' => conj (A n) * coefAt m φ (n - n') * B n') := by
    intro n
    have := (hu_s n).mul_left (conj (A n))
    refine this.congr fun n' => ?_
    ring
  have key : ∀ (a : ℤ → ℂ) (F0 : Finset ℤ) (t : ℝ), 0 < t →
      ‖∑ n ∈ F0, conj (a n) * ∑' n', coefAt m φ (n - n') * B n'‖ ≤
        M / 2 * (t * ∑ n ∈ F0, ‖a n‖ ^ 2 + 1 / t * ∑' n, Q n) := by
    intro a F0 t ht
    have e : ∑ n ∈ F0, conj (a n) * ∑' n', coefAt m φ (n - n') * B n' =
        ∑' n', ∑ n ∈ F0, conj (a n) * (coefAt m φ (n - n') * B n') := by
      rw [Summable.tsum_finsetSum (fun n _ => (hu_s n).mul_left (conj (a n)))]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [tsum_mul_left]
    have hg : Summable (fun n' => ∑ n ∈ F0, conj (a n) * (coefAt m φ (n - n') * B n')) :=
      summable_sum fun n _ => (hu_s n).mul_left _
    have hlim : Filter.Tendsto (fun G : Finset ℤ => ∑ n' ∈ G, ∑ n ∈ F0, conj (a n) * (coefAt m φ (n - n') * B n'))
        Filter.atTop (nhds (∑' n', ∑ n ∈ F0, conj (a n) * (coefAt m φ (n - n') * B n'))) := hg.hasSum
    rw [e]
    refine le_of_tendsto' hlim.norm (fun G => ?_)
    rw [Finset.sum_comm]
    have h := finite_pair m hm hφ hφi a B F0 G ht
    simp_rw [mul_assoc] at h
    refine h.trans ?_
    have hG : ∑ n ∈ G, ‖B n‖ ^ 2 ≤ ∑' n, Q n :=
      (Finset.sum_le_sum fun n _ => hB n).trans (hQ.sum_le_tsum G fun n _ => hQ0 n)
    gcongr
  set u : ℤ → ℂ := fun n => ∑' n', coefAt m φ (n - n') * B n' with hu
  have hu2 : Summable (fun n => ‖u n‖ ^ 2) := by
    refine summable_of_sum_le (c := M * (M + 1) * ∑' n, Q n) (fun n => sq_nonneg _) (fun F0 => ?_)
    have h := key u F0 (1 / (M + 1)) (by positivity)
    have e : ∑ n ∈ F0, conj (u n) * ∑' n', coefAt m φ (n - n') * B n' = ((∑ n ∈ F0, ‖u n‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun n _ => Complex.conj_mul' _
    have hY0 : 0 ≤ ∑ n ∈ F0, ‖u n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hY0, one_div_one_div] at h
    have hq : M * (1 / (M + 1)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    have h3 : M / 2 * (1 / (M + 1) * ∑ n ∈ F0, ‖u n‖ ^ 2) ≤ (∑ n ∈ F0, ‖u n‖ ^ 2) / 2 := by
      have : M / 2 * (1 / (M + 1) * ∑ n ∈ F0, ‖u n‖ ^ 2) = (M * (1 / (M + 1))) * (∑ n ∈ F0, ‖u n‖ ^ 2) / 2 := by
        ring
      rw [this]
      have := mul_le_mul_of_nonneg_right hq hY0
      linarith
    nlinarith
  have hout_eq : ∀ n, ∑' n', conj (A n) * coefAt m φ (n - n') * B n' = conj (A n) * u n := by
    intro n
    rw [hu, ← tsum_mul_left]
    congr 1; funext n'; ring
  have hout : Summable (fun n => conj (A n) * u n) := by
    refine Summable.of_norm_bounded ((hAs.add hu2).mul_left (1 / 2)) (fun n => ?_)
    rw [norm_mul, Complex.norm_conj]
    nlinarith [sq_nonneg (‖A n‖ - ‖u n‖)]
  refine ⟨hinner, ?_, ?_⟩
  · simp_rw [hout_eq]; exact hout
  · simp_rw [hout_eq]
    have hlim : Filter.Tendsto (fun F0 : Finset ℤ => ∑ n ∈ F0, conj (A n) * u n) Filter.atTop
        (nhds (∑' n, conj (A n) * u n)) := hout.hasSum
    refine le_of_tendsto' hlim.norm (fun F0 => ?_)
    have h := key A F0 1 one_pos
    refine h.trans ?_
    have hA' : ∑ n ∈ F0, ‖A n‖ ^ 2 ≤ ∑' n, Q n :=
      (Finset.sum_le_sum fun n _ => hA n).trans (hQ.sum_le_tsum F0 fun n _ => hQ0 n)
    calc M / 2 * (1 * ∑ n ∈ F0, ‖A n‖ ^ 2 + 1 / 1 * ∑' n, Q n) ≤ M / 2 * (1 * ∑' n, Q n + 1 / 1 * ∑' n, Q n) := by
          gcongr
      _ = M * ∑' n, Q n := by ring

end Breakdown.CellCert.CellAnalysis.SharpWaveSumBound.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts SharpSupremumParts ComplexConjugate SharpWaveSumBound.Internal

theorem waveSumBound_holds : WaveSumBoundStatement := by
  intro α hα1 hα2 k N c hc K S B Cl slots R hR hw x hx
  obtain ⟨M, hM⟩ := symbol_bound c hc
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0).1
  refine ⟨333 * (M * ((S.resolved.card : ℝ) + 1)) * 81, fun p hp hs hv => ?_⟩
  set sG : ℤ → Fin 3 → Fin 3 → ℂ := fun n => sharpGrad c K S x n p with hsG
  set sV : ℤ → Fin 3 → ℂ := fun n => sharpVel c K S x n p with hsV
  set Q : ℤ → ℝ := fun n => 81 * (sumSq (sG n) + vecSq (sV n)) with hQdef
  have hQ0 : ∀ n, 0 ≤ Q n := fun n => by
    have := sumSq_nonneg' (sG n); have := vecSq_nonneg' (sV n); simp only [hQdef]; positivity
  have hQs : Summable Q := (hs.add hv).mul_left 81
  have hQt : ∑' n, Q n = 81 * ∑' n : ℤ, (sumSq (sG n) + vecSq (sV n)) := tsum_mul_left
  have hQt0 : 0 ≤ ∑' n, Q n := tsum_nonneg hQ0
  set K0 : ℝ := M * ((S.resolved.card : ℝ) + 1) * ∑' n, Q n with hK0
  have base : ∀ (φ : ℝ → ℝ) (A B : ℤ → ℂ), (∀ θ, |φ θ| ≤ M) → (∀ n, ‖A n‖ ^ 2 ≤ Q n) →
      (∀ n, ‖B n‖ ^ 2 ≤ Q n) →
      Good (fun n n' => conj (A n) * coefAt c.order (fun θ => (φ θ : ℂ)) (n - n') * B n') K0 := by
    intro φ A B hφ hA hB
    have hφ' : ∀ θ, ‖(φ θ : ℂ)‖ ≤ M := fun θ => by rw [Complex.norm_real, Real.norm_eq_abs]; exact hφ θ
    rcases Nat.eq_zero_or_pos c.order with h0 | hpos
    · refine good_mono (good_base_fin hφ' hQ0 hQs S.resolved ?_ hA hB) ?_
      · intro n hn
        show 81 * (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) = 0
        rw [order_zero_vanish c K S x p h0 hs hv n hn, mul_zero]
      · rw [hK0]; gcongr; linarith
    · refine good_mono (good_base_pos hpos hφ' hQ0 hQs hA hB) ?_
      rw [hK0]
      have : M * 1 ≤ M * ((S.resolved.card : ℝ) + 1) := by gcongr; linarith [(Nat.cast_nonneg S.resolved.card : (0:ℝ) ≤ _)]
      nlinarith
  have hS : ∀ a b θ, |frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b| ≤ M :=
    fun a b θ => (frame_bound θ _ a b).trans (hM _).1
  have hC : ∀ a b θ, |frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) a b| ≤ M :=
    fun a b θ => (frame_bound θ _ a b).trans (hM _).2
  have hcurl : ∀ a n, ‖curlComp (sG n) a‖ ^ 2 ≤ Q n := fun a n =>
    (curl_sq_le (sG n) a).trans (by simp only [hQdef]; have := vecSq_nonneg' (sV n); nlinarith)
  have hent : ∀ i l n, ‖sG n i l‖ ^ 2 ≤ Q n := fun i l n =>
    (entry_sq_le (sG n) i l).trans (by
      simp only [hQdef]; have := vecSq_nonneg' (sV n); have := sumSq_nonneg' (sG n); nlinarith)
  have hvec : ∀ b n, ‖sV n b‖ ^ 2 ≤ Q n := fun b n =>
    (vec_sq_le (sV n) b).trans (by
      simp only [hQdef]; have := vecSq_nonneg' (sV n); have := sumSq_nonneg' (sG n); nlinarith)
  have h12 : ‖(-(1 / 2) : ℂ)‖ ≤ 1 := by norm_num
  have h14 : ‖((1 / 4) : ℂ)‖ ≤ 1 := by norm_num
  have g1 := good_sum3 fun a => good_sum3 fun b =>
    good_mul (-1 : ℂ) (base (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)) a b)
      (fun n => curlComp (sG n) a) (fun n => curlComp (sG n) b) (hS a b) (hcurl a) (hcurl b)) (r := 1) (by simp)
  have g2 := good_sum3 fun i => good_sum3 fun l => good_sum3 fun j => good_sum3 fun b =>
    good_mul (-(1 / 2) * (CellCert.permSign i l j : ℂ))
      (base (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) j b)
      (fun n => sG n i l) (fun n => sV n b) (hC j b) (hent i l) (hvec b)) (permSign_norm i l j _ h12)
  have g3 := good_sum3 fun i => good_sum3 fun l => good_sum3 fun q => good_sum3 fun j =>
    good_mul ((1 / 4) * (CellCert.permSign i q j : ℂ))
      (base (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) l q)
      (fun n => sG n i l) (fun n => sV n j) (hC l q) (hent i l) (hvec j)) (permSign_norm i q j _ h14)
  have g4 := good_sum3 fun i => good_sum3 fun l => good_sum3 fun j => good_sum3 fun b =>
    good_mul (-(1 / 2) * (CellCert.permSign i l j : ℂ))
      (base (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) j b)
      (fun n => sV n b) (fun n => sG n i l) (hC j b) (hvec b) (hent i l)) (permSign_norm i l j _ h12)
  have g5 := good_sum3 fun i => good_sum3 fun l => good_sum3 fun q => good_sum3 fun j =>
    good_mul ((1 / 4) * (CellCert.permSign i q j : ℂ))
      (base (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) l q)
      (fun n => sV n j) (fun n => sG n i l) (hC l q) (hvec j) (hent i l)) (permSign_norm i q j _ h14)
  have gall := good_add (good_add (good_add (good_add g1 g2) g3) g4) g5
  have hG : ∀ n n' : ℤ, ∀ j b, conj (CellScalars.curlGradMode c (n' - n) p j b) =
      CellScalars.curlGradMode c (n - n') p j b := by
    intro n n' j b
    have e : n' - n = -(n - n') := by ring
    rw [e]
    exact coef_conj_neg c.order (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)) j b) (n - n')
  have gw := good_congr gall (fun n n' => (wave_split _ _ _ (hG n n') (sG n) (sV n) (sG n') (sV n')).symm)
  have hbd := gw.2.2
  have hK : (1 * K0 * 3 * 3 + ((1 * K0 * 3 * 3 * 3 * 3 + 1 * K0 * 3 * 3 * 3 * 3) +
      1 * K0 * 3 * 3 * 3 * 3) + 1 * K0 * 3 * 3 * 3 * 3) = 333 * K0 := by ring
  calc |(waveSum c K S x p).re| ≤ ‖waveSum c K S x p‖ := Complex.abs_re_le_norm _
    _ ≤ _ := hbd
    _ ≤ 333 * (M * ((S.resolved.card : ℝ) + 1)) * 81 *
        ∑' n : ℤ, (sumSq (sharpGrad c K S x n p) + vecSq (sharpVel c K S x n p)) := by
      rw [hK0, hQt]; ring_nf; rfl

end Breakdown.CellCert.CellAnalysis
