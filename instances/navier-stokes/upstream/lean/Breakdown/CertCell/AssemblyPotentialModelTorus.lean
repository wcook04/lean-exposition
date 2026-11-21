import Breakdown.CertCell.AssemblyPotentialModelCharges

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

open Bridge


section Pointwise

theorem high_pointwise (S Gω : Fin 3 → Fin 3 → ℂ) (hs hg yc ys yv : ℝ) (hhs : 0 ≤ hs) (hhg : 0 ≤ hg)
    (hyc : 0 < yc) (hys : 0 < ys) (hyv : 0 < yv)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ hs ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ hg ^ 2 * cnormSq u)
    (U V : Fin 12 → ℂ) :
    -(chargeForm (yc * hs) (3 / (2 * Real.sqrt 2) * hg * ys) (3 / (2 * Real.sqrt 2) * hg * yv) U
        + chargeForm (hs / yc) (3 / (2 * Real.sqrt 2) * hg / yv) (3 / (2 * Real.sqrt 2) * hg / ys) V)
      ≤ 2 * (pairSesq (tripleMatrix S Gω) U V).re := by
  have hc : ∀ j l, curlGradOfSecondDeriv (curlGradPreimage Gω) (j, l) = Gω j l := curlGradOfSecondDeriv_preimage Gω
  rw [sesq_tripleMatrix, modelTriple_eq_stretchTriple]
  have hB := stretchTripleBound (fun ij => S ij.1 ij.2) (curlGradPreimage Gω) hs hg hhs hhg (fun u => hS u)
    (fun u => by simpa only [hc] using hG u) (velOf V) (gradOf V) (star (velOf U)) (star (gradOf U))
  rw [curlOfGrad_star_grad, cnormSq_star_vec, cnormSq_star_vec, cnormSq_star_vec] at hB
  set cU := cnormSq (curlOfGrad (gradOf U))
  set cV := cnormSq (curlOfGrad (gradOf V))
  set gU := cnormSq (gradOf U)
  set gV := cnormSq (gradOf V)
  set aU := cnormSq (velOf U)
  set aV := cnormSq (velOf V)
  have n0 : ∀ x : Fin 3 → ℂ, 0 ≤ cnormSq x := fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have n1 : ∀ x : Fin 3 × Fin 3 → ℂ, 0 ≤ cnormSq x := fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  have y1 := two_sqrt_mul_le cU cV yc (n0 _) (n0 _) hyc
  have y2 := two_sqrt_mul_le gU aV ys (n1 _) (n0 _) hys
  have y3 := two_sqrt_mul_le aU gV yv (n0 _) (n1 _) hyv
  have hk : 0 ≤ 3 / (2 * Real.sqrt 2) * hg := by positivity
  have m1 := mul_le_mul_of_nonneg_left y1 hhs
  have m2 := mul_le_mul_of_nonneg_left y2 hk
  have m3 := mul_le_mul_of_nonneg_left y3 hk
  have e := Complex.abs_re_le_norm (stretchTriple (fun ij => S ij.1 ij.2) (curlGradPreimage Gω) (velOf V) (gradOf V)
    (star (velOf U)) (star (gradOf U)))
  have := neg_abs_le (stretchTriple (fun ij => S ij.1 ij.2) (curlGradPreimage Gω) (velOf V) (gradOf V)
    (star (velOf U)) (star (gradOf U))).re
  have f1 : hs * (yc * cU + cV / yc) = yc * hs * cU + hs / yc * cV := by field_simp
  have f2 : 3 / (2 * Real.sqrt 2) * hg * (ys * gU + aV / ys)
      = 3 / (2 * Real.sqrt 2) * hg * ys * gU + 3 / (2 * Real.sqrt 2) * hg / ys * aV := by field_simp
  have f3 : 3 / (2 * Real.sqrt 2) * hg * (yv * aU + gV / yv)
      = 3 / (2 * Real.sqrt 2) * hg * yv * aU + 3 / (2 * Real.sqrt 2) * hg / yv * gV := by field_simp
  have s1 : Real.sqrt cV * Real.sqrt cU = Real.sqrt cU * Real.sqrt cV := mul_comm _ _
  have s2 : Real.sqrt aV * Real.sqrt gU = Real.sqrt gU * Real.sqrt aV := mul_comm _ _
  unfold chargeForm
  nlinarith [hB, m1, m2, m3, f1, f2, f3, s1, s2]

theorem rest_pointwise (S Gω : Fin 3 → Fin 3 → ℂ) (εS εG L ℓ : ℝ) (hσ : 0 ≤ εS) (hγ : 0 ≤ εG) (hL : 0 < L)
    (hℓ : 0 < ℓ)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ εS ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ εG ^ 2 * cnormSq u)
    (U W : Fin 12 → ℂ) :
    -(chargeForm (2 * εS) (3 / (2 * Real.sqrt 2) * εG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * εG / L) U
        + chargeForm εS (3 / (2 * Real.sqrt 2) * εG * L) (3 / (2 * Real.sqrt 2) * εG / ℓ) W)
      ≤ (pairSesq (tripleMatrix S Gω) U U + 2 * pairSesq (tripleMatrix S Gω) U W).re := by
  have h1 := high_pointwise S Gω εS εG 1 L L⁻¹ hσ hγ one_pos hL (inv_pos.2 hL) hS hG U U
  have h2 := high_pointwise S Gω εS εG 1 ℓ L⁻¹ hσ hγ one_pos hℓ (inv_pos.2 hL) hS hG U W
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  rw [Complex.add_re, h2re]
  unfold chargeForm at h1 h2 ⊢
  simp only [div_inv_eq_mul] at h1 h2
  linear_combination h1 / 2 + h2

end Pointwise


section TorusCore

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

theorem torusIntegrable_of_cont {f : ℝ → ℝ → ℂ} (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) :
    IsTorusIntegrable f := by
  unfold IsTorusIntegrable boxMeasure
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

theorem pairSesq_sub_mat (M M' : Matrix (Fin 12) (Fin 12) ℂ) (U V : Fin 12 → ℂ) :
    pairSesq (M - M') U V = pairSesq M U V - pairSesq M' U V := by
  simp only [pairSesq, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]

theorem pairSesq_add_right (M : Matrix (Fin 12) (Fin 12) ℂ) (U V V' : Fin 12 → ℂ) :
    pairSesq M U (V + V') = pairSesq M U V + pairSesq M U V' := by
  simp only [pairSesq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem pairSesq_smul_right (M : Matrix (Fin 12) (Fin 12) ℂ) (c : ℂ) (U V : Fin 12 → ℂ) :
    pairSesq M U (c • V) = c * pairSesq M U V := by
  simp only [pairSesq, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem waveSum_add (m : ℕ) (S : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) :
    waveSum m S (fun ι => X ι + Y ι) τ φ = waveSum m S X τ φ + waveSum m S Y τ φ := by
  funext j
  simp only [waveSum, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem waveSum_smul (m : ℕ) (S : Finset (ℤ × ℤ)) (c : ℂ) (X : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) :
    waveSum m S (fun ι => c • X ι) τ φ = c • waveSum m S X τ φ := by
  funext j
  simp only [waveSum, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  ring

theorem waveSum_union (m : ℕ) {S T : Finset (ℤ × ℤ)} (h : Disjoint S T) (X Y : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) :
    waveSum m (S ∪ T) (fun ι => if ι ∈ S then X ι else Y ι) τ φ = waveSum m S X τ φ + waveSum m T Y τ φ := by
  classical
  funext j
  simp only [waveSum, Pi.add_apply]
  rw [Finset.sum_union h]
  congr 1
  · refine Finset.sum_congr rfl fun ι hι => ?_
    simp [hι]
  · refine Finset.sum_congr rfl fun ι hι => ?_
    have : ι ∉ S := fun hS => Finset.disjoint_left.1 h hS hι
    simp [this]

theorem tripleMatrix_entry_integrable (S Gω : ℝ → ℝ → Fin 3 → Fin 3 → ℂ)
    (hS : ∀ a b, IsTorusIntegrable (fun τ φ => S τ φ a b)) (hG : ∀ a b, IsTorusIntegrable (fun τ φ => Gω τ φ a b))
    (i j : Fin 12) : IsTorusIntegrable (fun τ φ => tripleMatrix (S τ φ) (Gω τ φ) i j) := by
  simp only [tripleMatrix, modelTriple_eq_coef]
  refine torusIntegrable_add (torusIntegrable_finsum _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => ?_)
    (torusIntegrable_finsum _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => ?_)
  · exact Integrable.mul_const (hS a b) _
  · exact Integrable.mul_const (hG a b) _

theorem chargeForm_wave_integrable (c₁ c₂ c₃ : ℝ) (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) :
    IsTorusIntegrable (fun τ φ => ((chargeForm c₁ c₂ c₃ (waveSum m S X τ φ) : ℝ) : ℂ)) :=
  torusIntegrable_of_cont (Complex.continuous_ofReal.comp (chargeForm_wave_continuous c₁ c₂ c₃ m S X))

theorem torusProduct_re (hT : TorusFacts) (m : ℕ) {M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : ∀ i j, IsTorusIntegrable (fun τ φ => M τ φ i j)) (S T : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S, ∑ ι' ∈ T, (pairSesq (torusCoef m M (ι - ι')) (X ι) (Y ι')).re
      = (torusMean (fun τ φ => pairSesq (M τ φ) (waveSum m S X τ φ) (waveSum m T Y τ φ))).re := by
  rw [hT.product m M S T X Y hM, Complex.re_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Complex.re_sum]

end TorusCore


section TorusMain

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

def epsOwnForm (εS εG L ℓ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm (2 * εS) (3 / (2 * Real.sqrt 2) * εG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * εG / L) U

def epsPartnerForm (εS εG L ℓ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm εS (3 / (2 * Real.sqrt 2) * εG * L) (3 / (2 * Real.sqrt 2) * εG / ℓ) U

def ownForm (hs hg yc ys yv : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm (yc * hs) (3 / (2 * Real.sqrt 2) * hg * ys) (3 / (2 * Real.sqrt 2) * hg * yv) U

def partnerForm (hs hg yc ys yv : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm (hs / yc) (3 / (2 * Real.sqrt 2) * hg / yv) (3 / (2 * Real.sqrt 2) * hg / ys) U

def IsSymOpBound (c : ℝ) (S : Fin 3 → Fin 3 → ℂ) : Prop :=
  ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ c ^ 2 * cnormSq u

def IsOpBound (c : ℝ) (S : Fin 3 → Fin 3 → ℂ) : Prop :=
  ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, S j l * u l) ≤ c ^ 2 * cnormSq u

theorem torus_core_eps (hT : TorusFacts) {m : ℕ} (hm : 1 ≤ m) {Rs Bd : Finset (ℤ × ℤ)} (hdisj : Disjoint Rs Bd)
    (SW GW Sm Gm Sh Gh : ℝ → ℝ → Fin 3 → Fin 3 → ℂ)
    (iSW : ∀ a b, IsTorusIntegrable (fun τ φ => SW τ φ a b)) (iGW : ∀ a b, IsTorusIntegrable (fun τ φ => GW τ φ a b))
    (iSm : ∀ a b, IsTorusIntegrable (fun τ φ => Sm τ φ a b)) (iGm : ∀ a b, IsTorusIntegrable (fun τ φ => Gm τ φ a b))
    (iSh : ∀ a b, IsTorusIntegrable (fun τ φ => Sh τ φ a b)) (iGh : ∀ a b, IsTorusIntegrable (fun τ φ => Gh τ φ a b))
    {εS εG L ℓ hs hg yc ys yv : ℝ} (hεS : 0 ≤ εS) (hεG : 0 ≤ εG) (hL : 0 < L) (hℓ : 0 < ℓ) (hhs : 0 ≤ hs) (hhg : 0 ≤ hg)
    (hyc : 0 < yc) (hys : 0 < ys) (hyv : 0 < yv)
    (hrest : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      IsSymOpBound εS (SW τ φ - Sm τ φ - Sh τ φ) ∧ IsOpBound εG (GW τ φ - Gm τ φ - Gh τ φ))
    (hhigh : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → IsSymOpBound hs (Sh τ φ) ∧ IsOpBound hg (Gh τ φ))
    (X O Yl Tt B : ℤ × ℤ → Fin 12 → ℂ) (hO : ∀ ι ∈ Rs, O ι = Yl ι + Tt ι) :
    (∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) (ι - ι'))
          (X ι) (X ι' + (2 : ℂ) • O ι')).re
        + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ Bd, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) (ι - ι'))
          (X ι) (B ι')).re)
      - (∑ ι ∈ Rs, epsOwnForm εS εG L ℓ (X ι) + ∑ ι ∈ Rs, epsPartnerForm εS εG L ℓ (O ι)
        + ∑ ι ∈ Bd, epsPartnerForm εS εG L ℓ (B ι)
        + ∑ ι ∈ Rs, ownForm hs hg yc ys yv (X ι) + ∑ ι ∈ Rs, partnerForm hs hg yc ys yv (Tt ι)
        + ∑ ι ∈ Bd, partnerForm hs hg yc ys yv (B ι))
    ≤ (∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) (ι - ι'))
          (X ι) (X ι' + (2 : ℂ) • O ι')).re
        + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ Bd, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) (ι - ι'))
          (X ι) (B ι')).re)
      - ∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sh τ φ) (Gh τ φ)) (ι - ι'))
          (X ι) (X ι' + (2 : ℂ) • Yl ι')).re := by
  classical
  set MW : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ := fun τ φ => tripleMatrix (SW τ φ) (GW τ φ) with hMW
  set Mm : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ := fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ) with hMm
  set Mh : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ := fun τ φ => tripleMatrix (Sh τ φ) (Gh τ φ) with hMh
  have iMW : ∀ i j, IsTorusIntegrable (fun τ φ => MW τ φ i j) := tripleMatrix_entry_integrable SW GW iSW iGW
  have iMm : ∀ i j, IsTorusIntegrable (fun τ φ => Mm τ φ i j) := tripleMatrix_entry_integrable Sm Gm iSm iGm
  have iMh : ∀ i j, IsTorusIntegrable (fun τ φ => Mh τ φ i j) := tripleMatrix_entry_integrable Sh Gh iSh iGh
  set Z1 : ℤ × ℤ → Fin 12 → ℂ := fun ι => X ι + (2 : ℂ) • O ι with hZ1
  set Z2 : ℤ × ℤ → Fin 12 → ℂ := fun ι => X ι + (2 : ℂ) • Yl ι with hZ2
  rw [torusProduct_re hT m iMm Rs Rs X Z1, torusProduct_re hT m iMm Rs Bd X B, torusProduct_re hT m iMW Rs Rs X Z1,
    torusProduct_re hT m iMW Rs Bd X B, torusProduct_re hT m iMh Rs Rs X Z2]
  set P1 := fun τ φ => pairSesq (MW τ φ) (waveSum m Rs X τ φ) (waveSum m Rs Z1 τ φ)
  set P2 := fun τ φ => pairSesq (Mm τ φ) (waveSum m Rs X τ φ) (waveSum m Rs Z1 τ φ)
  set P3 := fun τ φ => pairSesq (MW τ φ) (waveSum m Rs X τ φ) (waveSum m Bd B τ φ)
  set P4 := fun τ φ => pairSesq (Mm τ φ) (waveSum m Rs X τ φ) (waveSum m Bd B τ φ)
  set P5 := fun τ φ => pairSesq (Mh τ φ) (waveSum m Rs X τ φ) (waveSum m Rs Z2 τ φ)
  have i1 : IsTorusIntegrable P1 := pairSesq_wave_integrable m iMW Rs Rs X Z1
  have i2 : IsTorusIntegrable P2 := pairSesq_wave_integrable m iMm Rs Rs X Z1
  have i3 : IsTorusIntegrable P3 := pairSesq_wave_integrable m iMW Rs Bd X B
  have i4 : IsTorusIntegrable P4 := pairSesq_wave_integrable m iMm Rs Bd X B
  have i5 : IsTorusIntegrable P5 := pairSesq_wave_integrable m iMh Rs Rs X Z2
  set FOB : ℤ × ℤ → Fin 12 → ℂ := fun ι => if ι ∈ Rs then O ι else B ι with hFOB
  set FTB : ℤ × ℤ → Fin 12 → ℂ := fun ι => if ι ∈ Rs then Tt ι else B ι with hFTB
  set Cf : ℝ → ℝ → ℂ := fun τ φ => ((epsOwnForm εS εG L ℓ (waveSum m Rs X τ φ)
      + epsPartnerForm εS εG L ℓ (waveSum m (Rs ∪ Bd) FOB τ φ)
      + ownForm hs hg yc ys yv (waveSum m Rs X τ φ) + partnerForm hs hg yc ys yv (waveSum m (Rs ∪ Bd) FTB τ φ) : ℝ) : ℂ)
    with hCf
  have iC : IsTorusIntegrable Cf := by
    refine torusIntegrable_of_cont (Complex.continuous_ofReal.comp ?_)
    exact ((((chargeForm_wave_continuous _ _ _ m Rs X)).add
      (chargeForm_wave_continuous _ _ _ m (Rs ∪ Bd) FOB)).add (chargeForm_wave_continuous _ _ _ m Rs X)).add
      (chargeForm_wave_continuous _ _ _ m (Rs ∪ Bd) FTB)
  have iNC : IsTorusIntegrable (fun τ φ => -Cf τ φ) := Integrable.neg iC
  set Df : ℝ → ℝ → ℂ := fun τ φ => P1 τ φ - P2 τ φ + 2 * (P3 τ φ - P4 τ φ) - P5 τ φ with hDf
  have iA : IsTorusIntegrable (fun τ φ => P1 τ φ - P2 τ φ) := torusIntegrable_sub i1 i2
  have iB : IsTorusIntegrable (fun τ φ => 2 * (P3 τ φ - P4 τ φ)) := torusIntegrable_const_mul 2 (torusIntegrable_sub i3 i4)
  have iAB : IsTorusIntegrable (fun τ φ => P1 τ φ - P2 τ φ + 2 * (P3 τ φ - P4 τ φ)) := torusIntegrable_add iA iB
  have iD : IsTorusIntegrable Df := torusIntegrable_sub iAB i5
  have hmono := hT.re_mono (fun τ φ => -Cf τ φ) Df iNC iD (fun τ φ h1 h2 h3 h4 => by
    obtain ⟨hrS, hrG⟩ := hrest τ φ h1 h2 h3 h4
    obtain ⟨hhS, hhG⟩ := hhigh τ φ h1 h2 h3 h4
    have hwO : waveSum m Rs O τ φ = waveSum m Rs Yl τ φ + waveSum m Rs Tt τ φ := by
      rw [← waveSum_add]
      funext j
      simp only [waveSum]
      refine Finset.sum_congr rfl fun ι hι => ?_
      rw [hO ι hι]
    have hsplit : Df τ φ
        = pairSesq (tripleMatrix (SW τ φ - Sm τ φ - Sh τ φ) (GW τ φ - Gm τ φ - Gh τ φ)) (waveSum m Rs X τ φ)
            (waveSum m Rs X τ φ)
          + 2 * pairSesq (tripleMatrix (SW τ φ - Sm τ φ - Sh τ φ) (GW τ φ - Gm τ φ - Gh τ φ)) (waveSum m Rs X τ φ)
            (waveSum m (Rs ∪ Bd) FOB τ φ)
          + 2 * pairSesq (tripleMatrix (Sh τ φ) (Gh τ φ)) (waveSum m Rs X τ φ) (waveSum m (Rs ∪ Bd) FTB τ φ) := by
      simp only [hDf, P1, P2, P3, P4, P5, hMW, hMm, hMh, hZ1, hZ2, hFOB, hFTB]
      rw [waveSum_union m hdisj, waveSum_union m hdisj, tripleMatrix_sub, tripleMatrix_sub, waveSum_add, waveSum_add,
        waveSum_smul, waveSum_smul, hwO]
      simp only [pairSesq_sub_mat, pairSesq_add_right, pairSesq_smul_right, smul_add]
      ring
    have r1 := rest_pointwise (SW τ φ - Sm τ φ - Sh τ φ) (GW τ φ - Gm τ φ - Gh τ φ) εS εG L ℓ hεS hεG hL hℓ hrS hrG
      (waveSum m Rs X τ φ) (waveSum m (Rs ∪ Bd) FOB τ φ)
    have r2 := high_pointwise (Sh τ φ) (Gh τ φ) hs hg yc ys yv hhs hhg hyc hys hyv hhS hhG
      (waveSum m Rs X τ φ) (waveSum m (Rs ∪ Bd) FTB τ φ)
    rw [hsplit]
    have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
    simp only [Cf, Complex.neg_re, Complex.ofReal_re, Complex.add_re, h2re, epsOwnForm, epsPartnerForm, ownForm,
      partnerForm]
    rw [Complex.add_re, h2re] at r1
    linarith)
  have hDmean : torusMean Df = torusMean P1 - torusMean P2 + 2 * (torusMean P3 - torusMean P4) - torusMean P5 := by
    simp only [hDf]
    rw [torusMean_sub hT iAB i5, hT.add _ _ iA iB, torusMean_sub hT i1 i2, torusMean_const_mul,
      torusMean_sub hT i3 i4]
  have hCmean : torusMean Cf = ((∑ ι ∈ Rs, epsOwnForm εS εG L ℓ (X ι) + (∑ ι ∈ Rs, epsPartnerForm εS εG L ℓ (O ι)
      + ∑ ι ∈ Bd, epsPartnerForm εS εG L ℓ (B ι)) + ∑ ι ∈ Rs, ownForm hs hg yc ys yv (X ι)
      + (∑ ι ∈ Rs, partnerForm hs hg yc ys yv (Tt ι) + ∑ ι ∈ Bd, partnerForm hs hg yc ys yv (B ι)) : ℝ) : ℂ) := by
    have j1 := chargeForm_wave_integrable (2 * εS) (3 / (2 * Real.sqrt 2) * εG * (L + ℓ))
      (2 * (3 / (2 * Real.sqrt 2)) * εG / L) m Rs X
    have j2 := chargeForm_wave_integrable εS (3 / (2 * Real.sqrt 2) * εG * L) (3 / (2 * Real.sqrt 2) * εG / ℓ) m
      (Rs ∪ Bd) FOB
    have j3 := chargeForm_wave_integrable (yc * hs) (3 / (2 * Real.sqrt 2) * hg * ys) (3 / (2 * Real.sqrt 2) * hg * yv)
      m Rs X
    have j4 := chargeForm_wave_integrable (hs / yc) (3 / (2 * Real.sqrt 2) * hg / yv) (3 / (2 * Real.sqrt 2) * hg / ys)
      m (Rs ∪ Bd) FTB
    have e : Cf = fun τ φ => ((chargeForm (2 * εS) (3 / (2 * Real.sqrt 2) * εG * (L + ℓ))
          (2 * (3 / (2 * Real.sqrt 2)) * εG / L) (waveSum m Rs X τ φ) : ℝ) : ℂ)
        + ((chargeForm εS (3 / (2 * Real.sqrt 2) * εG * L) (3 / (2 * Real.sqrt 2) * εG / ℓ)
          (waveSum m (Rs ∪ Bd) FOB τ φ) : ℝ) : ℂ)
        + ((chargeForm (yc * hs) (3 / (2 * Real.sqrt 2) * hg * ys) (3 / (2 * Real.sqrt 2) * hg * yv)
          (waveSum m Rs X τ φ) : ℝ) : ℂ)
        + ((chargeForm (hs / yc) (3 / (2 * Real.sqrt 2) * hg / yv) (3 / (2 * Real.sqrt 2) * hg / ys)
          (waveSum m (Rs ∪ Bd) FTB τ φ) : ℝ) : ℂ) := by
      funext τ φ
      simp only [Cf, epsOwnForm, epsPartnerForm, ownForm, partnerForm]
      push_cast
      ring
    rw [e, hT.add _ _ (torusIntegrable_add (torusIntegrable_add j1 j2) j3) j4,
      hT.add _ _ (torusIntegrable_add j1 j2) j3,
      hT.add _ _ j1 j2,
      torusMean_chargeForm_wave hT hm, torusMean_chargeForm_wave hT hm, torusMean_chargeForm_wave hT hm,
      torusMean_chargeForm_wave hT hm, Finset.sum_union hdisj, Finset.sum_union hdisj]
    have s1 : ∑ ι ∈ Rs, ((chargeForm εS (3 / (2 * Real.sqrt 2) * εG * L) (3 / (2 * Real.sqrt 2) * εG / ℓ) (FOB ι) : ℝ) : ℂ)
        = ∑ ι ∈ Rs, ((epsPartnerForm εS εG L ℓ (O ι) : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun ι hι => by simp [FOB, hι, epsPartnerForm]
    have s2 : ∑ ι ∈ Bd, ((chargeForm εS (3 / (2 * Real.sqrt 2) * εG * L) (3 / (2 * Real.sqrt 2) * εG / ℓ) (FOB ι) : ℝ) : ℂ)
        = ∑ ι ∈ Bd, ((epsPartnerForm εS εG L ℓ (B ι) : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun ι hι => by
        have : ι ∉ Rs := fun h => Finset.disjoint_left.1 hdisj h hι
        simp [FOB, this, epsPartnerForm]
    have s3 : ∑ ι ∈ Rs, ((chargeForm (hs / yc) (3 / (2 * Real.sqrt 2) * hg / yv) (3 / (2 * Real.sqrt 2) * hg / ys)
        (FTB ι) : ℝ) : ℂ) = ∑ ι ∈ Rs, ((partnerForm hs hg yc ys yv (Tt ι) : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun ι hι => by simp [FTB, hι, partnerForm]
    have s4 : ∑ ι ∈ Bd, ((chargeForm (hs / yc) (3 / (2 * Real.sqrt 2) * hg / yv) (3 / (2 * Real.sqrt 2) * hg / ys)
        (FTB ι) : ℝ) : ℂ) = ∑ ι ∈ Bd, ((partnerForm hs hg yc ys yv (B ι) : ℝ) : ℂ) :=
      Finset.sum_congr rfl fun ι hι => by
        have : ι ∉ Rs := fun h => Finset.disjoint_left.1 hdisj h hι
        simp [FTB, this, partnerForm]
    rw [s1, s2, s3, s4]
    simp only [epsOwnForm, epsPartnerForm, ownForm, partnerForm]
    push_cast
    ring
  have hneg : torusMean (fun τ φ => -Cf τ φ) = -torusMean Cf := by
    have := torusMean_const_mul (-1) Cf
    simpa using this
  rw [hneg, hCmean, hDmean] at hmono
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.sub_re, Complex.add_re, h2re] at hmono
  simp only [P1, P2, P3, P4, P5] at hmono
  linarith

end TorusMain

section TorusLong

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

def TorusLongStatement : Prop :=
  TorusFacts → ∀ m : ℕ, 1 ≤ m → ∀ (Rs T : Finset (ℤ × ℤ)) (Sl Gl : ℝ → ℝ → Fin 3 → Fin 3 → ℂ),
    (∀ a b, IsTorusIntegrable (fun τ φ => Sl τ φ a b)) → (∀ a b, IsTorusIntegrable (fun τ φ => Gl τ φ a b)) →
    ∀ (lS lG L ℓ β : ℝ) (N : ℕ), 0 ≤ lS → 0 ≤ lG → 0 < L → 0 < ℓ → 0 < β →
    (∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      (∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((Sl τ φ i j + Sl τ φ j i) / 2) * u j) ≤ lS ^ 2 * cnormSq u) ∧
      (∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gl τ φ j l * u l) ≤ lG ^ 2 * cnormSq u)) →
    (∀ α : ℤ × ℤ, |α.1| ≤ 2 * (N : ℤ) → torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) α = 0) →
    ∀ X W : ℤ × ℤ → Fin 12 → ℂ,
    -(∑ ι ∈ Rs, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) *
          chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * lG / L) (X ι)
        + ∑ ι ∈ T, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) *
          chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) (W ι))
    ≤ ∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) (ι - ι')) (X ι) (X ι')).re
      + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ T,
        (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) (ι - ι')) (X ι) (W ι')).re

theorem sum_ite_two {Bd Dd : Finset (ℤ × ℤ)} (h : Disjoint Bd Dd) (g : ℤ × ℤ → (Fin 12 → ℂ) → ℝ)
    (B Dv : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ Bd ∪ Dd, g ι (if ι ∈ Bd then B ι else Dv ι) = ∑ ι ∈ Bd, g ι (B ι) + ∑ ι ∈ Dd, g ι (Dv ι) := by
  classical
  rw [Finset.sum_union h]
  congr 1
  · exact Finset.sum_congr rfl fun ι hι => by rw [if_pos hι]
  · exact Finset.sum_congr rfl fun ι hι => by rw [if_neg (fun hB => Finset.disjoint_left.1 h hB hι)]

theorem sum_ite_three {Rs Bd Dd : Finset (ℤ × ℤ)} (h1 : Disjoint Rs Bd) (h2 : Disjoint Rs Dd) (h3 : Disjoint Bd Dd)
    (g : ℤ × ℤ → (Fin 12 → ℂ) → ℝ) (O B Dv : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ Rs ∪ Bd ∪ Dd, g ι (if ι ∈ Rs then O ι else if ι ∈ Bd then B ι else Dv ι)
      = ∑ ι ∈ Rs, g ι (O ι) + ∑ ι ∈ Bd, g ι (B ι) + ∑ ι ∈ Dd, g ι (Dv ι) := by
  classical
  rw [Finset.sum_union (Finset.disjoint_union_left.2 ⟨h2, h3⟩), Finset.sum_union h1]
  congr 1
  congr 1
  · exact Finset.sum_congr rfl fun ι hι => by rw [if_pos hι]
  · exact Finset.sum_congr rfl fun ι hι => by
      rw [if_neg (fun hR => Finset.disjoint_left.1 h1 hR hι), if_pos hι]
  · exact Finset.sum_congr rfl fun ι hι => by
      rw [if_neg (fun hR => Finset.disjoint_left.1 h2 hR hι), if_neg (fun hB => Finset.disjoint_left.1 h3 hB hι)]

theorem coefSum_of_sub (m : ℕ) {F G H : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hF : ∀ α, torusCoef m F α = torusCoef m G α - torusCoef m H α) (S T : Finset (ℤ × ℤ))
    (Y Z : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S, ∑ ι' ∈ T, (pairSesq (torusCoef m F (ι - ι')) (Y ι) (Z ι')).re
      = ∑ ι ∈ S, ∑ ι' ∈ T, (pairSesq (torusCoef m G (ι - ι')) (Y ι) (Z ι')).re
        - ∑ ι ∈ S, ∑ ι' ∈ T, (pairSesq (torusCoef m H (ι - ι')) (Y ι) (Z ι')).re := by
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ι' _ => ?_
  rw [hF, pairSesq_sub_mat, Complex.sub_re]

theorem coefSum_union (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) {Bd Dd : Finset (ℤ × ℤ)}
    (h : Disjoint Bd Dd) (S : Finset (ℤ × ℤ)) (Y B Dv : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S, ∑ ι' ∈ Bd ∪ Dd, (pairSesq (torusCoef m M (ι - ι')) (Y ι) (if ι' ∈ Bd then B ι' else Dv ι')).re
      = ∑ ι ∈ S, ∑ ι' ∈ Bd, (pairSesq (torusCoef m M (ι - ι')) (Y ι) (B ι')).re
        + ∑ ι ∈ S, ∑ ι' ∈ Dd, (pairSesq (torusCoef m M (ι - ι')) (Y ι) (Dv ι')).re := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  exact sum_ite_two h (fun ι' V => (pairSesq (torusCoef m M (ι - ι')) (Y ι) V).re) B Dv

theorem coefSum_union_three (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) {Rs Bd Dd : Finset (ℤ × ℤ)}
    (h1 : Disjoint Rs Bd) (h2 : Disjoint Rs Dd) (h3 : Disjoint Bd Dd) (S : Finset (ℤ × ℤ))
    (Y O B Dv : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S, ∑ ι' ∈ Rs ∪ Bd ∪ Dd, (pairSesq (torusCoef m M (ι - ι')) (Y ι)
        (if ι' ∈ Rs then O ι' else if ι' ∈ Bd then B ι' else Dv ι')).re
      = ∑ ι ∈ S, ∑ ι' ∈ Rs, (pairSesq (torusCoef m M (ι - ι')) (Y ι) (O ι')).re
        + ∑ ι ∈ S, ∑ ι' ∈ Bd, (pairSesq (torusCoef m M (ι - ι')) (Y ι) (B ι')).re
        + ∑ ι ∈ S, ∑ ι' ∈ Dd, (pairSesq (torusCoef m M (ι - ι')) (Y ι) (Dv ι')).re := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  exact sum_ite_three h1 h2 h3 (fun ι' V => (pairSesq (torusCoef m M (ι - ι')) (Y ι) V).re) O B Dv

theorem coefSum_add_smul (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) (S : Finset (ℤ × ℤ))
    (X O : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S, ∑ ι' ∈ S, (pairSesq (torusCoef m M (ι - ι')) (X ι) (X ι' + (2 : ℂ) • O ι')).re
      = ∑ ι ∈ S, ∑ ι' ∈ S, (pairSesq (torusCoef m M (ι - ι')) (X ι) (X ι')).re
        + 2 * ∑ ι ∈ S, ∑ ι' ∈ S, (pairSesq (torusCoef m M (ι - ι')) (X ι) (O ι')).re := by
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun ι' _ => ?_
  rw [pairSesq_add_right, pairSesq_smul_right, Complex.add_re]
  simp [Complex.mul_re]

theorem torus_core (hT : TorusFacts) (hTL : TorusLongStatement) {m : ℕ} (hm : 1 ≤ m) {Rs Bd Dd : Finset (ℤ × ℤ)}
    (hdisj : Disjoint Rs Bd) (hdisjD : Disjoint Rs Dd) (hdisjBD : Disjoint Bd Dd)
    (SW GW Sm Gm Sh Gh Sl Gl : ℝ → ℝ → Fin 3 → Fin 3 → ℂ)
    (iSW : ∀ a b, IsTorusIntegrable (fun τ φ => SW τ φ a b)) (iGW : ∀ a b, IsTorusIntegrable (fun τ φ => GW τ φ a b))
    (iSm : ∀ a b, IsTorusIntegrable (fun τ φ => Sm τ φ a b)) (iGm : ∀ a b, IsTorusIntegrable (fun τ φ => Gm τ φ a b))
    (iSh : ∀ a b, IsTorusIntegrable (fun τ φ => Sh τ φ a b)) (iGh : ∀ a b, IsTorusIntegrable (fun τ φ => Gh τ φ a b))
    (iSl : ∀ a b, IsTorusIntegrable (fun τ φ => Sl τ φ a b)) (iGl : ∀ a b, IsTorusIntegrable (fun τ φ => Gl τ φ a b))
    {εS εG L ℓ hs hg yc ys yv lS lG β : ℝ} {N : ℕ} (hεS : 0 ≤ εS) (hεG : 0 ≤ εG) (hL : 0 < L) (hℓ : 0 < ℓ)
    (hhs : 0 ≤ hs) (hhg : 0 ≤ hg) (hyc : 0 < yc) (hys : 0 < ys) (hyv : 0 < yv)
    (hlS : 0 ≤ lS) (hlG : 0 ≤ lG) (hβ : 0 < β)
    (hrest : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      IsSymOpBound εS (SW τ φ - Sm τ φ - Sh τ φ - Sl τ φ) ∧ IsOpBound εG (GW τ φ - Gm τ φ - Gh τ φ - Gl τ φ))
    (hhigh : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → IsSymOpBound hs (Sh τ φ) ∧ IsOpBound hg (Gh τ φ))
    (hlong : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi → IsSymOpBound lS (Sl τ φ) ∧ IsOpBound lG (Gl τ φ))
    (hsupp : ∀ α : ℤ × ℤ, |α.1| ≤ 2 * (N : ℤ) → torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) α = 0)
    (X O Yl Tt B Dv : ℤ × ℤ → Fin 12 → ℂ) (hO : ∀ ι ∈ Rs, O ι = Yl ι + Tt ι) :
    (∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) (ι - ι'))
          (X ι) (X ι' + (2 : ℂ) • O ι')).re
        + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ Bd, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) (ι - ι'))
          (X ι) (B ι')).re
        + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ Dd, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) (ι - ι'))
          (X ι) (Dv ι')).re)
      - (∑ ι ∈ Rs, epsOwnForm εS εG L ℓ (X ι) + ∑ ι ∈ Rs, epsPartnerForm εS εG L ℓ (O ι)
        + ∑ ι ∈ Bd, epsPartnerForm εS εG L ℓ (B ι) + ∑ ι ∈ Dd, epsPartnerForm εS εG L ℓ (Dv ι)
        + ∑ ι ∈ Rs, ownForm hs hg yc ys yv (X ι) + ∑ ι ∈ Rs, partnerForm hs hg yc ys yv (Tt ι)
        + ∑ ι ∈ Bd, partnerForm hs hg yc ys yv (B ι) + ∑ ι ∈ Dd, partnerForm hs hg yc ys yv (Dv ι)
        + ∑ ι ∈ Rs, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * epsOwnForm lS lG L ℓ (X ι)
        + ∑ ι ∈ Rs, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * epsPartnerForm lS lG L ℓ (O ι)
        + ∑ ι ∈ Bd, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * epsPartnerForm lS lG L ℓ (B ι)
        + ∑ ι ∈ Dd, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * epsPartnerForm lS lG L ℓ (Dv ι))
    ≤ (∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) (ι - ι'))
          (X ι) (X ι' + (2 : ℂ) • O ι')).re
        + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ Bd, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) (ι - ι'))
          (X ι) (B ι')).re
        + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ Dd, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) (ι - ι'))
          (X ι) (Dv ι')).re)
      - ∑ ι ∈ Rs, ∑ ι' ∈ Rs, (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sh τ φ) (Gh τ φ)) (ι - ι'))
          (X ι) (X ι' + (2 : ℂ) • Yl ι')).re := by
  classical
  have hRBD : Disjoint Rs (Bd ∪ Dd) := Finset.disjoint_union_right.2 ⟨hdisj, hdisjD⟩
  have iSW' : ∀ a b, IsTorusIntegrable (fun τ φ => (SW τ φ - Sl τ φ) a b) := fun a b => by
    simpa only [Pi.sub_apply] using torusIntegrable_sub (iSW a b) (iSl a b)
  have iGW' : ∀ a b, IsTorusIntegrable (fun τ φ => (GW τ φ - Gl τ φ) a b) := fun a b => by
    simpa only [Pi.sub_apply] using torusIntegrable_sub (iGW a b) (iGl a b)
  have hrest' : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      IsSymOpBound εS (SW τ φ - Sl τ φ - Sm τ φ - Sh τ φ) ∧ IsOpBound εG (GW τ φ - Gl τ φ - Gm τ φ - Gh τ φ) := by
    intro τ φ h1 h2 h3 h4
    have e1 : SW τ φ - Sl τ φ - Sm τ φ - Sh τ φ = SW τ φ - Sm τ φ - Sh τ φ - Sl τ φ := by abel
    have e2 : GW τ φ - Gl τ φ - Gm τ φ - Gh τ φ = GW τ φ - Gm τ φ - Gh τ φ - Gl τ φ := by abel
    rw [e1, e2]
    exact hrest τ φ h1 h2 h3 h4
  have base := torus_core_eps hT hm hRBD (fun τ φ => SW τ φ - Sl τ φ) (fun τ φ => GW τ φ - Gl τ φ) Sm Gm Sh Gh
    iSW' iGW' iSm iGm iSh iGh hεS hεG hL hℓ hhs hhg hyc hys hyv hrest' hhigh X O Yl Tt
    (fun ι => if ι ∈ Bd then B ι else Dv ι) hO
  beta_reduce at base
  have iMW : ∀ i j, IsTorusIntegrable (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ) i j) :=
    tripleMatrix_entry_integrable SW GW iSW iGW
  have iMl : ∀ i j, IsTorusIntegrable (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ) i j) :=
    tripleMatrix_entry_integrable Sl Gl iSl iGl
  have hcW : ∀ α, torusCoef m (fun τ φ => tripleMatrix (SW τ φ - Sl τ φ) (GW τ φ - Gl τ φ)) α
      = torusCoef m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) α
        - torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) α := by
    intro α
    have e : (fun τ φ => tripleMatrix (SW τ φ - Sl τ φ) (GW τ φ - Gl τ φ))
        = fun τ φ => tripleMatrix (SW τ φ) (GW τ φ) - tripleMatrix (Sl τ φ) (Gl τ φ) := by
      funext τ φ
      exact tripleMatrix_sub _ _ _ _
    rw [e]
    exact torusCoef_sub hT m iMW iMl α
  have w1 := coefSum_of_sub m hcW Rs Rs X (fun ι => X ι + (2 : ℂ) • O ι)
  have w2 := coefSum_of_sub m hcW Rs (Bd ∪ Dd) X (fun ι => if ι ∈ Bd then B ι else Dv ι)
  beta_reduce at w1 w2
  have u1 := coefSum_union m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) hdisjBD Rs X B Dv
  have u2 := coefSum_union m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) hdisjBD Rs X B Dv
  have u3 := coefSum_union m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) hdisjBD Rs X B Dv
  have c1 := sum_ite_two hdisjBD (fun _ V => epsPartnerForm εS εG L ℓ V) B Dv
  have c2 := sum_ite_two hdisjBD (fun _ V => partnerForm hs hg yc ys yv V) B Dv
  beta_reduce at c1 c2
  have hLT := hTL hT m hm Rs (Rs ∪ Bd ∪ Dd) Sl Gl iSl iGl lS lG L ℓ β N hlS hlG hL hℓ hβ
    (fun τ φ h1 h2 h3 h4 => hlong τ φ h1 h2 h3 h4) hsupp X
    (fun ι => if ι ∈ Rs then O ι else if ι ∈ Bd then B ι else Dv ι)
  beta_reduce at hLT
  have t1 := coefSum_union_three m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) hdisj hdisjD hdisjBD Rs X O B Dv
  have t2 := sum_ite_three hdisj hdisjD hdisjBD
    (fun ι V => (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) *
      chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) V) O B Dv
  beta_reduce at t2
  have s1 := coefSum_add_smul m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) Rs X O
  have s2 := coefSum_add_smul m (fun τ φ => tripleMatrix (SW τ φ) (GW τ φ)) Rs X O
  have s3 := coefSum_add_smul m (fun τ φ => tripleMatrix (SW τ φ - Sl τ φ) (GW τ φ - Gl τ φ)) Rs X O
  have s4 := coefSum_add_smul m (fun τ φ => tripleMatrix (Sm τ φ) (Gm τ φ)) Rs X O
  simp only [epsOwnForm, epsPartnerForm] at base c1 ⊢
  linarith [base, w1, w2, u1, u2, u3, c1, c2, hLT, t1, t2, s1, s2, s3, s4]

end TorusLong

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
