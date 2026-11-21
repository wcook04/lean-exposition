import Breakdown.CertCell.AssemblyPotentialModelCharges

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace ModelPart

namespace LongPart

open Bridge

section Pointwise

private theorem young_pointwise (S Gω : Fin 3 → Fin 3 → ℂ) (hs hg yc ys yv : ℝ) (hhs : 0 ≤ hs) (hhg : 0 ≤ hg)
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

private def selfForm (lS lG L : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / L) U

private def crossForm (lS lG L ℓ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm lS (3 / (2 * Real.sqrt 2) * lG * ℓ) (3 / (2 * Real.sqrt 2) * lG / L) U

private def partForm (lS lG L ℓ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) U

private def ownForm (lS lG L ℓ : ℝ) (U : Fin 12 → ℂ) : ℝ :=
  chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * lG / L) U

private theorem ownForm_eq (lS lG L ℓ : ℝ) (U : Fin 12 → ℂ) :
    ownForm lS lG L ℓ U = selfForm lS lG L U + crossForm lS lG L ℓ U := by
  unfold ownForm selfForm crossForm chargeForm
  ring

private theorem self_scaled (S Gω : Fin 3 → Fin 3 → ℂ) {lS lG L t : ℝ} (hlS : 0 ≤ lS) (hlG : 0 ≤ lG) (hL : 0 < L)
    (ht : 0 < t)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ lS ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ lG ^ 2 * cnormSq u)
    (U V : Fin 12 → ℂ) :
    -(t * selfForm lS lG L U + t⁻¹ * selfForm lS lG L V) ≤ 2 * (pairSesq (tripleMatrix S Gω) U V).re := by
  have h := young_pointwise S Gω lS lG t (t * L) (t / L) hlS hlG ht (mul_pos ht hL) (div_pos ht hL) hS hG U V
  have e1 : chargeForm (t * lS) (3 / (2 * Real.sqrt 2) * lG * (t * L)) (3 / (2 * Real.sqrt 2) * lG * (t / L)) U
      = t * selfForm lS lG L U := by
    unfold selfForm chargeForm
    ring
  have e2 : chargeForm (lS / t) (3 / (2 * Real.sqrt 2) * lG / (t / L)) (3 / (2 * Real.sqrt 2) * lG / (t * L)) V
      = t⁻¹ * selfForm lS lG L V := by
    unfold selfForm chargeForm
    field_simp
  rw [e1, e2] at h
  exact h

private theorem cross_scaled (S Gω : Fin 3 → Fin 3 → ℂ) {lS lG L ℓ t : ℝ} (hlS : 0 ≤ lS) (hlG : 0 ≤ lG) (hL : 0 < L)
    (hℓ : 0 < ℓ) (ht : 0 < t)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ lS ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ lG ^ 2 * cnormSq u)
    (U V : Fin 12 → ℂ) :
    -(t * crossForm lS lG L ℓ U + t⁻¹ * partForm lS lG L ℓ V) ≤ 2 * (pairSesq (tripleMatrix S Gω) U V).re := by
  have h := young_pointwise S Gω lS lG t (t * ℓ) (t / L) hlS hlG ht (mul_pos ht hℓ) (div_pos ht hL) hS hG U V
  have e1 : chargeForm (t * lS) (3 / (2 * Real.sqrt 2) * lG * (t * ℓ)) (3 / (2 * Real.sqrt 2) * lG * (t / L)) U
      = t * crossForm lS lG L ℓ U := by
    unfold crossForm chargeForm
    ring
  have e2 : chargeForm (lS / t) (3 / (2 * Real.sqrt 2) * lG / (t / L)) (3 / (2 * Real.sqrt 2) * lG / (t * ℓ)) V
      = t⁻¹ * partForm lS lG L ℓ V := by
    unfold partForm chargeForm
    field_simp
  rw [e1, e2] at h
  exact h

private theorem pairSesq_add_left' (M : Matrix (Fin 12) (Fin 12) ℂ) (U U' V : Fin 12 → ℂ) :
    pairSesq M (U + U') V = pairSesq M U V + pairSesq M U' V := by
  simp only [pairSesq, Pi.add_apply, map_add, add_mul, Finset.sum_add_distrib]

private theorem pairSesq_add_right' (M : Matrix (Fin 12) (Fin 12) ℂ) (U V V' : Fin 12 → ℂ) :
    pairSesq M U (V + V') = pairSesq M U V + pairSesq M U V' := by
  simp only [pairSesq, Pi.add_apply, mul_add, Finset.sum_add_distrib]

private theorem long_pointwise (S Gω : Fin 3 → Fin 3 → ℂ) {lS lG L ℓ β : ℝ} (hlS : 0 ≤ lS) (hlG : 0 ≤ lG) (hL : 0 < L)
    (hℓ : 0 < ℓ) (hβ : 0 < β)
    (hS : ∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((S i j + S j i) / 2) * u j) ≤ lS ^ 2 * cnormSq u)
    (hG : ∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gω j l * u l) ≤ lG ^ 2 * cnormSq u)
    (xL xH wL wH : Fin 12 → ℂ) :
    -(β * ownForm lS lG L ℓ xL + (1 + 1 / β) * ownForm lS lG L ℓ xH + β * partForm lS lG L ℓ wL
        + (1 + 1 / β) * partForm lS lG L ℓ wH)
      ≤ (pairSesq (tripleMatrix S Gω) (xL + xH) (xL + xH) + 2 * pairSesq (tripleMatrix S Gω) (xL + xH) (wL + wH)).re
        - (pairSesq (tripleMatrix S Gω) xL xL + 2 * pairSesq (tripleMatrix S Gω) xL wL).re := by
  have hβ' : 0 < β⁻¹ := inv_pos.2 hβ
  have e1 := self_scaled S Gω hlS hlG hL hβ hS hG xL xH
  have e2 := self_scaled S Gω hlS hlG hL hβ' hS hG xH xL
  have e3 := self_scaled S Gω hlS hlG hL one_pos hS hG xH xH
  have e4 := cross_scaled S Gω hlS hlG hL hℓ hβ hS hG xL wH
  have e5 := cross_scaled S Gω hlS hlG hL hℓ hβ' hS hG xH wL
  have e6 := cross_scaled S Gω hlS hlG hL hℓ one_pos hS hG xH wH
  rw [inv_inv] at e2 e5
  rw [ownForm_eq, ownForm_eq]
  simp only [pairSesq_add_left', pairSesq_add_right']
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  simp only [mul_add, Complex.add_re, h2re]
  simp only [inv_one, one_mul] at e3 e6
  rw [one_div]
  linear_combination e1 / 2 + e2 / 2 + e3 / 2 + e4 + e5 + e6

end Pointwise

section Torus

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

private theorem long_torusIntegrable_of_cont {f : ℝ → ℝ → ℂ} (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) :
    IsTorusIntegrable f := by
  unfold IsTorusIntegrable boxMeasure
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  exact (hf.continuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)).mono_set
    (Set.prod_mono Set.Ioc_subset_Icc_self Set.Ioc_subset_Icc_self)

private theorem long_entry_integrable (S Gω : ℝ → ℝ → Fin 3 → Fin 3 → ℂ)
    (hS : ∀ a b, IsTorusIntegrable (fun τ φ => S τ φ a b)) (hG : ∀ a b, IsTorusIntegrable (fun τ φ => Gω τ φ a b))
    (i j : Fin 12) : IsTorusIntegrable (fun τ φ => tripleMatrix (S τ φ) (Gω τ φ) i j) := by
  simp only [tripleMatrix, modelTriple_eq_coef]
  refine torusIntegrable_add (torusIntegrable_finsum _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => ?_)
    (torusIntegrable_finsum _ _ fun a _ => torusIntegrable_finsum _ _ fun b _ => ?_)
  · exact Integrable.mul_const (hS a b) _
  · exact Integrable.mul_const (hG a b) _

private theorem long_form_integrable (c₁ c₂ c₃ r : ℝ) (m : ℕ) (S : Finset (ℤ × ℤ)) (X : ℤ × ℤ → Fin 12 → ℂ) :
    IsTorusIntegrable (fun τ φ => (r : ℂ) * ((chargeForm c₁ c₂ c₃ (waveSum m S X τ φ) : ℝ) : ℂ)) :=
  torusIntegrable_const_mul _
    (long_torusIntegrable_of_cont (Complex.continuous_ofReal.comp (chargeForm_wave_continuous c₁ c₂ c₃ m S X)))

private theorem long_product_re (hT : TorusFacts) (m : ℕ) {M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : ∀ i j, IsTorusIntegrable (fun τ φ => M τ φ i j)) (S T : Finset (ℤ × ℤ)) (X Y : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S, ∑ ι' ∈ T, (pairSesq (torusCoef m M (ι - ι')) (X ι) (Y ι')).re
      = (torusMean (fun τ φ => pairSesq (M τ φ) (waveSum m S X τ φ) (waveSum m T Y τ φ))).re := by
  rw [hT.product m M S T X Y hM, Complex.re_sum]
  refine Finset.sum_congr rfl fun ι _ => ?_
  rw [Complex.re_sum]

private theorem waveSum_filter_split (m : ℕ) (S : Finset (ℤ × ℤ)) (p : ℤ × ℤ → Prop) [DecidablePred p]
    (X : ℤ × ℤ → Fin 12 → ℂ) (τ φ : ℝ) :
    waveSum m S X τ φ = waveSum m (S.filter p) X τ φ + waveSum m (S.filter fun ι => ¬ p ι) X τ φ := by
  funext j
  simp only [waveSum, Pi.add_apply]
  exact (Finset.sum_filter_add_sum_filter_not S p _).symm

private theorem sum_class_split (S : Finset (ℤ × ℤ)) (N : ℕ) (β : ℝ) (g : ℤ × ℤ → ℝ) :
    ∑ ι ∈ S, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) * g ι
      = β * ∑ ι ∈ S.filter (fun ι => |ι.1| ≤ (N : ℤ)), g ι
        + (1 + 1 / β) * ∑ ι ∈ S.filter (fun ι => ¬ |ι.1| ≤ (N : ℤ)), g ι := by
  rw [← Finset.sum_filter_add_sum_filter_not S (fun ι => |ι.1| ≤ (N : ℤ)), Finset.mul_sum, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun ι hι => ?_
    rw [if_pos (Finset.mem_filter.1 hι).2]
  · refine Finset.sum_congr rfl fun ι hι => ?_
    rw [if_neg (Finset.mem_filter.1 hι).2]

private theorem low_block_zero (m : ℕ) (M : ℝ → ℝ → Matrix (Fin 12) (Fin 12) ℂ) (N : ℕ)
    (hsupp : ∀ α : ℤ × ℤ, |α.1| ≤ 2 * (N : ℤ) → torusCoef m M α = 0) (S T : Finset (ℤ × ℤ))
    (X Y : ℤ × ℤ → Fin 12 → ℂ) :
    ∑ ι ∈ S.filter (fun ι => |ι.1| ≤ (N : ℤ)), ∑ ι' ∈ T.filter (fun ι => |ι.1| ≤ (N : ℤ)),
      (pairSesq (torusCoef m M (ι - ι')) (X ι) (Y ι')).re = 0 := by
  refine Finset.sum_eq_zero fun ι hι => Finset.sum_eq_zero fun ι' hι' => ?_
  have h1 := (Finset.mem_filter.1 hι).2
  have h2 := (Finset.mem_filter.1 hι').2
  have h : |(ι - ι').1| ≤ 2 * (N : ℤ) := by
    rw [Prod.fst_sub]
    have := abs_sub ι.1 ι'.1
    linarith
  rw [hsupp _ h]
  simp [pairSesq]

end Torus

section Main

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation

theorem long_class_bound (hT : TorusFacts) {m : ℕ} (hm : 1 ≤ m) {Rs T : Finset (ℤ × ℤ)}
    (Sl Gl : ℝ → ℝ → Fin 3 → Fin 3 → ℂ)
    (iSl : ∀ a b, IsTorusIntegrable (fun τ φ => Sl τ φ a b)) (iGl : ∀ a b, IsTorusIntegrable (fun τ φ => Gl τ φ a b))
    {lS lG L ℓ β : ℝ} (N : ℕ) (hlS : 0 ≤ lS) (hlG : 0 ≤ lG) (hL : 0 < L) (hℓ : 0 < ℓ) (hβ : 0 < β)
    (hbound : ∀ τ φ : ℝ, 0 < τ → τ ≤ 1 → 0 < φ → φ ≤ 2 * Real.pi →
      (∀ u : Fin 3 → ℂ, cnormSq (fun i => ∑ j : Fin 3, ((Sl τ φ i j + Sl τ φ j i) / 2) * u j) ≤ lS ^ 2 * cnormSq u) ∧
      (∀ u : Fin 3 → ℂ, cnormSq (fun j => ∑ l : Fin 3, Gl τ φ j l * u l) ≤ lG ^ 2 * cnormSq u))
    (hsupp : ∀ α : ℤ × ℤ, |α.1| ≤ 2 * (N : ℤ) → torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) α = 0)
    (X W : ℤ × ℤ → Fin 12 → ℂ) :
    -(∑ ι ∈ Rs, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) *
          chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * lG / L) (X ι)
        + ∑ ι ∈ T, (if |ι.1| ≤ (N : ℤ) then β else 1 + 1 / β) *
          chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) (W ι))
    ≤ ∑ ι ∈ Rs, ∑ ι' ∈ Rs,
        (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) (ι - ι')) (X ι) (X ι')).re
      + 2 * ∑ ι ∈ Rs, ∑ ι' ∈ T,
        (pairSesq (torusCoef m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) (ι - ι')) (X ι) (W ι')).re := by
  classical
  have iM : ∀ i j, IsTorusIntegrable (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ) i j) :=
    long_entry_integrable Sl Gl iSl iGl
  have z1 := low_block_zero m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) N hsupp Rs Rs X X
  have z2 := low_block_zero m (fun τ φ => tripleMatrix (Sl τ φ) (Gl τ φ)) N hsupp Rs T X W
  rw [long_product_re hT m iM] at z1 z2
  rw [long_product_re hT m iM, long_product_re hT m iM]
  have s1 := sum_class_split Rs N β
    (fun ι => chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * lG / L) (X ι))
  have s2 := sum_class_split T N β
    (fun ι => chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) (W ι))
  set RL := Rs.filter (fun ι => |ι.1| ≤ (N : ℤ)) with hRL
  set RH := Rs.filter (fun ι => ¬ |ι.1| ≤ (N : ℤ)) with hRH
  set TL := T.filter (fun ι => |ι.1| ≤ (N : ℤ)) with hTL
  set TH := T.filter (fun ι => ¬ |ι.1| ≤ (N : ℤ)) with hTH
  set P1 := fun τ φ => pairSesq (tripleMatrix (Sl τ φ) (Gl τ φ)) (waveSum m Rs X τ φ) (waveSum m Rs X τ φ) with hP1
  set P2 := fun τ φ => pairSesq (tripleMatrix (Sl τ φ) (Gl τ φ)) (waveSum m Rs X τ φ) (waveSum m T W τ φ) with hP2
  set P3 := fun τ φ => pairSesq (tripleMatrix (Sl τ φ) (Gl τ φ)) (waveSum m RL X τ φ) (waveSum m RL X τ φ) with hP3
  set P4 := fun τ φ => pairSesq (tripleMatrix (Sl τ φ) (Gl τ φ)) (waveSum m RL X τ φ) (waveSum m TL W τ φ) with hP4
  have i1 : IsTorusIntegrable P1 := pairSesq_wave_integrable m iM Rs Rs X X
  have i2 : IsTorusIntegrable P2 := pairSesq_wave_integrable m iM Rs T X W
  have i3 : IsTorusIntegrable P3 := pairSesq_wave_integrable m iM RL RL X X
  have i4 : IsTorusIntegrable P4 := pairSesq_wave_integrable m iM RL TL X W
  have iA : IsTorusIntegrable (fun τ φ => P1 τ φ + 2 * P2 τ φ) :=
    torusIntegrable_add i1 (torusIntegrable_const_mul 2 i2)
  have iB : IsTorusIntegrable (fun τ φ => P3 τ φ + 2 * P4 τ φ) :=
    torusIntegrable_add i3 (torusIntegrable_const_mul 2 i4)
  set Df : ℝ → ℝ → ℂ := fun τ φ => (P1 τ φ + 2 * P2 τ φ) - (P3 τ φ + 2 * P4 τ φ) with hDf
  have iD : IsTorusIntegrable Df := torusIntegrable_sub iA iB
  set c₁ : ℝ := β with hc₁
  set c₂ : ℝ := 1 + 1 / β with hc₂
  set Cf : ℝ → ℝ → ℂ := fun τ φ =>
      (c₁ : ℂ) * ((chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ)) (2 * (3 / (2 * Real.sqrt 2)) * lG / L)
          (waveSum m RL X τ φ) : ℝ) : ℂ)
        + (c₂ : ℂ) * ((chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ))
          (2 * (3 / (2 * Real.sqrt 2)) * lG / L) (waveSum m RH X τ φ) : ℝ) : ℂ)
        + (c₁ : ℂ) * ((chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ)
          (waveSum m TL W τ φ) : ℝ) : ℂ)
        + (c₂ : ℂ) * ((chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ)
          (waveSum m TH W τ φ) : ℝ) : ℂ) with hCf
  have j1 := long_form_integrable (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ))
    (2 * (3 / (2 * Real.sqrt 2)) * lG / L) c₁ m RL X
  have j2 := long_form_integrable (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ))
    (2 * (3 / (2 * Real.sqrt 2)) * lG / L) c₂ m RH X
  have j3 := long_form_integrable lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) c₁ m TL W
  have j4 := long_form_integrable lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) c₂ m TH W
  have iC : IsTorusIntegrable Cf := torusIntegrable_add (torusIntegrable_add (torusIntegrable_add j1 j2) j3) j4
  have hmono := hT.re_mono (fun τ φ => -Cf τ φ) Df (Integrable.neg iC) iD (fun τ φ h1 h2 h3 h4 => by
    obtain ⟨hS, hG⟩ := hbound τ φ h1 h2 h3 h4
    have hp := long_pointwise (Sl τ φ) (Gl τ φ) hlS hlG hL hℓ hβ hS hG (waveSum m RL X τ φ) (waveSum m RH X τ φ)
      (waveSum m TL W τ φ) (waveSum m TH W τ φ)
    have hx : waveSum m Rs X τ φ = waveSum m RL X τ φ + waveSum m RH X τ φ :=
      waveSum_filter_split m Rs (fun ι => |ι.1| ≤ (N : ℤ)) X τ φ
    have hw : waveSum m T W τ φ = waveSum m TL W τ φ + waveSum m TH W τ φ :=
      waveSum_filter_split m T (fun ι => |ι.1| ≤ (N : ℤ)) W τ φ
    have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
    simp only [hDf, hCf, hP1, hP2, hP3, hP4, Complex.neg_re, Complex.add_re, Complex.sub_re, h2re,
      Complex.re_ofReal_mul, Complex.ofReal_re]
    rw [hx, hw]
    unfold ownForm partForm at hp
    simp only [Complex.add_re, h2re] at hp
    rw [hc₁, hc₂]
    linarith)
  have hDmean : torusMean Df = torusMean P1 + 2 * torusMean P2 - (torusMean P3 + 2 * torusMean P4) := by
    simp only [hDf]
    rw [torusMean_sub hT iA iB, hT.add _ _ i1 (torusIntegrable_const_mul 2 i2),
      hT.add _ _ i3 (torusIntegrable_const_mul 2 i4), torusMean_const_mul, torusMean_const_mul]
  have hCmean : torusMean Cf = (((c₁ * ∑ ι ∈ RL, chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ))
        (2 * (3 / (2 * Real.sqrt 2)) * lG / L) (X ι)
      + c₂ * ∑ ι ∈ RH, chargeForm (2 * lS) (3 / (2 * Real.sqrt 2) * lG * (L + ℓ))
        (2 * (3 / (2 * Real.sqrt 2)) * lG / L) (X ι)
      + c₁ * ∑ ι ∈ TL, chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) (W ι)
      + c₂ * ∑ ι ∈ TH, chargeForm lS (3 / (2 * Real.sqrt 2) * lG * L) (3 / (2 * Real.sqrt 2) * lG / ℓ) (W ι)) : ℝ)
        : ℂ) := by
    simp only [hCf]
    rw [hT.add _ _ (torusIntegrable_add (torusIntegrable_add j1 j2) j3) j4,
      hT.add _ _ (torusIntegrable_add j1 j2) j3, hT.add _ _ j1 j2,
      torusMean_const_mul, torusMean_const_mul, torusMean_const_mul, torusMean_const_mul,
      torusMean_chargeForm_wave hT hm, torusMean_chargeForm_wave hT hm, torusMean_chargeForm_wave hT hm,
      torusMean_chargeForm_wave hT hm]
    push_cast
    ring
  have hneg : torusMean (fun τ φ => -Cf τ φ) = -torusMean Cf := by
    have := torusMean_const_mul (-1) Cf
    simpa using this
  rw [hneg, hCmean, hDmean] at hmono
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp [Complex.mul_re]
  simp only [Complex.neg_re, Complex.ofReal_re, Complex.sub_re, Complex.add_re, h2re] at hmono
  rw [s1, s2]
  linarith

end Main

end LongPart

end ModelPart

end Internal

end Assembly

end CertCell

end Breakdown
