import Breakdown.CertCell.AssemblyRowExpansionRestDeact
import Breakdown.CertCell.OwnSolidOrbit
import Breakdown.CertCell.AssemblyRowExpansionRestFrameFacts

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation TorusMean CellCert.CellAnalysis CellCert.CellFormula
  CellCalculus Coercive.StretchInternal

theorem conj_labelPhase_exp (m : ℕ) (α : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (labelPhase m α τ φ)
      = Complex.exp (-(((2 * Real.pi * ((labelHarmonic m α).1 : ℝ) * τ + ((labelHarmonic m α).2 : ℝ) * φ : ℝ) : ℂ)
          * Complex.I)) := by
  unfold labelPhase labelHarmonic
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  ring

theorem coefOf_fibVel (m : ℕ) (α : ℤ × ℤ) (W : ℝ → Space → Space) (y : Space) (a : Fin 3) :
    coefOf m α (fun τ φ => ((fibVel W y τ φ a : ℝ) : ℂ)) = modeVel (labelHarmonic m α) W 0 y a := by
  unfold coefOf torusMean modeVel modeAverage fibVel
  simp only [conj_labelPhase_exp, zero_add]

theorem fibVel_sq (X : ℝ → Space → Space) (y : Space) (τ φ : ℝ) :
    ∑ a, ‖((fibVel X y τ φ a : ℝ) : ℂ)‖ ^ 2 = ‖X τ (axialRot φ y)‖ ^ 2 := by
  have e : ∀ z, axialRot (-φ) z = Coercive.RotationInternal.axialRotEquiv (-φ) z := fun _ => rfl
  simp only [Complex.norm_real, fibVel]
  rw [← (Coercive.RotationInternal.axialRotEquiv (-φ)).norm_map (X τ (axialRot φ y)), ← e, EuclideanSpace.norm_sq_eq]

theorem rotated_coordinate_continuous {V : ℝ × ℝ → Space} (hV : Continuous V) (a : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ((axialRot (-z.2) (V z) a : ℝ) : ℂ)) := by
  unfold axialRot
  fun_prop

theorem orbit_pair_continuous (y : Space) : Continuous (fun z : ℝ × ℝ => (z.1, axialRot z.2 y)) := by
  unfold axialRot
  fun_prop

theorem orbit_continuous_of_continuous {X : ℝ → Space → Space} (hX : Continuous (fun z : ℝ × Space => X z.1 z.2))
    (y : Space) : Continuous (fun z : ℝ × ℝ => X z.1 (axialRot z.2 y)) :=
  hX.comp (orbit_pair_continuous y)

theorem fibVel_continuous_of_orbit {X : ℝ → Space → Space} {y : Space}
    (hX : Continuous (fun z : ℝ × ℝ => X z.1 (axialRot z.2 y))) (a : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ((fibVel X y z.1 z.2 a : ℝ) : ℂ)) :=
  rotated_coordinate_continuous hX a

theorem torusIntegrable_of_continuous_box {f : ℝ → ℝ → ℂ} (hf : Continuous (fun z : ℝ × ℝ => f z.1 z.2)) :
    IsTorusIntegrable f := by
  obtain ⟨C, hC⟩ := ((isCompact_Icc (a := (0 : ℝ)) (b := 1)).prod (isCompact_Icc (a := (0 : ℝ)) (b := 2 * Real.pi))).exists_bound_of_continuousOn hf.continuousOn
  exact bounded_integrable f hf.aestronglyMeasurable ⟨C, fun τ φ h1 h2 h3 h4 => hC (τ, φ) ⟨⟨h1.le, h2⟩, ⟨h3.le, h4⟩⟩⟩

theorem coefOf_sub (m : ℕ) (α : ℤ × ℤ) {A B : ℝ → ℝ → ℂ} (hA : IsTorusIntegrable A) (hB : IsTorusIntegrable B) :
    coefOf m α (fun τ φ => A τ φ - B τ φ) = coefOf m α A - coefOf m α B := by
  unfold coefOf
  have e : (fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * (A τ φ - B τ φ))
      = fun τ φ => (starRingEnd ℂ) (labelPhase m α τ φ) * A τ φ + (-1) * ((starRingEnd ℂ) (labelPhase m α τ φ) * B τ φ) := by
    funext τ φ; ring
  have hA' := isTorusIntegrable_conj_label_mul m α hA
  have hB' := isTorusIntegrable_conj_label_mul m α hB
  have hB'' : IsTorusIntegrable (fun τ φ => (-1 : ℂ) * ((starRingEnd ℂ) (labelPhase m α τ φ) * B τ φ)) := by
    unfold IsTorusIntegrable at hB' ⊢; exact hB'.const_mul (-1)
  rw [e, torusMean_add _ _ hA' hB'', torusMean_const_mul]
  ring

theorem split_long_sq_bound {solid : Set Space} {W M hi L : ℝ → Space → Space} {eh el e : ℝ}
    (hs : CellCalculus.IsSplitPart solid W M hi L eh el e) (σ : ℝ) (y : Space) (hy : y ∈ solid) :
    ‖W σ y - M σ y - L σ y‖ ^ 2 ≤ (e + eh) ^ 2 := by
  have h1 := hs.rest_bound σ y hy
  have h2 := hs.high_bound σ y hy
  have h3 : ‖W σ y - M σ y - L σ y‖ ≤ e + eh := by
    calc ‖W σ y - M σ y - L σ y‖ = ‖(W σ y - M σ y - hi σ y - L σ y) + hi σ y‖ := by congr 1; abel
      _ ≤ ‖W σ y - M σ y - hi σ y - L σ y‖ + ‖hi σ y‖ := norm_add_le _ _
      _ ≤ e + eh := add_le_add h1 h2
  exact pow_le_pow_left₀ (norm_nonneg _) h3 2

theorem fibVel_sub (X Y : ℝ → Space → Space) (y : Space) (τ φ : ℝ) (a : Fin 3) :
    fibVel X y τ φ a - fibVel Y y τ φ a = fibVel (fun σ z => X σ z - Y σ z) y τ φ a := by
  have e : ∀ z, axialRot (-φ) z = Coercive.RotationInternal.axialRotEquiv (-φ) z := fun _ => rfl
  unfold fibVel
  rw [e, e, e, map_sub]
  rfl

theorem error_field {count : ℕ} (box : Fin count → CellBox) (K : Fin count) (m : ℕ) (hm : 1 ≤ m)
    (W L : ℝ → Space → Space) (F : CellVecField count) (hi : ℝ → Space → Space) {eh el e : ℝ}
    (hs : CellCalculus.IsSplitPart (CellCalculus.ownSolid box K) W (F.field box m) hi L eh el e)
    (p : ℝ × ℝ) (hsol : ∀ φ, axialRot φ (planePoint p) ∈ CellCalculus.ownSolid box K)
    (hWc : Continuous (fun z : ℝ × ℝ => W z.1 (axialRot z.2 (planePoint p))))
    (hLc : Continuous (fun z : ℝ × ℝ => L z.1 (axialRot z.2 (planePoint p))))
    (hfr : ∀ τ φ : ℝ, ∀ a : Fin 3, ((fibVel (F.field box m) (planePoint p) τ φ a : ℝ) : ℂ)
        = ∑ α ∈ F.labels K, labelPhase m α τ φ * F.planeValue box K α a p)
    (hoff : ∀ α, α ∉ F.labels K → ∀ a, F.planeValue box K α a p = 0) :
    ∃ E : ℝ → ℝ → Fin 3 → ℂ, (∀ a, IsTorusIntegrable (fun τ φ => E τ φ a)) ∧
      (∀ τ φ, ∑ a, ‖E τ φ a‖ ^ 2 ≤ (e + eh) ^ 2) ∧
      ∀ α a, coefOf m α (fun τ φ => E τ φ a)
        = labelVel m α W p a - F.planeValue box K α a p - labelVel m α L p a := by
  let E : ℝ → ℝ → Fin 3 → ℂ := fun τ φ a => (((fibVel W (planePoint p) τ φ a : ℝ) : ℂ)
    - ((fibVel L (planePoint p) τ φ a : ℝ) : ℂ))
    - ∑ α ∈ F.labels K, F.planeValue box K α a p * labelPhase m α τ φ
  have hE : ∀ τ φ a, E τ φ a
      = ((fibVel (fun σ z => W σ z - F.field box m σ z - L σ z) (planePoint p) τ φ a : ℝ) : ℂ) := by
    intro τ φ a
    have h2 := fibVel_sub W (F.field box m) (planePoint p) τ φ a
    have h1 := fibVel_sub (fun σ z => W σ z - F.field box m σ z) L (planePoint p) τ φ a
    beta_reduce at h1
    rw [← h1, ← h2]
    simp only [E]
    push_cast
    rw [hfr τ φ a, Finset.sum_congr rfl (fun α _ => mul_comm (F.planeValue box K α a p) (labelPhase m α τ φ))]
    ring
  have hb : ∀ τ φ, ∑ a, ‖E τ φ a‖ ^ 2 ≤ (e + eh) ^ 2 := by
    intro τ φ
    simp only [hE]
    rw [fibVel_sq]
    exact split_long_sq_bound hs τ _ (hsol φ)
  have hWf : ∀ a, Continuous (fun z : ℝ × ℝ => ((fibVel W (planePoint p) z.1 z.2 a : ℝ) : ℂ)) :=
    fun a => fibVel_continuous_of_orbit hWc a
  have hLf : ∀ a, Continuous (fun z : ℝ × ℝ => ((fibVel L (planePoint p) z.1 z.2 a : ℝ) : ℂ)) :=
    fun a => fibVel_continuous_of_orbit hLc a
  have hcont : ∀ a, Continuous (fun z : ℝ × ℝ => E z.1 z.2 a) := fun a =>
    ((hWf a).sub (hLf a)).sub (trig_continuous m _ _)
  refine ⟨E, fun a => torusIntegrable_of_continuous_box (hcont a), hb, fun α a => ?_⟩
  have hWi := torusIntegrable_of_continuous_box (f := fun τ φ => ((fibVel W (planePoint p) τ φ a : ℝ) : ℂ)) (hWf a)
  have hLi := torusIntegrable_of_continuous_box (f := fun τ φ => ((fibVel L (planePoint p) τ φ a : ℝ) : ℂ)) (hLf a)
  have hWLi := torusIntegrable_of_continuous_box (f := fun τ φ => ((fibVel W (planePoint p) τ φ a : ℝ) : ℂ)
    - ((fibVel L (planePoint p) τ φ a : ℝ) : ℂ)) ((hWf a).sub (hLf a))
  rw [show (fun τ φ => E τ φ a) = fun τ φ => (((fibVel W (planePoint p) τ φ a : ℝ) : ℂ)
      - ((fibVel L (planePoint p) τ φ a : ℝ) : ℂ))
      - ∑ α ∈ F.labels K, F.planeValue box K α a p * labelPhase m α τ φ from rfl,
    coefOf_sub m α hWLi (trig_integrable m _ _), coefOf_sub m α hWi hLi, coefOf_fibVel, coefOf_fibVel,
    coefOf_trig m hm]
  unfold labelVel
  split_ifs with h
  · ring
  · rw [hoff α h a]; ring

theorem torusMean_const (m : ℕ) (hm : 1 ≤ m) (b : ℂ) : torusMean (fun _ _ => b) = b := by
  have h1 : torusMean (fun τ φ => (starRingEnd ℂ) (labelPhase m 0 τ φ)) = 1 := by
    rw [torusMean_label m hm]; simp
  have h2 : (fun τ φ => (starRingEnd ℂ) (labelPhase m 0 τ φ)) = fun _ _ => (1 : ℂ) := by
    funext τ φ
    simp [labelPhase, labelTime, labelAzimuth]
  rw [h2] at h1
  have := torusMean_const_mul b (fun _ _ => (1 : ℂ))
  simp only [mul_one] at this
  rw [this, h1, mul_one]
theorem coef_vec_sq_le (m : ℕ) (hm : 1 ≤ m) (α : ℤ × ℤ) (E : ℝ → ℝ → Fin 3 → ℂ)
    (hE : ∀ a, IsTorusIntegrable (fun τ φ => E τ φ a)) (b : ℝ) (hb : ∀ τ φ, ∑ a, ‖E τ φ a‖ ^ 2 ≤ b) :
    ∑ a, ‖coefOf m α (fun τ φ => E τ φ a)‖ ^ 2 ≤ b := by
  have hn : ∀ a, IsTorusIntegrable (fun τ φ => ((‖E τ φ a‖ ^ 2 : ℝ) : ℂ)) := fun a =>
    torusIntegrable_normSq_of_bound (hE a) b (fun τ φ => le_trans
      (Finset.single_le_sum (f := fun a => ‖E τ φ a‖ ^ 2) (fun _ _ => by positivity) (Finset.mem_univ a)) (hb τ φ))
  have h1 : ∀ a, ‖coefOf m α (fun τ φ => E τ φ a)‖ ^ 2 ≤ (torusMean (fun τ φ => ((‖E τ φ a‖ ^ 2 : ℝ) : ℂ))).re := by
    intro a
    have := coef_sq_sum_le m hm {α} (fun τ φ => E τ φ a) (hE a) (hn a)
    rwa [Finset.sum_singleton] at this
  have hs : IsTorusIntegrable (fun τ φ => ((∑ a, ‖E τ φ a‖ ^ 2 : ℝ) : ℂ)) := by
    have h := isTorusIntegrable_sum Finset.univ _ (fun a _ => hn a)
    unfold IsTorusIntegrable at h ⊢
    refine h.congr (Filter.Eventually.of_forall (fun z => ?_))
    simp only [Complex.ofReal_sum]
  calc ∑ a, ‖coefOf m α (fun τ φ => E τ φ a)‖ ^ 2
      ≤ ∑ a, (torusMean (fun τ φ => ((‖E τ φ a‖ ^ 2 : ℝ) : ℂ))).re := Finset.sum_le_sum (fun a _ => h1 a)
    _ = (torusMean (fun τ φ => ((∑ a, ‖E τ φ a‖ ^ 2 : ℝ) : ℂ))).re := by
        rw [← Complex.re_sum, ← torusMean_sum _ _ (fun a _ => hn a)]
        congr 2
        funext τ φ
        push_cast
        rfl
    _ ≤ (torusMean (fun _ _ => ((b : ℝ) : ℂ))).re :=
        torusMean_re_mono _ _ hs (torusIntegrable_const _) (fun τ φ _ _ _ _ => by
          rw [Complex.ofReal_re, Complex.ofReal_re]; exact hb τ φ)
    _ = b := by rw [torusMean_const m hm, Complex.ofReal_re]


theorem offAxis_isOpen : IsOpen {z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2
    ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0} := by
  have hr : Continuous (fun z : ℝ × Space => CellCert.CellAnalysis.cylRadius z.2) := by
    unfold CellCert.CellAnalysis.cylRadius
    fun_prop
  have hh : Continuous (fun z : ℝ × Space => CellCert.CellAnalysis.cylHeight z.2) := by
    unfold CellCert.CellAnalysis.cylHeight
    fun_prop
  exact (isOpen_lt continuous_const hr).inter (isOpen_ne_fun hh continuous_const)

theorem orbit_offAxis_mem (p : ℝ × ℝ) (hp1 : 0 < p.1) (hp2 : p.2 ≠ 0) (σ φ : ℝ) :
    (σ, axialRot φ (planePoint p)) ∈ {z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2
      ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0} :=
  ⟨by rw [orbit_radius φ p hp1.le]; exact hp1, by rw [orbit_height]; exact hp2⟩

theorem orbit_continuous_of_offAxis {X : ℝ → Space → Space}
    (hX : ContinuousOn (fun z : ℝ × Space => X z.1 z.2) {z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2
      ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0}) (p : ℝ × ℝ) (hp1 : 0 < p.1) (hp2 : p.2 ≠ 0) :
    Continuous (fun z : ℝ × ℝ => X z.1 (axialRot z.2 (planePoint p))) :=
  hX.comp_continuous (orbit_pair_continuous (planePoint p)) (fun z => orbit_offAxis_mem p hp1 hp2 z.1 z.2)

theorem labelVel_measurable_of_offAxis (m : ℕ) (X : ℝ → Space → Space)
    (hX : ContinuousOn (fun z : ℝ × Space => X z.1 z.2) {z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2
      ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0})
    (M : CellMesh) (hM : IsCellMesh M) (K : Fin M.count) (α : ℤ × ℤ) (a : Fin 3) :
    AEStronglyMeasurable (fun p => labelVel m α X p a) (volume.restrict (M.box K).rect) := by
  have hs := offAxis_isOpen.measurableSet
  let Y : ℝ → Space → Space := fun σ y => ({z : ℝ × Space | 0 < CellCert.CellAnalysis.cylRadius z.2
      ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0}).indicator (fun z : ℝ × Space => X z.1 z.2) (σ, y)
  have hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume :=
    (aestronglyMeasurable_indicator_iff hs).2 (hX.aestronglyMeasurable hs)
  have h1 := (TrueRegular.aesm_modeVel_plane hY (labelHarmonic m α) a).mono_ac
    (TrueRegular.restrict_ac (TrueRegular.rect_ae_le_halfPlane (hM.box_valid K)))
  refine h1.congr ?_
  filter_upwards [ae_own_point M hM K, ae_off_plane (M.box K)] with p hown hp2
  have e : (fun τ φ i => axialRot (-φ) (Y (0 + τ) (axialRot φ (planePoint p))) i)
      = (fun τ φ i => axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p))) i) := by
    funext τ φ i
    simp only [Y, Set.indicator_of_mem (orbit_offAxis_mem p hown.1 hp2 (0 + τ) φ)]
  simp only [labelVel, modeVel]
  rw [e]

section Error

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def errVec (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ℓ : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun c =>
  ∑ ι' ∈ S, crossVec (bandProfile D ι' v G p)
    (fun a => trueVelocity D (ℓ - ι') p a - modelVelocity D K (ℓ - ι') p a - longVelocity D R K (ℓ - ι') p a)
    (fun a => trueVorticity D (ℓ - ι') p a - modelVorticity D K (ℓ - ι') p a - longVorticity D R K (ℓ - ι') p a) c

theorem error_pointwise (hCC : CellCalculusConditions D R) (hmesh : IsCellMesh D.mesh) (hm : 1 ≤ D.azimuthOrder) {B0 : ℝ}
    (hWS : CoerciveWeak.IsWeakSecondDerivState D.given D.givenHess B0)
    (hvo : ∀ K α, α ∉ D.model.velocity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
      D.model.velocity.planeValue D.mesh.box K α a p = 0)
    (hwo : ∀ K α, α ∉ D.model.vorticity.labels K → ∀ p ∈ (D.mesh.box K).rect, ∀ a,
      D.model.vorticity.planeValue D.mesh.box K α a p = 0)
    (hFr : VecFieldFrameStatement) (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ))
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect),
      (∑ ℓ ∈ D.mesh.tested K, ∑ c, ‖errVec D R K S v G ℓ p c‖ ^ 2
        ≤ 2 * ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2
            * ∑ ι' ∈ S, modeCurlSq D ι' G p
          + 2 * ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2
            * ∑ ι' ∈ S, modeVelSq D ι' v p) ∧
      (∀ α, ∑ a, ‖trueVelocity D α p a - modelVelocity D K α p a - longVelocity D R K α p a‖ ^ 2
        ≤ ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2) ∧
      (∀ α, ∑ a, ‖trueVorticity D α p a - modelVorticity D K α p a - longVorticity D R K α p a‖ ^ 2
        ≤ ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2) := by
  have hK := hmesh.box_valid K
  have hsp := hCC.model_split K
  have hFV := hFr D.mesh D.model.velocity D.azimuthOrder K hmesh hsp.model_conj_closed.1
  have hFW := hFr D.mesh D.model.vorticity D.azimuthOrder K hmesh hsp.model_conj_closed.2.1
  have hcW : Continuous (fun z : ℝ × Space => D.given z.1 z.2) := hWS.smooth.continuous
  have hcO : Continuous (fun z : ℝ × Space => vorticityOf D.given z.1 z.2) :=
    TrueRegular.continuous_curlVec.comp (CoerciveWeak.Internal.AbsorbStep.continuous_fderiv_slice_of_one hWS.smooth)
  obtain ⟨hLV, hLO, _⟩ := hsp.long_regular
  filter_upwards [hFV, hFW, ae_restrict_mem (rect_measurableSet (D.mesh.box K)), ae_own_point D.mesh hmesh K,
    ae_off_plane (D.mesh.box K)] with p hV hO hp hown hp2
  have hsol : ∀ φ, axialRot φ (planePoint p) ∈ ownSolid D.mesh.box K := fun φ =>
    orbit_mem_ownSolid D.mesh.box K hK p hp hown.1 hown.2 φ
  have hWo := orbit_continuous_of_continuous (X := D.given) hcW (planePoint p)
  have hOo := orbit_continuous_of_continuous (X := vorticityOf D.given) hcO (planePoint p)
  have hLVo := orbit_continuous_of_offAxis (X := (R.long K).velocity) hLV p hown.1 hp2
  have hLOo := orbit_continuous_of_offAxis (X := (R.long K).vorticity) hLO p hown.1 hp2
  obtain ⟨EW, hWi, hWb, hWc⟩ := error_field D.mesh.box K D.azimuthOrder hm D.given (R.long K).velocity
    D.model.velocity (R.high K).velocity hsp.velocity p hsol hWo hLVo hV (fun α h a => hvo K α h p hp a)
  obtain ⟨EO, hOi, hOb, hOc⟩ := error_field D.mesh.box K D.azimuthOrder hm (vorticityOf D.given)
    (R.long K).vorticity D.model.vorticity (R.high K).vorticity hsp.vorticity p hsol hOo hLOo hO
    (fun α h a => hwo K α h p hp a)
  refine ⟨?_, fun α => ?_, fun α => ?_⟩
  · have h := cross_coef_sum_le D.azimuthOrder hm S (D.mesh.tested K)
      (fun ι' => bandProfile D ι' v G p) EW EO hWi hOi _ _ hWb hOb
    simp only [hWc, hOc, curlOfU_bandProfile, velOfU_bandProfile] at h
    simp only [errVec, trueVelocity, trueVorticity, modelVelocity, modelVorticity, longVelocity, longVorticity]
    exact h
  · have h := coef_vec_sq_le D.azimuthOrder hm α EW hWi _ hWb
    simp only [hWc] at h
    simp only [trueVelocity, modelVelocity, longVelocity]
    exact h
  · have h := coef_vec_sq_le D.azimuthOrder hm α EO hOi _ hOb
    simp only [hOc] at h
    simp only [trueVorticity, modelVorticity, longVorticity]
    exact h

end Error

end Internal

open Coupling CellCert.CellAnalysis CellCert.CellFormula CellCalculus _root_.Breakdown.CertCell.Assembly.Internal

namespace Internal

theorem inverseWeightedSq_inv_smul {n : Type*} [Fintype n] [DecidableEq n] (M : Matrix n n ℂ) {c : ℝ} (hc : c ≠ 0)
    (t : n → ℂ) : inverseWeightedSq (((c : ℂ)⁻¹) • M) t = c * inverseWeightedSq M t := by
  have hc' : (c : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hc
  have hinv : ((c : ℂ)⁻¹ • M)⁻¹ = (c : ℂ) • M⁻¹ := by
    by_cases h : IsUnit M.det
    · refine Matrix.inv_eq_right_inv ?_
      rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_nonsing_inv M h, smul_smul, inv_mul_cancel₀ hc', one_smul]
    · have h2 : ¬ IsUnit ((c : ℂ)⁻¹ • M).det := by
        rw [Matrix.det_smul]
        intro hu
        exact h (isUnit_of_mul_isUnit_right hu)
      rw [Matrix.nonsing_inv_apply_not_isUnit _ h, Matrix.nonsing_inv_apply_not_isUnit _ h2, smul_zero]
  unfold inverseWeightedSq quadForm
  rw [hinv, Matrix.smul_mulVec]
  simp [dotProduct_smul]

theorem scaledRowGram_const {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (K : Fin D.mesh.count)
    {V : Type} (B : CellBlocks V) (c : ℝ) :
    scaledRowGram D K B (fun _ => c) = ((c : ℂ)⁻¹) • rowGram D K B := by
  ext i i'
  simp only [scaledRowGram, Matrix.smul_apply, smul_eq_mul]
  rw [div_eq_inv_mul]

theorem modelPlaneValue_aesm {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (K : Fin D.mesh.count)
    (hK : IsCellBox (D.mesh.box K)) (F : CellVecField D.mesh.count) (α : ℤ × ℤ) (a : Fin 3) :
    AEStronglyMeasurable (fun p => F.planeValue D.mesh.box K α a p) (volume.restrict (D.mesh.box K).rect) := by
  have h : ∀ p ∈ (D.mesh.box K).rect, (F.comp K α a).eval (D.mesh.box K) p = F.planeValue D.mesh.box K α a p := by
    intro p hp
    have h2 : 0 ≤ p.2 := le_trans hK.z_order.1 hp.2.1
    simp only [CellVecField.planeValue, labelValueAt, if_pos h2]
  exact (cellPoly_eval_continuous _ _).aestronglyMeasurable.congr
    (ae_restrict_of_forall_mem (rect_measurableSet _) h)

end Internal

theorem errorPieceBound_of (hFr : Internal.VecFieldFrameStatement) : ErrorPieceBoundHolds := by
  intro k C nE nM D R A P states hstates hReg hTF hvo hwo hC hF K q v G H g κ F Pg ht
  classical
  have hK := hC.mesh_valid.box_valid K
  have hcost : 0 < (A.blocks K).errorCost := (hF.costs_pos K).1
  have hm : 1 ≤ D.azimuthOrder := hReg.field.azimuth_pos
  obtain ⟨B0, hWS⟩ := hReg.field.model_state
  obtain ⟨S, hS⟩ : ∃ S, S = D.mesh.resolved K ∪ D.mesh.band K ∪ deactSources D K (P.potential K) := ⟨_, rfl⟩
  have hae := error_pointwise D R hF.cell_conditions hC.mesh_valid hm hWS hvo hwo hFr K S v G
  have hsp := hF.cell_conditions.model_split K
  have hmeas := fun α => Internal.TrueRegular.given_modes_measurable hWS D.azimuthOrder
    (Internal.TrueRegular.rect_ae_le_halfPlane hK) α
  have hLV : ∀ α a, AEStronglyMeasurable (fun p => longVelocity D R K α p a) (volume.restrict (D.mesh.box K).rect) :=
    fun α a => labelVel_measurable_of_offAxis D.azimuthOrder _ hsp.long_regular.1 D.mesh hC.mesh_valid K α a
  have hLO : ∀ α a, AEStronglyMeasurable (fun p => longVorticity D R K α p a) (volume.restrict (D.mesh.box K).rect) :=
    fun α a => labelVel_measurable_of_offAxis D.azimuthOrder _ hsp.long_regular.2.1 D.mesh hC.mesh_valid K α a
  have hbpm : ∀ ι j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect) :=
    fun ι j => ((hTF.1 K q v G H g κ F Pg ht).1 ι).1 j
  have hbpi : ∀ ι, IntegrableOn (fun p => p.1 * ∑ j, ‖bandProfile D ι v G p j‖ ^ 2) (D.mesh.box K).rect :=
    fun ι => ((hTF.1 K q v G H g κ F Pg ht).1 ι).2
  have hWm : ∀ α a, AEStronglyMeasurable
      (fun p => trueVelocity D α p a - modelVelocity D K α p a - longVelocity D R K α p a)
      (volume.restrict (D.mesh.box K).rect) :=
    fun α a => (((hmeas α).2.2.1 a).sub (modelPlaneValue_aesm D K hK D.model.velocity α a)).sub (hLV α a)
  have hOm : ∀ α a, AEStronglyMeasurable
      (fun p => trueVorticity D α p a - modelVorticity D K α p a - longVorticity D R K α p a)
      (volume.restrict (D.mesh.box K).rect) :=
    fun α a => (((hmeas α).2.2.2 a).sub (modelPlaneValue_aesm D K hK D.model.vorticity α a)).sub (hLO α a)
  have hφc : ∀ i c, Continuous (fun p => rowTestValue D K (A.blocks K) i p c) :=
    fun i c => rowTestValue_continuous D K (A.blocks K) i c
  have hterm : ∀ i ι', IntegrableOn (fun p => (p.1 : ℂ) * ∑ c, crossVec (bandProfile D ι' v G p)
      (fun a => trueVelocity D ((A.blocks K).rowLabel i - ι') p a
        - modelVelocity D K ((A.blocks K).rowLabel i - ι') p a - longVelocity D R K ((A.blocks K).rowLabel i - ι') p a)
      (fun a => trueVorticity D ((A.blocks K).rowLabel i - ι') p a
        - modelVorticity D K ((A.blocks K).rowLabel i - ι') p a
        - longVorticity D R K ((A.blocks K).rowLabel i - ι') p a) c
      * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c)) (D.mesh.box K).rect := by
    intro i ι'
    refine crossVec_term_integrable hK (hbpm ι') (hbpi ι') (hWm _) (hOm _)
      (CW := ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2)
      (CΩ := ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2) ?_ ?_ (hφc i)
    · filter_upwards [hae] with p hp using hp.2.1 _
    · filter_upwards [hae] with p hp using hp.2.2 _
  have heq : ∀ i, errorPiece D R K (A.blocks K) (P.potential K) v G i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ c, errVec D R K S v G ((A.blocks K).rowLabel i) p c * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c) := by
    intro i
    unfold errorPiece
    rw [← hS]
    simp only [crossTest_pairing]
    rw [← integral_finsetSum _ (fun ι' _ => hterm i ι')]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [errVec, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  set ev := ((D.modelErrors K).velocity + (D.modelErrors K).velocityHigh) ^ 2 with hev
  set ew := ((D.modelErrors K).vorticity + (D.modelErrors K).vorticityHigh) ^ 2 with hew
  set Rd : ℝ × ℝ → ℝ := fun p => 2 * ev * ∑ ι' ∈ S, modeCurlSq D ι' G p + 2 * ew * ∑ ι' ∈ S, modeVelSq D ι' v p
    with hRd
  have hcs := fun ι => (profile_integrable D hTF hK ht ι).2.1
  have hvs := fun ι => (profile_integrable D hTF hK ht ι).1
  have hRdi : IntegrableOn (fun p => p.1 * Rd p) (D.mesh.box K).rect := by
    have h : IntegrableOn (fun p => 2 * ev * ∑ ι' ∈ S, p.1 * modeCurlSq D ι' G p
        + 2 * ew * ∑ ι' ∈ S, p.1 * modeVelSq D ι' v p) (D.mesh.box K).rect :=
      ((integrable_finsetSum _ (fun ι' _ => hcs ι')).const_mul _).add
        ((integrable_finsetSum _ (fun ι' _ => hvs ι')).const_mul _)
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    show 2 * ev * ∑ ι' ∈ S, p.1 * modeCurlSq D ι' G p + 2 * ew * ∑ ι' ∈ S, p.1 * modeVelSq D ι' v p = p.1 * Rd p
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    simp only [hRd]
    ring
  have hfm : ∀ ℓ ∈ D.mesh.tested K, ∀ c, AEStronglyMeasurable (fun p => errVec D R K S v G ℓ p c)
      (volume.restrict (D.mesh.box K).rect) := by
    intro ℓ _ c
    unfold errVec
    exact Finset.aestronglyMeasurable_fun_sum _ (fun ι' _ => crossVec_measurable (hbpm _) (hWm _) (hOm _) c)
  have hfi : ∀ ℓ ∈ D.mesh.tested K, ∀ c, IntegrableOn (fun p => p.1 * ‖errVec D R K S v G ℓ p c‖ ^ 2)
      (D.mesh.box K).rect := by
    intro ℓ hℓ c
    refine Integrable.mono' hRdi (continuous_fst.aestronglyMeasurable.mul ((hfm ℓ hℓ c).norm.pow 2)) ?_
    filter_upwards [ae_restrict_mem (rect_measurableSet (D.mesh.box K)), hae] with p hp hpa
    have hp0 := rect_first_nonneg hK hp
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hpa.1) hp0
    refine le_trans ?_ (Finset.single_le_sum (f := fun ℓ => ∑ c, ‖errVec D R K S v G ℓ p c‖ ^ 2)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => by positivity)) hℓ)
    exact Finset.single_le_sum (f := fun c => ‖errVec D R K S v G ℓ p c‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ c)
  have hb := inverseWeightedSq_rows_le D R A hC K (fun ℓ p c => errVec D R K S v G ℓ p c) hfm hfi
    (errorPiece D R K (A.blocks K) (P.potential K) v G) heq
  have hsumi : ∀ ℓ ∈ D.mesh.tested K, IntegrableOn (fun p => p.1 * ∑ c, ‖errVec D R K S v G ℓ p c‖ ^ 2)
      (D.mesh.box K).rect := by
    intro ℓ hℓ
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun c _ => hfi ℓ hℓ c)
  have h1 : ∑ ℓ ∈ D.mesh.tested K, ∫ p in (D.mesh.box K).rect, p.1 * ∑ c, ‖errVec D R K S v G ℓ p c‖ ^ 2
      ≤ ∫ p in (D.mesh.box K).rect, p.1 * Rd p := by
    rw [← integral_finsetSum _ hsumi]
    refine integral_mono_ae (integrable_finsetSum _ hsumi) hRdi ?_
    filter_upwards [ae_restrict_mem (rect_measurableSet (D.mesh.box K)), hae] with p hp hpa
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left hpa.1 (rect_first_nonneg hK hp)
  have hdisj1 : Disjoint (D.mesh.resolved K) (D.mesh.band K) := hC.mesh_valid.band_apart K
  have hdisj2 : Disjoint (D.mesh.resolved K ∪ D.mesh.band K) (deactSources D K (P.potential K)) := by
    rw [Finset.disjoint_left]
    intro ι h1 h2
    simp only [deactSources, Finset.mem_filter] at h2
    rcases Finset.mem_union.1 h1 with h | h
    · exact h2.2.1 h
    · exact h2.2.2 h
  have h2 : (A.blocks K).errorCost * ∫ p in (D.mesh.box K).rect, p.1 * Rd p
      = errorAllowance D K (A.blocks K) (D.mesh.resolved K) v G + errorAllowance D K (A.blocks K) (D.mesh.band K) v G
        + errorAllowance D K (A.blocks K) (deactSources D K (P.potential K)) v G := by
    unfold errorAllowance
    rw [← Finset.sum_union hdisj1, ← Finset.sum_union hdisj2, ← hS]
    rw [← hev, ← hew]
    have hint : ∀ ι ∈ S, IntegrableOn (fun p => 2 * (A.blocks K).errorCost *
        (p.1 * (ev * modeCurlSq D ι G p + ew * modeVelSq D ι v p))) (D.mesh.box K).rect := by
      intro ι _
      refine ((((hcs ι).const_mul ev).add ((hvs ι).const_mul ew)).const_mul (2 * (A.blocks K).errorCost)).congr
        (Filter.Eventually.of_forall (fun p => ?_))
      simp only [Pi.add_apply]
      ring
    rw [Finset.sum_congr rfl (fun ι _ => (integral_const_mul (2 * (A.blocks K).errorCost)
      (fun p => p.1 * (ev * modeCurlSq D ι G p + ew * modeVelSq D ι v p))).symm),
      ← integral_finsetSum _ hint, ← integral_const_mul]
    congr 1
    funext p
    have e1 : ∀ ι, 2 * (A.blocks K).errorCost * (p.1 * (ev * modeCurlSq D ι G p + ew * modeVelSq D ι v p))
        = (2 * (A.blocks K).errorCost * p.1 * ev) * modeCurlSq D ι G p
          + (2 * (A.blocks K).errorCost * p.1 * ew) * modeVelSq D ι v p := fun ι => by ring
    simp only [e1, Finset.sum_add_distrib, ← Finset.mul_sum, hRd]
    ring
  have hscale : inverseWeightedSq (scaledRowGram D K (A.blocks K) (fun _ => (A.blocks K).errorCost))
      (errorPiece D R K (A.blocks K) (P.potential K) v G)
      = (A.blocks K).errorCost * inverseWeightedSq (rowGram D K (A.blocks K))
        (errorPiece D R K (A.blocks K) (P.potential K) v G) := by
    rw [scaledRowGram_const, inverseWeightedSq_inv_smul _ hcost.ne']
  rw [hscale]
  calc (A.blocks K).errorCost * inverseWeightedSq (rowGram D K (A.blocks K))
        (errorPiece D R K (A.blocks K) (P.potential K) v G)
      ≤ (A.blocks K).errorCost
        * ∑ ℓ ∈ D.mesh.tested K, ∫ p in (D.mesh.box K).rect, p.1 * ∑ c, ‖errVec D R K S v G ℓ p c‖ ^ 2 :=
        mul_le_mul_of_nonneg_left hb hcost.le
    _ ≤ (A.blocks K).errorCost * ∫ p in (D.mesh.box K).rect, p.1 * Rd p :=
        mul_le_mul_of_nonneg_left h1 hcost.le
    _ = _ := h2

theorem errorPieceBound_holds : ErrorPieceBoundHolds :=
  errorPieceBound_of Internal.vecFieldFrame

end Assembly

end CertCell

end Breakdown
