import Breakdown.CertCell.AssemblyRowExpansionRestTorus
import Breakdown.CertCell.AssemblyTrueRegularParts
import Breakdown.CertCell.OwnSolidOrbit

open MeasureTheory Matrix
open scoped ComplexOrder

noncomputable section

namespace Breakdown

namespace CertCell

namespace Assembly

namespace Internal

namespace LongPart

open Bridge.Internal.MeanStretch Coercive.Internal.ModeRotation TorusMean CellCert.CellAnalysis CellCert.CellFormula
  CellCalculus Coercive.StretchInternal Coupling

theorem conj_phase_eq (m : ℕ) (α : ℤ × ℤ) (τ φ : ℝ) :
    (starRingEnd ℂ) (labelPhase m α τ φ)
      = Complex.exp (-(((2 * Real.pi * ((labelHarmonic m α).1 : ℝ) * τ + ((labelHarmonic m α).2 : ℝ) * φ : ℝ) : ℂ)
          * Complex.I)) := by
  rw [labelPhase, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, labelHarmonic]
  ring

theorem coef_fiber (m : ℕ) (α : ℤ × ℤ) (X : ℝ → Space → Space) (p : ℝ × ℝ) (a : Fin 3) :
    coefOf m α (fun τ φ => ((fibVel X (planePoint p) τ φ a : ℝ) : ℂ)) = labelVel m α X p a := by
  simp only [coefOf, torusMean, labelVel, modeVel, modeAverage, fibVel, conj_phase_eq, zero_add]

theorem fiber_normSq (X : ℝ → Space → Space) (y : Space) (τ φ : ℝ) :
    ∑ a, ‖((fibVel X y τ φ a : ℝ) : ℂ)‖ ^ 2 = ‖X τ (axialRot φ y)‖ ^ 2 := by
  have e : ∀ z, axialRot (-φ) z = Coercive.RotationInternal.axialRotEquiv (-φ) z := fun _ => rfl
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs, fibVel]
  rw [← (Coercive.RotationInternal.axialRotEquiv (-φ)).norm_map (X τ (axialRot φ y)), ← e,
    EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs]

def offAxisPoints : Set (ℝ × Space) :=
  {z | 0 < CellCert.CellAnalysis.cylRadius z.2 ∧ CellCert.CellAnalysis.cylHeight z.2 ≠ 0}

theorem offAxisPoints_open : IsOpen offAxisPoints := by
  have h1 : Continuous (fun z : ℝ × Space => CellCert.CellAnalysis.cylRadius z.2) := by
    unfold CellCert.CellAnalysis.cylRadius
    fun_prop
  have h2 : Continuous (fun z : ℝ × Space => CellCert.CellAnalysis.cylHeight z.2) := by
    unfold CellCert.CellAnalysis.cylHeight
    fun_prop
  exact (isOpen_lt continuous_const h1).inter (isOpen_ne_fun h2 continuous_const)

theorem orbit_offAxis (p : ℝ × ℝ) (hp1 : 0 < p.1) (hp2 : p.2 ≠ 0) (τ φ : ℝ) :
    (τ, axialRot φ (planePoint p)) ∈ offAxisPoints :=
  ⟨by rw [orbit_radius φ p hp1.le]; exact hp1, by rw [orbit_height]; exact hp2⟩

theorem rotated_coord_continuous (V : ℝ × ℝ → Space) (hV : Continuous V) (a : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ((axialRot (-z.2) (V z) a : ℝ) : ℂ)) := by
  unfold axialRot
  fun_prop

theorem fiber_continuous {X : ℝ → Space → Space} (hX : ContinuousOn (fun z : ℝ × Space => X z.1 z.2) offAxisPoints)
    (p : ℝ × ℝ) (hp1 : 0 < p.1) (hp2 : p.2 ≠ 0) (a : Fin 3) :
    Continuous (fun z : ℝ × ℝ => ((fibVel X (planePoint p) z.1 z.2 a : ℝ) : ℂ)) := by
  have hg : Continuous (fun z : ℝ × ℝ => (z.1, axialRot z.2 (planePoint p))) := by
    unfold axialRot
    fun_prop
  have hV : Continuous (fun z : ℝ × ℝ => X z.1 (axialRot z.2 (planePoint p))) :=
    hX.comp_continuous hg (fun z => orbit_offAxis p hp1 hp2 z.1 z.2)
  exact rotated_coord_continuous _ hV a

theorem fiber_coefficients (m : ℕ) (X : ℝ → Space → Space)
    (hX : ContinuousOn (fun z : ℝ × Space => X z.1 z.2) offAxisPoints)
    (S : Set Space) {e : ℝ} (he : 0 ≤ e) (hb : ∀ σ, ∀ y ∈ S, ‖X σ y‖ ≤ e) (p : ℝ × ℝ) (hp1 : 0 < p.1)
    (hp2 : p.2 ≠ 0) (hS : ∀ φ, axialRot φ (planePoint p) ∈ S) :
    ∃ E : ℝ → ℝ → Fin 3 → ℂ, (∀ a, IsTorusIntegrable (fun τ φ => E τ φ a)) ∧
      (∀ τ φ, ∑ a, ‖E τ φ a‖ ^ 2 ≤ e ^ 2) ∧
      ∀ α a, coefOf m α (fun τ φ => E τ φ a) = labelVel m α X p a := by
  refine ⟨fun τ φ a => ((fibVel X (planePoint p) τ φ a : ℝ) : ℂ), ?_, ?_, fun α a => coef_fiber m α X p a⟩
  · intro a
    refine torusIntegrable_of_continuous (fiber_continuous hX p hp1 hp2 a) ⟨e, fun τ φ => ?_⟩
    have h1 : ‖((fibVel X (planePoint p) τ φ a : ℝ) : ℂ)‖ ^ 2 ≤ e ^ 2 := by
      refine le_trans (Finset.single_le_sum (f := fun a => ‖((fibVel X (planePoint p) τ φ a : ℝ) : ℂ)‖ ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a)) ?_
      rw [fiber_normSq]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb τ _ (hS φ)) 2
    exact (abs_le_of_sq_le_sq' h1 he).2
  · intro τ φ
    rw [fiber_normSq]
    exact pow_le_pow_left₀ (norm_nonneg _) (hb τ _ (hS φ)) 2

theorem label_coefficient_measurable (m : ℕ) (X : ℝ → Space → Space)
    (hX : ContinuousOn (fun z : ℝ × Space => X z.1 z.2) offAxisPoints) (M : CellMesh) (hM : IsCellMesh M)
    (K : Fin M.count) (α : ℤ × ℤ) (a : Fin 3) :
    AEStronglyMeasurable (fun p => labelVel m α X p a) (volume.restrict (M.box K).rect) := by
  have hs : MeasurableSet offAxisPoints := offAxisPoints_open.measurableSet
  set Y : ℝ → Space → Space := fun σ y => offAxisPoints.indicator (fun z : ℝ × Space => X z.1 z.2) (σ, y) with hYdef
  have hY : AEStronglyMeasurable (fun z : ℝ × Space => Y z.1 z.2) volume :=
    (aestronglyMeasurable_indicator_iff hs).2 (hX.aestronglyMeasurable hs)
  have h1 := (TrueRegular.aesm_modeVel_plane hY (labelHarmonic m α) a).mono_ac
    (TrueRegular.restrict_ac (TrueRegular.rect_ae_le_halfPlane (hM.box_valid K)))
  refine h1.congr ?_
  filter_upwards [ae_own_point M hM K, ae_off_plane (M.box K)] with p hown hp2
  have e : (fun τ φ i => axialRot (-φ) (Y (0 + τ) (axialRot φ (planePoint p))) i)
      = (fun τ φ i => axialRot (-φ) (X (0 + τ) (axialRot φ (planePoint p))) i) := by
    funext τ φ i
    simp only [hYdef, Set.indicator_of_mem (orbit_offAxis p hown.1 hp2 (0 + τ) φ)]
  simp only [labelVel, modeVel]
  rw [e]

theorem crossVec_zero_zero (U : Fin 12 → ℂ) (c : Fin 3) : crossVec U 0 0 c = 0 := by
  fin_cases c <;> simp [crossVec, crossC]

theorem crossVec_aesm {μ : Measure (ℝ × ℝ)} {U : ℝ × ℝ → Fin 12 → ℂ} {W Ω : ℝ × ℝ → Fin 3 → ℂ}
    (hU : ∀ j, AEStronglyMeasurable (fun p => U p j) μ) (hW : ∀ a, AEStronglyMeasurable (fun p => W p a) μ)
    (hΩ : ∀ a, AEStronglyMeasurable (fun p => Ω p a) μ) (c : Fin 3) :
    AEStronglyMeasurable (fun p => crossVec (U p) (W p) (Ω p) c) μ := by
  have hc : ∀ i, AEStronglyMeasurable (fun p => curlOfU (U p) i) μ := by
    intro i
    unfold curlOfU curlComp
    fun_prop
  have hv : ∀ i, AEStronglyMeasurable (fun p => velOfU (U p) i) μ := fun i => hU _
  unfold crossVec crossC
  fin_cases c <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons, Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue] <;> fun_prop

theorem weighted_pair_integrable {B : CellBox} (hB : IsCellBox B) {g φ : ℝ × ℝ → Fin 3 → ℂ} {Bd : ℝ × ℝ → ℝ}
    (hg : ∀ c, AEStronglyMeasurable (fun p => g p c) (volume.restrict B.rect))
    (hBd : IntegrableOn (fun p => p.1 * Bd p) B.rect)
    (hle : ∀ᵐ p ∂(volume.restrict B.rect), ∑ c, ‖g p c‖ ^ 2 ≤ Bd p)
    (hφ : ∀ c, Continuous (fun p => φ p c)) :
    IntegrableOn (fun p => (p.1 : ℂ) * ∑ c, g p c * (starRingEnd ℂ) (φ p c)) B.rect := by
  have hb : ∀ c, ∃ M, ∀ p ∈ B.rect, ‖φ p c‖ ≤ M := fun c =>
    (rect_isCompact B).exists_bound_of_continuousOn (hφ c).continuousOn
  choose M hM using hb
  set Cφ := ∑ c, |M c| with hCφ
  have hφb : ∀ p ∈ B.rect, ∀ c, ‖φ p c‖ ≤ Cφ := fun p hp c =>
    (hM c p hp).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun c => |M c|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ c)))
  have hC0 : 0 ≤ Cφ := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hp1 : IntegrableOn (fun p : ℝ × ℝ => p.1) B.rect := integrableOn_rect_of_continuous continuous_fst
  refine Integrable.mono' ((hp1.const_mul (3 * Cφ)).add (hBd.const_mul Cφ)) ?_ ?_
  · refine (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul ?_
    exact Finset.aestronglyMeasurable_fun_sum _ (fun c _ => (hg c).mul
      (Complex.continuous_conj.comp (hφ c)).aestronglyMeasurable)
  · filter_upwards [ae_restrict_mem (rect_measurableSet B), hle] with p hp hpl
    have hp0 : 0 ≤ p.1 := rect_first_nonneg hB hp
    have hs : ‖∑ c, g p c * (starRingEnd ℂ) (φ p c)‖ ≤ Cφ * (3 + ∑ c, ‖g p c‖ ^ 2) := by
      refine (norm_sum_le _ _).trans ?_
      calc ∑ c, ‖g p c * (starRingEnd ℂ) (φ p c)‖ ≤ ∑ c, Cφ * (1 + ‖g p c‖ ^ 2) := by
            refine Finset.sum_le_sum (fun c _ => ?_)
            rw [norm_mul, Complex.norm_conj]
            have h1 : ‖g p c‖ ≤ 1 + ‖g p c‖ ^ 2 := by nlinarith [sq_nonneg (‖g p c‖ - 1), norm_nonneg (g p c)]
            calc ‖g p c‖ * ‖φ p c‖ ≤ (1 + ‖g p c‖ ^ 2) * Cφ :=
                  mul_le_mul h1 (hφb p hp c) (norm_nonneg _) (by positivity)
              _ = Cφ * (1 + ‖g p c‖ ^ 2) := by ring
        _ = Cφ * (3 + ∑ c, ‖g p c‖ ^ 2) := by
            rw [← Finset.mul_sum, Finset.sum_add_distrib]
            simp
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg hp0]
    have h3 : Cφ * (3 + ∑ c, ‖g p c‖ ^ 2) ≤ Cφ * (3 + Bd p) := mul_le_mul_of_nonneg_left (by linarith) hC0
    calc p.1 * ‖∑ c, g p c * (starRingEnd ℂ) (φ p c)‖ ≤ p.1 * (Cφ * (3 + Bd p)) :=
          mul_le_mul_of_nonneg_left (hs.trans h3) hp0
      _ = 3 * Cφ * p.1 + Cφ * (p.1 * Bd p) := by ring

section Pointwise

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

def longCouplingVec (K : Fin D.mesh.count) (S : Finset (ℤ × ℤ)) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (ℓ : ℤ × ℤ) (p : ℝ × ℝ) : Fin 3 → ℂ := fun c =>
  ∑ ι' ∈ S, crossVec (bandProfile D ι' v G p) (longVelocity D R K (ℓ - ι') p) (longVorticity D R K (ℓ - ι') p) c

theorem curl_band_eq (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ∑ i, ‖curlOfU (bandProfile D ι v G p) i‖ ^ 2 = modeCurlSq D ι G p := by
  unfold modeCurlSq curlOfU
  refine Finset.sum_congr rfl (fun i _ => ?_)
  congr 3
  funext a b
  exact (gradAt_eq_bandProfile D ι v G a b p).symm

theorem vel_band_eq (ι : ℤ × ℤ) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) :
    ∑ a, ‖velOfU (bandProfile D ι v G p) a‖ ^ 2 = modeVelSq D ι v p := by
  unfold modeVelSq velOfU
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [velAt_eq_bandProfile D ι v G a p]

theorem long_parseval (hCC : CellCalculusConditions D R) (hmesh : IsCellMesh D.mesh) (hm : 1 ≤ D.azimuthOrder)
    (K : Fin D.mesh.count) (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) :
    ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect), ∀ S T : Finset (ℤ × ℤ),
      ∑ ℓ ∈ T, ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2
        ≤ 2 * (R.long K).errVelocity ^ 2 * ∑ ι ∈ S, modeCurlSq D ι G p
          + 2 * (R.long K).errVorticity ^ 2 * ∑ ι ∈ S, modeVelSq D ι v p := by
  have hK := hmesh.box_valid K
  have hsp := hCC.model_split K
  obtain ⟨heW, heO, _, _⟩ := hsp.long_nonneg
  filter_upwards [ae_own_point D.mesh hmesh K, ae_off_plane (D.mesh.box K),
    ae_restrict_mem (rect_measurableSet (D.mesh.box K))] with p hown hp2 hp
  have hsol : ∀ φ, axialRot φ (planePoint p) ∈ ownSolid D.mesh.box K :=
    orbit_mem_ownSolid D.mesh.box K hK p hp hown.1 hown.2
  obtain ⟨EW, hWi, hWb, hWc⟩ := fiber_coefficients D.azimuthOrder (R.long K).velocity hsp.long_regular.1
    (ownSolid D.mesh.box K) heW hsp.velocity.long_bound p hown.1 hp2 hsol
  obtain ⟨EO, hOi, hOb, hOc⟩ := fiber_coefficients D.azimuthOrder (R.long K).vorticity hsp.long_regular.2.1
    (ownSolid D.mesh.box K) heO hsp.vorticity.long_bound p hown.1 hp2 hsol
  intro S T
  have h := cross_coef_sum_le D.azimuthOrder hm S T (fun ι => bandProfile D ι v G p) EW EO hWi hOi _ _ hWb hOb
  simp only [hWc, hOc, curl_band_eq, vel_band_eq] at h
  exact h

open Classical in
theorem long_class_split (hCC : CellCalculusConditions D R) (K : Fin D.mesh.count) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (S T : Finset (ℤ × ℤ)) (uL uH : ℝ) (huL : 0 ≤ uL) (huH : 0 ≤ uH)
    (p : ℝ × ℝ)
    (hP : ∀ S' : Finset (ℤ × ℤ), ∑ ℓ ∈ T, ∑ c, ‖longCouplingVec D R K S' v G ℓ p c‖ ^ 2
        ≤ 2 * (R.long K).errVelocity ^ 2 * ∑ ι ∈ S', modeCurlSq D ι G p
          + 2 * (R.long K).errVorticity ^ 2 * ∑ ι ∈ S', modeVelSq D ι v p) :
    ∑ ℓ ∈ T, (if (R.long K).IsLowLabel ℓ then uL else uH) * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2
      ≤ ∑ ι ∈ S, 2 * (if (R.long K).IsLowLabel ι then uH else uL + uH)
          * ((R.long K).errVelocity ^ 2 * modeCurlSq D ι G p + (R.long K).errVorticity ^ 2 * modeVelSq D ι v p) := by
  set SH := S.filter (fun ι => ¬ (R.long K).IsLowLabel ι) with hSH
  have hlow : ∀ ℓ, (R.long K).IsLowLabel ℓ → ∀ c,
      longCouplingVec D R K S v G ℓ p c = longCouplingVec D R K SH v G ℓ p c := by
    intro ℓ hℓ c
    unfold longCouplingVec
    rw [hSH, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    by_cases hι : (R.long K).IsLowLabel ι
    · rw [if_neg (not_not.2 hι)]
      have hι' := hι
      unfold CellModelLong.IsLowLabel at hℓ hι'
      have hlab : |(ℓ - ι).1| ≤ 2 * ((R.long K).cut : ℤ) := by
        rw [Prod.fst_sub]
        obtain ⟨a1, a2⟩ := abs_le.1 hℓ
        obtain ⟨b1, b2⟩ := abs_le.1 hι'
        exact abs_le.2 ⟨by linarith, by linarith⟩
      obtain ⟨h1, h2, _, _⟩ := (hCC.model_split K).long_modes (ℓ - ι) hlab p
      have e1 : longVelocity D R K (ℓ - ι) p = 0 := funext h1
      have e2 : longVorticity D R K (ℓ - ι) p = 0 := funext h2
      rw [e1, e2, crossVec_zero_zero]
    · rw [if_pos hι]
  have hX0 : ∀ S' ℓ, 0 ≤ ∑ c, ‖longCouplingVec D R K S' v G ℓ p c‖ ^ 2 := fun _ _ =>
    Finset.sum_nonneg (fun _ _ => by positivity)
  have hterm : ∀ ℓ ∈ T, (if (R.long K).IsLowLabel ℓ then uL else uH) * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2
      ≤ uL * ∑ c, ‖longCouplingVec D R K SH v G ℓ p c‖ ^ 2 + uH * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2 := by
    intro ℓ _
    by_cases hℓ : (R.long K).IsLowLabel ℓ
    · rw [if_pos hℓ]
      have e : ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2 = ∑ c, ‖longCouplingVec D R K SH v G ℓ p c‖ ^ 2 :=
        Finset.sum_congr rfl (fun c _ => by rw [hlow ℓ hℓ c])
      rw [← e]
      nlinarith [mul_nonneg huH (hX0 S ℓ)]
    · rw [if_neg hℓ]
      nlinarith [mul_nonneg huL (hX0 SH ℓ)]
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  refine hsum.trans ?_
  refine le_trans (add_le_add (mul_le_mul_of_nonneg_left (hP SH) huL) (mul_le_mul_of_nonneg_left (hP S) huH))
    (le_of_eq ?_)
  rw [hSH, Finset.sum_filter, Finset.sum_filter]
  simp only [Finset.mul_sum, mul_add, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun ι _ => ?_)
  by_cases h : (R.long K).IsLowLabel ι
  · simp only [h, not_true_eq_false, if_false, if_true]
    ring
  · simp only [h, not_false_eq_true, if_false, if_true]
    ring

end Pointwise


section Rows

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem scaledRowGram_congr {V : Type} (K : Fin D.mesh.count) (B : CellBlocks V) (w s : ℤ × ℤ → ℝ)
    (hs : ∀ i, s (B.rowLabel i) * s (B.rowLabel i) * w (B.rowLabel i) = 1) :
    scaledRowGram D K B w = (diagonal (fun i => ((s (B.rowLabel i) : ℝ) : ℂ)))ᴴ * rowGram D K B
      * diagonal (fun i => ((s (B.rowLabel i) : ℝ) : ℂ)) := by
  ext i i'
  rw [diagonal_conjTranspose, mul_diagonal, diagonal_mul]
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_ofReal]
  unfold scaledRowGram
  by_cases h : B.rowLabel i = B.rowLabel i'
  · have hw : s (B.rowLabel i) * s (B.rowLabel i) = (w (B.rowLabel i))⁻¹ := eq_inv_of_mul_eq_one_left (hs i)
    rw [← h, div_eq_mul_inv, ← Complex.ofReal_inv, ← hw]
    push_cast
    ring
  · simp [rowGram, h]

theorem scaled_rows_le (A : AssemblyEntry D R) (hC : RowConditions D R A) (K : Fin D.mesh.count)
    (w : ℤ × ℤ → ℝ) (hw : ∀ ℓ ∈ D.mesh.tested K, 0 < w ℓ) (f : ℤ × ℤ → ℝ × ℝ → Fin 3 → ℂ)
    (hfm : ∀ ℓ ∈ D.mesh.tested K, ∀ a, AEStronglyMeasurable (fun p => f ℓ p a) (volume.restrict (D.mesh.box K).rect))
    (hfi : ∀ ℓ ∈ D.mesh.tested K, ∀ a, IntegrableOn (fun p => p.1 * ‖f ℓ p a‖ ^ 2) (D.mesh.box K).rect)
    (t : Fin (A.blocks K).rowCount → ℂ)
    (ht : ∀ i, t i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ a, f ((A.blocks K).rowLabel i) p a * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p a)) :
    inverseWeightedSq (scaledRowGram D K (A.blocks K) w) t
      ≤ ∑ ℓ ∈ D.mesh.tested K, w ℓ * ∫ p in (D.mesh.box K).rect, p.1 * ∑ a, ‖f ℓ p a‖ ^ 2 := by
  classical
  have hK : IsCellBox (D.mesh.box K) := hC.mesh_valid.box_valid K
  set s : ℤ × ℤ → ℝ := fun ℓ => (Real.sqrt (w ℓ))⁻¹ with hsdef
  have hsq : ∀ ℓ ∈ D.mesh.tested K, Real.sqrt (w ℓ) * s ℓ = 1 := fun ℓ hℓ =>
    mul_inv_cancel₀ (Real.sqrt_pos.2 (hw ℓ hℓ)).ne'
  have hsw : ∀ ℓ ∈ D.mesh.tested K, s ℓ * s ℓ * w ℓ = 1 := by
    intro ℓ hℓ
    have h1 := hsq ℓ hℓ
    have h2 : Real.sqrt (w ℓ) * Real.sqrt (w ℓ) = w ℓ := Real.mul_self_sqrt (hw ℓ hℓ).le
    rw [← h2]
    linear_combination (1 + Real.sqrt (w ℓ) * s ℓ) * h1
  have hsw' : ∀ i, s ((A.blocks K).rowLabel i) * s ((A.blocks K).rowLabel i) * w ((A.blocks K).rowLabel i) = 1 := fun i => hsw _ (hC.label_tested K i)
  have hpos : (scaledRowGram D K (A.blocks K) w).PosDef := by
    rw [scaledRowGram_congr D K (A.blocks K) w s hsw']
    refine (hC.gram_pos K).conjTranspose_mul_mul_same ?_
    intro x y hxy
    funext i
    have h := congrFun hxy i
    simp only [mulVec_diagonal] at h
    have hne : ((s ((A.blocks K).rowLabel i) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      rw [Complex.ofReal_eq_zero] at h0
      have := hsw' i
      rw [h0] at this
      simp at this
    exact mul_left_cancel₀ hne h
  unfold inverseWeightedSq
  have key := quadForm_inv_le_of_tests (A.blocks K).rowLabel (D.mesh.tested K) (hC.label_tested K) (fun p : ℝ × ℝ => p.1)
    (ae_rect_first_nonneg hK) continuous_fst.aestronglyMeasurable
    (fun i p a => ((s ((A.blocks K).rowLabel i) : ℝ) : ℂ) * rowTestValue D K (A.blocks K) i p a)
    (fun ℓ p a => ((Real.sqrt (w ℓ) : ℝ) : ℂ) * f ℓ p a)
    (fun i a => (continuous_const.mul (rowTestValue_continuous D K (A.blocks K) i a)).aestronglyMeasurable)
    (fun ℓ hℓ a => aestronglyMeasurable_const.mul (hfm ℓ hℓ a))
    (fun i a => integrableOn_rect_of_continuous
      (continuous_fst.mul ((continuous_const.mul (rowTestValue_continuous D K (A.blocks K) i a)).norm.pow 2)))
    ?_ _ ?_ hpos t ?_
  · refine le_trans key (le_of_eq (Finset.sum_congr rfl (fun ℓ hℓ => ?_)))
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hw ℓ hℓ).le,
      ← Finset.mul_sum]
    ring
  · intro ℓ hℓ a
    refine ((hfi ℓ hℓ a).const_mul (w ℓ)).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, Real.sq_sqrt (hw ℓ hℓ).le]
    ring
  · intro i i'
    unfold scaledRowGram rowGram
    split_ifs with h
    · have e1 : ∀ p : ℝ × ℝ, ((p.1 : ℝ) : ℂ) * ∑ c, ((s ((A.blocks K).rowLabel i') : ℝ) : ℂ) * rowTestValue D K (A.blocks K) i' p c
            * (starRingEnd ℂ) (((s ((A.blocks K).rowLabel i) : ℝ) : ℂ) * rowTestValue D K (A.blocks K) i p c)
          = ((s ((A.blocks K).rowLabel i) * s ((A.blocks K).rowLabel i) : ℝ) : ℂ) * ((p.1 : ℂ) * ∑ c, testAt D K ((A.blocks K).rowLabel i) ((A.blocks K).rowTest i') c p
            * (starRingEnd ℂ) (testAt D K ((A.blocks K).rowLabel i) ((A.blocks K).rowTest i) c p)) := by
        intro p
        simp only [rowTestValue, rowTestPoly, testAt, map_mul, Complex.conj_ofReal, Finset.mul_sum]
        rw [← h]
        refine Finset.sum_congr rfl (fun c _ => ?_)
        push_cast
        ring
      rw [integral_congr_ae (Filter.Eventually.of_forall e1), integral_const_mul]
      have hw1 : s ((A.blocks K).rowLabel i) * s ((A.blocks K).rowLabel i) = (w ((A.blocks K).rowLabel i))⁻¹ := eq_inv_of_mul_eq_one_left (hsw' i)
      rw [hw1, div_eq_mul_inv, mul_comm, Complex.ofReal_inv]
    · simp
  · intro i
    rw [ht i]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    have hone : ((Real.sqrt (w ((A.blocks K).rowLabel i)) : ℝ) : ℂ) * ((s ((A.blocks K).rowLabel i) : ℝ) : ℂ) = 1 := by
      rw [← Complex.ofReal_mul, hsq _ (hC.label_tested K i), Complex.ofReal_one]
    simp only [map_mul, Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl (fun c _ => ?_)
    linear_combination (-(f ((A.blocks K).rowLabel i) p c * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c))) * hone

end Rows

end LongPart

end Internal

open Coupling CellCert.CellAnalysis CellCert.CellFormula CellCalculus _root_.Breakdown.CertCell.Assembly.Internal
  _root_.Breakdown.CertCell.Assembly.Internal.LongPart

theorem longPieceBound_holds : LongPieceBoundHolds := by
  intro k C nE nM D R A P states hstates hReg hTF hC hF K q v G H g κ F Pg ht
  have hK := hC.mesh_valid.box_valid K
  have hm : 1 ≤ D.azimuthOrder := hReg.field.azimuth_pos
  have hCC := hF.cell_conditions
  have hsp := hCC.model_split K
  obtain ⟨_, _, huL, huH, _⟩ := hF.costs_pos K
  set S := D.mesh.resolved K ∪ D.mesh.band K ∪ deactSources D K (P.potential K) with hS
  set eW := (R.long K).errVelocity with heWdef
  set eO := (R.long K).errVorticity with heOdef
  have hae := long_parseval D R hCC hC.mesh_valid hm K v G
  have hbpm : ∀ ι j, AEStronglyMeasurable (fun p => bandProfile D ι v G p j) (volume.restrict (D.mesh.box K).rect) :=
    fun ι j => ((hTF.1 K q v G H g κ F Pg ht).1 ι).1 j
  have hLm : ∀ α a, AEStronglyMeasurable (fun p => longVelocity D R K α p a) (volume.restrict (D.mesh.box K).rect) :=
    fun α a => label_coefficient_measurable D.azimuthOrder (R.long K).velocity hsp.long_regular.1 D.mesh
      hC.mesh_valid K α a
  have hOm : ∀ α a, AEStronglyMeasurable (fun p => longVorticity D R K α p a) (volume.restrict (D.mesh.box K).rect) :=
    fun α a => label_coefficient_measurable D.azimuthOrder (R.long K).vorticity hsp.long_regular.2.1 D.mesh
      hC.mesh_valid K α a
  have hcs := fun ι => (profile_integrable D hTF hK ht ι).2.1
  have hvs := fun ι => (profile_integrable D hTF hK ht ι).1
  set Bd : Finset (ℤ × ℤ) → ℝ × ℝ → ℝ := fun S' p =>
    2 * eW ^ 2 * ∑ ι ∈ S', modeCurlSq D ι G p + 2 * eO ^ 2 * ∑ ι ∈ S', modeVelSq D ι v p with hBd
  have hBdi : ∀ S', IntegrableOn (fun p => p.1 * Bd S' p) (D.mesh.box K).rect := by
    intro S'
    have h : IntegrableOn (fun p => 2 * eW ^ 2 * ∑ ι ∈ S', p.1 * modeCurlSq D ι G p
        + 2 * eO ^ 2 * ∑ ι ∈ S', p.1 * modeVelSq D ι v p) (D.mesh.box K).rect :=
      ((integrable_finsetSum _ (fun ι _ => hcs ι)).const_mul _).add
        ((integrable_finsetSum _ (fun ι _ => hvs ι)).const_mul _)
    refine h.congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [hBd, ← Finset.mul_sum]
    ring
  have hfm : ∀ S' ℓ c, AEStronglyMeasurable (fun p => longCouplingVec D R K S' v G ℓ p c)
      (volume.restrict (D.mesh.box K).rect) := by
    intro S' ℓ c
    unfold longCouplingVec
    exact Finset.aestronglyMeasurable_fun_sum _ (fun ι' _ => crossVec_aesm (hbpm ι') (hLm _) (hOm _) c)
  have hXle : ∀ ℓ, ∀ᵐ p ∂(volume.restrict (D.mesh.box K).rect),
      ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2 ≤ Bd S p := by
    intro ℓ
    filter_upwards [hae] with p hp
    have h := hp S {ℓ}
    rw [Finset.sum_singleton] at h
    exact h
  have hfi : ∀ ℓ c, IntegrableOn (fun p => p.1 * ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2) (D.mesh.box K).rect := by
    intro ℓ c
    refine Integrable.mono' (hBdi S) (continuous_fst.aestronglyMeasurable.mul ((hfm S ℓ c).norm.pow 2)) ?_
    filter_upwards [ae_restrict_mem (rect_measurableSet (D.mesh.box K)), hXle ℓ] with p hp hpl
    have hp0 := rect_first_nonneg hK hp
    rw [Real.norm_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left (le_trans ?_ hpl) hp0
    exact Finset.single_le_sum (f := fun c => ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ c)
  have hterm : ∀ i ι', IntegrableOn (fun p => (p.1 : ℂ) * ∑ c, crossVec (bandProfile D ι' v G p)
      (longVelocity D R K ((A.blocks K).rowLabel i - ι') p) (longVorticity D R K ((A.blocks K).rowLabel i - ι') p) c
      * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c)) (D.mesh.box K).rect := by
    intro i ι'
    refine weighted_pair_integrable hK (fun c => crossVec_aesm (hbpm ι') (hLm _) (hOm _) c) (hBdi {ι'}) ?_
      (fun c => rowTestValue_continuous D K (A.blocks K) i c)
    filter_upwards [hae] with p hp
    have h := hp {ι'} {(A.blocks K).rowLabel i}
    simpa only [Finset.sum_singleton, longCouplingVec, hBd] using h
  have heq : ∀ i, longPiece D R K (A.blocks K) (P.potential K) v G i = ∫ p in (D.mesh.box K).rect, (p.1 : ℂ) *
      ∑ c, longCouplingVec D R K S v G ((A.blocks K).rowLabel i) p c
        * (starRingEnd ℂ) (rowTestValue D K (A.blocks K) i p c) := by
    intro i
    unfold longPiece
    simp only [crossTest_pairing]
    rw [← integral_finsetSum _ (fun ι' _ => hterm i ι')]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    simp only [longCouplingVec, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_comm
  have hcost : ∀ ℓ ∈ D.mesh.tested K, 0 < longRowCost D R K (A.blocks K) ℓ := by
    intro ℓ _
    unfold longRowCost
    split_ifs
    · exact huL
    · exact huH
  have hb := scaled_rows_le D R A hC K (longRowCost D R K (A.blocks K)) hcost (longCouplingVec D R K S v G)
    (fun ℓ _ c => hfm S ℓ c) (fun ℓ _ c => hfi ℓ c) _ heq
  have hsumi : ∀ ℓ, IntegrableOn (fun p => p.1 * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2)
      (D.mesh.box K).rect := by
    intro ℓ
    simp only [Finset.mul_sum]
    exact integrable_finsetSum _ (fun c _ => hfi ℓ c)
  have hWterm : ∀ ι, IntegrableOn (fun p => 2 * longSourceCost D R K (A.blocks K) ι
      * (p.1 * (eW ^ 2 * modeCurlSq D ι G p + eO ^ 2 * modeVelSq D ι v p))) (D.mesh.box K).rect := by
    intro ι
    refine ((((hcs ι).const_mul (eW ^ 2)).add ((hvs ι).const_mul (eO ^ 2))).const_mul
      (2 * longSourceCost D R K (A.blocks K) ι)).congr (Filter.Eventually.of_forall (fun p => ?_))
    simp only [Pi.add_apply]
    ring
  have h1 : ∑ ℓ ∈ D.mesh.tested K, longRowCost D R K (A.blocks K) ℓ
        * ∫ p in (D.mesh.box K).rect, p.1 * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2
      ≤ ∑ ι ∈ S, ∫ p in (D.mesh.box K).rect, 2 * longSourceCost D R K (A.blocks K) ι
          * (p.1 * (eW ^ 2 * modeCurlSq D ι G p + eO ^ 2 * modeVelSq D ι v p)) := by
    simp only [← integral_const_mul]
    rw [← integral_finsetSum _ (fun ℓ _ => (hsumi ℓ).const_mul _), ← integral_finsetSum _ (fun ι _ => hWterm ι)]
    refine integral_mono_ae (integrable_finsetSum _ (fun ℓ _ => (hsumi ℓ).const_mul _))
      (integrable_finsetSum _ (fun ι _ => hWterm ι)) ?_
    filter_upwards [hae, ae_restrict_mem (rect_measurableSet (D.mesh.box K))] with p hp hpr
    have hp0 := rect_first_nonneg hK hpr
    have hcl := long_class_split D R hCC K v G S (D.mesh.tested K) _ _ huL.le huH.le p
      (fun S' => hp S' (D.mesh.tested K))
    have e1 : ∑ ℓ ∈ D.mesh.tested K, longRowCost D R K (A.blocks K) ℓ
          * (p.1 * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2)
        = p.1 * ∑ ℓ ∈ D.mesh.tested K, longRowCost D R K (A.blocks K) ℓ
          * ∑ c, ‖longCouplingVec D R K S v G ℓ p c‖ ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ℓ _ => ?_)
      ring
    have e2 : ∑ ι ∈ S, 2 * longSourceCost D R K (A.blocks K) ι
          * (p.1 * (eW ^ 2 * modeCurlSq D ι G p + eO ^ 2 * modeVelSq D ι v p))
        = p.1 * ∑ ι ∈ S, 2 * longSourceCost D R K (A.blocks K) ι
          * (eW ^ 2 * modeCurlSq D ι G p + eO ^ 2 * modeVelSq D ι v p) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun ι _ => ?_)
      ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left hcl hp0
  have h2 : ∑ ι ∈ S, ∫ p in (D.mesh.box K).rect, 2 * longSourceCost D R K (A.blocks K) ι
          * (p.1 * (eW ^ 2 * modeCurlSq D ι G p + eO ^ 2 * modeVelSq D ι v p))
      = longAllowance D R K (A.blocks K) (D.mesh.resolved K) v G + longAllowance D R K (A.blocks K) (D.mesh.band K) v G
        + longAllowance D R K (A.blocks K) (deactSources D K (P.potential K)) v G := by
    unfold longAllowance
    have hd1 : Disjoint (D.mesh.resolved K) (D.mesh.band K) := hC.mesh_valid.band_apart K
    have hd2 : Disjoint (D.mesh.resolved K ∪ D.mesh.band K) (deactSources D K (P.potential K)) := by
      rw [Finset.disjoint_left]
      intro ι h1 h2
      unfold deactSources at h2
      rw [Finset.mem_filter] at h2
      rcases Finset.mem_union.1 h1 with h | h
      · exact h2.2.1 h
      · exact h2.2.2 h
    rw [← Finset.sum_union hd1, ← Finset.sum_union hd2]
    refine Finset.sum_congr rfl (fun ι _ => ?_)
    rw [← integral_const_mul]
  calc _ ≤ _ := hb
    _ ≤ _ := h1
    _ = _ := h2

end Assembly

end CertCell

end Breakdown
