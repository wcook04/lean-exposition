import Breakdown.CertCell.InstanceStatements
import Breakdown.CertCell.InstanceGeneratorForm
import Breakdown.CertCell.InstanceModeMean
import Breakdown.FracCell.CylIntegral

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Instance

open Breakdown Breakdown.CertCell
open Breakdown.CellCert.CellAnalysis (CellBox IsCellBox cylRadius cylHeight radialUnit angularUnit axialUnit)

namespace Internal.PairingFormula

theorem harm_neg (m : ℕ) (ι : ℤ × ℤ) : labelHarmonic m (-ι) = -labelHarmonic m ι := by
  refine Prod.ext ?_ ?_ <;> simp [labelHarmonic, labelTime, labelAzimuth] <;> ring

theorem harm_eq_iff {m : ℕ} (hm : 0 < m) (ι κ : ℤ × ℤ) :
    labelHarmonic m ι = labelHarmonic m κ ↔ ι = κ := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  have h2 : ι.1 * (m : ℤ) = κ.1 * m := congrArg Prod.snd h
  have h1 : 2 * ι.2 - ι.1 = 2 * κ.2 - κ.1 := congrArg Prod.fst h
  have e1 : ι.1 = κ.1 := mul_right_cancel₀ (by exact_mod_cast hm.ne') h2
  exact Prod.ext e1 (by omega)

theorem harm_eq_neg_iff {m : ℕ} (hm : 0 < m) (ι κ : ℤ × ℤ) :
    labelHarmonic m ι = -labelHarmonic m κ ↔ ι = -κ := by
  rw [← harm_neg, harm_eq_iff hm]

theorem flip_flip (ι : ℤ × ℤ) : labelFlip (labelFlip ι) = ι := by
  refine Prod.ext ?_ ?_ <;> simp [labelFlip]

theorem flip_neg (ι : ℤ × ℤ) : labelFlip (-ι) = -labelFlip ι := by
  refine Prod.ext ?_ ?_ <;> simp [labelFlip] <;> ring

theorem flip_eq_iff (ι κ : ℤ × ℤ) : labelFlip ι = labelFlip κ ↔ ι = κ :=
  ⟨fun h => by rw [← flip_flip ι, h, flip_flip], fun h => h ▸ rfl⟩

theorem harm_flip_eq_iff {m : ℕ} (hm : 0 < m) (ι κ : ℤ × ℤ) :
    labelHarmonic m (labelFlip ι) = labelHarmonic m (labelFlip κ) ↔ ι = κ := by
  rw [harm_eq_iff hm, flip_eq_iff]

theorem harm_flip_eq_neg_iff {m : ℕ} (hm : 0 < m) (ι κ : ℤ × ℤ) :
    labelHarmonic m (labelFlip ι) = -labelHarmonic m (labelFlip κ) ↔ ι = -κ := by
  rw [harm_eq_neg_iff hm, ← flip_neg, flip_eq_iff]

theorem frameUnit_eq (θ : ℝ) (c : Fin 3) :
    frameUnit θ c = CellCert.Spectral.Internal.SpectralBlocksMode.frameAt c θ := by
  fin_cases c <;> rfl

theorem frameUnit_inner (θ : ℝ) (c c' : Fin 3) :
    inner ℝ (frameUnit θ c) (frameUnit θ c') = if c = c' then (1 : ℝ) else 0 := by
  rw [frameUnit_eq, frameUnit_eq]
  exact CellCert.Spectral.Internal.SpectralBlocksMode.frame_inner c c' θ

theorem inner_frame_sum (A B : Fin 3 → ℝ) (θ : ℝ) :
    inner ℝ (∑ c : Fin 3, A c • frameUnit θ c) (∑ c : Fin 3, B c • frameUnit θ c) =
      ∑ c : Fin 3, A c * B c := by
  simp only [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, frameUnit_inner]
  simp [Fin.sum_univ_three]
  ring

open Classical in
def unitOn {α : Type*} (S : Set α) (x : α) : ℝ := if x ∈ S then 1 else 0

variable {count rowCount : ℕ}

def coefAt (R : RowValues count rowCount) (box : Fin count → CellBox) (m : ℕ) (a : Fin rowCount)
    (σ : ℝ) (y : Space) (c : Fin 3) : ℝ :=
  (labelPhase m (if 0 ≤ y 2 then R.labelOf a else labelFlip (R.labelOf a)) σ (pointAngle y) *
    (if 0 ≤ y 2 then rowPartFactor (R.realPart a) * R.testValue box a c (pointPlane y)
      else (frameSign c : ℂ) * rowPartFactor (R.realPart a) *
        R.testValue box a c ((pointPlane y).1, -(pointPlane y).2))).re

def GenShape (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (a : Fin rowCount) : Prop :=
  ∀ σ y, R.generatorField M.box m a σ y = Set.indicator (M.box (R.cellOf a)).solid
    (fun y => ∑ c : Fin 3, coefAt R M.box m a σ y c • frameUnit (pointAngle y) c) y

theorem inner_gen {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {a b : Fin rowCount}
    (hA : GenShape M R m a) (hB : GenShape M R m b) (σ : ℝ) (y : Space) :
    inner ℝ (R.generatorField M.box m a σ y) (R.generatorField M.box m b σ y) =
      unitOn (M.box (R.cellOf a)).solid y * unitOn (M.box (R.cellOf b)).solid y *
        ∑ c : Fin 3, coefAt R M.box m a σ y c * coefAt R M.box m b σ y c := by
  rw [hA, hB]
  unfold unitOn
  by_cases ha : y ∈ (M.box (R.cellOf a)).solid <;> by_cases hb : y ∈ (M.box (R.cellOf b)).solid <;>
    simp [ha, hb, inner_frame_sum]

theorem measurable_pointAngle : Measurable pointAngle := by
  unfold pointAngle; fun_prop

theorem continuous_pointPlane : Continuous pointPlane := by
  unfold pointPlane; fun_prop

theorem continuous_testValue (R : RowValues count rowCount) (box : Fin count → CellBox) (a : Fin rowCount)
    (c : Fin 3) : Continuous (R.testValue box a c) := by
  unfold RowValues.testValue CellPoly.eval CellBox.refR CellBox.refZ; fun_prop

theorem measurableSet_solid (K : CellBox) : MeasurableSet K.solid := by
  have hr : Measurable cylRadius := by unfold cylRadius; fun_prop
  have hz : Measurable fun y : Space => |cylHeight y| := by unfold cylHeight; fun_prop
  exact (measurableSet_le measurable_const hr).inter ((measurableSet_le hr measurable_const).inter
    ((measurableSet_le measurable_const hz).inter (measurableSet_le hz measurable_const)))

theorem measurable_unitOn {α : Type*} [MeasurableSpace α] {S : Set α} (hS : MeasurableSet S) :
    Measurable (unitOn S) := by
  unfold unitOn
  exact Measurable.ite hS measurable_const measurable_const

theorem coefAt_eq_ite (R : RowValues count rowCount) (box : Fin count → CellBox) (m : ℕ) (a : Fin rowCount)
    (σ : ℝ) (y : Space) (c : Fin 3) : coefAt R box m a σ y c = if 0 ≤ y 2 then
      (labelPhase m (R.labelOf a) σ (pointAngle y) *
        (rowPartFactor (R.realPart a) * R.testValue box a c (pointPlane y))).re
    else (labelPhase m (labelFlip (R.labelOf a)) σ (pointAngle y) *
        ((frameSign c : ℂ) * rowPartFactor (R.realPart a) *
          R.testValue box a c ((pointPlane y).1, -(pointPlane y).2))).re := by
  unfold coefAt; split_ifs <;> rfl

theorem measurable_coefAt (R : RowValues count rowCount) (box : Fin count → CellBox) (m : ℕ)
    (a : Fin rowCount) (c : Fin 3) : Measurable (fun q : ℝ × Space => coefAt R box m a q.1 q.2 c) := by
  simp only [coefAt_eq_ite]
  have hθ := measurable_pointAngle
  have hp := continuous_pointPlane
  have ht := continuous_testValue R box a c
  refine Measurable.ite ?_ ?_ ?_
  · exact measurableSet_le measurable_const (by fun_prop)
  · unfold labelPhase; fun_prop
  · unfold labelPhase; fun_prop

theorem norm_rowPartFactor (b : Bool) : ‖rowPartFactor b‖ = 1 := by
  cases b <;> simp [rowPartFactor]

theorem norm_frameSign (c : Fin 3) : ‖((frameSign c : ℝ) : ℂ)‖ = 1 := by
  unfold frameSign; split_ifs <;> simp

theorem frameSign_mul_self (c : Fin 3) : ((frameSign c : ℝ) : ℂ) * (frameSign c : ℂ) = 1 := by
  unfold frameSign; split_ifs <;> simp

theorem frameSign_pair (c : Fin 3) (x y x' y' : ℂ) :
    (frameSign c : ℂ) * x * y * ((frameSign c : ℂ) * x' * y') = x * x' * (y * y') := by
  linear_combination (x * x' * (y * y')) * frameSign_mul_self c

theorem norm_labelPhase (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) : ‖labelPhase m ι σ θ‖ = 1 := by
  unfold labelPhase; exact Complex.norm_exp_ofReal_mul_I _

theorem exists_testBound (R : RowValues count rowCount) (box : Fin count → CellBox) (a : Fin rowCount) :
    ∃ C, 0 ≤ C ∧ ∀ c, ∀ p ∈ (box (R.cellOf a)).rect, ‖R.testValue box a c p‖ ≤ C := by
  have hc : IsCompact (box (R.cellOf a)).rect := isCompact_Icc.prod isCompact_Icc
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn (f := fun p => ∑ c : Fin 3, ‖R.testValue box a c p‖)
    (continuous_finsetSum _ fun c _ => (continuous_testValue R box a c).norm).continuousOn
  refine ⟨max C 0, le_max_right _ _, fun c p hp => ?_⟩
  have h1 := hC p hp
  rw [Real.norm_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)] at h1
  exact ((Finset.single_le_sum (f := fun c => ‖R.testValue box a c p‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_univ c)).trans h1).trans (le_max_left _ _)

theorem abs_coefAt_le {R : RowValues count rowCount} {box : Fin count → CellBox} {m : ℕ} {a : Fin rowCount}
    {C : ℝ} (hC : ∀ c, ∀ p ∈ (box (R.cellOf a)).rect, ‖R.testValue box a c p‖ ≤ C) {y : Space}
    (hy : y ∈ (box (R.cellOf a)).solid) (σ : ℝ) (c : Fin 3) : |coefAt R box m a σ y c| ≤ C := by
  obtain ⟨h1, h2, h3, h4⟩ := hy
  unfold cylHeight at h3 h4
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, norm_labelPhase, one_mul]
  split_ifs with h
  · rw [norm_mul, norm_rowPartFactor, one_mul]
    rw [abs_of_nonneg h] at h3 h4
    exact hC c _ (Set.mem_prod.2 ⟨Set.mem_Icc.2 ⟨h1, h2⟩, Set.mem_Icc.2 ⟨h3, h4⟩⟩)
  · rw [norm_mul, norm_mul, norm_frameSign, norm_rowPartFactor, one_mul, one_mul]
    rw [abs_of_neg (not_le.1 h)] at h3 h4
    exact hC c _ (Set.mem_prod.2 ⟨Set.mem_Icc.2 ⟨h1, h2⟩, Set.mem_Icc.2 ⟨h3, h4⟩⟩)

theorem solid_bounded (K : CellBox) : Bornology.IsBounded K.solid := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨Real.sqrt (K.r₂ ^ 2 + K.z₂ ^ 2), fun y hy => ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hy
  rw [Metric.mem_closedBall, dist_zero_right]
  have hn : ‖y‖ ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq, Fin.sum_univ_three]
    simp [Real.norm_eq_abs, sq_abs]
  have hr : y 0 ^ 2 + y 1 ^ 2 ≤ K.r₂ ^ 2 := by
    have h0 : 0 ≤ cylRadius y := Real.sqrt_nonneg _
    have := pow_le_pow_left₀ h0 h2 2
    rwa [cylRadius, Real.sq_sqrt (by positivity)] at this
  have hz : y 2 ^ 2 ≤ K.z₂ ^ 2 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h4 2
    rwa [cylHeight, sq_abs] at this
  have := Real.abs_le_sqrt (show ‖y‖ ^ 2 ≤ K.r₂ ^ 2 + K.z₂ ^ 2 by rw [hn]; linarith)
  rwa [abs_of_nonneg (norm_nonneg _)] at this

theorem integrable_pairing {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {a b : Fin rowCount}
    (hA : GenShape M R m a) (hB : GenShape M R m b) :
    Integrable (Function.uncurry fun σ y =>
        inner ℝ (R.generatorField M.box m a σ y) (R.generatorField M.box m b σ y))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  obtain ⟨Ca, hCa0, hCa⟩ := exists_testBound R M.box a
  obtain ⟨Cb, hCb0, hCb⟩ := exists_testBound R M.box b
  have hfun : (Function.uncurry fun σ y =>
      inner ℝ (R.generatorField M.box m a σ y) (R.generatorField M.box m b σ y)) =
      fun q : ℝ × Space => unitOn (M.box (R.cellOf a)).solid q.2 * unitOn (M.box (R.cellOf b)).solid q.2 *
        ∑ c : Fin 3, coefAt R M.box m a q.1 q.2 c * coefAt R M.box m b q.1 q.2 c := by
    funext q; exact inner_gen hA hB q.1 q.2
  rw [hfun]
  have hSa := measurableSet_solid (M.box (R.cellOf a))
  have hSb := measurableSet_solid (M.box (R.cellOf b))
  have hmeas : Measurable fun q : ℝ × Space => unitOn (M.box (R.cellOf a)).solid q.2 *
      unitOn (M.box (R.cellOf b)).solid q.2 *
        ∑ c : Fin 3, coefAt R M.box m a q.1 q.2 c * coefAt R M.box m b q.1 q.2 c :=
    (((measurable_unitOn hSa).comp measurable_snd).mul ((measurable_unitOn hSb).comp measurable_snd)).mul
      (Finset.measurable_sum _ fun c _ => (measurable_coefAt R M.box m a c).mul (measurable_coefAt R M.box m b c))
  have hg : Integrable (fun q : ℝ × Space => (fun _ : ℝ => (1 : ℝ)) q.1 *
      (M.box (R.cellOf a)).solid.indicator (fun _ => ∑ _c : Fin 3, Ca * Cb) q.2)
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
    refine Integrable.mul_prod (f := fun _ : ℝ => (1 : ℝ))
      (g := (M.box (R.cellOf a)).solid.indicator (fun _ => ∑ _c : Fin 3, Ca * Cb)) ?_ ?_
    · exact continuous_const.integrableOn_Icc
    · exact (integrable_indicator_iff hSa).2 (integrableOn_const ((solid_bounded _).measure_lt_top).ne)
  refine hg.mono' hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  have hD : 0 ≤ ∑ _c : Fin 3, Ca * Cb := Finset.sum_nonneg fun _ _ => mul_nonneg hCa0 hCb0
  simp only [one_mul, Real.norm_eq_abs]
  unfold unitOn
  by_cases ha : q.2 ∈ (M.box (R.cellOf a)).solid <;> by_cases hb : q.2 ∈ (M.box (R.cellOf b)).solid
  · simp only [ha, hb, ↓reduceIte, one_mul, Set.indicator_of_mem ha]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [abs_mul]
    exact mul_le_mul (abs_coefAt_le hCa ha _ _) (abs_coefAt_le hCb hb _ _) (abs_nonneg _) hCa0
  all_goals simp only [ha, hb, ↓reduceIte, mul_zero, zero_mul, abs_zero]
  all_goals exact Set.indicator_nonneg (fun _ _ => hD) _

theorem periodPairing_cyl {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {a b : Fin rowCount}
    (hA : GenShape M R m a) (hB : GenShape M R m b) :
    periodPairing (R.generatorField M.box m a) (R.generatorField M.box m b) =
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), q.1 * ∫ θ in (-Real.pi)..Real.pi,
        ∫ σ in Set.Icc (0 : ℝ) 1,
          inner ℝ (R.generatorField M.box m a σ (CellCert.Spectral.cylPoint q.1 θ q.2))
            (R.generatorField M.box m b σ (CellCert.Spectral.cylPoint q.1 θ q.2)) := by
  have hI := integrable_pairing hA hB
  unfold periodPairing
  rw [integral_integral_swap hI]
  exact CellCert.Spectral.cylIntegral _ hI.integral_prod_right

def sideLabel (z : ℝ) (ι : ℤ × ℤ) : ℤ × ℤ := if 0 ≤ z then ι else labelFlip ι

def sideValue (R : RowValues count rowCount) (box : Fin count → CellBox) (a : Fin rowCount) (c : Fin 3)
    (r z : ℝ) : ℂ :=
  if 0 ≤ z then rowPartFactor (R.realPart a) * R.testValue box a c (r, z)
  else (frameSign c : ℂ) * rowPartFactor (R.realPart a) * R.testValue box a c (r, -z)

def phaseProd (m : ℕ) (ι κ : ℤ × ℤ) (A B : ℂ) (σ θ : ℝ) : ℝ :=
  (labelPhase m ι σ θ * A).re * (labelPhase m κ σ θ * B).re

def pairDensity (R : RowValues count rowCount) (box : Fin count → CellBox) (a b : Fin rowCount)
    (p : ℝ × ℝ) : ℂ :=
  (if R.labelOf a = R.labelOf b then
      rowPartFactor (R.realPart a) * starRingEnd ℂ (rowPartFactor (R.realPart b))
        * ∑ c : Fin 3, R.testValue box a c p * starRingEnd ℂ (R.testValue box b c p)
    else 0)
  + (if R.labelOf a = -R.labelOf b then
      rowPartFactor (R.realPart a) * rowPartFactor (R.realPart b)
        * ∑ c : Fin 3, R.testValue box a c p * R.testValue box b c p
    else 0)

def radialDensity (R : RowValues count rowCount) (box : Fin count → CellBox) (a b : Fin rowCount)
    (p : ℝ × ℝ) : ℝ :=
  p.1 * (unitOn (box (R.cellOf a)).rect p * unitOn (box (R.cellOf b)).rect p * (pairDensity R box a b p).re)

theorem cyl_mem_solid (K : CellBox) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    CellCert.Spectral.cylPoint r θ z ∈ K.solid ↔ (r, |z|) ∈ K.rect := by
  have h1 : Breakdown.CellCert.CellAnalysis.cylRadius (CellCert.Spectral.cylPoint r θ z) = r :=
    CellCert.Spectral.Internal.SpectralBlocksMode.radial_cyl hr θ z
  have h2 : Breakdown.CellCert.CellAnalysis.cylHeight (CellCert.Spectral.cylPoint r θ z) = z :=
    CellCert.Spectral.Internal.SpectralBlocksMode.cyl2 r θ z
  simp only [CellBox.solid, CellBox.rect, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_Icc, h1, h2, and_assoc]

theorem unitOn_cyl (K : CellBox) {r : ℝ} (hr : 0 < r) (θ z : ℝ) :
    unitOn K.solid (CellCert.Spectral.cylPoint r θ z) = unitOn K.rect (r, |z|) := by
  unfold unitOn
  by_cases h : (r, |z|) ∈ K.rect
  · rw [if_pos ((cyl_mem_solid K hr θ z).2 h), if_pos h]
  · rw [if_neg (mt (cyl_mem_solid K hr θ z).1 h), if_neg h]

theorem pairing_at_cyl {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {a b : Fin rowCount}
    (hA : GenShape M R m a) (hB : GenShape M R m b) {r : ℝ} (hr : 0 < r) {θ : ℝ}
    (hθ : θ ∈ Set.Ioc (-Real.pi) Real.pi) (z σ : ℝ) :
    inner ℝ (R.generatorField M.box m a σ (CellCert.Spectral.cylPoint r θ z))
        (R.generatorField M.box m b σ (CellCert.Spectral.cylPoint r θ z)) =
      unitOn (M.box (R.cellOf a)).rect (r, |z|) * unitOn (M.box (R.cellOf b)).rect (r, |z|) *
        ∑ c : Fin 3, phaseProd m (sideLabel z (R.labelOf a)) (sideLabel z (R.labelOf b))
          (sideValue R M.box a c r z) (sideValue R M.box b c r z) σ θ := by
  have hang : pointAngle (CellCert.Spectral.cylPoint r θ z) = θ := by
    have := CellCert.Spectral.Internal.SpectralBlocksMode.angle_cyl hr hθ z
    rw [CellCert.Spectral.angleCoord, Complex.mk_eq_add_mul_I] at this
    exact this
  have hpl : pointPlane (CellCert.Spectral.cylPoint r θ z) = (r, z) :=
    Prod.ext (CellCert.Spectral.Internal.SpectralBlocksMode.radial_cyl hr θ z)
      (CellCert.Spectral.Internal.SpectralBlocksMode.cyl2 r θ z)
  have h2 : (CellCert.Spectral.cylPoint r θ z) 2 = z := CellCert.Spectral.Internal.SpectralBlocksMode.cyl2 r θ z
  rw [inner_gen hA hB, unitOn_cyl _ hr, unitOn_cyl _ hr]
  simp only [coefAt, hang, hpl, h2, phaseProd, sideLabel, sideValue]

theorem labelPhase_add_two_pi (m : ℕ) (ι : ℤ × ℤ) (σ θ : ℝ) :
    labelPhase m ι σ (θ + 2 * Real.pi) = labelPhase m ι σ θ := by
  unfold labelPhase
  have e : ((((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * (θ + 2 * Real.pi)) : ℝ) : ℂ)
      * Complex.I) = (((2 * Real.pi * (labelTime ι : ℝ) * σ + (labelAzimuth m ι : ℝ) * θ : ℝ) : ℂ)
        * Complex.I) + (labelAzimuth m ι : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem continuous_phaseProd (m : ℕ) (ι κ : ℤ × ℤ) (A B : ℂ) :
    Continuous (Function.uncurry (phaseProd m ι κ A B)) := by
  change Continuous fun x : ℝ × ℝ => phaseProd m ι κ A B x.1 x.2
  unfold phaseProd labelPhase; fun_prop

theorem slice_mean (hmean : ∀ (ξ ζ : ℤ × ℤ) (A B : ℂ),
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
          (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
        Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re)
    (m : ℕ) (ι κ : ℤ × ℤ) (A B : ℂ) :
    ∫ θ in (-Real.pi)..Real.pi, ∫ σ in Set.Icc (0 : ℝ) 1, phaseProd m ι κ A B σ θ =
      Real.pi * ((if labelHarmonic m ι = labelHarmonic m κ then A * starRingEnd ℂ B else 0) +
        (if labelHarmonic m ι = -labelHarmonic m κ then A * B else 0)).re := by
  have hc := continuous_phaseProd m ι κ A B
  have hper : Function.Periodic (fun θ => ∫ σ in Set.Icc (0 : ℝ) 1, phaseProd m ι κ A B σ θ)
      (2 * Real.pi) := by
    intro θ
    simp only [phaseProd, labelPhase_add_two_pi]
  have h1 := hper.intervalIntegral_add_eq (-Real.pi) 0
  rw [show -Real.pi + 2 * Real.pi = Real.pi by ring, zero_add] at h1
  rw [h1, intervalIntegral_integral_swap (f := fun θ σ => phaseProd m ι κ A B σ θ)]
  · exact hmean (labelHarmonic m ι) (labelHarmonic m κ) A B
  · rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    have hc' : Continuous (Function.uncurry fun θ σ => phaseProd m ι κ A B σ θ) := hc.comp continuous_swap
    exact (hc'.continuousOn.integrableOn_compact (isCompact_uIcc.prod isCompact_Icc)).mono_set
      (Set.prod_mono Set.uIoc_subset_uIcc subset_rfl)

theorem slice_integral (hmean : ∀ (ξ ζ : ℤ × ℤ) (A B : ℂ),
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
          (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
        Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re)
    (s : ℝ) (m : ℕ) (ι κ : ℤ × ℤ) (A B : Fin 3 → ℂ) :
    ∫ θ in (-Real.pi)..Real.pi, ∫ σ in Set.Icc (0 : ℝ) 1, s * ∑ c : Fin 3, phaseProd m ι κ (A c) (B c) σ θ =
      s * ∑ c : Fin 3, Real.pi *
        ((if labelHarmonic m ι = labelHarmonic m κ then A c * starRingEnd ℂ (B c) else 0) +
          (if labelHarmonic m ι = -labelHarmonic m κ then A c * B c else 0)).re := by
  have hc := fun c => continuous_phaseProd m ι κ (A c) (B c)
  have hin : ∀ θ, ∫ σ in Set.Icc (0 : ℝ) 1, s * ∑ c : Fin 3, phaseProd m ι κ (A c) (B c) σ θ =
      s * ∑ c : Fin 3, ∫ σ in Set.Icc (0 : ℝ) 1, phaseProd m ι κ (A c) (B c) σ θ := by
    intro θ
    rw [integral_const_mul, integral_finsetSum _ fun c _ =>
      (show Continuous fun σ => phaseProd m ι κ (A c) (B c) σ θ by
        unfold phaseProd labelPhase; fun_prop).integrableOn_Icc]
  simp only [hin, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_finsetSum fun c _ =>
    (continuous_parametric_integral_of_continuous (f := fun θ σ => phaseProd m ι κ (A c) (B c) σ θ)
      ((hc c).comp continuous_swap) isCompact_Icc).intervalIntegrable _ _]
  simp only [slice_mean hmean]

theorem sum_terms {m : ℕ} (hm : 0 < m) (R : RowValues count rowCount) (box : Fin count → CellBox)
    (a b : Fin rowCount) (r z : ℝ) :
    ∑ c : Fin 3, ((if labelHarmonic m (sideLabel z (R.labelOf a)) = labelHarmonic m (sideLabel z (R.labelOf b))
        then sideValue R box a c r z * starRingEnd ℂ (sideValue R box b c r z) else 0) +
      (if labelHarmonic m (sideLabel z (R.labelOf a)) = -labelHarmonic m (sideLabel z (R.labelOf b))
        then sideValue R box a c r z * sideValue R box b c r z else 0)) =
      pairDensity R box a b (r, |z|) := by
  unfold sideLabel sideValue pairDensity
  by_cases hz : 0 ≤ z
  · simp only [hz, ↓reduceIte, abs_of_nonneg hz, harm_eq_iff hm, harm_eq_neg_iff hm]
    rw [Finset.sum_add_distrib]
    congr 1 <;> split_ifs <;> simp only [Finset.sum_const_zero, Finset.mul_sum, map_mul] <;>
      exact Finset.sum_congr rfl fun c _ => by ring
  · simp only [hz, ↓reduceIte, abs_of_neg (not_le.1 hz), harm_flip_eq_iff hm, harm_flip_eq_neg_iff hm]
    rw [Finset.sum_add_distrib]
    congr 1 <;> split_ifs <;>
      simp only [Finset.sum_const_zero, Finset.mul_sum, map_mul, Complex.conj_ofReal] <;>
      exact Finset.sum_congr rfl fun c _ => frameSign_pair c _ _ _ _

theorem angular_value {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {a b : Fin rowCount}
    (hm : 0 < m) (hmean : ∀ (ξ ζ : ℤ × ℤ) (A B : ℂ),
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
          (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
        Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re)
    (hA : GenShape M R m a) (hB : GenShape M R m b) {r : ℝ} (hr : 0 < r) (z : ℝ) :
    r * ∫ θ in (-Real.pi)..Real.pi, ∫ σ in Set.Icc (0 : ℝ) 1,
        inner ℝ (R.generatorField M.box m a σ (CellCert.Spectral.cylPoint r θ z))
          (R.generatorField M.box m b σ (CellCert.Spectral.cylPoint r θ z)) =
      Real.pi * radialDensity R M.box a b (r, |z|) := by
  have hcongr : ∫ θ in (-Real.pi)..Real.pi, ∫ σ in Set.Icc (0 : ℝ) 1,
      inner ℝ (R.generatorField M.box m a σ (CellCert.Spectral.cylPoint r θ z))
        (R.generatorField M.box m b σ (CellCert.Spectral.cylPoint r θ z)) =
      ∫ θ in (-Real.pi)..Real.pi, ∫ σ in Set.Icc (0 : ℝ) 1,
        unitOn (M.box (R.cellOf a)).rect (r, |z|) * unitOn (M.box (R.cellOf b)).rect (r, |z|) *
          ∑ c : Fin 3, phaseProd m (sideLabel z (R.labelOf a)) (sideLabel z (R.labelOf b))
            (sideValue R M.box a c r z) (sideValue R M.box b c r z) σ θ := by
    refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun θ hθ => ?_)
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at hθ
    simp only [pairing_at_cyl hA hB hr hθ]
  rw [hcongr, slice_integral hmean, ← Finset.mul_sum, ← Complex.re_sum, sum_terms hm]
  unfold radialDensity
  dsimp only
  ring

theorem fold_abs (k : ℝ × ℝ → ℝ) (hk : Integrable fun q : ℝ × ℝ => k (q.1, |q.2|)) :
    ∫ q in Set.Ioi (0 : ℝ) ×ˢ (Set.univ : Set ℝ), k (q.1, |q.2|) =
      2 * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), k q := by
  rw [← Set.Ioi_union_Iic (a := (0 : ℝ)), Set.prod_union,
    setIntegral_union (Set.disjoint_prod.2 (Or.inr (Set.Iic_disjoint_Ioi le_rfl).symm))
      (measurableSet_Ioi.prod measurableSet_Iic) hk.integrableOn hk.integrableOn]
  have h1 : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), k (q.1, |q.2|) =
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), k q :=
    setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Ioi) fun q hq => by
      simp only [abs_of_pos (show (0 : ℝ) < q.2 from hq.2), Prod.mk.eta]
  have hmp : MeasurePreserving (fun q : ℝ × ℝ => (q.1, -q.2)) volume volume := by
    have := (MeasurePreserving.id (volume : Measure ℝ)).prod (Measure.measurePreserving_neg (volume : Measure ℝ))
    rw [← Measure.volume_eq_prod] at this
    exact this
  have hemb : MeasurableEmbedding (fun q : ℝ × ℝ => (q.1, -q.2)) :=
    (MeasurableEquiv.prodCongr (MeasurableEquiv.refl ℝ) (MeasurableEquiv.neg ℝ)).measurableEmbedding
  have hpre : (fun q : ℝ × ℝ => (q.1, -q.2)) ⁻¹' (Set.Ioi (0 : ℝ) ×ˢ Set.Ici 0) =
      Set.Ioi 0 ×ˢ Set.Iic 0 := by
    ext q; simp
  have h2 : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Iic (0 : ℝ), k (q.1, |q.2|) =
      ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ici (0 : ℝ), k q := by
    rw [← hmp.setIntegral_preimage_emb hemb k, hpre]
    exact setIntegral_congr_fun (measurableSet_Ioi.prod measurableSet_Iic) fun q hq => by
      simp only [abs_of_nonpos (show q.2 ≤ 0 from hq.2)]
  have h3 : (Set.Ioi (0 : ℝ) ×ˢ Set.Ici (0 : ℝ) : Set (ℝ × ℝ)) =ᵐ[volume] Set.Ioi 0 ×ˢ Set.Ioi 0 := by
    rw [ae_eq_set]
    constructor
    · refine measure_mono_null (t := Set.Ioi (0 : ℝ) ×ˢ ({0} : Set ℝ)) ?_ ?_
      · rintro ⟨r, z⟩ ⟨⟨hr, hz⟩, hn⟩
        exact ⟨hr, Set.mem_singleton_iff.2 (le_antisymm (not_lt.1 fun h => hn ⟨hr, h⟩) hz)⟩
      · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    · rw [Set.sdiff_eq_empty.2 (Set.prod_mono le_rfl Set.Ioi_subset_Ici_self), measure_empty]
  rw [h1, h2, setIntegral_congr_set h3]
  ring

theorem continuous_ite_const {P : Prop} [Decidable P] {f : ℝ × ℝ → ℂ} (hf : Continuous f) :
    Continuous fun p => if P then f p else 0 := by
  by_cases hP : P
  · simp only [if_pos hP]; exact hf
  · simp only [if_neg hP]; exact continuous_const

theorem continuous_pairDensity (R : RowValues count rowCount) (box : Fin count → CellBox) (a b : Fin rowCount) :
    Continuous (pairDensity R box a b) := by
  have ha := continuous_testValue R box a
  have hb := continuous_testValue R box b
  unfold pairDensity
  exact (continuous_ite_const (by fun_prop)).add (continuous_ite_const (by fun_prop))

theorem measurableSet_rect (K : CellBox) : MeasurableSet K.rect :=
  (isClosed_Icc.prod isClosed_Icc).measurableSet

theorem integrable_radial (R : RowValues count rowCount) (box : Fin count → CellBox) (a b : Fin rowCount) :
    Integrable fun q : ℝ × ℝ => radialDensity R box a b (q.1, |q.2|) := by
  set K := box (R.cellOf a)
  have hKc : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hg : Continuous fun p : ℝ × ℝ => p.1 * (pairDensity R box a b p).re := by
    exact continuous_fst.mul (Complex.continuous_re.comp (continuous_pairDensity R box a b))
  obtain ⟨D, hD⟩ := hKc.exists_bound_of_continuousOn hg.continuousOn
  have hfold : Continuous fun q : ℝ × ℝ => (q.1, |q.2|) := by fun_prop
  set T := (fun q : ℝ × ℝ => (q.1, |q.2|)) ⁻¹' K.rect
  have hT : MeasurableSet T := (measurableSet_rect K).preimage hfold.measurable
  have hTsub : T ⊆ Set.Icc K.r₁ K.r₂ ×ˢ Set.Icc (-K.z₂) K.z₂ := by
    rintro ⟨r, z⟩ ⟨hr, hz⟩
    exact ⟨hr, abs_le.1 hz.2⟩
  have hTfin : volume T < ⊤ :=
    (measure_mono hTsub).trans_lt ((isCompact_Icc.prod isCompact_Icc).measure_lt_top)
  have hmeas : Measurable fun q : ℝ × ℝ => radialDensity R box a b (q.1, |q.2|) := by
    have h1 := measurable_unitOn (measurableSet_rect K)
    have h2 := measurable_unitOn (measurableSet_rect (box (R.cellOf b)))
    have h3 := (continuous_pairDensity R box a b).measurable
    have hm : Measurable (radialDensity R box a b) := by
      unfold radialDensity
      exact measurable_fst.mul ((h1.mul h2).mul (Complex.measurable_re.comp h3))
    exact hm.comp hfold.measurable
  refine Integrable.mono' ((integrable_indicator_iff hT).2 (integrableOn_const (C := D) hTfin.ne) :
      Integrable (T.indicator fun _ => D) volume) hmeas.aestronglyMeasurable (Filter.Eventually.of_forall fun q => ?_)
  unfold radialDensity unitOn
  by_cases ha : (q.1, |q.2|) ∈ K.rect
  · rw [Set.indicator_of_mem (show q ∈ T from ha), if_pos ha, one_mul]
    have hD' := hD _ ha
    simp only [Real.norm_eq_abs] at hD' ⊢
    split_ifs
    · simpa using hD'
    · simp only [zero_mul, mul_zero, abs_zero]
      exact (abs_nonneg _).trans hD'
  · rw [Set.indicator_of_notMem (show q ∉ T from ha), if_neg ha]
    simp

theorem half_value {M : CellMesh} {R : RowValues M.count rowCount} (hM : IsCellMesh M) (a b : Fin rowCount) :
    Real.pi * (2 * ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), radialDensity R M.box a b q) =
      R.testPairingMatrix M.box a b := by
  unfold RowValues.testPairingMatrix
  by_cases hS : R.SameBlock a b
  · rw [if_pos hS]
    obtain ⟨hc, -⟩ := hS
    have hK := hM.box_valid (R.cellOf a)
    have heq : ∀ q, radialDensity R M.box a b q = (M.box (R.cellOf a)).rect.indicator
        (fun p => p.1 * (pairDensity R M.box a b p).re) q := by
      intro q
      unfold radialDensity unitOn
      rw [← hc]
      by_cases h : q ∈ (M.box (R.cellOf a)).rect
      · rw [Set.indicator_of_mem h, if_pos h]; ring
      · rw [Set.indicator_of_notMem h, if_neg h]; ring
    simp only [heq]
    have hae : (Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ) ∩ (M.box (R.cellOf a)).rect : Set (ℝ × ℝ)) =ᵐ[volume]
        (M.box (R.cellOf a)).rect := by
      rw [ae_eq_set]
      constructor
      · rw [Set.sdiff_eq_empty.2 Set.inter_subset_right, measure_empty]
      · refine measure_mono_null (t := ({0} : Set ℝ) ×ˢ Set.univ ∪ Set.univ ×ˢ ({0} : Set ℝ)) ?_ ?_
        · rintro ⟨r, z⟩ ⟨⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩, hn⟩
          have hr0 : 0 ≤ r := hK.r_order.1.trans hr1
          have hz0 : 0 ≤ z := hK.z_order.1.trans hz1
          by_cases hr : r = 0
          · exact Or.inl ⟨hr, trivial⟩
          · refine Or.inr ⟨trivial, Set.mem_singleton_iff.2 ?_⟩
            by_contra hz
            exact hn ⟨⟨lt_of_le_of_ne hr0 (Ne.symm hr), lt_of_le_of_ne hz0 (Ne.symm hz)⟩,
              ⟨⟨hr1, hr2⟩, ⟨hz1, hz2⟩⟩⟩
        · refine measure_union_null ?_ ?_
          · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]
          · rw [Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, mul_zero]
    rw [setIntegral_indicator (measurableSet_rect _), setIntegral_congr_set hae]
    unfold pairDensity
    ring
  · rw [if_neg hS]
    have hz : ∫ q in Set.Ioi (0 : ℝ) ×ˢ Set.Ioi (0 : ℝ), radialDensity R M.box a b q = 0 := by
      by_cases hc : R.cellOf a = R.cellOf b
      · have hl : ¬(R.labelOf a = R.labelOf b ∨ R.labelOf a = -R.labelOf b) := fun h => hS ⟨hc, h⟩
        push Not at hl
        simp [radialDensity, pairDensity, hl.1, hl.2]
      · have h0 := hM.boxes_apart _ _ hc
        refine integral_eq_zero_of_ae (ae_restrict_of_ae ?_)
        filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with p hp
        unfold radialDensity unitOn
        by_cases ha : p ∈ (M.box (R.cellOf a)).rect
        · have hb : p ∉ (M.box (R.cellOf b)).rect := fun hb => hp ⟨ha, hb⟩
          simp [ha, hb]
        · simp [ha]
    rw [hz]
    ring

theorem pairing_entry {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {a b : Fin rowCount}
    (hm : 0 < m) (hM : IsCellMesh M) (hmean : ∀ (ξ ζ : ℤ × ℤ) (A B : ℂ),
      ∫ σ in Set.Icc (0 : ℝ) 1, ∫ θ in (0 : ℝ)..(2 * Real.pi),
        (Complex.exp (((2 * Real.pi * ξ.1 * σ + ξ.2 * θ : ℝ) : ℂ) * Complex.I) * A).re *
          (Complex.exp (((2 * Real.pi * ζ.1 * σ + ζ.2 * θ : ℝ) : ℂ) * Complex.I) * B).re =
        Real.pi * ((if ξ = ζ then A * starRingEnd ℂ B else 0) + (if ξ = -ζ then A * B else 0)).re)
    (hA : GenShape M R m a) (hB : GenShape M R m b) :
    periodPairing (R.generatorField M.box m a) (R.generatorField M.box m b) =
      R.testPairingMatrix M.box a b := by
  rw [periodPairing_cyl hA hB,
    setIntegral_congr_fun (measurableSet_Ioi.prod MeasurableSet.univ)
      (g := fun q => Real.pi * radialDensity R M.box a b (q.1, |q.2|))
      (fun q hq => angular_value hm hmean hA hB hq.1 q.2),
    integral_const_mul, fold_abs _ (integrable_radial R M.box a b)]
  exact half_value hM a b

end Internal.PairingFormula

open Internal.PairingFormula in
theorem generatorPairingMatrixFormula : GeneratorPairingMatrixFormula := by
  intro rowCount M R m tauMax hR
  ext a b
  exact pairing_entry hR.azimuth_pos hR.mesh_valid modeProduct_mean
    (fun σ y => generatorField_eq M R m a σ y) (fun σ y => generatorField_eq M R m b σ y)

end Breakdown.CertCell.Instance
