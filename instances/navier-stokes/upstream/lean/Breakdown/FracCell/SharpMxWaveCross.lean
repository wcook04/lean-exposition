import Breakdown.FracCell.SharpMxModeWaveRegular
import Breakdown.FracCell.SharpMxGradSeries
import Breakdown.FracCell.SharpDensityModeSeries
import Breakdown.FracCell.AxisLiftWeak

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace Breakdown.CellCert.CellAnalysis.SharpMxWaveCross.Internal

open SteadyCert Assembly SharpParts ModeExpansionParts
open Breakdown.FracInternal.CircleSliceCoupling

theorem sum3 {g : Fin 3 → ℂ} {M : ℝ} (h : ∀ i, ‖g i‖ ≤ M) : ‖∑ i, g i‖ ≤ 3 * M := by
  refine (norm_sum_le _ _).trans ?_
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem rsum3 {g : Fin 3 → ℝ} {M : ℝ} (h : ∀ i, g i ≤ M) : ∑ i, g i ≤ 3 * M := by
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem half_abs (i j l : Fin 3) : |(-(1 / 2) * CellCert.permSign i j l : ℝ)| ≤ 1 := by
  have h := Breakdown.FracInternal.CellDensityModesCoupling.perm_le i j l
  have h0 := abs_nonneg (CellCert.permSign i j l)
  rw [abs_mul]
  norm_num
  linarith

theorem quarter_abs (i j l : Fin 3) : |((1 / 4) * CellCert.permSign i j l : ℝ)| ≤ 1 := by
  have h := Breakdown.FracInternal.CellDensityModesCoupling.perm_le i j l
  have h0 := abs_nonneg (CellCert.permSign i j l)
  rw [abs_mul]
  norm_num
  linarith

theorem curl_le (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) : ‖curlComp s i‖ ≤ ∑ j, ∑ l, ‖s l j‖ := by
  unfold curlComp
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_sum_le _ _).trans
    (Finset.sum_le_sum fun l _ => ?_))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h := Breakdown.FracInternal.CellDensityModesCoupling.perm_le i j l
  calc |CellCert.permSign i j l| * ‖s l j‖ ≤ 1 * ‖s l j‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖s l j‖ := one_mul _

theorem atom_r {t : ℝ} (ht : |t| ≤ 1) {x y z : ℂ} {L T : ℝ} (hx : ‖x‖ ≤ L) (hyz : ‖y‖ * ‖z‖ ≤ T)
    (hL : 0 ≤ L) : ‖(t : ℂ) * (x * (y * z))‖ ≤ L * T := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖x‖ * (‖y‖ * ‖z‖) ≤ L * T := mul_le_mul hx hyz (by positivity) hL
  calc |t| * (‖x‖ * (‖y‖ * ‖z‖)) ≤ 1 * (‖x‖ * (‖y‖ * ‖z‖)) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ ≤ L * T := by rw [one_mul]; exact h1

theorem atom_l {t : ℝ} (ht : |t| ≤ 1) {x y z : ℂ} {L T : ℝ} (hxy : ‖x‖ * ‖y‖ ≤ T) (hz : ‖z‖ ≤ L)
    (hT : 0 ≤ T) : ‖(t : ℂ) * (x * (y * z))‖ ≤ L * T := by
  rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have h1 : ‖x‖ * ‖y‖ * ‖z‖ ≤ T * L := mul_le_mul hxy hz (norm_nonneg _) hT
  calc |t| * (‖x‖ * (‖y‖ * ‖z‖)) ≤ 1 * (‖x‖ * (‖y‖ * ‖z‖)) :=
        mul_le_mul_of_nonneg_right ht (by positivity)
    _ = ‖x‖ * ‖y‖ * ‖z‖ := by ring
    _ ≤ T * L := h1
    _ = L * T := mul_comm _ _

theorem five_le (X Y₂ Y₃ Y₄ Y₅ : ℂ) :
    ‖-X + Y₂ + Y₃ + Y₄ + Y₅‖ ≤ ‖X‖ + ‖Y₂‖ + ‖Y₃‖ + ‖Y₄‖ + ‖Y₅‖ := by
  have h1 := norm_add_le (-X + Y₂ + Y₃ + Y₄) Y₅
  have h2 := norm_add_le (-X + Y₂ + Y₃) Y₄
  have h3 := norm_add_le (-X + Y₂) Y₃
  have h4 := norm_add_le (-X) Y₂
  rw [norm_neg] at h4
  linarith

theorem wave_right_le (A B C s s' : Fin 3 → Fin 3 → ℂ) (v v' : Fin 3 → ℂ) {L T : ℝ} (hL : 0 ≤ L)
    (hs : ∀ a b, ‖s a b‖ ≤ L) (hv : ∀ a, ‖v a‖ ≤ L)
    (hA : ∀ a b i j, ‖A a b‖ * ‖s' i j‖ ≤ T) (hB : ∀ a b i, ‖B a b‖ * ‖v' i‖ ≤ T)
    (hC : ∀ a b i j, ‖C a b‖ * ‖s' i j‖ ≤ T) :
    ‖waveForm A B C s v s' v'‖ ≤ 2000 * (L * T) := by
  have hT : 0 ≤ T := (by positivity : 0 ≤ ‖A 0 0‖ * ‖s' 0 0‖).trans (hA 0 0 0 0)
  have hLT : 0 ≤ L * T := mul_nonneg hL hT
  rw [wave_expand]
  refine (five_le _ _ _ _ _).trans ?_
  calc _ ≤ 3 * (3 * (81 * (L * T))) + 3 * (3 * (3 * (3 * (L * T)))) + 3 * (3 * (3 * (3 * (L * T))))
        + 3 * (3 * (3 * (3 * (L * T)))) + 3 * (3 * (3 * (3 * (L * T)))) := by
        refine add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_
        · refine sum3 fun a => sum3 fun b => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have h1 : ‖curlComp s a‖ ≤ 3 * (3 * L) :=
            (curl_le s a).trans (rsum3 fun j => rsum3 fun l => hs l j)
          have h2 : ‖A a b‖ * ‖curlComp s' b‖ ≤ 3 * (3 * T) := by
            refine (mul_le_mul_of_nonneg_left (curl_le s' b) (norm_nonneg _)).trans ?_
            rw [Finset.mul_sum]
            refine rsum3 fun j => ?_
            rw [Finset.mul_sum]
            exact rsum3 fun l => hA a b l j
          calc ‖curlComp s a‖ * (‖A a b‖ * ‖curlComp s' b‖) ≤ (3 * (3 * L)) * (3 * (3 * T)) :=
                mul_le_mul h1 h2 (by positivity) (by linarith)
            _ = 81 * (L * T) := by ring
        · exact sum3 fun i => sum3 fun l => sum3 fun j => sum3 fun b =>
            atom_r (half_abs i l j) (by rw [Complex.norm_conj]; exact hs i l) (hB j b b) hL
        · exact sum3 fun i => sum3 fun l => sum3 fun q => sum3 fun j =>
            atom_r (quarter_abs i q j) (by rw [Complex.norm_conj]; exact hs i l) (hB l q j) hL
        · exact sum3 fun i => sum3 fun l => sum3 fun j => sum3 fun b =>
            atom_r (half_abs i l j) (by rw [Complex.norm_conj]; exact hv b)
              (by rw [Complex.norm_conj]; exact hC j b i l) hL
        · exact sum3 fun i => sum3 fun l => sum3 fun q => sum3 fun j =>
            atom_r (quarter_abs i q j) (by rw [Complex.norm_conj]; exact hv j)
              (by rw [Complex.norm_conj]; exact hC l q i l) hL
    _ ≤ 2000 * (L * T) := by linarith

theorem wave_left_le (A B C s s' : Fin 3 → Fin 3 → ℂ) (v v' : Fin 3 → ℂ) {L T : ℝ} (hL : 0 ≤ L)
    (hs' : ∀ a b, ‖s' a b‖ ≤ L) (hv' : ∀ a, ‖v' a‖ ≤ L)
    (hA : ∀ a b i j, ‖s i j‖ * ‖A a b‖ ≤ T) (hB : ∀ i l j b, ‖s i l‖ * ‖B j b‖ ≤ T)
    (hC : ∀ b j l, ‖v b‖ * ‖C j l‖ ≤ T) :
    ‖waveForm A B C s v s' v'‖ ≤ 2000 * (L * T) := by
  have hT : 0 ≤ T := (by positivity : 0 ≤ ‖s 0 0‖ * ‖A 0 0‖).trans (hA 0 0 0 0)
  have hLT : 0 ≤ L * T := mul_nonneg hL hT
  rw [wave_expand]
  refine (five_le _ _ _ _ _).trans ?_
  calc _ ≤ 3 * (3 * (81 * (L * T))) + 3 * (3 * (3 * (3 * (L * T)))) + 3 * (3 * (3 * (3 * (L * T))))
        + 3 * (3 * (3 * (3 * (L * T)))) + 3 * (3 * (3 * (3 * (L * T)))) := by
        refine add_le_add (add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_) ?_
        · refine sum3 fun a => sum3 fun b => ?_
          rw [norm_mul, norm_mul, Complex.norm_conj]
          have h1 : ‖curlComp s a‖ * ‖A a b‖ ≤ 3 * (3 * T) := by
            refine (mul_le_mul_of_nonneg_right (curl_le s a) (norm_nonneg _)).trans ?_
            rw [Finset.sum_mul]
            refine rsum3 fun j => ?_
            rw [Finset.sum_mul]
            exact rsum3 fun l => hA a b l j
          have h2 : ‖curlComp s' b‖ ≤ 3 * (3 * L) :=
            (curl_le s' b).trans (rsum3 fun j => rsum3 fun l => hs' l j)
          calc ‖curlComp s a‖ * (‖A a b‖ * ‖curlComp s' b‖) = (‖curlComp s a‖ * ‖A a b‖) * ‖curlComp s' b‖ := by
                ring
            _ ≤ (3 * (3 * T)) * (3 * (3 * L)) := mul_le_mul h1 h2 (norm_nonneg _) (by linarith)
            _ = 81 * (L * T) := by ring
        · exact sum3 fun i => sum3 fun l => sum3 fun j => sum3 fun b =>
            atom_l (half_abs i l j) (by rw [Complex.norm_conj]; exact hB i l j b) (hv' b) hT
        · exact sum3 fun i => sum3 fun l => sum3 fun q => sum3 fun j =>
            atom_l (quarter_abs i q j) (by rw [Complex.norm_conj]; exact hB i l l q) (hv' j) hT
        · exact sum3 fun i => sum3 fun l => sum3 fun j => sum3 fun b =>
            atom_l (half_abs i l j) (by rw [Complex.norm_conj, Complex.norm_conj]; exact hC b j b) (hs' i l) hT
        · exact sum3 fun i => sum3 fun l => sum3 fun q => sum3 fun j =>
            atom_l (quarter_abs i q j) (by rw [Complex.norm_conj, Complex.norm_conj]; exact hC j l q) (hs' i l) hT
    _ ≤ 2000 * (L * T) := by linarith

theorem entry_le2 (f : Fin 3 → Fin 3 → ℝ) (hf : ∀ a b, 0 ≤ f a b) (a b : Fin 3) :
    f a b ≤ ∑ a, ∑ b, f a b :=
  (Finset.single_le_sum (f := fun b => f a b) (fun b _ => hf a b) (Finset.mem_univ b)).trans
    (Finset.single_le_sum (f := fun a => ∑ b, f a b) (fun a _ => Finset.sum_nonneg fun b _ => hf a b)
      (Finset.mem_univ a))

theorem pair_le {x y T : ℝ} (h1 : x ^ 2 ≤ T) (h2 : y ^ 2 ≤ T) : x * y ≤ T := by
  nlinarith [sq_nonneg (x - y)]

def Good (K : CellBox) (g : ℤ → ℝ × ℝ → ℝ) : Prop :=
  (∀ j, IntegrableOn (g j) K.rect) ∧ Summable (fun j => ∫ p in K.rect, g j p)

theorem good_add {K : CellBox} {f g : ℤ → ℝ × ℝ → ℝ} (hf : Good K f) (hg : Good K g) :
    Good K (fun j p => f j p + g j p) :=
  ⟨fun j => (hf.1 j).add (hg.1 j), (hf.2.add hg.2).congr fun j => (integral_add (hf.1 j) (hg.1 j)).symm⟩

theorem good_mul {K : CellBox} {f : ℤ → ℝ × ℝ → ℝ} (r : ℝ) (hf : Good K f) :
    Good K (fun j p => r * f j p) :=
  ⟨fun j => (hf.1 j).const_mul r, (hf.2.mul_left r).congr fun _ => (integral_const_mul r _).symm⟩

theorem good_sum {K : CellBox} {g : Fin 3 → ℤ → ℝ × ℝ → ℝ} (h : ∀ i, Good K (g i)) :
    Good K (fun j p => ∑ i, g i j p) :=
  ⟨fun j => integrable_finsetSum _ fun i _ => (h i).1 j,
    (summable_sum fun i _ => (h i).2).congr fun j => (integral_finsetSum _ fun i _ => (h i).1 j).symm⟩

theorem rect_meas' (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem entry_nonneg' (G : Space →L[ℝ] Space) : 0 ≤ entrySq G := by
  unfold entrySq
  positivity

theorem good_mode {K : CellBox} (hK : IsCellBox K) {m : ℕ} (hm : 1 ≤ m) {G : Space → (Space →L[ℝ] Space)}
    (hG : AEStronglyMeasurable G volume) {C : ℝ} (hC : ∀ y ∈ K.solid, ‖G y‖ ≤ C) {f : ℤ → ℤ}
    (hf : Function.Injective f) (a b : Fin 3) :
    Good K (fun j p => K.lineWeight p.1 * ‖modeMat m (f j) G p.1 p.2 a b‖ ^ 2) := by
  have hsm := Breakdown.FracInternal.CellDensityModesSolid.solid_closed K
  have hE1 : AEStronglyMeasurable (K.solid.indicator G) volume := hG.indicator hsm
  have hE2 : Integrable (fun y => entrySq (K.solid.indicator G y)) := by
    have e : (fun y => entrySq (K.solid.indicator G y)) = K.solid.indicator (fun y => entrySq (G y)) := by
      funext y
      by_cases hy : y ∈ K.solid
      · simp [hy]
      · simp [hy, entrySq]
    rw [e, integrable_indicator_iff hsm]
    refine Measure.integrableOn_of_bounded (M := 3 * C ^ 2)
      Breakdown.FracInternal.CellDensityModesCoupling.solid_finite.ne
      (Breakdown.CellCert.Spectral.Internal.AxisLiftWeak.entry_cont.comp_aestronglyMeasurable hG) ?_
    refine (ae_restrict_iff' hsm).2 (Filter.Eventually.of_forall fun y hy => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (entry_nonneg' _)]
    have h1 := Breakdown.CellCert.Spectral.Internal.AxisLiftWeak.entry_le (G y)
    have h2 := hC y hy
    have h3 := norm_nonneg (G y)
    nlinarith
  have heq : ∀ j, Set.EqOn (fun p : ℝ × ℝ => K.lineWeight p.1 * ‖gradMode m (f j) (K.solid.indicator G) a b p‖ ^ 2)
      (fun p => K.lineWeight p.1 * ‖modeMat m (f j) G p.1 p.2 a b‖ ^ 2) K.rect := by
    intro j p hp
    have hθ : ∀ θ, K.solid.indicator G (cylPoint p.1 θ p.2) = G (cylPoint p.1 θ p.2) := fun θ =>
      Set.indicator_of_mem (Breakdown.FracInternal.CircleSliceRegular.cyl_solid hK hp θ) _
    simp only [gradMode, modeMat, hθ]
  refine ⟨fun j => (Breakdown.CellCert.CellAnalysis.ModeGradSquare.Internal.gm_sq K hK m (f j) hE1 hE2 a b).congr_fun
    (heq j) (rect_meas' K), ?_⟩
  refine ((gradSeries_holds K hK m hm _ hE1 hE2 a b).comp_injective hf).congr fun j => ?_
  exact setIntegral_congr_fun (rect_meas' K) (heq j)

section Concrete

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def modeSq (β : ℤ) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, (‖CellScalars.strainMode c β p a b‖ ^ 2 + ‖CellScalars.curlGradMode c β p a b‖ ^ 2)

def sharpSq (j : ℤ) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, ‖sharpGrad c K S x j p a b‖ ^ 2 + ∑ a : Fin 3, ‖sharpVel c K S x j p a‖ ^ 2

def modeW (β : ℤ) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, (K.lineWeight p.1 * ‖CellScalars.strainMode c β p a b‖ ^ 2
    + K.lineWeight p.1 * ‖CellScalars.curlGradMode c β p a b‖ ^ 2)

def fullW (j : ℤ) (p : ℝ × ℝ) : ℝ :=
  ∑ a : Fin 3, ∑ b : Fin 3, (2 * (K.lineWeight p.1 * ‖gradMode c.order j x.2.1 a b p‖ ^ 2)
      + 2 * (K.lineWeight p.1 * ‖lowGrad c K S x j p a b‖ ^ 2))
    + ∑ a : Fin 3, (2 * (K.lineWeight p.1 * ‖modeVec c.order j x.1 p.1 p.2 a‖ ^ 2)
      + 2 * (K.lineWeight p.1 * ‖lowVel c K S x j p a‖ ^ 2))

theorem modeSq_nonneg (β : ℤ) (p : ℝ × ℝ) : 0 ≤ modeSq c β p := by
  unfold modeSq
  positivity

theorem sharpSq_nonneg (j : ℤ) (p : ℝ × ℝ) : 0 ≤ sharpSq c K S x j p := by
  unfold sharpSq
  positivity

theorem strain_sq (β : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    ‖CellScalars.strainMode c β p a b‖ ^ 2 ≤ modeSq c β p := by
  have h := entry_le2 (fun a b => ‖CellScalars.strainMode c β p a b‖ ^ 2 + ‖CellScalars.curlGradMode c β p a b‖ ^ 2)
    (fun a b => by positivity) a b
  have h2 : 0 ≤ ‖CellScalars.curlGradMode c β p a b‖ ^ 2 := by positivity
  unfold modeSq
  linarith

theorem curlGrad_sq (β : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    ‖CellScalars.curlGradMode c β p a b‖ ^ 2 ≤ modeSq c β p := by
  have h := entry_le2 (fun a b => ‖CellScalars.strainMode c β p a b‖ ^ 2 + ‖CellScalars.curlGradMode c β p a b‖ ^ 2)
    (fun a b => by positivity) a b
  have h2 : 0 ≤ ‖CellScalars.strainMode c β p a b‖ ^ 2 := by positivity
  unfold modeSq
  linarith

theorem sharpGrad_sq (j : ℤ) (p : ℝ × ℝ) (a b : Fin 3) :
    ‖sharpGrad c K S x j p a b‖ ^ 2 ≤ sharpSq c K S x j p := by
  have h := entry_le2 (fun a b => ‖sharpGrad c K S x j p a b‖ ^ 2) (fun a b => by positivity) a b
  have h2 : 0 ≤ ∑ a : Fin 3, ‖sharpVel c K S x j p a‖ ^ 2 := by positivity
  unfold sharpSq
  linarith

theorem sharpVel_sq (j : ℤ) (p : ℝ × ℝ) (a : Fin 3) :
    ‖sharpVel c K S x j p a‖ ^ 2 ≤ sharpSq c K S x j p := by
  have h : ‖sharpVel c K S x j p a‖ ^ 2 ≤ ∑ a : Fin 3, ‖sharpVel c K S x j p a‖ ^ 2 :=
    Finset.single_le_sum (f := fun a => ‖sharpVel c K S x j p a‖ ^ 2) (fun a _ => sq_nonneg _) (Finset.mem_univ a)
  have h2 : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖sharpGrad c K S x j p a b‖ ^ 2 :=
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  unfold sharpSq
  linarith

theorem modeW_eq (β : ℤ) (p : ℝ × ℝ) : K.lineWeight p.1 * modeSq c β p = modeW c K β p := by
  simp only [modeSq, modeW, Finset.mul_sum, mul_add]

theorem sharpSq_le (j : ℤ) (p : ℝ × ℝ) (hw : 0 ≤ K.lineWeight p.1) :
    K.lineWeight p.1 * sharpSq c K S x j p ≤ fullW c K S x j p := by
  unfold sharpSq fullW
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  refine add_le_add (Finset.sum_le_sum fun a _ => ?_) (Finset.sum_le_sum fun a _ => ?_)
  · rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun b _ => ?_
    have h := mul_le_mul_of_nonneg_left
      (Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.nsq_sub
        (gradMode c.order j x.2.1 a b p) (lowGrad c K S x j p a b)) hw
    have e : sharpGrad c K S x j p a b = gradMode c.order j x.2.1 a b p - lowGrad c K S x j p a b := rfl
    rw [e]
    exact h.trans (le_of_eq (by ring))
  · have h := mul_le_mul_of_nonneg_left
      (Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.nsq_sub
        (modeVec c.order j x.1 p.1 p.2 a) (lowVel c K S x j p a)) hw
    have e : sharpVel c K S x j p a = modeVec c.order j x.1 p.1 p.2 a - lowVel c K S x j p a := rfl
    rw [e]
    exact h.trans (le_of_eq (by ring))

theorem cross_le (hK : IsCellBox K) {n n' : ℤ} {L : ℝ} (hL : 0 ≤ L) {p : ℝ × ℝ} (hp : p ∈ K.rect)
    (hg : ∀ a b, ‖lowGrad c K S x n p a b‖ ≤ L) (hv : ∀ a, ‖lowVel c K S x n p a‖ ≤ L) :
    ‖p.1 * (crossPair c K S x n n' p).re‖ ≤
      (max 1 K.r₂ * (4000 * L)) * (modeW c K (n - n') p + modeW c K (n' - n) p + fullW c K S x n' p) := by
  have h0 := Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.r_nonneg hK hp
  have hw0 := Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.lw_nonneg hK hp
  have hr := Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.r_le_lw hK hp
  set T := modeSq c (n - n') p + modeSq c (n' - n) p + sharpSq c K S x n' p with hT
  have q1 := modeSq_nonneg c (n - n') p
  have q2 := modeSq_nonneg c (n' - n) p
  have q3 := sharpSq_nonneg c K S x n' p
  have hT0 : 0 ≤ T := by linarith
  have sA : ∀ a b, ‖CellScalars.strainMode c (n - n') p a b‖ ^ 2 ≤ T := fun a b => by
    linarith [strain_sq c (n - n') p a b]
  have sA' : ∀ a b, ‖CellScalars.strainMode c (n' - n) p a b‖ ^ 2 ≤ T := fun a b => by
    linarith [strain_sq c (n' - n) p a b]
  have sB : ∀ a b, ‖CellScalars.curlGradMode c (n - n') p a b‖ ^ 2 ≤ T := fun a b => by
    linarith [curlGrad_sq c (n - n') p a b]
  have sB' : ∀ a b, ‖CellScalars.curlGradMode c (n' - n) p a b‖ ^ 2 ≤ T := fun a b => by
    linarith [curlGrad_sq c (n' - n) p a b]
  have sG : ∀ a b, ‖sharpGrad c K S x n' p a b‖ ^ 2 ≤ T := fun a b => by
    linarith [sharpGrad_sq c K S x n' p a b]
  have sV : ∀ a, ‖sharpVel c K S x n' p a‖ ^ 2 ≤ T := fun a => by
    linarith [sharpVel_sq c K S x n' p a]
  have hR : ‖lowSharpPair c K S x n n' p‖ ≤ 2000 * (L * T) :=
    wave_right_le (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p) (lowGrad c K S x n p) (sharpGrad c K S x n' p)
      (lowVel c K S x n p) (sharpVel c K S x n' p) hL hg hv
      (fun a b i j => pair_le (sA a b) (sG i j))
      (fun a b i => pair_le (sB a b) (sV i))
      (fun a b i j => pair_le (sB' a b) (sG i j))
  have hLe : ‖sharpLowPair c K S x n' n p‖ ≤ 2000 * (L * T) :=
    wave_left_le (CellScalars.strainMode c (n' - n) p) (CellScalars.curlGradMode c (n' - n) p)
      (CellScalars.curlGradMode c (n - n') p) (sharpGrad c K S x n' p) (lowGrad c K S x n p)
      (sharpVel c K S x n' p) (lowVel c K S x n p) hL hg hv
      (fun a b i j => pair_le (sG i j) (sA' a b))
      (fun i l j b => pair_le (sG i l) (sB' j b))
      (fun b j l => pair_le (sV b) (sB j l))
  have hX : ‖crossPair c K S x n n' p‖ ≤ 4000 * (L * T) := by
    have := norm_add_le (lowSharpPair c K S x n n' p) (sharpLowPair c K S x n' n p)
    unfold crossPair
    linarith
  have hre : ‖p.1 * (crossPair c K S x n n' p).re‖ ≤ p.1 * ‖crossPair c K S x n n' p‖ := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) h0
  have hwT : K.lineWeight p.1 * T ≤ modeW c K (n - n') p + modeW c K (n' - n) p + fullW c K S x n' p := by
    rw [hT, mul_add, mul_add, modeW_eq, modeW_eq]
    linarith [sharpSq_le c K S x n' p hw0]
  have hM : 0 ≤ max 1 K.r₂ * (4000 * L) :=
    mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (by linarith)
  calc ‖p.1 * (crossPair c K S x n n' p).re‖ ≤ p.1 * ‖crossPair c K S x n n' p‖ := hre
    _ ≤ p.1 * (4000 * (L * T)) := mul_le_mul_of_nonneg_left hX h0
    _ ≤ (max 1 K.r₂ * K.lineWeight p.1) * (4000 * (L * T)) :=
        mul_le_mul_of_nonneg_right hr (mul_nonneg (by norm_num) (mul_nonneg hL hT0))
    _ = (max 1 K.r₂ * (4000 * L)) * (K.lineWeight p.1 * T) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hwT hM

theorem low_bound (n : ℤ) : ∃ L : ℝ, 0 ≤ L ∧ (∀ p ∈ K.rect, ∀ a b, ‖lowGrad c K S x n p a b‖ ≤ L) ∧
    ∀ p ∈ K.rect, ∀ a, ‖lowVel c K S x n p a‖ ≤ L := by
  have hcont : Continuous (fun p => ∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖
      + ∑ a : Fin 3, ‖lowVel c K S x n p a‖) :=
    (continuous_finsetSum _ fun a _ => continuous_finsetSum _ fun b _ =>
      continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp
        (Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.lowGrad_cont c K S x n)))).add
    (continuous_finsetSum _ fun a _ => continuous_norm.comp ((continuous_apply a).comp
      (Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.lowVel_cont c K S x n)))
  obtain ⟨L, hL⟩ := (isCompact_Icc.prod isCompact_Icc : IsCompact K.rect).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max L 0, le_max_right _ _, fun p hp a b => ?_, fun p hp a => ?_⟩
  · have h1 : ‖∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖ + ∑ a : Fin 3, ‖lowVel c K S x n p a‖‖ ≤ L :=
      hL p hp
    have h2 : ‖lowGrad c K S x n p a b‖ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖ :=
      entry_le2 (fun a b => ‖lowGrad c K S x n p a b‖) (fun a b => norm_nonneg _) a b
    have h3 : 0 ≤ ∑ a : Fin 3, ‖lowVel c K S x n p a‖ := by positivity
    have h4 := Real.le_norm_self (∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖
      + ∑ a : Fin 3, ‖lowVel c K S x n p a‖)
    linarith [le_max_left L 0]
  · have h1 : ‖∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖ + ∑ a : Fin 3, ‖lowVel c K S x n p a‖‖ ≤ L :=
      hL p hp
    have h2 : ‖lowVel c K S x n p a‖ ≤ ∑ a : Fin 3, ‖lowVel c K S x n p a‖ :=
      Finset.single_le_sum (f := fun a => ‖lowVel c K S x n p a‖) (fun a _ => norm_nonneg _) (Finset.mem_univ a)
    have h3 : 0 ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖ := by positivity
    have h4 := Real.le_norm_self (∑ a : Fin 3, ∑ b : Fin 3, ‖lowGrad c K S x n p a b‖
      + ∑ a : Fin 3, ‖lowVel c K S x n p a‖)
    linarith [le_max_left L 0]

theorem good_lowGrad (a b : Fin 3) :
    Good K (fun j p => K.lineWeight p.1 * ‖lowGrad c K S x j p a b‖ ^ 2) :=
  ⟨fun j => ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((Breakdown.CellCert.CellAnalysis.LowEntry.Internal.lineWeight_cont K).comp continuous_fst).mul
        ((continuous_norm.comp ((continuous_apply b).comp ((continuous_apply a).comp
          (Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.lowGrad_cont c K S x j)))).pow 2))).continuousOn,
    summable_of_ne_finset_zero (s := S.resolved) fun j hj => by simp [lowGrad, hj]⟩

theorem good_lowVel (a : Fin 3) :
    Good K (fun j p => K.lineWeight p.1 * ‖lowVel c K S x j p a‖ ^ 2) :=
  ⟨fun j => ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
      ((((Breakdown.CellCert.CellAnalysis.LowEntry.Internal.lineWeight_cont K).comp continuous_fst).mul
        ((continuous_norm.comp ((continuous_apply a).comp
          (Breakdown.CellCert.CellAnalysis.SharpYDensityRegular.Internal.lowVel_cont c K S x j))).pow 2))).continuousOn,
    summable_of_ne_finset_zero (s := S.resolved) fun j hj => by simp [lowVel, hj]⟩

theorem good_full (hK : IsCellBox K) (hm : 1 ≤ c.order) (hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1) :
    Good K (fun j p => fullW c K S x j p) := by
  unfold fullW
  refine good_add (good_sum fun a => good_sum fun b => good_add (good_mul 2 ?_) (good_mul 2 (good_lowGrad c K S x a b)))
    (good_sum fun a => good_add (good_mul 2 ?_) (good_mul 2 (good_lowVel c K S x a)))
  · exact ⟨fun j => (modeGradSquare K hK _ _ _ _ hs j a b).2,
      gradSeries_holds K hK c.order hm x.2.1 hs.measurable_gradient hs.gradient_two a b⟩
  · exact ⟨fun j => (modeVelSquare K hK _ _ _ _ hs j a).2,
      (modeSeries_holds K hK c.order hm x.1 x.2.1 x.2.2.1 hs).1 a⟩

theorem good_modeW (hK : IsCellBox K) (hm : 1 ≤ c.order) (hS : AEStronglyMeasurable c.modelStrain volume)
    (hG : AEStronglyMeasurable c.modelCurlGrad volume) {C : ℝ}
    (hC : ∀ y ∈ K.solid, ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C) {f : ℤ → ℤ}
    (hf : Function.Injective f) :
    Good K (fun j p => modeW c K (f j) p) := by
  unfold modeW
  exact good_sum fun a => good_sum fun b =>
    good_add (good_mode hK hm hS (fun y hy => (hC y hy).1) hf a b)
      (good_mode hK hm hG (fun y hy => (hC y hy).2) hf a b)

end Concrete

end Breakdown.CellCert.CellAnalysis.SharpMxWaveCross.Internal

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly SharpParts ModeExpansionParts
open Breakdown.CellCert.CellAnalysis.SharpMxWaveCross.Internal
open Breakdown.CellCert.CellAnalysis.SharpModeExpansionRegular.Internal

theorem modeWaveCross_holds : ModeWaveCrossStatement := by
  intro α hα₁ hα₂ k N c hc K S B Cl slots R hd hax x hx n hn
  have hK := hd.box
  have hs : IsSecondOrderField c.order x.1 x.2.1 x.2.2.1 := hx.1
  have hm : 1 ≤ c.order := le_trans (by norm_num) hc.base.order_ge
  obtain ⟨C, hC⟩ := hc.model_bounded
  have hCst : ∀ y ∈ K.solid, ‖c.modelStrain y‖ ≤ C ∧ ‖c.modelCurlGrad y‖ ≤ C := fun y hy =>
    ⟨(hC y (hd.solid_in_region hy)).2.2.1, (hC y (hd.solid_in_region hy)).2.2.2⟩
  obtain ⟨L, hL0, hLg, hLv⟩ := low_bound c K S x n
  have g1 := good_modeW c K hK hm hc.model_measurable.2.2.1 hc.model_measurable.2.2.2 hCst
    (sub_right_injective : Function.Injective fun j : ℤ => n - j)
  have g2 := good_modeW c K hK hm hc.model_measurable.2.2.1 hc.model_measurable.2.2.2 hCst
    (sub_left_injective : Function.Injective fun j : ℤ => j - n)
  have g3 := good_full c K S x hK hm hs
  have hG := good_mul (max 1 K.r₂ * (4000 * L)) (good_add (good_add g1 g2) g3)
  refine Summable.of_nonneg_of_le (fun j => integral_nonneg fun p => norm_nonneg _) (fun j => ?_) hG.2
  refine setIntegral_mono_on (wt_re K (cross_wt c K S x α hc hK hs n j)).norm (hG.1 j) (rect_meas' K)
    fun p hp => ?_
  exact cross_le c K S x hK hL0 hp (hLg p hp) (hLv p hp)

theorem modeWaveRegular_holds : ModeWaveRegularStatement :=
  modeWaveRegular_of_cross modeWaveCross_holds

end Breakdown.CellCert.CellAnalysis
