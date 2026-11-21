import Breakdown.CertCell.InstancePairingPosDef
import Breakdown.CertCell.TailFlipDecay
import Breakdown.Cert.CoerciveSmoothEpsPointwiseProduct

open scoped ComplexOrder
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CertCell

namespace Instance

open CellCert.CellAnalysis (CellBox IsCellBox)

namespace Internal

namespace ClassForm

open RowPairing Matrix

theorem map_conj_inv {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    (A⁻¹).map (starRingEnd ℂ) = (A.map (starRingEnd ℂ))⁻¹ := by
  have e : ∀ B : Matrix (Fin n) (Fin n) ℂ, B.map (starRingEnd ℂ) = B.conjTranspose.transpose := by
    intro B
    ext i j
    simp [Matrix.conjTranspose_apply]
  rw [e, e, Matrix.conjTranspose_nonsing_inv, Matrix.transpose_nonsing_inv]

theorem conj_inv_mulVec {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) (i : Fin n) :
    starRingEnd ℂ ((A⁻¹ *ᵥ u) i) =
      ((A.map (starRingEnd ℂ))⁻¹ *ᵥ fun j => starRingEnd ℂ (u j)) i := by
  rw [← map_conj_inv]
  simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply]

theorem quad_conj {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    (star (fun j => starRingEnd ℂ (u j)) ⬝ᵥ
      ((A.map (starRingEnd ℂ))⁻¹ *ᵥ fun j => starRingEnd ℂ (u j))).re =
      (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  rw [← Complex.conj_re (star u ⬝ᵥ (A⁻¹ *ᵥ u))]
  congr 1
  simp only [dotProduct, map_sum, map_mul, Pi.star_apply, conj_inv_mulVec]
  simp

theorem quad_conj_cast {n n' : ℕ} (hn : n' = n) (A : Matrix (Fin n) (Fin n) ℂ)
    (B : Matrix (Fin n') (Fin n') ℂ) (u : Fin n → ℂ) (v : Fin n' → ℂ)
    (hB : ∀ i j, B i j = starRingEnd ℂ (A (Fin.cast hn i) (Fin.cast hn j)))
    (hv : ∀ i, v i = starRingEnd ℂ (u (Fin.cast hn i))) :
    (star v ⬝ᵥ (B⁻¹ *ᵥ v)).re = (star u ⬝ᵥ (A⁻¹ *ᵥ u)).re := by
  subst hn
  have e1 : B = A.map (starRingEnd ℂ) := by
    ext i j
    simpa using hB i j
  have e2 : v = fun j => starRingEnd ℂ (u j) := by
    funext i
    simpa using hv i
  rw [e1, e2, quad_conj]

theorem quad_eq_zero {n : ℕ} (hn : n = 0) (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    star u ⬝ᵥ (A⁻¹ *ᵥ u) = 0 := by
  subst hn
  simp [dotProduct]

theorem inv_mulVec_im {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ)
    (hA : ∀ i j, starRingEnd ℂ (A i j) = A i j) (hu : ∀ i, starRingEnd ℂ (u i) = u i) (i : Fin n) :
    ((A⁻¹ *ᵥ u) i).im = 0 := by
  have h1 : A.map (starRingEnd ℂ) = A := by
    ext i j
    exact hA i j
  have h2 : (fun j => starRingEnd ℂ (u j)) = u := funext hu
  have h := conj_inv_mulVec A u i
  rw [h1, h2] at h
  exact Complex.conj_eq_iff_im.mp h

theorem sum_ite_unique {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] (x : ℂ)
    (hu : ∀ a b, P a → P b → a = b) :
    ∑ a, (if P a then x else 0) = if ∃ a, P a then x else 0 := by
  by_cases h : ∃ a, P a
  · obtain ⟨a0, ha0⟩ := h
    rw [if_pos ⟨a0, ha0⟩, Finset.sum_eq_single a0]
    · rw [if_pos ha0]
    · intro b _ hb
      rw [if_neg fun hb' => hb (hu b a0 hb' ha0)]
    · intro h
      exact absurd (Finset.mem_univ _) h
  · rw [if_neg h]
    exact Finset.sum_eq_zero fun a _ => if_neg fun ha => h ⟨a, ha⟩

theorem conj_setIntegral_eq (s : Set (ℝ × ℝ)) (f : ℝ × ℝ → ℂ) (hf : ∀ p, starRingEnd ℂ (f p) = f p) :
    starRingEnd ℂ (∫ p in s, f p) = ∫ p in s, f p := by
  rw [← integral_conj]
  congr 1
  funext p
  exact hf p

theorem labelHarmonic_neg (m : ℕ) (ι : ℤ × ℤ) : labelHarmonic m (-ι) = -labelHarmonic m ι := by
  refine Prod.ext ?_ ?_ <;> simp [labelHarmonic, labelTime, labelAzimuth]
  ring

theorem labelVel_neg (m : ℕ) (ι : ℤ × ℤ) (F : ℝ → Space → Space) (p : ℝ × ℝ) (c : Fin 3) :
    labelVel m (-ι) F p c = starRingEnd ℂ (labelVel m ι F p c) := by
  unfold labelVel
  rw [labelHarmonic_neg]
  exact Coercive.Internal.SmoothEpsPointwise.modeVel_neg _ _ _ _ _

theorem labelHarmonic_labelFlip (m : ℕ) (ι : ℤ × ℤ) :
    ((labelHarmonic m (labelFlip ι)).1, -(labelHarmonic m (labelFlip ι)).2) = labelHarmonic m ι := by
  refine Prod.ext ?_ ?_ <;> simp [labelHarmonic, labelTime, labelAzimuth, labelFlip]
  ring

theorem labelVel_flip {F : ℝ → Space → Space} (hF : ∀ σ y, F σ (flipPoint y) = flipPoint (F σ y))
    (m : ℕ) (ι : ℤ × ℤ) (p : ℝ × ℝ) (c : Fin 3) :
    labelVel m (labelFlip ι) F (p.1, -p.2) c = (frameSign c : ℂ) * labelVel m ι F p c := by
  unfold labelVel
  rw [TailBand.Internal.FlipDecay.modeVel_flip_of _ p (ae_of_all _ fun q => hF _ _) c,
    labelHarmonic_labelFlip]

theorem frameSign_mul_conj (c : Fin 3) (z : ℂ) :
    (frameSign c : ℂ) * starRingEnd ℂ ((frameSign c : ℂ) * z) = starRingEnd ℂ z := by
  fin_cases c <;> simp [frameSign]

theorem lowerMoment_eq_upper {count rowCount : ℕ} (R : RowValues count rowCount) (box : Fin count → CellBox)
    {F : ℝ → Space → Space} (hF : ∀ σ y, F σ (flipPoint y) = flipPoint (F σ y)) (m : ℕ) (a : Fin rowCount) :
    R.lowerMoment box m a F = R.upperMoment box m a F := by
  unfold RowValues.lowerMoment RowValues.upperMoment
  congr 1
  refine integral_congr_ae (ae_of_all _ fun p => ?_)
  simp only [labelVel_flip hF, frameSign_mul_conj]

theorem momentIntegrand_integrableOn {count rowCount : ℕ} (R : RowValues count rowCount)
    (box : Fin count → CellBox) {m : ℕ} {F : ℝ → Space → Space} (a : Fin rowCount)
    (hint : ∀ c, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m (R.labelOf a) F p c)
      (box (R.cellOf a)).rect) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ c : Fin 3,
      starRingEnd ℂ (labelVel m (R.labelOf a) F p c) * R.testValue box a c p) (box (R.cellOf a)).rect := by
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ c : Fin 3,
      starRingEnd ℂ (labelVel m (R.labelOf a) F p c) * R.testValue box a c p) =
      fun p => ∑ c : Fin 3,
        starRingEnd ℂ ((p.1 : ℂ) * labelVel m (R.labelOf a) F p c) * R.testValue box a c p := by
    funext p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [map_mul, Complex.conj_ofReal]
    ring
  rw [e]
  refine integrable_finsetSum _ fun c _ => ?_
  refine IntegrableOn.mul_continuousOn ?_ (Continuous.continuousOn ?_) (rect_compact _)
  · exact Complex.conjCLE.toContinuousLinearMap.integrable_comp (hint c)
  · unfold RowValues.testValue
    exact eval_continuous _ _

section Algebra

variable {rowCount : ℕ} (M : CellMesh) (R : RowValues M.count rowCount) (m : ℕ) (F : ℝ → Space → Space)

def momentAt (K : Fin M.count) (ι : ℤ × ℤ) (j : ℕ) : ℂ :=
  if h : j < R.testCount K ι then R.cellMoment M.box m K ι F ⟨j, h⟩ else 0

def solutionVec (K : Fin M.count) (ι : ℤ × ℤ) : Fin (R.testCount K ι) → ℂ :=
  ((2 / blockFactor ι : ℝ) : ℂ) • ((R.testBlockMatrix M.box K ι)⁻¹ *ᵥ R.cellMoment M.box m K ι F)

def solutionAt (K : Fin M.count) (ι : ℤ × ℤ) (j : ℕ) : ℂ :=
  if h : j < R.testCount K ι then solutionVec M R m F K ι ⟨j, h⟩ else 0

def solution (a : Fin rowCount) : ℝ :=
  (starRingEnd ℂ (rowPartFactor (R.realPart a)) *
    solutionAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a)).re

def blockSum (P : Fin rowCount → ℝ) (K : Fin M.count) (ι : ℤ × ℤ) : ℝ :=
  ∑ a, if R.cellOf a = K ∧ R.labelOf a = ι then
    R.testWeight (R.cellOf a) (R.labelOf a) * P a * solution M R m F a else 0

def blockForm (K : Fin M.count) (ι : ℤ × ℤ) : ℝ :=
  R.testWeight K ι * (star (R.cellMoment M.box m K ι F) ⬝ᵥ
    ((R.testBlockMatrix M.box K ι)⁻¹ *ᵥ R.cellMoment M.box m K ι F)).re

end Algebra

variable {rowCount : ℕ} {M : CellMesh} {R : RowValues M.count rowCount} {m : ℕ} {tauMax : ℝ}
  {F : ℝ → Space → Space}

theorem upperMoment_eq (hR : IsRowValues M R m tauMax) (a : Fin rowCount)
    (hI : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * ∑ c : Fin 3,
      starRingEnd ℂ (labelVel m (R.labelOf a) F p c) * R.testValue M.box a c p) (M.box (R.cellOf a)).rect) :
    R.upperMoment M.box m a F = 2 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re := by
  unfold RowValues.upperMoment
  rw [integral_re_mul _ _ hI]
  unfold momentAt RowValues.cellMoment
  rw [dif_pos (hR.test_index a), ← integral_conj]
  congr 4
  funext p
  simp only [map_mul, map_sum, Complex.conj_conj, Complex.conj_ofReal, RowValues.testValue]

theorem pairing_eq (hR : IsRowValues M R m tauMax) (hmom : GeneratorPairingMoments)
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFp : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hflip : ∀ σ y, F σ (flipPoint y) = flipPoint (F σ y))
    (hint : ∀ K ι c, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m ι F p c) (M.box K).rect)
    (a : Fin rowCount) :
    periodPairing F (R.generatorField M.box m a) = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re := by
  rw [hmom M R m tauMax hR F hFm hFp hF2 a, lowerMoment_eq_upper R M.box hflip,
    upperMoment_eq hR a (momentIntegrand_integrableOn R M.box a fun c => hint _ _ c)]
  ring


theorem exists_row_part (hR : IsRowValues M R m tauMax) {K : Fin M.count} {ι : ℤ × ℤ} (a0 : Fin rowCount)
    (h0 : R.cellOf a0 = K ∧ R.labelOf a0 = ι) (j : ℕ) (hj : j < R.testCount K ι) (b : Bool)
    (hb : ι = -ι → b = true) :
    ∃ a, ((R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = j) ∧ R.realPart a = b := by
  obtain ⟨hK, hι⟩ := h0
  have hT : ι ∈ M.tested K := by
    rw [← hK, ← hι]
    exact hR.row_tested a0
  obtain ⟨a, ha1, ha2, ha3, ha4⟩ := hR.rows_complete K ι hT j hj b hb
  refine ⟨a, ⟨⟨ha1, ?_⟩, ha3⟩, ha4⟩
  rcases ha2 with h | h
  · exact h
  · exact (hR.rows_one_member a a0 (ha1.trans hK.symm) (by rw [h, hι])).trans hι

theorem rowVec_solution (hR : IsRowValues M R m tauMax) {K : Fin M.count} {ι : ℤ × ℤ} (a0 : Fin rowCount)
    (h0 : R.cellOf a0 = K ∧ R.labelOf a0 = ι)
    (hreal : ι = -ι → ∀ j, (solutionVec M R m F K ι j).im = 0) (j : Fin (R.testCount K ι)) :
    rowVec R (solution M R m F) K ι j = solutionVec M R m F K ι j := by
  unfold rowVec
  set s := solutionVec M R m F K ι j with hs
  have hterm : ∀ a, (if (R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ) then
      (solution M R m F a : ℂ) * rowPartFactor (R.realPart a) else 0) =
      (if ((R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ)) ∧ R.realPart a = true then
        ((s.re : ℝ) : ℂ) else 0) +
      (if ((R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ)) ∧ R.realPart a = false then
        ((s.im : ℝ) : ℂ) * Complex.I else 0) := by
    intro a
    by_cases hc : (R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ)
    · have hsa : solutionAt M R m F K ι (j : ℕ) = s := by
        unfold solutionAt
        rw [dif_pos j.isLt]
      cases hp : R.realPart a <;> simp [hc, hp, solution, hsa, rowPartFactor]
    · simp [hc]
  have hu : ∀ b : Bool, ∀ a a', (((R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ)) ∧ R.realPart a = b) →
      (((R.cellOf a' = K ∧ R.labelOf a' = ι) ∧ R.testOf a' = (j : ℕ)) ∧ R.realPart a' = b) → a = a' :=
    fun b a a' ha ha' => hR.rows_distinct a a' (ha.1.1.1.trans ha'.1.1.1.symm) (ha.1.1.2.trans ha'.1.1.2.symm)
      (ha.1.2.trans ha'.1.2.symm) (ha.2.trans ha'.2.symm)
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_add_distrib, sum_ite_unique _ _ (hu true),
    sum_ite_unique _ _ (hu false), if_pos (exists_row_part hR a0 h0 j j.isLt true fun _ => rfl)]
  by_cases hz : ι = -ι
  · have hf : ¬ ∃ a, ((R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ)) ∧ R.realPart a = false := by
      rintro ⟨a, ha, hp⟩
      have h := hR.zero_label_real a (by rw [ha.1.2]; exact hz)
      rw [hp] at h
      exact Bool.false_ne_true h
    have hsi : s.im = 0 := hreal hz j
    rw [if_neg hf, add_zero]
    apply Complex.ext <;> simp [hsi]
  · rw [if_pos (exists_row_part hR a0 h0 j j.isLt false fun h => absurd h hz)]
    apply Complex.ext <;> simp

theorem blockMatrix_mulVec_solution (hR : IsRowValues M R m tauMax) {K : Fin M.count} {ι : ℤ × ℤ}
    (hT : ι ∈ M.tested K) :
    R.testBlockMatrix M.box K ι *ᵥ solutionVec M R m F K ι =
      ((2 / blockFactor ι : ℝ) : ℂ) • R.cellMoment M.box m K ι F := by
  have hdet : IsUnit (R.testBlockMatrix M.box K ι).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (hR.block_posDef K ι hT).isUnit
  unfold solutionVec
  rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hdet, Matrix.one_mulVec]

theorem sum_conj_rowVec_mul (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (K : Fin M.count)
    (ι : ℤ × ℤ) (g : ℕ → ℂ) :
    ∑ j : Fin (R.testCount K ι), starRingEnd ℂ (rowVec R x K ι j) * g j =
      ∑ a, if R.cellOf a = K ∧ R.labelOf a = ι then
        (x a : ℂ) * starRingEnd ℂ (rowPartFactor (R.realPart a)) * g (R.testOf a) else 0 := by
  simp only [rowVec, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ j : Fin (R.testCount K ι), starRingEnd ℂ (if (R.cellOf a = K ∧ R.labelOf a = ι) ∧
      R.testOf a = (j : ℕ) then (x a : ℂ) * rowPartFactor (R.realPart a) else 0) * g j =
      if (R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ) then
        (x a : ℂ) * starRingEnd ℂ (rowPartFactor (R.realPart a)) * g (R.testOf a) else 0 := by
    intro j
    split_ifs with hc
    · rw [map_mul, Complex.conj_ofReal, hc.2]
    · simp
  rw [Finset.sum_congr rfl fun j _ => h j]
  exact sum_fin_ite _ _ _ (fun hc => by rw [← hc.1, ← hc.2]; exact hR.test_index a)
    (fun _ => (x a : ℂ) * starRingEnd ℂ (rowPartFactor (R.realPart a)) * g (R.testOf a))

theorem sum_rowVec_mul (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (K : Fin M.count)
    (ι : ℤ × ℤ) (g : ℕ → ℂ) :
    ∑ j : Fin (R.testCount K ι), rowVec R x K ι j * g j =
      ∑ a, if R.cellOf a = K ∧ R.labelOf a = ι then
        (x a : ℂ) * rowPartFactor (R.realPart a) * g (R.testOf a) else 0 := by
  simp only [rowVec, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  have h : ∀ j : Fin (R.testCount K ι), (if (R.cellOf a = K ∧ R.labelOf a = ι) ∧
      R.testOf a = (j : ℕ) then (x a : ℂ) * rowPartFactor (R.realPart a) else 0) * g j =
      if (R.cellOf a = K ∧ R.labelOf a = ι) ∧ R.testOf a = (j : ℕ) then
        (x a : ℂ) * rowPartFactor (R.realPart a) * g (R.testOf a) else 0 := by
    intro j
    split_ifs with hc
    · rw [hc.2]
    · simp
  rw [Finset.sum_congr rfl fun j _ => h j]
  exact sum_fin_ite _ _ _ (fun hc => by rw [← hc.1, ← hc.2]; exact hR.test_index a)
    (fun _ => (x a : ℂ) * rowPartFactor (R.realPart a) * g (R.testOf a))

theorem pairingMatrix_mulVec (hR : IsRowValues M R m tauMax) (x : Fin rowCount → ℝ) (a : Fin rowCount) :
    (R.testPairingMatrix M.box *ᵥ x) a = 2 * Real.pi * blockFactor (R.labelOf a) *
      (rowPartFactor (R.realPart a) * ∑ j : Fin (R.testCount (R.cellOf a) (R.labelOf a)),
        starRingEnd ℂ (rowVec R x (R.cellOf a) (R.labelOf a) j) *
          blockEntry R M.box (R.cellOf a) (R.labelOf a) j (R.testOf a)).re := by
  have hs := sum_conj_rowVec_mul hR x (R.cellOf a) (R.labelOf a)
    (fun n => blockEntry R M.box (R.cellOf a) (R.labelOf a) n (R.testOf a))
  rw [hs]
  simp only [Matrix.mulVec, dotProduct, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  by_cases hb : R.cellOf b = R.cellOf a ∧ R.labelOf b = R.labelOf a
  · rw [if_pos hb, entry_eq hR a b hb.1 hb.2]
    rw [show rowPartFactor (R.realPart a) * ((x b : ℂ) * starRingEnd ℂ (rowPartFactor (R.realPart b)) *
        blockEntry R M.box (R.cellOf a) (R.labelOf a) (R.testOf b) (R.testOf a)) =
        (x b : ℂ) * (rowPartFactor (R.realPart a) * starRingEnd ℂ (rowPartFactor (R.realPart b)) *
        blockEntry R M.box (R.cellOf a) (R.labelOf a) (R.testOf b) (R.testOf a)) by ring,
      Complex.re_ofReal_mul]
    ring
  · have hns : ¬ R.SameBlock a b := fun h => hb ⟨h.1.symm, (sameBlock_label hR h).symm⟩
    rw [if_neg hb, entry_zero hns]
    simp

theorem solutionVec_im (hR : IsRowValues M R m tauMax) {K : Fin M.count} {ι : ℤ × ℤ} (hT : ι ∈ M.tested K)
    (hz : ι = -ι) (j : Fin (R.testCount K ι)) : (solutionVec M R m F K ι j).im = 0 := by
  have hTr : ∀ i < R.testCount K ι, ∀ c p, starRingEnd ℂ ((R.testField K ι i c).eval (M.box K) p) =
      (R.testField K ι i c).eval (M.box K) p := by
    intro i hi c p
    have h := (hR.tests_conj K ι hT).2 i hi c p
    rw [← hz] at h
    conv_lhs => rw [h]
    exact Complex.conj_conj _
  have hVr : ∀ p c, starRingEnd ℂ (labelVel m ι F p c) = labelVel m ι F p c := by
    intro p c
    have h := labelVel_neg m ι F p c
    rw [← hz] at h
    exact h.symm
  have hA : ∀ i k : Fin (R.testCount K ι), starRingEnd ℂ (R.testBlockMatrix M.box K ι i k) =
      R.testBlockMatrix M.box K ι i k := by
    intro i k
    unfold RowValues.testBlockMatrix
    refine conj_setIntegral_eq _ _ fun p => ?_
    simp [map_sum, hTr i i.isLt, hTr k k.isLt]
  have hu : ∀ i : Fin (R.testCount K ι), starRingEnd ℂ (R.cellMoment M.box m K ι F i) =
      R.cellMoment M.box m K ι F i := by
    intro i
    unfold RowValues.cellMoment
    refine conj_setIntegral_eq _ _ fun p => ?_
    simp [map_sum, hTr i i.isLt, hVr]
  unfold solutionVec
  rw [Pi.smul_apply, smul_eq_mul, Complex.im_ofReal_mul, inv_mulVec_im _ _ hA hu j, mul_zero]

theorem pairingMatrix_mulVec_solution (hR : IsRowValues M R m tauMax) (a : Fin rowCount) :
    (R.testPairingMatrix M.box *ᵥ solution M R m F) a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re := by
  have hT := hR.row_tested a
  have ht := hR.test_index a
  have hsum : ∑ j : Fin (R.testCount (R.cellOf a) (R.labelOf a)),
      starRingEnd ℂ (rowVec R (solution M R m F) (R.cellOf a) (R.labelOf a) j) *
        blockEntry R M.box (R.cellOf a) (R.labelOf a) j (R.testOf a) =
      starRingEnd ℂ (((2 / blockFactor (R.labelOf a) : ℝ) : ℂ) *
        momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a)) := by
    have hv := congrFun (blockMatrix_mulVec_solution (F := F) hR hT) ⟨R.testOf a, ht⟩
    unfold momentAt
    rw [dif_pos ht]
    simp only [Pi.smul_apply, smul_eq_mul] at hv
    rw [← hv]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rowVec_solution hR a ⟨rfl, rfl⟩ (fun hz => solutionVec_im hR hT hz) j, testBlockMatrix_apply,
      blockEntry_conj R M.box _ _ (R.testOf a) j]
    ring
  rw [pairingMatrix_mulVec hR, hsum, map_mul, Complex.conj_ofReal]
  rw [show rowPartFactor (R.realPart a) * (((2 / blockFactor (R.labelOf a) : ℝ) : ℂ) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))) =
      ((2 / blockFactor (R.labelOf a) : ℝ) : ℂ) * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))) by ring,
    Complex.re_ofReal_mul]
  have hb := (blockFactor_pos (R.labelOf a)).ne'
  field_simp
  ring

theorem inv_mulVec_eq (hR : IsRowValues M R m tauMax) (hpd : (R.testPairingMatrix M.box).PosDef)
    (P : Fin rowCount → ℝ) (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re) :
    (R.testPairingMatrix M.box)⁻¹ *ᵥ P = solution M R m F := by
  have hGP : R.testPairingMatrix M.box *ᵥ solution M R m F = P :=
    funext fun a => (pairingMatrix_mulVec_solution hR a).trans (hP a).symm
  have hdet : IsUnit (R.testPairingMatrix M.box).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp hpd.isUnit
  rw [← hGP, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mulVec]

theorem blockSum_eq (hR : IsRowValues M R m tauMax) (P : Fin rowCount → ℝ)
    (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re)
    (K : Fin M.count) (ι : ℤ × ℤ) :
    blockSum M R m F P K ι = 4 * Real.pi * R.testWeight K ι *
      (∑ j : Fin (R.testCount K ι), rowVec R (solution M R m F) K ι j *
        starRingEnd ℂ (momentAt M R m F K ι j)).re := by
  have hs := sum_rowVec_mul hR (solution M R m F) K ι (fun n => starRingEnd ℂ (momentAt M R m F K ι n))
  rw [hs, Complex.re_sum, Finset.mul_sum]
  unfold blockSum
  refine Finset.sum_congr rfl fun a _ => ?_
  by_cases hc : R.cellOf a = K ∧ R.labelOf a = ι
  · rw [if_pos hc, if_pos hc, hP a, hc.1, hc.2]
    rw [show (solution M R m F a : ℂ) * rowPartFactor (R.realPart a) *
        starRingEnd ℂ (momentAt M R m F K ι (R.testOf a)) = (solution M R m F a : ℂ) *
        (rowPartFactor (R.realPart a) * starRingEnd ℂ (momentAt M R m F K ι (R.testOf a))) by ring,
      Complex.re_ofReal_mul]
    ring
  · rw [if_neg hc, if_neg hc, Complex.zero_re, mul_zero]

theorem blockSum_of_row (hR : IsRowValues M R m tauMax) (P : Fin rowCount → ℝ)
    (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re)
    {K : Fin M.count} {ι : ℤ × ℤ} (a0 : Fin rowCount) (h0 : R.cellOf a0 = K ∧ R.labelOf a0 = ι) :
    blockSum M R m F P K ι = 4 * Real.pi * (2 / blockFactor ι) * blockForm M R m F K ι := by
  have hT : ι ∈ M.tested K := by
    rw [← h0.1, ← h0.2]
    exact hR.row_tested a0
  have hsum : ∑ j : Fin (R.testCount K ι), rowVec R (solution M R m F) K ι j *
      starRingEnd ℂ (momentAt M R m F K ι j) =
      star (R.cellMoment M.box m K ι F) ⬝ᵥ solutionVec M R m F K ι := by
    simp only [dotProduct, Pi.star_apply, Complex.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rowVec_solution hR a0 h0 (fun hz => solutionVec_im hR hT hz) j]
    unfold momentAt
    rw [dif_pos j.isLt]
    ring
  have hdot : star (R.cellMoment M.box m K ι F) ⬝ᵥ solutionVec M R m F K ι =
      ((2 / blockFactor ι : ℝ) : ℂ) * (star (R.cellMoment M.box m K ι F) ⬝ᵥ
        ((R.testBlockMatrix M.box K ι)⁻¹ *ᵥ R.cellMoment M.box m K ι F)) := by
    unfold solutionVec
    rw [dotProduct_smul, smul_eq_mul]
  rw [blockSum_eq hR P hP, hsum, hdot, Complex.re_ofReal_mul]
  unfold blockForm
  ring

theorem blockSum_of_empty (P : Fin rowCount → ℝ) {K : Fin M.count} {ι : ℤ × ℤ}
    (h : ¬ ∃ a, R.cellOf a = K ∧ R.labelOf a = ι) : blockSum M R m F P K ι = 0 :=
  Finset.sum_eq_zero fun a _ => if_neg fun hc => h ⟨a, hc⟩

theorem blockForm_neg (hR : IsRowValues M R m tauMax) {K : Fin M.count} {ι : ℤ × ℤ} (hT : ι ∈ M.tested K) :
    blockForm M R m F K (-ι) = blockForm M R m F K ι := by
  obtain ⟨hn, hconj⟩ := hR.tests_conj K ι hT
  unfold blockForm
  rw [hR.weight_neg K ι hT]
  congr 1
  refine quad_conj_cast hn _ _ _ _ (fun i k => ?_) (fun i => ?_)
  · unfold RowValues.testBlockMatrix
    rw [← integral_conj]
    congr 1
    funext p
    simp [map_sum, hconj i (hn ▸ i.isLt), hconj k (hn ▸ k.isLt)]
  · unfold RowValues.cellMoment
    rw [← integral_conj]
    congr 1
    funext p
    simp [map_sum, hconj i (hn ▸ i.isLt), labelVel_neg]

theorem blockForm_zero {K : Fin M.count} {ι : ℤ × ℤ} (h : R.testCount K ι = 0) :
    blockForm M R m F K ι = 0 := by
  unfold blockForm
  rw [quad_eq_zero h]
  simp

theorem pair_of_row (hR : IsRowValues M R m tauMax) (P : Fin rowCount → ℝ)
    (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re)
    {K : Fin M.count} {ι : ℤ × ℤ} (hT : ι ∈ M.tested K) (a0 : Fin rowCount)
    (h0 : R.cellOf a0 = K ∧ R.labelOf a0 = ι) :
    blockSum M R m F P K ι + blockSum M R m F P K (-ι) =
      4 * Real.pi * (blockForm M R m F K ι + blockForm M R m F K (-ι)) := by
  rw [blockForm_neg hR hT, blockSum_of_row hR P hP a0 h0]
  by_cases hz : ι = -ι
  · rw [← hz, blockSum_of_row hR P hP a0 h0]
    simp only [blockFactor, if_pos hz]
    ring
  · have hne : ¬ ∃ a, R.cellOf a = K ∧ R.labelOf a = -ι := by
      rintro ⟨a, ha⟩
      have h := hR.rows_one_member a a0 (ha.1.trans h0.1.symm) (by rw [ha.2, h0.2])
      rw [ha.2, h0.2] at h
      exact hz h.symm
    rw [blockSum_of_empty P hne]
    simp only [blockFactor, if_neg hz]
    ring

theorem pair_sum (hR : IsRowValues M R m tauMax) (P : Fin rowCount → ℝ)
    (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re)
    {K : Fin M.count} {ι : ℤ × ℤ} (hT : ι ∈ M.tested K) :
    blockSum M R m F P K ι + blockSum M R m F P K (-ι) =
      4 * Real.pi * (blockForm M R m F K ι + blockForm M R m F K (-ι)) := by
  by_cases h1 : ∃ a, R.cellOf a = K ∧ R.labelOf a = ι
  · obtain ⟨a0, h0⟩ := h1
    exact pair_of_row hR P hP hT a0 h0
  by_cases h2 : ∃ a, R.cellOf a = K ∧ R.labelOf a = -ι
  · obtain ⟨a0, h0⟩ := h2
    have h := pair_of_row hR P hP (hR.mesh_valid.tested_neg K ι hT) a0 h0
    rw [neg_neg] at h
    linarith
  · have hc : R.testCount K ι = 0 := by
      by_contra hne
      obtain ⟨a, ha1, ha2, -, -⟩ := hR.rows_complete K ι hT 0 (Nat.pos_of_ne_zero hne) true fun _ => rfl
      rcases ha2 with h | h
      · exact h1 ⟨a, ha1, h⟩
      · exact h2 ⟨a, ha1, h⟩
    rw [blockSum_of_empty P h1, blockSum_of_empty P h2, blockForm_neg hR hT, blockForm_zero hc]
    ring

theorem tested_sum (hR : IsRowValues M R m tauMax) (P : Fin rowCount → ℝ)
    (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re)
    (K : Fin M.count) :
    ∑ ι ∈ M.tested K, blockSum M R m F P K ι = 4 * Real.pi * ∑ ι ∈ M.tested K, blockForm M R m F K ι := by
  have hneg : ∀ f : ℤ × ℤ → ℝ, ∑ ι ∈ M.tested K, f (-ι) = ∑ ι ∈ M.tested K, f ι := fun f =>
    Finset.sum_nbij' (fun ι => -ι) (fun ι => -ι) (fun ι h => hR.mesh_valid.tested_neg K ι h)
      (fun ι h => hR.mesh_valid.tested_neg K ι h) (fun ι _ => neg_neg ι) (fun ι _ => neg_neg ι)
      (fun ι _ => rfl)
  have h := Finset.sum_congr rfl fun ι (hι : ι ∈ M.tested K) => pair_sum hR P hP hι
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, hneg (blockSum M R m F P K),
    hneg (blockForm M R m F K)] at h
  linarith

theorem sum_by_block (hR : IsRowValues M R m tauMax) (g : Fin rowCount → ℝ) :
    ∑ a, g a = ∑ K, ∑ ι ∈ M.tested K, ∑ a, if R.cellOf a = K ∧ R.labelOf a = ι then g a else 0 := by
  have key : ∀ a, ∑ K, ∑ ι ∈ M.tested K, (if R.cellOf a = K ∧ R.labelOf a = ι then g a else 0) = g a := by
    intro a
    rw [Finset.sum_eq_single (R.cellOf a)]
    · rw [Finset.sum_eq_single_of_mem (R.labelOf a) (hR.row_tested a)]
      · rw [if_pos ⟨rfl, rfl⟩]
      · intro ι _ hι
        rw [if_neg fun h => hι h.2.symm]
    · intro K _ hK
      exact Finset.sum_eq_zero fun ι _ => if_neg fun h => hK h.1.symm
    · intro h
      exact absurd (Finset.mem_univ _) h
  calc ∑ a, g a = ∑ a, ∑ K, ∑ ι ∈ M.tested K, (if R.cellOf a = K ∧ R.labelOf a = ι then g a else 0) :=
        (Finset.sum_congr rfl fun a _ => key a).symm
    _ = ∑ K, ∑ a, ∑ ι ∈ M.tested K, (if R.cellOf a = K ∧ R.labelOf a = ι then g a else 0) :=
        Finset.sum_comm
    _ = ∑ K, ∑ ι ∈ M.tested K, ∑ a, (if R.cellOf a = K ∧ R.labelOf a = ι then g a else 0) :=
        Finset.sum_congr rfl fun K _ => Finset.sum_comm

theorem weighted_form_eq (hR : IsRowValues M R m tauMax) (hpd : (R.testPairingMatrix M.box).PosDef)
    (P : Fin rowCount → ℝ) (hP : ∀ a, P a = 4 * Real.pi * (rowPartFactor (R.realPart a) *
      starRingEnd ℂ (momentAt M R m F (R.cellOf a) (R.labelOf a) (R.testOf a))).re) :
    ∑ a, ∑ b, R.testWeight (R.cellOf a) (R.labelOf a) * (R.testPairingMatrix M.box)⁻¹ a b * P a * P b =
      4 * Real.pi * ∑ K, ∑ ι ∈ M.tested K, R.testWeight K ι *
        (star (R.cellMoment M.box m K ι F) ⬝ᵥ
          ((R.testBlockMatrix M.box K ι)⁻¹ *ᵥ R.cellMoment M.box m K ι F)).re := by
  have hsol := inv_mulVec_eq hR hpd P hP
  have h1 : ∑ a, ∑ b, R.testWeight (R.cellOf a) (R.labelOf a) * (R.testPairingMatrix M.box)⁻¹ a b *
      P a * P b = ∑ a, R.testWeight (R.cellOf a) (R.labelOf a) * P a * solution M R m F a := by
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hsol]
    simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [h1, sum_by_block hR, Finset.mul_sum]
  exact Finset.sum_congr rfl fun K _ => tested_sum hR P hP K

theorem classForm_of_integrable (hpair : GeneratorPairingMatrixFormula) (hpd : RowPairingPosDef)
    (hmom : GeneratorPairingMoments) (hnorm : RowNormIdentity) {c : ℝ} (hR : IsRowValues M R m tauMax)
    (hc : 0 < c) (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume)
    (hFp : IsTimePeriodic F) (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤)
    (hflip : ∀ σ y, F σ (flipPoint y) = flipPoint (F σ y))
    (hint : ∀ K ι c, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m ι F p c) (M.box K).rect) :
    c * rowNorm (R.rowFieldOf M.box m) (R.rowWeightOf c) F ^ 2 =
      4 * Real.pi * ∑ K, ∑ ι ∈ M.tested K, R.testWeight K ι *
        (dotProduct (star (R.cellMoment M.box m K ι F))
          (Matrix.mulVec (R.testBlockMatrix M.box K ι)⁻¹ (R.cellMoment M.box m K ι F))).re := by
  have hG := hpd M R m tauMax hR
  have hpf := hpair M R m tauMax hR
  have hG' : (R.fieldPairingMatrix M.box m).PosDef := by
    rw [hpf]
    exact hG
  rw [hnorm M R m tauMax c hR hc hG' F hFm hFp hF2, hpf]
  exact weighted_form_eq hR hG (fun a => periodPairing F (R.generatorField M.box m a))
    (fun a => pairing_eq hR hmom hFm hFp hF2 hflip hint a)

end ClassForm

end Internal

def LabelVelIntegrableOnBounded : Prop :=
  ∀ (F : ℝ → Space → Space), AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume →
    periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤ → ∀ (m : ℕ) (κ : ℤ × ℤ) (S : Set (ℝ × ℝ)),
    MeasurableSet S → Bornology.IsBounded S → S ⊆ {p | 0 ≤ p.1} → ∀ c : Fin 3,
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * labelVel m κ F p c) S

open Internal.ClassForm Internal.RowPairing in
theorem rowsClassForm_of (hvel : LabelVelIntegrableOnBounded) (hpair : GeneratorPairingMatrixFormula)
    (hpd : RowPairingPosDef) (hmom : GeneratorPairingMoments) (hnorm : RowNormIdentity) : RowsClassForm := by
  intro rowCount M R m tauMax c hR hc F hFm hFp hF2 hflip
  refine classForm_of_integrable hpair hpd hmom hnorm hR hc hFm hFp hF2 hflip fun K ι c' => ?_
  have hK := hR.mesh_valid.box_valid K
  exact hvel F hFm hF2 m ι _ (measurableSet_Icc.prod measurableSet_Icc) (rect_compact _).isBounded
    (fun p hp => le_trans hK.r_order.1 hp.1.1) c'

end Instance

end CertCell

end Breakdown
