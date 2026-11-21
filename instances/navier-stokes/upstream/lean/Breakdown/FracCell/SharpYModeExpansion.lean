import Breakdown.FracCell.SharpYChargeSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly SharpParts


namespace ModeExpansionParts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

def sharpPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p)

def lowSharpPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (lowGrad c K S x n p) (lowVel c K S x n p) (sharpGrad c K S x n' p) (sharpVel c K S x n' p)

def sharpLowPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (sharpGrad c K S x n p) (sharpVel c K S x n p) (lowGrad c K S x n' p) (lowVel c K S x n' p)

def lowLowPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ :=
  pairWave c n n' p (lowGrad c K S x n p) (lowVel c K S x n p) (lowGrad c K S x n' p) (lowVel c K S x n' p)

def crossPair (n n' : ℤ) (p : ℝ × ℝ) : ℂ := lowSharpPair c K S x n n' p + sharpLowPair c K S x n' n p

def fieldSharp (E : Space → (Space →L[ℝ] Space)) (n : ℤ) (p : ℝ × ℝ) : ℂ :=
  entryPairing (sharpGrad c K S x n p) (fun a b => modeMat c.order n E p.1 p.2 a b)

def fieldLow (E : Space → (Space →L[ℝ] Space)) (n : ℤ) (p : ℝ × ℝ) : ℂ :=
  entryPairing (lowGrad c K S x n p) (fun a b => modeMat c.order n E p.1 p.2 a b)

def energyAt (n : ℤ) (p : ℝ × ℝ) : ℝ :=
  (c.innerWeight - c.coercivity) * secondModeSq c.order n x.2.2.1 p
    + (c.splitVisc - c.innerWeight) * curlGradModeSq c.order n x.2.2.1 p

end ModeExpansionParts

open ModeExpansionParts


def ModeExpansionRegularStatement : Prop :=
  ∀ (α : ℝ), 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (c : FracCellData k N), IsFormData α c →
    ∀ (K : CellBox) (S : CellScalars) (B : CellBases) (Cl : CellClasses) {slots : ℕ}
      (R : CellRows N slots k), IsCellData α c K S B Cl R → IsAxisymmetricWeight c K →
    ∀ x : FieldTuple k, IsAdmissible c x →
      (∀ᵐ p ∂(volume.restrict K.rect),
        (∀ n, Summable (fun n' => sharpPair c K S x n n' p)) ∧
        Summable (fun n => ∑' n', sharpPair c K S x n n' p) ∧
        (∀ n ∈ S.resolved, Summable (fun n' => lowSharpPair c K S x n n' p) ∧
          Summable (fun n' => sharpLowPair c K S x n' n p)) ∧
        (∀ i, Summable (fun n => fieldSharp c K S x (c.modelActuatorGrad i) n p) ∧
          Summable (fun n => fieldSharp c K S x (c.modelPinField i) n p))) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * energyAt c x n p) K.rect) ∧
      (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * densityAt c x α n p) K.rect) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * modeLocalDensity c α x n p‖) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * energyAt c x n p) ∧
      Summable (fun n : ℤ => ∫ p in K.rect, p.1 * densityAt c x α n p) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * ∑' n : ℤ, modeLocalDensity c α x n p) K.rect ∧
      (∀ n ∈ S.resolved, ∀ n' ∈ S.resolved,
        IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * lowLowPair c K S x n n' p) K.rect) ∧
      (∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * lowMatrixDensity c K S x n p) K.rect) ∧
      (∀ n ∈ S.resolved, ∀ n', IntegrableOn (fun p : ℝ × ℝ => p.1 * (crossPair c K S x n n' p).re) K.rect) ∧
      (∀ n ∈ S.resolved, Summable (fun n' : ℤ => ∫ p in K.rect, ‖p.1 * (crossPair c K S x n n' p).re‖)) ∧
      (∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n', crossPair c K S x n n' p).re) K.rect) ∧
      IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, ∑' n', sharpPair c K S x n n' p).re) K.rect ∧
      ∀ i, ∀ E, (E = c.modelActuatorGrad i ∨ E = c.modelPinField i) →
        (∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (fieldSharp c K S x E n p).re) K.rect) ∧
        Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (fieldSharp c K S x E n p).re‖) ∧
        IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, fieldSharp c K S x E n p).re) K.rect ∧
        (∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * fieldLow c K S x E n p) K.rect)

namespace SharpYModeExpansion.Internal

theorem curl_add (s₁ s₂ : Fin 3 → Fin 3 → ℂ) (i : Fin 3) : curlComp (s₁ + s₂) i = curlComp s₁ i + curlComp s₂ i := by
  simp only [curlComp, Pi.add_apply, mul_add, Finset.sum_add_distrib]

theorem coupling_add (Gm : Fin 3 → Fin 3 → ℂ) (v₁ v₂ : Fin 3 → ℂ) :
    couplingMap Gm (v₁ + v₂) = couplingMap Gm v₁ + couplingMap Gm v₂ := by
  funext i l
  simp only [couplingMap, bracketMat, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  ring

theorem pairing_add_left (s₁ s₂ t : Fin 3 → Fin 3 → ℂ) : entryPairing (s₁ + s₂) t = entryPairing s₁ t + entryPairing s₂ t := by
  simp only [entryPairing, Pi.add_apply, add_mul, Finset.sum_add_distrib]

theorem pairing_add_right (s t₁ t₂ : Fin 3 → Fin 3 → ℂ) : entryPairing s (t₁ + t₂) = entryPairing s t₁ + entryPairing s t₂ := by
  simp only [entryPairing, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib]

theorem wave_add_left (Sb Gb Gm : Fin 3 → Fin 3 → ℂ) (s₁ s₂ : Fin 3 → Fin 3 → ℂ) (v₁ v₂ : Fin 3 → ℂ)
    (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    waveForm Sb Gb Gm (s₁ + s₂) (v₁ + v₂) s' v' = waveForm Sb Gb Gm s₁ v₁ s' v' + waveForm Sb Gb Gm s₂ v₂ s' v' := by
  simp only [waveForm, curl_add, coupling_add, pairing_add_right, map_add, add_mul, Finset.sum_add_distrib]
  ring

theorem wave_add_right (Sb Gb Gm : Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ)
    (s₁ s₂ : Fin 3 → Fin 3 → ℂ) (v₁ v₂ : Fin 3 → ℂ) :
    waveForm Sb Gb Gm s v (s₁ + s₂) (v₁ + v₂) = waveForm Sb Gb Gm s v s₁ v₁ + waveForm Sb Gb Gm s v s₂ v₂ := by
  simp only [waveForm, curl_add, coupling_add, pairing_add_left, mul_add, Finset.sum_add_distrib]
  ring

theorem wave_zero_left (Sb Gb Gm : Fin 3 → Fin 3 → ℂ) (s' : Fin 3 → Fin 3 → ℂ) (v' : Fin 3 → ℂ) :
    waveForm Sb Gb Gm 0 0 s' v' = 0 := by
  simp [waveForm, curlComp, couplingMap, bracketMat, entryPairing]

theorem wave_zero_right (Sb Gb Gm : Fin 3 → Fin 3 → ℂ) (s : Fin 3 → Fin 3 → ℂ) (v : Fin 3 → ℂ) :
    waveForm Sb Gb Gm s v 0 0 = 0 := by
  simp [waveForm, curlComp, couplingMap, bracketMat, entryPairing]


section Pointwise

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem grad_split (n : ℤ) (p : ℝ × ℝ) :
    (fun a b => gradMode c.order n x.2.1 a b p) = lowGrad c K S x n p + sharpGrad c K S x n p := by
  funext a b
  simp [sharpGrad]

theorem vel_split (n : ℤ) (p : ℝ × ℝ) :
    modeVec c.order n x.1 p.1 p.2 = lowVel c K S x n p + sharpVel c K S x n p := by
  funext a
  simp [sharpVel]

theorem low_zero {n : ℤ} (h : n ∉ S.resolved) (p : ℝ × ℝ) : lowGrad c K S x n p = 0 ∧ lowVel c K S x n p = 0 := by
  simp [lowGrad, lowVel, h]

theorem lowLow_zero {n n' : ℤ} (h : n ∉ S.resolved ∨ n' ∉ S.resolved) (p : ℝ × ℝ) : lowLowPair c K S x n n' p = 0 := by
  rcases h with h | h
  · rw [lowLowPair, pairWave, (low_zero c K S x h p).1, (low_zero c K S x h p).2, wave_zero_left]
  · rw [lowLowPair, pairWave, (low_zero c K S x h p).1, (low_zero c K S x h p).2, wave_zero_right]

theorem lowSharp_zero {n : ℤ} (h : n ∉ S.resolved) (n' : ℤ) (p : ℝ × ℝ) : lowSharpPair c K S x n n' p = 0 := by
  rw [lowSharpPair, pairWave, (low_zero c K S x h p).1, (low_zero c K S x h p).2, wave_zero_left]

theorem sharpLow_zero (n : ℤ) {n' : ℤ} (h : n' ∉ S.resolved) (p : ℝ × ℝ) : sharpLowPair c K S x n n' p = 0 := by
  rw [sharpLowPair, pairWave, (low_zero c K S x h p).1, (low_zero c K S x h p).2, wave_zero_right]

theorem wave_split (n n' : ℤ) (p : ℝ × ℝ) :
    waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p)
      (fun a b => gradMode c.order n x.2.1 a b p) (modeVec c.order n x.1 p.1 p.2)
      (fun a b => gradMode c.order n' x.2.1 a b p) (modeVec c.order n' x.1 p.1 p.2)
    = lowLowPair c K S x n n' p + lowSharpPair c K S x n n' p + sharpLowPair c K S x n n' p + sharpPair c K S x n n' p := by
  rw [grad_split c K S x n p, vel_split c K S x n p, grad_split c K S x n' p, vel_split c K S x n' p,
    wave_add_left, wave_add_right, wave_add_right]
  simp only [lowLowPair, lowSharpPair, sharpLowPair, sharpPair, pairWave]
  ring

theorem coupling_split (p : ℝ × ℝ) (h1 : ∀ n, Summable (fun n' => sharpPair c K S x n n' p))
    (h2 : Summable (fun n => ∑' n', sharpPair c K S x n n' p))
    (h3 : ∀ n ∈ S.resolved, Summable (fun n' => lowSharpPair c K S x n n' p) ∧
      Summable (fun n' => sharpLowPair c K S x n' n p)) :
    modeCoupling c x p = ((∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, lowLowPair c K S x n n' p)
      + (∑ n ∈ S.resolved, ∑' n', crossPair c K S x n n' p) + ∑' n, ∑' n', sharpPair c K S x n n' p).re := by
  have hA : ∀ n, Summable (fun n' => lowLowPair c K S x n n' p) := fun n =>
    summable_of_ne_finset_zero (s := S.resolved) (fun n' hn' => lowLow_zero c K S x (Or.inr hn') p)
  have hAt : ∀ n, ∑' n', lowLowPair c K S x n n' p = ∑ n' ∈ S.resolved, lowLowPair c K S x n n' p := fun n =>
    tsum_eq_sum (fun n' hn' => lowLow_zero c K S x (Or.inr hn') p)
  have hB : ∀ n, Summable (fun n' => lowSharpPair c K S x n n' p) := by
    intro n
    by_cases hn : n ∈ S.resolved
    · exact (h3 n hn).1
    · have : (fun n' => lowSharpPair c K S x n n' p) = fun _ => 0 := funext (fun n' => lowSharp_zero c K S x hn n' p)
      rw [this]; exact summable_zero
  have hC : ∀ n, Summable (fun n' => sharpLowPair c K S x n n' p) := fun n =>
    summable_of_ne_finset_zero (s := S.resolved) (fun n' hn' => sharpLow_zero c K S x n hn' p)
  have hCt : ∀ n, ∑' n', sharpLowPair c K S x n n' p = ∑ n' ∈ S.resolved, sharpLowPair c K S x n n' p := fun n =>
    tsum_eq_sum (fun n' hn' => sharpLow_zero c K S x n hn' p)
  have inner : ∀ n, ∑' n', waveForm (CellScalars.strainMode c (n - n') p) (CellScalars.curlGradMode c (n - n') p)
      (CellScalars.curlGradMode c (n' - n) p)
      (fun a b => gradMode c.order n x.2.1 a b p) (modeVec c.order n x.1 p.1 p.2)
      (fun a b => gradMode c.order n' x.2.1 a b p) (modeVec c.order n' x.1 p.1 p.2)
      = (∑ n' ∈ S.resolved, lowLowPair c K S x n n' p) + (∑' n', lowSharpPair c K S x n n' p)
        + (∑ n' ∈ S.resolved, sharpLowPair c K S x n n' p) + ∑' n', sharpPair c K S x n n' p := by
    intro n
    simp only [wave_split c K S x n]
    rw [Summable.tsum_add (((hA n).add (hB n)).add (hC n)) (h1 n), Summable.tsum_add ((hA n).add (hB n)) (hC n),
      Summable.tsum_add (hA n) (hB n), hAt, hCt]
  rw [modeCoupling]
  simp only [inner]
  have sA : Summable (fun n => ∑ n' ∈ S.resolved, lowLowPair c K S x n n' p) :=
    summable_of_ne_finset_zero (s := S.resolved) (fun n hn => Finset.sum_eq_zero (fun n' _ => lowLow_zero c K S x (Or.inl hn) p))
  have sB : Summable (fun n => ∑' n', lowSharpPair c K S x n n' p) :=
    summable_of_ne_finset_zero (s := S.resolved) (fun n hn => by
      simp only [lowSharp_zero c K S x hn, tsum_zero])
  have sC : Summable (fun n => ∑ n' ∈ S.resolved, sharpLowPair c K S x n n' p) :=
    summable_sum (fun n' hn' => (h3 n' hn').2)
  rw [Summable.tsum_add ((sA.add sB).add sC) h2, Summable.tsum_add (sA.add sB) sC, Summable.tsum_add sA sB,
    tsum_eq_sum (s := S.resolved) (fun n hn => Finset.sum_eq_zero (fun n' _ => lowLow_zero c K S x (Or.inl hn) p)),
    tsum_eq_sum (s := S.resolved) (fun n hn => by simp only [lowSharp_zero c K S x hn, tsum_zero]),
    Summable.tsum_finsetSum (fun n' hn' => (h3 n' hn').2)]
  have hX : ∑ n ∈ S.resolved, ∑' n', crossPair c K S x n n' p
      = (∑ n ∈ S.resolved, ∑' n', lowSharpPair c K S x n n' p) + ∑ n ∈ S.resolved, ∑' n', sharpLowPair c K S x n' n p := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n hn => Summable.tsum_add (h3 n hn).1 (h3 n hn).2)
  rw [hX]
  congr 1
  ring

end Pointwise


section Integrals

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem weight_rhat (p : ℝ × ℝ) : K.lineWeight p.1 * CellScalars.rHat K p = p.1 := by
  unfold CellScalars.rHat CellBox.lineWeight
  split_ifs with h
  · by_cases hp : p.1 = 0
    · simp [hp]
    · field_simp
  · simp

theorem re_integral {f : ℝ × ℝ → ℂ} (h : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * f p) K.rect) :
    (∫ p in K.rect, (p.1 : ℂ) * f p).re = ∫ p in K.rect, p.1 * (f p).re := by
  have e := integral_re h
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at e
  exact e.symm

theorem re_integrable {f : ℝ × ℝ → ℂ} (h : IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * f p) K.rect) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (f p).re) K.rect := by
  have e := h.re
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at e
  exact e

theorem field_split (E : Space → (Space →L[ℝ] Space)) (p : ℝ × ℝ) (h : Summable (fun n => fieldSharp c K S x E n p)) :
    modeFieldPair c x.2.1 E p = ((∑ n ∈ S.resolved, fieldLow c K S x E n p) + ∑' n, fieldSharp c K S x E n p).re := by
  have hsplit : ∀ n, entryPairing (fun a b => gradMode c.order n x.2.1 a b p) (fun a b => modeMat c.order n E p.1 p.2 a b)
      = fieldLow c K S x E n p + fieldSharp c K S x E n p := by
    intro n
    rw [grad_split c K S x n p, pairing_add_left]
    rfl
  have hz : ∀ n ∉ S.resolved, fieldLow c K S x E n p = 0 := by
    intro n hn
    simp [fieldLow, (low_zero c K S x hn p).1, entryPairing]
  have hL : Summable (fun n => fieldLow c K S x E n p) := summable_of_ne_finset_zero (s := S.resolved) hz
  rw [modeFieldPair]
  simp only [hsplit]
  rw [Summable.tsum_add hL h, tsum_eq_sum (s := S.resolved) hz]

theorem density_part (α : ℝ)
    (hE : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * energyAt c x n p) K.rect)
    (hD : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * densityAt c x α n p) K.rect)
    (hM : Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * modeLocalDensity c α x n p‖))
    (hEs : Summable (fun n : ℤ => ∫ p in K.rect, p.1 * energyAt c x n p))
    (hDs : Summable (fun n : ℤ => ∫ p in K.rect, p.1 * densityAt c x α n p)) :
    modeEnergy c K x + densitySum c K x α = ∫ p in K.rect, p.1 * ∑' n : ℤ, modeLocalDensity c α x n p := by
  have split : ∀ n p, p.1 * modeLocalDensity c α x n p = p.1 * energyAt c x n p + p.1 * densityAt c x α n p := by
    intro n p
    simp only [modeLocalDensity, energyAt, densityAt]
    ring
  have hint : ∀ n, Integrable (fun p : ℝ × ℝ => p.1 * modeLocalDensity c α x n p) (volume.restrict K.rect) := by
    intro n
    simp only [split]
    exact Integrable.add (hE n) (hD n)
  have e1 : (fun p : ℝ × ℝ => p.1 * ∑' n : ℤ, modeLocalDensity c α x n p)
      = fun p => ∑' n : ℤ, p.1 * modeLocalDensity c α x n p := funext (fun p => tsum_mul_left.symm)
  rw [e1, ← integral_tsum_of_summable_integral_norm hint hM]
  have e2 : modeEnergy c K x = ∑' n : ℤ, ∫ p in K.rect, p.1 * energyAt c x n p := rfl
  have e3 : densitySum c K x α = ∑' n : ℤ, ∫ p in K.rect, p.1 * densityAt c x α n p := rfl
  rw [e2, e3, ← Summable.tsum_add hEs hDs]
  congr 1
  funext n
  simp only [split]
  rw [integral_add (hE n) (hD n)]

theorem series_part {f : ℤ → ℝ × ℝ → ℂ} (hae : ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n => f n p))
    (hI : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (f n p).re) K.rect)
    (hS : Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (f n p).re‖)) :
    ∫ p in K.rect, p.1 * (∑' n, f n p).re = ∑' n, ∫ p in K.rect, p.1 * (f n p).re := by
  rw [integral_tsum_of_summable_integral_norm hI hS]
  refine integral_congr_ae ?_
  filter_upwards [hae] with p hp
  rw [Complex.re_tsum hp, tsum_mul_left]

theorem cross_part (T : Set ℤ)
    (hae : ∀ n ∈ S.resolved, ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n' => crossPair c K S x n n' p))
    (hXint : ∀ n ∈ S.resolved, ∀ n', IntegrableOn (fun p : ℝ × ℝ => p.1 * (crossPair c K S x n n' p).re) K.rect)
    (hXsum : ∀ n ∈ S.resolved, Summable (fun n' : ℤ => ∫ p in K.rect, ‖p.1 * (crossPair c K S x n n' p).re‖)) :
    crossOn c K S x T + crossOn c K S x Tᶜ
      = ∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (∑' n', crossPair c K S x n n' p).re := by
  classical
  unfold crossOn
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  rw [series_part K (hae n hn) (hXint n hn) (hXsum n hn)]
  have hT : ∀ T' : Set ℤ, Summable (fun n' => ∫ p in K.rect, p.1 * (if n' ∈ T' then crossPair c K S x n n' p else 0).re) := by
    intro T'
    refine (hXsum n hn).of_norm_bounded (fun n' => ?_)
    by_cases h : n' ∈ T'
    · simp only [h, if_true]
      exact norm_integral_le_integral_norm _
    · simp only [h, if_false, Complex.zero_re, mul_zero, integral_zero, norm_zero]
      exact integral_nonneg (fun _ => norm_nonneg _)
  show (∑' n', ∫ p in K.rect, p.1 * (if n' ∈ T then crossPair c K S x n n' p else 0).re)
      + (∑' n', ∫ p in K.rect, p.1 * (@ite ℂ (n' ∈ Tᶜ) (Classical.propDecidable _) (crossPair c K S x n n' p) 0).re) = _
  rw [← Summable.tsum_add (hT T) (hT Tᶜ)]
  congr 1
  funext n'
  by_cases h : n' ∈ T
  · have h' : n' ∉ Tᶜ := fun hc => hc h
    simp only [h, h', if_true, if_false, Complex.zero_re, mul_zero, integral_zero, add_zero]
  · have h' : n' ∈ Tᶜ := h
    simp only [h, h', if_true, if_false, Complex.zero_re, mul_zero, integral_zero, zero_add]

end Integrals

section Parts

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem coupling_part
    (hae : ∀ᵐ p ∂(volume.restrict K.rect), (∀ n, Summable (fun n' => sharpPair c K S x n n' p)) ∧
      Summable (fun n => ∑' n', sharpPair c K S x n n' p) ∧
      (∀ n ∈ S.resolved, Summable (fun n' => lowSharpPair c K S x n n' p) ∧
        Summable (fun n' => sharpLowPair c K S x n' n p)))
    (hLL : ∀ n ∈ S.resolved, ∀ n' ∈ S.resolved,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * lowLowPair c K S x n n' p) K.rect)
    (hXt : ∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n', crossPair c K S x n n' p).re) K.rect)
    (hSS : IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, ∑' n', sharpPair c K S x n n' p).re) K.rect) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * modeCoupling c x p) K.rect ∧
      ∫ p in K.rect, p.1 * modeCoupling c x p
        = (∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, ∫ p in K.rect, p.1 * (lowLowPair c K S x n n' p).re)
          + (∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (∑' n', crossPair c K S x n n' p).re) + sharpSharp c K S x := by
  have hLLr : ∀ n ∈ S.resolved, ∀ n' ∈ S.resolved,
      Integrable (fun p : ℝ × ℝ => p.1 * (lowLowPair c K S x n n' p).re) (volume.restrict K.rect) :=
    fun n hn n' hn' => re_integrable K (hLL n hn n' hn')
  have hI1 : ∀ n ∈ S.resolved, Integrable (fun p : ℝ × ℝ =>
      ∑ n' ∈ S.resolved, p.1 * (lowLowPair c K S x n n' p).re) (volume.restrict K.rect) :=
    fun n hn => integrable_finsetSum _ (fun n' hn' => hLLr n hn n' hn')
  have hI2 : Integrable (fun p : ℝ × ℝ => ∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, p.1 * (lowLowPair c K S x n n' p).re)
      (volume.restrict K.rect) := integrable_finsetSum _ hI1
  have hI3 : Integrable (fun p : ℝ × ℝ => ∑ n ∈ S.resolved, p.1 * (∑' n', crossPair c K S x n n' p).re)
      (volume.restrict K.rect) := integrable_finsetSum _ hXt
  have heq : (fun p : ℝ × ℝ => p.1 * modeCoupling c x p) =ᵐ[volume.restrict K.rect] fun p =>
      (∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, p.1 * (lowLowPair c K S x n n' p).re)
        + (∑ n ∈ S.resolved, p.1 * (∑' n', crossPair c K S x n n' p).re)
        + p.1 * (∑' n, ∑' n', sharpPair c K S x n n' p).re := by
    filter_upwards [hae] with p hp
    rw [coupling_split c K S x p hp.1 hp.2.1 hp.2.2]
    simp only [Complex.add_re, Complex.re_sum, mul_add, Finset.mul_sum]
  have hI23 : Integrable (fun p : ℝ × ℝ => (∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, p.1 * (lowLowPair c K S x n n' p).re)
      + (∑ n ∈ S.resolved, p.1 * (∑' n', crossPair c K S x n n' p).re)) (volume.restrict K.rect) := hI2.add hI3
  refine ⟨(hI23.add hSS).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hI23 hSS, integral_add hI2 hI3, integral_finsetSum _ hI1,
    integral_finsetSum _ hXt]
  congr 2
  exact Finset.sum_congr rfl (fun n hn => integral_finsetSum _ (fun n' hn' => hLLr n hn n' hn'))

theorem localPair_part
    (hLL : ∀ n ∈ S.resolved, ∀ n' ∈ S.resolved,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * lowLowPair c K S x n n' p) K.rect)
    (hD : ∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => p.1 * lowMatrixDensity c K S x n p) K.rect) :
    CellScalars.localPairForm c K S x.1 x.2.1 - lowMatrixSum c K S x
      = ∑ n ∈ S.resolved, ∑ n' ∈ S.resolved, ∫ p in K.rect, p.1 * (lowLowPair c K S x n n' p).re := by
  have hpt : ∀ n ∈ S.resolved, ∀ n' ∈ S.resolved, ∀ p : ℝ × ℝ,
      ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) * CellScalars.pairIntegrand c K S x.1 x.2.1 n n' p
        = (p.1 : ℂ) * lowLowPair c K S x n n' p
          + (if n = n' then (((p.1 * lowMatrixDensity c K S x n p : ℝ)) : ℂ) else 0) := by
    intro n hn n' hn' p
    rw [weight_rhat]
    simp only [CellScalars.pairIntegrand, lowLowPair, pairWave, lowGrad, lowVel, lowMatrixDensity, hn, hn', if_true]
    split_ifs with h
    · subst h
      push_cast
      ring
    · ring
  have hval : ∀ n ∈ S.resolved, ∀ n' ∈ S.resolved,
      (∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) * CellScalars.pairIntegrand c K S x.1 x.2.1 n n' p).re
        = (∫ p in K.rect, p.1 * (lowLowPair c K S x n n' p).re)
          + (if n = n' then ∫ p in K.rect, p.1 * lowMatrixDensity c K S x n p else 0) := by
    intro n hn n' hn'
    have hite : Integrable (fun p : ℝ × ℝ => (if n = n' then (((p.1 * lowMatrixDensity c K S x n p : ℝ)) : ℂ) else 0))
        (volume.restrict K.rect) := by
      split_ifs
      · exact (hD n hn).ofReal
      · exact integrable_zero _ _ _
    rw [integral_congr_ae (ae_of_all _ (hpt n hn n' hn')), integral_add (hLL n hn n' hn') hite, Complex.add_re,
      re_integral K (hLL n hn n' hn')]
    congr 1
    split_ifs
    · rw [integral_complex_ofReal, Complex.ofReal_re]
    · simp
  simp only [CellScalars.localPairForm, Complex.re_sum]
  rw [Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun n' hn' => hval n hn n' hn'))]
  simp only [Finset.sum_add_distrib, Finset.sum_ite_eq]
  rw [lowMatrixSum]
  rw [Finset.sum_congr rfl (fun n hn => if_pos hn)]
  ring

theorem field_part (E : Space → (Space →L[ℝ] Space))
    (hae : ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n => fieldSharp c K S x E n p))
    (hI : ∀ n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (fieldSharp c K S x E n p).re) K.rect)
    (hS : Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (fieldSharp c K S x E n p).re‖))
    (hT : IntegrableOn (fun p : ℝ × ℝ => p.1 * (∑' n, fieldSharp c K S x E n p).re) K.rect)
    (hL : ∀ n ∈ S.resolved, IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * fieldLow c K S x E n p) K.rect) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * modeFieldPair c x.2.1 E p) K.rect ∧
      ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 E p
        = (∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (fieldLow c K S x E n p).re)
          + ∑' n, ∫ p in K.rect, p.1 * (fieldSharp c K S x E n p).re := by
  have hLr : ∀ n ∈ S.resolved, Integrable (fun p : ℝ × ℝ => p.1 * (fieldLow c K S x E n p).re) (volume.restrict K.rect) :=
    fun n hn => re_integrable K (hL n hn)
  have hI1 : Integrable (fun p : ℝ × ℝ => ∑ n ∈ S.resolved, p.1 * (fieldLow c K S x E n p).re) (volume.restrict K.rect) :=
    integrable_finsetSum _ hLr
  have heq : (fun p : ℝ × ℝ => p.1 * modeFieldPair c x.2.1 E p) =ᵐ[volume.restrict K.rect] fun p =>
      (∑ n ∈ S.resolved, p.1 * (fieldLow c K S x E n p).re) + p.1 * (∑' n, fieldSharp c K S x E n p).re := by
    filter_upwards [hae] with p hp
    rw [field_split c K S x E p hp]
    simp only [Complex.add_re, Complex.re_sum, mul_add, Finset.mul_sum]
  refine ⟨(hI1.add hT).congr heq.symm, ?_⟩
  rw [integral_congr_ae heq, integral_add hI1 hT, integral_finsetSum _ hLr, series_part K hae hI hS]

end Parts

section Linear

variable {k N : ℕ} (c : FracCellData k N) (K : CellBox) (S : CellScalars) (x : FieldTuple k)

theorem linear_part (ζ : Fin k → ℝ)
    (hLA : ∀ i, ∀ n ∈ S.resolved,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * fieldLow c K S x (c.modelActuatorGrad i) n p) K.rect)
    (hLP : ∀ i, ∀ n ∈ S.resolved,
      IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * fieldLow c K S x (c.modelPinField i) n p) K.rect)
    (hIA : ∀ i n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re) K.rect)
    (hIP : ∀ i n, IntegrableOn (fun p : ℝ × ℝ => p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re) K.rect)
    (hSA : ∀ i, Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re‖))
    (hSP : ∀ i, Summable (fun n : ℤ => ∫ p in K.rect, ‖p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re‖)) :
    CellScalars.linearTerm c K S x.2.2.2.1 ζ x.2.1 + linearSharp c K S x ζ
      = (∑ i, x.2.2.2.1 i * ((∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (fieldLow c K S x (c.modelActuatorGrad i) n p).re)
          + ∑' n, ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re))
        + ∑ i, 2 * ζ i * ((∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (fieldLow c K S x (c.modelPinField i) n p).re)
          + ∑' n, ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re) := by
  have low : ∀ n ∈ S.resolved, ∀ i, (∫ p in K.rect, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
        (((x.2.2.2.1 i / 2 : ℝ) : ℂ) * entryPairing (K.lowStrainAt c.order n S.degHigh x.2.1 p)
            (fun a b => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
          + ((ζ i : ℝ) : ℂ) * entryPairing (K.lowStrainAt c.order n S.degHigh x.2.1 p)
            (fun a b => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))).re
      = x.2.2.2.1 i / 2 * (∫ p in K.rect, p.1 * (fieldLow c K S x (c.modelActuatorGrad i) n p).re)
        + ζ i * ∫ p in K.rect, p.1 * (fieldLow c K S x (c.modelPinField i) n p).re := by
    intro n hn i
    have hpt : ∀ p : ℝ × ℝ, ((K.lineWeight p.1 * CellScalars.rHat K p : ℝ) : ℂ) *
        (((x.2.2.2.1 i / 2 : ℝ) : ℂ) * entryPairing (K.lowStrainAt c.order n S.degHigh x.2.1 p)
            (fun a b => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
          + ((ζ i : ℝ) : ℂ) * entryPairing (K.lowStrainAt c.order n S.degHigh x.2.1 p)
            (fun a b => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))
        = ((x.2.2.2.1 i / 2 : ℝ) : ℂ) * ((p.1 : ℂ) * fieldLow c K S x (c.modelActuatorGrad i) n p)
          + ((ζ i : ℝ) : ℂ) * ((p.1 : ℂ) * fieldLow c K S x (c.modelPinField i) n p) := by
      intro p
      rw [weight_rhat]
      simp only [fieldLow, lowGrad, hn, if_true]
      ring
    rw [integral_congr_ae (ae_of_all _ hpt), integral_add ((hLA i n hn).const_mul _) ((hLP i n hn).const_mul _),
      integral_const_mul, integral_const_mul, Complex.add_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
      re_integral K (hLA i n hn), re_integral K (hLP i n hn)]
  have sharp : ∀ n, ∫ p in K.rect, p.1 * (∑ i : Fin k,
      (((x.2.2.2.1 i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x n p)
          (fun a b => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
        + ((2 * ζ i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x n p)
          (fun a b => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))).re
      = ∑ i, (x.2.2.2.1 i * (∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re)
        + 2 * ζ i * ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re) := by
    intro n
    have hpt : ∀ p : ℝ × ℝ, p.1 * (∑ i : Fin k,
        (((x.2.2.2.1 i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x n p)
            (fun a b => modeMat c.order n (c.modelActuatorGrad i) p.1 p.2 a b)
          + ((2 * ζ i : ℝ) : ℂ) * entryPairing (sharpGrad c K S x n p)
            (fun a b => modeMat c.order n (c.modelPinField i) p.1 p.2 a b))).re
        = ∑ i, (x.2.2.2.1 i * (p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re)
          + 2 * ζ i * (p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re)) := by
      intro p
      simp only [Complex.re_sum, Complex.add_re, Complex.re_ofReal_mul, Finset.mul_sum, fieldSharp]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
    have hint : ∀ i ∈ (Finset.univ : Finset (Fin k)), Integrable (fun p : ℝ × ℝ =>
        x.2.2.2.1 i * (p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re)
          + 2 * ζ i * (p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re)) (volume.restrict K.rect) :=
      fun i _ => ((hIA i n).const_mul _).add ((hIP i n).const_mul _)
    rw [integral_congr_ae (ae_of_all _ hpt), integral_finsetSum _ hint]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [integral_add ((hIA i n).const_mul _) ((hIP i n).const_mul _), integral_const_mul, integral_const_mul]
  have sumA : ∀ i, Summable (fun n : ℤ => ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re) :=
    fun i => (hSA i).of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  have sumP : ∀ i, Summable (fun n : ℤ => ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re) :=
    fun i => (hSP i).of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  rw [CellScalars.linearTerm, Complex.re_sum]
  simp only [Complex.re_sum]
  rw [Finset.sum_congr rfl (fun n hn => Finset.sum_congr rfl (fun i _ => low n hn i))]
  rw [linearSharp]
  simp only [sharp]
  rw [Summable.tsum_finsetSum (fun i _ => ((sumA i).mul_left _).add ((sumP i).mul_left _))]
  simp only [Summable.tsum_add ((sumA _).mul_left _) ((sumP _).mul_left _), tsum_mul_left]
  rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  ring

end Linear

end SharpYModeExpansion.Internal

open SharpYModeExpansion.Internal in
theorem modeExpansion (h : ModeExpansionRegularStatement) : ModeExpansionStatement := by
  intro α h1 h2 k N c hc K S B Cl slots R hK hW x hx ζ
  obtain ⟨hae, hE, hD, hM, hEs, hDs, hMint, hLL, hLD, hXint, hXsum, hXt, hSS, hF⟩ :=
    h α h1 h2 c hc K S B Cl R hK hW x hx
  have hA := fun i => hF i (c.modelActuatorGrad i) (Or.inl rfl)
  have hP := fun i => hF i (c.modelPinField i) (Or.inr rfl)
  obtain ⟨hCi, hCv⟩ := coupling_part c K S x (hae.mono (fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1⟩)) hLL hXt hSS
  have hFA := fun i => field_part c K S x (c.modelActuatorGrad i) (hae.mono (fun p hp => (hp.2.2.2 i).1))
    (hA i).1 (hA i).2.1 (hA i).2.2.1 (hA i).2.2.2
  have hFP := fun i => field_part c K S x (c.modelPinField i) (hae.mono (fun p hp => (hp.2.2.2 i).2))
    (hP i).1 (hP i).2.1 (hP i).2.2.1 (hP i).2.2.2
  have hcross : ∀ n ∈ S.resolved, ∀ᵐ p ∂(volume.restrict K.rect), Summable (fun n' => crossPair c K S x n n' p) :=
    fun n hn => hae.mono (fun p hp => (hp.2.2.1 n hn).1.add (hp.2.2.1 n hn).2)
  have eD := density_part c K x α hE hD hM hEs hDs
  have eL := localPair_part c K S x hLL hLD
  have eX := cross_part c K S x (↑(S.resolved ∪ S.band)) hcross hXint hXsum
  have eLin := linear_part c K S x ζ (fun i => (hA i).2.2.2) (fun i => (hP i).2.2.2) (fun i => (hA i).1)
    (fun i => (hP i).1) (fun i => (hA i).2.1) (fun i => (hP i).2.1)
  have hsumF : ∀ i ∈ (Finset.univ : Finset (Fin k)), Integrable (fun p : ℝ × ℝ =>
      x.2.2.2.1 i * (p.1 * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p)) (volume.restrict K.rect) :=
    fun i _ => (hFA i).1.const_mul _
  have hMC : Integrable (fun p : ℝ × ℝ => p.1 * ∑' n : ℤ, modeLocalDensity c α x n p + p.1 * modeCoupling c x p)
      (volume.restrict K.rect) := hMint.add hCi
  have eRHS : (∫ p in K.rect, p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
        + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
      = (∫ p in K.rect, p.1 * ∑' n : ℤ, modeLocalDensity c α x n p) + (∫ p in K.rect, p.1 * modeCoupling c x p)
        + ∑ i, x.2.2.2.1 i * ∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p := by
    have e : (fun p : ℝ × ℝ => p.1 * ((∑' n : ℤ, modeLocalDensity c α x n p) + modeCoupling c x p
        + ∑ i, x.2.2.2.1 i * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p))
        = fun p => p.1 * ∑' n : ℤ, modeLocalDensity c α x n p + p.1 * modeCoupling c x p
          + ∑ i, x.2.2.2.1 i * (p.1 * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p) := by
      funext p
      rw [mul_add, mul_add, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [e, integral_add hMC (integrable_finsetSum _ hsumF), integral_add hMint hCi, integral_finsetSum _ hsumF]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => integral_const_mul _ _)
  have eAct : ∑ i, x.2.2.2.1 i * (∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelActuatorGrad i) p)
      = ∑ i, x.2.2.2.1 i * ((∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (fieldLow c K S x (c.modelActuatorGrad i) n p).re)
          + ∑' n, ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelActuatorGrad i) n p).re) :=
    Finset.sum_congr rfl (fun i _ => by rw [(hFA i).2])
  have ePin : ∑ i, 2 * ζ i * (∫ p in K.rect, p.1 * modeFieldPair c x.2.1 (c.modelPinField i) p)
      = ∑ i, 2 * ζ i * ((∑ n ∈ S.resolved, ∫ p in K.rect, p.1 * (fieldLow c K S x (c.modelPinField i) n p).re)
          + ∑' n, ∫ p in K.rect, p.1 * (fieldSharp c K S x (c.modelPinField i) n p).re) :=
    Finset.sum_congr rfl (fun i _ => by rw [(hFP i).2])
  apply le_of_eq
  rw [eRHS, ← eD, hCv, eAct, ePin]
  linarith [eL, eX, eLin]

end CellAnalysis

end CellCert

end Breakdown
