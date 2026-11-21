import Breakdown.CertCell.AssemblyStatements
import Breakdown.CertCell.LabelResolvedEnergy
import Breakdown.CertCell.LabelModeFacts
import Breakdown.CertCell.LocalAngularFrame
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.SixthPower
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SecondDerivEnergyIdentity
import Breakdown.FracCell.SharpEnergyVorticityIdentity
import Breakdown.FracCell.SharpEnergyStrainIdentity
import Breakdown.FracCell.BasisEnergySum
import Breakdown.FracCell.ProjCoef

open MeasureTheory

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCert.CellAnalysis CellCert.CellEnergy CellCalculus

namespace Internal.TailGain

open CellCert.CellAnalysis.SharpEnergyVorticityIdentityInternal

theorem coef_congr {K : CellBox} (B : CellBases) {F F' : ℝ × ℝ → ℂ} (h : F =ᵐ[volume.restrict K.rect] F')
    (j l : ℕ) : B.coef K F j l = B.coef K F' j l := by
  unfold CellBases.coef
  exact integral_congr_ae (h.mono fun p hp => by simp only [hp])

theorem eigen_nonneg {K : CellBox} (j l : ℕ) : 0 ≤ radialEigen K j ∧ 0 ≤ heightEigen K l := by
  refine ⟨?_, ?_⟩
  · unfold radialEigen
    split_ifs <;> positivity
  · unfold heightEigen
    positivity

theorem innerRadius_nonneg {K : CellBox} (hK : IsCellBox K) : 0 ≤ K.innerRadius := by
  unfold CellBox.innerRadius
  split_ifs
  · exact zero_le_one
  · exact hK.r_order.1

theorem min_le_eigen {K : CellBox} {Q j l : ℕ} (h : Q < max j l) :
    min (radialEigen K (Q + 1)) (heightEigen K (Q + 1)) ≤ radialEigen K j + heightEigen K l := by
  have h0 : (0 : ℝ) ≤ (Q : ℝ) := Nat.cast_nonneg Q
  rcases lt_max_iff.mp h with hj | hl
  · have hj' : (Q : ℝ) + 1 ≤ (j : ℝ) := by
      have : Q + 1 ≤ j := hj
      exact_mod_cast this
    have hr : radialEigen K (Q + 1) ≤ radialEigen K j := by
      unfold radialEigen
      push_cast
      split_ifs
      · exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
      · exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    linarith [min_le_left (radialEigen K (Q + 1)) (heightEigen K (Q + 1)), (eigen_nonneg (K := K) j l).2]
  · have hl' : (Q : ℝ) + 1 ≤ (l : ℝ) := by
      have : Q + 1 ≤ l := hl
      exact_mod_cast this
    have hz : heightEigen K (Q + 1) ≤ heightEigen K l := by
      unfold heightEigen
      push_cast
      exact mul_le_mul_of_nonneg_right (by nlinarith) (sq_nonneg _)
    linarith [min_le_right (radialEigen K (Q + 1)) (heightEigen K (Q + 1)), (eigen_nonneg (K := K) j l).1]

theorem tail_hasSum {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (Q : ℕ)
    (F : ℝ × ℝ → ℂ) (hFm : AEStronglyMeasurable F (volume.restrict K.rect))
    (hFi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect) :
    HasSum (fun jl : ℕ × ℕ => if Q < max jl.1 jl.2 then ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) (K.tailNormSq Q F) := by
  obtain ⟨hT, hc⟩ := projCoef_holds K B hK hB F ⟨hFm, hFi⟩ Q
  have hP := basisEnergySum_holds K B hK hB Unit (fun _ => fun p => F p - K.proj Q Q F p)
    (fun _ => fun p => F p - K.proj Q Q F p) (fun _ => hT) (fun _ => hT)
  simp only [Finset.univ_unique, Finset.sum_singleton] at hP
  rw [← Complex.hasSum_ofReal]
  convert hP using 1
  · funext jl
    rw [hc jl.1 jl.2, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    by_cases h : Q < max jl.1 jl.2
    · rw [if_pos h, if_neg (not_le.mpr h)]
    · rw [if_neg h, if_pos (not_lt.mp h)]
      simp
  · unfold CellBox.tailNormSq CellBox.normSqOn CellBox.lineWeightFn
    rw [← integral_complex_ofReal]
    congr 1
    funext p
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    push_cast
    ring

theorem grad_tail_sum {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (Q : ℕ)
    (F Fr Fz : ℝ × ℝ → ℂ) (hFm : AEStronglyMeasurable F (volume.restrict K.rect))
    (hFi : IntegrableOn (fun p => K.lineWeight p.1 * ‖F p‖ ^ 2) K.rect)
    (hRm : AEStronglyMeasurable Fr (volume.restrict K.rect)) (hRi : IntegrableOn (fun p => p.1 * ‖Fr p‖ ^ 2) K.rect)
    (hZm : AEStronglyMeasurable Fz (volume.restrict K.rect)) (hZi : IntegrableOn (fun p => p.1 * ‖Fz p‖ ^ 2) K.rect)
    (hR : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr p * ψ p
          = -∫ p in K.rect, F p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p)
    (hZ : ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F p * CellBox.heightDeriv ψ p) :
    Summable (fun jl : ℕ × ℕ => if Q < max jl.1 jl.2 then
      (radialEigen K jl.1 + heightEigen K jl.2) * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) ∧
    K.innerRadius * (∑' jl : ℕ × ℕ, if Q < max jl.1 jl.2 then
      (radialEigen K jl.1 + heightEigen K jl.2) * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.tailGradWeight Q F Fr Fz := by
  have hRt := radial_tail K B hK hB Q F Fr hFm hRm hFi hRi hR
  have hZt := height_tail K B hK hB Q F Fz hFm hZm hFi hZi hZ
  have hfin : ∀ T : Finset (ℕ × ℕ), ∑ jl ∈ T, (if Q < max jl.1 jl.2 then
      (radialEigen K jl.1 + heightEigen K jl.2) * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0)
      ≤ K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refR p.1 ^ 2))
          (fun p => Fr p - CellBox.radialDeriv (K.proj Q Q F) p)
        + K.normSqOn (fun p => K.lineWeight p.1 * (1 - K.refZ p.2 ^ 2))
          (fun p => Fz p - CellBox.heightDeriv (K.proj Q Q F) p) := by
    intro T
    refine le_trans (le_of_eq ?_) (add_le_add (hRt T) (hZt T))
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun jl _ => ?_
    split_ifs <;> ring
  have hn : ∀ jl : ℕ × ℕ, 0 ≤ (if Q < max jl.1 jl.2 then
      (radialEigen K jl.1 + heightEigen K jl.2) * ‖B.coef K F jl.1 jl.2‖ ^ 2 else 0) := fun jl => by
    split_ifs
    · exact mul_nonneg (add_nonneg (eigen_nonneg (K := K) jl.1 jl.2).1 (eigen_nonneg (K := K) jl.1 jl.2).2) (sq_nonneg _)
    · exact le_rfl
  have hs := summable_of_sum_le hn hfin
  exact ⟨hs, mul_le_mul_of_nonneg_left (hs.tsum_le_of_sum_le hfin) (innerRadius_nonneg hK)⟩

theorem gain_core {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (Q : ℕ)
    {β : Type*} [Fintype β] (F Fr Fz θ L : β → ℝ × ℝ → ℂ) (g c : ℝ) (hc : 0 ≤ c)
    (hFm : ∀ i, AEStronglyMeasurable (F i) (volume.restrict K.rect))
    (hFi : ∀ i, IntegrableOn (fun p => K.lineWeight p.1 * ‖F i p‖ ^ 2) K.rect)
    (hRm : ∀ i, AEStronglyMeasurable (Fr i) (volume.restrict K.rect))
    (hRi : ∀ i, IntegrableOn (fun p => p.1 * ‖Fr i p‖ ^ 2) K.rect)
    (hZm : ∀ i, AEStronglyMeasurable (Fz i) (volume.restrict K.rect))
    (hZi : ∀ i, IntegrableOn (fun p => p.1 * ‖Fz i p‖ ^ 2) K.rect)
    (hR : ∀ i, ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ z, ψ (K.r₁, z) = 0) → (∀ z, ψ (K.r₂, z) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fr i p * ψ p
          = -∫ p in K.rect, F i p * CellBox.radialDeriv (fun p => (K.lineWeight p.1 : ℂ) * ψ p) p)
    (hZ : ∀ i, ∀ ψ : ℝ × ℝ → ℂ, ContDiff ℝ 1 ψ → (∀ r, ψ (r, K.z₁) = 0) → (∀ r, ψ (r, K.z₂) = 0) →
        ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * Fz i p * ψ p
          = -∫ p in K.rect, (K.lineWeight p.1 : ℂ) * F i p * CellBox.heightDeriv ψ p)
    (hθ : ∀ i, θ i =ᵐ[volume.restrict K.rect] L i)
    (hLm : ∀ i, AEStronglyMeasurable (L i) (volume.restrict K.rect))
    (hLi : ∀ i, IntegrableOn (fun p => K.lineWeight p.1 * ‖L i p‖ ^ 2) K.rect)
    (hpt : ∀ j l : ℕ, Q < max j l → g * ∑ i, ‖B.coef K (F i) j l‖ ^ 2
      ≤ K.innerRadius * (radialEigen K j + heightEigen K l) * ∑ i, ‖B.coef K (F i) j l‖ ^ 2
        + c * ∑ i, ‖B.coef K (L i) j l‖ ^ 2) :
    g * ∑ i, K.tailNormSq Q (F i) ≤ ∑ i, (K.tailGradWeight Q (F i) (Fr i) (Fz i) + c * K.tailNormSq Q (θ i)) := by
  have P := fun i => tail_hasSum hK hB Q (F i) (hFm i) (hFi i)
  have Gd := fun i => grad_tail_sum hK hB Q (F i) (Fr i) (Fz i) (hFm i) (hFi i) (hRm i) (hRi i) (hZm i) (hZi i)
    (hR i) (hZ i)
  have hθm : ∀ i, AEStronglyMeasurable (θ i) (volume.restrict K.rect) := fun i => (hLm i).congr (hθ i).symm
  have hθi : ∀ i, IntegrableOn (fun p => K.lineWeight p.1 * ‖θ i p‖ ^ 2) K.rect := fun i =>
    (hLi i).congr ((hθ i).mono fun p hp => by simp only [hp])
  have A := fun i => SharpEnergyStrainIdentityInternal.coefSq_tail hB Q (θ i) (hθm i) (hθi i)
  have eC : ∀ i j l, B.coef K (θ i) j l = B.coef K (L i) j l := fun i j l => coef_congr B (hθ i) j l
  have h1 := (hasSum_sum (s := Finset.univ) fun i _ => P i).mul_left g
  have h2 := hasSum_sum (s := Finset.univ) fun i _ =>
    (((Gd i).1.hasSum.mul_left K.innerRadius).add ((A i).1.hasSum.mul_left c))
  refine le_trans (hasSum_le (fun jl => ?_) h1 h2) ?_
  · by_cases h : Q < max jl.1 jl.2
    · simp only [if_pos h, eC]
      refine le_trans (hpt jl.1 jl.2 h) (le_of_eq ?_)
      rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      refine congrArg₂ (· + ·) (Finset.sum_congr rfl fun i _ => by ring) rfl
    · simp only [if_neg h, Finset.sum_const_zero, mul_zero, add_zero, le_refl]
  · exact Finset.sum_le_sum fun i _ => add_le_add (Gd i).2 (mul_le_mul_of_nonneg_left (A i).2 hc)

theorem tail_le_core {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (Q : ℕ)
    {β γ : Type*} [Fintype β] [Fintype γ] (F : β → ℝ × ℝ → ℂ) (F' : γ → ℝ × ℝ → ℂ)
    (hFm : ∀ i, AEStronglyMeasurable (F i) (volume.restrict K.rect))
    (hFi : ∀ i, IntegrableOn (fun p => K.lineWeight p.1 * ‖F i p‖ ^ 2) K.rect)
    (hGm : ∀ i, AEStronglyMeasurable (F' i) (volume.restrict K.rect))
    (hGi : ∀ i, IntegrableOn (fun p => K.lineWeight p.1 * ‖F' i p‖ ^ 2) K.rect) (c : ℝ)
    (hpt : ∀ j l : ℕ, Q < max j l → ∑ i, ‖B.coef K (F i) j l‖ ^ 2 ≤ c * ∑ i, ‖B.coef K (F' i) j l‖ ^ 2) :
    ∑ i, K.tailNormSq Q (F i) ≤ c * ∑ i, K.tailNormSq Q (F' i) := by
  have h1 := hasSum_sum (s := Finset.univ) fun i _ => tail_hasSum hK hB Q (F i) (hFm i) (hFi i)
  have h2 := (hasSum_sum (s := Finset.univ) fun i _ => tail_hasSum hK hB Q (F' i) (hGm i) (hGi i)).mul_left c
  refine hasSum_le (fun jl => ?_) h1 h2
  by_cases h : Q < max jl.1 jl.2
  · simp only [if_pos h]
    exact hpt _ _ h
  · simp only [if_neg h, Finset.sum_const_zero, mul_zero, le_refl]

theorem gain_point {K : CellBox} (hK : IsCellBox K) (n : ℤ) (k0 shift : ℝ) (hshift : 0 ≤ shift)
    (hax : K.r₁ = 0 → k0 = 0) {Q j l : ℕ} (hjl : Q < max j l) (S M : ℝ) (hS : 0 ≤ S)
    (hM : max (|k0| - shift) 0 ^ 2 * S ≤ M) :
    TailBand.tailGain K Q |k0| shift * S
      ≤ K.innerRadius * (radialEigen K j + heightEigen K l) * S + K.angularWeight n * M := by
  have h1 : K.innerRadius * min (radialEigen K (Q + 1)) (heightEigen K (Q + 1)) * S
      ≤ K.innerRadius * (radialEigen K j + heightEigen K l) * S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (min_le_eigen hjl) (innerRadius_nonneg hK)) hS
  have hMn : 0 ≤ M := le_trans (mul_nonneg (sq_nonneg _) hS) hM
  have h2 : max (|k0| - shift) 0 ^ 2 / K.r₂ * S ≤ K.angularWeight n * M := by
    by_cases h0 : K.r₁ = 0
    · have e : max (|k0| - shift) 0 = 0 := by
        rw [hax h0, abs_zero, zero_sub]
        exact max_eq_right (by linarith)
      rw [e]
      calc (0 : ℝ) ^ 2 / K.r₂ * S = 0 := by ring
        _ ≤ K.angularWeight n * M := mul_nonneg (angW_nonneg hK n) hMn
    · have hw : K.angularWeight n = K.r₂⁻¹ := by
        unfold CellBox.angularWeight
        rw [if_neg h0]
      rw [hw, div_eq_inv_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left hM (inv_nonneg.mpr (by linarith [hK.r_order.1, hK.r_order.2]))
  unfold TailBand.tailGain
  rw [add_mul]
  linarith

theorem turned_ae {K : CellBox} (hK : IsCellBox K) (m : ℕ) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hs : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ) (a b : Fin 3) :
    ∀ᵐ p ∂(volume.restrict K.rect), turnedSlopeAt m ι H a b p
      = ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m ι.1) a b a' b' * gradAt m ι G a' b' p := by
  obtain ⟨ν, n, hev, rfl⟩ := LabelModeFacts.Internal.exists_harmonic ι
  obtain ⟨hc, hsn, hprof⟩ := harmonicLift_holds m v G H hs ν
  have hAc := LocalField.localAngularFrame m _ _ _ hc K hK n a b
  have hAs := LocalField.localAngularFrame m _ _ _ hsn K hK n a b
  filter_upwards [LabelModeFacts.Internal.ae_rect_pos K hK, ae_restrict_of_ae (hprof n hev), hAc, hAs]
    with p hp hq h1 h2
  obtain ⟨-, hg, hh⟩ := hq hp
  have e1 : (p.1 : ℂ) * modeThird m n (harmonicCos ν H) a b 1 p = ∑ a' : Fin 3, ∑ b' : Fin 3,
      angularComb (azimuth m n) a b a' b' * gradMode m n (harmonicCos ν G) a' b' p := h1
  have e2 : (p.1 : ℂ) * modeThird m n (harmonicSin ν H) a b 1 p = ∑ a' : Fin 3, ∑ b' : Fin 3,
      angularComb (azimuth m n) a b a' b' * gradMode m n (harmonicSin ν G) a' b' p := h2
  simp only [turnedSlopeAt, hh, hg]
  show (p.1 : ℂ) * (modeThird m n (harmonicCos ν H) a b 1 p + Complex.I * modeThird m n (harmonicSin ν H) a b 1 p)
    = ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m n) a b a' b'
      * (gradMode m n (harmonicCos ν G) a' b' p + Complex.I * gradMode m n (harmonicSin ν G) a' b' p)
  simp only [Fin.sum_univ_three] at e1 e2 ⊢
  linear_combination e1 + Complex.I * e2


theorem strain_shift (k : ℝ) (s : Fin 3 → Fin 3 → ℂ) :
    max (|k| - 2) 0 ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2
      ≤ ∑ a : Fin 3, ∑ b : Fin 3, ‖∑ a' : Fin 3, ∑ b' : Fin 3, angularComb k a b a' b' * s a' b'‖ ^ 2 := by
  have hcb := SharpEnergyStrainIdentityInternal.comb_bound k s
  have hsp := SharpEnergyStrainIdentityInternal.split_sq s
  have hanti : 0 ≤ antiSq s := by
    unfold antiSq
    positivity
  have hmono : max (|k| - 2) 0 ^ 2 ≤ max (|k| - 1) 0 ^ 2 :=
    pow_le_pow_left₀ (le_max_right _ _) (max_le_max (by linarith) le_rfl) 2
  have e : ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 = symSq s + antiSq s := by
    rw [hsp]
    rfl
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_right hmono hanti]

theorem curl_le (s : Fin 3 → Fin 3 → ℂ) :
    ∑ i : Fin 3, ‖curlComp s i‖ ^ 2 ≤ 2 * ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 := by
  have h1 := anti_curl s
  have hsp := SharpEnergyStrainIdentityInternal.split_sq s
  have hsym : 0 ≤ symSq s := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => sq_nonneg _
  have e : ∑ a : Fin 3, ∑ b : Fin 3, ‖s a b‖ ^ 2 = symSq s + antiSq s := by
    rw [hsp]
    rfl
  rw [e, ← h1]
  linarith

open CellCert.CellAnalysis.ResolvedEnergyInternal LabelResolvedEnergyInternal in
theorem label_tail_gain {K : CellBox} {B : CellBases} (hK : IsCellBox K) (hB : IsCellBases K B) (m Q : ℕ)
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (hs : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ)
    (hax : K.r₁ = 0 → azimuth m ι.1 = 0) :
    TailBand.hessTailGain K Q |azimuth m ι.1| * (∑ a : Fin 3, ∑ b : Fin 3, K.tailNormSq Q (fun p => gradAt m ι G a b p))
        ≤ labelStrainTail K m ι Q G H ∧
      TailBand.curlTailGain K Q |azimuth m ι.1| * (∑ i : Fin 3, K.tailNormSq Q (fun p => curlComp (gradArray m ι G p) i))
        ≤ labelVorticityTail K m ι Q G H ∧
      (∑ i : Fin 3, K.tailNormSq Q (fun p => curlComp (gradArray m ι G p) i))
        ≤ 2 * ∑ a : Fin 3, ∑ b : Fin 3, K.tailNormSq Q (fun p => gradAt m ι G a b p) := by
  have fact := fun Cf : Fin 3 → Fin 3 → ℂ => labelModeFacts_holds harmonicLift_holds K hK m v G H hs ι Cf
  have hg : ∀ a b, comboGradAt (unitCoef a b) m ι G = gradAt m ι G a b :=
    fun a b => funext fun p => unit_sum a b _
  have ht : ∀ a b c, comboSlopeAt (unitCoef a b) m ι H c = fun p => slopeAt m ι H a b c p :=
    fun a b c => funext fun p => unit_sum a b _
  have hgc : ∀ i, comboGradAt (curlCoef i) m ι G = fun p => curlComp (fun a b => gradAt m ι G a b p) i :=
    fun i => funext fun p => curl_sum i _
  have htc : ∀ i c, comboSlopeAt (curlCoef i) m ι H c = fun p => curlComp (fun a b => slopeAt m ι H a b c p) i :=
    fun i c => funext fun p => curl_sum i _
  have hgm : ∀ a b, AEStronglyMeasurable (gradAt m ι G a b) (volume.restrict K.rect) ∧
      IntegrableOn (fun p => K.lineWeight p.1 * ‖gradAt m ι G a b p‖ ^ 2) K.rect := fun a b => by
    have h1 : AEStronglyMeasurable (comboGradAt (unitCoef a b) m ι G) (volume.restrict K.rect) :=
      (fact (unitCoef a b)).1
    have h2 : IntegrableOn (fun p => K.lineWeight p.1 * ‖comboGradAt (unitCoef a b) m ι G p‖ ^ 2) K.rect :=
      (fact (unitCoef a b)).2.1
    rw [hg a b] at h1 h2
    exact ⟨h1, h2⟩
  have hcoef : ∀ (Cf : Fin 3 → Fin 3 → ℂ) (j l : ℕ), B.coef K (comboGradAt Cf m ι G) j l
      = ∑ a : Fin 3, ∑ b : Fin 3, Cf a b * B.coef K (gradAt m ι G a b) j l :=
    fun Cf j l => coef_lin (gradAt m ι G) Cf j l (fun a b => bas_int _ (hgm a b).1 (hgm a b).2 j l)
  have hall : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a b, turnedSlopeAt m ι H a b p
      = ∑ a' : Fin 3, ∑ b' : Fin 3, angularComb (azimuth m ι.1) a b a' b' * gradAt m ι G a' b' p := by
    rw [ae_all_iff]
    intro a
    rw [ae_all_iff]
    intro b
    exact turned_ae hK m hs ι a b
  refine ⟨?_, ?_, ?_⟩
  · have hcore := gain_core hK hB Q (β := Fin 3 × Fin 3)
      (fun x => comboGradAt (unitCoef x.1 x.2) m ι G) (fun x => comboSlopeAt (unitCoef x.1 x.2) m ι H 0)
      (fun x => comboSlopeAt (unitCoef x.1 x.2) m ι H 2) (fun x => turnedSlopeAt m ι H x.1 x.2)
      (fun x => comboGradAt (angularComb (azimuth m ι.1) x.1 x.2) m ι G)
      (TailBand.hessTailGain K Q |azimuth m ι.1|) (K.angularWeight ι.1) (angW_nonneg hK _)
      (fun x => (fact (unitCoef x.1 x.2)).1) (fun x => (fact (unitCoef x.1 x.2)).2.1)
      (fun x => ((fact (unitCoef x.1 x.2)).2.2.1 0).1) (fun x => ((fact (unitCoef x.1 x.2)).2.2.1 0).2)
      (fun x => ((fact (unitCoef x.1 x.2)).2.2.1 2).1) (fun x => ((fact (unitCoef x.1 x.2)).2.2.1 2).2)
      (fun x => (fact (unitCoef x.1 x.2)).2.2.2.1) (fun x => (fact (unitCoef x.1 x.2)).2.2.2.2)
      (fun x => hall.mono fun p hp => hp x.1 x.2)
      (fun x => (fact (angularComb (azimuth m ι.1) x.1 x.2)).1)
      (fun x => (fact (angularComb (azimuth m ι.1) x.1 x.2)).2.1) ?_
    · simp only [Fintype.sum_prod_type, hg, ht] at hcore
      exact hcore
    · intro j l hjl
      simp only [hcoef, unit_sum, Fintype.sum_prod_type]
      exact gain_point hK ι.1 (azimuth m ι.1) 2 (by norm_num) hax hjl _ _ (by positivity) (strain_shift _ _)
  · have hcore := gain_core hK hB Q (β := Fin 3)
      (fun i => comboGradAt (curlCoef i) m ι G) (fun i => comboSlopeAt (curlCoef i) m ι H 0)
      (fun i => comboSlopeAt (curlCoef i) m ι H 2) (fun i p => curlComp (fun a b => turnedSlopeAt m ι H a b p) i)
      (fun i => comboGradAt (fun a' b' => ∑ a : Fin 3, ∑ b : Fin 3,
        curlCoef i a b * angularComb (azimuth m ι.1) a b a' b') m ι G)
      (TailBand.curlTailGain K Q |azimuth m ι.1|) (K.angularWeight ι.1) (angW_nonneg hK _)
      (fun i => (fact (curlCoef i)).1) (fun i => (fact (curlCoef i)).2.1)
      (fun i => ((fact (curlCoef i)).2.2.1 0).1) (fun i => ((fact (curlCoef i)).2.2.1 0).2)
      (fun i => ((fact (curlCoef i)).2.2.1 2).1) (fun i => ((fact (curlCoef i)).2.2.1 2).2)
      (fun i => (fact (curlCoef i)).2.2.2.1) (fun i => (fact (curlCoef i)).2.2.2.2)
      (fun i => hall.mono fun p hp => by
        simp only [hp]
        exact curl_expand (fun a b a' b' => angularComb (azimuth m ι.1) a b a' b')
          (fun a' b' => gradAt m ι G a' b' p) i)
      (fun i => (fact (fun a' b' => ∑ a : Fin 3, ∑ b : Fin 3,
        curlCoef i a b * angularComb (azimuth m ι.1) a b a' b')).1)
      (fun i => (fact (fun a' b' => ∑ a : Fin 3, ∑ b : Fin 3,
        curlCoef i a b * angularComb (azimuth m ι.1) a b a' b')).2.1) ?_
    · simp only [hgc, htc] at hcore
      exact hcore
    · intro j l hjl
      have eL : ∀ i, B.coef K (comboGradAt (fun a' b' => ∑ a : Fin 3, ∑ b : Fin 3,
          curlCoef i a b * angularComb (azimuth m ι.1) a b a' b') m ι G) j l
          = curlComp (fun a b => ∑ a' : Fin 3, ∑ b' : Fin 3,
            angularComb (azimuth m ι.1) a b a' b' * B.coef K (gradAt m ι G a' b') j l) i := fun i => by
        rw [hcoef]
        exact (curl_expand (fun a b a' b' => angularComb (azimuth m ι.1) a b a' b')
          (fun a' b' => B.coef K (gradAt m ι G a' b') j l) i).symm
      simp only [eL]
      simp only [hcoef, curl_sum]
      exact gain_point hK ι.1 (azimuth m ι.1) 1 (by norm_num) hax hjl _ _ (by positivity) (ang_ineq _ _)
  · have h3 := tail_le_core hK hB Q (β := Fin 3) (γ := Fin 3 × Fin 3)
      (fun i => comboGradAt (curlCoef i) m ι G) (fun x => comboGradAt (unitCoef x.1 x.2) m ι G)
      (fun i => (fact (curlCoef i)).1) (fun i => (fact (curlCoef i)).2.1)
      (fun x => (fact (unitCoef x.1 x.2)).1) (fun x => (fact (unitCoef x.1 x.2)).2.1) 2 ?_
    · simp only [Fintype.sum_prod_type, hg, hgc] at h3
      exact h3
    · intro j l _
      simp only [hcoef, curl_sum, unit_sum, Fintype.sum_prod_type]
      exact curl_le _

end Internal.TailGain

theorem tailGainHolds : TailGainHolds := by
  intro k Cty nE nM D R _ _ hC K q v G H gg κ Fs Pg hT ι hι
  obtain ⟨c0, S0, -, -, hL⟩ := (hC.layouts_valid K).layout_valid ι hι
  have hs : IsPeriodicSecondOrder v G H :=
    periodicSecondOrder_of_perturbation (Bridge.velocitySixthIntegral ⟨_, sixthPowerGradientBound_four_thirds⟩)
      Bridge.secondDerivEnergyIdentity _ _ v G H gg hT.perturbation
  have hk : ((labelAzimuth D.azimuthOrder ι : ℤ) : ℝ) = azimuth D.azimuthOrder ι.1 := by
    simp [labelAzimuth, azimuth]
  have hax : (D.mesh.box K).r₁ = 0 → azimuth D.azimuthOrder ι.1 = 0 := fun h => by
    simp [azimuth, hC.axis_modes K h ι hι]
  rw [hk]
  exact Internal.TailGain.label_tail_gain hL.box_valid hL.bases_valid D.azimuthOrder _ hs ι hax

end Breakdown.CertCell.Assembly
