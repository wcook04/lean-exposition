import Breakdown.FracCell.ResolvedEnergyCross

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace ResolvedEnergyInternal

theorem combo_bound (hI : ModeSquareIntegrableStatement) (hR : ModeRadialPartsStatement)
    (hZ : ModeHeightPartsStatement) (hC : ResolvedComponentStatement)
    (K : CellBox) (hK : IsCellBox K) (m : ℕ) (Q q : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsSecondOrderField m v G H) (n : ℤ)
    (hn : K.IsAxis → n = 0) (κ : Fin 3 → Fin 3 → ℂ) :
    K.radialEnergy Q q (comboGrad κ m n G) (comboThird κ m n H 0)
        + K.heightEnergy Q q (comboGrad κ m n G) (comboThird κ m n H 2)
        + K.angularEnergy Q (fun p => (p.1 : ℂ) * comboThird κ m n H 1 p)
        + (K.tailGradWeight Q (comboGrad κ m n G) (comboThird κ m n H 0) (comboThird κ m n H 2)
          + K.angularWeight n * K.tailNormSq Q (fun p => (p.1 : ℂ) * comboThird κ m n H 1 p))
      ≤ ∫ p in K.rect, p.1 * (‖comboThird κ m n H 0 p‖ ^ 2 + ‖comboThird κ m n H 1 p‖ ^ 2
          + ‖comboThird κ m n H 2 p‖ ^ 2) := by
  obtain ⟨hFm, hFi, hT⟩ := hI K hK m v G H hs n κ
  exact hC K hK Q q n hn _ _ _ _ hFm (hT 0).1 (hT 2).1 (hT 1).1 hFi (hT 0).2 (hT 2).2 (hT 1).2
    (fun ψ hψ h1 h2 => hR K hK m v G H hs n κ ψ hψ h1 h2)
    (fun ψ hψ h1 h2 => hZ K hK m v G H hs n κ ψ hψ h1 h2)

theorem combo_integrable (hI : ModeSquareIntegrableStatement)
    (K : CellBox) (hK : IsCellBox K) (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (hs : IsSecondOrderField m v G H) (n : ℤ)
    (κ : Fin 3 → Fin 3 → ℂ) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖comboThird κ m n H 0 p‖ ^ 2 + ‖comboThird κ m n H 1 p‖ ^ 2
          + ‖comboThird κ m n H 2 p‖ ^ 2)) K.rect := by
  obtain ⟨-, -, hT⟩ := hI K hK m v G H hs n κ
  have h := (((hT 0).2.add (hT 1).2).add (hT 2).2)
  refine h.congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
  simp only [Pi.add_apply]
  ring

def unitCoef (a b : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a' b' => if a' = a ∧ b' = b then 1 else 0

def curlCoef (i : Fin 3) : Fin 3 → Fin 3 → ℂ := fun a b => (CellCert.permSign i b a : ℂ)

theorem unit_sum (a b : Fin 3) (f : Fin 3 → Fin 3 → ℂ) :
    ∑ a' : Fin 3, ∑ b' : Fin 3, unitCoef a b a' b' * f a' b' = f a b := by
  simp [unitCoef, Fin.sum_univ_three]
  fin_cases a <;> fin_cases b <;> simp

theorem curl_mul (i : Fin 3) (x : ℂ) (f : Fin 3 → Fin 3 → ℂ) :
    curlComp (fun a b => x * f a b) i = x * curlComp f i := by
  simp only [curlComp, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => ?_))
  ring

theorem curl_sum (i : Fin 3) (f : Fin 3 → Fin 3 → ℂ) :
    ∑ a : Fin 3, ∑ b : Fin 3, curlCoef i a b * f a b = curlComp f i := by
  unfold curlComp curlCoef
  rw [Finset.sum_comm]

end ResolvedEnergyInternal

open ResolvedEnergyInternal in
theorem resolvedEnergy_of (hI : ModeSquareIntegrableStatement) (hR : ModeRadialPartsStatement)
    (hZ : ModeHeightPartsStatement) (hC : ResolvedComponentStatement) : ResolvedEnergyStatement := by
  intro K hK m Q q _ _ v G H hs n hn
  constructor
  · have hb := fun a b => combo_bound hI hR hZ hC K hK m Q q v G H hs n hn (unitCoef a b)
    have hg : ∀ a b, comboGrad (unitCoef a b) m n G = gradMode m n G a b := fun a b => by
      funext p; exact unit_sum a b (fun a' b' => gradMode m n G a' b' p)
    have ht : ∀ a b c, comboThird (unitCoef a b) m n H c = fun p => modeThird m n H a b c p := fun a b c => by
      funext p; exact unit_sum a b (fun a' b' => modeThird m n H a' b' c p)
    simp only [hg, ht] at hb
    have hint : ∀ a b, IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
        + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2)) K.rect := fun a b => by
      have := combo_integrable hI K hK m v G H hs n (unitCoef a b)
      simpa only [ht] using this
    calc _ = ∑ a : Fin 3, ∑ b : Fin 3,
          (K.radialEnergy Q q (gradMode m n G a b) (fun p => modeThird m n H a b 0 p)
            + K.heightEnergy Q q (gradMode m n G a b) (fun p => modeThird m n H a b 2 p)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * modeThird m n H a b 1 p)
            + (K.tailGradWeight Q (gradMode m n G a b) (fun p => modeThird m n H a b 0 p)
                (fun p => modeThird m n H a b 2 p)
              + K.angularWeight n * K.tailNormSq Q (fun p => (p.1 : ℂ) * modeThird m n H a b 1 p))) := by
          simp only [CellBox.strainEnergy, ← Finset.sum_add_distrib]
          rfl
      _ ≤ ∑ a : Fin 3, ∑ b : Fin 3, ∫ p in K.rect, p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
            + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2) :=
          Finset.sum_le_sum (fun a _ => Finset.sum_le_sum (fun b _ => hb a b))
      _ = ∑ a : Fin 3, ∫ p in K.rect, ∑ b : Fin 3, p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
            + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2) :=
          Finset.sum_congr rfl (fun a _ => (integral_finsetSum _ (fun b _ => hint a b)).symm)
      _ = ∫ p in K.rect, ∑ a : Fin 3, ∑ b : Fin 3, p.1 * (‖modeThird m n H a b 0 p‖ ^ 2
            + ‖modeThird m n H a b 1 p‖ ^ 2 + ‖modeThird m n H a b 2 p‖ ^ 2) :=
          (integral_finsetSum _ (fun a _ => integrable_finsetSum _ (fun b _ => hint a b))).symm
      _ = ∫ p in K.rect, p.1 * secondModeSq m n H p := by
          congr 1
          funext p
          simp only [secondModeSq, Fin.sum_univ_three]
          ring
  · have hb := fun i => combo_bound hI hR hZ hC K hK m Q q v G H hs n hn (curlCoef i)
    have hg : ∀ i, comboGrad (curlCoef i) m n G = fun p => curlComp (fun a b => gradMode m n G a b p) i :=
      fun i => by funext p; exact curl_sum i (fun a b => gradMode m n G a b p)
    have ht : ∀ i c, comboThird (curlCoef i) m n H c = fun p => curlComp (fun a b => modeThird m n H a b c p) i :=
      fun i c => by funext p; exact curl_sum i (fun a b => modeThird m n H a b c p)
    simp only [hg, ht] at hb
    have hint : ∀ i, IntegrableOn (fun p : ℝ × ℝ => p.1 * (‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
        + ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
        + ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2)) K.rect := fun i => by
      have := combo_integrable hI K hK m v G H hs n (curlCoef i)
      simpa only [ht] using this
    have hang : ∀ i, (fun p : ℝ × ℝ => curlComp (fun a b => angularGradMode m n H a b p) i)
        = fun p => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i := fun i => by
      funext p; exact curl_mul i (p.1 : ℂ) (fun a b => modeThird m n H a b 1 p)
    calc _ = ∑ i : Fin 3,
          (K.radialEnergy Q q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
              (fun p => curlComp (fun a b => modeThird m n H a b 0 p) i)
            + K.heightEnergy Q q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
              (fun p => curlComp (fun a b => modeThird m n H a b 2 p) i)
            + K.angularEnergy Q (fun p => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i)
            + (K.tailGradWeight Q (fun p => curlComp (fun a b => gradMode m n G a b p) i)
                (fun p => curlComp (fun a b => modeThird m n H a b 0 p) i)
                (fun p => curlComp (fun a b => modeThird m n H a b 2 p) i)
              + K.angularWeight n * K.tailNormSq Q
                (fun p => (p.1 : ℂ) * curlComp (fun a b => modeThird m n H a b 1 p) i))) := by
          simp only [CellBox.vorticityEnergy, ← Finset.sum_add_distrib, ← hang]
          rfl
      _ ≤ ∑ i : Fin 3, ∫ p in K.rect, p.1 * (‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2) :=
          Finset.sum_le_sum (fun i _ => hb i)
      _ = ∫ p in K.rect, ∑ i : Fin 3, p.1 * (‖curlComp (fun a b => modeThird m n H a b 0 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 1 p) i‖ ^ 2
            + ‖curlComp (fun a b => modeThird m n H a b 2 p) i‖ ^ 2) :=
          (integral_finsetSum _ (fun i _ => hint i)).symm
      _ = ∫ p in K.rect, p.1 * curlGradModeSq m n H p := by
          congr 1
          funext p
          simp only [curlGradModeSq, Fin.sum_univ_three]
          ring

theorem resolvedEnergy_of_modes (hI : ModeSquareIntegrableStatement) (hR : ModeRadialPartsStatement)
    (hZ : ModeHeightPartsStatement) (hr : RadialCrossStatement) (hz : HeightCrossStatement) :
    ResolvedEnergyStatement :=
  resolvedEnergy_of hI hR hZ (resolvedComponent_of hr hz)

theorem resolvedEnergy_of_modeFacts (hI : ModeSquareIntegrableStatement) (hR : ModeRadialPartsStatement)
    (hZ : ModeHeightPartsStatement) : ResolvedEnergyStatement :=
  resolvedEnergy_of_modes hI hR hZ radialCross heightCross

end CellAnalysis

end CellCert

end Breakdown
