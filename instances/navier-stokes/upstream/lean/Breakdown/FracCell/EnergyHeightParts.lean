import Breakdown.FracCell.EnergyHeightProj
import Breakdown.FracCell.EnergyRadialPairing

open MeasureTheory Matrix

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula SteadyCert Assembly

def HeightWeakPair (K : CellBox) (F dF : ℝ × ℝ → ℂ) : Prop :=
  ∀ (t s : ℝ → ℝ), Continuous t → Continuous s →
    (0 < K.r₁ ∨ ∃ t₀ : ℝ → ℝ, Continuous t₀ ∧ ∀ r, t r = r * t₀ r) →
    IntegrableOn (fun p : ℝ × ℝ => ((t p.1 * s p.2 : ℝ) : ℂ) * F p) K.rect ∧
    IntegrableOn (fun p : ℝ × ℝ => ((t p.1 * s p.2 : ℝ) : ℂ) * dF p) K.rect ∧
    (ContDiff ℝ 1 s → s K.z₁ = 0 → s K.z₂ = 0 →
      ∫ p in K.rect, ((t p.1 * s p.2 : ℝ) : ℂ) * dF p =
        -∫ p in K.rect, ((t p.1 * deriv s p.2 : ℝ) : ℂ) * F p)

def HeightModeWeakStatement : Prop :=
  ∀ (m : ℕ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)), IsSecondOrderField m v G H →
    ∀ K : CellBox, IsCellBox K → ∀ (n : ℤ) (a b : Fin 3),
      HeightWeakPair K (gradMode m n G a b) (heightGradMode m n H a b)

namespace HeightParts

variable {D : Type} [Fintype D] [DecidableEq D] {modes : Finset ℤ} {Q q : ℕ}

theorem testSup_polyFn (K : CellBox) (hK : IsCellBox K) (m : ℝ × ℝ → ℝ) (hmc : Continuous m)
    (hm0 : ∀ p ∈ K.rect, 0 ≤ m p) (hmpos : ∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, 0 < m p)
    (d d' : ℕ) (g : ℝ × ℝ → ℂ) (rows : Fin (d + 1) × Fin (d' + 1) → D → ℂ) (u : D → ℂ)
    (hg : ∀ i : Fin (d + 1) × Fin (d' + 1),
      IntegrableOn (fun p => (m p : ℂ) * g p * ((monomial i.1 i.2 p : ℝ) : ℂ)) K.rect)
    (hrow : ∀ i : Fin (d + 1) × Fin (d' + 1),
      rowApply (rows i) u = ∫ p in K.rect, (m p : ℂ) * g p * ((monomial i.1 i.2 p : ℝ) : ℂ)) :
    K.testSupremum m (polyFn d d') g =
      quadFormValue (testSupForm rows
        (testInnerMatrix K m (fun i : Fin (d + 1) × Fin (d' + 1) => monomial i.1 i.2))) u := by
  classical
  set Pm : Fin (d + 1) × Fin (d' + 1) → ℝ × ℝ → ℝ := fun i => monomial i.1 i.2 with hPm
  set Gm := testInnerMatrix K m Pm with hGm
  set b : Fin (d + 1) × Fin (d' + 1) → ℂ := fun i => rowApply (rows i) u with hb
  have hcomp : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc
  have hPc : ∀ i, Continuous (Pm i) := fun i => by
    show Continuous (fun p : ℝ × ℝ => p.1 ^ (i.1 : ℕ) * p.2 ^ (i.2 : ℕ)); fun_prop
  have hint : ∀ i i', IntegrableOn (fun p => m p * Pm i p * Pm i' p) K.rect := fun i i' =>
    ((hmc.mul (hPc i)).mul (hPc i')).continuousOn.integrableOn_compact hcomp
  have hind : ∀ c : Fin (d + 1) × Fin (d' + 1) → ℂ,
      (∀ p ∈ Set.Ioo K.r₁ K.r₂ ×ˢ Set.Ioo K.z₁ K.z₂, ∑ i, c i * (Pm i p : ℂ) = 0) → c = 0 := by
    intro c hc
    have h0 := RadialForm.monomial_indep hK.r_order.2 hK.z_order.2 (fun j l => c (j, l)) (fun r hr z hz => by
      have := hc (r, z) ⟨hr, hz⟩
      rw [Fintype.sum_prod_type] at this
      simpa [hPm, monomial, mul_assoc] using this)
    funext i
    exact congrFun (congrFun h0 i.1) i.2
  have hpos := fun c hc => RadialForm.pairing_pos K m Pm hmc hPc hm0 hmpos hind c hc
  have hH := RadialForm.pairing_selfAdj K m Pm
  have hU := RadialForm.pairing_unit Gm hpos
  have key : ∀ c : Fin (d + 1) × Fin (d' + 1) → ℂ,
      K.normSqOn m (fun p => ∑ i, c i * (Pm i p : ℂ)) = (star c ⬝ᵥ (Gm *ᵥ c)).re ∧
      K.pairOn m g (fun p => ∑ i, c i * (Pm i p : ℂ)) = star c ⬝ᵥ b := by
    intro c
    refine ⟨(RadialForm.pairing_value K m Pm hint c).symm, ?_⟩
    unfold CellBox.pairOn
    have h1 : ∀ p, (m p : ℂ) * g p * (starRingEnd ℂ) (∑ i, c i * (Pm i p : ℂ))
        = ∑ i, star (c i) * ((m p : ℂ) * g p * ((Pm i p : ℝ) : ℂ)) := by
      intro p
      simp only [map_sum, map_mul, Complex.conj_ofReal, Finset.mul_sum, RCLike.star_def]
      exact Finset.sum_congr rfl (fun i _ => by ring)
    simp_rw [h1]
    rw [integral_finsetSum _ (fun i _ => (hg i).const_mul _)]
    simp only [dotProduct, hb, hrow, integral_const_mul, Pi.star_apply]
  have hconv : ∀ P ∈ polyFn d d', ∃ c : Fin (d + 1) × Fin (d' + 1) → ℂ, P = fun p => ∑ i, c i * (Pm i p : ℂ) := by
    rintro P ⟨c', hc'⟩
    refine ⟨fun i => c' i.1 i.2, funext fun p => ?_⟩
    rw [hc' p, Fintype.sum_prod_type]
    simp only [hPm, monomial]; push_cast; simp only [mul_assoc]
  have hset : {t | ∃ P ∈ polyFn d d', 0 < K.normSqOn m P ∧ t = ‖K.pairOn m g P‖ ^ 2 / K.normSqOn m P}
      = {t : ℝ | ∃ c : Fin (d + 1) × Fin (d' + 1) → ℂ, 0 < (star c ⬝ᵥ (Gm *ᵥ c)).re ∧
          t = ‖star c ⬝ᵥ b‖ ^ 2 / (star c ⬝ᵥ (Gm *ᵥ c)).re} := by
    ext t; constructor
    · rintro ⟨P, hP, hpos', rfl⟩
      obtain ⟨c, rfl⟩ := hconv P hP
      refine ⟨c, by rw [← (key c).1]; exact hpos', by rw [(key c).1, (key c).2]⟩
    · rintro ⟨c, hpos', rfl⟩
      refine ⟨fun p => ∑ i, c i * (Pm i p : ℂ), ⟨fun j l => c (j, l), fun p => ?_⟩, ?_, ?_⟩
      · show ∑ i, c i * ((Pm i p : ℝ) : ℂ) = _
        rw [Fintype.sum_prod_type]; simp only [hPm, monomial]; push_cast; simp only [mul_assoc]
      · rw [(key c).1]; exact hpos'
      · rw [(key c).1, (key c).2]
  unfold CellBox.testSupremum
  rw [hset, RadialForm.sup_identity Gm hH hpos hU b]
  unfold testSupForm
  rw [RadialForm.value_formOfRows]

end HeightParts

end Breakdown.CellCert.CellEnergy
