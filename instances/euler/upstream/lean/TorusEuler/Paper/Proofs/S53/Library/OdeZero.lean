import TorusEuler.Paper.Proofs.S53.Library.OdeJets2
import TorusEuler.OscillatoryLabelRegularity

/-!
# S53 library: the zero-order estimate for the jet spaces

The estimate `‖v‖_{[0]} ≤ K ‖L v‖` of the hypothesis of Lemma D.3: variation of constants from the
stability hypothesis (5.18)/(5.23) (`weighted_linearODE_forced_norm_le`).
-/

open Set MeasureTheory
open scoped ContDiff Interval


namespace TorusEuler.Paper.Lib.S53

noncomputable section

open TorusEuler

variable {Idx P E : Type} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace OdeData

variable (D : OdeData Idx P E)

/-- Auxiliary fact `zeroOrder` on the jet spaces of the linear ODE (instance of Lemma D.3). -/
theorem zeroOrder {n : ℕ} {C : ℝ}
    (hC : ∀ w : List Idx, w.length ≤ n → w ≠ [] → ∀ t ∈ Icc D.l D.r,
      ‖phaseOperatorWord (fun i _ => D.d i) w (D.A t) D.p‖ ≤ C)
    (hK : 0 ≤ D.K) (u : Esub Idx E D.slab) :
    pE D.slab Idx E u ≤ D.K *
      pF D.slab Idx E (L0 D.slab u + Tmap D.slab (D.aE n hC) u) := by
  set Fr := L0 D.slab u + Tmap D.slab (D.aE n hC) u with hFr
  let X : ℝ → E := u.1 []
  let Aop : ℝ → E →L[ℝ] E := fun t => D.A t D.p
  let φ : ℝ → E := fun t => derivWithin X (Icc D.l D.r) t - Aop t (X t)
  have hφ : ∀ t ∈ Icc D.l D.r, Fr.1.1 [] t = φ t := by
    intro t ht
    have h1 : Fr.1.1 [] t = (L0 D.slab u).1.1 [] t + (Tmap D.slab (D.aE n hC) u).1.1 [] t := rfl
    rw [h1, L0_fst D.slab u [] ht, Tmap_fst]
    have : lsum [] (fun v₁ v₂ => (D.aE n hC).1 v₁ t (u.1 v₂ t)) = Aop t (X t) := by
      simp only [lsum]
      change D.aj n [] t (u.1 [] t) = _
      rw [D.aj_of_mem (Nat.zero_le n) ht]
      rfl
    rw [this]
    exact (sub_eq_add_neg _ _).symm
  have hAc : ContinuousOn Aop (Icc D.l D.r) :=
    D.hA.continuousOn.comp (continuous_id.prodMk continuous_const).continuousOn
      (fun t ht => ⟨ht, mem_univ D.p⟩)
  have hXd : DifferentiableOn ℝ X (Icc D.l D.r) := (u.2.2 []).1
  have hXc : ContinuousOn X (Icc D.l D.r) := hXd.continuousOn
  have hφc : ContinuousOn φ (Icc D.l D.r) :=
    (u.2.2 []).2.sub (hAc.clm_apply hXc)
  have hx : ∀ t ∈ Icc D.l D.r,
      HasDerivWithinAt X (Aop t (X t) + φ t) (Icc D.l D.r) t := by
    intro t ht
    have := (hXd t ht).hasDerivWithinAt
    convert this using 1
    simp only [φ]; abel
  have hfs : 0 ≤ pFsup D.slab Idx E Fr := apply_nonneg _ _
  have hI : Fr.1.2 [] = X D.l := by
    have : Fr.1.2 [] = (L0 D.slab u).1.2 [] + (Tmap D.slab (D.aE n hC) u).1.2 [] := rfl
    rw [this, L0_snd, Tmap_snd]
    simp [X]
    rfl
  have hpF : pF D.slab Idx E Fr = pFsup D.slab Idx E Fr + (D.g D.l)⁻¹ * ‖X D.l‖ := by
    rw [pF_apply, hI]
    rfl
  have hr : 0 < D.r - D.l := sub_pos.mpr D.hlr
  have hφb : ∀ t ∈ Icc D.l D.r, ‖φ t‖ / D.g t ≤ pFsup D.slab Idx E Fr / (D.r - D.l) := by
    intro t ht
    rw [le_div_iff₀ hr]
    have := pFsup_ge D.slab Fr t ht
    rw [hφ t ht] at this
    change (D.r - D.l) * (‖φ t‖ / D.g t) ≤ _ at this
    linarith
  refine pE_le D.slab u fun t ht0 => ?_
  have ht : t ∈ Icc D.l D.r := ht0
  have hmain := weighted_linearODE_forced_norm_le (A := Aop) (g := D.g) (dg := D.dg) (x := X)
    (f := φ) (a := D.l) (b := D.r) (t := t) (K := D.K) hAc hφc D.hg0 D.hg D.hdg D.hStable hx ht
  have hint : ∫ s in D.l..t, ‖φ s‖ / D.g s ≤ pFsup D.slab Idx E Fr := by
    have hgc : ContinuousOn D.g (Icc D.l D.r) := D.slab.hgc
    have hcont : ContinuousOn (fun s => ‖φ s‖ / D.g s) (Icc D.l D.r) :=
      hφc.norm.div hgc fun s hs => (D.hg0 s hs).ne'
    have hsub : Icc D.l t ⊆ Icc D.l D.r := Icc_subset_Icc_right ht.2
    have hII : IntervalIntegrable (fun s => ‖φ s‖ / D.g s) volume D.l t := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le ht.1]
      exact hcont.mono hsub
    calc ∫ s in D.l..t, ‖φ s‖ / D.g s
        ≤ ∫ _ in D.l..t, pFsup D.slab Idx E Fr / (D.r - D.l) :=
          intervalIntegral.integral_mono_on ht.1 hII intervalIntegrable_const
            (fun s hs => hφb s (hsub hs))
      _ = (t - D.l) * (pFsup D.slab Idx E Fr / (D.r - D.l)) := by
          rw [intervalIntegral.integral_const, smul_eq_mul]
      _ ≤ (D.r - D.l) * (pFsup D.slab Idx E Fr / (D.r - D.l)) :=
          mul_le_mul_of_nonneg_right (by linarith [ht.2]) (div_nonneg hfs hr.le)
      _ = _ := mul_div_cancel₀ _ hr.ne'
  rw [hpF]
  have hX : ‖X D.l‖ / D.g D.l = (D.g D.l)⁻¹ * ‖X D.l‖ := by rw [div_eq_inv_mul]
  calc ‖u.1 [] t‖ / D.g t ≤ D.K * (‖X D.l‖ / D.g D.l + ∫ s in D.l..t, ‖φ s‖ / D.g s) := hmain
    _ ≤ D.K * (‖X D.l‖ / D.g D.l + pFsup D.slab Idx E Fr) :=
        mul_le_mul_of_nonneg_left (add_le_add le_rfl hint) hK
    _ = _ := by rw [hX]; ring

end OdeData

end

end TorusEuler.Paper.Lib.S53
