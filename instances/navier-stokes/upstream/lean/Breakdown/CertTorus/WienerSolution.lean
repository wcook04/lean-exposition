import Breakdown.CertTorus.RegularStatements
import Breakdown.Uniqueness.RegPhysAux

open MeasureTheory Set Real Filter
open scoped ContDiff ENNReal Topology FourierTransform

noncomputable section

namespace Breakdown.FarField

open Freq SmoothFlow

namespace Internal.FourierSolution

theorem toWeightL1_of_memLp {k : ℕ} {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure k)) :
    toWeightL1 k f = hf.toLp f := by
  rw [toWeightL1, dif_pos hf]

theorem exists_timeDeriv_map (k : ℕ) :
    ∃ Φ : Lp CSpace 1 (weightL1Measure (k + 2)) × Lp CSpace 1 (weightL1Measure (k + 1)) →
        Lp CSpace 1 (weightL1Measure k),
      (∀ n : ℕ, ContDiff ℝ n Φ) ∧
      ∀ (f : Space → CSpace) (h2 : MemLp f 1 (weightL1Measure (k + 2)))
        (h1 : MemLp f 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (timeDerivSymbol f) 1 (weightL1Measure k), Φ (h2.toLp f, h1.toLp f) = h.toLp _ := by
  obtain ⟨L, hL⟩ : ∃ L : Lp CSpace 1 (weightL1Measure (k + 2)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 2))),
        ∃ hg : MemLp (fun ξ => -(((4 * π ^ 2 * ‖ξ‖ ^ 2 : ℝ)) : ℂ) • f ξ) 1 (weightL1Measure k),
          L (hf.toLp f) = hg.toLp _ := exists_clm_mulNormSq k
  obtain ⟨P, hP⟩ : ∃ P : Lp CSpace 1 (weightL1Measure k) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f : Space → CSpace) (hf : MemLp f 1 (weightL1Measure k)),
        ∃ hg : MemLp (fun ξ => -divFreeC ξ (f ξ)) 1 (weightL1Measure k),
          P (hf.toLp f) = hg.toLp _ := exists_clm_divFree k
  obtain ⟨B, hB⟩ : ∃ B : Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ]
        Lp CSpace 1 (weightL1Measure (k + 1)) →L[ℝ] Lp CSpace 1 (weightL1Measure k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightL1Measure (k + 1)))
        (hg : MemLp g 1 (weightL1Measure (k + 1))),
        ∃ h : MemLp (advectionBilin f g) 1 (weightL1Measure k),
          B (hf.toLp f) (hg.toLp g) = h.toLp _ := exists_bilin_advection k
  refine ⟨fun p => L p.1 + P (B p.2 p.2), fun n => ?_, fun f h2 h1 => ?_⟩
  · exact (L.contDiff.comp contDiff_fst).add
      (P.contDiff.comp (B.isBoundedBilinearMap.contDiff.comp (contDiff_snd.prodMk contDiff_snd)))
  · obtain ⟨hl, el⟩ := hL f h2
    obtain ⟨ha, ea⟩ := hB f f h1 h1
    obtain ⟨hn, en⟩ := hP _ ha
    exact ⟨hl.add hn, (congrArg₂ (· + ·) el ((congrArg P ea).trans en)).trans (MemLp.toLp_add hl hn).symm⟩

theorem memLp_timeDeriv {f : Space → CSpace} (hf : ∀ k, MemLp f 1 (weightL1Measure k)) (k : ℕ) :
    MemLp (timeDerivSymbol f) 1 (weightL1Measure k) := by
  obtain ⟨Φ, -, hΦ⟩ := exists_timeDeriv_map k
  obtain ⟨h, -⟩ := hΦ f (hf (k + 2)) (hf (k + 1))
  exact h

theorem integrable_lapSymbol {f : Space → CSpace} (hf : MemLp f 1 (weightL1Measure 2)) :
    Integrable (sspSymbol f) := by
  obtain ⟨L, hL⟩ := exists_clm_mulNormSq 0
  obtain ⟨h, -⟩ := hL f hf
  exact integrable_of_memLp_weight (k := 0) h

theorem single_ne_zero : EuclideanSpace.single (0 : Fin 3) (1 : ℂ) ≠ 0 := by
  intro h0
  have := congrArg (fun v : CSpace => v (0 : Fin 3)) h0
  simp at this

theorem integrable_pressure {f : Space → CSpace} (hf : ∀ k, MemLp f 1 (weightL1Measure k))
    (hs : IsSolenoidalSymbol f) : Integrable (pressureSymbol f) :=
  (integrable_smul_const single_ne_zero).1
    (integrable_of_memLp_weight (memLp_pressureSymbol_single hf hs 0))

theorem fourierInv_smul_const (g : Space → ℂ) (v : CSpace) (x : Space) :
    𝓕⁻ (fun ξ => g ξ • v) x = 𝓕⁻ g x • v := by
  simp only [Real.fourierInv_eq, Circle.smul_def, smul_smul, smul_eq_mul]
  exact integral_smul_const _ _

def reFirst : CSpace →L[ℝ] ℝ :=
  Complex.reCLM.comp ((EuclideanSpace.proj (0 : Fin 3) : CSpace →L[ℂ] ℂ).restrictScalars ℝ)

theorem physScalar_eq_reFirst (g : Space → ℂ) (x : Space) :
    physScalar g x = reFirst (𝓕⁻ (fun ξ => g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) x) := by
  rw [fourierInv_smul_const]
  simp [reFirst, physScalar]

variable {a b : ℝ} {F : ℝ → Space → CSpace}

theorem contDiffOn_weighted (hab : a < b)
    (hm : ∀ t ∈ Icc a b, ∀ k, MemLp (F t) 1 (weightL1Measure k))
    (hd : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun τ => toWeightL1 k (F τ))
      (toWeightL1 k (timeDerivSymbol (F t))) (Icc a b) t) (n k : ℕ) :
    ContDiffOn ℝ n (fun τ => toWeightL1 k (F τ)) (Icc a b) := by
  induction n generalizing k with
  | zero => exact contDiffOn_zero.mpr fun t ht => (hd k t ht).continuousWithinAt
  | succ n ih =>
    obtain ⟨Φ, hΦ, hΦe⟩ := exists_timeDeriv_map k
    rw [Nat.cast_succ, contDiffOn_succ_iff_derivWithin (uniqueDiffOn_Icc hab)]
    refine ⟨fun t ht => (hd k t ht).differentiableWithinAt, fun h => absurd h (by simp), ?_⟩
    refine ((hΦ n).comp_contDiffOn ((ih (k + 2)).prodMk (ih (k + 1)))).congr fun t ht => ?_
    obtain ⟨h, eh⟩ := hΦe (F t) (hm t ht (k + 2)) (hm t ht (k + 1))
    rw [(hd k t ht).derivWithin (uniqueDiffOn_Icc hab t ht), toWeightL1_of_memLp h,
      Function.comp_apply, toWeightL1_of_memLp (hm t ht (k + 2)),
      toWeightL1_of_memLp (hm t ht (k + 1)), eh]

theorem contDiffOn_pressureSingle (hab : a < b)
    (hm : ∀ t ∈ Icc a b, ∀ k, MemLp (F t) 1 (weightL1Measure k))
    (hsol : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t))
    (hd : ∀ k, ∀ t ∈ Icc a b, HasDerivWithinAt (fun τ => toWeightL1 k (F τ))
      (toWeightL1 k (timeDerivSymbol (F t))) (Icc a b) t) (n k : ℕ) :
    ContDiffOn ℝ n (fun τ => toWeightL1 k
      (fun ξ => pressureSymbol (F τ) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ))) (Icc a b) := by
  obtain ⟨B, hB⟩ : ∃ B : Lp CSpace 1 (weightL1Measure k) →L[ℝ] Lp CSpace 1 (weightL1Measure k) →L[ℝ]
        Lp CSpace 1 (weightL1Measure k),
      ∀ (f g : Space → CSpace) (hf : MemLp f 1 (weightL1Measure k)) (hg : MemLp g 1 (weightL1Measure k)),
        ∃ h : MemLp (fun ξ => pressureBilinSymbol f g ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) 1
          (weightL1Measure k), B (hf.toLp f) (hg.toLp g) = h.toLp _ := exists_bilin_pressureSingle k
  have hc := contDiffOn_weighted hab hm hd n k
  refine (B.isBoundedBilinearMap.contDiff.comp_contDiffOn (hc.prodMk hc)).congr fun t ht => ?_
  have hp := memLp_pressureSymbol_single (hm t ht) (hsol t ht) k
  obtain ⟨h, eh⟩ := hB (F t) (F t) (hm t ht k) (hm t ht k)
  have hae : (fun ξ => pressureSymbol (F t) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ))
      =ᵐ[weightL1Measure k]
      (fun ξ => pressureBilinSymbol (F t) (F t) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) := by
    refine (weight_ac_volume k).ae_le ?_
    filter_upwards [PressureSingle.Internal.pressureSymbol_ae_eq (hm t ht 1) (hsol t ht)] with ξ hξ
    rw [hξ]
  rw [toWeightL1_of_memLp hp, Function.comp_apply, toWeightL1_of_memLp (hm t ht k)]
  exact (MemLp.toLp_congr hp h hae).trans eh.symm

end Internal.FourierSolution

open Internal.FourierSolution in
theorem wienerSolution_holds : WienerSolution := by
  intro F a b hab hF hd
  have hm : ∀ t ∈ Icc a b, ∀ k, MemLp (F t) 1 (weightL1Measure k) := fun t ht => (hF t ht).2
  have hsol : ∀ t ∈ Icc a b, IsSolenoidalSymbol (F t) := fun t ht => (hF t ht).1
  have hT0 : 0 < b - a := sub_pos.2 hab
  have hmap : MapsTo (fun τ : ℝ => τ + a) (Icc 0 (b - a)) (Icc a b) := fun τ hτ =>
    ⟨by linarith [hτ.1], by linarith [hτ.2]⟩
  have hshift : MapsTo (fun z : ℝ × Space => (z.1 - a, z.2)) (Icc a b ×ˢ univ)
      (Icc 0 (b - a) ×ˢ univ) := fun z hz =>
    ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, mem_univ _⟩
  have hsm : ContDiff ℝ ∞ (fun z : ℝ × Space => (z.1 - a, z.2)) := by fun_prop
  have key : ∀ c : ℝ → Space → CSpace, (∀ t ∈ Icc a b, ∀ k, MemLp (c t) 1 (weightL1Measure k)) →
      (∀ k n : ℕ, ContDiffOn ℝ n (fun τ => toWeightL1 k (c τ)) (Icc a b)) →
      ContDiffOn ℝ ∞ (fun z : ℝ × Space => 𝓕⁻ (c z.1) z.2) (Icc a b ×ˢ univ) := by
    intro c hcm hcc
    have h := contDiffOn_freqTrInv_curve hT0 (c := fun τ => c (τ + a))
      (fun t ht k => hcm _ (hmap ht) k)
      (fun k n => (hcc k n).comp (by fun_prop : ContDiff ℝ n (fun τ : ℝ => τ + a)).contDiffOn hmap)
    refine (h.comp hsm.contDiffOn hshift).congr fun z _ => ?_
    simp only [Function.comp_apply, sub_add_cancel]
  have hcurve : ∀ k n : ℕ, ContDiffOn ℝ n (fun τ => toWeightL1 k (F τ)) (Icc a b) :=
    fun k n => contDiffOn_weighted hab hm hd n k
  refine ⟨realVec.contDiff.comp_contDiffOn (key F hm hcurve), ?_, ?_, ?_⟩
  · have h := key (fun τ ξ => pressureSymbol (F τ) ξ • EuclideanSpace.single (0 : Fin 3) (1 : ℂ))
      (fun t ht k => memLp_pressureSymbol_single (hm t ht) (hsol t ht) k)
      (fun k n => contDiffOn_pressureSingle hab hm hsol hd n k)
    refine (reFirst.contDiff.comp_contDiffOn h).congr fun z _ => ?_
    exact physScalar_eq_reFirst _ _
  · intro t ht x
    have htc : t ∈ Icc a b := Ioo_subset_Icc_self ht
    have hta : t - a ∈ Ioo 0 (b - a) := ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hmd := memLp_timeDeriv (hm t htc) 0
    have hc0 : HasDerivWithinAt (fun τ => toWeightL1 0 (F (τ + a)))
        (toWeightL1 0 (timeDerivSymbol (F t))) (Icc 0 (b - a)) (t - a) := by
      have hh : HasDerivWithinAt (fun τ : ℝ => τ + a) 1 (Icc 0 (b - a)) (t - a) :=
        ((hasDerivAt_id _).add_const a).hasDerivWithinAt
      have := (hd 0 t htc).scomp_of_eq (t - a) hh hmap (by simp)
      rwa [one_smul] at this
    have h1 := hasDerivAt_freqTrInv_curve (c := fun τ => F (τ + a)) hta
      (fun τ hτ => hm _ (hmap hτ) 0) hmd hc0 x
    have h2 := (realVec.hasFDerivAt.comp_hasDerivAt (t - a) h1).comp_sub_const t a
    have e : (fun τ => physField (F τ) x) =
        fun τ => (realVec ∘ fun σ => 𝓕⁻ (F (σ + a)) x) (τ - a) := by
      funext τ
      simp only [Function.comp_apply, sub_add_cancel, physField]
    rw [e]
    refine h2.congr_deriv ?_
    have hA := integrable_of_memLp_weight (memLp_advectionSymbol (hm t htc) 0)
    have hL := integrable_lapSymbol (hm t htc 2)
    have hTd := integrable_of_memLp_weight hmd
    have hdecomp : ∀ ξ, gradPressureSymbol (F t) ξ =
        sspSymbol (F t) ξ - timeDerivSymbol (F t) ξ - advectionSymbol (F t) ξ := fun ξ => by
      rw [sub_sub, timeDerivSymbol_add_advectionSymbol]
      abel
    have hG : Integrable (gradPressureSymbol (F t)) :=
      ((hL.sub hTd).sub hA).congr (Eventually.of_forall fun ξ => (hdecomp ξ).symm)
    have hP := integrable_pressure (hm t htc) (hsol t htc)
    have hPf : Integrable (fun ξ => pressureSymbol (F t) ξ • freqVec ξ) := by
      refine (hG.smul (2 * (π : ℂ) * Complex.I)⁻¹).congr (Eventually.of_forall fun ξ => ?_)
      simp only [Pi.smul_apply, gradPressureSymbol, smul_smul]
      rw [← mul_assoc, inv_mul_cancel₀ (by simp [Real.pi_ne_zero, Complex.I_ne_zero]), one_mul]
    have e2 : timeDerivSymbol (F t) =
        fun ξ => (sspSymbol (F t) ξ - gradPressureSymbol (F t) ξ) - advectionSymbol (F t) ξ := by
      funext ξ
      rw [hdecomp ξ]
      abel
    have s1 := physField_sub (f := fun ξ => sspSymbol (F t) ξ - gradPressureSymbol (F t) ξ)
      (g := advectionSymbol (F t)) (hL.sub hG) hA x
    have s2 := physField_sub (f := sspSymbol (F t)) (g := gradPressureSymbol (F t)) hL hG x
    beta_reduce at s1
    show physField (timeDerivSymbol (F t)) x = _
    rw [sumSecondPartialsAt_physField (hm t htc 2) x, advectionAt_physField (hm t htc) (hsol t htc) x,
      gradientAt_physScalar hP hPf x, e2, s1, s2, sub_right_comm]
    rfl
  · intro t ht x
    exact divergenceAt_physField (hm t ht 1) (fun ξ => (hsol t ht ξ).1) x

end Breakdown.FarField
