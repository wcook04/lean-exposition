import TorusEuler.Paper.S5.Statements
import TorusEuler.Paper.S34A.Statements
import TorusEuler.Paper.SBD.Statements
import TorusEuler.Paper.Proofs.S5a.Proposition51
import TorusEuler.Paper.Proofs.S5a.Library.Launch

/-!
# S5a library: (D.6) for the mean coefficients `K`, `Ω` of (4.1)

`exists_KOmega_power`: the coefficients `K = (D_aX)ᵀ D_aX` and `Ω = (D_aX)ᵀ(Mᵀ - M)D_aX` satisfy the power bound
(D.6) with absolute exponents and constants (`sections/06d_mean_estimates.tex:30-33`: Proposition 5.1 for `D_aX`, `M`, then Lemma D.2(a) for the three
products); shared by the nodes (5.13) and (5.14), one derivation.
-/

open Set UnitAddTorus
open scoped ContDiff InnerProductSpace

namespace TorusEuler.Paper

noncomputable section

open AppendixD HierarchyTwistedProfile Lib.S5a

namespace Lib.S5a

/-- (D.6) from operator-norm jet bounds with arbitrary (possibly negative) constants. -/
theorem coefficientPower_of_jets_max {I X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {c : I → Vec3 → X} {K : ℕ → ℝ} {D : ℝ} {a : ℕ} (hD : 0 ≤ D)
    (hc : ∀ t, ContDiff ℝ ∞ (c t))
    (hj : ∀ m t x, ‖iteratedFDeriv ℝ m (c t) x‖ ≤ K m * D ^ (a * (m + 1))) :
    CoefficientPower
      (fun m => ((appendixCoefficientOrderWords m).card : ℝ) * max (K m) 0) D a c :=
  coefficientPower_of_jets hD (fun _ => le_max_right _ _) hc
    (fun m t x => (hj m t x).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hD _)))


/-- (D.6) for the coefficients `K`, `Ω` of (4.1) (`sections/06d_mean_estimates.tex:30-33`). -/
theorem exists_KOmega_power (h5_1 : Statement.proposition_5_1) (hD_2 : Statement.lemma_D_2) :
    ∃ (CK CO : ℕ → ℝ) (aK aO : ℕ), (∀ m, 0 ≤ CK m) ∧ (∀ m, 0 ≤ CO m) ∧
      ∀ {T : ℝ} {U : Velocity} {X : ℝ → Velocity} {pU : Pressure} {D lam : ℝ}, 0 < T →
        S5.Parent T U X pU D lam →
        CoefficientPower CK D aK (fun (t : Icc (0 : ℝ) T) (a : Vec3) => meanKinetic X t a) ∧
        CoefficientPower CO D aO (fun (t : Icc (0 : ℝ) T) (a : Vec3) => meanVorticity U X t a) := by
  obtain ⟨C, Kc, hK⟩ := h5_1
  obtain ⟨Kf, hKf⟩ := hK (fun _ => 0)
  let W (m : ℕ) : ℝ := ((appendixCoefficientOrderWords m).card : ℝ)
  let CF (m : ℕ) : ℝ := W m * max (Kc m) 0
  let CDf (m : ℕ) : ℝ := W m * max (2 * Kc m) 0
  obtain ⟨CK, hCK, hDK⟩ := hD_2.1 (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) CF CF C C
  obtain ⟨CQ, hCQ, hDQ⟩ := hD_2.1 (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) CDf CF C C
  obtain ⟨CO, hCO, hDO⟩ := hD_2.1 (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) (Vec3 →L[ℝ] Vec3) CF CQ C
    (2 * max C C)
  refine ⟨CK, CO, 2 * max C C, 2 * max C (2 * max C C), hCK, hCO, ?_⟩
  intro T U X pU D lam hT hP
  have hD2 : 2 ≤ D := hP.scale_ge_two
  have hD1 : 1 ≤ D := by linarith
  have hD₀ : 0 < D := by linarith
  obtain ⟨k, t₀, hL⟩ := Lib.S5a.exists_launch hT hP
  have hD6 := (hKf hT hP hL).1
  have hXsmooth (t : ℝ) (ht : t ∈ Icc 0 T) : ContDiff ℝ ∞ (X 0 t) :=
    contDiff_infty.mpr fun j =>
      (hP.flow.labelJets_evolve j hT hP.velocity_smooth hP.velocity_periodic).1 t ht
  let I := ↥(Icc (0 : ℝ) T)
  let cF : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => fderiv ℝ (X 0 t) a
  let cFt : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => (cF t a).adjoint
  let cM : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => S5.strainField U X t a
  let cMt : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => (cM t a).adjoint
  let cDf : I → Vec3 → (Vec3 →L[ℝ] Vec3) := fun t a => cMt t a - cM t a
  let J := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := Vec3) (F := Vec3)
  have hFs (t : I) : ContDiff ℝ ∞ (cF t) := (contDiff_infty_iff_fderiv.mp (hXsmooth t t.2)).2
  have hMs (t : I) : ContDiff ℝ ∞ (cM t) :=
    ((contDiff_infty_iff_fderiv.mp (contDiff_slice hP.velocity_smooth t.2)).2).comp
      (hXsmooth t t.2)
  have hFts (t : I) : ContDiff ℝ ∞ (cFt t) := J.toContinuousLinearEquiv.contDiff.comp (hFs t)
  have hMts (t : I) : ContDiff ℝ ∞ (cMt t) := J.toContinuousLinearEquiv.contDiff.comp (hMs t)
  have hjF (m : ℕ) (t : I) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (cF t) x‖ ≤ Kc m * D ^ (C * (m + 1)) := (hD6 m t t.2 x).1
  have hjM (m : ℕ) (t : I) (x : Vec3) :
      ‖iteratedFDeriv ℝ m (cM t) x‖ ≤ Kc m * D ^ (C * (m + 1)) := (hD6 m t t.2 x).2.2.1
  have hPF : CoefficientPower CF D C cF :=
    coefficientPower_of_jets_max hD₀.le hFs hjF
  have hPM : CoefficientPower CF D C cM :=
    coefficientPower_of_jets_max hD₀.le hMs hjM
  have hPFt : CoefficientPower CF D C cFt := by
    refine coefficientPower_of_jets_max hD₀.le hFts fun m t x => ?_
    change ‖iteratedFDeriv ℝ m (J ∘ cF t) x‖ ≤ _
    rw [J.norm_iteratedFDeriv_comp_left (cF t) x m]
    exact hjF m t x
  have hPDf : CoefficientPower CDf D C cDf := by
    refine coefficientPower_of_jets_max hD₀.le (fun t => (hMts t).sub (hMs t)) fun m t x => ?_
    have hsub : iteratedFDeriv ℝ m (cDf t) x =
        iteratedFDeriv ℝ m (cMt t) x - iteratedFDeriv ℝ m (cM t) x :=
      iteratedFDeriv_sub_apply (((hMts t).of_le (by simp)).contDiffAt) (((hMs t).of_le (by simp)).contDiffAt)
    have h1 : ‖iteratedFDeriv ℝ m (cMt t) x‖ ≤ Kc m * D ^ (C * (m + 1)) := by
      change ‖iteratedFDeriv ℝ m (J ∘ cM t) x‖ ≤ _
      rw [J.norm_iteratedFDeriv_comp_left (cM t) x m]
      exact hjM m t x
    calc ‖iteratedFDeriv ℝ m (cDf t) x‖ ≤ _ := by
          rw [hsub]; exact norm_sub_le _ _
      _ ≤ Kc m * D ^ (C * (m + 1)) + Kc m * D ^ (C * (m + 1)) := add_le_add h1 (hjM m t x)
      _ = 2 * Kc m * D ^ (C * (m + 1)) := by ring
  have hBn : ‖ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3‖ ≤ 1 :=
    ContinuousLinearMap.norm_compL_le _ _ _ _
  have hPK := hDK _ hBn I D hD1 cFt cF hPFt hPF
  have hPQ := hDQ _ hBn I D hD1 cDf cF hPDf hPF
  have hPO := hDO _ hBn I D hD1 cFt _ hPFt hPQ
  have hKin : (fun (t : Icc (0 : ℝ) T) (a : Vec3) => meanKinetic X t a) =
      fun t x => ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3 (cFt t x) (cF t x) := by
    funext t x
    simp [meanKinetic, kineticForm, meanDeformation, cFt, cF, ContinuousLinearMap.compL_apply]
  have hOm : (fun (t : Icc (0 : ℝ) T) (a : Vec3) => meanVorticity U X t a) =
      fun t x => ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3 (cFt t x)
        ((ContinuousLinearMap.compL ℝ Vec3 Vec3 Vec3) (cDf t x) (cF t x)) := by
    funext t x
    simp [meanVorticity, vorticityForm, meanDeformation, meanGradient, cFt, cF, cDf, cMt, cM,
      S5.strainField, ContinuousLinearMap.compL_apply]
  rw [hKin, hOm]
  exact ⟨hPK, hPO⟩

end Lib.S5a

end

end TorusEuler.Paper
