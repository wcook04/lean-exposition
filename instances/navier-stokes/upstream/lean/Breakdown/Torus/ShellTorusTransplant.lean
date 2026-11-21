import Breakdown.Torus.ShellTorusBase

open MeasureTheory Set Real
open scoped ENNReal ContDiff Topology

noncomputable section

namespace Breakdown.Periodic

namespace ShellTorus.Internal

theorem ae_mem_open_cell : ∀ᵐ x ∂(volume.restrict cell), ∀ i, x i ∈ Ioo (0 : ℝ) 1 := by
  have hnull : volume (⋃ i : Fin 3, ({x : Space | x i = 0} ∪ {x : Space | x i = 1})) = 0 :=
    measure_iUnion_null fun i => measure_union_null (volume_coord_eq i 0) (volume_coord_eq i 1)
  refine (ae_restrict_iff' FreqTrSeries.Internal.isCompact_cell.isClosed.measurableSet).mpr ?_
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hnull] with x hx hxc i
  have h1 : x i ∈ Icc (0 : ℝ) 1 := hxc i
  exact ⟨lt_of_le_of_ne h1.1 fun h => hx (mem_iUnion.mpr ⟨i, Or.inl h.symm⟩),
    lt_of_le_of_ne h1.2 fun h => hx (mem_iUnion.mpr ⟨i, Or.inr h⟩)⟩

theorem simCoord_open_cell (μ : ℝ) {x : Space} (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) :
    simCoord μ x = (Real.sqrt μ)⁻¹ • (x - center) := by
  rw [simCoord, wrap_eq_self fun i => Ioo_subset_Ico_self (hx i)]

theorem fderiv_transplant_open_cell (μ : ℝ) (φ : Space → Space) (hφ : IsTestField φ) {x : Space}
    (hx : ∀ i, x i ∈ Ioo (0 : ℝ) 1) (v : Space) :
    fderiv ℝ (fun x' => μ ^ (1 / 4 : ℝ) • transplantField μ φ x') x v =
      (μ ^ (1 / 4 : ℝ) * ((Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹)) •
        fderiv ℝ φ ((Real.sqrt μ)⁻¹ • (x - center)) v := by
  have hev : (fun x' => μ ^ (1 / 4 : ℝ) • transplantField μ φ x') =ᶠ[𝓝 x]
      fun x' => μ ^ (1 / 4 : ℝ) • ((Real.sqrt μ)⁻¹ • φ ((Real.sqrt μ)⁻¹ • (x' - center))) := by
    have h : ∀ᶠ x' in 𝓝 x, ∀ i, x' i ∈ Ioo (0 : ℝ) 1 :=
      Filter.eventually_all.2 fun i =>
        (PiLp.continuous_apply 2 _ i).continuousAt.eventually_mem (isOpen_Ioo.mem_nhds (hx i))
    filter_upwards [h] with x' hx'
    rw [transplantField, simCoord_open_cell μ hx']
  have hL0 := ((hasFDerivAt_id (𝕜 := ℝ) x).sub_const center).const_smul (Real.sqrt μ)⁻¹
  have hL : HasFDerivAt (fun x' : Space => (Real.sqrt μ)⁻¹ • (x' - center))
      ((Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ Space) x := hL0
  have hφd : HasFDerivAt φ (fderiv ℝ φ ((Real.sqrt μ)⁻¹ • (x - center))) ((Real.sqrt μ)⁻¹ • (x - center)) :=
    ((FreqTrSeries.Internal.contDiff_one hφ.1).differentiable one_ne_zero _).hasFDerivAt
  have hd0 := ((hφd.comp x hL).const_smul (Real.sqrt μ)⁻¹).const_smul (μ ^ (1 / 4 : ℝ))
  have hd : HasFDerivAt (fun x' => μ ^ (1 / 4 : ℝ) • ((Real.sqrt μ)⁻¹ • φ ((Real.sqrt μ)⁻¹ • (x' - center))))
      (μ ^ (1 / 4 : ℝ) • ((Real.sqrt μ)⁻¹ • ((fderiv ℝ φ ((Real.sqrt μ)⁻¹ • (x - center))).comp
        ((Real.sqrt μ)⁻¹ • ContinuousLinearMap.id ℝ Space)))) x := hd0
  rw [hev.fderiv_eq, hd.fderiv]
  simp only [FunLike.coe_smul, Pi.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply, map_smul, smul_smul, mul_assoc]

theorem qmp_simAffine {μ : ℝ} (hμ : 0 < μ) :
    Measure.QuasiMeasurePreserving (fun x : Space => (Real.sqrt μ)⁻¹ • (x - center)) volume volume :=
  (Measure.quasiMeasurePreserving_smul volume (inv_ne_zero (Real.sqrt_pos.2 hμ).ne')).comp
    (measurePreserving_sub_right volume center).quasiMeasurePreserving

theorem advectShell_restrict_ae (φ : Space → Space) (hφ : IsTestField φ) (b μ : ℝ)
    (hμ : IsShellScale μ b) (z : V) :
    ∀ᵐ y ∂volume, (advectShell φ hφ b (restrictTorus μ b z) : Space → Space) y =
      (Metric.closedBall (0 : Space) b).indicator (fun y => ∑ j : Fin 3,
        (φ y j • (μ ^ (3 / 4 : ℝ) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))) +
          (μ ^ (1 / 4 : ℝ) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))) j •
            Freq.partialField φ j y)) y := by
  set ζ := restrictTorus μ b z with hζdef
  have hζ : ζ = ((fun j => Freq.toLpOrZero 2 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (3 / 4 : ℝ)) •
          Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))))),
      Freq.toLpOrZero 6 ((Metric.closedBall (0 : Space) b).indicator
        (fun y => (μ ^ (1 / 4 : ℝ)) •
          Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))))) := by
    show restrictTorusFun μ b z = _
    rw [restrictTorusFun, if_pos hμ]
  have h1 : ∀ j, (ζ.1 j : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
      (fun y => (μ ^ (3 / 4 : ℝ)) • Freq.realVec (torusSeries 2 (gradCoef j z) (center + Real.sqrt μ • y))) := by
    intro j
    have hm := (ShellDefs.Internal.norm_shell_le 2 (by norm_num) hμ ShellDefs.Internal.exp_two
      (torusSeries 2 (gradCoef j z))).1
    rw [hζ]
    simp only
    rw [ShellDefs.Internal.toLpOrZero_eq hm]
    exact hm.coeFn_toLp
  have h2 : (ζ.2 : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
      (fun y => (μ ^ (1 / 4 : ℝ)) • Freq.realVec (torusSeries 6 (coeff z) (center + Real.sqrt μ • y))) := by
    have hm := (ShellDefs.Internal.norm_shell_le 6 (by norm_num) hμ ShellDefs.Internal.exp_six
      (torusSeries 6 (coeff z))).1
    rw [hζ]
    simp only
    rw [ShellDefs.Internal.toLpOrZero_eq hm]
    exact hm.coeFn_toLp
  obtain ⟨M0, M1, -, hM1, hb0, hb1⟩ := ShellDefs.Internal.test_bounds hφ
  have hmA : MemLp ((Metric.closedBall (0 : Space) b).indicator
      (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
        (ζ.2 : Space → Space) y j • Freq.partialField φ j y))) 2 volume :=
    (ShellDefs.Internal.advect_bound hφ hM1 hb0 hb1 b ζ).1
  have hA : (advectShell φ hφ b ζ : Space → Space) =ᵐ[volume] (Metric.closedBall (0 : Space) b).indicator
      (fun y => ∑ j : Fin 3, (φ y j • (ζ.1 j : Space → Space) y +
        (ζ.2 : Space → Space) y j • Freq.partialField φ j y)) := by
    show (advectShellFun φ b ζ : Space → Space) =ᵐ[volume] _
    unfold advectShellFun
    rw [ShellDefs.Internal.toLpOrZero_eq hmA]
    exact hmA.coeFn_toLp
  filter_upwards [hA, ae_all_iff.2 h1, h2] with y hyA hy1 hy2
  rw [hyA]
  by_cases hb : y ∈ Metric.closedBall (0 : Space) b
  · rw [indicator_of_mem hb, indicator_of_mem hb]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hy1 j, hy2, indicator_of_mem hb, indicator_of_mem hb]
  · rw [indicator_of_notMem hb, indicator_of_notMem hb]

theorem productField_transplant (hT : TransplantSmooth) (φ : Space → Space) (hφ : IsTestField φ)
    (b μ : ℝ) (hμ : IsShellScale μ b) (hsupp : tsupport φ ⊆ Metric.closedBall 0 b) (z : V) :
    productField (fun x => μ ^ (1 / 4 : ℝ) • transplantField μ φ x) z =ᵐ[volume.restrict cell]
      fun x => μ⁻¹ • (advectShell φ hφ b (restrictTorus μ b z) : Space → Space) (simCoord μ x) := by
  have hμ0 : 0 < μ := hμ.1
  have hs0 : 0 < Real.sqrt μ := Real.sqrt_pos.2 hμ0
  have hss : Real.sqrt μ * Real.sqrt μ = μ := Real.mul_self_sqrt hμ0.le
  have hpull := ae_restrict_of_ae (s := cell) ((qmp_simAffine hμ0).ae (advectShell_restrict_ae φ hφ b μ hμ z))
  filter_upwards [ae_mem_open_cell, hpull] with x hx hxA
  have hcy : center + Real.sqrt μ • ((Real.sqrt μ)⁻¹ • (x - center)) = x := by
    rw [smul_smul, mul_inv_cancel₀ hs0.ne', one_smul, add_sub_cancel]
  simp only [productField]
  simp only [fderiv_transplant_open_cell μ φ hφ hx]
  simp only [transplantField, simCoord_open_cell μ hx]
  rw [hxA]
  by_cases hb : (Real.sqrt μ)⁻¹ • (x - center) ∈ Metric.closedBall (0 : Space) b
  · rw [indicator_of_mem hb]
    simp only [hcy, gField, zField, Freq.partialField, Finset.smul_sum]
    have e1 : μ ^ (1 / 4 : ℝ) * (Real.sqrt μ)⁻¹ = μ⁻¹ * μ ^ (3 / 4 : ℝ) := by
      have h34 : μ ^ (3 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * Real.sqrt μ := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_add hμ0]
        norm_num
      have hinv : μ⁻¹ = (Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹ := by rw [← mul_inv, hss]
      rw [h34, hinv, show (Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹ * (μ ^ (1 / 4 : ℝ) * Real.sqrt μ) =
        μ ^ (1 / 4 : ℝ) * (Real.sqrt μ)⁻¹ * ((Real.sqrt μ)⁻¹ * Real.sqrt μ) by ring,
        inv_mul_cancel₀ hs0.ne', mul_one]
    have e2 : μ ^ (1 / 4 : ℝ) * ((Real.sqrt μ)⁻¹ * (Real.sqrt μ)⁻¹) = μ⁻¹ * μ ^ (1 / 4 : ℝ) := by
      rw [← mul_inv, hss, mul_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, smul_add, smul_smul]
    rw [e2]
    congr 2
    · rw [e1]
      ring
    · ring
  · have hφy : φ ((Real.sqrt μ)⁻¹ • (x - center)) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hb (hsupp h)
    have hdy : fderiv ℝ φ ((Real.sqrt μ)⁻¹ • (x - center)) = 0 :=
      image_eq_zero_of_notMem_tsupport fun h => hb (hsupp (tsupport_fderiv_subset ℝ h))
    rw [indicator_of_notMem hb, hφy, hdy]
    simp

end ShellTorus.Internal

end Breakdown.Periodic
