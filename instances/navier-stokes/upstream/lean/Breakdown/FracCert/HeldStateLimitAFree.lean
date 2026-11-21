import Breakdown.FracCert.HeldStateLimitADefect
import Breakdown.FracCert.GradientOrthogonal

open scoped ContDiff ENNReal
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace SteadyCert

namespace FreeBoundInternal

theorem l2Norm_eq {f : Space → Space} (hf : MemLp f 2 volume) : l2Norm f = ‖hf.toLp f‖ := by
  rw [l2Norm, ← WeakPairingInternal.norm_toLp_sq hf, Real.sqrt_sq (norm_nonneg _)]

theorem l2_add_le {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    l2Norm (fun y => f y + g y) ≤ l2Norm f + l2Norm g := by
  have hfg : MemLp (fun y => f y + g y) 2 volume := hf.add hg
  rw [l2Norm_eq hfg, l2Norm_eq hf, l2Norm_eq hg]
  have e : hfg.toLp (fun y => f y + g y) = hf.toLp f + hg.toLp g := by
    rw [← MemLp.toLp_add]
    rfl
  rw [e]
  exact norm_add_le _ _

theorem l2_smul (c : ℝ) (f : Space → Space) : l2Norm (fun y => c • f y) = |c| * l2Norm f := by
  unfold l2Norm
  have e : (fun y => ‖c • f y‖ ^ 2) = fun y => c ^ 2 * ‖f y‖ ^ 2 := by
    funext y
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e, integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

theorem l2_sum_le {k : ℕ} (s : Finset (Fin k)) (c : Fin k → ℝ) (b : Fin k → Space → Space)
    (hb : ∀ i, MemLp (b i) 2 volume) :
    l2Norm (fun y => ∑ i ∈ s, c i • b i y) ≤ ∑ i ∈ s, |c i| * l2Norm (b i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp [l2Norm]
  | insert j s hj ih =>
    rw [Finset.sum_insert hj]
    have e : (fun y => ∑ i ∈ insert j s, c i • b i y) = fun y => c j • b j y + ∑ i ∈ s, c i • b i y := by
      funext y
      rw [Finset.sum_insert hj]
    rw [e]
    have h := l2_add_le (f := fun y => c j • b j y) (g := fun y => ∑ i ∈ s, c i • b i y)
      ((hb j).const_smul (c j)) (memLp_finsetSum s fun i _ => (hb i).const_smul (c i))
    rw [l2_smul] at h
    linarith

theorem gradient_zero : IsGradientField (fun _ => (0 : Space)) := by
  refine ⟨fun _ => 0, ?_, ?_, aestronglyMeasurable_const, ?_⟩
  · intro K hK; simp
  · intro K hK; simp
  · intro φ hφ j; simp

end FreeBoundInternal

open FreeBoundInternal in
theorem heldFreeBound_of (hsol : DriftPowerSolenoidalStatement) : HeldFreeBoundStatement := by
  intro α hα1 hα2 k N d hd R
  obtain ⟨Cx, hCx⟩ := crossUniformBound α hα1 hα2 d hd (R ^ 2)
  have hμ := hd.multiplierScale_pos
  set Sb := ∑ i, (|R| / d.multiplierScale) * l2Norm (d.actuator i) with hSb
  refine ⟨(Real.sqrt Cx + Sb + d.defectBound + 1) ^ 2, fun p hp u G H P κ hh hsize => ?_⟩
  have hst := hh.state
  set F : Space → Space := fun y => driftField α (d.rotationRate p) u G y + P y with hFdef
  have hF2 : MemLp F 2 volume := hst.drift.add hst.power.1
  have hFs : IsSolenoidalL2 F := hsol α hα1 hα2 (d.rotationRate p) d.order u G H P hst.second hst.power hst.drift
  have hE : d.energy G H ≤ R ^ 2 := by
    have h0 : 0 ≤ d.size G H κ := Real.sqrt_nonneg _
    have e := HeldLimitInternal.size_sq d hd G H κ
    have hk : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 :=
      mul_nonneg (sq_nonneg _) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    nlinarith
  obtain ⟨mX, hXb⟩ := hCx p hp u G H hst.second hE
  set X : Space → Space := fun y => d.gradProfile p y (u y) + G y (d.profile p y) + G y (u y) with hXdef
  set S : Space → Space := fun y => ∑ i, κ i • d.actuator i y with hSdef
  have mS : MemLp S 2 volume := memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (κ i)
  have hdf := ActiveEnclosureInternal.defect_memLp hd hp
  obtain ⟨Q, hQg, hQe⟩ := hh.equation
  have hne : {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => d.defect α p y + Q y) 2 volume ∧
      r = l2Norm (fun y => d.defect α p y + Q y)}.Nonempty :=
    ⟨_, fun _ => 0, gradient_zero, by simpa using hdf, rfl⟩
  obtain ⟨r, ⟨Q', hQ'g, hQ'2, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne one_pos
  have hpn := hd.defect_norm p hp
  unfold projectedNorm at hpn
  set Y : Space → Space := fun y => d.defect α p y + Q' y with hYdef
  have hQ'L : MemLp Q' 2 volume := by
    have : Q' = fun y => Y y - d.defect α p y := by funext y; simp [hYdef]
    rw [this]
    exact hQ'2.sub hdf
  have halg : ∀ y, d.fullField α p u G H P κ y + G y (u y) = F y + X y + S y := by
    intro y
    simp only [FracCertData.fullField, FracCertData.localField, FracCertData.splitField, symProduct, hFdef,
      hXdef, hSdef, smul_smul, smul_add]
    norm_num
    abel
  have hQae : ∀ᵐ y ∂volume, Q y = -(F y + X y + S y + d.defect α p y) := by
    filter_upwards [hQe] with y hy
    rw [halg] at hy
    rw [eq_neg_iff_add_eq_zero]
    rw [← hy]
    abel
  have hQL : MemLp Q 2 volume := by
    have h := (((hF2.add mX).add mS).add hdf).neg
    exact h.ae_eq (by filter_upwards [hQae] with y hy; rw [hy]; rfl)
  have o1 := gradientOrthogonal Q F hQg hQL hFs
  have o2 := gradientOrthogonal Q' F hQ'g hQ'L hFs
  set Z : Space → Space := fun y => X y + S y + Y y with hZdef
  have mZ : MemLp Z 2 volume := (mX.add mS).add hQ'2
  have iFF := ActiveEnclosureInternal.pair_integrable hF2 hF2
  have iFZ := ActiveEnclosureInternal.pair_integrable hF2 mZ
  have iQF := ActiveEnclosureInternal.pair_integrable hQL hF2
  have iQ'F := ActiveEnclosureInternal.pair_integrable hQ'L hF2
  have hkey : ∫ y, inner ℝ (F y) (F y) = -(∫ y, inner ℝ (F y) (Z y)) - (∫ y, inner ℝ (Q y) (F y))
      + ∫ y, inner ℝ (Q' y) (F y) := by
    have i1 : Integrable (fun y => -inner ℝ (F y) (Z y) - inner ℝ (Q y) (F y)) volume := iFZ.neg.sub iQF
    have i0 : Integrable (fun y => -inner ℝ (F y) (Z y)) volume := iFZ.neg
    have e : ∫ y, inner ℝ (F y) (F y) =
        ∫ y, (-inner ℝ (F y) (Z y) - inner ℝ (Q y) (F y) + inner ℝ (Q' y) (F y)) := by
      refine integral_congr_ae ?_
      filter_upwards [hQae] with y hy
      rw [hy]
      simp only [hZdef, hYdef, inner_add_left, inner_add_right, inner_neg_left,
        real_inner_comm (F y) (Q' y)]
      rw [real_inner_comm (X y) (F y), real_inner_comm (S y) (F y), real_inner_comm (d.defect α p y) (F y)]
      ring
    rw [e, integral_add i1 iQ'F, integral_sub i0 iQF, integral_neg]
  rw [o1, o2, sub_zero, add_zero] at hkey
  have hFF : l2Norm F ^ 2 = ∫ y, inner ℝ (F y) (F y) := by
    rw [l2Norm, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
    exact integral_congr_ae (Eventually.of_forall fun y => (real_inner_self_eq_norm_sq _).symm)
  have hCst : -(∫ y, inner ℝ (F y) (Z y)) ≤ l2Norm F * l2Norm Z := by
    have := ApplyPairingInternal.abs_pair_le hF2 mZ
    have e1 : Real.sqrt (∫ y, ‖F y‖ ^ 2) = l2Norm F := rfl
    have e2 : Real.sqrt (∫ y, ‖Z y‖ ^ 2) = l2Norm Z := rfl
    rw [e1, e2] at this
    linarith [neg_abs_le (∫ y, inner ℝ (F y) (Z y))]
  have hZ : l2Norm Z ≤ Real.sqrt Cx + Sb + d.defectBound + 1 := by
    have h1 : l2Norm X ≤ Real.sqrt Cx := Real.sqrt_le_sqrt hXb
    have h2 : l2Norm S ≤ Sb := by
      refine (l2_sum_le Finset.univ κ d.actuator hd.actuator_two).trans ?_
      refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
      rw [le_div_iff₀ hμ, mul_comm]
      exact (HeldLimitInternal.coord_bound d hd G H κ hsize i).trans (le_abs_self R)
    have h3 : l2Norm Y ≤ d.defectBound + 1 := by linarith
    have h4 := l2_add_le (f := fun y => X y + S y) (g := Y) (mX.add mS) hQ'2
    have h5 := l2_add_le (f := X) (g := S) mX mS
    rw [← hZdef] at h4
    linarith
  have hF0 : 0 ≤ l2Norm F := Real.sqrt_nonneg _
  have hZ0 : 0 ≤ l2Norm Z := Real.sqrt_nonneg _
  have hFZ : l2Norm F ≤ l2Norm Z := by
    by_contra hc
    push Not at hc
    nlinarith
  have hfin : l2Norm F ^ 2 ≤ (Real.sqrt Cx + Sb + d.defectBound + 1) ^ 2 :=
    pow_le_pow_left₀ hF0 (hFZ.trans hZ) 2
  rwa [l2Norm, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)] at hfin

private theorem box_compact {k : ℕ} (rad : Fin k → ℝ) : IsCompact (box rad) := by
  have e : box rad = Set.pi Set.univ (fun i => Set.Icc (-rad i) (rad i)) := by
    ext p
    simp only [box, Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, Set.mem_Icc, forall_const, abs_le]
  rw [e]
  exact isCompact_univ_pi fun i => isCompact_Icc

open FreeBoundInternal in
theorem profileFreeBound_of (hsol : DriftPowerSolenoidalStatement) : ProfileFreeBoundStatement := by
  intro α hα1 hα2 k N d hd
  obtain ⟨C, hC⟩ := ActiveEnclosureInternal.profile_bounds_of hd
  obtain ⟨Λ, hΛ⟩ := (box_compact d.radius).exists_bound_of_continuousOn hd.multiplier_continuous
  set D6 := ∫ y : Space, ((1 + ‖y‖)⁻¹) ^ 6
  refine ⟨(Real.sqrt (C ^ 4 * D6) + ∑ i, Λ * l2Norm (d.actuator i) + d.defectBound + 1) ^ 2, fun p hp => ?_⟩
  have hemb := profileEmbedData α hα1 hα2 d hd p hp
  set F : Space → Space := fun y => driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p) y
    + d.profilePower p y with hFdef
  have hF2 : MemLp F 2 volume := (hd.profile_drift p hp).add (hd.profile_power p hp).1
  have hFs : IsSolenoidalL2 F := hsol α hα1 hα2 (d.rotationRate p) d.order _ _ _ _
    (CrossTestInternal.profile_second_order hα1 hα2 hd hp) (hd.profile_power p hp) (hd.profile_drift p hp)
  set X : Space → Space := fun y => d.gradProfile p y (d.profile p y) with hXdef
  have mX : MemLp X 2 volume :=
    ActiveEnclosureInternal.decay_apply_memLp ((hd.profile_smooth p hp).continuous_fderiv one_ne_zero)
      (fun y => (hC p hp y).2) hemb.1 (hemb.2.1.integrable_norm_pow (p := 6) (by norm_num))
  set S : Space → Space := fun y => ∑ i, d.multiplier p i • d.actuator i y with hSdef
  have mS : MemLp S 2 volume := memLp_finsetSum _ fun i _ => (hd.actuator_two i).const_smul (d.multiplier p i)
  have hdf := ActiveEnclosureInternal.defect_memLp hd hp
  have hne : {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => d.defect α p y + Q y) 2 volume ∧
      r = l2Norm (fun y => d.defect α p y + Q y)}.Nonempty :=
    ⟨_, fun _ => 0, gradient_zero, by simpa using hdf, rfl⟩
  obtain ⟨r, ⟨Q', hQ'g, hQ'2, rfl⟩, hlt⟩ := Real.lt_sInf_add_pos hne one_pos
  have hpn := hd.defect_norm p hp
  unfold projectedNorm at hpn
  set Y : Space → Space := fun y => d.defect α p y + Q' y with hYdef
  have hQ'L : MemLp Q' 2 volume := by
    have : Q' = fun y => Y y - d.defect α p y := by funext y; simp [hYdef]
    rw [this]
    exact hQ'2.sub hdf
  have o2 := gradientOrthogonal Q' F hQ'g hQ'L hFs
  set Z : Space → Space := fun y => Y y - X y - S y with hZdef
  have mZ : MemLp Z 2 volume := (hQ'2.sub mX).sub mS
  have iFZ := ActiveEnclosureInternal.pair_integrable hF2 mZ
  have iQ'F := ActiveEnclosureInternal.pair_integrable hQ'L hF2
  have hkey : ∫ y, inner ℝ (F y) (F y) = (∫ y, inner ℝ (F y) (Z y)) - ∫ y, inner ℝ (Q' y) (F y) := by
    rw [← integral_sub iFZ iQ'F]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    have e : F y = Z y - Q' y := by
      simp only [hZdef, hYdef, hXdef, hSdef, hFdef, FracCertData.defect]
      abel
    show inner ℝ (F y) (F y) = inner ℝ (F y) (Z y) - inner ℝ (Q' y) (F y)
    have h' : inner ℝ (F y) (F y) = inner ℝ (F y) (Z y - Q' y) := by rw [← e]
    rw [h', inner_sub_right, real_inner_comm (Q' y) (F y)]
  rw [o2, sub_zero] at hkey
  have hFF : l2Norm F ^ 2 = ∫ y, inner ℝ (F y) (F y) := by
    rw [l2Norm, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)]
    exact integral_congr_ae (Eventually.of_forall fun y => (real_inner_self_eq_norm_sq _).symm)
  have hCst : ∫ y, inner ℝ (F y) (Z y) ≤ l2Norm F * l2Norm Z := by
    have := ApplyPairingInternal.abs_pair_le hF2 mZ
    exact (le_abs_self _).trans this
  have hXn : l2Norm X ≤ Real.sqrt (C ^ 4 * D6) := by
    refine Real.sqrt_le_sqrt ?_
    calc ∫ y, ‖X y‖ ^ 2 ≤ ∫ y, C ^ 4 * ((1 + ‖y‖)⁻¹) ^ 6 :=
          integral_mono (mX.integrable_norm_pow (p := 2) (by norm_num))
            (ActiveEnclosureInternal.decay_six.const_mul _) fun y => by
            have h1 : ‖X y‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2 * ‖d.profile p y‖ :=
              ((d.gradProfile p y).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hC p hp y).2 (norm_nonneg _))
            have h2 : ‖d.profile p y‖ ≤ C * (1 + ‖y‖)⁻¹ := (hC p hp y).1
            have h0 : 0 ≤ (1 + ‖y‖)⁻¹ := by positivity
            have hC0 : 0 ≤ C := le_trans (norm_nonneg _) ((hC p hp 0).1.trans (by simp))
            have h3 : ‖X y‖ ≤ C * ((1 + ‖y‖)⁻¹) ^ 2 * (C * (1 + ‖y‖)⁻¹) :=
              h1.trans (mul_le_mul_of_nonneg_left h2 (by positivity))
            have h4 := pow_le_pow_left₀ (norm_nonneg _) h3 2
            calc ‖X y‖ ^ 2 ≤ (C * ((1 + ‖y‖)⁻¹) ^ 2 * (C * (1 + ‖y‖)⁻¹)) ^ 2 := h4
              _ = C ^ 4 * ((1 + ‖y‖)⁻¹) ^ 6 := by ring
      _ = C ^ 4 * D6 := integral_const_mul _ _
  have hSn : l2Norm S ≤ ∑ i, Λ * l2Norm (d.actuator i) := by
    refine (l2_sum_le Finset.univ (d.multiplier p) d.actuator hd.actuator_two).trans ?_
    refine Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
    exact (norm_le_pi_norm (d.multiplier p) i).trans (hΛ p hp) |>.trans_eq' (Real.norm_eq_abs _).symm
  have hYn : l2Norm Y ≤ d.defectBound + 1 := by linarith
  have hZn : l2Norm Z ≤ Real.sqrt (C ^ 4 * D6) + ∑ i, Λ * l2Norm (d.actuator i) + d.defectBound + 1 := by
    have h1 := l2_add_le (f := fun y => Y y - X y) (g := fun y => -S y) (hQ'2.sub mX) mS.neg
    have h2 := l2_add_le (f := Y) (g := fun y => -X y) hQ'2 mX.neg
    have e1 : (fun y => Y y - X y + -S y) = Z := by funext y; simp [hZdef, sub_eq_add_neg]
    have e2 : (fun y => Y y + -X y) = fun y => Y y - X y := by funext y; rw [sub_eq_add_neg]
    have n1 : l2Norm (fun y => -S y) = l2Norm S := by
      have := l2_smul (-1) S
      simpa using this
    have n2 : l2Norm (fun y => -X y) = l2Norm X := by
      have := l2_smul (-1) X
      simpa using this
    rw [e1, n1] at h1
    rw [e2, n2] at h2
    linarith
  have hF0 : 0 ≤ l2Norm F := Real.sqrt_nonneg _
  have hZ0 : 0 ≤ l2Norm Z := Real.sqrt_nonneg _
  have hFZ : l2Norm F ≤ l2Norm Z := by
    by_contra hc
    push Not at hc
    nlinarith
  have hfin : l2Norm F ^ 2 ≤ (Real.sqrt (C ^ 4 * D6) + ∑ i, Λ * l2Norm (d.actuator i) + d.defectBound + 1) ^ 2 :=
    pow_le_pow_left₀ hF0 (hFZ.trans hZn) 2
  rwa [l2Norm, Real.sq_sqrt (integral_nonneg fun y => sq_nonneg _)] at hfin

end SteadyCert

end Breakdown
