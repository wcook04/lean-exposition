import Breakdown.FracCell.GivenProfileDriftSt

open MeasureTheory Filter Topology

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace FieldDriftInternal

theorem turn_add (u w : Space) : axialTurn (u + w) = axialTurn u + axialTurn w := by
  ext i; fin_cases i <;> simp [axialTurn]; ring

theorem turn_smul (c : ℝ) (u : Space) : axialTurn (c • u) = c • axialTurn u := by
  ext i; fin_cases i <;> simp [axialTurn]

theorem turn_zero' : axialTurn 0 = 0 := by
  ext i; fin_cases i <;> simp [axialTurn]

theorem continuous_axialTurn' : Continuous axialTurn := by
  let L : Space →ₗ[ℝ] Space := { toFun := axialTurn, map_add' := turn_add, map_smul' := turn_smul }
  exact L.continuous_of_finiteDimensional

theorem drift_add (α a : ℝ) (v w : Space → Space) (G H : Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun z => v z + w z) (fun z => G z + H z) y =
      driftField α a v G y + driftField α a w H y := by
  simp only [driftField, FunLike.coe_add, Pi.add_apply, turn_add]
  module

theorem drift_smul (α a c : ℝ) (v : Space → Space) (G : Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun z => c • v z) (fun z => c • G z) y = c • driftField α a v G y := by
  simp only [driftField, FunLike.coe_smul, Pi.smul_apply, turn_smul]
  module

theorem drift_zero (α a : ℝ) (y : Space) :
    driftField α a (fun _ => (0 : Space)) (fun _ => (0 : Space →L[ℝ] Space)) y = 0 := by
  simp [driftField, turn_zero']

theorem drift_sum {ι : Type*} (s : Finset ι) (α a : ℝ) (c : ι → ℝ) (v : ι → Space → Space)
    (G : ι → Space → (Space →L[ℝ] Space)) (y : Space) :
    driftField α a (fun z => ∑ i ∈ s, c i • v i z) (fun z => ∑ i ∈ s, c i • G i z) y =
      ∑ i ∈ s, c i • driftField α a (v i) (G i) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using drift_zero α a y
  | insert j s hj ih =>
    have e1 : (fun z => ∑ i ∈ insert j s, c i • v i z) =
        fun z => (fun z => c j • v j z) z + (fun z => ∑ i ∈ s, c i • v i z) z := by
      funext z; rw [Finset.sum_insert hj]
    have e2 : (fun z => ∑ i ∈ insert j s, c i • G i z) =
        fun z => (fun z => c j • G j z) z + (fun z => ∑ i ∈ s, c i • G i z) z := by
      funext z; rw [Finset.sum_insert hj]
    rw [e1, e2, drift_add, drift_smul, ih, Finset.sum_insert hj]

theorem profile_hasFDerivAt {k : ℕ} (D : ProfileData k) (hD : IsProfileData D) (q : Fin k → ℝ)
    (y : Space) :
    HasFDerivAt (D.profile q)
      (∑ μ ∈ D.index, ProfileData.monomialOf q μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase q)) y) y := by
  have h := HasFDerivAt.sum (u := D.index) (A := fun μ z => ProfileData.monomialOf q μ • fieldOf D.chart (D.part μ) (D.phase q) z)
    (fun μ hμ => ((fieldOf_differentiable D.chart hD.chart (D.part μ) (hD.parts μ hμ) (D.phase q)
      y).hasFDerivAt).const_smul (ProfileData.monomialOf q μ))
  have e : D.profile q = ∑ μ ∈ D.index,
      fun z => ProfileData.monomialOf q μ • fieldOf D.chart (D.part μ) (D.phase q) z := by
    funext z; simp [ProfileData.profile, Finset.sum_apply]
  rw [e]; exact h

theorem box_compact {k : ℕ} (r : Fin k → ℝ) : IsCompact (box r) := by
  have : box r = Set.pi Set.univ (fun i => Set.Icc (-r i) (r i)) := by
    ext q; simp [box, abs_le, Pi.le_def, forall_and]
  rw [this]
  exact isCompact_univ_pi (fun i => isCompact_Icc)

theorem box_bound {k : ℕ} (D : ProfileData k) :
    ∃ M : ℝ, ∀ q ∈ box D.radius, (∀ μ ∈ D.index, |ProfileData.monomialOf q μ| ≤ M) ∧ |D.phase q| ≤ M := by
  have hcont : Continuous (fun q : Fin k → ℝ => ∑ μ ∈ D.index, |ProfileData.monomialOf q μ| + |D.phase q|) := by
    unfold ProfileData.monomialOf ProfileData.phase ProfileData.rate
    fun_prop
  obtain ⟨M, hM⟩ := (box_compact D.radius).exists_bound_of_continuousOn hcont.continuousOn
  refine ⟨M, fun q hq => ⟨fun μ hμ => ?_, ?_⟩⟩
  · have h1 := hM q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have h2 : |ProfileData.monomialOf q μ| ≤ ∑ μ ∈ D.index, |ProfileData.monomialOf q μ| :=
      Finset.single_le_sum (f := fun μ => |ProfileData.monomialOf q μ|) (fun _ _ => abs_nonneg _) hμ
    linarith [abs_nonneg (D.phase q)]
  · have h1 := hM q hq
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at h1
    have : 0 ≤ ∑ μ ∈ D.index, |ProfileData.monomialOf q μ| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
    linarith

theorem entrySq_le (A : Space →L[ℝ] Space) : entrySq A ≤ 3 * ‖A‖ ^ 2 := by
  have h : ∀ i : Fin 3, ‖A (unitVector i)‖ ^ 2 ≤ ‖A‖ ^ 2 := fun i => by
    have : ‖A (unitVector i)‖ ≤ ‖A‖ := by
      have h1 := A.le_opNorm (unitVector i)
      have h2 : ‖unitVector i‖ = 1 := by simp [unitVector]
      rw [h2, mul_one] at h1
      exact h1
    exact pow_le_pow_left₀ (norm_nonneg _) this 2
  unfold entrySq
  rw [Fin.sum_univ_three]
  linarith [h 0, h 1, h 2]

theorem entrySq_continuous : Continuous (fun A : Space →L[ℝ] Space => entrySq A) := by
  unfold entrySq
  fun_prop

theorem memLp_two_of_bound {v : Space → Space} (hm : AEStronglyMeasurable v volume) {C : ℝ}
    (hC : ∀ y, ‖v y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ))) : MemLp v 2 volume := by
  have hr : ((Module.finrank ℝ Space : ℕ) : ℝ) < 4 := by
    rw [finrank_euclideanSpace_fin]; norm_num
  have hint := integrable_one_add_norm (E := Space) (μ := volume) hr
  have hm' : AEStronglyMeasurable (fun x : Space => (1 + ‖x‖) ^ (-(2 : ℝ))) volume :=
    (Continuous.rpow_const (continuous_const.add continuous_norm)
      fun x => Or.inl (by show (1 : ℝ) + ‖x‖ ≠ 0; positivity)).aestronglyMeasurable
  have hdom : MemLp (fun x : Space => (1 + ‖x‖) ^ (-(2 : ℝ))) 2 volume := by
    refine (integrable_norm_rpow_iff hm' (by norm_num) (by norm_num)).1 ?_
    refine hint.congr (ae_of_all _ fun x => ?_)
    have hx : (0 : ℝ) < 1 + ‖x‖ := by positivity
    show (1 + ‖x‖) ^ (-(4 : ℝ)) = ‖(1 + ‖x‖) ^ (-(2 : ℝ))‖ ^ ENNReal.toReal 2
    rw [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hx _), ← Real.rpow_mul hx.le]
    norm_num
  refine (hdom.const_mul C).of_le hm (ae_of_all _ fun x => ?_)
  exact (hC x).trans (le_abs_self _)

theorem drift_measurable (α a : ℝ) {v : Space → Space} (hv : Continuous v) :
    Measurable (driftField α a v (fun z => fderiv ℝ v z)) := by
  have hG : Measurable (fun z => fderiv ℝ v z) := measurable_fderiv ℝ v
  have hev : Continuous (fun q : (Space →L[ℝ] Space) × Space => q.1 q.2) :=
    isBoundedBilinearMap_apply.continuous
  have hGy : Measurable (fun z => fderiv ℝ v z z) :=
    hev.measurable.comp (hG.prodMk measurable_id)
  have hGt : Measurable (fun z => fderiv ℝ v z (axialTurn z)) :=
    hev.measurable.comp (hG.prodMk continuous_axialTurn'.measurable)
  have hvt : Measurable (fun z => axialTurn (v z)) := (continuous_axialTurn'.comp hv).measurable
  have e : driftField α a v (fun z => fderiv ℝ v z) = fun y => (1 - 1 / (2 * α)) • v y +
      (1 / (2 * α)) • fderiv ℝ v y y + a • (fderiv ℝ v y (axialTurn y) - axialTurn (v y)) := rfl
  rw [e]
  have h1 : Measurable (fun y => (1 - 1 / (2 * α)) • v y) := (hv.const_smul (1 - 1 / (2 * α))).measurable
  have h2 : Measurable (fun y => (1 / (2 * α)) • fderiv ℝ v y y) := by
    have := hGy.const_smul (1 / (2 * α))
    exact this
  have h3 : Measurable (fun y => fderiv ℝ v y (axialTurn y) - axialTurn (v y)) := hGt.sub hvt
  have h4 : Measurable (fun y => a • (fderiv ℝ v y (axialTurn y) - axialTurn (v y))) := by
    have := h3.const_smul a
    exact this
  exact (h1.add h2).add h4

theorem fieldOf_drift (P : ChartParams) (hP : IsChartParams P) (F : FieldData)
    (hF : IsFieldData P 1 F) (α a : ℝ) (hα : α = 1 + P.eps) :
    MemLp (driftField α a (fieldOf P F (-(2 * α * (P.m : ℝ) * a)))
      (fun y => fderiv ℝ (fieldOf P F (-(2 * α * (P.m : ℝ) * a))) y)) 2 volume := by
  obtain ⟨C, hC⟩ := fieldOf_drift_bound P hP F hF α a hα
  exact memLp_two_of_bound (drift_measurable α a
    (fieldOf_differentiable P hP F hF _).continuous).aestronglyMeasurable hC

end FieldDriftInternal

open FieldDriftInternal

theorem profile_drift_of {k N : ℕ} (α : ℝ) (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) (hα : α = D.power) :
    ∀ p ∈ box d.radius,
      MemLp (driftField α (d.rotationRate p) (d.profile p) (d.gradProfile p)) 2 volume := by
  intro p _
  have hg : d.gradProfile p = fun z => ∑ μ ∈ D.index,
      ProfileData.monomialOf p μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z := by
    funext z
    simp only [FracCertData.gradProfile, hd.profile_eq]
    exact (profile_hasFDerivAt D hD p z).fderiv
  have hv : d.profile p = fun z => ∑ μ ∈ D.index,
      ProfileData.monomialOf p μ • fieldOf D.chart (D.part μ) (D.phase p) z := by
    rw [hd.profile_eq]; rfl
  rw [hg, hv, hd.rate_eq]
  have he : driftField α (D.rate p) (fun z => ∑ μ ∈ D.index,
      ProfileData.monomialOf p μ • fieldOf D.chart (D.part μ) (D.phase p) z) (fun z => ∑ μ ∈ D.index,
      ProfileData.monomialOf p μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z) =
      fun y => ∑ μ ∈ D.index, ProfileData.monomialOf p μ • driftField α (D.rate p)
        (fieldOf D.chart (D.part μ) (D.phase p))
        (fun z => fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z) y := by
    funext y
    exact drift_sum D.index α (D.rate p) (fun μ => ProfileData.monomialOf p μ)
      (fun μ => fieldOf D.chart (D.part μ) (D.phase p))
      (fun μ z => fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase p)) z) y
  rw [he]
  refine memLp_finsetSum D.index (fun μ hμ => ?_)
  have hph : D.phase p = -(2 * α * (D.chart.m : ℝ) * D.rate p) := by
    rw [hα]; rfl
  rw [hph]
  exact (fieldOf_drift D.chart hD.chart (D.part μ) (hD.parts μ hμ) α (D.rate p)
    (hα.trans hD.power_eq)).const_smul (ProfileData.monomialOf p μ)

theorem profile_continuous_of {k N : ℕ} (D : ProfileData k) (d : FracCertData k N)
    (hD : IsProfileData D) (hd : IsProfileInstance D d) :
    ∀ p ∈ box d.radius, ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ p' ∈ box d.radius,
      dist p' p < δ → ∫ y, entrySq (d.gradProfile p' y - d.gradProfile p y) < ε := by
  intro p hp ε hε
  rw [hd.radius_eq] at hp ⊢
  set g : (Fin k → ℝ) → Space → (Space →L[ℝ] Space) := fun q z => ∑ μ ∈ D.index,
    ProfileData.monomialOf q μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase q)) z with hgdef
  have hg : ∀ q z, d.gradProfile q z = g q z := fun q z => by
    simp only [FracCertData.gradProfile, hd.profile_eq]
    exact (profile_hasFDerivAt D hD q z).fderiv
  simp only [hg]
  obtain ⟨M, hM⟩ := box_bound D
  have hC : ∀ μ, ∃ C : ℝ, μ ∈ D.index → ∀ β : ℝ, |β| ≤ M → ∀ y : Space,
      ‖fderiv ℝ (fieldOf D.chart (D.part μ) β) y‖ ≤ C * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    intro μ
    by_cases hμ : μ ∈ D.index
    · obtain ⟨C, hC⟩ := fieldOf_grad_bound D.chart hD.chart (D.part μ) (hD.parts μ hμ) M
      exact ⟨C, fun _ => hC⟩
    · exact ⟨0, fun h => absurd h hμ⟩
  choose C hC using hC
  set K : ℝ := ∑ μ ∈ D.index, M * |C μ| with hK
  have hgb : ∀ q ∈ box D.radius, ∀ y, ‖g q y‖ ≤ K * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
    intro q hq y
    have hw : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := Real.rpow_nonneg (by positivity) _
    calc ‖g q y‖ ≤ ∑ μ ∈ D.index, ‖ProfileData.monomialOf q μ • fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase q)) y‖ :=
          norm_sum_le _ _
      _ ≤ ∑ μ ∈ D.index, M * |C μ| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
          refine Finset.sum_le_sum (fun μ hμ => ?_)
          rw [norm_smul, Real.norm_eq_abs]
          have h1 := (hM q hq).1 μ hμ
          have h2 := hC μ hμ (D.phase q) (hM q hq).2 y
          have h3 : C μ * (1 + ‖y‖) ^ (-(2 : ℝ)) ≤ |C μ| * (1 + ‖y‖) ^ (-(2 : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hw
          have h4 : 0 ≤ |C μ| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by positivity
          calc |ProfileData.monomialOf q μ| * ‖fderiv ℝ (fieldOf D.chart (D.part μ) (D.phase q)) y‖
              ≤ M * (|C μ| * (1 + ‖y‖) ^ (-(2 : ℝ))) :=
                mul_le_mul h1 (h2.trans h3) (norm_nonneg _) ((abs_nonneg _).trans h1)
            _ = M * |C μ| * (1 + ‖y‖) ^ (-(2 : ℝ)) := by ring
      _ = K * (1 + ‖y‖) ^ (-(2 : ℝ)) := by rw [hK, Finset.sum_mul]
  set bound : Space → ℝ := fun y => 12 * K ^ 2 * (1 + ‖y‖) ^ (-(4 : ℝ)) with hbound
  have hbi : Integrable bound volume := by
    have hr : ((Module.finrank ℝ Space : ℕ) : ℝ) < 4 := by
      rw [finrank_euclideanSpace_fin]; norm_num
    exact (integrable_one_add_norm (E := Space) (μ := volume) hr).const_mul _
  have hdom : ∀ q ∈ box D.radius, ∀ y,
      ‖entrySq (g q y - g p y)‖ ≤ bound y := by
    intro q hq y
    have hy : (0 : ℝ) < 1 + ‖y‖ := by positivity
    have hw : 0 ≤ (1 + ‖y‖) ^ (-(2 : ℝ)) := Real.rpow_nonneg hy.le _
    have h1 : ‖g q y - g p y‖ ≤ 2 * K * (1 + ‖y‖) ^ (-(2 : ℝ)) := by
      have := norm_sub_le (g q y) (g p y)
      have a1 := hgb q hq y
      have a2 := hgb p hp y
      linarith
    have h0 : 0 ≤ entrySq (g q y - g p y) := by
      unfold entrySq; positivity
    rw [Real.norm_eq_abs, abs_of_nonneg h0]
    have h2 : ‖g q y - g p y‖ ^ 2 ≤ (2 * K * (1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) h1 2
    have h3 : ((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 = (1 + ‖y‖) ^ (-(4 : ℝ)) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hy.le]; norm_num
    have h4 := entrySq_le (g q y - g p y)
    calc entrySq (g q y - g p y) ≤ 3 * ‖g q y - g p y‖ ^ 2 := h4
      _ ≤ 3 * (2 * K * (1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 := by linarith
      _ = 12 * K ^ 2 * ((1 + ‖y‖) ^ (-(2 : ℝ))) ^ 2 := by ring
      _ = bound y := by rw [h3]
  have hmeas : ∀ q, AEStronglyMeasurable (fun y => entrySq (g q y - g p y)) volume := by
    intro q
    have e : ∀ q', g q' = fderiv ℝ (D.profile q') := fun q' => by
      funext z; exact ((profile_hasFDerivAt D hD q' z).fderiv).symm
    rw [e q, e p]
    exact (entrySq_continuous.measurable.comp
      ((measurable_fderiv ℝ (D.profile q)).sub (measurable_fderiv ℝ (D.profile p)))).aestronglyMeasurable
  have hae : ∀ᵐ y ∂(volume : Measure Space), ∀ μ ∈ D.index,
      Continuous (fun β : ℝ => fderiv ℝ (fieldOf D.chart (D.part μ) β) y) :=
    (eventually_all_finset D.index).2
      (fun μ hμ => fieldOf_grad_continuous D.chart hD.chart (D.part μ) (hD.parts μ hμ))
  have hlim : ∀ᵐ y ∂(volume : Measure Space),
      Tendsto (fun q => entrySq (g q y - g p y)) (𝓝[box D.radius] p) (𝓝 0) := by
    filter_upwards [hae] with y hy
    have hc : Continuous (fun q => g q y) := by
      have hph : Continuous (fun q : Fin k → ℝ => D.phase q) := by
        unfold ProfileData.phase ProfileData.rate; fun_prop
      have hmo : ∀ μ, Continuous (fun q : Fin k → ℝ => ProfileData.monomialOf q μ) := fun μ => by
        unfold ProfileData.monomialOf; fun_prop
      exact continuous_finsetSum _ (fun μ hμ => (hmo μ).smul ((hy μ hμ).comp hph))
    have h0 : entrySq (g p y - g p y) = 0 := by simp [entrySq]
    have ht : Tendsto (fun q => entrySq (g q y - g p y)) (𝓝 p) (𝓝 (entrySq (g p y - g p y))) :=
      ((entrySq_continuous.comp (hc.sub continuous_const)).tendsto p)
    rw [h0] at ht
    exact ht.mono_left nhdsWithin_le_nhds
  have hT := tendsto_integral_filter_of_dominated_convergence bound
    (Eventually.of_forall hmeas)
    (eventually_nhdsWithin_of_forall (fun q hq => ae_of_all _ (hdom q hq))) hbi hlim
  rw [integral_zero] at hT
  have hev := hT.eventually (gt_mem_nhds hε)
  obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
  exact ⟨δ, hδ, fun p' hp' hd' => hsub ⟨Metric.mem_ball.2 hd', hp'⟩⟩

end GivenFields

end CellCert

end Breakdown
