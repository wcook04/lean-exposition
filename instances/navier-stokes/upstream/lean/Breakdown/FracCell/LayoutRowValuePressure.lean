import Breakdown.FracCell.LayoutRowValueModes
import Breakdown.FracCell.ModeVelSquare
import Breakdown.FracCell.LayoutRowPressureModeIdentity

open MeasureTheory Set

noncomputable section

namespace Breakdown.FracInternal.LayoutRowPressure

open CellCert CellCert.CellFormula CellCert.CellAnalysis CellCert.CellAnalysis.CellScalars SteadyCert
  CellCert.Assembly Spectral.Internal.CylIntegral CellAnalysis.ModeVelSquareInternal

private theorem trig_expand (m : ℕ) (hm : 0 < m) (g : ℝ → ℂ) (hg : Continuous g)
    (hper : Function.Periodic g (2 * Real.pi / m)) (s : Finset ℤ)
    (hz : ∀ n ∉ s, (1 / (2 * Real.pi) : ℂ) *
      ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) * g θ = 0) (θ : ℝ) :
    g θ = ∑ n ∈ s, ((1 / (2 * Real.pi) : ℂ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t) *
        Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hT : 0 < 2 * Real.pi / m := by positivity
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast hm.ne'
  have : Fact (0 < 2 * Real.pi / m) := ⟨hT⟩
  let F : C(AddCircle (2 * Real.pi / m), ℂ) := ⟨hper.lift, continuous_coinduced_dom.mpr hg⟩
  have hF : ∀ x : ℝ, F (x : AddCircle (2 * Real.pi / m)) = g x := fun x => hper.lift_coe x
  have hfo : ∀ (n : ℤ) (x : ℝ), fourier n (x : AddCircle (2 * Real.pi / m)) =
      Complex.exp ((azimuth m n * x : ℝ) * Complex.I) := by
    intro n x
    rw [fourier_coe_apply]
    congr 1
    unfold azimuth
    push_cast
    field_simp
  have hcoef : ∀ n : ℤ, fourierCoeff F n = (1 / (2 * Real.pi) : ℂ) *
      ∫ t in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t := by
    intro n
    rw [fourierCoeff_eq_intervalIntegral F n 0]
    have hh : Function.Periodic (fun t : ℝ => Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t)
        (2 * Real.pi / m) := by
      intro t
      simp only
      rw [hper t]
      congr 1
      have harg : -(((azimuth m n * (t + 2 * Real.pi / m) : ℝ)) : ℂ) * Complex.I =
          -(((azimuth m n * t : ℝ)) : ℂ) * Complex.I + ((-n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
        unfold azimuth; push_cast; field_simp; ring
      rw [harg, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    have hcont : Continuous (fun t : ℝ => Complex.exp (-(azimuth m n * t : ℝ) * Complex.I) * g t) := by
      fun_prop
    have hsum := hh.intervalIntegral_add_zsmul_eq (m : ℤ) 0 (fun a b => hcont.intervalIntegrable a b)
    rw [zero_add, zero_add, show ((m : ℤ) • (2 * Real.pi / m)) = 2 * Real.pi by
      rw [zsmul_eq_mul]; push_cast; field_simp] at hsum
    rw [hsum]
    have e : ∀ x : ℝ, fourier (-n) (x : AddCircle (2 * Real.pi / m)) • F x =
        Complex.exp (-(azimuth m n * x : ℝ) * Complex.I) * g x := by
      intro x
      rw [hF, hfo, smul_eq_mul]
      congr 2
      unfold azimuth
      push_cast
      ring
    simp_rw [e, zero_add]
    rw [zsmul_eq_mul, Complex.real_smul, ← mul_assoc]
    congr 1
    push_cast
    field_simp
  have hsupp : ∀ n ∉ s, fourierCoeff F n • fourier n (θ : AddCircle (2 * Real.pi / m)) = 0 := by
    intro n hn
    rw [hcoef, hz n hn, zero_smul]
  have h1 := has_pointwise_sum_fourier_series_of_summable
    (summable_of_ne_finset_zero (s := s) (fun n hn => by rw [hcoef, hz n hn])) (θ : AddCircle (2 * Real.pi / m))
  have h2 : HasSum (fun n => fourierCoeff F n • fourier n (θ : AddCircle (2 * Real.pi / m)))
      (∑ n ∈ s, fourierCoeff F n • fourier n (θ : AddCircle (2 * Real.pi / m))) :=
    hasSum_sum_of_ne_finset_zero hsupp
  rw [hF] at h1
  rw [h1.unique h2]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hcoef, hfo, smul_eq_mul]


private theorem cyl_cont : Continuous (fun q : (ℝ × ℝ) × ℝ => cylPoint q.1.1 q.2 q.1.2) := by
  unfold cylPoint
  exact (((single_cont 0).comp (by fun_prop)).add ((single_cont 1).comp (by fun_prop))).add
    ((single_cont 2).comp (by fun_prop))

private theorem turn_cont (m : ℕ) : Continuous (turnStep m) := by
  unfold turnStep
  exact (((single_cont 0).comp (by fun_prop)).add ((single_cont 1).comp (by fun_prop))).add
    ((single_cont 2).comp (by fun_prop))

private theorem turn_cyl (m : ℕ) (r θ z : ℝ) :
    cylPoint r (θ + 2 * Real.pi / m) z = turnStep m (cylPoint r θ z) := by
  ext j
  fin_cases j <;> simp [cylPoint, turnStep, Real.cos_add, Real.sin_add] <;> ring

private theorem turn_frame (m : ℕ) (θ : ℝ) (w : Space) (i : Fin 3) :
    frameVec (θ + 2 * Real.pi / m) (turnStep m w) i = frameVec θ w i := by
  have hs := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  fin_cases i <;>
    simp [frameVec, radialUnit, angularUnit, axialUnit, turnStep, inner_add_left, inner_add_right,
      EuclideanSpace.inner_single_right, Real.cos_add, Real.sin_add] <;>
    first
      | linear_combination (w 0 * Real.cos θ + w 1 * Real.sin θ) * hs
      | linear_combination (-(w 0 * Real.sin θ) + w 1 * Real.cos θ) * hs

private theorem turn_radius (m : ℕ) (y : Space) : cylRadius (turnStep m y) = cylRadius y := by
  unfold cylRadius
  congr 1
  have hs := Real.sin_sq_add_cos_sq (2 * Real.pi / m)
  simp [turnStep]
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * hs

private theorem turn_height (m : ℕ) (y : Space) : cylHeight (turnStep m y) = cylHeight y := by
  simp [cylHeight, turnStep]

private theorem mem_solid {K : CellBox} (hK : IsCellBox K) {q : ℝ × ℝ} (hq : q ∈ K.rect) (θ : ℝ) :
    cylPoint q.1 θ q.2 ∈ K.solid := by
  obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := hq
  have hr : 0 ≤ q.1 := hK.r_order.1.trans h1
  have hz : 0 ≤ q.2 := hK.z_order.1.trans h3
  simp only [CellBox.solid, Set.mem_ofPred_eq, CellDensityModesSolid.cyl_radius hr,
    CellDensityModesSolid.cyl_height, abs_of_nonneg hz]
  exact ⟨h1, h2, h3, h4⟩

private theorem upper_open (K : CellBox) :
    IsOpen {y : Space | K.r₁ < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < cylHeight y ∧ cylHeight y < K.z₂} := by
  have h0 : Continuous cylRadius := by unfold cylRadius; fun_prop
  have h2 : Continuous cylHeight := by unfold cylHeight; fun_prop
  exact (isOpen_lt continuous_const h0).inter ((isOpen_lt h0 continuous_const).inter
    ((isOpen_lt continuous_const h2).inter (isOpen_lt h2 continuous_const)))

private theorem mem_upper {K : CellBox} (hK : IsCellBox K) {q : ℝ × ℝ} (hq : q ∈ K.rect) (θ : ℝ) :
    cylPoint q.1 θ q.2 ∈ K.solid ∩ {y : Space | 0 ≤ cylHeight y} := by
  refine ⟨mem_solid hK hq θ, ?_⟩
  show 0 ≤ cylHeight (cylPoint q.1 θ q.2)
  rw [CellDensityModesSolid.cyl_height]
  exact hK.z_order.1.trans hq.2.1

private theorem turn_sym {K : CellBox} (hK : IsCellBox K) {m : ℕ} {row : Space → Space}
    (hf : ContinuousOn row (K.solid ∩ {y : Space | 0 ≤ cylHeight y})) (hcl : IsClassField m row) :
    ∀ y, K.r₁ < cylRadius y → cylRadius y < K.r₂ → K.z₁ < cylHeight y → cylHeight y < K.z₂ →
      row (turnStep m y) = turnStep m (row y) := by
  set U := {y : Space | K.r₁ < cylRadius y ∧ cylRadius y < K.r₂ ∧ K.z₁ < cylHeight y ∧ cylHeight y < K.z₂}
  have hUo : IsOpen U := upper_open K
  have hUs : U ⊆ K.solid ∩ {y : Space | 0 ≤ cylHeight y} := by
    intro y hy
    have h0 : 0 ≤ cylHeight y := hK.z_order.1.trans hy.2.2.1.le
    refine ⟨⟨hy.1.le, hy.2.1.le, ?_, ?_⟩, h0⟩
    · rw [abs_of_nonneg h0]; exact hy.2.2.1.le
    · rw [abs_of_nonneg h0]; exact hy.2.2.2.le
  have hUt : Set.MapsTo (turnStep m) U U := by
    intro y hy
    simp only [U, Set.mem_ofPred_eq, turn_radius, turn_height]
    exact hy
  have h : (fun y => row (turnStep m y)) =ᵐ[volume.restrict U] (fun y => turnStep m (row y)) :=
    ae_restrict_of_ae hcl.1
  have hE := Measure.eqOn_open_of_ae_eq h hUo ((hf.mono hUs).comp (turn_cont m).continuousOn hUt)
    ((turn_cont m).comp_continuousOn (hf.mono hUs))
  intro y h1 h2 h3 h4
  exact hE ⟨h1, h2, h3, h4⟩

private theorem frame_periodic_f {K : CellBox} (hK : IsCellBox K) {m : ℕ} {row : Space → Space}
    (hf : ContinuousOn row (K.solid ∩ {y : Space | 0 ≤ cylHeight y})) (hcl : IsClassField m row) (i : Fin 3)
    {p : ℝ × ℝ} (hp : p ∈ K.rect) (t : ℝ) :
    frameVec (t + 2 * Real.pi / m) (row (cylPoint p.1 (t + 2 * Real.pi / m) p.2)) i =
      frameVec t (row (cylPoint p.1 t p.2)) i := by
  have hc : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => frameVec s (row (cylPoint q.1 s q.2)) i) K.rect := by
    intro s
    have h1 : Continuous (fun q : ℝ × ℝ => cylPoint q.1 s q.2) :=
      cyl_cont.comp (continuous_id.prodMk continuous_const)
    have h2 : ContinuousOn (fun q : ℝ × ℝ => row (cylPoint q.1 s q.2)) K.rect :=
      hf.comp h1.continuousOn (fun q hq => mem_upper hK hq s)
    simp_rw [frameVec_eq]
    exact h2.inner continuousOn_const
  have hsub : Set.EqOn (fun q : ℝ × ℝ => frameVec (t + 2 * Real.pi / m)
      (row (cylPoint q.1 (t + 2 * Real.pi / m) q.2)) i) (fun q : ℝ × ℝ => frameVec t (row (cylPoint q.1 t q.2)) i)
      (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂) := by
    rintro q ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
    have hr : 0 ≤ q.1 := hK.r_order.1.trans h1.le
    have hy := turn_sym hK hf hcl (cylPoint q.1 t q.2)
      (by rw [CellDensityModesSolid.cyl_radius hr]; exact h1)
      (by rw [CellDensityModesSolid.cyl_radius hr]; exact h2)
      (by rw [CellDensityModesSolid.cyl_height]; exact h3)
      (by rw [CellDensityModesSolid.cyl_height]; exact h4)
    simp only
    rw [turn_cyl, hy, turn_frame]
  have hcls : K.rect ⊆ closure (Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂) := by
    rw [closure_prod_eq, closure_Ioo hK.r_order.2.ne, closure_Ioo hK.z_order.2.ne]
    exact subset_rfl
  have hsr : Ioo K.r₁ K.r₂ ×ˢ Ioo K.z₁ K.z₂ ⊆ K.rect :=
    fun q hq => ⟨⟨hq.1.1.le, hq.1.2.le⟩, ⟨hq.2.1.le, hq.2.2.le⟩⟩
  exact hsub.of_subset_closure (hc _) (hc _) hsr hcls hp

theorem row_expansion {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} (hc : IsFormData α c)
    (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) {a : Fin N} (ha : a ∈ R.rowSet) :
    ∀ p ∈ K.rect, ∀ θ (i : Fin 3), frameVec θ (c.row a (cylPoint p.1 θ p.2)) i =
      (∑ n ∈ R.rowModes, rowModeVec c a n p i * Complex.exp ((azimuth c.order n * θ : ℝ) * Complex.I)).re := by
  intro p hp θ i
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  have hK := hD.box
  have hfc : ContinuousOn (c.row a) (K.solid ∩ {y : Space | 0 ≤ cylHeight y}) := hL.continuousOn
  have hm : 0 < c.order := by have := hc.base.order_ge; omega
  have hgc : Continuous (fun t => (frameVec t (c.row a (cylPoint p.1 t p.2)) i : ℂ)) := by
    have h1 : Continuous (fun t : ℝ => cylPoint p.1 t p.2) :=
      cyl_cont.comp (continuous_const.prodMk continuous_id)
    have h2 : Continuous (fun t : ℝ => c.row a (cylPoint p.1 t p.2)) :=
      hfc.comp_continuous h1 (fun t => mem_upper hK hp t)
    have h3 : Continuous (fun t : ℝ => frameVec t (c.row a (cylPoint p.1 t p.2)) i) := by
      simp_rw [frameVec_eq]
      exact h2.inner (frameUnit_cont i)
    exact Complex.continuous_ofReal.comp h3
  have hper : Function.Periodic (fun t => (frameVec t (c.row a (cylPoint p.1 t p.2)) i : ℂ))
      (2 * Real.pi / c.order) := by
    intro t
    simp only
    rw [frame_periodic_f hK hfc (hR.row_class a ha) i hp t]
  have hz : ∀ n ∉ R.rowModes, (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(azimuth c.order n * t : ℝ) * Complex.I) *
        (fun t => (frameVec t (c.row a (cylPoint p.1 t p.2)) i : ℂ)) t = 0 :=
    fun n hn => congrFun (hD.row_modes a ha n hn p hp) i
  have key := trig_expand c.order hm _ hgc hper R.rowModes hz θ
  rw [← Complex.ofReal_re (frameVec θ (c.row a (cylPoint p.1 θ p.2)) i)]
  exact congrArg Complex.re key

private theorem cyl_fun_eq (r z θ : ℝ) : toSpace (cylMap.symm (swapEquiv ((r, z), θ))) = cylPoint r θ z := by
  rw [swapEquiv_apply, symm_apply, toSpace_apply]
  rfl

private theorem joint_meas {F : Space → Space} (hF : AEStronglyMeasurable F volume) :
    AEStronglyMeasurable (fun x : (ℝ × ℝ) × ℝ => F (cylPoint x.1.1 x.2 x.1.2))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod, ← swapEquiv_preimage]
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hv : AEStronglyMeasurable (fun x => F (toSpace (cylMap.symm x))) (volume.restrict cylMap.target) :=
    hF.comp_quasiMeasurePreserving (toSpace_mp.quasiMeasurePreserving.comp symm_qmp)
  refine (hv.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply]
  rw [cyl_fun_eq]

private theorem joint_int {f : Space → ℝ} (hf : Integrable f) :
    Integrable (fun x : (ℝ × ℝ) × ℝ => x.1.1 * f (cylPoint x.1.1 x.2 x.1.2))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-Real.pi) Real.pi))) := by
  have hg : Integrable (fun w => f (toSpace w)) := (toSpace_mp.integrable_comp_emb toSpace.measurableEmbedding).mpr hf
  have hH := change_integrable hg
  have hσ := (swapEquiv_mp.integrableOn_comp_preimage swapEquiv.measurableEmbedding).mpr hH
  rw [swapEquiv_preimage] at hσ
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  refine hσ.congr_fun (fun x _ => ?_) ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply]
  rw [cyl_fun_eq, swapEquiv_apply]


private theorem frame_periodic (F : Space → Space) (r z : ℝ) (i : Fin 3) :
    Function.Periodic (fun θ => frameVec θ (F (cylPoint r θ z)) i) (2 * Real.pi) := by
  intro θ
  simp only [frameVec, radialUnit, angularUnit, cylPoint, Real.cos_add_two_pi, Real.sin_add_two_pi]

theorem circle_integrable {K : CellBox} (hK : IsCellBox K) {F : Space → Space}
    (hF : AEStronglyMeasurable F volume) (hFi : IntegrableOn (fun y => ‖F y‖) K.solid) :
    ∀ᵐ p ∂(volume.restrict K.rect), ∀ i : Fin 3,
      IntervalIntegrable (fun θ => frameVec θ (F (cylPoint p.1 θ p.2)) i) volume 0 (2 * Real.pi) := by
  have hsm : MeasurableSet K.solid := CellDensityModesSolid.solid_closed K
  have hf : Integrable (K.solid.indicator (fun y => ‖F y‖)) := hFi.integrable_indicator hsm
  have h1 := (joint_int hf).prod_right_ae
  have h2 := (joint_meas hF).prodMk_left
  have hA : MeasurableSet (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) := measurableSet_Ioi.prod MeasurableSet.univ
  rw [← Measure.restrict_congr_set (CellDensityModesSolid.rect_ae hK)]
  have h12 : ∀ᵐ p ∂(volume.restrict ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect)),
      Integrable (fun θ => p.1 * K.solid.indicator (fun y => ‖F y‖) (cylPoint p.1 θ p.2))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) ∧
      AEStronglyMeasurable (fun θ => F (cylPoint p.1 θ p.2)) (volume.restrict (Ioo (-Real.pi) Real.pi)) :=
    ae_restrict_of_ae_restrict_of_subset inter_subset_left (h1.and h2)
  filter_upwards [h12, ae_restrict_mem (hA.inter (CellDensityModesSolid.rect_meas K))] with p hp hpA i
  obtain ⟨hint, hmeas⟩ := hp
  have hr : 0 < p.1 := hpA.1.1
  have hmem : ∀ θ, cylPoint p.1 θ p.2 ∈ K.solid := fun θ =>
    ((CellDensityModesSolid.cyl_mem hK hr θ p.2).2 hpA.2).1
  have hnorm : Integrable (fun θ => ‖F (cylPoint p.1 θ p.2)‖) (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    refine (hint.const_mul p.1⁻¹).congr (ae_of_all _ fun θ => ?_)
    simp only [Set.indicator_of_mem (hmem θ)]
    field_simp
  have hcomp : Integrable (fun θ => frameVec θ (F (cylPoint p.1 θ p.2)) i)
      (volume.restrict (Ioo (-Real.pi) Real.pi)) := by
    have e : (fun θ => frameVec θ (F (cylPoint p.1 θ p.2)) i) =
        fun θ => inner ℝ (F (cylPoint p.1 θ p.2)) (frameUnit θ i) := funext fun θ => frameVec_eq _ _ _
    rw [e]
    have hm2 : AEStronglyMeasurable (fun θ => inner ℝ (F (cylPoint p.1 θ p.2)) (frameUnit θ i))
        (volume.restrict (Ioo (-Real.pi) Real.pi)) := hmeas.inner (frameUnit_cont i).aestronglyMeasurable
    refine hnorm.mono' hm2 (ae_of_all _ fun θ => ?_)
    rw [Real.norm_eq_abs, ← frameVec_eq]
    exact frameVec_abs _ _ _
  have hII : IntervalIntegrable (fun θ => frameVec θ (F (cylPoint p.1 θ p.2)) i) volume (-Real.pi)
      (-Real.pi + 2 * Real.pi) := by
    have hle : -Real.pi ≤ -Real.pi + 2 * Real.pi := by linarith [Real.pi_pos]
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le hle, show -Real.pi + 2 * Real.pi = Real.pi by ring]
    exact hcomp
  exact (frame_periodic F p.1 p.2 i).intervalIntegrable (by positivity) hII 0 (2 * Real.pi)

private theorem kern_meas_gen {v : Space → Space} (hv : AEStronglyMeasurable v volume) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    AEStronglyMeasurable (kern m n v a)
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod
        (volume.restrict (Ioc (-Real.pi) Real.pi))) := by
  rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
  have hset : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ×ˢ Ioc (-Real.pi) Real.pi =ᵐ[volume]
      swapEquiv ⁻¹' cylMap.target := by
    rw [swapEquiv_preimage]
    exact Measure.set_prod_ae_eq .rfl Ioo_ae_eq_Ioc.symm
  rw [Measure.restrict_congr_set hset]
  have hmp := swapEquiv_mp.restrict_preimage_emb swapEquiv.measurableEmbedding cylMap.target
  have hΨ : Continuous fun q : ℝ × Space =>
      Complex.exp (-(azimuth m n * q.1 : ℝ) * Complex.I) * (frameVec q.1 q.2 a : ℂ) := by
    have := frameVec_cont a
    fun_prop
  have hvc : AEStronglyMeasurable (fun x => v (toSpace (cylMap.symm x))) (volume.restrict cylMap.target) :=
    hv.comp_quasiMeasurePreserving (toSpace_mp.quasiMeasurePreserving.comp symm_qmp)
  have hk := hΨ.comp_aestronglyMeasurable
      ((continuous_snd.comp continuous_fst).aestronglyMeasurable.prodMk hvc)
  refine (hk.comp_measurePreserving hmp).congr (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨⟨r, z⟩, θ⟩ := x
  simp only [Function.comp_apply, swapEquiv_apply, kern]
  rw [symm_apply, toSpace_apply]
  rfl

private theorem mode_meas_gen {v : Space → Space} (hv : AEStronglyMeasurable v volume) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := by
  have h := (kern_meas_gen hv m n a).integral_prod_right'
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 a) = fun p =>
      (1 / (2 * Real.pi) : ℂ) * ∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (p, θ) :=
    funext (mode_eq m n v a)
  rw [e]
  exact h.const_mul _

private theorem kern_norm_le (m : ℕ) (n : ℤ) (v : Space → Space) (a : Fin 3) (x : (ℝ × ℝ) × ℝ) :
    ‖kern m n v a x‖ ≤ ‖v (cylPoint x.1.1 x.2 x.1.2)‖ := by
  unfold kern
  rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs]
  exact frameVec_abs _ _ _

private theorem mode_r_integrable {K : CellBox} (hK : IsCellBox K) {v : Space → Space}
    (hv : AEStronglyMeasurable v volume) (hvi : IntegrableOn (fun y => ‖v y‖) K.solid) (m : ℕ) (n : ℤ)
    (a : Fin 3) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖) K.rect := by
  have hp := Real.pi_pos
  have hsm : MeasurableSet K.solid := CellDensityModesSolid.solid_closed K
  have hF : Integrable (K.solid.indicator (fun y => ‖v y‖)) := hvi.integrable_indicator hsm
  have h3 := joint_int hF
  rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc] at h3
  have hB := h3.integral_prod_left
  have hsl := h3.prod_right_ae
  have hks := (kern_meas_gen hv m n a).prodMk_left
  have hT : MeasurableSet ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) :=
    (measurableSet_Ioi.prod MeasurableSet.univ).inter (measurableSet_Icc.prod measurableSet_Icc)
  have hsub : (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect ⊆ Ioi (0 : ℝ) ×ˢ (univ : Set ℝ) :=
    inter_subset_left
  have hhalf : IntegrableOn (fun p : ℝ × ℝ => p.1 * ‖modeVec m n v p.1 p.2 a‖)
      ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) := by
    have hB' : IntegrableOn (fun q : ℝ × ℝ => ∫ θ in Ioc (-Real.pi) Real.pi,
        q.1 * K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2))
        ((Ioi (0 : ℝ) ×ˢ (univ : Set ℝ)) ∩ K.rect) :=
      IntegrableOn.mono_set hB hsub
    refine (hB'.const_mul (1 / (2 * Real.pi))).mono'
      (continuous_fst.aestronglyMeasurable.mul
        ((mode_meas_gen hv m n a).mono_measure (Measure.restrict_mono hsub le_rfl)).norm) ?_
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hsl,
      ae_restrict_of_ae_restrict_of_subset hsub hks, ae_restrict_mem hT] with q hq hk hqS
    have hpos : 0 < q.1 := hqS.1.1
    have hgi : Integrable (fun θ => K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2))
        (volume.restrict (Ioc (-Real.pi) Real.pi)) := by
      refine (hq.const_mul (q.1⁻¹)).congr (ae_of_all _ fun θ => ?_)
      simp only []
      field_simp
    have hkb : ∀ θ, ‖kern m n v a (q, θ)‖ ≤ K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2) := by
      intro θ
      rw [Set.indicator_of_mem (mem_solid hK hqS.2 θ)]
      exact kern_norm_le m n v a (q, θ)
    have hI := norm_integral_le_of_norm_le hgi (ae_of_all _ hkb)
    have e1 : ∫ θ in Ioc (-Real.pi) Real.pi, q.1 * K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2) =
        q.1 * ∫ θ in Ioc (-Real.pi) Real.pi, K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2) :=
      integral_const_mul _ _
    have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
      rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    show ‖q.1 * ‖modeVec m n v q.1 q.2 a‖‖ ≤
      1 / (2 * Real.pi) * ∫ θ in Ioc (-Real.pi) Real.pi,
        q.1 * K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2)
    rw [e1, Real.norm_of_nonneg (by positivity), mode_eq, norm_mul, hn]
    calc q.1 * (1 / (2 * Real.pi) * ‖∫ θ in Ioc (-Real.pi) Real.pi, kern m n v a (q, θ)‖)
        ≤ q.1 * (1 / (2 * Real.pi) *
            ∫ θ in Ioc (-Real.pi) Real.pi, K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2)) := by
          gcongr
      _ = 1 / (2 * Real.pi) * (q.1 * ∫ θ in Ioc (-Real.pi) Real.pi,
            K.solid.indicator (fun y => ‖v y‖) (cylPoint q.1 θ q.2)) := by ring
  refine hhalf.of_forall_sdiff_eq_zero (measurableSet_Icc.prod measurableSet_Icc) fun p hp => ?_
  have h1 : K.r₁ ≤ p.1 := hp.1.1.1
  have h2 : ¬ (0 < p.1) := fun h => hp.2 ⟨⟨h, trivial⟩, hp.1⟩
  have h3 : p.1 = 0 := le_antisymm (not_lt.mp h2) (le_trans hK.r_order.1 h1)
  simp [h3]

private theorem mode_norm_le {v : Space → Space} {C : ℝ} (hC : ∀ y, ‖v y‖ ≤ C) (m : ℕ) (n : ℤ) (r z : ℝ)
    (a : Fin 3) : ‖modeVec m n v r z a‖ ≤ C := by
  have hp := Real.pi_pos
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  unfold modeVec
  rw [norm_mul]
  have hn : ‖(1 / (2 * Real.pi) : ℂ)‖ = 1 / (2 * Real.pi) := by
    rw [show (1 / (2 * Real.pi) : ℂ) = ((1 / (2 * Real.pi) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hI : ‖∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
      (frameVec θ (v (cylPoint r θ z)) a : ℂ)‖ ≤ C * |2 * Real.pi - 0| := by
    refine intervalIntegral.norm_integral_le_of_norm_le_const fun θ _ => ?_
    rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_eq_abs]
    exact (frameVec_abs _ _ _).trans (hC _)
  rw [hn, sub_zero, abs_of_pos (by positivity)] at *
  calc 1 / (2 * Real.pi) * ‖∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(azimuth m n * θ : ℝ) * Complex.I) *
        (frameVec θ (v (cylPoint r θ z)) a : ℂ)‖ ≤ 1 / (2 * Real.pi) * (C * (2 * Real.pi)) := by gcongr
    _ = C := by field_simp

private theorem pair_integrable {K : CellBox} (hK : IsCellBox K) {Q row : Space → Space}
    (hQ : AEStronglyMeasurable Q volume) (hQi : IntegrableOn (fun y => ‖Q y‖) K.solid)
    (hr : AEStronglyMeasurable row volume) {C : ℝ} (hC : ∀ y, ‖row y‖ ≤ C) (m : ℕ) (n : ℤ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * pairC (modeVec m n Q p.1 p.2) (modeVec m n row p.1 p.2))
      K.rect := by
  have hmQ : ∀ i : Fin 3, AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n Q p.1 p.2 i)
      (volume.restrict K.rect) := fun i => (mode_meas_gen hQ m n i).mono_measure (rect_ae_le K hK)
  have hmr : ∀ i : Fin 3, AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n row p.1 p.2 i)
      (volume.restrict K.rect) := fun i => (mode_meas_gen hr m n i).mono_measure (rect_ae_le K hK)
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => (p.1 : ℂ) * pairC (modeVec m n Q p.1 p.2) (modeVec m n row p.1 p.2))
      (volume.restrict K.rect) := by
    unfold pairC
    refine (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul ?_
    have h := Finset.aestronglyMeasurable_sum (Finset.univ : Finset (Fin 3))
      (fun i _ => (hmQ i).mul (Complex.continuous_conj.comp_aestronglyMeasurable (hmr i)))
    refine h.congr (ae_of_all _ fun p => ?_)
    simp [Finset.sum_apply]
  refine Integrable.mono' (integrable_finsetSum (Finset.univ : Finset (Fin 3))
    fun i _ => (mode_r_integrable hK hQ hQi m n i).const_mul C) hmeas ?_
  filter_upwards [ae_restrict_mem (CellDensityModesSolid.rect_meas K)] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  unfold pairC
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg h0]
  calc p.1 * ‖∑ i : Fin 3, modeVec m n Q p.1 p.2 i * (starRingEnd ℂ) (modeVec m n row p.1 p.2 i)‖
      ≤ p.1 * ∑ i : Fin 3, ‖modeVec m n Q p.1 p.2 i * (starRingEnd ℂ) (modeVec m n row p.1 p.2 i)‖ := by
        gcongr; exact norm_sum_le _ _
    _ ≤ p.1 * ∑ i : Fin 3, ‖modeVec m n Q p.1 p.2 i‖ * C := by
        gcongr with i
        rw [norm_mul, Complex.norm_conj]
        gcongr
        exact mode_norm_le hC m n p.1 p.2 i
    _ = ∑ i : Fin 3, C * (p.1 * ‖modeVec m n Q p.1 p.2 i‖) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring

private theorem mirror_norm (v : Space) : ‖mirror v‖ = ‖v‖ :=
  LinearSolveCore.mirrorIsometry.norm_map v

private theorem row_bound {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} (hc : IsFormData α c)
    (hD : IsCellData α c K S B Cl R) (hR : IsRowShape c K S R) {a : Fin N} (ha : a ∈ R.rowSet) :
    ∃ C, ∀ y, ‖c.row a y‖ ≤ C := by
  obtain ⟨L, hL⟩ := hR.row_slope a ha
  have hTb : Bornology.IsBounded (K.solid ∩ {y : Space | 0 ≤ cylHeight y}) :=
    hc.cellRegion_bounded.subset (fun y hy => hD.solid_in_region hy.1)
  obtain ⟨C, hC⟩ : ∃ C, ∀ y ∈ K.solid ∩ {y : Space | 0 ≤ cylHeight y}, ‖c.row a y‖ ≤ C := by
    rcases (K.solid ∩ {y : Space | 0 ≤ cylHeight y}).eq_empty_or_nonempty with hT | ⟨y₀, hy₀⟩
    · exact ⟨0, fun y hy => by rw [hT] at hy; exact absurd hy (Set.notMem_empty y)⟩
    · obtain ⟨ρ, hρ⟩ := hTb.subset_closedBall y₀
      refine ⟨‖c.row a y₀‖ + L * ρ, fun y hy => ?_⟩
      have h1 := hL.dist_le_mul y hy y₀ hy₀
      have h2 : dist y y₀ ≤ ρ := Metric.mem_closedBall.mp (hρ hy)
      have h3 : ‖c.row a y‖ - ‖c.row a y₀‖ ≤ dist (c.row a y) (c.row a y₀) := by
        rw [dist_eq_norm]; exact norm_sub_norm_le _ _
      have h4 : (L : ℝ) * dist y y₀ ≤ L * ρ := mul_le_mul_of_nonneg_left h2 L.coe_nonneg
      linarith
  refine ⟨max C 0, fun y => ?_⟩
  by_cases hy : y ∈ K.solid
  · by_cases hz : 0 ≤ cylHeight y
    · exact (hC y ⟨hy, hz⟩).trans (le_max_left _ _)
    · have hneg : cylHeight y < 0 := not_le.mp hz
      have hm : mirror y ∈ K.solid ∩ {y : Space | 0 ≤ cylHeight y} := by
        refine ⟨?_, ?_⟩
        · have hy' := hy
          simp only [CellBox.solid, Set.mem_ofPred_eq] at hy' ⊢
          rw [CellDensityModesSolid.mirror_radius, CellDensityModesSolid.mirror_height]
          exact hy'
        · show 0 ≤ cylHeight (mirror y)
          have h5 : cylHeight (mirror y) = -cylHeight y := by simp [cylHeight, mirror]
          rw [h5]
          linarith
      rw [hR.row_mirror a ha y hy hneg, mirror_norm]
      exact (hC _ hm).trans (le_max_left _ _)
  · rw [hD.rows_in_cell a ha y hy, norm_zero]
    exact le_max_right _ _

private theorem mode_zero {k N : ℕ} {c : FracCellData k N} {K : CellBox} {a : Fin N} {n : ℤ} (Q : Space → Space)
    (h : ∀ p ∈ K.rect, rowModeVec c a n p = 0) :
    ∫ p in K.rect, (p.1 : ℂ) * pairC (modeVec c.order n Q p.1 p.2) (rowModeVec c a n p) = 0 := by
  refine setIntegral_eq_zero_of_forall_eq_zero fun p hp => ?_
  rw [h p hp]
  simp [pairC]

theorem pressure_modes {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hpres : ∀ a ∈ R.rowSet, ∀ s n, ∃ P : ℝ → ℂ, (∃ cf : Fin L.degSide → ℂ, ∀ t, P t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = P p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = P p.1)) :
    ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, pairC (modeVec c.order n x.2.2.2.2 p.1 p.2) (rowModeVec c a n p)).re =
      (LayoutRowParts.presSideSum c L a x).re := by
  have hM := fun n => LayoutRowPressureModeIdentity.mode_identity hα1 hα2 hc hD hR hL hx ha hpres n
  obtain ⟨_, _, hQ2, hQm, _⟩ := hx.2.1
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hTf : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have hQn : IntegrableOn (fun y => ‖x.2.2.2.2 y‖) K.solid := by
    have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hTf.ne
    have hm : MemLp x.2.2.2.2 2 (volume.restrict K.solid) :=
      (memLp_two_iff_integrable_sq_norm hQm.restrict).2 ((hQ2 _ hT0).mono_set hTT)
    exact (hm.integrable one_le_two).norm
  obtain ⟨C, hC⟩ := row_bound hc hD hR ha
  have hInt : ∀ n, IntegrableOn (fun p : ℝ × ℝ =>
      (p.1 : ℂ) * pairC (modeVec c.order n x.2.2.2.2 p.1 p.2) (rowModeVec c a n p)) K.rect := fun n =>
    pair_integrable hD.box hQm hQn (hc.base.row_two a).aestronglyMeasurable hC c.order n
  set Bd : ℤ → ℂ := fun n => ∑ s : Fin L.presCount, ∑ d : Fin L.degSide, presSideRowCoef c L a n s d *
    (L.presSegment s).moment true (L.pressMode n x) (L.pressureGradMode n x 0) (L.pressureGradMode n x 2) d
    with hBd
  have hL1 : ∫ p in K.rect, p.1 * (∑ n ∈ R.rowModes, pairC (modeVec c.order n x.2.2.2.2 p.1 p.2)
      (rowModeVec c a n p)).re = (∑ n ∈ R.rowModes, Bd n).re := by
    have e1 : (fun p : ℝ × ℝ => p.1 * (∑ n ∈ R.rowModes, pairC (modeVec c.order n x.2.2.2.2 p.1 p.2)
        (rowModeVec c a n p)).re) = fun p => RCLike.re (∑ n ∈ R.rowModes, (p.1 : ℂ) *
          pairC (modeVec c.order n x.2.2.2.2 p.1 p.2) (rowModeVec c a n p)) := by
      funext p
      rw [← Finset.mul_sum]
      exact (Complex.re_ofReal_mul _ _).symm
    rw [e1, integral_re (integrable_finsetSum _ fun n _ => hInt n), integral_finsetSum _ fun n _ => hInt n]
    exact congrArg Complex.re (Finset.sum_congr rfl fun n _ => hM n)
  have hR1 : LayoutRowParts.presSideSum c L a x = ∑ n ∈ L.modes, Bd n := by
    unfold LayoutRowParts.presSideSum
    rw [Fintype.sum_prod_type, ← Finset.sum_coe_sort L.modes]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Fintype.sum_prod_type]
  have hz : ∀ n, (∀ p ∈ K.rect, rowModeVec c a n p = 0) → Bd n = 0 := fun n h =>
    (hM n).symm.trans (mode_zero _ h)
  have hn0 : R.rowModeOf a ∈ L.modes := by
    rw [hL.layout.modes_eq]; exact hD.row_mode_resolved a ha
  have hn1 : -R.rowModeOf a ∈ L.modes := hL.modes_symm _ hn0
  have hA : ∑ n ∈ R.rowModes, Bd n = ∑ n ∈ R.rowModes ∩ L.modes, Bd n := by
    refine (Finset.sum_subset Finset.inter_subset_left fun n hn hnT => ?_).symm
    have hnL : n ∉ L.modes := fun h => hnT (Finset.mem_inter.2 ⟨hn, h⟩)
    refine hz n fun p hp => hD.row_mode_of a ha n (fun h => hnL (h ▸ hn0)) (fun h => hnL (h ▸ hn1)) p hp
  have hB : ∑ n ∈ L.modes, Bd n = ∑ n ∈ R.rowModes ∩ L.modes, Bd n := by
    refine (Finset.sum_subset Finset.inter_subset_right fun n hn hnT => ?_).symm
    have hnR : n ∉ R.rowModes := fun h => hnT (Finset.mem_inter.2 ⟨h, hn⟩)
    exact hz n fun p hp => hD.row_modes a ha n hnR p hp
  rw [hL1, hR1, hA, hB]

theorem pressure_identity_of_modes {α : ℝ} {k N slots : ℕ} {c : FracCellData k N} {K : CellBox} {S : CellScalars}
    {B : CellBases} {Cl : CellClasses} {R : CellRows N slots k} {L : CellLayout} {x : FieldTuple k} {a : Fin N}
    (hα1 : 1 < α) (hα2 : α < 5 / 4) (hc : IsFormData α c) (hD : IsCellData α c K S B Cl R)
    (hR : IsRowShape c K S R) (hL : IsPressureLayout c K S B L) (hx : IsAdmissible c x) (ha : a ∈ R.rowSet)
    (hpres : ∀ a ∈ R.rowSet, ∀ s n, ∃ P : ℝ → ℂ, (∃ cf : Fin L.degSide → ℂ, ∀ t, P t = ∑ d, cf d * ((L.presSegment s).test d t : ℂ)) ∧
      ∀ p ∈ K.rect, ((L.presSegment s).radial → p.1 = (L.presSegment s).level → rowModeVec c a n p 0 = P p.2) ∧
        (¬ (L.presSegment s).radial → p.2 = (L.presSegment s).level → rowModeVec c a n p 2 = P p.1)) :
    l2Pair x.2.2.2.2 (c.row a) / (4 * Real.pi) = (LayoutRowParts.presSideSum c L a x).re := by
  have hQi := (LayoutRowParts.pairings_integrable hα1 hα2 hc hD hR hL hx ha).2.2.1
  obtain ⟨_, _, hQ2, hQm, _⟩ := hx.2.1
  have hT0 : IsCompact (closure c.cellRegion) := hc.cellRegion_bounded.isCompact_closure
  have hTT : K.solid ⊆ closure c.cellRegion := hD.solid_in_region.trans subset_closure
  have hTf : volume K.solid < ⊤ := (hc.cellRegion_bounded.subset hD.solid_in_region).measure_lt_top
  have hQn : IntegrableOn (fun y => ‖x.2.2.2.2 y‖) K.solid := by
    have : IsFiniteMeasure (volume.restrict K.solid) := isFiniteMeasure_restrict.mpr hTf.ne
    have hm : MemLp x.2.2.2.2 2 (volume.restrict K.solid) :=
      (memLp_two_iff_integrable_sq_norm hQm.restrict).2 ((hQ2 _ hT0).mono_set hTT)
    exact (hm.integrable one_le_two).norm
  have hmir := LayoutRowModes.class_pairing_mirror hx.2.2 (hc.base.row_class a)
  have h := LayoutRowModes.pairing_modes hD.box (hD.rows_in_cell a ha) hQi
    (by filter_upwards [hmir] with y hy _ using hy) c.order R.rowModes (fun p n => rowModeVec c a n p)
    (row_expansion hc hD hR ha) (circle_integrable hD.box hQm hQn)
  rw [h, ← pressure_modes hα1 hα2 hc hD hR hL hx ha hpres]
  field_simp

end Breakdown.FracInternal.LayoutRowPressure
