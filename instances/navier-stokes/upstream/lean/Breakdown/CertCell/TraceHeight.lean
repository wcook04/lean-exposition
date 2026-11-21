import Breakdown.CertCell.BridgeStatements
import Breakdown.Weak.ConstOfWeakDeriv

open MeasureTheory Set
open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace Bridge

private theorem weak_identity_component (L : ℂ →L[ℝ] ℝ) {f fz : ℝ → ℂ} {l r : ℝ}
    (hW : HasWeakDerivOn f fz l r) (θ : ℝ → ℝ) (hθ : ContDiff ℝ ∞ θ) (hc : HasCompactSupport θ)
    (hts : tsupport θ ⊆ Ioo l r) :
    ∫ t, deriv θ t * L (f t) = ∫ t, θ t * -(L (fz t)) := by
  have hdc : Continuous (deriv θ) := hθ.continuous_deriv (by simp)
  obtain ⟨C1, hC1⟩ := hdc.bounded_above_of_compact_support hc.deriv
  obtain ⟨C2, hC2⟩ := hθ.continuous.bounded_above_of_compact_support hc
  have i1 : Integrable (fun z => f z * ((deriv θ z : ℝ) : ℂ)) (volume.restrict (Ioo l r)) :=
    hW.1.mul_bdd (Complex.continuous_ofReal.comp hdc).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC1 x)
  have i2 : Integrable (fun z => fz z * ((θ z : ℝ) : ℂ)) (volume.restrict (Ioo l r)) :=
    hW.2.1.mul_bdd (Complex.continuous_ofReal.comp hθ.continuous).aestronglyMeasurable
      (Filter.Eventually.of_forall fun x => by simpa using hC2 x)
  have key := congrArg L (hW.2.2 θ hθ hc hts)
  rw [← L.integral_comp_comm i1, L.map_neg, ← L.integral_comp_comm i2] at key
  have e1 : ∀ z s, L (f z * ((s : ℝ) : ℂ)) = s * L (f z) := fun z s => by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul]
  have e2 : ∀ z s, L (fz z * ((s : ℝ) : ℂ)) = s * L (fz z) := fun z s => by
    rw [mul_comm, ← Complex.real_smul, L.map_smul, smul_eq_mul]
  simp_rw [e1, e2] at key
  have z1 : ∀ x, x ∉ Ioo l r → θ x = 0 := fun x hx =>
    image_eq_zero_of_notMem_tsupport (fun h => hx (hts h))
  have z2 : ∀ x, x ∉ Ioo l r → deriv θ x = 0 := fun x hx =>
    Function.notMem_support.1 (fun h => hx (hts (support_deriv_subset h)))
  have a1 : ∫ t, deriv θ t * L (f t) = ∫ t in Ioo l r, deriv θ t * L (f t) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [z2 x hx, zero_mul]).symm
  have a2 : ∫ t, θ t * -(L (fz t)) = ∫ t in Ioo l r, θ t * -(L (fz t)) :=
    (setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by rw [z1 x hx, zero_mul]).symm
  rw [a1, a2, key, ← integral_neg]
  congr 1
  funext t
  ring

private theorem interval_integrable_inside {fz : ℝ → ℂ} {l r a b : ℝ}
    (h : IntegrableOn fz (Ioo l r)) (hla : l ≤ a) (hab : a ≤ b) (hbr : b < r) :
    IntervalIntegrable fz volume a b :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (h.mono_set fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)

private theorem weak_primitive_representative {f fz : ℝ → ℂ} {l r : ℝ} (hlr : l < r)
    (hW : HasWeakDerivOn f fz l r) :
    ∃ c : ℂ, ∀ᵐ t ∂(volume.restrict (Ioo l r)), f t = c + ∫ τ in l..t, fz τ := by
  obtain ⟨c1, h1⟩ := WeakProfile.constOfWeakDeriv_holds (fun t => Complex.reCLM (f t))
    (fun t => -(Complex.reCLM (fz t))) l r hlr (Complex.reCLM.integrable_comp hW.1)
    (Complex.reCLM.integrable_comp hW.2.1).neg (weak_identity_component Complex.reCLM hW)
  obtain ⟨c2, h2⟩ := WeakProfile.constOfWeakDeriv_holds (fun t => Complex.imCLM (f t))
    (fun t => -(Complex.imCLM (fz t))) l r hlr (Complex.imCLM.integrable_comp hW.1)
    (Complex.imCLM.integrable_comp hW.2.1).neg (weak_identity_component Complex.imCLM hW)
  refine ⟨⟨c1, c2⟩, ?_⟩
  filter_upwards [h1, h2, ae_restrict_mem measurableSet_Ioo] with t hr hi ht
  have hii : IntervalIntegrable fz volume l t :=
    interval_integrable_inside hW.2.1 le_rfl ht.1.le ht.2
  have er := Complex.reCLM.intervalIntegral_comp_comm hii
  have ei := Complex.imCLM.intervalIntegral_comp_comm hii
  rw [intervalIntegral.integral_neg] at hr hi
  apply Complex.ext
  · simp only [Complex.reCLM_apply] at hr er
    rw [Complex.add_re, ← er, hr, sub_neg_eq_add]
  · simp only [Complex.imCLM_apply] at hi ei
    rw [Complex.add_im, ← ei, hi, sub_neg_eq_add]

private theorem integral_primitive_eq_weighted {g : ℝ → ℂ} {h : ℝ} (hh : 0 < h)
    (hg : IntegrableOn g (Ioc 0 h)) :
    ∫ z in (0 : ℝ)..h, ∫ s in (0 : ℝ)..z, g s = ∫ s in (0 : ℝ)..h, g s * ((h - s : ℝ) : ℂ) := by
  set μ := volume.restrict (Ioc (0 : ℝ) h) with hμ
  set K : ℝ × ℝ → ℂ := Set.indicator {p : ℝ × ℝ | p.2 ≤ p.1} (fun p => g p.2) with hK
  have hone : Integrable (fun _ : ℝ => (1 : ℂ)) μ :=
    integrableOn_const (by simp)
  have hKi : Integrable K (μ.prod μ) := by
    have := (hone.mul_prod (show Integrable g μ from hg)).indicator
      (measurableSet_le measurable_snd measurable_fst)
    simpa [hK, one_mul] using this
  have inner : ∀ z ∈ Ioc (0 : ℝ) h, ∫ s in (0 : ℝ)..z, g s = ∫ s, K (z, s) ∂μ := by
    intro z hz
    rw [intervalIntegral.integral_of_le hz.1.le]
    have : (fun s => K (z, s)) = Set.indicator (Iic z) g := by
      funext s
      simp [hK, Set.indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Iic, Ioc_inter_Iic, min_eq_right hz.2]
  have outer : ∀ s ∈ Ioc (0 : ℝ) h, ∫ z, K (z, s) ∂μ = g s * ((h - s : ℝ) : ℂ) := by
    intro s hs
    have : (fun z => K (z, s)) = Set.indicator (Ici s) (fun _ => g s) := by
      funext z
      simp [hK, Set.indicator_apply]
    rw [this, hμ, setIntegral_indicator measurableSet_Ici, setIntegral_const]
    have hset : Ioc (0 : ℝ) h ∩ Ici s = Icc s h := by
      ext x
      simp only [mem_inter_iff, mem_Ioc, mem_Ici, mem_Icc]
      constructor
      · rintro ⟨⟨_, b⟩, c⟩
        exact ⟨c, b⟩
      · rintro ⟨c, b⟩
        exact ⟨⟨by linarith [hs.1], b⟩, c⟩
    rw [hset, Real.volume_real_Icc_of_le hs.2, Complex.real_smul, mul_comm]
  rw [intervalIntegral.integral_of_le hh.le, intervalIntegral.integral_of_le hh.le,
    setIntegral_congr_fun measurableSet_Ioc inner,
    setIntegral_congr_fun measurableSet_Ioc fun s hs => (outer s hs).symm]
  exact integral_integral_swap (f := fun z s => K (z, s)) hKi

private theorem upperTrace_primitive {g : ℝ → ℂ} {h : ℝ} (hh : 0 < h) (F0 : ℂ)
    (hg : IntegrableOn g (Ioc 0 h)) :
    -∫ z in (0 : ℝ)..h, (g z * ((1 - z / h : ℝ) : ℂ) - (F0 + ∫ s in (0 : ℝ)..z, g s) / (h : ℂ))
      = F0 := by
  have hh0 : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
  have hgi : IntervalIntegrable g volume 0 h :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hh.le).2 hg
  have hGc : ContinuousOn (fun z => ∫ s in (0 : ℝ)..z, g s) (uIcc 0 h) :=
    intervalIntegral.continuousOn_primitive_interval (by
      rw [uIcc_of_le hh.le]
      exact (integrableOn_Icc_iff_integrableOn_Ioc).2 hg)
  have hGi : IntervalIntegrable (fun z => ∫ s in (0 : ℝ)..z, g s) volume 0 h :=
    hGc.intervalIntegrable
  have hwi : IntervalIntegrable (fun z => g z * ((h - z : ℝ) : ℂ)) volume 0 h :=
    hgi.mul_continuousOn (by fun_prop)
  have pt : ∀ z, g z * ((1 - z / h : ℝ) : ℂ) - (F0 + ∫ s in (0 : ℝ)..z, g s) / (h : ℂ)
      = (g z * ((h - z : ℝ) : ℂ) - ∫ s in (0 : ℝ)..z, g s) / (h : ℂ) - F0 / (h : ℂ) := by
    intro z
    push_cast
    field_simp
    ring
  simp_rw [pt]
  rw [intervalIntegral.integral_sub ((hwi.sub hGi).div_const _) intervalIntegrable_const,
    intervalIntegral.integral_div, intervalIntegral.integral_sub hwi hGi,
    integral_primitive_eq_weighted hh hg, sub_self, zero_div, intervalIntegral.integral_const]
  simp only [sub_zero, Complex.real_smul]
  field_simp
  ring

theorem traceHeight : TraceHeightHolds := by
  intro f fz h h' hh hhh' hW
  have hh' : 0 < h' := lt_of_lt_of_le hh hhh'
  have hlr : -(2 * h') < 2 * h' := by linarith
  obtain ⟨c, hc⟩ := weak_primitive_representative hlr hW
  have hval : ∀ k, 0 < k → k ≤ h' →
      upperTrace f fz k = c + ∫ τ in (-(2 * h'))..0, fz τ := by
    intro k hk hkh
    have hgk : IntegrableOn fz (Ioc 0 k) :=
      hW.2.1.mono_set fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩
    rw [← upperTrace_primitive hk (c + ∫ τ in (-(2 * h'))..0, fz τ) hgk, upperTrace]
    congr 1
    apply intervalIntegral.integral_congr_ae
    have hc' := (ae_restrict_iff' measurableSet_Ioo).1 hc
    filter_upwards [hc'] with z hz hzk
    rw [uIoc_of_le hk.le] at hzk
    have hzi : z ∈ Ioo (-(2 * h')) (2 * h') := ⟨by linarith [hzk.1], by linarith [hzk.2]⟩
    rw [hz hzi, add_assoc, ← intervalIntegral.integral_add_adjacent_intervals
      (interval_integrable_inside hW.2.1 le_rfl (by linarith) (by linarith))
      (interval_integrable_inside hW.2.1 (by linarith) hzk.1.le (by linarith [hzk.2]))]
  rw [hval h hh hhh', hval h' hh' le_rfl]

end Bridge

end CertCell

end Breakdown
