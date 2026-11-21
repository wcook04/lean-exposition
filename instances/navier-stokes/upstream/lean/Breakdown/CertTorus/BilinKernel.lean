import Breakdown.CertTorus.KernelStatementsIntegral

open MeasureTheory Set Real Filter Topology
open scoped ContDiff ENNReal

noncomputable section

namespace Breakdown.FarField

open Freq

namespace Internal.BilinKernel

theorem holderTriple_six_six_three : ENNReal.HolderTriple 6 6 3 := by
  constructor
  have h6 : (6 : ℝ≥0∞) = 2 * 3 := by norm_num
  rw [← two_mul, h6, ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), ← mul_assoc,
    ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

theorem norm_tensor_le (p q : Space) : ‖(fun j k : Fin 3 => p j * q k)‖ ≤ ‖p‖ * ‖q‖ := by
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun j => ?_
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun k => ?_
  rw [norm_mul]
  exact mul_le_mul (PiLp.norm_apply_le p j) (PiLp.norm_apply_le q k) (norm_nonneg _) (norm_nonneg _)

theorem continuous_tensor :
    Continuous (fun r : Space × Space => (fun j k : Fin 3 => r.1 j * r.2 k)) := by
  refine continuous_pi fun j => continuous_pi fun k => ?_
  exact ((PiLp.continuous_apply 2 _ j).comp continuous_fst).mul
    ((PiLp.continuous_apply 2 _ k).comp continuous_snd)

theorem tensorField_aestronglyMeasurable {a b : Space → Space}
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume) :
    AEStronglyMeasurable (tensorField a b) volume :=
  continuous_tensor.comp_aestronglyMeasurable (ha.prodMk hb)

theorem tensor_nnnorm_le (a b : Space → Space) :
    ∀ᵐ z ∂(volume : Measure Space),
      ‖(fun j k : Fin 3 => a z j * b z k)‖₊ ≤ (1 : NNReal) * ‖a z‖₊ * ‖b z‖₊ :=
  Filter.Eventually.of_forall fun z => by
    rw [one_mul, ← NNReal.coe_le_coe]
    push_cast
    exact norm_tensor_le (a z) (b z)

theorem eLpNorm_tensorField_le {a b : Space → Space}
    (ha : AEStronglyMeasurable a volume) (hb : AEStronglyMeasurable b volume) :
    eLpNorm (tensorField a b) 3 volume ≤ eLpNorm a 6 volume * eLpNorm b 6 volume := by
  have := holderTriple_six_six_three
  have h := eLpNorm_le_eLpNorm_mul_eLpNorm_of_nnnorm (p := 6) (q := 6) (r := 3) ha hb
    (fun p q : Space => (fun j k : Fin 3 => p j * q k)) 1 (tensor_nnnorm_le a b)
  rw [ENNReal.coe_one, one_mul] at h
  exact h

theorem tensorField_memLp {a b : Space → Space} (ha : MemLp a 6 volume) (hb : MemLp b 6 volume) :
    MemLp (tensorField a b) 3 volume :=
  ⟨tensorField_aestronglyMeasurable ha.1 hb.1,
    lt_of_le_of_lt (eLpNorm_tensorField_le ha.1 hb.1) (ENNReal.mul_lt_top ha.2 hb.2)⟩

theorem kernelConv_sub (τ : ℝ) (F G : Space → Fin 3 → Fin 3 → ℝ) (y : Space)
    (hF : ∀ i : Fin 3, Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k))
    (hG : ∀ i : Fin 3, Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * G z j k)) :
    kernelConv τ (F - G) y = kernelConv τ F y - kernelConv τ G y := by
  unfold kernelConv
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← sub_smul, ← integral_sub (hF i) (hG i)]
  congr 1
  congr 1
  funext z
  simp only [Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem kernelConv_tensor_congr_ae (τ : ℝ) {a b : Space → Space} (h : a =ᵐ[volume] b) (y : Space) :
    kernelConv τ (tensorField a a) y = kernelConv τ (tensorField b b) y := by
  unfold kernelConv
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_congr_ae (g := fun z => ∑ j : Fin 3, ∑ k : Fin 3,
    lerayKernel i j k τ (y - z) * tensorField b b z j k)]
  filter_upwards [h] with z hz
  simp only [tensorField, hz]

theorem tensor_sub_eq (a b : Space → Space) :
    tensorField a a - tensorField b b = tensorField (a - b) a + tensorField b (a - b) := by
  funext z j k
  simp only [tensorField, Pi.sub_apply, Pi.add_apply, PiLp.sub_apply]
  ring

theorem toReal_eLpNorm_tensor_sub_le (w v : L6R) :
    (eLpNorm (tensorField (w : Space → Space) w - tensorField (v : Space → Space) v) 3 volume).toReal ≤
      (eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume).toReal * ‖w‖ +
        ‖v‖ * (eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume).toReal := by
  have hw := Lp.memLp w
  have hv := Lp.memLp v
  have hd : MemLp ((w : Space → Space) - (v : Space → Space)) 6 volume := hw.sub hv
  have ed : eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume =
      ENNReal.ofReal (eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume).toReal :=
    (ENNReal.ofReal_toReal hd.2.ne).symm
  have ew : eLpNorm (w : Space → Space) 6 volume = ENNReal.ofReal ‖w‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal hw.2.ne]
  have ev : eLpNorm (v : Space → Space) 6 volume = ENNReal.ofReal ‖v‖ := by
    rw [Lp.norm_def, ENNReal.ofReal_toReal hv.2.ne]
  have h0 : 0 ≤ (eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume).toReal := ENNReal.toReal_nonneg
  refine ENNReal.toReal_le_of_le_ofReal (by positivity) ?_
  rw [tensor_sub_eq]
  calc eLpNorm (tensorField ((w : Space → Space) - (v : Space → Space)) w + tensorField (v : Space → Space) ((w : Space → Space) - (v : Space → Space))) 3 volume
      ≤ eLpNorm (tensorField ((w : Space → Space) - (v : Space → Space)) w) 3 volume +
          eLpNorm (tensorField (v : Space → Space) ((w : Space → Space) - (v : Space → Space))) 3 volume :=
        eLpNorm_add_le (tensorField_aestronglyMeasurable hd.1 hw.1)
          (tensorField_aestronglyMeasurable hv.1 hd.1) (by norm_num)
    _ ≤ eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume * eLpNorm (w : Space → Space) 6 volume +
          eLpNorm (v : Space → Space) 6 volume * eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume :=
        add_le_add (eLpNorm_tensorField_le hd.1 hw.1) (eLpNorm_tensorField_le hv.1 hd.1)
    _ = ENNReal.ofReal ((eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume).toReal * ‖w‖ +
          ‖v‖ * (eLpNorm ((w : Space → Space) - (v : Space → Space)) 6 volume).toReal) := by
        rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul h0,
          ENNReal.ofReal_mul (norm_nonneg _), ← ed, ← ew, ← ev]

theorem kernelConv_tendsto {C τ : ℝ}
    (hC : ∀ F : Space → Fin 3 → Fin 3 → ℝ, MemLp F 3 volume → ∀ y : Space,
      (∀ i : Fin 3, Integrable (fun z => ∑ j : Fin 3, ∑ k : Fin 3, lerayKernel i j k τ (y - z) * F z j k)) ∧
        ‖kernelConv τ F y‖ ≤ C * τ ^ (-(1 : ℝ)) * (eLpNorm F 3 volume).toReal)
    {w : ℕ → L6R} {v : L6R} (hw : Tendsto w atTop (𝓝 v)) (y : Space) :
    Tendsto (fun n => kernelConv τ (tensorField (w n : Space → Space) (w n : Space → Space)) y) atTop
      (𝓝 (kernelConv τ (tensorField (v : Space → Space) (v : Space → Space)) y)) := by
  have hT : ∀ n, MemLp (tensorField (w n : Space → Space) (w n : Space → Space)) 3 volume :=
    fun n => tensorField_memLp (Lp.memLp _) (Lp.memLp _)
  have hTv : MemLp (tensorField (v : Space → Space) (v : Space → Space)) 3 volume :=
    tensorField_memLp (Lp.memLp _) (Lp.memLp _)
  have ha : Tendsto (fun n => (eLpNorm ((w n : Space → Space) - (v : Space → Space)) 6 volume).toReal) atTop (𝓝 0) := by
    have h := (Lp.tendsto_Lp_iff_tendsto_eLpNorm' w v).mp hw
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h
    rw [ENNReal.toReal_zero] at h2
    exact h2
  have hnorm : Tendsto (fun n => ‖w n‖) atTop (𝓝 ‖v‖) := (continuous_norm.tendsto v).comp hw
  have hb : Tendsto (fun n => (eLpNorm ((w n : Space → Space) - (v : Space → Space)) 6 volume).toReal * ‖w n‖ +
      ‖v‖ * (eLpNorm ((w n : Space → Space) - (v : Space → Space)) 6 volume).toReal) atTop (𝓝 0) := by
    simpa using (ha.mul hnorm).add (tendsto_const_nhds.mul ha)
  have hd : Tendsto (fun n => (eLpNorm (tensorField (w n : Space → Space) (w n : Space → Space) -
      tensorField (v : Space → Space) (v : Space → Space)) 3 volume).toReal) atTop (𝓝 0) :=
    squeeze_zero (fun n => ENNReal.toReal_nonneg) (fun n => toReal_eLpNorm_tensor_sub_le (w n) v) hb
  have hK : Tendsto (fun n => C * τ ^ (-(1 : ℝ)) * (eLpNorm (tensorField (w n : Space → Space)
      (w n : Space → Space) - tensorField (v : Space → Space) (v : Space → Space)) 3 volume).toReal)
      atTop (𝓝 0) := by
    simpa using hd.const_mul (C * τ ^ (-(1 : ℝ)))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) hK
  rw [← kernelConv_sub τ _ _ y (hC _ (hT n) y).1 (hC _ hTv y).1]
  exact (hC _ ((hT n).sub hTv) y).2

end Internal.BilinKernel

open Internal.BilinKernel in
theorem bilinKernel_of_test_decay (hBT : BilinTestKernel) (hTD : KernelConvTestDecay)
    (hLp : KernelConvL3Pointwise) : BilinKernel := by
  obtain ⟨C, hC⟩ := hLp
  intro τ hτ u
  obtain ⟨x, hxs, hxu⟩ := mem_closure_iff_seq_limit.mp (testDense_holds.2 u)
  choose φ hφ hφx using fun n => testSpan_holds (x n) (hxs n)
  have hvn : Tendsto (fun n => velocity (x n)) atTop (𝓝 (velocity u)) :=
    (velocity.continuous.tendsto u).comp hxu
  have hc : Continuous fun w : X => velocity (bilinX τ w w) :=
    velocity.continuous.comp ((bilinX τ).continuous.clm_apply continuous_id)
  have hLn : Tendsto (fun n => velocity (bilinX τ (x n) (x n))) atTop
      (𝓝 (velocity (bilinX τ u u))) := (hc.tendsto u).comp hxu
  have hv : ∀ n, (velocity (x n) : Space → Space) =ᵐ[volume] φ n := by
    intro n
    have h := Freq.Internal.BilinTestFormula.velocity_test velocity_holds (hφ n)
    rwa [hφx n] at h
  have hKn : ∀ n, (velocity (bilinX τ (x n) (x n)) : Space → Space) =ᵐ[volume]
      fun y => -kernelConv τ (tensorField (φ n) (φ n)) y := by
    intro n
    have h1 : bilinX τ (x n) (x n) =
        embedX (fun y => -kernelConv τ (tensorField (φ n) (φ n)) y) := by
      rw [← hφx n]
      exact hBT τ hτ (φ n) (hφ n)
    rw [h1]
    exact velocityDecay_holds _ (hTD τ hτ (φ n) (hφ n))
  have hmeas : TendstoInMeasure volume (fun n => (velocity (bilinX τ (x n) (x n)) : Space → Space))
      atTop (velocity (bilinX τ u u) : Space → Space) :=
    tendstoInMeasure_of_tendsto_eLpNorm (p := 6) (by norm_num)
      (fun n => Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable _)
      ((Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ _).mp hLn)
  have hsub := hmeas.exists_seq_tendsto_ae
  obtain ⟨ns, hns, hae⟩ := hsub
  have hall : ∀ᵐ y ∂(volume : Measure Space), ∀ n,
      (velocity (bilinX τ (x n) (x n)) : Space → Space) y =
        -kernelConv τ (tensorField (φ n) (φ n)) y := by
    rw [ae_all_iff]
    intro n
    exact hKn n
  filter_upwards [hae, hall] with y hy1 hy2
  have hR : Tendsto (fun i => (velocity (bilinX τ (x (ns i)) (x (ns i))) : Space → Space) y) atTop
      (𝓝 (-kernelConv τ (tensorField (velocity u : Space → Space) (velocity u : Space → Space)) y)) := by
    have h := ((kernelConv_tendsto (hC τ hτ) hvn y).comp hns.tendsto_atTop).neg
    refine h.congr fun i => ?_
    have e1 : kernelConv τ (tensorField (velocity (x (ns i)) : Space → Space)
        (velocity (x (ns i)) : Space → Space)) y = kernelConv τ (tensorField (φ (ns i)) (φ (ns i))) y :=
      kernelConv_tensor_congr_ae τ (hv (ns i)) y
    exact (congrArg Neg.neg e1).trans (hy2 (ns i)).symm
  exact tendsto_nhds_unique hy1 hR

end Breakdown.FarField
