import Breakdown.FracCell.UnresolvedRowClassSt
import Breakdown.FracCell.ModeGradSquare
import Breakdown.FracCell.CellDensityModesSolid
import Breakdown.FracCell.MeshTailEnergy

open MeasureTheory Set Real

noncomputable section

namespace Breakdown.FracInternal.ClassRowSq

open SteadyCert CellCert CellCert.CellAnalysis
open CellCert.CellAnalysis.LowEntry.Internal CellCert.CellAnalysis.ModeGradSquare.Internal

theorem pos_phase_per (m : ℕ) (n : ℤ) (θ : ℝ) :
    Complex.exp (((azimuth m n * (θ + 2 * π) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((azimuth m n * θ : ℝ) : ℂ) * Complex.I) := by
  have e : ((azimuth m n * (θ + 2 * π) : ℝ) : ℂ) * Complex.I =
      ((azimuth m n * θ : ℝ) : ℂ) * Complex.I + (((n * (m : ℤ)) : ℤ) : ℂ) * (2 * π * Complex.I) := by
    simp only [azimuth]; push_cast; ring
  rw [e, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem orth_circ {m : ℕ} (hm : 1 ≤ m) (n n' : ℤ) :
    ∫ θ in Ioo (-π) π, ((1 / (2 * π) : ℝ) : ℂ) *
        (Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) *
          (starRingEnd ℂ) (Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)))
      = if n = n' then 1 else 0 := by
  have h := per_interval (fun θ : ℝ => ((1 / (2 * π) : ℝ) : ℂ) *
        (Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) *
          (starRingEnd ℂ) (Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I))))
    (fun θ => by simp only [pos_phase_per])
  rw [← h, intervalIntegral.integral_of_le (by positivity)]
  exact MeshTailEnergy.exp_orth hm n n'

theorem per_real (f : ℝ → ℝ) (hf : Function.Periodic f (2 * π)) :
    ∫ θ in (0 : ℝ)..(2 * π), f θ = ∫ θ in Ioo (-π) π, f θ := by
  have h := hf.intervalIntegral_add_eq 0 (-π)
  rw [zero_add, show -π + 2 * π = π by ring] at h
  rw [h, intervalIntegral.integral_of_le (by linarith [Real.pi_pos]), integral_Ioc_eq_integral_Ioo]

theorem coef_sq_le_circ {m : ℕ} (hm : 1 ≤ m) (s : Finset ℤ) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioo (-π) π))) :
    ∑ n ∈ s, ‖(1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
        Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * f θ‖ ^ 2
      ≤ (1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖f θ‖ ^ 2 := by
  have : IsFiniteMeasure (volume.restrict (Ioo (-π) π)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  set ν : Measure ℝ := volume.restrict (Ioo (-π) π) with hν
  set e : ℤ → ℝ → ℂ := fun n θ => Complex.exp (((azimuth m n * θ : ℝ) : ℂ) * Complex.I) with he
  set a : ℤ → ℂ := fun n => (1 / (2 * π) : ℂ) * ∫ θ, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * f θ ∂ν
    with ha
  set P : ℝ → ℂ := fun θ => ∑ n ∈ s, a n * e n θ with hP
  have hconj : ∀ n θ, (starRingEnd ℂ) (e n θ) = Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) := by
    intro n θ
    simp only [he, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring_nf
  have hec : ∀ n, Continuous (e n) := fun n => by simp only [he]; fun_prop
  have hPc : Continuous P := by
    simp only [hP]
    exact continuous_finsetSum _ fun n _ => continuous_const.mul (hec n)
  have hfi : Integrable f ν := hf.integrable one_le_two
  have hf2 : Integrable (fun θ => ‖f θ‖ ^ 2) ν := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  have hP2 : Integrable (fun θ => ‖P θ‖ ^ 2) ν :=
    (hPc.norm.pow 2).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hkn : ∀ n, Integrable (fun θ => Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * f θ) ν :=
    fun n => hfi.norm.mono'
      ((by fun_prop : Continuous fun θ : ℝ => Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable.mul
        hfi.1)
      (ae_of_all _ fun θ => by
        rw [norm_mul, ← Complex.ofReal_neg, Complex.norm_exp_ofReal_mul_I, one_mul])
  have hpt : ∀ θ, ((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ) = ∑ n ∈ s, (starRingEnd ℂ) (a n) *
      ((1 / (2 * π) : ℂ) * (Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) * f θ)) := by
    intro θ
    simp only [hP, map_sum, map_mul, hconj, Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    push_cast
    ring
  have hcrI : Integrable (fun θ => ((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ)) ν := by
    rw [show (fun θ => ((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ)) = _ from funext hpt]
    exact integrable_finsetSum s fun n _ => ((hkn n).const_mul _).const_mul _
  have hcr : ∫ θ, ((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ) ∂ν =
      ∑ n ∈ s, ((‖a n‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    rw [integral_finsetSum s fun n _ => ((hkn n).const_mul _).const_mul _]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [integral_const_mul, integral_const_mul]
    show (starRingEnd ℂ) (a n) * a n = _
    rw [Complex.conj_mul', Complex.ofReal_pow]
  have hcrRe : Integrable (fun θ => (((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ)).re) ν :=
    hcrI.re
  have hre : ∫ θ, (((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ)).re ∂ν = ∑ n ∈ s, ‖a n‖ ^ 2 := by
    have h := integral_re hcrI
    simp only [RCLike.re_to_complex] at h
    rw [h, hcr, Complex.re_sum]
    simp only [Complex.ofReal_re]
  have hpp : ∫ θ, (1 / (2 * π)) * ‖P θ‖ ^ 2 ∂ν = ∑ n ∈ s, ‖a n‖ ^ 2 :=
    MeshTailEnergy.sq_sum_orth (μ := ν) s (fun _ => 1 / (2 * π)) e a
      (fun k _ k' _ => (continuous_const.mul ((hec k).mul (Complex.continuous_conj.comp (hec k')))).integrableOn_Icc.mono_set
        Ioo_subset_Icc_self)
      (fun k _ k' _ => orth_circ hm k k')
  have hexp : ∀ θ, (1 / (2 * π)) * ‖f θ - P θ‖ ^ 2 = (1 / (2 * π)) * ‖f θ‖ ^ 2
      - 2 * (((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ)).re + (1 / (2 * π)) * ‖P θ‖ ^ 2 := by
    intro θ
    simp only [Complex.sq_norm, Complex.normSq_sub, Complex.re_ofReal_mul, mul_comm ((starRingEnd ℂ) (P θ)) (f θ)]
    ring
  have hnn : 0 ≤ ∫ θ, (1 / (2 * π)) * ‖f θ - P θ‖ ^ 2 ∂ν :=
    integral_nonneg fun θ => by positivity
  have hI : ∫ θ, (1 / (2 * π)) * ‖f θ - P θ‖ ^ 2 ∂ν =
      (1 / (2 * π)) * ∫ θ, ‖f θ‖ ^ 2 ∂ν - 2 * ∑ n ∈ s, ‖a n‖ ^ 2 + ∑ n ∈ s, ‖a n‖ ^ 2 := by
    have h1 : Integrable (fun θ => 1 / (2 * π) * ‖f θ‖ ^ 2
        - 2 * (((1 / (2 * π) : ℝ) : ℂ) * ((starRingEnd ℂ) (P θ) * f θ)).re) ν :=
      (hf2.const_mul _).sub (hcrRe.const_mul 2)
    rw [integral_congr_ae (ae_of_all _ hexp), integral_add h1 (hP2.const_mul _),
      integral_sub (hf2.const_mul _) (hcrRe.const_mul 2), integral_const_mul, integral_const_mul, hre, hpp]
  show ∑ n ∈ s, ‖a n‖ ^ 2 ≤ _
  linarith

theorem frame_sq (θ : ℝ) (u : Space) : ∑ b : Fin 3, frameVec θ u b ^ 2 = ‖u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [frameVec, Fin.sum_univ_three, radialUnit, angularUnit, axialUnit, inner_add_right,
    EuclideanSpace.inner_single_right, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, conj_trivial, one_mul]
  rw [PiLp.inner_apply]
  simp only [Fin.sum_univ_three, conj_trivial, RCLike.inner_apply]
  linear_combination (u 0 ^ 2 + u 1 ^ 2) * Real.sin_sq_add_cos_sq θ

theorem frame_lin (θ : ℝ) {ι : Type*} (A : Finset ι) (w : ι → ℝ) (v : ι → Space) (b : Fin 3) :
    frameVec θ (∑ i ∈ A, w i • v i) b = ∑ i ∈ A, w i * frameVec θ (v i) b := by
  simp only [frameVec_eq, sum_inner, real_inner_smul_left]

theorem circ_pair {U : ℝ → Space} (hU : AEStronglyMeasurable U (volume.restrict (Ioo (-π) π))) :
    AEStronglyMeasurable (fun θ : ℝ => (θ, U θ)) (volume.restrict (Ioo (-π) π)) :=
  measurable_id.aestronglyMeasurable.prodMk hU

theorem frame_meas {U : ℝ → Space} (hU : AEStronglyMeasurable U (volume.restrict (Ioo (-π) π))) (b : Fin 3) :
    AEStronglyMeasurable (fun θ => ((frameVec θ (U θ) b : ℝ) : ℂ)) (volume.restrict (Ioo (-π) π)) := by
  have hc : Continuous (fun q : ℝ × Space => ((frameVec q.1 q.2 b : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp (frameVec_cont b)
  have := hc.comp_aestronglyMeasurable (μ := volume.restrict (Ioo (-π) π)) (circ_pair hU)
  exact this

theorem kernel_meas (m : ℕ) (n : ℤ) {U : ℝ → Space} (hU : AEStronglyMeasurable U (volume.restrict (Ioo (-π) π)))
    (b : Fin 3) :
    AEStronglyMeasurable (fun θ => velKernel m n b θ (U θ)) (volume.restrict (Ioo (-π) π)) := by
  have := (velKernel_cont m n b).comp_aestronglyMeasurable (μ := volume.restrict (Ioo (-π) π)) (circ_pair hU)
  exact this

theorem frame_norm_le (θ : ℝ) (u : Space) (b : Fin 3) : ‖((frameVec θ u b : ℝ) : ℂ)‖ ≤ ‖u‖ := by
  rw [Complex.norm_real, Real.norm_eq_abs, frameVec_eq]
  exact inner_unit_bound θ u b

theorem frame_memLp {U : ℝ → Space} (hU : MemLp U 2 (volume.restrict (Ioo (-π) π))) (b : Fin 3) :
    MemLp (fun θ => ((frameVec θ (U θ) b : ℝ) : ℂ)) 2 (volume.restrict (Ioo (-π) π)) :=
  MemLp.of_le (g := U) hU (frame_meas hU.aestronglyMeasurable b)
    (ae_of_all _ fun θ => frame_norm_le θ (U θ) b)

theorem lin_mode (m : ℕ) (n : ℤ) {ι : Type*} (A : Finset ι) (w : ι → ℝ)
    (v : ι → Space → Space) (r z : ℝ) (b : Fin 3)
    (hv : ∀ i ∈ A, MemLp (fun θ => v i (cylPoint r θ z)) 2 (volume.restrict (Ioo (-π) π))) :
    ∑ i ∈ A, ((w i : ℝ) : ℂ) * modeVec m n (v i) r z b =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((frameVec θ (∑ i ∈ A, w i • v i (cylPoint r θ z)) b : ℝ) : ℂ) := by
  have : IsFiniteMeasure (volume.restrict (Ioo (-π) π)) :=
    isFiniteMeasure_restrict.2 measure_Ioo_lt_top.ne
  have hk : ∀ i ∈ A, Integrable (fun θ => velKernel m n b θ (v i (cylPoint r θ z)))
      (volume.restrict (Ioo (-π) π)) :=
    fun i hi => MeasureTheory.Integrable.mono' (g := fun θ => ‖v i (cylPoint r θ z)‖)
      ((hv i hi).integrable one_le_two).norm (kernel_meas m n (hv i hi).aestronglyMeasurable b)
      (ae_of_all _ fun θ => velKernel_bound m n b θ _)
  have e1 : ∀ i, modeVec m n (v i) r z b =
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n b θ (v i (cylPoint r θ z)) :=
    fun i => modeVec_eq m n (v i) b (r, z)
  have e2 : ∀ θ, ∑ i ∈ A, ((w i : ℝ) : ℂ) * velKernel m n b θ (v i (cylPoint r θ z)) =
      Complex.exp (-((azimuth m n * θ : ℝ) : ℂ) * Complex.I) *
        ((frameVec θ (∑ i ∈ A, w i • v i (cylPoint r θ z)) b : ℝ) : ℂ) := by
    intro θ
    rw [frame_lin, Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [velKernel, Complex.ofReal_mul]
    ring
  calc ∑ i ∈ A, ((w i : ℝ) : ℂ) * modeVec m n (v i) r z b
      = (1 / (2 * π) : ℂ) * ∑ i ∈ A, ∫ θ in Ioo (-π) π,
          ((w i : ℝ) : ℂ) * velKernel m n b θ (v i (cylPoint r θ z)) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [e1, integral_const_mul]
        ring
    _ = (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π,
          ∑ i ∈ A, ((w i : ℝ) : ℂ) * velKernel m n b θ (v i (cylPoint r θ z)) := by
        rw [integral_finsetSum A fun i hi => (hk i hi).const_mul _]
    _ = _ := by simp only [e2]

theorem point_bound {m : ℕ} (hm : 1 ≤ m) (s : Finset ℤ) {ι : Type*} (A : Finset ι) (w : ι → ℝ)
    (v : ι → Space → Space) (r z : ℝ)
    (hv : ∀ i ∈ A, MemLp (fun θ => v i (cylPoint r θ z)) 2 (volume.restrict (Ioo (-π) π))) :
    ∑ n ∈ s, vecSq (fun b => ∑ i ∈ A, ((w i : ℝ) : ℂ) * modeVec m n (v i) r z b)
      ≤ (1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖∑ i ∈ A, w i • v i (cylPoint r θ z)‖ ^ 2 := by
  have hUm : MemLp (fun θ => ∑ i ∈ A, w i • v i (cylPoint r θ z)) 2 (volume.restrict (Ioo (-π) π)) :=
    memLp_finsetSum A fun i hi => (hv i hi).const_smul (w i)
  have hB : ∀ b, ∑ n ∈ s, ‖∑ i ∈ A, ((w i : ℝ) : ℂ) * modeVec m n (v i) r z b‖ ^ 2 ≤
      (1 / (2 * π)) * ∫ θ in Ioo (-π) π,
        ‖((frameVec θ (∑ i ∈ A, w i • v i (cylPoint r θ z)) b : ℝ) : ℂ)‖ ^ 2 := by
    intro b
    rw [Finset.sum_congr rfl fun n _ => by rw [lin_mode m n A w v r z b hv]]
    exact coef_sq_le_circ hm s (frame_memLp hUm b)
  have hsum : ∑ b : Fin 3, ∫ θ in Ioo (-π) π,
      ‖((frameVec θ (∑ i ∈ A, w i • v i (cylPoint r θ z)) b : ℝ) : ℂ)‖ ^ 2 =
      ∫ θ in Ioo (-π) π, ‖∑ i ∈ A, w i • v i (cylPoint r θ z)‖ ^ 2 := by
    rw [← integral_finsetSum _ fun b _ =>
      (memLp_two_iff_integrable_sq_norm (frame_memLp hUm b).1).1 (frame_memLp hUm b)]
    refine integral_congr_ae (ae_of_all _ fun θ => ?_)
    simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    exact frame_sq θ _
  calc ∑ n ∈ s, vecSq (fun b => ∑ i ∈ A, ((w i : ℝ) : ℂ) * modeVec m n (v i) r z b)
      = ∑ b : Fin 3, ∑ n ∈ s, ‖∑ i ∈ A, ((w i : ℝ) : ℂ) * modeVec m n (v i) r z b‖ ^ 2 := by
        unfold vecSq
        exact Finset.sum_comm
    _ ≤ ∑ b : Fin 3, (1 / (2 * π)) * ∫ θ in Ioo (-π) π,
          ‖((frameVec θ (∑ i ∈ A, w i • v i (cylPoint r θ z)) b : ℝ) : ℂ)‖ ^ 2 :=
        Finset.sum_le_sum fun b _ => hB b
    _ = _ := by rw [← Finset.mul_sum, hsum]

end Breakdown.FracInternal.ClassRowSq

namespace Breakdown.FracInternal.ClassRowSq

open SteadyCert CellCert CellCert.CellAnalysis
open CellCert.CellAnalysis.LowEntry.Internal CellCert.CellAnalysis.ModeGradSquare.Internal

theorem cyl_int {F : Space → Space} (hF : MemLp F 2 volume) :
    Integrable (fun q : (ℝ × ℝ) × ℝ => q.1.1 * ‖F (cylArg q)‖ ^ 2) muU := by
  have hm : AEStronglyMeasurable (fun q => F (cylArg q)) muU := hF.1.comp_quasiMeasurePreserving qmp
  refine ⟨(measurable_fst.fst.aestronglyMeasurable).mul (hm.norm.pow 2), ?_⟩
  unfold HasFiniteIntegral
  have hpos : ∀ᵐ q ∂muU, 0 < q.1.1 := by
    rw [muU_eq]
    exact (ae_restrict_mem ((measurableSet_Ioi.prod MeasurableSet.univ).prod measurableSet_Ioo)).mono
      fun q hq => hq.1.1
  have hi := ((memLp_two_iff_integrable_sq_norm hF.1).1 hF).2
  unfold HasFiniteIntegral at hi
  calc ∫⁻ q, ‖q.1.1 * ‖F (cylArg q)‖ ^ 2‖ₑ ∂muU
      = ∫⁻ q, ENNReal.ofReal q.1.1 * ‖F (cylArg q)‖ₑ ^ 2 ∂muU := by
        refine lintegral_congr_ae (hpos.mono fun q hq => ?_)
        dsimp only
        rw [enorm_mul, enorm_pow, enorm_norm, Real.enorm_eq_ofReal hq.le]
    _ = ∫⁻ y, ‖F y‖ₑ ^ 2 := key (fun y => ‖F y‖ₑ ^ 2)
    _ < ⊤ := by simpa only [enorm_pow, enorm_norm] using hi

theorem circ_memLp {F : Space → Space} (hF : MemLp F 2 volume) :
    ∀ᵐ p ∂(volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))),
      MemLp (fun θ => F (cylPoint p.1 θ p.2)) 2 (volume.restrict (Ioo (-π) π)) := by
  have hi := cyl_int hF
  rw [muU_def] at hi
  have hm : AEStronglyMeasurable (fun q => F (cylArg q))
      ((volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))).prod (volume.restrict (Ioo (-π) π))) := by
    rw [← muU_def]
    exact hF.1.comp_quasiMeasurePreserving qmp
  filter_upwards [hi.prod_right_ae, hm.prodMk_left,
    ae_restrict_mem (measurableSet_Ioi.prod MeasurableSet.univ)] with p h1 h2 h3
  have hp : 0 < p.1 := h3.1
  refine (memLp_two_iff_integrable_sq_norm h2).2 ?_
  refine (h1.const_mul p.1⁻¹).congr (ae_of_all _ fun θ => ?_)
  simp only [cylArg]
  field_simp

theorem circ_integrable {K : CellBox} (hK : IsCellBox K) {F : Space → Space} (hF : MemLp F 2 volume) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 * ∫ θ in Ioo (-π) π, ‖F (cylPoint p.1 θ p.2)‖ ^ 2) K.rect := by
  have hi := cyl_int hF
  rw [muU_def] at hi
  have h : Integrable (fun p : ℝ × ℝ => ∫ θ in Ioo (-π) π, p.1 * ‖F (cylPoint p.1 θ p.2)‖ ^ 2)
      (volume.restrict (Ioi (0 : ℝ) ×ˢ (univ : Set ℝ))) := hi.integral_prod_left
  refine (h.mono_measure (hle K hK)).congr (ae_of_all _ fun p => ?_)
  exact integral_const_mul _ _

theorem mv_meas (K : CellBox) (hK : IsCellBox K) (m : ℕ) (n : ℤ) {v : Space → Space}
    (hv : AEStronglyMeasurable v volume) (b : Fin 3) :
    AEStronglyMeasurable (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 b) (volume.restrict K.rect) := by
  have hF := meas_gen hv (velKernel m n b) (velKernel_cont m n b)
  have e : (fun p : ℝ × ℝ => modeVec m n v p.1 p.2 b) = fun p =>
      (1 / (2 * π) : ℂ) * ∫ θ in Ioo (-π) π, velKernel m n b θ (v (cylPoint p.1 θ p.2)) :=
    funext fun p => modeVec_eq m n v b p
  rw [e]
  exact (hF.mono_measure (hle K hK)).const_mul _

theorem inner_int {u v : Space → Space} (hu : MemLp u 2 volume) (hv : MemLp v 2 volume) :
    Integrable (fun y => inner ℝ (u y) (v y)) := by
  have h1 := (memLp_two_iff_integrable_sq_norm hu.1).1 hu
  have h2 := (memLp_two_iff_integrable_sq_norm hv.1).1 hv
  refine (h1.add h2).mono' (hu.1.inner hv.1) (ae_of_all _ fun y => ?_)
  show ‖inner ℝ (u y) (v y)‖ ≤ ‖u y‖ ^ 2 + ‖v y‖ ^ 2
  rw [Real.norm_eq_abs]
  have := abs_real_inner_le_norm (u y) (v y)
  nlinarith [sq_nonneg (‖u y‖ - ‖v y‖), norm_nonneg (u y), norm_nonneg (v y)]

end Breakdown.FracInternal.ClassRowSq

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly
open Breakdown.FracInternal.ClassRowSq LowEntry.Internal ModeGradSquare.Internal

theorem classRowSq_holds : ClassRowSqStatement := by
  intro α _ _ k N c hc K S B Cl slots R hD _ μ i
  have hK := hD.box
  set A := R.rowSet.filter (fun a => R.rowModeOf a ∈ Cl.resolvedPart i) with hA
  set G : Space → Space := fun y => ∑ a ∈ A, μ a • c.row a y with hG
  have hm : 1 ≤ c.order := by
    obtain ⟨n, hn⟩ := Infinite.exists_notMem_finset S.resolved
    have h3 := hD.scalars.unresolved_large n hn
    by_contra h0
    have h00 : c.order = 0 := by omega
    have hz : modeNumber c.order n = 0 := by simp [modeNumber, azimuth, h00]
    linarith
  have hrow2 : ∀ a, MemLp (c.row a) 2 volume := hc.base.row_two
  have hG2 : MemLp G 2 volume := memLp_finsetSum A fun a _ => (hrow2 a).const_smul (μ a)
  have hGi : Integrable (fun y => ‖G y‖ ^ 2) := (memLp_two_iff_integrable_sq_norm hG2.1).1 hG2
  have hcirc : ∀ᵐ p ∂(volume.restrict K.rect), ∀ a,
      MemLp (fun θ => c.row a (cylPoint p.1 θ p.2)) 2 (volume.restrict (Ioo (-π) π)) :=
    ae_mono (hle K hK) (ae_all_iff.2 fun a => circ_memLp (hrow2 a))
  have hle' : ∀ᵐ p ∂(volume.restrict K.rect), p.1 * CellScalars.classRowSq c R Cl μ i p ≤
      (1 / (2 * π)) * (p.1 * ∫ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ ^ 2) := by
    filter_upwards [hcirc, ae_restrict_mem (FracInternal.CellDensityModesSolid.rect_meas K)] with p hp hpK
    have h0 : 0 ≤ p.1 := le_trans hK.r_order.1 hpK.1.1
    have hb := point_bound hm R.rowModes A μ (fun a => c.row a) p.1 p.2 (fun a _ => hp a)
    have hb' : CellScalars.classRowSq c R Cl μ i p ≤
        (1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ ^ 2 := hb
    calc p.1 * CellScalars.classRowSq c R Cl μ i p
        ≤ p.1 * ((1 / (2 * π)) * ∫ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hb' h0
      _ = _ := by ring
  have hnn : ∀ᵐ p ∂(volume.restrict K.rect), 0 ≤ p.1 * CellScalars.classRowSq c R Cl μ i p := by
    filter_upwards [ae_restrict_mem (FracInternal.CellDensityModesSolid.rect_meas K)] with p hpK
    refine mul_nonneg (le_trans hK.r_order.1 hpK.1.1) ?_
    unfold CellScalars.classRowSq vecSq
    positivity
  have hT := (circ_integrable hK hG2).const_mul (1 / (2 * π))
  have hLm : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1 * CellScalars.classRowSq c R Cl μ i p)
      (volume.restrict K.rect) := by
    refine continuous_fst.aestronglyMeasurable.mul ?_
    unfold CellScalars.classRowSq vecSq CellScalars.rowMode
    refine R.rowModes.aestronglyMeasurable_fun_sum fun m _ => ?_
    refine Finset.univ.aestronglyMeasurable_fun_sum fun b _ => ?_
    refine (A.aestronglyMeasurable_fun_sum fun a _ => ?_).norm.pow 2
    exact aestronglyMeasurable_const.mul (mv_meas K hK c.order m (hrow2 a).1 b)
  have hLi : IntegrableOn (fun p : ℝ × ℝ => p.1 * CellScalars.classRowSq c R Cl μ i p) K.rect := by
    refine hT.mono' hLm ?_
    filter_upwards [hle', hnn] with p h1 h2
    rw [Real.norm_eq_abs, abs_of_nonneg h2]
    exact h1
  refine ⟨hLi, ?_⟩
  have hsupp : ∀ y ∉ K.solid, G y = 0 := by
    intro y hy
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hD.rows_in_cell a (Finset.mem_filter.1 ha).1 y hy, smul_zero]
  have hmir : ∀ᵐ y ∂volume, y ∈ K.solid → ‖G (mirror y)‖ ^ 2 = ‖G y‖ ^ 2 := by
    filter_upwards [ae_all_iff.2 fun a => (hc.base.row_class a).2] with y hy _
    have e : G (mirror y) = LinearSolveCore.mirrorIsometry (G y) := by
      simp only [hG, map_sum, map_smul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hy a]
      rfl
    rw [e, LinearIsometryEquiv.norm_map]
  have hsf := FracInternal.CellDensityModesSolid.solid_formula K hK (fun y => ‖G y‖ ^ 2) hGi.integrableOn hmir
  have hper : ∀ p : ℝ × ℝ, ∫ θ in (0 : ℝ)..(2 * π), ‖G (cylPoint p.1 θ p.2)‖ ^ 2 =
      ∫ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ ^ 2 :=
    fun p => per_real _ (fun θ => by simp only [cylPoint_per])
  simp only [hper] at hsf
  have hall : ∫ y in K.solid, ‖G y‖ ^ 2 = ∫ y, ‖G y‖ ^ 2 := by
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy => ?_
    rw [hsupp y hy, norm_zero]
    ring
  have hval : ∫ y, ‖G y‖ ^ 2 = ∑ a ∈ A, μ a ^ 2 := by
    have hpt : ∀ y, ‖G y‖ ^ 2 = ∑ a ∈ A, ∑ b ∈ A, μ a * μ b * inner ℝ (c.row a y) (c.row b y) := by
      intro y
      rw [← real_inner_self_eq_norm_sq]
      simp only [hG, sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      ring
    simp_rw [hpt]
    rw [integral_finsetSum A fun a _ => integrable_finsetSum A fun b _ =>
      (inner_int (hrow2 a) (hrow2 b)).const_mul _]
    refine Finset.sum_congr rfl fun a ha => ?_
    rw [integral_finsetSum A fun b _ => (inner_int (hrow2 a) (hrow2 b)).const_mul _]
    have hz : ∀ b ∈ A, ∫ y, μ a * μ b * inner ℝ (c.row a y) (c.row b y) = if a = b then μ a ^ 2 else 0 := by
      intro b _
      rw [integral_const_mul]
      have ho := hc.base.row_orthonormal a b
      unfold l2Pair at ho
      rw [ho]
      split_ifs with hab
      · subst hab; ring
      · ring
    rw [Finset.sum_congr rfl hz, Finset.sum_ite_eq A a (fun _ => μ a ^ 2), if_pos ha]
  calc ∫ p in K.rect, p.1 * CellScalars.classRowSq c R Cl μ i p
      ≤ ∫ p in K.rect, (1 / (2 * π)) * (p.1 * ∫ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ ^ 2) :=
        integral_mono_ae hLi hT hle'
    _ = (1 / (2 * π)) * ∫ p in K.rect, p.1 * ∫ θ in Ioo (-π) π, ‖G (cylPoint p.1 θ p.2)‖ ^ 2 :=
        integral_const_mul _ _
    _ = (1 / (2 * π)) * ((1 / 2) * ∑ a ∈ A, μ a ^ 2) := by
        rw [← hval, ← hall, hsf]
        ring
    _ = ∑ a ∈ A, μ a ^ 2 / (4 * π) := by
        rw [← Finset.sum_div]
        field_simp
        ring

end Breakdown.CellCert.CellAnalysis
