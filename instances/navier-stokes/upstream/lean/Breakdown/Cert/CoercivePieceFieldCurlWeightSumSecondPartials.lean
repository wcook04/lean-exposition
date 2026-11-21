import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveModeRotation
import Breakdown.Cert.CoerciveRotation
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal Topology
open MeasureTheory Filter

noncomputable section

namespace Breakdown

namespace Coercive

namespace CurlWeight.Internal.SumSecondPartialsModes

theorem reVec_coord (x : Fin 3 → ℂ) (i : Fin 3) : reVec x i = (x i).re := by
  fin_cases i <;> simp [reVec, unitVector, Fin.sum_univ_three]

theorem imVec_coord (x : Fin 3 → ℂ) (i : Fin 3) : imVec x i = (x i).im := by
  fin_cases i <;> simp [imVec, unitVector, Fin.sum_univ_three]

theorem reMat_coord (g : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) : reMat g (unitVector j) i = (g (i, j)).re := by
  fin_cases i <;> fin_cases j <;> simp [reMat, unitVector, Fin.sum_univ_three, EuclideanSpace.inner_single_left]

theorem imMat_coord (g : Fin 3 × Fin 3 → ℂ) (i j : Fin 3) : imMat g (unitVector j) i = (g (i, j)).im := by
  fin_cases i <;> fin_cases j <;> simp [imMat, unitVector, Fin.sum_univ_three, EuclideanSpace.inner_single_left]

theorem locInt_coord {f : Space → Space} (hf : LocallyIntegrable f volume) (n : Fin 3) :
    LocallyIntegrable (fun y => f y n) volume :=
  locallyIntegrable_iff.2 fun K hK =>
    (EuclideanSpace.proj (𝕜 := ℝ) n).integrable_comp (locallyIntegrable_iff.1 hf K hK)

theorem locInt_apply {g : Space → (Space →L[ℝ] Space)} (hg : LocallyIntegrable g volume) (u : Space)
    (n : Fin 3) : LocallyIntegrable (fun y => g y u n) volume :=
  locallyIntegrable_iff.2 fun K hK =>
    (EuclideanSpace.proj (𝕜 := ℝ) n).integrable_comp
      ((locallyIntegrable_iff.1 hg K hK).apply_continuousLinearMap u)

theorem coord_weak {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient f g)
    {φ : Space → ℝ} (hφ : IsTestFunction φ) (a n : Fin 3) :
    ∫ y, φ y * g y (unitVector a) n = -∫ y, fderiv ℝ φ y (unitVector a) * f y n := by
  have hL : Integrable (fun y => φ y • g y (unitVector a)) volume :=
    (h.2.1.integrable_smul_left_of_hasCompactSupport hφ.1.continuous hφ.2).apply_continuousLinearMap
      (unitVector a)
  have hR : Integrable (fun y => fderiv ℝ φ y (unitVector a) • f y) volume :=
    h.1.integrable_smul_left_of_hasCompactSupport
      ((hφ.1.continuous_fderiv (by simp)).clm_apply continuous_const) (hφ.2.fderiv_apply (𝕜 := ℝ) _)
  have e := congrArg (fun w : Space => w n) (h.2.2 φ hφ a)
  have c1 : (∫ y, φ y • g y (unitVector a)) n = ∫ y, φ y * g y (unitVector a) n := by
    simpa using ((EuclideanSpace.proj (𝕜 := ℝ) n).integral_comp_comm hL).symm
  have c2 : (∫ y, fderiv ℝ φ y (unitVector a) • f y) n = ∫ y, fderiv ℝ φ y (unitVector a) * f y n := by
    simpa using ((EuclideanSpace.proj (𝕜 := ℝ) n).integral_comp_comm hR).symm
  simp only at e
  rw [← c1, ← c2, e, PiLp.neg_apply]

theorem test_fderiv {φ : Space → ℝ} (hφ : IsTestFunction φ) (a : Fin 3) :
    IsTestFunction (fun y => fderiv ℝ φ y (unitVector a)) :=
  ⟨(hφ.1.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).clm_apply contDiff_const,
    hφ.2.fderiv_apply (𝕜 := ℝ) _⟩

theorem fderiv_fderiv_symm {φ : Space → ℝ} (hφ : ContDiff ℝ ∞ φ) (a b : Fin 3) (y : Space) :
    fderiv ℝ (fun x => fderiv ℝ φ x (unitVector a)) y (unitVector b) =
      fderiv ℝ (fun x => fderiv ℝ φ x (unitVector b)) y (unitVector a) := by
  have hd : Differentiable ℝ (fderiv ℝ φ) :=
    (hφ.fderiv_right (m := ∞) (by exact_mod_cast le_rfl)).differentiable (by simp)
  have e : ∀ c : Fin 3, fderiv ℝ (fun x => fderiv ℝ φ x (unitVector c)) y =
      (fderiv ℝ (fderiv ℝ φ) y).flip (unitVector c) := by
    intro c
    rw [fderiv_clm_apply (hd y) (differentiableAt_const _)]
    simp
  rw [e a, e b, ContinuousLinearMap.flip_apply, ContinuousLinearMap.flip_apply]
  exact (((contDiff_infty.1 hφ 2).contDiffAt (x := y)).isSymmSndFDerivAt (by simp)) _ _

theorem ae_symm {u : Fin 3 → Space → ℝ} {g : Fin 3 → Fin 3 → Space → ℝ}
    {h : Fin 3 → Fin 3 → Fin 3 → Space → ℝ}
    (hh : ∀ n a b, LocallyIntegrable (h n a b) volume)
    (F1 : ∀ φ, IsTestFunction φ → ∀ a n, ∫ y, φ y * g n a y = -∫ y, fderiv ℝ φ y (unitVector a) * u n y)
    (F2 : ∀ φ, IsTestFunction φ → ∀ a b n,
      ∫ y, φ y * h n a b y = -∫ y, fderiv ℝ φ y (unitVector a) * g n b y)
    (n a b : Fin 3) : ∀ᵐ y, h n a b y = h n b a y := by
  have hd : LocallyIntegrable (fun y => h n a b y - h n b a y) volume := (hh n a b).sub (hh n b a)
  have key := ae_eq_zero_of_integral_contDiff_smul_eq_zero hd (fun φ hφ hc => ?_)
  · filter_upwards [key] with y hy
    exact sub_eq_zero.1 hy
  · have ht : IsTestFunction φ := ⟨hφ, hc⟩
    have i1 : Integrable (fun y => φ y * h n a b y) volume := by
      simpa [smul_eq_mul] using (hh n a b).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
    have i2 : Integrable (fun y => φ y * h n b a y) volume := by
      simpa [smul_eq_mul] using (hh n b a).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
    show ∫ y, φ y • (h n a b y - h n b a y) = 0
    simp only [smul_eq_mul, mul_sub]
    rw [integral_sub i1 i2, F2 φ ht a b n, F2 φ ht b a n]
    have e1 := F1 _ (test_fderiv ht a) b n
    have e2 := F1 _ (test_fderiv ht b) a n
    rw [e1, e2]
    simp only [fderiv_fderiv_symm ht.1 a b]
    ring

theorem ae_trace {g : Fin 3 → Fin 3 → Space → ℝ}
    {h : Fin 3 → Fin 3 → Fin 3 → Space → ℝ}
    (hg : ∀ n b, LocallyIntegrable (g n b) volume)
    (hh : ∀ n a b, LocallyIntegrable (h n a b) volume)
    (F2 : ∀ φ, IsTestFunction φ → ∀ a b n,
      ∫ y, φ y * h n a b y = -∫ y, fderiv ℝ φ y (unitVector a) * g n b y)
    (hdiv : ∀ᵐ y, ∑ j : Fin 3, g j j y = 0) (l : Fin 3) : ∀ᵐ y, ∑ j : Fin 3, h j l j y = 0 := by
  have hd : LocallyIntegrable (fun y => ∑ j : Fin 3, h j l j y) volume := by
    simpa using locallyIntegrable_finsetSum Finset.univ (fun j _ => hh j l j)
  refine ae_eq_zero_of_integral_contDiff_smul_eq_zero hd (fun φ hφ hc => ?_)
  have ht : IsTestFunction φ := ⟨hφ, hc⟩
  have i1 : ∀ j : Fin 3, Integrable (fun y => φ y * h j l j y) volume := fun j => by
    simpa [smul_eq_mul] using (hh j l j).integrable_smul_left_of_hasCompactSupport hφ.continuous hc
  have hcd : Continuous (fun y => fderiv ℝ φ y (unitVector l)) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have i2 : ∀ j : Fin 3, Integrable (fun y => fderiv ℝ φ y (unitVector l) * g j j y) volume := fun j => by
    simpa [smul_eq_mul] using (hg j j).integrable_smul_left_of_hasCompactSupport hcd
      (hc.fderiv_apply (𝕜 := ℝ) _)
  simp only [smul_eq_mul, Finset.mul_sum]
  rw [integral_finsetSum _ (fun j _ => i1 j)]
  rw [Finset.sum_congr rfl fun j _ => F2 φ ht l j j]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun j _ => i2 j)]
  have h0 : (fun y => ∑ j : Fin 3, fderiv ℝ φ y (unitVector l) * g j j y) =ᵐ[volume] fun _ => (0 : ℝ) := by
    filter_upwards [hdiv] with y hy
    rw [← Finset.mul_sum, hy, mul_zero]
  rw [integral_congr_ae h0]
  simp

theorem sum_rot_diag (φ : ℝ) (B : Space →L[ℝ] Space →L[ℝ] Space) (l : Fin 3) :
    ∑ j : Fin 3, axialRot (-φ) (B (axialRot φ (unitVector j)) (axialRot φ (unitVector j))) l =
      axialRot (-φ) (secondDerivTrace B) l := by
  have e0 : axialRot φ (unitVector 0) = Real.cos φ • unitVector 0 + Real.sin φ • unitVector 1 := by
    ext i; fin_cases i <;> simp [axialRot, unitVector]
  have e1 : axialRot φ (unitVector 1) = (-Real.sin φ) • unitVector 0 + Real.cos φ • unitVector 1 := by
    ext i; fin_cases i <;> simp [axialRot, unitVector]
  have e2 : axialRot φ (unitVector 2) = unitVector 2 := by
    ext i; fin_cases i <;> simp [axialRot, unitVector]
  have h := Real.sin_sq_add_cos_sq φ
  rw [Fin.sum_univ_three, e0, e1, e2]
  unfold secondDerivTrace
  rw [Fin.sum_univ_three]
  simp only [map_add, map_smul, FunLike.coe_add, Pi.add_apply, FunLike.coe_smul,
    Pi.smul_apply]
  generalize B (unitVector 0) (unitVector 0) = B00
  generalize B (unitVector 0) (unitVector 1) = B01
  generalize B (unitVector 1) (unitVector 0) = B10
  generalize B (unitVector 1) (unitVector 1) = B11
  generalize B (unitVector 2) (unitVector 2) = B22
  fin_cases l <;> simp [axialRot, unitVector, Real.cos_neg, Real.sin_neg] <;> ring_nf
  · linear_combination (Real.cos φ * (B00 0 + B11 0) + Real.sin φ * (B00 1 + B11 1)) * h
  · linear_combination (-Real.sin φ * (B00 0 + B11 0) + Real.cos φ * (B00 1 + B11 1)) * h
  · linear_combination (B00 2 + B11 2) * h

theorem continuous_rot_comp {X : Type*} [TopologicalSpace X] {a : X → ℝ} {w : X → Space}
    (ha : Continuous a) (hw : Continuous w) : Continuous (fun x => axialRot (a x) (w x)) := by
  have c0 : Continuous (fun x => w x 0) := (EuclideanSpace.proj 0 : Space →L[ℝ] ℝ).continuous.comp hw
  have c1 : Continuous (fun x => w x 1) := (EuclideanSpace.proj 1 : Space →L[ℝ] ℝ).continuous.comp hw
  have c2 : Continuous (fun x => w x 2) := (EuclideanSpace.proj 2 : Space →L[ℝ] ℝ).continuous.comp hw
  have cc : Continuous (fun x => Real.cos (a x)) := Real.continuous_cos.comp ha
  have cs : Continuous (fun x => Real.sin (a x)) := Real.continuous_sin.comp ha
  have e1 : Continuous (fun x => (Real.cos (a x) * w x 0 - Real.sin (a x) * w x 1) • unitVector 0) :=
    ((cc.mul c0).sub (cs.mul c1)).smul continuous_const
  have e2 : Continuous (fun x => (Real.sin (a x) * w x 0 + Real.cos (a x) * w x 1) • unitVector 1) :=
    ((cs.mul c0).add (cc.mul c1)).smul continuous_const
  have e3 : Continuous (fun x => w x 2 • unitVector 2) := c2.smul continuous_const
  unfold axialRot
  exact (e1.add e2).add e3

theorem integrable_secondDerivDiag {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => H (z.1 + p.1) (axialRot p.2 z.2)) Internal.ModeRotation.boxMeasure)
    (l j : Fin 3) :
    Integrable (fun p : ℝ × ℝ => axialRot (-p.2) (H (z.1 + p.1) (axialRot p.2 z.2)
      (axialRot p.2 (unitVector j)) (axialRot p.2 (unitVector j))) l) Internal.ModeRotation.boxMeasure := by
  refine hz.norm.mono' ?_ (Eventually.of_forall fun p => ?_)
  · have hr : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot q.1.2 (unitVector j)) :=
      continuous_rot_comp (continuous_snd.comp continuous_fst) continuous_const
    have hb : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space →L[ℝ] Space) =>
        q.2 (axialRot q.1.2 (unitVector j)) (axialRot q.1.2 (unitVector j))) :=
      (continuous_snd.clm_apply hr).clm_apply hr
    have hc : Continuous (fun q : (ℝ × ℝ) × (Space →L[ℝ] Space →L[ℝ] Space) =>
        axialRot (-q.1.2) (q.2 (axialRot q.1.2 (unitVector j)) (axialRot q.1.2 (unitVector j))) l) :=
      (PiLp.continuous_apply 2 _ l).comp (continuous_rot_comp (continuous_snd.comp continuous_fst).neg hb)
    have hm : AEStronglyMeasurable (fun p : ℝ × ℝ => (p, H (z.1 + p.1) (axialRot p.2 z.2)))
        Internal.ModeRotation.boxMeasure := aestronglyMeasurable_id.prodMk hz.1
    have h2 := hc.comp_aestronglyMeasurable hm
    exact h2
  · refine (PiLp.norm_apply_le _ l).trans ?_
    rw [RotationInternal.axialRot_norm]
    refine ((H (z.1 + p.1) (axialRot p.2 z.2)).le_opNorm₂ _ _).trans ?_
    rw [RotationInternal.axialRot_norm, unitVector, PiLp.norm_single, norm_one, mul_one, mul_one]

theorem modeSecondDeriv_trace_eq {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} (ι : ℤ × ℤ) {z : ℝ × Space}
    (hz : Integrable (fun p : ℝ × ℝ => H (z.1 + p.1) (axialRot p.2 z.2)) Internal.ModeRotation.boxMeasure)
    (l : Fin 3) :
    ∑ j : Fin 3, modeSecondDeriv ι H z.1 z.2 (l, j, j) =
      modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2 l := by
  have e := Internal.ModeRotation.modeAverage_sum ι (fun _ : Fin 3 => (1 : ℝ))
    (fun j τ φ => axialRot (-φ) (H (z.1 + τ) (axialRot φ z.2) (axialRot φ (unitVector j))
      (axialRot φ (unitVector j))) l)
    (fun j => integrable_secondDerivDiag hz l j)
  have hR : modeVel ι (fun σ y => secondDerivTrace (H σ y)) z.1 z.2 l =
      (1 / (2 * Real.pi) : ℂ) * ∫ τ in (0 : ℝ)..1, ∫ φ in (0 : ℝ)..(2 * Real.pi),
        Internal.ModeRotation.expFactor ι τ φ * ((∑ j : Fin 3, (1 : ℝ) * axialRot (-φ) (H (z.1 + τ)
          (axialRot φ z.2) (axialRot φ (unitVector j)) (axialRot φ (unitVector j))) l : ℝ) : ℂ) := by
    unfold modeVel
    rw [Internal.ModeRotation.modeAverage_eq]
    simp only [one_mul, sum_rot_diag]
  rw [hR, e]
  unfold modeSecondDeriv
  simp only [Internal.ModeRotation.modeAverage_eq, Complex.ofReal_one, one_mul]
  rw [Finset.mul_sum]

theorem real_parts {u : Space → Space} {Du : Space → (Space →L[ℝ] Space)} {c : Fin 3 → Space → Space}
    {Dc : Fin 3 → Space → (Space →L[ℝ] Space)} (h1 : IsWeakGradient u Du)
    (h2 : ∀ b, IsWeakGradient (c b) (Dc b)) (hcol : ∀ b y n, c b y n = Du y (unitVector b) n)
    (hdiv : ∀ᵐ y, ∑ j : Fin 3, Du y (unitVector j) j = 0) :
    (∀ᵐ y, ∀ n a b : Fin 3, Dc b y (unitVector a) n = Dc a y (unitVector b) n) ∧
      ∀ᵐ y, ∀ l : Fin 3, ∑ j : Fin 3, Dc j y (unitVector l) j = 0 := by
  have hh : ∀ n a b : Fin 3, LocallyIntegrable (fun y => Dc b y (unitVector a) n) volume :=
    fun n a b => locInt_apply (h2 b).2.1 _ n
  have hg : ∀ n b : Fin 3, LocallyIntegrable (fun y => Du y (unitVector b) n) volume :=
    fun n b => locInt_apply h1.2.1 _ n
  have F1 : ∀ φ, IsTestFunction φ → ∀ a n : Fin 3,
      ∫ y, φ y * Du y (unitVector a) n = -∫ y, fderiv ℝ φ y (unitVector a) * u y n :=
    fun φ hφ a n => coord_weak h1 hφ a n
  have F2 : ∀ φ, IsTestFunction φ → ∀ a b n : Fin 3,
      ∫ y, φ y * Dc b y (unitVector a) n = -∫ y, fderiv ℝ φ y (unitVector a) * Du y (unitVector b) n := by
    intro φ hφ a b n
    rw [coord_weak (h2 b) hφ a n]
    simp only [hcol]
  refine ⟨?_, ?_⟩
  · refine ae_all_iff.2 fun n => ae_all_iff.2 fun a => ae_all_iff.2 fun b => ?_
    exact ae_symm (u := fun n y => u y n) (g := fun n b y => Du y (unitVector b) n)
      (h := fun n a b y => Dc b y (unitVector a) n) hh F1 F2 n a b
  · refine ae_all_iff.2 fun l => ?_
    exact ae_trace (g := fun n b y => Du y (unitVector b) n)
      (h := fun n a b y => Dc b y (unitVector a) n) hg hh F2 hdiv l

theorem contraction_eq (h : Fin 3 × Fin 3 × Fin 3 → ℂ) (w : Fin 3 → ℂ)
    (S : ∀ n a b, h (n, a, b) = h (n, b, a)) (T0 : ∀ l, ∑ j : Fin 3, h (j, l, j) = 0)
    (T1 : ∀ l, ∑ j : Fin 3, h (l, j, j) = w l) (l : Fin 3) :
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 3, ∑ n : Fin 3,
      (alternatingSymbol i j l : ℂ) * (alternatingSymbol i m n : ℂ) * h (n, j, m) = w l := by
  have t1 := T1 l
  have t0 := T0 l
  have s0 := S 0 0 l
  have s1 := S 1 1 l
  have s2 := S 2 2 l
  simp only [Fin.sum_univ_three] at t1 t0 ⊢
  fin_cases l <;> simp [alternatingSymbol] at t1 t0 s0 s1 s2 ⊢ <;> linear_combination t1 - t0 - s0 - s1 - s2

end CurlWeight.Internal.SumSecondPartialsModes

open CurlWeight.Internal.SumSecondPartialsModes in
theorem CurlWeight.Internal.ae_modeSlice_sumSecondPartials (hD : ModeDerivativeHolds) {Γ : Set Symmetry} {P : ℝ}
    {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) (ι : ℤ × ℤ) :
    ∀ᵐ σ, ∀ᵐ y, ∀ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, ∑ m : Fin 3, ∑ n : Fin 3,
      (alternatingSymbol i j l : ℂ) * (alternatingSymbol i m n : ℂ) * modeSecondDeriv ι H σ y (n, j, m)
        = modeVel ι (fun σ y => secondDerivTrace (H σ y)) σ y l := by
  obtain ⟨c1, c2, c3⟩ := hD Γ P v G H g hv ι
  obtain ⟨-, -, hlH⟩ := perturbationLocalIntegrabilityHolds_proof Γ P v G H g hv
  have horb := Internal.ModeRotation.ae_integrable_orbit axialRotationHolds_proof hlH
  have horb' : ∀ᵐ σ, ∀ᵐ y, Integrable (fun p : ℝ × ℝ => H (σ + p.1) (axialRot p.2 y))
      Internal.ModeRotation.boxMeasure :=
    Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) horb
  have c3' : ∀ᵐ σ, ∀ᵐ y, ∑ i : Fin 3, modeGrad ι G σ y (i, i) = 0 :=
    Measure.ae_ae_of_ae_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure Space)) c3
  filter_upwards [c1, c2, c3', horb'] with σ h1 h2 h3 h4
  have hre := real_parts h1.1 (fun b => (h2 b).1)
    (fun b y n => by rw [reVec_coord, reMat_coord])
    (by
      filter_upwards [h3] with y hy
      simp only [reMat_coord]
      rw [← Complex.re_sum, hy, Complex.zero_re])
  have him := real_parts h1.2 (fun b => (h2 b).2)
    (fun b y n => by rw [imVec_coord, imMat_coord])
    (by
      filter_upwards [h3] with y hy
      simp only [imMat_coord]
      rw [← Complex.im_sum, hy, Complex.zero_im])
  filter_upwards [hre.1, hre.2, him.1, him.2, h4] with y r1 r2 i1 i2 hy
  refine contraction_eq (modeSecondDeriv ι H σ y) _ ?_ ?_ (fun l => modeSecondDeriv_trace_eq ι (z := (σ, y)) hy l)
  · intro n a b
    have e1 := r1 n a b
    have e2 := i1 n a b
    simp only [reMat_coord, imMat_coord] at e1 e2
    exact Complex.ext e1 e2
  · intro l
    have e1 := r2 l
    have e2 := i2 l
    simp only [reMat_coord, imMat_coord] at e1 e2
    exact Complex.ext (by rw [Complex.re_sum, e1, Complex.zero_re])
      (by rw [Complex.im_sum, e2, Complex.zero_im])

end Coercive

end Breakdown
