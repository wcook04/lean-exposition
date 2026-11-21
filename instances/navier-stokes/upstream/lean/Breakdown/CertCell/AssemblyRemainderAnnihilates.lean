import Breakdown.CertCell.AssemblyStatements
import Breakdown.Cert.CoercivePerturbationFactsProof
import Breakdown.Cert.CoerciveFrequencySeminormTransportModes
import Breakdown.FracCell.AdjointConvectionPairingParts

open MeasureTheory
open scoped ContDiff

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCalculus

namespace Internal.RemainderAnnihilates

theorem vec_coord (x : Space) : x = ∑ j : Fin 3, x j • unitVector j := by
  ext i
  simp [unitVector, Fin.sum_univ_three]
  fin_cases i <;> simp

theorem sum_unit_coord (c : Fin 3 → ℝ) (i : Fin 3) : (∑ j : Fin 3, c j • unitVector j) i = c i := by
  fin_cases i <;> simp [unitVector, Fin.sum_univ_three]

theorem clm_coord (M : Space →L[ℝ] Space) (x : Space) (i : Fin 3) :
    M x i = ∑ j : Fin 3, x j * M (unitVector j) i := by
  conv_lhs => rw [vec_coord x]
  simp [map_sum, map_smul]

theorem inner_coord (x y : Space) : inner ℝ x y = ∑ i : Fin 3, x i * y i := by
  simp [PiLp.inner_apply, mul_comm]

theorem cross_identity (M : Space →L[ℝ] Space) (x ψ : Space) :
    inner ℝ (M x - crossVec (curlVec M) x) ψ =
      ∑ l : Fin 3, ∑ i : Fin 3, M (unitVector i) l * x l * ψ i := by
  rw [inner_coord]
  simp only [PiLp.sub_apply, clm_coord M x, crossVec, curlVec, sum_unit_coord]
  simp only [Fin.sum_univ_three, alternatingSymbol]
  norm_num
  ring

theorem continuous_apply_coord (m : Fin 3) : Continuous (fun x : Space => x m) :=
  (EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous

theorem norm_unit (i : Fin 3) : ‖unitVector i‖ = 1 := by
  simp [unitVector]

theorem column_loc {g : Space → (Space →L[ℝ] Space)} (hg : LocallyIntegrable g volume) (i : Fin 3) :
    LocallyIntegrable (fun y => g y (unitVector i)) volume := by
  refine hg.mono ((ContinuousLinearMap.apply ℝ Space (unitVector i)).continuous.comp_aestronglyMeasurable
    hg.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  calc ‖g y (unitVector i)‖ ≤ ‖g y‖ * ‖unitVector i‖ := (g y).le_opNorm _
    _ = ‖g y‖ := by rw [norm_unit, mul_one]

theorem coord_loc {f : Space → Space} (hf : LocallyIntegrable f volume) (m : Fin 3) :
    LocallyIntegrable (fun y => f y m) volume := by
  refine hf.mono ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).continuous.comp_aestronglyMeasurable
    hf.aestronglyMeasurable) (Filter.Eventually.of_forall fun y => ?_)
  exact PiLp.norm_apply_le (f y) m

theorem int_mul {f c : Space → ℝ} (hf : LocallyIntegrable f volume) (hc : Continuous c)
    (hcs : HasCompactSupport c) : Integrable (fun y => f y * c y) volume := by
  simpa [smul_eq_mul, mul_comm] using hf.integrable_smul_left_of_hasCompactSupport hc hcs

theorem coord_contDiff {n : WithTop ℕ∞} {ψ : Space → Space} (hψ : ContDiff ℝ n ψ) (m : Fin 3) :
    ContDiff ℝ n (fun y => ψ y m) :=
  (EuclideanSpace.proj m : Space →L[ℝ] ℝ).contDiff.comp hψ

theorem coord_support {ψ : Space → Space} (hψ : HasCompactSupport ψ) (m : Fin 3) :
    HasCompactSupport (fun y => ψ y m) :=
  hψ.comp_left (g := fun x : Space => x m) (by simp)

theorem fderiv_coord {ψ : Space → Space} {y : Space} (hd : DifferentiableAt ℝ ψ y) (m : Fin 3) (u : Space) :
    fderiv ℝ (fun y => ψ y m) y u = fderiv ℝ ψ y u m := by
  have h := ((EuclideanSpace.proj m : Space →L[ℝ] ℝ).hasFDerivAt.comp y hd.hasFDerivAt).fderiv
  have e : (fun y => ψ y m) = (EuclideanSpace.proj m : Space →L[ℝ] ℝ) ∘ ψ := rfl
  rw [e, h]
  rfl

theorem weak_coord {f : Space → Space} {g : Space → (Space →L[ℝ] Space)} (h : IsWeakGradient f g)
    {φ : Space → ℝ} (hφ : ContDiff ℝ 1 φ) (hφc : HasCompactSupport φ) (i m : Fin 3) :
    ∫ y, φ y * g y (unitVector i) m = -∫ y, fderiv ℝ φ y (unitVector i) * f y m := by
  have hOf : SteadyCert.IsWeakGradientOf f g := fun ψ hψ j => by
    rw [h.2.2 ψ hψ j, neg_neg]
  have e := FracInternal.ConvectionPairing.weak_of_C1 h.1 i (column_loc h.2.1 i) hOf hφ hφc
  have hd : Continuous (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφ.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hdc : HasCompactSupport (fun y => fderiv ℝ φ y (unitVector i)) :=
    (hφc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector i)) rfl
  have I1 : Integrable (fun y => φ y • g y (unitVector i)) volume :=
    (column_loc h.2.1 i).integrable_smul_left_of_hasCompactSupport hφ.continuous hφc
  have I2 : Integrable (fun y => fderiv ℝ φ y (unitVector i) • f y) volume :=
    h.1.integrable_smul_left_of_hasCompactSupport hd hdc
  have c1 := (EuclideanSpace.proj m : Space →L[ℝ] ℝ).integral_comp_comm I1
  have c2 := (EuclideanSpace.proj m : Space →L[ℝ] ℝ).integral_comp_comm I2
  simp only [map_smul, smul_eq_mul] at c1 c2
  have c3 := congrArg (EuclideanSpace.proj m : Space →L[ℝ] ℝ) e
  rw [map_neg, ← c1, ← c2] at c3
  simp at c3
  linarith


theorem second_derivative_pairing {Gs : Space → (Space →L[ℝ] Space)} {Hs : Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : ∀ j : Fin 3, IsWeakGradient (fun y => Gs y (unitVector j)) (fun y => (Hs y).flip (unitVector j)))
    {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ) :
    ∫ y, (matInner (Gs y) (fderiv ℝ ψ y) + inner ℝ (secondDerivTrace (Hs y)) (ψ y)) = 0 := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hdiff : Differentiable ℝ ψ := hψ1.differentiable one_ne_zero
  have term : ∀ j m : Fin 3,
      Integrable (fun y => Gs y (unitVector j) m * fderiv ℝ (fun y => ψ y m) y (unitVector j)) volume ∧
      Integrable (fun y => Hs y (unitVector j) (unitVector j) m * ψ y m) volume ∧
      ∫ y, (Gs y (unitVector j) m * fderiv ℝ (fun y => ψ y m) y (unitVector j)
        + Hs y (unitVector j) (unitVector j) m * ψ y m) = 0 := by
    intro j m
    have hc := coord_contDiff hψ1 m
    have hcs := coord_support hψc m
    have hd : Continuous (fun y => fderiv ℝ (fun y => ψ y m) y (unitVector j)) :=
      (hc.continuous_fderiv one_ne_zero).clm_apply continuous_const
    have hdc : HasCompactSupport (fun y => fderiv ℝ (fun y => ψ y m) y (unitVector j)) :=
      (hcs.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] ℝ => L (unitVector j)) rfl
    have I1 := int_mul (coord_loc (hH j).1 m) hd hdc
    have hHl : LocallyIntegrable (fun y => Hs y (unitVector j) (unitVector j) m) volume := by
      have := coord_loc (column_loc (hH j).2.1 j) m
      simpa [ContinuousLinearMap.flip_apply] using this
    have I2 := int_mul hHl hc.continuous hcs
    refine ⟨I1, I2, ?_⟩
    rw [integral_add I1 I2]
    have e := weak_coord (hH j) hc hcs j m
    simp only [ContinuousLinearMap.flip_apply] at e
    have e2 : ∫ y, Hs y (unitVector j) (unitVector j) m * ψ y m =
        ∫ y, ψ y m * Hs y (unitVector j) (unitVector j) m := by
      congr 1; funext y; ring
    have e3 : ∫ y, Gs y (unitVector j) m * fderiv ℝ (fun y => ψ y m) y (unitVector j) =
        ∫ y, fderiv ℝ (fun y => ψ y m) y (unitVector j) * Gs y (unitVector j) m := by
      congr 1; funext y; ring
    rw [e2, e3, e]
    ring
  have pt : ∀ y, matInner (Gs y) (fderiv ℝ ψ y) + inner ℝ (secondDerivTrace (Hs y)) (ψ y) =
      ∑ j : Fin 3, ∑ m : Fin 3, (Gs y (unitVector j) m * fderiv ℝ (fun y => ψ y m) y (unitVector j)
        + Hs y (unitVector j) (unitVector j) m * ψ y m) := by
    intro y
    simp only [matInner, secondDerivTrace, inner_coord, fderiv_coord (hdiff y), Fin.sum_univ_three, PiLp.add_apply]
    ring
  have hsum : ∀ j m : Fin 3, Integrable (fun y => Gs y (unitVector j) m * fderiv ℝ (fun y => ψ y m) y (unitVector j)
      + Hs y (unitVector j) (unitVector j) m * ψ y m) volume := fun j m => (term j m).1.add (term j m).2.1
  rw [integral_congr_ae (Filter.Eventually.of_forall pt)]
  rw [integral_finsetSum _ (fun j _ => integrable_finsetSum _ (fun m _ => hsum j m))]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_finsetSum _ (fun m _ => hsum j m)]
  exact Finset.sum_eq_zero fun m _ => (term j m).2.2

theorem product_pairing {u : Space → Space} {Gs : Space → (Space →L[ℝ] Space)} (hw : IsWeakGradient u Gs)
    {w : Space → Space} (hwC : ContDiff ℝ 1 w) {ψ : Space → Space} (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ) (hdiv : ∀ y, divergenceAt ψ y = 0) :
    ∫ y, ∑ l : Fin 3, ∑ i : Fin 3, (Gs y (unitVector i) l * w y l * ψ y i
      + fderiv ℝ w y (unitVector i) l * u y l * ψ y i) = 0 := by
  have hψ1 : ContDiff ℝ 1 ψ := hψ.of_le (by simp)
  have hψd : Differentiable ℝ ψ := hψ1.differentiable one_ne_zero
  have hwd : Differentiable ℝ w := hwC.differentiable one_ne_zero
  have hwD : Continuous (fun y => fderiv ℝ w y) := hwC.continuous_fderiv one_ne_zero
  have hψD : Continuous (fun y => fderiv ℝ ψ y) := hψ1.continuous_fderiv one_ne_zero
  have term : ∀ l i : Fin 3,
      Integrable (fun y => Gs y (unitVector i) l * w y l * ψ y i
        + fderiv ℝ w y (unitVector i) l * u y l * ψ y i) volume ∧
      Integrable (fun y => u y l * (w y l * fderiv ℝ ψ y (unitVector i) i)) volume ∧
      ∫ y, (Gs y (unitVector i) l * w y l * ψ y i + fderiv ℝ w y (unitVector i) l * u y l * ψ y i) =
        -∫ y, u y l * (w y l * fderiv ℝ ψ y (unitVector i) i) := by
    intro l i
    have hwl := coord_contDiff hwC l
    have hψi := coord_contDiff hψ1 i
    have hψs := coord_support hψc i
    have hχC : ContDiff ℝ 1 (fun y => w y l * ψ y i) := hwl.mul hψi
    have hχs : HasCompactSupport (fun y => w y l * ψ y i) := hψs.mul_left
    have hχd : ∀ y, fderiv ℝ (fun y => w y l * ψ y i) y (unitVector i) =
        fderiv ℝ w y (unitVector i) l * ψ y i + w y l * fderiv ℝ ψ y (unitVector i) i := by
      intro y
      have hm : HasFDerivAt (fun y => w y l * ψ y i)
          (w y l • fderiv ℝ (fun y => ψ y i) y + ψ y i • fderiv ℝ (fun y => w y l) y) y :=
        ((hwl.differentiable one_ne_zero) y).hasFDerivAt.mul ((hψi.differentiable one_ne_zero) y).hasFDerivAt
      rw [hm.fderiv]
      simp only [add_apply, smul_apply, smul_eq_mul,
        fderiv_coord (hwd y), fderiv_coord (hψd y)]
      ring
    have e := weak_coord hw hχC hχs i l
    have cW : Continuous (fun y => fderiv ℝ w y (unitVector i) l * ψ y i) :=
      ((continuous_apply_coord l).comp (hwD.clm_apply continuous_const)).mul hψi.continuous
    have cP : Continuous (fun y => w y l * fderiv ℝ ψ y (unitVector i) i) :=
      hwl.continuous.mul ((continuous_apply_coord i).comp (hψD.clm_apply continuous_const))
    have sP : HasCompactSupport (fun y => w y l * fderiv ℝ ψ y (unitVector i) i) :=
      ((hψc.fderiv (𝕜 := ℝ)).comp_left (g := fun L : Space →L[ℝ] Space => L (unitVector i) i) (by simp)).mul_left
    have I1 : Integrable (fun y => Gs y (unitVector i) l * (w y l * ψ y i)) volume :=
      int_mul (coord_loc (column_loc hw.2.1 i) l) hχC.continuous hχs
    have I2 : Integrable (fun y => u y l * (fderiv ℝ w y (unitVector i) l * ψ y i)) volume :=
      int_mul (coord_loc hw.1 l) cW hψs.mul_left
    have I3 : Integrable (fun y => u y l * (w y l * fderiv ℝ ψ y (unitVector i) i)) volume :=
      int_mul (coord_loc hw.1 l) cP sP
    have eA : ∫ y, Gs y (unitVector i) l * (w y l * ψ y i) =
        -((∫ y, u y l * (fderiv ℝ w y (unitVector i) l * ψ y i))
          + ∫ y, u y l * (w y l * fderiv ℝ ψ y (unitVector i) i)) := by
      calc ∫ y, Gs y (unitVector i) l * (w y l * ψ y i)
          = ∫ y, (w y l * ψ y i) * Gs y (unitVector i) l := by congr 1; funext y; ring
        _ = -∫ y, fderiv ℝ (fun y => w y l * ψ y i) y (unitVector i) * u y l := e
        _ = -∫ y, (u y l * (fderiv ℝ w y (unitVector i) l * ψ y i)
              + u y l * (w y l * fderiv ℝ ψ y (unitVector i) i)) := by
            congr 2; funext y; rw [hχd y]; ring
        _ = _ := by rw [integral_add I2 I3]
    refine ⟨(I1.add I2).congr (Filter.Eventually.of_forall fun y => by simp only [Pi.add_apply]; ring), I3, ?_⟩
    calc ∫ y, (Gs y (unitVector i) l * w y l * ψ y i + fderiv ℝ w y (unitVector i) l * u y l * ψ y i)
        = ∫ y, (Gs y (unitVector i) l * (w y l * ψ y i) + u y l * (fderiv ℝ w y (unitVector i) l * ψ y i)) := by
          congr 1; funext y; ring
      _ = _ := by rw [integral_add I1 I2, eA]; ring
  rw [integral_finsetSum _ (fun l _ => integrable_finsetSum _ (fun i _ => (term l i).1))]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [integral_finsetSum _ (fun i _ => (term l i).1)]
  simp only [fun i => (term l i).2.2]
  rw [Finset.sum_neg_distrib, ← integral_finsetSum _ (fun i _ => (term l i).2.1), neg_eq_zero]
  refine integral_eq_zero_of_ae (Filter.Eventually.of_forall fun y => ?_)
  have h := hdiv y
  simp only [divergenceAt, Fin.sum_univ_three] at h
  simp only [Fin.sum_univ_three, Pi.zero_apply]
  linear_combination (u y l * w y l) * h

theorem integrable_of_local_bound {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] [T2Space X] {μ : Measure X} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {f : X → E} (hf : LocallyIntegrable f μ) {c : X → ℝ} (hc : Continuous c) (hcs : HasCompactSupport c)
    {h : X → ℝ} (hm : AEStronglyMeasurable h μ) {K : ℝ} (hK : 0 ≤ K) (hb : ∀ x, |h x| ≤ K * ‖f x‖ * c x) :
    Integrable h μ := by
  have hi := (hf.integrable_smul_left_of_hasCompactSupport hc hcs).norm.const_mul K
  refine hi.mono' hm (Filter.Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, norm_smul, Real.norm_eq_abs]
  calc |h x| ≤ K * ‖f x‖ * c x := hb x
    _ ≤ K * ‖f x‖ * |c x| := mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg hK (norm_nonneg _))
    _ = K * (|c x| * ‖f x‖) := by ring

theorem slice_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : Differentiable ℝ (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) (y : Space) :
    fderiv ℝ (f σ) y =
      (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  have h : HasFDerivAt (f σ)
      ((fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) (σ, y)).comp (ContinuousLinearMap.inr ℝ ℝ Space)) y :=
    (hf (σ, y)).hasFDerivAt.comp y (hasFDerivAt_prodMk_right σ y)
  exact h.fderiv

theorem slice_fderiv_eq {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) =
      fun z => (fderiv ℝ (fun z : ℝ × Space => f z.1 z.2) z).comp (ContinuousLinearMap.inr ℝ ℝ Space) := by
  funext z
  exact slice_fderiv (hf.differentiable one_ne_zero) z.1 z.2

theorem slice_fderiv_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) := by
  rw [slice_fderiv_eq hf]
  exact (hf.continuous_fderiv one_ne_zero).clm_comp continuous_const

theorem slice_fderiv_support {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : ℝ → Space → E}
    (hf : ContDiff ℝ 1 (fun z : ℝ × Space => f z.1 z.2)) (hs : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) :
    HasCompactSupport (fun z : ℝ × Space => fderiv ℝ (f z.1) z.2) := by
  rw [slice_fderiv_eq hf]
  exact (hs.fderiv (𝕜 := ℝ)).comp_left
    (g := fun L : ℝ × Space →L[ℝ] E => L.comp (ContinuousLinearMap.inr ℝ ℝ Space))
    (ContinuousLinearMap.zero_comp _)

theorem slice_support {E : Type*} [NormedAddCommGroup E] {f : ℝ → Space → E}
    (hs : HasCompactSupport (fun z : ℝ × Space => f z.1 z.2)) (σ : ℝ) : HasCompactSupport (f σ) := by
  refine HasCompactSupport.intro (IsCompact.image hs continuous_snd) fun y hy => ?_
  exact image_eq_zero_of_notMem_tsupport (f := fun z : ℝ × Space => f z.1 z.2) (fun h => hy ⟨(σ, y), h, rfl⟩)

theorem coord_abs_le (x : Space) (m : Fin 3) : |x m| ≤ ‖x‖ := by
  have h := PiLp.norm_apply_le x m
  rwa [Real.norm_eq_abs] at h

theorem unit_apply_le (M : Space →L[ℝ] Space) (i : Fin 3) : ‖M (unitVector i)‖ ≤ ‖M‖ :=
  (M.le_opNorm _).trans (by rw [norm_unit, mul_one])

theorem entry_abs_le (M : Space →L[ℝ] Space) (i l : Fin 3) : |M (unitVector i) l| ≤ ‖M‖ :=
  (coord_abs_le _ l).trans (unit_apply_le M i)

theorem entry_pairing_abs_le (M N : Space →L[ℝ] Space) : |matInner M N| ≤ 3 * ‖M‖ * ‖N‖ := by
  unfold matInner
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have h : ∀ i : Fin 3, |inner ℝ (M (unitVector i)) (N (unitVector i))| ≤ ‖M‖ * ‖N‖ := fun i =>
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul (unit_apply_le M i) (unit_apply_le N i) (norm_nonneg _) (norm_nonneg _))
  calc ∑ i : Fin 3, |inner ℝ (M (unitVector i)) (N (unitVector i))| ≤ ∑ _i : Fin 3, ‖M‖ * ‖N‖ :=
        Finset.sum_le_sum fun i _ => h i
    _ = 3 * ‖M‖ * ‖N‖ := by simp; ring

theorem trace_norm_le (A : Space →L[ℝ] Space →L[ℝ] Space) : ‖secondDerivTrace A‖ ≤ 3 * ‖A‖ := by
  unfold secondDerivTrace
  refine (norm_sum_le _ _).trans ?_
  have h : ∀ j : Fin 3, ‖A (unitVector j) (unitVector j)‖ ≤ ‖A‖ := fun j =>
    (A.le_opNorm₂ _ _).trans (by rw [norm_unit, mul_one, mul_one])
  calc ∑ j : Fin 3, ‖A (unitVector j) (unitVector j)‖ ≤ ∑ _j : Fin 3, ‖A‖ := Finset.sum_le_sum fun j _ => h j
    _ = 3 * ‖A‖ := by simp

theorem entry_pairing_continuous :
    Continuous (fun p : (Space →L[ℝ] Space) × (Space →L[ℝ] Space) => matInner p.1 p.2) := by
  unfold matInner
  exact continuous_finsetSum _ fun i _ =>
    (continuous_fst.clm_apply continuous_const).inner (continuous_snd.clm_apply continuous_const)

theorem trace_continuous : Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => secondDerivTrace A) := by
  unfold secondDerivTrace
  exact continuous_finsetSum _ fun j _ => (continuous_id.clm_apply continuous_const).clm_apply continuous_const

theorem entry_pairing_measurable {X : Type*} [MeasurableSpace X] {μ : Measure X} {A B : X → (Space →L[ℝ] Space)}
    (hA : AEStronglyMeasurable A μ) (hB : AEStronglyMeasurable B μ) :
    AEStronglyMeasurable (fun x => matInner (A x) (B x)) μ := by
  have h := entry_pairing_continuous.comp_aestronglyMeasurable (hA.prodMk hB)
  exact h

theorem trace_measurable {X : Type*} [MeasurableSpace X] {μ : Measure X}
    {A : X → (Space →L[ℝ] Space →L[ℝ] Space)} (hA : AEStronglyMeasurable A μ) :
    AEStronglyMeasurable (fun x => secondDerivTrace (A x)) μ := by
  have h := trace_continuous.comp_aestronglyMeasurable hA
  exact h

theorem remainder_annihilates_of {k : ℕ} {W : ℝ → Space → Space} {HW : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {B : ℝ} (hW : CoerciveWeak.IsWeakSecondDerivState W HW B) {b : Fin k → ℝ → Space → Space}
    (hb : ∀ i, LocallyIntegrable (fun z : ℝ × Space => b i z.1 z.2) volume)
    {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space}
    (hP : IsPerturbation Γ P v G H g) (κ : Fin k → ℝ) {F : ℝ → Space → Space}
    (hFm : AEStronglyMeasurable (fun z : ℝ × Space => F z.1 z.2) volume) (hFper : IsTimePeriodic F)
    (hF2 : periodLIntegral (fun σ y => ‖F σ y‖ ^ 2) < ⊤) (hRS : IsRightSide W b κ v G g F) :
    IsSpaceTimeAnnihilator (strongRemainder W b κ v G H g F) := by
  intro φ hφ
  obtain ⟨hφs, hφc, hφd⟩ := hφ
  have hφ1 : ContDiff ℝ 1 (fun z : ℝ × Space => φ z.1 z.2) := hφs.of_le (by simp)
  have hΦc : Continuous (fun z : ℝ × Space => φ z.1 z.2) := hφs.continuous
  have hDc := slice_fderiv_continuous hφ1
  have hDs := slice_fderiv_support hφ1 hφc
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.smooth.continuous
  have hDWc := slice_fderiv_continuous hW.smooth
  have hB : 0 ≤ |B| := abs_nonneg B
  have hWb : ∀ σ y, ‖W σ y‖ ≤ |B| := fun σ y => by
    have hp : (1 : ℝ) ≤ 1 + ‖y‖ := by linarith [norm_nonneg y]
    calc ‖W σ y‖ ≤ B / (1 + ‖y‖) := (hW.decay σ y).1
      _ ≤ |B| / (1 + ‖y‖) := div_le_div_of_nonneg_right (le_abs_self B) (by linarith)
      _ ≤ |B| := div_le_self hB hp
  have hDWb : ∀ σ y, ‖fderiv ℝ (W σ) y‖ ≤ |B| := fun σ y => by
    have hp : (1 : ℝ) ≤ (1 + ‖y‖) ^ 2 := one_le_pow₀ (by linarith [norm_nonneg y])
    calc ‖fderiv ℝ (W σ) y‖ ≤ B / (1 + ‖y‖) ^ 2 := (hW.decay σ y).2.1
      _ ≤ |B| / (1 + ‖y‖) ^ 2 := div_le_div_of_nonneg_right (le_abs_self B) (by linarith)
      _ ≤ |B| := div_le_self hB hp
  have hvL := Coercive.Internal.PerturbationFacts.velocity_locallyIntegrable hP
  have hGL := Coercive.Internal.PerturbationFacts.gradient_locallyIntegrable hP
  have hHL := Coercive.Internal.PerturbationFacts.secondDeriv_locallyIntegrable hP
  have hgL := Coercive.FrequencySeminorm.Internal.derivative_locallyIntegrable hP
  have hFL : LocallyIntegrable (fun z : ℝ × Space => F z.1 z.2) volume := by
    have hn := Cert.Internal.CoerciveBordered.locallyIntegrable_of_periodic_sq (fun σ y => ‖F σ y‖)
      hFm.norm (fun σ y => by simp only [hFper σ y]) hF2
    exact hn.mono hFm (Filter.Eventually.of_forall fun z => by simp)
  have cφ : Continuous (fun z : ℝ × Space => ‖φ z.1 z.2‖) := hΦc.norm
  have sφ : HasCompactSupport (fun z : ℝ × Space => ‖φ z.1 z.2‖) := hφc.norm
  have cD : Continuous (fun z : ℝ × Space => ‖fderiv ℝ (φ z.1) z.2‖) := hDc.norm
  have sD : HasCompactSupport (fun z : ℝ × Space => ‖fderiv ℝ (φ z.1) z.2‖) := hDs.norm
  have mΦ := hΦc.aestronglyMeasurable (μ := volume)
  have mW := hWc.aestronglyMeasurable (μ := volume)
  have mDW := hDWc.aestronglyMeasurable (μ := volume)
  have mG := hGL.aestronglyMeasurable
  have mv := hvL.aestronglyMeasurable
  have iX1 : Integrable (fun z : ℝ × Space => inner ℝ (F z.1 z.2) (φ z.1 z.2)) volume :=
    integrable_of_local_bound hFL cφ sφ (hFm.inner mΦ) zero_le_one fun z => by
      rw [one_mul]; exact abs_real_inner_le_norm _ _
  have ig : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2) (φ z.1 z.2)) volume :=
    integrable_of_local_bound hgL cφ sφ (hgL.aestronglyMeasurable.inner mΦ) zero_le_one fun z => by
      rw [one_mul]; exact abs_real_inner_le_norm _ _
  have iGW : Integrable (fun z : ℝ × Space => inner ℝ (G z.1 z.2 (W z.1 z.2)) (φ z.1 z.2)) volume := by
    have m : AEStronglyMeasurable (fun z : ℝ × Space => G z.1 z.2 (W z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd :
        Continuous fun p : (Space →L[ℝ] Space) × Space => p.1 p.2).comp_aestronglyMeasurable (mG.prodMk mW)
    refine integrable_of_local_bound hGL cφ sφ (m.inner mΦ) hB fun z => ?_
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖G z.1 z.2 (W z.1 z.2)‖ * ‖φ z.1 z.2‖ ≤ (‖G z.1 z.2‖ * |B|) * ‖φ z.1 z.2‖ :=
          mul_le_mul_of_nonneg_right (((G z.1 z.2).le_opNorm _).trans
            (mul_le_mul_of_nonneg_left (hWb _ _) (norm_nonneg _))) (norm_nonneg _)
      _ = |B| * ‖G z.1 z.2‖ * ‖φ z.1 z.2‖ := by ring
  have iDWv : Integrable (fun z : ℝ × Space => inner ℝ (fderiv ℝ (W z.1) z.2 (v z.1 z.2)) (φ z.1 z.2)) volume := by
    have m : AEStronglyMeasurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (v z.1 z.2)) volume :=
      (continuous_fst.clm_apply continuous_snd :
        Continuous fun p : (Space →L[ℝ] Space) × Space => p.1 p.2).comp_aestronglyMeasurable (mDW.prodMk mv)
    refine integrable_of_local_bound hvL cφ sφ (m.inner mΦ) hB fun z => ?_
    refine (abs_real_inner_le_norm _ _).trans ?_
    calc ‖fderiv ℝ (W z.1) z.2 (v z.1 z.2)‖ * ‖φ z.1 z.2‖ ≤ (|B| * ‖v z.1 z.2‖) * ‖φ z.1 z.2‖ :=
          mul_le_mul_of_nonneg_right (((fderiv ℝ (W z.1) z.2).le_opNorm _).trans
            (mul_le_mul_of_nonneg_right (hDWb _ _) (norm_nonneg _))) (norm_nonneg _)
      _ = |B| * ‖v z.1 z.2‖ * ‖φ z.1 z.2‖ := by ring
  have iK : Integrable (fun z : ℝ × Space => inner ℝ (∑ i, κ i • b i z.1 z.2) (φ z.1 z.2)) volume := by
    have each : ∀ i, Integrable (fun z : ℝ × Space => κ i * inner ℝ (b i z.1 z.2) (φ z.1 z.2)) volume :=
      fun i => integrable_of_local_bound (hb i) cφ sφ
        (((hb i).aestronglyMeasurable.inner mΦ).const_mul (κ i)) (abs_nonneg (κ i)) fun z => by
          rw [abs_mul, mul_assoc]
          exact mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) (abs_nonneg _)
    refine (integrable_finsetSum Finset.univ fun i _ => each i).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [sum_inner, real_inner_smul_left]
  have mFr : AEStronglyMeasurable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume :=
    entry_pairing_measurable mG hDc.aestronglyMeasurable
  have iFr : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume :=
    integrable_of_local_bound hGL cD sD mFr (by norm_num : (0 : ℝ) ≤ 3) fun z => entry_pairing_abs_le _ _
  have iTr : Integrable (fun z : ℝ × Space => inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) volume := by
    have mTr : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivTrace (H z.1 z.2)) volume :=
      trace_measurable hHL.aestronglyMeasurable
    refine integrable_of_local_bound hHL cφ sφ (mTr.inner mΦ) (by norm_num : (0 : ℝ) ≤ 3) fun z => ?_
    exact (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (trace_norm_le _) (norm_nonneg _))
  have tA : ∀ l i : Fin 3, Integrable (fun z : ℝ × Space => G z.1 z.2 (unitVector i) l * W z.1 z.2 l * φ z.1 z.2 i
      + fderiv ℝ (W z.1) z.2 (unitVector i) l * v z.1 z.2 l * φ z.1 z.2 i) volume := by
    intro l i
    have c1 : Continuous (fun p : (Space →L[ℝ] Space) × Space × Space => p.1 (unitVector i) l * p.2.1 l * p.2.2 i) :=
      (((continuous_apply_coord l).comp (continuous_fst.clm_apply continuous_const)).mul
        ((continuous_apply_coord l).comp continuous_snd.fst)).mul ((continuous_apply_coord i).comp continuous_snd.snd)
    have t1 : Integrable (fun z : ℝ × Space => G z.1 z.2 (unitVector i) l * W z.1 z.2 l * φ z.1 z.2 i) volume := by
      refine integrable_of_local_bound hGL cφ sφ (c1.comp_aestronglyMeasurable (mG.prodMk (mW.prodMk mΦ))) hB
        fun z => ?_
      rw [abs_mul, abs_mul]
      calc |G z.1 z.2 (unitVector i) l| * |W z.1 z.2 l| * |φ z.1 z.2 i| ≤ ‖G z.1 z.2‖ * |B| * ‖φ z.1 z.2‖ :=
            mul_le_mul (mul_le_mul (entry_abs_le _ _ _) ((coord_abs_le _ _).trans (hWb _ _)) (abs_nonneg _)
              (norm_nonneg _)) (coord_abs_le _ _) (abs_nonneg _) (mul_nonneg (norm_nonneg _) hB)
        _ = |B| * ‖G z.1 z.2‖ * ‖φ z.1 z.2‖ := by ring
    have t2 : Integrable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector i) l * v z.1 z.2 l * φ z.1 z.2 i)
        volume := by
      refine integrable_of_local_bound hvL cφ sφ (c1.comp_aestronglyMeasurable (mDW.prodMk (mv.prodMk mΦ))) hB
        fun z => ?_
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul ((entry_abs_le _ _ _).trans (hDWb _ _)) (coord_abs_le _ _) (abs_nonneg _) hB)
              (coord_abs_le _ _) (abs_nonneg _) (mul_nonneg hB (norm_nonneg _))
    exact t1.add t2
  have iA : Integrable (fun z : ℝ × Space => ∑ l : Fin 3, ∑ i : Fin 3,
      (G z.1 z.2 (unitVector i) l * W z.1 z.2 l * φ z.1 z.2 i
        + fderiv ℝ (W z.1) z.2 (unitVector i) l * v z.1 z.2 l * φ z.1 z.2 i)) volume :=
    integrable_finsetSum _ fun l _ => integrable_finsetSum _ fun i _ => tA l i
  have iB : Integrable (fun z : ℝ × Space => matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)
      + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) volume := iFr.add iTr
  have iX2 : Integrable (fun z : ℝ × Space => inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2)
      + fderiv ℝ (W z.1) z.2 (v z.1 z.2) + ∑ i, κ i • b i z.1 z.2) (φ z.1 z.2)
      + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)) volume := by
    refine ((((ig.add iGW).add iDWv).add iK).add iFr).congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.add_apply, inner_add_left]
  have hA0 : ∫ z : ℝ × Space, (∑ l : Fin 3, ∑ i : Fin 3,
      (G z.1 z.2 (unitVector i) l * W z.1 z.2 l * φ z.1 z.2 i
        + fderiv ℝ (W z.1) z.2 (unitVector i) l * v z.1 z.2 l * φ z.1 z.2 i)) = 0 := by
    rw [Measure.volume_eq_prod] at iA ⊢
    rw [integral_prod _ iA]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hP.weak_gradient] with σ hσ
    exact product_pairing hσ (hW.smooth.comp (contDiff_const.prodMk contDiff_id))
      (hφs.comp (contDiff_const.prodMk contDiff_id)) (slice_support hφc σ) (hφd σ)
  have hB0 : ∫ z : ℝ × Space, (matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2)
      + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) = 0 := by
    rw [Measure.volume_eq_prod] at iB ⊢
    rw [integral_prod _ iB]
    refine integral_eq_zero_of_ae ?_
    filter_upwards [hP.weak_secondDeriv] with σ hσ
    exact second_derivative_pairing hσ (hφs.comp (contDiff_const.prodMk contDiff_id)) (slice_support hφc σ)
  have pt : ∀ z : ℝ × Space, inner ℝ (strongRemainder W b κ v G H g F z.1 z.2) (φ z.1 z.2) =
      inner ℝ (F z.1 z.2) (φ z.1 z.2)
        - (inner ℝ (g z.1 z.2 + G z.1 z.2 (W z.1 z.2) + fderiv ℝ (W z.1) z.2 (v z.1 z.2)
          + ∑ i, κ i • b i z.1 z.2) (φ z.1 z.2) + matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2))
        + (∑ l : Fin 3, ∑ i : Fin 3, (G z.1 z.2 (unitVector i) l * W z.1 z.2 l * φ z.1 z.2 i
          + fderiv ℝ (W z.1) z.2 (unitVector i) l * v z.1 z.2 l * φ z.1 z.2 i))
        + (matInner (G z.1 z.2) (fderiv ℝ (φ z.1) z.2) + inner ℝ (secondDerivTrace (H z.1 z.2)) (φ z.1 z.2)) := by
    intro z
    have c1 := cross_identity (G z.1 z.2) (W z.1 z.2) (φ z.1 z.2)
    have c2 := cross_identity (fderiv ℝ (W z.1) z.2) (v z.1 z.2) (φ z.1 z.2)
    simp only [inner_sub_left] at c1 c2
    simp only [strongRemainder, couplingField, vorticityOf, inner_sub_left, inner_add_left,
      Finset.sum_add_distrib]
    linarith
  have hRS' := hRS φ ⟨hφs, hφc, hφd⟩
  rw [integral_congr_ae (Filter.Eventually.of_forall pt)]
  have e1 := integral_add ((iX1.sub iX2).add iA) iB
  have e2 := integral_add (iX1.sub iX2) iA
  have e3 := integral_sub iX1 iX2
  simp only [Pi.add_apply, Pi.sub_apply] at e1 e2
  rw [e1, e2, e3, hRS', hA0, hB0]
  ring

end Internal.RemainderAnnihilates

open Internal.RemainderAnnihilates in
theorem remainderAnnihilates_holds : RemainderAnnihilatesHolds := by
  intro k C nE nM D hPF q hq v G H g hP κ F hFm hFper hF2 hRS
  obtain ⟨B, hW⟩ := hPF.model_state
  have hb : ∀ i, LocallyIntegrable (fun z : ℝ × Space => D.cert.actuator i z.1 z.2) volume := by
    intro i
    obtain ⟨S, hS⟩ := hPF.actuators i
    have hn := Cert.Internal.CoerciveBordered.locallyIntegrable_of_periodic_sq
      (fun σ y => ‖D.cert.actuator i σ y‖) hS.measurable.norm (fun σ y => by simp only [hS.periodic σ y])
      hS.square_finite
    exact hn.mono hS.measurable (Filter.Eventually.of_forall fun z => by simp)
  exact remainder_annihilates_of hW hb hP κ hFm hFper hF2 hRS

end Breakdown.CertCell.Assembly
