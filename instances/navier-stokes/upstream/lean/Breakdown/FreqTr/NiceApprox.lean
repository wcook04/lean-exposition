import Breakdown.FreqTr.Statements

open MeasureTheory Set Real
open scoped ENNReal ContDiff SchwartzMap FourierTransform

noncomputable section

namespace Breakdown.Freq

namespace Internal.NiceApprox

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def pd (v : Space) (f : Space → E) : Space → E := fun x => fderiv ℝ f x v

theorem contDiff_pd {f : Space → E} (hf : ContDiff ℝ ∞ f) (v : Space) :
    ContDiff ℝ ∞ (pd v f) :=
  (contDiff_infty_iff_fderiv.1 hf).2.clm_apply contDiff_const

theorem differentiable_pd {f : Space → E} (hf : ContDiff ℝ ∞ f) (v : Space) :
    Differentiable ℝ (pd v f) :=
  (contDiff_pd hf v).differentiable (by simp)

theorem pd_pd_apply {f : Space → E} (hf : ContDiff ℝ ∞ f) (v w x : Space) :
    pd v (pd w f) x = fderiv ℝ (fderiv ℝ f) x v w := by
  have hd : Differentiable ℝ (fderiv ℝ f) :=
    ((contDiff_infty_iff_fderiv.1 hf).2).differentiable (by simp)
  show fderiv ℝ (fun y => fderiv ℝ f y w) x v = _
  rw [fderiv_clm_apply (hd x) (differentiableAt_const w)]
  simp

theorem pd_comm {f : Space → E} (hf : ContDiff ℝ ∞ f) (v w : Space) :
    pd v (pd w f) = pd w (pd v f) := by
  funext x
  rw [pd_pd_apply hf, pd_pd_apply hf]
  exact (hf.contDiffAt.isSymmSndFDerivAt (by
    simp
    exact WithTop.coe_le_coe.2 (le_top : (2 : ℕ∞) ≤ ⊤))) v w

theorem pd_sum {ι : Type*} (s : Finset ι) (f : ι → Space → E) (hf : ∀ i, Differentiable ℝ (f i))
    (v : Space) : pd v (fun x => ∑ i ∈ s, f i x) = fun x => ∑ i ∈ s, pd v (f i) x := by
  funext x
  simp only [pd]
  have e : (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, f i := by
    funext y
    simp
  rw [e, fderiv_sum (fun i _ => hf i x)]
  simp

theorem pd_neg (f : Space → E) (v : Space) : pd v (fun x => -f x) = fun x => -pd v f x := by
  funext x
  simp [pd]

theorem pd_const_zero (v : Space) : pd v (fun _ : Space => (0 : E)) = fun _ => 0 := by
  funext x
  simp [pd]

theorem pd_apply_coord {g : Space → Space} (hg : Differentiable ℝ g) (v x : Space) (j : Fin 3) :
    pd v g x j = pd v (fun y => g y j) x := by
  simp only [pd]
  have h := ((EuclideanSpace.proj j : Space →L[ℝ] ℝ).hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv
  have e : (fun y => g y j) = (EuclideanSpace.proj j : Space →L[ℝ] ℝ) ∘ g := rfl
  rw [e, h]
  rfl

theorem hasCompactSupport_pd {f : Space → E} (hs : HasCompactSupport f) (v : Space) :
    HasCompactSupport (pd v f) :=
  (hs.fderiv (𝕜 := ℝ)).mono (fun x hx h0 => hx (by simp [pd, h0]))

theorem negSsp_eq (φ : Space → Space) (hf : ContDiff ℝ ∞ φ) :
    negSsp φ = fun x => -∑ i : Fin 3, pd (unitVector i) (pd (unitVector i) φ) x := by
  funext x
  simp only [negSsp, sumSecondPartialsAt, iteratedFDeriv_two_apply, pd_pd_apply hf]
  rfl

end Internal.NiceApprox

namespace Internal.NiceApprox

theorem divergence_eq_sum (g : Space → Space) (y : Space) :
    divergenceAt g y = ∑ j : Fin 3, pd (unitVector j) g y j := rfl

theorem contDiff_coord {f : Space → Space} (hf : ContDiff ℝ ∞ f) (j : Fin 3) :
    ContDiff ℝ ∞ (fun x => f x j) :=
  (EuclideanSpace.proj j : Space →L[ℝ] ℝ).contDiff.comp hf

theorem pd_coord_fun {g : Space → Space} (hg : Differentiable ℝ g) (v : Space) (j : Fin 3) :
    (fun x => pd v g x j) = pd v (fun y => g y j) := funext fun x => pd_apply_coord hg v x j

theorem divergence_negSsp {φ : Space → Space} (hf : ContDiff ℝ ∞ φ)
    (hdiv : ∀ y, divergenceAt φ y = 0) (y : Space) : divergenceAt (negSsp φ) y = 0 := by
  have hpp : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (unitVector i) (pd (unitVector i) φ)) :=
    fun i => contDiff_pd (contDiff_pd hf _) _
  have hS : ∀ j : Fin 3, ContDiff ℝ ∞ (fun x => pd (unitVector j) φ x j) :=
    fun j => contDiff_coord (contDiff_pd hf _) j
  have key : ∀ i j : Fin 3, pd (unitVector j) (pd (unitVector i) (pd (unitVector i) φ)) y j =
      pd (unitVector i) (pd (unitVector i) (fun x => pd (unitVector j) φ x j)) y := by
    intro i j
    rw [pd_comm (contDiff_pd hf (unitVector i)) (unitVector j) (unitVector i),
      pd_comm hf (unitVector j) (unitVector i),
      pd_apply_coord (differentiable_pd (contDiff_pd hf _) _),
      pd_coord_fun (differentiable_pd hf _)]
  have hj : ∀ j : Fin 3, pd (unitVector j) (negSsp φ) y j =
      -∑ i : Fin 3, pd (unitVector i) (pd (unitVector i) (fun x => pd (unitVector j) φ x j)) y := by
    intro j
    have e1 : pd (unitVector j) (fun x => ∑ i : Fin 3, pd (unitVector i) (pd (unitVector i) φ) x) =
        fun x => ∑ i : Fin 3, pd (unitVector j) (pd (unitVector i) (pd (unitVector i) φ)) x :=
      pd_sum _ _ (fun i => (hpp i).differentiable (by simp)) _
    rw [negSsp_eq φ hf, pd_neg, e1]
    rw [← Finset.sum_congr rfl (fun i _ => key i j)]
    simp
  have hsum : ∀ i : Fin 3,
      ∑ j : Fin 3, pd (unitVector i) (pd (unitVector i) (fun x => pd (unitVector j) φ x j)) y = 0 := by
    intro i
    have h1 : (fun x => ∑ j : Fin 3, pd (unitVector j) φ x j) = fun _ => (0 : ℝ) := funext hdiv
    have e2 : pd (unitVector i) (fun x => ∑ j : Fin 3, pd (unitVector j) φ x j) =
        fun x => ∑ j : Fin 3, pd (unitVector i) (fun x => pd (unitVector j) φ x j) x :=
      pd_sum _ _ (fun j => (hS j).differentiable (by simp)) _
    have e3 : pd (unitVector i) (fun x => ∑ j : Fin 3, pd (unitVector i) (fun x => pd (unitVector j) φ x j) x) =
        fun x => ∑ j : Fin 3, pd (unitVector i) (pd (unitVector i) (fun x => pd (unitVector j) φ x j)) x :=
      pd_sum _ _ (fun j => differentiable_pd (hS j) _) _
    calc ∑ j : Fin 3, pd (unitVector i) (pd (unitVector i) (fun x => pd (unitVector j) φ x j)) y
        = pd (unitVector i) (pd (unitVector i) (fun x => ∑ j : Fin 3, pd (unitVector j) φ x j)) y := by
          rw [e2, e3]
      _ = 0 := by rw [h1, pd_const_zero, pd_const_zero]
  rw [divergence_eq_sum, Finset.sum_congr rfl (fun j _ => hj j), Finset.sum_neg_distrib,
    Finset.sum_comm, Finset.sum_congr rfl (fun i _ => hsum i)]
  simp

theorem negSsp_isTestField {φ : Space → Space} (h : IsTestField φ) : IsTestField (negSsp φ) := by
  obtain ⟨hd, hs, hdiv⟩ := h
  have hpp : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (unitVector i) (pd (unitVector i) φ)) :=
    fun i => contDiff_pd (contDiff_pd hd _) _
  have hcs : ∀ i : Fin 3, HasCompactSupport (pd (unitVector i) (pd (unitVector i) φ)) :=
    fun i => hasCompactSupport_pd (hasCompactSupport_pd hs _) _
  refine ⟨?_, ?_, divergence_negSsp hd hdiv⟩
  · rw [negSsp_eq φ hd]
    exact (ContDiff.sum (fun i _ => hpp i)).neg
  · rw [negSsp_eq φ hd]
    have : HasCompactSupport (fun x => ∑ i : Fin 3, pd (unitVector i) (pd (unitVector i) φ) x) := by
      simp only [Fin.sum_univ_three]
      exact ((hcs 0).add (hcs 1)).add (hcs 2)
    exact this.neg

end Internal.NiceApprox

namespace Internal.NiceApprox

def crossL (a : Space) : Space →L[ℝ] Space :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 ![a 1 * z 2 - a 2 * z 1, a 2 * z 0 - a 0 * z 2,
        a 0 * z 1 - a 1 * z 0]
      map_add' := fun z w => by
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := fun c z => by
        ext i
        fin_cases i <;> simp <;> ring }

theorem crossL_apply (a z : Space) : crossL a z = WithLp.toLp 2 ![a 1 * z 2 - a 2 * z 1,
    a 2 * z 0 - a 0 * z 2, a 0 * z 1 - a 1 * z 0] := rfl

def curlField (A : Space → Space) : Space → Space := fun x =>
  ∑ j : Fin 3, crossL (unitVector j) (pd (unitVector j) A x)

theorem pd_clm {F G : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G]
    [NormedSpace ℝ G] (L : F →L[ℝ] G) {g : Space → F} (hg : Differentiable ℝ g) (v : Space) :
    pd v (fun x => L (g x)) = fun x => L (pd v g x) := by
  funext x
  simp only [pd]
  have h := (L.hasFDerivAt.comp x (hg x).hasFDerivAt).fderiv
  have e : (fun y => L (g y)) = L ∘ g := rfl
  rw [e, h]
  rfl

theorem contDiff_curlField {A : Space → Space} (hA : ContDiff ℝ ∞ A) : ContDiff ℝ ∞ (curlField A) :=
  ContDiff.sum (fun j _ => (crossL (unitVector j)).contDiff.comp (contDiff_pd hA _))

theorem divergence_curlField {A : Space → Space} (hA : ContDiff ℝ ∞ A) (y : Space) :
    divergenceAt (curlField A) y = 0 := by
  have hk : ∀ k : Fin 3, pd (unitVector k) (curlField A) y =
      ∑ j : Fin 3, crossL (unitVector j) (pd (unitVector k) (pd (unitVector j) A) y) := by
    intro k
    have e1 : pd (unitVector k) (curlField A) =
        fun x => ∑ j : Fin 3, pd (unitVector k) (fun x => crossL (unitVector j) (pd (unitVector j) A x)) x :=
      pd_sum _ _ (fun j => ((crossL (unitVector j)).contDiff.comp (contDiff_pd hA _)).differentiable
        (by simp)) _
    rw [e1]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [pd_clm _ (differentiable_pd hA _)]
  rw [divergence_eq_sum]
  simp only [hk, Fin.sum_univ_three]
  rw [pd_comm hA (unitVector 1) (unitVector 0), pd_comm hA (unitVector 2) (unitVector 0),
    pd_comm hA (unitVector 2) (unitVector 1)]
  simp [crossL_apply, unitVector]
  ring

theorem rapid_bound {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] (H : 𝓢(Space, F))
    (k : ℕ) : ∃ C : ℝ, ∀ y, ‖H y‖ ≤ C / (1 + ‖y‖) ^ k := by
  refine ⟨2 ^ k * (Finset.Iic (k, 0)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) H, fun y => ?_⟩
  have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (k, 0)) (k := k) (n := 0)
    le_rfl le_rfl H y
  rw [norm_iteratedFDeriv_zero] at h
  rw [le_div_iff₀ (by positivity)]
  linarith [mul_comm ((1 + ‖y‖) ^ k) ‖H y‖]

theorem isDecayField_rapid (G : 𝓢(Space, Space)) (hdiv : ∀ y, divergenceAt G y = 0) :
    IsDecayField G := by
  obtain ⟨C1, hC1⟩ := rapid_bound G 1
  obtain ⟨C2, hC2⟩ := rapid_bound (SchwartzMap.fderivCLM ℝ Space Space G) 2
  refine ⟨G.smooth ⊤, hdiv, max C1 C2, fun y => ⟨?_, ?_⟩⟩
  · have h1 := hC1 y
    rw [pow_one] at h1
    refine h1.trans ?_
    gcongr
    exact le_max_left _ _
  · have h2 := hC2 y
    rw [SchwartzMap.fderivCLM_apply] at h2
    refine h2.trans ?_
    gcongr
    exact le_max_right _ _

def curlS (A : 𝓢(Space, Space)) : 𝓢(Space, Space) :=
  ∑ j : Fin 3, SchwartzMap.postcompCLM (crossL (unitVector j)) (LineDeriv.lineDerivOp (unitVector j) A)

theorem curlS_apply (A : 𝓢(Space, Space)) : ⇑(curlS A) = curlField A := by
  funext x
  simp [curlS, curlField, SchwartzMap.postcompCLM_apply, SchwartzMap.lineDerivOp_apply_eq_fderiv, pd]

def negSspS (G : 𝓢(Space, Space)) : 𝓢(Space, Space) :=
  -∑ i : Fin 3, LineDeriv.lineDerivOp (unitVector i) (LineDeriv.lineDerivOp (unitVector i) G)

theorem negSspS_apply (G : 𝓢(Space, Space)) : ⇑(negSspS G) = negSsp G := by
  rw [negSsp_eq _ (G.smooth ⊤)]
  have e : ∀ i : Fin 3, ⇑(LineDeriv.lineDerivOp (unitVector i) G) = pd (unitVector i) ⇑G :=
    fun i => rfl
  funext x
  simp [negSspS, SchwartzMap.lineDerivOp_apply_eq_fderiv, e]
  rfl

theorem curl_decay (A : 𝓢(Space, Space)) :
    IsDecayField (curlField A) ∧ IsDecayField (negSsp (curlField A)) := by
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  have hdiv := divergence_curlField hA
  have hc : ContDiff ℝ ∞ (curlField A) := contDiff_curlField hA
  refine ⟨?_, ?_⟩
  · rw [← curlS_apply]
    exact isDecayField_rapid _ (by rw [curlS_apply]; exact hdiv)
  · rw [← curlS_apply, ← negSspS_apply]
    refine isDecayField_rapid _ ?_
    rw [negSspS_apply, curlS_apply]
    exact divergence_negSsp hc hdiv

end Internal.NiceApprox

namespace Internal.NiceApprox

def stdBump : ContDiffBump (0 : Space) := ⟨1, 2, one_pos, one_lt_two⟩

def cutField (A : Space → Space) (R : ℝ) : Space → Space := fun y => stdBump (R⁻¹ • y) • A y

theorem contDiff_cutField {A : Space → Space} (hA : ContDiff ℝ ∞ A) (R : ℝ) :
    ContDiff ℝ ∞ (cutField A R) :=
  (stdBump.contDiff.comp (contDiff_id.const_smul R⁻¹)).smul hA

theorem hasCompactSupport_cutField (A : Space → Space) {R : ℝ} (hR : R ≠ 0) :
    HasCompactSupport (cutField A R) := by
  have h : HasCompactSupport (fun y : Space => stdBump (R⁻¹ • y)) :=
    stdBump.hasCompactSupport.comp_smul (inv_ne_zero hR)
  exact h.smul_right

theorem hasCompactSupport_curlField {A : Space → Space} (hs : HasCompactSupport A) :
    HasCompactSupport (curlField A) := by
  have h : ∀ j : Fin 3, HasCompactSupport (fun x => crossL (unitVector j) (pd (unitVector j) A x)) :=
    fun j => (hasCompactSupport_pd hs _).comp_left (map_zero _)
  unfold curlField
  simp only [Fin.sum_univ_three]
  exact ((h 0).add (h 1)).add (h 2)

theorem cutoff_isTestField {A : Space → Space} (hA : ContDiff ℝ ∞ A) {R : ℝ} (hR : R ≠ 0) :
    IsTestField (curlField (cutField A R)) :=
  ⟨contDiff_curlField (contDiff_cutField hA R),
    hasCompactSupport_curlField (hasCompactSupport_cutField A hR),
    divergence_curlField (contDiff_cutField hA R)⟩

theorem pd_sub' {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f g : Space → E}
    (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) (v : Space) :
    pd v (fun x => f x - g x) = fun x => pd v f x - pd v g x := by
  funext x
  simp only [pd]
  rw [fderiv_fun_sub (hf x) (hg x)]
  rfl

theorem curlField_sub {f g : Space → Space} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g) :
    curlField (fun x => f x - g x) = fun x => curlField f x - curlField g x := by
  funext x
  simp only [curlField, pd_sub' hf hg, map_sub, Finset.sum_sub_distrib]

theorem negSsp_sub {f g : Space → Space} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) :
    negSsp (fun x => f x - g x) = fun x => negSsp f x - negSsp g x := by
  rw [negSsp_eq _ (hf.sub hg), negSsp_eq _ hf, negSsp_eq _ hg]
  have h1 := pd_sub' (hf.differentiable (by simp)) (hg.differentiable (by simp))
  have h2 : ∀ v w : Space, pd w (fun x => pd v f x - pd v g x) =
      fun x => pd w (pd v f) x - pd w (pd v g) x :=
    fun v w => pd_sub' (differentiable_pd hf v) (differentiable_pd hg v) w
  funext x
  simp only [h1, h2, Finset.sum_sub_distrib]
  abel

theorem negSsp_isTestField_aux {f : Space → Space} (hf : ContDiff ℝ ∞ f) : ContDiff ℝ ∞ (negSsp f) := by
  rw [negSsp_eq f hf]
  exact (ContDiff.sum (fun i _ => contDiff_pd (contDiff_pd hf _) _)).neg

theorem pd_zero_on {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    {U : Set Space} (hU : IsOpen U) (h : ∀ x ∈ U, f x = 0) (v : Space) :
    ∀ x ∈ U, pd v f x = 0 := by
  intro x hx
  have hev : f =ᶠ[nhds x] fun _ => 0 := by
    filter_upwards [hU.mem_nhds hx] with y hy
    exact h y hy
  simp only [pd, hev.fderiv_eq]
  simp

theorem curlField_zero_on {f : Space → Space} {U : Set Space} (hU : IsOpen U)
    (h : ∀ x ∈ U, f x = 0) : ∀ x ∈ U, curlField f x = 0 := by
  intro x hx
  simp [curlField, pd_zero_on hU h _ x hx]

theorem negSsp_zero_on {f : Space → Space} (hf : ContDiff ℝ ∞ f) {U : Set Space} (hU : IsOpen U)
    (h : ∀ x ∈ U, f x = 0) : ∀ x ∈ U, negSsp f x = 0 := by
  intro x hx
  rw [negSsp_eq f hf]
  simp [pd_zero_on hU (pd_zero_on hU h _) _ x hx]

theorem cutField_sub_zero_on (A : Space → Space) {R : ℝ} (hR : 0 < R) :
    ∀ x ∈ Metric.ball (0 : Space) R, cutField A R x - A x = 0 := by
  intro x hx
  have h1 : stdBump (R⁻¹ • x) = 1 := by
    apply stdBump.one_of_mem_closedBall
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hR]
    have : ‖x‖ < R := by simpa using hx
    show R⁻¹ * ‖x‖ ≤ 1
    rw [inv_mul_le_iff₀ hR]
    linarith
  simp [cutField, h1]

theorem cutoff_eventually_zero (A : 𝓢(Space, Space)) (y : Space) :
    ∀ᶠ R in Filter.atTop,
      (∑ i : Fin 3, ‖fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i)‖ ^ 2) = 0 ∧
      (∑ i : Fin 3,
        ‖fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i)‖ ^ 2) = 0 := by
  filter_upwards [Filter.eventually_gt_atTop ‖y‖, Filter.eventually_gt_atTop 0] with R hR hR0
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  have hψ : ContDiff ℝ ∞ (fun x => cutField A R x - A x) := (contDiff_cutField hA R).sub hA
  have hU : IsOpen (Metric.ball (0 : Space) R) := Metric.isOpen_ball
  have hy : y ∈ Metric.ball (0 : Space) R := by simpa using hR
  have hc := curlField_zero_on hU (cutField_sub_zero_on A hR0)
  have hl := negSsp_zero_on (contDiff_curlField hψ) hU hc
  have e1 : ∀ i : Fin 3, fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i) = 0 :=
    fun i => pd_zero_on hU hc _ y hy
  have e2 : ∀ i : Fin 3,
      fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i) = 0 :=
    fun i => pd_zero_on hU hl _ y hy
  simp [e1, e2]

theorem le_infty_of_nat (n : ℕ) : (n : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

theorem norm_iter_pd {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : ContDiff ℝ ∞ f) (w x : Space) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (pd w f) x‖ ≤ ‖w‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have e : pd w f = (ContinuousLinearMap.apply ℝ E w) ∘ fderiv ℝ f := rfl
  rw [e, (ContinuousLinearMap.apply ℝ E w).iteratedFDeriv_comp_left
    ((contDiff_infty_iff_fderiv.1 hf).2.contDiffAt) (le_infty_of_nat n)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  rw [norm_iteratedFDeriv_fderiv]
  gcongr
  refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun L => ?_)
  rw [ContinuousLinearMap.apply_apply, mul_comm]
  exact L.le_opNorm w

theorem norm_unitVector (j : Fin 3) : ‖unitVector j‖ = 1 := by
  simp [unitVector]

theorem norm_pd_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : Space → E}
    (hf : ContDiff ℝ ∞ f) (j : Fin 3) (x : Space) :
    ‖pd (unitVector j) f x‖ ≤ ‖iteratedFDeriv ℝ 1 f x‖ := by
  have h := norm_iter_pd hf (unitVector j) x 0
  rw [norm_iteratedFDeriv_zero, norm_unitVector, one_mul] at h
  exact h

def curlConst : ℝ := ∑ j : Fin 3, ‖crossL (unitVector j)‖

theorem norm_iter_curl {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x : Space) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (curlField f) x‖ ≤ curlConst * ‖iteratedFDeriv ℝ (n + 1) f x‖ := by
  have hc : ∀ j : Fin 3, ContDiff ℝ ∞ (fun z => crossL (unitVector j) (pd (unitVector j) f z)) :=
    fun j => (crossL (unitVector j)).contDiff.comp (contDiff_pd hf _)
  unfold curlField
  rw [iteratedFDeriv_fun_sum_apply (fun j _ => (hc j).contDiffAt.of_le (le_infty_of_nat n))]
  refine (norm_sum_le _ _).trans ?_
  rw [curlConst, Finset.sum_mul]
  gcongr with j
  have e : (fun z => crossL (unitVector j) (pd (unitVector j) f z)) =
      crossL (unitVector j) ∘ pd (unitVector j) f := rfl
  rw [e, (crossL (unitVector j)).iteratedFDeriv_comp_left (contDiff_pd hf _).contDiffAt
    (le_infty_of_nat n)]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  gcongr
  have h := norm_iter_pd hf (unitVector j) x n
  rwa [norm_unitVector, one_mul] at h

theorem norm_iter_negSsp {f : Space → Space} (hf : ContDiff ℝ ∞ f) (x : Space) (n : ℕ) :
    ‖iteratedFDeriv ℝ n (negSsp f) x‖ ≤ 3 * ‖iteratedFDeriv ℝ (n + 2) f x‖ := by
  have hc : ∀ i : Fin 3, ContDiff ℝ ∞ (pd (unitVector i) (pd (unitVector i) f)) :=
    fun i => contDiff_pd (contDiff_pd hf _) _
  rw [negSsp_eq f hf]
  have e : (fun x => -∑ i : Fin 3, pd (unitVector i) (pd (unitVector i) f) x) =
      -(fun x => ∑ i : Fin 3, pd (unitVector i) (pd (unitVector i) f) x) := rfl
  rw [e, iteratedFDeriv_neg_apply, norm_neg,
    iteratedFDeriv_fun_sum_apply (fun i _ => (hc i).contDiffAt.of_le (le_infty_of_nat n))]
  refine (norm_sum_le _ _).trans ?_
  have hb : ∀ i : Fin 3, ‖iteratedFDeriv ℝ n (pd (unitVector i) (pd (unitVector i) f)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + 2) f x‖ := by
    intro i
    have h1 := norm_iter_pd (contDiff_pd hf (unitVector i)) (unitVector i) x n
    have h2 := norm_iter_pd hf (unitVector i) x (n + 1)
    rw [norm_unitVector, one_mul] at h1 h2
    exact h1.trans h2
  calc ∑ i : Fin 3, ‖iteratedFDeriv ℝ n (pd (unitVector i) (pd (unitVector i) f)) x‖
      ≤ ∑ _i : Fin 3, ‖iteratedFDeriv ℝ (n + 2) f x‖ := Finset.sum_le_sum (fun i _ => hb i)
    _ = 3 * ‖iteratedFDeriv ℝ (n + 2) f x‖ := by simp

theorem cut_iter_bound (A : 𝓢(Space, Space)) (n : ℕ) : ∃ C : ℝ, ∀ R : ℝ, 1 ≤ R → ∀ y,
    ‖iteratedFDeriv ℝ n (fun x => cutField A R x - A x) y‖ ≤ C / (1 + ‖y‖) ^ 4 := by
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  have hB : ∀ i : ℕ, ∃ B : ℝ, ∀ z, ‖iteratedFDeriv ℝ i stdBump z‖ ≤ B := fun i =>
    (stdBump.contDiff.continuous_iteratedFDeriv (le_infty_of_nat i)).norm.bounded_above_of_compact_support
      (stdBump.hasCompactSupport.iteratedFDeriv i).norm |>.imp fun B hB z => by
        simpa using hB z
  have hS : ∀ j : ℕ, ∃ S : ℝ, ∀ y, (1 + ‖y‖) ^ 4 * ‖iteratedFDeriv ℝ j A y‖ ≤ S := fun j =>
    ⟨_, fun y => SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := (4, j)) le_rfl le_rfl A y⟩
  choose B hB using hB
  choose S hS using hS
  have hB0 : ∀ i, 0 ≤ B i := fun i => (norm_nonneg _).trans (hB i 0)
  have hχ : ∀ R : ℝ, 1 ≤ R → ∀ (i : ℕ) (y : Space),
      ‖iteratedFDeriv ℝ i (fun y : Space => stdBump (R⁻¹ • y)) y‖ ≤ B i := by
    intro R hR i y
    set L : Space →L[ℝ] Space := R⁻¹ • ContinuousLinearMap.id ℝ Space with hLdef
    have e : (fun y : Space => stdBump (R⁻¹ • y)) = ⇑stdBump ∘ ⇑L := rfl
    rw [e, L.iteratedFDeriv_comp_right stdBump.contDiff y (le_infty_of_nat i)]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have hR0 : 0 < R := lt_of_lt_of_le one_pos hR
    have hL : ‖L‖ ≤ 1 := by
      refine (norm_smul_le _ _).trans ?_
      rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hR0)]
      calc R⁻¹ * ‖ContinuousLinearMap.id ℝ Space‖ ≤ 1 * 1 :=
            mul_le_mul (inv_le_one_of_one_le₀ hR) ContinuousLinearMap.norm_id_le (norm_nonneg _)
              zero_le_one
        _ = 1 := one_mul 1
    calc ‖iteratedFDeriv ℝ i stdBump (L y)‖ * ∏ _j : Fin i, ‖L‖ ≤ B i * 1 :=
          mul_le_mul (hB i _) (Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun _ _ => hL))
            (Finset.prod_nonneg fun _ _ => norm_nonneg _) (hB0 i)
      _ = B i := mul_one _
  refine ⟨∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * S (n - i) + S n,
    fun R hR y => ?_⟩
  have hp : 0 < (1 + ‖y‖) ^ 4 := by positivity
  have hAb : ∀ j, ‖iteratedFDeriv ℝ j A y‖ ≤ S j / (1 + ‖y‖) ^ 4 := fun j => by
    rw [le_div_iff₀ hp]
    linarith [hS j y, mul_comm ((1 + ‖y‖) ^ 4) ‖iteratedFDeriv ℝ j A y‖]
  have hχc : ContDiff ℝ ∞ (fun y : Space => stdBump (R⁻¹ • y)) :=
    stdBump.contDiff.comp (contDiff_id.const_smul R⁻¹)
  have hsub : iteratedFDeriv ℝ n (fun x => cutField A R x - A x) y =
      iteratedFDeriv ℝ n (cutField A R) y - iteratedFDeriv ℝ n A y :=
    iteratedFDeriv_sub_apply ((contDiff_cutField hA R).contDiffAt.of_le (le_infty_of_nat n))
      (hA.contDiffAt.of_le (le_infty_of_nat n))
  have hcut : cutField A R = fun x => stdBump (R⁻¹ • x) • A x := rfl
  calc ‖iteratedFDeriv ℝ n (fun x => cutField A R x - A x) y‖
      ≤ ‖iteratedFDeriv ℝ n (cutField A R) y‖ + ‖iteratedFDeriv ℝ n A y‖ := by
        rw [hsub]
        exact norm_sub_le _ _
    _ ≤ ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * B i * (S (n - i) / (1 + ‖y‖) ^ 4) +
        S n / (1 + ‖y‖) ^ 4 := by
        refine add_le_add ?_ (hAb n)
        rw [hcut]
        refine (norm_iteratedFDeriv_smul_le hχc hA y (le_infty_of_nat n)).trans ?_
        refine Finset.sum_le_sum fun i _ => ?_
        exact mul_le_mul (mul_le_mul_of_nonneg_left (hχ R hR i y) (Nat.cast_nonneg _)) (hAb _)
          (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (hB0 i))
    _ = _ := by
        rw [add_div, Finset.sum_div]
        congr 1
        exact Finset.sum_congr rfl fun i _ => by ring

theorem curlConst_nonneg : 0 ≤ curlConst := Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem cutoff_dominated (A : 𝓢(Space, Space)) :
    ∃ g : Space → ℝ, Integrable g ∧ ∀ᶠ R in Filter.atTop, ∀ y,
      (∑ i : Fin 3, ‖fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i)‖ ^ 2) ≤ g y ∧
      (∑ i : Fin 3,
        ‖fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i)‖ ^ 2) ≤ g y := by
  obtain ⟨C2, hC2⟩ := cut_iter_bound A 2
  obtain ⟨C4, hC4⟩ := cut_iter_bound A 4
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  have hK := curlConst_nonneg
  set K1 : ℝ := 3 * (curlConst * C2) ^ 2
  set K2 : ℝ := 3 * (3 * curlConst * C4) ^ 2
  refine ⟨fun y => (K1 + K2) * ((1 + ‖y‖) ^ 8)⁻¹, ?_, ?_⟩
  · have hi : Integrable (fun y : Space => (1 + ‖y‖) ^ (-(8 : ℝ))) volume :=
      integrable_one_add_norm (by simp; norm_num)
    refine (hi.const_mul (K1 + K2)).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only
    rw [Real.rpow_neg (by positivity)]
    norm_cast
  · filter_upwards [Filter.eventually_ge_atTop 1] with R hR y
    have hψ : ContDiff ℝ ∞ (fun x => cutField A R x - A x) := (contDiff_cutField hA R).sub hA
    have hc := contDiff_curlField hψ
    have hl := negSsp_isTestField_aux hc
    have hp : 0 < (1 + ‖y‖) ^ 4 := by positivity
    have hq : ((1 + ‖y‖) ^ 8)⁻¹ = ((1 + ‖y‖) ^ 4)⁻¹ ^ 2 := by
      rw [inv_pow, ← pow_mul]
    have h1 : ∀ i : Fin 3,
        ‖fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i)‖ ^ 2 ≤
          (curlConst * C2) ^ 2 * ((1 + ‖y‖) ^ 8)⁻¹ := by
      intro i
      have a := norm_pd_le hc i y
      have b := norm_iter_curl hψ y 1
      have c := hC2 R hR y
      have d : ‖fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i)‖ ≤
          curlConst * C2 * ((1 + ‖y‖) ^ 4)⁻¹ := by
        calc _ ≤ curlConst * ‖iteratedFDeriv ℝ 2 (fun x => cutField A R x - A x) y‖ := a.trans b
          _ ≤ curlConst * (C2 / (1 + ‖y‖) ^ 4) := mul_le_mul_of_nonneg_left c hK
          _ = _ := by ring
      rw [hq, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) d 2
    have h2 : ∀ i : Fin 3,
        ‖fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i)‖ ^ 2 ≤
          (3 * curlConst * C4) ^ 2 * ((1 + ‖y‖) ^ 8)⁻¹ := by
      intro i
      have a := norm_pd_le hl i y
      have b := norm_iter_negSsp hc y 1
      have b2 := norm_iter_curl hψ y 3
      have c := hC4 R hR y
      have d : ‖fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i)‖ ≤
          3 * curlConst * C4 * ((1 + ‖y‖) ^ 4)⁻¹ := by
        calc _ ≤ 3 * ‖iteratedFDeriv ℝ 3 (curlField (fun x => cutField A R x - A x)) y‖ := a.trans b
          _ ≤ 3 * (curlConst * ‖iteratedFDeriv ℝ 4 (fun x => cutField A R x - A x) y‖) :=
            mul_le_mul_of_nonneg_left b2 (by norm_num)
          _ ≤ 3 * (curlConst * (C4 / (1 + ‖y‖) ^ 4)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left c hK) (by norm_num)
          _ = _ := by ring
      rw [hq, ← mul_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) d 2
    have hw : 0 ≤ ((1 + ‖y‖) ^ 8)⁻¹ := by positivity
    have hK1 : 0 ≤ K1 := by positivity
    have hK2 : 0 ≤ K2 := by positivity
    constructor
    · calc _ ≤ ∑ _i : Fin 3, (curlConst * C2) ^ 2 * ((1 + ‖y‖) ^ 8)⁻¹ :=
            Finset.sum_le_sum fun i _ => h1 i
        _ = K1 * ((1 + ‖y‖) ^ 8)⁻¹ := by simp [K1]; ring
        _ ≤ (K1 + K2) * ((1 + ‖y‖) ^ 8)⁻¹ := by nlinarith
    · calc _ ≤ ∑ _i : Fin 3, (3 * curlConst * C4) ^ 2 * ((1 + ‖y‖) ^ 8)⁻¹ :=
            Finset.sum_le_sum fun i _ => h2 i
        _ = K2 * ((1 + ‖y‖) ^ 8)⁻¹ := by simp [K2]; ring
        _ ≤ (K1 + K2) * ((1 + ‖y‖) ^ 8)⁻¹ := by nlinarith

theorem cutoff_tendsto (A : 𝓢(Space, Space)) :
    Filter.Tendsto (fun R : ℝ => ∫ y, ∑ i : Fin 3,
      ‖fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i)‖ ^ 2)
      Filter.atTop (nhds 0) ∧
    Filter.Tendsto (fun R : ℝ => ∫ y, ∑ i : Fin 3,
      ‖fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i)‖ ^ 2)
      Filter.atTop (nhds 0) := by
  obtain ⟨g, hg, hb⟩ := cutoff_dominated A
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  have hcont : ∀ R : ℝ, Continuous (fun y => ∑ i : Fin 3,
      ‖fderiv ℝ (curlField (fun x => cutField A R x - A x)) y (unitVector i)‖ ^ 2) ∧
      Continuous (fun y => ∑ i : Fin 3,
      ‖fderiv ℝ (negSsp (curlField (fun x => cutField A R x - A x))) y (unitVector i)‖ ^ 2) := by
    intro R
    have hψ : ContDiff ℝ ∞ (fun x => cutField A R x - A x) := (contDiff_cutField hA R).sub hA
    have hc := contDiff_curlField hψ
    have hl := (negSsp_isTestField_aux hc)
    exact ⟨continuous_finsetSum _ (fun i _ => ((contDiff_pd hc (unitVector i)).continuous).norm.pow 2),
      continuous_finsetSum _ (fun i _ => ((contDiff_pd hl (unitVector i)).continuous).norm.pow 2)⟩
  have h0 : (0 : ℝ) = ∫ _ : Space, (0 : ℝ) := by simp
  constructor
  · rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence g
      (Filter.Eventually.of_forall fun R => (hcont R).1.aestronglyMeasurable) ?_ hg ?_
    · filter_upwards [hb] with R hR
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
        exact (hR y).1
    · exact Filter.Eventually.of_forall fun y => tendsto_const_nhds.congr'
        ((cutoff_eventually_zero A y).mono fun R hR => hR.1.symm)
  · rw [h0]
    refine tendsto_integral_filter_of_dominated_convergence g
      (Filter.Eventually.of_forall fun R => (hcont R).2.aestronglyMeasurable) ?_ hg ?_
    · filter_upwards [hb] with R hR
      exact Filter.Eventually.of_forall fun y => by
        rw [Real.norm_of_nonneg (Finset.sum_nonneg fun i _ => by positivity)]
        exact (hR y).2
    · exact Filter.Eventually.of_forall fun y => tendsto_const_nhds.congr'
        ((cutoff_eventually_zero A y).mono fun R hR => hR.2.symm)

theorem cutoff_approx (A : 𝓢(Space, Space)) (δ : ℝ) (hδ : 0 < δ) : ∃ φ, IsTestField φ ∧
    ∫ y, ∑ i : Fin 3, ‖fderiv ℝ (φ - curlField A) y (unitVector i)‖ ^ 2 < δ ∧
    ∫ y, ∑ i : Fin 3,
      ‖fderiv ℝ (negSsp φ - negSsp (curlField A)) y (unitVector i)‖ ^ 2 < δ := by
  have hA : ContDiff ℝ ∞ (A : Space → Space) := A.smooth ⊤
  obtain ⟨t1, t2⟩ := cutoff_tendsto A
  obtain ⟨R, h1, h2, hR⟩ := ((t1.eventually (gt_mem_nhds hδ)).and
    ((t2.eventually (gt_mem_nhds hδ)).and (Filter.eventually_gt_atTop 0))).exists
  have hc := contDiff_cutField hA R
  have eq1 : curlField (cutField A R) - curlField A = curlField (fun x => cutField A R x - A x) := by
    rw [curlField_sub (hc.differentiable (by simp)) (hA.differentiable (by simp))]
    rfl
  have eq2 : negSsp (curlField (cutField A R)) - negSsp (curlField A) =
      negSsp (curlField (fun x => cutField A R x - A x)) := by
    rw [curlField_sub (hc.differentiable (by simp)) (hA.differentiable (by simp)),
      negSsp_sub (contDiff_curlField hc) (contDiff_curlField hA)]
    rfl
  refine ⟨curlField (cutField A R), cutoff_isTestField hA hR.ne', ?_, ?_⟩
  · rw [eq1]
    exact h1
  · rw [eq2]
    exact h2

end Internal.NiceApprox

namespace Internal.NiceApprox

theorem exists_bound_of_compactSupport {F : Type*} [NormedAddCommGroup F] {g : Space → F}
    (hg : Continuous g) (hs : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, ∀ y, ‖g y‖ ≤ C / (1 + ‖y‖) ^ k := by
  have hc : Continuous (fun y => (1 + ‖y‖) ^ k * ‖g y‖) := by fun_prop
  have hs' : HasCompactSupport (fun y => (1 + ‖y‖) ^ k * ‖g y‖) := hs.norm.mul_left
  obtain ⟨C, hC⟩ := hc.bounded_above_of_compact_support hs'
  refine ⟨C, fun y => ?_⟩
  have hpos : 0 < (1 + ‖y‖) ^ k := by positivity
  rw [le_div_iff₀ hpos]
  have := hC y
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
  linarith [mul_comm ((1 + ‖y‖) ^ k) ‖g y‖]

theorem isDecayField_of_isTestField {φ : Space → Space} (h : IsTestField φ) : IsDecayField φ := by
  obtain ⟨hd, hs, hdiv⟩ := h
  refine ⟨hd, hdiv, ?_⟩
  obtain ⟨C1, hC1⟩ := exists_bound_of_compactSupport hd.continuous hs 1
  obtain ⟨C2, hC2⟩ := exists_bound_of_compactSupport (hd.continuous_fderiv (by simp))
    (hs.fderiv (𝕜 := ℝ)) 2
  refine ⟨max C1 C2, fun y => ⟨?_, ?_⟩⟩
  · have h1 := hC1 y
    rw [pow_one] at h1
    refine h1.trans ?_
    gcongr
    exact le_max_left _ _
  · refine (hC2 y).trans ?_
    gcongr
    exact le_max_right _ _

theorem isDecayField_sub {f g : Space → Space} (hf : IsDecayField f) (hg : IsDecayField g) :
    IsDecayField (f - g) := by
  obtain ⟨hf1, hf2, C, hC⟩ := hf
  obtain ⟨hg1, hg2, D, hD⟩ := hg
  have e : ∀ y, fderiv ℝ (f - g) y = fderiv ℝ f y - fderiv ℝ g y := fun y =>
    fderiv_sub ((hf1.differentiable (by simp)) y) ((hg1.differentiable (by simp)) y)
  refine ⟨hf1.sub hg1, fun y => ?_, C + D, fun y => ⟨?_, ?_⟩⟩
  · have a := hf2 y
    have b := hg2 y
    simp only [divergenceAt, e] at a b ⊢
    simp [Finset.sum_sub_distrib, a, b]
  · calc ‖(f - g) y‖ ≤ ‖f y‖ + ‖g y‖ := norm_sub_le _ _
      _ ≤ C / (1 + ‖y‖) + D / (1 + ‖y‖) := add_le_add (hC y).1 (hD y).1
      _ = (C + D) / (1 + ‖y‖) := by ring
  · calc ‖fderiv ℝ (f - g) y‖ ≤ ‖fderiv ℝ f y‖ + ‖fderiv ℝ g y‖ := by rw [e]; exact norm_sub_le _ _
      _ ≤ C / (1 + ‖y‖) ^ 2 + D / (1 + ‖y‖) ^ 2 := add_le_add (hC y).2 (hD y).2
      _ = (C + D) / (1 + ‖y‖) ^ 2 := by ring

theorem eLpNorm_embed_sub_lt (h3 : EmbedNorm) (h4 : EmbedLinear) {f g : Space → Space}
    {n : Space → CSpace} (hf : IsDecayField f) (hg : IsDecayField g)
    (hn : ((embedX g : X) : L2C) =ᵐ[volume] n) {ε : ℝ} (hε : 0 < ε)
    (hint : ∫ y, ∑ i : Fin 3, ‖fderiv ℝ (f - g) y (unitVector i)‖ ^ 2 < ε ^ 2) :
    (eLpNorm (fun ξ => ((embedX f : X) : L2C) ξ - n ξ) 2 volume).toReal < ε := by
  have hsub := h4.2.1 f g hf hg
  have hnorm := h3 (f - g) (isDecayField_sub hf hg)
  have key : eLpNorm (fun ξ => ((embedX f : X) : L2C) ξ - n ξ) 2 volume =
      eLpNorm (((embedX (f - g) : X) : L2C) : Space → CSpace) 2 volume := by
    apply eLpNorm_congr_ae
    rw [hsub]
    filter_upwards [hn, Lp.coeFn_sub ((embedX f : X) : L2C) ((embedX g : X) : L2C)] with ξ ha hb
    rw [Submodule.coe_sub, hb, Pi.sub_apply, ha]
  rw [key, ← Lp.norm_def]
  have hx : ‖((embedX (f - g) : X) : L2C)‖ ^ 2 < ε ^ 2 := by
    rw [← Submodule.coe_norm, hnorm]
    exact hint
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hx

theorem cmul_norm_le (c : ℂ) : ‖cmul c‖ ≤ ‖c‖ :=
  ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) (fun z => by
    show ‖c • z‖ ≤ ‖c‖ * ‖z‖
    exact (norm_smul c z).le)

theorem continuous_cmul : Continuous cmul := by
  have : cmul = fun c : ℂ => c • ((ContinuousLinearMap.id ℂ CSpace).restrictScalars ℝ) := by
    funext c
    ext z i
    simp [cmul]
  rw [this]
  fun_prop

theorem gradSymbol_norm_le (k : Fin 3) (ξ : Space) : ‖gradSymbol k ξ‖ ≤ 1 := by
  rcases eq_or_ne ξ 0 with h | h
  · simp [gradSymbol, h]
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 h
  have hk : |ξ k| ≤ ‖ξ‖ := by
    have := EuclideanSpace.norm_eq ξ
    rw [this]
    calc |ξ k| = Real.sqrt (ξ k ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt (∑ i, ‖ξ i‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        have := Finset.single_le_sum (f := fun i => ‖ξ i‖ ^ 2) (fun i _ => by positivity) (Finset.mem_univ k)
        simpa [Real.norm_eq_abs, sq_abs] using this
  simp only [gradSymbol, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos hn]
  exact (div_le_one hn).2 hk

theorem measurable_gradSymbol (k : Fin 3) : Measurable (gradSymbol k) := by
  unfold gradSymbol
  fun_prop

theorem fieldOp_grad_ae (h1 : FieldOpRealized) (k : Fin 3) (f : L2C) :
    (fieldOp id (fun ξ => cmul (gradSymbol k ξ)) f : Space → CSpace) =ᵐ[volume]
      fun ξ => gradSymbol k ξ • (f ξ) := by
  have hm : AEStronglyMeasurable (fun ξ => cmul (gradSymbol k ξ)) volume :=
    (continuous_cmul.measurable.comp (measurable_gradSymbol k)).aestronglyMeasurable
  have e := h1 (ContinuousLinearEquiv.refl ℝ Space) (fun ξ => cmul (gradSymbol k ξ)) 1 hm
    (fun ξ => (cmul_norm_le _).trans (gradSymbol_norm_le k ξ)) f
  filter_upwards [e] with ξ hξ
  rw [show (id : Space → Space) = ⇑(ContinuousLinearEquiv.refl ℝ Space) from rfl, hξ]
  rfl

theorem scalar_identity (ξ : Space) (F : CSpace) :
    ∑ k : Fin 3, gradSymbol k ξ • ((2 * π * Complex.I) • ((ξ k : ℝ) • F)) = (2 * π * ‖ξ‖) • F := by
  rcases eq_or_ne ξ 0 with h | h
  · simp [gradSymbol, h]
  have hn : (‖ξ‖ : ℂ) ≠ 0 := by exact_mod_cast (norm_pos_iff.2 h).ne'
  have hn2 : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [sq_abs]
  have hn2c : ((‖ξ‖ : ℝ) : ℂ) ^ 2 = ((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2 := by
    exact_mod_cast hn2
  have e : ∀ k : Fin 3, gradSymbol k ξ • ((2 * π * Complex.I) • ((ξ k : ℝ) • F)) =
      (gradSymbol k ξ * (2 * π * Complex.I) * ((ξ k : ℝ) : ℂ)) • F := by
    intro k
    rw [← Complex.coe_smul, smul_smul, smul_smul]
  simp only [e, Fin.sum_univ_three, ← add_smul]
  rw [← Complex.coe_smul]
  congr 1
  simp only [gradSymbol]
  have hI := Complex.I_sq
  have key : -(Complex.I * ((ξ 0 : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ)) * (2 * π * Complex.I) * ((ξ 0 : ℝ) : ℂ) +
      -(Complex.I * ((ξ 1 : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ)) * (2 * π * Complex.I) * ((ξ 1 : ℝ) : ℂ) +
      -(Complex.I * ((ξ 2 : ℝ) : ℂ) / ((‖ξ‖ : ℝ) : ℂ)) * (2 * π * Complex.I) * ((ξ 2 : ℝ) : ℂ) =
      (2 * π) * (((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2) *
        ((‖ξ‖ : ℝ) : ℂ)⁻¹ * (-(Complex.I ^ 2)) := by ring
  rw [key, hI, ← hn2c]
  push_cast
  field_simp

theorem embed_rapid (h1 : FieldOpRealized) (h2 : EmbedMem) (G : 𝓢(Space, Space))
    (hdiv : ∀ y, divergenceAt G y = 0) :
    ((embedX G : X) : L2C) =ᵐ[volume]
      fun ξ => (2 * π * ‖ξ‖) • FourierTransform.fourier (fun x => complexifyVec (G x)) ξ := by
  set g : 𝓢(Space, CSpace) := SchwartzMap.postcompCLM complexifyVec G with hg
  have hgc : ⇑g = fun x => complexifyVec (G x) := funext fun x => SchwartzMap.postcompCLM_apply _ _ _
  have hdec : IsDecayField G := isDecayField_rapid G hdiv
  have hemb : ((embedX G : X) : L2C) = ofGrad G := by
    simp only [embedX, dif_pos (h2 _ hdec)]
  have hA : ∀ k : Fin 3, ⇑(LineDeriv.lineDerivOp (unitVector k) g) =
      fun x => complexifyVec (partialField G k x) := by
    intro k
    show pd (unitVector k) ⇑g = _
    rw [hgc, pd_clm complexifyVec G.differentiable]
    rfl
  have hB : ∀ k : Fin 3, complexify (toLpOrZero 2 (partialField G k)) =
      (LineDeriv.lineDerivOp (unitVector k) g).toLp 2 := by
    intro k
    have hm : MemLp (partialField G k) 2 volume :=
      (LineDeriv.lineDerivOp (unitVector k) G).memLp 2 volume
    have t1 : toLpOrZero 2 (partialField G k) = hm.toLp _ := dif_pos hm
    rw [t1]
    apply Lp.ext
    filter_upwards [ContinuousLinearMap.coeFn_compLpL (p := 2) (μ := (volume : Measure Space))
      complexifyVec (hm.toLp _), hm.coeFn_toLp,
      (LineDeriv.lineDerivOp (unitVector k) g).coeFn_toLp 2 volume] with ξ a b c
    rw [c, hA]
    show (ContinuousLinearMap.compLpL 2 volume complexifyVec (hm.toLp _)) ξ = _
    rw [a, b]
  have hC : ∀ k : Fin 3, freqTrR ((LineDeriv.lineDerivOp (unitVector k) g).toLp 2) =
      (𝓕 (LineDeriv.lineDerivOp (unitVector k) g)).toLp 2 := fun k =>
    SchwartzMap.toLp_fourier_eq _
  have hT : ∀ k : Fin 3, (fun x : Space => inner ℝ x (unitVector k)).HasTemperateGrowth :=
    fun k => ((innerSL ℝ).flip (unitVector k)).hasTemperateGrowth
  have hD : ∀ (k : Fin 3) (ξ : Space), (𝓕 (LineDeriv.lineDerivOp (unitVector k) g)) ξ =
      (2 * π * Complex.I) • ((ξ k : ℝ) • FourierTransform.fourier (fun x => complexifyVec (G x)) ξ) := by
    intro k ξ
    rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply,
      SchwartzMap.smulLeftCLM_apply_apply (hT k), SchwartzMap.fourier_coe, hgc]
    congr 2
    simp [unitVector, EuclideanSpace.inner_single_right]
  have hk : ∀ k : Fin 3, (fieldOp id (fun ξ => cmul (gradSymbol k ξ))
      (freqTrR (complexify (toLpOrZero 2 (partialField G k)))) : Space → CSpace) =ᵐ[volume]
      fun ξ => gradSymbol k ξ • ((2 * π * Complex.I) •
        ((ξ k : ℝ) • FourierTransform.fourier (fun x => complexifyVec (G x)) ξ)) := by
    intro k
    rw [hB, hC]
    filter_upwards [fieldOp_grad_ae h1 k ((𝓕 (LineDeriv.lineDerivOp (unitVector k) g)).toLp 2),
      (𝓕 (LineDeriv.lineDerivOp (unitVector k) g)).coeFn_toLp 2 volume] with ξ a b
    rw [a, b, hD]
  rw [hemb]
  unfold ofGrad
  simp only [Fin.sum_univ_three]
  filter_upwards [Lp.coeFn_add (_ + _ : L2C) (_ : L2C), Lp.coeFn_add (_ : L2C) (_ : L2C),
    hk 0, hk 1, hk 2] with ξ a b c0 c1 c2
  rw [a, Pi.add_apply, b, Pi.add_apply, c0, c1, c2, ← scalar_identity ξ, Fin.sum_univ_three]

theorem freqTr_lineDeriv_apply (f : 𝓢(Space, CSpace)) (k : Fin 3) (ξ : Space) :
    (𝓕 (LineDeriv.lineDerivOp (unitVector k) f)) ξ = (2 * π * Complex.I) • ((ξ k : ℝ) • (𝓕 f) ξ) := by
  have hT : (fun x : Space => inner ℝ x (unitVector k)).HasTemperateGrowth :=
    ((innerSL ℝ).flip (unitVector k)).hasTemperateGrowth
  rw [SchwartzMap.fourier_lineDerivOp_eq, smul_apply, SchwartzMap.smulLeftCLM_apply_apply hT]
  congr 2
  simp [unitVector, EuclideanSpace.inner_single_right]

theorem postcomp_negSspS (G : 𝓢(Space, Space)) :
    SchwartzMap.postcompCLM complexifyVec (negSspS G) =
      -∑ i : Fin 3, LineDeriv.lineDerivOp (unitVector i)
        (LineDeriv.lineDerivOp (unitVector i) (SchwartzMap.postcompCLM complexifyVec G)) := by
  have hgc : ⇑(SchwartzMap.postcompCLM complexifyVec G) = fun x => complexifyVec (G x) :=
    funext fun x => SchwartzMap.postcompCLM_apply _ _ _
  have hi : ∀ i : Fin 3, ⇑(LineDeriv.lineDerivOp (unitVector i)
      (LineDeriv.lineDerivOp (unitVector i) (SchwartzMap.postcompCLM complexifyVec G))) =
      fun x => complexifyVec (pd (unitVector i) (pd (unitVector i) ⇑G) x) := by
    intro i
    show pd (unitVector i) (pd (unitVector i) ⇑(SchwartzMap.postcompCLM complexifyVec G)) = _
    rw [hgc, pd_clm complexifyVec G.differentiable,
      pd_clm complexifyVec (differentiable_pd (G.smooth ⊤) _)]
  ext x : 1
  rw [SchwartzMap.postcompCLM_apply, negSspS_apply, negSsp_eq _ (G.smooth ⊤)]
  simp only [Fin.sum_univ_three, neg_apply, add_apply, hi, map_neg, map_add]

theorem freqTr_negSsp (G : 𝓢(Space, Space)) (ξ : Space) :
    FourierTransform.fourier (fun x => complexifyVec (negSsp G x)) ξ =
      sspFactor ξ • FourierTransform.fourier (fun x => complexifyVec (G x)) ξ := by
  have h1 : (fun x => complexifyVec (negSsp G x)) =
      ⇑(SchwartzMap.postcompCLM complexifyVec (negSspS G)) := by
    funext x
    rw [SchwartzMap.postcompCLM_apply, negSspS_apply]
  have h2 : (fun x => complexifyVec (G x)) = ⇑(SchwartzMap.postcompCLM complexifyVec G) :=
    funext fun x => (SchwartzMap.postcompCLM_apply _ _ _).symm
  rw [h1, h2, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourier_coe, postcomp_negSspS]
  set g := SchwartzMap.postcompCLM complexifyVec G
  have hn2 : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [sq_abs]
  have e : ∀ i : Fin 3, (𝓕 (LineDeriv.lineDerivOp (unitVector i) (LineDeriv.lineDerivOp (unitVector i) g))) ξ =
      (-(4 * π ^ 2 * ξ i ^ 2) : ℝ) • (𝓕 g) ξ := by
    intro i
    rw [freqTr_lineDeriv_apply, freqTr_lineDeriv_apply]
    simp only [← Complex.coe_smul, smul_smul]
    congr 1
    push_cast
    linear_combination (4 * (π : ℂ) ^ 2 * ((ξ i : ℝ) : ℂ) ^ 2) * Complex.I_sq
  rw [← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]
  simp only [Fin.sum_univ_three, map_neg, map_add, neg_apply, add_apply,
    SchwartzMap.fourierTransformCLM_apply, e]
  rw [← add_smul, ← add_smul, ← neg_smul]
  congr 1
  simp only [sspFactor, hn2]
  ring

theorem freqTr_clm_apply (L : CSpace →L[ℂ] CSpace) (f : 𝓢(Space, CSpace)) (ξ : Space) :
    FourierTransform.fourier (fun x => L (f x)) ξ = L (FourierTransform.fourier (⇑f) ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi : Integrable (fun v : Space => 𝐞 (-inner ℝ v ξ) • f v) volume :=
    (Real.fourierIntegral_convergent_iff ξ).2 f.integrable
  rw [← L.integral_comp_comm hi]
  congr 1
  funext v
  rw [Circle.smul_def, Circle.smul_def, map_smul]

theorem conjVec_circle_smul (t : ℝ) (w : CSpace) :
    conjVec (𝐞 t • w) = 𝐞 (-t) • conjVec w := by
  rw [Circle.smul_def, Circle.smul_def]
  ext i
  simp only [conjVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.toLp_apply, PiLp.smul_apply, smul_eq_mul, star_mul', Real.fourierChar_apply]
  congr 1
  change (starRingEnd ℂ) _ = _
  rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

theorem conjVec_conjVec (w : CSpace) : conjVec (conjVec w) = w := by
  ext i
  simp [conjVec]

theorem freqTrInv_conj (a : 𝓢(Space, CSpace)) (ha : ∀ ξ, a (-ξ) = conjVec (a ξ)) (x : Space) :
    conjVec ((𝓕⁻ a) x) = (𝓕⁻ a) x := by
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  have hi : Integrable (fun v : Space => 𝐞 (inner ℝ v x) • a v) volume := by
    have := (Real.fourierIntegral_convergent_iff (-x)).2 (a.integrable (μ := volume))
    simpa [inner_neg_right] using this
  rw [← conjVec.integral_comp_comm hi]
  simp only [conjVec_circle_smul]
  rw [← integral_neg_eq_self]
  congr 1
  funext v
  rw [inner_neg_left, neg_neg, ha, conjVec_conjVec]

theorem complexify_realVec_of_conj {z : CSpace} (h : conjVec z = z) : complexifyVec (realVec z) = z := by
  ext i
  have hi := congrArg (fun w : CSpace => w i) h
  simp only [conjVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk, AddHom.coe_mk,
    PiLp.toLp_apply] at hi
  simp only [complexifyVec, realVec, LinearMap.coe_toContinuousLinearMap', LinearMap.coe_mk,
    AddHom.coe_mk, PiLp.toLp_apply]
  exact Complex.conj_eq_iff_re.1 hi

def crossC (a : Space) : CSpace →L[ℂ] CSpace :=
  LinearMap.toContinuousLinearMap
    { toFun := fun z => WithLp.toLp 2 ![(a 1 : ℂ) * z 2 - (a 2 : ℂ) * z 1,
        (a 2 : ℂ) * z 0 - (a 0 : ℂ) * z 2, (a 0 : ℂ) * z 1 - (a 1 : ℂ) * z 0]
      map_add' := fun z w => by
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := fun c z => by
        ext i
        fin_cases i <;> simp <;> ring }

theorem crossC_apply (a : Space) (z : CSpace) : crossC a z = WithLp.toLp 2 ![(a 1 : ℂ) * z 2 - (a 2 : ℂ) * z 1,
    (a 2 : ℂ) * z 0 - (a 0 : ℂ) * z 2, (a 0 : ℂ) * z 1 - (a 1 : ℂ) * z 0] := rfl

theorem complexify_crossL (a z : Space) : complexifyVec (crossL a z) = crossC a (complexifyVec z) := by
  ext i
  fin_cases i <;> simp [crossL_apply, crossC_apply, complexifyVec]

def potentialSymbol (m : Space → CSpace) (ξ : Space) : CSpace :=
  ((4 * π ^ 2 * ‖ξ‖ ^ 3)⁻¹ : ℝ) • (Complex.I • crossC ξ (m ξ))

theorem potentialSymbol_conjSym {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ : Space) :
    potentialSymbol m (-ξ) = conjVec (potentialSymbol m ξ) := by
  have h := hm.2.2.2.1 ξ
  simp only [potentialSymbol, norm_neg, h]
  ext i
  fin_cases i <;> simp [crossC_apply, conjVec] <;> ring

theorem potentialSymbol_contDiff {m : Space → CSpace} (hm : IsNiceSymbol m) :
    ContDiff ℝ ∞ (potentialSymbol m) := by
  obtain ⟨hs, -, ⟨r, hr, hz⟩, -, -⟩ := hm
  have hmi : ∀ j, ContDiff ℝ ∞ (fun ξ => m ξ j) := fun j => (contDiff_piLp 2).1 hs j
  have hξ : ∀ j : Fin 3, ContDiff ℝ ∞ (fun ξ : Space => ((ξ j : ℝ) : ℂ)) := fun j =>
    Complex.ofRealCLM.contDiff.comp (contDiff_coord contDiff_id j)
  have hc : ContDiff ℝ ∞ (fun ξ : Space => Complex.I • crossC ξ (m ξ)) := by
    refine ContDiff.const_smul Complex.I ?_
    rw [contDiff_piLp 2]
    intro i
    fin_cases i
    · exact ((hξ 1).mul (hmi 2)).sub ((hξ 2).mul (hmi 1))
    · exact ((hξ 2).mul (hmi 0)).sub ((hξ 0).mul (hmi 2))
    · exact ((hξ 0).mul (hmi 1)).sub ((hξ 1).mul (hmi 0))
  rw [contDiff_iff_contDiffAt]
  intro ξ
  rcases lt_or_ge ‖ξ‖ r with h | h
  · have hev : potentialSymbol m =ᶠ[nhds ξ] fun _ => 0 := by
      filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds h] with y hy
      simp [potentialSymbol, hz y hy]
    exact contDiffAt_const.congr_of_eventuallyEq hev
  · have hne : ξ ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at h
      linarith
    have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hne
    have hn : ContDiffAt ℝ ∞ (fun y : Space => (4 * π ^ 2 * ‖y‖ ^ 3)⁻¹) ξ :=
      (contDiffAt_const.mul ((contDiffAt_norm ℝ hne).pow 3)).inv (by positivity)
    exact hn.smul hc.contDiffAt

theorem potentialSymbol_hasCompactSupport {m : Space → CSpace} (hm : IsNiceSymbol m) :
    HasCompactSupport (potentialSymbol m) :=
  hm.2.1.mono (fun ξ hξ h0 => hξ (by simp [potentialSymbol, h0]))

theorem potential_algebra {m : Space → CSpace} (hm : IsNiceSymbol m) (ξ : Space) (hξ : ξ ≠ 0) :
    (2 * π * ‖ξ‖) • ∑ j : Fin 3, crossC (unitVector j)
      ((2 * π * Complex.I) • ((ξ j : ℝ) • potentialSymbol m ξ)) = m ξ := by
  have hdiv := hm.2.2.2.2 ξ
  simp only [Fin.sum_univ_three] at hdiv
  have hn2 : ‖ξ‖ ^ 2 = ξ 0 ^ 2 + ξ 1 ^ 2 + ξ 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_three]
    simp [sq_abs]
  have hp : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  have hn0 : ((‖ξ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hπ0 : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  set n : ℂ := ((‖ξ‖ : ℝ) : ℂ) with hn
  set u : ℂ := n⁻¹ with hu
  set P : ℂ := (π : ℂ) * (π : ℂ)⁻¹ with hPdef
  have hN : n * u = 1 := mul_inv_cancel₀ hn0
  have hP : P = 1 := mul_inv_cancel₀ hπ0
  have hn2c : n ^ 2 = ((ξ 0 : ℝ) : ℂ) ^ 2 + ((ξ 1 : ℝ) : ℂ) ^ 2 + ((ξ 2 : ℝ) : ℂ) ^ 2 := by
    rw [hn]
    exact_mod_cast hn2
  ext i
  fin_cases i <;> simp [crossC_apply, potentialSymbol, unitVector, Fin.sum_univ_three]
  · linear_combination (P ^ 2 * Complex.I ^ 2 * n * u ^ 3 * ((ξ 0 : ℝ) : ℂ)) * hdiv +
      (P ^ 2 * Complex.I ^ 2 * n * u ^ 3 * m ξ 0) * hn2c + (-(m ξ 0) * P ^ 2 * (n * u) ^ 3) * Complex.I_sq +
      (m ξ 0 * (P + 1) * (n * u) ^ 3) * hP + (m ξ 0 * ((n * u) ^ 2 + n * u + 1)) * hN
  · linear_combination (P ^ 2 * Complex.I ^ 2 * n * u ^ 3 * ((ξ 1 : ℝ) : ℂ)) * hdiv +
      (P ^ 2 * Complex.I ^ 2 * n * u ^ 3 * m ξ 1) * hn2c + (-(m ξ 1) * P ^ 2 * (n * u) ^ 3) * Complex.I_sq +
      (m ξ 1 * (P + 1) * (n * u) ^ 3) * hP + (m ξ 1 * ((n * u) ^ 2 + n * u + 1)) * hN
  · linear_combination (P ^ 2 * Complex.I ^ 2 * n * u ^ 3 * ((ξ 2 : ℝ) : ℂ)) * hdiv +
      (P ^ 2 * Complex.I ^ 2 * n * u ^ 3 * m ξ 2) * hn2c + (-(m ξ 2) * P ^ 2 * (n * u) ^ 3) * Complex.I_sq +
      (m ξ 2 * (P + 1) * (n * u) ^ 3) * hP + (m ξ 2 * ((n * u) ^ 2 + n * u + 1)) * hN

theorem symbol_curl_freqTr (m : Space → CSpace) (hm : IsNiceSymbol m) :
    ∃ A : 𝓢(Space, Space), ∀ ξ : Space, ξ ≠ 0 →
      (2 * π * ‖ξ‖) • FourierTransform.fourier (fun x => complexifyVec (curlField A x)) ξ = m ξ := by
  set a : 𝓢(Space, CSpace) :=
    (potentialSymbol_hasCompactSupport hm).toSchwartzMap (potentialSymbol_contDiff hm) with ha
  have haf : ⇑a = potentialSymbol m := rfl
  set Ac : 𝓢(Space, CSpace) := 𝓕⁻ a with hAc
  set A : 𝓢(Space, Space) := SchwartzMap.postcompCLM realVec Ac with hA
  have hcA : ∀ x, complexifyVec (A x) = Ac x := by
    intro x
    rw [hA, SchwartzMap.postcompCLM_apply]
    exact complexify_realVec_of_conj
      (freqTrInv_conj a (fun ξ => by rw [haf]; exact potentialSymbol_conjSym hm ξ) x)
  have hcAf : (fun x => complexifyVec (A x)) = ⇑Ac := funext hcA
  have hpd : ∀ (j : Fin 3) (x : Space), complexifyVec (pd (unitVector j) (⇑A) x) =
      (LineDeriv.lineDerivOp (unitVector j) Ac) x := by
    intro j x
    show _ = pd (unitVector j) ⇑Ac x
    rw [← hcAf, pd_clm complexifyVec A.differentiable]
  set S : 𝓢(Space, CSpace) := ∑ j : Fin 3, SchwartzMap.postcompCLM
    ((crossC (unitVector j)).restrictScalars ℝ) (LineDeriv.lineDerivOp (unitVector j) Ac) with hSdef
  have hS : (fun x => complexifyVec (curlField A x)) = ⇑S := by
    funext x
    simp only [hSdef, curlField, Fin.sum_univ_three, map_add, add_apply,
      SchwartzMap.postcompCLM_apply, complexify_crossL, hpd, ContinuousLinearMap.coe_restrictScalars']
  refine ⟨A, fun ξ hξ => ?_⟩
  have hF : ∀ j : Fin 3, (𝓕 (SchwartzMap.postcompCLM ((crossC (unitVector j)).restrictScalars ℝ)
      (LineDeriv.lineDerivOp (unitVector j) Ac))) ξ =
      crossC (unitVector j) ((2 * π * Complex.I) • ((ξ j : ℝ) • potentialSymbol m ξ)) := by
    intro j
    rw [SchwartzMap.fourier_coe]
    have e : ⇑(SchwartzMap.postcompCLM ((crossC (unitVector j)).restrictScalars ℝ)
        (LineDeriv.lineDerivOp (unitVector j) Ac)) =
        fun x => crossC (unitVector j) ((LineDeriv.lineDerivOp (unitVector j) Ac) x) :=
      funext fun x => SchwartzMap.postcompCLM_apply _ _ _
    rw [e, freqTr_clm_apply, ← SchwartzMap.fourier_coe, freqTr_lineDeriv_apply, hAc,
      FourierTransform.fourier_fourierInv_eq, haf]
  rw [hS, ← SchwartzMap.fourier_coe, ← SchwartzMap.fourierTransformCLM_apply (𝕜 := ℂ)]
  simp only [hSdef, Fin.sum_univ_three, map_add, add_apply, SchwartzMap.fourierTransformCLM_apply, hF]
  rw [← potential_algebra hm ξ hξ, Fin.sum_univ_three]

theorem symbol_rapid (m : Space → CSpace) (hm : IsNiceSymbol m) :
    ∃ A : 𝓢(Space, Space), ∀ ξ : Space, ξ ≠ 0 →
      (2 * π * ‖ξ‖) • FourierTransform.fourier (fun x => complexifyVec (curlField A x)) ξ = m ξ ∧
      (2 * π * ‖ξ‖) • FourierTransform.fourier
        (fun x => complexifyVec (negSsp (curlField A) x)) ξ = sspFactor ξ • m ξ := by
  obtain ⟨A, hA⟩ := symbol_curl_freqTr m hm
  refine ⟨A, fun ξ hξ => ⟨hA ξ hξ, ?_⟩⟩
  have h := freqTr_negSsp (curlS A) ξ
  rw [curlS_apply] at h
  rw [h, smul_comm, hA ξ hξ]

theorem symbol_curl_embed (h1 : FieldOpRealized) (h2 : EmbedMem) (m : Space → CSpace)
    (hm : IsNiceSymbol m) :
    ∃ A : 𝓢(Space, Space), ((embedX (curlField A) : X) : L2C) =ᵐ[volume] m ∧
      ((embedX (negSsp (curlField A)) : X) : L2C) =ᵐ[volume] fun ξ => sspFactor ξ • m ξ := by
  obtain ⟨A, hA⟩ := symbol_rapid m hm
  have hne : ∀ᵐ ξ ∂(volume : Measure Space), ξ ≠ 0 := by
    filter_upwards [compl_mem_ae_iff.2 (measure_singleton (0 : Space))] with ξ hξ
    exact Set.mem_compl_singleton_iff.1 hξ
  have hc : ContDiff ℝ ∞ (curlField A) := contDiff_curlField (A.smooth ⊤)
  have hd : ∀ y, divergenceAt (curlField A) y = 0 := divergence_curlField (A.smooth ⊤)
  refine ⟨A, ?_, ?_⟩
  · have h := embed_rapid h1 h2 (curlS A) (by rw [curlS_apply]; exact hd)
    rw [curlS_apply] at h
    filter_upwards [h, hne] with ξ hξ hξ0
    rw [hξ, (hA ξ hξ0).1]
  · have h := embed_rapid h1 h2 (negSspS (curlS A))
      (by rw [negSspS_apply, curlS_apply]; exact divergence_negSsp hc hd)
    rw [negSspS_apply, curlS_apply] at h
    filter_upwards [h, hne] with ξ hξ hξ0
    rw [hξ, (hA ξ hξ0).2]

end Internal.NiceApprox

theorem niceApprox (h1 : FieldOpRealized) (h2 : EmbedMem) (h3 : EmbedNorm) (h4 : EmbedLinear)
    (_h5 : EmbedNegSsp) : NiceApprox := by
  intro m hm ε hε
  obtain ⟨A, hA1, hA2⟩ := Internal.NiceApprox.symbol_curl_embed h1 h2 m hm
  obtain ⟨hu, hlu⟩ := Internal.NiceApprox.curl_decay A
  obtain ⟨φ, hφ, hφ1, hφ2⟩ := Internal.NiceApprox.cutoff_approx A (ε ^ 2) (by positivity)
  have hφd := Internal.NiceApprox.isDecayField_of_isTestField hφ
  have hlφd := Internal.NiceApprox.isDecayField_of_isTestField (Internal.NiceApprox.negSsp_isTestField hφ)
  exact ⟨φ, hφ, Internal.NiceApprox.eLpNorm_embed_sub_lt h3 h4 hφd hu hA1 hε hφ1,
    Internal.NiceApprox.eLpNorm_embed_sub_lt h3 h4 hlφd hlu hA2 hε hφ2⟩

end Breakdown.Freq
