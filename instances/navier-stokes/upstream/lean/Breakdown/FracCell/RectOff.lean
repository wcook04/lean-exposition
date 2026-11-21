import Breakdown.FracCell.FieldWitness
import Breakdown.FracCell.FieldWitnessRect

open MeasureTheory Polynomial Set
open scoped Interval

noncomputable section

namespace Breakdown.CellCert.Spectral

open SteadyCert

namespace Internal.RectOff

open Internal.FieldWitness

def scaledRes (x0 x1 lam : ℝ) (p : ℝ[X]) (x : ℝ) : ℝ :=
  intervalResolvent (lam * (x1 - x0) ^ 2 / 4) (p.comp (C ((x1 - x0) / 2) * X + C ((x0 + x1) / 2)))
    (2 / (x1 - x0) * x - (x0 + x1) / (x1 - x0))

def pairMat (x0 x1 : ℝ) (φ ψ : ℕ → ℝ → ℝ) (j j' : ℕ) : ℝ := ∫ x in x0..x1, φ j x * ψ j' x

def bform (n : ℕ) (e e' : ℕ → ℝ) (M : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n, e j * e' j' * M j j'

def kform (n : ℕ) (c : ℕ → ℕ → ℝ) (M N : ℕ → ℕ → ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n, M j j' * bform n (c j) (c j') N

def tensorSum (n : ℕ) (c : ℕ → ℕ → ℝ) (α β : ℕ → ℝ → ℝ) (r z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, α j r * ∑ i ∈ Finset.range n, c j i * β i z

def powF (j : ℕ) (x : ℝ) : ℝ := x ^ j

def resF (x0 x1 lam : ℝ) (j : ℕ) : ℝ → ℝ := scaledRes x0 x1 lam (X ^ j)

def dresF (x0 x1 lam : ℝ) (j : ℕ) : ℝ → ℝ := deriv (resF x0 x1 lam j)

def diffF (x0 x1 lam : ℝ) (j : ℕ) (x : ℝ) : ℝ := x ^ j - resF x0 x1 lam j x

theorem scaledRes_props (x0 x1 lam : ℝ) (hlam : 0 < lam) (hx : x0 < x1) (p : ℝ[X]) :
    ContDiff ℝ 2 (scaledRes x0 x1 lam p) ∧ scaledRes x0 x1 lam p x0 = 0 ∧ scaledRes x0 x1 lam p x1 = 0 := by
  have hL : 0 < x1 - x0 := sub_pos.2 hx
  have hL' : x1 - x0 ≠ 0 := hL.ne'
  have hμ : 0 < lam * (x1 - x0) ^ 2 / 4 := by positivity
  obtain ⟨hC, h0, h1, -⟩ := intervalIdentity _ (p.comp (C ((x1 - x0) / 2) * X + C ((x0 + x1) / 2))) hμ
  refine ⟨?_, ?_, ?_⟩
  · show ContDiff ℝ 2 (fun x => intervalResolvent (lam * (x1 - x0) ^ 2 / 4)
      (p.comp (C ((x1 - x0) / 2) * X + C ((x0 + x1) / 2))) (2 / (x1 - x0) * x - (x0 + x1) / (x1 - x0)))
    exact hC.comp ((contDiff_const.mul contDiff_id).sub contDiff_const)
  · have e : 2 / (x1 - x0) * x0 - (x0 + x1) / (x1 - x0) = -1 := by field_simp; ring
    simp only [scaledRes, e, h0]
  · have e : 2 / (x1 - x0) * x1 - (x0 + x1) / (x1 - x0) = 1 := by field_simp; ring
    simp only [scaledRes, e, h1]

theorem res_sum (μ : ℝ) (s : Finset ℕ) (e : ℕ → ℝ) (p : ℕ → ℝ[X]) (x : ℝ) :
    intervalResolvent μ (∑ j ∈ s, e j • p j) x = ∑ j ∈ s, e j * intervalResolvent μ (p j) x := by
  classical
  refine Finset.induction_on s ?_ ?_
  · have h := resolvent_linear μ 0 0 0 0 x
    simpa using h
  · intro j s hj ih
    rw [Finset.sum_insert hj, Finset.sum_insert hj, ← ih]
    have h := resolvent_linear μ (e j) 1 (p j) (∑ j ∈ s, e j • p j) x
    simpa using h

theorem scaledRes_sum (x0 x1 lam : ℝ) (s : Finset ℕ) (e : ℕ → ℝ) (p : ℕ → ℝ[X]) (x : ℝ) :
    scaledRes x0 x1 lam (∑ j ∈ s, e j • p j) x = ∑ j ∈ s, e j * scaledRes x0 x1 lam (p j) x := by
  simp only [scaledRes, Polynomial.sum_comp, Polynomial.smul_comp]
  exact res_sum _ _ _ _ _

theorem scaledRes_pair (x0 x1 lam : ℝ) (hlam : 0 < lam) (hx : x0 < x1) (p g : ℝ[X]) :
    (∫ x in x0..x1, scaledRes x0 x1 lam p x * g.eval x)
      = (∫ x in x0..x1, scaledRes x0 x1 lam p x * scaledRes x0 x1 lam g x)
        + lam⁻¹ * ∫ x in x0..x1, deriv (scaledRes x0 x1 lam p) x * deriv (scaledRes x0 x1 lam g) x := by
  have hL : 0 < x1 - x0 := sub_pos.2 hx
  have hL' : x1 - x0 ≠ 0 := hL.ne'
  have hμ : 0 < lam * (x1 - x0) ^ 2 / 4 := by positivity
  have hc0 : 2 / (x1 - x0) ≠ 0 := by positivity
  set L := x1 - x0 with hLdef
  set μ := lam * L ^ 2 / 4 with hμdef
  set c := 2 / L with hcdef
  set d := (x0 + x1) / L with hddef
  set pt := p.comp (C (L / 2) * X + C ((x0 + x1) / 2)) with hptdef
  set gt := g.comp (C (L / 2) * X + C ((x0 + x1) / 2)) with hgtdef
  obtain ⟨hCp, -, -, -⟩ := intervalIdentity μ pt hμ
  obtain ⟨hCg, -, -, -⟩ := intervalIdentity μ gt hμ
  have hpair := resolvent_pair intervalIdentity μ hμ pt gt
  have hg : ∀ r, g.eval r = gt.eval (c * r - d) := by
    intro r
    simp only [hgtdef, eval_comp, eval_add, eval_mul, eval_C, eval_X]
    congr 1
    rw [hcdef, hddef]
    field_simp
    ring
  have hWp : scaledRes x0 x1 lam p = fun r => intervalResolvent μ pt (c * r - d) := rfl
  have hWg : scaledRes x0 x1 lam g = fun r => intervalResolvent μ gt (c * r - d) := rfl
  have hdR : ∀ (f : ℝ → ℝ), ContDiff ℝ 2 f → ∀ r, deriv (fun s => f (c * s - d)) r = c * deriv f (c * r - d) := by
    intro f hf r
    have hd : DifferentiableAt ℝ f (c * r - d) := (hf.differentiable (by norm_num)).differentiableAt
    have h2 : HasDerivAt (fun s => c * s - d) c r := by
      simpa using ((hasDerivAt_id r).const_mul c).sub_const d
    have h3 := hd.hasDerivAt.comp r h2
    rw [show (fun s => f (c * s - d)) = f ∘ (fun s => c * s - d) from rfl, h3.deriv]
    ring
  have hcv : ∀ f : ℝ → ℝ, ∫ r in x0..x1, f (c * r - d) = (L / 2) * ∫ x in (-1 : ℝ)..1, f x := by
    intro f
    rw [intervalIntegral.integral_comp_mul_sub (f := f) hc0 d, smul_eq_mul]
    have e0 : c * x0 - d = -1 := by rw [hcdef, hddef]; field_simp; ring
    have e1 : c * x1 - d = 1 := by rw [hcdef, hddef]; field_simp; ring
    rw [e0, e1, hcdef]
    congr 1
    field_simp
  have i1 : ∫ x in x0..x1, scaledRes x0 x1 lam p x * g.eval x
      = (L / 2) * ∫ x in (-1 : ℝ)..1, intervalResolvent μ pt x * gt.eval x := by
    rw [← hcv (fun x => intervalResolvent μ pt x * gt.eval x), hWp]
    congr 1
    funext r
    rw [hg r]
  have i2 : ∫ x in x0..x1, scaledRes x0 x1 lam p x * scaledRes x0 x1 lam g x
      = (L / 2) * ∫ x in (-1 : ℝ)..1, intervalResolvent μ pt x * intervalResolvent μ gt x := by
    rw [← hcv (fun x => intervalResolvent μ pt x * intervalResolvent μ gt x), hWp, hWg]
  have i3 : ∫ x in x0..x1, deriv (scaledRes x0 x1 lam p) x * deriv (scaledRes x0 x1 lam g) x
      = c ^ 2 * ((L / 2) * ∫ x in (-1 : ℝ)..1,
          deriv (intervalResolvent μ pt) x * deriv (intervalResolvent μ gt) x) := by
    rw [← hcv (fun x => deriv (intervalResolvent μ pt) x * deriv (intervalResolvent μ gt) x),
      ← intervalIntegral.integral_const_mul, hWp, hWg]
    congr 1
    funext r
    rw [hdR _ hCp r, hdR _ hCg r]
    ring
  have hcμ : lam⁻¹ * c ^ 2 = μ⁻¹ := by
    rw [hcdef, hμdef]
    field_simp
    norm_num
  rw [i1, i2, i3, hpair]
  rw [← hcμ]
  ring

theorem pairMat_symm (x0 x1 : ℝ) (φ ψ : ℕ → ℝ → ℝ) (j j' : ℕ) :
    pairMat x0 x1 φ ψ j j' = pairMat x0 x1 ψ φ j' j := by
  simp only [pairMat]
  congr 1
  funext x
  ring

theorem integral_bform (x0 x1 : ℝ) (n : ℕ) (e e' : ℕ → ℝ) (φ ψ : ℕ → ℝ → ℝ)
    (hφ : ∀ j, Continuous (φ j)) (hψ : ∀ j, Continuous (ψ j)) :
    (∫ x in x0..x1, (∑ j ∈ Finset.range n, e j * φ j x) * (∑ j ∈ Finset.range n, e' j * ψ j x))
      = bform n e e' (pairMat x0 x1 φ ψ) := by
  simp only [bform, pairMat, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j' _ => ?_
      rw [← intervalIntegral.integral_const_mul]
      congr 1
      funext x
      ring
    · intro j' _
      exact (((continuous_const.mul (hφ j)).mul (continuous_const.mul (hψ j'))).intervalIntegrable _ _)
  · intro j _
    exact (continuous_finsetSum _ fun j' _ =>
      ((continuous_const.mul (hφ j)).mul (continuous_const.mul (hψ j')))).intervalIntegrable _ _

theorem bform_pairMat_nonneg (x0 x1 : ℝ) (hx : x0 ≤ x1) (n : ℕ) (e : ℕ → ℝ) (φ : ℕ → ℝ → ℝ)
    (hφ : ∀ j, Continuous (φ j)) : 0 ≤ bform n e e (pairMat x0 x1 φ φ) := by
  rw [← integral_bform x0 x1 n e e φ φ hφ hφ]
  exact intervalIntegral.integral_nonneg hx fun x _ => mul_self_nonneg _

theorem kform_symm (n : ℕ) (c : ℕ → ℕ → ℝ) (M N : ℕ → ℕ → ℝ) :
    kform n c M N = kform n (fun i j => c j i) N M := by
  simp only [kform, bform, Finset.mul_sum]
  calc _ = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range n, ∑ j' ∈ Finset.range n, ∑ i' ∈ Finset.range n,
        M j j' * (c j i * c j' i' * N i i') := Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n, ∑ i' ∈ Finset.range n,
        M j j' * (c j i * c j' i' * N i i') := Finset.sum_comm
    _ = ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ i' ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        M j j' * (c j i * c j' i' * N i i') :=
          Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = ∑ i ∈ Finset.range n, ∑ i' ∈ Finset.range n, ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
        M j j' * (c j i * c j' i' * N i i') := Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ =>
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring

theorem kform_lin3 (n : ℕ) (c : ℕ → ℕ → ℝ) (A0 A1 A2 C0 C1 C2 : ℕ → ℕ → ℝ) (x0 x1 x2 y0 y1 y2 : ℝ) :
    kform n c (fun j j' => x0 * A0 j j' + x1 * A1 j j' + x2 * A2 j j')
        (fun i i' => y0 * C0 i i' + y1 * C1 i i' + y2 * C2 i i')
      = x0 * y0 * kform n c A0 C0 + x0 * y1 * kform n c A0 C1 + x0 * y2 * kform n c A0 C2
        + x1 * y0 * kform n c A1 C0 + x1 * y1 * kform n c A1 C1 + x1 * y2 * kform n c A1 C2
        + x2 * y0 * kform n c A2 C0 + x2 * y1 * kform n c A2 C1 + x2 * y2 * kform n c A2 C2 := by
  simp only [kform, bform, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ =>
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => by ring

theorem bform_lin3 (n : ℕ) (e : ℕ → ℝ) (A0 A1 A2 : ℕ → ℕ → ℝ) (x0 x1 x2 : ℝ) :
    bform n e e (fun j j' => x0 * A0 j j' + x1 * A1 j j' + x2 * A2 j j')
      = x0 * bform n e e A0 + x1 * bform n e e A1 + x2 * bform n e e A2 := by
  simp only [bform, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => by ring

end Internal.RectOff

end Breakdown.CellCert.Spectral

namespace Breakdown.CellCert.Spectral

open SteadyCert

namespace Internal.RectOff

open Internal.FieldWitness

theorem tensor_cont (n : ℕ) (c : ℕ → ℕ → ℝ) (α β : ℕ → ℝ → ℝ) (hα : ∀ j, Continuous (α j))
    (hβ : ∀ j, Continuous (β j)) : Continuous (Function.uncurry (tensorSum n c α β)) := by
  show Continuous fun p : ℝ × ℝ => ∑ j ∈ Finset.range n, α j p.1 * ∑ i ∈ Finset.range n, c j i * β i p.2
  exact continuous_finsetSum _ fun j _ => ((hα j).comp continuous_fst).mul
    (continuous_finsetSum _ fun i _ => continuous_const.mul ((hβ i).comp continuous_snd))

theorem iint_tensor (r0 r1 z0 z1 : ℝ) (n : ℕ) (c : ℕ → ℕ → ℝ) (α β α' β' : ℕ → ℝ → ℝ)
    (hα : ∀ j, Continuous (α j)) (hβ : ∀ j, Continuous (β j))
    (hα' : ∀ j, Continuous (α' j)) (hβ' : ∀ j, Continuous (β' j)) :
    (∫ r in r0..r1, ∫ z in z0..z1, tensorSum n c α β r z * tensorSum n c α' β' r z)
      = kform n c (pairMat r0 r1 α α') (pairMat z0 z1 β β') := by
  have hE : ∀ j, Continuous fun z => ∑ i ∈ Finset.range n, c j i * β i z :=
    fun j => continuous_finsetSum _ fun i _ => continuous_const.mul (hβ i)
  have hE' : ∀ j, Continuous fun z => ∑ i ∈ Finset.range n, c j i * β' i z :=
    fun j => continuous_finsetSum _ fun i _ => continuous_const.mul (hβ' i)
  have hG : ∀ j j', pairMat z0 z1 (fun j z => ∑ i ∈ Finset.range n, c j i * β i z)
      (fun j z => ∑ i ∈ Finset.range n, c j i * β' i z) j j' = bform n (c j) (c j') (pairMat z0 z1 β β') :=
    fun j j' => integral_bform z0 z1 n (c j) (c j') β β' hβ hβ'
  have inner : ∀ r, (∫ z in z0..z1, tensorSum n c α β r z * tensorSum n c α' β' r z)
      = ∑ j ∈ Finset.range n, ∑ j' ∈ Finset.range n,
          α j r * α' j' r * bform n (c j) (c j') (pairMat z0 z1 β β') := by
    intro r
    have h := integral_bform z0 z1 n (fun j => α j r) (fun j => α' j r)
      (fun j z => ∑ i ∈ Finset.range n, c j i * β i z) (fun j z => ∑ i ∈ Finset.range n, c j i * β' i z) hE hE'
    rw [bform] at h
    simp only [tensorSum]
    rw [h]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => congrArg _ (hG j j')
  simp only [inner]
  have hc : ∀ j j', Continuous fun r => α j r * α' j' r * bform n (c j) (c j') (pairMat z0 z1 β β') :=
    fun j j' => ((hα j).mul (hα' j')).mul continuous_const
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (continuous_finsetSum _ fun j' _ => hc j j').intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun j' _ => (hc j j').intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [intervalIntegral.integral_mul_const]
  rfl

theorem kform_nonneg (z0 z1 : ℝ) (hz : z0 ≤ z1) (n : ℕ) (c : ℕ → ℕ → ℝ) (M : ℕ → ℕ → ℝ)
    (hM : ∀ e, 0 ≤ bform n e e M) (β : ℕ → ℝ → ℝ) (hβ : ∀ j, Continuous (β j)) :
    0 ≤ kform n c M (pairMat z0 z1 β β) := by
  have hE : ∀ j, Continuous fun z => ∑ i ∈ Finset.range n, c j i * β i z :=
    fun j => continuous_finsetSum _ fun i _ => continuous_const.mul (hβ i)
  have hb : ∀ j j', bform n (c j) (c j') (pairMat z0 z1 β β)
      = ∫ z in z0..z1, (∑ i ∈ Finset.range n, c j i * β i z) * (∑ i ∈ Finset.range n, c j' i * β i z) :=
    fun j j' => (integral_bform z0 z1 n (c j) (c j') β β hβ hβ).symm
  have h1 : kform n c M (pairMat z0 z1 β β) = ∫ z in z0..z1,
      bform n (fun j => ∑ i ∈ Finset.range n, c j i * β i z) (fun j => ∑ i ∈ Finset.range n, c j i * β i z) M := by
    have hk : ∀ j j', Continuous fun z => ((∑ i ∈ Finset.range n, c j i * β i z)
        * ∑ i ∈ Finset.range n, c j' i * β i z) * M j j' :=
      fun j j' => ((hE j).mul (hE j')).mul continuous_const
    simp only [kform, hb]
    simp only [bform]
    rw [intervalIntegral.integral_finsetSum fun j _ =>
      (continuous_finsetSum _ fun j' _ => hk j j').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_finsetSum fun j' _ => (hk j j').intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [intervalIntegral.integral_mul_const]
    ring
  rw [h1]
  exact intervalIntegral.integral_nonneg hz fun z _ => hM _

theorem iint_sum {ι : Type*} (s : Finset ι) (r0 r1 z0 z1 : ℝ) (k : ι → ℝ) (F : ι → ℝ → ℝ → ℝ)
    (hF : ∀ m, Continuous (Function.uncurry (F m))) :
    (∫ r in r0..r1, ∫ z in z0..z1, ∑ m ∈ s, k m * F m r z)
      = ∑ m ∈ s, k m * ∫ r in r0..r1, ∫ z in z0..z1, F m r z := by
  have hi : ∀ m r, IntervalIntegrable (fun z => F m r z) volume z0 z1 :=
    fun m r => ((hF m).comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  have hc : ∀ m, Continuous fun r => ∫ z in z0..z1, F m r z :=
    fun m => intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (hF m) z0 z1
  have inner : ∀ r, (∫ z in z0..z1, ∑ m ∈ s, k m * F m r z) = ∑ m ∈ s, k m * ∫ z in z0..z1, F m r z := by
    intro r
    rw [intervalIntegral.integral_finsetSum fun m _ => (hi m r).const_mul (k m)]
    exact Finset.sum_congr rfl fun m _ => intervalIntegral.integral_const_mul _ _
  simp only [inner]
  rw [intervalIntegral.integral_finsetSum fun m _ =>
    (show Continuous fun r => k m * ∫ z in z0..z1, F m r z from continuous_const.mul (hc m)).intervalIntegrable _ _]
  exact Finset.sum_congr rfl fun m _ => intervalIntegral.integral_const_mul _ _

theorem cont_pow (j : ℕ) : Continuous (powF j) := continuous_pow j

theorem cert_bform (x0 x1 lam v : ℝ) (q : ℕ) (hlam : 0 < lam) (hx : x0 < x1)
    (hc : IntervalCertificate q (lam * (x1 - x0) ^ 2 / 4) v) (e : ℕ → ℝ) :
    bform (q + 1) e e (pairMat x0 x1 (diffF x0 x1 lam) (diffF x0 x1 lam))
        + lam⁻¹ * bform (q + 1) e e (pairMat x0 x1 (dresF x0 x1 lam) (dresF x0 x1 lam))
      ≤ v * bform (q + 1) e e (pairMat x0 x1 powF powF) := by
  set p : ℝ[X] := ∑ j ∈ Finset.range (q + 1), e j • X ^ j with hp
  have hpd : p.natDegree ≤ q := by
    refine natDegree_sum_le_of_forall_le _ _ fun j hj => (natDegree_smul_le _ _).trans ?_
    rw [natDegree_X_pow]
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have key := interval_scaled intervalIdentity q x0 x1 lam v hlam hx hc p hpd
  change (∫ r in x0..x1, (p.eval r - scaledRes x0 x1 lam p r) ^ 2)
      + lam⁻¹ * (∫ r in x0..x1, deriv (scaledRes x0 x1 lam p) r ^ 2) ≤ v * ∫ r in x0..x1, p.eval r ^ 2 at key
  have hcont : ∀ j, ContDiff ℝ 2 (resF x0 x1 lam j) := fun j => (scaledRes_props x0 x1 lam hlam hx _).1
  have hev : ∀ r, p.eval r = ∑ j ∈ Finset.range (q + 1), e j * powF j r := by
    intro r
    simp [hp, eval_finsetSum, powF]
  have hW : scaledRes x0 x1 lam p = fun r => ∑ j ∈ Finset.range (q + 1), e j * resF x0 x1 lam j r := by
    funext r
    exact scaledRes_sum x0 x1 lam _ e (fun j => X ^ j) r
  have hD : ∀ r, deriv (scaledRes x0 x1 lam p) r = ∑ j ∈ Finset.range (q + 1), e j * dresF x0 x1 lam j r := by
    intro r
    rw [hW]
    have h : HasDerivAt (fun r => ∑ j ∈ Finset.range (q + 1), e j * resF x0 x1 lam j r)
        (∑ j ∈ Finset.range (q + 1), e j * dresF x0 x1 lam j r) r :=
      HasDerivAt.fun_sum fun j _ =>
        (((hcont j).differentiable (by norm_num)).differentiableAt.hasDerivAt).const_mul (e j)
    exact h.deriv
  simp only [hD] at key
  simp only [hev, hW] at key
  have cr : ∀ j, Continuous (resF x0 x1 lam j) := fun j => (hcont j).continuous
  have cd : ∀ j, Continuous (dresF x0 x1 lam j) := fun j => (hcont j).continuous_deriv (by norm_num)
  have cf : ∀ j, Continuous (diffF x0 x1 lam j) := fun j => (continuous_pow j).sub (cr j)
  have i1 : (∫ r in x0..x1, (∑ j ∈ Finset.range (q + 1), e j * powF j r
      - ∑ j ∈ Finset.range (q + 1), e j * resF x0 x1 lam j r) ^ 2)
      = bform (q + 1) e e (pairMat x0 x1 (diffF x0 x1 lam) (diffF x0 x1 lam)) := by
    rw [← integral_bform x0 x1 (q + 1) e e _ _ cf cf]
    congr 1
    funext r
    simp only [diffF, powF, mul_sub, Finset.sum_sub_distrib]
    ring
  have i2 : (∫ r in x0..x1, (∑ j ∈ Finset.range (q + 1), e j * dresF x0 x1 lam j r) ^ 2)
      = bform (q + 1) e e (pairMat x0 x1 (dresF x0 x1 lam) (dresF x0 x1 lam)) := by
    rw [← integral_bform x0 x1 (q + 1) e e _ _ cd cd]
    congr 1
    funext r
    ring
  have i3 : (∫ r in x0..x1, (∑ j ∈ Finset.range (q + 1), e j * powF j r) ^ 2)
      = bform (q + 1) e e (pairMat x0 x1 powF powF) := by
    rw [← integral_bform x0 x1 (q + 1) e e _ _ cont_pow cont_pow]
    congr 1
    funext r
    ring
  rw [i1, i2, i3] at key
  exact key

theorem pairMat_pow_res (x0 x1 lam : ℝ) (hlam : 0 < lam) (hx : x0 < x1) (j j' : ℕ) :
    pairMat x0 x1 powF (resF x0 x1 lam) j j'
      = lam⁻¹ * pairMat x0 x1 (dresF x0 x1 lam) (dresF x0 x1 lam) j j'
        + pairMat x0 x1 (resF x0 x1 lam) (resF x0 x1 lam) j j' := by
  have h := scaledRes_pair x0 x1 lam hlam hx (X ^ j') (X ^ j)
  simp only [eval_pow, eval_X] at h
  have e1 : pairMat x0 x1 powF (resF x0 x1 lam) j j'
      = ∫ x in x0..x1, scaledRes x0 x1 lam (X ^ j') x * x ^ j := by
    simp only [pairMat, powF, resF]
    congr 1
    funext x
    ring
  have e2 : pairMat x0 x1 (resF x0 x1 lam) (resF x0 x1 lam) j j'
      = ∫ x in x0..x1, scaledRes x0 x1 lam (X ^ j') x * scaledRes x0 x1 lam (X ^ j) x := by
    simp only [pairMat, resF]
    congr 1
    funext x
    ring
  have e3 : pairMat x0 x1 (dresF x0 x1 lam) (dresF x0 x1 lam) j j'
      = ∫ x in x0..x1, deriv (scaledRes x0 x1 lam (X ^ j')) x * deriv (scaledRes x0 x1 lam (X ^ j)) x := by
    simp only [pairMat, dresF, resF]
    congr 1
    funext x
    ring
  rw [e1, e2, e3, h]
  ring

theorem pairMat_pow_pow (x0 x1 lam : ℝ) (hlam : 0 < lam) (hx : x0 < x1) (j j' : ℕ) :
    pairMat x0 x1 powF powF j j'
      = pairMat x0 x1 (diffF x0 x1 lam) (diffF x0 x1 lam) j j'
        + 2 * lam⁻¹ * pairMat x0 x1 (dresF x0 x1 lam) (dresF x0 x1 lam) j j'
        + pairMat x0 x1 (resF x0 x1 lam) (resF x0 x1 lam) j j' := by
  have cr : ∀ j, Continuous (resF x0 x1 lam j) :=
    fun j => (scaledRes_props x0 x1 lam hlam hx _).1.continuous
  have h1 := pairMat_pow_res x0 x1 lam hlam hx j j'
  have h2 := pairMat_pow_res x0 x1 lam hlam hx j' j
  have s1 := pairMat_symm x0 x1 (resF x0 x1 lam) powF j j'
  have s2 := pairMat_symm x0 x1 (dresF x0 x1 lam) (dresF x0 x1 lam) j' j
  have s3 := pairMat_symm x0 x1 (resF x0 x1 lam) (resF x0 x1 lam) j' j
  have hd : pairMat x0 x1 (diffF x0 x1 lam) (diffF x0 x1 lam) j j'
      = pairMat x0 x1 powF powF j j' - pairMat x0 x1 powF (resF x0 x1 lam) j j'
        - pairMat x0 x1 (resF x0 x1 lam) powF j j' + pairMat x0 x1 (resF x0 x1 lam) (resF x0 x1 lam) j j' := by
    simp only [pairMat, diffF, powF]
    have i1 : IntervalIntegrable (fun x => x ^ j * x ^ j') volume x0 x1 :=
      ((continuous_pow j).mul (continuous_pow j')).intervalIntegrable _ _
    have i2 : IntervalIntegrable (fun x => x ^ j * resF x0 x1 lam j' x) volume x0 x1 :=
      ((continuous_pow j).mul (cr j')).intervalIntegrable _ _
    have i3 : IntervalIntegrable (fun x => resF x0 x1 lam j x * x ^ j') volume x0 x1 :=
      ((cr j).mul (continuous_pow j')).intervalIntegrable _ _
    have i4 : IntervalIntegrable (fun x => resF x0 x1 lam j x * resF x0 x1 lam j' x) volume x0 x1 :=
      ((cr j).mul (cr j')).intervalIntegrable _ _
    rw [← intervalIntegral.integral_sub i1 i2, ← intervalIntegral.integral_sub (i1.sub i2) i3,
      ← intervalIntegral.integral_add ((i1.sub i2).sub i3) i4]
    congr 1
    funext x
    ring
  rw [s2, s3] at h2
  linear_combination -hd + h1 + s1 + h2

theorem twoVar_expand (q : ℕ) (P : ℝ[X][X]) (hP : P.natDegree ≤ q) (hPc : ∀ j, (P.coeff j).natDegree ≤ q)
    (r z : ℝ) : twoVarEval P r z = tensorSum (q + 1) (fun j i => (P.coeff j).coeff i) powF powF r z := by
  have h1 : (P.map (evalRingHom z)).natDegree < q + 1 :=
    lt_of_le_of_lt (natDegree_map_le.trans hP) (Nat.lt_succ_self q)
  rw [twoVarEval, eval_eq_sum_range' h1]
  simp only [tensorSum, powF]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_map, coe_evalRingHom, eval_eq_sum_range' (lt_of_le_of_lt (hPc j) (Nat.lt_succ_self q))]
  ring

end Internal.RectOff

end Breakdown.CellCert.Spectral

namespace Breakdown.CellCert.Spectral

open SteadyCert Internal.RectOff

theorem rectOff_holds : RectOffStatement := by
  intro q r0 r1 z0 z1 lam vr vz a hlam hr hz ha hcr hcz P hP hPc
  have hla : 0 < lam + a := by linarith
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ, κ = lam / (lam + a) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by rw [hκ]; exact div_pos hlam hla
  have hκ1 : κ ≤ 1 := by rw [hκ, div_le_one hla]; linarith
  have hρ : ratioFn lam a = 1 - κ := by
    rw [ratioFn, hκ]
    field_simp
    ring
  have hκw : κ ^ 2 + lam⁻¹ * (a * κ ^ 2) = κ := by
    rw [hκ]
    field_simp
  have h1κ : 0 ≤ 1 - κ := by linarith
  have h2κ : 0 ≤ 2 - κ := by linarith
  have h3κ : 0 ≤ 3 - 2 * κ := by linarith
  have h4κ : 0 ≤ 4 - 2 * κ := by linarith
  have h5κ : 0 ≤ 1 - κ ^ 2 := by nlinarith
  have hTV := twoVar_expand q P hP hPc
  generalize hc : (fun j i => (P.coeff j).coeff i : ℕ → ℕ → ℝ) = c at hTV
  have hrC : ∀ j, ContDiff ℝ 2 (resF r0 r1 lam j) := fun j => (scaledRes_props r0 r1 lam hlam hr _).1
  have hzC : ∀ j, ContDiff ℝ 2 (resF z0 z1 lam j) := fun j => (scaledRes_props z0 z1 lam hlam hz _).1
  have hr0 : ∀ j, resF r0 r1 lam j r0 = 0 := fun j => (scaledRes_props r0 r1 lam hlam hr _).2.1
  have hr1 : ∀ j, resF r0 r1 lam j r1 = 0 := fun j => (scaledRes_props r0 r1 lam hlam hr _).2.2
  have hz0 : ∀ j, resF z0 z1 lam j z0 = 0 := fun j => (scaledRes_props z0 z1 lam hlam hz _).2.1
  have hz1 : ∀ j, resF z0 z1 lam j z1 = 0 := fun j => (scaledRes_props z0 z1 lam hlam hz _).2.2
  have crr : ∀ j, Continuous (resF r0 r1 lam j) := fun j => (hrC j).continuous
  have crz : ∀ j, Continuous (resF z0 z1 lam j) := fun j => (hzC j).continuous
  have cdr : ∀ j, Continuous (dresF r0 r1 lam j) := fun j => (hrC j).continuous_deriv (by norm_num)
  have cdz : ∀ j, Continuous (dresF z0 z1 lam j) := fun j => (hzC j).continuous_deriv (by norm_num)
  have cfr : ∀ j, Continuous (diffF r0 r1 lam j) := fun j => (continuous_pow j).sub (crr j)
  have cfz : ∀ j, Continuous (diffF z0 z1 lam j) := fun j => (continuous_pow j).sub (crz j)
  refine ⟨fun r z => κ * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show ContDiff ℝ 1 fun p : ℝ × ℝ => κ * ∑ j ∈ Finset.range (q + 1), resF r0 r1 lam j p.1
        * ∑ i ∈ Finset.range (q + 1), c j i * resF z0 z1 lam i p.2
    exact contDiff_const.mul (ContDiff.sum fun j _ => (((hrC j).of_le (by norm_num)).comp contDiff_fst).mul
      (ContDiff.sum fun i _ => contDiff_const.mul (((hzC i).of_le (by norm_num)).comp contDiff_snd)))
  · intro z
    simp [tensorSum, hr0]
  · intro z
    simp [tensorSum, hr1]
  · intro r
    simp [tensorSum, hz0]
  · intro r
    simp [tensorSum, hz1]
  have hDr : ∀ r z, deriv (fun s => κ * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) s z) r = κ * tensorSum (q + 1) c (dresF r0 r1 lam) (resF z0 z1 lam) r z := by
    intro r z
    have h : HasDerivAt (fun s => κ * ∑ j ∈ Finset.range (q + 1), resF r0 r1 lam j s
          * ∑ i ∈ Finset.range (q + 1), c j i * resF z0 z1 lam i z)
        (κ * ∑ j ∈ Finset.range (q + 1), dresF r0 r1 lam j r
          * ∑ i ∈ Finset.range (q + 1), c j i * resF z0 z1 lam i z) r :=
      (HasDerivAt.fun_sum fun j _ =>
        (((hrC j).differentiable (by norm_num)).differentiableAt.hasDerivAt).mul_const _).const_mul κ
    exact h.deriv
  have hDz : ∀ r z, deriv (fun t => κ * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r t) z = κ * tensorSum (q + 1) c (resF r0 r1 lam) (dresF z0 z1 lam) r z := by
    intro r z
    have h : HasDerivAt (fun t => κ * ∑ j ∈ Finset.range (q + 1), resF r0 r1 lam j r
          * ∑ i ∈ Finset.range (q + 1), c j i * resF z0 z1 lam i t)
        (κ * ∑ j ∈ Finset.range (q + 1), resF r0 r1 lam j r
          * ∑ i ∈ Finset.range (q + 1), c j i * dresF z0 z1 lam i z) z :=
      (HasDerivAt.fun_sum fun j _ => (HasDerivAt.fun_sum fun i _ =>
        (((hzC i).differentiable (by norm_num)).differentiableAt.hasDerivAt).const_mul (c j i)).const_mul
          (resF r0 r1 lam j r)).const_mul κ
    exact h.deriv
  have cf := tensor_cont (q + 1) c powF powF cont_pow cont_pow
  have cw := tensor_cont (q + 1) c _ _ crr crz
  have cu := tensor_cont (q + 1) c _ _ cdr crz
  have cv := tensor_cont (q + 1) c _ _ crr cdz
  have hI := iint_sum (Finset.univ : Finset (Fin 5)) r0 r1 z0 z1 ![1, -2 * κ, κ, lam⁻¹ * κ ^ 2, lam⁻¹ * κ ^ 2]
    ![fun r z => tensorSum (q + 1) c powF powF r z * tensorSum (q + 1) c powF powF r z,
      fun r z => tensorSum (q + 1) c powF powF r z * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z,
      fun r z => tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z,
      fun r z => tensorSum (q + 1) c (dresF r0 r1 lam) (resF z0 z1 lam) r z * tensorSum (q + 1) c (dresF r0 r1 lam) (resF z0 z1 lam) r z,
      fun r z => tensorSum (q + 1) c (resF r0 r1 lam) (dresF z0 z1 lam) r z * tensorSum (q + 1) c (resF r0 r1 lam) (dresF z0 z1 lam) r z] (by
        intro m
        fin_cases m
        · exact cf.mul cf
        · exact cf.mul cw
        · exact cw.mul cw
        · exact cu.mul cu
        · exact cv.mul cv)
  simp only [Fin.sum_univ_five, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.head_cons, Matrix.tail_cons] at hI
  rw [iint_tensor r0 r1 z0 z1 (q + 1) c _ _ _ _ cont_pow cont_pow cont_pow cont_pow,
    iint_tensor r0 r1 z0 z1 (q + 1) c _ _ _ _ cont_pow cont_pow crr crz,
    iint_tensor r0 r1 z0 z1 (q + 1) c _ _ _ _ crr crz crr crz,
    iint_tensor r0 r1 z0 z1 (q + 1) c _ _ _ _ cdr crz cdr crz,
    iint_tensor r0 r1 z0 z1 (q + 1) c _ _ _ _ crr cdz crr cdz] at hI
  have hRHS : (∫ r in r0..r1, ∫ z in z0..z1, twoVarEval P r z ^ 2) = kform (q + 1) c (pairMat r0 r1 powF powF) (pairMat z0 z1 powF powF) := by
    rw [← iint_tensor r0 r1 z0 z1 (q + 1) c _ _ _ _ cont_pow cont_pow cont_pow cont_pow]
    congr 1
    funext r
    congr 1
    funext z
    rw [hTV]
    ring
  have hNr : (pairMat r0 r1 powF powF) = fun j j' => 1 * (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) j j' + (2 * lam⁻¹) * (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) j j' + 1 * (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) j j' := by
    funext j j'
    rw [pairMat_pow_pow r0 r1 lam hlam hr j j']
    ring
  have hNz : (pairMat z0 z1 powF powF) = fun j j' => 1 * (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) j j' + (2 * lam⁻¹) * (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) j j' + 1 * (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) j j' := by
    funext j j'
    rw [pairMat_pow_pow z0 z1 lam hlam hz j j']
    ring
  have hGr : (pairMat r0 r1 powF (resF r0 r1 lam)) = fun j j' => 0 * (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) j j' + lam⁻¹ * (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) j j' + 1 * (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) j j' := by
    funext j j'
    rw [pairMat_pow_res r0 r1 lam hlam hr j j']
    ring
  have hGz : (pairMat z0 z1 powF (resF z0 z1 lam)) = fun j j' => 0 * (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) j j' + lam⁻¹ * (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) j j' + 1 * (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) j j' := by
    funext j j'
    rw [pairMat_pow_res z0 z1 lam hlam hz j j']
    ring
  have hMr : ∀ e, 0 ≤ bform (q + 1) e e (fun j j' => (vr - 1) * (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) j j' + (2 * lam⁻¹ * vr - lam⁻¹) * (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) j j' + vr * (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) j j') := by
    intro e
    have h := cert_bform r0 r1 lam vr q hlam hr hcr e
    rw [hNr, bform_lin3] at h
    rw [bform_lin3]
    linarith
  have hMz : ∀ e, 0 ≤ bform (q + 1) e e (fun j j' => (vz - 1) * (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) j j' + (2 * lam⁻¹ * vz - lam⁻¹) * (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) j j' + vz * (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) j j') := by
    intro e
    have h := cert_bform z0 z1 lam vz q hlam hz hcz e
    rw [hNz, bform_lin3] at h
    rw [bform_lin3]
    linarith
  have hCr : 0 ≤ kform (q + 1) c (fun j j' => (vr - 1) * (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) j j' + (2 * lam⁻¹ * vr - lam⁻¹) * (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) j j' + vr * (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) j j') (pairMat z0 z1 powF powF) := kform_nonneg z0 z1 hz.le (q + 1) c _ hMr _ cont_pow
  have hCz : 0 ≤ kform (q + 1) c (pairMat r0 r1 powF powF) (fun j j' => (vz - 1) * (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) j j' + (2 * lam⁻¹ * vz - lam⁻¹) * (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) j j' + vz * (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) j j') := by
    rw [kform_symm]
    exact kform_nonneg r0 r1 hr.le (q + 1) _ _ hMz _ cont_pow
  rw [hNz, kform_lin3] at hCr
  rw [hNr, kform_lin3] at hCz
  have e1 : kform (q + 1) c (pairMat r0 r1 powF powF) (pairMat z0 z1 powF powF) = kform (q + 1) c (fun j j' => 1 * (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) j j' + (2 * lam⁻¹) * (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) j j' + 1 * (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) j j') (fun j j' => 1 * (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) j j' + (2 * lam⁻¹) * (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) j j' + 1 * (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) j j') := by
    rw [← hNr, ← hNz]
  rw [kform_lin3] at e1
  have e2 : kform (q + 1) c (pairMat r0 r1 powF (resF r0 r1 lam)) (pairMat z0 z1 powF (resF z0 z1 lam)) = kform (q + 1) c (fun j j' => 0 * (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) j j' + lam⁻¹ * (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) j j' + 1 * (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) j j') (fun j j' => 0 * (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) j j' + lam⁻¹ * (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) j j' + 1 * (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) j j') := by
    rw [← hGr, ← hGz]
  rw [kform_lin3] at e2
  have m00 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ cfr) _ cfz
  have m01 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ cfr) _ cdz
  have m02 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ cfr) _ crz
  have m10 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ cdr) _ cfz
  have m11 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ cdr) _ cdz
  have m12 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ cdr) _ crz
  have m20 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ crr) _ cfz
  have m21 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ crr) _ cdz
  have m22 : 0 ≤ kform (q + 1) c (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) :=
    kform_nonneg z0 z1 hz.le (q + 1) c _ (fun e => bform_pairMat_nonneg r0 r1 hr.le (q + 1) e _ crr) _ crz
  have p10 : 0 ≤ (lam⁻¹ * (3 - 2 * κ)) * kform (q + 1) c (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) := mul_nonneg (by positivity) m10
  have p11 : 0 ≤ (lam⁻¹ ^ 2 * (4 - 2 * κ)) * kform (q + 1) c (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) := mul_nonneg (by positivity) m11
  have p12 : 0 ≤ (lam⁻¹ * (1 - κ ^ 2)) * kform (q + 1) c (pairMat r0 r1 (dresF r0 r1 lam) (dresF r0 r1 lam)) (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) := mul_nonneg (by positivity) m12
  have p20 : 0 ≤ (1 - κ) * kform (q + 1) c (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) := mul_nonneg (by positivity) m20
  have p21 : 0 ≤ (lam⁻¹ * (1 - κ ^ 2)) * kform (q + 1) c (pairMat r0 r1 (resF r0 r1 lam) (resF r0 r1 lam)) (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) := mul_nonneg (by positivity) m21
  have p00 : 0 ≤ (2 - κ) * kform (q + 1) c (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) (pairMat z0 z1 (diffF z0 z1 lam) (diffF z0 z1 lam)) := mul_nonneg (by positivity) m00
  have p01 : 0 ≤ (lam⁻¹ * (3 - 2 * κ)) * kform (q + 1) c (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) (pairMat z0 z1 (dresF z0 z1 lam) (dresF z0 z1 lam)) := mul_nonneg (by positivity) m01
  have p02 : 0 ≤ (1 - κ) * kform (q + 1) c (pairMat r0 r1 (diffF r0 r1 lam) (diffF r0 r1 lam)) (pairMat z0 z1 (resF z0 z1 lam) (resF z0 z1 lam)) := mul_nonneg (by positivity) m02
  rw [hρ, hRHS]
  calc _ = ∫ r in r0..r1, ∫ z in z0..z1,
        (1 * (tensorSum (q + 1) c powF powF r z * tensorSum (q + 1) c powF powF r z)
          + -2 * κ * (tensorSum (q + 1) c powF powF r z * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z)
          + κ * (tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z)
          + lam⁻¹ * κ ^ 2 * (tensorSum (q + 1) c (dresF r0 r1 lam) (resF z0 z1 lam) r z * tensorSum (q + 1) c (dresF r0 r1 lam) (resF z0 z1 lam) r z)
          + lam⁻¹ * κ ^ 2 * (tensorSum (q + 1) c (resF r0 r1 lam) (dresF z0 z1 lam) r z * tensorSum (q + 1) c (resF r0 r1 lam) (dresF z0 z1 lam) r z)) := by
        congr 1
        funext r
        congr 1
        funext z
        rw [hTV, hDr, hDz]
        linear_combination (tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z * tensorSum (q + 1) c (resF r0 r1 lam) (resF z0 z1 lam) r z) * hκw
    _ = _ := hI
    _ ≤ _ := by
      linear_combination hCr + hCz + p00 + p01 + p02 + p10 + p11 + p12 + p20 + p21
        - (vr + vz - κ) * e1 - 2 * κ * e2

end Breakdown.CellCert.Spectral
