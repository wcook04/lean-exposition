import Breakdown.FracCell.DensitySlice

open MeasureTheory Real ComplexConjugate

noncomputable section

namespace Breakdown.FracInternal.CircleSliceCoupling

open CellCert CellAnalysis SteadyCert Assembly Breakdown.FracInternal.DensitySlice

def cf (m : ℕ) (n : ℤ) (h : ℝ → ℝ) : ℂ := circleCoeff (azimuth m n) (fun θ => (h θ : ℂ))

def Cst (f : ℤ → ℂ) (F : ℝ → ℝ) : Prop :=
  IntervalIntegrable F volume 0 (2 * π) ∧ HasSum f (((2 * π)⁻¹ * ∫ θ in (0 : ℝ)..(2 * π), F θ : ℝ) : ℂ)

theorem cst_add {f g : ℤ → ℂ} {F K : ℝ → ℝ} (h₁ : Cst f F) (h₂ : Cst g K) :
    Cst (fun n => f n + g n) (fun θ => F θ + K θ) := by
  refine ⟨h₁.1.add h₂.1, ?_⟩
  rw [intervalIntegral.integral_add h₁.1 h₂.1, mul_add, Complex.ofReal_add]
  exact h₁.2.add h₂.2

theorem cst_neg {f : ℤ → ℂ} {F : ℝ → ℝ} (h : Cst f F) : Cst (fun n => -f n) (fun θ => -F θ) := by
  refine ⟨h.1.neg, ?_⟩
  rw [intervalIntegral.integral_neg, mul_neg, Complex.ofReal_neg]
  exact h.2.neg

theorem cst_const (w : ℝ) {f : ℤ → ℂ} {F : ℝ → ℝ} (h : Cst f F) :
    Cst (fun n => (w : ℂ) * f n) (fun θ => w * F θ) := by
  refine ⟨h.1.const_mul w, ?_⟩
  rw [intervalIntegral.integral_const_mul, mul_left_comm, Complex.ofReal_mul]
  exact h.2.mul_left _

theorem cst_sum {ι : Type} (s : Finset ι) {f : ι → ℤ → ℂ} {F : ι → ℝ → ℝ} (h : ∀ i ∈ s, Cst (f i) (F i)) :
    Cst (fun n => ∑ i ∈ s, f i n) (fun θ => ∑ i ∈ s, F i θ) := by
  refine ⟨?_, ?_⟩
  · have := IntervalIntegrable.sum s fun i hi => (h i hi).1
    simpa [Finset.sum_fn] using this
  · rw [intervalIntegral.integral_finsetSum fun i hi => (h i hi).1, Finset.mul_sum, Complex.ofReal_sum]
    exact hasSum_sum fun i hi => (h i hi).2

theorem cst_atom {m : ℕ} (hm : 0 < m) {f h : ℝ → ℝ} (hf : IsCircleSliceRegular m f)
    (hfp : ∀ θ, f (θ + 2 * π) = f θ) (hh : MemLp h 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    Cst (fun n => conj (cf m n f) * cf m n h) (fun θ => f θ * h θ) := by
  refine ⟨product_integrable hf.1 hh, ?_⟩
  have H := Complex.hasSum_conj'.2 (entry_modes hm hf hh hfp)
  simpa only [map_mul, Complex.conj_conj, Complex.conj_ofReal, cf] using H

theorem bounded_memLp {w : ℝ → ℝ} (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * π))))
    {C : ℝ} (hC : ∀ θ, |w θ| ≤ C) {g : ℝ → ℝ} (hg : MemLp g 2 (volume.restrict (Set.Ioc 0 (2 * π)))) :
    MemLp (fun θ => w θ * g θ) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  refine (hg.const_mul C).of_le (hw.mul hg.1) (Filter.Eventually.of_forall fun θ => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right ((hC θ).trans (le_abs_self C)) (abs_nonneg _)

theorem bounded_memLp_self {w : ℝ → ℝ} (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioc 0 (2 * π))))
    {C : ℝ} (hC : ∀ θ, |w θ| ≤ C) : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π))) := by
  have : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (2 * π))) :=
    isFiniteMeasure_restrict.2 measure_Ioc_lt_top.ne
  exact MemLp.of_bound hw C (Filter.Eventually.of_forall fun θ => by simpa [Real.norm_eq_abs] using hC θ)

theorem atom_inner {m : ℕ} (hm : 0 < m) {w g : ℝ → ℝ}
    (hw : MemLp w 2 (volume.restrict (Set.Ioc 0 (2 * π)))) (hg : IsCircleSliceRegular m g)
    (hgp : ∀ θ, g (θ + 2 * π) = g θ) (n : ℤ) :
    HasSum (fun n' : ℤ => cf m (n - n') w * cf m n' g) (cf m n (fun θ => w θ * g θ)) := by
  have H := circle_conv hm (f := fun θ => (g θ : ℂ)) (w := fun θ => (w θ : ℂ)) hg.1.ofReal hw.ofReal
    (fun θ => by simp only [hgp]) (hg.2.mono fun θ hθ => by simp only [hθ]) n
  simp only [cf, Complex.ofReal_mul]
  convert H using 1
  funext n'
  ring

theorem cf_conj (m : ℕ) (n n' : ℤ) (w : ℝ → ℝ) : conj (cf m (n' - n) w) = cf m (n - n') w := by
  have hp : (0 : ℝ) ≤ 2 * π := circle_len_pos.le
  unfold cf circleCoeff
  rw [map_mul, intervalIntegral.integral_of_le hp, intervalIntegral.integral_of_le hp, ← integral_conj]
  congr 1
  · rw [show (1 / (2 * π) : ℂ) = ((1 / (2 * π) : ℝ) : ℂ) by push_cast; ring, Complex.conj_ofReal]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
    simp only [map_mul, ← Complex.exp_conj, map_neg, Complex.conj_ofReal, Complex.conj_I]
    congr 2
    unfold azimuth
    push_cast
    ring


theorem hs3 {f : Fin 3 → ℤ → ℂ} {a : Fin 3 → ℂ} (h : ∀ i, HasSum (f i) (a i)) :
    HasSum (fun n => ∑ i, f i n) (∑ i, a i) :=
  hasSum_sum fun i _ => h i

theorem cst3 {f : Fin 3 → ℤ → ℂ} {F : Fin 3 → ℝ → ℝ} (h : ∀ i, Cst (f i) (F i)) :
    Cst (fun n => ∑ i, f i n) (fun θ => ∑ i, F i θ) :=
  cst_sum Finset.univ fun i _ => h i

theorem cst_congr {f f' : ℤ → ℂ} {F F' : ℝ → ℝ} (h : Cst f F) (hf : ∀ n, f n = f' n)
    (hF : ∀ θ, F θ = F' θ) : Cst f' F' := by
  have e1 : f = f' := funext hf
  have e2 : F = F' := funext hF
  rw [← e1, ← e2]
  exact h

def curlRow (D : Fin 3 → Fin 3 → ℝ) (a : Fin 3) : ℝ := ∑ j : Fin 3, ∑ l : Fin 3, permSign a j l * D l j

def jSlice (D S G : Fin 3 → Fin 3 → ℝ) (V : Fin 3 → ℝ) : ℝ :=
  -(∑ a : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, permSign a j l * D l j) *
      ∑ b : Fin 3, S a b * (∑ j : Fin 3, ∑ l : Fin 3, permSign b j l * D l j))
    + ∑ i : Fin 3, ∑ l : Fin 3,
      (-(∑ j : Fin 3, permSign i l j * ∑ b : Fin 3, G j b * V b)
        + (1 / 2 : ℝ) * ∑ q : Fin 3, (∑ j : Fin 3, permSign i q j * V j) * G l q) * D i l

theorem jSlice_expand (D S G : Fin 3 → Fin 3 → ℝ) (V : Fin 3 → ℝ) :
    jSlice D S G V =
      -(∑ a : Fin 3, ∑ b : Fin 3, curlRow D a * (S a b * curlRow D b))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3, (-(1 / 2) * permSign i l j) * (D i l * (G j b * V b))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3, ((1 / 4) * permSign i q j) * (D i l * (G l q * V j))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3, (-(1 / 2) * permSign i l j) * (V b * (G j b * D i l))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3, ((1 / 4) * permSign i q j) * (V j * (G l q * D i l)) := by
  simp only [jSlice, curlRow, Fin.sum_univ_three]
  ring

theorem wave_expand (Sβ Gβ Gmβ s s' : Fin 3 → Fin 3 → ℂ) (v v' : Fin 3 → ℂ) :
    waveForm Sβ Gβ Gmβ s v s' v' =
      -(∑ a : Fin 3, ∑ b : Fin 3, conj (curlComp s a) * (Sβ a b * curlComp s' b))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
          ((-(1 / 2) * permSign i l j : ℝ) : ℂ) * (conj (s i l) * (Gβ j b * v' b))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3,
          (((1 / 4) * permSign i q j : ℝ) : ℂ) * (conj (s i l) * (Gβ l q * v' j))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3,
          ((-(1 / 2) * permSign i l j : ℝ) : ℂ) * (conj (v b) * (conj (Gmβ j b) * s' i l))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3,
          (((1 / 4) * permSign i q j : ℝ) : ℂ) * (conj (v j) * (conj (Gmβ l q) * s' i l)) := by
  simp only [waveForm, couplingMap, bracketMat, entryPairing, map_add, map_neg, map_mul,
    Complex.conj_ofReal, map_div₀, map_one, map_ofNat, Fin.sum_univ_three]
  push_cast
  ring

theorem curl_coeff {m : ℕ} (D : ℝ → Fin 3 → Fin 3 → ℝ)
    (hD : ∀ a b, IntervalIntegrable (fun θ => D θ a b) volume 0 (2 * π)) (n : ℤ) (a : Fin 3) :
    curlComp (fun a b => cf m n (fun θ => D θ a b)) a = cf m n (fun θ => curlRow (D θ) a) := by
  have hI : ∀ j, IntervalIntegrable (fun θ => ∑ l : Fin 3, permSign a j l * D θ l j) volume 0 (2 * π) := by
    intro j
    have := IntervalIntegrable.sum Finset.univ fun l _ => (hD l j).const_mul (permSign a j l)
    simpa [Finset.sum_fn] using this
  simp only [curlRow, cf, curlComp]
  rw [circleCoeff_sum _ _ (fun j θ => ∑ l : Fin 3, permSign a j l * D θ l j) fun j _ => hI j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [circleCoeff_sum _ _ (fun l θ => permSign a j l * D θ l j) fun l _ => (hD l j).const_mul _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [circleCoeff_const]

theorem hbase {m : ℕ} (hm : 0 < m) (D S G : ℝ → Fin 3 → Fin 3 → ℝ) (V : ℝ → Fin 3 → ℝ)
    (hD : ∀ a b, IsCircleSliceRegular m (fun θ => D θ a b)) (hDp : ∀ θ, D (θ + 2 * π) = D θ)
    (hV : ∀ a, IsCircleSliceRegular m (fun θ => V θ a)) (hVp : ∀ θ, V (θ + 2 * π) = V θ)
    (hS : ∀ a b, AEStronglyMeasurable (fun θ => S θ a b) (volume.restrict (Set.Ioc 0 (2 * π))))
    (hG : ∀ a b, AEStronglyMeasurable (fun θ => G θ a b) (volume.restrict (Set.Ioc 0 (2 * π))))
    (C : ℝ) (hC : ∀ θ a b, |S θ a b| ≤ C ∧ |G θ a b| ≤ C) :
    Cst (fun n => ∑' n' : ℤ, waveForm (fun a b => cf m (n - n') (fun θ => S θ a b))
        (fun a b => cf m (n - n') (fun θ => G θ a b)) (fun a b => cf m (n' - n) (fun θ => G θ a b))
        (fun a b => cf m n (fun θ => D θ a b)) (fun a => cf m n (fun θ => V θ a))
        (fun a b => cf m n' (fun θ => D θ a b)) (fun a => cf m n' (fun θ => V θ a)))
      (fun θ => jSlice (D θ) (S θ) (G θ) (V θ)) := by
  have rK : ∀ a, IsCircleSliceRegular m (fun θ => curlRow (D θ) a) := fun a =>
    regular_sum _ fun j _ => regular_sum _ fun l _ => regular_const _ (hD l j)
  have pK : ∀ a θ, curlRow (D (θ + 2 * π)) a = curlRow (D θ) a := fun a θ => by rw [hDp]
  have pD : ∀ a b θ, D (θ + 2 * π) a b = D θ a b := fun a b θ => by rw [hDp]
  have pV : ∀ a θ, V (θ + 2 * π) a = V θ a := fun a θ => by rw [hVp]
  have mS : ∀ a b, MemLp (fun θ => S θ a b) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := fun a b =>
    bounded_memLp_self (hS a b) (fun θ => (hC θ a b).1)
  have mG : ∀ a b, MemLp (fun θ => G θ a b) 2 (volume.restrict (Set.Ioc 0 (2 * π))) := fun a b =>
    bounded_memLp_self (hG a b) (fun θ => (hC θ a b).2)
  have cK : ∀ (n : ℤ) a, curlComp (fun a b => cf m n (fun θ => D θ a b)) a = cf m n (fun θ => curlRow (D θ) a) :=
    fun n a => curl_coeff D (fun a b => regular_integrable (hD a b)) n a
  have hin : ∀ n : ℤ, HasSum (fun n' : ℤ => waveForm (fun a b => cf m (n - n') (fun θ => S θ a b))
        (fun a b => cf m (n - n') (fun θ => G θ a b)) (fun a b => cf m (n' - n) (fun θ => G θ a b))
        (fun a b => cf m n (fun θ => D θ a b)) (fun a => cf m n (fun θ => V θ a))
        (fun a b => cf m n' (fun θ => D θ a b)) (fun a => cf m n' (fun θ => V θ a)))
      (-(∑ a : Fin 3, ∑ b : Fin 3, conj (cf m n (fun θ => curlRow (D θ) a)) *
          cf m n (fun θ => S θ a b * curlRow (D θ) b))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3, ((-(1 / 2) * permSign i l j : ℝ) : ℂ) *
          (conj (cf m n (fun θ => D θ i l)) * cf m n (fun θ => G θ j b * V θ b))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3, (((1 / 4) * permSign i q j : ℝ) : ℂ) *
          (conj (cf m n (fun θ => D θ i l)) * cf m n (fun θ => G θ l q * V θ j))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ j : Fin 3, ∑ b : Fin 3, ((-(1 / 2) * permSign i l j : ℝ) : ℂ) *
          (conj (cf m n (fun θ => V θ b)) * cf m n (fun θ => G θ j b * D θ i l))
      + ∑ i : Fin 3, ∑ l : Fin 3, ∑ q : Fin 3, ∑ j : Fin 3, (((1 / 4) * permSign i q j : ℝ) : ℂ) *
          (conj (cf m n (fun θ => V θ j)) * cf m n (fun θ => G θ l q * D θ i l))) := by
    intro n
    have H := (((((hs3 fun a => hs3 fun b => (atom_inner hm (mS a b) (rK b) (pK b) n).mul_left
        (conj (cf m n (fun θ => curlRow (D θ) a)))).neg).add
      (hs3 fun i => hs3 fun l => hs3 fun j => hs3 fun b =>
        ((atom_inner hm (mG j b) (hV b) (pV b) n).mul_left (conj (cf m n (fun θ => D θ i l)))).mul_left
          ((-(1 / 2) * permSign i l j : ℝ) : ℂ))).add
      (hs3 fun i => hs3 fun l => hs3 fun q => hs3 fun j =>
        ((atom_inner hm (mG l q) (hV j) (pV j) n).mul_left (conj (cf m n (fun θ => D θ i l)))).mul_left
          (((1 / 4) * permSign i q j : ℝ) : ℂ))).add
      (hs3 fun i => hs3 fun l => hs3 fun j => hs3 fun b =>
        ((atom_inner hm (mG j b) (hD i l) (pD i l) n).mul_left (conj (cf m n (fun θ => V θ b)))).mul_left
          ((-(1 / 2) * permSign i l j : ℝ) : ℂ))).add
      (hs3 fun i => hs3 fun l => hs3 fun q => hs3 fun j =>
        ((atom_inner hm (mG l q) (hD i l) (pD i l) n).mul_left (conj (cf m n (fun θ => V θ j)))).mul_left
          (((1 / 4) * permSign i q j : ℝ) : ℂ))
    convert H using 1
    all_goals first
      | rfl
      | (funext n'
         rw [wave_expand]
         simp only [cK, cf_conj])
  have hout := cst_add (cst_add (cst_add (cst_add
      (cst_neg (cst3 fun a => cst3 fun b => cst_atom hm (rK a) (pK a) (bounded_memLp (hS a b) (fun θ => (hC θ a b).1) (rK b).1)))
      (cst3 fun i => cst3 fun l => cst3 fun j => cst3 fun b => cst_const (-(1 / 2) * permSign i l j)
        (cst_atom hm (hD i l) (pD i l) (bounded_memLp (hG j b) (fun θ => (hC θ j b).2) (hV b).1))))
      (cst3 fun i => cst3 fun l => cst3 fun q => cst3 fun j => cst_const ((1 / 4) * permSign i q j)
        (cst_atom hm (hD i l) (pD i l) (bounded_memLp (hG l q) (fun θ => (hC θ l q).2) (hV j).1))))
      (cst3 fun i => cst3 fun l => cst3 fun j => cst3 fun b => cst_const (-(1 / 2) * permSign i l j)
        (cst_atom hm (hV b) (pV b) (bounded_memLp (hG j b) (fun θ => (hC θ j b).2) (hD i l).1))))
      (cst3 fun i => cst3 fun l => cst3 fun q => cst3 fun j => cst_const ((1 / 4) * permSign i q j)
        (cst_atom hm (hV j) (pV j) (bounded_memLp (hG l q) (fun θ => (hC θ l q).2) (hD i l).1)))
  exact cst_congr hout (fun n => ((hin n).tsum_eq).symm) (fun θ => (jSlice_expand _ _ _ _).symm)

end Breakdown.FracInternal.CircleSliceCoupling

namespace Breakdown.CellCert.CellAnalysis

open SteadyCert Assembly Breakdown.FracInternal.DensitySlice Breakdown.FracInternal.CircleSliceCoupling

theorem circleSliceCoupling_holds : CircleSliceCouplingStatement := by
  intro k N c hm x p hd
  obtain ⟨hV, hD, -, hSG, ⟨C, hC⟩, -, -⟩ := hd
  have key := hbase (m := c.order) (by omega) (fun θ => frameMat θ (x.2.1 (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)))
    (fun θ => frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2)))
    (fun θ => frameVec θ (x.1 (cylPoint p.1 θ p.2))) hD
    (fun θ => by funext a b; simp only [cyl_per, frameMat_add]) hV
    (fun θ => by
      funext a
      simp only [cyl_per, frameVec, radialUnit, angularUnit, Real.cos_add_two_pi, Real.sin_add_two_pi])
    (fun a b => (hSG a b).1) (fun a b => (hSG a b).2) C hC
  have ej : (fun θ => jForm (c.modelStrain (cylPoint p.1 θ p.2)) (c.modelCurlGrad (cylPoint p.1 θ p.2))
      (x.2.1 (cylPoint p.1 θ p.2)) (x.1 (cylPoint p.1 θ p.2))) = fun θ =>
      jSlice (frameMat θ (x.2.1 (cylPoint p.1 θ p.2))) (frameMat θ (c.modelStrain (cylPoint p.1 θ p.2)))
        (frameMat θ (c.modelCurlGrad (cylPoint p.1 θ p.2))) (frameVec θ (x.1 (cylPoint p.1 θ p.2))) :=
    funext fun θ => frame_jForm θ _ _ _ _
  rw [ej]
  refine ⟨key.1, ?_⟩
  have h2 := congrArg Complex.re key.2.tsum_eq
  rw [Complex.ofReal_re] at h2
  have h3 : modeCoupling c x p = _ := h2
  rw [h3, ← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul]

end Breakdown.CellCert.CellAnalysis

