import Breakdown.FracCert.StHeldParts
import Breakdown.FracCert.StQuadratic
import Breakdown.FracCert.StGradientAdd

open scoped ContDiff ENNReal
open MeasureTheory Matrix Filter Topology

noncomputable section

namespace Breakdown

namespace SteadyCert

def WeakPowerSubStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ v P v' P' : Space → Space, MemLp v 6 volume → MemLp v' 6 volume →
    IsWeakFractionalPower α v P → IsWeakFractionalPower α v' P' →
      IsWeakFractionalPower α (fun y => v y - v' y) (fun y => P y - P' y)

def DefectRightSideStatement : Prop :=
  ∀ α : ℝ, 1 < α → α < 5 / 4 → ∀ {k N : ℕ} (d : FracCertData k N), IsFracCert α d → ∀ p ∈ box d.radius,
    MemLp (d.defect α p) 2 volume ∧
      ∀ u G H, IsSecondOrderField d.order u G H → IsClassField d.order (fun y => -d.defect α p y - G y (u y))

end SteadyCert

namespace FracInternal.HeldExists

open SteadyCert

structure HeldState (k : ℕ) where
  v : Space → Space
  G : Space → (Space →L[ℝ] Space)
  H : Space → (Space →L[ℝ] Space →L[ℝ] Space)
  P : Space → Space
  κ : Fin k → ℝ

variable {k N : ℕ}

def HeldState.zero : HeldState k := ⟨fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩

def dsz (d : FracCertData k N) (a b : HeldState k) : ℝ :=
  d.size (fun y => a.G y - b.G y) (fun y => a.H y - b.H y) (fun i => a.κ i - b.κ i)

def sz (d : FracCertData k N) (a : HeldState k) : ℝ := d.size a.G a.H a.κ

theorem axialTurn_sub (a b : Space) : axialTurn (a - b) = axialTurn a - axialTurn b := by
  ext i
  fin_cases i <;> simp [axialTurn] <;> ring

theorem isGradientField_neg {Q : Space → Space} (hQ : IsGradientField Q) : IsGradientField (fun y => -Q y) := by
  obtain ⟨q, hq2, hQ2, hQm, hid⟩ := hQ
  refine ⟨fun y => -q y, ?_, ?_, hQm.neg, ?_⟩
  · intro K hK; simpa [neg_sq] using hq2 K hK
  · intro K hK; simpa [norm_neg] using hQ2 K hK
  · intro φ hφ j
    have := hid φ hφ j
    simp only [mul_neg, inner_neg_left, integral_neg, this, neg_neg]

theorem isGradientField_zero : IsGradientField (fun _ => (0 : Space)) := by
  refine ⟨fun _ => 0, ?_, ?_, aestronglyMeasurable_const, ?_⟩
  · intro K hK; simp
  · intro K hK; simp
  · intro φ hφ j; simp

theorem secondOrder_zero (m : ℕ) : IsSecondOrderField m (fun _ => (0 : Space)) (fun _ => 0) (fun _ => 0) := by
  refine ⟨aestronglyMeasurable_const, aestronglyMeasurable_const, aestronglyMeasurable_const, MemLp.zero',
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [entrySq]
  · simp
  · intro φ hφ j; simp
  · intro φ hφ i j; simp
  · simp
  · constructor
    · filter_upwards with y
      ext i; fin_cases i <;> simp [turnStep]
    · filter_upwards with y
      ext i; fin_cases i <;> simp [mirror]

theorem size_zero (d : FracCertData k N) : sz d HeldState.zero = 0 := by
  simp [sz, HeldState.zero, FracCertData.size, sizeNorm, weightedEnergy, secondTrace, entrySq]

theorem size_neg (d : FracCertData k N) (G : Space → (Space →L[ℝ] Space))
    (H : Space → (Space →L[ℝ] Space →L[ℝ] Space)) (κ : Fin k → ℝ) :
    d.size (fun y => -G y) (fun y => -H y) (fun i => -κ i) = d.size G H κ := by
  simp [FracCertData.size, sizeNorm, weightedEnergy, secondTrace, entrySq, Finset.sum_neg_distrib]

theorem dsz_zero_right (d : FracCertData k N) (a : HeldState k) : dsz d a HeldState.zero = sz d a := by
  simp [dsz, sz, HeldState.zero]

theorem dsz_comm (d : FracCertData k N) (a b : HeldState k) : dsz d a b = dsz d b a := by
  have h := size_neg d (fun y => a.G y - b.G y) (fun y => a.H y - b.H y) (fun i => a.κ i - b.κ i)
  simp only [neg_sub] at h
  exact h.symm

theorem dsz_nonneg (d : FracCertData k N) (a b : HeldState k) : 0 ≤ dsz d a b := Real.sqrt_nonneg _

theorem energy_nonneg {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) (G H) :
    0 ≤ d.energy G H := by
  unfold FracCertData.energy weightedEnergy
  refine add_nonneg (integral_nonneg fun y => by positivity) (integral_nonneg fun y => ?_)
  exact mul_nonneg (le_trans hd.weightMin_pos.le (hd.weight_lower y)) (Finset.sum_nonneg fun i _ => by positivity)

theorem energy_le {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) (G H κ) :
    d.energy G H ≤ d.size G H κ ^ 2 := by
  have h0 := energy_nonneg hd G H
  have h1 : 0 ≤ d.multiplierScale ^ 2 * ∑ i, κ i ^ 2 := by positivity
  unfold FracCertData.size sizeNorm
  rw [Real.sq_sqrt (by unfold FracCertData.energy at h0; linarith)]
  unfold FracCertData.energy at *
  linarith

theorem sqrt_energy_le {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) (G H κ) :
    Real.sqrt (d.energy G H) ≤ d.size G H κ := by
  rw [Real.sqrt_le_left]
  · exact energy_le hd G H κ
  · exact Real.sqrt_nonneg _

theorem l2Norm_eq {F : Space → Space} (h : MemLp F 2 volume) : l2Norm F = (eLpNorm F 2 volume).toReal := by
  rw [h.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  have h0 : 0 ≤ ∫ a, ‖F a‖ ^ (2 : ℝ≥0∞).toReal := integral_nonneg fun a => by positivity
  rw [ENNReal.toReal_ofReal (by positivity), l2Norm, Real.sqrt_eq_rpow]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  norm_num

theorem l2Norm_nonneg (F : Space → Space) : 0 ≤ l2Norm F := Real.sqrt_nonneg _

theorem l2Norm_sub_le {F F' : Space → Space} (h : MemLp F 2 volume) (h' : MemLp F' 2 volume) :
    l2Norm (fun y => F y - F' y) ≤ l2Norm F + l2Norm F' := by
  have e : (fun y => F y - F' y) = F - F' := rfl
  rw [e, l2Norm_eq (h.sub h'), l2Norm_eq h, l2Norm_eq h', ← ENNReal.toReal_add h.eLpNorm_ne_top h'.eLpNorm_ne_top]
  exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h.eLpNorm_ne_top, h'.eLpNorm_ne_top⟩)
    (eLpNorm_sub_le h.1 h'.1 (by norm_num))

theorem l2Norm_le_add_sub {F F' : Space → Space} (h : MemLp F 2 volume) (h' : MemLp F' 2 volume) :
    l2Norm F ≤ l2Norm F' + l2Norm (fun y => F y - F' y) := by
  have hd : MemLp (fun y => F y - F' y) 2 volume := h.sub h'
  have e : F = F' + (fun y => F y - F' y) := by funext y; simp
  rw [l2Norm_eq h, l2Norm_eq h', l2Norm_eq hd, ← ENNReal.toReal_add h'.eLpNorm_ne_top hd.eLpNorm_ne_top]
  refine ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨h'.eLpNorm_ne_top, hd.eLpNorm_ne_top⟩) ?_
  conv_lhs => rw [e]
  exact eLpNorm_add_le h'.1 hd.1 (by norm_num)

theorem product_bound {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) (hQ : QuadraticSquareIntegrableStatement)
    (h4 : SecondOrderLinearStatement)
    {u G H u' G' H'} (hs : IsSecondOrderField d.order u G H) (hs' : IsSecondOrderField d.order u' G' H') :
    l2Norm (fun y => G y (u y) - G' y (u' y)) ≤ d.productConst *
      Real.sqrt (d.energy (fun y => G y - G' y) (fun y => H y - H' y)) *
        (Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H')) := by
  have hsum := h4 d.order u u' G G' H H' 1 hs hs'
  have hdif := h4 d.order u u' G G' H H' (-1) hs hs'
  simp only [one_smul] at hsum
  simp only [neg_one_smul, ← sub_eq_add_neg] at hdif
  have mA := hQ _ _ _ _ hs
  have mB := hQ _ _ _ _ hs'
  have mS := hQ _ _ _ _ hsum
  have hS1 : symProduct u G (fun y => u y - u' y) (fun y => G y - G' y) =
      ((2 : ℝ)⁻¹ * 3) • (fun y => G y (u y)) - (2 : ℝ)⁻¹ • (fun y => (G y + G' y) (u y + u' y)) +
        (2 : ℝ)⁻¹ • (fun y => G' y (u' y)) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, symProduct, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_add, map_sub]
    module
  have hS2 : symProduct u' G' (fun y => u y - u' y) (fun y => G y - G' y) =
      (2 : ℝ)⁻¹ • (fun y => (G y + G' y) (u y + u' y)) - (2 : ℝ)⁻¹ • (fun y => G y (u y)) -
        ((2 : ℝ)⁻¹ * 3) • (fun y => G' y (u' y)) := by
    funext y
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, symProduct, ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply, map_add, map_sub]
    module
  have m1 : MemLp (symProduct u G (fun y => u y - u' y) (fun y => G y - G' y)) 2 volume := by
    rw [hS1]; exact ((mA.const_smul ((2 : ℝ)⁻¹ * 3)).sub (mS.const_smul (2 : ℝ)⁻¹)).add (mB.const_smul (2 : ℝ)⁻¹)
  have m2 : MemLp (symProduct u' G' (fun y => u y - u' y) (fun y => G y - G' y)) 2 volume := by
    rw [hS2]; exact ((mS.const_smul (2 : ℝ)⁻¹).sub (mA.const_smul (2 : ℝ)⁻¹)).sub (mB.const_smul ((2 : ℝ)⁻¹ * 3))
  have hsplit : (fun y => G y (u y) - G' y (u' y)) = fun y =>
      symProduct u G (fun y => u y - u' y) (fun y => G y - G' y) y -
        -symProduct u' G' (fun y => u y - u' y) (fun y => G y - G' y) y := by
    funext y
    rw [hS1, hS2]
    simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply]
    module
  rw [hsplit]
  have b1 := hd.productConst_bound u G H hs _ _ _ hdif
  have b2 := hd.productConst_bound u' G' H' hs' _ _ _ hdif
  have hneg : l2Norm (-symProduct u' G' (fun y => u y - u' y) (fun y => G y - G' y)) =
      l2Norm (symProduct u' G' (fun y => u y - u' y) (fun y => G y - G' y)) := by
    simp [l2Norm, norm_neg]
  refine (l2Norm_sub_le m1 m2.neg).trans ?_
  rw [hneg]
  have e : d.productConst * Real.sqrt (d.energy (fun y => G y - G' y) (fun y => H y - H' y)) *
      (Real.sqrt (d.energy G H) + Real.sqrt (d.energy G' H')) =
      d.productConst * Real.sqrt (d.energy G H) * Real.sqrt (d.energy (fun y => G y - G' y) (fun y => H y - H' y)) +
      d.productConst * Real.sqrt (d.energy G' H') * Real.sqrt (d.energy (fun y => G y - G' y) (fun y => H y - H' y)) := by
    ring
  linarith [b1, b2]

theorem product_self {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d)
    {u G H} (hs : IsSecondOrderField d.order u G H) :
    l2Norm (fun y => G y (u y)) ≤ d.productConst * d.energy G H := by
  have h := hd.productConst_bound u G H hs u G H hs
  have he : symProduct u G u G = fun y => G y (u y) := by
    funext y
    simp only [symProduct]
    rw [← two_smul ℝ (G y (u y)), smul_smul]
    norm_num
  rw [he, mul_assoc, Real.mul_self_sqrt (energy_nonneg hd G H)] at h
  exact h

theorem l2_limit (F : ℕ → Space → Space) (hF : ∀ n, MemLp (F n) 2 volume)
    (hC : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M, l2Norm (fun y => F n y - F m y) < ε) :
    ∃ F₀, MemLp F₀ 2 volume ∧ Tendsto (fun n => ∫ y, ‖F n y - F₀ y‖ ^ 2) atTop (𝓝 0) := by
  let L : ℕ → Lp Space 2 (volume : Measure Space) := fun n => (hF n).toLp (F n)
  have hdist : ∀ n m, dist (L n) (L m) = l2Norm (fun y => F n y - F m y) := by
    intro n m
    show dist ((hF n).toLp (F n)) ((hF m).toLp (F m)) = l2Norm (F n - F m)
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp, l2Norm_eq ((hF n).sub (hF m))]
  have hcs : CauchySeq L := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨M, hM⟩ := hC ε hε
    exact ⟨M, fun m hm n hn => by rw [hdist]; exact hM m hm n hn⟩
  obtain ⟨L₀, hL₀⟩ := cauchySeq_tendsto_of_complete hcs
  refine ⟨(L₀ : Space → Space), Lp.memLp L₀, ?_⟩
  have hsq : ∀ n, ∫ y, ‖F n y - (L₀ : Space → Space) y‖ ^ 2 = dist (L n) L₀ ^ 2 := by
    intro n
    have hm : dist (L n) L₀ = l2Norm (F n - (L₀ : Space → Space)) := by
      show dist ((hF n).toLp (F n)) L₀ = _
      conv_lhs => rw [← Lp.toLp_coeFn L₀ (Lp.memLp L₀)]
      rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp, l2Norm_eq ((hF n).sub (Lp.memLp L₀))]
    rw [hm, l2Norm, Real.sq_sqrt (integral_nonneg fun y => by positivity)]
    rfl
  simp_rw [hsq]
  have := (tendsto_iff_dist_tendsto_zero.1 hL₀).pow 2
  simpa using this

theorem l2_unique (F : ℕ → Space → Space) (F₀ F₁ : Space → Space) (hF : ∀ n, MemLp (F n) 2 volume)
    (h₀ : MemLp F₀ 2 volume) (h₁ : MemLp F₁ 2 volume)
    (t₀ : Tendsto (fun n => ∫ y, ‖F n y - F₀ y‖ ^ 2) atTop (𝓝 0))
    (t₁ : Tendsto (fun n => l2Norm (fun y => F n y - F₁ y)) atTop (𝓝 0)) : F₀ =ᵐ[volume] F₁ := by
  have hm0 : ∀ n, dist ((hF n).toLp (F n)) (h₀.toLp F₀) = l2Norm (F n - F₀) := fun n => by
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp, l2Norm_eq ((hF n).sub h₀)]
  have hm1 : ∀ n, dist ((hF n).toLp (F n)) (h₁.toLp F₁) = l2Norm (F n - F₁) := fun n => by
    rw [dist_eq_norm, ← MemLp.toLp_sub, Lp.norm_toLp, l2Norm_eq ((hF n).sub h₁)]
  have t0' : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (h₀.toLp F₀)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp_rw [hm0]
    have := t₀.sqrt
    simpa [l2Norm] using this
  have t1' : Tendsto (fun n => (hF n).toLp (F n)) atTop (𝓝 (h₁.toLp F₁)) := by
    rw [tendsto_iff_dist_tendsto_zero]
    simp_rw [hm1]
    exact t₁
  exact (MemLp.toLp_eq_toLp_iff h₀ h₁).1 (tendsto_nhds_unique t0' t1')

theorem g_mono {A A' y y' D : ℝ} (hD : 0 < D) (hA : A ≤ A') (hA0 : 0 ≤ A) (hy0 : 0 ≤ y) (hy : y ≤ y') :
    (1 / 2) * A + Real.sqrt ((1 / 4) * A ^ 2 + y ^ 2 / D) ≤ (1 / 2) * A' + Real.sqrt ((1 / 4) * A' ^ 2 + y' ^ 2 / D) := by
  have h1 : A ^ 2 ≤ A' ^ 2 := pow_le_pow_left₀ hA0 hA 2
  have h2 : y ^ 2 ≤ y' ^ 2 := pow_le_pow_left₀ hy0 hy 2
  have h3 : y ^ 2 / D ≤ y' ^ 2 / D := div_le_div_of_nonneg_right h2 hD.le
  have h4 : (1 / 4) * A ^ 2 + y ^ 2 / D ≤ (1 / 4) * A' ^ 2 + y' ^ 2 / D := by linarith
  linarith [Real.sqrt_le_sqrt h4]

theorem g_add {A₁ A₂ y₁ y₂ D : ℝ} (hD : 0 < D) :
    (1 / 2) * (A₁ + A₂) + Real.sqrt ((1 / 4) * (A₁ + A₂) ^ 2 + (y₁ + y₂) ^ 2 / D) ≤
      ((1 / 2) * A₁ + Real.sqrt ((1 / 4) * A₁ ^ 2 + y₁ ^ 2 / D)) +
        ((1 / 2) * A₂ + Real.sqrt ((1 / 4) * A₂ ^ 2 + y₂ ^ 2 / D)) := by
  set c := 1 / D with hcdef
  have hc : 0 < c := by positivity
  have e : ∀ A y : ℝ, (1 / 4) * A ^ 2 + y ^ 2 / D = (1 / 4) * A ^ 2 + c * y ^ 2 := by
    intro A y; rw [hcdef]; ring
  rw [e, e, e]
  have h1 : 0 ≤ (1 / 4) * A₁ ^ 2 + c * y₁ ^ 2 := by positivity
  have h2 : 0 ≤ (1 / 4) * A₂ ^ 2 + c * y₂ ^ 2 := by positivity
  set S₁ := Real.sqrt ((1 / 4) * A₁ ^ 2 + c * y₁ ^ 2) with hS₁
  set S₂ := Real.sqrt ((1 / 4) * A₂ ^ 2 + c * y₂ ^ 2) with hS₂
  have hS1 : S₁ ^ 2 = (1 / 4) * A₁ ^ 2 + c * y₁ ^ 2 := Real.sq_sqrt h1
  have hS2 : S₂ ^ 2 = (1 / 4) * A₂ ^ 2 + c * y₂ ^ 2 := Real.sq_sqrt h2
  have hS1n : 0 ≤ S₁ := Real.sqrt_nonneg _
  have hS2n : 0 ≤ S₂ := Real.sqrt_nonneg _
  have hsq : ((1 / 4) * A₁ * A₂ + c * y₁ * y₂) ^ 2 ≤ (S₁ * S₂) ^ 2 := by
    rw [mul_pow, hS1, hS2]
    nlinarith [mul_nonneg hc.le (sq_nonneg (A₁ * y₂ - A₂ * y₁))]
  have hcs : (1 / 4) * A₁ * A₂ + c * y₁ * y₂ ≤ S₁ * S₂ :=
    calc _ ≤ |(1 / 4) * A₁ * A₂ + c * y₁ * y₂| := le_abs_self _
      _ = Real.sqrt (((1 / 4) * A₁ * A₂ + c * y₁ * y₂) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((S₁ * S₂) ^ 2) := Real.sqrt_le_sqrt hsq
      _ = S₁ * S₂ := Real.sqrt_sq (mul_nonneg hS1n hS2n)
  have hm : Real.sqrt ((1 / 4) * (A₁ + A₂) ^ 2 + c * (y₁ + y₂) ^ 2) ≤ S₁ + S₂ :=
    calc _ ≤ Real.sqrt ((S₁ + S₂) ^ 2) := Real.sqrt_le_sqrt (by nlinarith [hS1, hS2, hcs])
      _ = S₁ + S₂ := Real.sqrt_sq (by positivity)
  linarith

theorem g_smul {A y D x : ℝ} (hx : 0 ≤ x) :
    (1 / 2) * (x * A) + Real.sqrt ((1 / 4) * (x * A) ^ 2 + (x * y) ^ 2 / D) =
      x * ((1 / 2) * A + Real.sqrt ((1 / 4) * A ^ 2 + y ^ 2 / D)) := by
  have h : (1 / 4) * (x * A) ^ 2 + (x * y) ^ 2 / D = x ^ 2 * ((1 / 4) * A ^ 2 + y ^ 2 / D) := by ring
  rw [h, Real.sqrt_mul (sq_nonneg x), Real.sqrt_sq hx]
  ring

theorem bc_nonneg {sc th cp t : ℝ} (hcp : 0 ≤ cp) (hth : 0 ≤ th) (hth1 : th < 1) (x y : ℝ) :
    0 ≤ boundConst sc th cp t x y 0 := by
  unfold boundConst
  have hD : 0 < 1 - th ^ 2 := by nlinarith
  refine mul_nonneg (Real.rpow_nonneg hcp _) ?_
  · set A := (sc * x + 2 * th * y) / (1 - th ^ 2)
    have hy : 0 ≤ (y ^ 2 + t * 0 ^ 2) / (1 - th ^ 2) := by
      have : y ^ 2 + t * 0 ^ 2 = y ^ 2 := by ring
      rw [this]; positivity
    have h1 : |A / 2| ≤ Real.sqrt ((1 / 4) * A ^ 2 + (y ^ 2 + t * 0 ^ 2) / (1 - th ^ 2)) := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (by nlinarith)
    linarith [neg_abs_le (A / 2)]

theorem bc_split {sc th cp t : ℝ} (hsc : 0 ≤ sc) (hth : 0 ≤ th) (hth1 : th < 1) (hcp : 0 ≤ cp)
    {X Y a b x R : ℝ} (hX0 : 0 ≤ X) (hY0 : 0 ≤ Y) (ha : 0 ≤ a) (hb : 0 ≤ b) (hx : 0 ≤ x) (hR : 0 ≤ R)
    (hX : X ≤ a + x) (hY : Y ≤ b + x * R) :
    boundConst sc th cp t X Y 0 ≤ boundConst sc th cp t a b 0 + x * boundConst sc th cp t 1 R 0 := by
  unfold boundConst
  have hD : 0 < 1 - th ^ 2 := by nlinarith
  have ez : ∀ y : ℝ, y ^ 2 + t * 0 ^ 2 = y ^ 2 := fun y => by ring
  simp only [ez]
  set D := 1 - th ^ 2 with hDdef
  set c := cp ^ (-(1 / 2 : ℝ)) with hc
  have hc0 : 0 ≤ c := Real.rpow_nonneg hcp _
  set Aa := (sc * a + 2 * th * b) / D with hAa
  set A1 := (sc * 1 + 2 * th * R) / D with hA1
  have hnum : sc * X + 2 * th * Y ≤ (sc * a + 2 * th * b) + x * (sc * 1 + 2 * th * R) := by
    have h1 : sc * X ≤ sc * (a + x) := mul_le_mul_of_nonneg_left hX hsc
    have h2 : 2 * th * Y ≤ 2 * th * (b + x * R) := mul_le_mul_of_nonneg_left hY (by positivity)
    nlinarith
  have hA : (sc * X + 2 * th * Y) / D ≤ Aa + x * A1 := by
    have : Aa + x * A1 = ((sc * a + 2 * th * b) + x * (sc * 1 + 2 * th * R)) / D := by
      rw [hAa, hA1]; ring
    rw [this]; exact div_le_div_of_nonneg_right hnum hD.le
  have hA0 : 0 ≤ (sc * X + 2 * th * Y) / D := by positivity
  have s1 := g_mono hD hA hA0 hY0 hY
  have s2 := g_add (A₁ := Aa) (A₂ := x * A1) (y₁ := b) (y₂ := x * R) hD
  have s3 := g_smul (A := A1) (y := R) (D := D) hx
  rw [s3] at s2
  have key := s1.trans s2
  calc c * ((1 / 2) * ((sc * X + 2 * th * Y) / D) + Real.sqrt ((1 / 4) * ((sc * X + 2 * th * Y) / D) ^ 2 + Y ^ 2 / D))
      ≤ c * (((1 / 2) * Aa + Real.sqrt ((1 / 4) * Aa ^ 2 + b ^ 2 / D)) +
        x * ((1 / 2) * A1 + Real.sqrt ((1 / 4) * A1 ^ 2 + R ^ 2 / D))) := mul_le_mul_of_nonneg_left key hc0
    _ = _ := by ring

theorem l2Norm_congr_ae {F F' : Space → Space} (h : F =ᵐ[volume] F') : l2Norm F = l2Norm F' := by
  unfold l2Norm
  congr 1
  exact integral_congr_ae (h.mono fun y hy => by simp only [hy])

theorem inner_integrable {X e : Space → Space} (hX : MemLp X 2 volume) (he : MemLp e 2 volume) :
    Integrable (fun y => inner ℝ (X y) (e y)) := by
  refine (L2.integrable_inner (hX.toLp X) (he.toLp e)).congr ?_
  filter_upwards [hX.coeFn_toLp, he.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem inner_toLp {f g : Space → Space} (hf : MemLp f 2 volume) (hg : MemLp g 2 volume) :
    inner ℝ (hf.toLp f) (hg.toLp g) = ∫ y, inner ℝ (f y) (g y) := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hf.coeFn_toLp, hg.coeFn_toLp] with y h1 h2
  rw [h1, h2]

theorem pair_triangle {Z X e : Space → Space} (hX : MemLp X 2 volume) (he : MemLp e 2 volume) :
    |l2Pair (fun y => -Z y - X y) e| ≤ |l2Pair Z e| + |l2Pair X e| := by
  have hXe : Integrable (fun y => inner ℝ (X y) (e y)) := inner_integrable hX he
  simp only [l2Pair]
  have hfun : (fun y => inner ℝ (-Z y - X y) (e y)) = fun y => -(inner ℝ (Z y) (e y)) - inner ℝ (X y) (e y) := by
    funext y; rw [inner_sub_left, inner_neg_left]
  by_cases hZ : Integrable (fun y => inner ℝ (Z y) (e y))
  · have hZn : Integrable (fun y => -(inner ℝ (Z y) (e y))) := hZ.neg
    rw [hfun, integral_sub hZn hXe, integral_neg]
    exact (abs_sub _ _).trans (by rw [abs_neg])
  · have hnot : ¬ Integrable (fun y => inner ℝ (-Z y - X y) (e y)) := by
      intro h
      apply hZ
      have : (fun y => inner ℝ (Z y) (e y)) = fun y => -(inner ℝ (-Z y - X y) (e y)) - inner ℝ (X y) (e y) := by
        funext y; rw [inner_sub_left, inner_neg_left]; ring
      rw [this]; exact h.neg.sub hXe
    rw [integral_undef hnot, abs_zero]; positivity

theorem rowSize_le {e : Fin N → Space → Space} {τ : Fin N → ℝ} (hτ : ∀ a, 0 ≤ τ a) {F Z X : Space → Space}
    (h : ∀ a, |l2Pair F (e a)| ≤ |l2Pair Z (e a)| + |l2Pair X (e a)|) :
    rowSize e τ F ≤ rowSize e τ Z + rowSize e τ X := by
  unfold rowSize
  have hV : 0 ≤ ∑ a, τ a * l2Pair Z (e a) ^ 2 := Finset.sum_nonneg fun a _ => mul_nonneg (hτ a) (sq_nonneg _)
  have hW : 0 ≤ ∑ a, τ a * l2Pair X (e a) ^ 2 := Finset.sum_nonneg fun a _ => mul_nonneg (hτ a) (sq_nonneg _)
  have hcs : ∑ a, τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|) ≤
      Real.sqrt (∑ a, τ a * l2Pair Z (e a) ^ 2) * Real.sqrt (∑ a, τ a * l2Pair X (e a) ^ 2) := by
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => Real.sqrt (τ a) * |l2Pair Z (e a)|)
      (fun a => Real.sqrt (τ a) * |l2Pair X (e a)|)
    have e1 : ∀ a, Real.sqrt (τ a) * |l2Pair Z (e a)| * (Real.sqrt (τ a) * |l2Pair X (e a)|) =
        τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|) := fun a => by
      calc _ = (Real.sqrt (τ a) * Real.sqrt (τ a)) * (|l2Pair Z (e a)| * |l2Pair X (e a)|) := by ring
        _ = _ := by rw [Real.mul_self_sqrt (hτ a)]
    have e2 : ∀ a, (Real.sqrt (τ a) * |l2Pair Z (e a)|) ^ 2 = τ a * l2Pair Z (e a) ^ 2 := fun a => by
      rw [mul_pow, Real.sq_sqrt (hτ a), sq_abs]
    have e3 : ∀ a, (Real.sqrt (τ a) * |l2Pair X (e a)|) ^ 2 = τ a * l2Pair X (e a) ^ 2 := fun a => by
      rw [mul_pow, Real.sq_sqrt (hτ a), sq_abs]
    simp only [e1, e2, e3] at hc
    calc _ ≤ |∑ a, τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|)| := le_abs_self _
      _ = Real.sqrt ((∑ a, τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|)) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((∑ a, τ a * l2Pair Z (e a) ^ 2) * ∑ a, τ a * l2Pair X (e a) ^ 2) := Real.sqrt_le_sqrt hc
      _ = _ := Real.sqrt_mul hV _
  have hpt : ∀ a, τ a * l2Pair F (e a) ^ 2 ≤ τ a * l2Pair Z (e a) ^ 2 + τ a * l2Pair X (e a) ^ 2 +
      2 * (τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|)) := by
    intro a
    have h1 : l2Pair F (e a) ^ 2 ≤ (|l2Pair Z (e a)| + |l2Pair X (e a)|) ^ 2 := by
      rw [← sq_abs (l2Pair F (e a))]; exact pow_le_pow_left₀ (abs_nonneg _) (h a) 2
    have h2 : (|l2Pair Z (e a)| + |l2Pair X (e a)|) ^ 2 =
        l2Pair Z (e a) ^ 2 + l2Pair X (e a) ^ 2 + 2 * (|l2Pair Z (e a)| * |l2Pair X (e a)|) := by
      rw [add_sq, sq_abs, sq_abs]; ring
    have h3 := mul_le_mul_of_nonneg_left h1 (hτ a)
    rw [h2] at h3
    linarith
  have hsum : ∑ a, τ a * l2Pair F (e a) ^ 2 ≤ ∑ a, τ a * l2Pair Z (e a) ^ 2 + ∑ a, τ a * l2Pair X (e a) ^ 2 +
      2 * ∑ a, τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|) := by
    calc _ ≤ ∑ a, (τ a * l2Pair Z (e a) ^ 2 + τ a * l2Pair X (e a) ^ 2 +
          2 * (τ a * (|l2Pair Z (e a)| * |l2Pair X (e a)|))) := Finset.sum_le_sum fun a _ => hpt a
      _ = _ := by rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hsV := Real.sq_sqrt hV
  have hsW := Real.sq_sqrt hW
  have hn1 := Real.sqrt_nonneg (∑ a, τ a * l2Pair Z (e a) ^ 2)
  have hn2 := Real.sqrt_nonneg (∑ a, τ a * l2Pair X (e a) ^ 2)
  calc Real.sqrt (∑ a, τ a * l2Pair F (e a) ^ 2) ≤
      Real.sqrt ((Real.sqrt (∑ a, τ a * l2Pair Z (e a) ^ 2) + Real.sqrt (∑ a, τ a * l2Pair X (e a) ^ 2)) ^ 2) :=
        Real.sqrt_le_sqrt (by nlinarith [hsum, hcs, hsV, hsW])
    _ = _ := Real.sqrt_sq (by positivity)

theorem rows_le {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) {X : Space → Space} (hX : MemLp X 2 volume) :
    d.rows X ≤ Real.sqrt d.rowMax * l2Norm X := by
  let E : Fin N → Lp Space 2 (volume : Measure Space) := fun a => (hd.row_two a).toLp (d.row a)
  have hE : Orthonormal ℝ E := by
    rw [orthonormal_iff_ite]
    intro a b
    rw [inner_toLp]
    exact hd.row_orthonormal a b
  have hb := hE.sum_inner_products_le (x := hX.toLp X) (s := Finset.univ)
  have hpair : ∀ a, ‖inner ℝ (E a) (hX.toLp X)‖ ^ 2 = l2Pair X (d.row a) ^ 2 := by
    intro a
    rw [inner_toLp, Real.norm_eq_abs, sq_abs]
    unfold l2Pair
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun y => real_inner_comm _ _)
  simp only [hpair] at hb
  rw [Lp.norm_toLp, ← l2Norm_eq hX] at hb
  unfold FracCertData.rows rowSize
  have hsum : ∑ a, d.rowWeight a * l2Pair X (d.row a) ^ 2 ≤ d.rowMax * ∑ a, l2Pair X (d.row a) ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_right (hd.rowWeight_le a) (sq_nonneg _)
  have h3 : d.rowMax * ∑ a, l2Pair X (d.row a) ^ 2 ≤ d.rowMax * l2Norm X ^ 2 :=
    mul_le_mul_of_nonneg_left hb hd.rowMax_pos.le
  calc Real.sqrt (∑ a, d.rowWeight a * l2Pair X (d.row a) ^ 2) ≤ Real.sqrt (d.rowMax * l2Norm X ^ 2) :=
        Real.sqrt_le_sqrt (hsum.trans h3)
    _ = Real.sqrt d.rowMax * l2Norm X := by
        rw [Real.sqrt_mul hd.rowMax_pos.le, Real.sqrt_sq (l2Norm_nonneg X)]

theorem apriori_rhs {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {d : FracCertData k N} (hd : IsFracCert α d)
    (hgadd : GradientAddStatement) (h2 : AprioriBoundStatement) {p : Fin k → ℝ} (hp : p ∈ box d.radius)
    (t : HeldState k) (hL : d.IsLinearState α p t.v t.G t.H t.P) (Y X : Space → Space)
    (hY : MemLp Y 2 volume) (hX : MemLp X 2 volume)
    (hE : ∃ Q, IsGradientField Q ∧ ∀ᵐ y ∂volume, d.fullField α p t.v t.G t.H t.P t.κ y = -Y y - X y + Q y)
    (hpin : d.pins t.G = 0) {a b : ℝ} (ha : projectedNorm Y ≤ a) (hb : d.rowsModGrad Y ≤ b) :
    sz d t ≤ d.boundFn a b 0 + d.rowConst * l2Norm X := by
  obtain ⟨Q, hQ, hE⟩ := hE
  have hth : 0 ≤ d.contraction := Real.sqrt_nonneg _
  have hth1 := hd.contraction_lt
  have hcp : 0 ≤ d.reducedGap := hd.reducedGap_pos.le
  have hA := h2 α hα1 hα2 d hd p hp t.v t.G t.H t.P hL t.κ
  rw [hpin] at hA
  have hv0 : vecNorm (0 : Fin k → ℝ) = 0 := by simp [vecNorm]
  rw [hv0] at hA
  set ff := d.fullField α p t.v t.G t.H t.P t.κ with hff
  have hrow0 : 0 ≤ d.rowsModGrad ff := by
    refine Real.sInf_nonneg fun r hr => ?_
    obtain ⟨_, _, rfl⟩ := hr
    exact Real.sqrt_nonneg _
  have hsq : Real.sqrt (d.rowsModGrad ff ^ 2 + d.pinWeight * 0 ^ 2) = d.rowsModGrad ff := by
    rw [show d.rowsModGrad ff ^ 2 + d.pinWeight * 0 ^ 2 = d.rowsModGrad ff ^ 2 by ring, Real.sqrt_sq hrow0]
  rw [hsq] at hA
  have hpn0 : 0 ≤ projectedNorm ff := by
    refine Real.sInf_nonneg fun r hr => ?_
    obtain ⟨_, _, _, rfl⟩ := hr
    exact Real.sqrt_nonneg _
  have ha0 : 0 ≤ a := by
    refine le_trans (Real.sInf_nonneg fun r hr => ?_) ha
    obtain ⟨_, _, _, rfl⟩ := hr
    exact Real.sqrt_nonneg _
  have hb0 : 0 ≤ b := by
    refine le_trans (Real.sInf_nonneg fun r hr => ?_) hb
    obtain ⟨_, _, rfl⟩ := hr
    exact Real.sqrt_nonneg _
  have hQ' : ∀ QY, IsGradientField QY → IsGradientField (fun y => -Q y + -QY y) :=
    fun QY hQY => hgadd _ _ (isGradientField_neg hQ) (isGradientField_neg hQY)
  have hae : ∀ QY : Space → Space, (fun y => ff y + (-Q y + -QY y)) =ᵐ[volume] fun y => -(Y y + QY y) - X y := by
    intro QY
    filter_upwards [hE] with y hy
    rw [hy]; abel
  have hP1 : projectedNorm ff ≤ a + l2Norm X := by
    have hne : Set.Nonempty {r | ∃ Q', IsGradientField Q' ∧ MemLp (fun y => Y y + Q' y) 2 volume ∧
        r = l2Norm (fun y => Y y + Q' y)} := ⟨_, fun _ => 0, isGradientField_zero, by simpa using hY, rfl⟩
    have key : ∀ r ∈ {r | ∃ Q', IsGradientField Q' ∧ MemLp (fun y => Y y + Q' y) 2 volume ∧
        r = l2Norm (fun y => Y y + Q' y)}, projectedNorm ff - l2Norm X ≤ r := by
      rintro r ⟨QY, hQY, hmY, rfl⟩
      have hm : MemLp (fun y => -(Y y + QY y) - X y) 2 volume := hmY.neg.sub hX
      have hm' : MemLp (fun y => ff y + (-Q y + -QY y)) 2 volume := hm.ae_eq (hae QY).symm
      have h1 : projectedNorm ff ≤ l2Norm (fun y => ff y + (-Q y + -QY y)) := by
        refine csInf_le ⟨0, fun r hr => ?_⟩ ⟨fun y => -Q y + -QY y, hQ' QY hQY, hm', rfl⟩
        obtain ⟨_, _, _, rfl⟩ := hr
        exact Real.sqrt_nonneg _
      rw [l2Norm_congr_ae (hae QY)] at h1
      have hmYn : MemLp (fun y => -(Y y + QY y)) 2 volume := hmY.neg
      have h2 := l2Norm_sub_le hmYn hX
      beta_reduce at h2
      have h3 : l2Norm (fun y => -(Y y + QY y)) = l2Norm (fun y => Y y + QY y) := by simp only [l2Norm, norm_neg]
      linarith
    have := le_csInf hne key
    have ha' : projectedNorm Y ≤ a := ha
    unfold projectedNorm at ha'
    linarith
  have hR1 : d.rowsModGrad ff ≤ b + l2Norm X * Real.sqrt d.rowMax := by
    have hne : Set.Nonempty {r | ∃ Q', IsGradientField Q' ∧ r = rowSize d.row d.rowWeight (fun y => Y y + Q' y)} :=
      ⟨_, fun _ => 0, isGradientField_zero, rfl⟩
    have key : ∀ r ∈ {r | ∃ Q', IsGradientField Q' ∧ r = rowSize d.row d.rowWeight (fun y => Y y + Q' y)},
        d.rowsModGrad ff - l2Norm X * Real.sqrt d.rowMax ≤ r := by
      rintro r ⟨QY, hQY, rfl⟩
      have h1 : d.rowsModGrad ff ≤ rowSize d.row d.rowWeight (fun y => ff y + (-Q y + -QY y)) := by
        refine csInf_le ⟨0, fun r hr => ?_⟩ ⟨fun y => -Q y + -QY y, hQ' QY hQY, rfl⟩
        obtain ⟨_, _, rfl⟩ := hr
        exact Real.sqrt_nonneg _
      have h2 : rowSize d.row d.rowWeight (fun y => ff y + (-Q y + -QY y)) =
          rowSize d.row d.rowWeight (fun y => -(Y y + QY y) - X y) := by
        unfold rowSize l2Pair
        congr 1
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 2
        exact integral_congr_ae ((hae QY).mono fun y hy => by simp only [hy])
      have h3 : rowSize d.row d.rowWeight (fun y => -(Y y + QY y) - X y) ≤
          rowSize d.row d.rowWeight (fun y => Y y + QY y) + rowSize d.row d.rowWeight X :=
        rowSize_le (fun i => (hd.rowWeight_pos i).le) (fun i => pair_triangle hX (hd.row_two i))
      have h4 := rows_le hd hX
      unfold FracCertData.rows at h4
      linarith
    have h5 : d.rowsModGrad ff - l2Norm X * Real.sqrt d.rowMax ≤ d.rowsModGrad Y := le_csInf hne key
    linarith
  have hsp := bc_split (t := d.pinWeight) hd.formScale_nonneg hth hth1 hcp hpn0 hrow0 ha0 hb0 (l2Norm_nonneg X)
    (Real.sqrt_nonneg _) hP1 hR1
  unfold sz
  calc d.size t.G t.H t.κ ≤ d.boundFn (projectedNorm ff) (d.rowsModGrad ff) 0 := hA
    _ ≤ d.boundFn a b 0 + l2Norm X * d.boundFn 1 (Real.sqrt d.rowMax) 0 := hsp
    _ = d.boundFn a b 0 + d.rowConst * l2Norm X := by unfold FracCertData.rowConst; ring

theorem boundFn_zero (d : FracCertData k N) : d.boundFn 0 0 0 = 0 := by
  simp [FracCertData.boundFn, boundConst]

theorem projectedNorm_zero : projectedNorm (fun _ => (0 : Space)) ≤ 0 := by
  unfold projectedNorm
  have hmem : (0 : ℝ) ∈ {r | ∃ Q, IsGradientField Q ∧ MemLp (fun y => (fun _ => (0 : Space)) y + Q y) 2 volume ∧
      r = l2Norm (fun y => (fun _ => (0 : Space)) y + Q y)} :=
    ⟨fun _ => 0, isGradientField_zero, by simp, by simp [l2Norm]⟩
  refine csInf_le ⟨0, fun r hr => ?_⟩ hmem
  obtain ⟨Q, -, -, rfl⟩ := hr
  exact Real.sqrt_nonneg _

theorem rowsModGrad_zero (d : FracCertData k N) : d.rowsModGrad (fun _ => (0 : Space)) ≤ 0 := by
  unfold FracCertData.rowsModGrad rowSeminorm
  have hmem : (0 : ℝ) ∈ {r | ∃ Q, IsGradientField Q ∧ r = rowSize d.row d.rowWeight (fun y => (fun _ => (0 : Space)) y + Q y)} :=
    ⟨fun _ => 0, isGradientField_zero, by simp [rowSize, l2Pair]⟩
  refine csInf_le ⟨0, fun r hr => ?_⟩ hmem
  obtain ⟨Q, -, rfl⟩ := hr
  exact Real.sqrt_nonneg _

theorem lin_sub {α : ℝ} (hα1 : 1 < α) (hα2 : α < 5 / 4) {d : FracCertData k N}
    (hW : WeakPowerSubStatement) (h4 : SecondOrderLinearStatement) {p : Fin k → ℝ}
    (t t' : HeldState k) (hL : d.IsLinearState α p t.v t.G t.H t.P)
    (hL' : d.IsLinearState α p t'.v t'.G t'.H t'.P) :
    d.IsLinearState α p (fun y => t.v y - t'.v y) (fun y => t.G y - t'.G y) (fun y => t.H y - t'.H y)
      (fun y => t.P y - t'.P y) := by
  obtain ⟨hs, hP, hdr⟩ := hL
  obtain ⟨hs', hP', hdr'⟩ := hL'
  refine ⟨?_, hW α hα1 hα2 _ _ _ _ hs.velocity_six hs'.velocity_six hP hP', ?_⟩
  · have := h4 d.order t.v t'.v t.G t'.G t.H t'.H (-1) hs hs'
    simpa only [neg_one_smul, ← sub_eq_add_neg] using this
  · have e : driftField α (d.rotationRate p) (fun y => t.v y - t'.v y) (fun y => t.G y - t'.G y) =
        driftField α (d.rotationRate p) t.v t.G - driftField α (d.rotationRate p) t'.v t'.G := by
      funext y
      simp only [driftField, Pi.sub_apply, ContinuousLinearMap.sub_apply, map_sub, axialTurn_sub, smul_sub]
      module
    rw [e]; exact hdr.sub hdr'

theorem fullField_sub (d : FracCertData k N) (α : ℝ) (p : Fin k → ℝ) (t t' : HeldState k) (y : Space) :
    d.fullField α p (fun y => t.v y - t'.v y) (fun y => t.G y - t'.G y) (fun y => t.H y - t'.H y)
      (fun y => t.P y - t'.P y) (fun i => t.κ i - t'.κ i) y =
    d.fullField α p t.v t.G t.H t.P t.κ y - d.fullField α p t'.v t'.G t'.H t'.P t'.κ y := by
  simp only [FracCertData.fullField, FracCertData.localField, FracCertData.splitField, driftField, symProduct,
    secondTrace, ContinuousLinearMap.sub_apply, map_sub, smul_sub, Finset.sum_sub_distrib, smul_add, sub_smul,
    axialTurn_sub]
  module

theorem entryInner_integrable {G χ : Space → (Space →L[ℝ] Space)} (hG : AEStronglyMeasurable G volume)
    (hχ : AEStronglyMeasurable χ volume) (hG2 : Integrable (fun y => entrySq (G y)))
    (hχ2 : Integrable (fun y => entrySq (χ y))) : Integrable (fun y => entryInner (G y) (χ y)) := by
  unfold entryInner
  refine integrable_finsetSum _ fun i _ => ?_
  have m1 : AEStronglyMeasurable (fun y => G y (unitVector i)) volume := hG.apply_continuousLinearMap _
  have m2 : AEStronglyMeasurable (fun y => χ y (unitVector i)) volume := hχ.apply_continuousLinearMap _
  refine Integrable.mono' (hG2.add hχ2) (m1.inner m2) (Filter.Eventually.of_forall fun y => ?_)
  have a1 : ‖G y (unitVector i)‖ ^ 2 ≤ entrySq (G y) :=
    Finset.single_le_sum (f := fun j => ‖G y (unitVector j)‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have a2 : ‖χ y (unitVector i)‖ ^ 2 ≤ entrySq (χ y) :=
    Finset.single_le_sum (f := fun j => ‖χ y (unitVector j)‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have a3 : ‖inner ℝ (G y (unitVector i)) (χ y (unitVector i))‖ ≤ ‖G y (unitVector i)‖ * ‖χ y (unitVector i)‖ := by
    rw [Real.norm_eq_abs]; exact abs_real_inner_le_norm _ _
  show _ ≤ entrySq (G y) + entrySq (χ y)
  nlinarith [sq_nonneg (‖G y (unitVector i)‖ - ‖χ y (unitVector i)‖), norm_nonneg (G y (unitVector i)),
    norm_nonneg (χ y (unitVector i))]

theorem pins_sub {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) {v G H v' G' H'}
    (hs : IsSecondOrderField d.order v G H) (hs' : IsSecondOrderField d.order v' G' H') :
    d.pins (fun y => G y - G' y) = d.pins G - d.pins G' := by
  funext i
  simp only [FracCertData.pins, pinValue, Pi.sub_apply]
  have e : ∀ y, entryInner (G y - G' y) (d.pin i y) = entryInner (G y) (d.pin i y) - entryInner (G' y) (d.pin i y) := by
    intro y; simp only [entryInner, ContinuousLinearMap.sub_apply, inner_sub_left, Finset.sum_sub_distrib]
  simp_rw [e]
  exact integral_sub (entryInner_integrable hs.measurable_gradient (hd.pin_measurable i).1 hs.gradient_two (hd.pin_two i).1)
    (entryInner_integrable hs'.measurable_gradient (hd.pin_measurable i).1 hs'.gradient_two (hd.pin_two i).1)

theorem radius_facts {α : ℝ} {d : FracCertData k N} (hd : IsFracCert α d) :
    0 ≤ d.heldRadius ∧ d.sizeBound + d.rowConst * d.productConst * d.heldRadius ^ 2 ≤ d.heldRadius ∧
      2 * (d.rowConst * d.productConst) * d.heldRadius < 1 ∧ 0 ≤ d.rowConst := by
  have hth : 0 ≤ d.contraction := Real.sqrt_nonneg _
  have hth1 := hd.contraction_lt
  have hcp : 0 ≤ d.reducedGap := hd.reducedGap_pos.le
  have hRc : 0 ≤ d.rowConst := bc_nonneg hcp hth hth1 _ _
  have hρ : 0 ≤ d.sizeBound := le_trans (bc_nonneg hcp hth hth1 _ _) hd.size_ge
  have hP : 0 ≤ d.productConst := hd.productConst_nonneg
  set K := d.rowConst * d.productConst with hK
  have hK0 : 0 ≤ K := mul_nonneg hRc hP
  set ρ := d.sizeBound with hρdef
  have hsmall : 4 * K * ρ < 1 := by
    have := hd.size_small
    have e : 4 * d.rowConst * d.productConst * d.sizeBound = 4 * K * ρ := by rw [hK, hρdef]; ring
    linarith
  have hKρ : 0 ≤ 4 * K * ρ := by positivity
  set s := Real.sqrt (1 - 4 * d.rowConst * d.productConst * d.sizeBound) with hs
  have hs' : s = Real.sqrt (1 - 4 * K * ρ) := by rw [hs, hK, hρdef]; ring_nf
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = 1 - 4 * K * ρ := by rw [hs']; exact Real.sq_sqrt (by linarith)
  have hr : d.heldRadius = 2 * ρ / (1 + s) := rfl
  have h1s : 0 < 1 + s := by linarith
  have hr1 : d.heldRadius * (1 + s) = 2 * ρ := by rw [hr]; field_simp
  have hr0 : 0 ≤ d.heldRadius := by rw [hr]; positivity
  refine ⟨hr0, ?_, ?_, hRc⟩
  · have e : (ρ + K * d.heldRadius ^ 2 - d.heldRadius) * (1 + s) ^ 2 = ρ * (s ^ 2 - 1 + 4 * K * ρ) := by
      have : (ρ + K * d.heldRadius ^ 2 - d.heldRadius) * (1 + s) ^ 2 =
          ρ * (1 + s) ^ 2 + K * (d.heldRadius * (1 + s)) ^ 2 - (d.heldRadius * (1 + s)) * (1 + s) := by ring
      rw [this, hr1]; ring
    rw [hs2] at e
    have e2 : (ρ + K * d.heldRadius ^ 2 - d.heldRadius) * (1 + s) ^ 2 = 0 := by rw [e]; ring
    have hpos : (1 + s) ^ 2 ≠ 0 := by positivity
    have e3 : ρ + K * d.heldRadius ^ 2 - d.heldRadius = 0 := by
      rcases mul_eq_zero.1 e2 with h | h
      · exact h
      · exact absurd h hpos
    linarith
  · have e : 2 * K * d.heldRadius * (1 + s) = 4 * K * ρ := by
      calc 2 * K * d.heldRadius * (1 + s) = 2 * K * (d.heldRadius * (1 + s)) := by ring
        _ = 4 * K * ρ := by rw [hr1]; ring
    by_contra hcon
    have hcon' := not_lt.1 hcon
    have : 1 + s ≤ 2 * K * d.heldRadius * (1 + s) := by nlinarith
    linarith

end FracInternal.HeldExists

namespace SteadyCert

open FracInternal.HeldExists

theorem heldExists (h1 : LinearSolveStatement) (h2 : AprioriBoundStatement) (h3 : LinearStateClosedStatement)
    (h4 : SecondOrderLinearStatement) (h5 : QuadraticSquareIntegrableStatement) (h6 : GradientAddStatement)
    (h7 : WeakPowerSubStatement) (h8 : DefectRightSideStatement) : HeldExistsStatement := by
  intro α hα1 hα2 k N d hd p hp
  have hgadd := h6
  obtain ⟨hD, hcls⟩ := h8 α hα1 hα2 d hd p hp
  have hGu : ∀ u G H, IsSecondOrderField d.order u G H →
      MemLp (fun y => G y (u y)) 2 volume ∧ IsClassField d.order (fun y => -d.defect α p y - G y (u y)) :=
    fun u G H h => ⟨h5 _ u G H h, hcls u G H h⟩
  obtain ⟨hr0, hrfix, hq, hRc⟩ := radius_facts hd
  have hP0 : 0 ≤ d.productConst := hd.productConst_nonneg
  set r := d.heldRadius with hr
  set q := 2 * (d.rowConst * d.productConst) * r with hqdef
  have hq0 : 0 ≤ q := by positivity
  have hsol : ∀ s : HeldState k, ∃ t : HeldState k, IsSecondOrderField d.order s.v s.G s.H →
      d.IsLinearState α p t.v t.G t.H t.P ∧
      (∃ Q, IsGradientField Q ∧ ∀ᵐ y ∂volume,
        d.fullField α p t.v t.G t.H t.P t.κ y = -d.defect α p y - s.G y (s.v y) + Q y) ∧
      d.pins t.G = 0 := by
    intro s
    by_cases hs : IsSecondOrderField d.order s.v s.G s.H
    · obtain ⟨hm, hc⟩ := hGu s.v s.G s.H hs
      obtain ⟨v, G, H, P, κ, hL, ⟨Q, hQ, hE⟩, hpin⟩ :=
        h1 α hα1 hα2 d hd p hp (fun y => -d.defect α p y - s.G y (s.v y)) (hD.neg.sub hm) hc 0
      exact ⟨⟨v, G, H, P, κ⟩, fun _ => ⟨hL, ⟨Q, hQ, hE⟩, funext hpin⟩⟩
    · exact ⟨s, fun h => absurd h hs⟩
  choose T hT using hsol
  let s : ℕ → HeldState k := fun n => T^[n] HeldState.zero
  have hs_succ : ∀ n, s (n + 1) = T (s n) := fun n => Function.iterate_succ_apply' T n _
  have hgood : ∀ n, IsSecondOrderField d.order (s n).v (s n).G (s n).H := by
    intro n
    induction n with
    | zero => exact secondOrder_zero _
    | succ n ih => rw [hs_succ]; exact (hT (s n) ih).1.second
  have hspec : ∀ n, d.IsLinearState α p (s (n + 1)).v (s (n + 1)).G (s (n + 1)).H (s (n + 1)).P ∧
      (∃ Q, IsGradientField Q ∧ ∀ᵐ y ∂volume, d.fullField α p (s (n + 1)).v (s (n + 1)).G (s (n + 1)).H
        (s (n + 1)).P (s (n + 1)).κ y = -d.defect α p y - (s n).G y ((s n).v y) + Q y) ∧
      d.pins (s (n + 1)).G = 0 := fun n => by rw [hs_succ]; exact hT (s n) (hgood n)
  have hX : ∀ n, MemLp (fun y => (s n).G y ((s n).v y)) 2 volume := fun n => (hGu _ _ _ (hgood n)).1
  have hsz0 : ∀ n, 0 ≤ sz d (s n) := fun n => Real.sqrt_nonneg _
  have hsz : ∀ n, sz d (s n) ≤ r := by
    intro n
    induction n with
    | zero => show sz d HeldState.zero ≤ r; rw [size_zero]; exact hr0
    | succ n ih =>
      have hb := apriori_rhs hα1 hα2 hd h6 h2 hp (s (n + 1)) (hspec n).1 (d.defect α p) _ hD (hX n)
        (hspec n).2.1 (hspec n).2.2 (hd.defect_norm p hp) (hd.defect_rows p hp)
      have hps := product_self hd (hgood n)
      have hE := energy_le hd (s n).G (s n).H (s n).κ
      have hsq : sz d (s n) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (hsz0 n) ih 2
      have h3' : l2Norm (fun y => (s n).G y ((s n).v y)) ≤ d.productConst * r ^ 2 :=
        hps.trans (mul_le_mul_of_nonneg_left (hE.trans hsq) hP0)
      have hsg := hd.size_ge
      have h4' := mul_le_mul_of_nonneg_left h3' hRc
      calc sz d (s (n + 1)) ≤ d.sizeBound + d.rowConst * d.productConst * r ^ 2 := by nlinarith
        _ ≤ r := hrfix
  have hstep : ∀ a b, dsz d (s (a + 1)) (s (b + 1)) ≤ q * dsz d (s a) (s b) := by
    intro a b
    obtain ⟨hLa, ⟨Qa, hQa, hEa⟩, hpa⟩ := hspec a
    obtain ⟨hLb, ⟨Qb, hQb, hEb⟩, hpb⟩ := hspec b
    let t : HeldState k := ⟨fun y => (s (a + 1)).v y - (s (b + 1)).v y, fun y => (s (a + 1)).G y - (s (b + 1)).G y,
      fun y => (s (a + 1)).H y - (s (b + 1)).H y, fun y => (s (a + 1)).P y - (s (b + 1)).P y,
      fun i => (s (a + 1)).κ i - (s (b + 1)).κ i⟩
    have hLt : d.IsLinearState α p t.v t.G t.H t.P := lin_sub hα1 hα2 h7 h4 _ _ hLa hLb
    have hEt : ∃ Q, IsGradientField Q ∧ ∀ᵐ y ∂volume, d.fullField α p t.v t.G t.H t.P t.κ y =
        -(fun _ => (0 : Space)) y - (fun y => (s a).G y ((s a).v y) - (s b).G y ((s b).v y)) y + Q y := by
      refine ⟨fun y => Qa y + -Qb y, hgadd _ _ hQa (isGradientField_neg hQb), ?_⟩
      filter_upwards [hEa, hEb] with y hya hyb
      rw [fullField_sub d α p (s (a + 1)) (s (b + 1)) y, hya, hyb]
      simp only [neg_zero]
      abel
    have hpt : d.pins t.G = 0 := by
      rw [pins_sub hd hLa.second hLb.second, hpa, hpb, sub_zero]
    have hb := apriori_rhs hα1 hα2 hd h6 h2 hp t hLt (fun _ => (0 : Space)) (fun y => (s a).G y ((s a).v y) - (s b).G y ((s b).v y)) MemLp.zero' ((hX a).sub (hX b))
      hEt hpt projectedNorm_zero (rowsModGrad_zero d)
    rw [boundFn_zero, zero_add] at hb
    have hpb' := product_bound hd h5 h4 (hgood a) (hgood b)
    have hea := sqrt_energy_le hd (s a).G (s a).H (s a).κ
    have heb := sqrt_energy_le hd (s b).G (s b).H (s b).κ
    have hed := sqrt_energy_le hd (fun y => (s a).G y - (s b).G y) (fun y => (s a).H y - (s b).H y)
      (fun i => (s a).κ i - (s b).κ i)
    have hsum : Real.sqrt (d.energy (s a).G (s a).H) + Real.sqrt (d.energy (s b).G (s b).H) ≤ 2 * r := by
      have := hsz a; have := hsz b; unfold sz at *; linarith
    have hdd : 0 ≤ dsz d (s a) (s b) := dsz_nonneg d _ _
    have hbound : l2Norm (fun y => (s a).G y ((s a).v y) - (s b).G y ((s b).v y)) ≤
        d.productConst * dsz d (s a) (s b) * (2 * r) := by
      refine hpb'.trans ?_
      have h0 : 0 ≤ Real.sqrt (d.energy (fun y => (s a).G y - (s b).G y) (fun y => (s a).H y - (s b).H y)) :=
        Real.sqrt_nonneg _
      have h00 : 0 ≤ Real.sqrt (d.energy (s a).G (s a).H) + Real.sqrt (d.energy (s b).G (s b).H) := by positivity
      exact mul_le_mul (mul_le_mul_of_nonneg_left hed hP0) hsum h00 (mul_nonneg hP0 hdd)
    change dsz d (s (a + 1)) (s (b + 1)) ≤ _ at hb
    calc dsz d (s (a + 1)) (s (b + 1)) ≤ d.rowConst * (d.productConst * dsz d (s a) (s b) * (2 * r)) :=
          hb.trans (mul_le_mul_of_nonneg_left hbound hRc)
      _ = q * dsz d (s a) (s b) := by rw [hqdef]; ring
  have hiter : ∀ j a b, dsz d (s (a + j)) (s (b + j)) ≤ q ^ j * dsz d (s a) (s b) := by
    intro j
    induction j with
    | zero => intro a b; simp
    | succ j ih =>
      intro a b
      calc dsz d (s (a + (j + 1))) (s (b + (j + 1))) = dsz d (s (a + j + 1)) (s (b + j + 1)) := by
            rw [Nat.add_succ, Nat.add_succ]
        _ ≤ q * dsz d (s (a + j)) (s (b + j)) := hstep _ _
        _ ≤ q * (q ^ j * dsz d (s a) (s b)) := mul_le_mul_of_nonneg_left (ih a b) hq0
        _ = q ^ (j + 1) * dsz d (s a) (s b) := by ring
  have hfar : ∀ M x y, M ≤ x → M ≤ y → dsz d (s x) (s y) ≤ q ^ M * r := by
    intro M x y hx hy
    have hq1 : q ≤ 1 := hq.le
    rcases le_total x y with hxy | hxy
    · have h := hiter x 0 (y - x)
      rw [zero_add, Nat.sub_add_cancel hxy] at h
      have h0 : dsz d (s 0) (s (y - x)) ≤ r := by
        rw [dsz_comm]; show dsz d (s (y - x)) HeldState.zero ≤ r; rw [dsz_zero_right]; exact hsz _
      calc dsz d (s x) (s y) ≤ q ^ x * dsz d (s 0) (s (y - x)) := h
        _ ≤ q ^ M * r := mul_le_mul (pow_le_pow_of_le_one hq0 hq1 hx) h0 (dsz_nonneg _ _ _) (by positivity)
    · have h := hiter y (x - y) 0
      rw [zero_add, Nat.sub_add_cancel hxy] at h
      have h0 : dsz d (s (x - y)) (s 0) ≤ r := by
        show dsz d (s (x - y)) HeldState.zero ≤ r; rw [dsz_zero_right]; exact hsz _
      calc dsz d (s x) (s y) ≤ q ^ y * dsz d (s (x - y)) (s 0) := h
        _ ≤ q ^ M * r := mul_le_mul (pow_le_pow_of_le_one hq0 hq1 hy) h0 (dsz_nonneg _ _ _) (by positivity)
  have hsmall : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ x ≥ M, ∀ y ≥ M, dsz d (s x) (s y) < ε := by
    intro ε hε
    have hlim : Tendsto (fun M : ℕ => q ^ M * r) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq).mul_const r
    obtain ⟨M, hM⟩ := Filter.mem_atTop_sets.1 (hlim (Iio_mem_nhds hε))
    exact ⟨M, fun x hx y hy => (hfar M x y hx hy).trans_lt (hM M le_rfl)⟩
  let F : ℕ → Space → Space := fun n y => -d.defect α p y - (s n).G y ((s n).v y)
  have hF : ∀ n, MemLp (F n) 2 volume := fun n => hD.neg.sub (hX n)
  set c := d.productConst * (2 * r) with hc
  have hc0 : 0 ≤ c := by positivity
  have hXdiff : ∀ m n, l2Norm (fun y => (s m).G y ((s m).v y) - (s n).G y ((s n).v y)) ≤
      c * dsz d (s m) (s n) := by
    intro m n
    have hpb' := product_bound hd h5 h4 (hgood m) (hgood n)
    have hed := sqrt_energy_le hd (fun y => (s m).G y - (s n).G y) (fun y => (s m).H y - (s n).H y)
      (fun i => (s m).κ i - (s n).κ i)
    have hsum : Real.sqrt (d.energy (s m).G (s m).H) + Real.sqrt (d.energy (s n).G (s n).H) ≤ 2 * r := by
      have := sqrt_energy_le hd (s m).G (s m).H (s m).κ
      have := sqrt_energy_le hd (s n).G (s n).H (s n).κ
      have := hsz m; have := hsz n; unfold sz at *; linarith
    have h00 : 0 ≤ Real.sqrt (d.energy (s m).G (s m).H) + Real.sqrt (d.energy (s n).G (s n).H) := by positivity
    refine hpb'.trans ?_
    calc _ ≤ d.productConst * dsz d (s m) (s n) * (2 * r) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hed hP0) hsum h00 (mul_nonneg hP0 (dsz_nonneg _ _ _))
      _ = c * dsz d (s m) (s n) := by rw [hc]; ring
  have hFC : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n ≥ M, ∀ m ≥ M, l2Norm (fun y => F n y - F m y) < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hsmall (ε / (c + 1)) (div_pos hε (by linarith))
    refine ⟨M, fun n hn m hm => ?_⟩
    have heq : (fun y => F n y - F m y) = fun y => (s m).G y ((s m).v y) - (s n).G y ((s n).v y) := by
      funext y; simp only [F]; abel
    rw [heq]
    have h1' := hXdiff m n
    have h2' := hM m hm n hn
    have h3' : c * dsz d (s m) (s n) ≤ (c + 1) * dsz d (s m) (s n) := by
      nlinarith [dsz_nonneg d (s m) (s n)]
    have h4' : (c + 1) * dsz d (s m) (s n) < ε := by
      rw [lt_div_iff₀ (by linarith)] at h2'; linarith
    linarith
  obtain ⟨F₀, hF₀, hF₀t⟩ := l2_limit F hF hFC
  have hCa : ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ n ≥ M, ∀ n' ≥ M,
      d.size (fun y => (s (n + 1)).G y - (s (n' + 1)).G y) (fun y => (s (n + 1)).H y - (s (n' + 1)).H y)
        (fun i => (s (n + 1)).κ i - (s (n' + 1)).κ i) < ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hsmall ε hε
    exact ⟨M, fun n hn n' hn' => hM (n + 1) (by omega) (n' + 1) (by omega)⟩
  obtain ⟨v₀, G₀, H₀, P₀, κ₀, hL₀, ⟨Q₀, hQ₀, hE₀⟩, hconv, -, hpins⟩ :=
    h3 α hα1 hα2 d hd p hp (fun n => (s (n + 1)).v) (fun n => (s (n + 1)).G) (fun n => (s (n + 1)).H)
      (fun n => (s (n + 1)).P) F (fun n => (s (n + 1)).κ) F₀ (fun n => (hspec n).1) (fun n => (hspec n).2.1)
      hF hF₀ hF₀t hCa
  let s₀ : HeldState k := ⟨v₀, G₀, H₀, P₀, κ₀⟩
  have hpin0 : d.pins G₀ = 0 := by
    have hc' : (fun n => d.pins (s (n + 1)).G) = fun _ => 0 := funext fun n => (hspec n).2.2
    rw [hc'] at hpins
    exact (tendsto_nhds_unique tendsto_const_nhds hpins).symm
  have hX₀ : MemLp (fun y => G₀ y (v₀ y)) 2 volume := (hGu _ _ _ hL₀.second).1
  have hconv' : Tendsto (fun n => dsz d (s (n + 1)) s₀) atTop (𝓝 0) := hconv
  have hE₀0 : 0 ≤ Real.sqrt (d.energy G₀ H₀) := Real.sqrt_nonneg _
  have hX0diff : ∀ n, l2Norm (fun y => G₀ y (v₀ y) - (s (n + 1)).G y ((s (n + 1)).v y)) ≤
      d.productConst * dsz d (s (n + 1)) s₀ * (Real.sqrt (d.energy G₀ H₀) + r) := by
    intro n
    have hpb' := product_bound hd h5 h4 hL₀.second (hgood (n + 1))
    have hed := sqrt_energy_le hd (fun y => G₀ y - (s (n + 1)).G y) (fun y => H₀ y - (s (n + 1)).H y)
      (fun i => κ₀ i - (s (n + 1)).κ i)
    have hn := sqrt_energy_le hd (s (n + 1)).G (s (n + 1)).H (s (n + 1)).κ
    have hn' := hsz (n + 1)
    unfold sz at hn'
    have hsw : d.size (fun y => G₀ y - (s (n + 1)).G y) (fun y => H₀ y - (s (n + 1)).H y)
        (fun i => κ₀ i - (s (n + 1)).κ i) = dsz d (s (n + 1)) s₀ := dsz_comm d s₀ (s (n + 1))
    rw [hsw] at hed
    refine hpb'.trans ?_
    exact mul_le_mul (mul_le_mul_of_nonneg_left hed hP0) (by linarith)
      (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)) (mul_nonneg hP0 (dsz_nonneg _ _ _))
  have hlim0 : Tendsto (fun n => d.productConst * dsz d (s (n + 1)) s₀ * (Real.sqrt (d.energy G₀ H₀) + r))
      atTop (𝓝 0) := by
    simpa using (hconv'.const_mul d.productConst).mul_const (Real.sqrt (d.energy G₀ H₀) + r)
  let F' : Space → Space := fun y => -d.defect α p y - G₀ y (v₀ y)
  have hF' : MemLp F' 2 volume := hD.neg.sub hX₀
  have hFF' : Tendsto (fun n => l2Norm (fun y => F (n + 1) y - F' y)) atTop (𝓝 0) := by
    refine squeeze_zero (fun n => l2Norm_nonneg _) (fun n => ?_) hlim0
    have heq : (fun y => F (n + 1) y - F' y) = fun y => G₀ y (v₀ y) - (s (n + 1)).G y ((s (n + 1)).v y) := by
      funext y; simp only [F, F']; abel
    rw [heq]; exact hX0diff n
  have hFeq : F₀ =ᵐ[volume] F' :=
    l2_unique (fun n => F (n + 1)) F₀ F' (fun n => hF (n + 1)) hF₀ hF'
      (hF₀t.comp (tendsto_add_atTop_nat 1)) hFF'
  have hEq₀ : ∀ᵐ y ∂volume, d.fullField α p v₀ G₀ H₀ P₀ κ₀ y = -d.defect α p y - G₀ y (v₀ y) + Q₀ y := by
    filter_upwards [hE₀, hFeq] with y hy1 hy2
    rw [hy1, hy2]
  refine ⟨v₀, G₀, H₀, P₀, κ₀, ⟨hL₀, ⟨fun y => -Q₀ y, isGradientField_neg hQ₀, ?_⟩, fun i => congrFun hpin0 i⟩, ?_⟩
  · filter_upwards [hEq₀] with y hy
    rw [hy]; abel
  · have hb := apriori_rhs hα1 hα2 hd h6 h2 hp s₀ hL₀ (d.defect α p) _ hD hX₀ ⟨Q₀, hQ₀, hEq₀⟩ hpin0
      (hd.defect_norm p hp) (hd.defect_rows p hp)
    have hXb : l2Norm (fun y => G₀ y (v₀ y)) ≤ d.productConst * r ^ 2 := by
      refine ge_of_tendsto' (f := fun n => d.productConst * r ^ 2 +
        d.productConst * dsz d (s (n + 1)) s₀ * (Real.sqrt (d.energy G₀ H₀) + r)) (x := atTop)
        (by have := hlim0.const_add (d.productConst * r ^ 2); rwa [add_zero] at this) (fun n => ?_)
      have ht := l2Norm_le_add_sub hX₀ (hX (n + 1))
      beta_reduce at ht
      show l2Norm _ ≤ d.productConst * r ^ 2 + d.productConst * dsz d (s (n + 1)) s₀ * (Real.sqrt (d.energy G₀ H₀) + r)
      have hps := product_self hd (hgood (n + 1))
      have hE := energy_le hd (s (n + 1)).G (s (n + 1)).H (s (n + 1)).κ
      have hsq : sz d (s (n + 1)) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ (hsz0 _) (hsz _) 2
      have h3' : l2Norm (fun y => (s (n + 1)).G y ((s (n + 1)).v y)) ≤ d.productConst * r ^ 2 :=
        hps.trans (mul_le_mul_of_nonneg_left (hE.trans hsq) hP0)
      linarith [hX0diff n]
    have hsg := hd.size_ge
    have h4' := mul_le_mul_of_nonneg_left hXb hRc
    show sz d s₀ ≤ r
    nlinarith

end SteadyCert

end Breakdown
