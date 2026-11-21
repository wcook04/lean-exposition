import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoerciveFieldModes
import Breakdown.Cert.CoerciveModeL2
import Breakdown.Cert.CoercivePerturbationFactsProof

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.Absorb

theorem mul_le_absorb {u v K : ℝ} (hK : 0 < K) : u * v ≤ u ^ 2 * K / 4 + v ^ 2 / K := by
  have h : 0 ≤ (u * K / 2 - v) ^ 2 / K := div_nonneg (sq_nonneg _) hK.le
  have e : (u * K / 2 - v) ^ 2 / K = u ^ 2 * K / 4 + v ^ 2 / K - u * v := by
    field_simp
    ring
  linarith

theorem mul_le_half {u v t : ℝ} (ht : 0 < t) : u * v ≤ (1 / 2) * t * u ^ 2 + (1 / 2) * v ^ 2 / t := by
  have h := mul_le_absorb (u := u) (v := v) (mul_pos two_pos ht)
  have e1 : u ^ 2 * (2 * t) / 4 = (1 / 2) * t * u ^ 2 := by ring
  have e2 : v ^ 2 / (2 * t) = (1 / 2) * v ^ 2 / t := by field_simp
  linarith

theorem ind_nonneg (p : Prop) : 0 ≤ ModeWeights.ind p := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem ind_le_one (p : Prop) : ModeWeights.ind p ≤ 1 := by
  unfold ModeWeights.ind
  split_ifs <;> norm_num

theorem ind_mono {p q : Prop} (h : p → q) : ModeWeights.ind p ≤ ModeWeights.ind q := by
  unfold ModeWeights.ind
  by_cases hp : p
  · simp [hp, h hp]
  · by_cases hq : q <;> simp [hp, hq]

theorem ind_of {p : Prop} (h : p) : ModeWeights.ind p = 1 := by
  unfold ModeWeights.ind
  simp [h]

theorem wave_absorb {e x a w s z : ℝ} (he : 0 ≤ e) (_hx : 0 ≤ x) (ha : 0 ≤ a) (haw : a ≤ w) (hs : 0 < s)
    (_hz : 0 ≤ z) :
    e * x * (a * z) ≤ e ^ 2 * w / (4 * s) * x ^ 2 * a + s * (a / w) * ModeWeights.ind (0 < e) * z ^ 2 := by
  have hw : 0 ≤ w := ha.trans haw
  have h2 : 0 ≤ s * (a / w) * ModeWeights.ind (0 < e) * z ^ 2 :=
    mul_nonneg (mul_nonneg (mul_nonneg hs.le (div_nonneg ha hw)) (ind_nonneg _)) (sq_nonneg _)
  have h1 : 0 ≤ e ^ 2 * w / (4 * s) * x ^ 2 * a :=
    mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (sq_nonneg _) hw) (by positivity)) (sq_nonneg _)) ha
  rcases he.eq_or_lt with he0 | hepos
  · subst he0
    simp only [zero_mul]
    linarith
  rcases hw.eq_or_lt with hw0 | hwpos
  · have : a = 0 := le_antisymm (hw0 ▸ haw) ha
    subst this
    simp only [zero_mul, mul_zero]
    linarith
  rw [ind_of hepos, mul_one]
  have hK : 0 < w / s := div_pos hwpos hs
  have hy := mul_le_absorb (u := e * x) (v := z) hK
  have e1 : (e * x) ^ 2 * (w / s) / 4 = e ^ 2 * w / (4 * s) * x ^ 2 := by
    field_simp
  have e2 : z ^ 2 / (w / s) = s / w * z ^ 2 := by
    field_simp
  have hm := mul_le_mul_of_nonneg_left hy ha
  have e3 : e * x * (a * z) = a * (e * x * z) := by ring
  have e4 : s * (a / w) * z ^ 2 = a * (s / w * z ^ 2) := by ring
  rw [e3, e4]
  rw [e1, e2] at hm
  linarith

theorem sq_norm_sub_le (a b : ℂ) : ‖a - b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h := norm_sub_le a b
  have h0 : 0 ≤ ‖a - b‖ := norm_nonneg _
  have h1 : ‖a - b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 := pow_le_pow_left₀ h0 h 2
  nlinarith [sq_nonneg (‖a‖ - ‖b‖)]

theorem cnormSq_nonneg' {β : Type*} [Fintype β] (x : β → ℂ) : 0 ≤ cnormSq x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem cnormSq_curlOfGrad_le (g : Fin 3 × Fin 3 → ℂ) : cnormSq (curlOfGrad g) ≤ 2 * cnormSq g := by
  have e0 : curlOfGrad g 0 = g (2, 1) - g (1, 2) := by
    simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]; ring
  have e1 : curlOfGrad g 1 = g (0, 2) - g (2, 0) := by
    simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]; ring
  have e2 : curlOfGrad g 2 = g (1, 0) - g (0, 1) := by
    simp [curlOfGrad, alternatingSymbol, Fin.sum_univ_three]; ring
  simp only [cnormSq, Fin.sum_univ_three, Fintype.sum_prod_type, e0, e1, e2]
  nlinarith [sq_norm_sub_le (g (2, 1)) (g (1, 2)), sq_norm_sub_le (g (0, 2)) (g (2, 0)),
    sq_norm_sub_le (g (1, 0)) (g (0, 1)), sq_nonneg ‖g (0, 0)‖, sq_nonneg ‖g (1, 1)‖, sq_nonneg ‖g (2, 2)‖]

theorem vortAmp_le (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    vortAmp G ι σ y ≤ Real.sqrt 2 * gradAmp G ι σ y := by
  unfold vortAmp gradAmp
  rw [← Real.sqrt_mul (by norm_num)]
  exact Real.sqrt_le_sqrt (cnormSq_curlOfGrad_le _)

theorem single_le_of_sum_le {s : Finset (ℤ × ℤ)} {f : ℤ × ℤ → ℝ} {c : ℝ} (hf : ∀ α, 0 ≤ f α)
    (hs : ∑ α ∈ s, f α ≤ c) {α : ℤ × ℤ} (hα : α ∈ s) : f α ≤ c :=
  (Finset.single_le_sum (fun β _ => hf β) hα).trans hs

theorem eps_core {s : Finset (ℤ × ℤ)} {eps epsG dop r perp s1 s2 Ω mV Ωg mVG rate w0 w1 wV w2 l2 nb
    xc xo x1 x0 : ℝ} {aW gW oW hW xc' xo' x1' x0' : ℤ × ℤ → ℝ}
    (heps : 0 ≤ eps) (hepsG : 0 ≤ epsG) (hr : r ≤ perp) (hs1 : 0 < eps + epsG → 0 < s1) (hs2 : 0 < s2)
    (hΩ0 : 0 ≤ Ω) (hΩ : Ω ≤ mV) (hΩg0 : 0 ≤ Ωg) (hΩg : Ωg ≤ mVG) (hl2 : 0 < l2)
    (hxc : 0 ≤ xc) (hxo : 0 ≤ xo) (hx1 : 0 ≤ x1) (hx0 : 0 ≤ x0) (hcurl : xo ≤ Real.sqrt 2 * x1)
    (ha : ∀ α, 0 ≤ aW α) (hg : ∀ α, 0 ≤ gW α) (ho : ∀ α, 0 ≤ oW α) (hh : ∀ α, 0 ≤ hW α)
    (hxc' : ∀ α, 0 ≤ xc' α) (hxo' : ∀ α, 0 ≤ xo' α) (hcurl' : ∀ α, xo' α ≤ Real.sqrt 2 * x1' α)
    (hw0 : ∑ α ∈ s, aW α ≤ w0) (hw1 : ∑ α ∈ s, gW α ≤ w1) (hwV : ∑ α ∈ s, oW α ≤ wV)
    (hw2 : ∑ α ∈ s, hW α ≤ w2) :
    (-(s1 * ModeWeights.ind (0 < eps + epsG) + s2 * ModeWeights.ind (0 < nb)) * xc ^ 2
      + (eps * |dop| - (eps * perp + epsG) ^ 2 / (4 * s1) - eps ^ 2 * w0 ^ 2 / (4 * s2)
          - eps * ((1 / 2) * mV + |rate| + (1 / 2) * w1 + (1 / 2) * wV + (1 / 2) * l2 * w2)) * xo ^ 2
      - (Real.sqrt 2 * eps * mV + nb * (w1 + (1 / 2) * wV)) * x1 ^ 2
      - (1 / 2) * nb * w2 / l2 * x0 ^ 2 - Real.sqrt 2 * eps * mVG * x1 * x0)
      + (s2 * ModeWeights.ind (0 < nb) * xc ^ 2 + nb * (w1 + (1 / 2) * wV) * x1 ^ 2
        + (1 / 2) * nb * w2 / l2 * x0 ^ 2)
    ≤ eps * |dop| * xo ^ 2
      + (-((eps * r + epsG) * xc * xo) - eps * ((1 / 2) * Ω + |rate|) * xo ^ 2 - eps * Ωg * x0 * xo
        - eps * Ω * x1 * xo
        - eps * xo * ∑ α ∈ s, (aW α * xc' α + gW α * xo' α + hW α * x0' α + oW α * x1' α))
      + ∑ α ∈ s, (s2 * (aW α / w0) * ModeWeights.ind (0 < eps) * xc' α ^ 2 + eps * gW α * x1' α ^ 2
        + (1 / 2) * eps * oW α * x1' α ^ 2 + (1 / 2) * eps * hW α / l2 * x0' α ^ 2) := by
  have hsq2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hw0n : 0 ≤ w0 := (Finset.sum_nonneg fun α _ => ha α).trans hw0
  have h1 : (eps * r + epsG) * xc * xo ≤ s1 * ModeWeights.ind (0 < eps + epsG) * xc ^ 2
      + (eps * perp + epsG) ^ 2 / (4 * s1) * xo ^ 2 := by
    rcases (add_nonneg heps hepsG).eq_or_lt with h0 | hpos
    · have e0 : eps = 0 := by linarith
      have g0 : epsG = 0 := by linarith
      subst e0 g0
      simp [ModeWeights.ind]
    have hs := hs1 hpos
    rw [ind_of hpos, mul_one]
    have hA : (eps * r + epsG) * (xc * xo) ≤ (eps * perp + epsG) * (xc * xo) :=
      mul_le_mul_of_nonneg_right (by nlinarith) (mul_nonneg hxc hxo)
    have hy := mul_le_absorb (u := (eps * perp + epsG) * xo) (v := xc) (inv_pos.2 hs)
    have e1 : ((eps * perp + epsG) * xo) ^ 2 * s1⁻¹ / 4 = (eps * perp + epsG) ^ 2 / (4 * s1) * xo ^ 2 := by
      field_simp
    have e2 : xc ^ 2 / s1⁻¹ = s1 * xc ^ 2 := by field_simp
    rw [e1, e2] at hy
    linear_combination hA + hy
  have h2 : eps * ((1 / 2) * Ω + |rate|) * xo ^ 2 ≤ eps * ((1 / 2) * mV + |rate|) * xo ^ 2 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (by linarith) heps) (sq_nonneg _)
  have h3 : eps * Ωg * x0 * xo ≤ Real.sqrt 2 * eps * mVG * x1 * x0 := by
    have hm : Ωg * xo ≤ mVG * (Real.sqrt 2 * x1) := mul_le_mul hΩg hcurl hxo (hΩg0.trans hΩg)
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg heps hx0)
    linear_combination this
  have h4 : eps * Ω * x1 * xo ≤ Real.sqrt 2 * eps * mV * x1 ^ 2 := by
    have hm : Ω * xo ≤ mV * (Real.sqrt 2 * x1) := mul_le_mul hΩ hcurl hxo (hΩ0.trans hΩ)
    have := mul_le_mul_of_nonneg_left hm (mul_nonneg heps hx1)
    linear_combination this
  have hα : ∀ α ∈ s, eps * xo * (aW α * xc' α + gW α * xo' α + hW α * x0' α + oW α * x1' α) ≤
      eps ^ 2 * w0 / (4 * s2) * xo ^ 2 * aW α + (1 / 2) * eps * xo ^ 2 * gW α
        + (1 / 2) * eps * l2 * xo ^ 2 * hW α + (1 / 2) * eps * xo ^ 2 * oW α
        + (s2 * (aW α / w0) * ModeWeights.ind (0 < eps) * xc' α ^ 2 + eps * gW α * x1' α ^ 2
          + (1 / 2) * eps * oW α * x1' α ^ 2 + (1 / 2) * eps * hW α / l2 * x0' α ^ 2) := by
    intro α hαs
    have ya := wave_absorb heps hxo (ha α) (single_le_of_sum_le ha hw0 hαs) hs2 (hxc' α)
    have sq' : xo' α ^ 2 ≤ 2 * x1' α ^ 2 := by
      have := pow_le_pow_left₀ (hxo' α) (hcurl' α) 2
      rw [mul_pow, hsq2] at this
      exact this
    have yg : xo * xo' α ≤ (1 / 2) * xo ^ 2 + x1' α ^ 2 := by nlinarith [sq_nonneg (xo - xo' α)]
    have yh : xo * x0' α ≤ (1 / 2) * l2 * xo ^ 2 + (1 / 2) * x0' α ^ 2 / l2 := mul_le_half hl2
    have yo : xo * x1' α ≤ (1 / 2) * xo ^ 2 + (1 / 2) * x1' α ^ 2 := by nlinarith [sq_nonneg (xo - x1' α)]
    have g' := mul_le_mul_of_nonneg_left yg (mul_nonneg heps (hg α))
    have h' := mul_le_mul_of_nonneg_left yh (mul_nonneg heps (hh α))
    have o' := mul_le_mul_of_nonneg_left yo (mul_nonneg heps (ho α))
    linear_combination ya + g' + h' + o'
  have hS := Finset.sum_le_sum hα
  have eS : ∑ α ∈ s, (eps ^ 2 * w0 / (4 * s2) * xo ^ 2 * aW α + (1 / 2) * eps * xo ^ 2 * gW α
        + (1 / 2) * eps * l2 * xo ^ 2 * hW α + (1 / 2) * eps * xo ^ 2 * oW α
        + (s2 * (aW α / w0) * ModeWeights.ind (0 < eps) * xc' α ^ 2 + eps * gW α * x1' α ^ 2
          + (1 / 2) * eps * oW α * x1' α ^ 2 + (1 / 2) * eps * hW α / l2 * x0' α ^ 2)) =
      eps ^ 2 * w0 / (4 * s2) * xo ^ 2 * ∑ α ∈ s, aW α + (1 / 2) * eps * xo ^ 2 * ∑ α ∈ s, gW α
        + (1 / 2) * eps * l2 * xo ^ 2 * ∑ α ∈ s, hW α + (1 / 2) * eps * xo ^ 2 * ∑ α ∈ s, oW α
        + ∑ α ∈ s, (s2 * (aW α / w0) * ModeWeights.ind (0 < eps) * xc' α ^ 2 + eps * gW α * x1' α ^ 2
          + (1 / 2) * eps * oW α * x1' α ^ 2 + (1 / 2) * eps * hW α / l2 * x0' α ^ 2) := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have eL : eps * xo * ∑ α ∈ s, (aW α * xc' α + gW α * xo' α + hW α * x0' α + oW α * x1' α) =
      ∑ α ∈ s, eps * xo * (aW α * xc' α + gW α * xo' α + hW α * x0' α + oW α * x1' α) := Finset.mul_sum _ _ _
  have ca : 0 ≤ eps ^ 2 * w0 / (4 * s2) * xo ^ 2 := by positivity
  have cg : 0 ≤ (1 / 2) * eps * xo ^ 2 := by positivity
  have ch : 0 ≤ (1 / 2) * eps * l2 * xo ^ 2 := by positivity
  have ka := mul_le_mul_of_nonneg_left hw0 ca
  have kg := mul_le_mul_of_nonneg_left hw1 cg
  have kh := mul_le_mul_of_nonneg_left hw2 ch
  have ko := mul_le_mul_of_nonneg_left hwV cg
  rw [eS] at hS
  rw [← eL] at hS
  linear_combination h1 + h2 + h3 + h4 + hS + ka + kg + kh + ko

theorem sum_sq_le_weighted {s : Finset (ℤ × ℤ)} {a z : ℤ × ℤ → ℝ} (ha : ∀ α, 0 ≤ a α) :
    (∑ α ∈ s, a α * z α) ^ 2 ≤ (∑ α ∈ s, a α) * ∑ α ∈ s, a α * z α ^ 2 :=
  Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul s (fun α _ => ha α)
    (fun α _ => mul_nonneg (ha α) (sq_nonneg _)) (fun α _ => le_of_eq (by ring))

theorem mu_core {s : Finset (ℤ × ℤ)} {mu muG dop r perp s4 rate w0 w1 cμ mG mGb eta etaMin nbm i1 i2
    x1 x0 : ℝ} {aW gW x1' x0' : ℤ × ℤ → ℝ}
    (hmu : 0 ≤ mu) (hr : r ≤ perp) (hs4 : 0 < s4) (hmG0 : 0 ≤ mG) (hmG : mG ≤ mGb)
    (heta : 0 < eta) (hetaMin : 0 < etaMin) (hle : etaMin ≤ eta) (hi1 : 0 ≤ i1)
    (hx1 : 0 ≤ x1) (hx0 : 0 ≤ x0) (ha : ∀ α, 0 ≤ aW α) (hg : ∀ α, 0 ≤ gW α)
    (hx1' : ∀ α, 0 ≤ x1' α) (hw0 : ∑ α ∈ s, aW α ≤ w0) (hw1 : ∑ α ∈ s, gW α ≤ w1) :
    (-s4 * ModeWeights.ind (0 < nbm) * x1 ^ 2
      + ((1 - cμ) * mu * |dop| - mu * |rate| - mu ^ 2 * w0 ^ 2 / (4 * s4)
          - ((mGb ^ 2 / eta + (1 / 2) * eta * mu ^ 2) * i1 + (w1 ^ 2 / etaMin) * i2)) * x0 ^ 2
      - (mu * perp + muG) * x1 * x0)
      + (s4 * ModeWeights.ind (0 < nbm) * x1 ^ 2 + i2 * (w1 ^ 2 / etaMin) * x0 ^ 2)
    ≤ (1 - cμ) * mu * |dop| * x0 ^ 2
      + (-((mu * r + muG) * x1 * x0) - mu * |rate| * x0 ^ 2 - mu * x0 * ∑ α ∈ s, aW α * x1' α
        - i1 * ((mG ^ 2 * x0 ^ 2 + (∑ α ∈ s, gW α * x0' α) ^ 2) / eta + (1 / 2) * eta * mu ^ 2 * x0 ^ 2))
      + ∑ α ∈ s, (s4 * (aW α / w0) * ModeWeights.ind (0 < mu) * x1' α ^ 2
        + i1 * (w1 / etaMin) * gW α * x0' α ^ 2) := by
  have hw1n : 0 ≤ w1 := (Finset.sum_nonneg fun α _ => hg α).trans hw1
  have hw0n : 0 ≤ w0 := (Finset.sum_nonneg fun α _ => ha α).trans hw0
  have k1 : (mu * r + muG) * x1 * x0 ≤ (mu * perp + muG) * x1 * x0 :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (by nlinarith) hx1) hx0
  have hα : ∀ α ∈ s, mu * x0 * (aW α * x1' α) ≤ mu ^ 2 * w0 / (4 * s4) * x0 ^ 2 * aW α
      + s4 * (aW α / w0) * ModeWeights.ind (0 < mu) * x1' α ^ 2 := fun α hαs =>
    wave_absorb hmu hx0 (ha α) (single_le_of_sum_le ha hw0 hαs) hs4 (hx1' α)
  have hS := Finset.sum_le_sum hα
  have eS : ∑ α ∈ s, (mu ^ 2 * w0 / (4 * s4) * x0 ^ 2 * aW α
      + s4 * (aW α / w0) * ModeWeights.ind (0 < mu) * x1' α ^ 2) =
      mu ^ 2 * w0 / (4 * s4) * x0 ^ 2 * ∑ α ∈ s, aW α
        + ∑ α ∈ s, s4 * (aW α / w0) * ModeWeights.ind (0 < mu) * x1' α ^ 2 := by
    simp only [Finset.sum_add_distrib, Finset.mul_sum]
  have eL : mu * x0 * ∑ α ∈ s, aW α * x1' α = ∑ α ∈ s, mu * x0 * (aW α * x1' α) := Finset.mul_sum _ _ _
  rw [eS, ← eL] at hS
  have ka := mul_le_mul_of_nonneg_left hw0 (by positivity : 0 ≤ mu ^ 2 * w0 / (4 * s4) * x0 ^ 2)
  set Q := ∑ α ∈ s, gW α * x0' α ^ 2 with hQ
  have hQ0 : 0 ≤ Q := Finset.sum_nonneg fun α _ => mul_nonneg (hg α) (sq_nonneg _)
  have cs : (∑ α ∈ s, gW α * x0' α) ^ 2 ≤ w1 * Q :=
    (sum_sq_le_weighted hg).trans (mul_le_mul_of_nonneg_right hw1 hQ0)
  have c2 : (∑ α ∈ s, gW α * x0' α) ^ 2 / eta ≤ w1 * Q / etaMin :=
    (div_le_div_of_nonneg_right cs heta.le).trans (div_le_div_of_nonneg_left (mul_nonneg hw1n hQ0) hetaMin hle)
  have c1 : mG ^ 2 * x0 ^ 2 / eta ≤ mGb ^ 2 * x0 ^ 2 / eta :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hmG0 hmG 2) (sq_nonneg _)) heta.le
  have k3 : i1 * ((mG ^ 2 * x0 ^ 2 + (∑ α ∈ s, gW α * x0' α) ^ 2) / eta + (1 / 2) * eta * mu ^ 2 * x0 ^ 2)
      ≤ i1 * (mGb ^ 2 * x0 ^ 2 / eta + w1 * Q / etaMin + (1 / 2) * eta * mu ^ 2 * x0 ^ 2) := by
    apply mul_le_mul_of_nonneg_left _ hi1
    rw [add_div]
    linarith
  have eQ : ∑ α ∈ s, i1 * (w1 / etaMin) * gW α * x0' α ^ 2 = i1 * (w1 / etaMin) * Q := by
    rw [hQ, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [Finset.sum_add_distrib, eQ]
  linear_combination k1 + hS + ka + k3

theorem ofReal_eq_max (x : ℝ) : ENNReal.ofReal x = ENNReal.ofReal (max x 0) := by
  rcases le_total x 0 with h | h
  · rw [ENNReal.ofReal_of_nonpos h, max_eq_right h, ENNReal.ofReal_zero]
  · rw [max_eq_left h]

theorem max_split (x : ℝ) : max x 0 = x + max (-x) 0 := by
  rcases le_total x 0 with h | h
  · rw [max_eq_right h, max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h, max_eq_right (by linarith)]
    ring

theorem tsum_cancel {s : Finset (ℤ × ℤ)} {mT P R D : ℤ × ℤ → ℝ} {E : ℤ × ℤ → ℤ × ℤ → ℝ}
    (hP : ∀ ι, 0 ≤ P ι) (hD : ∀ ι, 0 ≤ D ι) (hE : ∀ α ι, 0 ≤ E α ι)
    (hA : ∀ ι, mT ι + D ι ≤ P ι + R ι + ∑ α ∈ s, E α ι)
    (hB : ∀ ι, ∑ α ∈ s, E α (ι + α) ≤ D ι)
    (hfin : ∑' ι, ENNReal.ofReal (D ι) ≠ ⊤) :
    (∑' ι, ENNReal.ofReal (mT ι)) + ∑' ι, ENNReal.ofReal (-R ι) ≤
      (∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (R ι)) + ∑' ι, ENNReal.ofReal (-mT ι) := by
  have per : ∀ ι, ENNReal.ofReal (mT ι) + ENNReal.ofReal (-R ι) + ENNReal.ofReal (D ι) ≤
      ENNReal.ofReal (P ι) + ENNReal.ofReal (R ι) + ∑ α ∈ s, ENNReal.ofReal (E α ι)
        + ENNReal.ofReal (-mT ι) := by
    intro ι
    rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => hE α ι), ofReal_eq_max (mT ι), ofReal_eq_max (-R ι),
      ofReal_eq_max (R ι), ofReal_eq_max (-mT ι),
      ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _),
      ← ENNReal.ofReal_add (add_nonneg (le_max_right _ _) (le_max_right _ _)) (hD ι),
      ← ENNReal.ofReal_add (hP ι) (le_max_right _ _),
      ← ENNReal.ofReal_add (add_nonneg (hP ι) (le_max_right _ _))
        (Finset.sum_nonneg fun α _ => hE α ι),
      ← ENNReal.ofReal_add (add_nonneg (add_nonneg (hP ι) (le_max_right _ _))
        (Finset.sum_nonneg fun α _ => hE α ι)) (le_max_right _ _)]
    apply ENNReal.ofReal_le_ofReal
    have a1 := max_split (mT ι)
    have a2 := max_split (R ι)
    have := hA ι
    linarith
  have hsum := ENNReal.tsum_le_tsum per
  simp only [ENNReal.tsum_add] at hsum
  have hsw : ∑' ι, ∑ α ∈ s, ENNReal.ofReal (E α ι) ≤ ∑' ι, ENNReal.ofReal (D ι) := by
    rw [Summable.tsum_finsetSum (fun α _ => ENNReal.summable)]
    have e : ∀ α ∈ s, ∑' ι, ENNReal.ofReal (E α ι) = ∑' ι, ENNReal.ofReal (E α (ι + α)) := by
      intro α _
      exact ((Equiv.addRight α).tsum_eq (fun ι => ENNReal.ofReal (E α ι))).symm
    rw [Finset.sum_congr rfl e, ← Summable.tsum_finsetSum (fun α _ => ENNReal.summable)]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    rw [← ENNReal.ofReal_sum_of_nonneg (fun α _ => hE α _)]
    exact ENNReal.ofReal_le_ofReal (hB ι)
  have key : (∑' ι, ENNReal.ofReal (mT ι)) + (∑' ι, ENNReal.ofReal (-R ι)) + ∑' ι, ENNReal.ofReal (D ι) ≤
      (∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (R ι)) + ∑' ι, ENNReal.ofReal (-mT ι)
        + ∑' ι, ENNReal.ofReal (D ι) := by
    calc _ ≤ _ := hsum
      _ ≤ (∑' ι, ENNReal.ofReal (P ι)) + (∑' ι, ENNReal.ofReal (R ι)) + (∑' ι, ENNReal.ofReal (D ι))
            + ∑' ι, ENNReal.ofReal (-mT ι) := by gcongr
      _ = _ := by ring
  exact ENNReal.le_of_add_le_add_right hfin key

theorem lintegral_add_left_iter {f g : ℝ → Space → ℝ≥0∞}
    (hf : AEMeasurable (fun z : ℝ × Space => f z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume)) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y) =
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, g σ y := by
  have h1 : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), AEMeasurable (fun y => f σ y) volume := by
    filter_upwards [hf.aestronglyMeasurable.prodMk_left] with σ hσ
    exact hσ.aemeasurable
  have h2 : ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (f σ y + g σ y) =
      ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, f σ y) + ∫⁻ y, g σ y) :=
    lintegral_congr_ae (h1.mono fun σ hσ => lintegral_add_left' hσ _)
  rw [h2, lintegral_add_left' (hf.lintegral_prod_right')]

theorem integrate_step {A B p r q : ℝ → Space → ℝ≥0∞} {X : ℝ}
    (hp : AEMeasurable (fun z : ℝ × Space => p z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (hr : AEMeasurable (fun z : ℝ × Space => r z.1 z.2) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume))
    (hpt : ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y, A σ y + (r σ y + q σ y) ≤ p σ y + B σ y)
    (hqB : ∀ σ y, q σ y ≤ B σ y)
    (h1 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, r σ y) < ⊤)
    (h2 : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, p σ y) + ENNReal.ofReal (-X) ≤
      ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (r σ y + q σ y)) :
    (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y) + ENNReal.ofReal (-X) ≤
      ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, B σ y := by
  by_cases hq : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, q σ y) = ⊤
  · have : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, B σ y) = ⊤ :=
      top_unique (hq ▸ lintegral_mono fun σ => lintegral_mono fun y => hqB σ y)
    rw [this, add_top]
    exact le_top
  have hrq := lintegral_add_left_iter (g := q) hr
  have hfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, r σ y) + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, q σ y) ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨h1.ne, hq⟩
  have hsup : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (r σ y + q σ y) ≤
      (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, p σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, B σ y := by
    calc _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ((∫⁻ y, A σ y) + ∫⁻ y, (r σ y + q σ y)) := le_lintegral_add _ _
      _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (A σ y + (r σ y + q σ y)) :=
          lintegral_mono fun σ => le_lintegral_add _ _
      _ ≤ ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (p σ y + B σ y) :=
          lintegral_mono_ae (hpt.mono fun σ hσ => lintegral_mono_ae hσ)
      _ = _ := lintegral_add_left_iter hp
  rw [hrq] at hsup h2
  refine ENNReal.le_of_add_le_add_right hfin ?_
  calc _ = ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, A σ y) + ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, r σ y)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, q σ y))) + ENNReal.ofReal (-X) := by ring
    _ ≤ ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, p σ y) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, B σ y)
        + ENNReal.ofReal (-X) := by gcongr
    _ = ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, p σ y) + ENNReal.ofReal (-X))
        + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, B σ y := by ring
    _ ≤ (ENNReal.ofReal X + ((∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, r σ y)
        + (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, q σ y))) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, B σ y := by gcongr
    _ = _ := by ring

section Concrete

variable {C : Type} (m : ModeWeights C) (b : FlowBounds C) (W v : ℝ → Space → Space)
  (G : ℝ → Space → (Space →L[ℝ] Space)) (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space)

def epsShift (α ι : ℤ × ℤ) : ℝ :=
  m.share2 y * (velAmp W α σ y / b.wave0 y) * ModeWeights.ind (0 < m.eps ι y) * vortGradAmp H (ι - α) σ y ^ 2
    + m.eps ι y * gradAmp (gradField W) α σ y * gradAmp G (ι - α) σ y ^ 2
    + (1 / 2) * m.eps ι y * vortAmp (gradField W) α σ y * gradAmp G (ι - α) σ y ^ 2
    + (1 / 2) * m.eps ι y * vortGradAmp (secondDerivField W) α σ y / m.len2 y * velAmp v (ι - α) σ y ^ 2

def muShift (α ι : ℤ × ℤ) : ℝ :=
  m.share4 y * (velAmp W α σ y / b.wave0 y) * ModeWeights.ind (0 < m.mu ι y) * gradAmp G (ι - α) σ y ^ 2
    + ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0) * (b.wave1 y / m.etaMin)
      * gradAmp (gradField W) α σ y * velAmp v (ι - α) σ y ^ 2

def epsDebt (ι : ℤ × ℤ) : ℝ :=
  m.share2 y * ModeWeights.ind (0 < m.epsNb ι y) * vortGradAmp H ι σ y ^ 2
    + m.epsNb ι y * (b.wave1 y + (1 / 2) * b.waveVort y) * gradAmp G ι σ y ^ 2
    + (1 / 2) * m.epsNb ι y * b.wave2 y / m.len2 y * velAmp v ι σ y ^ 2

def muDebt (ι : ℤ × ℤ) : ℝ :=
  m.share4 y * ModeWeights.ind (0 < m.muNb ι y) * gradAmp G ι σ y ^ 2
    + ModeWeights.ind (∃ α ∈ m.waves, ∃ x, m.muW (m.classOf (ι + α)) x ≠ 0) * (b.wave1 y ^ 2 / m.etaMin)
      * velAmp v ι σ y ^ 2

end Concrete

theorem density_split {C : Type} (m : ModeWeights C) (P : ℝ) (b : FlowBounds C) (w : Space → ℝ)
    (ι : ℤ × ℤ) (y : Space) (x2 xc x1 xo x0 : ℝ) :
    m.modeDensity P b w ι y x2 xc x1 xo x0 =
      baseDensity m.convD m.convZ (m.classOf ι) m.c w y x2 xc x1 xo x0
        + modeEpsDensity m P b ι y xc xo x1 x0 + modeMuDensity m P b ι y x1 x0 := by
  unfold ModeWeights.modeDensity baseDensity modeEpsDensity modeMuDensity ModeWeights.coefAA ModeWeights.coefC
  ring

variable {C : Type} {m : ModeWeights C} {P : ℝ} {b : FlowBounds C} {w : Space → ℝ} {W : ℝ → Space → Space}
  {w₀ epsSup epsGradSup ratio : ℝ}

theorem eps_mode (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeEpsDensity m P b ι y (vortGradAmp H ι σ y) (vortAmp G ι σ y) (gradAmp G ι σ y) (velAmp v ι σ y)
        + epsDebt m b v G H σ y ι
      ≤ modeEpsPos m P G ι σ y + modeEpsRest m W v G H ι σ y
        + ∑ α ∈ m.waves, epsShift m b W v G H σ y α ι := by
  have key := eps_core (s := m.waves) (eps := m.eps ι y) (epsG := m.epsGrad ι y) (dop := m.dop P ι y)
    (r := ‖relativeVelocity W (m.rate (m.classOf ι)) y‖) (perp := b.perpSpeed (m.classOf ι) y)
    (s1 := m.share1 (m.classOf ι) y) (s2 := m.share2 y) (Ω := ‖curlVec (fderiv ℝ (meanField W) y)‖)
    (mV := b.meanVort y) (Ωg := ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) y‖)
    (mVG := b.meanVortGrad y) (rate := m.rate (m.classOf ι) y) (w0 := b.wave0 y) (w1 := b.wave1 y)
    (wV := b.waveVort y) (w2 := b.wave2 y) (l2 := m.len2 y) (nb := m.epsNb ι y)
    (xc := vortGradAmp H ι σ y) (xo := vortAmp G ι σ y) (x1 := gradAmp G ι σ y) (x0 := velAmp v ι σ y)
    (aW := fun α => velAmp W α σ y) (gW := fun α => gradAmp (gradField W) α σ y)
    (oW := fun α => vortAmp (gradField W) α σ y) (hW := fun α => vortGradAmp (secondDerivField W) α σ y)
    (xc' := fun α => vortGradAmp H (ι - α) σ y) (xo' := fun α => vortAmp G (ι - α) σ y)
    (x1' := fun α => gradAmp G (ι - α) σ y) (x0' := fun α => velAmp v (ι - α) σ y)
    (abs_nonneg _) (norm_nonneg _) (hb.perpSpeed_ge _ _) (hm.share1_pos ι y) (hm.share2_pos y)
    (norm_nonneg _) (hb.meanVort_ge y) (norm_nonneg _) (hb.meanVortGrad_ge y) (hm.len2_pos y)
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) (vortAmp_le G ι σ y)
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    (fun α => vortAmp_le G (ι - α) σ y) (hb.wave0_ge σ y) (hb.wave1_ge σ y) (hb.waveVort_ge σ y)
    (hb.wave2_ge σ y)
  unfold modeEpsDensity ModeWeights.shareHat ModeWeights.coefA modeEpsPos modeEpsRest epsDebt epsShift
  linear_combination key

theorem mu_mode (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    modeMuDensity m P b ι y (gradAmp G ι σ y) (velAmp v ι σ y) + muDebt m b v G σ y ι
      ≤ modeMuPos m P v ι σ y + modeMuRest m W v G ι σ y + ∑ α ∈ m.waves, muShift m b W v G σ y α ι := by
  have key := mu_core (s := m.waves) (mu := m.mu ι y) (muG := m.muGrad ι y) (dop := m.dop P ι y)
    (r := ‖relativeVelocity W (m.rate (m.classOf ι)) y‖) (perp := b.perpSpeed (m.classOf ι) y)
    (s4 := m.share4 y) (rate := m.rate (m.classOf ι) y) (w0 := b.wave0 y) (w1 := b.wave1 y) (cμ := m.cμ)
    (mG := ‖fderiv ℝ (meanField W) y‖) (mGb := b.meanGrad y) (eta := m.eta (m.classOf ι))
    (etaMin := m.etaMin) (nbm := m.muNb ι y) (i1 := ModeWeights.ind (∃ x, m.muW (m.classOf ι) x ≠ 0))
    (i2 := ModeWeights.ind (∃ α ∈ m.waves, ∃ x, m.muW (m.classOf (ι + α)) x ≠ 0))
    (x1 := gradAmp G ι σ y) (x0 := velAmp v ι σ y) (aW := fun α => velAmp W α σ y)
    (gW := fun α => gradAmp (gradField W) α σ y) (x1' := fun α => gradAmp G (ι - α) σ y)
    (x0' := fun α => velAmp v (ι - α) σ y)
    (abs_nonneg _) (hb.perpSpeed_ge _ _) (hm.share4_pos y) (norm_nonneg _) (hb.meanGrad_ge y)
    (hm.eta_pos _) hm.etaMin_pos (hm.etaMin_le _) (ind_nonneg _) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _)
    (hb.wave0_ge σ y) (hb.wave1_ge σ y)
  unfold modeMuDensity ModeWeights.coefB ModeWeights.penalty modeMuPos modeMuRest muDebt muShift
  linear_combination key

theorem mode_step (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    m.modeTerm P b w v G H ι σ y + (epsDebt m b v G H σ y ι + muDebt m b v G σ y ι)
      ≤ modePos m P v G ι σ y + modeRest m w W v G H ι σ y
        + ∑ α ∈ m.waves, (epsShift m b W v G H σ y α ι + muShift m b W v G σ y α ι) := by
  have h1 := eps_mode hm hb v G H ι σ y
  have h2 := mu_mode hm hb v G ι σ y
  have e : m.modeTerm P b w v G H ι σ y = m.modeDensity P b w ι y (secondDerivAmp H ι σ y) (vortGradAmp H ι σ y)
      (gradAmp G ι σ y) (vortAmp G ι σ y) (velAmp v ι σ y) := rfl
  rw [e, density_split, Finset.sum_add_distrib]
  unfold modePos modeRest modeVals
  linear_combination h1 + h2

theorem eps_le_epsNb (m : ModeWeights C) {ι α : ℤ × ℤ} (y : Space) (hα : α ∈ m.waves) :
    m.eps (ι + α) y ≤ m.epsNb ι y := by
  unfold ModeWeights.eps ModeWeights.epsNb
  have h := NNReal.coe_le_coe.2 (Finset.le_sup (f := fun α => ‖m.epsW (m.classOf (ι + α)) y‖₊) hα)
  simpa [Real.norm_eq_abs] using h

theorem mu_le_muNb (m : ModeWeights C) {ι α : ℤ × ℤ} (y : Space) (hα : α ∈ m.waves) :
    m.mu (ι + α) y ≤ m.muNb ι y := by
  unfold ModeWeights.mu ModeWeights.muNb
  have h := NNReal.coe_le_coe.2 (Finset.le_sup (f := fun α => ‖m.muW (m.classOf (ι + α)) y‖₊) hα)
  simpa [Real.norm_eq_abs] using h

theorem shift_le_debt (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) (ι : ℤ × ℤ) :
    ∑ α ∈ m.waves, (epsShift m b W v G H σ y α (ι + α) + muShift m b W v G σ y α (ι + α))
      ≤ epsDebt m b v G H σ y ι + muDebt m b v G σ y ι := by
  have hw0n : 0 ≤ b.wave0 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave0_ge σ y)
  have hw1n : 0 ≤ b.wave1 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave1_ge σ y)
  have hs2 := hm.share2_pos y
  have hs4 := hm.share4_pos y
  have hl2 := hm.len2_pos y
  have het := hm.etaMin_pos
  have hxc : 0 ≤ vortGradAmp H ι σ y ^ 2 := sq_nonneg _
  have hx1 : 0 ≤ gradAmp G ι σ y ^ 2 := sq_nonneg _
  have hx0 : 0 ≤ velAmp v ι σ y ^ 2 := sq_nonneg _
  have hα : ∀ α ∈ m.waves, epsShift m b W v G H σ y α (ι + α) + muShift m b W v G σ y α (ι + α) ≤
      (m.share2 y * ModeWeights.ind (0 < m.epsNb ι y) * vortGradAmp H ι σ y ^ 2
          + m.share4 y * ModeWeights.ind (0 < m.muNb ι y) * gradAmp G ι σ y ^ 2) * (velAmp W α σ y / b.wave0 y)
        + (m.epsNb ι y * gradAmp G ι σ y ^ 2
          + ModeWeights.ind (∃ β ∈ m.waves, ∃ x, m.muW (m.classOf (ι + β)) x ≠ 0) * (b.wave1 y / m.etaMin)
            * velAmp v ι σ y ^ 2) * gradAmp (gradField W) α σ y
        + ((1 / 2) * m.epsNb ι y * gradAmp G ι σ y ^ 2) * vortAmp (gradField W) α σ y
        + ((1 / 2) * m.epsNb ι y / m.len2 y * velAmp v ι σ y ^ 2) * vortGradAmp (secondDerivField W) α σ y := by
    intro α hα
    unfold epsShift muShift
    simp only [add_sub_cancel_right]
    have e1 := eps_le_epsNb m y (ι := ι) hα
    have e2 := mu_le_muNb m y (ι := ι) hα
    have i1 : ModeWeights.ind (0 < m.eps (ι + α) y) ≤ ModeWeights.ind (0 < m.epsNb ι y) :=
      ind_mono fun h => h.trans_le e1
    have i2 : ModeWeights.ind (0 < m.mu (ι + α) y) ≤ ModeWeights.ind (0 < m.muNb ι y) :=
      ind_mono fun h => h.trans_le e2
    have i3 : ModeWeights.ind (∃ x, m.muW (m.classOf (ι + α)) x ≠ 0) ≤
        ModeWeights.ind (∃ β ∈ m.waves, ∃ x, m.muW (m.classOf (ι + β)) x ≠ 0) :=
      ind_mono fun h => ⟨α, hα, h⟩
    have ha : 0 ≤ velAmp W α σ y / b.wave0 y := div_nonneg (Real.sqrt_nonneg _) hw0n
    have hg : 0 ≤ gradAmp (gradField W) α σ y := Real.sqrt_nonneg _
    have ho : 0 ≤ vortAmp (gradField W) α σ y := Real.sqrt_nonneg _
    have hh : 0 ≤ vortGradAmp (secondDerivField W) α σ y := Real.sqrt_nonneg _
    have t1 := mul_le_mul_of_nonneg_left i1 (mul_nonneg (mul_nonneg hs2.le ha) hxc)
    have t2 := mul_le_mul_of_nonneg_left e1 (mul_nonneg hg hx1)
    have t3 := mul_le_mul_of_nonneg_left e1 (mul_nonneg ho hx1)
    have t4 := mul_le_mul_of_nonneg_left e1 (mul_nonneg (div_nonneg hh hl2.le) hx0)
    have t5 := mul_le_mul_of_nonneg_left i2 (mul_nonneg (mul_nonneg hs4.le ha) hx1)
    have t6 := mul_le_mul_of_nonneg_left i3 (mul_nonneg (mul_nonneg (div_nonneg hw1n het.le) hg) hx0)
    linear_combination t1 + t2 + (1 / 2 : ℝ) * t3 + (1 / 2 : ℝ) * t4 + t5 + t6
  have hS := Finset.sum_le_sum hα
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hS
  have hA : ∑ α ∈ m.waves, velAmp W α σ y / b.wave0 y ≤ 1 := by
    rw [← Finset.sum_div]
    exact div_le_one_of_le₀ (hb.wave0_ge σ y) hw0n
  have hnb : 0 ≤ m.epsNb ι y := NNReal.coe_nonneg _
  have k1 := mul_le_mul_of_nonneg_left hA (add_nonneg (mul_nonneg (mul_nonneg hs2.le (ind_nonneg (0 < m.epsNb ι y))) hxc)
    (mul_nonneg (mul_nonneg hs4.le (ind_nonneg (0 < m.muNb ι y))) hx1))
  have k2 := mul_le_mul_of_nonneg_left (hb.wave1_ge σ y) (add_nonneg (mul_nonneg hnb hx1)
    (mul_nonneg (mul_nonneg (ind_nonneg (∃ β ∈ m.waves, ∃ x, m.muW (m.classOf (ι + β)) x ≠ 0)) (div_nonneg hw1n het.le)) hx0))
  have k3 := mul_le_mul_of_nonneg_left (hb.waveVort_ge σ y) (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hnb) hx1)
  have k4 := mul_le_mul_of_nonneg_left (hb.wave2_ge σ y)
    (mul_nonneg (div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hnb) hl2.le) hx0)
  rw [Finset.sum_add_distrib]
  unfold epsDebt muDebt
  unfold velAmp gradAmp vortAmp vortGradAmp at *
  linear_combination hS + k1 + k2 + k3 + k4

theorem shift_nonneg (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) (α ι : ℤ × ℤ) :
    0 ≤ epsShift m b W v G H σ y α ι + muShift m b W v G σ y α ι := by
  have hw0n : 0 ≤ b.wave0 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave0_ge σ y)
  have hw1n : 0 ≤ b.wave1 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave1_ge σ y)
  have hs2 := hm.share2_pos y
  have hs4 := hm.share4_pos y
  have hl2 := hm.len2_pos y
  have het := hm.etaMin_pos
  unfold epsShift muShift ModeWeights.eps ModeWeights.mu velAmp gradAmp vortAmp vortGradAmp ModeWeights.ind
  positivity

theorem debt_nonneg (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space) (ι : ℤ × ℤ) :
    0 ≤ epsDebt m b v G H σ y ι + muDebt m b v G σ y ι := by
  have hw1n : 0 ≤ b.wave1 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave1_ge σ y)
  have hwVn : 0 ≤ b.waveVort y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.waveVort_ge σ y)
  have hw2n : 0 ≤ b.wave2 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave2_ge σ y)
  have hs2 := hm.share2_pos y
  have hs4 := hm.share4_pos y
  have hl2 := hm.len2_pos y
  have het := hm.etaMin_pos
  unfold epsDebt muDebt ModeWeights.epsNb velAmp gradAmp vortGradAmp ModeWeights.ind
  positivity

theorem modePos_nonneg (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (v : ℝ → Space → Space)
    (G : ℝ → Space → (Space →L[ℝ] Space)) (σ : ℝ) (y : Space) (ι : ℤ × ℤ) :
    0 ≤ modePos m P v G ι σ y := by
  have hc : 0 ≤ 1 - m.cμ := by linarith [hm.cμ_lt_one]
  unfold modePos modeEpsPos modeMuPos ModeWeights.eps ModeWeights.mu
  exact add_nonneg (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (sq_nonneg _))
    (mul_nonneg (mul_nonneg (mul_nonneg hc (abs_nonneg _)) (abs_nonneg _)) (sq_nonneg _))

theorem epsNb_le (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (ι : ℤ × ℤ) (y : Space) :
    m.epsNb ι y ≤ epsSup := by
  have h0 : 0 ≤ epsSup := (abs_nonneg _).trans (hm.epsW_le (m.classOf ι) y)
  have hs : (m.waves.sup fun α => ‖m.epsW (m.classOf (ι + α)) y‖₊) ≤ epsSup.toNNReal :=
    Finset.sup_le fun α _ => by
      rw [← NNReal.coe_le_coe, coe_nnnorm, Real.coe_toNNReal _ h0]
      exact (Real.norm_eq_abs _).le.trans (hm.epsW_le _ _)
  unfold ModeWeights.epsNb
  calc _ ≤ ((epsSup.toNNReal : NNReal) : ℝ) := NNReal.coe_le_coe.2 hs
    _ = epsSup := Real.coe_toNNReal _ h0

theorem debt_tsum_ne_top (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (hS : ∑' ι, ENNReal.ofReal (velAmp v ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2) ≠ ⊤) :
    ∑' ι, ENNReal.ofReal (epsDebt m b v G H σ y ι + muDebt m b v G σ y ι) ≠ ⊤ := by
  have hw1n : 0 ≤ b.wave1 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave1_ge σ y)
  have hwVn : 0 ≤ b.waveVort y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.waveVort_ge σ y)
  have hw2n : 0 ≤ b.wave2 y := (Finset.sum_nonneg fun α _ => Real.sqrt_nonneg _).trans (hb.wave2_ge σ y)
  have hs2 := hm.share2_pos y
  have hs4 := hm.share4_pos y
  have hl2 := hm.len2_pos y
  have het := hm.etaMin_pos
  have h0 : 0 ≤ epsSup := (abs_nonneg _).trans (hm.epsW_le (m.classOf 0) y)
  set K := m.share2 y + epsSup * (b.wave1 y + (1 / 2) * b.waveVort y) + (1 / 2) * epsSup * b.wave2 y / m.len2 y
    + m.share4 y + b.wave1 y ^ 2 / m.etaMin with hK
  have hK0 : 0 ≤ K := by positivity
  have per : ∀ ι, epsDebt m b v G H σ y ι + muDebt m b v G σ y ι ≤
      K * (velAmp v ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2) := by
    intro ι
    have hnb := epsNb_le hm ι y
    have hnb0 : 0 ≤ m.epsNb ι y := NNReal.coe_nonneg _
    have xc := sq_nonneg (vortGradAmp H ι σ y)
    have x1 := sq_nonneg (gradAmp G ι σ y)
    have x0 := sq_nonneg (velAmp v ι σ y)
    have t1 := mul_le_mul_of_nonneg_left (ind_le_one (0 < m.epsNb ι y)) (mul_nonneg hs2.le xc)
    have t2 := mul_le_mul_of_nonneg_left hnb
      (mul_nonneg (add_nonneg hw1n (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hwVn)) x1)
    have t3 := mul_le_mul_of_nonneg_left hnb (mul_nonneg (div_nonneg hw2n hl2.le) x0)
    have t4 := mul_le_mul_of_nonneg_left (ind_le_one (0 < m.muNb ι y)) (mul_nonneg hs4.le x1)
    have t5 := mul_le_mul_of_nonneg_left (ind_le_one (∃ α ∈ m.waves, ∃ x, m.muW (m.classOf (ι + α)) x ≠ 0))
      (mul_nonneg (div_nonneg (sq_nonneg (b.wave1 y)) het.le) x0)
    have e1 : K - m.share2 y = epsSup * (b.wave1 y + (1 / 2) * b.waveVort y) + (1 / 2) * epsSup * b.wave2 y / m.len2 y
        + m.share4 y + b.wave1 y ^ 2 / m.etaMin := by rw [hK]; ring
    have e2 : K - (epsSup * (b.wave1 y + (1 / 2) * b.waveVort y) + m.share4 y) = m.share2 y
        + (1 / 2) * epsSup * b.wave2 y / m.len2 y + b.wave1 y ^ 2 / m.etaMin := by rw [hK]; ring
    have e3 : K - ((1 / 2) * epsSup * b.wave2 y / m.len2 y + b.wave1 y ^ 2 / m.etaMin) = m.share2 y
        + epsSup * (b.wave1 y + (1 / 2) * b.waveVort y) + m.share4 y := by rw [hK]; ring
    have c1 : 0 ≤ (K - m.share2 y) * vortGradAmp H ι σ y ^ 2 := mul_nonneg (by rw [e1]; positivity) xc
    have c2 : 0 ≤ (K - (epsSup * (b.wave1 y + (1 / 2) * b.waveVort y) + m.share4 y)) * gradAmp G ι σ y ^ 2 :=
      mul_nonneg (by rw [e2]; positivity) x1
    have c3 : 0 ≤ (K - ((1 / 2) * epsSup * b.wave2 y / m.len2 y + b.wave1 y ^ 2 / m.etaMin))
        * velAmp v ι σ y ^ 2 := mul_nonneg (by rw [e3]; positivity) x0
    unfold epsDebt muDebt
    linear_combination t1 + t2 + (1 / 2 : ℝ) * t3 + t4 + t5 + c1 + c2 + c3
  refine ne_top_of_le_ne_top (b := ENNReal.ofReal K *
    ∑' ι, ENNReal.ofReal (velAmp v ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2))
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS) ?_
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun ι => ?_
  rw [← ENNReal.ofReal_mul hK0]
  exact ENNReal.ofReal_le_ofReal (per ι)

theorem cnormSq_curlGradOfSecondDeriv_le (h : Fin 3 × Fin 3 × Fin 3 → ℂ) :
    cnormSq (curlGradOfSecondDeriv h) ≤ 2 * cnormSq h := by
  have key : ∀ i l, curlGradOfSecondDeriv h (i, l) = curlOfGrad (fun p => h (p.1, l, p.2)) i := fun _ _ => rfl
  have h0 := cnormSq_curlOfGrad_le (fun p => h (p.1, 0, p.2))
  have h1 := cnormSq_curlOfGrad_le (fun p => h (p.1, 1, p.2))
  have h2 := cnormSq_curlOfGrad_le (fun p => h (p.1, 2, p.2))
  simp only [cnormSq, Fintype.sum_prod_type, Fin.sum_univ_three, key] at h0 h1 h2 ⊢
  linarith

theorem ac_slab : ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) ≪
    (volume : Measure (ℝ × Space)) := by
  rw [Measure.volume_eq_prod]
  exact Measure.AbsolutelyContinuous.prod (Measure.absolutelyContinuous_of_le Measure.restrict_le_self)
    Measure.AbsolutelyContinuous.rfl

theorem aesm_cnormSq {β : Type*} [Fintype β] {μ : Measure (ℝ × Space)} {a : ℝ × Space → β → ℂ}
    (ha : ∀ b, AEStronglyMeasurable (fun z => a z b) μ) : AEStronglyMeasurable (fun z => cnormSq (a z)) μ := by
  unfold cnormSq
  exact Finset.aestronglyMeasurable_fun_sum _ (fun b _ => (ha b).norm.pow 2)

theorem aem_ofReal_cnormSq {β : Type*} [Fintype β] {a : ℝ × Space → β → ℂ}
    (ha : ∀ b, AEStronglyMeasurable (fun z => a z b) volume) :
    AEMeasurable (fun z => ENNReal.ofReal (cnormSq (a z)))
      ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
  ((aesm_cnormSq ha).aemeasurable.ennreal_ofReal).mono_ac ac_slab

theorem aesm_modeSecondDeriv {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hH : AEStronglyMeasurable (fun z : ℝ × Space => H z.1 z.2) volume) (ι : ℤ × ℤ)
    (ijl : Fin 3 × Fin 3 × Fin 3) :
    AEStronglyMeasurable (fun z : ℝ × Space => modeSecondDeriv ι H z.1 z.2 ijl) volume := by
  have hc : Continuous (fun q : ℝ × (Space →L[ℝ] Space →L[ℝ] Space) =>
      axialRot (-q.1) (q.2 (axialRot q.1 (unitVector ijl.2.1)) (axialRot q.1 (unitVector ijl.2.2))) ijl.1) := by
    unfold axialRot
    fun_prop
  exact Internal.FieldModes.aestronglyMeasurable_modeAverage_comp ι ijl
    (E := Space →L[ℝ] Space →L[ℝ] Space)
    (fun (φ : ℝ) (A : Space →L[ℝ] Space →L[ℝ] Space) (k : Fin 3 × Fin 3 × Fin 3) =>
      axialRot (-φ) (A (axialRot φ (unitVector k.2.1)) (axialRot φ (unitVector k.2.2))) k.1) hc hH

theorem ae_of_tsum_lintegral {f : ℤ × ℤ → ℝ × Space → ℝ≥0∞}
    (hf : ∀ ι, AEMeasurable (f ι) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)))
    (h : ∑' ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f ι (σ, y) < ⊤) :
    ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)), ∑' ι, f ι z < ⊤ := by
  have e : ∀ ι, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f ι (σ, y) =
      ∫⁻ z, f ι z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)) :=
    fun ι => (lintegral_prod _ (hf ι)).symm
  simp only [e] at h
  rw [← lintegral_tsum hf] at h
  exact ae_lt_top' (AEMeasurable.ennreal_tsum hf) h.ne

theorem ae_amp_summable (hPars : ModeSquareSumHolds) {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    ∀ᵐ σ ∂(volume.restrict (Set.Icc (0 : ℝ) 1)), ∀ᵐ y,
      ∑' ι, ENNReal.ofReal (velAmp v ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2) ≠ ⊤ := by
  have hG : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ∑' ι, ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)) < ⊤ := by
    refine ae_of_tsum_lintegral (fun ι => aem_ofReal_cnormSq fun ij =>
      Internal.FieldModes.aestronglyMeasurable_modeGrad hv.measurable_gradient ι ij) ?_
    rw [← hPars.2.1 G hv.measurable_gradient hv.periodic_gradient hv.gradient_finite]
    exact hv.gradient_finite
  have hHf : periodLIntegral (fun σ y => secondDerivSq (H σ y)) < ⊤ :=
    (perturbationSecondDerivBoundHolds_proof _ _ _ _ _ _ hv).trans_lt hv.sumSecondPartials_finite
  have hH : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ∑' ι, ENNReal.ofReal (cnormSq (modeSecondDeriv ι H z.1 z.2)) < ⊤ := by
    refine ae_of_tsum_lintegral (fun ι => aem_ofReal_cnormSq fun ijl =>
      aesm_modeSecondDeriv hv.measurable_secondDeriv ι ijl) ?_
    rw [← hPars.2.2.1 H hv.measurable_secondDeriv hv.periodic_secondDeriv hHf]
    exact hHf
  have hV : ∀ n : ℕ, ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ∑' ι, ENNReal.ofReal (cnormSq (modeVel ι (Internal.FieldModes.ballPart n v) z.1 z.2)) < ⊤ := by
    intro n
    obtain ⟨h1, h2, h3⟩ := Internal.FieldModes.isSquareField_ballPart
      perturbationLocalSquareIntegrabilityHolds_proof hv n
    refine ae_of_tsum_lintegral (fun ι => aem_ofReal_cnormSq fun i =>
      Internal.FieldModes.aestronglyMeasurable_modeVel h1 ι i) ?_
    rw [← hPars.1 _ h1 h2 h3]
    exact h3
  have hall : ∀ᵐ z ∂((volume.restrict (Set.Icc (0 : ℝ) 1)).prod (volume : Measure Space)),
      ∑' ι, ENNReal.ofReal (velAmp v ι z.1 z.2 ^ 2 + gradAmp G ι z.1 z.2 ^ 2 + vortGradAmp H ι z.1 z.2 ^ 2)
        ≠ ⊤ := by
    filter_upwards [hG, hH, ae_all_iff.2 hV] with z hzG hzH hzV
    obtain ⟨n, hn⟩ := exists_nat_ge ‖z.2‖
    have e : ∀ ι, modeVel ι (Internal.FieldModes.ballPart n v) z.1 z.2 = modeVel ι v z.1 z.2 :=
      fun ι => Internal.FieldModes.modeVel_ballPart v ι z.1 hn
    have hvz := hzV n
    simp only [e] at hvz
    have h2 : ∑' ι, ENNReal.ofReal (2 * cnormSq (modeSecondDeriv ι H z.1 z.2)) ≠ ⊤ := by
      simp only [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
      rw [ENNReal.tsum_mul_left]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hzH.ne
    refine ne_top_of_le_ne_top (b := (∑' ι, ENNReal.ofReal (cnormSq (modeVel ι v z.1 z.2)))
      + (∑' ι, ENNReal.ofReal (cnormSq (modeGrad ι G z.1 z.2)))
      + ∑' ι, ENNReal.ofReal (2 * cnormSq (modeSecondDeriv ι H z.1 z.2)))
      (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hvz.ne, hzG.ne⟩, h2⟩) ?_
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun ι => ?_
    have a1 : velAmp v ι z.1 z.2 ^ 2 = cnormSq (modeVel ι v z.1 z.2) := Real.sq_sqrt (cnormSq_nonneg' _)
    have a2 : gradAmp G ι z.1 z.2 ^ 2 = cnormSq (modeGrad ι G z.1 z.2) := Real.sq_sqrt (cnormSq_nonneg' _)
    have a3 : vortGradAmp H ι z.1 z.2 ^ 2 ≤ 2 * cnormSq (modeSecondDeriv ι H z.1 z.2) := by
      unfold vortGradAmp
      rw [Real.sq_sqrt (cnormSq_nonneg' _)]
      exact cnormSq_curlGradOfSecondDeriv_le _
    rw [← ENNReal.ofReal_add (cnormSq_nonneg' _) (cnormSq_nonneg' _),
      ← ENNReal.ofReal_add (add_nonneg (cnormSq_nonneg' _) (cnormSq_nonneg' _))
        (mul_nonneg (by norm_num) (cnormSq_nonneg' _))]
    apply ENNReal.ofReal_le_ofReal
    linarith
  exact Measure.ae_ae_of_ae_prod hall

theorem pointwise (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio) (hb : b.IsValid m W)
    (v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
    (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)) (σ : ℝ) (y : Space)
    (hS : ∑' ι, ENNReal.ofReal (velAmp v ι σ y ^ 2 + gradAmp G ι σ y ^ 2 + vortGradAmp H ι σ y ^ 2) ≠ ⊤) :
    m.densityPos P b w v G H W σ y + (((∑' ι, ENNReal.ofReal (-modeRest m w W v G H ι σ y))
        + ENNReal.ofReal (-(0 : ℝ))) + ENNReal.ofReal (-stretchForm W v G σ y)) ≤
      ((∑' ι, ENNReal.ofReal (modePos m P v G ι σ y)) + (∑' ι, ENNReal.ofReal (modeRest m w W v G H ι σ y))
        + ENNReal.ofReal (0 : ℝ) + ENNReal.ofReal (stretchForm W v G σ y)) + m.densityNeg P b w v G H W σ y := by
  have hC := tsum_cancel (s := m.waves) (mT := fun ι => m.modeTerm P b w v G H ι σ y)
    (P := fun ι => modePos m P v G ι σ y) (R := fun ι => modeRest m w W v G H ι σ y)
    (D := fun ι => epsDebt m b v G H σ y ι + muDebt m b v G σ y ι)
    (E := fun α ι => epsShift m b W v G H σ y α ι + muShift m b W v G σ y α ι)
    (modePos_nonneg hm v G σ y) (debt_nonneg hm hb v G H σ y) (fun α ι => shift_nonneg hm hb v G H σ y α ι)
    (fun ι => mode_step hm hb v G H ι σ y) (shift_le_debt hm hb v G H σ y)
    (debt_tsum_ne_top hm hb v G H σ y hS)
  unfold ModeWeights.densityPos ModeWeights.densityNeg
  simp only [neg_zero, ENNReal.ofReal_zero, add_zero]
  calc _ = ((∑' ι, ENNReal.ofReal (m.modeTerm P b w v G H ι σ y))
          + ∑' ι, ENNReal.ofReal (-modeRest m w W v G H ι σ y))
          + (ENNReal.ofReal (stretchForm W v G σ y) + ENNReal.ofReal (-stretchForm W v G σ y)) := by ring
    _ ≤ ((∑' ι, ENNReal.ofReal (modePos m P v G ι σ y)) + (∑' ι, ENNReal.ofReal (modeRest m w W v G H ι σ y))
          + ∑' ι, ENNReal.ofReal (-m.modeTerm P b w v G H ι σ y))
          + (ENNReal.ofReal (stretchForm W v G σ y) + ENNReal.ofReal (-stretchForm W v G σ y)) := by
        gcongr
    _ = _ := by ring


theorem aem_velAmp' {X : ℝ → Space → Space} (hX : AEStronglyMeasurable (fun z : ℝ × Space => X z.1 z.2) volume)
    (ι : ℤ × ℤ) : AEMeasurable (fun z : ℝ × Space => velAmp X ι z.1 z.2) volume :=
  (aesm_cnormSq fun i => Internal.FieldModes.aestronglyMeasurable_modeVel hX ι i).aemeasurable.sqrt

theorem aem_gradAmp' {K : ℝ → Space → (Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => gradAmp K ι z.1 z.2) volume :=
  (aesm_cnormSq fun ij => Internal.FieldModes.aestronglyMeasurable_modeGrad hK ι ij).aemeasurable.sqrt

theorem aem_vortAmp' {K : ℝ → Space → (Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => vortAmp K ι z.1 z.2) volume := by
  refine (aesm_cnormSq fun i => ?_).aemeasurable.sqrt
  unfold curlOfGrad
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    (Internal.FieldModes.aestronglyMeasurable_modeGrad hK ι (l, j)).const_mul _

theorem aem_secondDerivAmp' {K : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => secondDerivAmp K ι z.1 z.2) volume :=
  (aesm_cnormSq fun ijl => aesm_modeSecondDeriv hK ι ijl).aemeasurable.sqrt

theorem aem_vortGradAmp' {K : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hK : AEStronglyMeasurable (fun z : ℝ × Space => K z.1 z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => vortGradAmp K ι z.1 z.2) volume := by
  refine (aesm_cnormSq fun il => ?_).aemeasurable.sqrt
  unfold curlGradOfSecondDeriv
  exact Finset.aestronglyMeasurable_fun_sum _ fun j _ => Finset.aestronglyMeasurable_fun_sum _ fun l _ =>
    (aesm_modeSecondDeriv hK ι (l, il.2, j)).const_mul _

theorem cont_gradField {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    ContDiff ℝ 1 (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2) :=
  ContDiff.fderiv (f := fun (p : ℝ × Space) (x : Space) => W p.1 x) (g := fun p => p.2)
    (hW.comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd (by norm_num)

theorem cont_secondDerivField {W : ℝ → Space → Space} (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) :
    Continuous (fun z : ℝ × Space => fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) :=
  (ContDiff.fderiv (m := 1) (n := 0) (f := fun (p : ℝ × Space) (x : Space) => fderiv ℝ (W p.1) x)
    (g := fun p => p.2) ((cont_gradField hW).comp (contDiff_fst.fst.prodMk contDiff_snd)) contDiff_snd
    (by norm_num)).continuous

theorem cont_modeVel_zero {W : ℝ → Space → Space} (hW : Continuous (fun z : ℝ × Space => W z.1 z.2))
    (i : Fin 3) : Continuous (fun y : Space => modeVel (0, 0) W 0 y i) := by
  unfold modeVel modeAverage
  refine continuous_const.mul ?_
  have hr : Continuous (fun q : (Space × ℝ) × ℝ => axialRot q.2 q.1.1) := by
    unfold axialRot
    fun_prop
  have hw : Continuous (fun q : (Space × ℝ) × ℝ => W (0 + q.1.2) (axialRot q.2 q.1.1)) :=
    hW.comp ((continuous_const.add continuous_fst.snd).prodMk hr)
  have hc : Continuous (fun p : ℝ × Space => axialRot (-p.1) p.2 i) := by
    unfold axialRot
    fun_prop
  have hR : Continuous (fun q : (Space × ℝ) × ℝ => axialRot (-q.2) (W (0 + q.1.2) (axialRot q.2 q.1.1)) i) :=
    Continuous.comp (g := fun p : ℝ × Space => axialRot (-p.1) p.2 i)
      (f := fun q : (Space × ℝ) × ℝ => (q.2, W (0 + q.1.2) (axialRot q.2 q.1.1))) hc (continuous_snd.prodMk hw)
  have hre : Continuous (fun q : (Space × ℝ) × ℝ =>
      (2 * Real.pi * ((((0, 0) : ℤ × ℤ).1 : ℤ) : ℝ) * q.1.2 + ((((0, 0) : ℤ × ℤ).2 : ℤ) : ℝ) * q.2)) := by
    fun_prop
  have he : Continuous (fun q : (Space × ℝ) × ℝ => Complex.exp (-(((2 * Real.pi * ((((0, 0) : ℤ × ℤ).1 : ℤ) : ℝ)
      * q.1.2 + ((((0, 0) : ℤ × ℤ).2 : ℤ) : ℝ) * q.2 : ℝ) : ℂ) * Complex.I))) :=
    Complex.continuous_exp.comp (((Complex.continuous_ofReal.comp hre).mul continuous_const).neg)
  have hF := he.mul (Complex.continuous_ofReal.comp hR)
  have h1 := intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun (p : Space × ℝ) (φ : ℝ) => Complex.exp (-(((2 * Real.pi * ((((0, 0) : ℤ × ℤ).1 : ℤ) : ℝ)
      * p.2 + ((((0, 0) : ℤ × ℤ).2 : ℤ) : ℝ) * φ : ℝ) : ℂ) * Complex.I))
        * ((axialRot (-φ) (W (0 + p.2) (axialRot φ p.1)) i : ℝ) : ℂ)) hF 0 (2 * Real.pi)
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' (μ := volume)
    (f := fun (y : Space) (τ : ℝ) => ∫ φ in (0 : ℝ)..(2 * Real.pi),
      Complex.exp (-(((2 * Real.pi * ((((0, 0) : ℤ × ℤ).1 : ℤ) : ℝ) * τ + ((((0, 0) : ℤ × ℤ).2 : ℤ) : ℝ) * φ : ℝ) : ℂ)
        * Complex.I)) * ((axialRot (-φ) (W (0 + τ) (axialRot φ y)) i : ℝ) : ℂ)) h1 0 1

theorem measurable_meanField {W : ℝ → Space → Space} (hW : Continuous (fun z : ℝ × Space => W z.1 z.2)) :
    Measurable (meanField W) := by
  unfold meanField
  exact Finset.measurable_sum _ fun i _ =>
    ((Complex.continuous_re.comp (cont_modeVel_zero hW i)).measurable.smul_const _)

theorem abs_aem {f : ℝ × Space → ℝ} (hf : AEMeasurable f volume) : AEMeasurable (fun z => |f z|) volume :=
  continuous_abs.measurable.comp_aemeasurable hf

theorem rest_aem {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (a1 : ∀ ι, AEMeasurable (fun z : ℝ × Space => velAmp v ι z.1 z.2) volume)
    (a2 : ∀ ι, AEMeasurable (fun z : ℝ × Space => gradAmp G ι z.1 z.2) volume)
    (a3 : ∀ ι, AEMeasurable (fun z : ℝ × Space => vortAmp G ι z.1 z.2) volume)
    (a4 : ∀ ι, AEMeasurable (fun z : ℝ × Space => secondDerivAmp H ι z.1 z.2) volume)
    (a5 : ∀ ι, AEMeasurable (fun z : ℝ × Space => vortGradAmp H ι z.1 z.2) volume)
    (b1 : ∀ ι, AEMeasurable (fun z : ℝ × Space => velAmp W ι z.1 z.2) volume)
    (b2 : ∀ ι, AEMeasurable (fun z : ℝ × Space => gradAmp (gradField W) ι z.1 z.2) volume)
    (b3 : ∀ ι, AEMeasurable (fun z : ℝ × Space => vortAmp (gradField W) ι z.1 z.2) volume)
    (b4 : ∀ ι, AEMeasurable (fun z : ℝ × Space => vortGradAmp (secondDerivField W) ι z.1 z.2) volume)
    (ye : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.eps ι z.2) volume)
    (ym : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.mu ι z.2) volume)
    (yeg : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.epsGrad ι z.2) volume)
    (ymg : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.muGrad ι z.2) volume)
    (yr : ∀ c, AEMeasurable (fun z : ℝ × Space => m.rate c z.2) volume)
    (yrel : ∀ c, AEMeasurable (fun z : ℝ × Space => ‖relativeVelocity W (m.rate c) z.2‖) volume)
    (yc : AEMeasurable (fun z : ℝ × Space => ‖curlVec (fderiv ℝ (meanField W) z.2)‖) volume)
    (ycg : AEMeasurable (fun z : ℝ × Space => ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2‖) volume)
    (ymgr : AEMeasurable (fun z : ℝ × Space => ‖fderiv ℝ (meanField W) z.2‖) volume)
    (yD : ∀ c, AEMeasurable (fun z : ℝ × Space => m.convD c z.2) volume)
    (yZ : ∀ c, AEMeasurable (fun z : ℝ × Space => m.convZ c z.2) volume)
    (yDh : ∀ c, AEMeasurable (fun z : ℝ × Space => ModeWeights.secondDerivNorm (m.convD c) z.2) volume)
    (yZh : ∀ c, AEMeasurable (fun z : ℝ × Space => ModeWeights.secondDerivNorm (m.convZ c) z.2) volume)
    (yw : AEMeasurable (fun z : ℝ × Space => w z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modeRest m w W v G H ι z.1 z.2) volume := by
  have hra := abs_aem (yr (m.classOf ι))
  have hS : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves,
      (velAmp W α z.1 z.2 * vortGradAmp H (ι - α) z.1 z.2 + gradAmp (gradField W) α z.1 z.2 * vortAmp G (ι - α) z.1 z.2
        + vortGradAmp (secondDerivField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2
        + vortAmp (gradField W) α z.1 z.2 * gradAmp G (ι - α) z.1 z.2)) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ =>
      ((((b1 α).mul (a5 _)).add ((b2 α).mul (a3 _))).add ((b4 α).mul (a1 _))).add ((b3 α).mul (a2 _))
  have hS1 : AEMeasurable (fun z : ℝ × Space => ∑ α ∈ m.waves, velAmp W α z.1 z.2 * gradAmp G (ι - α) z.1 z.2)
      volume := Finset.aemeasurable_fun_sum _ fun α _ => (b1 α).mul (a2 _)
  have hS2 : AEMeasurable (fun z : ℝ × Space =>
      ∑ α ∈ m.waves, gradAmp (gradField W) α z.1 z.2 * velAmp v (ι - α) z.1 z.2) volume :=
    Finset.aemeasurable_fun_sum _ fun α _ => (b2 α).mul (a1 _)
  have h1 : AEMeasurable (fun z : ℝ × Space => modeVals v G H ι z.1 z.2
      (baseDensity m.convD m.convZ (m.classOf ι) m.c w z.2)) volume := by
    unfold modeVals baseDensity
    exact ((((((yD _).sub aemeasurable_const).mul ((a4 ι).pow_const 2)).add
      ((aemeasurable_const.sub (yD _)).mul ((a5 ι).pow_const 2))).add
      ((aemeasurable_const.sub (yZ _)).mul ((a3 ι).pow_const 2))).add
      ((((yZ _).sub (yDh _)).sub (aemeasurable_const.mul yw)).mul ((a2 ι).pow_const 2))).sub
      ((yZh _).mul ((a1 ι).pow_const 2))
  have h2 : AEMeasurable (fun z : ℝ × Space => modeEpsRest m W v G H ι z.1 z.2) volume := by
    unfold modeEpsRest
    exact (((((((ye ι).mul (yrel _)).add (yeg ι)).mul (a5 ι)).mul (a3 ι)).neg.sub
      (((ye ι).mul ((aemeasurable_const.mul yc).add hra)).mul ((a3 ι).pow_const 2))).sub
      ((((ye ι).mul ycg).mul (a1 ι)).mul (a3 ι))).sub ((((ye ι).mul yc).mul (a2 ι)).mul (a3 ι)) |>.sub
      (((ye ι).mul (a3 ι)).mul hS)
  have h3 : AEMeasurable (fun z : ℝ × Space => modeMuRest m W v G ι z.1 z.2) volume := by
    unfold modeMuRest
    exact (((((((ym ι).mul (yrel _)).add (ymg ι)).mul (a2 ι)).mul (a1 ι)).neg.sub
      (((ym ι).mul hra).mul ((a1 ι).pow_const 2))).sub (((ym ι).mul (a1 ι)).mul hS1)).sub
      (aemeasurable_const.mul (((((ymgr.pow_const 2).mul ((a1 ι).pow_const 2)).add (hS2.pow_const 2)).div_const _).add
        ((aemeasurable_const.mul ((ym ι).pow_const 2)).mul ((a1 ι).pow_const 2))))
  unfold modeRest
  exact (h1.add h2).add h3

theorem pos_aem {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    (a1 : ∀ ι, AEMeasurable (fun z : ℝ × Space => velAmp v ι z.1 z.2) volume)
    (a3 : ∀ ι, AEMeasurable (fun z : ℝ × Space => vortAmp G ι z.1 z.2) volume)
    (ye : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.eps ι z.2) volume)
    (ym : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.mu ι z.2) volume)
    (ydop : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.dop P ι z.2) volume) (ι : ℤ × ℤ) :
    AEMeasurable (fun z : ℝ × Space => modePos m P v G ι z.1 z.2) volume := by
  have hd := continuous_abs.measurable.comp_aemeasurable (ydop ι)
  exact (((ye ι).mul hd).mul ((a3 ι).pow_const 2)).add
    (((aemeasurable_const.mul (ym ι)).mul hd).mul ((a1 ι).pow_const 2))

set_option maxHeartbeats 1000000 in
theorem stretch_aem {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
    (hvC : ∀ i, AEMeasurable (fun z : ℝ × Space => v z.1 z.2 i) volume)
    (hGC : ∀ j i, AEMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector j) i) volume)
    (hcG : ∀ i, AEMeasurable (fun z : ℝ × Space => curlVec (G z.1 z.2) i) volume)
    (hW1 : ∀ j i, AEMeasurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector j) i) volume)
    (hW2 : ∀ j k, AEMeasurable (fun z : ℝ × Space =>
      vortGrad (fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) j k) volume) :
    AEMeasurable (fun z : ℝ × Space => stretchForm W v G z.1 z.2) volume := by
  unfold stretchForm
  fun_prop

set_option maxHeartbeats 1000000 in
theorem aemeasurable_parts (hm : m.IsAdmissible P b w w₀ epsSup epsGradSup ratio)
    (hW : ContDiff ℝ 2 (fun z : ℝ × Space => W z.1 z.2)) {Γ : Set Symmetry} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hv : IsPerturbation Γ P v G H g) :
    AEMeasurable (fun z : ℝ × Space => (∑' ι, ENNReal.ofReal (modePos m P v G ι z.1 z.2))
        + (∑' ι, ENNReal.ofReal (modeRest m w W v G H ι z.1 z.2)) + ENNReal.ofReal (0 : ℝ)
        + ENNReal.ofReal (stretchForm W v G z.1 z.2)) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) ∧
    AEMeasurable (fun z : ℝ × Space => (∑' ι, ENNReal.ofReal (-modeRest m w W v G H ι z.1 z.2))
        + ENNReal.ofReal (-(0 : ℝ))) ((volume.restrict (Set.Icc (0 : ℝ) 1)).prod volume) := by
  have hWc : Continuous (fun z : ℝ × Space => W z.1 z.2) := hW.continuous
  have hgW : AEStronglyMeasurable (fun z : ℝ × Space => gradField W z.1 z.2) volume :=
    (cont_gradField hW).continuous.aestronglyMeasurable
  have hhW : AEStronglyMeasurable (fun z : ℝ × Space => secondDerivField W z.1 z.2) volume :=
    (cont_secondDerivField hW).aestronglyMeasurable
  have a1 := aem_velAmp' hv.measurable_velocity
  have a2 := aem_gradAmp' hv.measurable_gradient
  have a3 := aem_vortAmp' hv.measurable_gradient
  have a4 := aem_secondDerivAmp' hv.measurable_secondDeriv
  have a5 := aem_vortGradAmp' hv.measurable_secondDeriv
  have b1 := aem_velAmp' hWc.aestronglyMeasurable
  have b2 := aem_gradAmp' hgW
  have b3 := aem_vortAmp' hgW
  have b4 := aem_vortGradAmp' hhW
  have hcoord := ModeL2Internal.continuous_coord
  have ye : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.eps ι z.2) volume := fun ι => by
    obtain ⟨K, hK⟩ := hm.epsW_increment (m.classOf ι)
    exact (hK.continuous.abs.measurable.comp measurable_snd).aemeasurable
  have ym : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.mu ι z.2) volume := fun ι => by
    obtain ⟨K, hK⟩ := hm.muW_increment (m.classOf ι)
    exact (hK.continuous.abs.measurable.comp measurable_snd).aemeasurable
  have yeg : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.epsGrad ι z.2) volume := fun ι =>
    ((measurable_fderiv ℝ (m.epsW (m.classOf ι))).norm.comp measurable_snd).aemeasurable
  have ymg : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.muGrad ι z.2) volume := fun ι =>
    ((measurable_fderiv ℝ (m.muW (m.classOf ι))).norm.comp measurable_snd).aemeasurable
  have yr : ∀ c, AEMeasurable (fun z : ℝ × Space => m.rate c z.2) volume := fun c =>
    ((hm.rate_measurable c).comp measurable_snd).aemeasurable
  have ydop : ∀ ι, AEMeasurable (fun z : ℝ × Space => m.dop P ι z.2) volume := fun ι => by
    unfold ModeWeights.dop shiftedFrequency
    fun_prop
  have hmf := measurable_meanField hWc
  have yrel : ∀ c, AEMeasurable (fun z : ℝ × Space => ‖relativeVelocity W (m.rate c) z.2‖) volume := fun c => by
    have hrc := hm.rate_measurable c
    have h0 := (hcoord 0).measurable
    have h1 := (hcoord 1).measurable
    have hrel : Measurable (relativeVelocity W (m.rate c)) := by
      unfold relativeVelocity
      fun_prop
    exact (hrel.norm.comp measurable_snd).aemeasurable
  have hcv : Continuous curlVec := by
    unfold curlVec
    fun_prop
  have yc : AEMeasurable (fun z : ℝ × Space => ‖curlVec (fderiv ℝ (meanField W) z.2)‖) volume :=
    ((hcv.measurable.comp (measurable_fderiv ℝ (meanField W))).norm.comp measurable_snd).aemeasurable
  have ycg : AEMeasurable (fun z : ℝ × Space =>
      ‖fderiv ℝ (fun x => curlVec (fderiv ℝ (meanField W) x)) z.2‖) volume :=
    ((measurable_fderiv ℝ _).norm.comp measurable_snd).aemeasurable
  have ymgr : AEMeasurable (fun z : ℝ × Space => ‖fderiv ℝ (meanField W) z.2‖) volume :=
    ((measurable_fderiv ℝ _).norm.comp measurable_snd).aemeasurable
  have yD : ∀ c, AEMeasurable (fun z : ℝ × Space => m.convD c z.2) volume := fun c =>
    ((hm.convD_smooth c).continuous.measurable.comp measurable_snd).aemeasurable
  have yZ : ∀ c, AEMeasurable (fun z : ℝ × Space => m.convZ c z.2) volume := fun c =>
    ((hm.convZ_smooth c).continuous.measurable.comp measurable_snd).aemeasurable
  have yDh : ∀ c, AEMeasurable (fun z : ℝ × Space => ModeWeights.secondDerivNorm (m.convD c) z.2) volume := fun c =>
    (((hm.convD_smooth c).continuous_iteratedFDeriv (by norm_num)).norm.measurable.comp measurable_snd).aemeasurable
  have yZh : ∀ c, AEMeasurable (fun z : ℝ × Space => ModeWeights.secondDerivNorm (m.convZ c) z.2) volume := fun c =>
    (((hm.convZ_smooth c).continuous_iteratedFDeriv (by norm_num)).norm.measurable.comp measurable_snd).aemeasurable
  have yw : AEMeasurable (fun z : ℝ × Space => w z.2) volume := (hm.weight_measurable.comp measurable_snd).aemeasurable
  have hPos := pos_aem (m := m) (P := P) (G := G) a1 a3 ye ym ydop
  have hRest := rest_aem a1 a2 a3 a4 a5 b1 b2 b3 b4 ye ym yeg ymg yr yrel yc ycg ymgr yD yZ yDh yZh yw
  have hvC : ∀ i, AEMeasurable (fun z : ℝ × Space => v z.1 z.2 i) volume := fun i =>
    ((hcoord i).comp_aestronglyMeasurable hv.measurable_velocity).aemeasurable
  have hGC : ∀ j i, AEMeasurable (fun z : ℝ × Space => G z.1 z.2 (unitVector j) i) volume := fun j i =>
    (((hcoord i).comp (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous).comp_aestronglyMeasurable
      hv.measurable_gradient).aemeasurable
  have hcG : ∀ i, AEMeasurable (fun z : ℝ × Space => curlVec (G z.1 z.2) i) volume := fun i =>
    (((hcoord i).comp hcv).comp_aestronglyMeasurable hv.measurable_gradient).aemeasurable
  have hW1 : ∀ j i, AEMeasurable (fun z : ℝ × Space => fderiv ℝ (W z.1) z.2 (unitVector j) i) volume := fun j i =>
    (((hcoord i).comp (ContinuousLinearMap.apply ℝ Space (unitVector j)).continuous).comp
      (cont_gradField hW).continuous).measurable.aemeasurable
  have hvgc : ∀ j k, Continuous (fun A : Space →L[ℝ] Space →L[ℝ] Space => vortGrad A j k) := fun j k => by
    unfold vortGrad
    fun_prop
  have hW2 : ∀ j k, AEMeasurable (fun z : ℝ × Space =>
      vortGrad (fderiv ℝ (fun x => fderiv ℝ (W z.1) x) z.2) j k) volume := fun j k =>
    ((hvgc j k).comp (cont_secondDerivField hW)).measurable.aemeasurable
  have hJ := stretch_aem hvC hGC hcG hW1 hW2
  refine ⟨AEMeasurable.mono_ac ?_ ac_slab, AEMeasurable.mono_ac ?_ ac_slab⟩
  · exact (((AEMeasurable.ennreal_tsum fun ι => (hPos ι).ennreal_ofReal).add
      (AEMeasurable.ennreal_tsum fun ι => (hRest ι).ennreal_ofReal)).add aemeasurable_const).add
      hJ.ennreal_ofReal
  · exact (AEMeasurable.ennreal_tsum fun ι => (hRest ι).neg.ennreal_ofReal).add aemeasurable_const

end Internal.Absorb

open Internal.Absorb in
theorem modeAbsorbStepHolds_of (hPars : ModeSquareSumHolds) : ModeAbsorbStepHolds := by
  intro C m P b w Γ W w₀ epsSup epsGradSup ratio hm hb hW _ _ _ _ v G H g hv X hX
  obtain ⟨h1, h2⟩ := hX
  obtain ⟨hp, hr⟩ := aemeasurable_parts hm hW hv
  refine integrate_step (A := fun σ y => m.densityPos P b w v G H W σ y)
    (B := fun σ y => m.densityNeg P b w v G H W σ y)
    (p := fun σ y => (∑' ι, ENNReal.ofReal (modePos m P v G ι σ y))
      + (∑' ι, ENNReal.ofReal (modeRest m w W v G H ι σ y)) + ENNReal.ofReal (0 : ℝ)
      + ENNReal.ofReal (stretchForm W v G σ y))
    (r := fun σ y => (∑' ι, ENNReal.ofReal (-modeRest m w W v G H ι σ y)) + ENNReal.ofReal (-(0 : ℝ)))
    (q := fun σ y => ENNReal.ofReal (-stretchForm W v G σ y)) hp hr ?_ ?_ h1 h2
  · filter_upwards [ae_amp_summable hPars hv] with σ hσ
    filter_upwards [hσ] with y hy
    exact pointwise hm hb v G H σ y hy
  · intro σ y
    unfold ModeWeights.densityNeg
    exact le_add_self

end Coercive

end Breakdown
