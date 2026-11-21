import Breakdown.FracCell.GivenAuxDefs
import Breakdown.FracCell.GivenToolkit
import Mathlib.Analysis.Calculus.Rademacher

open scoped ContDiff ENNReal Topology
open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenFields

open SteadyCert

namespace PressureOpen

def shellSet (a b : ℝ) : Set Space := {z : Space | a ≤ ‖z‖ ∧ ‖z‖ ≤ b}

namespace PressureOpenInternal

theorem chartS_eq (P : ChartParams) (hP : IsChartParams P) (z : Space) :
    chartS P z = P.L0 / (‖z‖ + P.L0) := by
  have h : 0 < ‖z‖ + P.L0 := by have := hP.L0_pos; positivity
  unfold chartS chartT
  field_simp
  ring

theorem chartS_mem (P : ChartParams) (hP : IsChartParams P) (z : Space) :
    0 ≤ chartS P z ∧ chartS P z ≤ 1 := by
  rw [chartS_eq P hP]
  have h0 := hP.L0_pos
  have h : 0 < ‖z‖ + P.L0 := by positivity
  exact ⟨by positivity, (div_le_one h).2 (by linarith [norm_nonneg z])⟩

theorem chartT_mem (P : ChartParams) (hP : IsChartParams P) (z : Space) :
    0 ≤ chartT P z ∧ chartT P z ≤ 1 := by
  have h := chartS_mem P hP z
  unfold chartS at h
  constructor <;> linarith [h.1, h.2]

theorem chartS_le (P : ChartParams) (hP : IsChartParams P) {a : ℝ} (ha : 0 ≤ a) {z : Space} (hz : a ≤ ‖z‖) :
    chartS P z ≤ P.L0 / (a + P.L0) := by
  rw [chartS_eq P hP]
  have h0 := hP.L0_pos
  exact div_le_div_of_nonneg_left h0.le (by positivity) (by linarith)

theorem decay_mem (P : ChartParams) (hP : IsChartParams P) (z : Space) :
    0 ≤ decayFactor P z ∧ decayFactor P z ≤ 1 := by
  have h := chartS_mem P hP z
  have he := hP.eps_pos
  exact ⟨Real.rpow_nonneg h.1 _, Real.rpow_le_one h.1 h.2 (by positivity)⟩

theorem radial_norm_le (P : ChartParams) (hP : IsChartParams P) (k low high : ℕ) (hh : 2 ≤ high)
    {a : ℝ} (ha : 0 ≤ a) {z : Space} (hz : a ≤ ‖z‖) :
    ‖((decayFactor P z ^ k * chartT P z ^ low * chartS P z ^ high : ℝ) : ℂ)‖ ≤ (P.L0 / (a + P.L0)) ^ 2 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  obtain ⟨d0, d1⟩ := decay_mem P hP z
  obtain ⟨t0, t1⟩ := chartT_mem P hP z
  obtain ⟨s0, s1⟩ := chartS_mem P hP z
  have hs := chartS_le P hP ha hz
  rw [abs_of_nonneg (by positivity)]
  calc decayFactor P z ^ k * chartT P z ^ low * chartS P z ^ high ≤ 1 * 1 * chartS P z ^ 2 :=
        mul_le_mul (mul_le_mul (pow_le_one₀ d0 d1) (pow_le_one₀ t0 t1) (by positivity) zero_le_one)
          (pow_le_pow_of_le_one s0 s1 hh) (by positivity) (by positivity)
    _ = chartS P z ^ 2 := by ring
    _ ≤ (P.L0 / (a + P.L0)) ^ 2 := by gcongr

theorem qOf_mem (z : Space) : 0 ≤ qOf z ∧ qOf z ≤ 1 := by
  have hsq : (z 2) ^ 2 ≤ ‖z‖ ^ 2 := by
    have := EuclideanSpace.norm_eq z
    rw [this, Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
    nlinarith [sq_nonneg (z 0), sq_nonneg (z 1)]
  unfold qOf heightRatio
  constructor
  · by_cases h : ‖z‖ = 0
    · simp [h]
    · rw [div_pow, sub_nonneg, div_le_one (by positivity)]
      exact hsq
  · linarith [sq_nonneg (z 2 / ‖z‖)]

theorem angular_norm_le (P : ChartParams) (n : ℤ) (β : ℝ) (axis : ℕ) (z : Space) :
    ‖modePhase P n β z * ((qOf z ^ axis : ℝ) : ℂ)‖ ≤ 1 := by
  obtain ⟨q0, q1⟩ := qOf_mem z
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg q0 _)]
  have hp : ‖modePhase P n β z‖ = 1 := by
    unfold modePhase
    rw [Complex.norm_exp]
    simp
  rw [hp, one_mul]
  exact pow_le_one₀ q0 q1

theorem mul_sub_le (u v u' v' : ℂ) : ‖u * v - u' * v'‖ ≤ ‖u‖ * ‖v - v'‖ + ‖v'‖ * ‖u - u'‖ := by
  have : u * v - u' * v' = u * (v - v') + (u - u') * v' := by ring
  rw [this]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, mul_comm ‖u - u'‖]

theorem sum_shell {s : Finset ℤ} {F : ℤ → Space → ℂ} {U : Set Space}
    (h : ∀ n ∈ s, ∃ K : ℝ, ∀ x ∈ U, ∀ y ∈ U, ‖F n x - F n y‖ ≤ K * ‖x - y‖) :
    ∃ K : ℝ, ∀ x ∈ U, ∀ y ∈ U, ‖(∑ n ∈ s, F n x) - ∑ n ∈ s, F n y‖ ≤ K * ‖x - y‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun x _ y _ => by simp⟩
  | insert a s ha ih =>
    obtain ⟨K1, h1⟩ := ih fun n hn => h n (Finset.mem_insert_of_mem hn)
    obtain ⟨K2, h2⟩ := h a (Finset.mem_insert_self a s)
    refine ⟨K2 + K1, fun x hx y hy => ?_⟩
    simp only [Finset.sum_insert ha]
    have e : F a x + ∑ n ∈ s, F n x - (F a y + ∑ n ∈ s, F n y) =
        (F a x - F a y) + ((∑ n ∈ s, F n x) - ∑ n ∈ s, F n y) := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    have := h2 x hx y hy
    have := h1 x hx y hy
    linarith

end PressureOpenInternal

namespace PressureOpenInternal

theorem coord_abs_le (v : Space) (i : Fin 3) : |v i| ≤ ‖v‖ := by
  have := PiLp.norm_apply_le v i
  simpa [Real.norm_eq_abs] using this

theorem chartS_sub (P : ChartParams) (hP : IsChartParams P) {a : ℝ} (ha : 0 < a) {x y : Space}
    (hx : a ≤ ‖x‖) (hy : a ≤ ‖y‖) :
    |chartS P x - chartS P y| ≤ P.L0 / (a + P.L0) ^ 2 * ‖x - y‖ := by
  have hL := hP.L0_pos
  rw [chartS_eq P hP, chartS_eq P hP]
  have hx' : 0 < ‖x‖ + P.L0 := by positivity
  have hy' : 0 < ‖y‖ + P.L0 := by positivity
  have e : P.L0 / (‖x‖ + P.L0) - P.L0 / (‖y‖ + P.L0) = P.L0 * (‖y‖ - ‖x‖) / ((‖x‖ + P.L0) * (‖y‖ + P.L0)) := by
    field_simp; ring
  rw [e, abs_div, abs_mul, abs_of_pos hL, abs_of_pos (mul_pos hx' hy')]
  have h1 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y
  have h2 : (a + P.L0) ^ 2 ≤ (‖x‖ + P.L0) * (‖y‖ + P.L0) := by
    rw [sq]; exact mul_le_mul (by linarith) (by linarith) (by positivity) (by positivity)
  rw [div_le_iff₀ (mul_pos hx' hy')]
  calc P.L0 * |‖y‖ - ‖x‖| ≤ P.L0 * ‖x - y‖ := by gcongr
    _ = P.L0 / (a + P.L0) ^ 2 * ‖x - y‖ * (a + P.L0) ^ 2 := by field_simp
    _ ≤ P.L0 / (a + P.L0) ^ 2 * ‖x - y‖ * ((‖x‖ + P.L0) * (‖y‖ + P.L0)) := by gcongr

theorem chartT_sub (P : ChartParams) (hP : IsChartParams P) {a : ℝ} (ha : 0 < a) {x y : Space}
    (hx : a ≤ ‖x‖) (hy : a ≤ ‖y‖) :
    |chartT P x - chartT P y| ≤ P.L0 / (a + P.L0) ^ 2 * ‖x - y‖ := by
  have h := chartS_sub P hP ha hx hy
  unfold chartS at h
  rw [show 1 - chartT P x - (1 - chartT P y) = -(chartT P x - chartT P y) by ring, abs_neg] at h
  exact h

theorem ratio_sub {a : ℝ} (ha : 0 < a) {x y : Space} (hx : a ≤ ‖x‖) (hy : a ≤ ‖y‖) :
    |heightRatio x - heightRatio y| ≤ 2 / a * ‖x - y‖ := by
  unfold heightRatio
  have hx' : 0 < ‖x‖ := by linarith
  have hy' : 0 < ‖y‖ := by linarith
  have e : x 2 / ‖x‖ - y 2 / ‖y‖ = (x 2 - y 2) / ‖x‖ + y 2 * (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖) := by
    field_simp; ring
  rw [e]
  have h1 : |x 2 - y 2| ≤ ‖x - y‖ := by
    have := coord_abs_le (x - y) 2
    simpa using this
  have h2 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y
  have h3 := coord_abs_le y 2
  have hd := norm_nonneg (x - y)
  calc |(x 2 - y 2) / ‖x‖ + y 2 * (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)|
      ≤ |(x 2 - y 2) / ‖x‖| + |y 2 * (‖y‖ - ‖x‖) / (‖x‖ * ‖y‖)| := abs_add_le _ _
    _ = |x 2 - y 2| / ‖x‖ + |y 2| * |‖y‖ - ‖x‖| / (‖x‖ * ‖y‖) := by
        rw [abs_div, abs_div, abs_mul, abs_of_pos hx', abs_of_pos (mul_pos hx' hy')]
    _ ≤ ‖x - y‖ / a + ‖y‖ * ‖x - y‖ / (a * ‖y‖) := by
        gcongr
    _ = 2 / a * ‖x - y‖ := by field_simp; ring

theorem exp_sub_le {A B : ℝ} (hA : A ≤ 0) (hB : B ≤ 0) : |Real.exp A - Real.exp B| ≤ |A - B| := by
  wlog h : B ≤ A generalizing A B
  · rw [abs_sub_comm, abs_sub_comm A]; exact this hB hA (le_of_not_ge h)
  have h1 : Real.exp A - Real.exp B = Real.exp A * (1 - Real.exp (B - A)) := by
    rw [mul_sub, mul_one, ← Real.exp_add]; ring_nf
  have h2 : 1 - Real.exp (B - A) ≤ A - B := by linarith [Real.add_one_le_exp (B - A)]
  have h3 : 0 ≤ 1 - Real.exp (B - A) := by
    have : Real.exp (B - A) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
    linarith
  have h4 : Real.exp A ≤ 1 := Real.exp_le_one_iff.2 hA
  rw [h1, abs_of_nonneg (mul_nonneg (Real.exp_pos A).le h3), abs_of_nonneg (by linarith)]
  calc Real.exp A * (1 - Real.exp (B - A)) ≤ 1 * (A - B) := mul_le_mul h4 h2 h3 zero_le_one
    _ = A - B := one_mul _

theorem log_sub_le {u v c : ℝ} (hc : 0 < c) (hu : c ≤ u) (hv : c ≤ v) : |Real.log u - Real.log v| ≤ |u - v| / c := by
  wlog h : v ≤ u generalizing u v
  · rw [abs_sub_comm, abs_sub_comm u]; exact this hv hu (le_of_not_ge h)
  have hv0 : 0 < v := lt_of_lt_of_le hc hv
  have hu0 : 0 < u := lt_of_lt_of_le hc hu
  have h1 : Real.log u - Real.log v = Real.log (u / v) := (Real.log_div hu0.ne' hv0.ne').symm
  have h2 : Real.log (u / v) ≤ u / v - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : 0 ≤ Real.log u - Real.log v := by linarith [Real.log_le_log hv0 h]
  rw [abs_of_nonneg h3, abs_of_nonneg (by linarith)]
  calc Real.log u - Real.log v ≤ u / v - 1 := by rw [h1]; exact h2
    _ = (u - v) / v := by field_simp
    _ ≤ (u - v) / c := div_le_div_of_nonneg_left (by linarith) hc hv

theorem rpow_sub_le {u v c p : ℝ} (hc : 0 < c) (hu : c ≤ u) (hv : c ≤ v) (hu1 : u ≤ 1) (hv1 : v ≤ 1) (hp : 0 ≤ p) :
    |u ^ p - v ^ p| ≤ p * (|u - v| / c) := by
  have hu0 : 0 < u := lt_of_lt_of_le hc hu
  have hv0 : 0 < v := lt_of_lt_of_le hc hv
  rw [Real.rpow_def_of_pos hu0, Real.rpow_def_of_pos hv0]
  have hlu : Real.log u ≤ 0 := Real.log_nonpos hu0.le hu1
  have hlv : Real.log v ≤ 0 := Real.log_nonpos hv0.le hv1
  refine (exp_sub_le (by nlinarith) (by nlinarith)).trans ?_
  rw [← sub_mul, abs_mul, abs_of_nonneg hp, mul_comm]
  exact mul_le_mul_of_nonneg_left (log_sub_le hc hu hv) hp

theorem pow_sub_le {u v : ℝ} (n : ℕ) (hu : |u| ≤ 1) (hv : |v| ≤ 1) : |u ^ n - v ^ n| ≤ n * |u - v| := by
  have h := abs_pow_sub_pow_le u v n
  have hm : max |u| |v| ^ (n - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg u)) (max_le hu hv)
  calc |u ^ n - v ^ n| ≤ |u - v| * n * max |u| |v| ^ (n - 1) := h
    _ ≤ |u - v| * n * 1 := by gcongr
    _ = n * |u - v| := by ring

end PressureOpenInternal

open PressureOpenInternal

theorem radial_shell (P : ChartParams) (hP : IsChartParams P) (k low high : ℕ) (hh : 2 ≤ high) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ shellSet a b, ∀ y ∈ shellSet a b,
      ‖((decayFactor P x ^ k * chartT P x ^ low * chartS P x ^ high : ℝ) : ℂ) -
          ((decayFactor P y ^ k * chartT P y ^ low * chartS P y ^ high : ℝ) : ℂ)‖ ≤
        C * (1 + b / a) * (P.L0 / (a + P.L0)) ^ 2 / a * ‖x - y‖ := by
  have he := hP.eps_pos
  have hL := hP.L0_pos
  refine ⟨2 * P.eps * k + low + high, by positivity, fun a b ha hab x hx y hy => ?_⟩
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  set σ := P.L0 / (a + P.L0) with hσ
  set σb := P.L0 / (b + P.L0) with hσb
  set d := ‖x - y‖ with hd
  set δ := P.L0 / (a + P.L0) ^ 2 * d with hδ
  have hd0 : 0 ≤ d := norm_nonneg _
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hσb0 : 0 < σb := div_pos hL (by linarith)
  have hσ0 : 0 ≤ σ := by positivity
  have hσ1 : σ ≤ 1 := (div_le_one (by positivity)).2 (by linarith)
  have hδ0 : 0 ≤ δ := by positivity
  obtain ⟨sx0, sx1⟩ := chartS_mem P hP x
  obtain ⟨sy0, sy1⟩ := chartS_mem P hP y
  obtain ⟨tx0, tx1⟩ := chartT_mem P hP x
  obtain ⟨ty0, ty1⟩ := chartT_mem P hP y
  obtain ⟨dx0, dx1⟩ := decay_mem P hP x
  obtain ⟨dy0, dy1⟩ := decay_mem P hP y
  have hsxa : chartS P x ≤ σ := chartS_le P hP ha.le hx.1
  have hsya : chartS P y ≤ σ := chartS_le P hP ha.le hy.1
  have hsxb : σb ≤ chartS P x := by
    rw [chartS_eq P hP]; exact div_le_div_of_nonneg_left hL.le (by positivity) (by linarith [hx.2])
  have hsyb : σb ≤ chartS P y := by
    rw [chartS_eq P hP]; exact div_le_div_of_nonneg_left hL.le (by positivity) (by linarith [hy.2])
  have hds : |chartS P x - chartS P y| ≤ δ := chartS_sub P hP ha hx.1 hy.1
  have hdt : |chartT P x - chartT P y| ≤ δ := chartT_sub P hP ha hx.1 hy.1
  have hD : |decayFactor P x - decayFactor P y| ≤ 2 * P.eps * (δ / σb) := by
    unfold decayFactor
    refine (rpow_sub_le hσb0 hsxb hsyb sx1 sy1 (by positivity)).trans ?_
    gcongr
  have hDk : |decayFactor P x ^ k - decayFactor P y ^ k| ≤ k * (2 * P.eps * (δ / σb)) := by
    refine (pow_sub_le k (by rw [abs_of_nonneg dx0]; exact dx1) (by rw [abs_of_nonneg dy0]; exact dy1)).trans ?_
    gcongr
  have hTl : |chartT P x ^ low - chartT P y ^ low| ≤ low * δ := by
    refine (pow_sub_le low (by rw [abs_of_nonneg tx0]; exact tx1) (by rw [abs_of_nonneg ty0]; exact ty1)).trans ?_
    gcongr
  have hSh : |chartS P x ^ high - chartS P y ^ high| ≤ high * σ * δ := by
    refine (abs_pow_sub_pow_le _ _ high).trans ?_
    have hm : max |chartS P x| |chartS P y| ≤ σ := by
      rw [abs_of_nonneg sx0, abs_of_nonneg sy0]; exact max_le hsxa hsya
    have hm0 : 0 ≤ max |chartS P x| |chartS P y| := le_max_of_le_left (abs_nonneg _)
    have hp : max |chartS P x| |chartS P y| ^ (high - 1) ≤ σ :=
      (pow_le_pow_left₀ hm0 hm _).trans (pow_le_of_le_one hσ0 hσ1 (by omega))
    calc |chartS P x - chartS P y| * high * max |chartS P x| |chartS P y| ^ (high - 1) ≤ δ * high * σ := by
          gcongr
      _ = high * σ * δ := by ring
  have hSx : chartS P x ^ high ≤ σ ^ 2 :=
    (pow_le_pow_of_le_one sx0 sx1 hh).trans (pow_le_pow_left₀ sx0 hsxa 2)
  have hSx0 : 0 ≤ chartS P x ^ high := pow_nonneg sx0 _
  have hTx1 : chartT P x ^ low ≤ 1 := pow_le_one₀ tx0 tx1
  have hTy1 : chartT P y ^ low ≤ 1 := pow_le_one₀ ty0 ty1
  have hTy0 : 0 ≤ chartT P y ^ low := pow_nonneg ty0 _
  have hTx0 : 0 ≤ chartT P x ^ low := pow_nonneg tx0 _
  have hDy1 : decayFactor P y ^ k ≤ 1 := pow_le_one₀ dy0 dy1
  have hDy0 : 0 ≤ decayFactor P y ^ k := pow_nonneg dy0 _
  have e : decayFactor P x ^ k * chartT P x ^ low * chartS P x ^ high - decayFactor P y ^ k * chartT P y ^ low * chartS P y ^ high =
      (decayFactor P x ^ k - decayFactor P y ^ k) * (chartT P x ^ low * chartS P x ^ high) +
        decayFactor P y ^ k * ((chartT P x ^ low - chartT P y ^ low) * chartS P x ^ high) +
          decayFactor P y ^ k * chartT P y ^ low * (chartS P x ^ high - chartS P y ^ high) := by ring
  have hq1 : δ / σb ≤ (1 + b / a) / a * d := by
    rw [hδ, hσb, div_le_iff₀ hσb0]
    have hab' : 0 < b := lt_of_lt_of_le ha hab
    have k1 : P.L0 / (a + P.L0) ^ 2 ≤ (1 + b / a) / a * (P.L0 / (b + P.L0)) := by
      have eq1 : (1 + b / a) / a * (P.L0 / (b + P.L0)) = P.L0 * (a + b) / (a ^ 2 * (b + P.L0)) := by
        field_simp
      rw [eq1, div_le_div_iff₀ (by positivity) (by positivity)]
      have hid : P.L0 * (a + b) * (a + P.L0) ^ 2 - P.L0 * (a ^ 2 * (b + P.L0)) =
          P.L0 * (a ^ 3 + a ^ 2 * P.L0 + a * P.L0 ^ 2 + 2 * a * b * P.L0 + b * P.L0 ^ 2) := by ring
      have hpos : 0 ≤ P.L0 * (a ^ 3 + a ^ 2 * P.L0 + a * P.L0 ^ 2 + 2 * a * b * P.L0 + b * P.L0 ^ 2) := by positivity
      linarith
    calc P.L0 / (a + P.L0) ^ 2 * d ≤ (1 + b / a) / a * (P.L0 / (b + P.L0)) * d := by gcongr
      _ = (1 + b / a) / a * d * (P.L0 / (b + P.L0)) := by ring
  have hq2 : δ ≤ σ / a * d := by
    rw [hδ, hσ]
    have : P.L0 / (a + P.L0) ^ 2 ≤ P.L0 / (a + P.L0) / a := by
      rw [div_div, sq]
      exact div_le_div_of_nonneg_left hL.le (by positivity) (by nlinarith)
    gcongr
  have hr1 : 1 ≤ 1 + b / a := by
    have : 0 ≤ b / a := div_nonneg (ha.le.trans hab) ha.le
    linarith
  rw [e]
  calc |(decayFactor P x ^ k - decayFactor P y ^ k) * (chartT P x ^ low * chartS P x ^ high) +
        decayFactor P y ^ k * ((chartT P x ^ low - chartT P y ^ low) * chartS P x ^ high) +
          decayFactor P y ^ k * chartT P y ^ low * (chartS P x ^ high - chartS P y ^ high)|
      ≤ |decayFactor P x ^ k - decayFactor P y ^ k| * (1 * σ ^ 2) +
          1 * (|chartT P x ^ low - chartT P y ^ low| * σ ^ 2) +
            1 * 1 * |chartS P x ^ high - chartS P y ^ high| := by
        refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _).trans (add_le_add ?_ ?_)) ?_)
        · rw [abs_mul, abs_mul, abs_of_nonneg hTx0, abs_of_nonneg hSx0]
          gcongr
        · rw [abs_mul, abs_mul, abs_of_nonneg hDy0, abs_of_nonneg hSx0]
          gcongr
        · rw [abs_mul, abs_mul, abs_of_nonneg hDy0, abs_of_nonneg hTy0]
          gcongr
    _ ≤ k * (2 * P.eps * ((1 + b / a) / a * d)) * σ ^ 2 + low * (σ / a * d) * σ ^ 2 + high * σ * (σ / a * d) := by
        have h1 : |decayFactor P x ^ k - decayFactor P y ^ k| ≤ k * (2 * P.eps * ((1 + b / a) / a * d)) :=
          hDk.trans (by gcongr)
        have h2 : |chartT P x ^ low - chartT P y ^ low| ≤ low * (σ / a * d) := hTl.trans (by gcongr)
        have h3 : |chartS P x ^ high - chartS P y ^ high| ≤ high * σ * (σ / a * d) := hSh.trans (by gcongr)
        have hs2 : 0 ≤ σ ^ 2 := sq_nonneg σ
        have g1 := mul_le_mul_of_nonneg_right h1 hs2
        have g2 := mul_le_mul_of_nonneg_right h2 hs2
        linarith
    _ ≤ (2 * P.eps * k + low + high) * (1 + b / a) * σ ^ 2 / a * d := by
        have hσ3 : σ ^ 3 ≤ σ ^ 2 := pow_le_pow_of_le_one hσ0 hσ1 (by norm_num)
        have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        have hl0 : (0 : ℝ) ≤ low := Nat.cast_nonneg low
        have hh0 : (0 : ℝ) ≤ high := Nat.cast_nonneg high
        have hA : 0 ≤ σ ^ 2 / a * d := by positivity
        have e2 : k * (2 * P.eps * ((1 + b / a) / a * d)) * σ ^ 2 + low * (σ / a * d) * σ ^ 2 + high * σ * (σ / a * d)
            = 2 * P.eps * k * (1 + b / a) * (σ ^ 2 / a * d) + low * (σ ^ 3 / a * d) + high * (σ ^ 2 / a * d) := by ring
        have e3 : (2 * P.eps * k + low + high) * (1 + b / a) * σ ^ 2 / a * d
            = 2 * P.eps * k * (1 + b / a) * (σ ^ 2 / a * d) + low * (1 + b / a) * (σ ^ 2 / a * d) +
              high * (1 + b / a) * (σ ^ 2 / a * d) := by ring
        rw [e2, e3]
        have f1 : σ ^ 3 / a * d ≤ σ ^ 2 / a * d := by gcongr
        have f2 : σ ^ 2 / a * d ≤ (1 + b / a) * (σ ^ 2 / a * d) := le_mul_of_one_le_left hA hr1
        have g1 := mul_le_mul_of_nonneg_left (f1.trans f2) hl0
        have g2 := mul_le_mul_of_nonneg_left f2 hh0
        linarith


namespace PressureOpenInternal

theorem height_abs_le (z : Space) : |heightRatio z| ≤ 1 := by
  unfold heightRatio
  by_cases h : ‖z‖ = 0
  · simp [h]
  · rw [abs_div, abs_of_nonneg (norm_nonneg z), div_le_one (lt_of_le_of_ne (norm_nonneg z) (Ne.symm h))]
    exact coord_abs_le z 2

theorem expI_norm (v : ℝ) : ‖Complex.exp (Complex.I * v)‖ = 1 := by
  rw [Complex.norm_exp]; simp

theorem expI_sub (u v : ℝ) : ‖Complex.exp (Complex.I * u) - Complex.exp (Complex.I * v)‖ ≤ |u - v| := by
  have e : Complex.exp (Complex.I * u) - Complex.exp (Complex.I * v) =
      Complex.exp (Complex.I * v) * (Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]; push_cast; ring_nf
  rw [e, norm_mul, expI_norm, one_mul]
  first
    | exact (norm_exp_I_mul_ofReal_sub_one_le (x := u - v)).trans (le_of_eq (Real.norm_eq_abs _))
    | exact (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - v)).trans (le_of_eq (Real.norm_eq_abs _))

theorem logPhase_sub (P : ChartParams) (hP : IsChartParams P) {a b : ℝ} (ha : 0 < a) {x y : Space}
    (hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ b) (hy : a ≤ ‖y‖ ∧ ‖y‖ ≤ b) :
    |logPhase P x - logPhase P y| ≤ b / a ^ 2 * ‖x - y‖ := by
  unfold logPhase
  have hrc := hP.rc_pos
  have hc : 0 < 1 + a ^ 2 / P.rc ^ 2 := by positivity
  have hcx : 1 + a ^ 2 / P.rc ^ 2 ≤ 1 + ‖x‖ ^ 2 / P.rc ^ 2 := by
    gcongr; exact hx.1
  have hcy : 1 + a ^ 2 / P.rc ^ 2 ≤ 1 + ‖y‖ ^ 2 / P.rc ^ 2 := by
    gcongr; exact hy.1
  have hl := log_sub_le hc hcx hcy
  rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hd : |(1 + ‖x‖ ^ 2 / P.rc ^ 2) - (1 + ‖y‖ ^ 2 / P.rc ^ 2)| ≤ 2 * b * ‖x - y‖ / P.rc ^ 2 := by
    have e1 : (1 + ‖x‖ ^ 2 / P.rc ^ 2) - (1 + ‖y‖ ^ 2 / P.rc ^ 2) = ((‖x‖ + ‖y‖) * (‖x‖ - ‖y‖)) / P.rc ^ 2 := by ring
    have h6 := abs_norm_sub_norm_le x y
    have h7 : ‖x‖ + ‖y‖ ≤ 2 * b := by linarith [hx.2, hy.2]
    have h8 : 0 ≤ 2 * b := by linarith [ha, hx.1, hx.2]
    have h5 : |(‖x‖ + ‖y‖) * (‖x‖ - ‖y‖)| ≤ 2 * b * ‖x - y‖ := by
      rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ ‖x‖ + ‖y‖)]
      calc (‖x‖ + ‖y‖) * |‖x‖ - ‖y‖| ≤ (2 * b) * |‖x‖ - ‖y‖| := mul_le_mul_of_nonneg_right h7 (abs_nonneg _)
        _ ≤ (2 * b) * ‖x - y‖ := mul_le_mul_of_nonneg_left h6 h8
    rw [e1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < P.rc ^ 2)]
    exact div_le_div_of_nonneg_right h5 (by positivity)
  have hd0 := norm_nonneg (x - y)
  have hb0 : 0 ≤ b := by linarith [hx.1, hx.2]
  calc 1 / 2 * |Real.log (1 + ‖x‖ ^ 2 / P.rc ^ 2) - Real.log (1 + ‖y‖ ^ 2 / P.rc ^ 2)|
      ≤ 1 / 2 * ((2 * b * ‖x - y‖ / P.rc ^ 2) / (1 + a ^ 2 / P.rc ^ 2)) :=
        mul_le_mul_of_nonneg_left (hl.trans (div_le_div_of_nonneg_right hd hc.le)) (by norm_num)
    _ = b * ‖x - y‖ / (P.rc ^ 2 + a ^ 2) := by field_simp
    _ ≤ b * ‖x - y‖ / a ^ 2 := div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith)
    _ = b / a ^ 2 * ‖x - y‖ := by ring

theorem unit_pow_sub (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (n : ℕ) : ‖u ^ n - v ^ n‖ ≤ n * ‖u - v‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    have e : u ^ (n + 1) - v ^ (n + 1) = u ^ n * (u - v) + (u ^ n - v ^ n) * v := by ring
    rw [e]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, norm_pow, hu, hv, one_pow, one_mul, mul_one]
    push_cast
    linarith

theorem unit_zpow_sub (u v : ℂ) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (k : ℤ) :
    ‖u ^ k - v ^ k‖ ≤ (k.natAbs : ℝ) * ‖u - v‖ := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · simp only [zpow_natCast, Int.natAbs_natCast]
    exact unit_pow_sub u v hu hv n
  · have hu0 : u ^ n ≠ 0 := pow_ne_zero _ (by rw [← norm_ne_zero_iff, hu]; norm_num)
    have hv0 : v ^ n ≠ 0 := pow_ne_zero _ (by rw [← norm_ne_zero_iff, hv]; norm_num)
    rw [zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, inv_sub_inv' hu0 hv0, Int.natAbs_neg, Int.natAbs_natCast]
    rw [norm_mul, norm_mul, norm_inv, norm_inv, norm_pow, norm_pow, hu, hv, one_pow, inv_one, one_mul, mul_one,
      norm_sub_rev]
    exact unit_pow_sub u v hu hv n

theorem unit_sub_le (w w' : ℂ) (hw : w ≠ 0) (hw' : w' ≠ 0) :
    ‖w‖ * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ ≤ 2 * ‖w - w'‖ := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have hn' : (‖w'‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw'
  have e : (‖w‖ : ℂ) * (w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)) =
      (w - w') + w' / (‖w'‖ : ℂ) * (((‖w'‖ - ‖w‖ : ℝ)) : ℂ) := by
    push_cast; field_simp; ring
  have h1 : ‖w‖ * ‖w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ)‖ = ‖(‖w‖ : ℂ) * (w / (‖w‖ : ℂ) - w' / (‖w'‖ : ℂ))‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  have h2 : ‖w' / (‖w'‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.2 hw')
  rw [h1, e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, h2, one_mul, Complex.norm_real, Real.norm_eq_abs]
  have := abs_norm_sub_norm_le w' w
  rw [norm_sub_rev w' w] at this
  linarith

theorem expArg_eq (w : ℂ) (hw : w ≠ 0) (k : ℤ) :
    Complex.exp (Complex.I * ((k : ℝ) * Complex.arg w : ℝ)) = (w / (‖w‖ : ℂ)) ^ k := by
  have hn : (‖w‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hw
  have h1 : w / (‖w‖ : ℂ) = Complex.exp (Complex.arg w * Complex.I) := by
    rw [div_eq_iff hn, mul_comm]
    exact (Complex.norm_mul_exp_arg_mul_I w).symm
  rw [h1, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

theorem plane_sub (k : ℤ) (w w' : ℂ) {B : ℝ} (hb : ‖w‖ ≤ B) (hb' : ‖w'‖ ≤ B) :
    ‖Complex.exp (Complex.I * ((k : ℝ) * Complex.arg w : ℝ)) * ((‖w‖ ^ 2 : ℝ) : ℂ) -
      Complex.exp (Complex.I * ((k : ℝ) * Complex.arg w' : ℝ)) * ((‖w'‖ ^ 2 : ℝ) : ℂ)‖ ≤
        (2 * k.natAbs + 2) * B * ‖w - w'‖ := by
  have hB0 : 0 ≤ B := (norm_nonneg w).trans hb
  have hk0 : (0 : ℝ) ≤ k.natAbs := Nat.cast_nonneg _
  have hd0 := norm_nonneg (w - w')
  have hK : B * ‖w - w'‖ ≤ (2 * k.natAbs + 2) * B * ‖w - w'‖ := by
    have : 0 ≤ (2 * (k.natAbs : ℝ) + 1) * (B * ‖w - w'‖) := by positivity
    nlinarith
  by_cases hw : w = 0
  · subst hw
    rw [zero_sub, norm_neg] at hK
    rw [norm_zero, show ((0 : ℝ) ^ 2 : ℝ) = 0 by norm_num, Complex.ofReal_zero, mul_zero, zero_sub, norm_neg,
      norm_mul, expI_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), zero_sub,
      norm_neg, sq]
    exact (mul_le_mul_of_nonneg_right hb' (norm_nonneg _)).trans hK
  by_cases hw' : w' = 0
  · subst hw'
    rw [sub_zero] at hK
    rw [norm_zero, show ((0 : ℝ) ^ 2 : ℝ) = 0 by norm_num, Complex.ofReal_zero, mul_zero, sub_zero,
      norm_mul, expI_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity), sub_zero, sq]
    exact (mul_le_mul_of_nonneg_right hb (norm_nonneg _)).trans hK
  rw [expArg_eq w hw, expArg_eq w' hw']
  set u := w / (‖w‖ : ℂ) with hu
  set v := w' / (‖w'‖ : ℂ) with hv
  have hu1 : ‖u‖ = 1 := by
    rw [hu, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.2 hw)
  have hv1 : ‖v‖ = 1 := by
    rw [hv, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.2 hw')
  have e : u ^ k * ((‖w‖ ^ 2 : ℝ) : ℂ) - v ^ k * ((‖w'‖ ^ 2 : ℝ) : ℂ) =
      ((‖w‖ ^ 2 : ℝ) : ℂ) * (u ^ k - v ^ k) + v ^ k * (((‖w‖ ^ 2 - ‖w'‖ ^ 2 : ℝ)) : ℂ) := by
    push_cast; ring
  have hvk : ‖v ^ k‖ = 1 := by rw [norm_zpow, hv1, one_zpow]
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_mul, hvk, one_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by positivity)]
  have h1 := unit_zpow_sub u v hu1 hv1 k
  have h2 := unit_sub_le w w' hw hw'
  have h3 : |‖w‖ ^ 2 - ‖w'‖ ^ 2| ≤ 2 * B * ‖w - w'‖ := by
    rw [show ‖w‖ ^ 2 - ‖w'‖ ^ 2 = (‖w‖ + ‖w'‖) * (‖w‖ - ‖w'‖) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ ‖w‖ + ‖w'‖)]
    exact mul_le_mul (by linarith) (abs_norm_sub_norm_le w w') (abs_nonneg _) (by linarith)
  have hwn := norm_nonneg w
  have h4 : ‖w‖ ^ 2 * ‖u ^ k - v ^ k‖ ≤ 2 * k.natAbs * B * ‖w - w'‖ := by
    calc ‖w‖ ^ 2 * ‖u ^ k - v ^ k‖ ≤ ‖w‖ ^ 2 * ((k.natAbs : ℝ) * ‖u - v‖) := by gcongr
      _ = (k.natAbs : ℝ) * ‖w‖ * (‖w‖ * ‖u - v‖) := by ring
      _ ≤ (k.natAbs : ℝ) * B * (2 * ‖w - w'‖) := by gcongr
      _ = 2 * k.natAbs * B * ‖w - w'‖ := by ring
  linarith

end PressureOpenInternal


namespace PressureOpenInternal

theorem plane_norm_le (v : Space) : ‖(⟨v 0, v 1⟩ : ℂ)‖ ≤ ‖v‖ := by
  have h1 : ‖(⟨v 0, v 1⟩ : ℂ)‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]; ring
  have h2 : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  exact pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) (by norm_num : (2 : ℕ) ≠ 0) |>.1
    (by rw [h1, h2]; nlinarith [sq_nonneg (v 2)])

theorem q_eq (z : Space) (hz : z ≠ 0) : qOf z = ‖(⟨z 0, z 1⟩ : ℂ)‖ ^ 2 / ‖z‖ ^ 2 := by
  have h1 : ‖(⟨z 0, z 1⟩ : ℂ)‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_mk]; ring
  have h2 : ‖z‖ ^ 2 = z 0 ^ 2 + z 1 ^ 2 + z 2 ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    simp only [Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
  unfold qOf heightRatio
  rw [h1, div_pow, eq_div_iff (pow_ne_zero 2 hn)]
  field_simp
  linarith

theorem planeField_sub (k : ℤ) {a b : ℝ} (ha : 0 < a) {x y : Space}
    (hx : a ≤ ‖x‖ ∧ ‖x‖ ≤ b) (hy : a ≤ ‖y‖ ∧ ‖y‖ ≤ b) :
    ‖Complex.exp (Complex.I * ((k : ℝ) * angleOf x : ℝ)) * ((qOf x : ℝ) : ℂ) -
      Complex.exp (Complex.I * ((k : ℝ) * angleOf y : ℝ)) * ((qOf y : ℝ) : ℂ)‖ ≤
        (2 * k.natAbs + 4) * (b / a ^ 2) * ‖x - y‖ := by
  have hx0 : 0 < ‖x‖ := lt_of_lt_of_le ha hx.1
  have hy0 : 0 < ‖y‖ := lt_of_lt_of_le ha hy.1
  have hxz : x ≠ 0 := norm_pos_iff.1 hx0
  have hyz : y ≠ 0 := norm_pos_iff.1 hy0
  set wx : ℂ := ⟨x 0, x 1⟩ with hwx
  set wy : ℂ := ⟨y 0, y 1⟩ with hwy
  have e : ∀ z : Space, z ≠ 0 → Complex.exp (Complex.I * ((k : ℝ) * angleOf z : ℝ)) * ((qOf z : ℝ) : ℂ) =
      (Complex.exp (Complex.I * ((k : ℝ) * Complex.arg ⟨z 0, z 1⟩ : ℝ)) * ((‖(⟨z 0, z 1⟩ : ℂ)‖ ^ 2 : ℝ) : ℂ)) *
        ((1 / ‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z hz
    rw [q_eq z hz]
    unfold angleOf
    push_cast
    ring
  rw [e x hxz, e y hyz]
  have hwxb : ‖wx‖ ≤ b := (plane_norm_le x).trans hx.2
  have hwyb : ‖wy‖ ≤ b := (plane_norm_le y).trans hy.2
  have hwd : ‖wx - wy‖ ≤ ‖x - y‖ := by
    have : wx - wy = (⟨(x - y) 0, (x - y) 1⟩ : ℂ) := by
      apply Complex.ext <;> simp [hwx, hwy]
    rw [this]; exact plane_norm_le _
  have hH := plane_sub k wx wy hwxb hwyb
  have hHx : ‖Complex.exp (Complex.I * ((k : ℝ) * Complex.arg wx : ℝ)) * ((‖wx‖ ^ 2 : ℝ) : ℂ)‖ ≤ ‖x‖ ^ 2 := by
    rw [norm_mul, expI_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (plane_norm_le x) 2
  have hcy : ‖((1 / ‖y‖ ^ 2 : ℝ) : ℂ)‖ ≤ 1 / a ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact div_le_div_of_nonneg_left zero_le_one (by positivity) (pow_le_pow_left₀ ha.le hy.1 2)
  have hc : ‖((1 / ‖x‖ ^ 2 : ℝ) : ℂ) - ((1 / ‖y‖ ^ 2 : ℝ) : ℂ)‖ * ‖x‖ ^ 2 ≤ 2 * b / a ^ 2 * ‖x - y‖ := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    have e2 : 1 / ‖x‖ ^ 2 - 1 / ‖y‖ ^ 2 = (‖y‖ + ‖x‖) * (‖y‖ - ‖x‖) / (‖x‖ ^ 2 * ‖y‖ ^ 2) := by
      field_simp; ring
    rw [e2, abs_div, abs_mul, abs_of_nonneg (by positivity : 0 ≤ ‖y‖ + ‖x‖), abs_of_pos (by positivity : 0 < ‖x‖ ^ 2 * ‖y‖ ^ 2)]
    have h6 : |‖y‖ - ‖x‖| ≤ ‖x - y‖ := by rw [abs_sub_comm]; exact abs_norm_sub_norm_le x y
    have h7 : ‖y‖ + ‖x‖ ≤ 2 * b := by linarith [hx.2, hy.2]
    have h8 : 0 ≤ 2 * b := by linarith [ha, hx.1, hx.2]
    have h9 : (‖y‖ + ‖x‖) * |‖y‖ - ‖x‖| ≤ 2 * b * ‖x - y‖ := by
      calc (‖y‖ + ‖x‖) * |‖y‖ - ‖x‖| ≤ (2 * b) * |‖y‖ - ‖x‖| := mul_le_mul_of_nonneg_right h7 (abs_nonneg _)
        _ ≤ (2 * b) * ‖x - y‖ := mul_le_mul_of_nonneg_left h6 h8
    have e3 : (‖y‖ + ‖x‖) * |‖y‖ - ‖x‖| / (‖x‖ ^ 2 * ‖y‖ ^ 2) * ‖x‖ ^ 2 = (‖y‖ + ‖x‖) * |‖y‖ - ‖x‖| / ‖y‖ ^ 2 := by
      field_simp
    rw [e3, div_le_iff₀ (by positivity)]
    have hya : a ^ 2 ≤ ‖y‖ ^ 2 := pow_le_pow_left₀ ha.le hy.1 2
    calc (‖y‖ + ‖x‖) * |‖y‖ - ‖x‖| ≤ 2 * b * ‖x - y‖ := h9
      _ = 2 * b / a ^ 2 * ‖x - y‖ * a ^ 2 := by field_simp
      _ ≤ 2 * b / a ^ 2 * ‖x - y‖ * ‖y‖ ^ 2 := by gcongr
  refine (mul_sub_le _ _ _ _).trans ?_
  have hd0 := norm_nonneg (x - y)
  have hk0 : (0 : ℝ) ≤ k.natAbs := Nat.cast_nonneg _
  have hb0 : 0 ≤ b := by linarith [hx.1, hx.2]
  calc _ ≤ ‖x‖ ^ 2 * ‖((1 / ‖x‖ ^ 2 : ℝ) : ℂ) - ((1 / ‖y‖ ^ 2 : ℝ) : ℂ)‖ + 1 / a ^ 2 * ((2 * k.natAbs + 2) * b * ‖wx - wy‖) := by
        gcongr
    _ ≤ 2 * b / a ^ 2 * ‖x - y‖ + 1 / a ^ 2 * ((2 * k.natAbs + 2) * b * ‖x - y‖) := by
        rw [mul_comm (‖x‖ ^ 2)]
        gcongr
    _ = (2 * k.natAbs + 4) * (b / a ^ 2) * ‖x - y‖ := by ring

end PressureOpenInternal

theorem angular_shell (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) (axis : ℕ)
    (hax : n ≠ 0 → 1 ≤ axis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ shellSet a b, ∀ y ∈ shellSet a b,
      ‖modePhase P n β x * ((qOf x ^ axis : ℝ) : ℂ) - modePhase P n β y * ((qOf y ^ axis : ℝ) : ℂ)‖ ≤
        C * (1 + b / a) ^ 2 / a * ‖x - y‖ := by
  have hk0 : (0 : ℝ) ≤ ((n * (P.m : ℤ)).natAbs : ℝ) := Nat.cast_nonneg _
  refine ⟨|(n : ℝ) * β| + 2 * ((n * (P.m : ℤ)).natAbs : ℝ) + 4 + 4 * axis, by positivity,
    fun a b ha hab x hx y hy => ?_⟩
  have hd0 := norm_nonneg (x - y)
  have hb0 : 0 < b := lt_of_lt_of_le ha hab
  have hba0 : 0 ≤ b / a := div_nonneg hb0.le ha.le
  have hba : b / a ^ 2 ≤ (1 + b / a) ^ 2 / a := by
    rw [show b / a ^ 2 = (b / a) / a by field_simp]
    exact div_le_div_of_nonneg_right (by nlinarith) ha.le
  have h1a : 1 / a ≤ (1 + b / a) ^ 2 / a := div_le_div_of_nonneg_right (by nlinarith) ha.le
  obtain ⟨qx0, qx1⟩ := qOf_mem x
  obtain ⟨qy0, qy1⟩ := qOf_mem y
  have hqd : |qOf x - qOf y| ≤ 4 / a * ‖x - y‖ := by
    unfold qOf
    have h3 := ratio_sub ha hx.1 hy.1
    have hxa := height_abs_le x
    have hya := height_abs_le y
    rw [show 1 - heightRatio x ^ 2 - (1 - heightRatio y ^ 2) =
      (heightRatio y + heightRatio x) * (heightRatio y - heightRatio x) by ring, abs_mul]
    have h3' : |heightRatio y - heightRatio x| ≤ 2 / a * ‖x - y‖ := by rw [abs_sub_comm]; exact h3
    have hs : |heightRatio y + heightRatio x| ≤ 2 := (abs_add_le _ _).trans (by linarith)
    calc |heightRatio y + heightRatio x| * |heightRatio y - heightRatio x| ≤ 2 * (2 / a * ‖x - y‖) :=
          mul_le_mul hs h3' (abs_nonneg _) (by norm_num)
      _ = 4 / a * ‖x - y‖ := by ring
  have hq1 : ∀ m : ℕ, |qOf x ^ m - qOf y ^ m| ≤ m * (4 / a * ‖x - y‖) := fun m =>
    (pow_sub_le m (by rw [abs_of_nonneg qx0]; exact qx1) (by rw [abs_of_nonneg qy0]; exact qy1)).trans
      (mul_le_mul_of_nonneg_left hqd (Nat.cast_nonneg m))
  have hA : 0 ≤ ‖x - y‖ / a := by positivity
  by_cases hn : n = 0
  · subst hn
    have hp : ∀ z, modePhase P 0 β z = 1 := by intro z; unfold modePhase; simp
    rw [hp, hp, one_mul, one_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    refine (hq1 axis).trans ?_
    have : (axis : ℝ) * (4 / a * ‖x - y‖) ≤ 4 * axis * ((1 + b / a) ^ 2 / a * ‖x - y‖) := by
      have := mul_le_mul_of_nonneg_right h1a hd0
      have hax0 : (0 : ℝ) ≤ 4 * axis := by positivity
      calc (axis : ℝ) * (4 / a * ‖x - y‖) = 4 * axis * (1 / a * ‖x - y‖) := by ring
        _ ≤ 4 * axis * ((1 + b / a) ^ 2 / a * ‖x - y‖) := mul_le_mul_of_nonneg_left this hax0
    refine this.trans ?_
    have hr : 0 ≤ (1 + b / a) ^ 2 / a * ‖x - y‖ := by positivity
    have e4 : (|((0 : ℤ) : ℝ) * β| + 2 * ((0 * (P.m : ℤ)).natAbs : ℝ) + 4 + 4 * axis) * (1 + b / a) ^ 2 / a * ‖x - y‖
        = (4 + 4 * axis) * ((1 + b / a) ^ 2 / a * ‖x - y‖) := by simp; ring
    rw [e4]
    nlinarith
  · have hax1 := hax hn
    have hsplit : ∀ z, modePhase P n β z * ((qOf z ^ axis : ℝ) : ℂ) =
        Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ)) *
          (Complex.exp (Complex.I * ((((n * (P.m : ℤ) : ℤ) : ℝ) * angleOf z : ℝ) : ℂ)) * ((qOf z : ℝ) : ℂ)) *
            ((qOf z ^ (axis - 1) : ℝ) : ℂ) := by
      intro z
      have hq : qOf z ^ axis = qOf z * qOf z ^ (axis - 1) := by
        rw [← pow_succ']; congr 1; omega
      have hexp : Complex.exp (Complex.I * ((((n * P.m : ℤ) : ℝ) * angleOf z + n * β * logPhase P z : ℝ) : ℂ)) =
          Complex.exp (Complex.I * ((n * β * logPhase P z : ℝ) : ℂ)) *
            Complex.exp (Complex.I * ((((n * (P.m : ℤ) : ℤ) : ℝ) * angleOf z : ℝ) : ℂ)) := by
        rw [← Complex.exp_add]; congr 1; push_cast; ring
      unfold modePhase
      rw [hexp, hq]
      push_cast
      ring
    rw [hsplit x, hsplit y]
    set E1x := Complex.exp (Complex.I * ((n * β * logPhase P x : ℝ) : ℂ))
    set E1y := Complex.exp (Complex.I * ((n * β * logPhase P y : ℝ) : ℂ))
    set Gx := Complex.exp (Complex.I * ((((n * (P.m : ℤ) : ℤ) : ℝ) * angleOf x : ℝ) : ℂ)) * ((qOf x : ℝ) : ℂ)
    set Gy := Complex.exp (Complex.I * ((((n * (P.m : ℤ) : ℤ) : ℝ) * angleOf y : ℝ) : ℂ)) * ((qOf y : ℝ) : ℂ)
    have hE1 : ‖E1x - E1y‖ ≤ |(n : ℝ) * β| * (b / a ^ 2 * ‖x - y‖) := by
      refine (expI_sub _ _).trans ?_
      rw [show (n : ℝ) * β * logPhase P x - n * β * logPhase P y = (n * β) * (logPhase P x - logPhase P y) by ring,
        abs_mul]
      exact mul_le_mul_of_nonneg_left (logPhase_sub P hP ha hx hy) (abs_nonneg _)
    have hG := planeField_sub (n * (P.m : ℤ)) ha hx hy
    have hGy : ‖Gy‖ ≤ 1 := by
      rw [norm_mul, expI_norm, one_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg qy0]; exact qy1
    have hE1x : ‖E1x‖ = 1 := expI_norm _
    have hQy : ‖((qOf y ^ (axis - 1) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg qy0 _)]; exact pow_le_one₀ qy0 qy1
    have hEGx : ‖E1x * Gx‖ ≤ 1 := by
      rw [norm_mul, hE1x, one_mul, norm_mul, expI_norm, one_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg qx0]; exact qx1
    have hQd : ‖((qOf x ^ (axis - 1) : ℝ) : ℂ) - ((qOf y ^ (axis - 1) : ℝ) : ℂ)‖ ≤ (axis - 1 : ℕ) * (4 / a * ‖x - y‖) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]; exact hq1 (axis - 1)
    have hEG : ‖E1x * Gx - E1y * Gy‖ ≤ 1 * ((2 * (n * (P.m : ℤ)).natAbs + 4) * (b / a ^ 2) * ‖x - y‖) +
        1 * (|(n : ℝ) * β| * (b / a ^ 2 * ‖x - y‖)) := by
      refine (mul_sub_le _ _ _ _).trans ?_
      rw [hE1x]
      gcongr
    have hax' : ((axis - 1 : ℕ) : ℝ) ≤ axis := Nat.cast_le.2 (Nat.sub_le _ _)
    calc _ ≤ ‖E1x * Gx‖ * ‖((qOf x ^ (axis - 1) : ℝ) : ℂ) - ((qOf y ^ (axis - 1) : ℝ) : ℂ)‖ +
          ‖((qOf y ^ (axis - 1) : ℝ) : ℂ)‖ * ‖E1x * Gx - E1y * Gy‖ := mul_sub_le _ _ _ _
      _ ≤ 1 * ((axis - 1 : ℕ) * (4 / a * ‖x - y‖)) + 1 * (1 * ((2 * (n * (P.m : ℤ)).natAbs + 4) * (b / a ^ 2) * ‖x - y‖) +
          1 * (|(n : ℝ) * β| * (b / a ^ 2 * ‖x - y‖))) := by
        gcongr
      _ ≤ 4 * axis * (1 / a * ‖x - y‖) + ((2 * (n * (P.m : ℤ)).natAbs + 4) + |(n : ℝ) * β|) * (b / a ^ 2 * ‖x - y‖) := by
        have : ((axis - 1 : ℕ) : ℝ) * (4 / a * ‖x - y‖) ≤ 4 * axis * (1 / a * ‖x - y‖) := by
          rw [show (4 : ℝ) / a * ‖x - y‖ = 4 * (1 / a * ‖x - y‖) by ring]
          have h0 : 0 ≤ 1 / a * ‖x - y‖ := by positivity
          nlinarith
        nlinarith
      _ ≤ 4 * axis * ((1 + b / a) ^ 2 / a * ‖x - y‖) +
          ((2 * (n * (P.m : ℤ)).natAbs + 4) + |(n : ℝ) * β|) * ((1 + b / a) ^ 2 / a * ‖x - y‖) := by
        gcongr
      _ = (|(n : ℝ) * β| + 2 * ((n * (P.m : ℤ)).natAbs : ℝ) + 4 + 4 * axis) * (1 + b / a) ^ 2 / a * ‖x - y‖ := by
        ring

namespace PressureOpenInternal

theorem poly_bound (Q : MvPolynomial (Fin 2) ℂ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] Q‖ ≤ B := by
  have hc : Continuous (fun p : ℝ × ℝ => MvPolynomial.eval ![((p.1 : ℝ) : ℂ), ((p.2 : ℝ) : ℂ)] Q) :=
    (FracInternal.mvPoly_eval_contDiff Q contDiff_fst contDiff_snd).continuous
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun t x ht hx => ?_⟩
  have hm : (t, x) ∈ Metric.closedBall (0 : ℝ × ℝ) 1 := by
    rw [mem_closedBall_zero_iff, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
    exact max_le ht hx
  exact (hC _ hm).trans (le_max_left _ _)

theorem cellIndex_le_len (l : List ℝ) (u : ℝ) : cellIndex l u ≤ l.length := by
  unfold cellIndex
  calc _ ≤ ((l.drop 1).dropLast).length := List.length_filter_le _ _
    _ ≤ l.length := by simp only [List.length_dropLast, List.length_drop]; omega

theorem pieces_bounded (S : Spline) : ∃ B : ℝ, 0 ≤ B ∧ ∀ t x : ℝ, |t| ≤ 1 → |x| ≤ 1 →
    ∀ i j, i ≤ S.mesh.tBreaks.length → j ≤ S.mesh.xBreaks.length →
      ‖MvPolynomial.eval ![(t : ℂ), (x : ℂ)] (S.piece i j)‖ ≤ B := by
  choose B hB0 hB using fun ij : ℕ × ℕ => poly_bound (S.piece ij.1 ij.2)
  let R := Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1)
  refine ⟨∑ k ∈ R, B k, Finset.sum_nonneg fun k _ => hB0 k, fun t x ht hx i j hi hj => ?_⟩
  have hmem : (i, j) ∈ R := Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  exact (hB (i, j) t x ht hx).trans (Finset.single_le_sum (fun k _ => hB0 k) hmem)

end PressureOpenInternal

open PressureOpenInternal


namespace PressureOpenInternal

theorem count_sorted : ∀ (J : List ℝ), J.Pairwise (· < ·) → ∀ k (hk : k < J.length),
    (J.filter (fun b => decide (b ≤ J[k]))).length = k + 1 ∧ (J.filter (fun b => decide (b < J[k]))).length = k
  | [], _, k, hk => by simp at hk
  | c :: J', hs, k, hk => by
    rw [List.pairwise_cons] at hs
    obtain ⟨hc, hs'⟩ := hs
    rcases k with _ | k
    · have h1 : J'.filter (fun b => decide (b ≤ c)) = [] :=
        List.filter_eq_nil_iff.2 fun x hx => by simp [not_le.2 (hc x hx)]
      have h2 : J'.filter (fun b => decide (b < c)) = [] :=
        List.filter_eq_nil_iff.2 fun x hx => by simp [not_lt.2 (hc x hx).le]
      simp [h1, h2]
    · have hk' : k < J'.length := by simpa using hk
      obtain ⟨e1, e2⟩ := count_sorted J' hs' k hk'
      have hck : c < J'[k] := hc _ (List.getElem_mem hk')
      simp only [List.getElem_cons_succ, List.filter_cons, hck.le, hck, decide_true, if_true, List.length_cons, e1, e2]
      refine ⟨?_, ?_⟩ <;> trivial

theorem interior_facts (l : List ℝ) (hs : l.Pairwise (· < ·)) (hf : l.head? = some 0) {w : ℝ}
    (hw : w ∈ (l.drop 1).dropLast) :
    ((l.drop 1).dropLast.filter (fun b => decide (b < w))).length + 1 = cellIndex l w ∧ 1 ≤ cellIndex l w ∧
      cellIndex l w < cellCount l ∧ l.getD (cellIndex l w) 0 = w := by
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.1 hf
  have hs' : rest.Pairwise (· < ·) := (List.pairwise_cons.1 hs).2
  have hJ : rest.dropLast.Pairwise (· < ·) := hs'.sublist (List.dropLast_sublist _)
  simp only [List.drop_succ_cons, List.drop_zero] at hw ⊢
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hw
  obtain ⟨e1, e2⟩ := count_sorted _ hJ k hk
  have hci : cellIndex (0 :: rest) rest.dropLast[k] = k + 1 := by
    unfold cellIndex
    simpa using e1
  have hkl : k < rest.length - 1 := by simpa using hk
  rw [hci, e2]
  refine ⟨rfl, by omega, ?_, ?_⟩
  · unfold cellCount; simp; omega
  · rw [List.getD_cons_succ, List.getD_eq_getElem _ _ (by omega), List.getElem_dropLast]

theorem cellIndex_left (l : List ℝ) (w : ℝ) :
    ∀ᶠ s in 𝓝[<] w, cellIndex l s = ((l.drop 1).dropLast.filter (fun b => decide (b < w))).length := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝[<] w, decide (b ≤ s) = decide (b < w) := by
    intro b _
    rcases lt_or_ge b w with hb | hb
    · filter_upwards [nhdsWithin_le_nhds (eventually_gt_nhds hb)] with s hs
      simp [hb, hs.le]
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : s < w := hs
      simp [not_le.2 (lt_of_lt_of_le hs' hb), not_lt.2 hb]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem cellIndex_right' (l : List ℝ) (u : ℝ) : ∀ᶠ s in 𝓝[≥] u, cellIndex l s = cellIndex l u := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝[≥] u, decide (b ≤ s) = decide (b ≤ u) := by
    intro b _
    rcases le_or_gt b u with hb | hb
    · filter_upwards [self_mem_nhdsWithin] with s hs
      have hs' : u ≤ s := hs
      simp [hb, hb.trans hs']
    · filter_upwards [nhdsWithin_le_nhds (eventually_lt_nhds hb)] with s hs
      simp [not_le.2 hb, not_le.2 hs]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem cellIndex_off (l : List ℝ) {w : ℝ} (hw : w ∉ (l.drop 1).dropLast) :
    ∀ᶠ s in 𝓝 w, cellIndex l s = cellIndex l w := by
  have h : ∀ b ∈ ((l.drop 1).dropLast).toFinset, ∀ᶠ s in 𝓝 w, decide (b ≤ s) = decide (b ≤ w) := by
    intro b hb
    have hbw : b ≠ w := fun e => hw (e ▸ List.mem_toFinset.1 hb)
    rcases lt_or_gt_of_ne hbw with h1 | h1
    · filter_upwards [eventually_gt_nhds h1] with s hs
      simp [hs.le, h1.le]
    · filter_upwards [eventually_lt_nhds h1] with s hs
      simp [not_le.2 hs, not_le.2 h1]
  filter_upwards [(Filter.eventually_all_finset _).2 h] with s hs
  unfold cellIndex
  congr 1
  exact List.filter_congr fun b hb => hs b (List.mem_toFinset.2 hb)

theorem slope_one (l : List ℝ) (hs : l.Pairwise (· < ·)) (hf : l.head? = some 0) (F F' : ℕ → ℝ → ℂ) (Λ : ℝ)
    (hF : ∀ i w, HasDerivAt (F i) (F' i w) w) (hb : ∀ i w, i ≤ l.length → 0 ≤ w → w ≤ 1 → ‖F' i w‖ ≤ Λ)
    (hj : ∀ i, 1 ≤ i → i < cellCount l → F (i - 1) (l.getD i 0) = F i (l.getD i 0)) :
    ∀ u v, 0 ≤ u → u ≤ v → v ≤ 1 → ‖F (cellIndex l v) v - F (cellIndex l u) u‖ ≤ Λ * (v - u) := by
  intro u v hu huv hv
  set g : ℝ → ℂ := fun w => F (cellIndex l w) w with hg
  have hright : ∀ w, g =ᶠ[𝓝[≥] w] F (cellIndex l w) := fun w => by
    filter_upwards [cellIndex_right' l w] with s hs
    simp only [hg, hs]
  have hcont : Continuous g := by
    refine continuous_iff_continuousAt.2 fun w => ?_
    by_cases hw : w ∈ (l.drop 1).dropLast
    · obtain ⟨e1, e2, e3, e4⟩ := interior_facts l hs hf hw
      have hjw := hj _ e2 e3
      rw [e4] at hjw
      refine continuousAt_iff_continuous_left_right.2 ⟨?_, ?_⟩
      · rw [← continuousWithinAt_Iio_iff_Iic]
        have hl : g =ᶠ[𝓝[<] w] F (cellIndex l w - 1) := by
          filter_upwards [cellIndex_left l w] with s hs'
          simp only [hg, hs']
          congr 1
          omega
        exact ((hF _ w).continuousAt.continuousWithinAt).congr_of_eventuallyEq hl (by simp only [hg]; exact hjw.symm)
      · exact ((hF _ w).continuousAt.continuousWithinAt).congr_of_eventuallyEq (hright w) rfl
    · have h := cellIndex_off l hw
      have : g =ᶠ[𝓝 w] F (cellIndex l w) := by
        filter_upwards [h] with s hs'
        simp only [hg, hs']
      exact (hF _ w).continuousAt.congr this.symm
  have key := norm_image_sub_le_of_norm_deriv_right_le_segment (f := g) (f' := fun w => F' (cellIndex l w) w)
    (a := u) (b := v) (C := Λ) hcont.continuousOn
    (fun w _ => ((hF _ w).hasDerivWithinAt).congr_of_eventuallyEq (hright w) rfl)
    (fun w hw => hb _ w (cellIndex_le_len l w) (hu.trans hw.1) (hw.2.le.trans hv)) v ⟨huv, le_rfl⟩
  simpa [hg] using key

end PressureOpenInternal


namespace PressureOpenInternal

def evQ (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) : ℂ := MvPolynomial.eval ![(q.1 : ℂ), (q.2 : ℂ)] Q

theorem evQ_contDiff (Q : MvPolynomial (Fin 2) ℂ) : ContDiff ℝ ∞ (evQ Q) :=
  FracInternal.mvPoly_eval_contDiff Q contDiff_fst contDiff_snd

theorem eval_bind_pair (v : Fin 2 → ℂ) (g : Fin 2 → MvPolynomial (Fin 2) ℂ) (Q : MvPolynomial (Fin 2) ℂ) :
    MvPolynomial.eval v (MvPolynomial.bind₁ g Q) = MvPolynomial.eval (fun i => MvPolynomial.eval v (g i)) Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp
  | add p r hp hr => simp [hp, hr]
  | mul_X p i hp => simp [hp]

theorem evQ_atFirst (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    evQ (atFirst (c : ℂ) Q) q = evQ Q (c, q.2) := by
  unfold evQ atFirst
  rw [eval_bind_pair]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

theorem evQ_atSecond (c : ℝ) (Q : MvPolynomial (Fin 2) ℂ) (q : ℝ × ℝ) :
    evQ (atSecond (c : ℂ) Q) q = evQ Q (q.1, c) := by
  unfold evQ atSecond
  rw [eval_bind_pair]
  refine congrArg (fun v => MvPolynomial.eval v Q) (funext fun i => ?_)
  fin_cases i <;> simp

theorem join_first {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ} (h : atFirst (c : ℂ) Q = atFirst (c : ℂ) R) (x : ℝ) :
    evQ Q (c, x) = evQ R (c, x) := by
  have := congrArg (fun W => evQ W (0, x)) h
  simpa [evQ_atFirst] using this

theorem join_second {Q R : MvPolynomial (Fin 2) ℂ} {c : ℝ} (h : atSecond (c : ℂ) Q = atSecond (c : ℂ) R) (t : ℝ) :
    evQ Q (t, c) = evQ R (t, c) := by
  have := congrArg (fun W => evQ W (t, 0)) h
  simpa [evQ_atSecond] using this

theorem dbound (Q : MvPolynomial (Fin 2) ℂ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ p : ℝ × ℝ, ‖p‖ ≤ 1 → ‖fderiv ℝ (evQ Q) p‖ ≤ B := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℝ × ℝ) 1).exists_bound_of_continuousOn
    ((evQ_contDiff Q).continuous_fderiv (by simp)).continuousOn
  exact ⟨max C 0, le_max_right _ _, fun p hp => (hC p (mem_closedBall_zero_iff.2 hp)).trans (le_max_left _ _)⟩

theorem dbound_all (S : Spline) : ∃ B : ℝ, 0 ≤ B ∧ ∀ i j, i ≤ S.mesh.tBreaks.length → j ≤ S.mesh.xBreaks.length →
    ∀ p : ℝ × ℝ, ‖p‖ ≤ 1 → ‖fderiv ℝ (evQ (S.piece i j)) p‖ ≤ B := by
  choose B hB0 hB using fun ij : ℕ × ℕ => dbound (S.piece ij.1 ij.2)
  let R := Finset.range (S.mesh.tBreaks.length + 1) ×ˢ Finset.range (S.mesh.xBreaks.length + 1)
  refine ⟨∑ k ∈ R, B k, Finset.sum_nonneg fun k _ => hB0 k, fun i j hi hj p hp => ?_⟩
  have hmem : (i, j) ∈ R := Finset.mem_product.2 ⟨Finset.mem_range.2 (by omega), Finset.mem_range.2 (by omega)⟩
  exact (hB (i, j) p hp).trans (Finset.single_le_sum (fun k _ => hB0 k) hmem)

theorem cellIndex_lt_count (l : List ℝ) (hf : l.head? = some 0) (hl : l.getLast? = some 1) (u : ℝ) :
    cellIndex l u < cellCount l := by
  obtain ⟨rest, rfl⟩ := List.head?_eq_some_iff.1 hf
  cases rest with
  | nil => simp at hl
  | cons c rs =>
    unfold cellIndex cellCount
    have := List.length_filter_le (fun b => decide (b ≤ u)) ((List.drop 1 (0 :: c :: rs)).dropLast)
    simp only [List.length_dropLast, List.length_drop, List.length_cons] at this ⊢
    omega

theorem pair_norm_le {w x : ℝ} (hw0 : 0 ≤ w) (hw1 : w ≤ 1) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : ‖((w, x) : ℝ × ℝ)‖ ≤ 1 := by
  rw [Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hw0, abs_of_nonneg hx0]
  exact max_le hw1 hx1

end PressureOpenInternal

open PressureOpenInternal

theorem halfEval_slope (S : Spline) (hS : IsSplineClass 0 0 false S) :
    ∃ Λ : ℝ, 0 ≤ Λ ∧ ∀ t t' x x' : ℝ, 0 ≤ t → t ≤ 1 → 0 ≤ t' → t' ≤ 1 → 0 ≤ x → x ≤ 1 → 0 ≤ x' → x' ≤ 1 →
      ‖S.evalHalf t x - S.evalHalf t' x'‖ ≤ Λ * (|t - t'| + |x - x'|) := by
  obtain ⟨B, hB0, hB⟩ := dbound_all S
  have hm := hS.mesh
  have e1 : ‖((1 : ℝ), (0 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have e2 : ‖((0 : ℝ), (1 : ℝ))‖ = 1 := by simp [Prod.norm_def]
  have hT : ∀ x, 0 ≤ x → x ≤ 1 → ∀ u v, 0 ≤ u → u ≤ v → v ≤ 1 →
      ‖S.evalHalf v x - S.evalHalf u x‖ ≤ B * (v - u) := by
    intro x hx0 hx1 u v hu huv hv
    have := slope_one S.mesh.tBreaks hm.t_sorted hm.t_first
      (fun i w => evQ (S.piece i (cellIndex S.mesh.xBreaks x)) (w, x))
      (fun i w => fderiv ℝ (evQ (S.piece i (cellIndex S.mesh.xBreaks x))) (w, x) ((1 : ℝ), (0 : ℝ))) B
      (fun i w => ((evQ_contDiff _).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt w
        ((hasDerivAt_id w).prodMk (hasDerivAt_const w x)))
      (fun i w hi hw0 hw1 => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [e1, mul_one]
        exact hB _ _ hi (cellIndex_le_len _ _) _ (pair_norm_le hw0 hw1 hx0 hx1))
      (fun i hi1 hi2 => by
        have h := hS.t_joins i hi1 hi2 _ (cellIndex_lt_count _ hm.x_first hm.x_last x) 0 le_rfl
        simp only [tDeriv, Function.iterate_zero, id] at h
        exact join_first h x) u v hu huv hv
    simpa [Spline.evalHalf, evQ] using this
  have hX : ∀ t, 0 ≤ t → t ≤ 1 → ∀ u v, 0 ≤ u → u ≤ v → v ≤ 1 →
      ‖S.evalHalf t v - S.evalHalf t u‖ ≤ B * (v - u) := by
    intro t ht0 ht1 u v hu huv hv
    have := slope_one S.mesh.xBreaks hm.x_sorted hm.x_first
      (fun j w => evQ (S.piece (cellIndex S.mesh.tBreaks t) j) (t, w))
      (fun j w => fderiv ℝ (evQ (S.piece (cellIndex S.mesh.tBreaks t) j)) (t, w) ((0 : ℝ), (1 : ℝ))) B
      (fun j w => ((evQ_contDiff _).differentiable (by simp) _).hasFDerivAt.comp_hasDerivAt w
        ((hasDerivAt_const w t).prodMk (hasDerivAt_id w)))
      (fun j w hj hw0 hw1 => by
        refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
        rw [e2, mul_one]
        exact hB _ _ (cellIndex_le_len _ _) hj _ (pair_norm_le ht0 ht1 hw0 hw1))
      (fun j hj1 hj2 => by
        have h := hS.x_joins j hj1 hj2 _ (cellIndex_lt_count _ hm.t_first hm.t_last t) 0 le_rfl
        simp only [xDeriv, Function.iterate_zero, id] at h
        exact join_second h t) u v hu huv hv
    simpa [Spline.evalHalf, evQ] using this
  have hT' : ∀ x, 0 ≤ x → x ≤ 1 → ∀ u v, 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
      ‖S.evalHalf u x - S.evalHalf v x‖ ≤ B * |u - v| := by
    intro x hx0 hx1 u v hu0 hu1 hv0 hv1
    rcases le_total u v with h | h
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]; exact hT x hx0 hx1 u v hu0 h hv1
    · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact hT x hx0 hx1 v u hv0 h hu1
  have hX' : ∀ t, 0 ≤ t → t ≤ 1 → ∀ u v, 0 ≤ u → u ≤ 1 → 0 ≤ v → v ≤ 1 →
      ‖S.evalHalf t u - S.evalHalf t v‖ ≤ B * |u - v| := by
    intro t ht0 ht1 u v hu0 hu1 hv0 hv1
    rcases le_total u v with h | h
    · rw [norm_sub_rev, abs_sub_comm, abs_of_nonneg (sub_nonneg.2 h)]; exact hX t ht0 ht1 u v hu0 h hv1
    · rw [abs_of_nonneg (sub_nonneg.2 h)]; exact hX t ht0 ht1 v u hv0 h hu1
  refine ⟨B, hB0, fun t t' x x' ht0 ht1 ht0' ht1' hx0 hx1 hx0' hx1' => ?_⟩
  calc ‖S.evalHalf t x - S.evalHalf t' x'‖ ≤ ‖S.evalHalf t x - S.evalHalf t' x‖ + ‖S.evalHalf t' x - S.evalHalf t' x'‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ B * |t - t'| + B * |x - x'| :=
        add_le_add (hT' x hx0 hx1 t t' ht0 ht1 ht0' ht1') (hX' t' ht0' ht1' x x' hx0 hx1 hx0' hx1')
    _ = B * (|t - t'| + |x - x'|) := by ring

theorem shape_shell (P : ChartParams) (hP : IsChartParams P) (S : Spline) (hS : IsSplineClass 0 0 false S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ shellSet a b, ∀ y ∈ shellSet a b,
      ‖S.eval false (chartT P x) (heightRatio x) - S.eval false (chartT P y) (heightRatio y)‖ ≤ C / a * ‖x - y‖ := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := halfEval_slope S hS
  refine ⟨3 * Λ, by positivity, fun a b ha hab x hx y hy => ?_⟩
  have hL := hP.L0_pos
  have e : ∀ z, S.eval false (chartT P z) (heightRatio z) = S.evalHalf (chartT P z) |heightRatio z| := by
    intro z; simp [Spline.eval]
  rw [e x, e y]
  obtain ⟨tx0, tx1⟩ := chartT_mem P hP x
  obtain ⟨ty0, ty1⟩ := chartT_mem P hP y
  have h1 := hΛ _ _ _ _ tx0 tx1 ty0 ty1 (abs_nonneg _) (height_abs_le x) (abs_nonneg _) (height_abs_le y)
  have h2 := chartT_sub P hP ha hx.1 hy.1
  have h3 := ratio_sub ha hx.1 hy.1
  have h4 : abs (|heightRatio x| - |heightRatio y|) ≤ |heightRatio x - heightRatio y| := abs_abs_sub_abs_le_abs_sub _ _
  have h5 : P.L0 / (a + P.L0) ^ 2 ≤ 1 / a := by
    rw [div_le_div_iff₀ (by positivity) ha]; nlinarith
  have hd := norm_nonneg (x - y)
  calc _ ≤ Λ * (|chartT P x - chartT P y| + abs (|heightRatio x| - |heightRatio y|)) := h1
    _ ≤ Λ * (1 / a * ‖x - y‖ + 2 / a * ‖x - y‖) := by
        gcongr
        · exact h2.trans (by gcongr)
        · exact h4.trans h3
    _ = 3 * Λ / a * ‖x - y‖ := by ring

theorem shape_bounded (P : ChartParams) (hP : IsChartParams P) (S : Spline) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z : Space, ‖S.eval false (chartT P z) (heightRatio z)‖ ≤ M := by
  obtain ⟨B, hB0, hB⟩ := pieces_bounded S
  refine ⟨B, hB0, fun z => ?_⟩
  obtain ⟨t0, t1⟩ := chartT_mem P hP z
  have hx := height_abs_le z
  simp only [Spline.eval, Spline.evalHalf, Bool.false_and, Bool.false_eq_true, if_false, one_mul]
  exact hB _ _ (by rw [abs_of_nonneg t0]; exact t1) (by rw [abs_abs]; exact hx) _ _
    (cellIndex_le_len _ _) (cellIndex_le_len _ _)

theorem term_shell (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) (k low high axis : ℕ) (S : Spline)
    (hS : IsSplineClass 0 0 false S) (hh : 2 ≤ high) (hax : n ≠ 0 → 1 ≤ axis) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a b : ℝ, 0 < a → a ≤ b → ∀ x ∈ shellSet a b, ∀ y ∈ shellSet a b,
      ‖((decayFactor P x ^ k : ℝ) : ℂ) * modePhase P n β x * pressureShape P low high axis S x -
          ((decayFactor P y ^ k : ℝ) : ℂ) * modePhase P n β y * pressureShape P low high axis S y‖ ≤
        C * (1 + b / a) ^ 2 * (P.L0 / (a + P.L0)) ^ 2 / a * ‖x - y‖ := by
  obtain ⟨CA, hCA, hA⟩ := radial_shell P hP k low high hh
  obtain ⟨CB, hCB, hB⟩ := angular_shell P hP n β axis hax
  obtain ⟨CE, hCE, hE⟩ := shape_shell P hP S hS
  obtain ⟨M, hM, hMb⟩ := shape_bounded P hP S
  refine ⟨CE + M * CB + M * CA, by positivity, fun a b ha hab x hx y hy => ?_⟩
  have hf : ∀ z, ((decayFactor P z ^ k : ℝ) : ℂ) * modePhase P n β z * pressureShape P low high axis S z =
      ((decayFactor P z ^ k * chartT P z ^ low * chartS P z ^ high : ℝ) : ℂ) *
        (modePhase P n β z * ((qOf z ^ axis : ℝ) : ℂ)) * S.eval false (chartT P z) (heightRatio z) := by
    intro z
    unfold pressureShape
    push_cast
    ring
  rw [hf x, hf y]
  set S2 : ℝ := (P.L0 / (a + P.L0)) ^ 2 with hS2
  set d : ℝ := ‖x - y‖ with hd
  have hd0 : 0 ≤ d := norm_nonneg _
  have hS20 : 0 ≤ S2 := by positivity
  have hr : 1 ≤ 1 + b / a := by have : 0 ≤ b / a := div_nonneg (ha.le.trans hab) ha.le; linarith
  have hAx := radial_norm_le P hP k low high hh ha.le hx.1
  have hBx := angular_norm_le P n β axis x
  have hBy := angular_norm_le P n β axis y
  have hEy := hMb y
  have h1 := hA a b ha hab x hx y hy
  have h2 := hB a b ha hab x hx y hy
  have h3 := hE a b ha hab x hx y hy
  set Ax := ((decayFactor P x ^ k * chartT P x ^ low * chartS P x ^ high : ℝ) : ℂ)
  set Ay := ((decayFactor P y ^ k * chartT P y ^ low * chartS P y ^ high : ℝ) : ℂ)
  set Bx := modePhase P n β x * ((qOf x ^ axis : ℝ) : ℂ)
  set By := modePhase P n β y * ((qOf y ^ axis : ℝ) : ℂ)
  set Ex := S.eval false (chartT P x) (heightRatio x)
  set Ey := S.eval false (chartT P y) (heightRatio y)
  have hAB : ‖Ax * Bx - Ay * By‖ ≤ S2 * (CB * (1 + b / a) ^ 2 / a * d) + 1 * (CA * (1 + b / a) * S2 / a * d) := by
    refine (mul_sub_le _ _ _ _).trans ?_
    have hAy0 : 0 ≤ ‖Ax‖ := norm_nonneg _
    gcongr
  have hABx : ‖Ax * Bx‖ ≤ S2 * 1 := by
    rw [norm_mul]; gcongr
  calc ‖Ax * Bx * Ex - Ay * By * Ey‖ ≤ ‖Ax * Bx‖ * ‖Ex - Ey‖ + ‖Ey‖ * ‖Ax * Bx - Ay * By‖ := mul_sub_le _ _ _ _
    _ ≤ (S2 * 1) * (CE / a * d) + M * (S2 * (CB * (1 + b / a) ^ 2 / a * d) + 1 * (CA * (1 + b / a) * S2 / a * d)) := by
        gcongr
    _ = S2 / a * d * (CE + M * CB * (1 + b / a) ^ 2 + M * CA * (1 + b / a)) := by ring
    _ ≤ S2 / a * d * ((CE + M * CB + M * CA) * (1 + b / a) ^ 2) := by
        have hsq : 1 + b / a ≤ (1 + b / a) ^ 2 := by nlinarith
        have hsq1 : 1 ≤ (1 + b / a) ^ 2 := by nlinarith
        have : 0 ≤ S2 / a * d := by positivity
        refine mul_le_mul_of_nonneg_left ?_ this
        nlinarith [mul_le_mul_of_nonneg_left hsq (by positivity : 0 ≤ M * CA), mul_le_mul_of_nonneg_left hsq1 hCE]
    _ = (CE + M * CB + M * CA) * (1 + b / a) ^ 2 * S2 / a * d := by ring

theorem pressure_annulusSlope (P : ChartParams) (hP : IsChartParams P) (D : PressureData) (hD : IsPressureData P D)
    (β : ℝ) (ε : ℝ) (hε : 0 < ε) (R : ℝ) :
    ∃ K : NNReal, LipschitzOnWith K (pressureOf P D β) {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} := by
  by_cases hεR : ε ≤ R
  · have hU : ∀ n ∈ D.modes, ∃ K : ℝ, ∀ x ∈ shellSet ε R, ∀ y ∈ shellSet ε R,
        ‖(((decayFactor P x : ℝ) : ℂ) * modePhase P n β x * pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) x
          + ((decayFactor P x ^ 2 : ℝ) : ℂ) * modePhase P n β x * pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) x) -
        (((decayFactor P y : ℝ) : ℂ) * modePhase P n β y * pressureShape P (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n) y
          + ((decayFactor P y ^ 2 : ℝ) : ℂ) * modePhase P n β y * pressureShape P (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n) y)‖
          ≤ K * ‖x - y‖ := by
      intro n hn
      have hax : n ≠ 0 → 1 ≤ D.axisOrder n := hD.low_axis_ge n hn
      obtain ⟨C1, -, h1⟩ := term_shell P hP n β 1 (D.firstLow n) D.firstHigh (D.axisOrder n) (D.firstAmp n)
        (hD.amp_class n hn).1 hD.high_ge.1 hax
      obtain ⟨C2, -, h2⟩ := term_shell P hP n β 2 (D.secondLow n) D.secondHigh (D.axisOrder n) (D.secondAmp n)
        (hD.amp_class n hn).2 hD.high_ge.2 hax
      refine ⟨C1 * (1 + R / ε) ^ 2 * (P.L0 / (ε + P.L0)) ^ 2 / ε + C2 * (1 + R / ε) ^ 2 * (P.L0 / (ε + P.L0)) ^ 2 / ε,
        fun x hx y hy => ?_⟩
      have e1 := h1 ε R hε hεR x hx y hy
      have e2 := h2 ε R hε hεR x hx y hy
      simp only [pow_one] at e1
      rw [add_sub_add_comm]
      refine (norm_add_le _ _).trans ?_
      linarith
    obtain ⟨K, hK⟩ := sum_shell hU
    refine ⟨Real.toNNReal K, LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_⟩
    rw [dist_eq_norm, dist_eq_norm, Real.norm_eq_abs]
    unfold pressureOf
    rw [← Complex.sub_re]
    refine (Complex.abs_re_le_norm _).trans ?_
    refine (hK x hx y hy).trans ?_
    · exact mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal K) (norm_nonneg _)
  · have he : {y : Space | ε ≤ ‖y‖ ∧ ‖y‖ ≤ R} = ∅ := by
      ext y
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and, not_le]
      intro h
      linarith [not_le.1 hεR]
    rw [he]
    exact ⟨0, lipschitzOnWith_empty _ _⟩

theorem term_slope (P : ChartParams) (hP : IsChartParams P) (n : ℤ) (β : ℝ) (k low high axis : ℕ) (S : Spline)
    (hS : IsSplineClass 0 0 false S) (hh : 2 ≤ high) (hax : n ≠ 0 → 1 ≤ axis) :
    ∃ K : ℝ, ∀ᵐ y ∂volume,
      DifferentiableAt ℝ (fun z => ((decayFactor P z ^ k : ℝ) : ℂ) * modePhase P n β z * pressureShape P low high axis S z) y ∧
        ‖fderiv ℝ (fun z => ((decayFactor P z ^ k : ℝ) : ℂ) * modePhase P n β z * pressureShape P low high axis S z) y‖ ≤
          K * chartS P y ^ 2 / ‖y‖ := by
  obtain ⟨C, hC0, hC⟩ := term_shell P hP n β k low high axis S hS hh hax
  set f := fun z => ((decayFactor P z ^ k : ℝ) : ℂ) * modePhase P n β z * pressureShape P low high axis S z with hf
  have hslope : ∀ a b : ℝ, 0 < a → a ≤ b →
      LipschitzOnWith (Real.toNNReal (C * (1 + b / a) ^ 2 * (P.L0 / (a + P.L0)) ^ 2 / a)) f (shellSet a b) := by
    intro a b ha hab
    refine LipschitzOnWith.of_dist_le_mul fun x hx y hy => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact (hC a b ha hab x hx y hy).trans
      (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  have hdiff : ∀ᵐ y ∂(volume : Measure Space), ∀ m : ℕ,
      y ∈ {z : Space | 1 / ((m : ℝ) + 1) < ‖z‖ ∧ ‖z‖ < (m : ℝ) + 1} → DifferentiableAt ℝ f y := by
    rw [ae_all_iff]
    intro m
    have hm : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
    have hm2 : 1 / ((m : ℝ) + 1) ≤ (m : ℝ) + 1 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
    have hL := (hslope _ _ hm hm2).mono (fun z (hz : z ∈ {z : Space | 1 / ((m : ℝ) + 1) < ‖z‖ ∧ ‖z‖ < (m : ℝ) + 1}) =>
      (⟨hz.1.le, hz.2.le⟩ : z ∈ shellSet _ _))
    have hopen : IsOpen {z : Space | 1 / ((m : ℝ) + 1) < ‖z‖ ∧ ‖z‖ < (m : ℝ) + 1} :=
      (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)
    filter_upwards [hL.ae_differentiableWithinAt_of_mem] with y hy hym
    exact (hy hym).differentiableAt (hopen.mem_nhds hym)
  refine ⟨C * 128, ?_⟩
  filter_upwards [hdiff, compl_mem_ae_iff.2 (measure_singleton (0 : Space))] with y hy hy0
  have hy0' : y ≠ 0 := hy0
  have hr : 0 < ‖y‖ := norm_pos_iff.2 hy0'
  constructor
  · obtain ⟨m, hm⟩ := exists_nat_gt (max ‖y‖ (1 / ‖y‖))
    refine hy m ⟨?_, ?_⟩
    · rw [div_lt_iff₀ (by positivity)]
      have := (le_max_right ‖y‖ (1 / ‖y‖)).trans_lt hm
      rw [div_lt_iff₀ hr] at this
      nlinarith
    · linarith [(le_max_left ‖y‖ (1 / ‖y‖)).trans_lt hm]
  · have hsub : Metric.ball y (‖y‖ / 2) ⊆ shellSet (‖y‖ / 2) (3 * ‖y‖ / 2) := by
      intro z hz
      rw [Metric.mem_ball, dist_eq_norm] at hz
      have h1 := norm_sub_norm_le y z
      have h2 := norm_sub_norm_le z y
      rw [norm_sub_rev] at h1
      exact ⟨by linarith, by linarith⟩
    have hL := (hslope (‖y‖ / 2) (3 * ‖y‖ / 2) (by positivity) (by linarith)).mono hsub
    refine (norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y (by positivity)) hL).trans ?_
    rw [Real.coe_toNNReal _ (by positivity)]
    have hb : 3 * ‖y‖ / 2 / (‖y‖ / 2) = 3 := by field_simp
    rw [hb, chartS_eq P hP]
    have hL0 := hP.L0_pos
    have hq : P.L0 / (‖y‖ / 2 + P.L0) ≤ 2 * (P.L0 / (‖y‖ + P.L0)) := by
      rw [div_le_iff₀ (by positivity)]
      rw [show 2 * (P.L0 / (‖y‖ + P.L0)) * (‖y‖ / 2 + P.L0) = P.L0 * ((‖y‖ + 2 * P.L0) / (‖y‖ + P.L0)) by
        field_simp]
      have : 1 ≤ (‖y‖ + 2 * P.L0) / (‖y‖ + P.L0) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      nlinarith
    have hq2 : (P.L0 / (‖y‖ / 2 + P.L0)) ^ 2 ≤ 4 * (P.L0 / (‖y‖ + P.L0)) ^ 2 := by
      have h0 : 0 ≤ P.L0 / (‖y‖ / 2 + P.L0) := by positivity
      nlinarith
    calc C * (1 + 3) ^ 2 * (P.L0 / (‖y‖ / 2 + P.L0)) ^ 2 / (‖y‖ / 2)
        = C * 32 * (P.L0 / (‖y‖ / 2 + P.L0)) ^ 2 / ‖y‖ := by field_simp; ring
      _ ≤ C * 32 * (4 * (P.L0 / (‖y‖ + P.L0)) ^ 2) / ‖y‖ := by gcongr
      _ = C * 128 * (P.L0 / (‖y‖ + P.L0)) ^ 2 / ‖y‖ := by ring

end PressureOpen

end GivenFields

end CellCert

end Breakdown
