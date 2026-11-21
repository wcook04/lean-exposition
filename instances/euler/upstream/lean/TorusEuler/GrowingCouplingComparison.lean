import TorusEuler.AmplitudeScaledStrainBounds
import TorusEuler.GrowingCouplingBounds

/-! Quantitative comparison of the two normalized couplings in Lemma 2.5. -/

open Set
open scoped InnerProductSpace

namespace TorusEuler.GrowingCoupling

open MovingAmplitude (Entries normFactor scaledEntries referenceScaledStrainEntries)
open MovingWaveVector (Space)
open ReferenceRiccati (referenceNu referenceEta referenceY x s)

noncomputable section

/-- The scaled strain applied to the reference amplitude in the two
coupling numerators of Lemma 2.5. -/
def referenceForcing (ε y : ℝ) : Fin 3 → ℝ := ![1 / 2, -y, ε / 2]

/-- Control of the scaled strain coefficients implies control of the
forcing coordinates. The bound uses the actual size of the third
amplitude coordinate `z`, which can grow across the time window. -/
theorem forcing_sub_reference_le {A : Entries} {S w z ε y R d κ : ℝ}
    (hS : 1 ≤ S) (hR : 4 ≤ R) (hd : 0 ≤ d) (hw : |w| ≤ 2) (hz : |z| ≤ 6 * R)
    (hwy : |w - y| ≤ κ)
    (hA : ∀ i j, |scaledEntries A S i j - referenceScaledStrainEntries ε i j| ≤ d)
    (i : Fin 3) :
    |forcing A w z S i - referenceForcing ε y i| ≤ κ + 7 * R * d := by
  let a := scaledEntries A S
  let b := referenceScaledStrainEntries ε
  let v := if i = 1 then z / S else z
  have hv : |v| ≤ 6 * R := by
    unfold v
    split
    · rw [abs_div, abs_of_nonneg (zero_le_one.trans hS)]
      exact (div_le_self (abs_nonneg _) hS).trans hz
    · exact hz
  have hactual : forcing A w z S i = -w * a i 0 + a i 1 + v * a i 2 := by
    fin_cases i
    all_goals
      simp [forcing, scaledEntries, a, v, Fin.zero_eta, Fin.mk_one, Matrix.cons_val_two,
        Matrix.head_cons, Matrix.tail_cons]
    ring
  have href : referenceForcing ε y i = -y * b i 0 + b i 1 + v * b i 2 := by
    fin_cases i <;>
      simp [referenceForcing, referenceScaledStrainEntries, b, Fin.zero_eta, Fin.mk_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have hb₀ : |b i 0| ≤ 1 := by
    fin_cases i <;>
      norm_num [referenceScaledStrainEntries, b, Fin.zero_eta, Fin.mk_one,
        Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  have h₀ : |-w * (a i 0 - b i 0)| ≤ 2 * d := by
    rw [abs_mul, abs_neg]
    exact mul_le_mul hw (hA i 0) (abs_nonneg _) (by norm_num)
  have h₂ : |v * (a i 2 - b i 2)| ≤ 6 * R * d := by
    rw [abs_mul]
    exact mul_le_mul hv (hA i 2) (abs_nonneg _) (by linarith)
  have hyw : |(y - w) * b i 0| ≤ κ := by
    rw [abs_mul, abs_sub_comm y w, ← mul_one κ]
    exact mul_le_mul hwy hb₀ (abs_nonneg _) ((abs_nonneg _).trans hwy)
  rw [hactual, href, show
    -w * a i 0 + a i 1 + v * a i 2 - (-y * b i 0 + b i 1 + v * b i 2) =
      -w * (a i 0 - b i 0) + (a i 1 - b i 1) + v * (a i 2 - b i 2) +
        (y - w) * b i 0 by ring]
  calc
    _ ≤ |-w * (a i 0 - b i 0) + (a i 1 - b i 1) + v * (a i 2 - b i 2)| +
          |(y - w) * b i 0| := abs_add_le _ _
    _ ≤ (|-w * (a i 0 - b i 0) + (a i 1 - b i 1)| + |v * (a i 2 - b i 2)|) + κ :=
      add_le_add (abs_add_le _ _) hyw
    _ ≤ 2 * d + d + 6 * R * d + κ :=
      add_le_add (add_le_add ((abs_add_le _ _).trans (add_le_add h₀ (hA i 1))) h₂) le_rfl
    _ ≤ _ := by nlinarith only [mul_nonneg (show 0 ≤ R - 3 by linarith) hd]

private theorem abs_product_difference_le {a b a₀ b₀ dA bMax aMax dB : ℝ}
    (ha : |a - a₀| ≤ dA) (hb : |b| ≤ bMax)
    (ha₀ : |a₀| ≤ aMax) (hb₀ : |b - b₀| ≤ dB) :
    |a * b - a₀ * b₀| ≤ dA * bMax + aMax * dB := by
  rw [show a * b - a₀ * b₀ = (a - a₀) * b + a₀ * (b - b₀) by ring]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  exact add_le_add (mul_le_mul ha hb (abs_nonneg _) ((abs_nonneg _).trans ha))
    (mul_le_mul ha₀ hb₀ (abs_nonneg _) ((abs_nonneg _).trans ha₀))

private theorem coupling_coordinate_bounds {R κ X Q Z w x q₀ y : ℝ}
    (hR : 4 ≤ R) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hx : |x| ≤ R / 2) (hq₀ : |q₀| ≤ R / 2) (hy : |y| ≤ 1)
    (hX : |X - x| ≤ κ) (hQ : |Q - q₀| ≤ κ) (hZ : |Z - 1| ≤ κ) (hw : |w - y| ≤ κ) :
    let z := (X * w - Q) / Z
    let z₀ := x * y - q₀
    |X| ≤ R ∧ |Q| ≤ R ∧ 1 / 2 ≤ Z ∧ Z ≤ 2 ∧ |w| ≤ 2 ∧
      |z| ≤ 6 * R ∧ |z₀| ≤ 2 * R ∧ |z - z₀| ≤ 8 * R * κ := by
  let z₀ := x * y - q₀
  have hR₀ : 0 ≤ R := by linarith
  have hXbound : |X| ≤ R := by
    have h := (abs_sub_le X x 0).trans (add_le_add hX (by simpa only [sub_zero] using hx))
    simp only [sub_zero] at h
    linarith
  have hQbound : |Q| ≤ R := by
    have h := (abs_sub_le Q q₀ 0).trans (add_le_add hQ (by simpa only [sub_zero] using hq₀))
    simp only [sub_zero] at h
    linarith
  have hwbound : |w| ≤ 2 := by
    have h := (abs_sub_le w y 0).trans (add_le_add hw (by simpa only [sub_zero] using hy))
    simp only [sub_zero] at h
    linarith
  have hZlo : 1 / 2 ≤ Z := by linarith [(abs_le.mp hZ).1]
  have hZhi : Z ≤ 2 := by linarith [(abs_le.mp hZ).2]
  have hZpos : 0 < Z := by linarith
  have hnum : |X * w - Q| ≤ 3 * R := by
    calc
      _ ≤ |X * w| + |Q| := abs_sub _ _
      _ ≤ R * 2 + R := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hXbound hwbound (abs_nonneg w) hR₀) hQbound
      _ = _ := by ring
  have hzbound : |(X * w - Q) / Z| ≤ 6 * R := by
    rw [abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
    exact hnum.trans (by nlinarith [mul_nonneg hR₀ (sub_nonneg.mpr hZlo)])
  have hz₀bound : |z₀| ≤ 2 * R := by
    calc
      _ ≤ |x * y| + |q₀| := abs_sub _ _
      _ ≤ (R / 2) * 1 + R / 2 := by
        rw [abs_mul]
        exact add_le_add (mul_le_mul hx hy (abs_nonneg y) (by positivity)) hq₀
      _ ≤ _ := by linarith
  have hnumdiff : |X * w - Q - Z * z₀| ≤ 4 * R * κ := by
    have heq : X * w - Q - Z * z₀ =
        X * (w - y) + (X - x) * y - (Q - q₀) - (Z - 1) * z₀ := by
      unfold z₀
      ring
    rw [heq]
    calc
      _ ≤ |X * (w - y) + (X - x) * y - (Q - q₀)| + |(Z - 1) * z₀| := abs_sub _ _
      _ ≤ (|X * (w - y) + (X - x) * y| + |Q - q₀|) + |(Z - 1) * z₀| :=
        add_le_add (abs_sub _ _) le_rfl
      _ ≤ (|X * (w - y)| + |(X - x) * y| + |Q - q₀|) + |(Z - 1) * z₀| :=
        add_le_add (add_le_add (abs_add_le _ _) le_rfl) le_rfl
      _ ≤ (R * κ + κ * 1 + κ) + κ * (2 * R) := by
        rw [abs_mul, abs_mul, abs_mul]
        exact add_le_add
          (add_le_add (add_le_add
            (mul_le_mul hXbound hw (abs_nonneg _) hR₀)
            (mul_le_mul hX hy (abs_nonneg _) hκ)) hQ)
          (mul_le_mul hZ hz₀bound (abs_nonneg _) hκ)
      _ ≤ _ := by nlinarith [mul_nonneg hκ (show 0 ≤ R - 2 by linarith)]
  have hzdiff : |(X * w - Q) / Z - z₀| ≤ 8 * R * κ := by
    have heq : (X * w - Q) / Z - z₀ = (X * w - Q - Z * z₀) / Z := by
      field_simp
    rw [heq, abs_div, abs_of_pos hZpos, div_le_iff₀ hZpos]
    exact hnumdiff.trans (by
      nlinarith [mul_nonneg (mul_nonneg hR₀ hκ) (sub_nonneg.mpr hZlo)])
  exact ⟨hXbound, hQbound, hZlo, hZhi, hwbound, hzbound, hz₀bound, hzdiff⟩

private theorem coupling_abs_inv_sub_inv {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    |a⁻¹ - b⁻¹| = |a - b| / (a * b) := by
  rw [show a⁻¹ - b⁻¹ = (b - a) / (a * b) by field_simp,
    abs_div, abs_sub_comm b a, abs_of_pos (mul_pos ha hb)]

private theorem coupling_abs_inv_sub_one_le {a : ℝ} (ha : 1 ≤ a) :
    |a⁻¹ - 1| ≤ a - 1 := by
  have ha₀ : 0 < a := by linarith
  rw [← inv_one, coupling_abs_inv_sub_inv ha₀ zero_lt_one, mul_one,
    abs_of_nonneg (sub_nonneg.mpr ha)]
  exact (div_le_iff₀ ha₀).mpr (by nlinarith [sq_nonneg (a - 1)])

private theorem coupling_reciprocal_product_bounds
    {a a₀ b d e : ℝ} (ha : 1 / 2 ≤ a) (ha₀ : 1 ≤ a₀) (hb : 1 ≤ b)
    (hda : |a⁻¹ - a₀⁻¹| ≤ d) (hdb : |b⁻¹ - 1| ≤ e) :
    |(a * b)⁻¹| ≤ 2 ∧ |(a * b)⁻¹ - a₀⁻¹| ≤ d + e := by
  have hap : 0 < a := by linarith
  have ha₀p : 0 < a₀ := by linarith
  have hbp : 0 < b := by linarith
  have haInv : a⁻¹ ≤ 2 := by
    have h := (inv_le_inv₀ hap (by norm_num : 0 < (1 : ℝ) / 2)).mpr ha
    norm_num at h
    exact h
  have hbInv : b⁻¹ ≤ 1 := (inv_le_one₀ hbp).mpr hb
  have ha₀Inv : a₀⁻¹ ≤ 1 := (inv_le_one₀ ha₀p).mpr ha₀
  constructor
  · rw [mul_inv, abs_of_nonneg (by positivity)]
    have h := mul_le_mul haInv hbInv (by positivity : (0 : ℝ) ≤ b⁻¹)
      (by norm_num : (0 : ℝ) ≤ 2)
    rwa [mul_one] at h
  · rw [mul_inv, show a⁻¹ * b⁻¹ - a₀⁻¹ =
        (a⁻¹ - a₀⁻¹) * b⁻¹ + a₀⁻¹ * (b⁻¹ - 1) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : 0 ≤ b⁻¹),
      abs_of_nonneg (by positivity : 0 ≤ a₀⁻¹)]
    have h₁ := mul_le_mul hda hbInv (by positivity : (0 : ℝ) ≤ b⁻¹)
      ((abs_nonneg _).trans hda)
    have h₂ := mul_le_mul ha₀Inv hdb (abs_nonneg _)
      (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [mul_one, one_mul] using add_le_add h₁ h₂

/-- The reciprocal denominators of the two normalized couplings stay bounded
and are close to the common reference reciprocal. -/
private theorem coupling_denominator_bounds {R κ X Q Z w z S x : ℝ}
    (hR : 4 ≤ R) (hκ : 0 ≤ κ) (hx : |x| ≤ R / 2)
    (hX : |X| ≤ R) (hQ : |Q| ≤ R) (hZl : 1 / 2 ≤ Z) (hZh : Z ≤ 2)
    (hw : |w| ≤ 2) (hz : |z| ≤ 6 * R)
    (hXclose : |X - x| ≤ κ) (hZclose : |Z - 1| ≤ κ) (hSinv : (S ^ 2)⁻¹ ≤ κ) :
    let m := MovingAmplitude.normFactor X Q Z S
    let m₀ := 1 + x ^ 2
    let n := Real.sqrt (1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2))
    let Dν := (Real.sqrt m * n)⁻¹
    let Dη := (Real.sqrt m * n ^ 2)⁻¹
    let s := (Real.sqrt m₀)⁻¹
    |Dν| ≤ 2 ∧ |Dη| ≤ 2 ∧
      |Dν - s| ≤ 41 * R ^ 2 * κ ∧ |Dη - s| ≤ 41 * R ^ 2 * κ := by
  let m := MovingAmplitude.normFactor X Q Z S
  let m₀ := 1 + x ^ 2
  let n := Real.sqrt (1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2))
  let a := Real.sqrt m
  let a₀ := Real.sqrt m₀
  change |(a * n)⁻¹| ≤ 2 ∧ |(a * n ^ 2)⁻¹| ≤ 2 ∧
    |(a * n)⁻¹ - a₀⁻¹| ≤ 41 * R ^ 2 * κ ∧
    |(a * n ^ 2)⁻¹ - a₀⁻¹| ≤ 41 * R ^ 2 * κ
  have hR₀ : 0 ≤ R := by linarith
  have hZ₀ : 0 ≤ Z := by linarith
  have hm : 1 / 4 ≤ m := by
    have hZsq := (sq_le_sq₀ (by norm_num : 0 ≤ (1 : ℝ) / 2) hZ₀).mpr hZl
    unfold m MovingAmplitude.normFactor
    linarith [sq_nonneg X, div_nonneg (sq_nonneg Q) (sq_nonneg S)]
  have hm₀ : 1 ≤ m₀ := by unfold m₀; linarith [sq_nonneg x]
  have ha : 1 / 2 ≤ a := by
    have hs := Real.sqrt_le_sqrt hm
    rw [show (1 : ℝ) / 4 = ((1 : ℝ) / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num : 0 ≤ (1 : ℝ) / 2)] at hs
    exact hs
  have ha₀ : 1 ≤ a₀ := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hm₀
  have hn : 1 ≤ n := by
    have hp : 1 ≤ 1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2) :=
      le_add_of_nonneg_right (by positivity)
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hp
  have hnsq : 1 ≤ n ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ n + 1 by linarith)]
  have hxdiff : |X ^ 2 - x ^ 2| ≤ (R + R / 2) * κ := by
    rw [show X ^ 2 - x ^ 2 = (X + x) * (X - x) by ring, abs_mul]
    exact mul_le_mul ((abs_add_le X x).trans (add_le_add hX hx)) hXclose
      (abs_nonneg _) (by positivity)
  have hzdiff : |Z ^ 2 - 1| ≤ 3 * κ := by
    rw [show Z ^ 2 - 1 = (Z + 1) * (Z - 1) by ring, abs_mul,
      abs_of_nonneg (by positivity : 0 ≤ Z + 1)]
    exact mul_le_mul (by linarith) hZclose (abs_nonneg _) (by norm_num)
  have hqterm : |Q ^ 2 / S ^ 2| ≤ R ^ 2 * κ := by
    have hQsq := (sq_le_sq₀ (abs_nonneg Q) hR₀).mpr hQ
    rw [sq_abs] at hQsq
    rw [abs_of_nonneg (by positivity), div_eq_mul_inv]
    exact mul_le_mul hQsq hSinv (by positivity) (sq_nonneg _)
  have hmdiff : |m - m₀| ≤ 2 * R ^ 2 * κ := by
    rw [show m - m₀ = (X ^ 2 - x ^ 2) + (Z ^ 2 - 1) + Q ^ 2 / S ^ 2 by
      unfold m m₀ MovingAmplitude.normFactor
      ring]
    have hcoeff : R + R / 2 + 3 ≤ R ^ 2 := by
      nlinarith [sq_nonneg (R - 4)]
    calc
      _ ≤ |X ^ 2 - x ^ 2| + |Z ^ 2 - 1| + |Q ^ 2 / S ^ 2| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ (R + R / 2) * κ + 3 * κ + R ^ 2 * κ :=
        add_le_add (add_le_add hxdiff hzdiff) hqterm
      _ = (R + R / 2 + 3 + R ^ 2) * κ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hκ
  have hapos : 0 < a := by linarith
  have ha₀pos : 0 < a₀ := by linarith
  have hsumpos : 0 < a + a₀ := by positivity
  have hsq_a : a ^ 2 = m := Real.sq_sqrt (by linarith)
  have hsq_a₀ : a₀ ^ 2 = m₀ := Real.sq_sqrt (by linarith)
  have habsfactor : |a - a₀| * (a + a₀) = |m - m₀| := by
    rw [← abs_of_pos hsumpos, ← abs_mul,
      show (a - a₀) * (a + a₀) = a ^ 2 - a₀ ^ 2 by ring, hsq_a, hsq_a₀]
  have hadiff : |a⁻¹ - a₀⁻¹| ≤ 4 * R ^ 2 * κ := by
    have hprod : (1 : ℝ) / 2 ≤ a * a₀ := by
      simpa only [mul_one] using
        (mul_le_mul ha ha₀ (by norm_num : (0 : ℝ) ≤ 1) hapos.le)
    have hden : (1 : ℝ) / 2 ≤ a * a₀ * (a + a₀) := by
      simpa only [mul_one] using
        (mul_le_mul hprod (show 1 ≤ a + a₀ by linarith)
          (by norm_num : (0 : ℝ) ≤ 1) (mul_nonneg hapos.le ha₀pos.le))
    calc
      _ = |a - a₀| / (a * a₀) := coupling_abs_inv_sub_inv hapos ha₀pos
      _ ≤ 2 * |m - m₀| := by
        rw [← habsfactor, div_le_iff₀ (mul_pos hapos ha₀pos)]
        calc
          _ = 1 * |a - a₀| := (one_mul _).symm
          _ ≤ (2 * (a * a₀ * (a + a₀))) * |a - a₀| :=
            mul_le_mul_of_nonneg_right (by linarith) (abs_nonneg _)
          _ = _ := by ring
      _ ≤ _ := by linarith
  have hnerr : n ^ 2 - 1 ≤ 37 * R ^ 2 * κ := by
    have hwsq := (sq_le_sq₀ (abs_nonneg w) (by norm_num : (0 : ℝ) ≤ 2)).mpr hw
    have hzsq := (sq_le_sq₀ (abs_nonneg z) (by positivity : 0 ≤ 6 * R)).mpr hz
    rw [sq_abs] at hwsq hzsq
    have hsz : w ^ 2 + z ^ 2 ≤ 37 * R ^ 2 := by
      nlinarith [sq_nonneg (R - 4)]
    change (Real.sqrt (1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2))) ^ 2 - 1 ≤ _
    rw [Real.sq_sqrt (by positivity), add_sub_cancel_left]
    exact (mul_le_mul hSinv hsz (by positivity : 0 ≤ w ^ 2 + z ^ 2) hκ).trans_eq (mul_comm _ _)
  have hnInv : |n⁻¹ - 1| ≤ 37 * R ^ 2 * κ := by
    have hnle : n ≤ n ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ n by linarith)]
    exact (coupling_abs_inv_sub_one_le hn).trans ((sub_le_sub_right hnle 1).trans hnerr)
  have hnSqInv : |(n ^ 2)⁻¹ - 1| ≤ 37 * R ^ 2 * κ :=
    (coupling_abs_inv_sub_one_le hnsq).trans hnerr
  obtain ⟨hν, hνerr⟩ := coupling_reciprocal_product_bounds ha ha₀ hn hadiff hnInv
  obtain ⟨hη, hηerr⟩ := coupling_reciprocal_product_bounds ha ha₀ hnsq hadiff hnSqInv
  exact ⟨hν, hη, hνerr.trans_eq (by ring), hηerr.trans_eq (by ring)⟩

/-- The first numerator and its reference difference have linear coordinate bounds. -/
private theorem coupling_first_numerator_bounds {R κ X Q Z x q₀ y ε w z r z₀ : ℝ} {f : Fin 3 → ℝ}
    (hR : 4 ≤ R) (hκ : 0 ≤ κ) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1)
    (hx : |x| ≤ R / 2) (hq₀ : |q₀| ≤ R / 2) (hy : |y| ≤ 1)
    (hX : |X| ≤ R) (hQ : |Q| ≤ R) (hZlo : 0 ≤ Z) (hZhi : Z ≤ 2)
    (hXδ : |X - x| ≤ κ) (hQδ : |Q - q₀| ≤ κ) (hZδ : |Z - 1| ≤ κ)
    (hf : ∀ i, |f i - (![1 / 2, -y, ε / 2] : Fin 3 → ℝ) i| ≤ κ) :
    let f₀ : Fin 3 → ℝ := ![1 / 2, -y, ε / 2]
    let N₀ := couplingNumerators x q₀ 1 y z₀ 0 f₀
    let N := couplingNumerators X Q Z w z r f
    |N₀.1| ≤ 6 * R ∧ |N.1 - N₀.1| ≤ 8 * R * κ := by
  have h₀ : |(1 / 2 : ℝ)| ≤ 1 / 2 := by norm_num
  have h₁ : |-y| ≤ 1 := by simpa only [abs_neg] using hy
  have h₂ : |ε / 2| ≤ 1 / 2 := by
    rw [abs_of_nonneg (by positivity)]
    linarith
  have hZ : |Z| ≤ 2 := by rwa [abs_of_nonneg hZlo]
  have hf₀ : |f 0 - 1 / 2| ≤ κ := hf 0
  have hf₁ : |f 1 - (-y)| ≤ κ := hf 1
  have hf₂ : |f 2 - ε / 2| ≤ κ := hf 2
  have hP₀ : |x * (1 / 2)| ≤ (R / 2) * (1 / 2) := by
    rw [abs_mul]
    exact mul_le_mul hx h₀ (abs_nonneg _) (by linarith)
  have hP₁ : |q₀ * (-y)| ≤ (R / 2) * 1 := by
    rw [abs_mul]
    exact mul_le_mul hq₀ h₁ (abs_nonneg _) (by linarith)
  have hP₂ : |1 * (ε / 2)| ≤ 1 / 2 := by simpa only [one_mul] using h₂
  have hD₀ : |X * f 0 - x * (1 / 2)| ≤ R * κ + κ * (1 / 2) :=
    (by simpa only [mul_comm] using abs_product_difference_le hf₀ hX h₀ hXδ)
  have hD₁ : |Q * f 1 - q₀ * (-y)| ≤ R * κ + κ * 1 :=
    (by simpa only [mul_comm] using abs_product_difference_le hf₁ hQ h₁ hQδ)
  have hD₂ : |Z * f 2 - 1 * (ε / 2)| ≤ 2 * κ + κ * (1 / 2) :=
    (by simpa only [mul_comm] using abs_product_difference_le hf₂ hZ h₂ hZδ)
  change |2 * (x * (1 / 2) + q₀ * (-y) + 1 * (ε / 2))| ≤ 6 * R ∧
    |2 * (X * f 0 + Q * f 1 + Z * f 2) -
      2 * (x * (1 / 2) + q₀ * (-y) + 1 * (ε / 2))| ≤ 8 * R * κ
  constructor
  · rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hsum := (abs_add_le (x * (1 / 2) + q₀ * (-y)) (1 * (ε / 2))).trans
      (add_le_add (abs_add_le _ _) le_rfl)
    linarith
  · rw [show 2 * (X * f 0 + Q * f 1 + Z * f 2) -
      2 * (x * (1 / 2) + q₀ * (-y) + 1 * (ε / 2)) =
      2 * ((X * f 0 - x * (1 / 2)) + (Q * f 1 - q₀ * (-y)) +
        (Z * f 2 - 1 * (ε / 2))) by ring]
    rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    have hsum := (abs_add_le ((X * f 0 - x * (1 / 2)) + (Q * f 1 - q₀ * (-y)))
      (Z * f 2 - 1 * (ε / 2))).trans (add_le_add (abs_add_le _ _) le_rfl)
    nlinarith [mul_nonneg (sub_nonneg.mpr hR) hκ]

private theorem couplingAbs_mul_sub_le (a b a₀ b₀ : ℝ) :
    |a * b - a₀ * b₀| ≤ |a| * |b - b₀| + |a - a₀| * |b₀| := by
  calc
    _ = |a * (b - b₀) + (a - a₀) * b₀| := by congr 1; ring
    _ ≤ _ := by simpa only [abs_mul] using abs_add_le (a * (b - b₀)) ((a - a₀) * b₀)

private theorem couplingAbs_add3_le (a b c : ℝ) :
    |a + b + c| ≤ |a| + |b| + |c| :=
  (abs_add_le (a + b) c).trans (add_le_add (abs_add_le a b) le_rfl)

private theorem couplingAbs_sub_sums_le (a b c a₀ b₀ c₀ : ℝ) :
    |a - b + c - (a₀ - b₀ + c₀)| ≤ |a - a₀| + |b - b₀| + |c - c₀| := by
  calc
    _ = |(a - a₀) + -(b - b₀) + (c - c₀)| := by congr 1; ring
    _ ≤ _ := by simpa only [abs_neg] using couplingAbs_add3_le (a - a₀) (-(b - b₀)) (c - c₀)

private theorem coupling_second_numerator_bounds {R κ X Q Z w z x q₀ y z₀ r ε : ℝ}
    {f : Fin 3 → ℝ} (hR : 4 ≤ R) (hκ₀ : 0 ≤ κ) (hκ : κ ≤ 1 / 2)
    (hε₀ : 0 ≤ ε) (hε : ε ≤ 1)
    (hx : |x| ≤ R / 2) (hy : |y| ≤ 1)
    (hX : |X| ≤ R) (hQ : |Q| ≤ R) (hZ₀ : 1 / 2 ≤ Z) (hZ₁ : Z ≤ 2)
    (hw : |w| ≤ 2) (hz : |z| ≤ 6 * R) (hz₀ : |z₀| ≤ 2 * R)
    (hzd : |z - z₀| ≤ 8 * R * κ)
    (hXd : |X - x| ≤ κ) (hZd : |Z - 1| ≤ κ) (hwd : |w - y| ≤ κ)
    (hr₀ : 0 ≤ r) (hr : r ≤ κ)
    (hf : ∀ i, |f i - (![1 / 2, -y, ε / 2] : Fin 3 → ℝ) i| ≤ κ) :
    let f₀ : Fin 3 → ℝ := ![1 / 2, -y, ε / 2]
    let N := couplingNumerators X Q Z w z r f
    let N₀ := couplingNumerators x q₀ 1 y z₀ 0 f₀
    |N₀.2| ≤ 6 * R ^ 2 ∧ |N.2 - N₀.2| ≤ 74 * R ^ 2 * κ := by
  let f₀ : Fin 3 → ℝ := ![1 / 2, -y, ε / 2]
  change ∀ i, |f i - f₀ i| ≤ κ at hf
  let c₁ := -Z + Q * z * r
  let c₂ := Z * w + X * z
  let c₃ := X + Q * w * r
  let c₁₀ : ℝ := -1
  let c₂₀ := y + x * z₀
  let c₃₀ := x
  have hR₀ : 0 ≤ R := by linarith
  have hRlin : 4 * R ≤ R ^ 2 := by nlinarith [mul_nonneg (sub_nonneg.mpr hR) hR₀]
  have hf₀ (i : Fin 3) : |f₀ i| ≤ 1 := by
    fin_cases i
    · norm_num [f₀, Matrix.cons_val_zero, Fin.zero_eta]
    · simpa [f₀, Matrix.cons_val_one, Fin.mk_one] using hy
    · have heh : 0 ≤ ε / 2 := by positivity
      change |ε / 2| ≤ 1
      simpa only [abs_of_nonneg heh] using (show ε / 2 ≤ 1 by linarith)
  have hf₂ (i : Fin 3) : |f i| ≤ 2 := by
    calc
      _ ≤ |f i - f₀ i| + |f₀ i| := by
        simpa only [sub_add_cancel] using abs_add_le (f i - f₀ i) (f₀ i)
      _ ≤ κ + 1 := add_le_add (hf i) (hf₀ i)
      _ ≤ _ := by linarith
  have hZ : |Z| ≤ 2 := by
    rw [abs_of_nonneg (by linarith : 0 ≤ Z)]
    exact hZ₁
  have hprod₁ : |Q * z * r| ≤ 6 * R ^ 2 * κ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr₀]
    calc
      _ ≤ (R * (6 * R)) * κ := by gcongr
      _ = _ := by ring
  have hprod₃ : |Q * w * r| ≤ 2 * R * κ := by
    rw [abs_mul, abs_mul, abs_of_nonneg hr₀]
    calc
      _ ≤ (R * 2) * κ := by gcongr
      _ = _ := by ring
  have hc₁ : |c₁ - c₁₀| ≤ 7 * R ^ 2 * κ := by
    calc
      _ = |-(Z - 1) + Q * z * r| := by dsimp only [c₁, c₁₀]; congr 1; ring
      _ ≤ |Z - 1| + |Q * z * r| := by
        simpa only [abs_neg] using abs_add_le (-(Z - 1)) (Q * z * r)
      _ ≤ κ + 6 * R ^ 2 * κ := add_le_add hZd hprod₁
      _ = (1 + 6 * R ^ 2) * κ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hκ₀
  have hc₂ : |c₂ - c₂₀| ≤ 9 * R ^ 2 * κ := by
    have hZw : |Z * w - y| ≤ 3 * κ := by
      simpa only [one_mul] using
        calc
          |Z * w - 1 * y| ≤ |Z| * |w - y| + |Z - 1| * |y| := couplingAbs_mul_sub_le Z w 1 y
          _ ≤ 2 * κ + κ * 1 := by gcongr
          _ = _ := by ring
    have hXz : |X * z - x * z₀| ≤ (8 * R ^ 2 + 2 * R) * κ := by
      calc
        _ ≤ |X| * |z - z₀| + |X - x| * |z₀| := couplingAbs_mul_sub_le X z x z₀
        _ ≤ R * (8 * R * κ) + κ * (2 * R) := by gcongr
        _ = _ := by ring
    calc
      _ = |(Z * w - y) + (X * z - x * z₀)| := by dsimp only [c₂, c₂₀]; congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hZw hXz)
      _ = (3 + (8 * R ^ 2 + 2 * R)) * κ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hκ₀
  have hc₃ : |c₃ - c₃₀| ≤ R ^ 2 * κ := by
    calc
      _ = |(X - x) + Q * w * r| := by dsimp only [c₃, c₃₀]; congr 1; ring
      _ ≤ _ := (abs_add_le _ _).trans (add_le_add hXd hprod₃)
      _ = (1 + 2 * R) * κ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith) hκ₀
  have hc₀ : |c₁₀| + |c₂₀| + |c₃₀| ≤ 3 * R ^ 2 := by
    have hc₂₀ : |c₂₀| ≤ 1 + R ^ 2 := by
      calc
        _ ≤ |y| + |x| * |z₀| := by simpa only [c₂₀, abs_mul] using abs_add_le y (x * z₀)
        _ ≤ 1 + R / 2 * (2 * R) := by gcongr
        _ = _ := by ring
    have hc₁₀ : |c₁₀| = 1 := by norm_num [c₁₀]
    calc
      _ ≤ 1 + (1 + R ^ 2) + R / 2 :=
        add_le_add (add_le_add hc₁₀.le hc₂₀) hx
      _ ≤ _ := by linarith
  let A := c₁ * f 0 - c₂ * f 1 + c₃ * f 2
  let A₀ := c₁₀ * f₀ 0 - c₂₀ * f₀ 1 + c₃₀ * f₀ 2
  have hA₀ : |A₀| ≤ 3 * R ^ 2 := by
    calc
      _ ≤ |c₁₀| * |f₀ 0| + |c₂₀| * |f₀ 1| + |c₃₀| * |f₀ 2| := by
        simpa only [A₀, sub_eq_add_neg, abs_neg, abs_mul] using
          couplingAbs_add3_le (c₁₀ * f₀ 0) (-(c₂₀ * f₀ 1)) (c₃₀ * f₀ 2)
      _ ≤ |c₁₀| * 1 + |c₂₀| * 1 + |c₃₀| * 1 := by gcongr <;> exact hf₀ _
      _ ≤ _ := by simpa only [mul_one] using hc₀
  have hA : |A - A₀| ≤ 37 * R ^ 2 * κ := by
    have hterm (i : Fin 3) {c c₀ C : ℝ} (hc : |c - c₀| ≤ C) :
        |c * f i - c₀ * f₀ i| ≤ 2 * C + κ * |c₀| := by
      rw [mul_comm c, mul_comm c₀]
      apply (couplingAbs_mul_sub_le _ _ _ _).trans
      exact add_le_add
        (mul_le_mul (hf₂ i) hc (abs_nonneg _) (by norm_num))
        (mul_le_mul_of_nonneg_right (hf i) (abs_nonneg _))
    calc
      _ ≤ |c₁ * f 0 - c₁₀ * f₀ 0| + |c₂ * f 1 - c₂₀ * f₀ 1| +
          |c₃ * f 2 - c₃₀ * f₀ 2| := couplingAbs_sub_sums_le _ _ _ _ _ _
      _ ≤ _ := add_le_add (add_le_add (hterm 0 hc₁) (hterm 1 hc₂)) (hterm 2 hc₃)
      _ = 34 * R ^ 2 * κ + κ * (|c₁₀| + |c₂₀| + |c₃₀|) := by ring
      _ ≤ 34 * R ^ 2 * κ + κ * (3 * R ^ 2) := by gcongr
      _ = _ := by ring
  have hN : (couplingNumerators X Q Z w z r f).2 = 2 * A := rfl
  have hN₀ : (couplingNumerators x q₀ 1 y z₀ 0 f₀).2 = 2 * A₀ := by
    simp only [couplingNumerators, A₀, c₁₀, c₂₀, c₃₀, mul_zero, add_zero, one_mul]
  change |(couplingNumerators x q₀ 1 y z₀ 0 f₀).2| ≤ 6 * R ^ 2 ∧
    |(couplingNumerators X Q Z w z r f).2 -
      (couplingNumerators x q₀ 1 y z₀ 0 f₀).2| ≤ 74 * R ^ 2 * κ
  rw [hN, hN₀, ← mul_sub]
  simp only [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
  exact ⟨(mul_le_mul_of_nonneg_left hA₀ (by norm_num)).trans_eq (by ring),
    (mul_le_mul_of_nonneg_left hA (by norm_num)).trans_eq (by ring)⟩

/-- The rational terms for the first and second normalized couplings.
The second denominator includes two factors of the amplitude norm. -/
def rationalCouplings (X Q Z w S : ℝ) (f : Fin 3 → ℝ) : ℝ × ℝ :=
  let z := (X * w - Q) / Z
  let m := normFactor X Q Z S
  let n := Real.sqrt (1 + (S ^ 2)⁻¹ * (w ^ 2 + z ^ 2))
  let N := couplingNumerators X Q Z w z (S ^ 2)⁻¹ f
  (N.1 / (Real.sqrt m * n), N.2 / (Real.sqrt m * n ^ 2))

private theorem normalized_product_sub_le {R κ A A₀ D s₀ : ℝ}
    (hR : 4 ≤ R) (hκ : 0 ≤ κ)
    (hA : |A - A₀| ≤ 74 * R ^ 2 * κ) (hA₀ : |A₀| ≤ 6 * R ^ 2)
    (hD : |D| ≤ 2) (hD₀ : |D - s₀| ≤ 41 * R ^ 2 * κ) :
    |A * D - A₀ * s₀| ≤ 256 * R ^ 4 * κ := by
  refine (abs_product_difference_le hA hD hA₀ hD₀).trans ?_
  have hR₁₆ : 16 ≤ R ^ 2 := by
    nlinarith only [hR, sq_nonneg (R - 4)]
  have h := mul_nonneg (sub_nonneg.mpr hR₁₆) (show 0 ≤ R ^ 2 * κ by positivity)
  nlinarith only [h, show 0 ≤ R ^ 2 * κ by positivity]

private theorem reference_coordinate_box {ε τ T : ℝ}
    (hT : 2 ≤ T) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hτ : τ ∈ Icc 0 T) :
    4 ≤ T ^ 2 ∧ |x ε τ| ≤ T ^ 2 / 2 ∧ |-(ε * τ)| ≤ T ^ 2 / 2 := by
  have hT₀ : 0 ≤ T := by linarith
  have hTtwo : 4 ≤ T ^ 2 := by nlinarith only [hT, sq_nonneg (T - 2)]
  have hτ₂ : τ ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hτ.1 hτ.2 2
  refine ⟨hTtwo, ?_, ?_⟩
  · rw [abs_of_nonneg (ReferenceRiccati.x_nonneg hε τ), x]
    nlinarith only [hτ₂, mul_le_mul_of_nonneg_right hε₁ (sq_nonneg τ)]
  · rw [abs_neg, abs_of_nonneg (mul_nonneg hε hτ.1)]
    have hτbound := (mul_le_mul_of_nonneg_right hε₁ hτ.1).trans (by simpa using hτ.2)
    nlinarith only [hτbound, mul_nonneg (sub_nonneg.mpr hT) hT₀]


/-- If the scaled inputs in Lemma 2.5 have common error at most `κ`, the
two rational coupling values differ from their reference values by at
most `256 * T ^ 8 * κ`. -/
theorem rational_couplings_sub_reference_le {X Q Z w S ε τ T κ : ℝ}
    {Y : ℝ → ℝ} (f : Fin 3 → ℝ) (hT : 2 ≤ T) (hτ : τ ∈ Icc 0 T)
    (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hY : |Y τ| ≤ 1)
    (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hX : |X - x ε τ| ≤ κ) (hQ : |Q + ε * τ| ≤ κ) (hZ : |Z - 1| ≤ κ)
    (hw : |w - Y τ| ≤ κ) (hS : (S ^ 2)⁻¹ ≤ κ)
    (hf : ∀ i, |f i - referenceForcing ε (Y τ) i| ≤ κ) :
    let N := rationalCouplings X Q Z w S f
    |N.1 - referenceNu ε τ Y| ≤ 256 * T ^ 8 * κ ∧
      |N.2 - referenceEta ε τ Y| ≤ 256 * T ^ 8 * κ := by
  let R := T ^ 2
  let x₀ := x ε τ
  let q₀ := -(ε * τ)
  let y := Y τ
  let z₀ := x₀ * y - q₀
  let z := (X * w - Q) / Z
  let r := (S ^ 2)⁻¹
  let m := normFactor X Q Z S
  let n := Real.sqrt (1 + r * (w ^ 2 + z ^ 2))
  let Dν := (Real.sqrt m * n)⁻¹
  let Dη := (Real.sqrt m * n ^ 2)⁻¹
  let N := couplingNumerators X Q Z w z r f
  let N₀ := couplingNumerators x₀ q₀ 1 y z₀ 0 (referenceForcing ε y)
  obtain ⟨hR, hx₀, hq₀⟩ := reference_coordinate_box hT hε hε₁ hτ
  have hQ' : |Q - q₀| ≤ κ := by simpa only [q₀, sub_neg_eq_add] using hQ
  obtain ⟨hXmax, hQmax, hZlo, hZhi, hwmax, hzmax, hz₀max, hzd⟩ :=
    coupling_coordinate_bounds hR hκ hκhalf hx₀ hq₀ hY hX hQ' hZ hw
  obtain ⟨hDν, hDη, hDνd, hDηd⟩ :=
    coupling_denominator_bounds hR hκ hx₀ hXmax hQmax hZlo hZhi hwmax hzmax hX hZ hS
  have hZ₀ : 0 ≤ Z := by linarith
  obtain ⟨hN₀ν, hNν⟩ := coupling_first_numerator_bounds
    (w := w) (z := z) (r := r) (z₀ := z₀)
    hR hκ hε hε₁ hx₀ hq₀ hY hXmax hQmax hZ₀ hZhi hX hQ' hZ hf
  obtain ⟨hN₀η, hNη⟩ := coupling_second_numerator_bounds
    hR hκ hκhalf hε hε₁ hx₀ hY hXmax hQmax hZlo hZhi hwmax hzmax hz₀max
    hzd hX hZ hw (show 0 ≤ r by positivity) hS hf
  have hR₂ : R ≤ R ^ 2 := by
    nlinarith only [hR, sq_nonneg (R - 1)]
  have hN₀ν' : |N₀.1| ≤ 6 * R ^ 2 := hN₀ν.trans (by linarith only [hR₂])
  have hNν' : |N.1 - N₀.1| ≤ 74 * R ^ 2 * κ :=
    hNν.trans (mul_le_mul_of_nonneg_right (by nlinarith only [hR₂, hR]) hκ)
  have href : N₀ =
      (x₀ + ε + 2 * ε * τ * y,
        -1 + ε * x₀ + 2 * (1 + x₀ ^ 2) * y ^ 2 + 2 * ε * τ * x₀ * y) := by
    simpa only [N₀, q₀, z₀, sub_neg_eq_add, referenceForcing] using
      couplingNumerators_reference ε τ y
  have hrefν : referenceNu ε τ Y = N₀.1 * s ε τ := by rw [href, referenceNu]
  have hrefη : referenceEta ε τ Y = N₀.2 * s ε τ := by rw [href, referenceEta]
  have hRpow : R ^ 4 = T ^ 8 := by unfold R; ring
  change |N.1 / (Real.sqrt m * n) - referenceNu ε τ Y| ≤ _ ∧
    |N.2 / (Real.sqrt m * n ^ 2) - referenceEta ε τ Y| ≤ _
  rw [hrefν, hrefη, div_eq_mul_inv, div_eq_mul_inv, ← hRpow]
  exact ⟨normalized_product_sub_le hR hκ hNν' hN₀ν' hDν hDνd,
    normalized_product_sub_le hR hκ hNη hN₀η hDη hDηd⟩


/-- The reference error for the actual moving-frame couplings. The input
budget accounts for the wave coordinates, the amplitude ratio, and the
scaled older strain. The additional strain contributes at most `2 * δ`. -/
theorem normalized_couplings_sub_reference_le {e : ℝ → Fin 3 → Space} {k a : ℝ → Space}
    {Y : ℝ → ℝ} {scale S σratio ε τ T κ δ : ℝ} (B E : Space →L[ℝ] Space)
    (hT : 2 ≤ T) (hτ : τ ∈ Icc 0 T) (hε : 0 ≤ ε) (hε₁ : ε ≤ 1) (hY : |Y τ| ≤ 1)
    (he : Orthonormal ℝ (e τ)) (hOrient : cross3 (e τ 0) (e τ 1) = e τ 2)
    (hscale : 0 < scale) (hS : 1 ≤ S) (hV : 0 < MovingAmplitude.V e a τ)
    (hperp : ⟪k τ, a τ⟫_ℝ = 0)
    (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) (hκhalf : κ ≤ 1 / 2)
    (hX : |MovingWaveVector.X e k scale τ - x ε τ| ≤ κ)
    (hQ : |MovingWaveVector.Q e k scale S τ + ε * τ| ≤ κ)
    (hZ : |MovingWaveVector.Z e k scale τ - 1| ≤ κ)
    (hS₂ : (S ^ 2)⁻¹ ≤ κ)
    (hw : |MovingAmplitude.U e a S τ / MovingAmplitude.V e a τ - Y τ| +
      21 * T ^ 3 * δ ≤ κ)
    (hB : ‖B‖ ≤ δ)
    (h12 : |2 * S * MovingWaveVector.entry (e τ) B 0 1 - 1| ≤ δ)
    (h32 : |2 * S * MovingWaveVector.entry (e τ) B 2 1 - ε| ≤ δ)
    (hσ : |σratio - 1| ≤ 2 * T * δ) (hE : ‖E‖ ≤ δ / S) :
    let M := MovingWaveVector.strain (e τ) B E S σratio
    |normalizedNu M (k τ) (a τ) S - referenceNu ε τ Y| ≤ 256 * T ^ 8 * κ + 2 * δ ∧
      |normalizedEta M (k τ) (a τ) S - referenceEta ε τ Y| ≤ 256 * T ^ 8 * κ + 2 * δ := by
  let X := MovingWaveVector.X e k scale τ
  let Q := MovingWaveVector.Q e k scale S τ
  let Z := MovingWaveVector.Z e k scale τ
  let w := MovingAmplitude.U e a S τ / MovingAmplitude.V e a τ
  let z := (X * w - Q) / Z
  let M₀ := MovingWaveVector.strain (e τ) B 0 S σratio
  let M := MovingWaveVector.strain (e τ) B E S σratio
  let A := MovingWaveVector.entry (e τ) M₀
  let f := forcing A w z S
  have hT₁ : 1 ≤ T := by linarith
  have hS₀ : 0 < S := by linarith
  have hwκ : |w - Y τ| ≤ κ := hw.trans' (le_add_of_nonneg_right (by positivity))
  obtain ⟨hR, hx, hq⟩ := reference_coordinate_box hT hε hε₁ hτ
  have hQ' : |Q - (-(ε * τ))| ≤ κ := by simpa only [sub_neg_eq_add] using hQ
  obtain ⟨_, _, hZlo, _, hwmax, hzmax, _, _⟩ :=
    coupling_coordinate_bounds hR hκ hκhalf hx hq hY hX hQ' hZ hwκ
  have hZ₀ : Z ≠ 0 := by linarith
  have hf (i : Fin 3) : |f i - referenceForcing ε (Y τ) i| ≤ κ := by
    have hentry := MovingAmplitude.scaledStrainEntries_sub_ref_le he B hδ hT₁ hS hB h12 h32 hσ
    refine (forcing_sub_reference_le (A := A) hS hR (show 0 ≤ 3 * T * δ by positivity)
      hwmax hzmax (le_refl |w - Y τ|) hentry i).trans ?_
    calc
      _ = |w - Y τ| + 21 * T ^ 3 * δ := by ring
      _ ≤ κ := hw
  have hrat := rational_couplings_sub_reference_le f hT hτ hε hε₁ hY hκ hκhalf hX hQ hZ hwκ hS₂ hf
  obtain ⟨hν₀, hη₀⟩ := normalized_couplings_eq he hOrient hscale hS₀ hZ₀ hV hperp M₀
  change normalizedNu M₀ (k τ) (a τ) S = (rationalCouplings X Q Z w S f).1 at hν₀
  change normalizedEta M₀ (k τ) (a τ) S = (rationalCouplings X Q Z w S f).2 at hη₀
  have hK₀ : k τ ≠ 0 := by
    intro hk
    exact hZ₀ (by simp [Z, MovingWaveVector.Z, hk])
  have hA₀ : a τ ≠ 0 := by
    intro ha
    simp [MovingAmplitude.V, ha] at hV
  obtain ⟨hνE, hηE⟩ := normalized_couplings_strain_error hK₀ hA₀ hperp hS₀.le M₀ E
  have hM : M = M₀ + E := by simp only [M, M₀, MovingWaveVector.strain, add_zero]
  have hδE : 2 * S * ‖E‖ ≤ 2 * δ := by
    calc
      _ ≤ 2 * S * (δ / S) := mul_le_mul_of_nonneg_left hE (by positivity)
      _ = _ := by field_simp
  change |normalizedNu M (k τ) (a τ) S - referenceNu ε τ Y| ≤ _ ∧
    |normalizedEta M (k τ) (a τ) S - referenceEta ε τ Y| ≤ _
  rw [hM]
  have hν : |normalizedNu M₀ (k τ) (a τ) S - referenceNu ε τ Y| ≤ 256 * T ^ 8 * κ := by
    rw [hν₀]
    exact hrat.1
  have hη : |normalizedEta M₀ (k τ) (a τ) S - referenceEta ε τ Y| ≤ 256 * T ^ 8 * κ := by
    rw [hη₀]
    exact hrat.2
  exact ⟨(abs_sub_le _ (normalizedNu M₀ (k τ) (a τ) S) _).trans
      ((add_le_add (hνE.trans hδE) hν).trans_eq (add_comm _ _)),
    (abs_sub_le _ (normalizedEta M₀ (k τ) (a τ) S) _).trans
      ((add_le_add (hηE.trans hδE) hη).trans_eq (add_comm _ _))⟩


/-- A polynomial budget for the geometric and forcing inputs gives the
two coupling conclusions of Lemma 2.5 under the smallness in (2.5). -/
theorem coupling_conclusions_of_polynomial_budget {C ε T δ κ : ℝ} {p C₀ : ℕ}
    {Y e ν η : ℝ → ℝ} (hε : 0 < ε) (hT : 2 ≤ T) (hδ : 0 ≤ δ)
    (hC₀ : (16 : ℝ) ≤ C₀) (hp : p + 10 ≤ C₀) (hC : 8 * (256 * C + 2) ≤ C₀)
    (hsmallε : (C₀ : ℝ) * ε ≤ 1) (hsmallδ : (C₀ : ℝ) * T ^ C₀ * δ ≤ ε)
    (hform : Y = referenceY ε e) (he : MapsTo e (Ici 0) (Icc 0 (ε / 8)))
    (hκ : κ ≤ C * T ^ p * δ)
    (herr : ∀ t ∈ Icc 0 T, |ν t - referenceNu ε t Y| ≤ 256 * T ^ 8 * κ + 2 * δ ∧
      |η t - referenceEta ε t Y| ≤ 256 * T ^ 8 * κ + 2 * δ) :
    (∀ t ∈ Icc 0 T, ε / 2 ≤ ν t) ∧ (∀ t ∈ Icc 0 T, Real.sqrt 2 / ε ≤ t →
      |ν t - 1| ≤ ε ∧ |(η t / ν t) / s ε t - 1| ≤ 1 / 2) := by
  have hT₁ : 1 ≤ T := by linarith
  have hpow : 1 ≤ T ^ (p + 8) := one_le_pow₀ hT₁
  have hbudget : 256 * T ^ 8 * κ + 2 * δ ≤ (256 * C + 2) * T ^ (p + 8) * δ := by
    calc
      _ ≤ 256 * T ^ 8 * (C * T ^ p * δ) + 2 * (T ^ (p + 8) * δ) :=
        add_le_add (mul_le_mul_of_nonneg_left hκ (by positivity))
          (by nlinarith only [mul_le_mul_of_nonneg_right hpow hδ])
      _ = _ := by rw [pow_add]; ring
  exact ReferenceRiccati.actual_couplings_of_polynomial_error
    (C := 256 * C + 2) (p := p + 8) hε hT hδ hC₀ (by simpa only [Nat.add_assoc] using hp)
    hC hsmallε hsmallδ hform he (fun t ht => (herr t ht).1.trans hbudget)
    (fun t ht => (herr t ht).2.trans hbudget)


end

end TorusEuler.GrowingCoupling
