import Breakdown.FracCell.GivenModelMixClauses

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace GivenModel

namespace RowTurnInternal

open SteadyCert CellAnalysis

theorem turn_coords (φ : ℝ) (y : Space) :
    Reduction.turnBy φ y 0 = Real.cos φ * y 0 - Real.sin φ * y 1 ∧
    Reduction.turnBy φ y 1 = Real.sin φ * y 0 + Real.cos φ * y 1 ∧
    Reduction.turnBy φ y 2 = y 2 := by
  simp [Reduction.turnBy]

def turnLin (φ : ℝ) : Space →ₗ[ℝ] Space where
  toFun := Reduction.turnBy φ
  map_add' u v := by
    ext i
    fin_cases i <;> simp [Reduction.turnBy] <;> ring
  map_smul' t u := by
    ext i
    fin_cases i <;> simp [Reduction.turnBy] <;> ring

theorem turnLin_apply (φ : ℝ) (u : Space) : turnLin φ u = Reduction.turnBy φ u := rfl

theorem radius_turn (φ : ℝ) (y : Space) : cylRadius (Reduction.turnBy φ y) = cylRadius y := by
  unfold cylRadius
  obtain ⟨h0, h1, -⟩ := turn_coords φ y
  rw [h0, h1]
  congr 1
  have := Real.sin_sq_add_cos_sq φ
  linear_combination (y 0 ^ 2 + y 1 ^ 2) * this

theorem height_turn (φ : ℝ) (y : Space) : cylHeight (Reduction.turnBy φ y) = cylHeight y :=
  (turn_coords φ y).2.2

theorem sign_turn (φ : ℝ) (y : Space) (c : Fin 3) : vectorSign (Reduction.turnBy φ y) c = vectorSign y c := by
  unfold vectorSign
  rw [height_turn]

theorem solid_turn (K : CellBox) (φ : ℝ) (y : Space) : Reduction.turnBy φ y ∈ K.solid ↔ y ∈ K.solid := by
  unfold CellBox.solid
  simp only [Set.mem_ofPred_eq, radius_turn, height_turn]

theorem frame_turn (φ θ : ℝ) (n : ℤ) (w : Fin 3 → ℝ) :
    cartOfFrame (θ + φ + 2 * Real.pi * n) w = Reduction.turnBy φ (cartOfFrame θ w) := by
  have hc : Real.cos (θ + φ + 2 * Real.pi * n) = Real.cos (θ + φ) := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring, Real.cos_add_int_mul_two_pi]
  have hs : Real.sin (θ + φ + 2 * Real.pi * n) = Real.sin (θ + φ) := by
    rw [show 2 * Real.pi * (n : ℝ) = (n : ℝ) * (2 * Real.pi) by ring, Real.sin_add_int_mul_two_pi]
  ext i
  fin_cases i <;>
    simp [Reduction.turnBy, cartOfFrame, Fin.sum_univ_three, frameUnit, radialUnit, angularUnit, axialUnit, hc, hs,
      Real.cos_add, Real.sin_add] <;> ring

theorem angle_turn (φ : ℝ) (y : Space) (hy : cylRadius y ≠ 0) :
    ∃ n : ℤ, cylAngle (Reduction.turnBy φ y) = cylAngle y + φ + 2 * Real.pi * n := by
  obtain ⟨h0, h1, -⟩ := turn_coords φ y
  set x : ℂ := (y 0 : ℂ) + (y 1 : ℂ) * Complex.I with hx
  set u : ℂ := Complex.exp ((φ : ℂ) * Complex.I) with hu
  have hx0 : x ≠ 0 := by
    intro h0
    apply hy
    have h0r := congrArg Complex.re h0
    have h0i := congrArg Complex.im h0
    simp [hx] at h0r h0i
    unfold cylRadius
    rw [h0r, h0i]
    simp
  have hu0 : u ≠ 0 := Complex.exp_ne_zero _
  have hcu : u = ((Real.cos φ : ℝ) : ℂ) + ((Real.sin φ : ℝ) : ℂ) * Complex.I := by
    rw [hu, Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  have hxu : (Reduction.turnBy φ y 0 : ℂ) + (Reduction.turnBy φ y 1 : ℂ) * Complex.I = x * u := by
    rw [hcu, h0, h1]
    apply Complex.ext <;> simp [hx] <;> ring
  have hang : (Complex.arg (x * u) : Real.Angle) = ((Complex.arg x + φ : ℝ) : Real.Angle) := by
    rw [Complex.arg_mul_coe_angle hx0 hu0, Real.Angle.coe_add, hu, Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod]
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 hang
  refine ⟨k, ?_⟩
  unfold cylAngle
  rw [hxu]
  linarith

theorem mode_shift (P : ℂ) (κ θ φ : ℝ) (n j : ℤ) (hκ : κ = j) :
    (P * Complex.exp ((κ * (θ + φ + 2 * Real.pi * n) : ℝ) * Complex.I)).re =
      Real.cos (κ * φ) * (P * Complex.exp ((κ * θ : ℝ) * Complex.I)).re +
        Real.sin (κ * φ) * (Complex.I * P * Complex.exp ((κ * θ : ℝ) * Complex.I)).re := by
  have hsplit : ((κ * (θ + φ + 2 * Real.pi * n) : ℝ) : ℂ) * Complex.I =
      ((κ * θ : ℝ) : ℂ) * Complex.I + ((κ * φ : ℝ) : ℂ) * Complex.I + ((j * n : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    rw [hκ]
    push_cast
    ring
  rw [hsplit, Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    Complex.exp_mul_I (((κ * φ : ℝ) : ℂ)), ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  set E := Complex.exp (((κ * θ : ℝ) : ℂ) * Complex.I)
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring

theorem cart_lin (θ s t : ℝ) (w w' : Fin 3 → ℝ) :
    s • cartOfFrame θ w + t • cartOfFrame θ w' = cartOfFrame θ (fun c => s * w c + t * w' c) := by
  simp only [cartOfFrame, Finset.smul_sum, smul_smul, add_smul, Finset.sum_add_distrib]

theorem cart_smul (θ t : ℝ) (w : Fin 3 → ℝ) :
    t • cartOfFrame θ w = cartOfFrame θ (fun c => t * w c) := by
  simp only [cartOfFrame, Finset.smul_sum, smul_smul]

def quarterField {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (a : Fin N) (y : Space) : Space :=
  Set.indicator (M.box (R.cell a)).solid
    (fun z => cartOfFrame (cylAngle z) (fun c => vectorSign z c *
      (Complex.I * evalPoly (R.profile a c) (cylRadius z) |cylHeight z| *
        Complex.exp ((azimuth m (R.harmonic a : ℤ) * cylAngle z : ℝ) * Complex.I)).re)) y

theorem test_turn {M : CellMesh} {N : ℕ} (R : RowData M N) (m : ℕ) (b : Fin N) (φ : ℝ) (y : Space)
    (hy : cylRadius y ≠ 0) :
    R.testField m b (Reduction.turnBy φ y) = Reduction.turnBy φ
      (Real.cos (azimuth m (R.harmonic b : ℤ) * φ) • R.testField m b y +
        Real.sin (azimuth m (R.harmonic b : ℤ) * φ) • quarterField R m b y) := by
  obtain ⟨n, hn⟩ := angle_turn φ y hy
  unfold RowData.testField quarterField
  by_cases hs : y ∈ (M.box (R.cell b)).solid
  · rw [Set.indicator_of_mem ((solid_turn _ φ y).2 hs), Set.indicator_of_mem hs, Set.indicator_of_mem hs, hn,
      frame_turn φ (cylAngle y) n, cart_lin]
    congr 1
    congr 1
    funext c
    rw [sign_turn, radius_turn, height_turn,
      mode_shift _ _ _ _ n ((R.harmonic b : ℤ) * m) (by simp [azimuth])]
    ring
  · rw [Set.indicator_of_notMem (mt (solid_turn _ φ y).1 hs), Set.indicator_of_notMem hs,
      Set.indicator_of_notMem hs]
    ext i
    fin_cases i <;> simp [Reduction.turnBy]

theorem eval_I {d : ℕ} (P : CellPoly d) (r z : ℝ) :
    evalPoly (fun j l => Complex.I * P j l) r z = Complex.I * evalPoly P r z := by
  unfold evalPoly
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  ring

theorem quarter_eq {M : CellMesh} {N : ℕ} (R : RowData M N) {m : ℕ} {rowMax : ℝ} (hR : IsRowData R m rowMax)
    (b : Fin N) (hb : R.harmonic b ≠ 0) (y : Space) :
    quarterField R m b y = R.pairSign b • R.testField m (R.partner b) y := by
  unfold quarterField RowData.testField RowData.pairSign
  rw [hR.partner_cell b, hR.partner_harmonic b]
  by_cases hs : y ∈ (M.box (R.cell b)).solid
  · rw [Set.indicator_of_mem hs, Set.indicator_of_mem hs, cart_smul]
    congr 1
    funext c
    cases hpos : R.positive b
    · have hp : R.positive (R.partner b) = true := by rw [hR.partner_sign b hb, hpos]; rfl
      have hpb : R.harmonic (R.partner b) ≠ 0 := by rw [hR.partner_harmonic b]; exact hb
      have hprof : R.profile b c = fun j l => Complex.I * R.profile (R.partner b) c j l := by
        funext j l
        have := hR.partner_profile (R.partner b) hpb hp c j l
        rwa [hR.partner_invol b] at this
      rw [hprof, eval_I]
      simp only [Bool.false_eq_true, if_false]
      have hII : Complex.I * (Complex.I * evalPoly (R.profile (R.partner b) c) (cylRadius y) |cylHeight y|) =
          -evalPoly (R.profile (R.partner b) c) (cylRadius y) |cylHeight y| := by
        rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
      rw [hII, neg_mul, Complex.neg_re]
      ring
    · have hprof : R.profile (R.partner b) c = fun j l => Complex.I * R.profile b c j l := by
        funext j l
        exact hR.partner_profile b hb hpos c j l
      rw [hprof, eval_I]
      simp
  · rw [Set.indicator_of_notMem hs, Set.indicator_of_notMem hs, smul_zero]


theorem reindex {N : ℕ} (p : Fin N → Fin N) (hp : Function.Involutive p) (g : Fin N → ℝ) (T : Fin N → Space) :
    ∑ b, g b • T (p b) = ∑ b, g (p b) • T b := by
  rw [← Equiv.sum_comp (Function.Involutive.toPerm p hp) (fun b => g (p b) • T b)]
  simp [Function.Involutive.coe_toPerm, hp _]

theorem row_turn_core {M : CellMesh} {N : ℕ} (R : RowData M N) {m : ℕ} {rowMax : ℝ} (hR : IsRowData R m rowMax)
    (hsupp : ∀ a b, R.mix a b ≠ 0 → R.harmonic a = R.harmonic b)
    (hJ : ∀ a b, R.harmonic a ≠ 0 →
      R.mix a (R.partner b) * R.pairSign (R.partner b) = R.pairSign a * R.mix (R.partner a) b)
    (a : Fin N) (φ : ℝ) (y : Space) (hy : cylRadius y ≠ 0) :
    R.rowField m a (Reduction.turnBy φ y) = Reduction.turnBy φ
      (Real.cos ((R.turnMode m a : ℝ) * φ) • R.rowField m a y +
        Real.sin ((R.turnMode m a : ℝ) * φ) • R.rowField m (R.partner a) y) := by
  set κ := azimuth m (R.harmonic a : ℤ) with hκ
  have hb : ∀ b, R.mix a b • R.testField m b (Reduction.turnBy φ y) = R.mix a b • turnLin φ
      (Real.cos (κ * φ) • R.testField m b y + (Real.sin (κ * φ) * R.pairSign b) • R.testField m (R.partner b) y) := by
    intro b
    by_cases hab : R.mix a b = 0
    · simp [hab]
    have hh := hsupp a b hab
    rw [test_turn R m b φ y hy, turnLin_apply, ← hh, ← hκ]
    by_cases h0 : R.harmonic a = 0
    · have hk0 : κ = 0 := by simp [hκ, azimuth, h0]
      simp [hk0]
    · rw [quarter_eq R hR b (hh ▸ h0) y, smul_smul]
  unfold RowData.rowField
  rw [Finset.sum_congr rfl fun b _ => hb b, ← turnLin_apply]
  simp only [← map_smul, ← map_sum]
  congr 1
  by_cases h0 : R.harmonic a = 0
  · have hk0 : κ = 0 := by simp [hκ, azimuth, h0]
    have ht0 : (R.turnMode m a : ℝ) = 0 := by simp [RowData.turnMode, h0]
    simp [hk0, ht0]
  have hcos : Real.cos ((R.turnMode m a : ℝ) * φ) = Real.cos (κ * φ) := by
    cases hpos : R.positive a <;> simp [RowData.turnMode, hpos, hκ, azimuth] <;> ring_nf
  have hsin : Real.sin ((R.turnMode m a : ℝ) * φ) = R.pairSign a * Real.sin (κ * φ) := by
    cases hpos : R.positive a <;> simp [RowData.turnMode, RowData.pairSign, hpos, hκ, azimuth] <;> ring_nf
  simp only [smul_add, Finset.sum_add_distrib, smul_smul, Finset.smul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun b _ => ?_
    rw [hcos]
    ring_nf
  · refine (reindex R.partner hR.partner_invol (fun b => R.mix a b * (Real.sin (κ * φ) * R.pairSign b))
      (fun b => R.testField m b y)).trans ?_
    refine Finset.sum_congr rfl fun b _ => ?_
    congr 1
    rw [hsin]
    calc R.mix a (R.partner b) * (Real.sin (κ * φ) * R.pairSign (R.partner b))
        = Real.sin (κ * φ) * (R.mix a (R.partner b) * R.pairSign (R.partner b)) := by ring
      _ = Real.sin (κ * φ) * (R.pairSign a * R.mix (R.partner a) b) := by rw [hJ a b h0]
      _ = R.pairSign a * Real.sin (κ * φ) * R.mix (R.partner a) b := by ring

end RowTurnInternal

open SteadyCert CellAnalysis

theorem rowTurn_of {k N : ℕ} (c : FracCellData k N) (M : CellMesh) (R : RowData M N)
    (hM : IsCellMesh M) (hR : IsRowData R c.order c.rowMax) (hI : IsRowInstance c M R) :
    ∀ a (φ : ℝ) y, Reduction.horizontalNorm y ≠ 0 → c.row a (Reduction.turnBy φ y) =
      Reduction.turnBy φ (Real.cos ((R.turnMode c.order a : ℝ) * φ) • c.row a y +
        Real.sin ((R.turnMode c.order a : ℝ) * φ) • c.row (R.partner a) y) := by
  intro a φ y hy
  have hy' : cylRadius y ≠ 0 := hy
  obtain ⟨-, h2, h3⟩ := mix_clauses R c.order c.rowMax hR
  rw [hI.row_eq]
  exact RowTurnInternal.row_turn_core R hR (fun a b h => (h2 a b h).2) h3 a φ y hy'


end GivenModel

end CellCert

end Breakdown
