import Breakdown.FracCell.ReductionLossDefs
import Breakdown.FracCert.LinearSolveCore
import Breakdown.Cert.SupBoundRadial

open MeasureTheory Set

noncomputable section

namespace Breakdown

namespace CellCert

namespace Reduction

open SteadyCert

namespace KernelSectors

def planeAngle (y : Space) : ℝ := Complex.arg ⟨y 0, y 1⟩

def sectorPart (m : ℕ) (x : Space) (S : Set Space) (j : ℕ) : Set Space :=
  {y | y ∈ S ∧ 2 * Real.pi * j / m ≤ toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) ∧
    toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) < 2 * Real.pi * (j + 1) / m}


private theorem gapDist_le_aux (aLo : ℝ) (aHi : Option ℝ) (bLo : ℝ) (bHi : Option ℝ) (s t : ℝ) (h1 : aLo ≤ s)
    (h2 : ∀ h, aHi = some h → s ≤ h) (h3 : bLo ≤ t) (h4 : ∀ h, bHi = some h → t ≤ h) :
    0 ≤ gapDist aLo aHi bLo bHi ∧ gapDist aLo aHi bLo bHi ≤ |s - t| := by
  refine ⟨le_max_left _ _, ?_⟩
  have hA : ∀ h, bHi = some h → aLo - h ≤ |s - t| := fun h hh => le_abs.2 (Or.inl (by linarith [h4 h hh]))
  have hB : ∀ h, aHi = some h → bLo - h ≤ |s - t| := fun h hh => le_abs.2 (Or.inr (by linarith [h2 h hh]))
  unfold gapDist
  refine max_le (abs_nonneg _) (max_le ?_ ?_)
  · cases bHi with
    | none => exact abs_nonneg _
    | some h => exact hA h rfl
  · cases aHi with
    | none => exact abs_nonneg _
    | some h => exact hB h rfl

private theorem sq_le_of_gap_aux {g u : ℝ} (h0 : 0 ≤ g) (h : g ≤ |u|) : g ^ 2 ≤ u ^ 2 := by
  rw [← sq_abs u]
  exact pow_le_pow_left₀ h0 h 2

private theorem norm_sq_aux (v : Space) : ‖v‖ ^ 2 = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
  simp [Fin.sum_univ_three]

private theorem mirror_apply_aux (y : Space) : mirror y 0 = y 0 ∧ mirror y 1 = y 1 ∧ mirror y 2 = -y 2 := by
  simp [mirror]

private theorem planeAngle_measurable_aux : Measurable planeAngle := by
  have e : (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) = fun y => (y 0 : ℂ) + (y 1 : ℂ) * Complex.I := by
    funext y
    apply Complex.ext <;> simp
  have hc : Measurable (fun y : Space => (⟨y 0, y 1⟩ : ℂ)) := by
    rw [e]
    fun_prop
  exact Complex.measurable_arg.comp hc

theorem sectorPart_measurable (m : ℕ) (x : Space) (S : Set Space) (hS : MeasurableSet S) (j : ℕ) :
    MeasurableSet (sectorPart m x S j) := by
  have hF : Measurable (fun y => toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x)) := by
    have : (fun y => toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x)) =
        fun y => Int.fract ((planeAngle y - planeAngle x) / (2 * Real.pi)) * (2 * Real.pi) := by
      funext y
      exact toIcoMod_eq_fract_mul _ _
    rw [this]
    exact (((planeAngle_measurable_aux.sub_const _).div_const _).fract).mul_const _
  exact hS.inter ((measurableSet_le measurable_const hF).inter (measurableSet_lt hF measurable_const))

theorem sectorPart_cover (m : ℕ) (hm : 0 < m) (x : Space) (S : Set Space) :
    ∀ y ∈ S, ∃ j < m, y ∈ sectorPart m x S j := by
  intro y hy
  set t := toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) with ht
  have htm := toIcoMod_mem_Ico' Real.two_pi_pos (planeAngle y - planeAngle x)
  rw [← ht] at htm
  obtain ⟨t0, t1⟩ := htm
  have hp : 0 < 2 * Real.pi := Real.two_pi_pos
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set u := t * m / (2 * Real.pi) with hu
  have hu0 : 0 ≤ u := by positivity
  have hum : u < m := by
    rw [hu, div_lt_iff₀ hp]
    nlinarith
  refine ⟨⌊u⌋₊, ?_, hy, ?_, ?_⟩
  · exact (Nat.floor_lt hu0).2 hum
  · have h1 : (⌊u⌋₊ : ℝ) ≤ u := Nat.floor_le hu0
    rw [div_le_iff₀ hmr]
    rw [hu, le_div_iff₀ hp] at h1
    linarith
  · have h1 : u < (⌊u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one u
    rw [lt_div_iff₀ hmr]
    rw [hu, div_lt_iff₀ hp] at h1
    linarith


private theorem polar_aux (x : Space) : horizontalNorm x * Real.cos (planeAngle x) = x 0 ∧
    horizontalNorm x * Real.sin (planeAngle x) = x 1 := by
  have hn : ‖(⟨x 0, x 1⟩ : ℂ)‖ = horizontalNorm x := by
    rw [Complex.norm_eq_sqrt_sq_add_sq]
    rfl
  refine ⟨?_, ?_⟩
  · rw [← hn]
    exact Complex.norm_mul_cos_arg _
  · rw [← hn]
    exact Complex.norm_mul_sin_arg _

private theorem horizontal_polar_aux (x y : Space) :
    (x 0 - y 0) ^ 2 + (x 1 - y 1) ^ 2 = (horizontalNorm x - horizontalNorm y) ^ 2 +
      4 * horizontalNorm x * horizontalNorm y *
        Real.sin (toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) / 2) ^ 2 := by
  obtain ⟨hx0, hx1⟩ := polar_aux x
  obtain ⟨hy0, hy1⟩ := polar_aux y
  set t := toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) with ht
  have hd := toIcoMod_sub_self_eq_mul Real.two_pi_pos 0 (planeAngle y - planeAngle x)
  rw [← ht] at hd
  have hcos : Real.cos t = Real.cos (planeAngle y - planeAngle x) := by
    have : t = (planeAngle y - planeAngle x) + ((-toIcoDiv Real.two_pi_pos 0 (planeAngle y - planeAngle x) : ℤ) : ℝ) * (2 * Real.pi) := by
      push_cast
      linarith
    rw [this, Real.cos_add_int_mul_two_pi]
  have hhalf : Real.cos t = 1 - 2 * Real.sin (t / 2) ^ 2 := by
    have := Real.cos_sq_add_sin_sq (t / 2)
    have h2 : Real.cos t = Real.cos (2 * (t / 2)) := by ring_nf
    rw [h2, Real.cos_two_mul]
    linarith
  rw [Real.cos_sub] at hcos
  have px := Real.cos_sq_add_sin_sq (planeAngle x)
  have py := Real.cos_sq_add_sin_sq (planeAngle y)
  rw [← hx0, ← hx1, ← hy0, ← hy1]
  set p := horizontalNorm x
  set q := horizontalNorm y
  linear_combination (p ^ 2) * px + (q ^ 2) * py + (2 * p * q) * hcos - (2 * p * q) * hhalf

private theorem sin_sector_aux (m j : ℕ) (hm : Even m) (hj : j < m) (t : ℝ)
    (h1 : 2 * Real.pi * j / m ≤ t) (h2 : t < 2 * Real.pi * (j + 1) / m) :
    Real.sin (Real.pi * ((min j (m - 1 - j) : ℕ) : ℝ) / m) ^ 2 ≤ Real.sin (t / 2) ^ 2 := by
  obtain ⟨k, hk⟩ := hm
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 (by omega)
  have hpi := Real.pi_pos
  rcases le_total j (m - 1 - j) with hle | hle
  · rw [Nat.min_eq_left hle]
    have hjm : (2 * ((j : ℝ) + 1)) ≤ m := by
      have : 2 * (j + 1) ≤ m := by omega
      exact_mod_cast this
    have a1 : Real.pi * j / m ≤ t / 2 := by
      have : Real.pi * j / m = (2 * Real.pi * j / m) / 2 := by ring
      rw [this]
      linarith
    have a2 : t / 2 ≤ Real.pi / 2 := by
      have : 2 * Real.pi * (j + 1) / m ≤ Real.pi := by
        rw [div_le_iff₀ hmr]
        nlinarith
      linarith
    have a0 : 0 ≤ Real.pi * j / m := by positivity
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) a2 a1
    have hs0 : 0 ≤ Real.sin (Real.pi * j / m) :=
      Real.sin_nonneg_of_nonneg_of_le_pi a0 (by linarith)
    exact pow_le_pow_left₀ hs0 hs 2
  · rw [Nat.min_eq_right hle]
    set i := m - 1 - j with hi
    have hij : i + j + 1 = m := by omega
    have hijr : (i : ℝ) + j + 1 = m := by exact_mod_cast hij
    have him : (2 * ((i : ℝ) + 1)) ≤ m := by
      have : 2 * (i + 1) ≤ m := by omega
      exact_mod_cast this
    set u := Real.pi - t / 2 with hu
    have hsu : Real.sin (t / 2) = Real.sin u := by rw [hu, Real.sin_pi_sub]
    rw [hsu]
    have a1 : Real.pi * i / m ≤ u := by
      have e : Real.pi * i / m = Real.pi - Real.pi * (j + 1) / m := by
        field_simp
        linarith
      rw [e, hu]
      have : t / 2 ≤ Real.pi * (j + 1) / m := by
        have : Real.pi * (j + 1) / m = (2 * Real.pi * (j + 1) / m) / 2 := by ring
        rw [this]
        linarith
      linarith
    have a2 : u ≤ Real.pi / 2 := by
      have e : Real.pi * j / m = Real.pi - Real.pi * (i + 1) / m := by
        field_simp
        linarith
      have h3 : Real.pi * j / m ≤ t / 2 := by
        have : Real.pi * j / m = (2 * Real.pi * j / m) / 2 := by ring
        rw [this]
        linarith
      have h4 : Real.pi * (i + 1) / m ≤ Real.pi / 2 := by
        rw [div_le_iff₀ hmr]
        nlinarith
      rw [hu]
      linarith
    have a0 : 0 ≤ Real.pi * i / m := by positivity
    have hs := Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith) a2 a1
    have hs0 : 0 ≤ Real.sin (Real.pi * i / m) :=
      Real.sin_nonneg_of_nonneg_of_le_pi a0 (by
        have : Real.pi * i / m ≤ Real.pi / 2 := by
          rw [div_le_iff₀ hmr]
          nlinarith
        linarith)
    exact pow_le_pow_left₀ hs0 hs 2


private theorem plane_turn_aux (φ : ℝ) (y : Space) :
    (⟨turnBy φ y 0, turnBy φ y 1⟩ : ℂ) = Complex.exp (φ * Complex.I) * ⟨y 0, y 1⟩ := by
  rw [Complex.exp_mul_I]
  apply Complex.ext <;> simp [turnBy, Complex.cos_ofReal_re, Complex.sin_ofReal_re] <;> ring

private theorem angle_turn_aux (φ : ℝ) (y : Space) (hy : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    ∃ n : ℤ, planeAngle (turnBy φ y) = planeAngle y + φ + n * (2 * Real.pi) := by
  have h := Complex.arg_mul_coe_angle (Complex.exp_ne_zero ((φ : ℂ) * Complex.I)) hy
  rw [← plane_turn_aux, Complex.arg_exp_mul_I, Real.Angle.coe_toIocMod, ← Real.Angle.coe_add] at h
  obtain ⟨k, hk⟩ := Real.Angle.angle_eq_iff_two_pi_dvd_sub.1 h
  refine ⟨k, ?_⟩
  unfold planeAngle
  linarith

private theorem toIcoMod_shift_aux (p s : ℝ) (hp2 : p ≤ 2 * Real.pi) (hs0 : 0 ≤ s) (hs1 : s < 2 * Real.pi + p) :
    (s < 2 * Real.pi ∧ toIcoMod Real.two_pi_pos 0 s = s) ∨
      (2 * Real.pi ≤ s ∧ toIcoMod Real.two_pi_pos 0 s = s - 2 * Real.pi) := by
  have hp' := Real.two_pi_pos
  by_cases h : s < 2 * Real.pi
  · left
    refine ⟨h, (toIcoMod_eq_self Real.two_pi_pos).2 ⟨hs0, by linarith⟩⟩
  · right
    push Not at h
    refine ⟨h, ?_⟩
    have e : toIcoMod Real.two_pi_pos 0 s = toIcoMod Real.two_pi_pos 0 (s - 2 * Real.pi) := by
      have e' : s = (s - 2 * Real.pi) + 2 * Real.pi := by ring
      conv_lhs => rw [e']
      exact toIcoMod_add_right _ _ _
    rw [e]
    exact (toIcoMod_eq_self Real.two_pi_pos).2 ⟨by linarith, by linarith⟩


private theorem shifted_aux (φ : ℝ) (x y : Space) (hy : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    toIcoMod Real.two_pi_pos 0 (planeAngle (turnBy φ y) - planeAngle x) =
      toIcoMod Real.two_pi_pos 0 (toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) + φ) := by
  obtain ⟨n, hn⟩ := angle_turn_aux φ y hy
  have hd := toIcoMod_sub_self_eq_mul Real.two_pi_pos 0 (planeAngle y - planeAngle x)
  rw [toIcoMod_eq_toIcoMod]
  refine ⟨-toIcoDiv Real.two_pi_pos 0 (planeAngle y - planeAngle x) - n, ?_⟩
  rw [zsmul_eq_mul]
  push_cast
  rw [hn]
  linarith

private theorem mem_shift_aux (m : ℕ) (hm : 0 < m) (x : Space) (S : Set Space)
    (hS : ∀ (φ : ℝ) y, y ∈ S ↔ turnBy φ y ∈ S) (j : ℕ) (hj : j + 1 < m) (y : Space)
    (hy : (⟨y 0, y 1⟩ : ℂ) ≠ 0) :
    turnBy (2 * Real.pi / m) y ∈ sectorPart m x S (j + 1) ↔ y ∈ sectorPart m x S j := by
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hpi := Real.pi_pos
  have hp : 0 < 2 * Real.pi / m := by positivity
  have hp2 : 2 * Real.pi / m ≤ 2 * Real.pi := by
    rw [div_le_iff₀ hmr]
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith
  have hjr : ((j : ℝ) + 1) + 1 ≤ m := by exact_mod_cast hj
  have hjm : 2 * Real.pi * (((j : ℝ) + 1) + 1) / m ≤ 2 * Real.pi := by
    rw [div_le_iff₀ hmr]
    nlinarith
  set t := toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) with ht
  have htm := toIcoMod_mem_Ico' Real.two_pi_pos (planeAngle y - planeAngle x)
  rw [← ht] at htm
  obtain ⟨t0, t1⟩ := htm
  have hsh := shifted_aux (2 * Real.pi / m) x y hy
  rw [← ht] at hsh
  have e1 : 2 * Real.pi * ((j : ℝ) + 1) / m = 2 * Real.pi * j / m + 2 * Real.pi / m := by ring
  have e2 : 2 * Real.pi * (((j : ℝ) + 1) + 1) / m = 2 * Real.pi * ((j : ℝ) + 1) / m + 2 * Real.pi / m := by ring
  have hj0 : 0 ≤ 2 * Real.pi * j / m := by positivity
  unfold sectorPart
  simp only [Set.mem_ofPred_eq]
  rw [hsh, ← hS, Nat.cast_add, Nat.cast_one]
  rcases toIcoMod_shift_aux (2 * Real.pi / m) (t + 2 * Real.pi / m) hp2 (by linarith) (by linarith) with
    ⟨hlt, heq⟩ | ⟨hge, heq⟩
  · rw [heq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, by linarith, by linarith⟩
  · rw [heq]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exfalso
      have : 2 * Real.pi / m ≤ 2 * Real.pi * ((j : ℝ) + 1) / m := by
        rw [div_le_div_iff_of_pos_right hmr]
        nlinarith
      linarith
    · rintro ⟨h1, h2, h3⟩
      exfalso
      linarith

private theorem axis_null_aux : ∀ᵐ y ∂(volume : Measure Space), (⟨y 0, y 1⟩ : ℂ) ≠ 0 := by
  set s : Submodule ℝ Space := LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ)
  have hs : s ≠ ⊤ := by
    intro h
    have : EuclideanSpace.single (0 : Fin 3) (1 : ℝ) ∈ s := by rw [h]; exact Submodule.mem_top
    simp [s] at this
  have h0 := Measure.addHaar_submodule (volume : Measure Space) s hs
  rw [ae_iff]
  refine measure_mono_null (fun y hy => ?_) h0
  simp only [Set.mem_ofPred_eq, not_not] at hy
  have : y 0 = 0 := by
    have := congrArg Complex.re hy
    simpa using this
  simp [s, this]


private theorem solid_bounded_of_some (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (b : Fin D.pieceCount) (ρH zH : ℝ) (hρH : D.pieceRhoHi b = some ρH) (hzH : D.pieceZHi b = some zH) :
    Bornology.IsBounded (D.pieceSolid b) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨ρH + |D.pieceZLo b| + |zH|, fun y hy => ?_⟩
  obtain ⟨p1, p2, p3, p4⟩ := hD.piece_solid b y hy
  obtain ⟨q1, q2, q3, q4⟩ := hD.piece_box b
  have p2' := p2 ρH hρH
  have p4' := p4 zH hzH
  have q2' := q2 ρH hρH
  rw [Metric.mem_closedBall, dist_zero_right]
  have hρ0 : 0 ≤ horizontalNorm y := Real.sqrt_nonneg _
  have hρsq : horizontalNorm y ^ 2 = y 0 ^ 2 + y 1 ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg (y 0)) (sq_nonneg (y 1)))
  have hz : |y 2| ≤ |D.pieceZLo b| + |zH| := by
    rw [abs_le]
    constructor
    · nlinarith [abs_nonneg (D.pieceZLo b), abs_nonneg zH, le_abs_self (D.pieceZLo b)]
    · nlinarith [abs_nonneg (D.pieceZLo b), abs_nonneg zH, le_abs_self zH]
  have hR : 0 ≤ ρH + |D.pieceZLo b| + |zH| := by
    have := abs_nonneg (D.pieceZLo b)
    have := abs_nonneg zH
    linarith
  rw [← Real.sqrt_sq (norm_nonneg _), ← Real.sqrt_sq hR]
  apply Real.sqrt_le_sqrt
  rw [norm_sq_aux]
  have h2 : y 2 ^ 2 = |y 2| ^ 2 := (sq_abs _).symm
  nlinarith [abs_nonneg (y 2)]

private theorem solid_integrable_aux (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (b : Fin D.pieceCount) : IntegrableOn V (D.pieceSolid b) := hD.mass_integrable b

private theorem sector_disjoint_aux (m : ℕ) (hm : 0 < m) (x : Space) (S : Set Space) (i j : ℕ) (hij : i < j) :
    Disjoint (sectorPart m x S i) (sectorPart m x S j) := by
  rw [Set.disjoint_left]
  rintro y ⟨-, -, h1⟩ ⟨-, h2, -⟩
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  have hpi := Real.pi_pos
  have hijr : (i : ℝ) + 1 ≤ j := by exact_mod_cast hij
  have : 2 * Real.pi * ((i : ℝ) + 1) / m ≤ 2 * Real.pi * j / m := by
    rw [div_le_div_iff_of_pos_right hmr]
    nlinarith
  linarith

theorem sectorPart_mass (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (b : Fin D.pieceCount) (x : Space) (j : ℕ) (hj : j < m) :
    (∫ y in sectorPart m x (D.pieceSolid b) j, V y) ≤ D.pieceMass b / m := by
  have hm : 0 < m := by have := hD.order_even.2; omega
  have hmr : (0 : ℝ) < m := Nat.cast_pos.2 hm
  set S := D.pieceSolid b with hSdef
  set T : ℕ → Set Space := fun j => sectorPart m x S j with hT
  have hTm : ∀ j, MeasurableSet (T j) := fun j => sectorPart_measurable m x S (hD.solid_measurable b) j
  have hVi := solid_integrable_aux m V D hD b
  have hemb : MeasurableEmbedding (turnStep m) :=
    (LinearSolveCore.turnStepIsometry m).toHomeomorph.measurableEmbedding
  have hstep : ∀ k, k + 1 < m → (∫ y in T (k + 1), V y) = ∫ y in T k, V y := by
    intro k hk
    rw [← integral_indicator (hTm (k + 1)), ← integral_indicator (hTm k),
      ← (LinearSolveCore.turnStep_measurePreserving m).integral_comp hemb]
    refine integral_congr_ae ?_
    filter_upwards [axis_null_aux] with y hy
    have hmem := mem_shift_aux m hm x S (hD.solid_turn b) k hk y hy
    have hturn : turnStep m y = turnBy (2 * Real.pi / m) y := rfl
    simp only [hT]
    rw [hturn]
    by_cases hyk : y ∈ sectorPart m x S k
    · rw [Set.indicator_of_mem (hmem.2 hyk), Set.indicator_of_mem hyk, hD.turn_invariant]
    · rw [Set.indicator_of_notMem (fun h => hyk (hmem.1 h)), Set.indicator_of_notMem hyk]
  have hall : ∀ k, k < m → (∫ y in T k, V y) = ∫ y in T 0, V y := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro hk
      rw [hstep k hk, ih (by omega)]
  have hunion : S = ⋃ k ∈ Finset.range m, T k := by
    ext y
    simp only [Set.mem_iUnion, Finset.mem_range]
    constructor
    · intro hy
      obtain ⟨k, hk, hyk⟩ := sectorPart_cover m hm x S y hy
      exact ⟨k, hk, hyk⟩
    · rintro ⟨k, -, hyk⟩
      exact hyk.1
  have hsum : (∫ y in S, V y) = ∑ k ∈ Finset.range m, ∫ y in T k, V y := by
    conv_lhs => rw [hunion]
    refine integral_biUnion_finset _ (fun k _ => hTm k) ?_ (fun k _ => hVi.mono_set fun y hy => hy.1)
    intro i _ k _ hik
    rcases lt_or_gt_of_ne hik with h | h
    · exact sector_disjoint_aux m hm x S i k h
    · exact (sector_disjoint_aux m hm x S k i h).symm
  have hsum' : (∫ y in S, V y) = m * ∫ y in T 0, V y := by
    rw [hsum, Finset.sum_congr rfl fun k hk => hall k (Finset.mem_range.1 hk), Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  have hmass := hD.mass_le b
  rw [← hSdef, hsum'] at hmass
  show (∫ y in T j, V y) ≤ D.pieceMass b / m
  rw [hall j hj, le_div_iff₀ hmr]
  linarith

theorem sectorPart_dist (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) (j : ℕ) (hj : j < m) (y : Space) (hy : y ∈ sectorPart m x (D.pieceSolid b) j) :
    D.sectorDist m a b mirrored (min j (m - 1 - j)) ≤ ‖(if mirrored then mirror x else x) - y‖ := by
  obtain ⟨hyS, ht1, ht2⟩ := hy
  obtain ⟨p1, p2, p3, p4⟩ := hD.piece_solid b y hyS
  obtain ⟨q1, q2, q3, q4⟩ := hD.piece_box b
  obtain ⟨r1, r2⟩ := hD.box_lower a
  have hρ := gapDist_le_aux (D.boxRhoLo a) (D.boxRhoHi a) (D.pieceRhoLo b) (D.pieceRhoHi b)
    (horizontalNorm x) (horizontalNorm y) hρlo hρhi p1 p2
  have hρsq := sq_le_of_gap_aux hρ.1 hρ.2
  have hpol := horizontal_polar_aux x y
  have hsin := sin_sector_aux m j hD.order_even.1 hj _ ht1 ht2
  set st := Real.sin (toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) / 2) ^ 2
  set si := Real.sin (Real.pi * ((min j (m - 1 - j) : ℕ) : ℝ) / m) ^ 2
  have hsi0 : 0 ≤ si := sq_nonneg _
  have hρρ : D.boxRhoLo a * D.pieceRhoLo b ≤ horizontalNorm x * horizontalNorm y :=
    mul_le_mul hρlo p1 q1 (le_trans r1 hρlo)
  have hx0 : 0 ≤ horizontalNorm x := le_trans r1 hρlo
  have hsinterm : 4 * D.boxRhoLo a * D.pieceRhoLo b * si ≤ 4 * horizontalNorm x * horizontalNorm y * st := by
    have := mul_le_mul hρρ hsin hsi0 (mul_nonneg hx0 (le_trans q1 p1))
    nlinarith
  unfold CellSumData.sectorDist
  rw [← Real.sqrt_sq (norm_nonneg _), norm_sq_aux]
  apply Real.sqrt_le_sqrt
  cases mirrored with
  | false =>
    have hzg := gapDist_le_aux (D.boxZLo a) (D.boxZHi a) (D.pieceZLo b) (D.pieceZHi b) (x 2) (y 2)
      hzlo hzhi p3 p4
    have hzsq := sq_le_of_gap_aux hzg.1 hzg.2
    simp only [Bool.false_eq_true, if_false, PiLp.sub_apply]
    linarith
  | true =>
    obtain ⟨m0, m1, m2⟩ := mirror_apply_aux x
    simp only [if_true, PiLp.sub_apply, m0, m1, m2]
    have hzsq : (D.boxZLo a + D.pieceZLo b) ^ 2 ≤ (-x 2 - y 2) ^ 2 := by
      nlinarith
    linarith

end KernelSectors

private def shellCut (d R r : ℝ) : ℝ :=
  if 0 < r ∧ d ≤ r ∧ r ≤ R then 1 / (4 * Real.pi * r) - 1 / (4 * Real.pi * R) else 0

private theorem shellCut_nonneg (d R r : ℝ) : 0 ≤ shellCut d R r := by
  unfold shellCut
  split_ifs with h
  · obtain ⟨h0, -, h2⟩ := h
    have : 1 / (4 * Real.pi * R) ≤ 1 / (4 * Real.pi * r) := by
      apply one_div_le_one_div_of_le (by positivity)
      have := Real.pi_pos
      nlinarith
    linarith
  · exact le_rfl

private theorem shellCut_radial_eqOn (d R : ℝ) :
    EqOn (fun y : ℝ => y ^ (Module.finrank ℝ Space - 1) • shellCut d R y)
      ((Icc d R).indicator (fun y => y / (4 * Real.pi) - y ^ 2 / (4 * Real.pi * R))) (Ioi 0) := by
  intro y hy
  have hy : 0 < y := hy
  simp only [finrank_euclideanSpace, Fintype.card_fin, smul_eq_mul, shellCut]
  by_cases h : d ≤ y ∧ y ≤ R
  · rw [if_pos ⟨hy, h⟩, indicator_of_mem (show y ∈ Icc d R from h)]
    have := Real.pi_pos
    field_simp
  · rw [if_neg (fun h' => h h'.2), indicator_of_notMem (show y ∉ Icc d R from h)]
    ring

private theorem shellCut_Ioi (d R : ℝ) (hd : 0 ≤ d) (hdR : d ≤ R) :
    (∫ y in Ioi (0 : ℝ), (Icc d R).indicator (fun y => y / (4 * Real.pi) - y ^ 2 / (4 * Real.pi * R)) y) =
      ∫ y in d..R, (y / (4 * Real.pi) - y ^ 2 / (4 * Real.pi * R)) := by
  rw [setIntegral_indicator measurableSet_Icc, intervalIntegral.integral_of_le hdR]
  rcases hd.lt_or_eq with hd | hd
  · have e : Ioi (0 : ℝ) ∩ Icc d R = Icc d R := by
      ext y
      simp only [mem_inter_iff, mem_Ioi, mem_Icc]
      constructor
      · exact fun h => h.2
      · exact fun h => ⟨by linarith [h.1], h⟩
    rw [e, integral_Icc_eq_integral_Ioc]
  · subst hd
    have e : Ioi (0 : ℝ) ∩ Icc 0 R = Ioc 0 R := by
      ext y
      simp only [mem_inter_iff, mem_Ioi, mem_Icc, mem_Ioc]
      constructor
      · exact fun h => ⟨h.1, h.2.2⟩
      · exact fun h => ⟨h.1, le_of_lt h.1, h.2⟩
    rw [e]

private theorem shellCut_interval (d R : ℝ) (hR : 0 < R) :
    (∫ y in d..R, (y / (4 * Real.pi) - y ^ 2 / (4 * Real.pi * R))) =
      ((R ^ 2 - d ^ 2) / 2 - (R ^ 3 - d ^ 3) / (3 * R)) / (4 * Real.pi) := by
  rw [intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
    (Continuous.intervalIntegrable (by fun_prop) _ _), intervalIntegral.integral_div,
    intervalIntegral.integral_div, integral_id, integral_pow]
  have := Real.pi_pos
  field_simp
  ring

private theorem shellCut_integrable (d R : ℝ) (x : Space) :
    Integrable (fun y : Space => shellCut d R ‖x - y‖) := by
  have h : Integrable (fun y : Space => shellCut d R ‖y‖) := by
    refine (integrable_fun_norm_addHaar (volume : Measure Space) (f := shellCut d R)).2 ?_
    refine (integrableOn_congr_fun (shellCut_radial_eqOn d R) measurableSet_Ioi).2 ?_
    refine Integrable.integrableOn ?_
    rw [integrable_indicator_iff measurableSet_Icc]
    exact (by fun_prop : Continuous (fun y : ℝ => y / (4 * Real.pi) - y ^ 2 / (4 * Real.pi * R))).integrableOn_Icc
  exact h.comp_sub_left x

private theorem shellCut_integral (d R : ℝ) (hd : 0 ≤ d) (hdR : d ≤ R) (hR : 0 < R) (x : Space) :
    (∫ y : Space, shellCut d R ‖x - y‖) = (R ^ 2 - d ^ 2) / 2 - (R ^ 3 - d ^ 3) / (3 * R) := by
  rw [integral_sub_left_eq_self (fun y : Space => shellCut d R ‖y‖) volume x,
    integral_fun_norm_addHaar (volume : Measure Space) (shellCut d R),
    setIntegral_congr_fun measurableSet_Ioi (shellCut_radial_eqOn d R), shellCut_Ioi d R hd hdR,
    shellCut_interval d R hR, Internal.SupBoundRadial.volume_real_ball_one]
  simp only [finrank_euclideanSpace, Fintype.card_fin, nsmul_eq_mul, smul_eq_mul]
  have := Real.pi_pos
  field_simp
  ring


private theorem shell_pointwise (w M d R r : ℝ) (hw : 0 ≤ w) (hwM : w ≤ M) (hr : 0 ≤ r) (hdr : d ≤ r) (hR : 0 < R) :
    w / (4 * Real.pi * r) ≤ w / (4 * Real.pi * R) + M * shellCut d R r := by
  have hpi := Real.pi_pos
  have hM : 0 ≤ M := le_trans hw hwM
  have hc := mul_nonneg hM (shellCut_nonneg d R r)
  have hwR : 0 ≤ w / (4 * Real.pi * R) := by positivity
  rcases hr.lt_or_eq with hr | hr
  · by_cases hrR : r ≤ R
    · have e : shellCut d R r = 1 / (4 * Real.pi * r) - 1 / (4 * Real.pi * R) := by
        unfold shellCut
        rw [if_pos ⟨hr, hdr, hrR⟩]
      rw [e]
      have hdiff : 0 ≤ 1 / (4 * Real.pi * r) - 1 / (4 * Real.pi * R) := by
        have : 1 / (4 * Real.pi * R) ≤ 1 / (4 * Real.pi * r) := by
          apply one_div_le_one_div_of_le (by positivity)
          nlinarith
        linarith
      have h1 : w / (4 * Real.pi * r) = w / (4 * Real.pi * R) + w * (1 / (4 * Real.pi * r) - 1 / (4 * Real.pi * R)) := by
        field_simp
        ring
      rw [h1]
      have := mul_le_mul_of_nonneg_right hwM hdiff
      linarith
    · push Not at hrR
      have : w / (4 * Real.pi * r) ≤ w / (4 * Real.pi * R) := by
        apply div_le_div_of_nonneg_left hw (by positivity)
        nlinarith
      linarith
  · rw [← hr]
    simp only [mul_zero, div_zero]
    have := mul_nonneg hM (shellCut_nonneg d R 0)
    linarith

theorem shellKernel_le (W : Space → ℝ) (S : Set Space) (x : Space) (μ M d : ℝ)
    (hS : MeasurableSet S) (hW : Measurable W) (h0 : ∀ y, 0 ≤ W y) (hM0 : 0 ≤ M) (hM : ∀ y ∈ S, W y ≤ M)
    (hi : IntegrableOn W S) (hμ : (∫ y in S, W y) ≤ μ) (hd : 0 ≤ d) (hdist : ∀ y ∈ S, d ≤ ‖x - y‖) :
    IntegrableOn (fun y => W y / (4 * Real.pi * ‖x - y‖)) S ∧
      (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) ≤ kernelShell μ M d := by
  have hpi := Real.pi_pos
  have hKm : Measurable (fun y => W y / (4 * Real.pi * ‖x - y‖)) :=
    hW.div (measurable_const.mul (continuous_const.sub continuous_id).norm.measurable)
  have hK0 : ∀ y, 0 ≤ W y / (4 * Real.pi * ‖x - y‖) := fun y => by
    have := h0 y
    positivity
  have hdom : ∀ R, 0 < R → ∀ d', (∀ y ∈ S, d' ≤ ‖x - y‖) →
      IntegrableOn (fun y => W y / (4 * Real.pi * R) + M * shellCut d' R ‖x - y‖) S ∧
      ∀ y ∈ S, W y / (4 * Real.pi * ‖x - y‖) ≤ W y / (4 * Real.pi * R) + M * shellCut d' R ‖x - y‖ := by
    intro R hR d' hd'
    refine ⟨(hi.div_const _).add ((shellCut_integrable d' R x).const_mul M).integrableOn, fun y hy => ?_⟩
    exact shell_pointwise (W y) M d' R _ (h0 y) (hM y hy) (norm_nonneg _) (hd' y hy) hR
  have hKi : IntegrableOn (fun y => W y / (4 * Real.pi * ‖x - y‖)) S := by
    obtain ⟨hI, hle⟩ := hdom 1 one_pos 0 (fun y _ => norm_nonneg _)
    refine hI.mono' hKm.aestronglyMeasurable ((ae_restrict_iff' hS).2 (ae_of_all _ fun y hy => ?_))
    rw [Real.norm_eq_abs, abs_of_nonneg (hK0 y)]
    exact hle y hy
  refine ⟨hKi, ?_⟩
  set μ0 := ∫ y in S, W y with hμ0
  have hμ00 : 0 ≤ μ0 := setIntegral_nonneg hS fun y _ => h0 y
  have hbath : ∀ d', 0 ≤ d' → (∀ y ∈ S, d' ≤ ‖x - y‖) →
      (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) ≤
        (M / 2) * ((d' ^ 3 + 3 * μ / (4 * Real.pi * M)) ^ ((2 : ℝ) / 3) - d' ^ 2) := by
    intro d' hd' hd'S
    set a := d' ^ 3 + 3 * μ / (4 * Real.pi * M) with ha
    have ha0 : d' ^ 3 ≤ a := by
      have : 0 ≤ 3 * μ / (4 * Real.pi * M) := by
        have : 0 ≤ μ := le_trans hμ00 hμ
        positivity
      linarith
    have hd3 : 0 ≤ d' ^ 3 := by positivity
    have hRHS : 0 ≤ (M / 2) * (a ^ ((2 : ℝ) / 3) - d' ^ 2) := by
      have h2 : d' ^ 2 = (d' ^ 3) ^ ((2 : ℝ) / 3) := by
        rw [← Real.rpow_natCast d' 3, ← Real.rpow_mul hd',
          show ((3 : ℕ) : ℝ) * (2 / 3) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
      have : (d' ^ 3) ^ ((2 : ℝ) / 3) ≤ a ^ ((2 : ℝ) / 3) := Real.rpow_le_rpow hd3 ha0 (by norm_num)
      have : 0 ≤ M / 2 := by linarith
      nlinarith
    rcases hM0.lt_or_eq with hMp | hMz
    · rcases hμ00.lt_or_eq with hμp | hμz
      · have hμpos : 0 < μ := lt_of_lt_of_le hμp hμ
        have hagt : d' ^ 3 < a := by
          have : 0 < 3 * μ / (4 * Real.pi * M) := by positivity
          linarith
        have ha0' : 0 < a := lt_of_le_of_lt hd3 hagt
        set R := a ^ ((1 : ℝ) / 3) with hR
        have hR0 : 0 < R := Real.rpow_pos_of_pos ha0' _
        have hR3 : R ^ 3 = a := by
          rw [hR, ← Real.rpow_natCast (a ^ ((1 : ℝ) / 3)) 3, ← Real.rpow_mul ha0'.le,
            show (1 : ℝ) / 3 * ((3 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
        have hR2 : R ^ 2 = a ^ ((2 : ℝ) / 3) := by
          rw [hR, ← Real.rpow_natCast (a ^ ((1 : ℝ) / 3)) 2, ← Real.rpow_mul ha0'.le,
            show (1 : ℝ) / 3 * ((2 : ℕ) : ℝ) = 2 / 3 by norm_num]
        have hdR : d' ≤ R := by
          refine le_of_pow_le_pow_left₀ (n := 3) (by norm_num) hR0.le ?_
          rw [hR3]
          exact ha0
        obtain ⟨hI, hle⟩ := hdom R hR0 d' hd'S
        have hcutS : (∫ y in S, shellCut d' R ‖x - y‖) ≤ ∫ y, shellCut d' R ‖x - y‖ :=
          setIntegral_le_integral (shellCut_integrable d' R x) (ae_of_all _ fun y => shellCut_nonneg d' R _)
        have hstep : (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) ≤
            μ0 / (4 * Real.pi * R) + M * ∫ y in S, shellCut d' R ‖x - y‖ := by
          refine (setIntegral_mono_on hKi hI hS hle).trans (le_of_eq ?_)
          rw [integral_add (hi.div_const _) ((shellCut_integrable d' R x).const_mul M).integrableOn,
            integral_div, integral_const_mul]
        rw [shellCut_integral d' R hd' hdR hR0 x] at hcutS
        have hkey : M * ((R ^ 3 - d' ^ 3) / (3 * R)) = μ / (4 * Real.pi * R) := by
          rw [hR3, ha]
          field_simp
          ring
        have hμR : μ0 / (4 * Real.pi * R) ≤ μ / (4 * Real.pi * R) :=
          div_le_div_of_nonneg_right hμ (by positivity)
        rw [← hR2]
        have := mul_le_mul_of_nonneg_left hcutS hMp.le
        nlinarith
      · have hWz : ∀ᵐ y ∂(volume.restrict S), W y = 0 := by
          have := (integral_eq_zero_iff_of_nonneg (fun y => h0 y) hi).1 hμz.symm
          exact this
        have : (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) = 0 := by
          rw [← integral_zero Space ℝ]
          refine integral_congr_ae ?_
          filter_upwards [hWz] with y hy
          simp [hy]
        rw [this]
        exact hRHS
    · have : (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) = 0 := by
        rw [← integral_zero Space ℝ]
        refine setIntegral_congr_fun hS fun y hy => ?_
        have : W y = 0 := le_antisymm (hMz ▸ hM y hy) (h0 y)
        simp [this]
      rw [this]
      exact hRHS
  unfold kernelShell
  split_ifs with hdpos
  · refine le_min ?_ (hbath d hd hdist)
    have : (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) ≤ ∫ y in S, W y / (4 * Real.pi * d) := by
      refine setIntegral_mono_on hKi (hi.div_const _) hS fun y hy => ?_
      exact div_le_div_of_nonneg_left (h0 y) (by positivity)
        (mul_le_mul_of_nonneg_left (hdist y hy) (by positivity))
    rw [integral_div] at this
    exact this.trans (div_le_div_of_nonneg_right hμ (by positivity))
  · have hd0 : d = 0 := le_antisymm (not_lt.1 hdpos) hd
    have := hbath 0 le_rfl fun y _ => norm_nonneg _
    simpa using this


theorem shellKernel_le_ae (W : Space → ℝ) (S : Set Space) (x : Space) (μ M d : ℝ)
    (hS : MeasurableSet S) (hW : Measurable W) (h0 : ∀ y, 0 ≤ W y) (hM0 : 0 ≤ M)
    (hM : ∀ᵐ y ∂volume, y ∈ S → W y ≤ M)
    (hi : IntegrableOn W S) (hμ : (∫ y in S, W y) ≤ μ) (hd : 0 ≤ d) (hdist : ∀ y ∈ S, d ≤ ‖x - y‖) :
    IntegrableOn (fun y => W y / (4 * Real.pi * ‖x - y‖)) S ∧
      (∫ y in S, W y / (4 * Real.pi * ‖x - y‖)) ≤ kernelShell μ M d := by
  have hWe : (fun y => min (W y) M) =ᵐ[volume.restrict S] W :=
    (ae_restrict_iff' hS).2 (hM.mono fun y hy hyS => min_eq_left (hy hyS))
  have hKe : (fun y => min (W y) M / (4 * Real.pi * ‖x - y‖)) =ᵐ[volume.restrict S]
      fun y => W y / (4 * Real.pi * ‖x - y‖) :=
    hWe.mono fun y hy => by simp only at hy ⊢; rw [hy]
  have hi' : IntegrableOn (fun y => min (W y) M) S := hi.congr hWe.symm
  have hμ' : (∫ y in S, min (W y) M) ≤ μ := by rw [integral_congr_ae hWe]; exact hμ
  obtain ⟨k1, k2⟩ := shellKernel_le (fun y => min (W y) M) S x μ M d hS (hW.min measurable_const)
    (fun y => le_min (h0 y) hM0) hM0 (fun y _ => min_le_right _ _) hi' hμ' hd hdist
  exact ⟨k1.congr hKe, by rw [← integral_congr_ae hKe]; exact k2⟩

namespace KernelSectors

def signedTurn (x y : Space) : ℝ :=
  if toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) ≤ Real.pi then
    toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x)
  else toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) - 2 * Real.pi

def nearSheet (m : ℕ) (x : Space) (S : Set Space) (c l : ℝ) : Set Space :=
  {y | y ∈ sectorPart m x S 0 ∪ sectorPart m x S (m - 1) ∧ |c * signedTurn x y| ≤ l}

private theorem signedTurn_measurable (x : Space) : Measurable (signedTurn x) := by
  have hF : Measurable (fun y => toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x)) := by
    have : (fun y => toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x)) =
        fun y => Int.fract ((planeAngle y - planeAngle x) / (2 * Real.pi)) * (2 * Real.pi) := by
      funext y
      exact toIcoMod_eq_fract_mul _ _
    rw [this]
    exact (((planeAngle_measurable_aux.sub_const _).div_const _).fract).mul_const _
  exact Measurable.ite (measurableSet_le hF measurable_const) hF (hF.sub_const _)

private theorem signedTurn_props (m : ℕ) (hm : 4 ≤ m) (x : Space) (S : Set Space) (y : Space)
    (hy : y ∈ sectorPart m x S 0 ∪ sectorPart m x S (m - 1)) :
    |signedTurn x y| ≤ 2 * Real.pi / m ∧
      Real.sin (toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) / 2) ^ 2 =
        Real.sin (signedTurn x y / 2) ^ 2 := by
  have hmr : (0 : ℝ) < m := by positivity
  have hm4 : (4 : ℝ) ≤ m := by exact_mod_cast hm
  have hpi := Real.pi_pos
  set t := toIcoMod Real.two_pi_pos 0 (planeAngle y - planeAngle x) with ht
  have htm := toIcoMod_mem_Ico' Real.two_pi_pos (planeAngle y - planeAngle x)
  rw [← ht] at htm
  obtain ⟨t0, t1⟩ := htm
  have hq : 2 * Real.pi / m ≤ Real.pi / 2 := by
    rw [div_le_iff₀ hmr]
    nlinarith
  unfold signedTurn
  rw [← ht]
  rcases hy with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · rw [← ht] at h1 h2
    simp only [Nat.cast_zero, mul_zero, zero_div, zero_add, mul_one] at h1 h2
    have hle : t ≤ Real.pi := by linarith
    rw [if_pos hle]
    exact ⟨by rw [abs_of_nonneg t0]; linarith, rfl⟩
  · rw [← ht] at h1 h2
    have hcast : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [hcast] at h1 h2
    have e : 2 * Real.pi * ((m : ℝ) - 1) / m = 2 * Real.pi - 2 * Real.pi / m := by
      field_simp
    rw [e] at h1
    have hgt : ¬ t ≤ Real.pi := by
      intro h
      linarith
    rw [if_neg hgt]
    refine ⟨?_, ?_⟩
    · rw [abs_le]
      constructor <;> linarith
    · have : (t - 2 * Real.pi) / 2 = t / 2 - Real.pi := by ring
      rw [this, Real.sin_sub_pi, neg_sq]

private theorem sin_chord_aux (u a : ℝ) (hu : 0 ≤ u) (hua : u ≤ a) (ha : 0 < a) (hapi : a ≤ Real.pi) :
    u / a * Real.sin a ≤ Real.sin u := by
  have hc := strictConcaveOn_sin_Icc.concaveOn
  have hb : (0 : ℝ) ≤ 1 - u / a := by
    rw [sub_nonneg, div_le_one ha]
    exact hua
  have h := hc.2 (show a ∈ Icc 0 Real.pi from ⟨ha.le, hapi⟩) (show (0 : ℝ) ∈ Icc 0 Real.pi from ⟨le_rfl, Real.pi_pos.le⟩)
    (div_nonneg hu ha.le) hb (by ring)
  simp only [smul_eq_mul, Real.sin_zero, mul_zero, add_zero] at h
  have e : u / a * a = u := by field_simp
  rw [e] at h
  exact h

private theorem far_dist_aux (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) (hrule : D.rule a b mirrored = 2) (y : Space)
    (hyS : y ∈ D.pieceSolid b)
    (hyU : y ∈ sectorPart m x (D.pieceSolid b) 0 ∪ sectorPart m x (D.pieceSolid b) (m - 1))
    (hfar : D.sectorLength a b mirrored < |D.sectorConst m a b * signedTurn x y|) :
    Real.sqrt (D.sectorDist m a b mirrored 0 ^ 2 + D.sectorLength a b mirrored ^ 2) ≤
      ‖(if mirrored then mirror x else x) - y‖ := by
  obtain ⟨hl, hc, -⟩ := hD.near_valid a b mirrored hrule
  have hm4 := hD.order_even.2
  have hmr : (0 : ℝ) < m := by positivity
  have hm4r : (4 : ℝ) ≤ m := by exact_mod_cast hm4
  have hpi := Real.pi_pos
  obtain ⟨p1, p2, p3, p4⟩ := hD.piece_solid b y hyS
  obtain ⟨q1, q2, q3, q4⟩ := hD.piece_box b
  obtain ⟨r1, r2⟩ := hD.box_lower a
  obtain ⟨hδ, hsin⟩ := signedTurn_props m hm4 x (D.pieceSolid b) y hyU
  have hpol := horizontal_polar_aux x y
  rw [hsin] at hpol
  set δ := signedTurn x y with hδdef
  set l := D.sectorLength a b mirrored
  set c := D.sectorConst m a b with hcdef
  set A := Real.pi / m with hA
  have hA0 : 0 < A := by positivity
  have hApi : A ≤ Real.pi := by
    rw [hA, div_le_iff₀ hmr]
    nlinarith
  have hu : |δ| / 2 ≤ A := by
    rw [hA]
    have : 2 * Real.pi / m = 2 * (Real.pi / m) := by ring
    linarith
  have hchord := sin_chord_aux (|δ| / 2) A (by positivity) hu hA0 hApi
  have hsA : 0 ≤ Real.sin A := Real.sin_nonneg_of_nonneg_of_le_pi hA0.le hApi
  have hsinabs : Real.sin (δ / 2) ^ 2 = Real.sin (|δ| / 2) ^ 2 := by
    rcases le_total 0 δ with h | h
    · rw [abs_of_nonneg h]
    · rw [abs_of_nonpos h, neg_div, Real.sin_neg, neg_sq]
  have hkey1 : (Real.sin A / A) ^ 2 * δ ^ 2 ≤ 4 * Real.sin (δ / 2) ^ 2 := by
    rw [hsinabs]
    have h0 : 0 ≤ |δ| / 2 / A * Real.sin A := by positivity
    have h2 := pow_le_pow_left₀ h0 hchord 2
    have e : (Real.sin A / A) ^ 2 * δ ^ 2 = 4 * (|δ| / 2 / A * Real.sin A) ^ 2 := by
      rw [← sq_abs δ]
      field_simp
      ring
    rw [e]
    linarith
  have hρρ : D.boxRhoLo a * D.pieceRhoLo b ≤ horizontalNorm x * horizontalNorm y :=
    mul_le_mul hρlo p1 q1 (le_trans r1 hρlo)
  have hρρ0 : 0 ≤ D.boxRhoLo a * D.pieceRhoLo b := mul_nonneg r1 q1
  have hc2 : c ^ 2 = D.boxRhoLo a * D.pieceRhoLo b * (Real.sin A / A) ^ 2 := by
    rw [hcdef]
    unfold CellSumData.sectorConst
    rw [mul_div_assoc, mul_pow, Real.sq_sqrt hρρ0]
  have hcδ : (c * δ) ^ 2 ≤ 4 * horizontalNorm x * horizontalNorm y * Real.sin (δ / 2) ^ 2 := by
    rw [mul_pow, hc2]
    have hs0 : 0 ≤ Real.sin (δ / 2) ^ 2 := sq_nonneg _
    have h1 := mul_le_mul_of_nonneg_left hkey1 hρρ0
    have h2 := mul_le_mul_of_nonneg_right hρρ (by positivity : 0 ≤ 4 * Real.sin (δ / 2) ^ 2)
    nlinarith
  have hl2 : l ^ 2 ≤ (c * δ) ^ 2 := by
    rw [← sq_abs (c * δ)]
    exact pow_le_pow_left₀ hl.le hfar.le 2
  have hρ := gapDist_le_aux (D.boxRhoLo a) (D.boxRhoHi a) (D.pieceRhoLo b) (D.pieceRhoHi b)
    (horizontalNorm x) (horizontalNorm y) hρlo hρhi p1 p2
  have hρsq := sq_le_of_gap_aux hρ.1 hρ.2
  have hd0 : D.sectorDist m a b mirrored 0 ^ 2 =
      gapDist (D.boxRhoLo a) (D.boxRhoHi a) (D.pieceRhoLo b) (D.pieceRhoHi b) ^ 2 +
        (if mirrored then D.boxZLo a + D.pieceZLo b
          else gapDist (D.boxZLo a) (D.boxZHi a) (D.pieceZLo b) (D.pieceZHi b)) ^ 2 := by
    unfold CellSumData.sectorDist
    rw [Real.sq_sqrt (by positivity)]
    simp
  rw [hd0, ← Real.sqrt_sq (norm_nonneg _), norm_sq_aux]
  apply Real.sqrt_le_sqrt
  cases mirrored with
  | false =>
    have hzg := gapDist_le_aux (D.boxZLo a) (D.boxZHi a) (D.pieceZLo b) (D.pieceZHi b) (x 2) (y 2)
      hzlo hzhi p3 p4
    have hzsq := sq_le_of_gap_aux hzg.1 hzg.2
    simp only [Bool.false_eq_true, if_false, PiLp.sub_apply] at hzsq ⊢
    linarith
  | true =>
    obtain ⟨m0, m1, m2⟩ := mirror_apply_aux x
    simp only [if_true, PiLp.sub_apply, m0, m1, m2]
    have hzsq : (D.boxZLo a + D.pieceZLo b) ^ 2 ≤ (-x 2 - y 2) ^ 2 := by
      have e : (-x 2 - y 2) ^ 2 = (x 2 + y 2) ^ 2 := by ring
      rw [e]
      exact pow_le_pow_left₀ (add_nonneg r2 q3) (add_le_add hzlo p3) 2
    linarith

theorem twoSector_near_of_sheet (m : ℕ) (V : Space → ℝ) (D : CellSumData) (hD : IsCellSumData m V D)
    (a : Fin D.boxCount) (b : Fin D.pieceCount) (mirrored : Bool) (x : Space) (hz : 0 ≤ x 2)
    (hρlo : D.boxRhoLo a ≤ horizontalNorm x) (hρhi : ∀ h, D.boxRhoHi a = some h → horizontalNorm x ≤ h)
    (hzlo : D.boxZLo a ≤ x 2) (hzhi : ∀ h, D.boxZHi a = some h → x 2 ≤ h) (hrule : D.rule a b mirrored = 2)
    (hsheet : (∫ y in nearSheet m x (D.pieceSolid b) (D.sectorConst m a b) (D.sectorLength a b mirrored),
            1 / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖)) ≤
          (D.pieceRhoHi b).getD 0 * (sheetArea (D.sectorLength a b mirrored)
              (Real.sqrt (D.sectorDist m a b mirrored 0 ^ 2 +
                ((D.pieceRhoHi b).getD 0 - D.pieceRhoLo b) * ((D.pieceZHi b).getD 0 - D.pieceZLo b) / Real.pi)) -
            sheetArea (D.sectorLength a b mirrored) (D.sectorDist m a b mirrored 0)) /
            (2 * Real.pi * D.sectorConst m a b)) :
    (∫ y in sectorPart m x (D.pieceSolid b) 0 ∪ sectorPart m x (D.pieceSolid b) (m - 1),
      V y / (4 * Real.pi * ‖(if mirrored then mirror x else x) - y‖)) ≤ D.nearTerm m a b mirrored := by
  obtain ⟨hl, hc, hρs, hzs⟩ := hD.near_valid a b mirrored hrule
  obtain ⟨ρH, hρH⟩ := Option.isSome_iff_exists.1 hρs
  obtain ⟨zH, hzH⟩ := Option.isSome_iff_exists.1 hzs
  have hm4 := hD.order_even.2
  have hm : 0 < m := by omega
  have hmr : (0 : ℝ) < m := by positivity
  have hpi := Real.pi_pos
  set x' := (if mirrored then mirror x else x) with hx'
  set S := D.pieceSolid b with hSdef
  set U := sectorPart m x S 0 ∪ sectorPart m x S (m - 1) with hU
  set l := D.sectorLength a b mirrored with hldef
  set c := D.sectorConst m a b with hcdef
  set N := nearSheet m x S c l with hN
  have hUm : MeasurableSet U := (sectorPart_measurable m x S (hD.solid_measurable b) 0).union
    (sectorPart_measurable m x S (hD.solid_measurable b) (m - 1))
  have hUS : U ⊆ S := Set.union_subset (fun y hy => hy.1) (fun y hy => hy.1)
  have hNm : MeasurableSet N := by
    have : N = U ∩ {y | |c * signedTurn x y| ≤ l} := rfl
    rw [this]
    exact hUm.inter (measurableSet_le ((signedTurn_measurable x).const_mul c).abs measurable_const)
  have hNU : N ⊆ U := fun y hy => hy.1
  have hVi := solid_integrable_aux m V D hD b
  have hKS := (shellKernel_le_ae V S x' (D.pieceMass b) (D.pieceSup b) 0 (hD.solid_measurable b) hD.measurable
    hD.nonneg (hD.sup_nonneg b) (hD.sup_le b) hVi (hD.mass_le b) le_rfl fun y _ => norm_nonneg _).1
  have hKU := hKS.mono_set hUS
  have hfin : volume S < ⊤ := (solid_bounded_of_some m V D hD b ρH zH hρH hzH).measure_lt_top
  have hOneS : IntegrableOn (fun _ : Space => (1 : ℝ)) S := integrableOn_const hfin.ne
  have hkS := (shellKernel_le (fun _ => (1 : ℝ)) S x' (volume.real S) 1 0 (hD.solid_measurable b)
    measurable_const (fun _ => zero_le_one) zero_le_one (fun _ _ => le_rfl) hOneS
    (by simp) le_rfl fun y _ => norm_nonneg _).1
  have hkN : IntegrableOn (fun y => 1 / (4 * Real.pi * ‖x' - y‖)) N := hkS.mono_set (hNU.trans hUS)
  have hsplit := integral_inter_add_sdiff (μ := volume) (f := fun y => V y / (4 * Real.pi * ‖x' - y‖)) hNm hKU
  rw [Set.inter_eq_right.2 hNU] at hsplit
  have hnear : (∫ y in N, V y / (4 * Real.pi * ‖x' - y‖)) ≤
      D.pieceSup b * ∫ y in N, 1 / (4 * Real.pi * ‖x' - y‖) := by
    rw [← integral_const_mul]
    refine setIntegral_mono_ae_restrict (hKU.mono_set hNU) (hkN.const_mul _) ?_
    refine (ae_restrict_iff' hNm).2 ((hD.sup_le b).mono fun y hy hyN => ?_)
    simp only
    rw [mul_one_div]
    exact div_le_div_of_nonneg_right (hy (hUS (hNU hyN))) (by positivity)
  set s0 := Real.sqrt (D.sectorDist m a b mirrored 0 ^ 2 + l ^ 2) with hs0
  have hs0pos : 0 < s0 := Real.sqrt_pos.2 (by positivity)
  have hfar : (∫ y in U \ N, V y / (4 * Real.pi * ‖x' - y‖)) ≤ (2 * (D.pieceMass b / m)) / (4 * Real.pi * s0) := by
    have h1 : (∫ y in U \ N, V y / (4 * Real.pi * ‖x' - y‖)) ≤ ∫ y in U \ N, V y / (4 * Real.pi * s0) := by
      refine setIntegral_mono_on (hKU.mono_set Set.sdiff_subset) ((hVi.mono_set (Set.sdiff_subset.trans hUS)).div_const _)
        (hUm.diff hNm) fun y hy => ?_
      have hfarY : l < |c * signedTurn x y| := by
        by_contra h
        exact hy.2 ⟨hy.1, not_lt.1 h⟩
      have hdist := far_dist_aux m V D hD a b mirrored x hz hρlo hρhi hzlo hzhi hrule y (hUS hy.1) hy.1 hfarY
      exact div_le_div_of_nonneg_left (hD.nonneg y) (by positivity)
        (mul_le_mul_of_nonneg_left hdist (by positivity))
    have h2 : (∫ y in U \ N, V y) ≤ ∫ y in U, V y :=
      setIntegral_mono_set (hVi.mono_set hUS) (ae_of_all _ fun y => hD.nonneg y)
        (Set.sdiff_subset).eventuallyLE
    have h3 : (∫ y in U, V y) ≤ 2 * (D.pieceMass b / m) := by
      rw [hU, setIntegral_union (sector_disjoint_aux m hm x S 0 (m - 1) (by omega))
        (sectorPart_measurable m x S (hD.solid_measurable b) (m - 1))
        (hVi.mono_set fun y hy => hy.1) (hVi.mono_set fun y hy => hy.1)]
      have := sectorPart_mass m V D hD b x 0 hm
      have := sectorPart_mass m V D hD b x (m - 1) (by omega)
      linarith
    rw [integral_div] at h1
    exact h1.trans (div_le_div_of_nonneg_right (h2.trans h3) (by positivity))
  have hM0 := hD.sup_nonneg b
  have hfinal : D.nearTerm m a b mirrored = 2 * (D.pieceMass b / m) / (4 * Real.pi * s0) +
      D.pieceSup b * ((D.pieceRhoHi b).getD 0 * (sheetArea l
          (Real.sqrt (D.sectorDist m a b mirrored 0 ^ 2 +
            ((D.pieceRhoHi b).getD 0 - D.pieceRhoLo b) * ((D.pieceZHi b).getD 0 - D.pieceZLo b) / Real.pi)) -
        sheetArea l (D.sectorDist m a b mirrored 0)) / (2 * Real.pi * c)) := by
    unfold CellSumData.nearTerm
    simp only []
    ring
  rw [hfinal, ← hsplit]
  have := mul_le_mul_of_nonneg_left hsheet hM0
  linarith

end KernelSectors

end Reduction

end CellCert

end Breakdown
