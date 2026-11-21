import Breakdown.FracCell.SpectralBlocksOrth

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace Spectral

open SteadyCert

namespace Internal.ModeOrthSame

def rotLin (φ : ℝ) : Space →ₗ[ℝ] Space where
  toFun y := WithLp.toLp 2 ![Real.cos φ * y 0 - Real.sin φ * y 1, Real.sin φ * y 0 + Real.cos φ * y 1, y 2]
  map_add' y w := by
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' c y := by
    ext i
    fin_cases i <;> simp <;> ring

theorem rotLin_inner (φ : ℝ) (x y : Space) : inner ℝ (rotLin φ x) (rotLin φ y) = inner ℝ x y := by
  simp only [rotLin, LinearMap.coe_mk, AddHom.coe_mk, PiLp.inner_apply, Fin.sum_univ_three]
  simp
  linear_combination (y.ofLp 0 * x.ofLp 0 + y.ofLp 1 * x.ofLp 1) * Real.sin_sq_add_cos_sq φ

def rot (φ : ℝ) : Space ≃ₗᵢ[ℝ] Space :=
  ((rotLin φ).isometryOfInner (rotLin_inner φ)).toLinearIsometryEquiv rfl

theorem rot0 (φ : ℝ) (y : Space) : (rot φ y) 0 = Real.cos φ * y 0 - Real.sin φ * y 1 := rfl

theorem rot1 (φ : ℝ) (y : Space) : (rot φ y) 1 = Real.sin φ * y 0 + Real.cos φ * y 1 := rfl

theorem rot2 (φ : ℝ) (y : Space) : (rot φ y) 2 = y 2 := rfl

theorem radial_rot (φ : ℝ) (y : Space) : radialCoord (rot φ y) = radialCoord y := by
  simp only [radialCoord, rot0, rot1]
  congr 1
  linear_combination (y.ofLp 0 ^ 2 + y.ofLp 1 ^ 2) * Real.sin_sq_add_cos_sq φ

theorem mem_cellSolid_rot (g : CellBlock) (s : Fin 2) (φ : ℝ) (y : Space) :
    rot φ y ∈ cellSolid g s ↔ y ∈ cellSolid g s := by
  simp only [cellSolid, Set.mem_ofPred_eq, radial_rot, rot2]

theorem angle_rot (φ : ℝ) (y : Space) (hy : ¬ (y 0 = 0 ∧ y 1 = 0)) :
    ∃ k : ℤ, angleCoord (rot φ y) = angleCoord y + φ - k * (2 * Real.pi) := by
  have hz0 : (⟨y 0, y 1⟩ : ℂ) ≠ 0 := by
    intro h
    apply hy
    rw [Complex.ext_iff] at h
    exact ⟨h.1, h.2⟩
  have hr : 0 < ‖(⟨y 0, y 1⟩ : ℂ)‖ := norm_pos_iff.2 hz0
  obtain ⟨θ, hθ⟩ : ∃ θ, θ = angleCoord y := ⟨_, rfl⟩
  have hθ' : θ = Complex.arg ⟨y 0, y 1⟩ := hθ
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = toIocMod Real.two_pi_pos (-Real.pi) (θ + φ) := ⟨_, rfl⟩
  have hmem : ψ ∈ Set.Ioc (-Real.pi) Real.pi := by
    have := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) (θ + φ)
    rw [← hψ] at this
    exact ⟨this.1, by linarith [this.2]⟩
  have hk : ψ = θ + φ - (toIocDiv Real.two_pi_pos (-Real.pi) (θ + φ) : ℝ) * (2 * Real.pi) := by
    rw [hψ, toIocMod, zsmul_eq_mul]
  have hc : Real.cos ψ = Real.cos (θ + φ) := by
    rw [hk, sub_eq_add_neg, ← neg_mul, ← Int.cast_neg, Real.cos_add_int_mul_two_pi]
  have hs : Real.sin ψ = Real.sin (θ + φ) := by
    rw [hk, sub_eq_add_neg, ← neg_mul, ← Int.cast_neg, Real.sin_add_int_mul_two_pi]
  obtain ⟨r, hrdef⟩ : ∃ r, r = ‖(⟨y 0, y 1⟩ : ℂ)‖ := ⟨_, rfl⟩
  rw [← hrdef] at hr
  have h0 : y 0 = r * Real.cos θ := by
    rw [hrdef, hθ', Complex.cos_arg hz0]
    field_simp
  have h1 : y 1 = r * Real.sin θ := by
    rw [hrdef, hθ', Complex.sin_arg]
    field_simp
  refine ⟨toIocDiv Real.two_pi_pos (-Real.pi) (θ + φ), ?_⟩
  rw [← hθ, ← hk]
  have e : (⟨(rot φ y) 0, (rot φ y) 1⟩ : ℂ) =
      (r : ℂ) * (Complex.cos ψ + Complex.sin ψ * Complex.I) := by
    rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
    apply Complex.ext
    · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, rot0, hc, hs, Real.cos_add, Real.sin_add]
      rw [h0, h1]
      ring
    · simp only [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.add_im,
        Complex.mul_im, Complex.I_re, Complex.I_im, rot1, hc, hs, Real.cos_add, Real.sin_add]
      rw [h0, h1]
      ring
  show Complex.arg _ = ψ
  rw [e, Complex.arg_mul_cos_add_sin_mul_I hr hmem]

theorem trig_shift (t : Fin 2) (n : ℕ) (x : ℝ) (k : ℤ) :
    trigMode t (n * (x - k * (2 * Real.pi))) = trigMode t (n * x) := by
  have e : (n : ℝ) * (x - k * (2 * Real.pi)) = n * x + ((-(n * k) : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [e]
  simp only [trigMode]
  split_ifs
  · exact Real.cos_add_int_mul_two_pi _ _
  · exact Real.sin_add_int_mul_two_pi _ _

theorem trig_split (n n' : ℕ) (t t' : Fin 2) : ∃ A B : ℝ → ℝ, (∀ w, A (w + Real.pi) = -A w) ∧
    (∀ w, B (w + Real.pi) = -B w) ∧ ∀ θ, trigMode t (n * θ) * trigMode t' (n' * θ) =
      A (((n : ℝ) + n') * θ) + B (((n : ℝ) - n') * θ) := by
  fin_cases t <;> fin_cases t'
  · refine ⟨fun w => Real.cos w / 2, fun w => Real.cos w / 2, fun w => by simp only [Real.cos_add_pi]; ring,
      fun w => by simp only [Real.cos_add_pi]; ring, fun θ => ?_⟩
    simp only [trigMode]
    simp only [Fin.zero_eta, Fin.isValue, if_true]
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring
  · refine ⟨fun w => Real.sin w / 2, fun w => -(Real.sin w / 2), fun w => by simp only [Real.sin_add_pi]; ring,
      fun w => by simp only [Real.sin_add_pi]; ring, fun θ => ?_⟩
    simp only [trigMode]
    simp
    rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
    ring
  · refine ⟨fun w => Real.sin w / 2, fun w => Real.sin w / 2, fun w => by simp only [Real.sin_add_pi]; ring,
      fun w => by simp only [Real.sin_add_pi]; ring, fun θ => ?_⟩
    simp only [trigMode]
    simp
    rw [add_mul, sub_mul, Real.sin_add, Real.sin_sub]
    ring
  · refine ⟨fun w => -(Real.cos w / 2), fun w => Real.cos w / 2, fun w => by simp only [Real.cos_add_pi]; ring,
      fun w => by simp only [Real.cos_add_pi]; ring, fun θ => ?_⟩
    simp only [trigMode]
    simp
    rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
    ring

theorem four_zero (A B : ℝ → ℝ) (hA : ∀ w, A (w + Real.pi) = -A w) (hB : ∀ w, B (w + Real.pi) = -B w)
    (a b θ p q : ℝ) (hp : a * p = Real.pi) (hq : b * q = Real.pi) :
    (A (a * θ) + B (b * θ)) + (A (a * (θ + p)) + B (b * (θ + p))) + (A (a * (θ + q)) + B (b * (θ + q)))
      + (A (a * (θ + (p + q))) + B (b * (θ + (p + q)))) = 0 := by
  have e1 : a * (θ + p) = a * θ + Real.pi := by rw [mul_add, hp]
  have e2 : a * (θ + (p + q)) = a * (θ + q) + Real.pi := by rw [← hp]; ring
  have e3 : b * (θ + q) = b * θ + Real.pi := by rw [mul_add, hq]
  have e4 : b * (θ + (p + q)) = b * (θ + p) + Real.pi := by rw [← hq]; ring
  rw [e1, e2, e3, e4, hA, hA, hB, hB]
  ring

theorem axis_null : volume {y : Space | y 0 = 0 ∧ y 1 = 0} = 0 := by
  have hs : LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) ≠ ⊤ := by
    intro h
    have : unitVector 0 ∈ LinearMap.ker ((EuclideanSpace.proj (0 : Fin 3) : Space →L[ℝ] ℝ) : Space →ₗ[ℝ] ℝ) :=
      h ▸ Submodule.mem_top
    simp [unitVector] at this
  refine measure_mono_null (fun y hy => ?_) (Measure.addHaar_submodule volume _ hs)
  simp [hy.1]


theorem integral_eq_zero_of_modes {ι : Type*} [Fintype ι] (n n' : ℕ) (hne : n ≠ n') (h : Space → ℝ)
    (K : ι → Fin 2 → Fin 2 → Space → ℝ) (hK : ∀ i t t' φ y, K i t t' (rot φ y) = K i t t' y)
    (hh : ∀ w, h w = ∑ i, ∑ t, ∑ t',
      trigMode t (n * angleCoord w) * trigMode t' (n' * angleCoord w) * K i t t' w) :
    ∫ y, h y = 0 := by
  have ha : ((n : ℝ) + n') ≠ 0 := by
    have hpos : 0 < n + n' := by omega
    have : (0 : ℝ) < n + n' := by exact_mod_cast hpos
    exact this.ne'
  have hb : ((n : ℝ) - n') ≠ 0 := by
    rw [sub_ne_zero]
    exact_mod_cast hne
  obtain ⟨p, hpd⟩ : ∃ p, p = Real.pi / ((n : ℝ) + n') := ⟨_, rfl⟩
  obtain ⟨q, hqd⟩ : ∃ q, q = Real.pi / ((n : ℝ) - n') := ⟨_, rfl⟩
  have hp : ((n : ℝ) + n') * p = Real.pi := by rw [hpd]; field_simp
  have hq : ((n : ℝ) - n') * q = Real.pi := by rw [hqd]; field_simp
  have hpt : ∀ y : Space, ¬ (y 0 = 0 ∧ y 1 = 0) →
      h y + h (rot p y) + h (rot q y) + h (rot (p + q) y) = 0 := by
    intro y hy
    obtain ⟨k1, e1⟩ := angle_rot p y hy
    obtain ⟨k2, e2⟩ := angle_rot q y hy
    obtain ⟨k3, e3⟩ := angle_rot (p + q) y hy
    rw [hh, hh, hh, hh, e1, e2, e3]
    simp only [trig_shift, hK, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun t _ => Finset.sum_eq_zero fun t' _ => ?_
    obtain ⟨A, B, hA, hB, hAB⟩ := trig_split n n' t t'
    have z := four_zero A B hA hB _ _ (angleCoord y) _ _ hp hq
    rw [hAB, hAB, hAB, hAB]
    linear_combination (K i t t' y) * z
  by_cases hi : Integrable h
  · have hm : ∀ φ, ∫ y, h (rot φ y) = ∫ y, h y := fun φ =>
      (rot φ).measurePreserving.integral_comp (rot φ).toHomeomorph.measurableEmbedding h
    have hi' : ∀ φ, Integrable (fun y => h (rot φ y)) := fun φ =>
      ((rot φ).measurePreserving.integrable_comp_emb (rot φ).toHomeomorph.measurableEmbedding).2 hi
    have i1 : Integrable (fun y => h y + h (rot p y)) := hi.add (hi' p)
    have i2 : Integrable (fun y => h y + h (rot p y) + h (rot q y)) := i1.add (hi' q)
    have hz : ∫ y, (h y + h (rot p y) + h (rot q y) + h (rot (p + q) y)) = 0 := by
      refine integral_eq_zero_of_ae ?_
      filter_upwards [measure_eq_zero_iff_ae_notMem.1 axis_null] with y hy
      exact hpt y hy
    rw [integral_add i2 (hi' _), integral_add i1 (hi' _), integral_add hi (hi' _), hm, hm, hm] at hz
    linarith
  · exact integral_undef hi

theorem frame_inner (c c' : Fin 3) (w : Space) :
    inner ℝ (frameVector c w) (frameVector c' w) = if c = c' then 1 else 0 := by
  fin_cases c <;> fin_cases c' <;>
    simp only [frameVector, unitVector] <;> rw [PiLp.inner_apply] <;>
    simp [Fin.sum_univ_three, PiLp.single_apply] <;> ring

theorem field_expand {g : CellBlock} {F : Space → Space} (hF : ModeField g F) :
    ∃ κ : Fin 3 → Fin 2 → Space → ℝ, (∀ c t φ y, κ c t (rot φ y) = κ c t y) ∧
      ∀ w, F w = ∑ c, (∑ t, trigMode t (g.mode * angleCoord w) * κ c t w) • frameVector c w := by
  obtain ⟨f, -, hf⟩ := hF
  refine ⟨fun c t w => ∑ s, (cellSolid g s).indicator (fun w => f s c t (radialCoord w) (w 2)) w, ?_, ?_⟩
  · intro c t φ y
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : y ∈ cellSolid g s
    · rw [Set.indicator_of_mem ((mem_cellSolid_rot g s φ y).2 hs), Set.indicator_of_mem hs, radial_rot, rot2]
    · rw [Set.indicator_of_notMem (fun h => hs ((mem_cellSolid_rot g s φ y).1 h)), Set.indicator_of_notMem hs]
  · intro w
    rw [hf w]
    by_cases h0 : w ∈ cellSolid g 0 <;> by_cases h1 : w ∈ cellSolid g 1
    · simp only [Fin.sum_univ_two, Set.indicator_of_mem h0, Set.indicator_of_mem h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      module
    · simp only [Fin.sum_univ_two, Set.indicator_of_mem h0, Set.indicator_of_notMem h1, add_zero]
    · simp only [Fin.sum_univ_two, Set.indicator_of_notMem h0, Set.indicator_of_mem h1, zero_add]
    · simp [Fin.sum_univ_two, Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]

theorem inner_frame_sum (u v : Fin 3 → ℝ) (w : Space) :
    inner ℝ (∑ c, u c • frameVector c w) (∑ c, v c • frameVector c w) = ∑ c, u c * v c := by
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right, frame_inner]
  simp [mul_comm]

theorem field_orth (g g' : CellBlock) (hne : g.mode ≠ g'.mode) (F G : Space → Space)
    (hF : ModeField g F) (hG : ModeField g' G) : ∫ y, inner ℝ (F y) (G y) = 0 := by
  obtain ⟨κ, hκ, eF⟩ := field_expand hF
  obtain ⟨κ', hκ', eG⟩ := field_expand hG
  refine integral_eq_zero_of_modes g.mode g'.mode hne _ (fun c t t' w => κ c t w * κ' c t' w)
    (fun c t t' φ y => by simp only [hκ, hκ']) fun w => ?_
  rw [eF, eG, inner_frame_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
  ring

theorem grad_expand {g : CellBlock} {D : Space → (Space →L[ℝ] Space)} (hD : ModeGradient g D) :
    ∃ κ : Fin 3 × Fin 3 → Fin 2 → Space → ℝ, (∀ p t φ y, κ p t (rot φ y) = κ p t y) ∧
      ∀ w, D w = ∑ p : Fin 3 × Fin 3, (∑ t, trigMode t (g.mode * angleCoord w) * κ p t w) •
        (innerSL ℝ (frameVector p.2 w)).smulRight (frameVector p.1 w) := by
  obtain ⟨f, -, hf⟩ := hD
  refine ⟨fun p t w => ∑ s, (cellSolid g s).indicator (fun w => f s p.1 p.2 t (radialCoord w) (w 2)) w,
    ?_, ?_⟩
  · intro p t φ y
    refine Finset.sum_congr rfl fun s _ => ?_
    by_cases hs : y ∈ cellSolid g s
    · rw [Set.indicator_of_mem ((mem_cellSolid_rot g s φ y).2 hs), Set.indicator_of_mem hs, radial_rot, rot2]
    · rw [Set.indicator_of_notMem (fun h => hs ((mem_cellSolid_rot g s φ y).1 h)), Set.indicator_of_notMem hs]
  · intro w
    rw [hf w, Fintype.sum_prod_type]
    by_cases h0 : w ∈ cellSolid g 0 <;> by_cases h1 : w ∈ cellSolid g 1
    · simp only [Fin.sum_univ_two, Set.indicator_of_mem h0, Set.indicator_of_mem h1, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => ?_
      module
    · simp only [Fin.sum_univ_two, Set.indicator_of_mem h0, Set.indicator_of_notMem h1, add_zero]
    · simp only [Fin.sum_univ_two, Set.indicator_of_notMem h0, Set.indicator_of_mem h1, zero_add]
    · simp [Fin.sum_univ_two, Set.indicator_of_notMem h0, Set.indicator_of_notMem h1]

theorem coord_inner_sum (u v : Space) :
    ∑ i : Fin 3, inner ℝ u (unitVector i) * inner ℝ v (unitVector i) = inner ℝ u v := by
  simp [unitVector, PiLp.inner_apply, mul_comm]

theorem entryInner_basic (x y u v : Space) :
    entryInner ((innerSL ℝ x).smulRight u) ((innerSL ℝ y).smulRight v) = inner ℝ x y * inner ℝ u v := by
  simp only [entryInner, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, inner_smul_left,
    inner_smul_right, conj_trivial]
  rw [← coord_inner_sum x y, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

theorem entryInner_sum {ι : Type*} [Fintype ι] (a b : ι → ℝ) (X Y : ι → (Space →L[ℝ] Space)) :
    entryInner (∑ j, a j • X j) (∑ k, b k • Y k) = ∑ j, ∑ k, a j * b k * entryInner (X j) (Y k) := by
  simp only [entryInner, _root_.sum_apply, _root_.smul_apply, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, Finset.mul_sum, conj_trivial]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

theorem entryInner_frames (p p' : Fin 3 × Fin 3) (w : Space) :
    entryInner ((innerSL ℝ (frameVector p.2 w)).smulRight (frameVector p.1 w))
      ((innerSL ℝ (frameVector p'.2 w)).smulRight (frameVector p'.1 w)) = if p = p' then 1 else 0 := by
  rw [entryInner_basic, frame_inner, frame_inner]
  obtain ⟨c, d⟩ := p
  obtain ⟨c', d'⟩ := p'
  by_cases h1 : c = c' <;> by_cases h2 : d = d' <;> simp [h1, h2]

theorem grad_orth (g g' : CellBlock) (hne : g.mode ≠ g'.mode) (D D' : Space → (Space →L[ℝ] Space))
    (hD : ModeGradient g D) (hD' : ModeGradient g' D') : ∫ y, entryInner (D y) (D' y) = 0 := by
  obtain ⟨κ, hκ, eD⟩ := grad_expand hD
  obtain ⟨κ', hκ', eD'⟩ := grad_expand hD'
  refine integral_eq_zero_of_modes g.mode g'.mode hne _ (fun p t t' w => κ p t w * κ' p t' w)
    (fun p t t' φ y => by simp only [hκ, hκ']) fun w => ?_
  rw [eD, eD', entryInner_sum]
  simp only [entryInner_frames, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun t' _ => ?_
  ring

end Internal.ModeOrthSame

open Internal.ModeOrthSame in
theorem modeOrthSame_holds : ModeOrthSameStatement := by
  intro g g' _ _ _ _ hne
  exact ⟨fun F G hF hG _ _ => field_orth g g' hne F G hF hG,
    fun D D' hD hD' _ _ _ _ => grad_orth g g' hne D D' hD hD'⟩
