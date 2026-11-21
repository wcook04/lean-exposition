import Breakdown.FracCell.GivenModelModelFrame

open MeasureTheory

noncomputable section

namespace Breakdown.FracInternal.GivenModelModelModes

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert Breakdown.FracInternal.GivenModelModelFrame

def wave (κ : ℤ) (θ : ℝ) : ℂ := Complex.exp ((((κ : ℝ) * θ : ℝ) : ℂ) * Complex.I)

def TrigFree (ω : ℤ) (f : ℝ → ℂ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (c : ι → ℂ) (κ : ι → ℤ), (∀ i, κ i ≠ ω ∧ -κ i ≠ ω) ∧
    ∀ θ, f θ = ∑ i, c i * wave (κ i) θ

theorem tf_zero (ω : ℤ) : TrigFree ω 0 :=
  ⟨Empty, inferInstance, fun _ => 0, fun _ => 0, fun i => i.elim, fun θ => by simp⟩

theorem tf_add {ω : ℤ} {f g : ℝ → ℂ} (hf : TrigFree ω f) (hg : TrigFree ω g) : TrigFree ω (f + g) := by
  obtain ⟨ι, _, c, κ, hκ, hf⟩ := hf
  obtain ⟨ι', _, c', κ', hκ', hg⟩ := hg
  refine ⟨ι ⊕ ι', inferInstance, Sum.elim c c', Sum.elim κ κ', ?_, fun θ => ?_⟩
  · rintro (i | i)
    · exact hκ i
    · exact hκ' i
  · simp [Fintype.sum_sum_type, hf, hg]

theorem tf_mul {ω : ℤ} {f : ℝ → ℂ} (a : ℂ) (hf : TrigFree ω f) : TrigFree ω (fun θ => a * f θ) := by
  obtain ⟨ι, _, c, κ, hκ, hf⟩ := hf
  exact ⟨ι, inferInstance, fun i => a * c i, κ, hκ, fun θ => by simp [hf, Finset.mul_sum, mul_assoc]⟩

theorem wave_conj (κ : ℤ) (θ : ℝ) : (starRingEnd ℂ) (wave κ θ) = wave (-κ) θ := by
  unfold wave
  rw [← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

theorem tf_conj {ω : ℤ} {f : ℝ → ℂ} (hf : TrigFree ω f) : TrigFree ω (fun θ => (starRingEnd ℂ) (f θ)) := by
  obtain ⟨ι, _, c, κ, hκ, hf⟩ := hf
  refine ⟨ι, inferInstance, fun i => (starRingEnd ℂ) (c i), fun i => -κ i,
    fun i => ⟨(hκ i).2, by simpa using (hκ i).1⟩, fun θ => ?_⟩
  simp [hf, map_sum, wave_conj]

theorem tf_congr {ω : ℤ} {f g : ℝ → ℂ} (hf : TrigFree ω f) (h : ∀ θ, g θ = f θ) : TrigFree ω g := by
  obtain ⟨ι, _, c, κ, hκ, hf⟩ := hf
  exact ⟨ι, inferInstance, c, κ, hκ, fun θ => (h θ).trans (hf θ)⟩

theorem tf_re {ω : ℤ} {f : ℝ → ℂ} (hf : TrigFree ω f) : TrigFree ω (fun θ => (((f θ).re : ℝ) : ℂ)) := by
  refine tf_congr (tf_mul (1 / 2 : ℂ) (tf_add hf (tf_conj hf))) fun θ => ?_
  rw [Complex.re_eq_add_conj]
  simp only [Pi.add_apply]
  ring

theorem tf_sum {ω : ℤ} {α : Type*} (s : Finset α) (g : α → ℝ → ℂ) (h : ∀ K ∈ s, TrigFree ω (g K)) :
    TrigFree ω (fun θ => ∑ K ∈ s, g K θ) := by
  have := Finset.sum_induction g (TrigFree ω) (fun _ _ => tf_add) (tf_zero ω) h
  exact tf_congr this fun θ => by simp [Finset.sum_apply]

theorem tf_wave {ω κ : ℤ} (h1 : κ ≠ ω) (h2 : -κ ≠ ω) (a : ℂ) : TrigFree ω (fun θ => a * wave κ θ) :=
  ⟨Unit, inferInstance, fun _ => a, fun _ => κ, fun _ => ⟨h1, h2⟩, fun θ => by simp⟩

theorem wave_cont (κ : ℤ) : Continuous (wave κ) := by
  unfold wave
  fun_prop

theorem integral_wave (k : ℤ) (hk : k ≠ 0) : ∫ θ in (0 : ℝ)..(2 * Real.pi), wave k θ = 0 := by
  have hc : ((k : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
  have e : ∀ θ : ℝ, wave k θ = Complex.exp (((k : ℂ) * Complex.I) * θ) := fun θ => by
    unfold wave
    push_cast
    ring_nf
  simp_rw [e]
  rw [integral_exp_mul_complex hc]
  have h1 : Complex.exp ((k : ℂ) * Complex.I * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_int_mul_two_pi_mul_I k]
    congr 1
    push_cast
    ring
  rw [h1]
  simp

theorem tf_integral {ω : ℤ} {f : ℝ → ℂ} (hf : TrigFree ω f) (w : ℝ) (hw : w = (ω : ℝ)) :
    ∫ θ in (0 : ℝ)..(2 * Real.pi), Complex.exp (-(w * θ : ℝ) * Complex.I) * f θ = 0 := by
  obtain ⟨ι, _, c, κ, hκ, hf⟩ := hf
  have e : ∀ θ : ℝ, Complex.exp (-(w * θ : ℝ) * Complex.I) * f θ = ∑ i, c i * wave (κ i - ω) θ := by
    intro θ
    rw [hf, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    unfold wave
    rw [mul_left_comm, ← Complex.exp_add, hw]
    congr 2
    push_cast
    ring
  simp_rw [e]
  rw [intervalIntegral.integral_finsetSum (f := fun i θ => c i * wave (κ i - ω) θ) fun i _ =>
    ((continuous_const.mul (wave_cont _)).intervalIntegrable _ _)]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [intervalIntegral.integral_const_mul, integral_wave _ (sub_ne_zero.2 (hκ i).1), mul_zero]

end Breakdown.FracInternal.GivenModelModelModes

namespace Breakdown.FracInternal.GivenModelModelModes

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert Breakdown.FracInternal.GivenModelModelFrame

theorem pt0 (r θ z : ℝ) : cylPoint r θ z 0 = r * Real.cos θ := by simp [cylPoint]

theorem pt1 (r θ z : ℝ) : cylPoint r θ z 1 = r * Real.sin θ := by simp [cylPoint]

theorem pt_height (r θ z : ℝ) : cylHeight (cylPoint r θ z) = z := by simp [cylHeight, cylPoint]

theorem pt_radius (r θ z : ℝ) : cylRadius (cylPoint r θ z) = |r| := by
  unfold cylRadius
  rw [pt0, pt1, show (r * Real.cos θ) ^ 2 + (r * Real.sin θ) ^ 2 = r ^ 2 by
    have := Real.cos_sq_add_sin_sq θ
    linear_combination r ^ 2 * this]
  exact Real.sqrt_sq_eq_abs r

theorem angle_exp (r θ z : ℝ) (hr : r ≠ 0) :
    Complex.exp ((cylAngle (cylPoint r θ z) : ℂ) * Complex.I) =
      ((r / |r| : ℝ) : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
  unfold cylAngle
  set x : ℂ := ((cylPoint r θ z 0 : ℝ) : ℂ) + ((cylPoint r θ z 1 : ℝ) : ℂ) * Complex.I with hxdef
  have hx : x = (r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [hxdef, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, pt0, pt1]
    push_cast
    ring
  have hn : ‖x‖ = |r| := by
    rw [hx, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp_ofReal_mul_I, mul_one]
  have key := Complex.norm_mul_exp_arg_mul_I x
  rw [hn] at key
  have ha : ((|r| : ℝ) : ℂ) ≠ 0 := by exact_mod_cast abs_ne_zero.2 hr
  rw [Complex.ofReal_div]
  field_simp
  have hc : Complex.exp ((θ : ℂ) * Complex.I) = Complex.exp (Complex.I * (θ : ℂ)) := by rw [mul_comm]
  linear_combination key + hx + (r : ℂ) * hc

theorem angle_cos (r θ z : ℝ) (hr : r ≠ 0) :
    Real.cos (cylAngle (cylPoint r θ z)) = r / |r| * Real.cos θ := by
  have h := congrArg Complex.re (angle_exp r θ z hr)
  rw [Complex.exp_ofReal_mul_I_re, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re] at h
  exact h

theorem angle_sin (r θ z : ℝ) (hr : r ≠ 0) :
    Real.sin (cylAngle (cylPoint r θ z)) = r / |r| * Real.sin θ := by
  have h := congrArg Complex.im (angle_exp r θ z hr)
  rw [Complex.exp_ofReal_mul_I_im, Complex.im_ofReal_mul, Complex.exp_ofReal_mul_I_im] at h
  exact h

def frameScale (ε : ℝ) (a : Fin 3) : ℝ := if a = 2 then 1 else ε

theorem frame_angle (r θ z : ℝ) (hr : r ≠ 0) (a : Fin 3) :
    frameUnit (cylAngle (cylPoint r θ z)) a = frameScale (r / |r|) a • frameUnit θ a := by
  have hc := angle_cos r θ z hr
  have hs := angle_sin r θ z hr
  fin_cases a <;> ext i <;> fin_cases i <;>
    simp [frameUnit, radialUnit, angularUnit, axialUnit, frameScale, hc, hs]

theorem frameUnit_inner (θ : ℝ) (a b : Fin 3) :
    inner ℝ (frameUnit θ a) (frameUnit θ b) = if a = b then 1 else 0 := by
  rw [← frameUnit_coord θ a b]
  simp [PiLp.inner_apply, mul_comm]

theorem frameMat_eq (θ : ℝ) (A : Space →L[ℝ] Space) (a b : Fin 3) :
    frameMat θ A a b = inner ℝ (A (frameUnit θ b)) (frameUnit θ a) := by
  fin_cases a <;> fin_cases b <;> rfl

theorem frameMat_cartOp (θ φ : ℝ) (s : Fin 3 → ℝ) (hs : ∀ a, frameUnit φ a = s a • frameUnit θ a)
    (M : Fin 3 → Fin 3 → ℝ) (a b : Fin 3) : frameMat θ (cartOpOfFrame φ M) a b = s a * s b * M a b := by
  rw [frameMat_eq, cartOp_apply]
  simp only [hs, sum_inner, real_inner_smul_left, frameUnit_inner, mul_ite, mul_one, mul_zero]
  simp [Finset.sum_ite_eq']
  ring

theorem azimuth_exp (m : ℕ) (β : ℕ) (r θ z : ℝ) (hr : r ≠ 0) :
    Complex.exp ((azimuth m (β : ℤ) * cylAngle (cylPoint r θ z) : ℝ) * Complex.I) =
      (((r / |r|) ^ (β * m) : ℝ) : ℂ) * wave ((β * m : ℕ) : ℤ) θ := by
  have e1 : ((azimuth m (β : ℤ) * cylAngle (cylPoint r θ z) : ℝ) : ℂ) * Complex.I =
      ((β * m : ℕ) : ℂ) * ((cylAngle (cylPoint r θ z) : ℂ) * Complex.I) := by
    simp only [azimuth]
    push_cast
    ring
  have e2 : wave ((β * m : ℕ) : ℤ) θ = Complex.exp ((θ : ℂ) * Complex.I) ^ (β * m) := by
    unfold wave
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [e1, Complex.exp_nat_mul, angle_exp r θ z hr, mul_pow, e2]
  push_cast
  ring

end Breakdown.FracInternal.GivenModelModelModes

namespace Breakdown.FracInternal.GivenModelModelModes

open CellCert CellCert.GivenModel CellCert.CellAnalysis SteadyCert Breakdown.FracInternal.GivenModelModelFrame

theorem freq_ne (m : ℕ) (hm : 0 < m) (β : ℕ) (n : ℤ) (h1 : (β : ℤ) ≠ n) (h2 : -(β : ℤ) ≠ n) :
    (((β * m : ℕ) : ℤ) ≠ n * m) ∧ (-((β * m : ℕ) : ℤ) ≠ n * m) := by
  have hm' : (m : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
  constructor
  · intro h
    push_cast at h
    exact h1 (mul_right_cancel₀ hm' h)
  · intro h
    push_cast at h
    exact h2 (mul_right_cancel₀ hm' (by rw [← h]; ring))

theorem harmonic_tf (m : ℕ) (hm : 0 < m) {d J : ℕ} (P : Fin (J + 1) → CellPoly d) (r z : ℝ) (hr : r ≠ 0) (n : ℤ)
    (hβ : ∀ β : Fin (J + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n) :
    TrigFree (n * m) (fun θ => ((harmonicValue m P (cylPoint r θ z) : ℝ) : ℂ)) := by
  refine tf_congr (tf_re (tf_sum Finset.univ (fun (β : Fin (J + 1)) (θ : ℝ) =>
    ((((if (β : ℕ) = 0 then (1 : ℝ) else 2) : ℝ) : ℂ) * evalPoly (P β) |r| |z| *
      (((r / |r|) ^ ((β : ℕ) * m) : ℝ) : ℂ)) * wave (((β : ℕ) * m : ℕ) : ℤ) θ)
    fun β _ => tf_wave (freq_ne m hm β n (hβ β).1 (hβ β).2).1 (freq_ne m hm β n (hβ β).1 (hβ β).2).2 _)) fun θ => ?_
  rw [harmonicValue_eq, harmonicAt, pt_radius, pt_height]
  refine congrArg (fun w : ℂ => ((w.re : ℝ) : ℂ)) (Finset.sum_congr rfl fun β _ => ?_)
  rw [azimuth_exp m (β : ℕ) r θ z hr]
  ring

theorem tensor_tf (m : ℕ) (hm : 0 < m) {d J : ℕ} (P : Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (r z : ℝ)
    (hr : r ≠ 0) (n : ℤ) (hβ : ∀ β : Fin (J + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n) (a b : Fin 3) :
    TrigFree (n * m) (fun θ => ((frameMat θ (tensorOf m P (cylPoint r θ z)) a b : ℝ) : ℂ)) := by
  refine tf_congr (tf_mul ((frameScale (r / |r|) a * frameScale (r / |r|) b * vectorSign (cylPoint r 0 z) a *
    vectorSign (cylPoint r 0 z) b : ℝ) : ℂ) (harmonic_tf m hm (fun β => P β a b) r z hr n hβ)) fun θ => ?_
  have hs : ∀ c, vectorSign (cylPoint r θ z) c = vectorSign (cylPoint r 0 z) c := fun c => by
    simp [vectorSign, pt_height]
  unfold tensorOf
  rw [frameMat_cartOp θ _ _ (frame_angle r θ z hr)]
  simp only [hs]
  push_cast
  ring

open Classical in
theorem piecewise_tf (M : CellMesh) (m : ℕ) (hm : 0 < m) {d J : ℕ}
    (Q : Fin M.cellCount → Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (r z : ℝ) (hr : r ≠ 0) (n : ℤ)
    (hβ : ∀ β : Fin (J + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n) (a b : Fin 3) :
    TrigFree (n * m) (fun θ => ((frameMat θ (M.piecewise (fun K => tensorOf m (Q K)) (cylPoint r θ z)) a b : ℝ) : ℂ)) := by
  refine tf_congr (tf_sum Finset.univ (fun K (θ : ℝ) => if cylPoint r 0 z ∈ M.piece K then
    ((frameMat θ (tensorOf m (Q K) (cylPoint r θ z)) a b : ℝ) : ℂ) else 0) fun K _ => ?_) fun θ => ?_
  · by_cases h : cylPoint r 0 z ∈ M.piece K
    · simp only [h, if_true]
      exact tensor_tf m hm (Q K) r z hr n hβ a b
    · simp only [h, if_false]
      exact tf_zero _
  · unfold CellMesh.piecewise
    rw [frameMat_eq, sum_apply, sum_inner, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun K _ => ?_
    have e := mem_piece_congr M K (y := cylPoint r θ z) (y' := cylPoint r 0 z) (by rw [pt_radius, pt_radius])
      (by rw [pt_height, pt_height])
    by_cases h : cylPoint r 0 z ∈ M.piece K
    · rw [if_pos h, Set.indicator_of_mem (e.2 h), frameMat_eq]
    · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 h')), zero_apply, inner_zero_left, Complex.ofReal_zero]

theorem modes_zero (M : CellMesh) (m : ℕ) (hm : 0 < m) {d J : ℕ}
    (Q : Fin M.cellCount → Fin (J + 1) → Fin 3 → Fin 3 → CellPoly d) (r z : ℝ) (hr : r ≠ 0) (n : ℤ)
    (hβ : ∀ β : Fin (J + 1), (β : ℤ) ≠ n ∧ -(β : ℤ) ≠ n) :
    modeMat m n (M.piecewise (fun K => tensorOf m (Q K))) r z = 0 := by
  funext a b
  simp only [modeMat, Pi.zero_apply]
  rw [tf_integral (piecewise_tf M m hm Q r z hr n hβ a b) (azimuth m n) (by simp only [azimuth]; push_cast; ring)]
  simp

end Breakdown.FracInternal.GivenModelModelModes
