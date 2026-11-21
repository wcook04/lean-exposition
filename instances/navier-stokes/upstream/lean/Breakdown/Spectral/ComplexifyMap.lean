import Breakdown.Spectral.Complexify

noncomputable section

namespace Breakdown.Spectral

namespace Complexification

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

private theorem norm_mk_le (T : X →L[ℝ] X) (z : Complexification X) :
    ‖(⟨T z.re, T z.im⟩ : Complexification X)‖ ≤ ‖T‖ * ‖z‖ := by
  have h1 := norm_sq_eq (⟨T z.re, T z.im⟩ : Complexification X)
  have h2 := norm_sq_eq z
  have a := T.le_opNorm z.re
  have b := T.le_opNorm z.im
  have hsq : ‖(⟨T z.re, T z.im⟩ : Complexification X)‖ ^ 2 ≤ (‖T‖ * ‖z‖) ^ 2 := by
    rw [h1, mul_pow, h2]
    simp only
    have a2 : ‖T z.re‖ ^ 2 ≤ (‖T‖ * ‖z.re‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) a 2
    have b2 : ‖T z.im‖ ^ 2 ≤ (‖T‖ * ‖z.im‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) b 2
    nlinarith [a2, b2]
  exact (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mp hsq

def map (T : X →L[ℝ] X) : Complexification X →L[ℂ] Complexification X :=
  LinearMap.mkContinuous
    { toFun := fun z => ⟨T z.re, T z.im⟩
      map_add' := fun z w => by ext <;> simp
      map_smul' := fun c z => by ext <;> simp [map_sub, map_add, map_smul] } ‖T‖
    (fun z => norm_mk_le T z)

@[simp] theorem map_re (T : X →L[ℝ] X) (z : Complexification X) : (map T z).re = T z.re := rfl
@[simp] theorem map_im (T : X →L[ℝ] X) (z : Complexification X) : (map T z).im = T z.im := rfl

theorem map_add (S T : X →L[ℝ] X) : map (S + T) = map S + map T := by
  ext z <;> simp

theorem map_mul (S T : X →L[ℝ] X) : map (S * T) = map S * map T := by
  ext z <;> simp

theorem map_one : map (1 : X →L[ℝ] X) = 1 := by
  ext z <;> simp

theorem map_pow (T : X →L[ℝ] X) (n : ℕ) : map (T ^ n) = map T ^ n := by
  induction n with
  | zero => rw [pow_zero, pow_zero, map_one]
  | succ n ih => rw [pow_succ, pow_succ, map_mul, ih]

theorem norm_map_le (T : X →L[ℝ] X) : ‖map T‖ ≤ ‖T‖ :=
  LinearMap.mkContinuous_norm_le _ (norm_nonneg T) _

private theorem continuous_im' : Continuous (fun z : Complexification X => z.im) := by
  have h : (fun z : Complexification X => z.im) = fun z => reCLM ((-Complex.I) • z) := by
    funext z
    simp [smul_re]
  rw [h]
  exact reCLM.continuous.comp (continuous_const_smul _)

private theorem continuous_mk' :
    Continuous (fun p : X × X => (⟨p.1, p.2⟩ : Complexification X)) := by
  have h : (fun p : X × X => (⟨p.1, p.2⟩ : Complexification X)) =
      fun p => ofReal p.1 + Complex.I • ofReal p.2 := by
    funext p
    ext <;> simp [smul_re, smul_im]
  rw [h]
  exact (ofReal.continuous.comp continuous_fst).add
    ((continuous_const_smul Complex.I).comp (ofReal.continuous.comp continuous_snd))

theorem isCompactOperator_map {T : X →L[ℝ] X} (hT : IsCompactOperator T) :
    IsCompactOperator (map T) := by
  obtain ⟨K, hK, hKn⟩ := hT
  refine ⟨(fun p : X × X => (⟨p.1, p.2⟩ : Complexification X)) '' (K ×ˢ K),
    (hK.prod hK).image continuous_mk', ?_⟩
  have hre : (fun z : Complexification X => z.re) ⁻¹' (T ⁻¹' K) ∈ (nhds 0 : Filter _) := by
    have ht := (reCLM (X := X)).continuous.tendsto 0
    simp only [map_zero] at ht
    exact ht hKn
  have him : (fun z : Complexification X => z.im) ⁻¹' (T ⁻¹' K) ∈ (nhds 0 : Filter _) := by
    have ht := (continuous_im' (X := X)).tendsto 0
    simp only [zero_im] at ht
    exact ht hKn
  refine Filter.mem_of_superset (Filter.inter_mem hre him) ?_
  rintro z ⟨h1, h2⟩
  exact ⟨(T z.re, T z.im), ⟨h1, h2⟩, rfl⟩

theorem map_ofReal (T : X →L[ℝ] X) (x : X) : map T (ofReal x) = ofReal (T x) := by
  ext <;> simp

theorem conj_map (T : X →L[ℝ] X) (z : Complexification X) : conj (map T z) = map T (conj z) := by
  ext <;> simp [map_neg]

end Complexification

end Breakdown.Spectral
