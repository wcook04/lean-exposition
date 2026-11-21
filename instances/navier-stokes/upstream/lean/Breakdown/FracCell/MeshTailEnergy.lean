import Breakdown.FracCell.MeshTailSt

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellAnalysis

open SteadyCert Assembly

namespace MeshTailEnergy

theorem sq_sum_orth {α ι : Type*} [DecidableEq ι] [MeasurableSpace α] {μ : Measure α} (s : Finset ι) (ρ : α → ℝ)
    (e : ι → α → ℂ) (a : ι → ℂ)
    (hint : ∀ k ∈ s, ∀ k' ∈ s, Integrable (fun x => (ρ x : ℂ) * (e k x * (starRingEnd ℂ) (e k' x))) μ)
    (horth : ∀ k ∈ s, ∀ k' ∈ s, ∫ x, (ρ x : ℂ) * (e k x * (starRingEnd ℂ) (e k' x)) ∂μ = if k = k' then 1 else 0) :
    ∫ x, ρ x * ‖∑ k ∈ s, a k * e k x‖ ^ 2 ∂μ = ∑ k ∈ s, ‖a k‖ ^ 2 := by
  apply Complex.ofReal_injective
  rw [← integral_complex_ofReal]
  have hpt : ∀ x, ((ρ x * ‖∑ k ∈ s, a k * e k x‖ ^ 2 : ℝ) : ℂ)
      = ∑ k ∈ s, ∑ k' ∈ s, (a k * (starRingEnd ℂ) (a k')) * ((ρ x : ℂ) * (e k x * (starRingEnd ℂ) (e k' x))) := by
    intro x
    rw [Complex.ofReal_mul, Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k' _ => ?_
    rw [map_mul]
    ring
  simp_rw [hpt]
  rw [integral_finsetSum _ (fun k hk => integrable_finsetSum _ fun k' hk' => (hint k hk k' hk').const_mul _)]
  push_cast
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [integral_finsetSum _ (fun k' hk' => (hint k hk k' hk').const_mul _)]
  simp_rw [integral_const_mul]
  rw [Finset.sum_congr rfl fun k' hk' => by rw [horth k hk k' hk']]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, hk, if_true]
  rw [Complex.mul_conj']

theorem exp_orth {m : ℕ} (hm : 1 ≤ m) (n n' : ℤ) :
    ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        (Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) *
          (starRingEnd ℂ) (Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)))
      = if n = n' then 1 else 0 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  set c : ℂ := (((n - n') * m : ℤ) : ℂ) * Complex.I with hc
  have hpt : ∀ θ : ℝ, Complex.exp ((azimuth m n * θ : ℝ) * Complex.I) *
      (starRingEnd ℂ) (Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)) = Complex.exp (c * θ) := by
    intro θ
    rw [← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I, ← Complex.exp_add, hc]
    congr 1
    unfold azimuth
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_const_mul, ← intervalIntegral.integral_of_le hpi.le]
  by_cases hnn : n = n'
  · have hc0 : c = 0 := by rw [hc, hnn]; simp
    simp only [hc0, zero_mul, Complex.exp_zero, intervalIntegral.integral_const, hnn, if_true]
    rw [sub_zero, Complex.real_smul, mul_one]
    push_cast
    field_simp
  · have hk : ((n - n') * m : ℤ) ≠ 0 := by
      refine mul_ne_zero (sub_ne_zero.2 hnn) ?_
      exact_mod_cast (show m ≠ 0 by omega)
    have hc0 : c ≠ 0 := by
      rw [hc]; exact mul_ne_zero (by exact_mod_cast hk) Complex.I_ne_zero
    rw [integral_exp_mul_complex hc0]
    have h2 : Complex.exp (c * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [hc]
      have := Complex.exp_int_mul_two_pi_mul_I ((n - n') * m)
      rw [← this]
      congr 1
      push_cast
      ring
    push_cast at h2
    simp [h2, hnn]

theorem poly_step (a b : ℝ) (ρ : ℝ → ℝ) (hρ : Continuous ρ) (P : ℕ → ℝ → ℝ) (hP : ∀ l, Continuous (P l))
    (horth : ∀ l l', ∫ x in Set.Icc a b, ρ x * P l x * P l' x = if l = l' then 1 else 0)
    {C : Type*} [Fintype C] (s : Finset ℕ) (A : C → ℕ → ℂ) :
    ∫ x in Set.Icc a b, ρ x * ∑ c, ‖∑ l ∈ s, A c l * (P l x : ℂ)‖ ^ 2 = ∑ c, ∑ l ∈ s, ‖A c l‖ ^ 2 := by
  simp_rw [Finset.mul_sum]
  rw [integral_finsetSum _ (fun c _ => Continuous.integrableOn_Icc (by
    exact hρ.mul ((continuous_finsetSum _ fun l _ => continuous_const.mul
      (Complex.continuous_ofReal.comp (hP l))).norm.pow 2)))]
  refine Finset.sum_congr rfl fun c _ => ?_
  refine sq_sum_orth s ρ (fun l x => (P l x : ℂ)) (A c) (fun k _ k' _ => ?_) (fun k _ k' _ => ?_)
  · exact Continuous.integrableOn_Icc (by fun_prop)
  · have e : ∀ x, (ρ x : ℂ) * ((P k x : ℂ) * (starRingEnd ℂ) (P k' x : ℂ)) = ((ρ x * P k x * P k' x : ℝ) : ℂ) := by
      intro x; rw [Complex.conj_ofReal]; push_cast; ring
    simp_rw [e]
    rw [integral_complex_ofReal, horth k k']
    split_ifs <;> simp

theorem trig_step {m : ℕ} (hm : 1 ≤ m) {C : Type*} [Fintype C] (L : Finset ℕ) (S : Finset ℤ) (W : C → ℕ → ℤ → ℂ) :
    (1 / (2 * Real.pi)) * ∫ θ in (0 : ℝ)..(2 * Real.pi), ∑ c, ∑ l ∈ L,
        ‖∑ n' ∈ S, W c l n' * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)‖ ^ 2
      = ∑ c, ∑ l ∈ L, ∑ n' ∈ S, ‖W c l n'‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcont : ∀ c l, Continuous (fun θ : ℝ =>
      ‖∑ n' ∈ S, W c l n' * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)‖ ^ 2) := by
    intro c l
    exact (continuous_finsetSum _ fun n' _ => continuous_const.mul (by fun_prop)).norm.pow 2
  rw [intervalIntegral.integral_finsetSum (fun c _ => (continuous_finsetSum _ fun l _ => hcont c l).intervalIntegrable _ _),
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [intervalIntegral.integral_finsetSum (fun l _ => (hcont c l).intervalIntegrable _ _), Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_of_le hpi.le, ← integral_const_mul]
  exact sq_sum_orth S (fun _ => 1 / (2 * Real.pi)) (fun n' θ => Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I))
    (W c l) (fun k _ k' _ => Continuous.integrableOn_Ioc (by fun_prop)) (fun k _ k' _ => exp_orth hm k k')

end MeshTailEnergy

open MeshTailEnergy in
theorem inputEnergy_holds : InputEnergyStatement := by
  intro K B hK hB m hm I O _ _ T w i k
  have hlw : Continuous (fun r : ℝ => K.lineWeight r) := by
    by_cases h : K.r₁ = 0
    · simp only [CellBox.lineWeight, h, if_true]; exact continuous_id
    · simp only [CellBox.lineWeight, h, if_false]; exact continuous_const
  have hrp : ∀ j, Continuous (fun r : ℝ => B.radialPoly j r) := by
    intro j; unfold CellBases.radialPoly
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hhp : ∀ l, Continuous (fun z : ℝ => B.heightPoly l z) := by
    intro l; unfold CellBases.heightPoly
    exact continuous_finsetSum _ fun i _ => by fun_prop
  have hcA : ∀ (W : ℤ → ℂ), Continuous (fun θ : ℝ =>
      ‖∑ n' ∈ T.inModes, W n' * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)‖ ^ 2) := by
    intro W
    exact (continuous_finsetSum _ fun n' _ => continuous_const.mul (by fun_prop)).norm.pow 2
  have hz : (fun θ => ∫ z in Set.Icc K.z₁ K.z₂, ∑ c, ‖T.radialInput m B w i k c z θ‖ ^ 2)
      = fun θ => ∑ c, ∑ l ∈ Finset.range (T.inputDeg i + 1),
          ‖∑ n' ∈ T.inModes, w i n' k l c * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)‖ ^ 2 := by
    funext θ
    rw [← poly_step K.z₁ K.z₂ (fun _ => 1) continuous_const B.heightPoly hhp
      (fun l l' => by simp only [one_mul]; exact hB.height_orthonormal l l') (Finset.range (T.inputDeg i + 1))
      (fun c l => ∑ n' ∈ T.inModes, w i n' k l c * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [one_mul]
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold TailFamily.radialInput
    rw [Finset.sum_comm]
    congr 2
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n' _ => ?_
    ring
  have hr : (fun θ => ∫ r in Set.Icc K.r₁ K.r₂, K.lineWeight r * ∑ c, ‖T.heightInput m B w i k c r θ‖ ^ 2)
      = fun θ => ∑ c, ∑ j ∈ Finset.range (T.inputDeg i + 1),
          ‖∑ n' ∈ T.inModes, w i n' j k c * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I)‖ ^ 2 := by
    funext θ
    rw [← poly_step K.r₁ K.r₂ K.lineWeight hlw B.radialPoly hrp
      (fun j j' => hB.radial_orthonormal j j') (Finset.range (T.inputDeg i + 1))
      (fun c j => ∑ n' ∈ T.inModes, w i n' j k c * Complex.exp ((azimuth m n' * θ : ℝ) * Complex.I))]
    refine integral_congr_ae (Filter.Eventually.of_forall fun r => ?_)
    refine congrArg (K.lineWeight r * ·) ?_
    refine Finset.sum_congr rfl fun c _ => ?_
    unfold TailFamily.heightInput
    rw [Finset.sum_comm]
    congr 2
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun n' _ => ?_
    ring
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · rw [hz]
    exact (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun l _ => hcA _).intervalIntegrable _ _
  · rw [hz, trig_step hm (Finset.range (T.inputDeg i + 1)) T.inModes (fun c l n' => w i n' k l c)]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (T.dim i))))]
    rw [Finset.sum_comm]
  · rw [hr]
    exact (continuous_finsetSum _ fun c _ => continuous_finsetSum _ fun l _ => hcA _).intervalIntegrable _ _
  · rw [hr, trig_step hm (Finset.range (T.inputDeg i + 1)) T.inModes (fun c j n' => w i n' j k c)]
    rw [Finset.sum_comm]
    simp_rw [Finset.sum_comm (s := (Finset.univ : Finset (Fin (T.dim i))))]
    rw [Finset.sum_comm]

end CellAnalysis

end CellCert

end Breakdown
