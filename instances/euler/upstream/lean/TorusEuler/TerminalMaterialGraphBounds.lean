import TorusEuler.TerminalTimeGraphBounds

/-! Geometric spatial bounds on the graph of each material time jet. -/

open Set
open scoped ContDiff

namespace TorusEuler.HierarchyTwistedProfile

noncomputable section

variable {T : ℝ} {k : Vec3} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Fixed-order graph factor in the mean and oscillatory material readouts. -/
def materialGraphFactor (L : ℝ) (N : ℕ) : ℝ :=
  ((3 : ℝ) * (2 : ℝ) ^ N * L) ^ N * (4 : ℝ) ^ N

private theorem materialGraphFactor_mono {L : ℝ} (hL : 1 ≤ L) :
    Monotone (materialGraphFactor L) := by
  have hL₀ : 0 ≤ L := zero_le_one.trans hL
  intro m n hmn
  unfold materialGraphFactor
  have hbase : (3 : ℝ) * (2 : ℝ) ^ m * L ≤ 3 * 2 ^ n * L :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ (by norm_num) hmn) (by norm_num)) hL₀
  have hbase1 : 1 ≤ (3 : ℝ) * (2 : ℝ) ^ n * L :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (by norm_num) (one_le_pow₀ (by norm_num))) hL
  exact mul_le_mul ((pow_le_pow_left₀ (by positivity) hbase _).trans (pow_le_pow_right₀ hbase1 hmn))
    (pow_le_pow_right₀ (by norm_num) hmn) (by positivity) (by positivity)

local notation "I" => Icc (0 : ℝ) T

/-- The time jets of a phase-independent profile incur only the fixed label
scale on the Eulerian graph. -/
theorem norm_iteratedFDeriv_materialGraphRead_mean_le
    (hT : 0 < T) (f : HierarchyTwistedProfile T k E)
    (hmean : HierarchyPeriodicProfile.PhaseIndependent f.val.val)
    {A : Velocity} {t ℓ h D freq L C α : ℝ} {N j q a p : ℕ}
    {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ I) (hℓ : 0 < ℓ) (hD : 1 ≤ D) (hf : 0 < freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hLabel : ℓ⁻¹ ≤ D ^ a)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x)
    (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ m ≤ N, ∀ x, ℓ ^ m * ‖iteratedFDeriv ℝ m B x‖ ≤ L * D)
    (hNorm : ∀ i ≤ q, ∀ m ≤ N, unweightedSeminorm False ℓ h m hT (timeJet hT i f) ≤
      C * D ^ p * freq ^ α)
    (hj : j ≤ q) (m : ℕ) (hm : m ≤ N) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (graphRead A (timeJet hT j f) t) x‖ ≤
      ((((3 : ℝ) * (2 : ℝ) ^ N * L) ^ N * (4 : ℝ) ^ N) * C * D ^ p * freq ^ α) *
        (D ^ (a + 1)) ^ m := by
  have h := graphRead_frequency_jetBound_mean hT (timeJet hT j f)
    (timeJet_phaseIndependent hT f hmean j) (a := a) ht hℓ hD hf hL hC hLabel
    hA hB hBreg (fun i hi => hcoeff i (hi.trans hm)) (hNorm j hj m hm)
  refine (h m le_rfl x).trans ?_
  have hfα := Real.rpow_nonneg hf.le α
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  calc
    _ = (materialGraphFactor L m * C * D ^ p * freq ^ α) * (D ^ (a + 1)) ^ m := by
      rw [pow_add D ((a + 1) * m) p, pow_mul D (a + 1) m]
      unfold materialGraphFactor
      ring
    _ ≤ (materialGraphFactor L N * C * D ^ p * freq ^ α) * (D ^ (a + 1)) ^ m := by
      gcongr
      exact materialGraphFactor_mono hL hm

/-- The oscillatory graph rate preserves the amplitude weight and incurs
one carrier and one phase-width cost for each added spatial derivative. -/
theorem norm_iteratedFDeriv_materialGraphRead_weighted_le
    (hT : 0 < T) {t₀ : ℝ} (ht₀ : 0 ≤ t₀) (htT : t₀ ≤ T)
    (γ : ℝ → ℝ) (hγ : ContinuousOn γ (Icc t₀ T)) (hpos : ∀ r ∈ Icc t₀ T, 0 < γ r)
    (f : HierarchyTwistedProfile T k E)
    {A : Velocity} {t ℓ h D freq L C α : ℝ} {N j q a p : ℕ}
    {B : Vec3 → Vec3 →L[ℝ] Vec3}
    (ht : t ∈ Icc t₀ T) (hℓ : 0 < ℓ) (hh : 0 < h) (hD : 1 ≤ D) (hf : 1 ≤ freq)
    (hL : 1 ≤ L) (hC : 0 ≤ C) (hLabel : ℓ⁻¹ ≤ D ^ a) (hWidth : h = freq ^ (-1 / 2 : ℝ))
    (hCarrier : ‖k‖ ≤ D * freq)
    (hA : ContDiff ℝ ∞ (A t)) (hB : ∀ x, B (A t x) = fderiv ℝ (A t) x)
    (hBreg : ContDiff ℝ ∞ B)
    (hcoeff : ∀ m ≤ N, ∀ x, ℓ ^ m * ‖iteratedFDeriv ℝ m B x‖ ≤ L * D)
    (hNorm : ∀ i ≤ q, ∀ m ≤ N,
      amplitudeSeminorm False ℓ h m hT ht₀ htT γ hγ hpos (timeJet hT i f) ≤
        C * D ^ p * freq ^ α)
    (hj : j ≤ q) (m : ℕ) (hm : m ≤ N) (x : Vec3) :
    ‖iteratedFDeriv ℝ m (graphRead A (timeJet hT j f) t) x‖ ≤
      ((((3 : ℝ) * (2 : ℝ) ^ N * (2*L)) ^ N * (4 : ℝ) ^ N) * C * D ^ p * (γ t * freq ^ α)) *
        (D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ)) ^ m := by
  have hs := graphRead_frequency_jetBound_weighted (a := a) (p := p)
    hT ht₀ htT γ hγ hpos (timeJet hT j f) ht hℓ hh hD hf hL hC hLabel hWidth hCarrier
    hA hB hBreg (fun i hi => hcoeff i (hi.trans hm)) (hNorm j hj m hm)
  refine (hs m le_rfl x).trans ?_
  have hf' : 0 < freq := zero_lt_one.trans_le hf
  have hfα := Real.rpow_nonneg hf'.le α
  have hD₀ : 0 ≤ D := zero_le_one.trans hD
  have hγ₀ : 0 ≤ γ t := (hpos t ht).le
  have hL' : 1 ≤ 2 * L := one_le_mul_of_one_le_of_one_le (by norm_num) hL
  have hExp : (3 : ℝ) * m / 2 + α = (3/2 : ℝ) * m + α := by ring
  calc
    _ = (materialGraphFactor (2*L) m * C * D ^ p * (γ t * freq ^ α)) *
          (D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ)) ^ m := by
      rw [hExp, Real.rpow_add hf', Real.rpow_mul_natCast hf'.le,
        mul_pow (D ^ (max a 1 + 1)) (freq ^ (3/2 : ℝ)) m,
        ← pow_mul D (max a 1 + 1) m, pow_add D ((max a 1 + 1) * m) p]
      unfold materialGraphFactor
      ring
    _ ≤ (materialGraphFactor (2*L) N * C * D ^ p * (γ t * freq ^ α)) *
          (D ^ (max a 1 + 1) * freq ^ (3/2 : ℝ)) ^ m := by
      gcongr
      exact materialGraphFactor_mono hL' hm

end

end TorusEuler.HierarchyTwistedProfile
