import Breakdown.Cert.ExtendedNodes
import Breakdown.Held.Statements

open Matrix

noncomputable section

namespace Breakdown.Cert

namespace Internal.ExtendedExistsZeroHeld

theorem transpose_mulVec_apply {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (v : Fin k → ℝ)
    (j : Fin k) : (Uᵀ *ᵥ v) j = ∑ i, U i j * v i := by
  simp [Matrix.mulVec, dotProduct]

theorem sum_sq_add_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) {o t r : ℝ}
    (ha : Real.sqrt (∑ j ∈ s, a j ^ 2) ≤ o) (hb : Real.sqrt (∑ j ∈ s, b j ^ 2) ≤ t)
    (hr : o + t ≤ r) : ∑ j ∈ s, (a j + b j) ^ 2 ≤ r ^ 2 := by
  have hA : 0 ≤ ∑ j ∈ s, a j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (a j)
  have hB : 0 ≤ ∑ j ∈ s, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg (b j)
  have hAB := Real.sum_mul_le_sqrt_mul_sqrt s a b
  have hexp : ∑ j ∈ s, (a j + b j) ^ 2 =
      ∑ j ∈ s, a j ^ 2 + 2 * ∑ j ∈ s, a j * b j + ∑ j ∈ s, b j ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hsa := Real.sq_sqrt hA
  have hsb := Real.sq_sqrt hB
  have h0a := Real.sqrt_nonneg (∑ j ∈ s, a j ^ 2)
  have h0b := Real.sqrt_nonneg (∑ j ∈ s, b j ^ 2)
  have hsum : Real.sqrt (∑ j ∈ s, a j ^ 2) + Real.sqrt (∑ j ∈ s, b j ^ 2) ≤ r := by linarith
  have hsq : (Real.sqrt (∑ j ∈ s, a j ^ 2) + Real.sqrt (∑ j ∈ s, b j ^ 2)) ^ 2 ≤ r ^ 2 :=
    pow_le_pow_left₀ (add_nonneg h0a h0b) hsum 2
  rw [hexp]
  nlinarith

theorem box_split {ι : Type*} [Fintype ι] (F M K : ι → ℝ) (x P G O B R : ℝ)
    (hoff : |(∑ i, F i * M i - P - G) - x| ≤ O) (hen : |∑ l, F l * K l + P + G| ≤ B)
    (hinc : B + O ≤ R) : |∑ i, F i * (M i + K i) - x| ≤ R := by
  have h : ∑ i, F i * (M i + K i) - x =
      ((∑ i, F i * M i - P - G) - x) + (∑ l, F l * K l + P + G) := by
    simp only [mul_add, Finset.sum_add_distrib]
    ring
  rw [h]
  exact le_trans (abs_add_le _ _) (by linarith)

theorem stiff_split {ι : Type*} [Fintype ι] (F M K : ι → ℝ) (x : ℝ) :
    ∑ i, F i * (M i + K i) - x = (∑ i, F i * M i - x) + ∑ i, F i * K i := by
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem multiplierOf_eq {k : ℕ} (d : ExtendedCertificateData k) (p : Fin k → ℝ)
    (h : ∃ κ, ∃ f, d.IsHeldSolution p f κ) :
    d.multiplierOf p = fun i => d.multiplier p i + h.choose i := by
  unfold ExtendedCertificateData.multiplierOf
  rw [dif_pos h]
  rfl

theorem exists_held {k : ℕ} (d : ExtendedCertificateData k) (hd : IsNormalExtendedCertificate d)
    (h1 : ExtendedHeldExistsUniqueHolds) (p : Fin k → ℝ) (hp : p ∈ d.params) :
    ∃ κ, ∃ f, d.IsHeldSolution p f κ := by
  obtain ⟨f, κ, hs, -⟩ := h1 d hd p hp
  exact ⟨κ, f, hs⟩

theorem box_part {k : ℕ} (d : ExtendedCertificateData k) (hd : IsNormalExtendedCertificate d)
    (h1 : ExtendedHeldExistsUniqueHolds) (h3 : ExtendedAdjointEnclosureHolds)
    (p : Fin k → ℝ) (hp : p ∈ d.params) (j : Fin k) (hj : j ∈ d.adjointSet) :
    |(d.frameᵀ *ᵥ d.multiplierOf p) j - d.scale j * p j| ≤ |d.scale j| * d.radius j := by
  have he := exists_held d hd h1 p hp
  obtain ⟨f, hf⟩ := he.choose_spec
  have hoff := hd.certificate.adjoint_offset j hj p hp
  have hen := h3 d hd p hp f he.choose hf j hj
  have hinc := hd.certificate.adjoint_inclusion j hj p hp
  unfold ExtendedCertificateData.adjustedMultiplier at hoff
  rewrite [transpose_mulVec_apply d.frame (d.multiplierOf p) j, multiplierOf_eq d p he]
  exact box_split (fun i => d.frame i j) (d.multiplier p) he.choose _ _ _ _ _ _ hoff hen hinc

theorem stiff_term {k : ℕ} (d : ExtendedCertificateData k) (p : Fin k → ℝ)
    (he : ∃ κ, ∃ f, d.IsHeldSolution p f κ) (j : Fin k) :
    (d.frameᵀ *ᵥ d.multiplierOf p) j - d.scale j * p j =
      (∑ i, d.frame i j * d.multiplier p i - d.scale j * p j) + ∑ i, d.frame i j * he.choose i := by
  have hm : ∀ i, d.multiplierOf p i = d.multiplier p i + he.choose i := fun i =>
    congrFun (multiplierOf_eq d p he) i
  rewrite [transpose_mulVec_apply d.frame (d.multiplierOf p) j]
  simp only [hm]
  exact stiff_split (fun i => d.frame i j) (d.multiplier p) he.choose _

theorem stiff_part {k : ℕ} (d : ExtendedCertificateData k) (hd : IsNormalExtendedCertificate d)
    (h1 : ExtendedHeldExistsUniqueHolds) (h4 : ExtendedStiffEnclosureHolds)
    (p : Fin k → ℝ) (hp : p ∈ d.params) :
    ∑ j ∈ d.adjointSetᶜ, ((d.frameᵀ *ᵥ d.multiplierOf p) j - d.scale j * p j) ^ 2 ≤
      d.stiffRadius ^ 2 := by
  have he := exists_held d hd h1 p hp
  obtain ⟨f, hf⟩ := he.choose_spec
  rewrite [Finset.sum_congr rfl fun j _ => congrArg (· ^ 2) (stiff_term d p he j)]
  exact sum_sq_add_le d.adjointSetᶜ (fun j => ∑ i, d.frame i j * d.multiplier p i - d.scale j * p j)
    (fun j => ∑ i, d.frame i j * he.choose i) (hd.certificate.stiff_offset p hp)
    (h4 d hd p hp f he.choose hf) (by rw [add_comm]; exact hd.certificate.stiff_inclusion)

end Internal.ExtendedExistsZeroHeld

open Internal.ExtendedExistsZeroHeld in
theorem extendedExistsZeroHeldHolds_of (h1 : ExtendedHeldExistsUniqueHolds)
    (h2 : ExtendedMultiplierContinuityHolds) (h3 : ExtendedAdjointEnclosureHolds)
    (h4 : ExtendedStiffEnclosureHolds) (h5 : Held.TestSetZeroStatement) :
    ExtendedExistsZeroHeldHolds := by
  intro k d hd
  have hset : Held.testSet d.adjointSet d.radius d.scale d.stiffRadius = d.params := rfl
  obtain ⟨p, hp, hz⟩ := h5 d.adjointSet d.radius d.scale d.stiffRadius d.frame d.multiplierOf
    hd.certificate.radius_nonneg hd.certificate.stiffRadius_nonneg hd.certificate.scale_ne_zero
    ((Matrix.isUnit_iff_isUnit_det d.frame).mp hd.certificate.frame_unit)
    (hset ▸ h2 d hd) (hset ▸ box_part d hd h1 h3) (hset ▸ stiff_part d hd h1 h4)
  rw [hset] at hp
  have he := exists_held d hd h1 p hp
  obtain ⟨f, hf⟩ := he.choose_spec
  refine ⟨p, hp, f, he.choose, hf, ?_⟩
  rw [multiplierOf_eq d p he] at hz
  funext i
  exact congrFun hz i

end Breakdown.Cert
