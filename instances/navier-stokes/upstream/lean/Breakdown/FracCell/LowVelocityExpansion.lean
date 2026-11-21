import Breakdown.FracCell.EnergyPair
import Breakdown.FracCell.EnergyTop
import Breakdown.FracCell.LowEntry

open MeasureTheory Finset

noncomputable section

namespace Breakdown.CellCert.CellEnergy

open CellAnalysis CellFormula TopFormInternal

namespace LowVelocityExpansion.Internal

variable (K : CellBox)

theorem swap4 {A C E F : Type*} (s : Finset A) (t : Finset C) (u : Finset E) (v : Finset F)
    (f : A → C → E → F → ℂ) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
  _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, f a b c d := Finset.sum_comm
  _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
  _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem pair_expansion {B : CellBases} (hB : IsCellBases K B) {d d' : ℕ} (e : ℕ → ℕ → ℂ) {i k : ℕ}
    (hi : i ≤ d) (hk : k ≤ d') :
    K.pairOn K.lineWeightFn (fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), e i k * basisC B i k p)
      (basisC B i k) = e i k := by
  rw [pair_sum_left K _ (f := fun i p => ∑ k ∈ range (d' + 1), e i k * basisC B i k p)
    (fun i _ => continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k)) (basisC_cont B i k)]
  simp_rw [pair_comb_left K B _ _ _ (basisC_cont B i k), pairingMat K hB]
  rw [Finset.sum_eq_single i, Finset.sum_eq_single k]
  · simp
  · intro k' _ hk'
    simp [hk']
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h
  · intro i' _ hi'
    exact Finset.sum_eq_zero fun k' _ => by simp [hi']
  · intro h
    exact absurd (Finset.mem_range.2 (by omega)) h

theorem poly_recon {B : CellBases} (hB : IsCellBases K B) {d d' : ℕ} {R : ℝ × ℝ → ℂ} (hR : R ∈ polyFn d d') :
    ∀ p, R p = ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1),
      K.pairOn K.lineWeightFn R (basisC B i k) * basisC B i k p := by
  obtain ⟨c, hc⟩ := hR
  have hm : ∀ j l : ℕ, j ≤ d → l ≤ d' → ∃ w : ℕ → ℕ → ℂ, ∀ p : ℝ × ℝ, (p.1 : ℂ) ^ j * (p.2 : ℂ) ^ l
      = ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), w i k * basisC B i k p :=
    fun j l hj hl => mono_expand K hB hj hl
  choose! w hw using hm
  have hRe : ∀ p, R p = ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1),
      (∑ j : Fin (d + 1), ∑ l : Fin (d' + 1), c j l * w j l i k) * basisC B i k p := by
    intro p
    rw [hc p]
    have h1 : ∀ j : Fin (d + 1), ∀ l : Fin (d' + 1), c j l * ((p.1 : ℂ) ^ (j : ℕ)) * ((p.2 : ℂ) ^ (l : ℕ)) =
        ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), c j l * w j l i k * basisC B i k p := by
      intro j l
      rw [mul_assoc, hw j l (Nat.lt_succ_iff.1 j.isLt) (Nat.lt_succ_iff.1 l.isLt) p, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => h1 j l]
    rw [swap4]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul]
  have hfun := funext hRe
  intro p
  rw [hRe p]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
  rw [hfun, pair_expansion K hB _ (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk))]

theorem proj_expand {B : CellBases} (hB : IsCellBases K B) {F : ℝ × ℝ → ℂ}
    (hF : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect) (d d' : ℕ) (p : ℝ × ℝ) :
    K.proj d d' F p = ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), B.coef K F i k * basisC B i k p := by
  have hP₀c : Continuous fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), B.coef K F i k * basisC B i k p :=
    continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k)
  have hP₀poly : (fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), B.coef K F i k * basisC B i k p)
      ∈ polyFn d d' := by
    refine poly_sum _ fun i hi => poly_sum _ fun k hk => poly_smul _ (poly_basis B ?_ ?_)
    · have := Finset.mem_range.1 hi; omega
    · have := Finset.mem_range.1 hk; omega
  have hX : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * (F p -
      ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), B.coef K F i k * basisC B i k p)) K.rect := by
    refine (hF.sub (good_of_cont K hP₀c)).congr_fun (fun p _ => ?_) (measurableSet_Icc.prod measurableSet_Icc)
    simp only [Pi.sub_apply]
    ring
  have hb : ∀ i k, i ≤ d → k ≤ d' → K.pairOn K.lineWeightFn (fun p => F p -
      ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), B.coef K F i k * basisC B i k p) (basisC B i k) = 0 := by
    intro i k hi hk
    rw [pair_sub_left K hF (good_of_cont K hP₀c) (basisC_cont B i k), coef_eq, pair_expansion K hB _ hi hk,
      sub_self]
  have horth : ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p -
      ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1), B.coef K F i k * basisC B i k p) T = 0 := by
    intro T hT
    rw [show T = fun p => ∑ i ∈ range (d + 1), ∑ k ∈ range (d' + 1),
      K.pairOn K.lineWeightFn T (basisC B i k) * basisC B i k p from funext (poly_recon K hB hT)]
    rw [pair_sum_right K _ (g := fun i p => ∑ k ∈ range (d' + 1),
      K.pairOn K.lineWeightFn T (basisC B i k) * basisC B i k p) hX
      (fun i _ => continuous_finsetSum _ fun k _ => continuous_const.mul (basisC_cont B i k))]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [pair_comb_right K B _ _ _ hX]
    refine Finset.sum_eq_zero fun k hk => ?_
    rw [hb i k (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)) (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)),
      mul_zero]
  have hex : ∃ P ∈ polyFn d d', ∀ T ∈ polyFn d d', K.pairOn K.lineWeightFn (fun p => F p - P p) T = 0 :=
    ⟨_, hP₀poly, horth⟩
  have hproj : K.proj d d' F = hex.choose := by rw [CellBox.proj, dif_pos hex]
  obtain ⟨hPpoly, hPorth⟩ := hex.choose_spec
  rw [hproj, poly_recon K hB hPpoly p]
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k hk => ?_
  have h0 := hPorth (basisC B i k) (poly_basis B (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hk)))
  rw [pair_sub_left K hF (good_of_cont K (poly_cont hPpoly)) (basisC_cont B i k), coef_eq] at h0
  rw [show K.pairOn K.lineWeightFn hex.choose (basisC B i k) = B.coef K F i k by linear_combination -h0]

end LowVelocityExpansion.Internal

open LowVelocityExpansion.Internal

theorem lowVelocityExpansion : LowVelocityExpansionStatement := by
  intro α D _ _ k N c K B S modes Q q I v G H u h n a p hp
  have hQ : 1 ≤ Q := by
    have := h.scalars.degrees
    rw [h.degHigh_eq]
    omega
  have hF := LowEntry.Internal.modeVec_int K h.box c.order n h.field.velocity_six a
  unfold CellBox.lowVelocity
  rw [proj_expand K h.bases hF]
  have e : Q - 1 + 1 = Q := by omega
  rw [e, Finset.sum_range]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_range]
  rfl

end Breakdown.CellCert.CellEnergy
