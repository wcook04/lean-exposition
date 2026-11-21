import Breakdown.FracCell.StFormulaProof

open MeasureTheory

noncomputable section

namespace Breakdown

namespace CellCert

namespace CellFormula

namespace FormulaSynthesis.Internal

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars


theorem mono_span (a : ℕ → ℕ → ℝ) (ha : ∀ j, a j j ≠ 0) (Q : ℕ) :
    ∀ i, i ≤ Q → ∃ d : ℕ → ℝ, ∀ r : ℝ,
      r ^ i = ∑ j ∈ Finset.range (Q + 1), d j * ∑ t ∈ Finset.range (j + 1), a j t * r ^ t := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
  intro hi
  have hlt : ∀ t, t < i → ∃ d : ℕ → ℝ, ∀ r : ℝ,
      r ^ t = ∑ j ∈ Finset.range (Q + 1), d j * ∑ s ∈ Finset.range (j + 1), a j s * r ^ s :=
    fun t ht => ih t ht (by omega)
  choose! D hD using hlt
  refine ⟨fun j => ((if j = i then 1 else 0) - ∑ t ∈ Finset.range i, a i t * D t j) / a i i, ?_⟩
  intro r
  set P : ℕ → ℝ := fun j => ∑ t ∈ Finset.range (j + 1), a j t * r ^ t with hP
  have h1 : ∑ j ∈ Finset.range (Q + 1), (if j = i then (1 : ℝ) else 0) * P j = P i := by
    simp [Finset.mem_range, show i < Q + 1 by omega]
  have h2 : ∑ j ∈ Finset.range (Q + 1), (∑ t ∈ Finset.range i, a i t * D t j) * P j =
      ∑ t ∈ Finset.range i, a i t * r ^ t := by
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [hD t (Finset.mem_range.1 ht) r]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have h3 : P i = ∑ t ∈ Finset.range i, a i t * r ^ t + a i i * r ^ i := by
    simp only [hP]; rw [Finset.sum_range_succ]
  have h4 : ∑ j ∈ Finset.range (Q + 1),
      ((if j = i then (1 : ℝ) else 0) - ∑ t ∈ Finset.range i, a i t * D t j) / a i i * P j =
      (∑ j ∈ Finset.range (Q + 1), (if j = i then (1 : ℝ) else 0) * P j
        - ∑ j ∈ Finset.range (Q + 1), (∑ t ∈ Finset.range i, a i t * D t j) * P j) / a i i := by
    rw [← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  change r ^ i = ∑ j ∈ Finset.range (Q + 1),
      ((if j = i then (1 : ℝ) else 0) - ∑ t ∈ Finset.range i, a i t * D t j) / a i i * P j
  rw [h4, h1, h2, h3]
  field_simp [ha i]
  ring

theorem radialPoly_continuous (B : CellBases) (j : ℕ) : Continuous (B.radialPoly j) := by
  unfold CellBases.radialPoly
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem heightPoly_continuous (B : CellBases) (l : ℕ) : Continuous (B.heightPoly l) := by
  unfold CellBases.heightPoly
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_pow i)

theorem lineWeight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem basisVal_continuous (B : CellBases) (j l : ℕ) : Continuous (basisVal B j l) := by
  unfold basisVal
  exact Complex.continuous_ofReal.comp
    (((radialPoly_continuous B j).comp continuous_fst).mul ((heightPoly_continuous B l).comp continuous_snd))

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem basis_orth (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (j' l' j l : ℕ) :
    ∫ p in K.rect, (K.lineWeight p.1 : ℂ) * basisVal B j' l' p * basisVal B j l p =
      if j' = j ∧ l' = l then 1 else 0 := by
  have e1 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * basisVal B j' l' p * basisVal B j l p =
      (((K.lineWeight p.1 * B.radialPoly j' p.1 * B.radialPoly j p.1) *
        (B.heightPoly l' p.2 * B.heightPoly l p.2) : ℝ) : ℂ) := by
    intro p; unfold basisVal; push_cast; ring
  simp_rw [e1]
  rw [integral_complex_ofReal]
  unfold CellBox.rect
  rw [Measure.volume_eq_prod]
  rw [setIntegral_prod_mul (fun r => K.lineWeight r * B.radialPoly j' r * B.radialPoly j r)
    (fun z => B.heightPoly l' z * B.heightPoly l z)]
  rw [hB.radial_orthonormal j' j, hB.height_orthonormal l' l]
  by_cases h1 : j' = j <;> by_cases h2 : l' = l <;> simp [h1, h2]

theorem sum_swap4 {A C E F M : Type*} [AddCommMonoid M] (s : Finset A) (t : Finset C) (u : Finset E)
    (v : Finset F) (f : A → C → E → F → M) :
    ∑ a ∈ s, ∑ b ∈ t, ∑ c ∈ u, ∑ d ∈ v, f a b c d = ∑ c ∈ u, ∑ d ∈ v, ∑ a ∈ s, ∑ b ∈ t, f a b c d := by
  calc _ = ∑ a ∈ s, ∑ c ∈ u, ∑ b ∈ t, ∑ d ∈ v, f a b c d :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
  _ = ∑ c ∈ u, ∑ a ∈ s, ∑ b ∈ t, ∑ d ∈ v, f a b c d := Finset.sum_comm
  _ = ∑ c ∈ u, ∑ a ∈ s, ∑ d ∈ v, ∑ b ∈ t, f a b c d :=
        Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
  _ = _ := Finset.sum_congr rfl fun c _ => Finset.sum_comm

theorem poly_expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) {d Q : ℕ} (hd : d ≤ Q)
    (P : ℝ × ℝ → ℂ) (hP : P ∈ polyFn d d) :
    ∃ e : ℕ → ℕ → ℂ, ∀ p, P p =
      ∑ j ∈ Finset.range (Q + 1), ∑ l ∈ Finset.range (Q + 1), e j l * basisVal B j l p := by
  obtain ⟨c, hc⟩ := hP
  have hR := mono_span B.radialCoef (fun j => (hB.radial_leading j).ne') Q
  have hH := mono_span B.heightCoef (fun j => (hB.height_leading j).ne') Q
  choose! dR hdR using hR
  choose! dH hdH using hH
  refine ⟨fun j' l' => ∑ j : Fin (d + 1), ∑ l : Fin (d + 1), c j l * (dR j j' : ℂ) * (dH l l' : ℂ), ?_⟩
  intro p
  have hx : ∀ j : Fin (d + 1), (p.1 : ℂ) ^ (j : ℕ) =
      ∑ j' ∈ Finset.range (Q + 1), (dR j j' : ℂ) * (B.radialPoly j' p.1 : ℂ) := by
    intro j
    rw [← Complex.ofReal_pow, hdR j (by omega) p.1]
    simp only [CellBases.radialPoly]
    push_cast
    rfl
  have hy : ∀ l : Fin (d + 1), (p.2 : ℂ) ^ (l : ℕ) =
      ∑ l' ∈ Finset.range (Q + 1), (dH l l' : ℂ) * (B.heightPoly l' p.2 : ℂ) := by
    intro l
    rw [← Complex.ofReal_pow, hdH l (by omega) p.2]
    simp only [CellBases.heightPoly]
    push_cast
    rfl
  rw [hc p]
  have hterm : ∀ j l : Fin (d + 1), c j l * (p.1 : ℂ) ^ (j : ℕ) * (p.2 : ℂ) ^ (l : ℕ) =
      ∑ j' ∈ Finset.range (Q + 1), ∑ l' ∈ Finset.range (Q + 1),
        c j l * (dR j j' : ℂ) * (dH l l' : ℂ) * basisVal B j' l' p := by
    intro j l
    rw [hx j, hy l, mul_assoc, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    unfold basisVal
    push_cast
    ring
  simp_rw [hterm]
  rw [sum_swap4]
  refine Finset.sum_congr rfl fun j' _ => Finset.sum_congr rfl fun l' _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_mul]

theorem coef_comb (K : CellBox) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ) (e : ℕ → ℕ → ℂ)
    {j l : ℕ} (hj : j ≤ Q) (hl : l ≤ Q) :
    B.coef K (fun p => ∑ j' ∈ Finset.range (Q + 1), ∑ l' ∈ Finset.range (Q + 1), e j' l' * basisVal B j' l' p)
      j l = e j l := by
  unfold CellBases.coef
  have hint : ∀ j' l' : ℕ, IntegrableOn
      (fun p : ℝ × ℝ => e j' l' * ((K.lineWeight p.1 : ℂ) * basisVal B j' l' p * basisVal B j l p)) K.rect := by
    intro j' l'
    refine Continuous.continuousOn ?_ |>.integrableOn_compact (rect_compact K)
    exact continuous_const.mul (((Complex.continuous_ofReal.comp
      ((lineWeight_continuous K).comp continuous_fst)).mul (basisVal_continuous B j' l')).mul
        (basisVal_continuous B j l))
  have e1 : ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) *
      (∑ j' ∈ Finset.range (Q + 1), ∑ l' ∈ Finset.range (Q + 1), e j' l' * basisVal B j' l' p) *
        ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ) =
      ∑ j' ∈ Finset.range (Q + 1), ∑ l' ∈ Finset.range (Q + 1),
        e j' l' * ((K.lineWeight p.1 : ℂ) * basisVal B j' l' p * basisVal B j l p) := by
    intro p
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l' _ => ?_
    unfold basisVal
    ring
  simp_rw [e1]
  rw [integral_finsetSum _ fun j' _ => integrable_finsetSum _ fun l' _ => hint j' l']
  simp_rw [integral_finsetSum _ fun l' _ => hint _ l', integral_const_mul, basis_orth K B hB]
  simp [ite_and, Finset.mem_range, Nat.lt_succ_iff.2 hj, Nat.lt_succ_iff.2 hl]

theorem expand (K : CellBox) (B : CellBases) (hB : IsCellBases K B) {d Q : ℕ} (hd : d ≤ Q)
    (P : ℝ × ℝ → ℂ) (hP : P ∈ polyFn d d) (p : ℝ × ℝ) :
    P p = ∑ j ∈ Finset.range (Q + 1), ∑ l ∈ Finset.range (Q + 1), B.coef K P j l * basisVal B j l p := by
  obtain ⟨e, he⟩ := poly_expand K B hB hd P hP
  have hPe : P = fun p => ∑ j ∈ Finset.range (Q + 1), ∑ l ∈ Finset.range (Q + 1), e j l * basisVal B j l p :=
    funext he
  rw [he p]
  refine Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun l hl => ?_
  rw [hPe, coef_comb K B hB Q e (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))
    (Nat.lt_succ_iff.1 (Finset.mem_range.1 hl))]

theorem proj_mem (K : CellBox) (d d' : ℕ) (F : ℝ × ℝ → ℂ) : K.proj d d' F ∈ polyFn d d' := by
  unfold CellBox.proj
  split_ifs with h
  · exact h.choose_spec.1
  · exact ⟨fun _ _ => 0, fun p => by simp⟩

theorem collapse_strain (S : CellScalars) (B : CellBases) (g : LowIndex → ℂ) {n : ℤ} (hn : n ∈ S.resolved)
    (p : ℝ × ℝ) (a b : Fin 3) :
    ∑ i : LowSupp S, g i.1 * unitStrain B i.1 n p a b =
      ∑ j ∈ Finset.range (S.degHigh + 1), ∑ l ∈ Finset.range (S.degHigh + 1),
        g (n, a, Fin.castSucc b, j, l) * basisVal B j l p := by
  rw [Finset.sum_coe_sort (lowSupport S) (fun i => g i * unitStrain B i n p a b)]
  unfold lowSupport
  rw [Finset.sum_product, Finset.sum_eq_single_of_mem n hn]
  · rw [Finset.sum_product, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
    · rw [Finset.sum_product, Finset.sum_eq_single_of_mem (Fin.castSucc b) (Finset.mem_univ _)]
      · rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        simp [unitStrain, basisVal]
      · intro b' _ hb'
        refine Finset.sum_eq_zero fun y _ => ?_
        have hv : b'.val ≠ b.val := fun h => hb' (Fin.ext (by simp [h]))
        simp [unitStrain, hv]
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [unitStrain, ha']
  · intro n' _ hn'
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [unitStrain, hn']

theorem collapse_velocity (S : CellScalars) (B : CellBases) (g : LowIndex → ℂ) {n : ℤ} (hn : n ∈ S.resolved)
    (p : ℝ × ℝ) (a : Fin 3) :
    ∑ i : LowSupp S, g i.1 * unitVelocity B i.1 n p a =
      ∑ j ∈ Finset.range (S.degHigh + 1), ∑ l ∈ Finset.range (S.degHigh + 1),
        g (n, a, Fin.last 3, j, l) * basisVal B j l p := by
  rw [Finset.sum_coe_sort (lowSupport S) (fun i => g i * unitVelocity B i n p a)]
  unfold lowSupport
  rw [Finset.sum_product, Finset.sum_eq_single_of_mem n hn]
  · rw [Finset.sum_product, Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
    · rw [Finset.sum_product, Finset.sum_eq_single_of_mem (Fin.last 3) (Finset.mem_univ _)]
      · rw [Finset.sum_product]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
        simp [unitVelocity, basisVal]
      · intro b' _ hb'
        refine Finset.sum_eq_zero fun y _ => ?_
        have hv : b'.val ≠ 3 := fun h => hb' (Fin.ext (by simp [h]))
        simp [unitVelocity, hv]
    · intro a' _ ha'
      refine Finset.sum_eq_zero fun y _ => ?_
      simp [unitVelocity, ha']
  · intro n' _ hn'
    refine Finset.sum_eq_zero fun y _ => ?_
    simp [unitVelocity, hn']

end FormulaSynthesis.Internal

open SteadyCert Assembly CellAnalysis CellAnalysis.CellScalars FormulaSynthesis.Internal

theorem synthesis : SynthesisStatement := by
  intro α _ _ k N c _ K S B _ hB x _ ζ n hn p _
  constructor
  · funext a b
    simp only [synthStrain, augVector, Sum.elim_inl]
    rw [collapse_strain S B (lowCoef c K S B x) hn p a b]
    change K.proj S.degHigh S.degHigh (gradMode c.order n x.2.1 a b) p = _
    rw [expand K B hB le_rfl _ (proj_mem K _ _ _) p]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    have h3 : (Fin.castSucc b : Fin 4).val < 3 := by simp
    simp only [lowCoef, dif_pos h3]
    rfl
  · funext a
    simp only [synthVelocity, augVector, Sum.elim_inl]
    rw [collapse_velocity S B (lowCoef c K S B x) hn p a]
    change K.proj (S.degHigh - 1) (S.degHigh - 1) (fun p => modeVec c.order n x.1 p.1 p.2 a) p = _
    rw [expand K B hB (Nat.sub_le _ 1) _ (proj_mem K _ _ _) p]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    have h3 : ¬ (Fin.last 3 : Fin 4).val < 3 := by simp
    simp only [lowCoef, dif_neg h3]
    rfl

end CellFormula

end CellCert

end Breakdown
