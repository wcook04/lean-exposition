import Breakdown.CertCell.RowLowPartBasisDefs

open MeasureTheory Set

noncomputable section

namespace Breakdown.CertCell.CellCalculus.RowLow.Internal

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

theorem bi_mono {M N M' N' : ℕ} {h : ℝ × ℝ → ℂ} (hM : M ≤ M') (hN : N ≤ N') (hh : IsBivariatePoly M N h) :
    IsBivariatePoly M' N' h := by
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun i k => if i < M ∧ k < N then a i k else 0, fun p => ?_⟩
  rw [ha p]
  have e1 : ∀ i ∈ Finset.range M', ∑ k ∈ Finset.range N',
      (if i < M ∧ k < N then a i k else 0) * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k
      = if i < M then ∑ k ∈ Finset.range N, a i k * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k else 0 := by
    intro i _
    split_ifs with hi
    · rw [← Finset.sum_range_add_sum_Ico _ hN]
      have : ∑ k ∈ Finset.Ico N N', (if i < M ∧ k < N then a i k else 0) * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k = 0 :=
        Finset.sum_eq_zero (fun k hk => by
          have : ¬ k < N := by simp [Finset.mem_Ico] at hk; omega
          simp [this])
      rw [this, add_zero]
      exact Finset.sum_congr rfl (fun k hk => by simp [hi, Finset.mem_range.1 hk])
    · exact Finset.sum_eq_zero (fun k _ => by simp [hi])
  rw [Finset.sum_congr rfl e1, ← Finset.sum_range_add_sum_Ico _ hM]
  have : ∑ i ∈ Finset.Ico M M', (if i < M then ∑ k ∈ Finset.range N, a i k * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k else 0) = 0 :=
    Finset.sum_eq_zero (fun i hi => by
      have : ¬ i < M := by simp [Finset.mem_Ico] at hi; omega
      simp [this])
  rw [this, add_zero]
  exact Finset.sum_congr rfl (fun i hi => by simp [Finset.mem_range.1 hi])

theorem bi_add {M N : ℕ} {h g : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) (hg : IsBivariatePoly M N g) :
    IsBivariatePoly M N (fun p => h p + g p) := by
  obtain ⟨a, ha⟩ := hh
  obtain ⟨b, hb⟩ := hg
  refine ⟨fun i k => a i k + b i k, fun p => ?_⟩
  dsimp only
  rw [ha p, hb p, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem bi_const_mul {M N : ℕ} {h : ℝ × ℝ → ℂ} (c : ℂ) (hh : IsBivariatePoly M N h) :
    IsBivariatePoly M N (fun p => c * h p) := by
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun i k => c * a i k, fun p => ?_⟩
  dsimp only
  rw [ha p, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem bi_mul_fst {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) :
    IsBivariatePoly (M + 1) N (fun p => (p.1 : ℂ) * h p) := by
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun i k => if i = 0 then 0 else a (i - 1) k, fun p => ?_⟩
  dsimp only
  rw [ha p, Finset.sum_range_succ']
  simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_mul, Finset.sum_const_zero, add_zero,
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem bi_mul_snd {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) :
    IsBivariatePoly M (N + 1) (fun p => (p.2 : ℂ) * h p) := by
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun i k => if k = 0 then 0 else a i (k - 1), fun p => ?_⟩
  dsimp only
  rw [ha p]
  simp only [Finset.sum_range_succ' _ N, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, zero_mul,
    add_zero, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
  ring

theorem bi_zero (M N : ℕ) : IsBivariatePoly M N (fun _ => 0) :=
  ⟨fun _ _ => 0, fun p => by simp⟩

theorem bi_contDiff {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) : ContDiff ℝ 1 h := by
  obtain ⟨a, ha⟩ := hh
  have e : h = fun p : ℝ × ℝ => ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range N, a i k * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k :=
    funext ha
  rw [e]
  have h1 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.1 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_fst
  have h2 : ContDiff ℝ 1 (fun p : ℝ × ℝ => (p.2 : ℂ)) := Complex.ofRealCLM.contDiff.comp contDiff_snd
  refine ContDiff.sum (fun i _ => ContDiff.sum (fun k _ => ?_))
  exact (contDiff_const.mul (h1.pow i)).mul (h2.pow k)

theorem hasDerivAt_fst {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    HasDerivAt (fun r : ℝ => F (r, p.2)) (CellBox.radialDeriv F p) p.1 := by
  have hd : DifferentiableAt ℝ (fun r : ℝ => F (r, p.2)) p.1 :=
    (hF.differentiable one_ne_zero _).comp p.1 ((differentiableAt_id).prodMk (differentiableAt_const _))
  exact hd.hasDerivAt

theorem hasDerivAt_snd {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    HasDerivAt (fun z : ℝ => F (p.1, z)) (CellBox.heightDeriv F p) p.2 := by
  have hd : DifferentiableAt ℝ (fun z : ℝ => F (p.1, z)) p.2 :=
    (hF.differentiable one_ne_zero _).comp p.2 ((differentiableAt_const _).prodMk differentiableAt_id)
  exact hd.hasDerivAt

theorem radialDeriv_eq_fderiv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    CellBox.radialDeriv F p = fderiv ℝ F p (1, 0) := by
  have h1 : HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) := (hF.differentiable one_ne_zero p).hasFDerivAt
  have h2 : HasDerivAt (fun r : ℝ => (r, p.2)) ((1 : ℝ), (0 : ℝ)) p.1 :=
    (hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)
  exact (h1.comp_hasDerivAt p.1 h2).deriv

theorem heightDeriv_eq_fderiv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) (p : ℝ × ℝ) :
    CellBox.heightDeriv F p = fderiv ℝ F p (0, 1) := by
  have h1 : HasFDerivAt F (fderiv ℝ F p) (p.1, p.2) := (hF.differentiable one_ne_zero p).hasFDerivAt
  have h2 : HasDerivAt (fun z : ℝ => (p.1, z)) ((0 : ℝ), (1 : ℝ)) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  exact (h1.comp_hasDerivAt p.2 h2).deriv

theorem continuous_radialDeriv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (CellBox.radialDeriv F) := by
  have e : CellBox.radialDeriv F = fun p => fderiv ℝ F p (1, 0) := funext (radialDeriv_eq_fderiv hF)
  rw [e]
  exact (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem continuous_heightDeriv {F : ℝ × ℝ → ℂ} (hF : ContDiff ℝ 1 F) : Continuous (CellBox.heightDeriv F) := by
  have e : CellBox.heightDeriv F = fun p => fderiv ℝ F p (0, 1) := funext (heightDeriv_eq_fderiv hF)
  rw [e]
  exact (hF.continuous_fderiv one_ne_zero).clm_apply continuous_const

theorem ofReal_pow_hasDerivAt (i : ℕ) (r : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) ^ i) ((i : ℂ) * (r : ℂ) ^ (i - 1)) r := by
  have h := (hasDerivAt_pow i r).ofReal_comp
  simp only [Complex.ofReal_pow, Complex.ofReal_mul, Complex.ofReal_natCast] at h
  exact h

theorem bi_slice_snd {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) (c : ℝ) :
    IsUnivariatePoly N (fun u => h (c, u)) := by
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun k => ∑ i ∈ Finset.range M, a i k * (c : ℂ) ^ i, fun u => ?_⟩
  dsimp only
  rw [ha (c, u), Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finset.sum_mul]

theorem bi_slice_fst {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) (c : ℝ) :
    IsUnivariatePoly M (fun u => h (u, c)) := by
  obtain ⟨a, ha⟩ := hh
  refine ⟨fun i => ∑ k ∈ Finset.range N, a i k * (c : ℂ) ^ k, fun u => ?_⟩
  dsimp only
  rw [ha (u, c)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem bi_radialDeriv {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) :
    IsBivariatePoly M N (CellBox.radialDeriv h) := by
  obtain ⟨a, ha⟩ := hh
  have hd : ∀ p : ℝ × ℝ, CellBox.radialDeriv h p =
      ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range N, a i k * ((i : ℂ) * (p.1 : ℂ) ^ (i - 1)) * (p.2 : ℂ) ^ k := by
    intro p
    have e : (fun r : ℝ => h (r, p.2)) =
        fun r : ℝ => ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range N, a i k * (r : ℂ) ^ i * (p.2 : ℂ) ^ k :=
      funext fun r => ha (r, p.2)
    unfold CellBox.radialDeriv
    rw [e]
    refine HasDerivAt.deriv ?_
    refine HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun k _ => ?_))
    exact ((ofReal_pow_hasDerivAt i p.1).const_mul (a i k)).mul_const _
  cases M with
  | zero => exact ⟨fun _ _ => 0, fun p => by rw [hd p]; simp⟩
  | succ M' =>
    refine bi_mono (Nat.le_succ M') le_rfl ⟨fun i k => ((i + 1 : ℕ) : ℂ) * a (i + 1) k, fun p => ?_⟩
    rw [hd p, Finset.sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, Finset.sum_const_zero, add_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun k _ => ?_))
    push_cast
    ring

theorem bi_heightDeriv {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) :
    IsBivariatePoly M N (CellBox.heightDeriv h) := by
  obtain ⟨a, ha⟩ := hh
  have hd : ∀ p : ℝ × ℝ, CellBox.heightDeriv h p =
      ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range N, a i k * (p.1 : ℂ) ^ i * ((k : ℂ) * (p.2 : ℂ) ^ (k - 1)) := by
    intro p
    have e : (fun z : ℝ => h (p.1, z)) =
        fun z : ℝ => ∑ i ∈ Finset.range M, ∑ k ∈ Finset.range N, a i k * (p.1 : ℂ) ^ i * (z : ℂ) ^ k :=
      funext fun z => ha (p.1, z)
    unfold CellBox.heightDeriv
    rw [e]
    refine HasDerivAt.deriv ?_
    refine HasDerivAt.fun_sum (fun i _ => HasDerivAt.fun_sum (fun k _ => ?_))
    exact (ofReal_pow_hasDerivAt k p.2).const_mul _
  cases N with
  | zero => exact ⟨fun _ _ => 0, fun p => by rw [hd p]; simp⟩
  | succ N' =>
    refine bi_mono le_rfl (Nat.le_succ N') ⟨fun i k => ((k + 1 : ℕ) : ℂ) * a i (k + 1), fun p => ?_⟩
    rw [hd p]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.sum_range_succ']
    simp only [CharP.cast_eq_zero, zero_mul, mul_zero, add_zero, Nat.add_sub_cancel]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    push_cast
    ring

theorem bi_div_fst {M N : ℕ} {h : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) {z₁ z₂ : ℝ} (hz : z₁ < z₂)
    (h0 : ∀ z ∈ Set.Icc z₁ z₂, h (0, z) = 0) :
    ∃ h' : ℝ × ℝ → ℂ, IsBivariatePoly M N h' ∧ ∀ p, h p = (p.1 : ℂ) * h' p := by
  obtain ⟨a, ha⟩ := hh
  cases M with
  | zero => exact ⟨fun _ => 0, bi_zero 0 N, fun p => by rw [ha p]; simp⟩
  | succ M' =>
    set P : Polynomial ℂ := ∑ k ∈ Finset.range N, Polynomial.C (a 0 k) * Polynomial.X ^ k with hP
    have hPe : ∀ z : ℝ, P.eval (z : ℂ) = h (0, z) := by
      intro z
      rw [ha (0, z), Finset.sum_range_succ', hP, Polynomial.eval_finsetSum]
      simp
    have hP0 : P = 0 := by
      refine Polynomial.eq_zero_of_infinite_isRoot P ?_
      refine Set.Infinite.mono (s := (fun z : ℝ => (z : ℂ)) '' Set.Icc z₁ z₂) ?_ ?_
      · rintro _ ⟨z, hz', rfl⟩
        simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, hPe z, h0 z hz']
      · exact (Set.Icc_infinite hz).image Complex.ofReal_injective.injOn
    have hcoef : ∀ k < N, a 0 k = 0 := by
      intro k hk
      have := congrArg (fun Q : Polynomial ℂ => Q.coeff k) hP0
      simp only [hP, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero] at this
      rw [Finset.sum_eq_single k (fun b _ hb => by simp [Ne.symm hb]) (fun h => absurd (Finset.mem_range.2 hk) h)] at this
      simpa using this
    refine ⟨fun p => ∑ i ∈ Finset.range M', ∑ k ∈ Finset.range N, a (i + 1) k * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ k,
      bi_mono (Nat.le_succ M') le_rfl ⟨fun i k => a (i + 1) k, fun p => rfl⟩, fun p => ?_⟩
    rw [ha p, Finset.sum_range_succ']
    have : ∑ k ∈ Finset.range N, a 0 k * (p.1 : ℂ) ^ 0 * (p.2 : ℂ) ^ k = 0 :=
      Finset.sum_eq_zero (fun k hk => by rw [hcoef k (Finset.mem_range.1 hk)]; ring)
    rw [this, add_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => by ring)

def gTot (K : CellBox) (k : ℝ) (φ : Fin 3 → CellPoly) (p : ℝ × ℝ) (a b : Fin 3) : ℂ :=
  testGrad K k φ p a b + (1 / 2 : ℂ) * frameWeight p b * (φ a).eval K p

theorem shape_polys {K : CellBox} {q : ℕ} (hq : 1 ≤ q) {φ : Fin 3 → CellPoly} (hs : IsTestOfShape K q φ) :
    (∀ a, IsBivariatePoly (q + 1) (q + 1) (fun p => (φ a).eval K p)) ∧
    IsBivariatePoly (q + 1) q (fun p => (φ 0).eval K p) ∧ IsBivariatePoly q (q + 1) (fun p => (φ 2).eval K p) := by
  have h0 : IsBivariatePoly (q + 1) q (fun p => (φ 0).eval K p) := by
    obtain ⟨c, hc⟩ := hs 0
    refine ⟨c, fun p => ?_⟩
    dsimp only
    rw [hc p]
    simp only [Fin.isValue, Fin.reduceEq, if_false, if_true]
    rw [Nat.sub_add_cancel hq]
  have h2 : IsBivariatePoly q (q + 1) (fun p => (φ 2).eval K p) := by
    obtain ⟨c, hc⟩ := hs 2
    refine ⟨c, fun p => ?_⟩
    dsimp only
    rw [hc p]
    simp only [Fin.isValue, Fin.reduceEq, if_false, if_true]
    rw [Nat.sub_add_cancel hq]
  have h1 : IsBivariatePoly (q + 1) (q + 1) (fun p => (φ 1).eval K p) := by
    obtain ⟨c, hc⟩ := hs 1
    refine ⟨c, fun p => ?_⟩
    dsimp only
    rw [hc p]
    simp only [Fin.isValue, Fin.reduceEq, if_false]
  refine ⟨fun a => ?_, h0, h2⟩
  fin_cases a
  · exact bi_mono le_rfl (Nat.le_succ q) h0
  · exact h1
  · exact bi_mono (Nat.le_succ q) le_rfl h2

theorem bi_sub {M N : ℕ} {h g : ℝ × ℝ → ℂ} (hh : IsBivariatePoly M N h) (hg : IsBivariatePoly M N g) :
    IsBivariatePoly M N (fun p => h p - g p) := by
  have := bi_add hh (bi_const_mul (-1) hg)
  simpa [sub_eq_add_neg] using this

theorem turn_poly {K : CellBox} {q : ℕ} (k : ℝ) {φ : Fin 3 → CellPoly}
    (hφ : ∀ a, IsBivariatePoly (q + 1) (q + 1) (fun p => (φ a).eval K p)) (a : Fin 3) :
    IsBivariatePoly (q + 1) (q + 1) (fun p => turnVector k (testValue K φ p) a) := by
  unfold turnVector testValue
  fin_cases a
  · exact bi_sub (bi_const_mul _ (hφ 0)) (hφ 1)
  · exact bi_add (bi_const_mul _ (hφ 1)) (hφ 0)
  · exact bi_const_mul _ (hφ 2)

theorem lw_axis {K : CellBox} (h : K.r₁ = 0) (r : ℝ) : K.lineWeight r = r := by
  unfold CellBox.lineWeight; rw [if_pos h]

theorem lw_off {K : CellBox} (h : K.r₁ ≠ 0) (r : ℝ) : K.lineWeight r = 1 := by
  unfold CellBox.lineWeight; rw [if_neg h]

theorem vel_shape {K : CellBox} {q Q : ℕ} (hqQ : q + 2 ≤ Q) {f : ℝ × ℝ → ℂ} (hf : IsBivariatePoly (q + 1) (q + 1) f) :
    ∃ h : ℝ × ℝ → ℂ, IsBivariatePoly Q Q h ∧ ∀ p : ℝ × ℝ, (p.1 : ℂ) * f p = (K.lineWeight p.1 : ℂ) * h p := by
  by_cases h0 : K.r₁ = 0
  · exact ⟨f, bi_mono (by omega) (by omega) hf, fun p => by rw [lw_axis h0]⟩
  · exact ⟨fun p => (p.1 : ℂ) * f p, bi_mono (by omega) (by omega) (bi_mul_fst hf),
      fun p => by rw [lw_off h0]; simp⟩

theorem strain_shape {K : CellBox} (hK : IsCellBox K) (k : ℝ) {φ : Fin 3 → CellPoly} {q Q : ℕ} (hqQ : q + 2 ≤ Q)
    (hφ : ∀ a, IsBivariatePoly (q + 1) (q + 1) (fun p => (φ a).eval K p)) (hreg : IsAxisRegularTest K k φ)
    (a b : Fin 3) : ∃ h : ℝ × ℝ → ℂ, IsBivariatePoly (Q + 1) (Q + 1) h ∧
      ∀ p ∈ K.rect, (p.1 : ℂ) * gTot K k φ p a b = (K.lineWeight p.1 : ℂ) * h p := by
  have hdr := bi_radialDeriv (hφ a)
  have hdz := bi_heightDeriv (hφ a)
  have hr1 := bi_mul_fst (hφ a)
  have hz1 := bi_mul_snd (hφ a)
  obtain rfl | rfl | rfl : b = 0 ∨ b = 1 ∨ b = 2 := by fin_cases b <;> simp
  · have hg : IsBivariatePoly (q + 2) (q + 1) (fun p => CellBox.radialDeriv (fun p => (φ a).eval K p) p
        + (1 / 2 : ℂ) * (p.1 : ℂ) * (φ a).eval K p) :=
      bi_add (bi_mono (by omega) le_rfl hdr) (by
        have := bi_const_mul (1 / 2 : ℂ) hr1
        simpa [mul_assoc] using this)
    have hgt : ∀ p, gTot K k φ p a 0 = CellBox.radialDeriv (fun p => (φ a).eval K p) p
        + (1 / 2 : ℂ) * (p.1 : ℂ) * (φ a).eval K p := by
      intro p; simp [gTot, testGrad, frameWeight]
    by_cases h0 : K.r₁ = 0
    · exact ⟨_, bi_mono (by omega) (by omega) hg, fun p _ => by rw [lw_axis h0, hgt]⟩
    · exact ⟨_, bi_mono (by omega) (by omega) (bi_mul_fst hg), fun p _ => by rw [lw_off h0, hgt]; simp⟩
  · have hT := turn_poly k hφ a
    have hgt : ∀ p, gTot K k φ p a 1 = turnVector k (testValue K φ p) a / (p.1 : ℂ) := by
      intro p; simp [gTot, testGrad, frameWeight]
    by_cases h0 : K.r₁ = 0
    · obtain ⟨C, hC⟩ := hreg
      have hvan : ∀ z ∈ Icc K.z₁ K.z₂, turnVector k (testValue K φ (0, z)) a = 0 := by
        intro z hz
        have hp : ((0 : ℝ), z) ∈ K.rect := ⟨⟨h0.le, h0 ▸ hK.r_order.2.le⟩, hz⟩
        have := hC _ hp a
        simp only [mul_zero] at this
        exact norm_le_zero_iff.1 this
      obtain ⟨T, hTp, hTe⟩ := bi_div_fst hT hK.z_order.2 hvan
      refine ⟨T, bi_mono (by omega) (by omega) hTp, fun p _ => ?_⟩
      rw [lw_axis h0, hgt, hTe p]
      by_cases hp0 : (p.1 : ℂ) = 0
      · rw [hp0]; simp
      · field_simp
    · refine ⟨_, bi_mono (by omega) (by omega) hT, fun p hp => ?_⟩
      have hp0 : (p.1 : ℂ) ≠ 0 := by
        have : 0 < p.1 := lt_of_lt_of_le (lt_of_le_of_ne hK.r_order.1 (Ne.symm h0)) hp.1.1
        exact_mod_cast this.ne'
      rw [lw_off h0, hgt]
      field_simp
      simp
  · have hg : IsBivariatePoly (q + 1) (q + 2) (fun p => CellBox.heightDeriv (fun p => (φ a).eval K p) p
        + (1 / 2 : ℂ) * (p.2 : ℂ) * (φ a).eval K p) :=
      bi_add (bi_mono le_rfl (by omega) hdz) (by
        have := bi_const_mul (1 / 2 : ℂ) hz1
        simpa [mul_assoc] using this)
    have hgt : ∀ p, gTot K k φ p a 2 = CellBox.heightDeriv (fun p => (φ a).eval K p) p
        + (1 / 2 : ℂ) * (p.2 : ℂ) * (φ a).eval K p := by
      intro p; simp [gTot, testGrad, frameWeight]
    by_cases h0 : K.r₁ = 0
    · exact ⟨_, bi_mono (by omega) (by omega) hg, fun p _ => by rw [lw_axis h0, hgt]⟩
    · exact ⟨_, bi_mono (by omega) (by omega) (bi_mul_fst hg), fun p _ => by rw [lw_off h0, hgt]; simp⟩

end Breakdown.CertCell.CellCalculus.RowLow.Internal
