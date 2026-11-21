import Breakdown.CertCell.BridgeTraceStatements
import Breakdown.CertCell.CornerDataFlipLinks

open scoped ContDiff
open MeasureTheory Set Filter

noncomputable section

namespace Breakdown.CertCell.SideTrace

namespace Internal.CornerAxis

open CellCert.CellFormula CellCert.CellAnalysis Bridge
open Bridge.Internal.CornerDataFlip (ae_plane_flip plane_weak_data weak_on_rectangle)

theorem side_upper (f fd : ℝ → ℂ) {k : ℝ} (hk : 0 < k) :
    sideTrace f fd 0 k = upperTrace f fd k := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [sideTrace, upperTrace, edgeSign]
  rw [if_neg (not_lt.2 hk.le), min_eq_left hk.le, max_eq_right hk.le, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hk.le, neg_one_mul]
  congr 1
  refine intervalIntegral.integral_congr fun z _ => ?_
  push_cast
  field_simp
  ring

theorem side_lower (f fd : ℝ → ℂ) {k : ℝ} (hk : 0 < k) :
    sideTrace f fd 0 (-k) = lowerTrace f fd k := by
  have hk' : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
  simp only [sideTrace, lowerTrace, edgeSign]
  rw [if_pos (by linarith), min_eq_right (by linarith), max_eq_left (by linarith),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith), one_mul]
  refine intervalIntegral.integral_congr fun z _ => ?_
  have e : ∀ x : ℂ, (k : ℂ) * x * (k : ℂ)⁻¹ = x := fun x => by field_simp
  push_cast
  field_simp
  linear_combination e (f z) + e ((z : ℂ) * fd z) + e ((k : ℂ) * fd z)

theorem upper_flip (f g : ℝ → ℂ) (s : ℂ) (h : ℝ) :
    upperTrace (fun z => s * f (-z)) (fun z => -(s * g (-z))) h = s * lowerTrace f g h := by
  simp only [upperTrace, lowerTrace]
  rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_const_mul]
  have e := intervalIntegral.integral_comp_neg (a := 0) (b := h)
    (fun z => s * (g z * (((1 + z / h : ℝ)) : ℂ) + f z / (h : ℂ)))
  simp only [neg_zero] at e
  rw [← e]
  refine intervalIntegral.integral_congr fun z _ => ?_
  push_cast
  ring

theorem upper_congr {f f' g g' : ℝ → ℂ} (k : ℝ) (hf : ∀ᵐ z, f z = f' z) (hg : ∀ᵐ z, g z = g' z) :
    upperTrace f g k = upperTrace f' g' k := by
  simp only [upperTrace]
  congr 1
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [hf, hg] with z h1 h2 _
  rw [h1, h2]

theorem weak_congr {f g g' : ℝ → ℂ} {a b : ℝ} (h : HasWeakDerivOn f g a b) (hg : ∀ᵐ z, g z = g' z) :
    HasWeakDerivOn f g' a b := by
  refine ⟨h.1, h.2.1.congr_fun_ae (ae_restrict_of_ae hg), fun ψ h1 h2 h3 => ?_⟩
  rw [h.2.2 ψ h1 h2 h3]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_restrict_of_ae hg] with z hz
  rw [hz]

theorem side_comb (f0 f1 f2 f3 : ℝ → ℂ) (o β c α : ℝ) (hα : α = β * c)
    (h0 : IntegrableOn f0 (Icc (min 0 o) (max 0 o))) (h1 : IntegrableOn f1 (Icc (min 0 o) (max 0 o)))
    (h2 : IntegrableOn f2 (Icc (min 0 o) (max 0 o))) (h3 : IntegrableOn f3 (Icc (min 0 o) (max 0 o))) :
    (β : ℂ) * sideTrace f0 (fun z => f2 z + (c : ℂ) * f3 z) 0 o + (α : ℂ) * sideTrace f1 (fun _ => 0) 0 o
      = (β : ℂ) * sideTrace f0 f2 0 o + (α : ℂ) * sideTrace f1 f3 0 o := by
  have hw : Continuous fun z : ℝ => ((((z - o) / (0 - o)) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp ((continuous_id.sub continuous_const).div_const _)
  have i2 : ∀ f : ℝ → ℂ, IntegrableOn f (Icc (min 0 o) (max 0 o)) →
      IntegrableOn (fun z => ((((z - o) / (0 - o)) : ℝ) : ℂ) * f z) (Icc (min 0 o) (max 0 o)) :=
    fun f hf => hf.continuousOn_mul hw.continuousOn isCompact_Icc
  have i1 : ∀ f : ℝ → ℂ, IntegrableOn f (Icc (min 0 o) (max 0 o)) →
      IntegrableOn (fun z => (((1 / (0 - o)) : ℝ) : ℂ) * f z) (Icc (min 0 o) (max 0 o)) :=
    fun f hf => hf.const_mul _
  have hA : ∫ z in Icc (min 0 o) (max 0 o), ((((1 / (0 - o)) : ℝ) : ℂ) * f0 z
        + ((((z - o) / (0 - o)) : ℝ) : ℂ) * (f2 z + (c : ℂ) * f3 z))
      = (∫ z in Icc (min 0 o) (max 0 o), ((((1 / (0 - o)) : ℝ) : ℂ) * f0 z
        + ((((z - o) / (0 - o)) : ℝ) : ℂ) * f2 z))
        + (c : ℂ) * ∫ z in Icc (min 0 o) (max 0 o), ((((z - o) / (0 - o)) : ℝ) : ℂ) * f3 z := by
    rw [← integral_const_mul, ← integral_add (f := fun z => (((1 / (0 - o)) : ℝ) : ℂ) * f0 z
      + ((((z - o) / (0 - o)) : ℝ) : ℂ) * f2 z) (g := fun z => (c : ℂ) * (((((z - o) / (0 - o)) : ℝ) : ℂ) * f3 z))
      ((i1 _ h0).add (i2 _ h2)) ((i2 _ h3).const_mul _)]
    congr 1
    funext z
    ring
  have hD : ∫ z in Icc (min 0 o) (max 0 o), ((((1 / (0 - o)) : ℝ) : ℂ) * f1 z
        + ((((z - o) / (0 - o)) : ℝ) : ℂ) * f3 z)
      = (∫ z in Icc (min 0 o) (max 0 o), ((((1 / (0 - o)) : ℝ) : ℂ) * f1 z
        + ((((z - o) / (0 - o)) : ℝ) : ℂ) * 0))
        + ∫ z in Icc (min 0 o) (max 0 o), ((((z - o) / (0 - o)) : ℝ) : ℂ) * f3 z := by
    have e : (fun z : ℝ => ((((1 / (0 - o)) : ℝ) : ℂ) * f1 z + ((((z - o) / (0 - o)) : ℝ) : ℂ) * 0))
        = fun z => ((((1 / (0 - o)) : ℝ) : ℂ) * f1 z) := by
      funext z
      ring
    rw [e, ← integral_add (i1 _ h1) (i2 _ h3)]
  simp only [sideTrace]
  rw [hA, hD, hα]
  push_cast
  ring

theorem line_step {f0 f1 f2 f3 f3' e0 e1 e2 e3 : ℝ → ℂ} {s : ℂ} {β c α h h' : ℝ} (hα : α = β * c)
    (hh : 0 < h) (hh' : 0 < h') (hM : SideTraceMatchHolds)
    (hw0 : ∀ k, 0 < k → HasWeakDerivOn f0 f2 (-k) k) (hw1 : ∀ k, 0 < k → HasWeakDerivOn f1 f3' (-k) k)
    (hsym : ∀ᵐ z, f3' z = f3 z)
    (he0 : ∀ᵐ z, e0 z = s * f0 (-z)) (he1 : ∀ᵐ z, e1 z = s * f1 (-z))
    (he2 : ∀ᵐ z, e2 z = -(s * f2 (-z))) (he3 : ∀ᵐ z, e3 z = -(s * f3 (-z))) :
    (β : ℂ) * upperTrace e0 (fun z => e2 z + (c : ℂ) * e3 z) h + (α : ℂ) * upperTrace e1 (fun _ => 0) h
      = s * ((β : ℂ) * upperTrace f0 (fun z => f2 z + (c : ℂ) * f3 z) h'
        + (α : ℂ) * upperTrace f1 (fun _ => 0) h') := by
  have hw1' : ∀ k, 0 < k → HasWeakDerivOn f1 f3 (-k) k := fun k hk => weak_congr (hw1 k hk) hsym
  have u0 : upperTrace e0 (fun z => e2 z + (c : ℂ) * e3 z) h
      = s * lowerTrace f0 (fun z => f2 z + (c : ℂ) * f3 z) h := by
    rw [← upper_flip]
    refine upper_congr h he0 ?_
    filter_upwards [he2, he3] with z a b
    rw [a, b]
    ring
  have u1 : upperTrace e1 (fun _ => 0) h = s * lowerTrace f1 (fun _ => 0) h := by
    rw [← upper_flip]
    exact upper_congr h he1 (Eventually.of_forall fun z => by simp)
  rw [u0, u1, ← side_lower _ _ hh, ← side_lower _ _ hh, ← side_upper _ _ hh', ← side_upper _ _ hh']
  have hK : 0 < h + h' + 1 := by linarith
  have sub : ∀ o : ℝ, -(h + h' + 1) < o → o < h + h' + 1 →
      Icc (min 0 o) (max 0 o) ⊆ Ioo (-(h + h' + 1)) (h + h' + 1) := fun o a b =>
    Icc_subset_Ioo (lt_min (by linarith) a) (max_lt (by linarith) b)
  obtain ⟨i0, i2, -⟩ := hw0 (h + h' + 1) hK
  obtain ⟨i1, i3, -⟩ := hw1' (h + h' + 1) hK
  have s1 := sub (-h) (by linarith) (by linarith)
  have s2 := sub h' (by linarith) (by linarith)
  have L := side_comb f0 f1 f2 f3 (-h) β c α hα (i0.mono_set s1) (i1.mono_set s1) (i2.mono_set s1)
    (i3.mono_set s1)
  have R := side_comb f0 f1 f2 f3 h' β c α hα (i0.mono_set s2) (i1.mono_set s2) (i2.mono_set s2)
    (i3.mono_set s2)
  have hm : -(h + h' + 1) < min 0 (min (-h) h') :=
    lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hx : max 0 (max (-h) h') < h + h' + 1 :=
    max_lt (by linarith) (max_lt (by linarith) (by linarith))
  have t0 := hM f0 f2 0 (-h) h' _ _ (by linarith : -h < 0).ne' hh'.ne hm hx (hw0 _ hK)
  have t1 := hM f1 f3 0 (-h) h' _ _ (by linarith : -h < 0).ne' hh'.ne hm hx (hw1' _ hK)
  have key : (β : ℂ) * sideTrace f0 (fun z => f2 z + (c : ℂ) * f3 z) 0 (-h)
        + (α : ℂ) * sideTrace f1 (fun _ => 0) 0 (-h)
      = (β : ℂ) * sideTrace f0 (fun z => f2 z + (c : ℂ) * f3 z) 0 h'
        + (α : ℂ) * sideTrace f1 (fun _ => 0) 0 h' := by
    rw [L, R, t0, t1]
  linear_combination s * key

theorem corner_weighted (hC : CornerTraceHolds) (F Fr Fz Frz : ℝ × ℝ → ℂ) {cr orr k : ℝ} (hne : cr ≠ orr)
    (hk : 0 < k) (i0 : IntegrableOn F (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k))
    (i1 : IntegrableOn Fr (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k))
    (i2 : IntegrableOn Fz (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k))
    (i3 : IntegrableOn (fun p => ((p.1 - orr : ℝ) : ℂ) * Frz p) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k)) :
    cornerMoment cr orr 0 k F Fr Fz Frz = edgeSign cr orr * ∫ r in Icc (min cr orr) (max cr orr),
      ((((1 / (cr - orr)) : ℝ) : ℂ)
          * upperTrace (fun z => F (r, z)) (fun z => Fz (r, z) + ((r - orr : ℝ) : ℂ) * Frz (r, z)) k
        + (((r - orr) / (cr - orr) : ℝ) : ℂ) * upperTrace (fun z => Fr (r, z)) (fun _ => 0) k) := by
  have e : cornerMoment cr orr 0 k F Fr Fz Frz
      = cornerMoment cr orr 0 k F Fr (fun p => Fz p + ((p.1 - orr : ℝ) : ℂ) * Frz p) (fun _ => 0) := by
    simp only [cornerMoment]
    congr 1
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    push_cast
    ring
  rw [e]
  exact hC F Fr (fun p => Fz p + ((p.1 - orr : ℝ) : ℂ) * Frz p) (fun _ => 0) cr orr k hne hk i0 i1
    (i2.add i3) integrableOn_zero

theorem data_int {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (hU : ModeAxisPlainIntegrableHolds)
    (hA : ModeAxisIntegrableHolds) (hL : ModePlaneDerivsHolds) (ξ : ℤ × ℤ) (a : Fin 3) {cr orr k : ℝ}
    (hcr : 0 < cr) (hor : 0 ≤ orr) (hne : cr ≠ orr) (hk : 0 < k) :
    IntegrableOn (planeVelocity ξ v a) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) ∧
    IntegrableOn (planeGrad ξ G a 0) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) ∧
    IntegrableOn (planeGrad ξ G a 2) (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) ∧
    IntegrableOn (fun p => ((p.1 - orr : ℝ) : ℂ) * planeSlope ξ H a 0 2 p)
      (Icc (min cr orr) (max cr orr) ×ˢ Icc 0 k) := by
  rcases hor.eq_or_lt with h0 | h0
  · subst h0
    rw [min_eq_right hcr.le, max_eq_left hcr.le]
    obtain ⟨u0, u1⟩ := hU Γ P v G H g hp ξ a 0 cr 0 k hcr hk
    obtain ⟨-, u2⟩ := hU Γ P v G H g hp ξ a 2 cr 0 k hcr hk
    obtain ⟨-, -, w⟩ := hA Γ P v G H g hp ξ a 0 2 cr 0 k hcr hk
    refine ⟨u0, u1, u2, ?_⟩
    simpa only [sub_zero] using w
  · obtain ⟨hW, hI⟩ := hL Γ P v G H g hp ξ a (min cr orr) (max cr orr) 0 k (lt_min hcr h0)
      (min_lt_max.2 hne) hk
    refine ⟨hW.1, hW.2.1, hW.2.2.1, ?_⟩
    exact (hI 0 2).2.continuousOn_mul
      (Complex.continuous_ofReal.comp (continuous_fst.sub continuous_const)).continuousOn
      (isCompact_Icc.prod isCompact_Icc)

theorem slope_swap_ae {Γ : Set Symmetry} {P : ℝ} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    {g : ℝ → Space → Space} (hp : IsPerturbation Γ P v G H g) (hL : ModePlaneDerivsHolds) (ξ : ℤ × ℤ)
    (a : Fin 3) :
    ∀ᵐ p : ℝ × ℝ, 0 < p.1 → modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) = planeSlope ξ H a 0 2 p := by
  have key : ∀ n : ℕ, ∀ᵐ p : ℝ × ℝ,
      p ∈ Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Ioo (-((n : ℝ) + 2)) ((n : ℝ) + 2) →
        modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) - planeSlope ξ H a 0 2 p = 0 := by
    intro n
    have hn : (2 : ℝ) ≤ (n : ℝ) + 2 := by have := n.cast_nonneg (α := ℝ); linarith
    have hlo : 0 < 1 / ((n : ℝ) + 2) := by positivity
    have hlohi : 1 / ((n : ℝ) + 2) < (n : ℝ) + 2 := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    have hz : -((n : ℝ) + 2) < (n : ℝ) + 2 := by linarith
    obtain ⟨hW, hI⟩ := hL Γ P v G H g hp ξ a _ _ _ _ hlo hlohi hz
    obtain ⟨hI', hW'⟩ := plane_weak_data hp ξ a
    have iM := (hI' (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) (-((n : ℝ) + 2)) ((n : ℝ) + 2) hlo).2.2.2
    have iS := (hI 0 2).2
    have hint : interior (Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2))
        = Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Ioo (-((n : ℝ) + 2)) ((n : ℝ) + 2) := by
      rw [interior_prod_eq, interior_Icc, interior_Icc]
    refine (isOpen_Ioo.prod isOpen_Ioo).ae_eq_zero_of_integral_contDiff_smul_eq_zero ?_ ?_
    · exact ((iM.sub iS).mono_set (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)).locallyIntegrableOn
    · intro ψ hψ hc hsub
      rw [← hint] at hsub
      have hout : ∀ p, p ∉ Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2) →
          p ∉ tsupport ψ := fun p hp ht => hp (interior_subset (hsub ht))
      have z0 : ∀ p, p ∉ Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2) →
          ψ p = 0 := fun p hp => image_eq_zero_of_notMem_tsupport (hout p hp)
      have zd : ∀ p, p ∉ Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2) →
          fderiv ℝ ψ p (0, 1) = 0 := fun p hp => by
        rw [fderiv_of_notMem_tsupport ℝ (hout p hp)]
        rfl
      have hpos : ∀ p ∈ tsupport ψ, 0 < p.1 := fun p ht =>
        lt_of_lt_of_le hlo (interior_subset (hsub ht)).1.1
      have e1 := weak_on_rectangle z0 zd (hW' ψ hψ hc hpos).2.2
      have e2 := (hW.2.2.2.2 ψ hψ hc hsub).2.2
      have e3 : ∫ p in Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2),
            modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) * ((ψ p : ℝ) : ℂ)
          = ∫ p in Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2),
            planeSlope ξ H a 0 2 p * ((ψ p : ℝ) : ℂ) :=
        neg_injective (e1.symm.trans e2)
      have hψc : ContinuousOn (fun p => ((ψ p : ℝ) : ℂ))
          (Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2)) :=
        (Complex.continuous_ofReal.comp hψ.continuous).continuousOn
      have hK := (isCompact_Icc (a := 1 / ((n : ℝ) + 2)) (b := (n : ℝ) + 2)).prod
        (isCompact_Icc (a := -((n : ℝ) + 2)) (b := (n : ℝ) + 2))
      rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2))
        (fun p hp => by rw [z0 p hp, zero_smul])]
      have e4 : ∫ p in Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2),
            ψ p • (modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) - planeSlope ξ H a 0 2 p)
          = (∫ p in Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2),
              modeSecondDeriv ξ H 0 (planePoint p) (a, 0, 2) * ((ψ p : ℝ) : ℂ))
            - ∫ p in Icc (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Icc (-((n : ℝ) + 2)) ((n : ℝ) + 2),
              planeSlope ξ H a 0 2 p * ((ψ p : ℝ) : ℂ) := by
        rw [← integral_sub (iM.mul_continuousOn hψc hK) (iS.mul_continuousOn hψc hK)]
        refine integral_congr_ae (Eventually.of_forall fun p => ?_)
        simp only [Complex.real_smul]
        ring
      rw [e4, e3, sub_self]
  have hall := ae_all_iff.2 key
  filter_upwards [hall] with p hp hp1
  obtain ⟨n, hn⟩ := exists_nat_gt (max (1 / p.1) (max |p.1| |p.2|))
  have h1 : 1 / p.1 < (n : ℝ) + 2 := by
    have := le_max_left (1 / p.1) (max |p.1| |p.2|)
    linarith
  have h2 : |p.1| < (n : ℝ) + 2 := by
    have := le_max_left |p.1| |p.2|
    have := le_max_right (1 / p.1) (max |p.1| |p.2|)
    linarith
  have h3 : |p.2| < (n : ℝ) + 2 := by
    have := le_max_right |p.1| |p.2|
    have := le_max_right (1 / p.1) (max |p.1| |p.2|)
    linarith
  have hm : p ∈ Ioo (1 / ((n : ℝ) + 2)) ((n : ℝ) + 2) ×ˢ Ioo (-((n : ℝ) + 2)) ((n : ℝ) + 2) := by
    refine ⟨⟨?_, (abs_lt.1 h2).2⟩, abs_lt.1 h3⟩
    rw [div_lt_iff₀ (by linarith)]
    rw [div_lt_iff₀ hp1] at h1
    linarith
  exact sub_eq_zero.1 (hp n hm)

end Internal.CornerAxis

open Internal.CornerAxis CellCert.CellFormula CellCert.CellAnalysis Bridge in
theorem cornerDataFlipAxis (hX : Breakdown.CertCell.Bridge.ModeFlipHolds)
    (hF : Breakdown.CertCell.Bridge.CornerFlipHolds) (hC : Breakdown.CertCell.Bridge.CornerTraceHolds)
    (hM : Breakdown.CertCell.SideTrace.SideTraceMatchHolds)
    (hD : Breakdown.CertCell.Bridge.ModeHeightDerivHolds)
    (hA : Breakdown.CertCell.SideTrace.ModeAxisIntegrableHolds)
    (hU : Breakdown.CertCell.SideTrace.ModeAxisPlainIntegrableHolds)
    (hL : Breakdown.CertCell.SideTrace.ModePlaneDerivsHolds) :
    Breakdown.CertCell.SideTrace.CornerDataFlipAxisHolds := by
  intro Γ P v G H g hp hflip ξ a cr orr h h' hcr hor hne hh hh'
  obtain ⟨a0, a1, a2, a3⟩ := data_int hp hU hA hL (flipLabel ξ) a hcr hor hne hh
  obtain ⟨b0, b1, b2, b3⟩ := data_int hp hU hA hL ξ a hcr hor hne hh'
  rw [corner_weighted hC _ _ _ _ hne hh a0 a1 a2 a3, corner_weighted hC _ _ _ _ hne hh' b0 b1 b2 b3,
    mul_left_comm (frameSign a : ℂ) (CellCert.CellFormula.edgeSign cr orr)]
  congr 1
  rw [← integral_const_mul]
  refine integral_congr_ae ?_
  have hm0 : 0 ≤ min cr orr := le_min hcr.le hor
  have hs0 : frameSign (0 : Fin 3) = 1 := by simp [frameSign]
  have hs2 : frameSign (2 : Fin 3) = -1 := by simp [frameSign]
  have fD := (ae_restrict_iff' measurableSet_Ioi).1 (hD Γ P v G H g hp ξ a)
  have fS0 := slope_swap_ae hp hL ξ a
  rw [Measure.volume_eq_prod] at fS0
  have fS := Measure.ae_ae_of_ae_prod fS0
  have fF0 := Bridge.Internal.CornerDataFlip.ae_plane_flip hp hflip ξ
  rw [Measure.volume_eq_prod] at fF0
  have fF := Measure.ae_ae_of_ae_prod fF0
  have f0 : ∀ᵐ r : ℝ, r ≠ 0 := compl_mem_ae_iff.2 (measure_singleton 0)
  filter_upwards [ae_restrict_mem measurableSet_Icc, ae_restrict_of_ae fD, ae_restrict_of_ae fS,
    ae_restrict_of_ae fF, ae_restrict_of_ae f0] with r hrI hrD hrS hrF hr0
  have hr : 0 < r := lt_of_le_of_ne (hm0.trans hrI.1) (Ne.symm hr0)
  have hrD' := hrD hr
  refine line_step (β := 1 / (cr - orr)) (c := r - orr) (α := (r - orr) / (cr - orr)) (by ring) hh hh' hM
    (fun k hk => (hrD' k hk).1) (fun k hk => (hrD' k hk).2.2) (hrS.mono fun z hz => hz hr) ?_ ?_ ?_ ?_
  · filter_upwards [hrF] with z hz
    exact congrFun hz.1 a
  · filter_upwards [hrF] with z hz
    show modeGrad (flipLabel ξ) G 0 (planePoint (r, z)) (a, 0) = _
    rw [congrFun hz.2.1 (a, 0)]
    simp only [hs0]
    push_cast
    ring_nf
    rfl
  · filter_upwards [hrF] with z hz
    show modeGrad (flipLabel ξ) G 0 (planePoint (r, z)) (a, 2) = _
    rw [congrFun hz.2.1 (a, 2)]
    simp only [hs2]
    push_cast
    ring_nf
    rfl
  · filter_upwards [hrF] with z hz
    show modeSecondDeriv (flipLabel ξ) H 0 (planePoint (r, z)) (a, 2, 0) = _
    rw [congrFun hz.2.2 (a, 2, 0)]
    simp only [hs0, hs2]
    push_cast
    ring_nf
    rfl

end Breakdown.CertCell.SideTrace
