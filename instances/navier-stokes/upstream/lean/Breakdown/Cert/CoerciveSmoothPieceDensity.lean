import Breakdown.Cert.CoerciveNodes
import Breakdown.Cert.CoercivePieceAbsorb
import Breakdown.Cert.CoerciveSmoothPieceDensityMeasure
import Breakdown.Cert.CoerciveSmoothPieceDensityEnergy
import Breakdown.Cert.CoerciveSmoothPieceDensityBase
import Breakdown.Cert.CoerciveSmoothPieceDensityPairing

open scoped ContDiff ENNReal
open MeasureTheory

noncomputable section

namespace Breakdown

namespace Coercive

namespace Internal.SmoothPieceDensity

open Internal.PieceAbsorb

theorem real_form {a n : ℝ≥0∞} {x : ℝ} (ha : a ≠ ⊤) (hn : n ≠ ⊤) :
    a + ENNReal.ofReal (-x) ≤ ENNReal.ofReal x + n ↔ a.toReal ≤ x + n.toReal := by
  have e1 : a + ENNReal.ofReal (-x) = ENNReal.ofReal (a.toReal + max (-x) 0) := by
    rw [ENNReal.ofReal_add ENNReal.toReal_nonneg (le_max_right _ _), ENNReal.ofReal_toReal ha,
      ← ofReal_eq_max]
  have e2 : ENNReal.ofReal x + n = ENNReal.ofReal (max x 0 + n.toReal) := by
    rw [ENNReal.ofReal_add (le_max_right _ _) ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hn,
      ← ofReal_eq_max]
  rw [e1, e2, ENNReal.ofReal_le_ofReal_iff (add_nonneg (le_max_right _ _) ENNReal.toReal_nonneg)]
  have h5 : max x 0 - max (-x) 0 = x := by
    rcases le_total x 0 with hx | hx
    · rw [max_eq_right hx, max_eq_left (neg_nonneg.2 hx)]
      ring
    · rw [max_eq_left hx, max_eq_right (neg_nonpos.2 hx)]
      ring
  constructor <;> intro h <;> linarith

theorem ne_top_of_split {a n : ℝ≥0∞} {x : ℝ} (h : a + ENNReal.ofReal (-x) ≤ ENNReal.ofReal x + n)
    (hn : n ≠ ⊤) : a ≠ ⊤ :=
  ne_top_of_le_ne_top (ENNReal.add_ne_top.2 ⟨ENNReal.ofReal_ne_top, hn⟩) (le_trans le_self_add h)

theorem split_add {a1 a2 n1 n2 : ℝ≥0∞} {x1 x2 : ℝ}
    (h1 : a1 + ENNReal.ofReal (-x1) ≤ ENNReal.ofReal x1 + n1)
    (h2 : a2 + ENNReal.ofReal (-x2) ≤ ENNReal.ofReal x2 + n2) (hn1 : n1 ≠ ⊤) (hn2 : n2 ≠ ⊤) :
    (a1 + a2) + ENNReal.ofReal (-(x1 + x2)) ≤ ENNReal.ofReal (x1 + x2) + (n1 + n2) := by
  have ha1 := ne_top_of_split h1 hn1
  have ha2 := ne_top_of_split h2 hn2
  rw [real_form ha1 hn1] at h1
  rw [real_form ha2 hn2] at h2
  rw [real_form (ENNReal.add_ne_top.2 ⟨ha1, ha2⟩) (ENNReal.add_ne_top.2 ⟨hn1, hn2⟩),
    ENNReal.toReal_add ha1 ha2, ENNReal.toReal_add hn1 hn2]
  linarith

theorem split_sum {ι : Type*} (s : Finset ι) {a n : ι → ℝ≥0∞} {x : ι → ℝ}
    (h : ∀ i ∈ s, a i + ENNReal.ofReal (-x i) ≤ ENNReal.ofReal (x i) + n i) (hn : ∀ i ∈ s, n i ≠ ⊤) :
    (∑ i ∈ s, a i) + ENNReal.ofReal (-∑ i ∈ s, x i) ≤ ENNReal.ofReal (∑ i ∈ s, x i) + ∑ i ∈ s, n i := by
  classical
  revert h hn
  refine Finset.induction_on s ?_ ?_
  · intro _ _
    simp
  · intro i s hi ih h hn
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Finset.sum_insert hi]
    exact split_add (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)) (fun j hj => hn j (Finset.mem_insert_of_mem hj)))
      (hn i (Finset.mem_insert_self i s))
      (ENNReal.sum_ne_top.2 fun j hj => hn j (Finset.mem_insert_of_mem hj))

theorem dbl_sum {ι : Type*} (s : Finset ι) {f : ι → ℝ → Space → ℝ≥0∞}
    (hf : ∀ i ∈ s, AEMeasurable (fun z : ℝ × Space => f i z.1 z.2) slabMeasure) :
    ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑ i ∈ s, f i σ y
      = ∑ i ∈ s, ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, f i σ y := by
  classical
  revert hf
  refine Finset.induction_on s ?_ ?_
  · intro _
    simp
  · intro i s hi ih hf
    simp only [Finset.sum_insert hi]
    rw [lintegral_add_iter (f := fun σ y => f i σ y) (g := fun σ y => ∑ j ∈ s, f j σ y)
      (Finset.aemeasurable_fun_sum s fun j hj => hf j (Finset.mem_insert_of_mem hj)),
      ih fun j hj => hf j (Finset.mem_insert_of_mem hj)]

theorem ofReal_identity (b s : ℝ) (hs : 0 ≤ s) :
    ENNReal.ofReal (b - s) + (ENNReal.ofReal (-b) + ENNReal.ofReal s)
      = ENNReal.ofReal b + ENNReal.ofReal (-(b - s)) := by
  rw [ofReal_eq_max (b - s), ofReal_eq_max (-b), ofReal_eq_max b, ofReal_eq_max (-(b - s)),
    ← ENNReal.ofReal_add (le_max_right _ _) hs,
    ← ENNReal.ofReal_add (le_max_right _ _) (add_nonneg (le_max_right _ _) hs),
    ← ENNReal.ofReal_add (le_max_right _ _) (le_max_right _ _)]
  congr 1
  rw [max_def, max_def, max_def, max_def]
  split_ifs <;> linarith

theorem point {nE nM : ℕ} (b : ℤ × ℤ → ℝ) (ep er : Fin nE → ℤ × ℤ → ℝ) (eb : Fin nE → ℝ)
    (mp mr : Fin nM → ℤ × ℤ → ℝ) (mb : Fin nM → ℝ)
    (hep : ∀ β ι, 0 ≤ ep β ι) (her : ∀ β ι, er β ι ≤ 0) (heb : ∀ β, eb β ≤ 0)
    (hmp : ∀ β ι, 0 ≤ mp β ι) (hmr : ∀ β ι, mr β ι ≤ 0) (hmb : ∀ β, mb β ≤ 0) :
    (∑' ι, ENNReal.ofReal (∑ β, ep β ι + ∑ β, mp β ι))
        + (∑' ι, ENNReal.ofReal (b ι + ∑ β, er β ι + ∑ β, mr β ι))
        + ENNReal.ofReal (∑ β, eb β + ∑ β, mb β)
        + ((∑' ι, ENNReal.ofReal (-b ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β ι)) + ENNReal.ofReal (-eb β))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β ι)) + ENNReal.ofReal (-mb β)))
      ≤ ((∑ β, ∑' ι, ENNReal.ofReal (ep β ι)) + (∑ β, ∑' ι, ENNReal.ofReal (mp β ι))
          + ∑' ι, ENNReal.ofReal (b ι))
        + ((∑' ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)))
          + ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))) := by
  have hpos : ∀ ι, ENNReal.ofReal (∑ β, ep β ι + ∑ β, mp β ι)
      = ∑ β, ENNReal.ofReal (ep β ι) + ∑ β, ENNReal.ofReal (mp β ι) := by
    intro ι
    rw [ENNReal.ofReal_add (Finset.sum_nonneg fun β _ => hep β ι) (Finset.sum_nonneg fun β _ => hmp β ι),
      ENNReal.ofReal_sum_of_nonneg fun β _ => hep β ι, ENNReal.ofReal_sum_of_nonneg fun β _ => hmp β ι]
  have hblk : ENNReal.ofReal (∑ β, eb β + ∑ β, mb β) = 0 :=
    ENNReal.ofReal_of_nonpos (add_nonpos (Finset.sum_nonpos fun β _ => heb β) (Finset.sum_nonpos fun β _ => hmb β))
  have hblkn : ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))
      = ∑ β, ENNReal.ofReal (-eb β) + ∑ β, ENNReal.ofReal (-mb β) := by
    rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ENNReal.ofReal_add (Finset.sum_nonneg fun β _ => neg_nonneg.2 (heb β))
        (Finset.sum_nonneg fun β _ => neg_nonneg.2 (hmb β)),
      ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (heb β),
      ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (hmb β)]
  have hι : ∀ ι, ENNReal.ofReal (b ι + ∑ β, er β ι + ∑ β, mr β ι)
      + (ENNReal.ofReal (-b ι) + (∑ β, ENNReal.ofReal (-er β ι) + ∑ β, ENNReal.ofReal (-mr β ι)))
      = ENNReal.ofReal (b ι) + ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)) := by
    intro ι
    have hs1 : 0 ≤ ∑ β, -er β ι := Finset.sum_nonneg fun β _ => neg_nonneg.2 (her β ι)
    have hs2 : 0 ≤ ∑ β, -mr β ι := Finset.sum_nonneg fun β _ => neg_nonneg.2 (hmr β ι)
    have hx : b ι + ∑ β, er β ι + ∑ β, mr β ι = b ι - (∑ β, -er β ι + ∑ β, -mr β ι) := by
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
      ring
    have hsum : ∑ β, ENNReal.ofReal (-er β ι) + ∑ β, ENNReal.ofReal (-mr β ι)
        = ENNReal.ofReal (∑ β, -er β ι + ∑ β, -mr β ι) := by
      rw [ENNReal.ofReal_add hs1 hs2, ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (her β ι),
        ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (hmr β ι)]
    rw [hsum, hx]
    exact ofReal_identity _ _ (add_nonneg hs1 hs2)
  have hsumι := congrArg (fun f : ℤ × ℤ → ℝ≥0∞ => ∑' ι, f ι) (funext hι)
  simp only [ENNReal.tsum_add] at hsumι
  rw [Summable.tsum_finsetSum fun β _ => ENNReal.summable,
    Summable.tsum_finsetSum fun β _ => ENNReal.summable] at hsumι
  simp only [hpos, ENNReal.tsum_add, hblk, hblkn, Finset.sum_add_distrib]
  rw [Summable.tsum_finsetSum fun β _ => ENNReal.summable,
    Summable.tsum_finsetSum fun β _ => ENNReal.summable]
  refine le_of_eq ?_
  calc _ = (∑ β, ∑' ι, ENNReal.ofReal (ep β ι)) + (∑ β, ∑' ι, ENNReal.ofReal (mp β ι))
        + ((∑' ι, ENNReal.ofReal (b ι + ∑ β, er β ι + ∑ β, mr β ι))
          + ((∑' ι, ENNReal.ofReal (-b ι)) + ((∑ β, ∑' ι, ENNReal.ofReal (-er β ι))
            + ∑ β, ∑' ι, ENNReal.ofReal (-mr β ι))))
        + (∑ β, ENNReal.ofReal (-eb β) + ∑ β, ENNReal.ofReal (-mb β)) := by ring
    _ = _ := by rw [hsumι]; ring


theorem neg_point {nE nM : ℕ} (b : ℤ × ℤ → ℝ) (er : Fin nE → ℤ × ℤ → ℝ) (eb : Fin nE → ℝ)
    (mr : Fin nM → ℤ × ℤ → ℝ) (mb : Fin nM → ℝ)
    (her : ∀ β ι, er β ι ≤ 0) (heb : ∀ β, eb β ≤ 0) (hmr : ∀ β ι, mr β ι ≤ 0) (hmb : ∀ β, mb β ≤ 0) :
    (∑' ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)))
        + ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))
      ≤ (∑' ι, ENNReal.ofReal (-b ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β ι)) + ENNReal.ofReal (-eb β))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β ι)) + ENNReal.ofReal (-mb β)) := by
  have hblkn : ENNReal.ofReal (-(∑ β, eb β + ∑ β, mb β))
      = ∑ β, ENNReal.ofReal (-eb β) + ∑ β, ENNReal.ofReal (-mb β) := by
    rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib,
      ENNReal.ofReal_add (Finset.sum_nonneg fun β _ => neg_nonneg.2 (heb β))
        (Finset.sum_nonneg fun β _ => neg_nonneg.2 (hmb β)),
      ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (heb β),
      ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (hmb β)]
  have h1 : ∀ ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι))
      ≤ ENNReal.ofReal (-b ι) + ∑ β, ENNReal.ofReal (-er β ι) + ∑ β, ENNReal.ofReal (-mr β ι) := by
    intro ι
    have hs1 : 0 ≤ ∑ β, -er β ι := Finset.sum_nonneg fun β _ => neg_nonneg.2 (her β ι)
    have hs2 : 0 ≤ ∑ β, -mr β ι := Finset.sum_nonneg fun β _ => neg_nonneg.2 (hmr β ι)
    have hx : -(b ι + ∑ β, er β ι + ∑ β, mr β ι) = -b ι + ∑ β, -er β ι + ∑ β, -mr β ι := by
      rw [Finset.sum_neg_distrib, Finset.sum_neg_distrib]
      ring
    rw [hx, ← ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (her β ι),
      ← ENNReal.ofReal_sum_of_nonneg fun β _ => neg_nonneg.2 (hmr β ι)]
    exact ENNReal.ofReal_add_le.trans (add_le_add ENNReal.ofReal_add_le le_rfl)
  rw [hblkn]
  have step : (∑' ι, ENNReal.ofReal (-(b ι + ∑ β, er β ι + ∑ β, mr β ι)))
      ≤ (∑' ι, ENNReal.ofReal (-b ι)) + (∑ β, ∑' ι, ENNReal.ofReal (-er β ι))
          + ∑ β, ∑' ι, ENNReal.ofReal (-mr β ι) := by
    refine (ENNReal.tsum_le_tsum h1).trans (le_of_eq ?_)
    rw [ENNReal.tsum_add, ENNReal.tsum_add, Summable.tsum_finsetSum fun β _ => ENNReal.summable,
      Summable.tsum_finsetSum fun β _ => ENNReal.summable]
  refine (add_le_add step le_rfl).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

theorem assemble {nE nM : ℕ} {X Xb sJ : ℝ} {Xe : Fin nE → ℝ} {Xm : Fin nM → ℝ}
    (b : ℝ → Space → ℤ × ℤ → ℝ) (ep er : Fin nE → ℝ → Space → ℤ × ℤ → ℝ) (eb : Fin nE → ℝ → Space → ℝ)
    (mp mr : Fin nM → ℝ → Space → ℤ × ℤ → ℝ) (mb : Fin nM → ℝ → Space → ℝ) (S : ℝ → Space → ℝ)
    (hep : ∀ β σ y ι, 0 ≤ ep β σ y ι) (her : ∀ β σ y ι, er β σ y ι ≤ 0) (heb : ∀ β σ y, eb β σ y ≤ 0)
    (hmp : ∀ β σ y ι, 0 ≤ mp β σ y ι) (hmr : ∀ β σ y ι, mr β σ y ι ≤ 0) (hmb : ∀ β σ y, mb β σ y ≤ 0)
    (hE : ∀ β, IsSplitLowerBound (Xe β) (ep β) (er β) (eb β) (fun _ _ => 0))
    (hM : ∀ β, IsSplitLowerBound (Xm β) (mp β) (mr β) (mb β) (fun _ _ => 0))
    (hB : IsDensityLowerBound Xb b)
    (hbn : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-b σ y ι)) < ⊤)
    (mEp : ∀ β, AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (ep β z.1 z.2 ι)) slabMeasure)
    (mMp : ∀ β, AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (mp β z.1 z.2 ι)) slabMeasure)
    (mBp : AEMeasurable (fun z : ℝ × Space => ∑' ι, ENNReal.ofReal (b z.1 z.2 ι)) slabMeasure)
    (mEn : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-er β z.1 z.2 ι)) + ENNReal.ofReal (-eb β z.1 z.2)) slabMeasure)
    (mMn : ∀ β, AEMeasurable (fun z : ℝ × Space =>
      (∑' ι, ENNReal.ofReal (-mr β z.1 z.2 ι)) + ENNReal.ofReal (-mb β z.1 z.2)) slabMeasure)
    (mSp : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (S z.1 z.2)) slabMeasure)
    (mSn : AEMeasurable (fun z : ℝ × Space => ENNReal.ofReal (-S z.1 z.2)) slabMeasure)
    (hSp : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (S σ y)) < ⊤)
    (hSn : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-S σ y)) < ⊤)
    (hsJ : sJ = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (S σ y)).toReal
      - (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-S σ y)).toReal)
    (hX : X = Xb + sJ + ∑ β, Xe β + ∑ β, Xm β) :
    IsSplitLowerBound X (fun σ y ι => ∑ β, ep β σ y ι + ∑ β, mp β σ y ι)
      (fun σ y ι => b σ y ι + ∑ β, er β σ y ι + ∑ β, mr β σ y ι)
      (fun σ y => ∑ β, eb β σ y + ∑ β, mb β σ y) S := by
  have cE : ∀ β, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (ep β σ y ι)) + ENNReal.ofReal (-Xe β)
      ≤ ENNReal.ofReal (Xe β) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y)) := by
    intro β
    have h2 := (hE β).2
    have z1 : ∀ σ y ι, ENNReal.ofReal (er β σ y ι) = 0 := fun σ y ι => ENNReal.ofReal_of_nonpos (her β σ y ι)
    have z2 : ∀ σ y, ENNReal.ofReal (eb β σ y) = 0 := fun σ y => ENNReal.ofReal_of_nonpos (heb β σ y)
    simpa only [z1, z2, tsum_zero, add_zero, neg_zero, ENNReal.ofReal_zero] using h2
  have cM : ∀ β, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (mp β σ y ι)) + ENNReal.ofReal (-Xm β)
      ≤ ENNReal.ofReal (Xm β) + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
        ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y)) := by
    intro β
    have h2 := (hM β).2
    have z1 : ∀ σ y ι, ENNReal.ofReal (mr β σ y ι) = 0 := fun σ y ι => ENNReal.ofReal_of_nonpos (hmr β σ y ι)
    have z2 : ∀ σ y, ENNReal.ofReal (mb β σ y) = 0 := fun σ y => ENNReal.ofReal_of_nonpos (hmb β σ y)
    simpa only [z1, z2, tsum_zero, add_zero, neg_zero, ENNReal.ofReal_zero] using h2
  have fE := fun β => (hE β).1
  have fM := fun β => (hM β).1
  have sE := split_sum Finset.univ (fun β _ => cE β) (fun β _ => (fE β).ne)
  have sM := split_sum Finset.univ (fun β _ => cM β) (fun β _ => (fM β).ne)
  have sS : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (S σ y)) + ENNReal.ofReal (-sJ)
      ≤ ENNReal.ofReal sJ + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ENNReal.ofReal (-S σ y) := by
    rw [real_form hSp.ne hSn.ne]
    linarith
  have nE : ∑ β, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y))) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun β _ => (fE β).ne
  have nM : ∑ β, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
      ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y))) ≠ ⊤ :=
    ENNReal.sum_ne_top.2 fun β _ => (fM β).ne
  have tot := split_add (split_add (split_add hB sS hbn.ne hSn.ne) sE
    (ENNReal.add_ne_top.2 ⟨hbn.ne, hSn.ne⟩) nE) sM
    (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hbn.ne, hSn.ne⟩, nE⟩) nM
  rw [← hX] at tot
  have mAp := ((Finset.aemeasurable_fun_sum Finset.univ fun β _ => mEp β).add
    (Finset.aemeasurable_fun_sum Finset.univ fun β _ => mMp β)).add mBp
  have mNe := Finset.aemeasurable_fun_sum Finset.univ fun β _ => mEn β
  have mNm := Finset.aemeasurable_fun_sum Finset.univ fun β _ => mMn β
  have eN : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι, ENNReal.ofReal (-b σ y ι))
        + ∑ β, ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y))
        + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y))))
      = (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ∑' ι, ENNReal.ofReal (-b σ y ι))
        + ∑ β, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y)))
        + ∑ β, (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y,
          ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y))) := by
    rw [lintegral_add_iter mNm, lintegral_add_iter mNe, dbl_sum Finset.univ fun β _ => mEn β,
      dbl_sum Finset.univ fun β _ => mMn β]
  have hNfin : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, ((∑' ι, ENNReal.ofReal (-b σ y ι))
        + ∑ β, ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y))
        + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y)))) < ⊤ := by
    rw [eN]
    exact lt_top_iff_ne_top.2 (ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hbn.ne, nE⟩, nM⟩)
  have hpt : ∀ σ y, (∑' ι, ENNReal.ofReal (∑ β, ep β σ y ι + ∑ β, mp β σ y ι))
        + (∑' ι, ENNReal.ofReal (b σ y ι + ∑ β, er β σ y ι + ∑ β, mr β σ y ι))
        + ENNReal.ofReal (∑ β, eb β σ y + ∑ β, mb β σ y)
        + ((∑' ι, ENNReal.ofReal (-b σ y ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y)))
      ≤ ((∑ β, ∑' ι, ENNReal.ofReal (ep β σ y ι)) + (∑ β, ∑' ι, ENNReal.ofReal (mp β σ y ι))
          + ∑' ι, ENNReal.ofReal (b σ y ι))
        + ((∑' ι, ENNReal.ofReal (-(b σ y ι + ∑ β, er β σ y ι + ∑ β, mr β σ y ι)))
          + ENNReal.ofReal (-(∑ β, eb β σ y + ∑ β, mb β σ y))) := fun σ y =>
    point (b σ y) (fun β => ep β σ y) (fun β => er β σ y) (fun β => eb β σ y) (fun β => mp β σ y)
      (fun β => mr β σ y) (fun β => mb β σ y) (fun β => hep β σ y) (fun β => her β σ y) (fun β => heb β σ y)
      (fun β => hmp β σ y) (fun β => hmr β σ y) (fun β => hmb β σ y)
  have hXagg : (∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (((∑ β, ∑' ι, ENNReal.ofReal (ep β σ y ι))
          + (∑ β, ∑' ι, ENNReal.ofReal (mp β σ y ι)) + ∑' ι, ENNReal.ofReal (b σ y ι))
          + ENNReal.ofReal (S σ y))) + ENNReal.ofReal (-X)
      ≤ ENNReal.ofReal X + ∫⁻ σ in Set.Icc (0 : ℝ) 1, ∫⁻ y, (((∑' ι, ENNReal.ofReal (-b σ y ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y)))
          + ENNReal.ofReal (-S σ y)) := by
    rw [lintegral_add_iter mSp, lintegral_add_iter mBp,
      lintegral_add_iter (Finset.aemeasurable_fun_sum Finset.univ fun β _ => mMp β),
      dbl_sum Finset.univ fun β _ => mEp β, dbl_sum Finset.univ fun β _ => mMp β,
      lintegral_add_iter mSn, eN]
    refine le_trans (le_of_eq ?_) (tot.trans (le_of_eq ?_)) <;> ring
  have hA : AEMeasurable (fun z : ℝ × Space => ((∑ β, ∑' ι, ENNReal.ofReal (ep β z.1 z.2 ι))
      + (∑ β, ∑' ι, ENNReal.ofReal (mp β z.1 z.2 ι)) + ∑' ι, ENNReal.ofReal (b z.1 z.2 ι))
      + ENNReal.ofReal (S z.1 z.2)) slabMeasure := mAp.add mSp
  refine ⟨lt_of_le_of_lt (lintegral_mono fun σ => lintegral_mono fun y =>
    neg_point (b σ y) (fun β => er β σ y) (fun β => eb β σ y) (fun β => mr β σ y) (fun β => mb β σ y)
      (fun β => her β σ y) (fun β => heb β σ y) (fun β => hmr β σ y) (fun β => hmb β σ y)) hNfin, ?_⟩
  exact transfer (X := X)
    (Dp := fun σ y => (∑' ι, ENNReal.ofReal (∑ β, ep β σ y ι + ∑ β, mp β σ y ι))
        + (∑' ι, ENNReal.ofReal (b σ y ι + ∑ β, er β σ y ι + ∑ β, mr β σ y ι))
        + ENNReal.ofReal (∑ β, eb β σ y + ∑ β, mb β σ y))
    (Dn := fun σ y => (∑' ι, ENNReal.ofReal (-(b σ y ι + ∑ β, er β σ y ι + ∑ β, mr β σ y ι)))
          + ENNReal.ofReal (-(∑ β, eb β σ y + ∑ β, mb β σ y)))
    (Ap := fun σ y => (∑ β, ∑' ι, ENNReal.ofReal (ep β σ y ι)) + (∑ β, ∑' ι, ENNReal.ofReal (mp β σ y ι))
          + ∑' ι, ENNReal.ofReal (b σ y ι))
    (N := fun σ y => (∑' ι, ENNReal.ofReal (-b σ y ι))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-er β σ y ι)) + ENNReal.ofReal (-eb β σ y))
          + ∑ β, ((∑' ι, ENNReal.ofReal (-mr β σ y ι)) + ENNReal.ofReal (-mb β σ y)))
    (Jp := fun σ y => ENNReal.ofReal (S σ y)) (Jn := fun σ y => ENNReal.ofReal (-S σ y))
    hA mSn (Filter.Eventually.of_forall fun z => hpt z.1 z.2) hNfin hXagg


section Pieces

variable {C : Type} {nE nM : ℕ} (m : PieceWeights C nE nM) (P : ℝ) (h : HarmonicBounds) (w : Space → ℝ)
  (W v : ℝ → Space → Space) (G : ℝ → Space → (Space →L[ℝ] Space))
  (H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space))

theorem edgeSum_nonneg_of (hh : HarmonicBounds) (T : Set (ℤ × ℤ)) {X g : ℤ × ℤ → ℝ} (hX : ∀ β, 0 ≤ X β)
    (hg : ∀ κ, 0 ≤ g κ) (ι : ℤ × ℤ) : 0 ≤ edgeSum hh T X g ι := by
  unfold edgeSum
  split_ifs
  · exact Finset.sum_nonneg fun β _ => by
      split_ifs
      exacts [le_rfl, mul_nonneg (hX β) (hg _)]
  · exact Finset.sum_nonneg fun β _ => by
      split_ifs
      exacts [le_rfl, mul_nonneg (hX β) (hg _)]
  · exact le_rfl

theorem epsRest_nonpos (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (β : Fin nE) (ι : ℤ × ℤ) (σ : ℝ) (y : Space) :
    pieceEpsRestMode m h W v G H β ι σ y ≤ 0 := by
  unfold pieceEpsRestMode
  refine neg_nonpos.2 (mul_nonneg (mul_nonneg (hE β y) (Real.sqrt_nonneg _)) ?_)
  refine add_nonneg (add_nonneg (add_nonneg ?_ ?_) ?_) ?_ <;>
    exact edgeSum_nonneg_of _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) _

theorem muRest_nonpos (hM : ∀ β y, 0 ≤ (m.muP β).wt y) (hη : ∀ β, 0 < (m.muP β).eta) (β : Fin nM)
    (ι : ℤ × ℤ) (σ : ℝ) (y : Space) : pieceMuRestMode m h W v G β ι σ y ≤ 0 := by
  unfold pieceMuRestMode
  refine sub_nonpos.2 ((neg_nonpos.2 ?_).trans ?_)
  · exact mul_nonneg (mul_nonneg (hM β y) (Real.sqrt_nonneg _))
      (edgeSum_nonneg_of _ _ (fun _ => Real.sqrt_nonneg _) (fun _ => Real.sqrt_nonneg _) _)
  · refine mul_nonneg (ind_nonneg _) (add_nonneg (div_nonneg (sq_nonneg _) (by linarith [hη β])) ?_)
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (hη β).le) (sq_nonneg _)) (sq_nonneg _)

theorem epsBlock_nonpos (hE : ∀ β y, 0 ≤ (m.epsP β).wt y) (β : Fin nE) (σ : ℝ) (y : Space) :
    pieceEpsBlock m W v G H β σ y ≤ 0 := by
  have hFS : ∀ a, 0 ≤ frameSpeedSup W a y := fun a => Real.iSup_nonneg fun _ => norm_nonneg _
  have hvS : 0 ≤ vortSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hvGS : 0 ≤ vortGradSup W y := Real.iSup_nonneg fun _ => norm_nonneg _
  have hpn : ∀ T (g : ℤ × ℤ → ℝ), 0 ≤ pieceNorm T g := fun _ _ => Real.sqrt_nonneg _
  have hwg : ∀ f, 0 ≤ PieceWeights.wtGrad f y := fun _ => norm_nonneg _
  unfold pieceEpsBlock
  have ha := hE β y
  have h1 := hpn (m.epsP β).modes (fun κ => vortGradAmp H κ σ y)
  have h2 := hpn (m.epsP β).modes (fun κ => vortAmp G κ σ y)
  have h3 := hpn (m.epsP β).modes (fun κ => velAmp v κ σ y)
  have h4 := hpn (m.epsP β).modes (fun κ => gradAmp G κ σ y)
  nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.epsP β).frame)) (hwg (m.epsP β).wt)) h1) h2,
    mul_nonneg (mul_nonneg ha (add_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2) hvS)
      (abs_nonneg (m.epsP β).frame))) (sq_nonneg (pieceNorm (m.epsP β).modes (fun κ => vortAmp G κ σ y))),
    mul_nonneg (mul_nonneg (mul_nonneg ha hvGS) h3) h2, mul_nonneg (mul_nonneg (mul_nonneg ha hvS) h4) h2]

theorem muBlock_nonpos (hM : ∀ β y, 0 ≤ (m.muP β).wt y) (β : Fin nM) (σ : ℝ) (y : Space) :
    pieceMuBlock m W v G β σ y ≤ 0 := by
  have hFS : ∀ a, 0 ≤ frameSpeedSup W a y := fun a => Real.iSup_nonneg fun _ => norm_nonneg _
  have hpn : ∀ T (g : ℤ × ℤ → ℝ), 0 ≤ pieceNorm T g := fun _ _ => Real.sqrt_nonneg _
  have hwg : ∀ f, 0 ≤ PieceWeights.wtGrad f y := fun _ => norm_nonneg _
  unfold pieceMuBlock
  have ha := hM β y
  have h1 := hpn (m.muP β).modes (fun κ => gradAmp G κ σ y)
  have h2 := hpn (m.muP β).modes (fun κ => velAmp v κ σ y)
  nlinarith [mul_nonneg (mul_nonneg (add_nonneg (mul_nonneg ha (hFS (m.muP β).frame)) (hwg (m.muP β).wt)) h1) h2,
    mul_nonneg (mul_nonneg ha (abs_nonneg (m.muP β).frame))
      (sq_nonneg (pieceNorm (m.muP β).modes (fun κ => velAmp v κ σ y)))]

end Pieces

end Internal.SmoothPieceDensity

open Internal.SmoothPieceDensity Internal.PieceAbsorb in
theorem pieceDensitySmoothHolds_of (hP : ModeSquareSumHolds) (hSplit : PiecePairingSplitSmoothHolds) (hI1 : EnergyIdentitySmoothHolds)
    (hBase : BaseDensitySmoothHolds) (hEps : PieceEpsEstimateSmoothHolds) (hMu : PieceMuEstimateSmoothHolds)
    (hSolenoidal : SolenoidalModeHolds) : PieceDensitySmoothHolds := by
  intro C nE nM m P h w k W act w₀ epsSup epsGradSup ratio hm hW hWp hWdiv hWdecay hwb hactm hactp hact2 v hv κ M hM
  obtain ⟨hRm, hRp, hR2⟩ := right_side_sq P W v hW hWp hWdecay hv
  obtain ⟨Q, hQ, -⟩ := hSolenoidal _ hRm hRp hR2
  have hsplit := hSplit m P h w W hm hW hWp hWdiv hWdecay hwb v hv M Q hM hQ
  have hI := hI1 P W v hm.period_pos hW hWp hWdiv hWdecay hv
  have hB := hBase P m.classOf m.convD m.convZ m.c w w₀ hm.finite_classes hm.weight_pos hm.weight_lower hwb
    hm.weight_measurable hm.weight_axi hm.convD_smooth hm.convZ_smooth hm.convD_axi hm.convZ_axi hm.convD_decay
    hm.convZ_decay v hv
  have hE := fun β => hEps m P h w W hm hW hWp hWdiv hWdecay hwb v hv β
  have hMu' := fun β => hMu m P h w W hm hW hWp hWdiv hWdecay hwb v hv Q hQ β
  obtain ⟨mSp, mSn, hSp, hSn, hSeq⟩ := energy_split P W v hW hWp hWdiv hWdecay hv
  obtain ⟨mEp, mMp, mBp, mEn, mMn⟩ := parts_measurable m P h w W v hm hW hWdecay hv
  have hpart : ∀ β, pieceSeminormPart m P β v ≠ ⊤ := fun β => (part_finite m P v hm.cμ_lt_one β (hMu' β)).ne
  have hlin := pairing_linear (smoothRight P W v) M act κ hRm hR2 hactm hact2 hM.1 hM.2.2.1
  refine assemble
    (Xb := vorticityEnergy v - m.c * weightedEnergy w (gradField v) (secondDerivField v))
    (Xe := fun β => epsPairing (fun ι y => PieceWeights.sgn (m.epsP β).modes ι * (m.epsP β).wt y) v
      (smoothRight P W v))
    (Xm := fun β => muPairing (fun ι y => PieceWeights.sgn (m.muP β).modes ι * (m.muP β).wt y) v Q
      - m.cμ * (pieceSeminormPart m P β v).toReal)
    (fun σ y ι => modeVals v (gradField v) (secondDerivField v) ι σ y (baseDensity m.convD m.convZ (m.classOf ι) m.c w y))
    (fun β σ y ι => pieceEpsPos m P (gradField v) β ι σ y)
    (fun β σ y ι => pieceEpsRestMode m h W v (gradField v) (secondDerivField v) β ι σ y)
    (fun β σ y => pieceEpsBlock m W v (gradField v) (secondDerivField v) β σ y)
    (fun β σ y ι => pieceMuPos m P v β ι σ y)
    (fun β σ y ι => pieceMuRestMode m h W v (gradField v) β ι σ y)
    (fun β σ y => pieceMuBlock m W v (gradField v) β σ y)
    (stretchForm W v (gradField v))
    (fun β σ y ι => ?_) (fun β σ y ι => epsRest_nonpos m h W v _ _ hm.eps_wt_nonneg β ι σ y)
    (fun β σ y => epsBlock_nonpos m W v _ _ hm.eps_wt_nonneg β σ y)
    (fun β σ y ι => ?_) (fun β σ y ι => muRest_nonpos m h W v _ hm.mu_wt_nonneg hm.mu_eta_pos β ι σ y)
    (fun β σ y => muBlock_nonpos m W v _ hm.mu_wt_nonneg β σ y)
    hE hMu' hB (base_neg_finite_of_mode_sums m P h w W v hP hm hwb hv) mEp mMp mBp mEn mMn mSp mSn hSp hSn rfl ?_
  · unfold pieceEpsPos
    exact mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (hm.eps_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)
  · unfold pieceMuPos
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (ind_nonneg _) (sub_nonneg.2 hm.cμ_lt_one.le))
      (hm.mu_wt_nonneg β y)) (abs_nonneg _)) (sq_nonneg _)
  · unfold PieceWeights.multiplierGap
    rw [hlin, hsplit, hI, hSeq]
    have hsn : (m.seminormSq P v).toReal = ∑ β, (pieceSeminormPart m P β v).toReal := by
      rw [show m.seminormSq P v = ∑ β, pieceSeminormPart m P β v from rfl,
        ENNReal.toReal_sum fun β _ => hpart β]
    rw [hsn, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring

end Coercive

end Breakdown
