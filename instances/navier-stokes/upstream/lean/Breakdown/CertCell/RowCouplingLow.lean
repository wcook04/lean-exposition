import Breakdown.CertCell.RowProfileDefs
import Breakdown.CertCell.LocalModeIntegrable
import Breakdown.FracCell.LowVelocityExpansion

open MeasureTheory Matrix Finset

noncomputable section

namespace Breakdown

namespace CertCell

namespace CellCalculus

open SteadyCert CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.Assembly CellCert.CellEnergy LocalField

namespace Internal.RowCouplingLow

theorem low_expand (r : ℂ) (P : Fin 3 → Fin 3 → ℂ) (U W Ω φc : Fin 3 → ℂ) :
    r * ∑ i : Fin 3, (∑ j : Fin 3, ∑ l : Fin 3, (alternatingSymbol i j l : ℂ) *
        (curlComp P j * W l + Ω j * U l)) * φc i
      = ∑ a : Fin 3, ∑ b : Fin 3, P a b * (r * ∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
          ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol i j' l' : ℂ) * W j' * φc l')
        + ∑ a : Fin 3, U a * (r * ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol a j' l' : ℂ) * φc j' * Ω l') := by
  simp only [Fin.sum_univ_three, curlComp, alternatingSymbol, permSign]
  norm_num
  ring

theorem fst_ne_zero_ae : ∀ᵐ p ∂(volume : Measure (ℝ × ℝ)), p.1 ≠ 0 := by
  rw [ae_iff]
  have e : {a : ℝ × ℝ | ¬ a.1 ≠ 0} = ({0} : Set ℝ) ×ˢ (Set.univ : Set ℝ) := by
    ext p; simp
  rw [e, Measure.volume_eq_prod, Measure.prod_prod, Real.volume_singleton, zero_mul]

theorem weighted_cont (K : CellBox) (Q : ℕ) (W : ℝ × ℝ → Fin 3 → ℂ) (a : Fin 3)
    (hW : ∃ c : ℕ → ℕ → ℂ, ∀ p : ℝ × ℝ, (K.lineWeight p.1 : ℂ) * W p a * p.1
      = ∑ i ∈ Finset.range (Q + 1), ∑ j ∈ Finset.range (Q + 1), c i j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j) :
    ∃ g : ℝ × ℝ → ℂ, Continuous g ∧ ∀ p : ℝ × ℝ, p.1 ≠ 0 → (p.1 : ℂ) * W p a = g p := by
  obtain ⟨c, hc⟩ := hW
  by_cases h0 : K.r₁ = 0
  · have hw : ∀ r : ℝ, K.lineWeight r = r := fun r => by simp [CellBox.lineWeight, h0]
    refine ⟨fun p => ∑ i ∈ Finset.range Q, ∑ j ∈ Finset.range (Q + 1), c (i + 1) j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j,
      by fun_prop, fun p hp => ?_⟩
    have h1 := hc p
    have h2 := hc (0, p.2)
    rw [hw] at h1 h2
    rw [Finset.sum_range_succ'] at h1 h2
    simp only [Complex.ofReal_zero, zero_mul, mul_zero, pow_zero, mul_one, ne_eq, Nat.succ_ne_zero,
      not_false_eq_true, zero_pow, Finset.sum_const_zero, zero_add] at h2
    simp only [pow_zero, mul_one] at h1
    rw [← h2, add_zero] at h1
    show _ = ∑ i ∈ Finset.range Q, ∑ j ∈ Finset.range (Q + 1), c (i + 1) j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j
    have hp' : (p.1 : ℂ) ≠ 0 := by exact_mod_cast hp
    apply mul_left_cancel₀ hp'
    rw [show (p.1 : ℂ) * ((p.1 : ℂ) * W p a) = (p.1 : ℂ) * W p a * p.1 by ring, h1, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  · have hw : ∀ r : ℝ, K.lineWeight r = 1 := fun r => by simp [CellBox.lineWeight, h0]
    refine ⟨fun p => ∑ i ∈ Finset.range (Q + 1), ∑ j ∈ Finset.range (Q + 1), c i j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j,
      by fun_prop, fun p _ => ?_⟩
    have h1 := hc p
    rw [hw] at h1
    simp only [Complex.ofReal_one, one_mul] at h1
    show _ = ∑ i ∈ Finset.range (Q + 1), ∑ j ∈ Finset.range (Q + 1), c i j * (p.1 : ℂ) ^ i * (p.2 : ℂ) ^ j
    rw [← h1, mul_comm]

theorem rect_compact (K : CellBox) : IsCompact K.rect := isCompact_Icc.prod isCompact_Icc

theorem rect_meas (K : CellBox) : MeasurableSet K.rect := measurableSet_Icc.prod measurableSet_Icc

theorem ae_rect_pos (K : CellBox) (hK : IsCellBox K) : ∀ᵐ p ∂(volume.restrict K.rect), 0 < p.1 := by
  filter_upwards [ae_restrict_of_ae fst_ne_zero_ae, ae_restrict_mem (rect_meas K)] with p h1 h2
  exact lt_of_le_of_ne (hK.r_order.1.trans h2.1.1) (Ne.symm h1)

theorem eval_cont (K : CellBox) (P : CellPoly) : Continuous (fun p : ℝ × ℝ => P.eval K p) := by
  unfold CellPoly.eval CellBox.refR CellBox.refZ
  fun_prop

theorem basis_cont (B : CellBases) (j l : ℕ) : Continuous (basisValue B j l) := by
  unfold basisValue CellBases.radialPoly CellBases.heightPoly
  fun_prop

theorem strain_term_int (K : CellBox) (hK : IsCellBox K) (B : CellBases) (Wα : ℝ × ℝ → Fin 3 → ℂ)
    (g : Fin 3 → ℝ × ℝ → ℂ) (hg : ∀ a, Continuous (g a)) (hgW : ∀ a p, p.1 ≠ 0 → (p.1 : ℂ) * Wα p a = g a p)
    (φ : Fin 3 → CellPoly) (a b : Fin 3) (j l : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * basisValue B j l p *
      ∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
        ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol i j' l' : ℂ) * Wα p j' * (starRingEnd ℂ) ((φ l').eval K p))
      K.rect := by
  have hc : Continuous (fun p : ℝ × ℝ => basisValue B j l p * ∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
      ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol i j' l' : ℂ) * g j' p * (starRingEnd ℂ) ((φ l').eval K p)) := by
    have := basis_cont B j l
    have := fun l' => eval_cont K (φ l')
    fun_prop
  refine (hc.continuousOn.integrableOn_compact (rect_compact K)).congr_fun_ae ?_
  filter_upwards [ae_rect_pos K hK] with p hp
  have e := fun a => hgW a p hp.ne'
  simp only [Fin.sum_univ_three, ← e]
  ring

theorem bounded_int (K : CellBox) (f : ℝ × ℝ → ℂ) (hf : AEStronglyMeasurable f (volume.restrict K.rect))
    (hb : ∃ C : ℝ, ∀ p ∈ K.rect, ‖f p‖ ≤ C) : IntegrableOn f K.rect := by
  obtain ⟨C, hC⟩ := hb
  exact ⟨hf, .restrict_of_bounded (C := C) (rect_compact K).measure_lt_top
    ((ae_restrict_iff' (rect_meas K)).2 (ae_of_all _ hC))⟩

theorem velocity_term_int (K : CellBox) (B : CellBases) (Ωα : ℝ × ℝ → Fin 3 → ℂ)
    (hΩm : ∀ a, AEStronglyMeasurable (fun p => Ωα p a) (volume.restrict K.rect))
    (hΩb : ∃ C : ℝ, ∀ p ∈ K.rect, ∀ a, ‖Ωα p a‖ ≤ C) (φ : Fin 3 → CellPoly) (a : Fin 3) (j l : ℕ) :
    IntegrableOn (fun p : ℝ × ℝ => (p.1 : ℂ) * basisValue B j l p *
      ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol a j' l' : ℂ) * (starRingEnd ℂ) ((φ j').eval K p) * Ωα p l')
      K.rect := by
  obtain ⟨C, hC⟩ := hΩb
  have hi : ∀ l', IntegrableOn (fun p => Ωα p l') K.rect := fun l' =>
    bounded_int K _ (hΩm l') ⟨C, fun p hp => hC p hp l'⟩
  have e : (fun p : ℝ × ℝ => (p.1 : ℂ) * basisValue B j l p *
      ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol a j' l' : ℂ) * (starRingEnd ℂ) ((φ j').eval K p) * Ωα p l')
      = fun p => ∑ j' : Fin 3, ∑ l' : Fin 3, Ωα p l' *
          ((p.1 : ℂ) * basisValue B j l p * (alternatingSymbol a j' l' : ℂ) * (starRingEnd ℂ) ((φ j').eval K p)) := by
    funext p
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    ring
  rw [e]
  refine integrable_finsetSum _ fun j' _ => integrable_finsetSum _ fun l' _ => ?_
  have := basis_cont B j l
  have := eval_cont K (φ j')
  exact (hi l').mul_continuousOn (by fun_prop : Continuous _).continuousOn (rect_compact K)

theorem coef_lift (K : CellBox) (B : CellBases) {F Fc Fs : ℝ × ℝ → ℂ}
    (hc : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fc p) K.rect)
    (hs : IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * Fs p) K.rect)
    (hae : ∀ᵐ p ∂(volume.restrict K.rect), F p = Fc p + Complex.I * Fs p) :
    (∀ j l : ℕ, B.coef K Fc j l + Complex.I * B.coef K Fs j l = B.coef K F j l) ∧
      IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * F p) K.rect := by
  refine ⟨fun j l => ?_, ?_⟩
  · have bc : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) := by
      unfold CellBases.radialPoly CellBases.heightPoly
      fun_prop
    have i1 := hc.mul_continuousOn bc.continuousOn (rect_compact K)
    have i2 := hs.mul_continuousOn bc.continuousOn (rect_compact K)
    unfold CellBases.coef
    rw [← integral_const_mul, ← integral_add i1 (i2.const_mul Complex.I)]
    refine integral_congr_ae ?_
    filter_upwards [hae] with p hp
    rw [hp]
    ring
  · refine (hc.add (hs.const_mul Complex.I)).congr_fun_ae ?_
    filter_upwards [hae] with p hp
    simp only [Pi.add_apply]
    rw [hp]
    ring

theorem int_fsum {ι : Type*} [Fintype ι] (S : Set (ℝ × ℝ)) (f : ι → ℝ × ℝ → ℂ)
    (hf : ∀ i, IntegrableOn (f i) S) : ∫ p in S, ∑ i, f i p = ∑ i, ∫ p in S, f i p :=
  integral_finsetSum _ fun i _ => hf i

theorem pairing_expand (K : CellBox) (hK : IsCellBox K) (B : CellBases) (hB : IsCellBases K B) (Q : ℕ)
    (hQ : 1 ≤ Q) (s : Fin 3 → Fin 3 → ℝ × ℝ → ℂ) (u : Fin 3 → ℝ × ℝ → ℂ)
    (hsi : ∀ a b, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * s a b p) K.rect)
    (hui : ∀ a, IntegrableOn (fun p => (K.lineWeight p.1 : ℂ) * u a p) K.rect)
    (Wα Ωα : ℝ × ℝ → Fin 3 → ℂ) (g : Fin 3 → ℝ × ℝ → ℂ) (hg : ∀ a, Continuous (g a))
    (hgW : ∀ a p, p.1 ≠ 0 → (p.1 : ℂ) * Wα p a = g a p)
    (hΩm : ∀ a, AEStronglyMeasurable (fun p => Ωα p a) (volume.restrict K.rect))
    (hΩb : ∃ C : ℝ, ∀ p ∈ K.rect, ∀ a, ‖Ωα p a‖ ≤ C) (φ : Fin 3 → CellPoly) :
    rowPairing K (lowCoupling K Q Wα Ωα s u) φ
      = (∑ a : Fin 3, ∑ b : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
          B.coef K (s a b) j l * couplingStrainRow K B Wα φ a b j l)
        + ∑ a : Fin 3, ∑ j : Fin Q, ∑ l : Fin Q, B.coef K (u a) j l * couplingVelocityRow K B Ωα φ a j l := by
  set TS : Fin 3 → Fin 3 → ℕ → ℕ → ℝ × ℝ → ℂ := fun a b j l p => (p.1 : ℂ) * basisValue B j l p *
      ∑ i : Fin 3, (alternatingSymbol i b a : ℂ) *
        ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol i j' l' : ℂ) * Wα p j' * (starRingEnd ℂ) ((φ l').eval K p)
    with hTSdef
  set TV : Fin 3 → ℕ → ℕ → ℝ × ℝ → ℂ := fun a j l p => (p.1 : ℂ) * basisValue B j l p *
      ∑ j' : Fin 3, ∑ l' : Fin 3, (alternatingSymbol a j' l' : ℂ) * (starRingEnd ℂ) ((φ j').eval K p) * Ωα p l'
    with hTVdef
  have hTS : ∀ a b j l, IntegrableOn (TS a b j l) K.rect := fun a b j l =>
    strain_term_int K hK B Wα g hg hgW φ a b j l
  have hTV : ∀ a j l, IntegrableOn (TV a j l) K.rect := fun a j l =>
    velocity_term_int K B Ωα hΩm hΩb φ a j l
  have hP : ∀ a b p, K.proj Q Q (s a b) p
      = ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K (s a b) j l * basisValue B j l p := by
    intro a b p
    rw [LowVelocityExpansion.Internal.proj_expand K hB (hsi a b) Q Q p, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_range]
    rfl
  have hU : ∀ a p, K.proj (Q - 1) (Q - 1) (u a) p
      = ∑ j : Fin Q, ∑ l : Fin Q, B.coef K (u a) j l * basisValue B j l p := by
    intro a p
    rw [LowVelocityExpansion.Internal.proj_expand K hB (hui a) (Q - 1) (Q - 1) p]
    have e : Q - 1 + 1 = Q := by omega
    rw [e, Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_range]
    rfl
  have hpt : ∀ p : ℝ × ℝ, (p.1 : ℂ) * cdot3 (lowCoupling K Q Wα Ωα s u p) (testValue K φ p)
      = (∑ a : Fin 3, ∑ b : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1), B.coef K (s a b) j l * TS a b j l p)
        + ∑ a : Fin 3, ∑ j : Fin Q, ∑ l : Fin Q, B.coef K (u a) j l * TV a j l p := by
    intro p
    refine (low_expand (p.1 : ℂ) (fun a b => K.proj Q Q (s a b) p) (fun l => K.proj (Q - 1) (Q - 1) (u l) p)
      (Wα p) (Ωα p) (fun i => (starRingEnd ℂ) ((φ i).eval K p))).trans ?_
    congr 1
    · refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
      rw [hP a b p, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hTSdef]
      ring
    · refine Finset.sum_congr rfl fun a _ => ?_
      rw [hU a p, Finset.sum_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun l _ => ?_
      simp only [hTVdef]
      ring
  have iS : ∀ a, IntegrableOn (fun p => ∑ b : Fin 3, ∑ j : Fin (Q + 1), ∑ l : Fin (Q + 1),
      B.coef K (s a b) j l * TS a b j l p) K.rect := fun a =>
    integrable_finsetSum _ fun b _ => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ =>
      (hTS a b j l).const_mul _
  have iV : ∀ a, IntegrableOn (fun p => ∑ j : Fin Q, ∑ l : Fin Q, B.coef K (u a) j l * TV a j l p) K.rect :=
    fun a => integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (hTV a j l).const_mul _
  unfold rowPairing
  rw [show (fun p : ℝ × ℝ => (p.1 : ℂ) * cdot3 (lowCoupling K Q Wα Ωα s u p) (testValue K φ p)) = _ from funext hpt]
  rw [integral_add (integrable_finsetSum _ fun a _ => iS a) (integrable_finsetSum _ fun a _ => iV a),
    integral_finsetSum _ fun a _ => iS a, integral_finsetSum _ fun a _ => iV a]
  congr 1
  · refine Finset.sum_congr rfl fun a _ => ?_
    refine (int_fsum K.rect _ fun b => ?_).trans (Finset.sum_congr rfl fun b _ => ?_)
    · exact integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun l _ => (hTS a b j l).const_mul _
    refine (int_fsum K.rect _ fun j => ?_).trans (Finset.sum_congr rfl fun j _ => ?_)
    · exact integrable_finsetSum _ fun l _ => (hTS a b j l).const_mul _
    refine (int_fsum K.rect _ fun l => ?_).trans (Finset.sum_congr rfl fun l _ => ?_)
    · exact (hTS a b j l).const_mul _
    rw [integral_const_mul]
    rfl
  · refine Finset.sum_congr rfl fun a _ => ?_
    refine (int_fsum K.rect _ fun j => ?_).trans (Finset.sum_congr rfl fun j _ => ?_)
    · exact integrable_finsetSum _ fun l _ => (hTV a j l).const_mul _
    refine (int_fsum K.rect _ fun l => ?_).trans (Finset.sum_congr rfl fun l _ => ?_)
    · exact (hTV a j l).const_mul _
    rw [integral_const_mul]
    rfl

theorem sum_single_mode {s : Finset ℤ} {n : ℤ} (hs : s = {n}) {β : Type*} [AddCommMonoid β] (f : ↥s → β) (y : β)
    (hf : ∀ x : ↥s, (x : ℤ) = n → f x = y) : ∑ x, f x = y := by
  subst hs
  have e : ∀ x : ↥({n} : Finset ℤ), f x = y := fun x => hf x (Finset.mem_singleton.1 x.2)
  rw [Finset.sum_congr rfl fun x _ => e x, Finset.sum_const, Finset.card_univ, Fintype.card_coe,
    Finset.card_singleton, one_smul]

end Internal.RowCouplingLow

open Internal.RowCouplingLow

theorem rowCouplingLow_holds (h1 : HarmonicLiftStatement) : RowCouplingLowStatement := by
  intro m K B L hL v G H Pg hs hP ι' hmodes hax Wα Ωα hW hΩm hΩb φ
  obtain ⟨c, S, hco, -, hcl⟩ := hL
  have hK := hcl.box_valid
  have hB := hcl.bases_valid
  have hQ : 1 ≤ L.degCoef := by
    have := hcl.degSide_pos
    have := hcl.degSide_le
    omega
  have hord : L.order = m := hcl.order_eq.trans hco
  have hmode : harmonicMode (labelTime ι') ι'.1 = ι' := by
    unfold harmonicMode labelTime
    ext
    · rfl
    · simp only
      omega
  have heven : Even (ι'.1 + labelTime ι') := ⟨ι'.2, by unfold labelTime; ring⟩
  obtain ⟨hcF, hsF, hae⟩ := h1 m v G H hs (labelTime ι')
  have hae' := hae ι'.1 heven
  rw [hmode] at hae'
  have hr := ae_restrict_of_ae (μ := (volume : Measure (ℝ × ℝ))) (s := K.rect) hae'
  choose g hgc hgW using fun a => weighted_cont K L.degCoef Wα a (hW a)
  have hIc := fun a => localModeIntegrable m _ _ _ hcF K hK ι'.1 a
  have hIs := fun a => localModeIntegrable m _ _ _ hsF K hK ι'.1 a
  have hS := fun a b => coef_lift K B (F := fun p => gradAt m ι' G a b p) ((hIc a).2 b) ((hIs a).2 b)
    (by filter_upwards [hr, ae_rect_pos K hK] with p hp hp' using (hp hp').2.1 a b)
  have hV := fun a => coef_lift K B (F := fun p => velAt m ι' v a p)
    (Fc := fun p => modeVec m ι'.1 (harmonicCos (labelTime ι') v) p.1 p.2 a)
    (Fs := fun p => modeVec m ι'.1 (harmonicSin (labelTime ι') v) p.1 p.2 a) (hIc a).1 (hIs a).1
    (by filter_upwards [hr, ae_rect_pos K hK] with p hp hp' using (hp hp').1 a)
  rw [pairing_expand K hK B hB L.degCoef hQ _ _ (fun a b => (hS a b).2) (fun a => (hV a).2) Wα Ωα g hgc
    (fun a p hp => hgW a p hp) hΩm hΩb φ]
  obtain ⟨hbox, hbas⟩ := And.intro hcl.box_eq hcl.bases_eq
  subst hbox hbas hord
  simp only [Fintype.sum_sum_type, couplingRowVector, Sum.elim_inl, Sum.elim_inr, zero_mul,
    Finset.sum_const_zero, add_zero, Fintype.sum_prod_type, harmonicData, CellLayout.trueData,
    CellLayout.gradModeOf, cosTuple, sinTuple]
  congr 1
  · symm
    refine sum_single_mode hmodes _ _ fun x hx => ?_
    rw [hx]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun j _ =>
      Finset.sum_congr rfl fun l _ => ?_
    exact (mul_comm _ _).trans (congrArg (· * _) ((hS a b).1 j l))
  · symm
    refine sum_single_mode hmodes _ _ fun x hx => ?_
    rw [hx]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    exact (mul_comm _ _).trans (congrArg (· * _) ((hV a).1 j l))

end CellCalculus

end CertCell

end Breakdown
