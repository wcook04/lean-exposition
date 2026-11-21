import Breakdown.CertCell.AssemblyPotentialParts
import Breakdown.CertCell.HarmonicProfiles
import Breakdown.CertCell.PeriodicSecondOrder
import Breakdown.CertCell.SecondDerivEnergyIdentity
import Breakdown.CertCell.VelocitySixthIntegral
import Breakdown.CertCell.SixthPower
import Breakdown.CertCell.RowLowPartLift
import Breakdown.FracCell.LowVelocityExpansion
import Breakdown.CertCell.LeafDensityLower
import Breakdown.CertCell.LeafNorms
import Breakdown.CertCell.LabelModeFacts
import Breakdown.FracCell.SharpYChargeRegular

open MeasureTheory Matrix
open scoped ENNReal ComplexOrder

noncomputable section

namespace Breakdown.CertCell.Assembly

open CellCert CellCert.CellAnalysis CellCert.CellFormula CellCert.CellEnergy CellCalculus

namespace Internal.PotentialLeaf

theorem pairVec_split (s s₁ : Fin 3 → Fin 3 → ℂ) (w w₁ : Fin 3 → ℂ) :
    pairVec s w = pairVec s₁ w₁ + pairVec (fun a b => s a b - s₁ a b) (fun a => w a - w₁ a) := by
  funext i
  simp only [pairVec, Pi.add_apply]
  split_ifs <;> ring

theorem pairVec_grad (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) (a b : Fin 3) :
    pairVec s w ⟨3 * a.val + b.val, by omega⟩ = s a b := by
  have ha := a.isLt
  have hb := b.isLt
  unfold pairVec
  rw [dif_pos (by simp only; omega)]
  congr 1
  · exact Fin.ext (by simp only; omega)
  · exact Fin.ext (by simp only; omega)

theorem pairVec_vel (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) (a : Fin 3) :
    pairVec s w ⟨9 + a.val, by omega⟩ = w a := by
  unfold pairVec
  rw [dif_neg (by simp only; omega)]
  congr 1
  exact Fin.ext (by simp only; omega)

theorem norms_pairVec (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    ∑ j, ‖pairVec s w j‖ ^ 2 = sumSq s + vecSq w := by
  simp [Fin.sum_univ_succ, pairVec, sumSq, vecSq]
  ring

theorem sum_single (L : CellLayout) {n₀ : ℤ} (hmodes : L.modes = {n₀}) {β : Type*} [AddCommMonoid β]
    (f : L.modes → β) : ∑ n, f n = f ⟨n₀, by rw [hmodes]; exact Finset.mem_singleton_self n₀⟩ := by
  refine Fintype.sum_eq_single _ (fun n hn => ?_)
  exfalso
  apply hn
  have h2 : (n : ℤ) ∈ ({n₀} : Finset ℤ) := hmodes ▸ n.2
  exact Subtype.ext (Finset.mem_singleton.1 h2)

theorem weight_continuous (K : CellBox) : Continuous K.lineWeight := by
  unfold CellBox.lineWeight
  split_ifs
  · exact continuous_id
  · exact continuous_const

theorem coef_lift {K : CellBox} (B : CellBases) {F₁ F₂ F : ℝ × ℝ → ℂ}
    (h₁ : IntegrableOn F₁ K.rect) (h₂ : IntegrableOn F₂ K.rect)
    (hF : ∀ᵐ p ∂(volume.restrict K.rect), F p = F₁ p + Complex.I * F₂ p) (j l : ℕ) :
    B.coef K F₁ j l + Complex.I * B.coef K F₂ j l = B.coef K F j l := by
  set g : ℝ × ℝ → ℂ := fun p => (K.lineWeight p.1 : ℂ) * ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)
    with hg
  have hc : ContinuousOn g K.rect := by
    refine Continuous.continuousOn ?_
    have c1 : Continuous (fun p : ℝ × ℝ => ((K.lineWeight p.1 : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp ((weight_continuous K).comp continuous_fst)
    have c2 : Continuous (fun p : ℝ × ℝ => ((B.radialPoly j p.1 * B.heightPoly l p.2 : ℝ) : ℂ)) :=
      CellCert.CellEnergy.TopFormInternal.basisC_cont B j l
    exact c1.mul c2
  have i₁ := h₁.mul_continuousOn hc (RowLow.Internal.rect_compact K)
  have i₂ := (h₂.mul_continuousOn hc (RowLow.Internal.rect_compact K)).const_mul Complex.I
  have e : ∀ F' : ℝ × ℝ → ℂ, B.coef K F' j l = ∫ p in K.rect, F' p * g p := by
    intro F'
    unfold CellBases.coef
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hg]
    ring
  rw [e, e, e, ← integral_const_mul, ← integral_add i₁ i₂]
  refine integral_congr_ae ?_
  filter_upwards [hF] with p hp
  rw [hp]
  ring

section Low

variable {k : ℕ} {C : Type} {nE nM : ℕ} (D : CellLayerData k C nE nM) (R : CellCalculusEntry D)

theorem low_grad_eq (hC : CellCalculusConditions D R) {K : Fin D.mesh.count} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsPeriodicSecondOrder v G H) (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K) (p : ℝ × ℝ) (a b : Fin 3) :
    lowGrad D R K ⟨ι, hι⟩ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) p a b
      = (D.mesh.box K).proj ((R.layouts K).layout ι).degCoef ((R.layouts K).layout ι).degCoef
          (fun p' => gradAt D.azimuthOrder ι G a b p') p := by
  obtain ⟨c₀, S₀, hord, hres, hL⟩ := (hC.layouts_valid K).layout_valid ι hι
  have hmodes : ((R.layouts K).layout ι).modes = {ι.1} := hL.modes_eq.trans hres
  have hK : IsCellBox (D.mesh.box K) := hL.box_valid
  have hB : IsCellBases (D.mesh.box K) (R.layouts K).bases := hL.bases_valid
  have ho : ((R.layouts K).layout ι).order = D.azimuthOrder := hL.order_eq.trans hord
  obtain ⟨hc, hs, -⟩ := harmonicLift_holds D.azimuthOrder v G H hv (labelTime ι)
  have hw : ContinuousOn (fun p' : ℝ × ℝ => (((D.mesh.box K).lineWeight p'.1 : ℝ) : ℂ)) (D.mesh.box K).rect :=
    (Complex.continuous_ofReal.comp ((weight_continuous _).comp continuous_fst)).continuousOn
  have hint : IntegrableOn (fun p' => ((D.mesh.box K).lineWeight p'.1 : ℂ) * gradAt D.azimuthOrder ι G a b p')
      (D.mesh.box K).rect :=
    (RowLow.Internal.gradAt_int harmonicLift_holds hv D.azimuthOrder ι hK a b).continuousOn_mul hw
      (RowLow.Internal.rect_compact _)
  rw [CellCert.CellEnergy.LowVelocityExpansion.Internal.proj_expand (D.mesh.box K) hB hint, Finset.sum_range]
  unfold lowGrad
  rw [sum_single _ hmodes]
  unfold lowStrainOf
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine congrArg₂ (· * ·) ?_ ?_
  · show ((R.layouts K).layout ι).bases.coef ((R.layouts K).layout ι).box
          (gradMode ((R.layouts K).layout ι).order ι.1 (harmonicCos (labelTime ι) G) a b) j l
        + Complex.I * ((R.layouts K).layout ι).bases.coef ((R.layouts K).layout ι).box
          (gradMode ((R.layouts K).layout ι).order ι.1 (harmonicSin (labelTime ι) G) a b) j l = _
    rw [hL.box_eq, hL.bases_eq, ho]
    refine coef_lift _ (RowLow.Internal.grad_int hc _ _ a b hK) (RowLow.Internal.grad_int hs _ _ a b hK) ?_ j l
    filter_upwards [RowLow.Internal.lift_rect harmonicLift_holds hv D.azimuthOrder ι hK] with p hp
    exact hp.2.1 a b
  · rw [hL.bases_eq]
    rfl

theorem low_vel_eq (hC : CellCalculusConditions D R) {K : Fin D.mesh.count} {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsPeriodicSecondOrder v G H) (Pg : ℝ → Space → Space) (κ ζ : Fin k → ℝ)
    (η : Fin (R.portCount K) → ℂ) {ι : ℤ × ℤ} (hι : ι ∈ D.mesh.resolved K) (p : ℝ × ℝ) (a : Fin 3) :
    lowVel D R K ⟨ι, hι⟩ (cellState D.mesh K (R.layouts K) v G H Pg κ ζ η) p a
      = (D.mesh.box K).proj (((R.layouts K).layout ι).degCoef - 1) (((R.layouts K).layout ι).degCoef - 1)
          (fun p' => velAt D.azimuthOrder ι v a p') p := by
  obtain ⟨c₀, S₀, hord, hres, hL⟩ := (hC.layouts_valid K).layout_valid ι hι
  have hmodes : ((R.layouts K).layout ι).modes = {ι.1} := hL.modes_eq.trans hres
  have hK : IsCellBox (D.mesh.box K) := hL.box_valid
  have hB : IsCellBases (D.mesh.box K) (R.layouts K).bases := hL.bases_valid
  have ho : ((R.layouts K).layout ι).order = D.azimuthOrder := hL.order_eq.trans hord
  have hQ : ((R.layouts K).layout ι).degCoef - 1 + 1 = ((R.layouts K).layout ι).degCoef := by
    have h1 := hL.degSide_pos
    have h2 := hL.degSide_le
    omega
  obtain ⟨hc, hs, -⟩ := harmonicLift_holds D.azimuthOrder v G H hv (labelTime ι)
  have hw : ContinuousOn (fun p' : ℝ × ℝ => (((D.mesh.box K).lineWeight p'.1 : ℝ) : ℂ)) (D.mesh.box K).rect :=
    (Complex.continuous_ofReal.comp ((weight_continuous _).comp continuous_fst)).continuousOn
  have hint : IntegrableOn (fun p' => ((D.mesh.box K).lineWeight p'.1 : ℂ) * velAt D.azimuthOrder ι v a p')
      (D.mesh.box K).rect :=
    (RowLow.Internal.velAt_int harmonicLift_holds hv D.azimuthOrder ι hK a).continuousOn_mul hw
      (RowLow.Internal.rect_compact _)
  rw [CellCert.CellEnergy.LowVelocityExpansion.Internal.proj_expand (D.mesh.box K) hB hint, hQ, Finset.sum_range]
  unfold lowVel
  rw [sum_single _ hmodes]
  unfold lowVelocityOf
  refine Finset.sum_congr rfl (fun j _ => ?_)
  rw [Finset.sum_range]
  refine Finset.sum_congr rfl (fun l _ => ?_)
  refine congrArg₂ (· * ·) ?_ ?_
  · show ((R.layouts K).layout ι).bases.coef ((R.layouts K).layout ι).box
          (fun p => modeVec ((R.layouts K).layout ι).order ι.1 (harmonicCos (labelTime ι) v) p.1 p.2 a) j l
        + Complex.I * ((R.layouts K).layout ι).bases.coef ((R.layouts K).layout ι).box
          (fun p => modeVec ((R.layouts K).layout ι).order ι.1 (harmonicSin (labelTime ι) v) p.1 p.2 a) j l = _
    rw [hL.box_eq, hL.bases_eq, ho]
    refine coef_lift _ (RowLow.Internal.vel_int hc _ _ a hK) (RowLow.Internal.vel_int hs _ _ a hK) ?_ j l
    filter_upwards [RowLow.Internal.lift_rect harmonicLift_holds hv D.azimuthOrder ι hK] with p hp
    exact hp.1 a
  · rw [hL.bases_eq]
    rfl

end Low


theorem sesq_norm_le (M : Matrix (Fin 12) (Fin 12) ℂ) (U : Fin 12 → ℂ) (c : ℝ) (hc : ∀ i j, ‖M i j‖ ≤ c) :
    ‖sesq12 M U U‖ ≤ 144 * c * ∑ j, ‖U j‖ ^ 2 := by
  have hS : ∀ i, ‖U i‖ ^ 2 ≤ ∑ j, ‖U j‖ ^ 2 := fun i =>
    Finset.single_le_sum (f := fun j => ‖U j‖ ^ 2) (fun j _ => by positivity) (Finset.mem_univ i)
  have hc0 : 0 ≤ c := (norm_nonneg _).trans (hc 0 0)
  have hterm : ∀ i j, ‖(starRingEnd ℂ) (U i) * M i j * U j‖ ≤ c * ∑ m, ‖U m‖ ^ 2 := by
    intro i j
    rw [norm_mul, norm_mul, Complex.norm_conj]
    have h1 := hS i
    have h2 := hS j
    have hij : ‖U i‖ * ‖U j‖ ≤ ∑ m, ‖U m‖ ^ 2 := by
      nlinarith [norm_nonneg (U i), norm_nonneg (U j), sq_nonneg (‖U i‖ - ‖U j‖)]
    calc ‖U i‖ * ‖M i j‖ * ‖U j‖ = ‖M i j‖ * (‖U i‖ * ‖U j‖) := by ring
      _ ≤ c * ∑ m, ‖U m‖ ^ 2 := mul_le_mul (hc i j) hij (by positivity) hc0
  unfold sesq12
  calc ‖∑ i, ∑ j, (starRingEnd ℂ) (U i) * M i j * U j‖
      ≤ ∑ i, ∑ j, ‖(starRingEnd ℂ) (U i) * M i j * U j‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
    _ ≤ ∑ _i : Fin 12, ∑ _j : Fin 12, c * ∑ m, ‖U m‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hterm i j
    _ = 144 * c * ∑ j, ‖U j‖ ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        push_cast
        ring

theorem sesq_integrable {S : Set (ℝ × ℝ)} (hS : MeasurableSet S) (h0 : ∀ p ∈ S, 0 ≤ p.1)
    {U : ℝ × ℝ → Fin 12 → ℂ} (hU : ∀ j, AEStronglyMeasurable (fun p => U p j) (volume.restrict S))
    (hI : IntegrableOn (fun p => p.1 * ∑ j, ‖U p j‖ ^ 2) S)
    {M : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : ∀ i j, AEStronglyMeasurable (fun p => M p i j) (volume.restrict S))
    {c : ℝ} (hc : ∀ p ∈ S, ∀ i j, ‖M p i j‖ ≤ c) :
    IntegrableOn (fun p => (p.1 : ℂ) * sesq12 (M p) (U p) (U p)) S := by
  refine (hI.const_mul (144 * c)).mono' ?_ ?_
  · refine (Complex.continuous_ofReal.comp continuous_fst).aestronglyMeasurable.mul ?_
    unfold sesq12
    exact Finset.aestronglyMeasurable_fun_sum _ fun i _ => Finset.aestronglyMeasurable_fun_sum _ fun j _ =>
      ((Complex.continuous_conj.comp_aestronglyMeasurable (hU i)).mul (hM i j)).mul (hU j)
  · filter_upwards [ae_restrict_mem hS] with p hp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (h0 p hp)]
    calc p.1 * ‖sesq12 (M p) (U p) (U p)‖ ≤ p.1 * (144 * c * ∑ j, ‖U p j‖ ^ 2) :=
          mul_le_mul_of_nonneg_left (sesq_norm_le _ _ c (hc p hp)) (h0 p hp)
      _ = 144 * c * (p.1 * ∑ j, ‖U p j‖ ^ 2) := by ring

theorem box_bound (T : LeafValues) (ι : ℤ × ℤ) (s : Fin 3 → Fin 3 → ℂ) (w : Fin 3 → ℂ) :
    |T.boxPenalty ι s w| ≤ (27 * |T.boxCurl ι| + |T.boxStrain ι| + |T.boxVelocity ι|) * ∑ j, ‖pairVec s w j‖ ^ 2 := by
  rw [norms_pairVec]
  unfold LeafValues.boxPenalty
  have h1 : 0 ≤ curlSq s := Finset.sum_nonneg fun _ _ => by positivity
  have h2 : 0 ≤ sumSq s := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
  have h3 : 0 ≤ vecSq w := Finset.sum_nonneg fun _ _ => by positivity
  have h4 := SharpYChargeRegular.Internal.curlSq_le s
  have a1 := abs_nonneg (T.boxCurl ι)
  have a2 := abs_nonneg (T.boxStrain ι)
  have a3 := abs_nonneg (T.boxVelocity ι)
  have b1 : |T.boxCurl ι * curlSq s| ≤ 27 * |T.boxCurl ι| * sumSq s := by
    rw [abs_mul, abs_of_nonneg h1]
    nlinarith
  have b2 : |T.boxStrain ι * sumSq s| ≤ |T.boxStrain ι| * sumSq s := by rw [abs_mul, abs_of_nonneg h2]
  have b3 : |T.boxVelocity ι * vecSq w| ≤ |T.boxVelocity ι| * vecSq w := by rw [abs_mul, abs_of_nonneg h3]
  have t1 := abs_add_le (T.boxCurl ι * curlSq s + T.boxStrain ι * sumSq s) (T.boxVelocity ι * vecSq w)
  have t2 := abs_add_le (T.boxCurl ι * curlSq s) (T.boxStrain ι * sumSq s)
  nlinarith [mul_nonneg a1 h3, mul_nonneg a2 h3, mul_nonneg a3 h2]

theorem enorm_le_split (t : ℝ) : ‖t‖ₑ ≤ ENNReal.ofReal t + ENNReal.ofReal (-t) := by
  rw [Real.enorm_eq_ofReal_abs]
  rcases le_total 0 t with h | h
  · rw [abs_of_nonneg h]
    exact le_self_add
  · rw [abs_of_nonpos h]
    exact le_add_self

theorem curl_as_sum (s : Fin 3 → Fin 3 → ℂ) (i : Fin 3) :
    curlComp s i = ∑ a : Fin 3, ∑ b : Fin 3, ((CellCert.permSign i b a : ℝ) : ℂ) * s a b := by
  unfold curlComp
  exact Finset.sum_comm

theorem single_sum (f : Fin 3 → Fin 3 → ℂ) (a b : Fin 3) :
    ∑ a' : Fin 3, ∑ b' : Fin 3, (if a' = a ∧ b' = b then (1 : ℂ) else 0) * f a' b' = f a b := by
  simp [ite_and]

theorem slope_integrable {B : CellBox} (hK : IsCellBox B) (m : ℕ) {v : ℝ → Space → Space}
    {G : ℝ → Space → (Space →L[ℝ] Space)} {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)}
    (hv : IsPeriodicSecondOrder v G H) (ι : ℤ × ℤ) :
    IntegrableOn (fun p => p.1 * slopeSq m ι H p) B.rect ∧
      IntegrableOn (fun p => p.1 * curlSlopeSq m ι H p) B.rect := by
  have hmeas : MeasurableSet B.rect := RowLow.Internal.rect_meas _
  have hLM := labelModeFacts_holds harmonicLift_holds B hK m v G H hv ι
  have hslope : ∀ a b c, IntegrableOn (fun p => p.1 * ‖slopeAt m ι H a b c p‖ ^ 2) B.rect := by
    intro a b c
    obtain ⟨-, -, h3, -⟩ := hLM (fun a' b' => if a' = a ∧ b' = b then (1 : ℂ) else 0)
    refine (h3 c).2.congr_fun (fun p _ => ?_) hmeas
    simp only
    rw [single_sum (fun a' b' => slopeAt m ι H a' b' c p) a b]
  have hcurl : ∀ i c, IntegrableOn
      (fun p => p.1 * ‖curlComp (fun a b => slopeAt m ι H a b c p) i‖ ^ 2) B.rect := by
    intro i c
    obtain ⟨-, -, h3, -⟩ := hLM (fun a b => ((CellCert.permSign i b a : ℝ) : ℂ))
    refine (h3 c).2.congr_fun (fun p _ => ?_) hmeas
    simp only
    rw [curl_as_sum]
  constructor
  · refine (integrable_finset_sum Finset.univ fun a _ => integrable_finset_sum Finset.univ fun b _ =>
      integrable_finset_sum Finset.univ fun c _ => hslope a b c).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [slopeSq, Finset.mul_sum]
  · refine (integrable_finset_sum Finset.univ fun i _ => integrable_finset_sum Finset.univ fun c _ => hcurl i c).congr
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [curlSlopeSq, Finset.mul_sum]

section Leaf

variable {k : ℕ} {C : Type} {nE nM : ℕ} {D : CellLayerData k C nE nM} {R : CellCalculusEntry D}
  {K : Fin D.mesh.count} {q : Fin k → ℝ} {v : ℝ → Space → Space} {G : ℝ → Space → (Space →L[ℝ] Space)}
  {H : ℝ → Space → (Space →L[ℝ] Space →L[ℝ] Space)} {g : ℝ → Space → Space} {κ : Fin k → ℝ}
  {Fs Pg : ℝ → Space → Space}

theorem array_measurable (hT : TrueFieldRegular D) (ht : IsCellTuple D K q v G H g κ Fs Pg) (ι : ℤ × ℤ) :
    AEStronglyMeasurable (fun p => gradArray D.azimuthOrder ι G p) (volume.restrict (D.mesh.box K).rect) ∧
      AEStronglyMeasurable (fun p => velArray D.azimuthOrder ι v p) (volume.restrict (D.mesh.box K).rect) := by
  have hU := ((hT.1 K q v G H g κ Fs Pg ht).1 ι).1
  have mG : ∀ a b, AEStronglyMeasurable (fun p => gradAt D.azimuthOrder ι G a b p)
      (volume.restrict (D.mesh.box K).rect) := fun a b =>
    (hU ⟨3 * a.val + b.val, by omega⟩).congr (Filter.Eventually.of_forall fun p =>
      pairVec_grad (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p) a b)
  have mV : ∀ a, AEStronglyMeasurable (fun p => velAt D.azimuthOrder ι v a p)
      (volume.restrict (D.mesh.box K).rect) := fun a =>
    (hU ⟨9 + a.val, by omega⟩).congr (Filter.Eventually.of_forall fun p =>
      pairVec_vel (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p) a)
  exact ⟨(aemeasurable_pi_iff.2 fun a => aemeasurable_pi_iff.2 fun b => (mG a b).aemeasurable).aestronglyMeasurable,
    (aemeasurable_pi_iff.2 fun a => (mV a).aemeasurable).aestronglyMeasurable⟩

theorem curlSq_continuous : Continuous (fun s : Fin 3 → Fin 3 → ℂ => curlSq s) := by
  unfold curlSq curlComp
  fun_prop

theorem sumSq_continuous : Continuous (fun s : Fin 3 → Fin 3 → ℂ => sumSq s) := by
  unfold sumSq
  fun_prop

theorem vecSq_continuous : Continuous (fun w : Fin 3 → ℂ => vecSq w) := by
  unfold vecSq
  fun_prop

theorem box_integrable (hK : IsCellBox (D.mesh.box K)) (hT : TrueFieldRegular D)
    (ht : IsCellTuple D K q v G H g κ Fs Pg) (ι : ℤ × ℤ) (T : LeafValues) :
    IntegrableOn (fun p => p.1 * T.boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p))
      (D.mesh.box K).rect := by
  have hmeas : MeasurableSet (D.mesh.box K).rect := RowLow.Internal.rect_meas _
  have hI := ((hT.1 K q v G H g κ Fs Pg ht).1 ι).2
  obtain ⟨mGA, mVA⟩ := array_measurable hT ht ι
  have c1 : AEStronglyMeasurable (fun p => curlSq (gradArray D.azimuthOrder ι G p))
      (volume.restrict (D.mesh.box K).rect) := curlSq_continuous.comp_aestronglyMeasurable mGA
  have c2 : AEStronglyMeasurable (fun p => sumSq (gradArray D.azimuthOrder ι G p))
      (volume.restrict (D.mesh.box K).rect) := sumSq_continuous.comp_aestronglyMeasurable mGA
  have c3 : AEStronglyMeasurable (fun p => vecSq (velArray D.azimuthOrder ι v p))
      (volume.restrict (D.mesh.box K).rect) := vecSq_continuous.comp_aestronglyMeasurable mVA
  have m2 : AEStronglyMeasurable (fun p => T.boxPenalty ι (gradArray D.azimuthOrder ι G p)
      (velArray D.azimuthOrder ι v p)) (volume.restrict (D.mesh.box K).rect) := by
    unfold LeafValues.boxPenalty
    exact ((c1.const_mul _).add (c2.const_mul _)).add (c3.const_mul _)
  have m1 : AEStronglyMeasurable (fun p : ℝ × ℝ => p.1) (volume.restrict (D.mesh.box K).rect) :=
    continuous_fst.aestronglyMeasurable
  have m3 : AEStronglyMeasurable (fun p => p.1 * T.boxPenalty ι (gradArray D.azimuthOrder ι G p)
      (velArray D.azimuthOrder ι v p)) (volume.restrict (D.mesh.box K).rect) := m1.mul m2
  refine (hI.const_mul (27 * |T.boxCurl ι| + |T.boxStrain ι| + |T.boxVelocity ι|)).mono' m3 ?_
  filter_upwards [ae_restrict_mem hmeas] with p hp
  have h0 : 0 ≤ p.1 := hK.r_order.1.trans hp.1.1
  have hb := box_bound T ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)
  have hn : ‖p.1 * T.boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)‖
      = p.1 * |T.boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)| := by
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg h0]
  have hq : ∑ j, ‖bandProfile D ι v G p j‖ ^ 2
      = ∑ j, ‖pairVec (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p) j‖ ^ 2 := rfl
  rw [hn, hq]
  calc p.1 * |T.boxPenalty ι (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p)|
      ≤ p.1 * ((27 * |T.boxCurl ι| + |T.boxStrain ι| + |T.boxVelocity ι|) * ∑ j, ‖pairVec (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p) j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hb h0
    _ = (27 * |T.boxCurl ι| + |T.boxStrain ι| + |T.boxVelocity ι|) * (p.1 * ∑ j, ‖pairVec (gradArray D.azimuthOrder ι G p) (velArray D.azimuthOrder ι v p) j‖ ^ 2) := by
        ring

theorem pair_integrable (hK : IsCellBox (D.mesh.box K)) (hT : TrueFieldRegular D)
    (ht : IsCellTuple D K q v G H g κ Fs Pg) (ι : ℤ × ℤ) {M : ℝ × ℝ → Matrix (Fin 12) (Fin 12) ℂ}
    (hM : ∀ i j, Measurable (fun p => M p i j)) {c : ℝ} (hc : ∀ p ∈ (D.mesh.box K).rect, ∀ i j, ‖M p i j‖ ≤ c) :
    IntegrableOn (fun p => p.1 * (sesq12 (M p) (trueProfiles D v G ι p) (trueProfiles D v G ι p)).re)
      (D.mesh.box K).rect := by
  obtain ⟨hU, hI⟩ := (hT.1 K q v G H g κ Fs Pg ht).1 ι
  have h := (sesq_integrable (RowLow.Internal.rect_meas _) (fun p hp => hK.r_order.1.trans hp.1.1) hU hI
    (fun i j => (hM i j).aestronglyMeasurable) hc).re
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul]
  rfl

theorem density_integrable (hT : TrueFieldRegular D) (hF : CellPiecesFinite D R)
    (ht : IsCellTuple D K q v G H g κ Fs Pg) (ι : ℤ × ℤ) :
    IntegrableOn (fun p => D.labelDensity q v G H ι p * p.1) (D.mesh.box K).rect := by
  have hdm := (hT.2.1 q ht.param v G H g ht.perturbation K).1 ι
  have hfm : AEStronglyMeasurable (fun p => D.labelDensity q v G H ι p * p.1)
      (volume.restrict (D.mesh.box K).rect) := hdm.mul continuous_fst.aestronglyMeasurable
  refine ⟨hfm, ?_⟩
  have hpos : ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1) < ⊤ := by
    have hp := ht.pos_finite
    unfold cellPos at hp
    exact lt_of_le_of_lt ((ENNReal.le_tsum (f := fun ι : ℤ × ℤ => ∫⁻ p in (D.mesh.box K).rect,
      ENNReal.ofReal (D.labelDensity q v G H ι p * p.1)) ι).trans le_self_add) hp
  have hneg : ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)) < ⊤ := by
    have hn := (hF K q v G H g κ Fs Pg ht).1
    unfold cellNeg at hn
    exact lt_of_le_of_lt ((ENNReal.le_tsum (f := fun ι : ℤ × ℤ => ∫⁻ p in (D.mesh.box K).rect,
      ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1))) ι).trans le_self_add) hn
  unfold HasFiniteIntegral
  calc ∫⁻ p in (D.mesh.box K).rect, ‖D.labelDensity q v G H ι p * p.1‖ₑ
      ≤ ∫⁻ p in (D.mesh.box K).rect, (ENNReal.ofReal (D.labelDensity q v G H ι p * p.1)
        + ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1))) :=
        lintegral_mono fun p => enorm_le_split _
    _ = (∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (D.labelDensity q v G H ι p * p.1))
        + ∫⁻ p in (D.mesh.box K).rect, ENNReal.ofReal (-(D.labelDensity q v G H ι p * p.1)) :=
        lintegral_add_left' hfm.aemeasurable.ennreal_ofReal _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hpos, hneg⟩

end Leaf

end Internal.PotentialLeaf

end Breakdown.CertCell.Assembly
