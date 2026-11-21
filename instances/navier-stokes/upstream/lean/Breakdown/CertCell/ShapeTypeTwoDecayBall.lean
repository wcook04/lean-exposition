import Breakdown.CertCell.ShapeStatements

open scoped ContDiff

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

namespace Internal

variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def SlopeOn (f : Space → E) (K : ℝ) (s : Set Space) : Prop :=
  ∀ z ∈ s, ∀ w ∈ s, ‖f z - f w‖ ≤ K * ‖z - w‖

theorem slopeOn_of_fderiv {f : Space → E} {y : Space} {K : ℝ}
    (hd : ∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ f z) (hb : ∀ z ∈ Metric.ball y 1, ‖fderiv ℝ f z‖ ≤ K) :
    SlopeOn f K (Metric.ball y 1) := fun _ hz _ hw =>
  (convex_ball y 1).norm_image_sub_le_of_norm_fderiv_le hd hb hw hz

theorem SlopeOn.mono {f : Space → E} {K K' : ℝ} {s : Set Space} (h : SlopeOn f K s) (hK : K ≤ K') :
    SlopeOn f K' s := fun z hz w hw =>
  (h z hz w hw).trans (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

theorem SlopeOn.add {f g : Space → E} {K1 K2 : ℝ} {s : Set Space} (hf : SlopeOn f K1 s) (hg : SlopeOn g K2 s) :
    SlopeOn (fun z => f z + g z) (K1 + K2) s := fun z hz w hw => by
  have e : f z + g z - (f w + g w) = (f z - f w) + (g z - g w) := by abel
  rw [e, add_mul]
  exact (norm_add_le _ _).trans (add_le_add (hf z hz w hw) (hg z hz w hw))

theorem SlopeOn.congr {f g : Space → E} {K : ℝ} {s : Set Space} (h : SlopeOn g K s) (he : ∀ z ∈ s, f z = g z) :
    SlopeOn f K s := fun z hz w hw => by
  rw [he z hz, he w hw]
  exact h z hz w hw

theorem SlopeOn.bilin (B : E →L[ℝ] F →L[ℝ] G) (hB : ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) {f : Space → E} {g : Space → F}
    {K1 K2 M1 M2 : ℝ} {s : Set Space} (hf : SlopeOn f K1 s) (hg : SlopeOn g K2 s)
    (hf0 : ∀ z ∈ s, ‖f z‖ ≤ M1) (hg0 : ∀ z ∈ s, ‖g z‖ ≤ M2) :
    SlopeOn (fun z => B (f z) (g z)) (K1 * M2 + M1 * K2) s := fun z hz w hw => by
  have e : B (f z) (g z) - B (f w) (g w) = B (f z - f w) (g z) + B (f w) (g z - g w) := by
    simp only [map_sub, sub_apply]
    abel
  rw [e]
  have h1 := hf z hz w hw
  have h2 := hg z hz w hw
  have n1 := hg0 z hz
  have n2 := hf0 w hw
  calc ‖B (f z - f w) (g z) + B (f w) (g z - g w)‖ ≤ ‖f z - f w‖ * ‖g z‖ + ‖f w‖ * ‖g z - g w‖ :=
        (norm_add_le _ _).trans (add_le_add (hB _ _) (hB _ _))
    _ ≤ (K1 * ‖z - w‖) * M2 + M1 * (K2 * ‖z - w‖) :=
        add_le_add (mul_le_mul h1 n1 (norm_nonneg _) ((norm_nonneg _).trans h1))
          (mul_le_mul n2 h2 (norm_nonneg _) ((norm_nonneg _).trans n2))
    _ = (K1 * M2 + M1 * K2) * ‖z - w‖ := by ring

structure BallBound (f : Space → E) (y : Space) (v d l : ℝ) : Prop where
  diff : ∀ z ∈ Metric.ball y 1, DifferentiableAt ℝ f z
  val : ∀ z ∈ Metric.ball y 1, ‖f z‖ ≤ v
  der : ∀ z ∈ Metric.ball y 1, ‖fderiv ℝ f z‖ ≤ d
  slope : SlopeOn (fderiv ℝ f) l (Metric.ball y 1)

theorem BallBound.mono {f : Space → E} {y : Space} {v d l v' d' l' : ℝ} (h : BallBound f y v d l)
    (hv : v ≤ v') (hd : d ≤ d') (hl : l ≤ l') : BallBound f y v' d' l' :=
  ⟨h.diff, fun z hz => (h.val z hz).trans hv, fun z hz => (h.der z hz).trans hd, h.slope.mono hl⟩

theorem BallBound.add {f g : Space → E} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ} (hf : BallBound f y v1 d1 l1)
    (hg : BallBound g y v2 d2 l2) : BallBound (fun z => f z + g z) y (v1 + v2) (d1 + d2) (l1 + l2) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => f z + g z) z = fderiv ℝ f z + fderiv ℝ g z :=
    fun z hz => fderiv_add (hf.diff z hz) (hg.diff z hz)
  refine ⟨fun z hz => (hf.diff z hz).add (hg.diff z hz), fun z hz => (norm_add_le _ _).trans
    (add_le_add (hf.val z hz) (hg.val z hz)), fun z hz => ?_, (hf.slope.add hg.slope).congr hD⟩
  rw [hD z hz]
  exact (norm_add_le _ _).trans (add_le_add (hf.der z hz) (hg.der z hz))

theorem BallBound.neg {f : Space → E} {y : Space} {v d l : ℝ} (hf : BallBound f y v d l) :
    BallBound (fun z => -f z) y v d l := by
  have hD : ∀ z, fderiv ℝ (fun z => -f z) z = -fderiv ℝ f z := fun z => fderiv_neg
  refine ⟨fun z hz => (hf.diff z hz).neg, fun z hz => by rw [norm_neg]; exact hf.val z hz,
    fun z hz => by rw [hD, norm_neg]; exact hf.der z hz, fun z hz w hw => ?_⟩
  rw [hD, hD, neg_sub_neg, norm_sub_rev]
  exact hf.slope z hz w hw

theorem BallBound.bilin (B : E →L[ℝ] F →L[ℝ] G) (hB : ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) {f : Space → E}
    {g : Space → F} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ} (hf : BallBound f y v1 d1 l1)
    (hg : BallBound g y v2 d2 l2) :
    BallBound (fun z => B (f z) (g z)) y (v1 * v2) (v1 * d2 + d1 * v2)
      (d1 * d2 + v1 * l2 + (l1 * v2 + d1 * d2)) := by
  have hBu : ∀ u, ‖B u‖ ≤ ‖u‖ := fun u =>
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg u) fun v => hB u v
  have hR : ∀ u (T : Space →L[ℝ] F), ‖B.precompR Space u T‖ ≤ ‖u‖ * ‖T‖ := by
    intro u T
    rw [ContinuousLinearMap.precompR_apply, ContinuousLinearMap.compL_apply]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul_of_nonneg_right (hBu u) (norm_nonneg _))
  have hL : ∀ (T : Space →L[ℝ] E) v, ‖B.precompL Space T v‖ ≤ ‖T‖ * ‖v‖ := by
    intro T v
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
    rw [ContinuousLinearMap.precompL_apply]
    calc ‖B (T h) v‖ ≤ ‖T h‖ * ‖v‖ := hB _ _
      _ ≤ (‖T‖ * ‖h‖) * ‖v‖ := mul_le_mul_of_nonneg_right (T.le_opNorm h) (norm_nonneg _)
      _ = ‖T‖ * ‖v‖ * ‖h‖ := by ring
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => B (f z) (g z)) z =
      B.precompR Space (f z) (fderiv ℝ g z) + B.precompL Space (fderiv ℝ f z) (g z) :=
    fun z hz => B.fderiv_of_bilinear (hf.diff z hz) (hg.diff z hz)
  refine ⟨fun z hz => (B.hasFDerivAt_of_bilinear (hf.diff z hz).hasFDerivAt
      (hg.diff z hz).hasFDerivAt).differentiableAt, fun z hz => ?_, fun z hz => ?_, ?_⟩
  · exact (hB _ _).trans (mul_le_mul (hf.val z hz) (hg.val z hz) (norm_nonneg _)
      ((norm_nonneg _).trans (hf.val z hz)))
  · rw [hD z hz]
    refine (norm_add_le _ _).trans (add_le_add ((hR _ _).trans ?_) ((hL _ _).trans ?_))
    · exact mul_le_mul (hf.val z hz) (hg.der z hz) (norm_nonneg _) ((norm_nonneg _).trans (hf.val z hz))
    · exact mul_le_mul (hf.der z hz) (hg.val z hz) (norm_nonneg _) ((norm_nonneg _).trans (hf.der z hz))
  · have s1 := SlopeOn.bilin (B.precompR Space) hR (slopeOn_of_fderiv hf.diff hf.der) hg.slope hf.val hg.der
    have s2 := SlopeOn.bilin (B.precompL Space) hL hf.slope (slopeOn_of_fderiv hg.diff hg.der) hf.der hg.val
    exact (s1.add s2).congr hD

theorem BallBound.pair {f g : Space → ℝ} {y : Space} {v1 d1 l1 v2 d2 l2 : ℝ} (hf : BallBound f y v1 d1 l1)
    (hg : BallBound g y v2 d2 l2) : BallBound (fun z => (f z, g z)) y (v1 + v2) (d1 + d2) (l1 + l2) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => (f z, g z)) z = (fderiv ℝ f z).prod (fderiv ℝ g z) :=
    fun z hz => ((hf.diff z hz).hasFDerivAt.prodMk (hg.diff z hz).hasFDerivAt).fderiv
  have pb : ∀ (a b : ℝ) (A B : ℝ), ‖a‖ ≤ A → ‖b‖ ≤ B → ‖(a, b)‖ ≤ A + B := fun a b A B ha hb => by
    rw [Prod.norm_def]
    exact max_le (ha.trans (le_add_of_nonneg_right ((norm_nonneg b).trans hb)))
      (hb.trans (le_add_of_nonneg_left ((norm_nonneg a).trans ha)))
  have pc : ∀ (P Q : Space →L[ℝ] ℝ) (A B : ℝ), ‖P‖ ≤ A → ‖Q‖ ≤ B → ‖P.prod Q‖ ≤ A + B :=
    fun P Q A B hP hQ => by
      rw [ContinuousLinearMap.opNorm_prod, Prod.norm_def]
      exact max_le (hP.trans (le_add_of_nonneg_right ((norm_nonneg Q).trans hQ)))
        (hQ.trans (le_add_of_nonneg_left ((norm_nonneg P).trans hP)))
  refine ⟨fun z hz => (hf.diff z hz).prodMk (hg.diff z hz), fun z hz => pb _ _ _ _ (hf.val z hz) (hg.val z hz),
    fun z hz => by rw [hD z hz]; exact pc _ _ _ _ (hf.der z hz) (hg.der z hz), fun z hz w hw => ?_⟩
  rw [hD z hz, hD w hw]
  have e : (fderiv ℝ f z).prod (fderiv ℝ g z) - (fderiv ℝ f w).prod (fderiv ℝ g w) =
      (fderiv ℝ f z - fderiv ℝ f w).prod (fderiv ℝ g z - fderiv ℝ g w) := by
    ext h <;> simp
  rw [e, add_mul]
  exact pc _ _ _ _ (hf.slope z hz w hw) (hg.slope z hz w hw)

theorem BallBound.comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Φ : Space → V} {g : V → F}
    {K : Set V} {y : Space} {v d l c0 c1 c2 : ℝ} (hΦ : BallBound Φ y v d l) (hK : ∀ z ∈ Metric.ball y 1, Φ z ∈ K)
    (hgd : ∀ u ∈ K, DifferentiableAt ℝ g u) (hg0 : ∀ u ∈ K, ‖g u‖ ≤ c0) (hg1 : ∀ u ∈ K, ‖fderiv ℝ g u‖ ≤ c1)
    (hc2 : 0 ≤ c2) (hg2 : ∀ u ∈ K, ∀ u' ∈ K, ‖fderiv ℝ g u - fderiv ℝ g u'‖ ≤ c2 * ‖u - u'‖) :
    BallBound (fun z => g (Φ z)) y c0 (c1 * d) (c2 * d * d + c1 * l) := by
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ (fun z => g (Φ z)) z = (fderiv ℝ g (Φ z)).comp (fderiv ℝ Φ z) :=
    fun z hz => ((hgd _ (hK z hz)).hasFDerivAt.comp z (hΦ.diff z hz).hasFDerivAt).fderiv
  have hB : ∀ (P : V →L[ℝ] F) (Q : Space →L[ℝ] V),
      ‖ContinuousLinearMap.compL ℝ Space V F P Q‖ ≤ ‖P‖ * ‖Q‖ := fun P Q => by
    rw [ContinuousLinearMap.compL_apply]
    exact ContinuousLinearMap.opNorm_comp_le _ _
  have sΦ := slopeOn_of_fderiv hΦ.diff hΦ.der
  have s1 : SlopeOn (fun z => fderiv ℝ g (Φ z)) (c2 * d) (Metric.ball y 1) := fun z hz w hw => by
    refine (hg2 _ (hK z hz) _ (hK w hw)).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left (sΦ z hz w hw) hc2
  have s := SlopeOn.bilin (ContinuousLinearMap.compL ℝ Space V F) hB s1 hΦ.slope
    (fun z hz => hg1 _ (hK z hz)) hΦ.der
  refine ⟨fun z hz => ((hgd _ (hK z hz)).hasFDerivAt.comp z (hΦ.diff z hz).hasFDerivAt).differentiableAt,
    fun z hz => hg0 _ (hK z hz), fun z hz => ?_, s.congr fun z hz => by rw [hD z hz]; rfl⟩
  rw [hD z hz]
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_mul (hg1 _ (hK z hz)) (hΦ.der z hz)
    (norm_nonneg _) ((norm_nonneg _).trans (hg1 _ (hK z hz))))

theorem BallBound.congr {f g : Space → E} {y : Space} {v d l : ℝ} (hg : BallBound g y v d l) {U : Set Space}
    (hU : IsOpen U) (hsub : Metric.ball y 1 ⊆ U) (he : ∀ z ∈ U, f z = g z) : BallBound f y v d l := by
  have hev : ∀ z ∈ Metric.ball y 1, f =ᶠ[nhds z] g := fun z hz =>
    Filter.eventually_of_mem (hU.mem_nhds (hsub hz)) fun w hw => he w hw
  have hD : ∀ z ∈ Metric.ball y 1, fderiv ℝ f z = fderiv ℝ g z := fun z hz => (hev z hz).fderiv_eq
  refine ⟨fun z hz => (hg.diff z hz).congr_of_eventuallyEq (hev z hz), fun z hz => ?_, fun z hz => ?_,
    hg.slope.congr hD⟩
  · rw [he z (hsub hz)]
    exact hg.val z hz
  · rw [hD z hz]
    exact hg.der z hz

def FarBound (f : Space → E) (a : ℕ) : Prop :=
  ∃ M R : ℝ, 0 ≤ M ∧ 2 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ →
    BallBound f y (M / ‖y‖ ^ a) (M / ‖y‖ ^ (a + 1)) (M / ‖y‖ ^ (a + 2))

theorem ball_norm_near {y z : Space} (hz : z ∈ Metric.ball y 1) : ‖y‖ - 1 < ‖z‖ ∧ ‖z‖ < ‖y‖ + 1 := by
  have hd : ‖z - y‖ < 1 := by rwa [Metric.mem_ball, dist_eq_norm] at hz
  have h1 := norm_sub_norm_le y z
  have h2 := norm_sub_norm_le z y
  rw [norm_sub_rev] at h1
  constructor <;> linarith

theorem pow_div_le_of_half {r s C : ℝ} (k : ℕ) (hr : 0 < r) (hs : r / 2 ≤ s) (hC : 0 ≤ C) :
    C / s ^ k ≤ 2 ^ k * C / r ^ k := by
  have h1 : (r / 2) ^ k ≤ s ^ k := pow_le_pow_left₀ (by positivity) hs k
  calc C / s ^ k ≤ C / (r / 2) ^ k := div_le_div_of_nonneg_left hC (by positivity) h1
    _ = 2 ^ k * C / r ^ k := by rw [div_pow]; field_simp

theorem FarBound.add {f g : Space → E} {a : ℕ} (hf : FarBound f a) (hg : FarBound g a) :
    FarBound (fun z => f z + g z) a := by
  obtain ⟨M1, R1, hStrain, hR1, h1⟩ := hf
  obtain ⟨M2, R2, hM2, hR2, h2⟩ := hg
  refine ⟨M1 + M2, max R1 R2, by positivity, le_max_of_le_left hR1, fun y hy => ?_⟩
  refine ((h1 y (le_of_max_le_left hy)).add (h2 y (le_of_max_le_right hy))).mono ?_ ?_ ?_ <;>
    rw [add_div]

theorem FarBound.neg {f : Space → E} {a : ℕ} (hf : FarBound f a) : FarBound (fun z => -f z) a := by
  obtain ⟨M, R, hM, hR, h⟩ := hf
  exact ⟨M, R, hM, hR, fun y hy => (h y hy).neg⟩

theorem FarBound.bilin (B : E →L[ℝ] F →L[ℝ] G) (hB : ∀ u v, ‖B u v‖ ≤ ‖u‖ * ‖v‖) {f : Space → E}
    {g : Space → F} {a b : ℕ} (hf : FarBound f a) (hg : FarBound g b) :
    FarBound (fun z => B (f z) (g z)) (a + b) := by
  obtain ⟨M1, R1, hStrain, hR1, h1⟩ := hf
  obtain ⟨M2, R2, hM2, hR2, h2⟩ := hg
  refine ⟨4 * (M1 * M2), max R1 R2, by positivity, le_max_of_le_left hR1, fun y hy => ?_⟩
  have hr : 0 < ‖y‖ := by linarith [le_max_left R1 R2]
  set r := ‖y‖
  refine ((h1 y (le_of_max_le_left hy)).bilin B hB (h2 y (le_of_max_le_right hy))).mono ?_ ?_ ?_
  · rw [div_mul_div_comm, pow_add]
    have : 0 ≤ M1 * M2 / (r ^ a * r ^ b) := by positivity
    rw [show 4 * (M1 * M2) / (r ^ a * r ^ b) = 4 * (M1 * M2 / (r ^ a * r ^ b)) by ring]
    linarith
  · have e : M1 / r ^ a * (M2 / r ^ (b + 1)) + M1 / r ^ (a + 1) * (M2 / r ^ b) =
        2 * (M1 * M2 / r ^ (a + b + 1)) := by
      field_simp
      ring
    have : 0 ≤ M1 * M2 / r ^ (a + b + 1) := by positivity
    rw [e, show 4 * (M1 * M2) / r ^ (a + b + 1) = 4 * (M1 * M2 / r ^ (a + b + 1)) by ring]
    linarith
  · have e : M1 / r ^ (a + 1) * (M2 / r ^ (b + 1)) + M1 / r ^ a * (M2 / r ^ (b + 2)) +
        (M1 / r ^ (a + 2) * (M2 / r ^ b) + M1 / r ^ (a + 1) * (M2 / r ^ (b + 1))) =
        4 * (M1 * M2) / r ^ (a + b + 2) := by
      field_simp
      ring
    rw [e]

theorem FarBound.degree_le {f : Space → E} {a b : ℕ} (hf : FarBound f a) (hba : b ≤ a) : FarBound f b := by
  obtain ⟨M, R, hM, hR, h⟩ := hf
  refine ⟨M, R, hM, hR, fun y hy => (h y hy).mono ?_ ?_ ?_⟩ <;>
  · have h1 : (1 : ℝ) ≤ ‖y‖ := by linarith
    exact div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_right₀ h1 (by omega))

theorem farBound_const (c : E) : FarBound (fun _ : Space => c) 0 := by
  refine ⟨‖c‖, 2, norm_nonneg c, le_rfl, fun y hy => ⟨fun z _ => differentiableAt_const c,
    fun z _ => by simp, fun z _ => ?_, fun z _ w _ => ?_⟩⟩
  · rw [fderiv_const_apply, norm_zero]
    positivity
  · rw [fderiv_const_apply, fderiv_const_apply, sub_zero, norm_zero]
    have : 0 ≤ ‖c‖ / ‖y‖ ^ (0 + 2) := by positivity
    exact mul_nonneg this (norm_nonneg _)

theorem FarBound.congr {f g : Space → E} {a : ℕ} (hg : FarBound g a) {R0 : ℝ}
    (he : ∀ z : Space, R0 < ‖z‖ → f z = g z) : FarBound f a := by
  obtain ⟨M, R, hM, hR, h⟩ := hg
  refine ⟨M, max R (R0 + 1), hM, le_max_of_le_left hR, fun y hy => (h y (le_of_max_le_left hy)).congr
    (isOpen_lt continuous_const continuous_norm) (fun z hz => ?_) he⟩
  have := (ball_norm_near hz).1
  have := le_of_max_le_right hy
  show R0 < ‖z‖
  linarith

theorem FarBound.bounds_one {f : Space → E} (hf : FarBound f 1) :
    ∃ M R : ℝ, 0 ≤ M ∧ 2 ≤ R ∧ ∀ y : Space, R ≤ ‖y‖ → ‖f y‖ ≤ M / ‖y‖ ∧
      ‖fderiv ℝ f y‖ ≤ M / ‖y‖ ^ 2 ∧ ‖fderiv ℝ (fderiv ℝ f) y‖ ≤ M / ‖y‖ ^ 3 := by
  obtain ⟨M, R, hM, hR, h⟩ := hf
  refine ⟨M, R, hM, hR, fun y hy => ?_⟩
  have hb := h y hy
  have hy0 : y ∈ Metric.ball y 1 := Metric.mem_ball_self one_pos
  refine ⟨by simpa using hb.val y hy0, hb.der y hy0, ?_⟩
  have hl : LipschitzOnWith (Real.toNNReal (M / ‖y‖ ^ (1 + 2))) (fderiv ℝ f) (Metric.ball y 1) := by
    refine LipschitzOnWith.of_dist_le_mul fun z hz w hw => ?_
    rw [dist_eq_norm, dist_eq_norm]
    exact (hb.slope z hz w hw).trans (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal _) (norm_nonneg _))
  have := norm_fderiv_le_of_lipschitzOn ℝ (Metric.ball_mem_nhds y one_pos) hl
  rw [Real.coe_toNNReal _ (by positivity)] at this
  simpa using this

end Internal

end GivenShape

end CertCell

end Breakdown
