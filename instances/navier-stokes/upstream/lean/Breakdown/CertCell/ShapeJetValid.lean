import Breakdown.CertCell.ShapeJetEntry
import Breakdown.CertCell.ShapeJetJoin
import Breakdown.CertCell.ShapeJetReflect
import Breakdown.CertCell.ShapeJetConjReflect
import Breakdown.CertCell.ShapeJetStart
import Breakdown.CertCell.ShapeSplineAgree

noncomputable section

namespace Breakdown

namespace CertCell

namespace GivenShape

open CellCert.GivenFields (Spline)

namespace Internal

theorem joinedSpline_mono_of_le {a b a' b' : ℕ} {S : Spline} (h : IsJoinedSpline a b S) (ha : a' ≤ a) (hb : b' ≤ b) :
    IsJoinedSpline a' b' S :=
  ⟨h.mesh, fun i hi hi' j hj o ho => h.t_joins i hi hi' j hj o (ho.trans ha),
    fun j hj hj' i hi o ho => h.x_joins j hj hj' i hi o (ho.trans hb)⟩

theorem joinedSpline_of_jetClass (hJ : JetSplineJoined) {a b : ℕ} {H : JetSpline} (h : IsJetClass a b H) :
    IsJoinedSpline a b H.toSpline :=
  joinedSpline_mono_of_le (hJ H h.t_axis h.x_axis) (by have := h.t_depth; omega) (by have := h.x_depth; omega)

theorem conjReflectFixed_of_realCoef {odd : Bool} {H : JetSpline} (hr : H.HasRealCoef)
    (h : H.IsReflectFixed odd) : H.IsConjReflectFixed odd := fun d e he => by
  rw [h d e he, hr d e]

theorem label_fst_eq_zero_of_negKey_eq {κ : FieldKey} (h : κ.negKey = κ) : κ.label.1 = 0 := by
  have h1 := congrArg (fun κ : FieldKey => κ.label.1) h
  simp only [FieldKey.negKey, Prod.fst_neg] at h1
  omega

theorem splineAgrees_conj_of_reflect_fixed (hA : SplineAgreementRules) {odd : Bool} {S : Spline}
    (h1 : SplineAgrees S (reflectSpline odd S)) (h2 : SplineAgrees S (reflectSpline odd S.conj)) :
    SplineAgrees S S.conj := by
  have h3 : SplineAgrees (reflectSpline odd S) (reflectSpline odd (reflectSpline odd S.conj)) :=
    ((hA 0 0 odd S (reflectSpline odd S.conj) S).2.2.2.1 h2).2
  have h4 : SplineAgrees (reflectSpline odd (reflectSpline odd S.conj)) S.conj :=
    (hA 0 0 odd S.conj S S).2.2.2.2.2.1
  have h5 : SplineAgrees (reflectSpline odd S) S.conj :=
    (hA 0 0 odd (reflectSpline odd S) (reflectSpline odd (reflectSpline odd S.conj)) S.conj).2.2.1 h3 h4
  exact (hA 0 0 odd S (reflectSpline odd S) S.conj).2.2.1 h1 h5

end Internal

theorem givenJetDataValid_of (hJ : JetSplineJoined) (hR : JetReflection) (hC : JetConjReflection)
    (hS : JetStartVanish) (hA : SplineAgreementRules) : GivenJetDataValid := by
  intro J hJd
  exact
    { one_per_orbit := hJd.one_per_orbit
      radial_class := fun κ hκ h0 => Internal.joinedSpline_of_jetClass hJ (hJd.radial_class κ hκ h0)
      polar_class := fun κ hκ h0 => Internal.joinedSpline_of_jetClass hJ (hJd.polar_class κ hκ h0)
      lowOrder_ge := hJd.lowOrder_ge
      stream_class := fun κ hκ h0 => Internal.joinedSpline_of_jetClass hJ (hJd.stream_class κ hκ h0)
      swirl_class := fun κ hκ h0 => Internal.joinedSpline_of_jetClass hJ (hJd.swirl_class κ hκ h0)
      stream_origin := fun κ hκ h0 =>
        hS _ (hJd.stream_class κ hκ h0).t_axis (hJd.stream_class κ hκ h0).x_axis (hJd.typeTwo_start κ hκ h0).1
      swirl_origin := fun κ hκ h0 =>
        hS _ (hJd.swirl_class κ hκ h0).t_axis (hJd.swirl_class κ hκ h0).x_axis (hJd.typeTwo_start κ hκ h0).2
      highOrder_pos := hJd.highOrder_pos
      stream_odd := fun κ hκ h0 =>
        hR true _ (hJd.stream_class κ hκ h0).t_axis (hJd.stream_class κ hκ h0).x_axis
          (hJd.typeTwo_symmetric κ hκ h0).1 (hJd.typeTwo_odd κ hκ h0).1
      swirl_odd := fun κ hκ h0 =>
        hR true _ (hJd.swirl_class κ hκ h0).t_axis (hJd.swirl_class κ hκ h0).x_axis
          (hJd.typeTwo_symmetric κ hκ h0).2 (hJd.typeTwo_odd κ hκ h0).2
      self_conj := fun κ hκ hneg => by
        have h0 := Internal.label_fst_eq_zero_of_negKey_eq hneg
        obtain ⟨hrs, hrw, hax⟩ := hJd.self_conj κ hκ hneg
        obtain ⟨hss, hsw⟩ := hJd.typeTwo_symmetric κ hκ h0
        obtain ⟨hos, how⟩ := hJd.typeTwo_odd κ hκ h0
        have cs := hJd.stream_class κ hκ h0
        have cw := hJd.swirl_class κ hκ h0
        exact ⟨Internal.splineAgrees_conj_of_reflect_fixed hA (hR true _ cs.t_axis cs.x_axis hss hos)
            (hC true _ cs.t_axis cs.x_axis hss (Internal.conjReflectFixed_of_realCoef hrs hos)),
          Internal.splineAgrees_conj_of_reflect_fixed hA (hR true _ cw.t_axis cw.x_axis hsw how)
            (hC true _ cw.t_axis cw.x_axis hsw (Internal.conjReflectFixed_of_realCoef hrw how)), hax⟩
      self_conj_flip := fun κ hκ h0 hfn => by
        obtain ⟨hsr, hsp, hcr, hcp⟩ := hJd.self_conj_flip κ hκ h0 hfn
        have cr := hJd.radial_class κ hκ h0
        have cp := hJd.polar_class κ hκ h0
        exact ⟨hC false _ cr.t_axis cr.x_axis hsr hcr, hC true _ cp.t_axis cp.x_axis hsp hcp⟩ }

theorem givenJetDataValid_of_parts (h : ShapeParts) : GivenJetDataValid :=
  givenJetDataValid_of h.jet_joined h.jet_reflection h.jet_conj_reflection h.jet_start h.agreement_rules

theorem givenJetDataValid : GivenJetDataValid :=
  givenJetDataValid_of jetSplineJoined jetReflection (jetConjReflection_of_jetReflection jetReflection)
    jetStartVanish splineAgreementRules

end GivenShape

end CertCell

end Breakdown
