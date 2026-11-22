module

public import QuarticCorpus.Independent.SemanticMutations
public import QuarticCorpus.Independent.Controls.SharedAudit
public import QuarticQuery.Paper.ConstructionFull

/-! Type and transitive-axiom inspection target.
Native validation: `research/adjudication/round3_formal.json`. -/

#check @QuarticQuery.SemanticReview.identity_not_zero
#check @QuarticQuery.SemanticReview.orMixture_success
#check @QuarticQuery.SemanticReview.orTwo_RLe_one
#check @QuarticQuery.SemanticReview.trueOnly_R_eq_zero
#check @QuarticQuery.SemanticReview.trueOnly_Q_eq_zero
#check @QuarticQuery.SemanticReview.negativePair_Phi
#check @QuarticQuery.SemanticReview.negativePair_P_none
#check @QuarticQuery.SemanticReview.comparison_has_witness

#print axioms QuarticQuery.SemanticReview.identity_not_zero
#print axioms QuarticQuery.SemanticReview.orMixture_success
#print axioms QuarticQuery.SemanticReview.orTwo_RLe_one
#print axioms QuarticQuery.SemanticReview.trueOnly_R_eq_zero
#print axioms QuarticQuery.SemanticReview.trueOnly_Q_eq_zero
#print axioms QuarticQuery.SemanticReview.negativePair_Phi
#print axioms QuarticQuery.SemanticReview.negativePair_P_none
#print axioms QuarticQuery.SemanticReview.comparison_has_witness
#print axioms QuarticQuery.SemanticReview.wrong_quantifier_order_changes_answer
#print axioms QuarticQuery.SemanticReview.strict_threshold_mutant_rejects_mixture
#print axioms QuarticQuery.SemanticReview.absolute_high_changes_answer
#print axioms QuarticQuery.SemanticReview.off_promise_false_changes_zero_query_answer
#print axioms Round3.SharedAudit.shared_bad_spec_has_no_witness

#check QuarticQuery.Paper.construction_lemma_2_2_with_support
#print axioms QuarticQuery.Paper.construction_lemma_2_2_with_support
