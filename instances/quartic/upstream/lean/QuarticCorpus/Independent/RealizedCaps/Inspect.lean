module

public import QuarticQuery.ExternalRandomness
public import QuarticQuery.MeasurablePolicies
public import QuarticQuery.LowerBound.RealizedCaps
public import QuarticQuery.LowerBound.RealizedCapsExternal
public import QuarticQuery.Paper.RealizedCaps

/-! Type and transitive-axiom inspection of round-four return 05.
Native validation: `research/adjudication/round4_formal.json`. -/

#check @QuarticQuery.OutTree.clip_capped
#check @QuarticQuery.OutTree.clip_eval_eq_of_actualComplies
#check @QuarticQuery.OutTree.clip_path_eq_of_actualComplies
#check @QuarticQuery.compliantSuccess_le_clipped
#check @QuarticQuery.direct_product_realized_caps
#check @QuarticQuery.direct_product_realized_caps_average
#check @QuarticQuery.direct_product_external_finite_realized_caps
#check @QuarticQuery.Paper.classical_realized_caps
#check @QuarticQuery.finitePushforward_sum
#check @QuarticQuery.finitePushforward_nonneg
#check @QuarticQuery.finitePushforward_expectation
#check @QuarticQuery.compilePolicy_capped
#check @QuarticQuery.compilePolicy_depth_le

#print axioms QuarticQuery.OutTree.clip_capped
#print axioms QuarticQuery.OutTree.clip_eval_eq_of_actualComplies
#print axioms QuarticQuery.OutTree.clip_path_eq_of_actualComplies
#print axioms QuarticQuery.compliantSuccess_le_clipped
#print axioms QuarticQuery.direct_product_realized_caps
#print axioms QuarticQuery.direct_product_realized_caps_average
#print axioms QuarticQuery.direct_product_external_finite_realized_caps
#print axioms QuarticQuery.Paper.classical_realized_caps
#print axioms QuarticQuery.finitePushforward_sum
#print axioms QuarticQuery.finitePushforward_nonneg
#print axioms QuarticQuery.finitePushforward_expectation
#print axioms QuarticQuery.compilePolicy_capped
#print axioms QuarticQuery.compilePolicy_depth_le
