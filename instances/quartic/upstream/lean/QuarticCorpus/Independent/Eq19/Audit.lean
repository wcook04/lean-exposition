module

import QuarticCorpus.Independent.Eq19.Solution
import QuarticCorpus.Independent.Eq19.PathControls
import QuarticQuery.Paper.Eq19Complete
import QuarticQuery.Paper.Eq19Whole

/-! Re-entry type and axiom inspection. Never import the challenge here. -/

set_option pp.universes true in
#check QuarticQuery.Paper.eq19_whole
#print axioms QuarticQuery.Paper.eq19_whole

set_option pp.universes true in
#check QuarticQuery.Independent.Eq19.checked_eq19
#print axioms QuarticQuery.Independent.Eq19.checked_eq19

#check QuarticQuery.Independent.Eq19.repeatedZero_counts_once
#print axioms QuarticQuery.Independent.Eq19.repeatedZero_counts_once

#check QuarticQuery.Paper.eq_19_complete
#print axioms QuarticQuery.Paper.eq_19_complete
