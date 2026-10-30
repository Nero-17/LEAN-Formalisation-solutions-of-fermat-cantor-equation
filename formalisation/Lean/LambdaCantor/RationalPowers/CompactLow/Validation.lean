import LambdaCantor.RationalPowers.CompactLow.Data

namespace LambdaCantor.RationalPowers.CompactLow

theorem entries_eq : entries = sharedFullOrdinaryEntries.map forgetPayload := by
  have checked := data_checked
  unfold validation at checked
  exact of_decide_eq_true (Bool.and_eq_true_iff.mp checked).1

theorem references_accepted : sharedFullOrdinaryEntries.all referenceAccepted = true := by
  have checked := data_checked
  unfold validation at checked
  exact (Bool.and_eq_true_iff.mp checked).2

end LambdaCantor.RationalPowers.CompactLow
