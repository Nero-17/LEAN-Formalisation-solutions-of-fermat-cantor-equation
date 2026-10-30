import LambdaCantor.RationalPowers.ExceptionalRemainingSourceCatalogue
/- User-authorized finite native evaluation. The generated evaluation auxiliary
axiom certifies only rational/integer arithmetic in this six-source predicate.
The real-rpow enclosure and analytic soundness remain separate kernel theorems. -/
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.RationalPowers.Exceptional.RemainingSources

def sourceCatalogueCheck : Bool :=
  sourceCatalogue.all (fun source => decide source.Valid)

theorem sourceCatalogueCheck_verified : sourceCatalogueCheck = true := by
  native_decide

theorem all_sources_valid : ∀ source ∈ sourceCatalogue, source.Valid := by
  have accepted := sourceCatalogueCheck_verified
  simpa only [sourceCatalogueCheck,List.all_eq_true,decide_eq_true_eq] using accepted

theorem source24_23_valid : source24_23.Valid :=
  all_sources_valid source24_23 (by simp [sourceCatalogue])

theorem source19_18_valid : source19_18.Valid :=
  all_sources_valid source19_18 (by simp [sourceCatalogue])

theorem source13_12_valid : source13_12.Valid :=
  all_sources_valid source13_12 (by simp [sourceCatalogue])

theorem source8_7_valid : source8_7.Valid :=
  all_sources_valid source8_7 (by simp [sourceCatalogue])

theorem source11_4_valid : source11_4.Valid :=
  all_sources_valid source11_4 (by simp [sourceCatalogue])

theorem source53_2_valid : source53_2.Valid :=
  all_sources_valid source53_2 (by simp [sourceCatalogue])

#print axioms all_sources_valid
end LambdaCantor.RationalPowers.Exceptional.RemainingSources
