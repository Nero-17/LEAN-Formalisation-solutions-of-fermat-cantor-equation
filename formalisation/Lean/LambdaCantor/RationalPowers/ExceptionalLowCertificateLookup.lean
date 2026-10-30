import LambdaCantor.RationalPowers.ExceptionalTwentyFourTwentyThirdsLowCertificate
import LambdaCantor.RationalPowers.ExceptionalNineteenEighteenthsLowCertificate
import LambdaCantor.RationalPowers.ExceptionalThirteenTwelfthsLowCertificate
import LambdaCantor.RationalPowers.ExceptionalEightSeventhsLowCertificate
import LambdaCantor.RationalPowers.ExceptionalEightThirdsLowCertificate
import LambdaCantor.RationalPowers.ExceptionalElevenFourthsLowCertificate
import LambdaCantor.RationalPowers.ExceptionalFiftyThreeHalvesLowCertificate
import LambdaCantor.RationalPowers.LowPartitionChecks
set_option maxRecDepth 100000
set_option maxHeartbeats 0
namespace LambdaCantor.RationalPowers
def exceptionalCertificateCatalogue : Array LowExceptionalCertificate :=
  #[Exceptional.TwentyFourTwentyThirds.lowCertificate,Exceptional.NineteenEighteenths.lowCertificate,Exceptional.ThirteenTwelfths.lowCertificate,Exceptional.EightSevenths.lowCertificate,Exceptional.EightThirds.lowCertificate,Exceptional.ElevenFourths.lowCertificate,Exceptional.FiftyThreeHalves.lowCertificate]
theorem exceptionalCertificateCatalogue_size : exceptionalCertificateCatalogue.size = 7 := rfl
theorem exceptionalCertificateCatalogue_checked :
    exceptionalCertificateCatalogue.all (fun certificate => decide certificate.Checked) = true := by
  simp only [Array.all_eq_true', decide_eq_true_eq]
  intro certificate membership
  simp [exceptionalCertificateCatalogue] at membership
  rcases membership with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Exceptional.TwentyFourTwentyThirds.lowCertificate_checked
  · exact Exceptional.NineteenEighteenths.lowCertificate_checked
  · exact Exceptional.ThirteenTwelfths.lowCertificate_checked
  · exact Exceptional.EightSevenths.lowCertificate_checked
  · exact Exceptional.EightThirds.lowCertificate_checked
  · exact Exceptional.ElevenFourths.lowCertificate_checked
  · exact Exceptional.FiftyThreeHalves.lowCertificate_checked
def exceptionalCertificateEntries : Array (IdentifierEntry ℕ) :=
  #[⟨11,3⟩,⟨41,2⟩,⟨95,1⟩,⟨149,0⟩,⟨3677,4⟩,⟨3679,5⟩,⟨91875,6⟩]
theorem exceptionalCertificateEntries_size : exceptionalCertificateEntries.size = 7 := rfl
/- Finite binary lookup and decoded-pair checks only; the actual source/DAG
acceptance is reused by the kernel catalogue theorem above. -/
theorem exceptionalCertificateEntries_accepted :
    exceptionalCertificateEntries.all (fun entry => exceptionalIdentifierAccepted
      exceptionalCertificateCatalogue exceptionalCertificateEntries entry.identifier) = true := by
  native_decide
#print axioms exceptionalCertificateCatalogue_checked
#print axioms exceptionalCertificateEntries_accepted
end LambdaCantor.RationalPowers
