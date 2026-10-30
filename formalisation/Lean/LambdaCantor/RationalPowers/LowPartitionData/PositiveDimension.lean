import LambdaCantor.RationalPowers.LowPartitionData.Block00
import LambdaCantor.RationalPowers.LowPartitionData.Block01
import LambdaCantor.RationalPowers.LowPartitionData.Block02
import LambdaCantor.RationalPowers.LowPartitionData.Block03
import LambdaCantor.RationalPowers.LowPartitionData.Block04
import LambdaCantor.RationalPowers.LowPartitionData.Block05
import LambdaCantor.RationalPowers.LowPartitionData.Block06
import LambdaCantor.RationalPowers.LowPartitionData.Block07
import LambdaCantor.RationalPowers.LowPartitionData.Block08
import LambdaCantor.RationalPowers.LowPartitionData.Block09
import LambdaCantor.RationalPowers.LowPartitionData.Block10
import LambdaCantor.RationalPowers.LowPartitionData.Block11
import LambdaCantor.RationalPowers.LowPartitionData.Block12
import LambdaCantor.RationalPowers.LowPartitionData.Block13
import LambdaCantor.RationalPowers.LowPartitionData.Block14
import LambdaCantor.RationalPowers.LowPartitionData.Block15
import LambdaCantor.RationalPowers.LowPartitionData.Block16
import LambdaCantor.RationalPowers.LowPartitionData.Block17
import LambdaCantor.RationalPowers.LowPartitionData.Block18
import LambdaCantor.RationalPowers.LowPartitionData.Block19
import LambdaCantor.RationalPowers.LowPartitionData.Block20
import LambdaCantor.RationalPowers.LowPartitionData.Block21
import LambdaCantor.RationalPowers.LowPartitionData.Block22
import LambdaCantor.RationalPowers.LowPartitionData.Block23
import LambdaCantor.RationalPowers.LowPartitionData.Block24
import LambdaCantor.RationalPowers.LowPartitionData.Block25
import LambdaCantor.RationalPowers.LowPartitionData.Block26
import LambdaCantor.RationalPowers.LowPartitionData.Block27
import LambdaCantor.RationalPowers.LowPartitionData.Block28
import LambdaCantor.RationalPowers.LowPartitionData.Block29
import LambdaCantor.RationalPowers.LowPartitionData.Block30
import LambdaCantor.RationalPowers.LowPartitionData.Block31
import LambdaCantor.RationalPowers.LowPartitionData.Block32
import LambdaCantor.RationalPowers.LowPartitionData.Block33
import LambdaCantor.RationalPowers.LowPartitionData.Block34
import LambdaCantor.RationalPowers.LowPartitionPositive
import Mathlib.Tactic.FinCases

noncomputable section
namespace LambdaCantor.RationalPowers

theorem actualLowPartitionAllBlocks_checked (block : Fin 35) :
  lowRationalBlockCheck (64*block.val) (min 64 (2186-64*block.val)) actualLowPartitionPredicate = true := by
  fin_cases block
  · exact actualLowPartitionBlock00_checked
  · exact actualLowPartitionBlock01_checked
  · exact actualLowPartitionBlock02_checked
  · exact actualLowPartitionBlock03_checked
  · exact actualLowPartitionBlock04_checked
  · exact actualLowPartitionBlock05_checked
  · exact actualLowPartitionBlock06_checked
  · exact actualLowPartitionBlock07_checked
  · exact actualLowPartitionBlock08_checked
  · exact actualLowPartitionBlock09_checked
  · exact actualLowPartitionBlock10_checked
  · exact actualLowPartitionBlock11_checked
  · exact actualLowPartitionBlock12_checked
  · exact actualLowPartitionBlock13_checked
  · exact actualLowPartitionBlock14_checked
  · exact actualLowPartitionBlock15_checked
  · exact actualLowPartitionBlock16_checked
  · exact actualLowPartitionBlock17_checked
  · exact actualLowPartitionBlock18_checked
  · exact actualLowPartitionBlock19_checked
  · exact actualLowPartitionBlock20_checked
  · exact actualLowPartitionBlock21_checked
  · exact actualLowPartitionBlock22_checked
  · exact actualLowPartitionBlock23_checked
  · exact actualLowPartitionBlock24_checked
  · exact actualLowPartitionBlock25_checked
  · exact actualLowPartitionBlock26_checked
  · exact actualLowPartitionBlock27_checked
  · exact actualLowPartitionBlock28_checked
  · exact actualLowPartitionBlock29_checked
  · exact actualLowPartitionBlock30_checked
  · exact actualLowPartitionBlock31_checked
  · exact actualLowPartitionBlock32_checked
  · exact actualLowPartitionBlock33_checked
  · exact actualLowPartitionBlock34_checked

theorem actual_low_denominator_positive_dimension (numerator denominator : ℕ)
    (denominator_lower : 2 ≤ denominator) (denominator_upper : denominator ≤ 109)
    (numerator_lower : denominator < numerator) (numerator_upper : numerator < 2187*denominator)
    (coprime : numerator.Coprime denominator) :
    0 < dimH (intersection ((numerator : ℝ)/denominator) (1/3)) :=
  low_denominator_positive_dimension_of_acceptance sharedFullSourceBlocks sharedFullOrdinaryEntries
    (coarseCatalogueSelect coarseIntervalCatalogues) exceptionalCertificateCatalogue exceptionalCertificateEntries
    actualLowSourceCatalogues_checked actualLowPartitionAllBlocks_checked numerator denominator
    denominator_lower denominator_upper numerator_lower numerator_upper coprime

#print axioms actualLowSourceCatalogues_checked
#print axioms actualLowPartitionAllBlocks_checked
#print axioms actual_low_denominator_positive_dimension

end LambdaCantor.RationalPowers
