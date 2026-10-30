import LambdaCantor.RationalPowers.CoarseWitnessChecks
import LambdaCantor.RationalPowers.LowSourceLookup
import LambdaCantor.RationalPowers.LowExceptionalChecks
import LambdaCantor.RationalPowers.LowFinitePartition

namespace LambdaCantor.RationalPowers

/-- A generated coarse interval search returns the retained source witness.
Every returned witness is independently rechecked at the queried exponent;
neither sortedness nor a Python union-membership flag is trusted. -/
def coarseIdentifierAccepted (select : ℕ → Option CoarseWitness) (identifier : ℕ) : Bool :=
  match select identifier with
  | none => false
  | some witness =>
    let pair := lowRationalPairAt (identifier/3675) (identifier%3675)
    decide (witness.Checked pair.1 pair.2)

def exceptionalSourceLookup (certificates : Array LowExceptionalCertificate)
    (entries : Array (IdentifierEntry ℕ)) (identifier : ℕ) : Option LowExceptionalCertificate :=
  match identifierLookup entries identifier with
  | none => none
  | some entry => if bound : entry.payload < certificates.size then some certificates[entry.payload] else none

def exceptionalIdentifierAccepted (certificates : Array LowExceptionalCertificate)
    (entries : Array (IdentifierEntry ℕ)) (identifier : ℕ) : Bool :=
  match exceptionalSourceLookup certificates entries identifier with
  | none => false
  | some certificate => decide
    (lowRationalPairAt (identifier/3675) (identifier%3675) = (certificate.numerator,certificate.denominator))

/-- Global finite acceptance checks the expected 294016 ordinary plus 1464
repair rows, all shared logarithms and full derivative bands, and seven actual
exceptional source/DAG certificates. Coverage is checked separately below. -/
def lowSourceCataloguesAccepted (blocks : Array SharedSourceBlock)
    (exceptions : Array LowExceptionalCertificate) : Bool :=
  decide (blocks.foldl (fun count block => count+block.rows.size) 0 = 295480) &&
    ordinaryCatalogueAccepted blocks && decide (exceptions.size = 7) &&
      exceptions.all (fun certificate => decide certificate.Checked)

def lowPartitionIdentifierAccepted (blocks : Array SharedSourceBlock)
    (ordinaryEntries : Array (IdentifierEntry OrdinaryReference))
    (selectCoarse : ℕ → Option CoarseWitness) (exceptions : Array LowExceptionalCertificate)
    (exceptionalEntries : Array (IdentifierEntry ℕ)) (identifier : ℕ) : Bool :=
  coarseIdentifierAccepted selectCoarse identifier ||
    ordinaryIdentifierAccepted blocks ordinaryEntries identifier ||
      exceptionalIdentifierAccepted exceptions exceptionalEntries identifier

end LambdaCantor.RationalPowers
