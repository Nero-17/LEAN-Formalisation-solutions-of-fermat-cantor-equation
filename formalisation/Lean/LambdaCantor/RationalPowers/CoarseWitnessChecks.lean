import LambdaCantor.RationalPowers.CoarseCheckedParameters
import LambdaCantor.RationalPowers.SharedLogGeometry

namespace LambdaCantor.RationalPowers
open Integer

/-- A coarse interval lookup must retain its actual source, scale and band.
An interval-union membership flag alone does not supply these data. -/
structure CoarseWitness where
  row : CoarseSourceRow
  shift : ℕ
  band : ℕ
  deriving DecidableEq

/-- Reuse exactly the ordinary source's independently checked full-ratio
predicate, at the actual zero-extended horizontal word. Atom fields are
unused: coarse corners come from the proved logarithmic width inequality. -/
def CoarseWitness.sourceRow (witness : CoarseWitness) (numerator denominator : ℕ) : SharedLogRow :=
  ⟨numerator, denominator, witness.row.horizontal*3^witness.shift, witness.row.vertical,
    7+witness.shift, 7, 0, witness.band, 0, 0, 0, 0, 0, 0, 0, 0⟩

def CoarseWitness.Checked (witness : CoarseWitness) (numerator denominator : ℕ) : Prop :=
  witness.row.StaticChecked ∧ witness.row.IntegerWidthChecked numerator denominator witness.shift ∧
    (witness.sourceRow numerator denominator).GeometryChecked

instance (witness : CoarseWitness) (numerator denominator : ℕ) :
    Decidable (witness.Checked numerator denominator) := by
  unfold CoarseWitness.Checked
  infer_instance

end LambdaCantor.RationalPowers
