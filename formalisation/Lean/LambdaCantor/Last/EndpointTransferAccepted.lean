import LambdaCantor.Last.EndpointTransferReciprocalPower
import LambdaCantor.Last.EndpointTransferReciprocalLog

noncomputable section
namespace LambdaCantor.Last

/-- Every accepted endpoint source gives positive dimension for the actual
curve, in either power/logarithmic form and either coordinate orientation. -/
theorem endpoint_source_positive_dimension {exponent ratio : ℝ}
    (hexponent : 1 < exponent) (hpositive : 0 < ratio) (hhalf : ratio < 1 / 2)
    (source : EndpointRectangle exponent ratio) (haccepted : source.Accepted) :
    0 < dimH (intersection exponent ratio) := by
  rcases haccepted with hpower | hpowerReciprocal | hlog | hlogReciprocal
  · exact power_endpoint_source_positive_dimension hexponent hpositive hhalf source hpower
  · exact power_endpoint_source_reciprocal_positive_dimension hexponent hpositive hhalf source hpowerReciprocal
  · exact logarithmic_endpoint_source_positive_dimension hexponent hpositive hhalf source hlog
  · exact logarithmic_endpoint_source_reciprocal_positive_dimension hexponent hpositive hhalf source hlogReciprocal

end LambdaCantor.Last
