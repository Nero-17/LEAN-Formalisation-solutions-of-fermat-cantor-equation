import LambdaCantor.Integer.PhaseCellSelection
import LambdaCantor.Certificates.IntegerTailEndpoints

namespace LambdaCantor.Integer

theorem tail_parameter_cell_selection (t : ℝ) (lower : 1 ≤ t) (upper : t ≤ 3) :
    ∃ endpoint cell first last : ℕ,
      (endpoint,first,last) ∈ tailParameterRows ∧
      ternaryPrefix endpoint 11 = true ∧ 0 < endpoint ∧
      20/243 ≤ (endpoint : ℝ)/3^11 ∧
      first ≤ cell ∧ cell ≤ last ∧
      2*(cell : ℝ)-1 ≤ 4000*(t/((endpoint : ℝ)/3^11)) ∧
      4000*(t/((endpoint : ℝ)/3^11)) ≤ 2*(cell : ℝ)+1 := by
  obtain ⟨interval,member,lowerInterval,upperInterval⟩ := tail_parameter_cover t lower upper
  obtain ⟨row,rowMember,identity⟩ := List.mem_map.mp member
  subst interval
  have checked : ternaryPrefix row.1 11 = true ∧ 20*3^11 ≤ 243*row.1 ∧
      0 < row.2.1 ∧ row.2.1 ≤ row.2.2 := by
    simpa only [Bool.and_eq_true,decide_eq_true_eq,and_assoc] using
      ((List.all_eq_true.mp tail_endpoint_digits_check) row rowMember)
  have endpointPositive : 0 < row.1 := by
    have bound := checked.2.1
    norm_num at bound
    omega
  have endpointRealPositive : (0 : ℝ) < row.1 := by exact_mod_cast endpointPositive
  have coefficientIdentity : (t/((row.1 : ℝ)/3^11))*(row.1 : ℝ) = t*3^11 := by
    field_simp [ne_of_gt endpointRealPositive]
  have firstLower : 2*(row.2.1 : ℝ)-1 ≤ 4000*(t/((row.1 : ℝ)/3^11)) := by
    have castLower : ((2*(row.2.1 : ℝ)-1)*(row.1 : ℝ))/708588000 ≤ t := by
      simpa only [Nat.cast_mul,Nat.cast_sub (show 1 ≤ 2*row.2.1 by omega),
        Nat.cast_ofNat,Nat.cast_one,Int.cast_natCast,Int.cast_mul,Int.cast_sub,
        Int.cast_ofNat,Int.cast_one] using lowerInterval
    apply le_of_mul_le_mul_right (a := (row.1 : ℝ)) _ endpointRealPositive
    norm_num at coefficientIdentity
    nlinarith
  have lastUpper : 4000*(t/((row.1 : ℝ)/3^11)) ≤ 2*(row.2.2 : ℝ)+1 := by
    have castUpper : t ≤ ((2*(row.2.2 : ℝ)+1)*(row.1 : ℝ))/708588000 := by
      simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one,Int.cast_natCast,
        Int.cast_mul,Int.cast_add,Int.cast_ofNat,Int.cast_one] using upperInterval
    apply le_of_mul_le_mul_right (a := (row.1 : ℝ)) _ endpointRealPositive
    norm_num at coefficientIdentity
    nlinarith
  obtain ⟨cell,cellFirst,cellLast,cellLower,cellUpper⟩ := coefficient_cell_selection
    row.2.1 row.2.2 checked.2.2.2 checked.2.2.1 _ firstLower lastUpper
  refine ⟨row.1,cell,row.2.1,row.2.2,rowMember,checked.1,endpointPositive,?_,
    cellFirst,cellLast,cellLower,cellUpper⟩
  have bound : (20 : ℝ)*3^11 ≤ 243*(row.1 : ℝ) := by exact_mod_cast checked.2.1
  norm_num at bound ⊢
  linarith

end LambdaCantor.Integer
