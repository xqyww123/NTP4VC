theory BacktrackArray_Impl_stampqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice"
begin
theorem stamp'vc:
  fixes tb :: "'a t"
  assumes fact0: "correct tb"
  shows "timestamp'mk (current_time tb) (int (length (buffer tb))) (func_of_array (buffer tb) (Nil :: 'a list)) = current_timestamp tb"
  sorry
end
