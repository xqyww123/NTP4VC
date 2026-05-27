theory BacktrackArray_Impl_getqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice"
begin
theorem get'vc:
  fixes tb :: "'a t"
  fixes x :: "int"
  assumes fact0: "correct tb"
  assumes fact1: "(0 :: int) \<le> x"
  shows "let o1 :: int = int (length (buffer tb)) in (\<not>o1 \<le> x \<longrightarrow> (0 :: int) \<le> x \<and> x < int (length (buffer tb))) \<and> (\<forall>(result :: 'a list). (if o1 \<le> x then result = (Nil :: 'a list) else result = buffer tb ! nat x) \<longrightarrow> result = table (current_timestamp tb) x \<and> list_forall (inv tb) result)"
  sorry
end
