theory BacktrackArray_Impl_addqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice"
begin
theorem add'vc:
  fixes tb :: "'a t"
  fixes x :: "int"
  fixes b :: "'a"
  assumes fact0: "correct tb"
  assumes fact1: "(0 :: int) \<le> x"
  assumes fact2: "inv tb b = True"
  shows "if int (length (buffer tb)) \<le> x then (correct tb \<and> int (length (buffer tb)) \<le> x) \<and> (\<forall>(tb1 :: 'a t). inv tb1 = inv tb \<longrightarrow> x < int (length (buffer tb1)) \<and> precede tb tb1 \<and> correct tb1 \<and> table (current_timestamp tb1) = table (current_timestamp tb) \<longrightarrow> (((0 :: int) \<le> x \<and> x < int (length (buffer tb1))) \<and> correct tb1 \<and> inv tb1 b = True) \<and> (\<forall>(tb2 :: 'a t). length (buffer tb2) = length (buffer tb1) \<and> inv tb2 = inv tb1 \<longrightarrow> past_time (current_timestamp tb2) tb2 \<and> correct tb2 \<and> precede tb1 tb2 \<and> (let tb0 :: int \<Rightarrow> 'a list = table (current_timestamp tb1) in table (current_timestamp tb2) = update tb0 x (Cons b (tb0 x))) \<longrightarrow> past_time (current_timestamp tb2) tb2 \<and> correct tb2 \<and> precede tb tb2 \<and> (let tb0 :: int \<Rightarrow> 'a list = table (current_timestamp tb) in table (current_timestamp tb2) = update tb0 x (Cons b (tb0 x))))) else ((0 :: int) \<le> x \<and> x < int (length (buffer tb))) \<and> correct tb \<and> inv tb b = True"
  sorry
end
