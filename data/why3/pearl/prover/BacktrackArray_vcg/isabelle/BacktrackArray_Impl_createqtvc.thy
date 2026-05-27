theory BacktrackArray_Impl_createqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice"
begin
theorem create'vc:
  fixes p :: "'a \<Rightarrow> bool"
  shows "(0 :: int) \<le> (1 :: int)"
  and "\<forall>(o1 :: 'a list list). (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < (1 :: int) \<longrightarrow> o1 ! nat i = (Nil :: 'a list)) \<and> int (length o1) = (1 :: int) \<longrightarrow> (let res :: 'a t = t'mk (Nil :: int list) (0 :: int) o1 p in (\<forall>(t :: 'a timestamp). past_time t res \<longrightarrow> table t = (const :: 'a list \<Rightarrow> int \<Rightarrow> 'a list) (Nil :: 'a list)) \<and> past_time (current_timestamp res) res \<and> correct res)"
  sorry
end
