theory BacktrackArray_Impl_add_eventqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice"
begin
theorem add_event'vc:
  fixes tb :: "'a t"
  fixes x :: "int"
  fixes tb1 :: "'a t"
  fixes tb2 :: "'a t"
  assumes fact0: "history tb = Cons x (history tb1)"
  assumes fact1: "current_time tb = current_time tb1"
  assumes fact2: "buffer tb = buffer tb1"
  assumes fact3: "inv tb = inv tb1"
  assumes fact4: "history tb2 = history tb"
  assumes fact5: "current_time tb2 = current_time tb + (1 :: int)"
  assumes fact6: "buffer tb2 = buffer tb"
  assumes fact7: "inv tb2 = inv tb"
  shows "history tb2 = Cons x (history tb1)"
  and "current_time tb2 = current_time tb1 + (1 :: int)"
  sorry
end
