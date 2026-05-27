theory blocking_semantics5_TestSemantics_Test42
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp"
begin
consts x :: "ident"
consts y :: "mident"
theorem Test42:
  shows "eval_term ((const :: value \<Rightarrow> mident \<Rightarrow> value) (Vint (0 :: int))) (Cons (x, Vint (42 :: int)) (Nil :: (ident \<times> value) list)) (Tvar x) = Vint (42 :: int)"
  sorry
end
