theory blocking_semantics5_TestSemantics_Ass42
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp"
begin
consts x :: "ident"
consts y :: "mident"
theorem Ass42:
  fixes sigma' :: "mident \<Rightarrow> value"
  fixes pi' :: "(ident \<times> value) list"
  assumes fact0: "one_step ((const :: value \<Rightarrow> mident \<Rightarrow> value) (Vint (0 :: int))) (Cons (x, Vint (42 :: int)) (Nil :: (ident \<times> value) list)) (Sassign y (Tvalue (Vint (42 :: int)))) sigma' pi' Sskip"
  shows "sigma' y = Vint (42 :: int)"
  sorry
end
