theory blocking_semantics5_TestSemantics_If42
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp"
begin
consts x :: "ident"
consts y :: "mident"
theorem If42:
  fixes sigma1 :: "mident \<Rightarrow> value"
  fixes pi1 :: "(ident \<times> value) list"
  fixes s :: "stmt"
  fixes sigma2 :: "mident \<Rightarrow> value"
  fixes pi2 :: "(ident \<times> value) list"
  assumes fact0: "one_step ((const :: value \<Rightarrow> mident \<Rightarrow> value) (Vint (0 :: int))) (Cons (x, Vint (42 :: int)) (Nil :: (ident \<times> value) list)) (Sif (Tbin (Tderef y) Ole (Tvalue (Vint (10 :: int)))) (Sassign y (Tvalue (Vint (13 :: int)))) (Sassign y (Tvalue (Vint (42 :: int))))) sigma1 pi1 s"
  assumes fact1: "one_step sigma1 pi1 s sigma2 pi2 Sskip"
  shows "sigma2 y = Vint (13 :: int)"
  sorry
end
