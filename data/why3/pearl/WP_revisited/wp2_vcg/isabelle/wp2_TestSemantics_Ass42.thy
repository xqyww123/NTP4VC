theory wp2_TestSemantics_Ass42
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem Ass42:
  fixes sigma' :: "int \<Rightarrow> value"
  fixes pi' :: "int \<Rightarrow> value"
  assumes fact0: "one_step ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (0 :: int))) ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (42 :: int))) (Sassign (0 :: int) (Tconst (42 :: int))) sigma' pi' Sskip"
  shows "sigma' (0 :: int) = Vint (42 :: int)"
  sorry
end
