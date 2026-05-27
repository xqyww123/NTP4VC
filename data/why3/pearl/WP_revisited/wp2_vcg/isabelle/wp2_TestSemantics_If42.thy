theory wp2_TestSemantics_If42
  imports "NTP4Verif.NTP4Verif" "Why3STD.map_Const" "pearl_WP_revisited_lib.wp2_Imp"
begin
theorem If42:
  fixes sigma1 :: "int \<Rightarrow> value"
  fixes pi1 :: "int \<Rightarrow> value"
  fixes i :: "stmt"
  fixes sigma2 :: "int \<Rightarrow> value"
  fixes pi2 :: "int \<Rightarrow> value"
  assumes fact0: "one_step ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (0 :: int))) ((const :: value \<Rightarrow> int \<Rightarrow> value) (Vint (42 :: int))) (Sif (Tbin (Tderef (0 :: int)) Ole (Tconst (10 :: int))) (Sassign (0 :: int) (Tconst (13 :: int))) (Sassign (0 :: int) (Tconst (42 :: int)))) sigma1 pi1 i"
  assumes fact1: "one_step sigma1 pi1 i sigma2 pi2 Sskip"
  shows "sigma2 (0 :: int) = Vint (13 :: int)"
  sorry
end
