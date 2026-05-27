theory lemmas_Lemmas_value_sub_frame_shiftqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq"
begin
definition map_eq_sub_shift :: "(int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "map_eq_sub_shift x y xi yi sz \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < sz \<longrightarrow> x (xi + i) = y (yi + i))" for x y xi yi sz
consts value_sub :: "(int \<Rightarrow> 64 word) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where value_sub'def:   "if n < m then value_sub x n m = uint (x n) + ((18446744073709551615 :: int) + (1 :: int)) * value_sub x (n + (1 :: int)) m else value_sub x n m = (0 :: int)"
  for n :: "int"
  and m :: "int"
  and x :: "int \<Rightarrow> 64 word"
theorem value_sub_frame_shift'vc:
  fixes x :: "int \<Rightarrow> 64 word"
  fixes y :: "int \<Rightarrow> 64 word"
  fixes xi :: "int"
  fixes yi :: "int"
  fixes sz :: "int"
  assumes fact0: "map_eq_sub_shift x y xi yi sz"
  shows "value_sub x xi (xi + sz) = value_sub y yi (yi + sz)"
  sorry
end
