theory lemmas_Lemmas_value_tailqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq"
begin
definition map_eq_sub_shift :: "(int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "map_eq_sub_shift x y xi yi sz \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < sz \<longrightarrow> x (xi + i) = y (yi + i))" for x y xi yi sz
consts value_sub :: "(int \<Rightarrow> 64 word) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where value_sub'def:   "if n < m then value_sub x n m = uint (x n) + ((18446744073709551615 :: int) + (1 :: int)) * value_sub x (n + (1 :: int)) m else value_sub x n m = (0 :: int)"
  for n :: "int"
  and m :: "int"
  and x :: "int \<Rightarrow> 64 word"
definition "value" :: "64 word ptr \<Rightarrow> int \<Rightarrow> int"
  where "value x sz = value_sub (pelts x) (offset x) (offset x + sz)" for x sz
theorem value_tail'vc:
  fixes sz :: "32 word"
  fixes x :: "64 word ptr"
  assumes fact0: "(0 :: int) \<le> sint sz"
  shows "value x (sint sz + (1 :: int)) = value x (sint sz) + uint (pelts x (offset x + sint sz)) * ((18446744073709551615 :: int) + (1 :: int)) ^\<^sub>i sint sz"
  sorry
end
