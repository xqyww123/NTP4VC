theory stringlemmas_String_lemmas_svalue_subqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "pearl_multiprecision_lib.lemmas_Lemmas" "mach.int_Unsigned" "mach.c_C" "mach.c_UChar" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq"
begin
definition in_base :: "int \<Rightarrow> (int \<Rightarrow> 8 word) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "in_base b x n m \<longleftrightarrow> (\<forall>(i :: int). n \<le> i \<and> i < m \<longrightarrow> (0 :: int) \<le> uint (x i) \<and> uint (x i) < b)" for b x n m
consts svalue_le_sub :: "int \<Rightarrow> (int \<Rightarrow> 8 word) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where svalue_le_sub_def:   "if n < m then svalue_le_sub b x n m = uint (x n) + b * svalue_le_sub b x (n + (1 :: int)) m else svalue_le_sub b x n m = (0 :: int)"
  for n :: "int"
  and m :: "int"
  and b :: "int"
  and x :: "int \<Rightarrow> 8 word"
definition string_in_base :: "int \<Rightarrow> 8 word ptr \<Rightarrow> _"
  where "string_in_base b p \<longleftrightarrow> in_base b (pelts p) (c_C.min p) (c_C.max p)" for b p
definition svalue_le :: "int \<Rightarrow> 8 word ptr \<Rightarrow> int \<Rightarrow> int"
  where "svalue_le b x sz = svalue_le_sub b (pelts x) (offset x) (offset x + sz)" for b x sz
theorem svalue_sub'vc:
  fixes n :: "int"
  fixes m :: "int"
  assumes fact0: "n < m"
  shows "(0 :: int) \<le> m - n"
  and "m - (1 :: int) - n < m - n"
  sorry
end
