theory lemmas_Lemmas_prod_compat_lrqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "mach.c_C" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq"
begin
definition map_eq_sub_shift :: "(int \<Rightarrow> 'a) \<Rightarrow> (int \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> _"
  where "map_eq_sub_shift x y xi yi sz \<longleftrightarrow> (\<forall>(i :: int). (0 :: int) \<le> i \<and> i < sz \<longrightarrow> x (xi + i) = y (yi + i))" for x y xi yi sz
theorem prod_compat_lr'vc:
  fixes a :: "int"
  fixes b :: "int"
  fixes c :: "int"
  fixes d :: "int"
  assumes fact0: "(0 :: int) \<le> a"
  assumes fact1: "a \<le> b"
  assumes fact2: "(0 :: int) \<le> c"
  assumes fact3: "c \<le> d"
  shows "a * c \<le> b * d"
  sorry
end
