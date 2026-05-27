theory base_info_BaseInfo_pow_compatqtvc
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "pearl_multiprecision_lib.types_Config" "pearl_multiprecision_lib.types_Types" "mach.c_C" "pearl_multiprecision_lib.types_Int32Eq" "pearl_multiprecision_lib.types_UInt64Eq" "pearl_multiprecision_lib.logical_LogicalUtil" "pearl_multiprecision_lib.lemmas_Lemmas" "pearl_multiprecision_lib.logical_Logical" "pearl_multiprecision_lib.ptralias_Alias"
begin
typedecl  wmpn_base_info
consts b :: "wmpn_base_info \<Rightarrow> int"
consts exp :: "wmpn_base_info \<Rightarrow> 32 word"
consts bb :: "wmpn_base_info \<Rightarrow> 64 word"
axiomatization where wmpn_base_info'invariant'0:   "(2 :: int) \<le> b self"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'1:   "b self \<le> (256 :: int)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'2:   "uint (bb self) < (18446744073709551615 :: int) + (1 :: int)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'3:   "(18446744073709551615 :: int) + (1 :: int) \<le> uint (bb self) * b self"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'4:   "(7 :: int) \<le> uint (exp self)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'5:   "uint (exp self) \<le> (63 :: int)"
  for self :: "wmpn_base_info"
axiomatization where wmpn_base_info'invariant'6:   "uint (bb self) = b self ^\<^sub>i uint (exp self)"
  for self :: "wmpn_base_info"
definition wmpn_base_info'eq :: "wmpn_base_info \<Rightarrow> wmpn_base_info \<Rightarrow> _"
  where "wmpn_base_info'eq a b1 \<longleftrightarrow> b a = b b1 \<and> exp a = exp b1 \<and> bb a = bb b1" for a b1
axiomatization where wmpn_base_info'inj:   "a = b1"
 if "wmpn_base_info'eq a b1"
  for a :: "wmpn_base_info"
  and b1 :: "wmpn_base_info"
theorem pow_compat'vc:
  fixes b1 :: "int"
  fixes b2 :: "int"
  fixes e :: "int"
  assumes fact0: "(1 :: int) \<le> b1"
  assumes fact1: "b1 \<le> b2"
  assumes fact2: "(1 :: int) \<le> e"
  shows "b1 ^\<^sub>i e \<le> b2 ^\<^sub>i e"
  sorry
end
