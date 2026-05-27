theory base_info_BaseInfo
  imports "NTP4Verif.NTP4Verif" "Why3STD.Ref_Ref" "Why3STD.map_Const" "Why3STD.map_MapEq" "mach.int_Unsigned" "types_Config" "types_Types" "mach.c_C" "types_Int32Eq" "types_UInt64Eq" "logical_LogicalUtil" "lemmas_Lemmas" "logical_Logical" "ptralias_Alias"
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
end
