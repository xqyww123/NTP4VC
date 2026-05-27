theory A_CheckBytes8_A_CheckBytes8
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "Compound_Compound" "Why3STD.Cint_Cint"
begin
consts l_check_bytes8 :: "(addr \<Rightarrow> int) \<Rightarrow> addr \<Rightarrow> int \<Rightarrow> int \<Rightarrow> addr"
axiomatization where fix_l_check_bytes8:   "if bytes_0 = (0 :: int) then l_check_bytes8 mint_0 start_0 value_0 bytes_0 = Mk_addr (0 :: int) (0 :: int) else if mint_0 start_0 = value_0 then l_check_bytes8 mint_0 (shift start_0 (1 :: int)) value_0 (bytes_0 - (1 :: int)) = l_check_bytes8 mint_0 start_0 value_0 bytes_0 else l_check_bytes8 mint_0 start_0 value_0 bytes_0 = start_0"
  for mint_0 :: "addr \<Rightarrow> int"
  and start_0 :: "addr"
  and value_0 :: "int"
  and bytes_0 :: "int"
end
