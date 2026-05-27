theory div_u64_rem_0_Why3_ide_VCdiv_u64_rem_0_post_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes i_1 :: "int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let x :: int = i_1 cmod i in \<not>i = (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint32 i \<longrightarrow> is_uint64 i_1 \<longrightarrow> valid_rw t a (1 :: int) \<longrightarrow> x = to_uint32 x"
  sorry
end
