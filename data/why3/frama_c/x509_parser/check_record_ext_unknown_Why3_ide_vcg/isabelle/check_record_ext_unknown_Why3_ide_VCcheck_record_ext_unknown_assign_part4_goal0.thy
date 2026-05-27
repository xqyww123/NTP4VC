theory check_record_ext_unknown_Why3_ide_VCcheck_record_ext_unknown_assign_part4_goal0
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "Why3STD.Memory_Memory" "frama_c_x509_parser_lib.Compound_Compound" "Why3STD.Cint_Cint"
begin
theorem goal0:
  fixes a :: "addr"
  fixes i :: "int"
  fixes t_1 :: "addr \<Rightarrow> addr"
  fixes t_2 :: "addr \<Rightarrow> addr"
  fixes a_1 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  shows "let a_2 :: addr = shift a (0 :: int); a_3 :: addr = shift a i; a_4 :: addr = havoc t_1 t_2 a_2 (29 :: int) a_3 in \<not>a_4 = a_1 \<longrightarrow> a_4 = Mk_addr (0 :: int) (0 :: int) \<longrightarrow> region (base a) \<le> (0 :: int) \<longrightarrow> region (base a_1) \<le> (0 :: int) \<longrightarrow> i \<le> (28 :: int) \<longrightarrow> i \<le> (29 :: int) \<longrightarrow> framed t_2 \<longrightarrow> linked t \<longrightarrow> is_uint16 i \<longrightarrow> valid_rd t a_3 (1 :: int) \<longrightarrow> valid_rw t a_2 (29 :: int) \<longrightarrow> valid_rw t a_3 (1 :: int) \<longrightarrow> \<not>invalid t a_3 (1 :: int) \<longrightarrow> (0 :: int) \<le> i"
  sorry
end
