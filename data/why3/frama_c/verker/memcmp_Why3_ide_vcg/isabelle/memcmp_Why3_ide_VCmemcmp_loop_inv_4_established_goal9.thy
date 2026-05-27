theory memcmp_Why3_ide_VCmemcmp_loop_inv_4_established_goal9
  imports "NTP4Verif.NTP4Verif" "Why3STD.Qed_Qed" "frama_c_verker_lib.Axiomatic3_Axiomatic3" "Why3STD.Memory_Memory" "Why3STD.Cint_Cint" "frama_c_verker_lib.Compound_Compound"
begin
theorem goal9:
  fixes a_15 :: "addr"
  fixes a_5 :: "addr"
  fixes a_4 :: "addr"
  fixes a_3 :: "addr"
  fixes a_2 :: "addr"
  fixes a_11 :: "addr"
  fixes a_10 :: "addr"
  fixes a_9 :: "addr"
  fixes a_8 :: "addr"
  fixes a_17 :: "addr"
  fixes a_18 :: "addr"
  fixes t :: "int \<Rightarrow> int"
  fixes i :: "int"
  fixes a :: "addr"
  fixes a_1 :: "addr"
  fixes a_6 :: "addr"
  fixes a_7 :: "addr"
  fixes a_14 :: "addr"
  fixes a_13 :: "addr"
  fixes a_16 :: "addr"
  fixes a_12 :: "addr"
  shows "let x :: int = offset a_15 in (base a_5 = base a_4 \<longleftrightarrow> base a_3 = base a_2) \<longrightarrow> (base a_11 = base a_10 \<longleftrightarrow> base a_9 = base a_8) \<longrightarrow> region (base a_17) \<le> (0 :: int) \<longrightarrow> region (base a_18) \<le> (0 :: int) \<longrightarrow> linked t \<longrightarrow> is_uint64 i \<longrightarrow> valid_rd t (shift a (0 :: int)) i \<longrightarrow> valid_rd t (shift a_1 (0 :: int)) i \<longrightarrow> valid_rd t (shift a_6 (0 :: int)) i \<longrightarrow> valid_rd t (shift a_7 (0 :: int)) i \<longrightarrow> x = offset a_14 \<and> offset a_13 + offset a_16 = offset a_12 + x"
  sorry
end
