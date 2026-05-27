theory Firstorder_term_spec_Spec_subst_free_var_constructive_inversion_symbol_fo_term_listqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.Nat_Nat" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.OptionFuncs_Funcs" "pearl_prover_lib.Sum_Sum" "pearl_prover_lib.Firstorder_symbol_spec_Spec"
begin
datatype ('b0, 'b3) fo_term_list = FONil | FOCons "('b0, 'b3) fo_term" "('b0, 'b3) fo_term_list"
     and ('b0, 'b3) fo_term = Var_fo_term "'b3" | App "'b0 symbol" "('b0, 'b3) fo_term_list"
fun nat_size_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> Nat_Nat.nat"  and nat_size_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> Nat_Nat.nat"  and size_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> int"  and size_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> int"
  where "nat_size_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) = (let s :: Nat_Nat.nat = SNat ONat in s)"
      | "nat_size_fo_term_list (FOCons v0 v1) = (let s :: Nat_Nat.nat = SNat ONat; s1 :: Nat_Nat.nat = add_nat (nat_size_fo_term_list v1) s; s2 :: Nat_Nat.nat = add_nat (nat_size_fo_term v0) s1 in s2)" for v0 v1
      | "nat_size_fo_term (Var_fo_term v0) = SNat ONat" for v0
      | "nat_size_fo_term (App v0 v1) = (let s :: Nat_Nat.nat = SNat ONat; s1 :: Nat_Nat.nat = add_nat (nat_size_fo_term_list v1) s; s2 :: Nat_Nat.nat = add_nat (nat_size_symbol v0) s1 in s2)" for v0 v1
      | "size_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) = (let s :: int = 1 :: int in s)"
      | "size_fo_term_list (FOCons v0 v1) = (let s :: int = 1 :: int; s1 :: int = size_fo_term_list v1 + s; s2 :: int = size_fo_term v0 + s1 in s2)" for v0 v1
      | "size_fo_term (Var_fo_term v0) = (1 :: int)" for v0
      | "size_fo_term (App v0 v1) = (let s :: int = 1 :: int; s1 :: int = size_fo_term_list v1 + s; s2 :: int = size_symbol v0 + s1 in s2)" for v0 v1
fun rename_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> ('b0 \<Rightarrow> 'c0) \<Rightarrow> ('b3 \<Rightarrow> 'c3) \<Rightarrow> ('c0, 'c3) fo_term_list"  and rename_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> ('b0 \<Rightarrow> 'c0) \<Rightarrow> ('b3 \<Rightarrow> 'c3) \<Rightarrow> ('c0, 'c3) fo_term"
  where "rename_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) s0 s3 = (FONil :: ('c0, 'c3) fo_term_list)" for s0 s3
      | "rename_fo_term_list (FOCons v0 v1) s0 s3 = FOCons (rename_fo_term v0 s0 s3) (rename_fo_term_list v1 s0 s3)" for v0 v1 s0 s3
      | "rename_fo_term (Var_fo_term v0) s0 s3 = Var_fo_term (s3 v0)" for v0 s0 s3
      | "rename_fo_term (App v0 v1) s0 s3 = App (rename_symbol v0 s0) (rename_fo_term_list v1 s0 s3)" for v0 v1 s0 s3
consts rename_subst_fo_term :: "('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0 \<Rightarrow> 'd0) \<Rightarrow> ('c3 \<Rightarrow> 'd3) \<Rightarrow> 'b3 \<Rightarrow> ('d0, 'd3) fo_term"
axiomatization where rename_subst_fo_term_definition:   "rename_subst_fo_term s0 s10 s13 x = rename_fo_term (s0 x) s10 s13"
  for s0 :: "'b3 \<Rightarrow> ('c0, 'c3) fo_term"
  and s10 :: "'c0 \<Rightarrow> 'd0"
  and s13 :: "'c3 \<Rightarrow> 'd3"
  and x :: "'b3"
definition olifts_fo_term :: "('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> 'b3 option \<Rightarrow> ('c0, 'c3 option) fo_term"
  where "olifts_fo_term s = ocase (rename_subst_fo_term s identity some) (Var_fo_term (None :: 'c3 option))" for s
fun subst_fo_term_list :: "('b0, 'b3) fo_term_list \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> ('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0, 'c3) fo_term_list"  and subst_fo_term :: "('b0, 'b3) fo_term \<Rightarrow> ('b0 \<Rightarrow> 'c0 symbol) \<Rightarrow> ('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0, 'c3) fo_term"
  where "subst_fo_term_list (FONil :: ('b0, 'b3) fo_term_list) s0 s3 = (FONil :: ('c0, 'c3) fo_term_list)" for s0 s3
      | "subst_fo_term_list (FOCons v0 v1) s0 s3 = FOCons (subst_fo_term v0 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) (subst_fo_term_list v1 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity))" for v0 v1 s0 s3
      | "subst_fo_term (Var_fo_term v0) s0 s3 = s3 v0" for v0 s0 s3
      | "subst_fo_term (App v0 v1) s0 s3 = App (subst_symbol v0 (rename_subst_symbol s0 identity)) (subst_fo_term_list v1 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity))" for v0 v1 s0 s3
consts subst_compose_fo_term :: "('b3 \<Rightarrow> ('c0, 'c3) fo_term) \<Rightarrow> ('c0 \<Rightarrow> 'd0 symbol) \<Rightarrow> ('c3 \<Rightarrow> ('d0, 'd3) fo_term) \<Rightarrow> 'b3 \<Rightarrow> ('d0, 'd3) fo_term"
axiomatization where subst_compose_fo_term_definition:   "subst_compose_fo_term s0 s10 s13 x = subst_fo_term (s0 x) s10 s13"
  for s0 :: "'b3 \<Rightarrow> ('c0, 'c3) fo_term"
  and s10 :: "'c0 \<Rightarrow> 'd0 symbol"
  and s13 :: "'c3 \<Rightarrow> ('d0, 'd3) fo_term"
  and x :: "'b3"
consts subst_id_fo_term :: "'b3 \<Rightarrow> ('b0, 'b3) fo_term"
axiomatization where subst_id_fo_term_definition:   "(subst_id_fo_term :: 'b3 \<Rightarrow> ('b0, 'b3) fo_term) x = Var_fo_term x"
  for x :: "'b3"
fun is_symbol_free_var_in_fo_term_list :: "'b0 \<Rightarrow> ('b0, 'b3) fo_term_list \<Rightarrow> _"  and is_fo_term_free_var_in_fo_term_list :: "'b3 \<Rightarrow> ('b0, 'b3) fo_term_list \<Rightarrow> _"  and is_symbol_free_var_in_fo_term :: "'b0 \<Rightarrow> ('b0, 'b3) fo_term \<Rightarrow> _"  and is_fo_term_free_var_in_fo_term :: "'b3 \<Rightarrow> ('b0, 'b3) fo_term \<Rightarrow> _"
  where "is_symbol_free_var_in_fo_term_list x (FONil :: ('b0, 'b3) fo_term_list) = False" for x
      | "is_symbol_free_var_in_fo_term_list x (FOCons v0 v1) = (is_symbol_free_var_in_fo_term x v0 \<or> is_symbol_free_var_in_fo_term_list x v1)" for x v0 v1
      | "is_fo_term_free_var_in_fo_term_list x (FONil :: ('b0, 'b3) fo_term_list) = False" for x
      | "is_fo_term_free_var_in_fo_term_list x (FOCons v0 v1) = (is_fo_term_free_var_in_fo_term x v0 \<or> is_fo_term_free_var_in_fo_term_list x v1)" for x v0 v1
      | "is_symbol_free_var_in_fo_term x (Var_fo_term v0) = False" for x v0
      | "is_symbol_free_var_in_fo_term x (App v0 v1) = (is_symbol_free_var_in_symbol x v0 \<or> is_symbol_free_var_in_fo_term_list x v1)" for x v0 v1
      | "is_fo_term_free_var_in_fo_term x (Var_fo_term v0) = (v0 = x)" for x v0
      | "is_fo_term_free_var_in_fo_term x (App v0 v1) = is_fo_term_free_var_in_fo_term_list x v1" for x v0 v1
theorem subst_free_var_constructive_inversion_symbol_fo_term_list'vc:
  fixes x :: "'c0"
  fixes t :: "('b0, 'b3) fo_term_list"
  fixes s0 :: "'b0 \<Rightarrow> 'c0 symbol"
  fixes s3 :: "'b3 \<Rightarrow> ('c0, 'c3) fo_term"
  assumes fact0: "is_symbol_free_var_in_fo_term_list x (subst_fo_term_list t s0 s3)"
  shows "case t of (FONil :: ('b0, 'b3) fo_term_list) \<Rightarrow> False | FOCons v0 v1 \<Rightarrow> (if is_symbol_free_var_in_fo_term x (subst_fo_term v0 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) then let o1 :: 'b3 \<Rightarrow> ('c0, 'c3) fo_term = rename_subst_fo_term s3 identity identity; o2 :: 'b0 \<Rightarrow> 'c0 symbol = rename_subst_symbol s0 identity in (((0 :: int) \<le> size_fo_term_list t \<and> size_fo_term v0 < size_fo_term_list t) \<and> is_symbol_free_var_in_fo_term x (subst_fo_term v0 o2 o1)) \<and> (\<forall>(sumx :: ('b0, 'b3) sum). (case sumx of Left sumx1 \<Rightarrow> is_symbol_free_var_in_fo_term sumx1 v0 \<and> is_symbol_free_var_in_symbol x (o2 sumx1) | Right sumx1 \<Rightarrow> is_fo_term_free_var_in_fo_term sumx1 v0 \<and> is_symbol_free_var_in_fo_term x (o1 sumx1)) \<longrightarrow> (case sumx of Left sumx1 \<Rightarrow> is_symbol_free_var_in_symbol x (rename_symbol (s0 sumx1) identity) | Right sumx1 \<Rightarrow> is_symbol_free_var_in_fo_term x (rename_fo_term (s3 sumx1) identity identity))) else is_symbol_free_var_in_fo_term_list x (subst_fo_term_list v1 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) \<and> (let o1 :: 'b3 \<Rightarrow> ('c0, 'c3) fo_term = rename_subst_fo_term s3 identity identity; o2 :: 'b0 \<Rightarrow> 'c0 symbol = rename_subst_symbol s0 identity in (((0 :: int) \<le> size_fo_term_list t \<and> size_fo_term_list v1 < size_fo_term_list t) \<and> is_symbol_free_var_in_fo_term_list x (subst_fo_term_list v1 o2 o1)) \<and> (\<forall>(sumx :: ('b0, 'b3) sum). (case sumx of Left sumx1 \<Rightarrow> is_symbol_free_var_in_fo_term_list sumx1 v1 \<and> is_symbol_free_var_in_symbol x (o2 sumx1) | Right sumx1 \<Rightarrow> is_fo_term_free_var_in_fo_term_list sumx1 v1 \<and> is_symbol_free_var_in_fo_term x (o1 sumx1)) \<longrightarrow> (case sumx of Left sumx1 \<Rightarrow> is_symbol_free_var_in_symbol x (rename_symbol (s0 sumx1) identity) | Right sumx1 \<Rightarrow> is_symbol_free_var_in_fo_term x (rename_fo_term (s3 sumx1) identity identity)))))"
  and "\<forall>(result :: ('b0, 'b3) sum). (case t of (FONil :: ('b0, 'b3) fo_term_list) \<Rightarrow> False | FOCons v0 v1 \<Rightarrow> (if is_symbol_free_var_in_fo_term x (subst_fo_term v0 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) then \<exists>(sumx :: ('b0, 'b3) sum). (case sumx of Left sumx1 \<Rightarrow> is_symbol_free_var_in_fo_term sumx1 v0 \<and> is_symbol_free_var_in_symbol x (rename_subst_symbol s0 identity sumx1) | Right sumx1 \<Rightarrow> is_fo_term_free_var_in_fo_term sumx1 v0 \<and> is_symbol_free_var_in_fo_term x (rename_subst_fo_term s3 identity identity sumx1)) \<and> (case sumx of Left sumx1 \<Rightarrow> (\<exists>(y :: 'c0). (is_symbol_free_var_in_symbol y (s0 sumx1) \<and> identity y = x) \<and> result = Left sumx1) | Right sumx1 \<Rightarrow> (\<exists>(y :: 'c0). (is_symbol_free_var_in_fo_term y (s3 sumx1) \<and> identity y = x) \<and> result = Right sumx1)) else is_symbol_free_var_in_fo_term_list x (subst_fo_term_list v1 (rename_subst_symbol s0 identity) (rename_subst_fo_term s3 identity identity)) \<and> (\<exists>(sumx :: ('b0, 'b3) sum). (case sumx of Left sumx1 \<Rightarrow> is_symbol_free_var_in_fo_term_list sumx1 v1 \<and> is_symbol_free_var_in_symbol x (rename_subst_symbol s0 identity sumx1) | Right sumx1 \<Rightarrow> is_fo_term_free_var_in_fo_term_list sumx1 v1 \<and> is_symbol_free_var_in_fo_term x (rename_subst_fo_term s3 identity identity sumx1)) \<and> (case sumx of Left sumx1 \<Rightarrow> (\<exists>(y :: 'c0). (is_symbol_free_var_in_symbol y (s0 sumx1) \<and> identity y = x) \<and> result = Left sumx1) | Right sumx1 \<Rightarrow> (\<exists>(y :: 'c0). (is_symbol_free_var_in_fo_term y (s3 sumx1) \<and> identity y = x) \<and> result = Right sumx1))))) \<longrightarrow> (case result of Left sumx \<Rightarrow> is_symbol_free_var_in_fo_term_list sumx t \<and> is_symbol_free_var_in_symbol x (s0 sumx) | Right sumx \<Rightarrow> is_fo_term_free_var_in_fo_term_list sumx t \<and> is_symbol_free_var_in_fo_term x (s3 sumx))"
  sorry
end
