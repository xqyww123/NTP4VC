theory Firstorder_term_spec_Spec_size_positive_lemma_fo_term_listqtvc
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
theorem size_positive_lemma_fo_term_list'vc:
  fixes t :: "('b0, 'b3) fo_term_list"
  shows "(0 :: int) < size_fo_term_list t"
  sorry
end
