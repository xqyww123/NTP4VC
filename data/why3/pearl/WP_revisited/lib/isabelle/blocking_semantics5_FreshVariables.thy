theory blocking_semantics5_FreshVariables
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/blocking_semantics5_Syntax" "../../lib/isabelle/blocking_semantics5_SemOp"
begin
fun msubst_term :: "term \<Rightarrow> mident \<Rightarrow> ident \<Rightarrow> term"
  where "msubst_term (Tvalue x0) x v = Tvalue x0" for x0 x v
      | "msubst_term (Tvar x0) x v = Tvar x0" for x0 x v
      | "msubst_term (Tderef y) x v = (if x = y then Tvar v else Tderef y)" for y x v
      | "msubst_term (Tbin t1 op t2) x v = Tbin (msubst_term t1 x v) op (msubst_term t2 x v)" for t1 op t2 x v
fun msubst :: "fmla \<Rightarrow> mident \<Rightarrow> ident \<Rightarrow> fmla"
  where "msubst (Fterm e) x v = Fterm (msubst_term e x v)" for e x v
      | "msubst (Fand f1 f2) x v = Fand (msubst f1 x v) (msubst f2 x v)" for f1 f2 x v
      | "msubst (Fnot f1) x v = Fnot (msubst f1 x v)" for f1 x v
      | "msubst (Fimplies f1 f2) x v = Fimplies (msubst f1 x v) (msubst f2 x v)" for f1 f2 x v
      | "msubst (Flet y t f1) x v = Flet y (msubst_term t x v) (msubst f1 x v)" for y t f1 x v
      | "msubst (Fforall y ty f1) x v = Fforall y ty (msubst f1 x v)" for y ty f1 x v
fun fresh_in_term :: "ident \<Rightarrow> term \<Rightarrow> _"
  where "fresh_in_term id1 (Tvalue x) = True" for id1 x
      | "fresh_in_term id1 (Tderef x) = True" for id1 x
      | "fresh_in_term id1 (Tvar i) = (\<not>id1 = i)" for id1 i
      | "fresh_in_term id1 (Tbin t1 x t2) = (fresh_in_term id1 t1 \<and> fresh_in_term id1 t2)" for id1 t1 x t2
fun fresh_in_fmla :: "ident \<Rightarrow> fmla \<Rightarrow> _"
  where "fresh_in_fmla id1 (Fterm e) = fresh_in_term id1 e" for id1 e
      | "fresh_in_fmla id1 (Fand f1 f2) = (fresh_in_fmla id1 f1 \<and> fresh_in_fmla id1 f2)" for id1 f1 f2
      | "fresh_in_fmla id1 (Fimplies f1 f2) = (fresh_in_fmla id1 f1 \<and> fresh_in_fmla id1 f2)" for id1 f1 f2
      | "fresh_in_fmla id1 (Fnot f1) = fresh_in_fmla id1 f1" for id1 f1
      | "fresh_in_fmla id1 (Flet y t f1) = (\<not>id1 = y \<and> fresh_in_term id1 t \<and> fresh_in_fmla id1 f1)" for id1 y t f1
      | "fresh_in_fmla id1 (Fforall y x f1) = (\<not>id1 = y \<and> fresh_in_fmla id1 f1)" for id1 y x f1
end
