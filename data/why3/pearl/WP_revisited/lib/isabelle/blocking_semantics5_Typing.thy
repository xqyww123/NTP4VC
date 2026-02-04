theory blocking_semantics5_Typing
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/blocking_semantics5_Syntax"
begin
definition type_value :: "value \<Rightarrow> datatype"
  where "type_value v = (case v of Vvoid \<Rightarrow> TYunit | Vint _ \<Rightarrow> TYint | Vbool _ \<Rightarrow> TYbool)" for v
inductive type_operator :: "operator \<Rightarrow> datatype \<Rightarrow> datatype \<Rightarrow> datatype \<Rightarrow> bool" where
   Type_plus: "type_operator Oplus TYint TYint TYint"
 | Type_minus: "type_operator Ominus TYint TYint TYint"
 | Type_mult: "type_operator Omult TYint TYint TYint"
 | Type_le: "type_operator Ole TYint TYint TYbool"
typedecl  type_stack
fun get_vartype :: "ident \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> datatype"
  where "get_vartype i (Nil :: (ident \<times> datatype) list) = TYunit" for i
      | "get_vartype i (Cons (x, ty) r) = (if x = i then ty else get_vartype i r)" for i x ty r
typedecl  type_env
inductive type_term :: "(mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> term \<Rightarrow> datatype \<Rightarrow> bool" where
   Type_value: "type_term sigma pi (Tvalue v) (type_value v)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and v :: "value"
 | Type_var: "get_vartype v pi = ty \<Longrightarrow> type_term sigma pi (Tvar v) ty" for v :: "ident" and pi :: "(ident \<times> datatype) list" and ty :: "datatype" and sigma :: "mident \<Rightarrow> datatype"
 | Type_deref: "sigma v = ty \<Longrightarrow> type_term sigma pi (Tderef v) ty" for sigma :: "mident \<Rightarrow> datatype" and v :: "mident" and ty :: "datatype" and pi :: "(ident \<times> datatype) list"
 | Type_bin: "type_term sigma pi t1 ty1 \<Longrightarrow> type_term sigma pi t2 ty2 \<Longrightarrow> type_operator op ty1 ty2 ty \<Longrightarrow> type_term sigma pi (Tbin t1 op t2) ty" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and t1 :: "term" and ty1 :: "datatype" and t2 :: "term" and ty2 :: "datatype" and op :: "operator" and ty :: "datatype"
inductive type_fmla :: "(mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> fmla \<Rightarrow> bool" where
   Type_term: "type_term sigma pi t TYbool \<Longrightarrow> type_fmla sigma pi (Fterm t)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and t :: "term"
 | Type_conj: "type_fmla sigma pi f1 \<Longrightarrow> type_fmla sigma pi f2 \<Longrightarrow> type_fmla sigma pi (Fand f1 f2)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and f1 :: "fmla" and f2 :: "fmla"
 | Type_neg: "type_fmla sigma pi f \<Longrightarrow> type_fmla sigma pi (Fnot f)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and f :: "fmla"
 | Type_implies: "type_fmla sigma pi f1 \<Longrightarrow> type_fmla sigma pi f2 \<Longrightarrow> type_fmla sigma pi (Fimplies f1 f2)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and f1 :: "fmla" and f2 :: "fmla"
 | Type_let: "type_term sigma pi t ty \<Longrightarrow> type_fmla sigma (Cons (x, ty) pi) f \<Longrightarrow> type_fmla sigma pi (Flet x t f)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and t :: "term" and ty :: "datatype" and x :: "ident" and f :: "fmla"
 | Type_forall: "type_fmla sigma (Cons (x, ty) pi) f \<Longrightarrow> type_fmla sigma pi (Fforall x ty f)" for sigma :: "mident \<Rightarrow> datatype" and x :: "ident" and ty :: "datatype" and pi :: "(ident \<times> datatype) list" and f :: "fmla"
inductive type_stmt :: "(mident \<Rightarrow> datatype) \<Rightarrow> (ident \<times> datatype) list \<Rightarrow> stmt \<Rightarrow> bool" where
   Type_skip: "type_stmt sigma pi Sskip" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list"
 | Type_seq: "type_stmt sigma pi s1 \<Longrightarrow> type_stmt sigma pi s2 \<Longrightarrow> type_stmt sigma pi (Sseq s1 s2)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and s1 :: "stmt" and s2 :: "stmt"
 | Type_assigns: "sigma x = ty \<Longrightarrow> type_term sigma pi t ty \<Longrightarrow> type_stmt sigma pi (Sassign x t)" for sigma :: "mident \<Rightarrow> datatype" and x :: "mident" and ty :: "datatype" and pi :: "(ident \<times> datatype) list" and t :: "term"
 | Type_if: "type_term sigma pi t TYbool \<Longrightarrow> type_stmt sigma pi s1 \<Longrightarrow> type_stmt sigma pi s2 \<Longrightarrow> type_stmt sigma pi (Sif t s1 s2)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and t :: "term" and s1 :: "stmt" and s2 :: "stmt"
 | Type_assert: "type_fmla sigma pi p \<Longrightarrow> type_stmt sigma pi (Sassert p)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and p :: "fmla"
 | Type_while: "type_fmla sigma pi inv \<Longrightarrow> type_term sigma pi cond TYbool \<Longrightarrow> type_stmt sigma pi body \<Longrightarrow> type_stmt sigma pi (Swhile cond inv body)" for sigma :: "mident \<Rightarrow> datatype" and pi :: "(ident \<times> datatype) list" and inv :: "fmla" and cond :: "term" and body :: "stmt"
end
