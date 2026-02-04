theory blocking_semantics5_SemOp
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/blocking_semantics5_Syntax"
begin
typedecl  env
typedecl  stack
fun get_stack :: "ident \<Rightarrow> (ident \<times> value) list \<Rightarrow> value"
  where "get_stack i (Nil :: (ident \<times> value) list) = Vvoid" for i
      | "get_stack i (Cons (x, v) r) = (if x = i then v else get_stack i r)" for i x v r
definition eval_bin :: "value \<Rightarrow> operator \<Rightarrow> value \<Rightarrow> value"
  where "eval_bin x op y = (case (x, y) of (Vint x1, Vint y1) \<Rightarrow> (case op of Oplus \<Rightarrow> Vint (x1 + y1) | Ominus \<Rightarrow> Vint (x1 - y1) | Omult \<Rightarrow> Vint (x1 * y1) | Ole \<Rightarrow> Vbool (if x1 \<le> y1 then True else False)) | (_, _) \<Rightarrow> Vvoid)" for x op y
fun eval_term :: "(mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> term \<Rightarrow> value"
  where "eval_term sigma pi (Tvalue v) = v" for sigma pi v
      | "eval_term sigma pi (Tvar id1) = get_stack id1 pi" for sigma pi id1
      | "eval_term sigma pi (Tderef id1) = sigma id1" for sigma pi id1
      | "eval_term sigma pi (Tbin t1 op t2) = eval_bin (eval_term sigma pi t1) op (eval_term sigma pi t2)" for sigma pi t1 op t2
fun eval_fmla :: "(mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> fmla \<Rightarrow> _"
  where "eval_fmla sigma pi (Fterm t) = (eval_term sigma pi t = Vbool True)" for sigma pi t
      | "eval_fmla sigma pi (Fand f1 f2) = (eval_fmla sigma pi f1 \<and> eval_fmla sigma pi f2)" for sigma pi f1 f2
      | "eval_fmla sigma pi (Fnot f1) = (\<not>eval_fmla sigma pi f1)" for sigma pi f1
      | "eval_fmla sigma pi (Fimplies f1 f2) = (eval_fmla sigma pi f1 \<longrightarrow> eval_fmla sigma pi f2)" for sigma pi f1 f2
      | "eval_fmla sigma pi (Flet x t f1) = eval_fmla sigma (Cons (x, eval_term sigma pi t) pi) f1" for sigma pi x t f1
      | "eval_fmla sigma pi (Fforall x TYint f1) = (\<forall>(n :: int). eval_fmla sigma (Cons (x, Vint n) pi) f1)" for sigma pi x f1
      | "eval_fmla sigma pi (Fforall x TYbool f1) = (\<forall>(b :: bool). eval_fmla sigma (Cons (x, Vbool b) pi) f1)" for sigma pi x f1
      | "eval_fmla sigma pi (Fforall x TYunit f1) = eval_fmla sigma (Cons (x, Vvoid) pi) f1" for sigma pi x f1
definition valid_fmla :: "fmla \<Rightarrow> _"
  where "valid_fmla p \<longleftrightarrow> (\<forall>(sigma :: mident \<Rightarrow> value) (pi :: (ident \<times> value) list). eval_fmla sigma pi p)" for p
inductive one_step :: "(mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> stmt \<Rightarrow> (mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> stmt \<Rightarrow> bool" where
   one_step_assign: "sigma' = sigma(x := eval_term sigma pi t) \<Longrightarrow> one_step sigma pi (Sassign x t) sigma' pi Sskip" for sigma' :: "mident \<Rightarrow> value" and sigma :: "mident \<Rightarrow> value" and x :: "mident" and pi :: "(ident \<times> value) list" and t :: "term"
 | one_step_seq_noskip: "one_step sigma pi s1 sigma' pi' s1' \<Longrightarrow> one_step sigma pi (Sseq s1 s2) sigma' pi' (Sseq s1' s2)" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and s1 :: "stmt" and sigma' :: "mident \<Rightarrow> value" and pi' :: "(ident \<times> value) list" and s1' :: "stmt" and s2 :: "stmt"
 | one_step_seq_skip: "one_step sigma pi (Sseq Sskip s) sigma pi s" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and s :: "stmt"
 | one_step_if_true: "eval_term sigma pi t = Vbool True \<Longrightarrow> one_step sigma pi (Sif t s1 s2) sigma pi s1" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and t :: "term" and s1 :: "stmt" and s2 :: "stmt"
 | one_step_if_false: "eval_term sigma pi t = Vbool False \<Longrightarrow> one_step sigma pi (Sif t s1 s2) sigma pi s2" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and t :: "term" and s1 :: "stmt" and s2 :: "stmt"
 | one_step_assert: "eval_fmla sigma pi f \<Longrightarrow> one_step sigma pi (Sassert f) sigma pi Sskip" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and f :: "fmla"
 | one_step_while_true: "eval_fmla sigma pi inv \<Longrightarrow> eval_term sigma pi cond = Vbool True \<Longrightarrow> one_step sigma pi (Swhile cond inv body) sigma pi (Sseq body (Swhile cond inv body))" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and inv :: "fmla" and cond :: "term" and body :: "stmt"
 | one_step_while_false: "eval_fmla sigma pi inv \<Longrightarrow> eval_term sigma pi cond = Vbool False \<Longrightarrow> one_step sigma pi (Swhile cond inv body) sigma pi Sskip" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and inv :: "fmla" and cond :: "term" and body :: "stmt"
inductive many_steps :: "(mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> stmt \<Rightarrow> (mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> stmt \<Rightarrow> int \<Rightarrow> bool" where
   many_steps_refl: "many_steps sigma pi s sigma pi s (0 :: int)" for sigma :: "mident \<Rightarrow> value" and pi :: "(ident \<times> value) list" and s :: "stmt"
 | many_steps_trans: "one_step sigma1 pi1 s1 sigma2 pi2 s2 \<Longrightarrow> many_steps sigma2 pi2 s2 sigma3 pi3 s3 n \<Longrightarrow> many_steps sigma1 pi1 s1 sigma3 pi3 s3 (n + (1 :: int))" for sigma1 :: "mident \<Rightarrow> value" and pi1 :: "(ident \<times> value) list" and s1 :: "stmt" and sigma2 :: "mident \<Rightarrow> value" and pi2 :: "(ident \<times> value) list" and s2 :: "stmt" and sigma3 :: "mident \<Rightarrow> value" and pi3 :: "(ident \<times> value) list" and s3 :: "stmt" and n :: "int"
definition reductible :: "(mident \<Rightarrow> value) \<Rightarrow> (ident \<times> value) list \<Rightarrow> stmt \<Rightarrow> _"
  where "reductible sigma pi s \<longleftrightarrow> (\<exists>(sigma' :: mident \<Rightarrow> value) (pi' :: (ident \<times> value) list) (s' :: stmt). one_step sigma pi s sigma' pi' s')" for sigma pi s
end
