theory wp2_Imp
  imports "NTP4Verif.NTP4Verif"
begin
datatype  "datatype" = Tint | Tbool
datatype  operator = Oplus | Ominus | Omult | Ole
typedecl  ident
datatype  "term" = Tconst "int" | Tvar "int" | Tderef "int" | Tbin "term" "operator" "term"
datatype  fmla = Fterm "term" | Fand "fmla" "fmla" | Fnot "fmla" | Fimplies "fmla" "fmla" | Flet "int" "term" "fmla" | Fforall "int" "datatype" "fmla"
datatype  "value" = Vint "int" | Vbool "bool"
typedecl  env
definition eval_bin :: "value \<Rightarrow> operator \<Rightarrow> value \<Rightarrow> value"
  where "eval_bin x op y = (case (x, y) of (Vint x1, Vint y1) \<Rightarrow> (case op of Oplus \<Rightarrow> Vint (x1 + y1) | Ominus \<Rightarrow> Vint (x1 - y1) | Omult \<Rightarrow> Vint (x1 * y1) | Ole \<Rightarrow> Vbool (if x1 \<le> y1 then True else False)) | (_, _) \<Rightarrow> Vbool False)" for x op y
fun eval_term :: "(int \<Rightarrow> value) \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> term \<Rightarrow> value"
  where "eval_term sigma pi (Tconst n) = Vint n" for sigma pi n
      | "eval_term sigma pi (Tvar id1) = pi id1" for sigma pi id1
      | "eval_term sigma pi (Tderef id1) = sigma id1" for sigma pi id1
      | "eval_term sigma pi (Tbin t1 op t2) = eval_bin (eval_term sigma pi t1) op (eval_term sigma pi t2)" for sigma pi t1 op t2
fun eval_fmla :: "(int \<Rightarrow> value) \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> fmla \<Rightarrow> _"
  where "eval_fmla sigma pi (Fterm t) = (eval_term sigma pi t = Vbool True)" for sigma pi t
      | "eval_fmla sigma pi (Fand f1 f2) = (eval_fmla sigma pi f1 \<and> eval_fmla sigma pi f2)" for sigma pi f1 f2
      | "eval_fmla sigma pi (Fnot f1) = (\<not>eval_fmla sigma pi f1)" for sigma pi f1
      | "eval_fmla sigma pi (Fimplies f1 f2) = (eval_fmla sigma pi f1 \<longrightarrow> eval_fmla sigma pi f2)" for sigma pi f1 f2
      | "eval_fmla sigma pi (Flet x t f1) = eval_fmla sigma (pi(x := eval_term sigma pi t)) f1" for sigma pi x t f1
      | "eval_fmla sigma pi (Fforall x Tint f1) = (\<forall>(n :: int). eval_fmla sigma (pi(x := Vint n)) f1)" for sigma pi x f1
      | "eval_fmla sigma pi (Fforall x Tbool f1) = (\<forall>(b :: bool). eval_fmla sigma (pi(x := Vbool b)) f1)" for sigma pi x f1
fun subst_term :: "term \<Rightarrow> int \<Rightarrow> int \<Rightarrow> term"
  where "subst_term (Tconst x) r v = Tconst x" for x r v
      | "subst_term (Tvar x) r v = Tvar x" for x r v
      | "subst_term (Tderef x) r v = (if r = x then Tvar v else Tderef x)" for x r v
      | "subst_term (Tbin e1 op e2) r v = Tbin (subst_term e1 r v) op (subst_term e2 r v)" for e1 op e2 r v
fun fresh_in_term :: "int \<Rightarrow> term \<Rightarrow> _"
  where "fresh_in_term id1 (Tconst x) = True" for id1 x
      | "fresh_in_term id1 (Tvar v) = (\<not>id1 = v)" for id1 v
      | "fresh_in_term id1 (Tderef x) = True" for id1 x
      | "fresh_in_term id1 (Tbin t1 x t2) = (fresh_in_term id1 t1 \<and> fresh_in_term id1 t2)" for id1 t1 x t2
fun fresh_in_fmla :: "int \<Rightarrow> fmla \<Rightarrow> _"
  where "fresh_in_fmla id1 (Fterm e) = fresh_in_term id1 e" for id1 e
      | "fresh_in_fmla id1 (Fand f1 f2) = (fresh_in_fmla id1 f1 \<and> fresh_in_fmla id1 f2)" for id1 f1 f2
      | "fresh_in_fmla id1 (Fimplies f1 f2) = (fresh_in_fmla id1 f1 \<and> fresh_in_fmla id1 f2)" for id1 f1 f2
      | "fresh_in_fmla id1 (Fnot f1) = fresh_in_fmla id1 f1" for id1 f1
      | "fresh_in_fmla id1 (Flet y t f1) = (\<not>id1 = y \<and> fresh_in_term id1 t \<and> fresh_in_fmla id1 f1)" for id1 y t f1
      | "fresh_in_fmla id1 (Fforall y x f1) = (\<not>id1 = y \<and> fresh_in_fmla id1 f1)" for id1 y x f1
fun subst :: "fmla \<Rightarrow> int \<Rightarrow> int \<Rightarrow> fmla"
  where "subst (Fterm e) x v = Fterm (subst_term e x v)" for e x v
      | "subst (Fand f1 f2) x v = Fand (subst f1 x v) (subst f2 x v)" for f1 f2 x v
      | "subst (Fnot f1) x v = Fnot (subst f1 x v)" for f1 x v
      | "subst (Fimplies f1 f2) x v = Fimplies (subst f1 x v) (subst f2 x v)" for f1 f2 x v
      | "subst (Flet y t f1) x v = Flet y (subst_term t x v) (subst f1 x v)" for y t f1 x v
      | "subst (Fforall y ty f1) x v = Fforall y ty (subst f1 x v)" for y ty f1 x v
datatype  stmt = Sskip | Sassign "int" "term" | Sseq "stmt" "stmt" | Sif "term" "stmt" "stmt" | Sassert "fmla" | Swhile "term" "fmla" "stmt"
inductive one_step :: "(int \<Rightarrow> value) \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> stmt \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> stmt \<Rightarrow> bool" where
   one_step_assign: "one_step sigma pi (Sassign x e) (sigma(x := eval_term sigma pi e)) pi Sskip" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and x :: "int" and e :: "term"
 | one_step_seq: "one_step sigma pi i1 sigma' pi' i1' \<Longrightarrow> one_step sigma pi (Sseq i1 i2) sigma' pi' (Sseq i1' i2)" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and i1 :: "stmt" and sigma' :: "int \<Rightarrow> value" and pi' :: "int \<Rightarrow> value" and i1' :: "stmt" and i2 :: "stmt"
 | one_step_seq_skip: "one_step sigma pi (Sseq Sskip i) sigma pi i" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and i :: "stmt"
 | one_step_if_true: "eval_term sigma pi e = Vbool True \<Longrightarrow> one_step sigma pi (Sif e i1 i2) sigma pi i1" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and e :: "term" and i1 :: "stmt" and i2 :: "stmt"
 | one_step_if_false: "eval_term sigma pi e = Vbool False \<Longrightarrow> one_step sigma pi (Sif e i1 i2) sigma pi i2" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and e :: "term" and i1 :: "stmt" and i2 :: "stmt"
 | one_step_assert: "eval_fmla sigma pi f \<Longrightarrow> one_step sigma pi (Sassert f) sigma pi Sskip" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and f :: "fmla"
 | one_step_while_true: "eval_fmla sigma pi inv \<Longrightarrow> eval_term sigma pi e = Vbool True \<Longrightarrow> one_step sigma pi (Swhile e inv i) sigma pi (Sseq i (Swhile e inv i))" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and inv :: "fmla" and e :: "term" and i :: "stmt"
 | one_step_while_false: "eval_fmla sigma pi inv \<Longrightarrow> eval_term sigma pi e = Vbool False \<Longrightarrow> one_step sigma pi (Swhile e inv i) sigma pi Sskip" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and inv :: "fmla" and e :: "term" and i :: "stmt"
inductive many_steps :: "(int \<Rightarrow> value) \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> stmt \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> stmt \<Rightarrow> int \<Rightarrow> bool" where
   many_steps_refl: "many_steps sigma pi i sigma pi i (0 :: int)" for sigma :: "int \<Rightarrow> value" and pi :: "int \<Rightarrow> value" and i :: "stmt"
 | many_steps_trans: "one_step sigma1 pi1 i1 sigma2 pi2 i2 \<Longrightarrow> many_steps sigma2 pi2 i2 sigma3 pi3 i3 n \<Longrightarrow> many_steps sigma1 pi1 i1 sigma3 pi3 i3 (n + (1 :: int))" for sigma1 :: "int \<Rightarrow> value" and pi1 :: "int \<Rightarrow> value" and i1 :: "stmt" and sigma2 :: "int \<Rightarrow> value" and pi2 :: "int \<Rightarrow> value" and i2 :: "stmt" and sigma3 :: "int \<Rightarrow> value" and pi3 :: "int \<Rightarrow> value" and i3 :: "stmt" and n :: "int"
definition valid_fmla :: "fmla \<Rightarrow> _"
  where "valid_fmla p \<longleftrightarrow> (\<forall>(sigma :: int \<Rightarrow> value) (pi :: int \<Rightarrow> value). eval_fmla sigma pi p)" for p
definition valid_triple :: "fmla \<Rightarrow> stmt \<Rightarrow> fmla \<Rightarrow> _"
  where "valid_triple p i q \<longleftrightarrow> (\<forall>(sigma :: int \<Rightarrow> value) (pi :: int \<Rightarrow> value). eval_fmla sigma pi p \<longrightarrow> (\<forall>(sigma' :: int \<Rightarrow> value) (pi' :: int \<Rightarrow> value) (n :: int). many_steps sigma pi i sigma' pi' Sskip n \<longrightarrow> eval_fmla sigma' pi' q))" for p i q
end
