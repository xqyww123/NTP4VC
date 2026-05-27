theory wp2_WP_wpqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.wp2_Imp" "pearl_WP_revisited_lib.wp2_HoareLogic"
begin
typedecl  set
consts to_fset :: "set \<Rightarrow> int fset"
consts mk :: "int fset \<Rightarrow> set"
axiomatization where mk'spec:   "to_fset (mk s) = s"
  for s :: "int fset"
consts choose1 :: "set \<Rightarrow> int"
axiomatization where choose'spec:   "choose1 s |\<in>| to_fset s"
 if "\<not>to_fset s = fempty"
  for s :: "set"
definition assigns :: "(int \<Rightarrow> value) \<Rightarrow> int fset \<Rightarrow> (int \<Rightarrow> value) \<Rightarrow> _"
  where "assigns sigma a sigma' \<longleftrightarrow> (\<forall>(i :: int). \<not>i |\<in>| a \<longrightarrow> sigma i = sigma' i)" for sigma a sigma'
fun stmt_writes :: "stmt \<Rightarrow> int fset \<Rightarrow> _"
  where "stmt_writes Sskip w = True" for w
      | "stmt_writes (Sassert x) w = True" for x w
      | "stmt_writes (Sassign id1 x) w = (id1 |\<in>| w)" for id1 x w
      | "stmt_writes (Sseq s1 s2) w = (stmt_writes s1 w \<and> stmt_writes s2 w)" for s1 s2 w
      | "stmt_writes (Sif x s1 s2) w = (stmt_writes s1 w \<and> stmt_writes s2 w)" for x s1 s2 w
      | "stmt_writes (Swhile x x0 s) w = stmt_writes s w" for x x0 s w
theorem wp'vc:
  fixes i :: "stmt"
  fixes q :: "fmla"
  shows "case i of Sskip \<Rightarrow> True | Sseq i1 i2 \<Rightarrow> (case i of Sskip \<Rightarrow> False | Sassign _ _ \<Rightarrow> False | Sseq f f1 \<Rightarrow> f = i2 \<or> f1 = i2 | Sif _ f f1 \<Rightarrow> f = i2 \<or> f1 = i2 | Sassert _ \<Rightarrow> False | Swhile _ _ f \<Rightarrow> f = i2) \<and> (\<forall>(o1 :: fmla). valid_triple o1 i2 q \<longrightarrow> (case i of Sskip \<Rightarrow> False | Sassign _ _ \<Rightarrow> False | Sseq f f1 \<Rightarrow> f = i1 \<or> f1 = i1 | Sif _ f f1 \<Rightarrow> f = i1 \<or> f1 = i1 | Sassert _ \<Rightarrow> False | Swhile _ _ f \<Rightarrow> f = i1)) | Sassign x e \<Rightarrow> True | Sif e i1 i2 \<Rightarrow> (case i of Sskip \<Rightarrow> False | Sassign _ _ \<Rightarrow> False | Sseq f f1 \<Rightarrow> f = i2 \<or> f1 = i2 | Sif _ f f1 \<Rightarrow> f = i2 \<or> f1 = i2 | Sassert _ \<Rightarrow> False | Swhile _ _ f \<Rightarrow> f = i2) \<and> (\<forall>(o1 :: fmla). valid_triple o1 i2 q \<longrightarrow> (case i of Sskip \<Rightarrow> False | Sassign _ _ \<Rightarrow> False | Sseq f f1 \<Rightarrow> f = i1 \<or> f1 = i1 | Sif _ f f1 \<Rightarrow> f = i1 \<or> f1 = i1 | Sassert _ \<Rightarrow> False | Swhile _ _ f \<Rightarrow> f = i1)) | Sassert f \<Rightarrow> True | Swhile e inv' i1 \<Rightarrow> (case i of Sskip \<Rightarrow> False | Sassign _ _ \<Rightarrow> False | Sseq f f1 \<Rightarrow> f = i1 \<or> f1 = i1 | Sif _ f f1 \<Rightarrow> f = i1 \<or> f1 = i1 | Sassert _ \<Rightarrow> False | Swhile _ _ f \<Rightarrow> f = i1)"
  and "\<forall>(result :: fmla). (case i of Sskip \<Rightarrow> result = q | Sseq i1 i2 \<Rightarrow> (\<exists>(o1 :: fmla). valid_triple o1 i2 q \<and> valid_triple result i1 o1) | Sassign x e \<Rightarrow> (\<exists>(id1 :: int). fresh_in_fmla id1 q \<and> result = Flet id1 e (subst q x id1)) | Sif e i1 i2 \<Rightarrow> (\<exists>(o1 :: fmla). valid_triple o1 i2 q \<and> (\<exists>(o2 :: fmla). valid_triple o2 i1 q \<and> result = Fand (Fimplies (Fterm e) o2) (Fimplies (Fnot (Fterm e)) o1))) | Sassert f \<Rightarrow> result = Fimplies f q | Swhile e inv' i1 \<Rightarrow> (\<exists>(o1 :: fmla). valid_triple o1 i1 inv' \<and> (\<exists>(o2 :: fmla). (\<forall>(sigma :: int \<Rightarrow> value) (pi :: int \<Rightarrow> value). eval_fmla sigma pi o2 \<longrightarrow> eval_fmla sigma pi (Fand (Fimplies (Fand (Fterm e) inv') o1) (Fimplies (Fand (Fnot (Fterm e)) inv') q)) \<and> (\<forall>(sigma' :: int \<Rightarrow> value) (pi' :: int \<Rightarrow> value) (n :: int). many_steps sigma pi i1 sigma' pi' Sskip n \<longrightarrow> eval_fmla sigma' pi' o2)) \<and> result = Fand inv' o2))) \<longrightarrow> valid_triple result i q"
  sorry
end
