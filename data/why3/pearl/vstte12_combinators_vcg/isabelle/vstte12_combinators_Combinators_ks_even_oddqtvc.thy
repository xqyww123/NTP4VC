theory vstte12_combinators_Combinators_ks_even_oddqtvc
  imports "NTP4Verif.NTP4Verif"
begin
datatype  "term" = S | K | App "term" "term"
fun eq :: "term \<Rightarrow> term \<Rightarrow> _"
  where "eq S S = True"
      | "eq K K = True"
      | "eq (App x1 x2) (App y1 y2) = (eq x1 y1 \<and> eq x2 y2)" for x1 x2 y1 y2
      | "eq x x0 = False" for x x0
axiomatization where eq'spec:   "eq x y \<longleftrightarrow> x = y"
  for x :: "term"
  and y :: "term"
fun is_value :: "term \<Rightarrow> _"
  where "is_value K = True"
      | "is_value S = True"
      | "is_value (App K v) = is_value v" for v
      | "is_value (App S v) = is_value v" for v
      | "is_value (App (App S v1) v2) = (is_value v1 \<and> is_value v2)" for v1 v2
      | "is_value x = False" for x
datatype  "context" = Hole | Left "context" "term" | Right "term" "context"
fun is_context :: "context \<Rightarrow> _"
  where "is_context Hole = True"
      | "is_context (Left c1 x) = is_context c1" for c1 x
      | "is_context (Right v c1) = (is_value v \<and> is_context c1)" for v c1
fun subst :: "context \<Rightarrow> term \<Rightarrow> term"
  where "subst Hole t = t" for t
      | "subst (Left c1 t2) t = App (subst c1 t) t2" for c1 t2 t
      | "subst (Right v1 c2) t = App v1 (subst c2 t)" for v1 c2 t
inductive infix_mnmngt :: "term \<Rightarrow> term \<Rightarrow> bool" where
   red_K: "is_context c \<Longrightarrow> is_value v1 \<Longrightarrow> is_value v2 \<Longrightarrow> infix_mnmngt (subst c (App (App K v1) v2)) (subst c v1)" for c :: "context" and v1 :: "term" and v2 :: "term"
 | red_S: "is_context c \<Longrightarrow> is_value v1 \<Longrightarrow> is_value v2 \<Longrightarrow> is_value v3 \<Longrightarrow> infix_mnmngt (subst c (App (App (App S v1) v2) v3)) (subst c (App (App v1 v3) (App v2 v3)))" for c :: "context" and v1 :: "term" and v2 :: "term" and v3 :: "term"
inductive relTR :: "term \<Rightarrow> term \<Rightarrow> bool" where
   BaseTransRefl: "relTR x x" for x :: "term"
 | StepTransRefl: "relTR x y \<Longrightarrow> infix_mnmngt y z \<Longrightarrow> relTR x z" for x :: "term" and y :: "term" and z :: "term"
axiomatization where relTR_transitive:   "relTR x z"
 if "relTR x y"
 and "relTR y z"
  for x :: "term"
  and y :: "term"
  and z :: "term"
datatype  zipper = ZHole | ZLeft "context" "term" | ZRight "term" "context"
fun subst_c :: "context \<Rightarrow> context \<Rightarrow> context"
  where "subst_c Hole ct = ct" for ct
      | "subst_c (Left c1 t2) ct = Left (subst_c c1 ct) t2" for c1 t2 ct
      | "subst_c (Right v1 c2) ct = Right v1 (subst_c c2 ct)" for v1 c2 ct
axiomatization where subst_c'spec:   "is_context (subst_c c ct)"
 if "is_context c"
 and "is_context ct"
  for c :: "context"
  and ct :: "context"
definition irreducible :: "term \<Rightarrow> _"
  where "irreducible t \<longleftrightarrow> (\<forall>(t' :: term). \<not>infix_mnmngt t t')" for t
inductive only_K :: "term \<Rightarrow> bool" where
   only_K_K: "only_K K"
 | only_K_App: "only_K t1 \<Longrightarrow> only_K t2 \<Longrightarrow> only_K (App t1 t2)" for t1 :: "term" and t2 :: "term"
consts ks :: "int \<Rightarrow> term"
axiomatization where ks_def:   "if n = (0 :: int) then ks n = K else ks n = App (ks (n - (1 :: int))) K"
 if "(0 :: int) \<le> n"
  for n :: "int"
axiomatization where ks'spec:   "only_K (ks n)"
 if "(0 :: int) \<le> n"
  for n :: "int"
theorem ks_even_odd'vc:
  fixes n :: "int"
  assumes fact0: "(0 :: int) \<le> n"
  shows "relTR (ks ((2 :: int) * n)) K"
  and "relTR (ks ((2 :: int) * n + (1 :: int))) (App K K)"
  sorry
end
