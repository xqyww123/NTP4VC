theory blocking_semantics5_WP_distrib_conjqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax" "pearl_WP_revisited_lib.blocking_semantics5_SemOp" "pearl_WP_revisited_lib.blocking_semantics5_Typing" "pearl_WP_revisited_lib.blocking_semantics5_TypingAndSemantics" "pearl_WP_revisited_lib.blocking_semantics5_FreshVariables"
begin
consts fresh_from :: "fmla \<Rightarrow> ident"
axiomatization where fresh_from_fmla:   "fresh_in_fmla (fresh_from f) f"
  for f :: "fmla"
consts abstract_effects :: "stmt \<Rightarrow> fmla \<Rightarrow> fmla"
axiomatization where abstract_effects_specialize:   "eval_fmla sigma pi f"
 if "eval_fmla sigma pi (abstract_effects s f)"
  for sigma :: "mident \<Rightarrow> value"
  and pi :: "(ident \<times> value) list"
  and s :: "stmt"
  and f :: "fmla"
axiomatization where abstract_effects_distrib_conj:   "eval_fmla sigma pi (abstract_effects s (Fand p q))"
 if "eval_fmla sigma pi (abstract_effects s p)"
 and "eval_fmla sigma pi (abstract_effects s q)"
  for sigma :: "mident \<Rightarrow> value"
  and pi :: "(ident \<times> value) list"
  and s :: "stmt"
  and p :: "fmla"
  and q :: "fmla"
axiomatization where abstract_effects_monotonic:   "eval_fmla sigma pi (abstract_effects s q)"
 if "valid_fmla (Fimplies p q)"
 and "eval_fmla sigma pi (abstract_effects s p)"
  for p :: "fmla"
  and q :: "fmla"
  and sigma :: "mident \<Rightarrow> value"
  and pi :: "(ident \<times> value) list"
  and s :: "stmt"
fun wp :: "stmt \<Rightarrow> fmla \<Rightarrow> fmla"
  where "wp Sskip q = q" for q
      | "wp (Sassert f) q = Fand f (Fimplies f q)" for f q
      | "wp (Sseq s1 s2) q = wp s1 (wp s2 q)" for s1 s2 q
      | "wp (Sassign x t) q = (let id1 :: ident = fresh_from q in Flet id1 t (msubst q x id1))" for x t q
      | "wp (Sif t s1 s2) q = Fand (Fimplies (Fterm t) (wp s1 q)) (Fimplies (Fnot (Fterm t)) (wp s2 q))" for t s1 s2 q
      | "wp (Swhile cond inv body) q = Fand inv (abstract_effects body (Fand (Fimplies (Fand (Fterm cond) inv) (wp body inv)) (Fimplies (Fand (Fnot (Fterm cond)) inv) q)))" for cond inv body q
axiomatization where abstract_effects_writes:   "eval_fmla sigma pi (abstract_effects body (Fand (Fimplies (Fand (Fterm cond) inv) (wp body inv)) (Fimplies (Fand (Fnot (Fterm cond)) inv) q))) \<longrightarrow> eval_fmla sigma pi (wp body (abstract_effects body (Fand (Fimplies (Fand (Fterm cond) inv) (wp body inv)) (Fimplies (Fand (Fnot (Fterm cond)) inv) q))))"
  for body :: "stmt"
  and cond :: "term"
  and inv :: "fmla"
  and q :: "fmla"
  and sigma :: "mident \<Rightarrow> value"
  and pi :: "(ident \<times> value) list"
theorem distrib_conj'vc:
  fixes sigma :: "mident \<Rightarrow> value"
  fixes pi :: "(ident \<times> value) list"
  fixes s :: "stmt"
  fixes p :: "fmla"
  fixes q :: "fmla"
  assumes fact0: "eval_fmla sigma pi (wp s p)"
  assumes fact1: "eval_fmla sigma pi (wp s q)"
  shows "eval_fmla sigma pi (wp s (Fand p q))"
  sorry
end
