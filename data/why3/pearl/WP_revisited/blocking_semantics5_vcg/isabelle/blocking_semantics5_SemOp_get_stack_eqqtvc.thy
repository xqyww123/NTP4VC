theory blocking_semantics5_SemOp_get_stack_eqqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_WP_revisited_lib.blocking_semantics5_Syntax"
begin
typedecl  env
typedecl  stack
fun get_stack :: "ident \<Rightarrow> (ident \<times> value) list \<Rightarrow> value"
  where "get_stack i (Nil :: (ident \<times> value) list) = Vvoid" for i
      | "get_stack i (Cons (x, v) r) = (if x = i then v else get_stack i r)" for i x v r
theorem get_stack_eq'vc:
  fixes x :: "ident"
  fixes v :: "value"
  fixes r :: "(ident \<times> value) list"
  shows "get_stack x (Cons (x, v) r) = v"
  sorry
end
