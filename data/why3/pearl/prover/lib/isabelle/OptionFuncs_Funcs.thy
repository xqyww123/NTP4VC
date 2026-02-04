theory OptionFuncs_Funcs
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func"
begin
consts some :: "'a \<Rightarrow> 'a option"
axiomatization where some_def:   "some x = Some x"
  for x :: "'a"
consts ocase :: "('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a option \<Rightarrow> 'b"
axiomatization where ocase_def:   "ocase f d x = (case x of (None :: 'a option) \<Rightarrow> d | Some x1 \<Rightarrow> f x1)"
  for f :: "'a \<Rightarrow> 'b"
  and d :: "'b"
  and x :: "'a option"
definition omap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
  where "omap f x = (case x of (None :: 'a option) \<Rightarrow> (None :: 'b option) | Some x1 \<Rightarrow> Some (f x1))" for f x
definition olift :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a option \<Rightarrow> 'b option"
  where "olift f = ocase (compose some f) (None :: 'b option)" for f
end
