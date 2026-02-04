theory ISet_Logic
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/ISet_Types" "../../lib/isabelle/Functions_Config"
begin
inductive iset_ok :: "int list \<Rightarrow> bool" where
   Set_empty: "iset_ok (Nil :: int list)"
 | Set_one: "iset_ok (Cons x (Nil :: int list))" for x :: "int"
 | Set_two: "iset_ok (Cons y q) \<Longrightarrow> x < y \<Longrightarrow> iset_ok (Cons x (Cons y q))" for y :: "int" and q :: "int list" and x :: "int"
end
