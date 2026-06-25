theory register_allocation_Spec
  imports "NTP4Verif.NTP4Verif"
begin
typedecl  addr
datatype  expr = Evar "addr" | Eneg "expr" | Eadd "expr" "expr"
typedecl  memory
fun eval :: "(addr \<Rightarrow> int) \<Rightarrow> expr \<Rightarrow> int"
  where "eval m (Evar x) = m x" for m x
      | "eval m (Eneg e1) = -eval m e1" for m e1
      | "eval m (Eadd e1 e2) = eval m e1 + eval m e2" for m e1 e2
typedecl  register
datatype  instr = Iload "addr" "int" | Ineg "int" | Iadd "int" "int" | Ipush "int" | Ipop "int"
typedecl  registers
consts update :: "(int \<Rightarrow> int) \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int"
axiomatization where update_def:   "update reg1 r v r' = (if r' = r then v else reg1 r')"
  for reg1 :: "int \<Rightarrow> int"
  and r :: "int"
  and v :: "int"
  and r' :: "int"
typedecl  stack
datatype  state = state'mk (mem: "addr \<Rightarrow> int") (reg: "int \<Rightarrow> int") (st: "int list")
definition exec :: "instr \<Rightarrow> state \<Rightarrow> state"
  where "exec i s = (case i of Iload x r \<Rightarrow> state'mk (mem s) (update (reg s) r (mem s x)) (st s) | Ineg r \<Rightarrow> state'mk (mem s) (update (reg s) r (-reg s r)) (st s) | Iadd r1 r2 \<Rightarrow> state'mk (mem s) (update (reg s) r2 (reg s r1 + reg s r2)) (st s) | Ipush r \<Rightarrow> state'mk (mem s) (reg s) (Cons (reg s r) (st s)) | Ipop r \<Rightarrow> (case st s of Nil \<Rightarrow> s | Cons v st1 \<Rightarrow> state'mk (mem s) (update (reg s) r v) st1))" for i s
typedecl  code
fun exec_list :: "instr list \<Rightarrow> state \<Rightarrow> state"
  where "exec_list (Nil :: instr list) s = s" for s
      | "exec_list (Cons i l) s = exec_list l (exec i s)" for i l s
consts expr_post :: "expr \<Rightarrow> int \<Rightarrow> state \<Rightarrow> state \<Rightarrow> bool"
axiomatization where expr_post_def:   "expr_post e r s s' = True \<longleftrightarrow> mem s' = mem s \<and> reg s' r = eval (mem s) e \<and> st s' = st s \<and> (\<forall>(r' :: int). r' < r \<longrightarrow> reg s' r' = reg s r')"
  for e :: "expr"
  and r :: "int"
  and s :: "state"
  and s' :: "state"
end
