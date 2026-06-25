theory defunctionalization_SemWithError_cps_correctqtvc
  imports "NTP4Verif.NTP4Verif" "./defunctionalization_Expr"
begin
datatype  "value" = Vnum "int" | Underflow
fun eval_0 :: "expr \<Rightarrow> value"
  where "eval_0 (Cte n) = (if (0 :: int) \<le> n then Vnum n else Underflow)" for n
      | "eval_0 (Sub e1 e2) = (case eval_0 e1 of Underflow \<Rightarrow> Underflow | Vnum v1 \<Rightarrow> (case eval_0 e2 of Underflow \<Rightarrow> Underflow | Vnum v2 \<Rightarrow> (if v2 \<le> v1 then Vnum (v1 - v2) else Underflow)))" for e1 e2
consts fc :: "(value \<Rightarrow> 'a) \<Rightarrow> int \<Rightarrow> value \<Rightarrow> 'a"
consts fc1 :: "(value \<Rightarrow> 'a) \<Rightarrow> expr \<Rightarrow> value \<Rightarrow> 'a"
axiomatization where fc_def:   "fc k v1 v2 = (case v2 of Underflow \<Rightarrow> k Underflow | Vnum v21 \<Rightarrow> k (if v21 \<le> v1 then Vnum (v1 - v21) else Underflow))"
  for k :: "value \<Rightarrow> 'a"
  and v1 :: "int"
  and v2 :: "value"
fun eval_1 :: "expr \<Rightarrow> (value \<Rightarrow> 'a) \<Rightarrow> 'a"
  where "eval_1 (Cte n) k = k (if (0 :: int) \<le> n then Vnum n else Underflow)" for n k
      | "eval_1 (Sub e1 e2) k = eval_1 e1 (fc1 k e2)" for e1 e2 k
axiomatization where fc1_def:   "fc1 k e2 v1 = (case v1 of Underflow \<Rightarrow> k Underflow | Vnum v11 \<Rightarrow> eval_1 e2 (fc k v11))"
  for k :: "value \<Rightarrow> 'a"
  and e2 :: "expr"
  and v1 :: "value"
consts identity :: "value \<Rightarrow> value"
axiomatization where identity_def:   "identity y = y"
  for y :: "value"
definition interpret_1 :: "expr \<Rightarrow> value"
  where "interpret_1 p = eval_1 p identity" for p
theorem cps_correct'vc:
  fixes p :: "expr"
  shows "interpret_1 p = eval_0 p"
  sorry
end
