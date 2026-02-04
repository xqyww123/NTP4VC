theory BacktrackArray_Logic
  imports "NTP4Verif.NTP4Verif" "../../lib/isabelle/BacktrackArray_Types" "../../lib/isabelle/Functions_Config" "../../lib/isabelle/Functions_Func" "../../lib/isabelle/Predicates_Pred" "../../lib/isabelle/Choice_Choice"
begin
consts func_of_array :: "'a list \<Rightarrow> 'a \<Rightarrow> int \<Rightarrow> 'a"
axiomatization where func_of_array_def:   "func_of_array a def1 x = (if (0 :: int) \<le> x \<and> x < int (length a) then (nth a o nat) x else def1)"
  for a :: "'a list"
  and def1 :: "'a"
  and x :: "int"
definition current_timestamp :: "'a t \<Rightarrow> 'a timestamp"
  where "current_timestamp x = timestamp'mk (current_time x) (int (length (buffer x))) (func_of_array (buffer x) (Nil :: 'a list))" for x
definition correct_table :: "int \<Rightarrow> (int \<Rightarrow> 'a list) \<Rightarrow> _"
  where "correct_table sz b \<longleftrightarrow> (\<forall>(x :: int). sz \<le> x \<or> x < (0 :: int) \<longrightarrow> b x = (Nil :: 'a list))" for sz b
definition pop :: "'a list \<Rightarrow> 'a list"
  where "pop l = (case l of (Nil :: 'a list) \<Rightarrow> (default :: 'a list) | Cons x_x q \<Rightarrow> q)" for l
fun unroll :: "int \<Rightarrow> int \<Rightarrow> int list \<Rightarrow> (int \<Rightarrow> 'a list) \<Rightarrow> int \<Rightarrow> 'a timestamp"
  where "unroll tm t0 h b sz = (if tm = (0 :: int) then timestamp'mk t0 sz b else (case h of Nil \<Rightarrow> timestamp'mk (t0 + tm) sz b | Cons x q \<Rightarrow> (if x = -(1 :: int) then unroll (tm - (1 :: int)) t0 q b (sz cdiv (2 :: int)) else unroll (tm - (1 :: int)) t0 q (update b x (pop (b x))) sz)))" for tm t0 h b sz
fun unroll_correct :: "int \<Rightarrow> int list \<Rightarrow> (int \<Rightarrow> 'a list) \<Rightarrow> int \<Rightarrow> _"
  where "unroll_correct tm (Nil :: int list) b sz = (tm = (0 :: int))" for tm b sz
      | "unroll_correct tm (Cons x q) b sz = (if x = -(1 :: int) then let s0 :: int = sz cdiv (2 :: int) in s0 * (2 :: int) = sz \<and> unroll_correct (tm - (1 :: int)) q b s0 \<and> (\<forall>(i :: int). s0 \<le> i \<or> i < (0 :: int) \<longrightarrow> b i = (Nil :: 'a list)) else \<not>b x = (Nil :: 'a list) \<and> ((0 :: int) \<le> x \<and> x < sz) \<and> unroll_correct (tm - (1 :: int)) q (update b x (pop (b x))) sz)" for tm x q b sz
definition past_time :: "'a timestamp \<Rightarrow> 'a t \<Rightarrow> _"
  where "past_time t tb \<longleftrightarrow> time t \<le> current_time tb \<and> unroll (current_time tb - time t) (time t) (history tb) (func_of_array (buffer tb) (Nil :: 'a list)) (int (length (buffer tb))) = t" for t tb
definition precede :: "'a t \<Rightarrow> 'a t \<Rightarrow> _"
  where "precede tb1 tb2 \<longleftrightarrow> (\<forall>(t :: 'a timestamp). past_time t tb1 \<longrightarrow> past_time t tb2)" for tb1 tb2
definition before :: "'a timestamp \<Rightarrow> 'a timestamp \<Rightarrow> _"
  where "before t1 t2 \<longleftrightarrow> time t1 \<le> time t2" for t1 t2
fun list_forall :: "('a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> _"
  where "list_forall p (Nil :: 'a list) = True" for p
      | "list_forall p (Cons x q) = (p x = True \<and> list_forall p q)" for p x q
definition correct :: "'a t \<Rightarrow> _"
  where "correct tb \<longleftrightarrow> (\<forall>(t :: 'a timestamp). past_time t tb \<longrightarrow> (0 :: int) < BacktrackArray_Types.size t) \<and> (\<forall>(t :: 'a timestamp) (i :: int). past_time t tb \<and> (0 :: int) \<le> i \<longrightarrow> list_forall (inv tb) (table t i)) \<and> (\<forall>(t :: 'a timestamp). past_time t tb \<longrightarrow> correct_table (BacktrackArray_Types.size t) (table t)) \<and> unroll_correct (current_time tb) (history tb) (func_of_array (buffer tb) (Nil :: 'a list)) (int (length (buffer tb)))" for tb
definition backtrack_to :: "'a t \<Rightarrow> 'a t \<Rightarrow> 'a t \<Rightarrow> _"
  where "backtrack_to tbold tbinter tbnew \<longleftrightarrow> (\<forall>(tm :: 'a timestamp). past_time tm tbold \<longrightarrow> past_time tm tbinter \<and> time tm \<le> time (current_timestamp tbold) \<and> time tm \<le> time (current_timestamp tbnew) \<and> before tm (current_timestamp tbnew) \<and> past_time tm tbnew) \<and> (\<forall>(tm :: 'a timestamp). past_time tm tbold \<longrightarrow> past_time tm tbnew) \<and> precede tbold tbnew" for tbold tbinter tbnew
end
