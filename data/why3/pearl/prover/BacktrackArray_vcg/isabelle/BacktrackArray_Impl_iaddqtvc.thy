theory BacktrackArray_Impl_iaddqtvc
  imports "NTP4Verif.NTP4Verif" "pearl_prover_lib.BacktrackArray_Types" "pearl_prover_lib.Functions_Config" "pearl_prover_lib.Functions_Func" "pearl_prover_lib.Predicates_Pred" "pearl_prover_lib.BacktrackArray_Logic" "pearl_prover_lib.Choice_Choice"
begin
theorem iadd'vc:
  fixes x :: "int"
  fixes tb :: "'a t"
  fixes b :: "'a"
  assumes fact0: "(0 :: int) \<le> x"
  assumes fact1: "x < int (length (buffer tb))"
  assumes fact2: "correct tb"
  assumes fact3: "inv tb b = True"
  shows "let buf :: 'a list list = buffer tb in ((0 :: int) \<le> x \<and> x < int (length buf)) \<and> (let o1 :: 'a list = Cons b (buf ! nat x) in ((0 :: int) \<le> x \<and> x < int (length buf)) \<and> (length (buf[nat x := o1]) = length buf \<longrightarrow> length (buf[nat x := o1]) = length (buffer tb) \<longrightarrow> nth (buf[nat x := o1]) o nat = (nth buf o nat)(x := o1) \<longrightarrow> (\<forall>(tb1 :: 'a t). buffer tb1 = buffer (t'mk (history tb) (current_time tb) (buf[nat x := o1]) (inv tb)) \<and> inv tb1 = inv (t'mk (history tb) (current_time tb) (buf[nat x := o1]) (inv tb)) \<longrightarrow> history tb1 = Cons x (history (t'mk (history tb) (current_time tb) (buf[nat x := o1]) (inv tb))) \<and> current_time tb1 = current_time (t'mk (history tb) (current_time tb) (buf[nat x := o1]) (inv tb)) + (1 :: int) \<longrightarrow> past_time (current_timestamp tb1) tb1 \<and> correct tb1 \<and> precede tb tb1 \<and> (let tb0 :: int \<Rightarrow> 'a list = table (current_timestamp tb) in table (current_timestamp tb1) = update tb0 x (Cons b (tb0 x))))))"
  sorry
end
