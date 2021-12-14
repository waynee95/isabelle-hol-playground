theory Div2_Induction
  imports Main
begin

fun div2 :: "nat \<Rightarrow> nat" where
"div2 0 = 0" |
"div2 (Suc 0) = 0" |
"div2 (Suc (Suc n)) = Suc (div2 n)"

(* with normal structural induction, auto cannot finish off the proof *)
lemma "div2 n = n div 2"
  apply(induction n)
   apply (auto)
  oops 

(* explicitly tell Isabelle to use induction rule for div2, then auto can finish off the proof *)
lemma "div2 n = n div 2"
  apply (induction n rule: div2.induct)
  apply (auto)
  done

(* IH not strong enough to prove this *)
lemma "div2 n = n div 2"
  apply (induction n)
  subgoal by simp
  subgoal for m
    apply (cases m)
     apply simp
    oops

(* instead prove a strong lemma *)
lemma "div2 n = n div 2 \<and> div2 (Suc n) = (Suc n) div 2"
  apply (induction n)
  apply (auto)
  done

(* or use a stronger induction rule *)
lemma "div2 n = n div 2"
  apply (induction n rule: less_induct)
  subgoal for n
    apply (cases n)
    subgoal by simp
    subgoal for m
      apply (cases m)
       apply (auto)
      done
    done
  done

(* TODO: better write this in Isar *)

end