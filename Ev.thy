theory Ev
  imports Main
begin

(* "inductive evenness" *)
inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "ev(Suc(Suc(Suc(Suc(Suc(Suc 0))))))"
  apply (rule evSS)+
  apply (rule ev0)
  done

(* "recursive evenness" *)
fun evn :: "nat \<Rightarrow> bool" where
"evn 0 = True" |
"evn (Suc 0) = False" |
"evn (Suc(Suc n)) = evn n"

lemma "ev m \<Longrightarrow> evn m"
  apply (induction rule: ev.induct)
  apply (simp_all)
  done

lemma "evn m \<Longrightarrow> ev m"
  apply (induction rule: evn.induct)
  apply (simp_all add: ev0 evSS)
  done

end