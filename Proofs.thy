theory Proofs
  imports Main
begin

(* Problem: *)
lemma 
  assumes "\<forall>x. \<forall>y. x + y = y + x"
    and "\<forall>x. \<forall>y. \<forall>z. x + (y + z) = (x + y) + z"
    and "\<forall>x. 0 + x = x"
  shows "u + v = 0 \<longrightarrow> (v + w) + u = w"
  term u
proof
  (* from assms(3) have "0 + x = x" *)
  from assms(3) have "0 + (x::'c) = x" by (rule allE)
  oops






(* vollständig manuell *)
lemma 
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<oplus>" 80)
    and e :: 'a
  assumes "\<forall>x. \<forall>y. x \<oplus> y = y \<oplus> x"
    and "\<forall>x. \<forall>y. \<forall>z. x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    and "\<forall>x. e \<oplus> x = x"
  shows "u \<oplus> v = e \<longrightarrow> (v \<oplus> w) \<oplus> u = w"
proof
  assume A: "u \<oplus> v = e"

  thm assms
  thm assms(1)

  (* -------------------------------------------------- *)
  from assms(1) have "\<forall>y. u \<oplus> y = y \<oplus> u" by (rule allE)
  then have comm1: "u \<oplus> v = v \<oplus> u" by (rule allE)

  from assms(1) have "\<forall>y. u \<oplus> y = y \<oplus> u" by (rule allE)
  then have comm2: "u \<oplus> w = w \<oplus> u" by (rule allE)


  from assms(2) have "\<forall>y. \<forall>z. v \<oplus> (y \<oplus> z) = (v \<oplus> y) \<oplus> z" by (rule allE)
  then have "\<forall>z. v \<oplus> (u \<oplus> z) = (v \<oplus> u) \<oplus> z" by (rule allE)
  then have assoc1: "v \<oplus> (u \<oplus> w) = (v \<oplus> u) \<oplus> w" by (rule allE)

  from assms(2) have "\<forall>y. \<forall>z. v \<oplus> (y \<oplus> z) = (v \<oplus> y) \<oplus> z" by (rule allE)
  then have "\<forall>z. v \<oplus> (w \<oplus> z) = (v \<oplus> w) \<oplus> z" by (rule allE)
  then have assoc2: "v \<oplus> (w \<oplus> u) = (v \<oplus> w) \<oplus> u" by (rule allE)
  (* -------------------------------------------------- *)

  from assms(3) have "e \<oplus> w = w" by (rule allE)
  with A have "(u \<oplus> v) \<oplus> w = w" by (rule ssubst)
  with comm1 have "(v \<oplus> u) \<oplus> w = w" by (rule subst)
  with assoc1 have "v \<oplus> u \<oplus> w = w" by (rule ssubst)
  with comm2 have "v \<oplus> (w \<oplus> u) = w" by (rule subst)
  with assoc2 show "(v \<oplus> w) \<oplus> u = w" by (rule subst)
qed






(* mehr automatisiert *)
lemma 
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<oplus>" 80)
    and e :: 'a
  assumes "\<forall>x. \<forall>y. x \<oplus> y = y \<oplus> x"
    and "\<forall>x. \<forall>y. \<forall>z. x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    and "\<forall>x. e \<oplus> x = x"
  shows "u \<oplus> v = e \<longrightarrow> (v \<oplus> w) \<oplus> u = w"
proof
  assume A: "u \<oplus> v = e"

  from assms(3) have "e \<oplus> w = w" ..
  then have "(u \<oplus> v) \<oplus> w = w"
    by (simp add: A) 
  then have "(v \<oplus> u) \<oplus> w = w"
    by (simp add: assms(1))
  then have "v \<oplus> u \<oplus> w = w"
    by (simp add: assms(2)) 
  then have "v \<oplus> (w \<oplus> u) = w"
    by (simp add: assms(1)) 
  then show "(v \<oplus> w) \<oplus> u = w"
    by (simp add: assms(2))
qed

(* vollständig automatisiert *)
lemma 
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixr "\<oplus>" 80)
    and e :: 'a
  assumes "\<forall>x. \<forall>y. x \<oplus> y = y \<oplus> x"
    and "\<forall>x. \<forall>y. \<forall>z. x \<oplus> (y \<oplus> z) = (x \<oplus> y) \<oplus> z"
    and "\<forall>x. e \<oplus> x = x"
  shows "u \<oplus> v = e \<longrightarrow> (v \<oplus> w) \<oplus> u = w"
  by (simp add: assms)

end