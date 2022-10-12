theory DFA_NFA
  imports Main "HOL-Library.FSet"
begin

(* from: https://arxiv.org/pdf/1505.01662.pdf *)

record 'a dfa = 
  states :: "nat fset"
  init :: "nat"
  final :: "nat fset"
  trans :: "nat \<Rightarrow> 'a \<Rightarrow> nat"

locale dfa =
  fixes M :: "'a dfa"
  assumes init: "init M |\<in>| states M"
      and final: "final M |\<subseteq>| states M"
      and trans: "\<And>q x. q |\<in>| states M \<Longrightarrow> trans M q x |\<in>| states M"
begin

fun transl :: "nat \<Rightarrow> 'a list \<Rightarrow> nat" where
"transl q [] = q" |
"transl q (a#as) = transl (trans M q a) as"

definition language :: "('a list) set" where
"language \<equiv> {as. transl (init M) as |\<in>| final M}"

end \<comment> \<open>end context\<close>

definition regular :: "('a list) set \<Rightarrow> bool" where
"regular L \<equiv> \<exists>M. dfa M \<and> dfa.language M = L"

end