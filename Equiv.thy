theory Equiv
  imports Main
begin

type_synonym 'a rel = "('a \<times> 'a) set"

definition refl :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "refl S r \<longleftrightarrow> (\<forall>x. x \<in> S \<longrightarrow> (x, x) \<in> r)"

definition sym :: "'a rel \<Rightarrow> bool" where 
  "sym r \<longleftrightarrow> (\<forall>x y. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"

definition trans :: "'a rel \<Rightarrow> bool" where
  "trans r \<longleftrightarrow> (\<forall>x y z. (x, y) \<in> r \<and> (y, z) \<in> r \<longrightarrow> (x, z) \<in> r)"

definition equiv :: "'a set \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "equiv S r \<longleftrightarrow> (refl S r \<and> sym r \<and> trans r)" 
end
