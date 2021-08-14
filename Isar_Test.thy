theory Isar_Test
  imports Main
begin

lemma 
  fixes f :: "'a \<Rightarrow> 'a set"
  assumes s: "surj f"
  shows "False"
proof -
  have "\<exists> a. { x. x \<notin> f(x) } = f a" using s
    by (auto simp: surj_def)
  thus "False" by blast
qed

end