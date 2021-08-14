theory Cantor
  imports Main
begin

text \<open>
  Cantor's theorem states that every set has more subsets than it has element.

  This version of the theorem states for every function from \<alpha> to its powerset,
  some subset is outside its range.
\<close>

(* "automatic" *)
theorem Cantor: "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  by blast

(* "exploring, but unstructured" *)
theorem Cantor': "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
  apply (rule_tac x = "{ x. x \<notin> f x}" in exI)
  apply (rule notI)
  apply clarsimp
  apply blast
  done

(* "structured, explaining" *)
theorem Cantor'': "\<exists>S. S \<notin> range (f :: 'a \<Rightarrow> 'a set)"
proof
  let ?S = "{ x. x \<notin> f x }"
  show "?S \<notin> range f"
  proof
    assume "?S \<in> range f"
    then obtain y where fy: "?S = f y" ..
    show False
    proof cases
      assume "y \<in> ?S"
      hence "y \<notin> f y" by simp
      hence "y \<notin> ?S" by (simp add:fy)
      with \<open>y \<in> ?S\<close> show False by contradiction
    next
      assume "y \<notin> ?S"
      hence "y \<in> f y" by simp
      hence "y \<in> ?S" by (simp add:fy)
      with \<open>y \<notin> ?S\<close> show False by contradiction
    qed
  qed
qed

end