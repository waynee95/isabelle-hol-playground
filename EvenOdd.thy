theory EvenOdd
  imports Main
begin

thm ccontr

section "Using built-in odd predicate"

lemma 
  assumes 0: "odd n" 
  shows "odd (n * n)"
proof (rule ccontr)
  assume 1: "\<not> odd (n * n)"

  from 0 obtain a where 2: "n = 2 * a + 1"
    using oddE by auto
 
  let ?b = "2 * a * a + 2 * a"

  have "n * n = 2 * ?b + 1"
  proof -
    have "n * n = (2 * a + 1) * (2 * a + 1)"
      using 2 by simp
    moreover have "\<dots> = 4 * a * a + 4 * a + 1"
      using 0 1 by simp
    moreover have "\<dots> = 2 * (2 * a * a + 2 * a) + 1"
      using 0 1 by simp
    moreover have "\<dots> = 2 * ?b + 1"
      by simp
    ultimately show ?thesis
      using 0 1 by simp 
  qed

  then have "odd (n * n)" 
    by simp
  with 1 show False 
    by simp
qed

section "Own predicate for odd numbers"

definition isOdd :: "int \<Rightarrow> bool" where 
"isOdd n \<equiv> \<exists>a. n = 2 * a + 1"

lemma "isOdd 1"
  by (simp add: isOdd_def) 

lemma 
  assumes 0: "isOdd n" 
  shows "isOdd (n * n)"
proof (rule ccontr)
  assume 1: "\<not> isOdd (n * n)"

  from 0 obtain a where 2: "n = 2 * a + 1"
    using isOdd_def by auto
 
  let ?b = "2 * a * a + 2 * a"

  have "n * n = 2 * ?b + 1"
  proof -
    have "n * n = (2 * a + 1) * (2 * a + 1)"
      using 2 by simp
    moreover have "\<dots> = 4 * a * a + 4 * a + 1"
      using 0 1 by (simp add: field_simps)
    moreover have "\<dots> = 2 * (2 * a * a + 2 * a) + 1"
      by simp
    moreover have "\<dots> = 2 * ?b + 1"
      by simp
    ultimately show ?thesis
      by simp
  qed

  then have "isOdd (n * n)"
    using isOdd_def by blast 

  with 1 show False 
    by simp
qed

end