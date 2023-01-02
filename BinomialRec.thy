theory BinomialRec
  imports Main
begin

fun binomial :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"binomial _ 0 = 1" |
"binomial 0 _ = 0" |
"binomial (Suc n) (Suc k) = (if k \<ge> n then 1 else (binomial n (Suc k)) + (binomial n k))"

lemma binomial_n_n: "binomial n n = 1"
  by (induction n) auto

lemma "k \<le> n \<Longrightarrow> binomial n k = binomial n (n-k)"
proof (induction n k rule: binomial.induct)
  case (1 n)
  then show ?case
    by (simp add: binomial_n_n)
next
  case (2 k)
  then show ?case
    by simp
next
  case (3 n k)
  then show ?case
  proof (cases "k \<ge> n")
    case True
    then show ?thesis
      by simp
  next
    case False
    then have "k < n"
      by simp
    then have "binomial (Suc n) (Suc k) = binomial n (Suc k) + binomial n k"
      by simp
    also have "\<dots> = binomial n (n - Suc k) + binomial n k"
      using "3.IH" \<open>k < n\<close> by auto
    also have "\<dots> = binomial n (n - k) + binomial n (n - Suc k)"
      using "3.IH" \<open>k < n\<close> by auto
    also have "\<dots> = binomial (Suc n) (Suc n - Suc k)"
      using \<open>k < n\<close> less_iff_Suc_add by auto
    finally show ?thesis
      by simp
  qed
qed

end