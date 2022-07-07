theory Geometric_Series
  imports Complex_Main
begin

(* manually *)
lemma 
  assumes "(r::real) \<noteq> 1"
  shows "(\<Sum>k=0..n. r^k) = ((1 - r^(n+1)) / (1 - r))"
  using assms
proof (induction n) 
  case (Suc n)
  have "(\<Sum>k=0..Suc n. r^k) = (\<Sum>k=0..n. r^k) + r^(n+1)" 
    by simp
  also have "\<dots> = (\<Sum>k=0..n. r^k) + (((1 - r) * r^(n+1)) / (1 - r))"
    using assms by simp
  also have "\<dots> = ((1 - r^(n+1)) / (1 - r )) + (((1 - r) * r^(n+1)) / (1 - r))"
    using Suc.IH assms by simp 
  also have "\<dots> = (1 - r^(Suc n + 1)) / (1 - r)"
   by (simp add: algebra_simps diff_divide_distrib)
  finally show ?case .
qed auto
    

(* automatic *)
lemma 
  assumes "(r::real) \<noteq> 1"
  shows "(\<Sum>k=0..n. r^k) = ((1 - r^(n+1)) / (1 - r))"
  by (metis Suc_eq_plus1 assms atLeast0AtMost sum_gp0)
 
end