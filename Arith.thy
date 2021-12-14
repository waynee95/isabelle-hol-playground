theory Arith
  imports Main
begin

primrec pow :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"pow x 0 = Suc 0" |
"pow x (Suc n) = x * pow x n"

value "pow 2 2"
value "pow 3 2"
value "pow 2 8" 

lemma pow_add: "pow x (m + n) = pow x m * pow x n"
  apply (induction n)
   apply (auto)
  done

theorem pow_mult: "pow x (m * n) = pow (pow x m) n"
  apply (induction n)
  apply (auto simp add: pow_add)
  done

primrec sum :: "nat list \<Rightarrow> nat" where
"sum [] = 0" |
"sum (x # xs) = x + sum xs"

value "sum [1,2,3]"
value "sum []"

lemma sum_append: "sum (xs @ ys) = sum xs + sum ys"
  apply (induction xs)
  apply (auto)
  done

theorem sum_rev: "sum (rev xs) = sum xs"
  apply (induction xs)
   apply (auto simp add: sum_append)
  done

primrec Sum :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"Sum f 0 = 0" |
"Sum f (Suc n) = f n + Sum f n"

theorem "Sum (\<lambda>i. f i + g i) k = Sum f k + Sum g k"
  apply (induction k)
   apply (auto)
  done

theorem "Sum f (k + l) = Sum f k + Sum (\<lambda>i. f (k + i)) l"
  apply (induction l)
   apply (auto)
  done

theorem "Sum f k = sum (map f [0..<k])"
  apply (induction k)
   apply (auto simp add: sum_append)
  done

end