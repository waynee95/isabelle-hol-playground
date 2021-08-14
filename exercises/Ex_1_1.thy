theory Ex_1_1
  imports Main
begin

primrec snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (x # xs) a = x # snoc xs a"

value "snoc [] a = [a]"
value "snoc [a,b,c] d = [a,b,c,d]"

lemma snoc_append[simp]: "snoc xs a = xs @ [a]"
  apply (induction xs)
   apply (auto)
  done

theorem rev_cons: "rev (x # xs) = snoc (rev xs) x"
  apply (induction xs)
  apply (auto)
  done

end