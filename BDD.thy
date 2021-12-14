theory BDD
  imports Main
begin

datatype bdd = Leaf bool | Branch bdd bdd

primrec eval :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> bdd \<Rightarrow> bool" where
"eval e i (Leaf v) = v" |
"eval e i (Branch b1 b2) = 
  (if e i then eval e (Suc i) b2 else eval e (Suc i) b2)"

primrec bdd_unop :: "(bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_unop f (Leaf v) = Leaf (f v)" |
"bdd_unop f (Branch b1 b2) = Branch (bdd_unop f b1) (bdd_unop f b2)"

primrec bdd_binop :: "(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> bdd \<Rightarrow> bdd \<Rightarrow> bdd" where
"bdd_binop f (Leaf v) b = bdd_unop (f v) b" |
"bdd_binop f (Branch b1 b2) b = (case b of 
    Leaf v \<Rightarrow> Branch (bdd_binop f b1 (Leaf v)) (bdd_binop f b2 (Leaf v))
  | Branch b1' b2' \<Rightarrow> Branch (bdd_binop f b1 b1') (bdd_binop f b2 b2'))"

theorem bdd_unop_correct: "\<forall>i. eval e i (bdd_unop f b) = f (eval e i b)"
  apply (induction b)
   apply (auto)
  done

theorem bdd_binop_correct: "\<forall>i b2. eval e i (bdd_binop f b1 b2) = f (eval e i b1) (eval e i b2)"
  apply (induction b1)
   apply (auto split: bdd.split)
   apply (auto simp add: bdd_unop_correct)
  done

end