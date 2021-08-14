theory Ex
  imports Main
begin

prop "map (\<lambda>n. Suc n + 1) [0, 1] = [2,3]"
term "map (\<lambda>n. Suc n + 1) [0, 1] = [2,3]"
value "map (\<lambda>n. Suc n + 1) [0, 1] = [2,3]"

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where
"mirror Tip = Tip" |
"mirror (Node left x right) = Node (mirror left) x (mirror right)"

lemma "mirror (mirror t) = t"
  apply (induction t)
   apply (auto)
  done

end