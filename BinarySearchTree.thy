theory BinarySearchTree
  imports Main
begin

declare [[names_short]]

type_synonym key = nat

datatype 'v bst = Leaf | Node "'v bst" key 'v "'v bst"

definition ex1 where
"ex1 \<equiv> (Node (Node Leaf 2 ''two'' Leaf) 4 ''four'' (Node Leaf 5 ''five'' Leaf))"

fun insert :: "'v bst \<Rightarrow> key \<Rightarrow> 'v \<Rightarrow> 'v bst" where
"insert Leaf x v = Node Leaf x v Leaf" |
"insert (Node l y v' r) x v = (if x < y then Node (insert l x v) y v' r
                               else if x > y then Node l y v' (insert r x v)
                               else (Node l x v r))"

fun forallT :: "(key \<Rightarrow> 'v \<Rightarrow> bool) \<Rightarrow> 'v bst \<Rightarrow> bool" where
"forallT P Leaf = True" |
"forallT P (Node l k v r) = (P k v \<and> forallT P l \<and> forallT P r)"

inductive is_bst :: "'v bst \<Rightarrow> bool" where
is_bst_leaf: "is_bst Leaf" |
is_bst_node: "\<lbrakk> forallT (\<lambda> y _. y < x) l; forallT (\<lambda> y _. y > x) r; is_bst l; is_bst r \<rbrakk> 
  \<Longrightarrow>  is_bst (Node l x v r)"

lemma "is_bst ex1"
  unfolding ex1_def
  apply (rule is_bst_node)
     apply simp+
   apply (rule is_bst_node)
      apply simp+
    apply (rule is_bst_leaf)
   apply (rule is_bst_leaf)
  apply (rule is_bst_node)
     apply simp+
   apply (rule is_bst_leaf)
  apply (rule is_bst_leaf)
  done

lemma forallT_insert: "\<lbrakk> forallT P t; P k v \<rbrakk> \<Longrightarrow> forallT P (insert t k v)"
  apply (induction t)
   apply auto
  done

theorem "is_bst t \<Longrightarrow> is_bst (insert t k v)"
proof (induction t)
  case Leaf
  then show ?case
    by (simp add: is_bst_node) 
next
  case (Node l y v' r)
  then show ?case
    using forallT_insert
    by (smt (z3) bst.distinct(1) bst.inject insert.simps(2) is_bst.simps not_less_iff_gr_or_eq) 
qed

end