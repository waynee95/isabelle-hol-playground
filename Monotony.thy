theory Monotony
  imports Main
begin

type_synonym variable = string

datatype bexpr =
    Const bool
  | Var variable
  | And bexpr bexpr
  | Or bexpr bexpr
  | Imp bexpr bexpr
  | Neg bexpr

datatype occ =
    Even
  | Odd
  | Both

fun negate :: "occ \<Rightarrow> occ" where
"negate Even = Odd" |
"negate Odd = Even" |
"negate Both = Both"

fun merge :: "occ \<Rightarrow> occ \<Rightarrow> occ" where
"merge x y = (if x = y then x else Both)"

primrec occurrences :: "bexpr \<Rightarrow> variable \<Rightarrow> occ" where
"occurrences (Const _) _ = Even" |
"occurrences (Var y) x = Even" |
"occurrences (And phi psi) x = (merge (occurrences phi x) (occurrences psi x))" |
"occurrences (Or phi psi) x = (merge (occurrences phi x) (occurrences psi x))" |
"occurrences (Imp phi psi) x = (merge (negate (occurrences phi x)) (occurrences psi x))" |
"occurrences (Neg phi) x = (negate (occurrences phi x))"

type_synonym environment = "string \<Rightarrow> bool"

fun update :: "environment \<Rightarrow> variable \<Rightarrow> bool \<Rightarrow> environment" where
"update env x b y = (if y = x then b else env y)"

fun update2 :: "environment \<Rightarrow> variable \<Rightarrow> bool \<Rightarrow> environment" where
"update2 env x b = (\<lambda>y. (if y = x then b else env y))"

fun update3 :: "environment \<Rightarrow> variable \<Rightarrow> bool \<Rightarrow> environment" where
"update3 env x = (\<lambda>b. (\<lambda>y. (if y = x then b else env y)))"

definition env0 :: environment where
"env0 _ \<equiv> False"

value "(update env0 ''x'' True) ''y''"

primrec eval :: "bexpr \<Rightarrow> environment \<Rightarrow> bool" where
"eval (Const b) _ = b" |
"eval (Var x) env = (env x)" |
"eval (And phi psi) env = ((eval phi env) \<and> (eval psi env))" |
"eval (Or phi psi) env = ((eval phi env) \<or> (eval psi env))" |
"eval (Imp phi psi) env = ((eval phi env) \<longrightarrow> (eval psi env))" |
"eval (Neg phi) env = (\<not> (eval phi env))"

definition monotonic_in :: "bexpr \<Rightarrow> variable \<Rightarrow> bool" where
"monotonic_in phi x \<equiv> \<forall>env. (eval phi (update env x False)) \<longrightarrow> (eval phi (update env x True))"

definition antitonic_in :: "bexpr \<Rightarrow> variable \<Rightarrow> bool" where
"antitonic_in phi x \<equiv>  \<forall>env. (eval phi (update env x True)) \<longrightarrow> (eval phi (update env x False))"




lemma mergeBothEven: "merge x y = Even \<longrightarrow> x = Even \<and> y = Even"
  by simp

lemma mergeBothOdd: "merge x y = Odd \<longrightarrow> x = Odd \<and> y = Odd"
  by simp

lemma negateOccEvenIsOdd: "negate (occurrences phi x) = Even \<longrightarrow> occurrences phi x = Odd"
  using negate.elims by auto
 
lemma negateOccOddIsEven: "negate (occurrences phi x) = Odd \<longrightarrow> occurrences phi x = Even"
  using negate.elims by auto

lemma occNegEvenIsOdd: "occurrences (Neg phi) x = Even \<longrightarrow> occurrences phi x = Odd"
  using negateOccEvenIsOdd by auto

lemma occNegOddIsEven: "occurrences (Neg phi) x = Odd \<longrightarrow> occurrences phi x = Even"
  using negateOccOddIsEven by auto
  
  

lemma aux: "((occurrences phi x = Even) \<longrightarrow> (monotonic_in phi x)) \<and>
            ((occurrences phi x = Odd) \<longrightarrow> (antitonic_in phi x))"
proof (induction phi arbitrary: x)
  case (Const x)
  show ?case by (simp add: monotonic_in_def antitonic_in_def)
next
  case (Var x)
  show ?case by (simp add: monotonic_in_def antitonic_in_def)
next
  case (And phi1 phi2)
  show ?case
  proof
    show "occurrences (And phi1 phi2) x = Even \<longrightarrow> monotonic_in (And phi1 phi2) x"
    proof (rule impI)
      assume "occurrences (And phi1 phi2) x = Even"
      then have "merge (occurrences phi1 x) (occurrences phi2 x) = Even" 
        by simp
      then have bothEven: "occurrences phi1 x = Even \<and> occurrences phi2 x = Even"
        using mergeBothEven by blast
      from bothEven have "occurrences phi1 x = Even" ..
      with And.IH have mono1: "monotonic_in phi1 x" 
        by simp
      from bothEven have "occurrences phi2 x = Even" ..
      with And.IH have mono2: "monotonic_in phi2 x"
        by simp
      from mono1 mono2 show "monotonic_in (And phi1 phi2) x"
        by (simp add: monotonic_in_def)
    qed

    show "occurrences (And phi1 phi2) x = Odd \<longrightarrow> antitonic_in (And phi1 phi2) x"
    proof (rule impI)
      assume "occurrences (And phi1 phi2) x = Odd"
      then have "merge (occurrences phi1 x) (occurrences phi2 x) = Odd" 
        by simp
      then have bothOdd: "occurrences phi1 x = Odd \<and> occurrences phi2 x = Odd"
        using mergeBothOdd by blast
      from bothOdd have "occurrences phi1 x = Odd" ..
      with And.IH have anti1: "antitonic_in phi1 x"
        by simp
      from bothOdd have "occurrences phi2 x = Odd" ..
      with And.IH have anti2: "antitonic_in phi2 x" 
        by simp
      from anti1 anti2 show "antitonic_in (And phi1 phi2) x"
        by (simp add: antitonic_in_def)
    qed
  qed
next
  case (Or phi1 phi2)
  show ?case
  proof
    show "occurrences (Or phi1 phi2) x = Even \<longrightarrow> monotonic_in (Or phi1 phi2) x" 
    proof
      assume "occurrences (Or phi1 phi2) x = Even"
      then have "merge (occurrences phi1 x) (occurrences phi2 x) = Even"
        by simp
      then have bothEven: "occurrences phi1 x = Even \<and> occurrences phi2 x = Even"
        using mergeBothEven by blast
      from bothEven have "occurrences phi1 x = Even" ..
      with Or.IH have mono1: "monotonic_in phi1 x" 
        by simp
      from bothEven have "occurrences phi2 x = Even" ..
      with Or.IH have mono2: "monotonic_in phi2 x"
        by simp
      from mono1 mono2 show "monotonic_in (Or phi1 phi2) x"
        by (simp add: monotonic_in_def)
    qed

    show "occurrences (Or phi1 phi2) x = Odd \<longrightarrow> antitonic_in (Or phi1 phi2) x" 
    proof
      assume "occurrences (Or phi1 phi2) x = Odd"
      then have "merge (occurrences phi1 x) (occurrences phi2 x) = Odd"
        by simp
      then have bothOdd: "occurrences phi1 x = Odd \<and> occurrences phi2 x = Odd"
        using mergeBothOdd by blast
      from bothOdd have "occurrences phi1 x = Odd" ..
      with Or.IH have anti1: "antitonic_in phi1 x"
        by simp
      from bothOdd have "occurrences phi2 x = Odd" ..
      with Or.IH have anti2: "antitonic_in phi2 x"
        by simp
      from anti1 anti2 show "antitonic_in (Or phi1 phi2) x"
        by (simp add: antitonic_in_def)
    qed
  qed
next
  case (Imp phi1 phi2)
  show ?case
  proof
    show "occurrences (Imp phi1 phi2) x = Even \<longrightarrow> monotonic_in (Imp phi1 phi2) x"
    proof
      assume "occurrences (Imp phi1 phi2) x = Even"
      then have "merge (negate (occurrences phi1 x)) (occurrences phi2 x) = Even"
        by simp
      then have bothEven: "negate (occurrences phi1 x) = Even \<and> occurrences phi2 x = Even"
        using mergeBothEven by blast
      from bothEven have "negate (occurrences phi1 x) = Even" ..
      then have "occurrences phi1 x = Odd"
        using negateOccEvenIsOdd by simp
      with Imp.IH have anti1: "antitonic_in phi1 x"
        by simp
      from bothEven have "occurrences phi2 x = Even" ..
      with Imp.IH have mono2: "monotonic_in phi2 x"
        by simp
      from anti1 mono2 show "monotonic_in (Imp phi1 phi2) x" 
        by (simp add: antitonic_in_def monotonic_in_def)
    qed

    show "occurrences (Imp phi1 phi2) x = Odd \<longrightarrow> antitonic_in (Imp phi1 phi2) x"
    proof
      assume "occurrences (Imp phi1 phi2) x = Odd"
      then have "merge (negate (occurrences phi1 x)) (occurrences phi2 x) = Odd"
        by simp
      then have bothOdd: "negate (occurrences phi1 x) = Odd \<and> occurrences phi2 x = Odd"
        using mergeBothOdd by blast
      from bothOdd have "negate (occurrences phi1 x) = Odd" ..
      then have "occurrences phi1 x = Even"
        using negateOccOddIsEven by simp
      with Imp.IH have mono1: "monotonic_in phi1 x"
        by simp
      from bothOdd have "occurrences phi2 x = Odd" ..
      with Imp.IH have anti2: "antitonic_in phi2 x"
        by simp
      from mono1 anti2 show "antitonic_in (Imp phi1 phi2) x" 
        by (simp add: antitonic_in_def monotonic_in_def)
    qed
  qed
next
  case (Neg phi)
  show ?case
  proof
    show "occurrences (Neg phi) x = Even \<longrightarrow> monotonic_in (Neg phi) x"
    proof
      assume "occurrences (Neg phi) x = Even"
      then have "occurrences phi x = Odd"
        using occNegEvenIsOdd by simp
      with Neg.IH have "antitonic_in phi x" 
        by simp
      then show "monotonic_in (Neg phi) x" 
        by (auto simp add: antitonic_in_def monotonic_in_def)
    qed

    show "occurrences (Neg phi) x = Odd \<longrightarrow> antitonic_in (Neg phi) x"
    proof
      assume "occurrences (Neg phi) x = Odd"
      then have "occurrences phi x = Even"
        using occNegOddIsEven by simp
      with Neg.IH have "monotonic_in phi x" 
        by simp
      then show "antitonic_in (Neg phi) x" 
        by (auto simp add: antitonic_in_def monotonic_in_def)
    qed
  qed
qed



theorem "(occurrences phi x = Even) \<longrightarrow> (monotonic_in phi x)" 
  by (simp add: aux)
