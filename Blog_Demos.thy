theory Blog_Demos
  imports Complex_Main
begin

(* Proof 1 *)
lemma algebra_identity:
  fixes a b :: real
    shows "(a + b)^2 = a^2 + 2*a*b + b^2"
  by (simp add: power2_sum)

(* Proof 1 but manually *)
lemma algebra_identity2:
  fixes a b :: real
    shows "(a + b)^2 = a^2 + 2*a*b + b^2"
proof -
  have "(a + b)^2 = (a + b) * (a + b)"
    by (simp add: power2_eq_square)
  also have "... = a*a + a*b + b*a + b*b"
    by (simp add: distrib_left distrib_right)
  also have "... = a^2 + 2*a*b + b^2"
   by (simp add: power2_eq_square algebra_simps)
  finally show ?thesis .
qed

(* Map Composition *)
lemma map_composition:
  "map f (map g xs) = map (f \<circ> g) xs"
  by (induction xs) simp_all

(* Even predicate *)
inductive Even :: "nat \<Rightarrow> bool" where
  Even0:  "Even 0" |
  EvenSS: "Even n \<Longrightarrow> Even (Suc (Suc n))"

(* doing it apply-style ... *)
lemma Even_double: 
  "Even (2 * k)" 
  apply (induction k)
   apply auto
   apply (rule Even0)
  apply (rule EvenSS)
    apply auto
  done

(* now using Isar ... *)
lemma Even_double2: 
  "Even (2 * k)" 
proof (induction k)
  case 0
  have "Even 0" by (rule Even0)
  have "2 * 0 = (0::nat)" by simp
  with \<open>Even 0\<close> have "Even (2 * 0)" by simp
  then show ?case .
next
  case (Suc k)
  assume IH: "Even (2 * k)" 
  then have "Even (Suc (Suc (2 * k)))"
    by (simp add: EvenSS) 
  also have "Suc (Suc (2 * k)) = 2 * (Suc k)"
    by simp 
  finally show ?case . 
qed

(* but this can be done much shorter ... *)
lemma Even_double3: 
  "Even (2 * k)" 
proof (induction k)
  case 0
  then show ?case
    by (simp add: Even0) 
next
  case (Suc k)
  then show ?case 
    by (simp add: EvenSS)
qed

(* another proof *)

(* 
exI: P a \<Longrightarrow> \<exists>x. P x 
says if you can show P a for some witness a, then \<exists>x. P x holds.

Notation exI[...] is an instantiation attribute.
Using exI[of ...] plugs concrete terms into exI's schematic variables.

So exI[of _ "Suc k"] leaves ?P to be inferred and sets the witness to Suc k.
Alternatively, use exI[where x = "Suc k"].

This is combined with intro/rule to finish an \<exists>-goal.

*)
lemma Even_iff_dbl: 
  "Even n \<longleftrightarrow> (\<exists>k. n = 2 * k)"
proof
  assume "Even n"
  then show "\<exists>k. n = 2 * k" 
  proof (induction rule: Even.induct)
    case Even0
    have "(0::nat) = 2 * 0" by simp
    then show ?case 
      by (rule exI[where x = 0]) 
  next
    case (EvenSS n)
    from EvenSS.IH obtain k where n_eq: "n = 2 * k" by auto
    have "Suc (Suc n) = 2 * Suc k"
      by (simp add: n_eq)    
    then show ?case
      by (intro exI[where x = "Suc k"])
  qed 
next
  assume "\<exists>k. n = 2 * k"
  then obtain k where "n = 2 * k" by auto
  then show "Even n"
  proof (induction k)
    case 0
    then show ?case by (simp add: Even0)
  next
    case (Suc k)
    with Even_double show ?case 
      by fastforce
  qed
qed

end