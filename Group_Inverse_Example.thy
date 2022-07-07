theory Group_Inverse_Example  
  imports Main
begin

lemma "\<lbrakk> \<forall>x y z. f(x, f(y, z)) = f(f(x,y), z); 
         \<forall>x. f(e, x) = x \<and> f(x,e) = x;
         \<forall>x. \<exists>y. f(y,x) = e \<rbrakk> \<Longrightarrow> \<forall>x y. f(x,y) = e \<longrightarrow> f(y,x) = e"
  by metis

(* https://isabelle.in.tum.de/dist/library/HOL/HOL/Groups.html *)
context
  fixes f :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 70)
    and e :: 'a
  assumes assoc: "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
    and left_neutral: "e \<otimes> x = x" 
    and left_inv: "\<exists>z. z \<otimes> x = e"
begin

(* verbose *)
lemma 
  assumes "x \<otimes> y = e"
  shows "y \<otimes> x = e"
proof -
  have A: "(x \<otimes> y) \<otimes> x = x" 
  proof -
    have "(x \<otimes> y) \<otimes> x = x \<otimes> (y \<otimes> x)" 
      using assoc by simp
    also have "\<dots> = e \<otimes> x"
      using assms calculation by simp
    also have "\<dots> = x" 
      using left_neutral by simp
    finally show ?thesis .
  qed

  from left_inv obtain z where B: "z \<otimes> x = e" by auto

  have "z \<otimes> (x \<otimes> (y \<otimes> x)) = (z \<otimes> x) \<otimes> (y \<otimes> x)"
    using assoc by simp
  also have "\<dots> = e \<otimes> (y \<otimes> x)"
    using B by simp
  also have "\<dots> = y \<otimes> x"
    using left_neutral by simp
  finally show "\<dots> = e"
    using A assoc B by simp
qed

(* automatic *)
lemma 
  assumes "x \<otimes> y = e"
  shows "y \<otimes> x = e"
  oops

end

end