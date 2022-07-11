theory Termination
  imports Main
begin

(* Reference: https://isabelle.in.tum.de/dist/Isabelle2021-1/doc/functions.pdf *)
(* More details: https://www21.in.tum.de/~krauss/papers/krauss-thesis.pdf *)

function sum :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"sum i n = (if i > n then 0 else i + sum (Suc i) n)"
  by pat_completeness auto

(*
  The \<open>lexicographic_order\<close> method fails because none of the arguments decreases in the recursive call.
  To prove termination a custom well-founded relation has to be provided. The termination argument
  for \<open>sum\<close> is based on the fact that the difference between \<open>i\<close> and \<open>n\<close> gets smaller in every step and
  that the recursion stops when \<open>i\<close> is greater than \<open>n\<close>. The expression \<open>n + 1 - i\<close> always decreases.
*) 

term measure

termination
  apply (relation "measure (\<lambda>(i, n). n + 1 - i)")
   apply auto
  done

(* Partiality *)
function findzero :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
"findzero f n = (if f n = 0 then n else findzero f (Suc n))"
  by pat_completeness auto

(* 
  Isabelle generates a predicate \<open>findzero_dom\<close> that characterizes the values where the function
  termiantes aka the \<open>domain\<close> of the function 
*)

term findzero_dom

(*
If we treat partial function as a total function but with an additional domain predicate, we can 
derive simplification and induction rules as usual. They are guarded by domain conditions.
*)

thm findzero.psimps
thm findzero.pinduct
 
end