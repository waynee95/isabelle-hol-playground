theory Predic_Logic
  imports Main
begin

lemma "(\<exists>x. \<forall>y. P(x,y)) \<longrightarrow> (\<forall> y. \<exists>x. P(x,y))"
  apply (rule impI)
  apply (erule exE)
  apply (rule allI)
  apply (erule allE)
  apply (rule exI)
  apply assumption
  done

lemma "(\<forall>x. P(x) \<longrightarrow> Q) = ((\<exists>x. P(x)) \<longrightarrow> Q)"
  apply (rule iffI)
   apply (rule impI)
   apply (erule exE)
   apply (erule allE)
   apply (erule impE)
    apply assumption+
  apply (rule allI)
  apply (rule impI)
  apply (erule impE)
   apply (rule exI)
   apply assumption+
   done

lemma "\<forall>x. P(x)"
  quickcheck
  oops
  
end