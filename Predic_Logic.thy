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

lemma "(\<not> (\<forall>x. P x)) = (\<exists>x. \<not> P x)"
proof (rule iffI)
  assume "\<not> (\<forall>x. P x)"
  show "\<exists>x. \<not> P x"
  proof (rule ccontr)
    assume "\<not> (\<exists>x. \<not> P x)"
    then have "\<forall>x. P x" by simp 
    with \<open>\<not> (\<forall>x. P x)\<close> show False by contradiction
  qed
next
  assume "\<exists>x. \<not> P x"
  then obtain c where "\<not> P c" by (rule exE)
  show "\<not> (\<forall>x. P x)"
  proof (rule notI)
    assume "\<forall>x. P x"
    then have "P c" by (rule allE)
    with \<open>\<not> P c\<close> show False by contradiction
  qed
qed

end