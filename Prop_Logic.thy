theory Prop_Logic
  imports Main
begin

lemma "A \<longrightarrow> A"
  apply (rule impI)
  apply assumption
  done

lemma "A \<and> B \<Longrightarrow> B \<and> A"
  apply (rule conjI)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply assumption
  done

lemma "P \<or> Q \<Longrightarrow> Q \<or> P"
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption
  done

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
  by (rule impI, erule conjE, rule disjI1)

lemma "((A \<or> B) \<or> C) \<longrightarrow> A \<or> (B \<or> C)"
  apply (rule impI)
  apply (erule disjE)
   apply (erule disjE)
    apply (rule disjI1)
    apply assumption
   apply (rule disjI2)
   apply (rule disjI1)
   apply assumption
  apply (rule disjI2)
  apply (rule disjI2)
  apply assumption
  done

lemma "A \<longrightarrow> B \<longrightarrow> A"
  apply (rule impI)+
  apply assumption
  done

lemma "(A \<or> A) = (A \<and> A)"
  apply (rule iffI)
   apply (erule disjE)
    apply (rule conjI)
     apply assumption+
   apply (rule conjI)
    apply assumption+
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

lemma "(A \<longrightarrow> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> B) \<longrightarrow> A \<longrightarrow> C"
  apply (rule impI)+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption+
  done

lemma "\<not>\<not>A \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done

lemma "A \<longrightarrow> \<not>\<not>A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done

lemma "(\<not>A \<longrightarrow> B) \<longrightarrow> (\<not>B \<longrightarrow> A)"
  apply (rule impI)+
  apply (rule classical)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done

lemma "((A \<longrightarrow> B) \<longrightarrow> A) \<longrightarrow> A"
  apply (rule impI)
  apply (rule classical)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption+
  done

lemma "A \<or> \<not>A"
  apply (rule classical)
  apply (rule disjI2)
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI1)
  apply assumption
  done

lemma "(\<not>(A \<and> B)) = (\<not>A \<or> \<not>B)"
  apply (rule iffI)
   apply (rule classical)
   apply (erule notE)
   apply (rule conjI)
    apply (rule classical)
    apply (erule notE)
    apply (rule disjI1)
    apply assumption
   apply (rule classical)
   apply (erule notE)
   apply (rule disjI2)
   apply assumption
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE, assumption)+
  done

lemma "(\<not>(A \<or> B)) = (\<not>A \<and> \<not>B)"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule notI)
    apply (erule notE)
    apply (rule disjI1)
    apply assumption
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI2)
   apply assumption
  apply (erule conjE)
  apply (rule notI)
  apply (erule notE)
  apply (erule disjE)
   apply assumption
  apply (rule classical)
  apply (erule notE)
  apply assumption
  done  

lemma "p \<and> q \<longleftrightarrow> q \<and> p"
  apply (rule iffI)
   apply (rule conjI)
    apply (erule conjE)
    apply (assumption)
   apply (erule conjE)
   apply (assumption)
  apply (rule conjI)
   apply (erule conjE)
   apply (assumption)
  apply (erule conjE)
  apply (assumption)
  done

end