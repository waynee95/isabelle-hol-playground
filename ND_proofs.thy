theory ND_proofs
  imports Main
begin

lemma "A \<longrightarrow> (A \<and> A)"
proof (rule impI)
  assume A
  show "A \<and> A"
  proof (rule conjI)
    show A by fact
    show A by fact
  qed
qed

lemma "A \<longrightarrow> (A \<and> A)"
proof (rule impI)
  assume A
  then show "A \<and> A"
  proof (rule conjI)
    show A by fact
  qed
qed

lemma "A \<longrightarrow> (B \<longrightarrow> A)"
proof (rule impI)
  assume A
  show "B \<longrightarrow> A"
  proof (rule impI)
    show A by fact
  qed
qed

lemma "A \<longrightarrow> (A \<or> B)"
proof (rule impI)
  assume A
  show "A \<or> B"
  proof (rule disjI1)
    show A by fact
  qed
qed

lemma "(A \<longrightarrow> B) \<longrightarrow> ((B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C))"
  apply (rule impI)
  apply (rule impI)
  apply (rule impI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply assumption
  done

thm mp
thm impE

lemma "(A \<longrightarrow> B) \<longrightarrow> ((B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C))"
proof (rule impI)
  assume "A \<longrightarrow> B"
  show "(B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> C)"
  proof
    assume "B \<longrightarrow> C"
    show "A \<longrightarrow> C"
    proof (rule impI)
      assume A
      with \<open>A \<longrightarrow> B\<close> have B by (rule impE)
      with \<open>B \<longrightarrow> C\<close> show C by (rule impE)
    qed
  qed
qed

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof (rule impI)
  assume "A \<and> B"
  show "A \<or> B"
  proof (rule disjI1)
    from \<open>A \<and> B\<close> show A by (rule conjE)
  qed
qed

lemma "(A \<and> B) \<longrightarrow> (A \<or> B)"
proof (rule impI)
  assume "A \<and> B"
  then show "A \<or> B"
  proof (rule conjE) 
    from \<open>A \<and> B\<close> have A by (rule conjunct1)
    then show ?thesis by (rule disjI1)
  qed
qed

lemma "A \<or> (B \<and> C) \<longrightarrow> (A \<or> B) \<and> (A \<or> C)"
proof (rule impI)
  assume "A \<or> (B \<and> C)"
  then show "(A \<or> B) \<and> (A \<or> C)"
  proof (rule disjE)
    assume A
    then have "A \<or> B" by (rule disjI1)
    from \<open>A\<close> have "A \<or> C" by (rule disjI1)
    with \<open>A \<or> B\<close> show ?thesis by (rule conjI)
  next
    assume "B \<and> C"
    then show "(A \<or> B) \<and> (A \<or> C)"
    proof (rule conjE)
      assume B
      then have "A \<or> B" by (rule disjI2)
      assume C
      then have "A \<or> C" by (rule disjI2)
      with \<open>A \<or> B\<close> show ?thesis by (rule conjI)
    qed
  qed
qed

end