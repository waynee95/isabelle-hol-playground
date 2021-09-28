theory Isar
  imports Main
begin

lemma "xs \<noteq> [] \<longrightarrow> hd xs # tl xs = xs"
proof
  assume "xs \<noteq> []" show "hd xs # tl xs = xs"
  proof (cases xs)
    assume "xs = []"
    with \<open>xs \<noteq> []\<close> have False..
    then show ?thesis..
  next
    fix y ys
    assume "xs = y # ys"
    then show ?thesis by simp
  qed
qed

lemma "xs \<noteq> [] \<longrightarrow> hd xs # tl xs = xs"
proof
  assume "xs \<noteq> []" show "hd xs # tl xs = xs"
  proof (cases xs)
    case Nil
      with \<open>xs \<noteq> []\<close> have False ..
      thus ?thesis ..
  next
    case (Cons y ys)
    thus ?thesis by simp
  qed
qed

lemma "xs \<noteq> [] \<longrightarrow> hd xs # tl xs = xs"
  by auto

lemma "A \<and> B \<longleftrightarrow> B \<and> A"
proof
  assume "A \<and> B"
  then show "B \<and> A"
  proof
    assume B A
    then show ?thesis ..
  qed
  next
    assume "B \<and> A"
    then show "A \<and> B"
    proof
      assume A B
      then show ?thesis ..
    qed
  qed

lemma "A \<and> B \<longleftrightarrow> B \<and> A"
  by auto
 
end