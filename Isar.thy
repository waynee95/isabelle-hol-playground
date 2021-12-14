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

lemma "length (xs @ ys) = length xs + length ys"
proof (induction xs)
  case Nil
  have "length ([] @ ys) = length ys" by simp
  also have "... = 0 + length ys" by simp
  also have "... = length [] + length ys" by simp
  finally show ?case.
next
  case (Cons x xs)
  have "length ((x # xs) @ ys) = length (x # (xs @ ys))" by simp
  also have "... = Suc (length (xs @ ys))" by simp
  also from Cons.IH have "... = Suc (length xs + length ys)"..
  also have "... = Suc (length xs) + length ys" by simp
  also have "... = length (x # xs) + length ys" by simp
  finally show ?case.
qed

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto n = n + sum_upto (n - 1)"

lemma "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply auto
  done

lemma "sum_upto n = n * (n + 1) div 2"
  by (induction n) auto

lemma "A \<and> B \<longrightarrow> A \<or> B"
proof
  assume "A \<and> B"
  then have "A" ..
  then show "A \<or> B" ..
qed

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

lemma "(\<forall>x. P x) \<longrightarrow> (\<exists>x. P x)"
proof
  assume "\<forall>x. P x"
  then show "\<exists>x. P x"
  proof
    fix x
    assume "P x"
    then show ?thesis ..
  qed
qed

lemma "(\<forall>x. P x) \<longrightarrow> (\<exists>x. P x)"
proof
  assume "\<forall>x. P x"
  then obtain x where "P x" ..
  then show "\<exists>x. P x" ..
qed

lemma
  assumes "\<exists>x. \<forall>y. P x y"
  shows "\<forall>y. \<exists>x. P x y"
proof
  fix y
  from assms obtain x where "\<forall>y. P x y" ..
  hence "P x y" ..
  thus "\<exists>x. P x y" ..
qed

lemma
  assumes "x < (0::int)" 
  shows "x * x > 0"
proof -
  from assms show ?thesis
    by (simp add: mult_neg_neg)
qed

lemma
  assumes "x < (0::int)" 
  shows "x * x > 0"
proof -
  from \<open>x < 0\<close> show ?thesis
    by (simp add: mult_neg_neg)
qed

lemma "\<exists>ys zs. xs = ys @ zs \<and> (length ys = length zs \<or> length ys = length zs + 1)"
  (is "\<exists>ys zs. ?P ys zs")
proof -
  let ?n = "length xs"
  show ?thesis
  proof (cases "even ?n")
    case True
    then have "\<exists>k. ?n = 2 * k" by auto
    then obtain k where "?n = 2 * k" ..
    let ?ys = "take k xs"
    let ?zs = "drop k xs"
    from \<open>?n = 2 * k\<close> have "?P ?ys ?zs" by auto
    then show ?thesis by blast
  next
    case False
    then have "\<exists>k. ?n = 2 * k + 1" by arith
    then obtain k where "?n = 2 * k + 1" ..
    let ?ys = "take (k + 1) xs"
    let ?zs = "drop (k + 1) xs"
    from \<open>?n = 2 * k + 1\<close> have "?P ?ys ?zs" by auto
    then show ?thesis by blast
  qed
qed

definition sq :: "nat \<Rightarrow> nat" where
"sq n = n * n"

lemma "sq(n*n) = sq(n)*sq(n)"
  apply (simp add: sq_def)
  done

lemma "sq(n*n) = sq(n)*sq(n)"
  unfolding sq_def by simp

end