theory EulerSum
  imports Main
begin

lemma "2 * (\<Sum>i::nat=0..n. i) = (n * (n + 1))"
proof (induction n)
  case 0
  then show ?case
    by simp
next
  case (Suc n)
  have "2 * (\<Sum>i::nat=0..(Suc n). i) = 2 * (\<Sum>i::nat=0..n. i) + 2 * (Suc n)"
    by simp
  also have "\<dots> = (n * (n + 1)) + 2 * (Suc n)"
    using Suc.IH by simp
  also have "\<dots> = Suc n * ((Suc n) + 1)"
    by simp
  finally show ?case .
qed

end