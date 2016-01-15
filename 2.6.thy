theory Section2_6
  imports Main
begin

primrec sum :: "nat \<Rightarrow> nat" where
  "sum 0 = 0" |
  "sum (Suc n) = Suc n + sum n"

lemma "sum n + sum n = n*(Suc n)"
  apply (induct_tac n)
  apply auto
  done

lemma "\<lbrakk>\<not> m < n; m < n + (1::nat)\<rbrakk> \<Longrightarrow> m = n"
  apply arith
  done


lemma "m \<noteq> (n::nat) \<Longrightarrow> m < n \<or> n < m"
  apply arith
  done

lemma "min i (max j (k*k)) = max (min (k*k) i) (min i (j::nat))"
  apply arith
  done


end