theory Part_4 imports Main

begin

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

lemma suc_associative [simp] : "add m (Suc n) = Suc (add m n)"
  apply(induction m)
   apply(auto)
  done

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_is_add : "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

end