theory Part_4 imports Main Part_2

begin

fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"itadd 0 n = n" |
"itadd (Suc m) n = itadd m (Suc n)"

theorem itadd_is_add : "itadd m n = add m n"
  apply(induction m arbitrary: n)
   apply(auto)
  done

end