theory Part_1 imports Main

begin

lemma assumes T: "\<forall>x y. T x y \<or> T y x"
  and A: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
  and TA: "\<forall>x y. T x y \<longrightarrow> A x y" and "A x y"
  shows "T x y"
proof (rule ccontr)
  assume "\<not> T x y"
  from this and T have "T y x" by blast
  from this and TA have "A y x" by blast
  from this and `A x y` and A have "x = y" by blast
  from this and `\<not> T x y` and `T y x` show "False" by blast
qed

lemma "(\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs)
  \<or> (\<exists> ys zs. xs = ys @ zs \<and> length ys = length zs + 1)"
proof cases
  assume "even (length xs)"
  then obtain k where ks:"(length xs) = 2*k" by blast
  obtain ys where 1:"ys = take k xs" by auto
  obtain zs where 2:"zs = drop k xs" by auto
  then have "xs = ys @ zs" by (simp add: \<open>ys = take k xs\<close>)
  moreover have "length ys = length zs" using 1 and 2 and ks by simp
  ultimately show ?thesis by blast
next
  assume "odd (length xs)"
  then obtain k where ks:"length xs = 2*k + 1" using oddE by blast
  obtain ys where 1:"ys = take (Suc k) xs" by auto
  obtain zs where 2:"zs = drop (Suc k) xs" by auto
  then have "xs = ys @ zs" using 1 and 2 by simp
  moreover have "length ys = length zs + 1" by (simp add: "1" "2" ks)
  ultimately show ?thesis by blast
qed