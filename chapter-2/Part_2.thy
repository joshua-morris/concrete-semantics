theory Part_2 imports Main
begin

(* 2.1 *)

value "1 + (2::nat)"
value "1 + (2::int)"
value "1 - (2::nat)"
value "1 - (2::int)"

(* 2.2 *)

fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add 0 n = n" |
"add (Suc m) n = Suc (add m n)"

theorem nat_add_associative [simp] : "add m (add n p) = add (add m n) p"
  apply(induction m)
   apply(auto)
  done

lemma zero_commutative [simp] : "add n 0 = add 0 n"
  apply(induction n)
   apply(auto)
  done

lemma suc_associative [simp] : "add m (Suc n) = Suc (add m n)"
  apply(induction m)
   apply(auto)
  done

theorem nat_add_commutative : "add m n = add n m"
  apply(induction n)
   apply(auto)
  done

fun double :: "nat \<Rightarrow> nat" where
"double a = a + a"

lemma double_is_add : "double m = m + m"
  apply(induction m)
  apply(auto)
  done

(* 2.3 *)

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
"count a [] = 0" |
"count a (x#xs) = (if a = x then (1 + count a xs) else (count a xs))"

theorem count_lte_length : "count x xs \<le> length xs"
  apply(induction xs)
   apply(auto)
  done

(* 2.4 *)

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] a = [a]" |
"snoc (x#xs) a = x # (snoc xs a)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x#xs) = snoc (reverse xs) x"

lemma reverse_snoc [simp] : "reverse (snoc xs a) = a # reverse xs"
  apply(induction xs)
   apply(auto)
  done

theorem reverse_reverse : "reverse (reverse xs) = xs"
  apply(induction xs)
   apply(auto)
  done

(* 2.5 *)

fun sum_upto :: "nat \<Rightarrow> nat" where
"sum_upto 0 = 0" |
"sum_upto m = m + sum_upto (m - 1)"

theorem triangle_number : "sum_upto n = n * (n + 1) div 2"
  apply(induction n)
   apply(auto)
  done

end