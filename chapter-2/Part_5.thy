theory Part_5 imports Main

begin

(* 2.10 *)

datatype tree0 = Tip | Node "tree0" "tree0"

fun nodes :: "tree0 \<Rightarrow> nat" where
"nodes Tip = 1" |
"nodes (Node left right) = 1 + nodes left + nodes right"

fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
"explode 0 t = t" |
"explode (Suc m) t = explode m (Node t t)"

theorem explode_size : "nodes (explode n t) = (2 ^ n) * (nodes t) + (2 ^ n - 1)"
  apply(induction n arbitrary: t)
   apply(auto simp add: algebra_simps)
  done

(* 2.11 *)

datatype exp = Var | Const int | Add exp exp | Mult exp exp

fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
"eval Var n = n" |
"eval (Const m) n = m" |
"eval (Add m n) p = eval m p + eval n p" |
"eval (Mult m n) p = eval m p * eval n p"

fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
"evalp [] n = 0" |
"evalp (x#xs) n = x * n ^ (size xs) + evalp xs n"

(* TODO *)