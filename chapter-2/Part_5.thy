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
"evalp (x#xs) n = x + n * evalp xs n"

fun list_sum :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"list_sum [] xs = xs" |
"list_sum xs [] = xs" |
"list_sum (x#xs) (y#ys) = (x + y) # list_sum xs ys"

fun scalar_mult :: "int \<Rightarrow> int list \<Rightarrow> int list" where
"scalar_mult n [] = []" |
"scalar_mult n (x#xs) = n*x # scalar_mult n xs"

fun list_mult :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
"list_mult [] xs = xs" |
"list_mult (x#xs) ys = list_sum (scalar_mult x ys) (0 # list_mult xs ys)"

fun coeffs :: "exp \<Rightarrow> int list" where
"coeffs Var = [0, 1]" |
"coeffs (Const n) = [n]" |
"coeffs (Add a b) = list_sum (coeffs a) (coeffs b)" |
"coeffs (Mult a b) = list_mult (coeffs a) (coeffs b)"

lemma "evalp (coeffs e) x = eval e x"
  nitpick
  oops