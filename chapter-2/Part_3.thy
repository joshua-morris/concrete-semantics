theory Part_3 imports Main
begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun contents :: "'a tree \<Rightarrow> 'a list" where
"contents Tip = []" |
"contents (Node left a right) = a # (contents left @ contents right)"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
"sum_tree Tip = 0" |
"sum_tree (Node left a right) = a + sum_tree left + sum_tree right"

theorem "sum_tree t = sum_list (contents t)"
  apply(induction t)
   apply(auto)
  done

datatype 'a tree2 = Tip 'a | Node "'a tree2" 'a "'a tree2"

fun mirror :: "'a tree2 \<Rightarrow> 'a tree2" where
"mirror (Tip a) = Tip a" |
"mirror (Node left a right) = Node (mirror right) a (mirror left)"

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
"pre_order (Tip a) = [a]" |
"pre_order (Node left a right) = a # (pre_order left @ pre_order right)"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
"post_order (Tip a) = [a]" |
"post_order (Node left a right) = (post_order left @ post_order right) @ [a]"

theorem "pre_order (mirror t) = rev (post_order t)"
  apply(induction t)
   apply(auto)
  done

fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"intersperse a [] = [a]" |
"intersperse a (x#xs) = [x] @ [a] @ (intersperse a xs)"

theorem "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply(induction xs)
   apply(auto)
  done

end