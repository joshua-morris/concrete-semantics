theory Part_1 imports Main

begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node left a right) = (set left) \<union> (set right) \<union> {a}"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node left a right) = ((\<forall>x\<in>set left. x \<le> a) \<and> (\<forall>y\<in>set right. y > a) \<and> ord left \<and> ord right)"

end