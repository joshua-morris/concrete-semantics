theory Part_1 imports Main

begin

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun set :: "'a tree \<Rightarrow> 'a set" where
"set Tip = {}" |
"set (Node left a right) = (set left) \<union> (set right) \<union> {a}"

fun ord :: "int tree \<Rightarrow> bool" where
"ord Tip = True" |
"ord (Node left a right) = ((\<forall>x\<in>set left. x \<le> a) \<and> (\<forall>y\<in>set right. y > a) \<and> ord left \<and> ord right)"

fun ins :: "int \<Rightarrow> int tree \<Rightarrow> int tree" where
"ins n Tip = Node Tip n Tip" |
"ins n (Node left a right) = 
  (if n = a 
    then Node left a right 
  else if n \<le> a 
    then Node (ins n left) a right
  else
    Node left a (ins n right))"

lemma set_ins [simp] : "set (ins x t) = {x} \<union> set t"
  apply(induction t)
   apply(auto)
  done

lemma ord_ins : "ord t \<Longrightarrow> ord (ins i t)"
  apply(induction t)
   apply(auto)
  done

end