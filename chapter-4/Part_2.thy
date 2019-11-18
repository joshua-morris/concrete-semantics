theory Part_2 imports Main

begin

inductive palindrome :: "'a list \<Rightarrow> bool" where
pempty: "palindrome []" |
psingle: "palindrome [x]" |
plist: "palindrome xs \<Longrightarrow> palindrome (a # (xs @ [a]))"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
    apply(auto)
  done

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl': "star' r x x" |
step': "star' r x y \<Longrightarrow> r y z \<Longrightarrow> star' r x z"
  
lemma [simp] : "star' r y z \<Longrightarrow> r x y \<Longrightarrow> star' r x z"
  apply(induction rule: star'.induct)
   apply(auto intro: refl' step')
  done

theorem star_star' : "star r x y \<Longrightarrow> star' r x y"
  apply(induction rule: star.induct)
   apply(auto simp add: refl')
  done

   
  
