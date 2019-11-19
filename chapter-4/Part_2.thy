theory Part_2 imports Main

begin

(* 4.2 *)

inductive palindrome :: "'a list \<Rightarrow> bool" where
pempty: "palindrome []" |
psingle: "palindrome [x]" |
plist: "palindrome xs \<Longrightarrow> palindrome (a # (xs @ [a]))"

lemma "palindrome xs \<Longrightarrow> rev xs = xs"
  apply(induction rule: palindrome.induct)
    apply(auto)
  done

(* 4.3 *)

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

(* 4.4 *)

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
it0: "iter r 0 x x" |
itSS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma star_imp_iter : "star r x y \<Longrightarrow> \<exists>n. iter r n x y"
  apply(induction rule: star.induct)
   apply(auto intro: it0 itSS)
  done

(* 4.5 *)

datatype alpha = a | b (* a == '(', b == ')' *)

(* 
Grammar for balanced parentheses S
  S \<rightarrow> \<epsilon> | aSb | SS
*)
inductive S :: "alpha list \<Rightarrow> bool" where
S0: "S []" |
S1: "S w \<Longrightarrow> S (a # w @ [b])" (*S [a,b,a,b] \<rightarrow> S [a,b] \<rightarrow> S [] \<rightarrow> true *) |
S2: "S w \<Longrightarrow> S x \<Longrightarrow> S (w @ x)" (* S [a,b,a,b] \<rightarrow> S [a,b] \<and> S [a,b] \<rightarrow> true *)

(* 
Second grammar for balanced parentheses T
  T \<rightarrow> \<epsilon> | TaTb 
*)
inductive T :: "alpha list \<Rightarrow> bool" where
T0: "T []" |
T1: "T w \<Longrightarrow> T x \<Longrightarrow> T (w @ [a] @ x @ [b])"

lemma TS : "T w \<Longrightarrow> S w"
  apply(induction rule: T.induct)
   apply(auto intro: S0 S1 S2)
  done

lemma ST : "S w \<Longrightarrow> T w"
proof (induction rule: S.induct)
  case S0
  thus ?case by (simp add: T0)
next
  case S1
  thus ?case using T1 by blast
next
  case S2
  thus ?case using T1 by blast
qed

corollary SeqT: "S w \<longleftrightarrow> T w"
  apply(auto intro: ST TS)
  done
    