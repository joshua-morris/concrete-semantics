theory Part_2 imports Main

begin

inductive ev :: "nat \<Rightarrow> bool" where
ev0: "ev 0" |
evSS: "ev n \<Longrightarrow> ev(Suc(Suc n))"

(* 5.3 *)

lemma assumes a: "ev(Suc(Suc n))" shows "ev n"
proof -
  show ?thesis using a
  proof cases
    case evSS thus ?thesis by auto
  qed
qed

(* 5.4 *)

lemma "\<not> ev(Suc(Suc(Suc 0)))" (is "\<not> ?P")
proof
  assume "?P"
  hence "ev (Suc 0)" using ev.cases by blast
  thus "False" using ev.cases by blast
qed

(* 5.5 *)

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl: "star r x x" |
step: "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" where
it0: "iter r 0 x x" |
it_SS: "r x y \<Longrightarrow> iter r n y z \<Longrightarrow> iter r (Suc n) x z"

lemma "iter r n x y \<Longrightarrow> star r x y"
proof (induction rule: iter.induct)
  case it0
    show ?case by (simp add: star.refl)
next
  case it_SS
  thus ?case by (meson star.step)
qed

(* 5.6 *)

fun elems :: "'a list \<Rightarrow> 'a set" where
"elems [] = {}" |
"elems (x#xs) = {x} \<union> elems xs"

lemma "x \<in> elems xs \<Longrightarrow> \<exists>ys zs. xs = ys @ x # zs \<and> x \<notin> elems ys"
proof (induction xs)
  case Nil
  thus ?case by auto
next
  case (Cons a xs)
  show ?case
  proof cases
    assume "a = x"
    obtain ys where ys:"(ys::'a list) = []" by auto
    obtain zs where "zs = xs" by auto
    have "a \<notin> elems ys" by (simp add: ys)
    thus ?thesis using ys using \<open>a = x\<close> by blast
  next
    assume "a \<noteq> x"
    hence "x \<in> elems xs" using Cons.prems by auto
    obtain ys where ys:"ys = [a]" by auto
    obtain zs where zs:"zs = xs" by auto
    thus ?thesis using ys zs 
      by (metis Cons.IH Cons_eq_appendI Un_iff \<open>a \<noteq> x\<close> \<open>x \<in> elems xs\<close> elems.simps(2) ex_in_conv insert_iff)
  qed
qed

(* 5.7 *)

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

lemma [simp] : "T w \<Longrightarrow> T x \<Longrightarrow> T (w @ x)"
  apply(induction rule: T.induct)
   apply(auto)


lemma ST : "S w \<Longrightarrow> T w"
  apply(induction rule: S.induct)
    apply(simp add: T0)