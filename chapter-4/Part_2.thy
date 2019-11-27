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

(* 4.6 *)

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N c) s = c" |
"aval (V x) s = s x" |
"aval (Plus c d) s = aval c s + aval d s"

inductive rel_aval :: "aexp \<Rightarrow> state \<Rightarrow> val \<Rightarrow> bool" where
ConstN: "rel_aval (N c) s c" |
ValV: "rel_aval (V x) s (s x)" |
PlusX: "rel_aval p s x \<Longrightarrow> rel_aval q s y \<Longrightarrow> rel_aval (Plus p q) s (x + y)"

lemma aval_rel_aval: "rel_aval c s v \<Longrightarrow> aval c s = v"
  apply(induction rule: rel_aval.induct)
    apply(auto)
  done
  

lemma aval_aval_rel: "aval c s = v \<Longrightarrow> rel_aval c s v"
  apply(induction c arbitrary: v)
    apply(auto intro: ConstN ValV PlusX)
  done

corollary "rel_aval c s v \<longleftrightarrow> aval c s = v"
  apply(auto intro: aval_rel_aval aval_aval_rel)
  done

(* 4.7 *)
datatype instr = LOADI val | LOAD vname | ADD

type_synonym stack = "val list"

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec1 (LOADI n) _ stk = Some (n # stk)" |
"exec1 ADD _ [] = None" |
"exec1 ADD _ [c] = None" |
"exec1 (LOAD x) s stk = Some (s(x) # stk)" |
"exec1 ADD _ (j # i # stk) = Some ((i + j) # stk)"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option" where
"exec [] _ stk = Some stk" |
"exec (i#is) s stk = (case (exec1 i s stk) of
                      Some c \<Rightarrow> exec is s c |
                      None \<Rightarrow> None)"

fun comp :: "aexp \<Rightarrow> instr list" where
"comp (N n) = [LOADI n]" |
"comp (V x ) = [LOAD x ]" |
"comp (Plus e\<^sub>1 e\<^sub>2) = comp e\<^sub>1 @ comp e\<^sub>2 @ [ADD]"

lemma [simp] : "exec is\<^sub>1 s stk = Some c \<Longrightarrow> exec (is\<^sub>1 @ is\<^sub>2) s stk = exec is\<^sub>2 s c"
  apply(induction is\<^sub>1 arbitrary: stk)
   apply(auto simp add: option.split)
  apply (metis option.case_eq_if option.simps(3))
  done

lemma "exec (comp c) s stk = Some (aval c s # stk)"
  apply(induction c arbitrary: stk)
    apply(auto)
  done

inductive ok :: "nat \<Rightarrow> instr list \<Rightarrow> nat \<Rightarrow> bool" where
okBase : "ok n [] n" |
ok1 : "ok n is n' \<Longrightarrow> ok n (is @ [LOADI k]) (Suc n')" |
ok2 : "ok n is n' \<Longrightarrow> ok n (is @ [LOAD x]) (Suc n')" |
ok3 : "ok n is (Suc (Suc n')) \<Longrightarrow> ok n (is @ [ADD]) (Suc n')"

lemma "ok 0 [LOAD k] (Suc 0)"
  apply (induction k)
   apply (metis append_self_conv2 ok.simps)
  apply (metis append_eq_Cons_conv ok.simps ok2)
  done

lemma "ok 0 [LOAD x, LOADI v, ADD] (Suc 0)"
  apply(induction x)
  apply(induction v)
    apply (metis append.left_neutral append_Cons ok1 ok2 ok3 okBase)
   apply (metis append.left_neutral append_Cons ok.simps okBase)
  apply (metis append.left_neutral append_Cons ok1 ok2 ok3 okBase)
  done

lemma "ok (Suc (Suc 0)) [LOAD x, ADD, ADD, LOAD y] (Suc (Suc 0))"
  using ok.cases by force

lemma "\<lbrakk> ok n is n'; length stk = n; exec is s stk = Some c \<rbrakk> \<Longrightarrow> length c = n'"
  using ok.cases by force