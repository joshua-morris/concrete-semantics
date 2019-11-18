theory Part_1 imports Main
begin

type_synonym vname = string
datatype aexp = N int | V vname | Plus aexp aexp

type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N a) s = a" |
"aval (V x) s = s x" |
"aval (Plus a b) s = aval a s + aval b s"

value "aval (Plus (N 3) (V ''x'')) (\<lambda>x.0)"

fun asimp_const :: "aexp \<Rightarrow> aexp" where
"asimp_const (N n) = N n" |
"asimp_const (V n) = V n" |
"asimp_const (Plus a1 a2) =
  (case (asimp_const a1, asimp_const a2) of
    (N n1, N n2) \<Rightarrow> N (n1 + n2) |
    (b1, b2) \<Rightarrow> Plus b1 b2)"

lemma "aval (asimp_const a) s = aval a s"
  apply(induction a)
    apply(auto split: aexp.split)
  done

fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i1) (N i2) = N (i1 + i2)" |
"plus (N i) a = (if i = 0 then a else Plus (N i) a)" |
"plus a (N i) = (if i = 0 then a else Plus a (N i))" |
"plus a1 a2 = Plus a1 a2"

lemma aval_plus[simp] : "aval (plus a1 a2) s = aval a1 s + aval a2 s"
  apply(induction a1 a2 rule: plus.induct)
    apply auto
  done

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus a b) = ((optimal a) \<and> (optimal b))"

lemma is_optimal : "optimal (asimp_const a)"
  apply(induction a)
    apply(auto simp add: aexp.split)
  done

fun sumN :: "aexp \<Rightarrow> int" where
"sumN (N a) = a" |
"sumN (V x) = 0" |
"sumN (Plus a b) = sumN a + sumN b"

fun zeroN :: "aexp \<Rightarrow> aexp" where
"zeroN (N a) = N 0" |
"zeroN (V x) = V x" |
"zeroN (Plus a b) = Plus (zeroN a) (zeroN b)"

fun sepN :: "aexp \<Rightarrow> aexp" where
"sepN a = Plus (N (sumN a)) (zeroN a)"

lemma aval_sepN : "aval (sepN t) s = aval t s"
  apply(induction t)
    apply(auto)
  done

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a1 a2 ) = plus (asimp a1) (asimp a2)"

fun full_asimp :: "aexp \<Rightarrow> aexp" where
"full_asimp a = asimp (sepN a)"

lemma aval_full_asimp : "aval (full_asimp t) s = aval t s"
  apply(induction t)
    apply(auto)
  done

fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"subst x a (V v) = (if x = v then a else (V v))" |
"subst x a (Plus m n) = Plus (subst x a m) (subst x a n)" |
"subst _ _ (N v) = N v"

lemma subst_lemma [simp] : "aval (subst x a e) s = aval e (s(x := aval a s))"
  apply(induction e arbitrary: a)
    apply(auto simp add: aexp.split)
  done

lemma "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 e) s = aval (subst x a2 e) s"
  apply(auto)
  done

datatype aexp2 = N2 int | V2 vname | Plus2 aexp2 aexp2 | Times aexp2 aexp2

fun aval2 :: "aexp2 \<Rightarrow> state \<Rightarrow> val" where
"aval2 (N2 a) s = a" |
"aval2 (V2 x) s = s x" |
"aval2 (Plus2 a b) s = (aval2 a s) + (aval2 b s)" |
"aval2 (Times a b) s = (aval2 a s) * (aval2 b s)"

fun plus2 :: "aexp2 \<Rightarrow> aexp2 \<Rightarrow> aexp2" where
"plus2 (N2 i\<^sub>1) (N2 i\<^sub>2) = N2 (i\<^sub>1 + i\<^sub>2)" |
"plus2 (N2 i) a = (if i = 0 then a else Plus2 (N2 i) a)" |
"plus2 a (N2 i) = (if i = 0 then a else Plus2 a (N2 i))" |
"plus2 a\<^sub>1 a\<^sub>2 = Plus2 a\<^sub>1 a\<^sub>2"

fun mult :: "aexp2 \<Rightarrow> aexp2 \<Rightarrow> aexp2" where
"mult (N2 i\<^sub>1) (N2 i\<^sub>2) = N2 (i\<^sub>1*i\<^sub>2)" |
"mult (N2 i) a = 
  (if i=1 then a else if i=0 then (N2 0) else Times (N2 i) a)" |
"mult a (N2 i) = (if i=0 then (N2 0) else if i = 1 then a else Times a (N2 i))" |
"mult a\<^sub>1 a\<^sub>2 = Times a\<^sub>1 a\<^sub>2"

fun asimp2 :: "aexp2 \<Rightarrow> aexp2" where
"asimp2 (N2 n) = N2 n" |
"asimp2 (V2 x) = V2 x" |
"asimp2 (Plus2 a\<^sub>1 a\<^sub>2) = plus2 (asimp2 a\<^sub>1) (asimp2 a\<^sub>2)" |
"asimp2 (Times a\<^sub>1 a\<^sub>2) = mult (asimp2 a\<^sub>1) (asimp2 a\<^sub>2)"

lemma aval2_plus [simp] : "aval2 (plus2 a\<^sub>1 a\<^sub>2) s = aval2 a\<^sub>1 s + aval2 a\<^sub>2 s"
  apply(induction a\<^sub>1 a\<^sub>2 rule: plus2.induct)
    apply(auto)
  done

lemma aval2_mult [simp] : "aval2 (mult a\<^sub>1 a\<^sub>2) s = (aval2 a\<^sub>1) s * (aval2 a\<^sub>2) s"
  apply(induction a\<^sub>1 a\<^sub>2 rule: mult.induct)
    apply(auto)
  done

lemma aval2_asimp [simp] : "aval2 (asimp2 a) s = aval2 a s"
  apply(induction a)
     apply(auto simp add: aexp2.split)
  done