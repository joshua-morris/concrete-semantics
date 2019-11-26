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

(* 3.1 *)

fun optimal :: "aexp \<Rightarrow> bool" where
"optimal (N a) = True" |
"optimal (V x) = True" |
"optimal (Plus (N i) (N j)) = False" |
"optimal (Plus a b) = ((optimal a) \<and> (optimal b))"

lemma is_optimal : "optimal (asimp_const a)"
  apply(induction a)
    apply(auto simp add: aexp.split)
  done

(* 3.2 *)

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

(* 3.3 *)

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

(* 3.4 *)

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

(* 3.6 *)

datatype lexp = Nl int | Vl vname | Plusl lexp lexp | LET vname lexp lexp

fun lval :: "lexp \<Rightarrow> state \<Rightarrow> int" where
"lval (Nl a) _ = a" |
"lval (Vl x) s = s x" |
"lval (Plusl a\<^sub>1 a\<^sub>2) s = (lval a\<^sub>1 s) + (lval a\<^sub>2 s)" |
"lval (LET x a\<^sub>1 a\<^sub>2) s = lval a\<^sub>2 (s(x := lval a\<^sub>1 s))"

fun inline :: "lexp \<Rightarrow> aexp" where
"inline (Nl a) = N a" |
"inline (Vl x) = V x" |
"inline (Plusl a b) = Plus (inline a) (inline b)" |
"inline (LET x a b) = subst x (inline a) (inline b)"

lemma "aval (inline a) s = lval a s"
  apply(induction a arbitrary: s)
     apply(auto)
  done

(* 3.7 *)

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b\<^sub>1 b\<^sub>2) s = (bval b\<^sub>1 s \<and> bval b\<^sub>2 s)" |
"bval (Less a\<^sub>1 a\<^sub>2) s = (aval a\<^sub>1 s < aval a\<^sub>2 s)"

fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"

fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b\<^sub>1 b\<^sub>2 = And b\<^sub>1 b\<^sub>2"

fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N a) (N b) = Bc (a < b)" |
"less a b = Less a b"

fun Eq :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Eq a b = And (Not (less a b)) (Not (less b a))"

fun Le :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"Le a b = Not (And (Not (less a b)) (Not (Eq a b)))"

lemma "bval (Eq a b) s = (aval a s =  aval b s)"
  apply(induction a)
    apply(induction b)
      apply(auto)
  done

lemma "bval (Le a b) s = (aval a s \<le> aval b s)"
  apply(induction a)
    apply(induction b)
      apply(auto)
  done

(* 3.8 *)

datatype ifexp = Bc2 bool | If ifexp ifexp ifexp | Less2 aexp aexp

fun ifval :: "ifexp \<Rightarrow> state \<Rightarrow> bool" where
"ifval (Bc2 v) s = v" |
"ifval (If a b c) s = (if (ifval a s) then (ifval b s) else (ifval c s))" |
"ifval (Less2 a b) s = (aval a s < aval b s)"

fun b2ifexp :: "bexp \<Rightarrow> ifexp" where
"b2ifexp (Bc a) = Bc2 a" |
"b2ifexp (Less a b) = Less2 a b" |
"b2ifexp (Not a) = If (b2ifexp a) (Bc2 False) (Bc2 True)" |
"b2ifexp (And a b) = If (b2ifexp a) (b2ifexp b) (Bc2 False)"


fun if2bexp :: "ifexp \<Rightarrow> bexp" where
"if2bexp (Bc2 v) = Bc v" |
"if2bexp (If a b c) = Not (And (Not (And (if2bexp a) (if2bexp b))) (Not (And (Not (if2bexp a)) (if2bexp c))))" |
"if2bexp (Less2 a b) = Less a b"

lemma "bval (if2bexp exp) s = ifval exp s"
  apply(induction rule: if2bexp.induct)
    apply(auto)
  done

lemma "ifval (b2ifexp exp) s = bval exp s"
  apply(induction rule: b2ifexp.induct)
     apply(auto)
  done

(* 3.9 *)

datatype pbexp = VAR vname | NOT pbexp | AND pbexp pbexp | OR pbexp pbexp

fun pbval :: "pbexp \<Rightarrow> (vname \<Rightarrow> bool) \<Rightarrow> bool" where
"pbval (VAR x ) s = s x" |
"pbval (NOT b) s = (\<not> pbval b s)" |
"pbval (AND b1 b2) s = (pbval b1 s \<and> pbval b2 s)" |
"pbval (OR b1 b2) s = (pbval b1 s \<or> pbval b2 s)"

fun is_nnf :: "pbexp \<Rightarrow> bool" where
"is_nnf (NOT (VAR _)) = True" |
"is_nnf (NOT _) = False" |
"is_nnf (VAR x) = True" |
"is_nnf (AND a b) = (is_nnf a \<and> is_nnf b)" |
"is_nnf (OR a b) = (is_nnf a \<and> is_nnf b)"

fun nnf :: "pbexp \<Rightarrow> pbexp" where
"nnf (NOT (AND a b)) = OR (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (OR a b)) = AND (nnf (NOT a)) (nnf (NOT b))" |
"nnf (NOT (NOT a)) = nnf a" |
"nnf (AND a b) = AND (nnf a) (nnf b)" |
"nnf (OR a b) = OR (nnf a) (nnf b)" |
"nnf (NOT (VAR x)) = NOT (VAR x)" |
"nnf (VAR x) = VAR x"

lemma pbval_nnf : "pbval (nnf b) s = pbval b s"
  apply(induction rule: nnf.induct)
    apply(auto)
  done

lemma is_nnf_nnf : "is_nnf (nnf b)"
  apply(induction b rule: nnf.induct)
        apply(auto)
  done

fun or_below_and :: "pbexp \<Rightarrow> bool" where
"or_below_and (VAR x) = True" |
"or_below_and (NOT a) = or_below_and a" |
"or_below_and (AND a b) = (or_below_and a \<and> or_below_and b)" |
"or_below_and (OR (AND _ _) _) = False" |
"or_below_and (OR _ (AND _ _)) = False" |
"or_below_and (OR a b) = (or_below_and a \<and> or_below_and b)"

fun is_dnf :: "pbexp \<Rightarrow> bool" where
"is_dnf a = (is_nnf a \<and> or_below_and a)"

fun dist_AND :: "pbexp \<Rightarrow> pbexp \<Rightarrow> pbexp" where
"dist_AND (OR a\<^sub>1 a\<^sub>2) b = OR (dist_AND a\<^sub>1 b) (dist_AND a\<^sub>2 b)" |
"dist_AND a (OR b\<^sub>1 b\<^sub>2) = OR (dist_AND a b\<^sub>1) (dist_AND a b\<^sub>2)" |
"dist_AND a b = AND a b"

lemma pbval_dist : "pbval (dist_AND b\<^sub>1 b\<^sub>2) s = pbval (AND b\<^sub>1 b\<^sub>2) s"
  apply(induction b\<^sub>1 b\<^sub>2 rule: dist_AND.induct)
     apply(auto)
  done

lemma is_dnf_dist : "is_dnf a \<Longrightarrow> is_dnf b \<Longrightarrow> is_dnf (dist_AND a b)"
  oops
  