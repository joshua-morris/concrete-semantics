theory AExp_Copy imports Main begin

type_synonym vname = string
type_synonym val = int
type_synonym state = "vname \<Rightarrow> val"

text_raw\<open>\snip{AExpaexpdef}{2}{1}{%\<close>
datatype aexp = N int | V vname | Plus aexp aexp | Times aexp aexp
text_raw\<open>}%endsnip\<close>

text_raw\<open>\snip{AExpavaldef}{1}{2}{%\<close>
fun aval :: "aexp \<Rightarrow> state \<Rightarrow> val" where
"aval (N n) s = n" |
"aval (V x) s = s x" |
"aval (Plus a\<^sub>1 a\<^sub>2) s = aval a\<^sub>1 s + aval a\<^sub>2 s" |
"aval (Times a1 a2) s = aval a1 s * aval a2 s"
text_raw\<open>}%endsnip\<close>


value "aval (Plus (V ''x'') (N 5)) (\<lambda>x. if x = ''x'' then 7 else 0)"

text \<open>The same state more concisely:\<close>
value "aval (Plus (V ''x'') (N 5)) ((\<lambda>x. 0) (''x'':= 7))"

text \<open>A little syntax magic to write larger states compactly:\<close>

definition null_state ("<>") where
  "null_state \<equiv> \<lambda>x. 0"
syntax 
  "_State" :: "updbinds => 'a" ("<_>")
translations
  "_State ms" == "_Update <> ms"
  "_State (_updbinds b bs)" <= "_Update (_State b) bs"

text \<open>\noindent
  We can now write a series of updates to the function \<open>\<lambda>x. 0\<close> compactly:
\<close>
lemma "<a := 1, b := 2> = (<> (a := 1)) (b := (2::int))"
  by (rule refl)

value "aval (Plus (V ''x'') (N 5)) <''x'' := 7>"


text \<open>In  the @{term[source] "<a := b>"} syntax, variables that are not mentioned are 0 by default:
\<close>
value "aval (Plus (V ''x'') (N 5)) <''y'' := 7>"

text\<open>Note that this \<open><\<dots>>\<close> syntax works for any function space
\<open>\<tau>\<^sub>1 \<Rightarrow> \<tau>\<^sub>2\<close> where \<open>\<tau>\<^sub>2\<close> has a \<open>0\<close>.\<close>


subsection "Constant Folding"

text\<open>Now we also eliminate all occurrences 0 in additions. The standard
method: optimized versions of the constructors:\<close>

text_raw\<open>\snip{AExpplusdef}{0}{2}{%\<close>
fun plus :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"plus (N i\<^sub>1) (N i\<^sub>2) = N(i\<^sub>1+i\<^sub>2)" |
"plus (N i) a = (if i=0 then a else Plus (N i) a)" |
"plus a (N i) = (if i=0 then a else Plus a (N i))" |
"plus a\<^sub>1 a\<^sub>2 = Plus a\<^sub>1 a\<^sub>2"
text_raw\<open>}%endsnip\<close>

lemma aval_plus[simp]:
  "aval (plus a1 a2) s = aval a1 s + aval a2 s"
apply(induction a1 a2 rule: plus.induct)
apply simp_all (* just for a change from auto *)
done

fun times :: "aexp \<Rightarrow> aexp \<Rightarrow> aexp" where
"times (N i1) (N i2) = N (i1 * i2)" |
"times (N i) a = (if i=0 then a else Times (N i) a)" |
"times a (N i) = (if i=0 then a else Times a (N i))" |
"times a1 a2 = Times a1 a2"

fun asimp :: "aexp \<Rightarrow> aexp" where
"asimp (N n) = N n" |
"asimp (V x) = V x" |
"asimp (Plus a\<^sub>1 a\<^sub>2) = plus (asimp a\<^sub>1) (asimp a\<^sub>2)"
"asimp (Times a1 a2) = times (asimp a1) (asimp a2)

value "asimp (Plus (Plus (N 0) (N 0)) (Plus (V ''x'') (N 0)))"

theorem aval_asimp[simp]:
  "aval (asimp a) s = aval a s"
apply(induction a)
apply simp_all
done

end