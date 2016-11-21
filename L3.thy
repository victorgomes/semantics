theory L3
  imports RTC
begin

section \<open>Syntax\<close>

text \<open>Lambda terms are represented by De Brujin index\<close>

type_synonym loc = nat

datatype type =
  Unit | 
  Num |
  Bool |
  Prod type type (infix "\<otimes>" 80) |
  Sum type type (infix "\<oplus>" 80) |
  Fn type type (infix "\<rightarrow>" 70)

datatype type_loc = Numref

datatype binop = Plus (".+") | Geq (".\<ge>")

datatype exp =
  Skip ("skip") |
  Number int ("#_" [100] 100) |
  Boolean bool ("$_" [100] 100) |
  Binop exp binop exp ("_ _. _" [65, 1000, 65] 65) |
  Seq exp exp (infixr ";" 65) |
  Cond exp exp exp ("if _ then _ else _ fi" [50, 50, 50] 65) |
  While exp exp ("while _ do _ od" [50, 50] 65) |
  Deref loc ("!l_" [100] 100) |
  Assign loc exp ("l_ := _" [0, 65] 65) |
  Var nat ("`_" [100] 100) |
  App exp exp ("_\<^sup>._" [65, 65] 65) |
  Abs type exp ("fn _ \<Rightarrow> _" [50, 65] 65) |
  Pair exp exp ("<_,_>" [50, 50] 65) |
  Fst exp ("fst _" [65] 65) |
  Snd exp ("snd _" [65] 65) |
  Inl exp type ("inl _ : _" [65, 65] 65) |
  Inr exp type ("inr _ : _" [65, 65] 65) |
  CaseSum exp type exp type exp ("case _ of inl _ \<Rightarrow> _ | inr _ \<Rightarrow> _" [65, 65, 65, 65, 65] 65)

abbreviation true :: exp where "true \<equiv> $True"

abbreviation false :: exp where "false \<equiv> $False"

section \<open>Substitution\<close>

fun lift :: "exp \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> exp" ("_\<up>\<^sub>_\<^sup>_" [50, 55, 55] 50) where
  "skip\<up>\<^sub>n\<^sup>k        = skip" |
  "#m\<up>\<^sub>n\<^sup>k          = #m" |
  "$b\<up>\<^sub>n\<^sup>k          = $b" |
  "`i\<up>\<^sub>n\<^sup>k          = `(if i < k then i else i+n)" |
  "(e1 bop. e2)\<up>\<^sub>n\<^sup>k= (e1\<up>\<^sub>n\<^sup>k) bop. (e2\<up>\<^sub>n\<^sup>k)" |
  "(e1; e2)\<up>\<^sub>n\<^sup>k    = (e1\<up>\<^sub>n\<^sup>k); (e2\<up>\<^sub>n\<^sup>k)" |
  "(if e1 then e2 else e3 fi)\<up>\<^sub>n\<^sup>k =
    if e1\<up>\<^sub>n\<^sup>k then e2\<up>\<^sub>n\<^sup>k else e3\<up>\<^sub>n\<^sup>k fi" |
  "(while e1 do e2 od)\<up>\<^sub>n\<^sup>k =
    while e1\<up>\<^sub>n\<^sup>k do e2\<up>\<^sub>n\<^sup>k od" |
  "!l(i)\<up>\<^sub>n\<^sup>k       = !l(i)" |
  "(l(i):=e)\<up>\<^sub>n\<^sup>k   = l(i):=(e\<up>\<^sub>n\<^sup>k)" |
  "(e1\<^sup>.e2)\<up>\<^sub>n\<^sup>k     = (e1\<up>\<^sub>n\<^sup>k)\<^sup>.(e2\<up>\<^sub>n\<^sup>k)" |
  "(fn T \<Rightarrow> e)\<up>\<^sub>n\<^sup>k = fn T \<Rightarrow> (e\<up>\<^sub>n\<^sup>k+1)" |
  "<e1,e2>\<up>\<^sub>n\<^sup>k     = <e1\<up>\<^sub>n\<^sup>k, e2\<up>\<^sub>n\<^sup>k>" |
  "(fst e)\<up>\<^sub>n\<^sup>k     = fst (e\<up>\<^sub>n\<^sup>k)" |
  "(snd e)\<up>\<^sub>n\<^sup>k     = snd (e\<up>\<^sub>n\<^sup>k)" |
  "(inl e : T)\<up>\<^sub>n\<^sup>k   = inl (e\<up>\<^sub>n\<^sup>k) : T" |
  "(inr e : T)\<up>\<^sub>n\<^sup>k   = inr (e\<up>\<^sub>n\<^sup>k) : T" |
  "(case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2)\<up>\<^sub>n\<^sup>k =
    case (e\<up>\<^sub>n\<^sup>k) of inl T1 \<Rightarrow> (e1\<up>\<^sub>n\<^sup>k+1) | inr T2 \<Rightarrow> (e2\<up>\<^sub>n\<^sup>k+1)"
                   
fun subst :: "exp \<Rightarrow> nat \<Rightarrow> exp \<Rightarrow> exp" ("_[_::=_]" [65, 50, 50] 65) where
  "skip[k::=N]        = skip" |
  "#n[k::=N]          = #n" |
  "$b[k::=N]          = $b" |
  "`i[k::=N]          = (if i < k then `i else
                        if i = k then N else
                        `(i-1))" |
  "(e1 bop. e2)[k::=N]      = (e1[k::=N]) bop. (e2[k::=N])" |
  "(e1;e2)[k::=N]      = (e1[k::=N]);(e2[k::=N])" |
  "if e1 then e2 else e3 fi [k::=N] =
    if e1[k::=N] then e2[k::=N] else e3[k::=N] fi" |
  "while e1 do e2 od [k::=N] = while e1[k::=N] do e2[k::=N] od" |
  "!l(i)[k::=N]        = !l(i)" |
  "(l(i):=e)[k::=N]   = l(i):=(e[k::=N])" |
  "(e1\<^sup>.e2)[k::=N]     = (e1[k::=N])\<^sup>.(e2[k::=N])" |
  "(fn T \<Rightarrow> e)[k::=N] = fn T \<Rightarrow> (e[k+1 ::= N\<up>\<^sub>1\<^sup>0])" |
  "<e1, e2>[k::=N]    = <e1[k::=N], e2[k::=N]>" |
  "(fst e)[k::=N]     = fst (e[k::=N])" |
  "(snd e)[k::=N]     = snd (e[k::=N])" |
  "(inl e : T)[k::=N] = inl (e[k::=N]) : T" |
  "(inr e : T)[k::=N] = inr (e[k::=N]) : T" |
  "(case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2)[k::=N] =
    case (e[k::=N]) of inl T1 \<Rightarrow> (e1[k+1::=N\<up>\<^sub>1\<^sup>0]) | inr T2 \<Rightarrow> (e2[k+1::=N\<up>\<^sub>1\<^sup>0])"

fun closed_at :: "exp \<Rightarrow> nat \<Rightarrow> bool" where
  "closed_at skip _        = True" |
  "closed_at (#_) _        = True" |
  "closed_at ($_) _        = True" |
  "closed_at (`x) n        = (x < n)" |
  "closed_at (e1 bop. e2) n= (closed_at e1 n \<and> closed_at e2 n)" |
  "closed_at (e1;e2) n     = (closed_at e1 n \<and> closed_at e2 n)" |
  "closed_at (if e1 then e2 else e3 fi) n =
      (closed_at e1 n \<and> closed_at e2 n \<and> closed_at e3 n)" |
  "closed_at (while e1 do e2 od) n = (closed_at e1 n \<and> closed_at e2 n)" |
  "closed_at (!l_) _       = True" |
  "closed_at (l(i):=e) n   = closed_at e n" |
  "closed_at (fn _ \<Rightarrow> e) n = closed_at e (n+1)" |
  "closed_at (e1\<^sup>.e2) n     = (closed_at e1 n \<and> closed_at e2 n)" |
  "closed_at (<e1,e2>) n   = (closed_at e1 n \<and> closed_at e2 n)" |
  "closed_at (fst e) n     = closed_at e n" |
  "closed_at (snd e) n     = closed_at e n" |
  "closed_at (inl e : _) n = closed_at e n" |
  "closed_at (inr e : _) n = closed_at e n" |
  "closed_at (case e of inl _ \<Rightarrow> e1 | inr _ \<Rightarrow> e2) n =
    (closed_at e n \<and> closed_at e1 (n+1) \<and> closed_at e2 (n+1))"

abbreviation closed :: "exp \<Rightarrow> bool" where
  "closed e \<equiv> closed_at e 0"

section \<open>Operational semantics\<close>

fun is_value :: "exp \<Rightarrow> bool" where
  "is_value skip = True" |
  "is_value (#_) = True" |
  "is_value ($_) = True" |
  "is_value (fn _ \<Rightarrow> _) = True" |
  "is_value (<e1, e2>) = (is_value e1 \<and> is_value e2)" |
  "is_value (inl e : T) = is_value e" |
  "is_value (inr e : T) = is_value e" |
  "is_value _ = False"

type_synonym store = "loc \<Rightarrow> int option"

inductive sem :: "exp \<times> store \<Rightarrow> exp \<times> store \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  "(skip; e2, s) \<Rightarrow> (e2, s)" |
  "(#n1 .+. #n2, s) \<Rightarrow> (#(n1 + n2), s)" |
  "(#n1 .\<ge>. #n2, s) \<Rightarrow> ($(n1 \<ge> n2), s)" |
  "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (e1 bop. e2, s) \<Rightarrow> (e1' bop. e2, s')" |
  "is_value v \<Longrightarrow> (e2, s) \<Rightarrow> (e2', s') \<Longrightarrow> (v bop. e2, s) \<Rightarrow> (v bop. e2', s')" |
  "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (e1; e2, s) \<Rightarrow> (e1'; e2, s')" |
  "(if true then e2 else e3 fi, s) \<Rightarrow> (e2, s)" |
  "(if false then e2 else e3 fi, s) \<Rightarrow> (e3, s)" |
  "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (if e1 then e2 else e3 fi, s) \<Rightarrow> 
    (if e1' then e2 else e3 fi, s')" |
  "(while e1 do e2 od, s) \<Rightarrow> (if e1 then (e2; while e1 do e2 od) else skip fi, s)" |
  "i \<in> dom s \<Longrightarrow> s i = Some n \<Longrightarrow> (!li, s) \<Rightarrow> (#n, s)" |
  "i \<in> dom s \<Longrightarrow> (l(i) := #n, s) \<Rightarrow> (skip, s(i \<mapsto> n))" |
  "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (l(i) := e, s) \<Rightarrow> (l(i) := e', s')" |
  "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (e1\<^sup>.e2, s) \<Rightarrow> (e1'\<^sup>.e2, s')" |
  "is_value v \<Longrightarrow> (e2, s) \<Rightarrow> (e2', s') \<Longrightarrow> (v\<^sup>.e2, s) \<Rightarrow> (v\<^sup>.e2', s')" |
  "is_value v \<Longrightarrow> ((fn T \<Rightarrow> e)\<^sup>.v, s) \<Rightarrow> (e[0 ::= v], s)" |
  "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (<e1, e2>, s) \<Rightarrow> (<e1', e2>, s')" |
  "is_value v \<Longrightarrow> (e2, s) \<Rightarrow> (e2', s') \<Longrightarrow> (<v, e2>, s) \<Rightarrow> (<v, e2'>, s')" |
  "is_value v1 \<Longrightarrow> is_value v2 \<Longrightarrow> (fst <v1, v2>, s) \<Rightarrow> (v1, s)" |
  "is_value v1 \<Longrightarrow> is_value v2 \<Longrightarrow> (snd <v1, v2>, s) \<Rightarrow> (v2, s)" |
  "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (fst e, s) \<Rightarrow> (fst e', s')" |
  "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (snd e, s) \<Rightarrow> (snd e', s')" |
  "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (inl e : T, s) \<Rightarrow> (inl e' : T, s')" |
  "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (inr e : T, s) \<Rightarrow> (inr e' : T, s')" |
  "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2, s) \<Rightarrow> (case e' of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2, s')" |
  "is_value v \<Longrightarrow> (case inl v : T of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2, s) \<Rightarrow> (e1[0 ::= v], s)" |
  "is_value v \<Longrightarrow> (case inr v : T of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2, s) \<Rightarrow> (e2[0 ::= v], s)"

declare sem.intros[intro!]

inductive_cases sem_elims [elim!]:
  "(skip, s) \<Rightarrow> (e', s')"
  "(#x, s) \<Rightarrow> (e', s')"
  "($x, s) \<Rightarrow> (e', s')"
  "(e1 .+. e2, s) \<Rightarrow> (e', s')"
  "(e1 .\<ge>. e2, s) \<Rightarrow> (e', s')"
  "(e1 bop. e2, s) \<Rightarrow> (e', s')"
  "(`x, s) \<Rightarrow> (e', s')"
  "(e1; e2, s) \<Rightarrow> (e', s')"
  "(if e1 then e2 else e3 fi, s) \<Rightarrow> (e', s')"
  "(while e1 do e2 od, s) \<Rightarrow> (e', s')"
  "(!l(i), s) \<Rightarrow> (e', s')"
  "(l(i) := e, s) \<Rightarrow> (e', s')"
  "(fn T \<Rightarrow> e, s) \<Rightarrow> (e', s')"
  "(e1\<^sup>.e2, s) \<Rightarrow> (e', s')"
  "(<e1, e2>, s) \<Rightarrow> (e', s')"
  "(fst e, s) \<Rightarrow> (e', s')"
  "(snd e, s) \<Rightarrow> (e', s')"
  "(inl e : T, s) \<Rightarrow> (e', s')"
  "(inr e : T, s) \<Rightarrow> (e', s')"
  "(case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2, s) \<Rightarrow> (e', s')"

abbreviation sem_rtc :: "exp \<times> store \<Rightarrow> exp \<times> store \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>*" 50) where
  "\<sigma> \<Rightarrow>\<^sup>* \<sigma>' \<equiv> rtc sem \<sigma> \<sigma>'"

section \<open>Type environment\<close>

definition
  shift :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> nat \<Rightarrow> 'a"  ("_\<langle>_:_\<rangle>" [90, 0, 0] 91) where
  "\<Gamma>\<langle>i:a\<rangle> = (\<lambda>j. if j < i then \<Gamma> j else if j = i then a else \<Gamma> (j - 1))"

lemma shift_eq [simp]: "i = j \<Longrightarrow> (\<Gamma>\<langle>i:T\<rangle>) j = T"
  by (simp add: shift_def)

lemma shift_gt [simp]: "j < i \<Longrightarrow> (\<Gamma>\<langle>i:T\<rangle>) j = \<Gamma> j"
  by (simp add: shift_def)

lemma shift_lt [simp]: "i < j \<Longrightarrow> (\<Gamma>\<langle>i:T\<rangle>) j = \<Gamma> (j - 1)"
  by (simp add: shift_def)

lemma shift_commute [simp]: "\<Gamma>\<langle>i:U\<rangle>\<langle>0:T\<rangle> = \<Gamma>\<langle>0:T\<rangle>\<langle>Suc i:U\<rangle>"
  by (rule ext) (simp_all add: shift_def split: nat.split, force)

section \<open>Typing\<close>

type_synonym type_env = "(nat \<Rightarrow> type) \<times> (nat \<Rightarrow> type_loc option)"

inductive typing :: "(nat \<Rightarrow> type) \<Rightarrow> (nat \<Rightarrow> type_loc option) \<Rightarrow> exp \<Rightarrow> type \<Rightarrow> bool" ("_, _ \<turnstile> _ : _" [50, 50, 50] 50) where
  "\<Gamma>, \<Delta> \<turnstile> skip : Unit" |
  "\<Gamma>, \<Delta> \<turnstile> #n : Num" |
  "\<Gamma>, \<Delta> \<turnstile> $b : Bool" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : Num \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : Num \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e1 .+. e2 : Num" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : Num \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : Num \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e1 .\<ge>. e2 : Bool" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : Unit \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e1; e2 : T" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : Bool \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e3 : T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> if e1 then e2 else e3 fi : T" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : Bool \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : Unit \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> while e1 do e2 od : Unit" |
  "\<Delta> i = Some Numref \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> !l(i) : Num" |
  "\<Delta> i = Some Numref \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e : Num \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> l(i) := e : Unit" |
  "\<Gamma> n = T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> `n : T" |
  "\<Gamma>\<langle>0:T\<rangle>, \<Delta> \<turnstile> e : T' \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> fn T \<Rightarrow> e : T \<rightarrow> T'" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : T \<rightarrow> T' \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : T \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile>e1\<^sup>.e2 : T'" |
  "\<Gamma>, \<Delta> \<turnstile> e1 : T1 \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> e2 : T2 \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> <e1, e2> : T1 \<otimes> T2" |
  "\<Gamma>, \<Delta> \<turnstile> e : T1 \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> inl e : T1 \<oplus> T2 : T1 \<oplus> T2" |
  "\<Gamma>, \<Delta> \<turnstile> e : T2 \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> inr e : T1 \<oplus> T2 : T1 \<oplus> T2" |
  "\<Gamma>, \<Delta> \<turnstile> e : T1 \<oplus> T2 \<Longrightarrow> \<Gamma>\<langle>0:T1\<rangle>, \<Delta> \<turnstile> e1 : T \<Longrightarrow> \<Gamma>\<langle>0:T2\<rangle>, \<Delta> \<turnstile> e2 : T \<Longrightarrow>
    \<Gamma>, \<Delta> \<turnstile> case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2 : T"

declare typing.intros[intro!]

inductive_cases typing_elims[elim!]:
  "\<Gamma>, \<Delta> \<turnstile> skip : T"
  "\<Gamma>, \<Delta> \<turnstile> #x : T"
  "\<Gamma>, \<Delta> \<turnstile> $x : T"
  "\<Gamma>, \<Delta> \<turnstile> `x : T"
  "\<Gamma>, \<Delta> \<turnstile> e1 .+. e2 : T"
  "\<Gamma>, \<Delta> \<turnstile> e1 .\<ge>. e2 : T"
  "\<Gamma>, \<Delta> \<turnstile> e1; e2 : T"
  "\<Gamma>, \<Delta> \<turnstile> if e1 then e2 else e3 fi : T"
  "\<Gamma>, \<Delta> \<turnstile> while e1 do e2 od : T"
  "\<Gamma>, \<Delta> \<turnstile> !l(i) : T"
  "\<Gamma>, \<Delta> \<turnstile> l(i) := e : T"
  "\<Gamma>, \<Delta> \<turnstile> fn T \<Rightarrow> e : T'"
  "\<Gamma>, \<Delta> \<turnstile> e1\<^sup>.e2 : T"
  "\<Gamma>, \<Delta> \<turnstile> <e1,e2> : T"
  "\<Gamma>, \<Delta> \<turnstile> fst e: T"
  "\<Gamma>, \<Delta> \<turnstile> snd e : T"
  "\<Gamma>, \<Delta> \<turnstile> inl e : T : T'"
  "\<Gamma>, \<Delta> \<turnstile> inr e : T : T'"
  "\<Gamma>, \<Delta> \<turnstile> case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2 : T"

section \<open>Let constructor\<close>

definition LetVal :: "type \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" ("let val _ = _ in _ end" [50, 65, 65] 65)  where
  "LetVal T e1 e2 \<equiv> App (Abs T e2) e1"

lemma type_let: "\<Gamma>, \<Delta> \<turnstile> e1 : T \<Longrightarrow> \<Gamma>\<langle>0:T\<rangle>, \<Delta> \<turnstile> e2 : T' \<Longrightarrow> \<Gamma>, \<Delta> \<turnstile> let val T = e1 in e2 end : T'"
  by (auto simp: LetVal_def)

lemma sem_let1: "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (let val T = e1 in e2 end, s) \<Rightarrow> (let val T = e1' in e2 end, s')"
  by (auto simp: LetVal_def)

lemma sem_let2: "is_value v \<Longrightarrow> (let val T = v in e end, s) \<Rightarrow> (e[0 ::= v], s)"
  by (auto simp: LetVal_def)

section \<open>Properties about L2\<close>

lemma subst_appI: "is_value v \<Longrightarrow> e2 = e[0 ::= v] \<Longrightarrow> ((fn T \<Rightarrow> e)\<^sup>.v, s) \<Rightarrow> (e2, s)"
  by auto

lemma [dest]: "is_value e \<Longrightarrow> \<forall>s. \<not> (\<exists>e' s'. (e, s) \<Rightarrow> (e', s'))"
  by (induct e) auto

theorem determinacy:
  assumes "(e, s) \<Rightarrow> (e1, s1)" "(e, s) \<Rightarrow> (e2, s2)"
  shows "(e1, s1) = (e2, s2)"
  using assms by (induction arbitrary: e2 rule: sem.induct; (blast | clarsimp))

lemma lift_up: "e\<up>\<^sub>n\<^sup>k = e \<Longrightarrow> lift e n (Suc k) = e"
  by (induct arbitrary: n k rule: lift.induct) auto

lemma [simp]: "e\<up>\<^sub>0\<^sup>0= e"
  using lift_up by (induct e) auto

lemma shift_lift1 [intro!]: "\<Gamma>, \<Delta> \<turnstile> e : T \<Longrightarrow> \<Gamma>\<langle>i:U\<rangle>, \<Delta> \<turnstile> e\<up>\<^sub>1\<^sup>i : T"
  by (induct arbitrary: i rule: typing.induct)  auto

theorem subst_lemma [intro]:
  assumes "\<Gamma>, \<Delta>  \<turnstile> e : T" "\<Gamma>', \<Delta> \<turnstile> e' : T'" "\<Gamma>  = \<Gamma>'\<langle>i:T'\<rangle>"
  shows   "\<Gamma>', \<Delta> \<turnstile> e[i ::= e'] : T"
using assms proof (induct arbitrary: \<Gamma>' i e' rule: typing.induct)
  fix \<Gamma> \<Delta> e T1 T2 e1 T e2 \<Gamma>' i e'
  assume "\<Gamma>, \<Delta> \<turnstile> e : T1 \<oplus> T2" "\<Gamma>\<langle>0:T1\<rangle>, \<Delta> \<turnstile> e1 : T" "\<Gamma>\<langle>0:T2\<rangle>, \<Delta> \<turnstile> e2 : T"
         "(\<And>\<Gamma>' i e'. \<Gamma>', \<Delta> \<turnstile> e' : T' \<Longrightarrow> \<Gamma> = \<Gamma>'\<langle>i:T'\<rangle> \<Longrightarrow> \<Gamma>', \<Delta> \<turnstile> e[i::=e'] : T1 \<oplus> T2)"
         "(\<And>\<Gamma>' i e'. \<Gamma>', \<Delta> \<turnstile> e' : T' \<Longrightarrow> \<Gamma>\<langle>0:T1\<rangle> = \<Gamma>'\<langle>i:T'\<rangle> \<Longrightarrow> \<Gamma>', \<Delta> \<turnstile> e1[i::=e'] : T)"
         "(\<And>\<Gamma>' i e'. \<Gamma>', \<Delta> \<turnstile> e' : T' \<Longrightarrow> \<Gamma>\<langle>0:T2\<rangle> = \<Gamma>'\<langle>i:T'\<rangle> \<Longrightarrow> \<Gamma>', \<Delta> \<turnstile> e2[i::=e'] : T)"
         "\<Gamma>', \<Delta> \<turnstile> e' : T'" "\<Gamma> = \<Gamma>'\<langle>i:T'\<rangle>"
  thus   "\<Gamma>', \<Delta> \<turnstile> (case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2)[i::=e'] : T"
    apply clarsimp
    apply (rule typing.intros)
    apply force
    apply (erule_tac x="\<Gamma>'\<langle>0:T1\<rangle>" in meta_allE) back
    apply fastforce
    apply fastforce
  done
qed force+

lemma preservation:
  assumes "\<Gamma>, \<Delta> \<turnstile> e : T" "(e, s) \<Rightarrow> (e', s')"
  shows   "\<Gamma>, \<Delta> \<turnstile> e' : T"
  using assms by (induction arbitrary: e' rule: typing.induct) (erule sem_elims; blast)+

lemma preserv_dom:
  assumes "\<Gamma>, \<Delta> \<turnstile> e : T" "(e, s) \<Rightarrow> (e', s')" "dom \<Delta> \<subseteq> dom s"
  shows   "dom \<Delta> \<subseteq> dom s'"
  using assms by (induction arbitrary: e' s  rule: typing.induct) ((erule sem_elims, simp) | blast)+

corollary pres_rtc: 
  assumes "(e, s) \<Rightarrow>\<^sup>* (e', s')" "\<Gamma>, \<Delta> \<turnstile> e : T" "dom \<Delta> \<subseteq> dom s"
  shows   "\<Gamma>, \<Delta> \<turnstile> e' : T" "dom \<Delta> \<subseteq> dom s'"
  using assms by (induction rule: rtc_induct, simp+, (metis preservation preserv_dom)+) 

lemma [dest]: "\<Gamma>, \<Delta> \<turnstile> e : Num \<Longrightarrow> is_value e \<Longrightarrow> \<exists>n. e = #n"
  by (induction e) auto

lemma [dest]: "\<Gamma>, \<Delta> \<turnstile> e : Bool \<Longrightarrow> is_value e \<Longrightarrow> \<exists>n. e = Boolean n"
  by (induction e) auto

lemma [dest]: "\<Gamma>, \<Delta> \<turnstile> e : Unit \<Longrightarrow> is_value e \<Longrightarrow> e = skip"
  by (induction e) auto

lemma [dest]: "\<Gamma>, \<Delta> \<turnstile> e : T \<rightarrow> T' \<Longrightarrow> is_value e \<Longrightarrow> \<exists>e'. e = fn T \<Rightarrow> e'"
  by (induct e, auto)

lemma [dest]: "\<Gamma>, \<Delta> \<turnstile> e1 : Bool \<Longrightarrow> is_value e1 \<Longrightarrow> \<exists>e' s'. (if e1 then e2 else e3 fi, s) \<Rightarrow> (e', s')"
  by (induct e1, auto) (case_tac x, auto)

lemma sumD [dest]: "\<Gamma>, \<Delta> \<turnstile> e : T1 \<oplus> T2 \<Longrightarrow> is_value e \<Longrightarrow> (\<exists>e1. e = inl e1 : T1 \<oplus> T2) \<or> (\<exists>e2. e = inr e2 : T1 \<oplus> T2)"
  by (induct e) auto

lemma progress:
  assumes "\<Gamma>, \<Delta> \<turnstile> e : T" "closed e" "dom \<Delta> \<subseteq> dom s"
  shows   "is_value e \<or> (\<exists>e' s'. (e, s) \<Rightarrow> (e', s'))"
using assms proof (induction arbitrary: T rule: typing.induct) 
  fix \<Gamma> \<Delta> e T1 T2 e1 T e2
  assume "\<Gamma>, \<Delta> \<turnstile> e : T1 \<oplus> T2" "\<Gamma>\<langle>0:T1\<rangle>, \<Delta> \<turnstile> e1 : T" "\<Gamma>\<langle>0:T2\<rangle>, \<Delta> \<turnstile> e2 : T"
         "(closed e \<Longrightarrow> dom \<Delta> \<subseteq> dom s \<Longrightarrow> is_value e \<or> (\<exists>e' s'. (e, s) \<Rightarrow> (e', s')))"
         "closed (case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2)" "dom \<Delta> \<subseteq> dom s"
  thus   "is_value (case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2) \<or> (\<exists>e' s'. (case e of inl T1 \<Rightarrow> e1 | inr T2 \<Rightarrow> e2, s) \<Rightarrow> (e', s'))"
    by safe (drule sumD, force+)
qed (blast | simp)+

corollary safety:
  assumes "\<Gamma>, \<Delta> \<turnstile> e : T" "(e, s) \<Rightarrow>\<^sup>* (e', s')"
          "closed e'" "dom \<Delta> \<subseteq> dom s"
  shows   "is_value e' \<or> (\<exists>e'' s''. (e', s') \<Rightarrow> (e'', s''))"
  by (metis assms pres_rtc progress)

theorem uniqueness:
  assumes "\<Gamma>, \<Delta> \<turnstile> e : T" "\<Gamma>, \<Delta> \<turnstile> e : T'" 
  shows   "T = T'"
  using assms by (induction arbitrary: T' rule: typing.induct; blast)

end