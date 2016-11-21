theory L1
  imports RTC
begin

section \<open>Syntax\<close>

type_synonym loc = nat

datatype type = Num | Bool | Unit

datatype type_loc = Numref

datatype binop = Plus (".+") | Geq (".\<ge>")

datatype exp = Number int ("#_" [1000] 999)
  | Boolean bool ("$_" [1000] 999)
  | Binop exp binop exp ("_ _. _" [64, 1000, 64] 62)
  | Cond exp exp exp ("if _ then _ else _ fi" [0, 0, 0] 62)
  | Assign loc exp ("l_ := _" [0, 65] 62)
  | Deref loc ("!l_" [1000] 999)
  | Skip ("skip")
  | Seq exp exp ("_; _" [61, 59] 60)
  | While exp exp ("while _ do _od" [0, 0] 62)

abbreviation true :: exp where "true \<equiv> $True"

abbreviation false :: exp where "false \<equiv> $False"

section \<open>Operational Semantics\<close>

fun is_value :: "exp \<Rightarrow> bool" where
  "is_value (Number _)  = True"
| "is_value (Boolean b) = True"
| "is_value Skip = True"
| "is_value _ = False"

type_synonym store = "loc \<Rightarrow> int option"

inductive sem :: "exp * store \<Rightarrow> exp * store \<Rightarrow> bool" (infix "\<Rightarrow>" 50) where
  plus:    "(#n1 .+. #n2, s) \<Rightarrow> (#(n1 + n2), s)"
| geq:     "(#n1 .\<ge>. #n2, s) \<Rightarrow> ($(n1 \<ge> n2), s)"
| op1:     "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (e1 bop. e2, s) \<Rightarrow> (e1' bop. e2, s')"
| op2:     "is_value v \<Longrightarrow> (e2, s) \<Rightarrow> (e2', s') \<Longrightarrow> (v bop. e2, s) \<Rightarrow> (v bop. e2', s')"
| deref:   "i \<in> dom s \<Longrightarrow> s i = Some n \<Longrightarrow> (!li, s) \<Rightarrow> (#n, s)"
| assign1: "i \<in> dom s \<Longrightarrow> (l(i) := #n, s) \<Rightarrow> (skip, s(i \<mapsto> n))"
| assign2: "(e, s) \<Rightarrow> (e', s') \<Longrightarrow> (l(i) := e, s) \<Rightarrow> (l(i) := e', s')"
| seq1:    "(skip; e2, s) \<Rightarrow> (e2, s)"
| seq2:    "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (e1; e2, s) \<Rightarrow> (e1'; e2, s')"
| if1:     "(if true then e2 else e3 fi, s) \<Rightarrow> (e2, s)"
| if2:     "(if false then e2 else e3 fi, s) \<Rightarrow> (e3, s)"
| if3:     "(e1, s) \<Rightarrow> (e1', s') \<Longrightarrow> (if e1 then e2 else e3 fi, s) \<Rightarrow> (if e1' then e2 else e3 fi, s')"
| while:   "(while e1 do e2 od, s) \<Rightarrow> (if e1 then (e2; while e1 do e2 od) else skip fi, s)"

declare sem.intros[simp, intro!]

inductive_cases sem_elims [elim!]:  
  "(skip, s) \<Rightarrow> (e', s')"
  "(#n, s) \<Rightarrow> (e', s')"
  "($b, s) \<Rightarrow> (e', s')"
  "(e1 .+. e2, s) \<Rightarrow> (e', s')"
  "(e1 .\<ge>. e2, s) \<Rightarrow> (e', s')"
  "(e1 bop. e2, s) \<Rightarrow> (e', s')"
  "(!l(i), s) \<Rightarrow> (e', s')"
  "(l(i) := e, s) \<Rightarrow> (e', s')"
  "(e1; e2, s) \<Rightarrow> (e', s')"
  "(if e1 then e2 else e3 fi, s) \<Rightarrow> (e', s')"
  "(while e1 do e2 od, s) \<Rightarrow> (e', s')"

abbreviation sem_rtc :: "exp * store \<Rightarrow> exp * store \<Rightarrow> bool" (infix "\<Rightarrow>\<^sup>*" 50) where
  "x \<Rightarrow>\<^sup>* y \<equiv> rtc sem x y"

section \<open>Typing \<close>

type_synonym type_env = "nat \<Rightarrow> type_loc option"

inductive typing :: "type_env \<Rightarrow> exp \<Rightarrow> type \<Rightarrow> bool" ("_ \<turnstile> _ : _" [50, 50, 50] 50) where
  Tnum:     "\<Gamma> \<turnstile> #n : Num"
| Tbool:    "\<Gamma> \<turnstile> $b : Bool"
| Top_plus: "\<Gamma> \<turnstile> e1 : Num \<Longrightarrow> \<Gamma> \<turnstile> e2 : Num \<Longrightarrow> \<Gamma> \<turnstile> e1 .+. e2 : Num"
| Top_geq:  "\<Gamma> \<turnstile> e1 : Num \<Longrightarrow> \<Gamma> \<turnstile> e2 : Num \<Longrightarrow> \<Gamma> \<turnstile> e1 .\<ge>. e2 : Bool"
| Tif:      "\<Gamma> \<turnstile> e1 : Bool \<Longrightarrow> \<Gamma> \<turnstile> e2 : T \<Longrightarrow> \<Gamma> \<turnstile> e3 : T \<Longrightarrow> \<Gamma> \<turnstile> if e1 then e2 else e3 fi : T"
| Tassign:  "\<Gamma> i = Some Numref \<Longrightarrow> \<Gamma> \<turnstile> e : Num \<Longrightarrow> \<Gamma> \<turnstile> l(i) := e : Unit"
| Tderef:   "\<Gamma> i = Some Numref \<Longrightarrow> \<Gamma> \<turnstile> !l(i) : Num"
| Tskip:    "\<Gamma> \<turnstile> skip : Unit"
| Tseq:     "\<Gamma> \<turnstile> e1 : Unit \<Longrightarrow> \<Gamma> \<turnstile> e2 : T \<Longrightarrow> \<Gamma> \<turnstile> e1; e2 : T"
| Twhile:   "\<Gamma> \<turnstile> e1 : Bool \<Longrightarrow> \<Gamma> \<turnstile> e2 : Unit \<Longrightarrow> \<Gamma> \<turnstile> while e1 do e2 od : Unit"

declare typing.intros[simp, intro!]

inductive_cases type_elims[elim!]:
  "\<Gamma> \<turnstile> #n : T"
  "\<Gamma> \<turnstile> $b : T"
  "\<Gamma> \<turnstile> e1 .+. e2 : T"
  "\<Gamma> \<turnstile> e1 .\<ge>. e2 : T"
  "\<Gamma> \<turnstile> !l(i) : T"
  "\<Gamma> \<turnstile> l(i) := e : T"
  "\<Gamma> \<turnstile> e1; e2 : T"
  "\<Gamma> \<turnstile> skip : T"
  "\<Gamma> \<turnstile> if e1 then e2 else e3 fi : T"
  "\<Gamma> \<turnstile> while e1 do e2 od : T"

section \<open>Properties about L1\<close>

lemma [dest]: "is_value e \<Longrightarrow> \<forall>s. \<not> (\<exists>e' s'. (e, s) \<Rightarrow> (e', s'))"
  by (induct e, auto)

theorem determinacy:
  assumes "(e, s) \<Rightarrow> (e1, s1)" "(e, s) \<Rightarrow> (e2, s2)"
  shows "(e1, s1) = (e2, s2)"
  using assms by (induction arbitrary: e2 rule: sem.induct; (blast | clarsimp))

theorem preservation: 
  assumes "\<Gamma> \<turnstile> e : T" "dom \<Gamma> \<subseteq> dom s" "(e, s) \<Rightarrow> (e', s')"
  shows   "\<Gamma> \<turnstile> e' : T \<and> dom \<Gamma> \<subseteq> dom s'"
  using assms by (induction arbitrary: e' rule: typing.induct) (blast | (erule sem_elims; force) | fastforce)+

corollary pres_rtc: 
  assumes "(e, s) \<Rightarrow>\<^sup>* (e', s')" "\<Gamma> \<turnstile> e : T" "dom \<Gamma> \<subseteq> dom s" 
  shows   "\<Gamma> \<turnstile> e' : T \<and> dom \<Gamma> \<subseteq> dom s'"
  using assms by (induction rule: rtc_induct, simp) (drule preservation, simp+)

lemma [dest]: "\<Gamma> \<turnstile> e : Num \<Longrightarrow> is_value e \<Longrightarrow> \<exists>n. e = #n"
  by (induction e) auto

lemma [dest]: "\<Gamma> \<turnstile> e : Bool \<Longrightarrow> is_value e \<Longrightarrow> \<exists>n. e = Boolean n"
  by (induction e) auto

lemma [dest]: "\<Gamma> \<turnstile> e : Unit \<Longrightarrow> is_value e \<Longrightarrow> e = skip"
  by (induction e) auto

lemma [dest]: "\<Gamma> \<turnstile> e1 : Bool \<Longrightarrow> is_value e1 \<Longrightarrow> \<exists>e' s'. (if e1 then e2 else e3 fi, s) \<Rightarrow> (e', s')"
  by (induct e1, auto) (case_tac x, auto)

theorem progress[intro]:
  assumes "\<Gamma> \<turnstile> e : T" "dom \<Gamma> \<subseteq> dom s"
  shows   "is_value e \<or> (\<exists>e' s'. (e, s) \<Rightarrow> (e', s'))"
  using assms by (induction rule: typing.induct; (blast | simp))

corollary safety:
  assumes "\<Gamma> \<turnstile> e : T" "dom \<Gamma> \<subseteq> dom s" "(e, s) \<Rightarrow>\<^sup>* (e', s')"
  shows   "is_value e' \<or> (\<exists>e'' s''. (e', s') \<Rightarrow> (e'', s''))"
  by (metis assms pres_rtc progress)

theorem uniqueness:
  assumes "\<Gamma> \<turnstile> e : T" "\<Gamma> \<turnstile> e : T'"
  shows   "T = T'"
  using assms by (induction rule: typing.induct) auto

end