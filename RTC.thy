theory RTC
  imports Main
begin

inductive rtc :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
  refl: "rtc r x x"
| step: "r x y \<Longrightarrow> rtc r y z \<Longrightarrow> rtc r x z"

hide_fact (open) refl step

lemma star_trans: "rtc r x y \<Longrightarrow> rtc r y z \<Longrightarrow> rtc r x z"
  by (induction rule: rtc.induct) (auto intro: rtc.intros)

lemmas rtc_induct =rtc.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare rtc.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> rtc r x y"
  by(metis rtc.refl rtc.step)

code_pred rtc .

end