theory Hoare_Direct imports Hoare
begin

(* Implementation of a direct-style (as opposed to CPS) Hoare logic.
 * This ends up being useful for reasoning about single-steps for languages
 * that do not affect control flow.
 *)

definition HT :: 
  "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  ("{{_}} _ {{_}}" [0,0,0] 61) where
"HT pre x post =
  (\<forall> a b . pre a \<longrightarrow> x a b \<longrightarrow> post b)"

lemma HTI :
  assumes H1 : 
    "\<And> a b . pre a \<Longrightarrow> x a b \<Longrightarrow> post b"
  shows "HT pre x post" using assms
  unfolding HT_def by auto

lemma HTE :
  assumes H : "HT pre x post"
  assumes Ha : "pre a"
  assumes Hb : "x a b"
  shows "post b" using assms
  unfolding HT_def by auto

(* Hoare triple for an executable semantics *)
definition HTS ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ % {{_}} _ {{_}}" [250,252,254,256])  
  where
"HTS sem pre x post =
  HT pre (\<lambda> a b . sem x a = b) post"

lemma HTSI :
  assumes H1 : 
    "\<And> a . pre a \<Longrightarrow> post (sem x a)"
  shows "HTS sem pre x post" using assms
  unfolding HTS_def HT_def by auto

lemma HTSE :
  assumes H : "HTS sem pre x post"
  assumes Ha : "pre a"
  shows "post (sem x a)"
  using assms unfolding HTS_def HT_def by auto

lemma HTS_Conseq :
  assumes H1 : "sem % {{P}} c {{Q}}"
  assumes HP : "\<And> x . P' x \<Longrightarrow> P x"
  assumes HQ : "\<And> x . Q x \<Longrightarrow> Q' x"
  shows "sem % {{P'}} c {{Q'}}"
proof(rule HTSI)
  fix a
  assume P' : "P' a"
  hence P : "P a" using HP by blast
  have Q: "Q (sem c a)"
    using HTSE[OF H1 P] by simp
  show "Q' (sem c a)"
    using HQ[OF Q] by simp
qed


end