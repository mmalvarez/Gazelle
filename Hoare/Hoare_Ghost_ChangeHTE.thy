theory Hoare_Ghost imports 
 "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
 "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompFull"
 "../Relpath" "../Semantics/Gensyn_Sem_Small" "Hoare_Core"
begin

(* This file contains ghost state definitions that use an explicit ghost-state predicate
extension to the Hoare triples, rather than treating ghost state akin to other state.

This is almost definitely not the right approach.

*)

definition imm_safe :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control  \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((s_cont m = Inl []) \<or>
  (\<exists> m' . sem_step_p gs m m'))"

lemma imm_safeI_Done :
  assumes H : "s_cont m = Inl []"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def by auto

lemma imm_safeI_Step :
  assumes H : "sem_step_p gs m m'"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def
  by(cases m'; auto)

lemma imm_safeD :
  assumes H : "imm_safe gs m"
  shows "((s_cont m = Inl []) \<or>
  (\<exists> m' . sem_step_p gs m m'))" using H
  unfolding imm_safe_def by (auto)


definition safe :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
"safe gs m \<equiv>
  (\<forall> m' . sem_exec_p gs m m' \<longrightarrow> imm_safe gs m')"

lemma safeI [intro]:
  assumes H : "\<And> m' . sem_exec_p gs m m' \<Longrightarrow> imm_safe gs m'"
  shows "safe gs m" using H unfolding safe_def
  by auto

lemma safeD :
  assumes H : "safe gs m"
  assumes Hx : "sem_exec_p gs m m'"
  shows "imm_safe gs m'" using H Hx
  unfolding safe_def by blast

definition guarded :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> 'ghost \<Rightarrow> bool) \<Rightarrow> 'ghost \<Rightarrow> 'syn gensyn list \<Rightarrow> bool"
("|_| {_} _")
 where
"guarded gs P g c =
  (\<forall> m . P (payload m) g \<longrightarrow> s_cont m = Inl c \<longrightarrow> safe gs m)"

lemma guardedI [intro] :
  assumes H : "\<And> m . P (payload m) g \<Longrightarrow> s_cont m = Inl c \<Longrightarrow> safe gs m"
  shows "guarded gs P g c" using H
  unfolding guarded_def
  by auto

lemma guardedD :
  assumes H : "guarded gs P g c"
  assumes HP : "P (payload m) g"
  assumes Hcont : "s_cont m = Inl c"
  shows "safe gs m" using assms
  unfolding guarded_def by blast

(* need some way of saying that P and Q are compatible for ghost variables *)
(*
TODO: make sure this is a reasonable definition
*)

definition HT :: "('syn, 'mstate) semc \<Rightarrow> ('ghost \<Rightarrow> 'ghost \<Rightarrow> bool) \<Rightarrow> ('mstate \<Rightarrow> 'ghost \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> 'ghost \<Rightarrow> bool)\<Rightarrow> bool" 
  ("|_| {-_-} {=_=} _ {=_=}")
  where
"HT gs R P c Q =
  (\<forall> c' g g'.  R g g' \<longrightarrow> |gs| {Q} g' (c') \<longrightarrow> |gs| {P} g (c @ c'))"

lemma HTI [intro] :
  assumes H : "\<And> c' g g' . R g g' \<Longrightarrow> |gs| {Q} g' (c') \<Longrightarrow> |gs| {P} g (c @ c')"
  shows "HT gs R P c Q" using H unfolding HT_def
  by auto

lemma HTE [elim]:
  assumes H : "HT gs R P c Q"
  assumes Hg : "R g g'"
  assumes H' : "|gs| {Q} g' c'"
  shows "|gs| {P} g (c@c')" using assms
  unfolding HT_def
  by auto

(* Traditional Hoare triples, without ghost state/relation *)
definition HT' :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow>  bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow>  bool) \<Rightarrow> bool" 
(*  ("|_| {-_-} _ {-_-}") *) where
"HT' gs P c Q = 
  (HT gs (\<lambda> (_ :: unit) (_ :: unit) . True) (\<lambda> st g . P st) c (\<lambda> st g . Q st))"

(* TODO: can this be generalized further? *)
(*
lemma HConseq :
  assumes H : "|gs| {-R-} {= P' =} c {=Q'=}"
  assumes H' : "\<And> st g g' . P st g \<Longrightarrow> P' st g'"
  assumes H'' : "\<And> st g g' . Q' st g' \<Longrightarrow> Q st g"
  shows "|gs| {- R -} {=P=} c {=Q=}"
proof(rule HTI)
  fix c' g g'

  assume Rel : "R g g'"

  assume Exec : "|gs| {Q} g' c'"

  then have Exec1 : "|gs| {Q'} g c'"
    unfolding guarded_def using H'' by blast

  then have Exec2 : "|gs| {Q'} g' c'"
    using HTE[OF H Rel] by auto

  then have Exec'' :"|gs| {P'} g' (c@c')"
    using HTE[OF H Rel] by auto

  then show "|gs| {P} c @ c'"
    unfolding guarded_def using H' by blast
qed
*)

(* 2 approaches
   1. quantification over start + end states
   2. "real" ghost state - but then we need to be careful about collisions
*)

(* approach 1. *)

(* define immediately safe, safe as before. *)
(* guarded now also quantifies over start, end states. or, at least, 2 adjacent states?*)

(* approach 2 *)
(* immediately safe and safe are still the same (?) *)
(* guard now takes a ghost state, assumes that ghost predicate is satisfied *)
(* predicates extended to use ghost state *)




end