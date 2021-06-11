theory CPS_Hoare imports 
 "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
 "../Lifting/LiftUtils" "../Lifting/LiftInstances" "../Lifting/LangCompFull"
 "../Relpath" "../Semantics/Gensyn_Sem_Small" "Hoare"
begin

(* TODO: use general version of langcomp? *)

(* ok, so in order to adapt CPS hoare triples into this context,
   we need a more "normal-looking" system where we can separate
   continuations from state *)

(* TODO: we don't really need gensyn_sem_small i think? *)

datatype s_error =
  Exec childpath
  | BadPath
  | NoFuel
  | Done
  | Crash
  | Halted (* halted = too much fuel *)

fun s_error_safe :: "s_error \<Rightarrow> bool" where
"s_error_safe (Exec _) = True"
| "s_error_safe Done = True"
| "s_error_safe _ = False"

(* we also need to be able to separate sub-syntax from entire tree *)

(*
  new approach:
  - structure the state as a pair: continuations, everything else
  - OR. we keep going forward with the lifting approach, figure out the syntax issue
*)

type_synonym ('full, 'mstate) control =
  "('full gensyn list md_triv option md_prio * 'mstate)"

record ('syn, 'mstate) sem' =
  s_sem :: "'syn \<Rightarrow> 'mstate \<Rightarrow> 'mstate"

(* TODO: this should be an entire lifting (at least a weak lifting.) *)
(*
record ('syn, 'full, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_cont :: "'mstate \<Rightarrow> 'full gensyn list"
*)

(*
record ('syn, 'full, 'mstate) sem = "('syn, 'mstate) sem'" +
  s_l :: "('syn, 'full gensyn list, 'mstate) lifting"
*)

record ('syn, 'full, 'mstate) sem = 
  s_sem :: "'syn \<Rightarrow> ('full, 'mstate) control \<Rightarrow> ('full, 'mstate) control"

definition s_cont :: "('full, 'mstate) control \<Rightarrow> 'full gensyn list" where
"s_cont m \<equiv>
  (case m of
    ((mdp _ (Some (mdt x))), _) \<Rightarrow> x
    | _ \<Rightarrow> [])"

(*
definition close :: "('syn, 'full, 'mstate) sem \<Rightarrow> ('full \<Rightarrow> 'syn) \<Rightarrow> ('full, 'full, 'mstate) sem" where
"close s f =
  \<lparr> s_sem = (s_sem s o f)
  , s_cont = s_cont s \<rparr>"
*)
(* "closed" sem
   we obtain this when our "full" syntax becomes the same as
   our "individual syntax"
*)
type_synonym ('syn, 'mstate) semc = "('syn, 'syn, 'mstate) sem"

record ('syn, 'full, 'mstate) semt = "('syn, 'full, 'mstate) sem" +
  s_transl :: "'full \<Rightarrow> 'syn"

(*
definition s_semt :: "('syn, 'full, 'mstate) semt \<Rightarrow> 'full \<Rightarrow> 'mstate \<Rightarrow> 'mstate" where
"s_semt s = s_sem s o s_transl s"
*)
(* will integrating this with s_cont help? *)
definition sem_step ::
  "('syn, 'mstate) semc \<Rightarrow>
   ('syn, 'mstate) control \<Rightarrow>
   ('syn, 'mstate) control option" where
"sem_step gs m =
  (case s_cont m of
    [] \<Rightarrow> None
    | ((G x l)#tt) \<Rightarrow> Some (s_sem gs x m))"

(* Another option: leave an "open port" in all control flow modules?

see if this will break any typeclasses...

*)

fun sem_exec ::
  "('syn, 'mstate) semc \<Rightarrow>
   nat \<Rightarrow>
   ('syn, 'mstate) control \<Rightarrow>
   (('syn, 'mstate) control * s_error)" where
"sem_exec gs 0 m = 
  (case s_cont  m of
    [] \<Rightarrow> (m, Done)
    | _ \<Rightarrow> (m, NoFuel))"
| "sem_exec gs (Suc n) m =
   (case s_cont m of
    [] \<Rightarrow> (m, Halted)
    | ((G x l)#tt) \<Rightarrow> sem_exec gs n (s_sem gs x m))"

inductive sem_step_p ::
  "('syn, 'mstate) semc  \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool"
  where
"\<And> gs m m' x l  tt .
 s_cont m = ((G x l)#tt) \<Longrightarrow> 
 s_sem gs x m = m' \<Longrightarrow>
 sem_step_p gs m m'"

definition sem_exec_p ::
  "('syn, 'mstate) semc  \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
"sem_exec_p gs \<equiv>
  (rtranclp (sem_step_p gs))"

declare sem_exec_p_def [simp add]

lemma sem_step_p_sem_step :
  assumes H : "sem_step_p gs m m'"
  shows "sem_step gs m = Some m'" using H
proof(cases rule: sem_step_p.cases)
  case (1 sub)
  then show ?thesis 
    by(auto simp add: sem_step_def)
qed

lemma sem_step_sem_step_p :
  assumes H : "sem_step gs m = Some m'"
  shows "sem_step_p gs m m'" using H
  by(auto simp add: sem_step_def split: s_error.splits list.splits option.splits intro: sem_step_p.intros)

lemma sem_step_p_eq :
  "(sem_step_p gs m m') = (sem_step gs m = Some m') "
  using sem_step_p_sem_step[of gs m m'] sem_step_sem_step_p[of gs m m']
  by(auto)

lemma sem_step_exec1 :
  assumes H : "sem_step gs m = Some m'"
  shows "\<exists> s . (sem_exec gs 1 m = (m', s))" using H
  by(auto simp add: sem_step_def  split:list.splits option.splits)

lemma sem_exec1_step :
  assumes H : "(sem_exec gs 1 m = (m', s))"
  assumes H' : "s_error_safe s"
  shows "sem_step gs m = Some m'" using assms
  by(auto simp add: sem_step_def split:option.splits list.splits)

abbreviation spred :: "('b \<Rightarrow> bool) \<Rightarrow> ('a * 'b) \<Rightarrow> bool" ("\<star>_")
  where
"\<star>P \<equiv> P o snd"

(* have the state contain a delta to the continuation list?
   that is, a new prefix to prepend *)
definition imm_safe :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control  \<Rightarrow> bool" where
"imm_safe gs m \<equiv>
 ((s_cont m = []) \<or>
  (\<exists> m' . sem_step_p gs m m'))"

lemma imm_safeI_Done :
  assumes H : "s_cont m = []"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def by auto

lemma imm_safeI_Step :
  assumes H : "sem_step_p gs m m'"
  shows "imm_safe gs m" using H
  unfolding imm_safe_def
  by(cases m'; auto)

lemma imm_safeD :
  assumes H : "imm_safe gs m"
  shows "((s_cont m = []) \<or>
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

(* TODO: syntax *)
definition guarded :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> bool"
("|_| {_} _")
 where
"guarded gs P c =
  (\<forall> m . P (snd m) \<longrightarrow> s_cont m = c \<longrightarrow> safe gs m)"

lemma guardedI [intro] :
  assumes H : "\<And> m . P (snd m) \<Longrightarrow> s_cont m = c \<Longrightarrow> safe gs m"
  shows "guarded gs P c" using H
  unfolding guarded_def
  by auto

lemma guardedD :
  assumes H : "guarded gs P c"
  assumes HP : "P (snd m)"
  assumes Hcont : "s_cont m = c"
  shows "safe gs m" using assms
  unfolding guarded_def by blast

definition HT :: "('syn, 'mstate) semc \<Rightarrow> ('mstate \<Rightarrow> bool) \<Rightarrow> 'syn gensyn list \<Rightarrow> ('mstate \<Rightarrow> bool)\<Rightarrow> bool" 
  ("|_| {-_-} _ {-_-}")
  where
"HT gs P c Q =
  (\<forall> c' .  |gs| {Q} (c') \<longrightarrow> |gs| {P} (c @ c'))"

lemma HTI [intro] :
  assumes H : "\<And> c' . |gs| {Q} (c') \<Longrightarrow> |gs| {P} (c @ c')"
  shows "HT gs P c Q" using H unfolding HT_def
  by auto

lemma HTE [elim]:
  assumes H : "HT gs P c Q"
  assumes H' : "|gs| {Q} c'"
  shows "|gs| {P} (c@c')" using assms
  unfolding HT_def
  by auto

(* maybe there is another way we can achieve some kind of separation of concerns between control/continuation
   and the rest of the state... 
   heavy(ier) weight approach: just use lens (identity lifting)
   or just directly require that it be a product
    - continuation list
    - result continuation change (does this even need to be separate?)
    - other state
*)

lemma HConseq :
  assumes H : "|gs| {- P' -} c {-Q'-}"
  assumes H' : "\<And> st . P st \<Longrightarrow> P' st"
  assumes H'' : "\<And> st . Q' st \<Longrightarrow> Q st"
  shows "|gs| {-P-} c {-Q-}"
proof(rule HTI)
  fix c'
  assume Exec : "|gs| {Q} c'"

  then have Exec' : "|gs| {Q'} c'"
    unfolding guarded_def using H'' by blast

  then have Exec'' :"|gs| {P'} c@c'"
    using HTE[OF H Exec'] by auto

  then show "|gs| {P} c @ c'"
    unfolding guarded_def using H' by blast
qed

lemma HStep : 
  assumes H : "(! sem ) % {{P o snd}} c {{Q o snd}}"
  assumes Hgs : "s_sem gs = sem"
  shows "|gs| {-P-} [G c l] {-Q-}" 
proof(rule HTI)
  fix c'
  assume Exec : "|gs| {Q} c'"

  show "|gs| {P} [G c l] @ c'"
  proof(rule guardedI)
    fix m :: "('a, 'b) control"

    assume P : "P (snd m)"
    obtain ms mc where M: "m = (mc, ms)" and P' : "P ms"
      using P by (cases m; auto)

    assume Cont : "s_cont m = [G c l] @ c'"

    have Q: "Q (snd (s_sem gs c m))"
      using H P M unfolding semprop2_def VT_def Hgs
      by(auto)

    show "safe gs m"
    proof(rule safeI)
      fix m'
      assume Exec' : "sem_exec_p gs m m'"
      show "imm_safe gs m'"

      proof(cases "s_cont m'")
        case Nil
        then show ?thesis unfolding imm_safe_def by auto
      next
        case (Cons a list)
        then show ?thesis using Exec' unfolding sem_exec_p_def imm_safe_def sem_step_p_eq sem_step_def
          by(cases m; auto)
      qed
    qed
  qed
qed


(* sequencing lemma *)
lemma HCat :
  assumes H : "|gs| {- P1 -} c1 {- P2 -}"
  assumes H' : "|gs| {- P2 -} c2 {- P3 -}"
  shows "|gs| {- P1 -} c1 @ c2 {- P3 -}"
proof(rule HTI)
  fix c'
  assume HP3 : "|gs| {P3} c'"

  have P2_cont : "|gs| {P2} c2 @ c'"
    using HTE[OF H' HP3]
    by auto

  show "|gs| {P1} (c1 @ c2) @ c'"
    using HTE[OF H P2_cont]
    unfolding append_assoc
    by auto
qed

definition determ :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
"determ R \<equiv>
  (\<forall> a b b' . R a b \<longrightarrow> R a b' \<longrightarrow> b = b')"

lemma determI [intro] :
  assumes "\<And> a b b' . R a b \<Longrightarrow> R a b' \<Longrightarrow> b = b'"
  shows "determ R" using assms unfolding determ_def by auto

lemma determE :
  assumes H : "determ R"
  assumes H1 : "R a b"
  assumes H2 : "R a b'"
  shows "b = b'" using assms
  unfolding determ_def
  by auto

lemma sem_step_determ :
  "determ (sem_step_p gs)"
proof
  fix a b b'
  assume H1 : "sem_step_p gs a b"
  assume H2 : "sem_step_p gs a b'"

  show "b = b'" using H1 H2 unfolding sem_step_p_eq by auto
qed

(* lemma for reasoning about compound executions *)
lemma rtranclp_bisect1 :
  assumes H0 : "determ R"
  assumes H : "R\<^sup>*\<^sup>* xi xp"
  assumes H1 : "R xi x1"
  assumes H2 : "R xp xf"
  shows "R\<^sup>*\<^sup>* x1 xf" using H H0 H1 H2
proof(induction arbitrary: x1 xf rule: rtranclp_induct)
  case base

  have Eq : "x1 = xf" using determE[OF H0 base(2) base(3)] by auto

  then show ?case using base by auto
next
  case (step y z)

  have X1z : "R\<^sup>*\<^sup>* x1 z" using step.IH[OF step.prems(1) step.prems(2) step.hyps(2)]
    by auto

  show ?case using rtranclp.intros(2)[OF X1z step.prems(3)] by auto
qed

(* lemma for reasoning about executions which cannot step  *)
lemma rtranclp_nostep :
  assumes H0 : "determ R"
  assumes H : "R\<^sup>*\<^sup>* x1 x2"
  assumes H1 : "\<And> x1' . R x1 x1' \<Longrightarrow> False"
  shows "x1 = x2" using H H0 H1
proof(induction  rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step y z)

  have Xeq : "x1 = y"
    using step.IH[OF step.prems(1) step.prems(2), of id]
    by auto

  show ?case using step.hyps step.prems(2) unfolding Xeq
    by auto
qed


definition diverges :: "('syn, 'mstate) semc \<Rightarrow> ('syn, 'mstate) control \<Rightarrow> bool" where
"diverges gs st =
  (\<forall> st' . sem_exec_p gs st st' \<longrightarrow> (\<exists> st'' . sem_step_p gs st' st''))"

lemma divergesI :
  assumes H : "\<And> st' . sem_exec_p gs st st' \<Longrightarrow> (\<exists> st'' . sem_step_p gs st' st'')"
  shows "diverges gs st" using H unfolding diverges_def by auto

lemma divergesD :
  assumes H : "diverges gs st"
  assumes Hst : "sem_exec_p gs st st'"
  shows "\<exists> st'' . sem_step_p gs st' st''"
    using assms unfolding diverges_def by blast

lemma diverges_safe :
  assumes H : "diverges gs st"
  shows "safe gs st" using H
  unfolding diverges_def safe_def imm_safe_def by blast

(* lemma for lifting composed languages in the case where
   one "always wins" for a given syntax element
*)

(* A general version of this may be provable. for now let's just prove
different ones for each thing. *)

(*
lemma HDominant :
  assumes H0 : "gs = \<lparr> s_sem = pcomps' fs \<rparr>"
  assumes Hdom : "(f \<downharpoonleft> (set fs) x)"
  assumes Hnemp : "g \<in> set fs"

  assumes Hpres : "sups_pres (set fs)"

(* this does not quite work. we would need that the tail evaluates in
the big semantics. so maybe it's easier to just
do this on a case by case basis, one for each language element that
needs a multi-step treatment. *)
  assumes Htrip : "|\<lparr> s_sem = f \<rparr>| {- P1 -} [G x l] {- P2 -}"
  shows "|gs| {- P1 -} [G x l] {- P2 -}"
proof
  fix c'
  assume Guard :  "|gs| {P2} c'"

  show "|gs| {P1} [G x l] @ c'"
  proof
    fix m :: "('a, 'b) control"

    assume P1 : "P1 (snd m)"
    assume Cont1 : "s_cont m = [G x l] @ c'"

    show "safe gs m"
    proof(cases "sem_step gs m")
      case None
      then show ?thesis using Cont1 H0
        by(auto simp add: sem_step_def)
    next
      case (Some m')

      have F_eq : "sem_step \<lparr> s_sem = f \<rparr> m = Some m'"
        using sym[OF dominant_pcomps'[OF Hpres Hnemp Hdom]] Cont1 Some H0
        by(simp add: sem_step_def)

      then show ?thesis
      proof(cases "s_cont m'")
        case Nil
        then show ?thesis sorry (* halted means safe *)
      next
        case (Cons ch ct)

        have Step : "sem_step_p gs m m'" using Some
          unfolding sem_step_p_eq
          by auto

        have Safe' : "safe gs m'" using guardedD[OF Guard M' Fcont] by auto


        show "safe gs m"
        proof
          fix m''

          assume Exec : "sem_exec_p gs m m''"
          hence Exec' : "(sem_step_p gs)\<^sup>*\<^sup>* m m''"
            unfolding sem_exec_p_def by auto
  
          show "imm_safe gs m''" using Exec'
          proof(cases rule: rtranclp.cases)
            case rtrancl_refl
            then show ?thesis 
              using Some 
              unfolding imm_safe_def sem_step_p_eq
              by(auto)
          next
            case (rtrancl_into_rtrancl b)
  
            have Exec_final : "sem_exec_p gs m' m''"
              using rtranclp_bisect1
                [OF sem_step_determ rtrancl_into_rtrancl(1)
                    Step rtrancl_into_rtrancl(2)]
              unfolding sem_exec_p_def
              by auto
  
            show ?thesis using safeD[OF Safe' Exec_final] by auto
          qed
        qed
      qed
    qed

        have M' : "P1 (snd m')"
          using HTE[OF Htrip]

        then show ?thesis 
      qed
    qed


    proof
      fix m'

      assume Exec : "sem_exec_p gs m m'"

      then show "imm_safe gs m'"
        unfolding sem_exec_p_def
      proof(cases rule: rtranclp.cases)
        case rtrancl_refl
        then show ?thesis using Cont1 
          by(simp add: imm_safe_def sem_step_p_eq sem_step_def)
      next
        case (rtrancl_into_rtrancl b)

        

        then show ?thesis using HTE[OF Htrip]
      qed
*)
(* x' vs y' ? *)
(* need to handle early halting. 
to do this we can either make the semantics monotone, or have some way of handling this
we can also punt on the issue by requiring that the execution not have halted yet
*)
(*
need to account for the possibility that the sub-language ends early.
one approach: perhaps we could weaken this:
- whenever sem_exec_p of sub language can step to some state,
there will exist a state that sem_exec_p of big language steps to
*)
(* TODO: the following is the wrong approach.
instead we should quantify over arbitrary extensions
of each semantics
*)
(*
lemma sups_pres_merge :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "s_sem gs1 \<in> set l"
  assumes Exec : "(sem_exec_p \<lparr>sem.s_sem = pcomps' l\<rparr>) x x'"
  assumes Y : "y <[ x"
  shows "\<exists> y' . sem_exec_p gs1 y y' \<and> y' <[ x'"
  using Exec Pres Sem Y
  unfolding sem_exec_p_def
proof(induction arbitrary: gs1 y rule: rtranclp_induct)
  case base

  then have C1 : "(sem_step_p gs1)\<^sup>*\<^sup>* y y"
    by(auto)

  thus ?case using base
    by blast
next
  case (step y1 z1)
(* need to obtain a syn. for y1? *)

  obtain y' where Y' : "(sem_step_p gs1)\<^sup>*\<^sup>* y y'" and Y'_leq : "y' <[ y1"
    using step.IH[OF step.prems(1) step.prems(2) step.prems(3)]
    by auto

  obtain y1chs y1chl y1ct where Y1_cont : "s_cont y1 = (G y1chs y1chl)#y1ct"
    using step.hyps(2) unfolding sem_step_p_eq sem_step_def
    by (cases "s_cont y1"; auto)

  have Y'_in : "y' \<in> {y', y1}" by auto
  have Y'_fin : "finite {y', y1}" by auto
  have Y1_sup : "is_sup {y', y1} y1"
    using Y'_leq unfolding is_sup_def is_least_def is_ub_def
    by(auto simp add: leq_refl)
(*  have Gs1_sub : "{s_sem gs1} \<subseteq> set l" using step.prems(2) by auto *)
  have Gs1_sub : "set l \<subseteq> set l" by auto
  have Gs1_in : "s_sem gs1 \<in> set l" using step.prems(2) by auto

(*
  obtain supr where Supr1 : "is_sup ((\<lambda>f. f y1chs y1) ` set l) supr" 
  and Supr2 : "is_sup (scross ((\<lambda>f. f y1chs) ` set l) {y', y1}) supr"
    using sups_presD[OF step.prems(1) Y'_in Y'_fin Y1_sup Gs1_sub Gs1_in, of y1chs] 
    by auto
*)

  have Supr : "is_sup (scross ((\<lambda> f . f y1chs) ` set l) {y', y1}) (pcomps' l y1chs y1)"
    using sups_pres_pcomps'_gen[OF step.prems(1) Gs1_in Y'_fin Y'_in Y1_sup, of y1chs]
    by auto

(* need this or next *)
  have Step_in : "s_sem gs1 y1chs y1 \<in> ((\<lambda>f. f y1chs y1) ` set l)"
    using step.prems(2)
    by auto

(* need this or prev *)
  have Step_in2 : "s_sem gs1 y1chs y' \<in> (scross ((\<lambda>f. f y1chs) ` set l) {y', y1})"
  proof(rule scross_inI)
    show "s_sem gs1 y1chs \<in> (\<lambda>f. f y1chs) ` set l" using step.prems(2) by auto
    show "y' \<in> {y', y1}" by auto
    show "sem.s_sem gs1 y1chs y' = sem.s_sem gs1 y1chs y'" by auto
  qed

  have Compare : "s_sem gs1 y1chs y' <[ (pcomps' l y1chs y1)"
    using is_sup_unfold1[OF Supr Step_in2]
    by auto

(* this works but i don't think it's what we want. *)
(*
  have Hmm : "y1 <[ z1" using step.prems step.hyps
  *)

  have Step' : "sem_step_p gs1 y' (s_sem gs1 y1chs y')"
    using sem_step_p.intros[OF ]
    sorry
  show ?case using Y' step.prems step.hyps Y' Y'_leq Compare
qed

(* this one seems maybe not true... *)
lemma sups_pres_guard :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "s_sem gs1 \<in> set l"
  assumes Hguard : "|gs1| {X} c"
  shows "|\<lparr>s_sem = pcomps' l\<rparr>| {X} c"
proof
  fix m :: "('a gensyn list md_triv option md_prio \<times> 'b)"

  assume X : "X (snd m)"

  assume Xc : "s_cont m = c"

  show "safe \<lparr>sem.s_sem = pcomps' l\<rparr> m"
  proof

    fix m'
    (* we still have the problem that if gs1 terdminates early, we may miss the fact that
       the entire computation may not terminate... *)
    assume "sem_exec_p \<lparr>sem.s_sem = pcomps' l\<rparr> m m'"
(*
    using guardedD[OF Hguard X Xc]
    apply(cases m)
  *)



(* merging multi-step computations *)
(* i think we need either induction or some kind of inductive lemma. *)
(* it really feels like we are missing some information about Q... *)
lemma Hmerge :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "s_sem gs1 \<in> set l"
  assumes V : "|gs1| {-P-} x {-Q-}"
  shows "|\<lparr> s_sem = pcomps' l \<rparr>| 
         {-P-}
         x
         {-(\<lambda> st . \<exists> st_sub . Q st_sub \<and> st_sub <[ st)-}"
proof
  fix c'

  assume HQ : "|\<lparr>sem.s_sem = pcomps' l\<rparr>| {\<lambda>st. \<exists>st_sub. Q st_sub \<and> st_sub <[ st} c'"

  have HQ' :
    "|\<lparr>sem.s_sem = pcomps' l\<rparr>| {Q} c'"
  proof
    fix m :: "('a, 'b) control"
    assume Q : "Q (snd m)"
    assume HCont : "s_cont m = c'"

    have "Q (snd m) \<and> snd m <[ snd m"
      using Q leq_refl[of "snd m"]
      by auto

    hence Convert : "\<exists>st_sub. Q st_sub \<and> st_sub <[ snd m"
      by blast

    show "safe \<lparr>sem.s_sem = pcomps' l\<rparr> m"
      using guardedD[OF HQ Convert HCont] by auto
  qed


  show "|\<lparr>sem.s_sem = pcomps' l\<rparr>| {P} x @ c'"
(*
  proof(cases x)
    case Nil
    then show ?thesis using HTE[OF V]
  next
    case (Cons a list)
    then show ?thesis sorry
  qed
*)

  proof
    fix m :: "('a, 'b) control"
    assume HP : "P (snd m)"
    assume HCont : "s_cont m = x @ c'"

(*
(* cases on sem_step *)
    obtain m1 where "sem_step gs m = Some m1" using HCont unfolding sem_step_def
      apply(auto)
*)      

    show "safe \<lparr>sem.s_sem = pcomps' l\<rparr> m"

    proof
      fix m'
      assume Exec' : "sem_exec_p \<lparr>sem.s_sem = pcomps' l\<rparr> m m'"
        (* idea: change ordering on control data so that it is
              option of prio of triv of cont (but this doesn't work...)
              somehow make it so that if any one semantics is safe, they all are?

is this theorem true as we've stated it?
what do we want instead if it isn't?
*)

      show "imm_safe \<lparr>sem.s_sem = pcomps' l\<rparr> m'"
      proof(cases "sem_step \<lparr>sem.s_sem = pcomps' l\<rparr> m")
        case None
  
        then have Done : "s_cont m = []"
          using None by(cases "s_cont m"; auto simp add: sem_step_def)
   
        show ?thesis using Exec' unfolding sem_exec_p_def
        proof(cases rule: rtranclp.cases)
          case rtrancl_refl
          then show ?thesis using None Done unfolding imm_safe_def
            by(auto)
        next
          case (rtrancl_into_rtrancl b)
          then show ?thesis using 
              rtranclp_bisect1[OF sem_step_determ ] sorry
  (* need a lemma here but shouldn't be a big deal *)
        qed
      next
        case (Some m1)

        show ?thesis
        proof(cases "s_cont m")
          case Nil
          then show ?thesis sorry
        next
          case (Cons mch mct)
          then show ?thesis 
            using Some Exec' HTE[OF V] guardedD[OF HQ] HCont HP
          apply(simp add: sem_step_def)

        qed

        then show ?thesis using HTE[OF V]
(*
sups_presD[OF Pres]
  *)
          apply(simp add: sem_step_def)

(* one? way to think about this:
  

*)
(*
    proof
      fix m'
      assume Exec : "sem_exec_p \<lparr>sem.s_sem = pcomps' l\<rparr> m m'"

      show "imm_safe \<lparr>sem.s_sem = pcomps' l\<rparr> m'" using Exec unfolding sem_exec_p_def
      proof(cases rule: rtranclp.cases)
      case rtrancl_refl
      then show ?thesis using HCont unfolding imm_safe_def
        apply(cases x; auto)
         apply(simp add: sem_step_p_eq sem_step_def)
         apply(cases "s_cont m"; auto)
         apply(case_tac "pcomps' l x1 m"; auto)
         apply(simp add: sem_step_p_eq sem_step_def)
        done
      next
        case (rtrancl_into_rtrancl b)
        then show ?thesis
          using HTE[OF V] guardedD[OF HQ]
          
          using HP HCont unfolding sem_step_p_eq
      qed
*)
*)
end