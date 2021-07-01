theory Multistep_Hoare imports Hoare "../Semantics/Gensyn_Sem_Small"
begin

(* Idea here:
  - _partial_ correctness
  - so we need some kind of way to talk about case where we run out of gas (or don't terminate, etc)
 *)

(*
 * should we be explicit about how we pull out the gensyn_skel? 
 * this would (e.g. if it is a lifting) enable explicitly updating
 * however, we can probably handle this at the predicate level
*)

(*
definition semprop_gsx ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool)"
  ("|? _ ?|")  
  where
"semprop_gsx gs x m m' =
  (\<exists> n flag . gensyn_sem_small_exec_many gs x n m = (m', flag))"

*)

definition GVT ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   'x gensyn \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   bool"
  ("|? _ ?| %% {? _ ?} _ {? _ ?}")
  where
"GVT gs P prog Q =
  (\<forall> st .
    P st \<longrightarrow>
    (\<exists> n st' . gensyn_sem_small_exec_many gs prog n st = (st', Ok) \<and>
       Q st'))"

lemma GVTI [intro] :
  assumes "(\<And> st . P st \<Longrightarrow> 
              (\<exists> n st' . gensyn_sem_small_exec_many gs prog n st = (st', Ok) \<and> Q st'))"
  shows "|? gs ?| %% {?P?} prog {?Q?}" using assms
  unfolding GVT_def by auto

lemma GVTE [elim]:
  assumes "|? gs ?| %% {?P?} prog {?Q?}"
  assumes "P st"
  obtains n st' where 
    "gensyn_sem_small_exec_many gs prog n st = (st', Ok)"
    "Q st'"
  using assms
  unfolding GVT_def by auto

(* lifting Hoare rules from single step into VTSM *)
lemma vtsm_lift_step :
  assumes H0 : "gs_sem f' = f"
  assumes Hstart : "\<And> st . P st \<Longrightarrow> gs_getpath f' st = Some p"
  assumes Hpath : "gensyn_get prog p = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  shows "|? f' ?| %% {?P?} prog {?Q?}" 
proof
  fix st
  assume HP : "P st"
  
  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have Start : "gs_getpath f' st = Some p"
    using Hstart[OF HP] by auto

  have Conc' :  "gensyn_sem_small_exec_many f' prog 1 st = (f s st, Ok)"
    using Start Hpath H0
    by(auto split:option.splits)

  show "\<exists>n st'.
         gensyn_sem_small_exec_many f' prog n st = (st', Ok) \<and> Q st'"  
    using Conc' Qf by blast
qed


lemma vtsm_lift_cont :
  assumes H0 : "gs_sem f' = f"
  assumes Hstart : "\<And> st . P st \<Longrightarrow> gs_getpath f' st = Some p" 
  assumes Hp : "gensyn_get prog p = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  assumes H' : "|? f' ?| %% {?Q?} prog {?Q'?}"
  shows "|? f' ?| %% {?P?} prog {?Q'?}"
proof(rule GVTI)

  fix st
  assume HP : "P st"

(*
  obtain getpath where H0' : "f' = \<lparr> gs_sem = f, gs_getpath = getpath \<rparr>" using H0
    by(cases f'; auto)
*)
  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have Start : "gs_getpath f' st = Some p"
    using Hstart[OF HP] by auto

  obtain st' n where
    Exc : "gensyn_sem_small_exec_many f' prog n (f s st) = (st', Ok)" and
    Q' : "Q' st'"
    using GVTE[OF H' Qf] by auto

  have Conc' : "gensyn_sem_small_exec_many f' prog (n+1) st = (st', Ok)"
    using Exc Start H0 Hp
    by(auto split: option.splits)

  show "\<exists>n st'.
           gensyn_sem_small_exec_many f' prog n st = (st', Ok) \<and> Q' st'"
    using Conc' Q' by blast
qed



(* i think now we need more rules to deal with context.
   for instance, describing partial executions (?)
*)

(*we need a way to relate sub-trees to entire trees.
  this means we probably need some kind of actual lifting for the child-path

*)

(* we need a way to constrain P and Q's ability to talk about the path
   substitution?
   have path as another parameter?
   maybe we can get away with just AND-ing
*)

(* sub-prog *)

(* idea: sub program at path p1 in prog1
   same sub program at path p2 in prog2

   {{P \<and> path = p1}} prog1 {{Q \<and> halt}}
   {{P \<and> path = p2}} prog2 {{Q \<and> halt}}
   
*)

(*

we also need a non-halting version; what would that look like?
(or - halt in small program but not big)

this only works if the small program halts from reaching top
can we distinguish that case?

do we need Up/Down?

*)

(*
  idea: sub-program has halted but big program has not

  small prog
    steps from path p to None w/ success
  big prog
    steps from path (pref @ p) to Some p' w/ success

  (idea: we need to know that p is the last path (?))
*)

(*
  do we need direction?
  idea
  - start w/ (p, Down)
  - sub program goes from ([], Down) to ([], Up)
  - end w/ (p, Up)
*)

(*
  halt vs regular.

  - halt implies regular and (conclusion implies halt?)
  - regular and (conclusion implies halted) implies halt
*)

lemma gsxm_steps_steps :
  assumes H1 : "gensyn_sem_small_exec_many f' prog n1 st = (st1, Ok)"
  assumes H2 : "gensyn_sem_small_exec_many f' prog n2 st1 = (st2, f2)"
  shows "gensyn_sem_small_exec_many f' prog (n1 + n2) st = (st2, f2)" using assms
proof(induction n1 arbitrary: st st1 st2 f2 n2)
  case 0
  then show ?case by auto
next
  case (Suc n1)
  show ?case 
  proof(cases "gs_getpath f' st")
    case None
    then show ?thesis using Suc.prems by(cases n2; auto)
  next
    case (Some p)
    show ?thesis
    proof(cases "gensyn_get prog p")
      case None' : None
      then show ?thesis using Suc.prems Some by(auto)
    next
      case Some' : (Some prog')

      obtain x l where Prog' : "prog' = G x l" by(cases prog'; auto)

      have GS1 : "gensyn_sem_small_exec_many f' prog n1 (gs_sem f' x st) = (st1, Ok)"
        using Suc.prems Some Some' Prog'
        by(auto)

      show ?thesis using Suc.IH[OF GS1] Suc.prems Some Some' Prog'
        by(auto)
    qed
  qed
qed

lemma vtsm_seq :
  assumes H1 : "|? f' ?| %% {?P?} prog {?Q?}"
  assumes H2 : "|? f' ?| %% {?Q?} prog {?Q'?}"
  shows "|? f' ?| %% {?P?} prog {?Q'?}"
proof(rule GVTI)
  fix st
  assume HP : "P st"

  obtain n1 st1 where
    Ex1 : "gensyn_sem_small_exec_many f' prog n1 st = (st1, Ok)" and
    Q1 : "Q st1"
    using GVTE[OF H1 HP] by auto

  obtain n2 st2 where
    Ex2 : "gensyn_sem_small_exec_many f' prog n2 st1 = (st2, Ok)" and
    Q'2 : "Q' st2" using GVTE[OF H2 Q1] by auto

  have Conc' : "gensyn_sem_small_exec_many f' prog (n1 + n2) st = (st2, Ok)"
    using gsxm_steps_steps[OF Ex1 Ex2] by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' prog n st = (st', Ok) \<and> Q' st'"
    using Q'2 Conc' by blast
qed

(*
  next, we need to decide how we want to represent the path constraints
  probably "implies" is best.
*)

abbreviation GVT_halt ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   'x gensyn \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   bool"
  ("|! _ !| %% {! _ !} _ {! _ !}")
  where
"GVT_halt gs P prog Q \<equiv>
  ( |? gs ?| %% {? P ?} prog {? (\<lambda> st . Q st \<and>  gs_getpath gs st = None) ?})"


(* should we constrain P? 
   "there is a satisfying assignment for any path"?
*)

(* another option is just to use liftings here.
   the problem with that is that these liftings tend to modify
   other things *)


(*
lemma vtsm_ctx :
  assumes H0 : "gs_sem f' = f"
  assumes Hp : "gensyn_get prog1 p = Some prog2"

ok, we do need to (?) distinguish a "halt because we ran out of program" state
*)

definition path_shift ::
  "('x, 'mstate) g_sem \<Rightarrow>
   (childpath \<Rightarrow> childpath) \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   bool" where
"path_shift f cpt P P' =
  (\<forall> st p . P st \<longrightarrow>
            gs_getpath f st = Some p \<longrightarrow>
            (\<exists> st'. P' st' \<and> gs_getpath f st' = Some (cpt p)))"

lemma path_shiftE [elim] :
  assumes H0 : "path_shift f cpt P P'"
  assumes HP : "P st"
  assumes Hpath : "gs_getpath f st = Some p"
  obtains st' where
    "P' st'" "gs_getpath f st' = Some (cpt p)"
  using assms unfolding path_shift_def by auto
          

lemma vtsm_sub :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"

  assumes HPP' :
    "\<And> st psuf . P st \<Longrightarrow> gs_getpath f' st = Some (ppre @ psuf) \<Longrightarrow> P' st"

  assumes Exc : "|? f' ?| %% {? P' ?}
                             prog2
                             {? Q' ?}"
  
  shows "|? f' ?| %% {? (\<lambda> st . P st \<and> gs_getpath f' st = Some (ppre@p))?}
                     prog1
                     {? (\<lambda> st . Q st \<and> gs_getpath f' st = Some (ppre@p'))?}"
proof
  fix st1
  assume Hin : "P st1 \<and> gs_getpath f' st1 = Some (ppre @ p)"
  hence Hin1 : "P st1" and Hin2 : "gs_getpath f' st1 = Some (ppre @ p)"
    by auto

  (* hmmmmmm.... *)

  have HP' : "P' st1" using HPP'[OF Hin1 Hin2] by auto

  obtain n1 st'1 where 
    Ex2 : "gensyn_sem_small_exec_many f' prog2 n1 st'1 = (st', Ok)" and
    Post2 :

  show "\<exists>n st'. gensyn_sem_small_exec_many f' prog1 n st1 = (st', Ok) \<and>
                Q st' \<and> gs_getpath f' st' = Some (ppre @ p')"
    using GVTE[OF Exc HP']

lemma vtsm_sub :
  assumes Hp : "gensyn_get prog1 ppre = Some prog2"
  assumes Exc : "|? f' ?| %% {? (\<lambda> st . P st \<and> gs_getpath f' st = Some p) ?}
                             prog2
                             {? (\<lambda> st . Q st \<and> gs_getpath f' st = Some p') ?}"
  shows "|? f' ?| %% {? (\<lambda> st . P st \<and> gs_getpath f' st = Some (ppre@p))?}
                     prog1
                     {? (\<lambda> st . Q st \<and> gs_getpath f' st = Some (ppre@p'))?}"
proof
  fix st1
  assume Hin : "P st1 \<and> gs_getpath f' st1 = Some (ppre @ p)"
  hence Hin1 : "P st1" and Hin2 : "gs_getpath f' st1 = Some (ppre @ p)"
    by auto

  obtain st2 where "P st2 \<and> gs_getpath f' st2 = Some p"

  obtain n st' where Exc' :"gensyn_sem_small_exec_many f' prog2 n st = (st', Ok)" and
                     Q' : "Q st'" and
                     Path' : "gs_getpath f' st' = Some p'"
    using GVTE[OF Exc]


  show "\<exists>n st'. gensyn_sem_small_exec_many f' prog1 n st = (st', Ok) \<and>
                Q st' \<and> gs_getpath f' st' = Some (ppre @ p')"


      using 
    Exc' : 

(*
  assumes Exc1' : "|? f'1 ?| % {{(\<lambda> st . P st \<and> gs_getpath f'1 st = p)}} 
                               prog1
                               {{(\<lambda> st . gs_getpath f'1 st = None)}}"
  assumes Exc2 : "|! f'2 !| % {{(\<lambda> st . P st \<and> gs_getpath f'2 st = Some [])}} 
                              prog2
                              {{Q}}"
  assumes Halt1 : "|! f'1 !| % {{(\<lambda> st . P st \<and> gs_getpath f'1 st = p)}} 
                              prog1
                              {{(\<lambda> st . gs_getpath f'1 st = None)}}"
  shows Exc1 : "|! f'1 !| % {{(\<lambda> st . P st \<and> gs_getpath f'1 st = p)}} 
                              prog1
                            {{Q}}"
*)

  (*assumes Hp2 : "gensyn_get x1 p = Some x2"*)
    
(* then we need a non-halting version of this *)

(* OK, so new plan.
- start with seq
- relate behavior of sequence to individual ones using Hoare rules
*)

(*
 * mstate \<Rightarrow> childpath? just childpath?
 * mstate * unit gensyn * childpath list ?
 *)
(*
definition gVTS0 ::
  "('x, 'mstate, 'xr) x_sem \<Rightarrow> 
   ('mstate \<Rightarrow> childpath) \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow> 
   'x gensyn \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow> 
   bool"
  (" |! _ @ _ !| !% {!_!} _ {!_!}")
  where
"gVTS0 sem getpath P syn Q =
  (\<forall> st1 st2 n .
    P st1 \<longrightarrow>
    gensyn_sem_exec (sem) syn (getpath st1) st1 n = Some st2 \<longrightarrow>
    Q st2)
  "
*)
(*
lemma VTS_gVTS :
  assumes H : "sem % {{P}} x {{Q}}"
  shows ""
*)

(* OK - my worry here is that when we merge states, we may not
   be consistently getting the same thing out. *)

(* one way to deal with this is to use the x_sem' structure (?)
but it seems like maybe we are "throwing away" some information
by using xsem operator, before we can use it to determine
childpath... *)

(*
multiple challenges here:
1. lifting a single command
2. lifting multiple commands
- this could be interesting as, again, we are getting into the precise
relationship between the small and big representation w/r/t child path
*)

(* necessary theorems (sketch):
1. for a single instruction Hoare rule (assuming already lifted):
in
*)

(*
  can we phrase gVTS0 as VT?
*)

end