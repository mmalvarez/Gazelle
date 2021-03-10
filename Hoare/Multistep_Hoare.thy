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

(* will concrete childpaths be sufficient here? *)
definition GVT ::
  "('x, 'mstate) g_sem \<Rightarrow>
  childpath \<Rightarrow>
   (('mstate) \<Rightarrow> bool) \<Rightarrow> 
   'x gensyn \<Rightarrow> 
   gensyn_small_result \<Rightarrow>
   (('mstate) \<Rightarrow> bool) \<Rightarrow>
   bool"
  ("|? _ ?| % {? _, _ ?} _ {? _, _ ?}")
  where
"GVT gs cp1 P prog res Q =
  (\<forall> st .
    P (st) \<longrightarrow>
    (\<exists> n st' . gensyn_sem_small_exec_many gs cp1 prog n st = (st', res) \<and>
       Q (st')))"

lemma GVTI [intro] :
  assumes "(\<And> st . P st  \<Longrightarrow> 
              (\<exists> n st' . gensyn_sem_small_exec_many gs cp prog n st = (st', res) \<and> Q (st')))"
  shows "|? gs ?| % {?cp, P?} prog {?res, Q?}" using assms
  unfolding GVT_def 
  by(auto)

lemma GVTE [elim]:
  assumes "|? gs ?| % {?cp, P?} prog {?res, Q?}"
  assumes "P (st)"
  obtains n st' where 
    "gensyn_sem_small_exec_many gs cp prog n st = (st', res)"
    "Q (st')"
  using assms
  unfolding GVT_def 
  by blast

(* lifting Hoare rules from single step into VTSM *)
(* TODO: make this more general now that childpaths aren't concrete. *)
lemma vtsm_lift_step_cont :
  assumes H0 : "gs_sem f' = f"
  assumes Hend : "\<And> st . Q st \<Longrightarrow> childpath_update cp (gs_getpath f' st) = Some cp'"
  assumes Hpath : "gensyn_get prog cp = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  shows "|? f' ?| % {?cp,P?} prog {? Ok cp',Q?}"
proof
  fix st
  assume HP : "P st"
  
  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have End : "childpath_update cp (gs_getpath f' (f s st)) = Some cp'"
    using Hend[OF Qf] by auto

  have Conc' :  "gensyn_sem_small_exec_many f' cp prog 1 st = (f s st, Ok cp')"
    using H0 Hpath End by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' cp prog n st = (st', Ok cp') \<and> Q st'"  
    using Conc' Qf by blast
qed

lemma vtsm_step_halt :
  assumes H0 : "gs_sem f' = f"
  assumes Hend : "\<And> st . Q st \<Longrightarrow> childpath_update cp (gs_getpath f' st) = None"
  assumes Hpath : "gensyn_get prog cp = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  shows "|? f' ?| % {?cp,P?} prog {? Halted,Q?}"
proof
  fix st
  assume HP : "P st"
  
  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have End : "childpath_update cp (gs_getpath f' (f s st)) = None"
    using Hend[OF Qf] by auto

  have Conc' :  "gensyn_sem_small_exec_many f' cp prog 1 st = (f s st, Halted)"
    using H0 Hpath End by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' cp prog n st = (st', Halted) \<and> Q st'"  
    using Conc' Qf by blast
qed

lemma vtsm_lift_cont :
  assumes H0 : "gs_sem f' = f"
  assumes Hstart : "\<And> st . Q st \<Longrightarrow> childpath_update p1 (gs_getpath f' st) = Some p2" 
  assumes Hp1 : "gensyn_get prog p1 = Some (G s l)"
(*  assumes Hstart' : "\<And> st . Q st \<Longrightarrow> gs_pathD (gs_getpath f' st) p2 = Some p3" *)
  assumes H : "(!f) % {{P}} s {{Q}}"
  assumes H' : "|? f' ?| % {?p2,Q?} prog {?res,Q'?}"
  shows "|? f' ?| % {?p1,P?} prog {?res,Q'?}"
proof(rule GVTI)

  fix st
  assume HP : "P st"

  have Hf : "(!f) s st (f s st)" by(rule semprop2I)

  have Qf : "Q (f s st)" using VTE[OF H HP Hf] by auto

  have Start : "childpath_update p1 (gs_getpath f' (f s st)) = Some p2"
    using Hstart[OF Qf] by auto

  obtain st' n where
    Exc : "gensyn_sem_small_exec_many f' p2 prog n (f s st) = (st', res)" and
    Q' : "Q' st'"
    using GVTE[OF H' Qf] by auto

  have Conc' : "gensyn_sem_small_exec_many f' p1 prog (n+1) st = (st', res)"
    using Exc Start H0 Hp1
    by(auto)

  show "\<exists>n st'.
           gensyn_sem_small_exec_many f' p1 prog n st = (st', res) \<and> Q' st'"
    using Conc' Q' by blast
qed

lemma gsxm_steps_steps :
  assumes H1 : "gensyn_sem_small_exec_many f' cp1 prog n1 st1 = (st2, Ok cp2)"
  assumes H2 : "gensyn_sem_small_exec_many f' cp2 prog n2 st2 = (st3, res)"
  shows "gensyn_sem_small_exec_many f' cp1 prog (n1 + n2) st1 = (st3, res)" using assms
proof(induction n1 arbitrary: st1 st2 cp1 cp2 n2 res)
  case 0
  then show ?case by(auto)
next
  case (Suc n1)
  show ?case 
  proof(cases "gensyn_get prog cp1")
    case None
    then show ?thesis using Suc by(auto)
  next
    case (Some x1)

    obtain x1l x1t where X1 : "x1 = G x1l x1t" by(cases x1; auto)

    show ?thesis 
    proof(cases "childpath_update cp1 (gs_getpath f' (gs_sem f' x1l st1))")
      case None' : None
      then show ?thesis using Suc Some X1 by auto
    next
      case Some' : (Some cp2')

      have Cp2 : "cp2' = cp2'"
        using Suc Some Some' X1 by auto

      then show ?thesis using Suc Some X1 Some' by(auto)
    qed
  qed
qed

lemma vtsm_seq :
  assumes H1 : "|? f' ?| % {?cp1,P1?} prog {?Ok cp2,P2?}"
  assumes H2 : "|? f' ?| % {?cp2,P2?} prog {?res,P3?}"
  shows "|? f' ?| % {?cp1,P1?} prog {?res,P3?}"
proof(rule GVTI)
  fix st1
  assume HP : "P1 st1"

  obtain n1 st2 where
    Ex1 : "gensyn_sem_small_exec_many f' cp1 prog n1 st1 = (st2, Ok cp2)" and
    Q1 : "P2 st2"
    using GVTE[OF H1 HP] by auto

  obtain n2 st3 where
    Ex2 : "gensyn_sem_small_exec_many f' cp2 prog n2 st2 = (st3, res)" and
    Q'2 : "P3 st3" using GVTE[OF H2 Q1] by auto

  have Conc' : "gensyn_sem_small_exec_many f' cp1 prog (n1 + n2) st1 = (st3, res)"
    using gsxm_steps_steps[OF Ex1 Ex2] by auto

  show "\<exists>n st'. gensyn_sem_small_exec_many f' cp1 prog n st1 = (st', res) \<and> P3 st'"
    using Q'2 Conc' by blast
qed

(*
  next, we need to decide how we want to represent the path constraints
  probably "implies" is best.
*)

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