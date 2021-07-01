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

definition semprop_gsx ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool)"
  ("|? _ ?|")  
  where
"semprop_gsx gs x m m' =
  (\<exists> n  . gensyn_sem_small_exec_many gs x n m = (m', Ok))"

definition semprop_gsx_halt ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool)"
  ("|! _ !|")  
  where
"semprop_gsx_halt gs x m m' =
  (\<exists> n . gensyn_sem_small_exec_many gs x n m = (m', Ok) \<and>
         gs_getpath gs m' = None)"

(*
definition semprop_gsx_halt ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool)" where
"semprop_gsx gs x m m' =
  (\<exists> n flag . gensyn_sem_small_exec_many gs x n m = (m', flag))"

*)

(* problem: how do we figure out when we are done executing?
   e.g. "gotten to the end of the statement"

   one approach: run until halt, and then express what happens
   with complex terms in terms of hoare logic rules on simpler terms
*)
(*
definition VTSMx ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   ('x gensyn) \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   bool"
  (" |! _ !| !% {!_!} _ {!_!}")  
  where
"VTSMx gs P x Q =
  (\<forall> m m' n . 
    P m \<longrightarrow>
    gensyn_sem_small_exec_many gs x n m = (m', Halt) \<longrightarrow>
    Q m')"

lemma VTSMI :
  assumes
    "\<And> m m' n .
      P m \<Longrightarrow>
      gensyn_sem_small_exec_many gs x n m = (m', Halt) \<Longrightarrow> Q m'"
  shows "|! gs !| !% {!P!} x {!Q!}" using assms
  by(auto simp add: VTSMx_def)

lemma VTSME :
  assumes H : "|! gs !| !% {!P!} x {!Q!}"
  assumes H1 : "P m"
  assumes H2 : "gensyn_sem_small_exec_many gs x n m = (m', Halt)"
  shows "Q m'" using assms
  by(auto simp add: VTSMx_def)
*)


(* lifting Hoare rules from single step into VTSM *)

lemma vtsm_lift_halt :
  assumes H0 : "gs_sem f' = f"
  assumes Hstart : "\<And> st . P st \<Longrightarrow> gs_getpath f' st = Some p"
  assumes Hend : "\<And> st . Q st \<Longrightarrow> gs_getpath f' st = None"
  assumes Hp : "gensyn_get prog p = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  shows "|! f' !| !% {!P!} prog {!Q!}" using assms
  
  apply(cases f'; auto simp add: VTSMx_def VT_def)
  apply(case_tac n; auto split: option.splits)
  apply(drule_tac x = m in spec) apply(auto)
  apply(drule_tac x = "f s m" in spec)
  apply(case_tac nat; auto simp add: semprop2_def split:option.splits)
  done

(* not totally sure this is true though.
   plus even if it is it's probably going to be annoying to reason with *)
lemma vtsm_lift_halt_p :
  assumes H0 : "gs_sem f' = f"
  assumes Hp : "gensyn_get prog p = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  assumes H' : "(!f) % {{(\<lambda> st . gs_getpath f' st = Some p)}} s
                       {{(\<lambda> st . gs_getpath f' st = None)}}"
  shows "|! f' !| !% {! (\<lambda> st . P st \<and> gs_getpath f' st = Some p) !} prog 
                     {! (\<lambda> st . Q st \<and> gs_getpath f' st = None) !}" 
proof-
  have Combine :
    "(! gs_sem f') % {{\<lambda>st. P st \<and> gs_getpath f' st = Some p}} s {{\<lambda>st. Q st \<and> gs_getpath f' st = None}}"
    using Hoare.VandI[OF H H'] unfolding H0
    by auto
  show "|! f' !| !% {!\<lambda>st. P st \<and>
                         gs_getpath f' st =
                         Some p!} prog {!\<lambda>st. Q st \<and> gs_getpath f' st = None!}"

  using vtsm_lift_halt[OF H0, of "(\<lambda> st . P st \<and> gs_getpath f' st = Some p)" p
                                 "(\<lambda> st . Q st \<and> gs_getpath f' st = None)",
                       OF _ _ Hp]
  using Combine unfolding H0
  by(auto)
qed

lemma vtsm_lift_cont :
  assumes H0 : "gs_sem f' = f"
  assumes Hstart : "\<And> st . P st \<Longrightarrow> gs_getpath f' st = Some p" 
(*  assumes Hend : "\<And> st . Q st \<Longrightarrow> gs_getpath f' st = Some p'" *)
  assumes Hp : "gensyn_get prog p = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  assumes H' : "|! f' !| !% {!Q!} prog {!Q'!}"
  shows "|! f' !| !% {!P!} prog {!Q'!}" using assms
  apply(cases f'; auto simp add: VTSMx_def VT_def)
  apply(drule_tac x = m in spec) apply(auto)
  apply(case_tac n; auto)
  apply(drule_tac x = "f s m" in spec) apply(auto simp add: semprop2_def)
  done

lemma vtsm_lift_cont_p :
  assumes H0 : "gs_sem f' = f"
  assumes Hp : "gensyn_get prog p = Some (G s l)"
  assumes H : "(!f) % {{P}} s {{Q}}"
  assumes Hrec : "|! f' !| !% {!Q!} prog {!Q'!}"
  shows "|! f' !| !% {!(\<lambda> st . P st \<and> gs_getpath f' st = Some p)!} prog {!Q'!}" using assms
proof-

  have H' : "(!f) % {{(\<lambda>  st . gs_getpath f' st = Some p)}} s {{(\<lambda> st.  True)}}"
    unfolding VT_def by auto

  have Combine:
    "(! gs_sem f') % {{\<lambda>st. P st \<and> gs_getpath f' st = Some p}} s {{\<lambda>st. Q st \<and> (\<lambda> x . True) st}}"
    using Hoare.VandI[OF H H'] unfolding H0
    by auto

  show "|! f' !| !% {!\<lambda>st. P st \<and> gs_getpath f' st = Some p!} prog {!Q'!}"
    using vtsm_lift_cont[OF H0, of "(\<lambda> st . P st \<and> gs_getpath f' st = Some p)" p,
                         OF _ Hp, of Q Q']
    using Combine Hrec unfolding H0
    by(auto)
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



*)
lemma vtsm_ctx :
  assumes H1 : "gs_sem f'1 = f"
  assumes H2 : "gs_sem f'2 = f"
  assumes Hp : "gensyn_get prog1 p = Some prog2"
  assumes Exc1' : "|! f'1 !| % {{(\<lambda> st . P st \<and> gs_getpath f'1 st = p}} 
                               prog1
                               {{(\<lambda> st . gs_getpath f'1 st = None)}}"
  assumes Exc2 : "|! f'2 !| % {{(\<lambda> st . P st \<and> gs_getpath f'2 st = Some []}} 
                              prog2
                              {{Q}}"
  assumes Halt1 : "|! f'1 !| % {{(\<lambda> st . P st \<and> gs_getpath f'1 st = p}} 
                              prog1
                              {{(\<lambda> st . gs_getpath f'1 st = None)}}"

  shows Exc1 : "|! f'1 !| % {{(\<lambda> st . P st \<and> gs_getpath f'1 st = p}} 
                              prog1
                              {{Q}}"
 

  (*assumes Hp2 : "gensyn_get x1 p = Some x2"*)
  
  assumes Hstart1 : "\<And> st . P st \<Longrightarrow> gs_getpath f' st = Some p"
  
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