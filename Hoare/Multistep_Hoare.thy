theory Multistep_Hoare imports Hoare "../Semantics/Gensyn_Sem_Small"
begin

(* Idea here:
  - _partial_ correctness
  - so we need some kind of way to talk about case where we run out of gas (or don't terminate, etc)
 *)

(*
definition gsx_hoare :: 
*)

(* should we take an xsem or should we take a thing that we will package in xsem (xsem command)*)
(* xsem also needs some extra packaging.
   xsem is in Lifting/XSem
 *)

(*
 * should we be explicit about how we pull out the gensyn_skel? 
 * basically capture this "fan-out" structure from e.g. MemImp
   * do we need to make sure we have a lifting for the projection?
   * i think just a function is probably fine.
*)

(* this version doesn't know about the how exactly we are pulling out the childpath
*)
(*
 * do we use the VT primitive, or build something else?
 * here is a version that doesn't use VT
*)

(* x_sem' *)

(* forall then exists? exists then forall?
   fuel vs pre state
 *)

(* problem: how do we figure out when we are done executing?
   e.g. "gotten to the end of the statement"

   one approach: run until halt, and then express what happens
   with complex terms in terms of hoare logic rules on simpler terms
*)
definition VTSMx ::
  "('x, 'mstate) g_sem \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   ('x gensyn) \<Rightarrow>
   ('mstate \<Rightarrow> bool) \<Rightarrow>
   bool" where
"VTSMx gs P x Q =
  (\<forall> m m' n . 
    P m \<longrightarrow>
    gensyn_sem_small_exec_many gs x n m = (m', Halt) \<longrightarrow>
    Q m')"


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