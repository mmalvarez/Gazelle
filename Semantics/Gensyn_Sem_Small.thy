theory Gensyn_Sem_Small imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
"../Relpath"
                                

begin

datatype gensyn_small_result =
  Ok childpath
  | BadPath
  | NoFuel
  | Halted (* this means we executed _past_ the end *)

(* new approach to childpath: descend to an arbitrary descendent,
   or "bubble up" to immediate parent
*)
datatype gs_path =
  GcDown "childpath"
  | GcUp

(*
record ('x, 'mstate) g_semr =
  gsr_rel :: "'x \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  gsr_getpath :: "'mstate \<Rightarrow> gs_path \<Rightarrow> bool"
*)
record ('x, 'mstate) g_sem =
  gs_sem :: "'x \<Rightarrow> 'mstate \<Rightarrow> 'mstate"
  gs_getpath :: "'mstate \<Rightarrow> rel_update"
(*  gs_getdir :: "'mstate \<Rightarrow> dir" *)

(*
fun gs_halted :: "('x, 'mstate) g_sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gs_halted gs m = (gs_getpath gs m = None)"
*)

(* gs_getflag :: "'mstate \<Rightarrow> gensyn_small_flag" *)
(*
  new change: childpath (root \<rightarrow> this node) as an argument (?)
  keep the prefix separate
  how do we determine when we split out?
*)
(*
definition gensyn_sem_small ::
  "('x, 'mstate) g_semr \<Rightarrow> childpath \<Rightarrow>
   'x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gensyn_sem_small gsr path syn m m' =
 (\<exists> cp . gsr_getpath gsr m cp \<and>
 (\<exists> x l . gensyn_get syn cp = Some (G x l) \<and>
  gsr_rel gsr x m m'))"
*)
(*
inductive gensyn_sem_small_many ::
  "('x, 'mstate) g_semr \<Rightarrow> 
   'x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gensyn_sem_small gsr syn m m' \<Longrightarrow>
 gensyn_sem_small_many gsr syn m m'"
| "gensyn_sem_small gsr syn m m' \<Longrightarrow>
   gensyn_sem_small_many gsr syn m' m'' \<Longrightarrow>
   gensyn_sem_small_many gsr syn m m''"

definition gensyn_sem_small_many_halt ::
  "('x, 'mstate) g_semr \<Rightarrow> 
   'x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gensyn_sem_small_many_halt gsr syn m m' =
 (gensyn_sem_small_many gsr syn m m' \<and>
 (\<forall> cp . \<not> gsr_getpath gsr m' cp))"
*)

fun droplast :: "'a list \<Rightarrow> 'a list option" where
"droplast [] = None"
| "droplast [h] = Some []"
| "droplast (h1#h2#t) =
   (case droplast (h2#t) of
    None \<Rightarrow> None
    | Some p' \<Rightarrow> Some (h1#p'))"
    

fun gs_pathD :: "gs_path \<Rightarrow> childpath \<Rightarrow> childpath option" where
"gs_pathD (GcDown p') p = Some (p @ p')"
| "gs_pathD (GcUp) p = droplast p"

(* 
  idea: cp never changes in recursive calls.
  only relative path does.

  and the relative path is only allowed to change by relpath-updates.

  this is supposed to make it so that when we are inside a subtree, 
  we cannot tell the difference from being at the root.

  however, it seems like in practice maybe sometimes cp will change?
  the goal was to generalize over this extra cp argument in order to
  be able to avoid the issues i was having before with hoare triples.
  however, i am worried that now the triples will be provable but not
  useful, since we wouldn't be able to find situations where the cp's would
  be aligned in such a way where they would apply.

  Big question: how and when does the root childpath need to change?
  How do we keep this from becoming a problem?

  
*)
fun gensyn_sem_small_exec ::
  "('x, 'mstate) g_sem \<Rightarrow>
   childpath \<Rightarrow>
   'x gensyn \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_result)" where
"gensyn_sem_small_exec gs cp syn m =
  (case gensyn_get syn cp  of
      None \<Rightarrow> (m, BadPath)
      | Some (G x _) \<Rightarrow> 
      ( let m' = gs_sem gs x m in
        (case childpath_update cp (gs_getpath gs m') of
          None \<Rightarrow> (m', Halted)
          | Some cp' \<Rightarrow> (gs_sem gs x m, Ok cp'))))"

(*
(case gs_pathD (gs_getpath gs m') cp of
         None \<Rightarrow> (m', Ok)
         | Some cp'
*)
(*
  new idea. have local rather than absolute paths
  so when we get, we get based on a prefix (prefix @ gs_getpath gs m)

  keep prefix in a separate part of state
*)

(* gs_pathD (gs_getpath gs m) cp *)
(* idea here: cp + state \<Rightarrow> path that we should be executing this one at.
*)

(* new approach - 
   gs_pathD (cp, m') = where to find next instruction
   cp = where i am executing this instruction
   
*)

fun gensyn_sem_small_exec_many ::
  "('x, 'mstate) g_sem \<Rightarrow>
   childpath \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_result)" where
"gensyn_sem_small_exec_many gs cp syn 0 m =
  (m, Ok cp)"
| "gensyn_sem_small_exec_many gs cp syn (Suc n) m =
  (case gensyn_sem_small_exec gs cp syn m of
      (m', Ok cp') \<Rightarrow> gensyn_sem_small_exec_many gs cp' syn n m'
      | (m', x) \<Rightarrow> (m', x))"

(*
fun gensyn_sem_small_exec_many ::
  "('x, 'mstate) g_sem \<Rightarrow>
   childpath \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_error)" where
"gensyn_sem_small_exec_many gs cp syn 0 m =
  (m, Ok)"
| "gensyn_sem_small_exec_many gs cp syn (Suc n) m =
  (case gs_pathD (gs_getpath gs m) cp of
   None \<Rightarrow> (m, Ok)
   | Some _ \<Rightarrow>
    (case gensyn_sem_small_exec gs cp syn m of
      (m', Ok) \<Rightarrow>
        (case gs_pathD (gs_getpath gs m') cp of
         None \<Rightarrow> (m', Ok)
         | Some cp' \<Rightarrow> gensyn_sem_small_exec_many gs cp' syn n m')
      | (m', x) \<Rightarrow> (m', x)))"
*)

(*
| "gensyn_sem_small_exec_many gs syn (Suc n) m =
   (case gs_getpath gs m of
    None \<Rightarrow> (m, Ok)
    | _ \<Rightarrow> (case gensyn_sem_small_exec gs syn m of
            (m', Ok) \<Rightarrow> gensyn_sem_small_exec_many gs syn n m'
            | (m', f) \<Rightarrow> (m', f)))"
*)
(*
fun gensyn_sem_small_exec_many ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_flag)" where
"gensyn_sem_small_exec_many gs syn 0 m =
  (m, NoFuel)"
| "gensyn_sem_small_exec_many gs syn (Suc n) m =
   (case gensyn_sem_small_exec gs syn m of
    (m', Exec) \<Rightarrow> gensyn_sem_small_exec_many gs syn n m'
    | (m', f) \<Rightarrow> (m', f))"
*)

(* TODO: the ordering of checks is weird here and will lead to weird traces. *)
(*
fun gensyn_sem_small_exec_trace' ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate list \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate list * gensyn_small_error)" where
"gensyn_sem_small_exec_trace' gs syn 0 l m =
  (m#l, NoFuel)"
| "gensyn_sem_small_exec_trace' gs syn (Suc n) l m =
   (case gensyn_sem_small_exec gs syn m of
    (m', Ok) \<Rightarrow> 
      (case gs_getpath gs m of
        None \<Rightarrow> (m'#m#l, Ok)
        | _ \<Rightarrow> gensyn_sem_small_exec_trace' gs syn n (m#l) m')
    | (m', f) \<Rightarrow> (m'#m#l, f))"

fun gensyn_sem_small_exec_trace ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate list * gensyn_small_error)" where
"gensyn_sem_small_exec_trace gs syn n m =
 (case gensyn_sem_small_exec_trace' gs syn n [] m of
  (l, f) \<Rightarrow> (rev l, f))"
*)


end