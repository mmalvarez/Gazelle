theory Gensyn_Sem_Small imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"
                                

begin

datatype gensyn_small_error =
  Ok
  | BadPath
  | NoFuel
  | Halted (* this means we executed _past_ the end *)


record ('x, 'mstate) g_semr =
  gsr_rel :: "'x \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  gsr_getpath :: "'mstate \<Rightarrow> childpath \<Rightarrow> bool"
  gsr_getdir :: "'mstate \<Rightarrow> dir \<Rightarrow> bool"

record ('x, 'mstate) g_sem =
  gs_sem :: "'x \<Rightarrow> 'mstate \<Rightarrow> 'mstate"
  gs_getpath :: "'mstate \<Rightarrow> childpath option"
  (*gs_getdir :: "'mstate \<Rightarrow> dir"*)

fun gs_halted :: "('x, 'mstate) g_sem \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gs_halted gs m = (gs_getpath gs m = None)"

(* gs_getflag :: "'mstate \<Rightarrow> gensyn_small_flag" *)

definition gensyn_sem_small ::
  "('x, 'mstate) g_semr \<Rightarrow> 
   'x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gensyn_sem_small gsr syn m m' =
 (\<exists> cp . gsr_getpath gsr m cp \<and>
 (\<exists> x l . gensyn_get syn cp = Some (G x l) \<and>
  gsr_rel gsr x m m'))"

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

fun gensyn_sem_small_exec ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_error)" where
"gensyn_sem_small_exec gs syn m =
 (case gs_getpath gs m of
  None \<Rightarrow> (m, Ok)
  | Some cp \<Rightarrow> 
    (case gensyn_get syn cp of
     None \<Rightarrow> (m, BadPath)
     | Some (G x _) \<Rightarrow> (gs_sem gs x m, Ok)))"

(*
fun gensyn_sem_small_exec_many ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_error)" where
"gensyn_sem_small_exec_many gs syn 0 m =
  (case gs_getpath gs m of
    None \<Rightarrow> (m, Ok)
    | _ \<Rightarrow>  (m, NoFuel))"
| "gensyn_sem_small_exec_many gs syn (Suc n) m =
   (case gs_getpath gs m of
    None \<Rightarrow> (m, Halted)
    | _ \<Rightarrow> (case gensyn_sem_small_exec gs syn m of
            (m', Ok) \<Rightarrow> gensyn_sem_small_exec_many gs syn n m'
            | (m', f) \<Rightarrow> (m', f)))"
*)

(* one approach: just don't keep out of fuel flag. *)
fun gensyn_sem_small_exec_many ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_error)" where
"gensyn_sem_small_exec_many gs syn 0 m =
  (m, Ok)"
| "gensyn_sem_small_exec_many gs syn (Suc n) m =
   (case gs_getpath gs m of
    None \<Rightarrow> (m, Ok)
    | _ \<Rightarrow> (case gensyn_sem_small_exec gs syn m of
            (m', Ok) \<Rightarrow> gensyn_sem_small_exec_many gs syn n m'
            | (m', f) \<Rightarrow> (m', f)))"

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


end