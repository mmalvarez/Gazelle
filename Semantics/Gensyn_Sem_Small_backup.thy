theory Gensyn_Sem_Small imports "../Gensyn" "../Gensyn_Descend" "../Mergeable/Mergeable"

begin

datatype gensyn_small_flag =
  Exec
  | Halt
  | BadPath
  | NoFuel


record ('x, 'mstate) g_semr =
  gsr_rel :: "'x \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool"
  gsr_getpath :: "'mstate \<Rightarrow> childpath \<Rightarrow> bool"

record ('x, 'mstate) g_sem =
  gs_sem :: "'x \<Rightarrow> 'mstate \<Rightarrow> 'mstate"
  gs_getpath :: "'mstate \<Rightarrow> childpath option"

(* gs_getflag :: "'mstate \<Rightarrow> gensyn_small_flag" *)

definition gensyn_sem_small ::
  "('x, 'mstate) g_semr \<Rightarrow> 
   'x gensyn \<Rightarrow> 'mstate \<Rightarrow> 'mstate \<Rightarrow> bool" where
"gensyn_sem_small gsr syn m m' =
 (\<exists> cp . gsr_getpath gsr m cp \<and>
 (\<exists> x l . gensyn_get syn cp = Some (G x l) \<and>
  gsr_rel gsr x m m'))"

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


fun gensyn_sem_small_exec ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate * gensyn_small_flag)" where
"gensyn_sem_small_exec gs syn m =
 (case gs_getpath gs m of
  None \<Rightarrow> (m, Halt)
  | Some cp \<Rightarrow> 
    (case gensyn_get syn cp of
     None \<Rightarrow> (m, BadPath)
     | Some (G x _) \<Rightarrow> (gs_sem gs x m, Exec)))"

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

fun gensyn_sem_small_exec_trace' ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate list \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate list * gensyn_small_flag)" where
"gensyn_sem_small_exec_trace' gs syn 0 l m =
  (m#l, NoFuel)"
| "gensyn_sem_small_exec_trace' gs syn (Suc n) l m =
   (case gensyn_sem_small_exec gs syn m of
    (m', Exec) \<Rightarrow> gensyn_sem_small_exec_trace' gs syn n (m#l) m'
    | (m', f) \<Rightarrow> (m'#m#l, f))"

fun gensyn_sem_small_exec_trace ::
  "('x, 'mstate) g_sem \<Rightarrow>
   'x gensyn \<Rightarrow>
   nat \<Rightarrow>
   'mstate \<Rightarrow>
   ('mstate list * gensyn_small_flag)" where
"gensyn_sem_small_exec_trace gs syn n m =
 (case gensyn_sem_small_exec_trace' gs syn n [] m of
  (l, f) \<Rightarrow> (rev l, f))"


end