theory Mem
  imports "../../Mergeable/MergeableInstances"
          "../../Mergeable/MergeableAList"          
          "../../Lifting/LiftUtils"
          "../../Lifting/LiftInstances"
          "../../Lifting/AutoLift"
         
begin

(* Read = replace value in scratch location with one from memory
   Write = replace value in memory with scratch value *)

type_synonym str = "String.literal"

(* standard wrap *)
type_synonym 'a swr =
  "'a md_triv option md_prio"

datatype mem0 = 
  Mzlit "int"
  | Mzcopy
  | Mzskip

datatype syn = 
  Slit "str" "int"
  | Scopy "str" "str"
  | Sskip

type_synonym state0 = "(int * int)"

type_synonym state = "(String.literal, int swr) oalist"

definition Swr :: "'a \<Rightarrow> 'a swr" where
"Swr a = mdp 0 (Some (mdt a))"

fun mem_trans :: "syn \<Rightarrow> mem0" where
"mem_trans (Slit _ i) = Mzlit i"
| "mem_trans (Scopy _ _) = Mzcopy"
| "mem_trans (Sskip) = Mzskip"

(* do we lift from somethting more trivial? *)
(* what if variable can't be found? no-op? *)
fun mem0_sem :: "syn \<Rightarrow> state0 \<Rightarrow> state0" where
"mem0_sem Sskip s = s"
| "mem0_sem (Scopy _ _) (src, dest) = (src, src)"
| "mem0_sem (Slit _ i) (src, dest) = (src, i)"

fun mem_key_src :: "syn \<Rightarrow> str option" where
"mem_key_src (Slit s _) = None"
| "mem_key_src (Scopy s1 s2) = Some s1"
| "mem_key_src Sskip = None"

fun mem_key_dest :: "syn \<Rightarrow> str option" where
"mem_key_dest (Slit s _) = (Some s)"
| "mem_key_dest (Scopy s1 s2) = (Some s2)"
| "mem_key_dest Sskip = None"

(* where is post happening? *)
(* problem: post happens after data already lost in merge
   we either need to accept that merge_pl is "weird" in that it depends on
   post (hence non-idempotent)
   or else we need another solution *)
(* better (?) solution: have merge happen "at the level of the oalist"
rather than the inner prio contained. So rather than trying to merge the entire list,
we should be trying to merge specific keys/sub-lists *)
definition mem_sem :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem = 
  lift_map_s id
    (schem_lift (SP NA NB)
                (SM (SL mem_key_src (SPRI (SO NA)))
                    (SL mem_key_dest (SPRIN 2 (SO NB))))) mem0_sem"

definition test_store where
"test_store = to_oalist
  [ (STR ''a'', Swr (0 :: int))
  , (STR ''b'', Swr 2)
  , (STR ''z'', Swr (-1))]"

value "mem_sem (Scopy (STR ''b'') (STR ''y'')) test_store"

(*
definition t1 where
"t1 = (oalist_l mem_key_src ((prio_l_keep o option_l  o triv_l) id_l))"

definition t2 where
"t2 = (oalist_l mem_key_dest ((prio_l_inc o option_l  o triv_l) id_l))"

definition s where
"s = (Scopy (STR ''a'') (STR ''b''))"


value "LUpd t1 (Scopy (STR ''a'') (STR ''b'')) (80 :: int) test_store"
value "LUpd t2 (Scopy (STR ''a'') (STR ''b'')) (80 :: int) test_store"

value "LBase t1 s :: (_, int md_triv option md_prio) oalist"



value "mem_sem (Slit (STR ''f'') (4 :: int)) test_store"
value "mem_sem (Slit (STR ''b'') (4 :: int)) test_store"


value "mem_sem (Scopy (STR ''a'') (STR ''f'')) test_store"
value "mem_sem (Scopy (STR ''a'') (STR ''b'')) test_store"
*)




end
