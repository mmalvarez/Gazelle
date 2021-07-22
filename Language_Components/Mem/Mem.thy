theory Mem
  imports "../../Syntax/Gensyn" "../../Syntax/Gensyn_Descend" "../../Mergeable/Mergeable"
        "../../Mergeable/Mergeable_Instances"
        "../../Lifter/Lifter" "../../Lifter/Lifter_Instances"
        "../../Lifter/Auto_Lifter" "../../Lifter/Auto_Lifter_Proofs" 
        "../../Semantics/Semantics" 
        "../Utils"
         
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

fun mem0_sem :: "syn \<Rightarrow> state0 \<Rightarrow> state0" where
"mem0_sem Sskip s = s"
| "mem0_sem (Scopy _ _) (src, dest) = (src, src)"
| "mem0_sem (Slit _ i) (src, dest) = (src, i)"

(* we are using STR '''' as a "dummy" variable
 * when we would need to look up a nonexistent variable name *)
fun mem_key_src :: "syn \<Rightarrow> str" where
"mem_key_src (Slit s _) = (STR '''')"
| "mem_key_src (Scopy s1 s2) = s1"
| "mem_key_src Sskip = (STR '''')"

fun mem_key_dest :: "syn \<Rightarrow> str" where
"mem_key_dest (Slit s _) = s"
| "mem_key_dest (Scopy s1 s2) = s2"
| "mem_key_dest Sskip = (STR '''')"

definition mem_sem :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem = 
  lift_map_s id
    (schem_lift (SP NA NB)
                (SM (SL mem_key_src (SPRI (SO NA)))
                    (SL mem_key_dest (SPRIN 2 (SO NB))))) mem0_sem"

definition mem_sem_l_gen :: "('s \<Rightarrow> syn) \<Rightarrow> (syn, state, 'a) lifting \<Rightarrow> 's \<Rightarrow> ('a :: Mergeable) \<Rightarrow> 'a" where
"mem_sem_l_gen lfts lft =
  lift_map_s lfts
    (schem_lift NA (SINJ lft NA)) mem_sem"


definition test_store where
"test_store = to_oalist
  [ (STR ''a'', Swr (0 :: int))
  , (STR ''b'', Swr 2)
  , (STR ''z'', Swr (-1))]"

value "mem_sem (Scopy (STR ''b'') (STR ''y'')) test_store"
value "mem_sem (Slit (STR ''f'') (4 :: int)) test_store"

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
