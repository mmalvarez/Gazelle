(* Idea : Mem language has
   Read
   Write *)

theory Mem
  imports "../../MergeableTc/MergeableInstances"
          "../../MergeableTc/MergeableAList"
          "../../Lifting/LiftUtils"
          "../../Lifting/LiftInstances"
         
begin

(* Read = replace value in scratch location with one from memory
   Write = replace value in memory with scratch value *)

type_synonym str = "String.literal"

(* standard wrap *)
type_synonym 'a swr =
  "'a md_triv option md_prio"

datatype mem0 = 
  Mzread
  | Mzwrite
  | Mzskip

datatype syn = 
  Sread "str"
  | Swrite "str"
  | Sskip

type_synonym state0 = "(int * int)"

type_synonym state = "int swr * 
                      (String.literal, int swr) oalist"

definition Swr :: "'a \<Rightarrow> 'a swr" where
"Swr a = mdp 0 (Some (mdt a))"

fun mem_trans :: "syn \<Rightarrow> mem0" where
"mem_trans (Sread _) = Mzread"
| "mem_trans (Swrite _) = Mzwrite"
| "mem_trans (Sskip) = Mzskip"

(* do we lift from somethting more trivial? *)
(* what if variable can't be found? no-op? *)
fun mem0_sem :: "syn \<Rightarrow> state0 \<Rightarrow> state0" where
"mem0_sem Sskip s = s"
| "mem0_sem (Swrite _) (reg, store) = (reg, reg)"
| "mem0_sem (Sread _) (reg, store) = (store, store)"

fun mem_keys :: "syn \<Rightarrow> str option" where
"mem_keys (Sread s) = Some s"
| "mem_keys (Swrite s) = Some s"
| "mem_keys Sskip = None"

definition mem_sem :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem = 
  l_map_s id
    (prod_l ((prio_l_inc o option_l o triv_l) id_l)
            (oalist_l mem_keys ((prio_l_inc o option_l  o triv_l) id_l))) mem0_sem"

definition test_lift :: "(syn, state0, state) lifting" where
"test_lift = (prod_l ((prio_l_inc o option_l o triv_l) id_l)
            (oalist_l mem_keys ((prio_l_inc o option_l o triv_l) id_l)))"

definition test_store where
"test_store = to_oalist
  [ (STR ''a'', Swr 0)
  , (STR ''b'', Swr 2)
  , (STR ''z'', Swr (-1))]"

definition test_state where
"test_state = (Swr (3 :: int), test_store)"

value "mem_sem (Sread (STR ''b'')) test_state"

value "mem_sem (Swrite (STR ''b'')) test_state"
declare [[ML_exception_trace]]
value [code] "mem_sem (Swrite (STR ''f'')) test_state"

term "LOut ((prod_l ((prio_l_inc o option_l o triv_l) id_l)
            (oalist_l mem_keys ((prio_l_inc o option_dfl_l (0) o triv_l) id_l))))
(Swrite (STR ''f''))"



value "LOut ((prod_l ((prio_l_inc o option_l o triv_l) id_l)
            (oalist_l mem_keys ((prio_l_inc o option_dfl_l (2 :: int) o triv_l) id_l))))
(Swrite (STR ''f'')) test_state"

value "mem0_sem (Swrite (STR ''f'')) (0, 2)"

value "LUpd test_lift (Swrite (STR ''f'')) (0, 2) test_state"

value "LOut test_lift (Swrite (STR ''f'')) (LBase test_lift (Swrite (STR ''f'')))"


definition test where "test = mem_sem (Sskip) test_state"
definition test2 where "test2 = mem_sem (Swrite (STR ''f'')) test_state"



end