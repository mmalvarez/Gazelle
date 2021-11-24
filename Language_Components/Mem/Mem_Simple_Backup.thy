theory Mem_Simple
  imports "../../Syntax/Gensyn" "../../Syntax/Gensyn_Descend" "../../Mergeable/Mergeable"
        "../../Mergeable/Mergeable_Instances"
        "../../Lifter/Lifter" "../../Lifter/Lifter_Instances"
        "../../Lifter/Auto_Lifter" "../../Lifter/Auto_Lifter_Proofs" 
        "../../Semantics/Semantics" 
        "../Utils"
         
begin

(* A simpler version of Mem that avoids the issues that Mem.thy was having
 * with multiple simultaneous accesses to memory. In Mem_Simple,
 * we only do one read or one write at a time, and use control flow (provided elsewhere)
 * if we want to go beyond this. *)

type_synonym str = "String.literal"

(* standard wrap *)
type_synonym 'a swr =
  "'a md_triv option md_prio"

datatype mem0 = 
  Mzread
  | Mzwrite
  | Mzskip

(* 3 "registers" for use with Calc etc. *)
datatype reg_id =
  Reg_a
  | Reg_b
  | Reg_c
  | Reg_flag

datatype syn = 
  Sread "str" "reg_id"
  | Swrite "str" "reg_id"
  | Sskip

(*type_synonym state0 = "(int * int)"*)

(* type_synonym state0 = "int * (String.literal, int) oalist" *)
(*
fun mem0_sem :: "mem0 \<Rightarrow> state0 \<Rightarrow> state0" where
"mem0_sem Mzread (reg, mem) = (mem, mem)"
| "mem0_sem Mzwrite (reg, mem) = (reg, reg)"
| "mem0_sem Mzskip x = x"
*)
definition Swr :: "'a \<Rightarrow> 'a swr" where
"Swr a = mdp 0 (Some (mdt a))"

(*
fun mem_trans :: "syn \<Rightarrow> mem0" where
"mem_trans (Sread i) = Mzread"
| "mem_trans (Swrite i) = Mzwrite"
| "mem_trans (Sskip) = Mzskip"

(* we are using STR '''' as a "dummy" variable
 * when we would need to look up a nonexistent variable name *)
fun mem_key :: "syn \<Rightarrow> str" where
"mem_key (Sread s) = s"
| "mem_key (Swrite s) = s"
| "mem_key Sskip = (STR '''')"
*)

type_synonym state0 = "int * int * int * int * (String.literal, int) oalist"

type_synonym ('s, 'x) state' = "('s, (bool md_triv option md_prio * int md_triv option md_prio * 'x)) control"
(* tuple layout:
 * (continuation list, error flag, 
 *  bool condition flag, result register (c), register a, register b, mem, other stuff) *)
type_synonym ('s, 'x) state = "('s, int swr * int swr * int swr * int swr * (String.literal, int swr) oalist * 'x) control"

term "(schem_lift (SP NA NB)
                (SP (SPRI (SO NA))
                    (SL id (SPRI (SO NB)))))"

term "(schem_lift (SP NA NB)
                (SP (SPRI (SO NA))
                    (SL mem_key (SPRI (SO NB)))))"

(*
definition mem_sem :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem = 
  lift_map_s id
    (schem_lift (SP NA NB)
                (SP (SPRI (SO NA))
                    (SL mem_key (SPRI (SO NB))))) mem0_sem"

definition mem_sem_l_gen :: "('s \<Rightarrow> syn) \<Rightarrow> (syn, state, 'a) lifting \<Rightarrow> 's \<Rightarrow> ('a :: Mergeable) \<Rightarrow> 'a" where
"mem_sem_l_gen lfts lft =
  lift_map_s lfts
    (schem_lift NA (SINJ lft NA)) mem_sem"
*)

(* "bootleg" version of mem_sem.
 * we are not making full use of the lifting infrastructure here.
 * getting this to work is a TODO
 *)

term "undefined :: ('s, 'x) state"

(* TODO: priority calculations here are all wrong.
 * need to increment priority of the destination of the data. not the source. *)
fun mem_sem :: "syn \<Rightarrow> ('s, 'x) state \<Rightarrow> ('s, 'x) state" where
"mem_sem (Sread s r) (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz) =
  (case (get mem s) of
   Some (mdp _ (Some (mdt v))) \<Rightarrow> 
    (case r of
      Reg_a \<Rightarrow> 
        (case reg_a of
          (mdp p1 (Some (mdt _))) \<Rightarrow> (x0, x1, reg_flag, reg_c, (mdp (1 + p1) (Some (mdt v)), reg_b, mem, xz))
          | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, (mdp 0(Some (mdt v)), reg_b, mem, xz)))
      | Reg_b \<Rightarrow> 
        (case reg_b of
          (mdp p1 (Some (mdt _))) \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, (mdp (1 + p1) (Some (mdt v)), mem, xz))
          | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, (mdp 0 (Some (mdt v)), mem, xz)))
      | Reg_c \<Rightarrow> 
        (case reg_c of
          (mdp p1 (Some (mdt _))) \<Rightarrow> (x0, x1, reg_flag, (mdp (1 + p1) (Some (mdt v))), reg_a, reg_b, mem, xz)
          | _ \<Rightarrow> (x0, x1, reg_flag, (mdp 0 (Some (mdt v))), reg_a, reg_b, mem, xz))
      | Reg_flag \<Rightarrow> 
        (case reg_flag of
          (mdp p1 (Some (mdt _))) \<Rightarrow> (x0, x1, (mdp (1 + p1) (Some (mdt v))), reg_c, reg_a, reg_b, mem, xz)
          | _ \<Rightarrow> (x0, x1, (mdp 0 (Some (mdt v))), reg_c, reg_a, reg_b, mem, xz)))
   | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz))"

| "mem_sem (Swrite s r) (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz)  =
   (let p1 =
    (case get mem s of
      Some (mdp p1 _) \<Rightarrow> p1
      | _ \<Rightarrow> 0) in
   (case r of
    Reg_a \<Rightarrow> 
      (case reg_a of
        (mdp _ (Some (mdt x))) \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, 
                                    update s (mdp (1 + p1) (Some (mdt x))) mem, xz)
        | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz))
    | Reg_b \<Rightarrow>
      (case reg_b of
        (mdp _ (Some (mdt x))) \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, 
                                    update s (mdp (1 + p1) (Some (mdt x))) mem, xz)
        | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz))

    | Reg_c \<Rightarrow>
      (case reg_c of
        (mdp _ (Some (mdt x))) \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, 
                                    update s (mdp (1 + p1) (Some (mdt x))) mem, xz)
        | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz))

    | Reg_flag \<Rightarrow>
      (case reg_flag of
        (mdp _ (Some (mdt x))) \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, 
                                    update s (mdp (1 + p1) (Some (mdt x))) mem, xz)
        | _ \<Rightarrow> (x0, x1, reg_flag, reg_c, reg_a, reg_b, mem, xz))))"
| "mem_sem _ st = st"

(*
definition test_store where
"test_store = to_oalist
  [ (STR ''a'', Swr (0 :: int))
  , (STR ''b'', Swr 2)
  , (STR ''z'', Swr (-1))]"

definition test_state where
"test_state =
  (mdp 0 (Some (mdt 9))
  , (mdp 0 (Some (mdt 5)))
  , (mdp 0 (Some (mdt 0)))
  , (mdp 0 (Some (mdt 0)))
  , test_store)"

value "mem_sem (Sread (STR ''b'' ) Reg_a) test_state"
value "mem_sem (Swrite (STR ''f'') Reg_b) test_state"
*)
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
