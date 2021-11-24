theory Mem_Simple
  imports "../../Lib/Oalist/Oalist" 
        "../../Syntax/Gensyn" "../../Syntax/Gensyn_Descend" "../../Mergeable/Mergeable"
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

type_synonym 'x state1 = "int swr * int swr * int swr * int swr * (String.literal, int) oalist md_triv option md_prio * 'x"

(* tuple layout:
 * (continuation list, error flag, 
 *  bool condition flag, result register (c), register a, register b, mem, other stuff) *)
(* no_control_l *)
type_synonym ('s, 'x) state = "('s, int swr * int swr * int swr * int swr * (String.literal, int) oalist md_triv option md_prio * 'x) control"

(* TODO: we are updating the priority of the entire memory
 * this is inefficient *)
fun mem_prio_mem ::
  "syn \<Rightarrow> nat" where
"mem_prio_mem (Swrite _ _) = 2"
| "mem_prio_mem _ = 1"

fun mem_prio_reg ::
  "reg_id \<Rightarrow> syn \<Rightarrow> nat" where
"mem_prio_reg r (Sread _ r') =
  (if r = r' then 2 else 1)"
| "mem_prio_reg _ _ = 1"
  
definition mem_sem_lifting_inner ::
  "(syn, int, int md_triv option md_prio) lifting"
where
"mem_sem_lifting_inner = (schem_lift NA (SPRC mem_prio_mem (SO NA)))"


(* -, -, int, int, int, int, oalist, whatever*)
(* TODO: change this to no_control_l *)
(*
definition mem_sem_lifting_gen ::
  "(syn, state0, ('s, ('x :: Mergeableb)) state) lifting" where
"mem_sem_lifting_gen =
  schem_lift (SP NA (SP NB (SP NC (SP ND NE))))
    (SP NX (SP NX (SP (SPRC (mem_prio_reg Reg_flag) (SO NA)) 
                  (SP (SPRC (mem_prio_reg Reg_c) (SO NB))
                  (SP (SPRC (mem_prio_reg Reg_a) (SO NC))
                  (SP (SPRC (mem_prio_reg Reg_b) (SO ND))
                  (SP (SINJ (oalist_map_l mem_sem_lifting_inner) (NE)) NX)))))))"
*)
(*
definition mem_lift1 ::
  "(syn, state0, _ state1) lifting" where
"mem_lift1 =
  schem_lift (SP NA (SP NB (SP NC (SP ND NE))))
  (SP (SPRC (mem_prio_reg Reg_flag) (SO NA)) 
                  (SP (SPRC (mem_prio_reg Reg_c) (SO NB))
                  (SP (SPRC (mem_prio_reg Reg_a) (SO NC))
                  (SP (SPRC (mem_prio_reg Reg_b) (SO ND))
                  (SP (SINJ (oalist_map_l mem_sem_lifting_inner) (NE)) NX)))))"
*)

definition mem_lift1 ::
  "(syn, state0, _ state1) lifting" where
"mem_lift1 =
  schem_lift (SP NA (SP NB (SP NC (SP ND NE))))
  (SP (SPRC (mem_prio_reg Reg_flag) (SO NA)) 
                  (SP (SPRC (mem_prio_reg Reg_c) (SO NB))
                  (SP (SPRC (mem_prio_reg Reg_a) (SO NC))
                  (SP (SPRC (mem_prio_reg Reg_b) (SO ND))
                  (SP (SPRC mem_prio_mem (SO NE)) NX)))))"


(*
definition mem_sem_lifting_gen ::
  "(syn, state0, ('s, ('x :: Mergeableb)) state) lifting" where
"mem_sem_lifting_gen =
  schem_lift (SP NA (SP NB (SP NC (SP ND NE))))
    (SP NX (SP NX (SP (SPRC (mem_prio_reg Reg_flag) (SO NA)) 
                  (SP (SPRC (mem_prio_reg Reg_c) (SO NB))
                  (SP (SPRC (mem_prio_reg Reg_a) (SO NC))
                  (SP (SPRC (mem_prio_reg Reg_b) (SO ND))
                  (SP (SINJ (oalist_map_l mem_sem_lifting_inner) (NE)) NX)))))))"
*)

fun mem0_sem :: "syn \<Rightarrow> state0 \<Rightarrow> state0" where
"mem0_sem (Sread s r) (reg_flag, reg_c, reg_a, reg_b, mem) = 
  (case get mem s of
    Some v \<Rightarrow>
      (case r of
        Reg_a \<Rightarrow> (reg_flag, reg_c, v, reg_b, mem)
        | Reg_b \<Rightarrow> (reg_flag, reg_c, reg_a, v, mem)
        | Reg_c \<Rightarrow> (reg_flag, v, reg_a, reg_b, mem)
        | Reg_flag \<Rightarrow> (v, reg_c, reg_a, reg_b, mem))
    | None \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, mem))"
| "mem0_sem (Swrite s r) (reg_flag, reg_c, reg_a, reg_b, mem) =
  (case r of
    Reg_a \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, update s reg_a mem)
    | Reg_b \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, update s reg_b mem)
    | Reg_c \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, update s reg_c mem)
    | Reg_flag \<Rightarrow> (reg_flag, reg_c, reg_a, reg_b, update s reg_flag mem))"
| "mem0_sem _ st = st"

(*
definition mem_sem :: "syn \<Rightarrow> ('s, 'x :: Mergeableb) state \<Rightarrow> ('s, 'x) state" where
"mem_sem = 
  lift_map_s id mem_sem_lifting_gen mem0_sem"

definition mem_sem_l_gen :: "('s \<Rightarrow> syn) \<Rightarrow> (syn, ('s, 'x :: Mergeableb) state, 'a) lifting \<Rightarrow> 's \<Rightarrow> ('a :: Mergeable) \<Rightarrow> 'a" where
"mem_sem_l_gen lfts lft =
  lift_map_s lfts
    (schem_lift NA (SINJ lft NA)) mem_sem"
*)


end
