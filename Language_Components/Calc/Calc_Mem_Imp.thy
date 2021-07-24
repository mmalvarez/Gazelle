theory Calc_Mem_Imp imports Calc_Mem "../Cond/Cond" "../Imp_Ctl/Imp_Ctl" "../Seq/Seq"
begin

datatype syn =
  Sc "calc"
  | Sm "Mem_Simple.syn"
  | Sb "cond"
  | Si "Imp_Ctl.syn'"
  | Ss "Seq.syn"
  | Ssk

fun calc_trans :: "syn \<Rightarrow> calc" where
"calc_trans (Sc x ) = x"
| "calc_trans _ = Cskip"

fun mem_trans :: "syn \<Rightarrow> Mem_Simple.syn" where
"mem_trans (Sm m) = m"
| "mem_trans _ = Mem_Simple.Sskip"

fun cond_trans :: "syn \<Rightarrow> Cond.cond" where
"cond_trans (Sb x) = x"
| "cond_trans _ = Sskip_cond"

fun seq_trans :: "syn \<Rightarrow> Seq.syn" where
"seq_trans (Ss x) = x"
| "seq_trans _ = Seq.Sskip"

fun imp_trans :: "syn \<Rightarrow> Imp_Ctl.syn'" where
"imp_trans (Si x) = x"
| "imp_trans _ = Imp_Ctl.Sskip"

(* layout of state:
 * boolean flag
 * result int (for some reason)
 * input int 1
 * input int 2
 * control stuff (at end and probably don't need to care)
 *)

type_synonym ('s, 'x) state = 
  "('s, 'x) Mem_Simple.state"

(* now we need to restate this using no_control_l *)
definition calc_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"calc_sem_l =
  lift_map_s calc_trans
  (schem_lift
    (SP NA (SP NB NC))
    (SP NX (SP NX (SP (SPRI (SO NC)) (SP (SPRI (SO NB)) (SP (SPRI (SO NA)) NX))))))
  calc_sem"

definition mem_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"mem_sem_l = 
  lift_map_s mem_trans
    id_l
  mem_sem"

definition cond_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"cond_sem_l =
  lift_map_s cond_trans
    (schem_lift (SP NA NB) (SP NX (SP NX (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) NX)))))
  cond_sem
"

definition imp_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"imp_sem_l = imp_sem_l_gen imp_trans"

definition seq_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"seq_sem_l = seq_sem_l_gen seq_trans"


definition sem_final :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"sem_final =
  pcomps [calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l]"

(* testing *)

(*
term "(schem_lift (SP NA (SP NB (SP NC (SP ND (NE)))))
                    (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC))
                    (SP (SPRI (SO ND)) (SID NE))))))"

term "(schem_lift (SP NA (SP NB (SP NC (SP ND (SP NE NF)))))
                    (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC))
                    (SP (SPRI (SO ND)) (SP (SPRI (SO NE)) (SID NF)))))))"


definition st_lift :: "(syn, int * int * int * int  * (String.literal, int swr) oalist, state) lifting" where
"st_lift =
  (schem_lift (SP NA (SP NB (SP NC (SP ND (NE)))))
                    (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC))
                    (SP (SPRI (SO ND)) (SID NE))))))"
term "LNew st_lift"

value "sem_final (Sm (Swrite (STR ''a'') Reg_a)) (LNew st_lift Ssk (4, 0, 0, 0, empty))"
*)
end