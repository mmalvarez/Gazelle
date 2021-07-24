theory Calc_Mem_Cond_Imp imports Calc_Mem "../Cond/Cond"
begin

datatype syn =
  Sc "calc"
  | Sm "Mem_Simple.syn"
  | Sb "cond"
  | Ssk

fun calc_trans :: "syn \<Rightarrow> calc" where
"calc_trans (Sc x ) = x"
| "calc_trans _ = Cskip"

fun mem_trans :: "syn \<Rightarrow> Mem_Simple.syn" where
"mem_trans (Sm m) = m"
| "mem_trans _ = Sskip"

fun cond_trans :: "syn \<Rightarrow> Cond.cond" where
"cond_trans (Sb x) = x"
| "cond_trans _ = Sskip_cond"

type_synonym state = "(bool swr * Calc_Mem.state)"

definition calc_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"calc_sem_l =
  lift_map_s calc_trans
  (schem_lift
    (SP NA (SP NB NC)) (SP NX (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC)) NX)))))
  calc_sem"

definition mem_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem_l = 
  lift_map_s mem_trans
    (schem_lift 
      (SP NA NB) (SP NX (SP NX (SP NX (SP (SID NA) (SID NB))))))
  mem_sem"

definition cond_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"cond_sem_l =
  lift_map_s cond_trans
    (schem_lift (SP NA NB) (SP (SPRI (SO NA)) (SP NX (SP NX (SP (SPRI (SO NB)) NX)))))
  cond_sem
"

definition sem_final :: "syn \<Rightarrow> state \<Rightarrow> state" where
"sem_final =
  pcomps [calc_sem_l, mem_sem_l, cond_sem_l]"


end