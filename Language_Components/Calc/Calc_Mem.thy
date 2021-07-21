theory Calc_Mem imports Calc "../Mem/Mem" "../../Composition/Composition"
begin

datatype syn =
  Sc "calc" "str" "str" "str"
  | Sm "Mem.syn"
  | Ssk (* skip *)

fun calc2_key1 :: "syn \<Rightarrow> str option" where
"calc2_key1 (Sc _ s1 _ _) = Some s1"
| "calc2_key1 _ = None"

fun calc2_key2 :: "syn \<Rightarrow> str option" where
"calc2_key2 (Sc _ _ s2 _) = Some s2"
| "calc2_key2 _ = None"

fun calc2_key3 :: "syn \<Rightarrow> str option" where
"calc2_key3 (Sc _ _ _ s3) = Some s3"
| "calc2_key3 _ = None"

definition calc_key_lift :: "(syn, calc_state, (str, int swr) oalist) lifting" where
"calc_key_lift =
  schem_lift
        (SP NA (SP NB NC))
        (SM (SL calc2_key1 (SPRK (SO NA)))
        (SM (SL calc2_key2 (SPRK (SO NB)))
            (SL calc2_key3 (SPRI (SO NC)))))"

fun calc_trans :: "syn \<Rightarrow> calc" where
"calc_trans (Sc x _ _ _) = x"
| "calc_trans _ = Cskip"

(* We should be targeting a different state type. *)
definition calc_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"calc_sem_l =
  lift_map_s id
  (schem_lift
    NA (SINJ calc_key_lift NA))
  (calc_sem o calc_trans)"

fun mem_trans :: "syn \<Rightarrow> Mem.syn" where
"mem_trans (Sm m) = m"
| "mem_trans _ = Sskip"

definition mem_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem_l = 
  lift_map_s mem_trans
    (schem_lift NA (SID NA))
  mem_sem"

definition sem_final :: "(syn \<Rightarrow> state \<Rightarrow> state)" where
"sem_final = 
  pcomps [calc_sem_l, mem_sem_l]"

end