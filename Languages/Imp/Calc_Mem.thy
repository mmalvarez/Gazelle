theory Calc_Mem imports "../../Language_Components/Calc/Calc"
                        "../../Language_Components/Mem/Mem_Simple"
                        "../../Composition/Composition"
begin

datatype syn =
  Sc "calc"
  | Sm "Mem_Simple.syn"
  | Ssk (* skip *)

(*
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
*)
fun calc_trans :: "syn \<Rightarrow> calc" where
"calc_trans (Sc x ) = x"
| "calc_trans _ = Cskip"


type_synonym ('s, 'x) state = 
  "('s, 'x) Mem_Simple.state"
(*
type_synonym state = "(int swr * int swr * int swr * int swr * (str, int swr) oalist)"
*)

term "(schem_lift
    (SP NA (SP NB NC)) 
    (SP NX
      (SP NX
        (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC)) NX))))))"

term "undefined :: ('s, 'x) state"

(* NB: we are inferring mergeability on the last component - I think. *)
definition calc_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"calc_sem_l =
  lift_map_s calc_trans
  (schem_lift
    (SP NA (SP NB NC)) 
    (SP NX
      (SP NX
        (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC)) NX))))))
  calc_sem"

fun mem_trans :: "syn \<Rightarrow> Mem_Simple.syn" where
"mem_trans (Sm m) = m"
| "mem_trans _ = Sskip"
(*
definition mem_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"mem_sem_l = 
  lift_map_s mem_trans id_l
  mem_sem"

term "mem_sem_l"

definition sem_final :: "(syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state)" where
"sem_final = 
  pcomps [calc_sem_l, mem_sem_l]"
*)
end