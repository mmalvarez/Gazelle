theory Cond_Mem imports Cond "../Mem/Mem" "../../Composition/Composition"
begin

datatype syn =
  Sb cond str
  | Sm "Mem.syn"
  | Ssk

fun cond_key :: "syn \<Rightarrow> str option" where
"cond_key (Sb _ s) = Some s"
| "cond_key _ = None"

fun cond_trans :: "syn \<Rightarrow> cond" where
"cond_trans (Sb c _) = c"
| "cond_trans _ = Sskip_cond"

(* I think this state type is wrong. We need the boolean as well. *)
definition cond_sem_l ::  "syn \<Rightarrow> state \<Rightarrow> state" where
"cond_sem_l =
  lift_map_s id
  (schem_lift
    (SP NA NB)
    (SP NX
        (SP (SPRI (SO NA))
            (SL cond_key (SPRK (SO NB))))))
  (cond_sem o cond_trans)"
end