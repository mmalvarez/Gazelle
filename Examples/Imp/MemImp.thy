theory MemImp
  imports Mem "../ImpCtl" 
begin

datatype calc2 = 
  Cadd
  | Csub
  | Cmul
  | Cdiv
  | Cskip

datatype syn =
  Sc "calc2" "str" "str" "str"
  | Ss "Seq.syn"
  | Sb "ImpCtl.cond_syn'" "str"
  | Sm "Mem.syn"
  | Si "ImpCtl.syn'"
  | Ssk

type_synonym calc2_state =
  "(int * int * int)"

fun imp_trans :: "syn \<Rightarrow> ImpCtl.syn'" where
"imp_trans (Si x) = x"
| "imp_trans _ = ImpCtl.Sskip"

fun calc2_trans :: "syn \<Rightarrow> calc2" where
"calc2_trans (Sc x _ _ _) = x"
| "calc2_trans _ = Cskip"

fun calc2_key1 :: "syn \<Rightarrow> str option" where
"calc2_key1 (Sc _ s1 _ _) = Some s1"
| "calc2_key1 _ = None"

fun calc2_key2 :: "syn \<Rightarrow> str option" where
"calc2_key2 (Sc _ _ s2 _) = Some s2"
| "calc2_key2 _ = None"

fun calc2_key3 :: "syn \<Rightarrow> str option" where
"calc2_key3 (Sc _ _ _ s3) = Some s3"
| "calc2_key3 _ = None"

fun cond_key :: "syn \<Rightarrow> str option" where
"cond_key (Sb _ s) = Some s"
| "cond_key _ = None"
        
(*
definition calc2_key_lift :: "(syn, calc2_state, (str, int swr) oalist) lifting" where
"calc2_key_lift =
  merge_l
    (oalist_l calc2_key1 ((prio_l_keep o option_l o triv_l) id_l))
    (merge_l
      (oalist_l calc2_key2 ((prio_l_keep o option_l o triv_l) id_l))
      (oalist_l calc2_key3 ((prio_l_inc o option_l o triv_l) id_l)))"
*)

definition calc2_key_lift :: "(syn, calc2_state, (str, int swr) oalist) lifting" where
"calc2_key_lift =
  schem_lift
        (SP NA (SP NB NC))
        (SM (SL calc2_key1 (SPRK (SOT NA)))
        (SM (SL calc2_key2 (SPRK (SOT NB)))
            (SL calc2_key3 (SPRI (SOT NC)))))"

fun calc2_sem :: "calc2 \<Rightarrow> calc2_state \<Rightarrow> calc2_state" where
"calc2_sem (Cadd) (x1, x2, x3) =
  (x1, x2, x1 + x2)"
| "calc2_sem (Csub) (x1, x2, _) = (x1, x2, x1 - x2)"
| "calc2_sem (Cmul) (x1, x2, _) = (x1, x2, x1 * x2)"
| "calc2_sem (Cdiv) (x1, x2, _) = (x1, x2, divide_int_inst.divide_int x1 x2)"
| "calc2_sem (Cskip) st = st"

fun seq_trans :: "MemImp.syn \<Rightarrow> Seq.syn" where
"seq_trans (Ss s) = s"
| "seq_trans _ = Seq.Sskip"

fun cond_trans :: "syn \<Rightarrow> cond_syn'" where
"cond_trans (Sb s _) = s"
| "cond_trans _ = Sskip_cond"

fun mem_trans :: "syn \<Rightarrow> Mem.syn" where
"mem_trans (Sm s) = s"
| "mem_trans _ = Mem.Sskip"

type_synonym state =
  "Seq.state * 
    (bool md_triv option md_prio *
    (Mem.state))"

definition imp_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"imp_sem_l =
  l_map_s imp_trans
  (schem_lift
    (SP (SP NA (SP NB NC)) ND)
        (SP 
          (SP (SOT NA)
              (SP (SPRC imp_prio (SOT NB)) (SPRC imp_prio (SOT NC))))
          (SP (SPRK (SOT ND)) NX)))
  imp_ctl_sem"

definition calc2_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"calc2_sem_l =
  l_map_s id
  (schem_lift
    NA (SP NX (SP NX (SINJ calc2_key_lift NA))))
  (calc2_sem o calc2_trans)"

definition cond_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"cond_sem_l =
  l_map_s id
  (schem_lift
    (SP NA NB)
    (SP NX
        (SP (SPRI (SOT NA))
            (SL cond_key (SPRK (SOT NB))))))
  (cond_sem o cond_trans)"

definition mem_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"mem_sem_l = 
  l_map_s mem_trans
    (schem_lift NA (SP NX (SP NX NA)))
  mem_sem"

definition seq_sem_l :: "syn \<Rightarrow> state \<Rightarrow> state" where
"seq_sem_l =
  l_map_s seq_trans 
  (schem_lift NA (SP NA NX))
  Seq.seq_sem_l"

definition sems where
"sems = [imp_sem_l, calc2_sem_l, cond_sem_l, seq_sem_l, mem_sem_l]"

definition sem_final :: "(syn, state) x_sem'" where
"sem_final =
  l_map_s id
    (schem_lift
      NA (SFAN (LOut
                (schem_lift (SP NA NB) 
                            (SP (SP (SOT NA) (SP (SPRK (SOT NB)) NX)) NX))) 
          NA))
    (pcomps sems)"


definition gsx :: "syn gensyn \<Rightarrow> childpath \<Rightarrow> state \<Rightarrow> nat \<Rightarrow> state option" where
"gsx =
  gensyn_sem_exec (xsem sem_final)"

definition initial :: "syn gensyn \<Rightarrow> state" where
"initial p = 
  ( (Some (mdt (gs_sk p))
    , (mdp 0 (Some (mdt (GRPath []))))
    , mdp 0 (Some (mdt Down)))
  , (mdp 0 (Some (mdt False)))
  , empty)"

definition test0 :: "syn gensyn" where
"test0 = G (Sm (Slit (STR ''a'') 0)) []"


(* multiply by adding
   compute x * y, adding y to 0 x times *)
definition test1 :: "int \<Rightarrow> int \<Rightarrow> syn gensyn" where
"test1 x y =
  G (Ss Sseq)
  [ G (Sm (Slit (STR ''x'') x)) []
  , G (Sm (Slit (STR ''y'') y)) []
  , G (Sm (Slit (STR ''result'') 0)) []
  , G (Sm (Slit (STR ''1'') 1)) []
  , G (Si (Swhile))
    [ G (Sb Sgtz (STR ''x'') ) []
    , G (Ss Sseq)
      [ G (Sc Cadd (STR ''result'') (STR ''y'') (STR ''result'')) []
      , G (Sc Csub (STR ''x'') (STR ''1'') (STR ''x'')) [] ] ] ] "

value "gsx (test1 7 3) [] (initial (test1 7 3)) 999"

value "gsx (test0) [] (initial test0) 999"


end