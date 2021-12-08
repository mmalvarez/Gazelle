theory Calc_Mem_Imp_Hoare_Example
  imports Calc_Mem_Imp "../../Hoare/Hoare_Step" "../../Hoare/Hoare_Lift" 
    "../../Language_Components/Mem/Mem_Simple"
    "../../Lifter/Auto_Lifter_Proofs" "../../Composition/Composition_Lifter"
    "Calc_Mem_Imp_Hoare"
begin

(* final definitions that perhaps should be in mem_simple (TODO) *)


(* Deriving a set of Hoare logic rules useful for reasoning about imperative code in Imp.
 * then, proceeding with an example.
 *)

abbreviation sems where
"sems \<equiv> {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l}"

abbreviation sems_nos where
"sems_nos \<equiv> {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l}"

definition sem_final' :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"sem_final' =
  pcomps [calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l]"


(*lemma idea:
  - if, for each syntax, we can show one function is dominant
  - then we know sups_pres
  - maybe this is actually the best way to do it.
  - what about building this argument up from sub-sets?
    - might be ok if all languages leave things unchanged for other syntax.
*)
(*
lemma dominant_sups_pres2 ::
  assumes "f \<downharpoonleft> {} x"
*)  

(*
ok, so... how can we do this?
sups_pres of e.g. calc and mem...
- dominance
- need a nice way to "walk the tree" of liftings and compare priorities
*)

(*
(* New idea: have a lifting for use in theorems about the state. *)
(* in this case we can just use mem_lift1 I think. *)

lemma calc_sem_l_valid :
  ""
*)

lemma sups_pres_calc :
  "sups_pres {calc_sem_l} (\<lambda> _ . ok_S)"
  using sups_pres_singletonI
  by auto

lemma pres :
"sups_pres sems (\<lambda> _ . ok_S)"
  by(rule sups_pres_finite_all; auto)

(* concrete state *)
type_synonym cstate = "(syn, unit) Mem_Simple.state"

definition start_state :: "syn gensyn \<Rightarrow> (syn, unit) Mem_Simple.state" where
"start_state prog =
  ( Swr [prog]
  , mdp 0 (Some (mdt None))
  , Swr 0, Swr 0, Swr 0, Swr 0
  , Swr empty
  , ())"

definition state_mem where
"state_mem st =
  (case st of
    (_, _, _, _, _, _, m, _) \<Rightarrow> m)"

definition prog_mini :: "syn gensyn" where
"prog_mini =  G (Sc (Cnum 42)) []
"

(* first test: a simple arithmetic *)
definition prog0 :: "syn gensyn" where
"prog0 =
  G (Ss Sseq)
  [ G (Sc (Cnum 42)) []
  , G (Sm (Swrite (STR ''A'') Reg_c)) []
  ]"

definition prog00 :: "syn gensyn" where
"prog00 =
  G (Sb (Seqz)) []
  "


(* multiplication as repeated addition *)
(* start with c = 0
 * add arg1 to c
 * decrement arg2 *)

definition prog1 :: "int \<Rightarrow> int \<Rightarrow> syn gensyn" where
"prog1 i1 i2 =
  G (Ss Sseq)
  [ G (Sc (Cnum i1)) []
  , G (Sm (Swrite (STR ''arg1'') (Reg_c))) []
  , G (Sc (Cnum i2)) []
  , G (Sm (Swrite (STR ''arg2'') (Reg_c))) []
  , G (Sc (Cnum 1)) []
  , G (Sm (Swrite (STR ''one'') (Reg_c))) []
  , G (Sc (Cnum 0)) []
  , G (Sm (Swrite (STR ''acc'') (Reg_c))) []

  , G (Sm (Sread (STR ''arg2'') (Reg_c))) []
  , G (Sb Sgtz) []

  , G (Si SwhileC)
    [ G (Ss Sseq)
      [G (Sm (Sread (STR ''arg1'') (Reg_a))) []
      , G (Sm (Sread (STR ''acc'') (Reg_b))) []
      , G (Sc Cadd) []
      , G (Sm (Swrite (STR ''acc'') (Reg_c))) []
      , G (Sm (Sread (STR ''arg2'') (Reg_a))) []
      , G (Sm (Sread (STR ''one'') (Reg_b))) []
      , G (Sc Csub) []
      , G (Sm (Swrite (STR ''arg2'') (Reg_c))) []
      , G (Sm (Sread (STR ''arg2'') (Reg_c))) []
      , G (Sb Sgtz) []
      ]
    ]
  ]
"

(*
term "sem_run sem_final"

value "sem_run sem_final 100 (start_state prog0)"

value "sem_run (pcomps [calc_sem_l, mem_sem_l, seq_sem_l, cond_sem_l]) 100 (start_state prog_mini)"


value "sem_run sem_final 100 (start_state prog_mini)"

value "sem_run sem_final 100 (start_state (prog1 2 3))"
*)


definition oalist_check' :: "('a :: linorder * 'b md_triv option md_prio) list \<Rightarrow> bool"
  where
"oalist_check' l =
  list_all
    (\<lambda> x . case x of
      (k, mdp _ (Some (mdt _))) \<Rightarrow> True
      | _ \<Rightarrow> False ) l"

lift_definition oalist_check :: "('a :: linorder, 'b md_triv option md_prio) oalist \<Rightarrow> bool"
is oalist_check' .

fun oalist_unwrap' ::
"('a :: linorder * 'b md_triv option md_prio) list \<Rightarrow>
 ('a :: linorder * 'b) list option"
where
"oalist_unwrap' [] = Some []"
| "oalist_unwrap' (h#t) =
  (case h of
    (k, mdp _ (Some (mdt v))) \<Rightarrow>
      (case oalist_unwrap' t of
        Some t' \<Rightarrow> Some ((k, v)#t')
        | None \<Rightarrow> None)
    | _ \<Rightarrow> None)"

lemma oalist_unwrap'_keys :
  "oalist_unwrap' l = Some l' \<Longrightarrow>
   map fst l = map fst l'"
proof(induction l arbitrary: l')
  case Nil
  then show ?case by auto
next
  case (Cons a l)
  then show ?case 
    by(auto split: prod.splits option.splits md_triv.splits md_prio.splits)
qed

lift_definition oalist_unwrap ::
"('a :: linorder, 'b md_triv option md_prio) oalist \<Rightarrow> 
 ('a :: linorder, 'b ) oalist option"
is oalist_unwrap' 
proof-
  fix list :: "('a :: linorder * 'b md_triv option md_prio) list"
  assume H : "strict_order (map fst list)"
  
  show "pred_option (\<lambda>xs. strict_order (map fst xs))
        (oalist_unwrap' list)"
    using H oalist_unwrap'_keys[of list]
    by(auto simp add: pred_option_def)
qed


lemma prog1_spec :
  assumes Hi1 : "0 < i1" (* TODO: this should be \<le>, but for (i think) a technical reason this makes things hard (existential quantifier related problems) *)
  assumes Hi2 : "0 \<le> i2"

(* prog1 *)
(*
arg1 := i1
arg2 := i2
one := 1
acc := 0
while (arg2 > 0) {
  acc := acc + arg1
  arg2 := arg2 - one
}

*)

shows "|sem_final| {~ (\<lambda> st . st \<in> ok_S) ~}
                   [prog1 i1 i2]
                   {~ (\<lambda> st . st \<in> ok_S \<and>
                      (case st of
                        (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
                          (case mem of
                            (mdp p (Some (mdt mem'))) \<Rightarrow> get mem'(STR ''acc'') = Some (i1 * i2)
                            | _ \<Rightarrow> False)))
  ~}"
(*
  using HTS_imp_HT''[where l' = calc_trans, where x = "Calc_Mem_Imp.syn.Sc (Cnum i1)"
        , unfolded calc_trans.simps, OF HCalc_Cnum]
*)
proof-
  fix gs P z l

  have 1: "|sem_final| {~(\<lambda> st . st \<in> ok_S) ~}
[ G (Sc (Cnum i1)) []] 
  {~(\<lambda> st . st \<in> ok_S \<and> 
    (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c' \<Rightarrow> reg_c' = Some (mdt i1))))~}"
(is "|sem_final| {~ ?P0 ~}
[ G (Sc (Cnum i1)) []] 
  {~ ?P1~}")

    apply(rule HT'Conseq)
      apply(rule_tac P' = "\<lambda> _ . True" in Calc_Final)
       apply(fast) apply(fast)
    apply(force  simp add: calc_lift'_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S)
     apply(fast)
    apply(force  simp add: calc_lift'_def schem_lift_defs merge_l_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S)
    done

  have 2 : "|sem_final| 
    {~ ?P1 ~}
    [G (Sm (Swrite (STR ''arg1'') (Reg_c))) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> get m' (STR ''arg1'') = Some i1
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P1 ~}
    [G (Sm (Swrite (STR ''arg1'') (Reg_c))) []]
  {~ ?P2 ~}")


    apply(rule HT'Conseq)
      apply(rule_tac
 P = ?P1
and P' = "\<lambda> st . case st of (_, x, _, _) \<Rightarrow> x = i1"
in  Mem_Write_Final
;
fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
LNew_def)



     apply(fast)

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def) 


    done

(* TODO: need assumption about mem being empty? *)
  have 3: "|sem_final| {~ ?P2~}
[ G (Sc (Cnum i2)) []] 
  {~(\<lambda> st . ?P2 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c' \<Rightarrow> reg_c' = Some (mdt i2))))~}"
(is "|sem_final| {~ ?P2 ~}
[ G (Sc (Cnum i2)) []] 
  {~ ?P3~}")
    apply(rule HT'Conseq)
      apply(rule_tac P = ?P2 and P' = "\<lambda> _ . True" in Calc_Final)
       apply(fast) apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    done

  have 4 : "|sem_final| 
    {~ ?P3 ~}
    [G (Sm (Swrite (STR ''arg2'') (Reg_c))) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P3 ~}
    [G (Sm (Swrite (STR ''arg2'') (Reg_c))) []]
  {~ ?P4 ~}")

    apply(rule HT'Conseq)
      apply(rule_tac P = ?P3
and P' = "\<lambda> st . case st of (_, x, _, _, m) \<Rightarrow> x = i2 \<and> get m (STR ''arg1'') = Some i1"
  in Mem_Write_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
(* YOU ARE HERE. *)
(* wat *)
  apply(auto simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq
split:md_triv.splits) 
    done

  have 5 : "|sem_final| 
    {~ ?P4 ~}
    [G (Calc_Mem_Imp.syn.Sc (Cnum 1)) []]
{~(\<lambda>st. st \<in> ok_S \<and> ?P4 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c \<Rightarrow> reg_c = Some (mdt 1))))~}"
(is "|sem_final| 
    {~ ?P4 ~}
    _
  {~ ?P5 ~}")

    apply(rule HT'Conseq)
      apply(rule_tac P = ?P4
and P' = "\<lambda> _ . True"
  in Calc_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    done

  have 6 : "|sem_final| 
    {~ ?P5 ~}
    [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''one'' Reg_c)) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P5 ~}
    _
  {~ ?P6 ~}")

    apply(rule HT'Conseq)
    apply(rule_tac P = ?P5
and P' = "\<lambda> st . case st of (_, x, _, _, m) \<Rightarrow> x = 1 \<and> get m (STR ''arg1'') = Some i1 \<and> get m (STR ''arg2'') = Some i2"
in Mem_Write_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq
split: md_triv.splits) 

    done

  have 7 : "|sem_final| 
    {~ ?P6 ~}
    [G (Calc_Mem_Imp.syn.Sc (Cnum 0)) []]
{~(\<lambda>st. st \<in> ok_S \<and> ?P6 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b, mem, xz) \<Rightarrow>
      (case reg_c of mdp p reg_c \<Rightarrow> reg_c = Some (mdt 0))))~}"
(is "|sem_final| 
    {~ ?P6 ~}
    _
  {~ ?P7 ~}")
    apply(rule HT'Conseq)
      apply(rule_tac P = ?P6
and P' = "\<lambda> _ . True"
  in Calc_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 


    done

  have 8 : "|sem_final| 
    {~ ?P7 ~}
    [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''acc'' Reg_c)) []]
{~(\<lambda>st. st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1 \<and> get m' (STR ''acc'') = Some 0
                         | _ \<Rightarrow> False)))~}"
(is "|sem_final| 
    {~ ?P7 ~}
    _
  {~ ?P8 ~}")

    apply(rule HT'Conseq)
    apply(rule_tac P = ?P7
and P' = "\<lambda> st . case st of (_, x, _, _, m) \<Rightarrow> x = 0 \<and> get m (STR ''arg1'') = Some i1 
          \<and> get m (STR ''arg2'') = Some i2
          \<and> get m (STR ''one'') = Some 1"
        
in Mem_Write_Final)
       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(force simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(auto simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq) 

    done

(* TODO: we need to strengthen mem_read_final
along the same lines as mem_write_final. *)
  have 9 : "|sem_final| 
    {~ ?P8 ~}
    [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_c)) []]
{~ (\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1 \<and> get m' (STR ''acc'') = Some 0
                         | _ \<Rightarrow> False) \<and>
                      (case reg_c of 
                        mdp p (Some (mdt x)) \<Rightarrow> x = i2
                        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| 
    {~ ?P8 ~}
    _
  {~ ?P9 ~}")

    apply(rule HT'Conseq)
    apply(rule_tac P = ?P8
and P' = "\<lambda> st . (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m) \<Rightarrow>
                      get m (STR ''arg1'') = Some i1 
          \<and> get m (STR ''arg2'') = Some i2
          \<and> get m (STR ''one'') = Some 1
          \<and> get m (STR ''acc'') = Some 0)"
in Mem_Read_Final)

       apply(fast) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

      apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

(*
  apply(fastforce simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def oalist_map_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
*)

    apply(clarify)

  apply(simp add: calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq
split: md_triv.splits) 

    apply(clarify)

    apply(simp split: md_prio.splits md_triv.splits option.splits)


    done

(* establishing the invariant. *)
(*
invariant: acc = i1 * (arg2 - i2)
*)


  have 10 : "|sem_final| 
    {~ ?P9 ~}
    [G (Sb Sgtz) []]
    {~ (\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          get m' (STR ''arg1'') = Some i1 \<and> get m' (STR ''arg2'') = Some i2 \<and> get m' (STR ''one'') = Some 1 \<and> get m' (STR ''acc'') = Some 0 \<and>
                         (case reg_flag of
                          mdp p (Some (mdt reg_flag')) \<Rightarrow>
                            (reg_flag' = 0 \<and> i2 \<le> 0) \<or> (reg_flag' = 1 \<and> i2 > 0)
                          | _ \<Rightarrow> False)
                         | _ \<Rightarrow> False))) ~}"
(is "|sem_final|{~ ?P9 ~}
    [G (Sb Sgtz) []]
    {~ ?P10 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?P9 and P' = "\<lambda> st . (case st of (b, x) \<Rightarrow> x = i2)"
in Cond_Final)
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    apply(clarify)
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    apply(clarify)
    apply(case_tac "(0 < i2)")
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
    done

  obtain Inv :: "(_ :: {Bogus,Okay,Mergeableb,Pordc_all, Pordps}) Mem_Simple.state1 \<Rightarrow> bool" where Inv_def :
  "Inv = (\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          (\<exists> (idx :: int) . get m' (STR ''arg1'') = Some i1 \<and> 
                                       get m' (STR ''arg2'') = Some idx \<and>
                                       get m' (STR ''one'') = Some 1 \<and>
                                       get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                       i2 \<ge> idx \<and>
                                       (case reg_flag of mdp p (Some (mdt reg_flag')) \<Rightarrow>
                                         ((reg_flag' = 1 \<and> idx > 0) \<or> (reg_flag' = 0 \<and> idx = 0))
                                         | _ \<Rightarrow> False))
                        | _ \<Rightarrow> False)))"
    by simp


  have Inv_10 :
    "\<And> st . (?P10 st) \<Longrightarrow>
  Inv st"
    using Hi2 unfolding Inv_def
    by(auto split: md_triv.splits md_prio.splits option.splits)

(* while loop body *)
  have Body1 : 
"|sem_final| {~ (\<lambda> st . 
                  Inv st \<and>
                  (case st of (mdp p (Some (mdt reg_flag')), _) \<Rightarrow>
                    reg_flag' = 1
                   | _ \<Rightarrow> False)) ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg1'' Reg_a)) []]
  {~ (\<lambda> st . st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case reg_a of
        mdp p (Some (mdt reg_a')) \<Rightarrow> reg_a' = i1 \<and>
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow> 
            (\<exists> idx . 
get m' (STR ''arg1'') = Some i1 \<and>
get m' (STR ''arg2'') = Some idx \<and>
                     get m' (STR ''one'') = Some 1 \<and>
                     get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                     i2 \<ge> idx \<and>idx > 0)
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ ?B0 ~} _ {~ ?B1 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B0
and P' = "\<lambda> st . (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m) \<Rightarrow>
                     reg_flag = 1 \<and>
                     (\<exists> (idx :: int) . get m (STR ''arg1'') = Some i1 \<and> 
                                 get m (STR ''arg2'') = Some idx \<and>
                                 get m (STR ''one'') = Some 1 \<and>
                                 get m (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                 i2 \<ge> idx \<and>idx > 0))"
in Mem_Read_Final)

  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force  simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
 
  apply(force  simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

  apply(fastforce simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits option.splits) 
 
    done

(*
(\<lambda> st . st \<in> ok_S \<and> (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow>
                      (case m of
                        mdp p (Some (mdt m')) \<Rightarrow> 
                          (\<exists> idx . get m' (STR ''arg1'') = Some i1 \<and> 
                                       get m' (STR ''arg2'') = Some idx \<and>
                                       get m' (STR ''one'') = Some 1 \<and>
                                       get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                       i2 \<ge> idx \<and>idx \<ge> 0))))
*)
  have Body2 :
"|sem_final| {~ ?B1 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''acc'' Reg_b)) []]
  {~ (\<lambda> st . ?B1 st \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case reg_b of
        mdp p (Some (mdt reg_b')) \<Rightarrow> 
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow>
            (\<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> 
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some (i1 * (i2 - idx)))
                      | _ \<Rightarrow> False)
                    | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B2 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B1
and P' = "\<lambda> st . (case st of
                     (reg_flag, reg_c, reg_a, reg_b,  m) \<Rightarrow>
                     (\<exists> idx . get m (STR ''arg1'') = Some i1 \<and> i1 = reg_a \<and>
                                 get m (STR ''arg2'') = Some idx \<and>
                                 get m (STR ''one'') = Some 1 \<and>
                                 get m (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                                 i2 \<ge> idx \<and>idx > 0))"
in Mem_Read_Final)


  apply(force  simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(clarify)

  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
      apply(clarify)
  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
     apply(clarify)
  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(clarify)

     apply(
 simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits option.splits) 

    apply(clarify)
    apply(blast)

    done

  have Body3 :
(*
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . st \<in> ok_S \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow>
            (\<exists> idx . reg_c' = i1 * (i2 - idx) + i1 \<and>
                     reg_a' = i1 \<and> reg_b' = i1 * (i2 - idx) \<and>  get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                     i2 \<ge> idx \<and> idx \<ge> 0)
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B3 ~}")
*)
(*
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . ?B2 st \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        (case m of
          mdp p (Some (mdt m')) \<Rightarrow>
            (\<exists> (idx :: int) . reg_c' = i1 + i1 * (i2 - idx) \<and>
                     reg_a' = i1 \<and> reg_b' = i1 * (i2 - idx) \<and>  
                     get m' (STR ''acc'') = Some (i1 * (i2 - idx)) \<and>
                     get m' (STR ''arg2'') = Some idx \<and>
                     i2 \<ge> idx \<and> idx \<ge> 0)
          | _ \<Rightarrow> False)
        | _ \<Rightarrow> False))) ~}"
*)
(*
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . ?B2 st \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        reg_a' = i1 \<and>
         (\<exists> (idx :: int) . i2 \<ge> idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
*)
(*maybe we need a different calc rule(unchanged stuff *)
"|sem_final| {~ ?B2 ~}
  [G (Calc_Mem_Imp.syn.Sc Cadd) []]
  {~ (\<lambda> st . ?B2 st \<and>(case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c'))) \<Rightarrow> 
        reg_c' = reg_a' + reg_b'
                | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B3 ~}")

    apply(rule HT'Conseq)
(*
    apply(rule_tac P = ?B2
and P' = "\<lambda> _ . True"
in Calc_Final)
*)
(* TODO: looks like we actually do need a fact about the rest of the state
remaining unchanged. (this is in cases like arith, for instance, we need
to show a sort of "frame" where everything not in calc is unchanged *)

(*
    apply(rule_tac P = ?B2
and P' = "\<lambda> st . case st of (reg_a, reg_b, reg_c) \<Rightarrow>
          reg_a = i1 \<and>
          (\<exists> (idx :: int) . i2 \<ge> idx \<and> idx > 0 \<and> reg_b = i1 * (i2 - idx))"
in Calc_Final)
*)

    apply(rule_tac P = ?B2
and P' = "\<lambda> st . case st of (reg_a, reg_b, reg_c) \<Rightarrow>
          reg_a = i1 \<and>
          (\<exists> (idx :: int) . i2 \<ge> idx \<and> idx > 0 \<and> reg_b = i1 * (i2 - idx))"
in Add_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(insert Hi2)
    apply(insert Hi1)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)

    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
    apply(clarify)


    apply(simp)
    apply(insert Hi2)
    apply(insert Hi1)

  apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits) 

    apply(clarify)
    apply(simp (no_asm_simp))
(* begin experiment *)


(* end experiment *)
  apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def split: md_triv.splits
) 

    apply(clarify)

    apply(auto split: md_triv.splits)
(* idxb vs idx *)

    done

  have Body4 :
"|sem_final| {~ ?B3 ~}
  [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''acc'' Reg_c)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = i1 \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B4 ~}")

    apply(rule HT'Conseq)
(*
    apply(rule_tac P = ?B2
and P' = "\<lambda> _ . True"
in Calc_Final)
*)
    apply(rule_tac P = ?B3
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = i1 \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some ( i1 * (i2 - idx)) \<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Write_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
    done

  have Body5 : 
    "|sem_final| {~ ?B4 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_a)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"

(is "|sem_final| {~ _ ~} _ {~ ?B5 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B4
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = i1 \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some (i1 + i1 * (i2 - idx)) \<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Read_Final)

  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)

    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
    apply(auto split: option.splits)
    done


  have Body6 :
    "|sem_final| {~ ?B5 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''one'' Reg_b)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B6 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B5
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = i1 * (i2 - idx) \<and> reg_c' = i1 + i1 * (i2 - idx) \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some (i1 + i1 * (i2 - idx)) \<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Read_Final)

  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)

    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
    apply(auto split: option.splits)
    done

  have Body7 :
    "|sem_final| {~ ?B6 ~}
  [G (Calc_Mem_Imp.syn.Sc Csub) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B7 ~}")
    apply(rule HT'Conseq)
    apply(rule_tac P = ?B6
and P' = "\<lambda> st . case st of (reg_a', reg_b', reg_c') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1  \<and> reg_a' = idx"
in Sub_Final)
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 


    apply(insert Hi2)
    apply(insert Hi1)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
      apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits md_prio.splits)
     apply(clarify)

    apply(simp)
    apply(clarify)
    apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits)
    apply(clarify)


  apply(simp add: Inv_def cond_lift'_def calc_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def 
split: md_triv.splits) 

    done

    have Body8 :
    "|sem_final| {~ ?B7 ~}
  [G (Calc_Mem_Imp.syn.Sm (Swrite STR ''arg2'' Reg_c)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some (idx - 1) \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B8 ~}")
      apply(rule_tac HT'Conseq)
    apply(rule_tac P = ?B7
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some idx \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))\<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Write_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def get_update_neq get_delete_neq get_update
split: md_triv.splits) 
      done

    have Body9 :
    "|sem_final| {~ ?B8 ~}
  [G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_c)) []]
  {~ (\<lambda> st .  st \<in> ok_S \<and> (case st of (reg_flag, reg_c, reg_a, reg_b,  m, xz) \<Rightarrow> 
      (case (reg_a, reg_b, reg_c, m) of
        (mdp _ (Some (mdt reg_a')), mdp _ (Some (mdt reg_b')), mdp _ (Some (mdt reg_c')), mdp _ (Some (mdt m'))) \<Rightarrow> 
        \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some (idx - 1) \<and>
            get m' (STR ''one'') = Some (1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))
        | _ \<Rightarrow> False))) ~}"
(is "|sem_final| {~ _ ~} _ {~ ?B9 ~}")
      apply(rule_tac HT'Conseq)
    apply(rule_tac P = ?B8
and P' = "\<lambda> st . case st of (reg_flag', reg_c', reg_a', reg_b', m') \<Rightarrow>
            \<exists> (idx :: int) . i2 \<ge>  idx \<and> idx > 0 \<and> reg_b' = 1 \<and> reg_c' = idx - 1 \<and> reg_a' = idx \<and>
            get m' (STR ''arg1'') = Some i1 \<and>
            get m' (STR ''arg2'') = Some (idx - 1) \<and>
            get m' (STR ''acc'') = Some ( i1 + i1 * (i2 - idx))\<and>
 get m' (STR ''one'') = Some (1)"
in Mem_Read_Final)


  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 

    apply(clarify)

     apply(
 simp add: Inv_def cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits option.splits) 

      done

    have Helper : "\<And> (x :: int) (y :: int) . x + x * y = x * (1 + y)"
    proof-
      fix x y :: int
      show "x + x * y = x * (1 + y)"
        using int_distrib
        by auto
    qed

    have Body10:
    "|sem_final| {~ ?B9 ~}
  [G (Sb Sgtz) []]
  {~ Inv ~}"
(is "|sem_final| {~ _ ~} _ {~ _ ~}")
      apply(rule_tac HT'Conseq)
        apply(rule_tac
P = ?B9 and
P' = "\<lambda> st . (case st of (b, x) \<Rightarrow> \<exists> idx . i2 \<ge>  idx \<and> idx > 0 \<and> x = (idx - 1))" in
 Gtz_Final)
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(force simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def cond_sem_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def
split: md_triv.splits) 
      apply(clarify)
  apply(simp add: cond_lift'_def schem_lift_defs merge_l_def mem_lift1_def
mem_sem_lifting_inner_def Inv_def
fst_l_def snd_l_def prio_l_def option_l_def triv_l_def 
option_ok_S prod_ok_S prio_ok_S triv_ok_S oalist_ok_S
 LNew_def int_distrib
split: md_triv.splits) 
      done

      have Conclusion :
        "\<And> st . Inv st \<Longrightarrow> 
         get_cond st = Some False \<Longrightarrow>
    (case st of (_, _, _, _, mdp p (Some (mdt m')), _) \<Rightarrow> get m' (STR ''acc'') = Some (i1 * i2)
     | _ \<Rightarrow> False
      )"
    using Hi1 Hi2 unfolding Inv_def
    apply(auto simp add: get_cond_def split: md_triv.splits md_prio.splits)
    apply(case_tac x2a; simp)
    apply(case_tac a; simp)
    apply(case_tac x2; simp)
    apply(case_tac ad; simp)
    apply(case_tac "xa = 0"; simp)
    done


(* TODO: is our loop invariant correct? *)


(*
 [, ,
          , , , G (Calc_Mem_Imp.syn.Sm (Sread STR ''arg2'' Reg_c)) [], G (Sb Sgtz) []]]]
*)



end