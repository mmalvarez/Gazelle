theory Calc_Mem_Imp imports (*Calc_Mem*)
 "../../Language_Components/Cond/Cond" 
 "../../Language_Components/Calc/Calc"
  "../../Language_Components/Mem/Mem_Simple"
              "../../Language_Components/Imp_Ctl/Imp_Ctl" 
             "../../Language_Components/Seq/Seq" 
"../../Hoare/Hoare_Step"
"../../Composition/Dominant_Instances"
"../../Lifter/Auto_Lifter_Proofs"
"../../Lifter/Auto_Lifter"
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

fun calc_prio :: "(Calc.calc \<Rightarrow> nat)" where
"calc_prio (Cskip) = 1"
| "calc_prio _ = 2"

fun calc_toggle :: "syn \<Rightarrow> bool" where
"calc_toggle (Sc _) = True"
| "calc_toggle _ = False"

fun mem_trans :: "syn \<Rightarrow> Mem_Simple.syn" where
"mem_trans (Sm m) = m"
| "mem_trans _ = Mem_Simple.Sskip"

fun mem_toggle :: "syn \<Rightarrow> bool" where
"mem_toggle (Sm _) = True"
| "mem_toggle _ = False"

(* mem_prio not needed, handled by custom implementation (?still true?) *)

fun cond_trans :: "syn \<Rightarrow> Cond.cond" where
"cond_trans (Sb x) = x"
| "cond_trans _ = Sskip_cond"

fun cond_prio :: "Cond.cond \<Rightarrow> nat" where
"cond_prio (Sskip_cond) = 1"
| "cond_prio _ = 2"

fun cond_toggle :: "syn \<Rightarrow> bool" where
"cond_toggle (Sb _) = True"
| "cond_toggle _ = False"

fun seq_trans :: "syn \<Rightarrow> Seq.syn" where
"seq_trans (Ss x) = x"
| "seq_trans _ = Seq.Sskip"

(* NB seq is always active; this is handled by special rules *)

fun imp_trans :: "syn \<Rightarrow> Imp_Ctl.syn'" where
"imp_trans (Si x) = x"
| "imp_trans _ = Imp_Ctl.Sskip"

fun imp_toggle :: "syn \<Rightarrow> bool" where
"imp_toggle (Si _) = True"
| "imp_toggle _ = False"

(* layout of state:
 * boolean flag
 * result int (for some reason)
 * input int 1
 * input int 2
 * control stuff (at end and probably don't need to care)
 *)

type_synonym ('s, 'x) state =
  "('s, 'x) Mem_Simple.state"

definition calc_schemi where
"calc_schemi = (SP NA (SP NB NC))"
declare calc_schemi_def [simp]

definition calc_lift_aux1 where
"calc_lift_aux1 = 
  schem_lift NA (SPRI (SO NA))"
declare calc_lift_aux1_def [simp]

definition calc_lift_aux2 where
"calc_lift_aux2 =
  schem_lift NA (SP (SPRI (SO NA)) NX)"

definition calc_schemo where
"calc_schemo = (SP NX (SP (SPRC calc_prio (SO NC)) (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) NX))))"
declare calc_schemo_def [simp]

(* need no_control_lifting_S *)
definition calc_lift :: "(Calc.calc, Calc.calc_state, ('s, 'x :: {Bogus, Pord, Mergeableb, Okay, Pordps}) Mem_Simple.state) lifting" where
"calc_lift = 
  no_control_lifting (schem_lift calc_schemi calc_schemo)"

definition calc_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"calc_sem_l =
 lift_map_t_s calc_trans calc_lift calc_toggle
calc_sem"


lemma calc_prio_pos : "\<And> s . 0 < calc_prio s"
proof-
  fix s
  show "0 < calc_prio s"
    by(cases s; auto)
qed

lemma calc_valid :
  "lifting_valid_ok ((schem_lift calc_schemi calc_schemo)
::
    (Calc.calc, Calc.calc_state, ('x :: {Okay, Bogus, Mergeableb, Pordps}) state1) lifting)
    (schem_lift_S calc_schemi calc_schemo) "
  unfolding calc_lift_def schem_lift_defs schem_lift_S_defs
no_control_lifting_def calc_schemi_def calc_schemo_def 
  by(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)

lemma calc_valid_full' :
  "lifting_valid_ok (no_control_lifting (schem_lift calc_schemi calc_schemo)  ::
(Calc.calc, Calc.calc_state, ('s, 'x :: {Bogus, Pord, Mergeableb, Okay, Pordps}) Mem_Simple.state) lifting)
                    (no_control_lifting_S (schem_lift calc_schemi calc_schemo) (schem_lift_S calc_schemi calc_schemo))"
  using no_control_l_valid[OF calc_valid]
  by auto

lemma calc_valid_full :
  "lifting_valid_ok calc_lift
(no_control_lifting_S (schem_lift calc_schemi calc_schemo) (schem_lift_S calc_schemi calc_schemo))"
  unfolding calc_lift_def
  using calc_valid_full'
  by auto

(* the following sketch gives more detail into the proof structure.
 * it may be useful for debugging errors in the proof search, especially
 * tricky ones related to polymorphism *)
(*

  apply(rule merge_l_ortho.ax_g_comm)
          apply(auto intro: lifting_valid_slower lifting_ortho_slow)
        apply(rule merge_l_ortho.intro)
          apply(rule snd_l_ortho.ax_g)
          apply(auto intro: lifting_valid_slower lifting_ortho_slow)
              apply(rule snd_l_ortho.intro)
              apply(rule fst_l_snd_l_ortho.ax_g_comm)
          apply(auto intro: lifting_valid_slower lifting_ortho_slow)
              apply(rule fst_l_snd_l_ortho.intro)
               apply(rule lifting_valid_base_ext.intro)
               apply(simp add: prio_l_def option_l_def triv_l_def bot_defs)
  apply(rule lifting_valid_base_ext.intro)
        apply(simp add: lifter_instances bot_defs)
  apply(rule snd_l_ortho.ax_g)
         apply(auto intro: lifting_valid_slower lifting_ortho_slow)
       apply(rule snd_l_ortho.intro)
  apply(rule snd_l_ortho.ax_g)
         apply(auto intro: lifting_valid_slower lifting_ortho_slow)
       apply(rule snd_l_ortho.intro)
  apply(rule fst_l_snd_l_ortho.ax_g_comm)
         apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
        apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
       apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
      apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
         apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
    apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
  apply(rule merge_l_valid_ext.ax)
  apply(rule merge_l_valid_ext.intro)
    apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
   apply(rule merge_l_valid_ext.ax)
  apply(rule merge_l_valid_ext.intro)
    apply(fastforce intro: lifting_valid_slower lifting_ortho_slow)
   apply(rule snd_l_valid_ext.ax)
   apply(rule snd_l_valid_ext.intro)
   apply(rule fst_l_valid_ext.ax)
   apply(rule fst_l_valid_ext.intro)
   apply(rule prio_l_valid_ext_strong.ax)
   apply(rule prio_l_valid_ext_strong.intro)
   apply(rule prio_l_valid_ext_strong'.intro)
   apply(simp add: calc_prio_pos)

  apply(rule merge_l_valid_ok_ext.ax_g)
  apply(rule merge_l_valid_ok_ext.intro)
         apply(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)
  apply(rule snd_l_valid_ok_ext.ax_g)
     apply(rule snd_l_valid_ok_ext.intro)
  apply(rule snd_l_valid_ok_ext.ax_g)
  apply(rule snd_l_valid_ok_ext.intro)
  apply(rule fst_l_valid_ok_ext.ax_g)
       apply(rule fst_l_valid_ok_ext.intro)
       apply(rule prio_l_valid_ok_ext.ax)
       apply(rule prio_l_valid_ok_ext.intro)
       apply(rule option_l_valid_ok_ext.ax)
       apply(rule option_l_valid_ok_ext.intro)
(* Something weird about polymorphism is happening here. *)
  apply(rule triv_l_valid_ok_ext.ax)
         apply(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)
         apply(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)
         apply(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)
         apply(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)
         apply(fastforce simp add: calc_prio_pos intro: lifting_valid_fast lifting_ortho_fast)

(*
  using merge_l_ortho.ax_g_comm
  using merge_l_ortho.ax_g_comm
[of "(snd_l (snd_l (snd_l (fst_l (prio_l (\<lambda>_. 0) (\<lambda>_. (+) (Suc 0)) (option_l triv_l))))))"
     _ 
     "(snd_l (fst_l (prio_l calc_prio (\<lambda>s. (+) (calc_prio s)) (option_l triv_l))))" 
     _
     "(snd_l (snd_l (fst_l (prio_l (\<lambda>_. 0) (\<lambda>_. (+) (Suc 0)) (option_l triv_l)))))"]
*)
        apply(rule merge_l_ortho.ax_g_comm)
              apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
              apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom; simp add: fst_l_S_def snd_l_S_def prio_l_S_def)

          apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
        apply(rule merge_l_ortho.intro)
(* bad things start happening here - introducing existential-variable constraints that are not solvable! *)
  apply(rule snd_l_ortho.ax)
            apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
              apply(rule snd_l_ortho.intro)
  apply(rule fst_l_snd_l_ortho.ax_g_comm)
          apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom lifting_valid_base_ext.intro base_bot)
              apply(rule fst_l_snd_l_ortho.intro)
  apply(rule prio_l_valid_base_ext.ax)
  apply(rule prio_l_valid_base_ext.intro)
                apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
              apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
  apply(simp add: snd_l_S_def fst_l_S_def prio_l_S_def option_l_S_def split: md_prio.splits)
apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
              apply(rule snd_l_valid_base_ext.ax)
              apply(rule snd_l_valid_base_ext.intro)
           apply(rule fst_l_valid_base_ext.ax)
  apply(simp add: snd_l_S_def fst_l_S_def prio_l_S_def option_l_S_def split: md_prio.splits)
apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
  apply(simp add: snd_l_S_def fst_l_S_def prio_l_S_def option_l_S_def split: md_prio.splits)
apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)

                apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
*)

definition cond_lift :: "(Cond.cond, Cond.cond_state, ('s, 'x :: {Bogus, Pord, Mergeableb, Okay, Pordps}) Mem_Simple.state) lifting" where
"cond_lift = 
  no_control_lifting (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX)) :: (Cond.cond, Cond.cond_state, ('x :: {Okay, Bogus, Mergeableb, Pordps}) state1) lifting)
"

definition cond_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"cond_sem_l =
  lift_map_t_s cond_trans
    cond_lift cond_toggle
  cond_sem"

lemma cond_prio_pos :
  "\<And> s . 0 < cond_prio s"
proof-
  fix s
  show "0 < cond_prio s"
    by(cases s; auto)
qed

lemma cond_valid :
  "lifting_valid_ok ((schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX))) ::
    (Cond.cond, Cond.cond_state, ('x :: {Okay, Bogus, Mergeableb, Pordps}) state1) lifting)
    (schem_lift_S (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX))) "
  unfolding calc_lift_def schem_lift_defs schem_lift_S_defs
no_control_lifting_def calc_schemi_def calc_schemo_def 
  by(fastforce simp add: cond_prio_pos intro: lifting_valid_fast lifting_ortho_fast)

lemma cond_valid_full' :
  "lifting_valid_ok 
  (no_control_lifting (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX)) :: (Cond.cond, Cond.cond_state, ('x :: {Okay, Bogus, Mergeableb, Pordps}) state1) lifting))
  (no_control_lifting_S (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX)))
  (schem_lift_S (SP NA NB) (SP (SPRC cond_prio (SO NA))
                     (SP (SPRI (SO NB)) NX))))"
    using no_control_l_valid[OF cond_valid]
    by auto

lemma cond_valid_full :
  "lifting_valid_ok
  cond_lift
  (no_control_lifting_S (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX)))
  (schem_lift_S (SP NA NB) (SP (SPRC cond_prio (SO NA))
                     (SP (SPRI (SO NB)) NX))))"
  unfolding cond_lift_def
  using cond_valid_full'
  by blast


(*
definition imp_sem_l :: "syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state" where
"imp_sem_l = imp_sem_l_gen imp_trans"
*)


definition seq_sem_l :: "syn \<Rightarrow> ('s, _ ::{Okay, Bogus, Mergeableb, Pordps}) state \<Rightarrow> ('s, _) state" where
"seq_sem_l = seq_sem_l_gen seq_trans"

definition mem_lift :: "(Mem_Simple.syn, Mem_Simple.state0, ('s, _ ::{Okay, Bogus, Mergeableb, Pordps}) state) lifting" where
"mem_lift = no_control_lifting mem_lift1"

lemma mem_prio_reg_pos : "\<And> r s . 0 < mem_prio_reg r s"
proof-
  fix r s
  show "0 < mem_prio_reg r s"
    by(cases s; auto)
qed

lemma mem_prio_mem_pos : "\<And> s . 0 < mem_prio_mem s"
proof-
  fix s
  show "0 < mem_prio_mem s"
    by(cases s; auto)
qed

lemma mem_valid :
  "lifting_valid_ok mem_lift1 mem_lift1_S"
  unfolding mem_lift1_def mem_lift1_S_def
no_control_lifting_def calc_schemi_def calc_schemo_def schem_lift_defs schem_lift_S_defs
  by(fastforce simp add: mem_prio_reg_pos mem_prio_mem_pos intro: lifting_valid_fast lifting_ortho_fast)

lemma mem_valid_full :
  "lifting_valid_ok mem_lift (no_control_lifting_S mem_lift1 mem_lift1_S)"
  using no_control_l_valid[OF mem_valid]
  unfolding mem_lift_def
  by auto

definition mem_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"mem_sem_l = lift_map_t_s mem_trans mem_lift mem_toggle mem0_sem"

definition imp_sem_lifting_spec where
"imp_sem_lifting_spec = 
  (imp_sem_lifting_gen :: (_, _, (_, (_ :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state) lifting)"

definition imp_sem_l :: "syn \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps})) state" where
"imp_sem_l = lift_map_t_s imp_trans imp_sem_lifting_spec imp_toggle imp_ctl_sem"

definition sem_final :: "syn \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps})) state" where
"sem_final =
  pcomps [calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l]"

definition sems ::
  "(syn \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps})) state \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps})) state) set" where
"sems = {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l}"

(* sems without seq - this is used for certain Hoare facts. *)

definition sems' ::
  "(syn \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps})) state \<Rightarrow> ('s, (_ :: {Okay, Bogus, Mergeableb, Pordps})) state) set" where
"sems' = {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l}"

(* For a rather annoying technical reason we have to show that the other semantics
 * functions aren't equal to the Seq function (this is because we use sets in places
 * to reason about the semantics functions) 
 * Fortunately this is usually not hard to prove, but it feels like there should be
 * a way around it.*)
lemma calc_sem_l_noteq_seq :
  "(calc_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c )) state)) \<noteq>
   (seq_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state))"
proof
  assume H : "(calc_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state)) =
   (seq_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state))"

  have
    "(calc_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state)) (Sc Cadd) \<bottom> =
   (seq_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state))
    (Sc Cadd) \<bottom>"
    using fun_cong[OF fun_cong[OF H, of "Sc Cadd"], of \<bottom>]
    by(auto)
  then show False
    by(auto simp add: seq_sem_l_def calc_sem_l_def bot_defs
lift_map_t_s_def seq_sem_l_gen_def seq_sem_lifting_gen_def lift_map_s_def calc_lift_def no_control_lifting_def
schem_lift_defs lifter_instances)
qed

lemma mem_sem_l_noteq_seq :
  "(mem_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) \<noteq>
   (seq_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state))"
proof
  assume H : 
    "(mem_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) =
      (seq_sem_l ::  (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state))"

  have "(mem_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) Ssk \<bottom> = seq_sem_l Ssk \<bottom>"
    using fun_cong[OF fun_cong[OF H, of "Ssk"], of \<bottom>]
    by(auto)
  then show False
    by(auto simp add: seq_sem_l_def calc_sem_l_def mem_sem_l_def bot_defs
lift_map_t_s_def seq_sem_l_gen_def seq_sem_lifting_gen_def lift_map_s_def calc_lift_def no_control_lifting_def
schem_lift_defs lifter_instances)
qed

lemma cond_sem_l_noteq_seq :
  "(cond_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) \<noteq>
   (seq_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state))"
proof
  assume H : 
    "(cond_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) =
      (seq_sem_l ::  (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state))"

  have "(cond_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) Ssk \<bottom> = seq_sem_l Ssk \<bottom>"
    using fun_cong[OF fun_cong[OF H, of "Ssk"], of \<bottom>]
    by(auto)
  then show False
    by(auto simp add: seq_sem_l_def cond_sem_l_def mem_sem_l_def bot_defs
lift_map_t_s_def seq_sem_l_gen_def seq_sem_lifting_gen_def lift_map_s_def calc_lift_def no_control_lifting_def
schem_lift_defs lifter_instances)
qed

lemma imp_sem_l_noteq_seq :
  "(imp_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) \<noteq>
   (seq_sem_l :: (syn \<Rightarrow> ('s, ('c)) state \<Rightarrow> ('s, ('c)) state))"
proof
  assume H : 
    "(imp_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) =
      (seq_sem_l ::  (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state))"

  have "(imp_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) Ssk \<bottom> = seq_sem_l Ssk \<bottom>"
    using fun_cong[OF fun_cong[OF H, of "Ssk"], of \<bottom>]
    by(auto)
  then show False
    by(auto simp add: seq_sem_l_def imp_sem_l_def calc_sem_l_def mem_sem_l_def bot_defs
lift_map_t_s_def seq_sem_l_gen_def seq_sem_lifting_gen_def lift_map_s_def calc_lift_def no_control_lifting_def
schem_lift_defs lifter_instances)
qed



lemma sems'_eq :
  shows "sems' = sems - {seq_sem_l}"
proof
  show "sems - {seq_sem_l} \<subseteq> sems'"
    unfolding sems_def sems'_def
    by auto
next
  show "sems' \<subseteq> sems - {seq_sem_l}"
    unfolding sems'_def sems_def
    by(auto simp add: imp_sem_l_noteq_seq calc_sem_l_noteq_seq mem_sem_l_noteq_seq cond_sem_l_noteq_seq)
qed

(* Domination facts needed for proof. *)
lemma calc_dom :
  "(calc_sem_l :: (syn \<Rightarrow> ('s, ('c :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) state \<Rightarrow> ('s, ('c)) state)) \<downharpoonleft> sems' { x . (calc_toggle x = True)}"
  unfolding calc_sem_l_def
proof(rule dominant_toggles)
  show "lifting_valid calc_lift 
     (no_control_lifting_S (schem_lift calc_schemi calc_schemo)
       (schem_lift_S calc_schemi calc_schemo))"
    using lifting_valid_ok.axioms[OF calc_valid_full] unfolding calc_lift_def
    by(auto)
next
  show "finite sems'"
    unfolding sems'_def
    by auto
next
  show "lift_map_t_s calc_trans calc_lift calc_toggle calc_sem \<in> sems'"
    unfolding sems'_def
    calc_sem_l_def
    by auto
next
  show "\<And>s. s \<in> {x. calc_toggle x = True} \<Longrightarrow> calc_toggle s"
    by auto
next
  fix f s z
  assume F1 :"f \<in> sems'"
  assume F2 :"f \<noteq> lift_map_t_s calc_trans calc_lift calc_toggle calc_sem"

  have Calc_Mem : "(\<forall>s. calc_toggle s \<longrightarrow> \<not> mem_toggle s)"
  proof
    fix s
    show "calc_toggle s \<longrightarrow> \<not> mem_toggle s"
      by(cases s; auto)
  qed

  have Calc_Imp : "(\<forall>s. calc_toggle s \<longrightarrow> \<not> imp_toggle s)"
  proof
    fix s
    show "calc_toggle s \<longrightarrow> \<not> imp_toggle s"
      by(cases s; auto)
  qed

  have Calc_Cond : "(\<forall>s. calc_toggle s \<longrightarrow> \<not> cond_toggle s)"
  proof
    fix s
    show "calc_toggle s \<longrightarrow> \<not> cond_toggle s"
      by(cases s; auto)
  qed


  show "\<exists>tg g. f = toggle tg g \<and> (\<forall>s. s \<in> {x. calc_toggle x = True} \<longrightarrow> \<not> tg s)"
    using F1 F2 Calc_Mem Calc_Imp Calc_Cond
    unfolding sems'_def calc_sem_l_def mem_sem_l_def cond_sem_l_def imp_sem_l_def
      lift_map_t_s_toggle
    by(auto)
qed

lemma mem_dom :
  "mem_sem_l \<downharpoonleft> sems' { x . (mem_toggle x = True)}"
  unfolding mem_sem_l_def
proof(rule dominant_toggles)
  show "lifting_valid mem_lift (no_control_lifting_S mem_lift1 mem_lift1_S)"
    using lifting_valid_ok.axioms[OF mem_valid_full] 
    by(auto)
next
  show "finite sems'"
    unfolding sems'_def
    by auto
next
  show "lift_map_t_s mem_trans mem_lift mem_toggle mem0_sem \<in> sems'"
    unfolding sems'_def
    mem_sem_l_def
    by auto
next
  show "\<And>s. s \<in> {x. mem_toggle x = True} \<Longrightarrow> mem_toggle s"
    by auto
next
  fix f s z
  assume F1 :"f \<in> sems'"
  assume F2 :"f \<noteq> lift_map_t_s mem_trans mem_lift mem_toggle mem0_sem"

  have Mem_Calc : "(\<forall>s. mem_toggle s \<longrightarrow> \<not> calc_toggle s)"
  proof
    fix s
    show "mem_toggle s \<longrightarrow> \<not> calc_toggle s"
      by(cases s; auto)
  qed

  have Mem_Imp : "(\<forall>s. mem_toggle s \<longrightarrow> \<not> imp_toggle s)"
  proof
    fix s
    show "mem_toggle s \<longrightarrow> \<not> imp_toggle s"
      by(cases s; auto)
  qed

  have Mem_Cond : "(\<forall>s. mem_toggle s \<longrightarrow> \<not> cond_toggle s)"
  proof
    fix s
    show "mem_toggle s \<longrightarrow> \<not> cond_toggle s"
      by(cases s; auto)
  qed


  show "\<exists>tg g. f = toggle tg g \<and> (\<forall>s. s \<in> {x. mem_toggle x = True} \<longrightarrow> \<not> tg s)"
    using F1 F2 Mem_Calc Mem_Imp Mem_Cond
    unfolding sems'_def calc_sem_l_def mem_sem_l_def cond_sem_l_def imp_sem_l_def
      lift_map_t_s_toggle
    by(auto)
qed

lemma cond_dom :
  "cond_sem_l \<downharpoonleft> sems' { x . (cond_toggle x = True)}"
  unfolding cond_sem_l_def
proof(rule dominant_toggles)
  show "lifting_valid cond_lift (no_control_lifting_S (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX)))
  (schem_lift_S (SP NA NB) (SP (SPRC cond_prio (SO NA))
                     (SP (SPRI (SO NB)) NX))))"
    using lifting_valid_ok.axioms[OF cond_valid_full] 
    by(auto)
next
  show "finite sems'"
    unfolding sems'_def
    by auto
next
  show "lift_map_t_s cond_trans cond_lift cond_toggle cond_sem \<in> sems'"
    unfolding sems'_def
    cond_sem_l_def
    by auto
next
  show "\<And>s. s \<in> {x. cond_toggle x = True} \<Longrightarrow> cond_toggle s"
    by auto
next
  fix f s z
  assume F1 :"f \<in> sems'"
  assume F2 :"f \<noteq> lift_map_t_s cond_trans cond_lift cond_toggle cond_sem"

  have Cond_Calc : "(\<forall>s. cond_toggle s \<longrightarrow> \<not> calc_toggle s)"
  proof
    fix s
    show "cond_toggle s \<longrightarrow> \<not> calc_toggle s"
      by(cases s; auto)
  qed

  have Cond_Imp : "(\<forall>s. cond_toggle s \<longrightarrow> \<not> imp_toggle s)"
  proof
    fix s
    show "cond_toggle s \<longrightarrow> \<not> imp_toggle s"
      by(cases s; auto)
  qed

  have Cond_Mem : "(\<forall>s. cond_toggle s \<longrightarrow> \<not> mem_toggle s)"
  proof
    fix s
    show "cond_toggle s \<longrightarrow> \<not> mem_toggle s"
      by(cases s; auto)
  qed

  show "\<exists>tg g. f = toggle tg g \<and> (\<forall>s. s \<in> {x. cond_toggle x = True} \<longrightarrow> \<not> tg s)"
    using F1 F2 Cond_Calc Cond_Imp Cond_Mem
    unfolding sems'_def calc_sem_l_def mem_sem_l_def cond_sem_l_def imp_sem_l_def
      lift_map_t_s_toggle
    by(auto)
qed
    
lemma imp_dom :
  "imp_sem_l \<downharpoonleft> sems' { x . (imp_toggle x = True)}"
  unfolding imp_sem_l_def
proof(rule dominant_toggles)
  show "lifting_valid imp_sem_lifting_spec
         (schem_lift_S (SP NA NB)
             (SP (SPRC imp_prio (SO NA)) (SP NX (SP (SPRI (SO NB)) NX))))"
    using lifting_valid_ok.axioms[OF imp_sem_lifting_gen_valid2] 
    unfolding imp_sem_lifting_gen_def imp_sem_lifting_spec_def
    by(auto)
next
  show "finite sems'"
    unfolding sems'_def
    by auto
next
  show "lift_map_t_s imp_trans imp_sem_lifting_spec imp_toggle imp_ctl_sem \<in> sems'"
    unfolding sems'_def
    imp_sem_l_def
    by auto
next
  show "\<And>s. s \<in> {x. imp_toggle x = True} \<Longrightarrow> imp_toggle s"
    by auto
next
  fix f s z
  assume F1 :"f \<in> sems'"
  assume F2 :"f \<noteq> lift_map_t_s imp_trans imp_sem_lifting_spec imp_toggle imp_ctl_sem"

  have Imp_Calc : "(\<forall>s. imp_toggle s \<longrightarrow> \<not> calc_toggle s)"
  proof
    fix s
    show "imp_toggle s \<longrightarrow> \<not> calc_toggle s"
      by(cases s; auto)
  qed

  have Imp_Cond : "(\<forall>s. imp_toggle s \<longrightarrow> \<not> cond_toggle s)"
  proof
    fix s
    show "imp_toggle s \<longrightarrow> \<not> cond_toggle s"
      by(cases s; auto)
  qed

  have Imp_Mem : "(\<forall>s. imp_toggle s \<longrightarrow> \<not> mem_toggle s)"
  proof
    fix s
    show "imp_toggle s \<longrightarrow> \<not> mem_toggle s"
      by(cases s; auto)
  qed


  show "\<exists>tg g. f = toggle tg g \<and> (\<forall>s. s \<in> {x. imp_toggle x = True} \<longrightarrow> \<not> tg s)"
    using F1 F2 Imp_Calc Imp_Cond Imp_Mem
    unfolding sems'_def calc_sem_l_def mem_sem_l_def cond_sem_l_def imp_sem_l_def
      lift_map_t_s_toggle
    by(auto)
qed

lemma seq_sem_lifting_gen_valid'' :
  "lifting_valid_ok (seq_sem_lifting_gen :: (Seq.syn, 'x state', ('x, _ :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all}) control) lifting) 
                  (schem_lift_S seq_sem_lifting_schem1 seq_sem_lifting_schem2)" unfolding seq_sem_lifting_gen_def seq_sem_lifting_schem1_def seq_sem_lifting_schem2_def
  unfolding seq_sem_lifting'_def schem_lift_defs schem_lift_S_defs
  by(fastforce intro: lifting_valid_fast)

lemma seq_dom :
  "((seq_sem_l :: (syn \<Rightarrow> ('s, _ ::{Okay, Bogus, Mergeableb, Pordps, Pordc_all}) state \<Rightarrow> ('s, _) state)) \<downharpoonleft> sems { Ss Sseq})"
  unfolding seq_sem_l_def seq_sem_l_gen_def
proof(rule dominant_toggle_others)
  show "lifting_valid 
    (seq_sem_lifting_gen ::
    (Seq.syn, 'x state', ('x, (_  :: {Okay, Bogus, Mergeableb, Pordps, Pordc_all})) control) lifting)
    (schem_lift_S seq_sem_lifting_schem1 seq_sem_lifting_schem2)"
    using lifting_valid_ok.axioms(1)[OF seq_sem_lifting_gen_valid'']
    unfolding seq_sem_lifting_gen_def 
    by(auto)
next
  show "finite sems"
    unfolding sems_def
    by auto
next
  show "lift_map_s seq_trans seq_sem_lifting_gen seq_sem \<in> sems"
    unfolding sems_def
    seq_sem_l_gen_def seq_sem_l_def
    by auto
next
  show "\<And>s. s \<in> {Ss Sseq} \<Longrightarrow> (\<lambda> x . x = (Ss Sseq)) s"
    by auto
next
  fix f s z
  assume F1 :"f \<in> sems"
  assume F2 :"f \<noteq> lift_map_s seq_trans seq_sem_lifting_gen seq_sem"

  have Seq_Calc : "(\<forall>s. s = Ss Sseq \<longrightarrow> \<not> calc_toggle s)"
  proof
    fix s
    show "s = Ss Sseq \<longrightarrow> \<not> calc_toggle s"
      by(cases s; auto)
  qed

  have Seq_Cond : "(\<forall>s. s = Ss Sseq \<longrightarrow> \<not> cond_toggle s)"
  proof
    fix s
    show "s = Ss Sseq  \<longrightarrow> \<not> cond_toggle s"
      by(cases s; auto)
  qed

  have Seq_Mem : "(\<forall>s. s = Ss Sseq \<longrightarrow> \<not> mem_toggle s)"
  proof
    fix s
    show "s = Ss Sseq \<longrightarrow> \<not> mem_toggle s"
      by(cases s; auto)
  qed

  have Seq_Imp : "(\<forall>s. s = Ss Sseq \<longrightarrow> \<not> imp_toggle s)"
  proof
    fix s
    show "s = Ss Sseq \<longrightarrow> \<not> imp_toggle s"
      by(cases s; auto)
  qed

  show "\<exists>tg g. f = toggle tg g \<and> (\<forall>s. s \<in> {Ss Sseq} \<longrightarrow> \<not> tg s)"
    using F1 F2 Seq_Calc Seq_Cond Seq_Mem
    unfolding sems_def sems'_def calc_sem_l_def mem_sem_l_def cond_sem_l_def imp_sem_l_def
      lift_map_t_s_toggle seq_sem_l_def seq_sem_l_gen_def
    by(auto)
qed


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