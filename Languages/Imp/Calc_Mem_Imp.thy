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

term "no_control_lifting"

(* need no_control_lifting_S *)
definition calc_lift :: "(Calc.calc, Calc.calc_state, ('s, 'x :: {Bogus, Pord, Mergeableb, Okay, Pordps}) Mem_Simple.state) lifting" where
"calc_lift = 
  no_control_lifting (schem_lift calc_schemi calc_schemo)"

definition calc_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"calc_sem_l =
 lift_map_t_s calc_trans calc_lift calc_toggle
calc_sem"

term "calc_sem_l"
term "calc_lift"

term "schem_lift_S calc_schemi calc_schemo"


(* something is wrong here. for some reason in the case of this merge
 * we end up having to prove that two non-equal (at least, not obviously equal)
 * valid sets are indeed equal.
 * Either the automation is making a poor choice w/r/t existential variables,
 * or something about this apporach to calculating valid sets (especially when
 * merging fst and snd) is broken 
 *)


lemma calc_valid :
  "lifting_valid_ok calc_lift (schem_lift_S calc_schemi calc_schemo)"
  unfolding calc_lift_def schem_lift_defs schem_lift_S_defs
no_control_lifting_def calc_schemi_def calc_schemo_def 
  apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom base_bot)
  apply(rule lifting_valid_ok.intro)
   apply(rule lifting_valid.intro)
  apply(rule snd_l_valid_weak.ax_g)
     apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
  apply(rule snd_l_valid_weak.intro)
      apply(rule snd_l_valid_weak.ax_g)
  apply(rule snd_l_valid_weak.intro)
       apply(rule merge_l_valid_weak.ax_g)
              apply(fastforce intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
       apply(rule refl)
  apply(auto simp add: lifter_S_instances)
  apply(simp add: option_l_S_def)
     apply(auto intro: lifting_valid_noaxiom lifting_ortho_noaxiom)
      apply(rule merge_l_valid_weak.intro)
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

(*
definition mem_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"mem_sem_l = 
  lift_map_s mem_trans
    id_l
  mem_sem"
*)
definition cond_lift where
"cond_lift = 
  no_control_lifting (schem_lift (SP NA NB) (SP (SPRC cond_prio (SO NA)) 
                     (SP (SPRI (SO NB)) NX)))"

definition cond_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"cond_sem_l =
  lift_map_t_s cond_trans
    cond_lift cond_toggle
  cond_sem
"

(*
definition imp_sem_l :: "syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state" where
"imp_sem_l = imp_sem_l_gen imp_trans"
*)

definition imp_sem_l :: "syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state" where
"imp_sem_l = lift_map_t_s imp_trans imp_sem_lifting_gen imp_toggle imp_ctl_sem"

definition seq_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"seq_sem_l = seq_sem_l_gen seq_trans"

definition mem_lift where
"mem_lift = no_control_lifting mem_lift1"

definition mem_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"mem_sem_l = lift_map_t_s mem_trans mem_lift mem_toggle mem0_sem"

definition sem_final :: "syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state" where
"sem_final =
  pcomps [calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l]"

definition sems ::
  "(syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state) set" where
"sems = {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l}"

(* sems without seq - this is used for certain Hoare facts. *)

definition sems' ::
  "(syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state) set" where
"sems' = {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l}"

(* Domination facts needed for proof. *)
(* TODO: need to include syntax translation in dominant2 *)
lemma calc_dom :
  "calc_sem_l \<downharpoonleft> sems' { x . (calc_toggle x = True)}"
  unfolding calc_sem_l_def
proof(rule dominant_toggles)


lemma calc_dom_mem :
  "(with_baseline calc_sem_l) \<downharpoonleft> {with_baseline mem_sem_l, with_baseline calc_sem_l} { x . case x of (Sc _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sc x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "
           is_sup
            ((\<lambda>g. g x b) `
             {with_baseline mem_sem_l,
              with_baseline calc_sem_l})
            (with_baseline calc_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline mem_sem_l x b <[
    with_baseline calc_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def baseline_l_def baseline_f_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits)
    by(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs
split: option.splits md_triv.splits prod.splits)
qed
qed

lemma calc_dom_cond :
  "(with_baseline calc_sem_l) \<downharpoonleft> {with_baseline cond_sem_l, with_baseline calc_sem_l} { x . case x of (Sc _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sc x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline cond_sem_l,
              with_baseline calc_sem_l})
            (with_baseline calc_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline cond_sem_l x b <[
    with_baseline calc_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits)
  by(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs
split: option.splits md_triv.splits prod.splits)
qed
qed


lemma calc_dom_imp :
  "(with_baseline calc_sem_l) \<downharpoonleft> {with_baseline imp_sem_l, with_baseline calc_sem_l} { x . case x of (Sc _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay, Pordc_all})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sc x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline imp_sem_l,
              with_baseline calc_sem_l})
            (with_baseline calc_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline imp_sem_l x b <[
    with_baseline calc_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  by(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits 
)

qed
qed
(*
lemma calc_dom_seq :
  "(with_baseline calc_sem_l) \<downharpoonleft> {with_baseline seq_sem_l, with_baseline calc_sem_l} { x . case x of (Sc _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sc x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline seq_sem_l,
              with_baseline calc_sem_l})
            (with_baseline calc_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline seq_sem_l x b <[
    with_baseline calc_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits 
)
*)

lemma mem_dom_calc :
  "(with_baseline mem_sem_l) \<downharpoonleft> {with_baseline calc_sem_l, with_baseline mem_sem_l} { x . case x of (Sm _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sm x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline calc_sem_l,
              with_baseline mem_sem_l})
            (with_baseline mem_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline calc_sem_l x b <[
    with_baseline mem_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma mem_dom_cond :
  "(with_baseline mem_sem_l) \<downharpoonleft> {with_baseline cond_sem_l, with_baseline mem_sem_l} { x . case x of (Sm _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sm x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline cond_sem_l,
              with_baseline mem_sem_l})
            (with_baseline mem_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline cond_sem_l x b <[
    with_baseline mem_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma mem_dom_imp :
  "(with_baseline mem_sem_l) \<downharpoonleft> {with_baseline imp_sem_l, with_baseline mem_sem_l} { x . case x of (Sm _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay, Pordc_all})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sm x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline imp_sem_l,
              with_baseline mem_sem_l})
            (with_baseline mem_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline imp_sem_l x b <[
    with_baseline mem_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma cond_dom_calc :
  "(with_baseline cond_sem_l) \<downharpoonleft> {with_baseline calc_sem_l, with_baseline cond_sem_l} { x . case x of (Sb _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sb x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline calc_sem_l,
              with_baseline cond_sem_l})
            (with_baseline cond_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline calc_sem_l x b <[
    with_baseline cond_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma cond_dom_mem :
  "(with_baseline cond_sem_l) \<downharpoonleft> {with_baseline mem_sem_l, with_baseline cond_sem_l} { x . case x of (Sb _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sb x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline mem_sem_l,
              with_baseline cond_sem_l})
            (with_baseline cond_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline mem_sem_l x b <[
    with_baseline cond_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma cond_dom_imp :
  "(with_baseline cond_sem_l) \<downharpoonleft> {with_baseline imp_sem_l, with_baseline cond_sem_l} { x . case x of (Sb _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay, Pordc_all})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Sb x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline imp_sem_l,
              with_baseline cond_sem_l})
            (with_baseline cond_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline imp_sem_l x b <[
    with_baseline cond_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma imp_dom_calc :
  "(with_baseline imp_sem_l) \<downharpoonleft> {with_baseline calc_sem_l, with_baseline imp_sem_l} { x . case x of (Si _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay, Pordc_all})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Si x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline calc_sem_l,
              with_baseline imp_sem_l})
            (with_baseline imp_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline calc_sem_l x b <[
    with_baseline imp_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed

lemma imp_dom_mem :
  "(with_baseline imp_sem_l) \<downharpoonleft> {with_baseline mem_sem_l, with_baseline imp_sem_l} { x . case x of (Si _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay, Pordc_all})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Si x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline mem_sem_l,
              with_baseline imp_sem_l})
            (with_baseline imp_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline mem_sem_l x b <[
    with_baseline imp_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
qed


lemma imp_dom_cond :
  "(with_baseline imp_sem_l) \<downharpoonleft> {with_baseline cond_sem_l, with_baseline imp_sem_l} { x . case x of (Si _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof
  fix b :: "(_, (_ :: {Bogus, Mergeableb, Okay, Pordc_all})) state"
  fix x
  assume Xin : "x \<in> {x. case x of Si x \<Rightarrow> True
                   | _ \<Rightarrow> False} "
  assume Bin : "b \<in> ok_S"
  show "is_sup
            ((\<lambda>g. g x b) `
             {with_baseline cond_sem_l,
              with_baseline imp_sem_l})
            (with_baseline imp_sem_l x b)"
  proof(simp; rule is_sup_pair)
    show "with_baseline cond_sem_l x b <[
    with_baseline imp_sem_l x b"
      using Xin Bin
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs with_baseline_def
mem_sem_l_def calc_sem_l_def cond_sem_l_def baseline_l_def baseline_f_def cond_lift_def cond_sem_def
imp_sem_l_def imp_sem_l_gen_def lift_map_s_def imp_ctl_sem_def get_cond_def imp_sem_lifting_gen_def
seq_sem_l_def seq_sem_l_gen_def seq_sem_lifting_gen_def
       apply(auto split: prod.splits md_prio.splits option.splits syn.splits md_triv.splits list.splits)
  apply(auto simp add: schem_lift_defs lifter_instances
    prod_ok_S prio_ok_S option_ok_S triv_ok_S
  prio_pleq triv_pleq
  prod_pleq leq_refl lift_map_s_def option_pleq
  prod_bsup prio_bsup option_bsup triv_bsup schem_lift_defs imp_prio_def
split: option.splits md_triv.splits prod.splits list.splits )
  done
qed
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