theory Calc_Mem_Imp imports (*Calc_Mem*)
 "../../Language_Components/Cond/Cond" 
 "../../Language_Components/Calc/Calc"
  "../../Language_Components/Mem/Mem_Simple"
              "../../Language_Components/Imp_Ctl/Imp_Ctl" 
             "../../Language_Components/Seq/Seq" 
"../../Hoare/Hoare_Step"
"../../Composition/Dominant_Instances"
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

fun mem_trans :: "syn \<Rightarrow> Mem_Simple.syn" where
"mem_trans (Sm m) = m"
| "mem_trans _ = Mem_Simple.Sskip"

(* mem_prio not needed, handled by custom implementation (?still true?) *)

fun cond_trans :: "syn \<Rightarrow> Cond.cond" where
"cond_trans (Sb x) = x"
| "cond_trans _ = Sskip_cond"

fun cond_prio :: "Cond.cond \<Rightarrow> nat" where
"cond_prio (Sskip_cond) = 1"
| "cond_prio _ = 2"

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
(*
definition calc_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"calc_sem_l =
  lift_map_s calc_trans
  (schem_lift
    (SP NA (SP NB NC))
    (SP NX (SP NX (SP (SPRI (SO NC)) (SP (SPRI (SO NB)) (SP (SPRI (SO NA)) NX))))))
  calc_sem"
*)

(*
('a::type, 'b::{Bogus,Pord},
       int md_triv option md_prio \<times>
       int md_triv option md_prio \<times>
       int md_triv option md_prio \<times>
       int md_triv option md_prio \<times>
       (String.literal,
        int md_triv option md_prio) oalist \<times>
       'c::{Bogus,Pord}) lifting
*)

definition baseline_l where
"baseline_l =
  schem_lift (SP NA (SP NB (SP NC (SP ND (SP NE (SP NF (SP NG NH)))))))
  (SP (SPRI (SO NA)) (SP (SPRI (SO NB)) (SP (SPRI (SO NC)) (SP (SPRI (SO ND)) (SP (SPRI (SO NE)) 
    (SP (SPRI (SO NF)) (SP (SPRI (SO NG)) (SID NH))))))))"

definition baseline_f where
"baseline_f =
  LMap baseline_l (\<lambda> _ . id)"

term "baseline_f id"
term "no_control_lifting (schem_lift (SP NA (SP NB NC)) (SP (SPRI (SO NC)) (SP (SPRI (SO NB)) (SP (SPRI (SO NA)) NX ))))"
term "no_control_lifting"

term "(SP NA (SP NB NC))"
term "(SP NX (SP (SPRC calc_prio (SO NC)) (SP (SPRK (SO NA)) (SP (SPRK (SO NB)) NX ))))"

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

definition calc_lift :: "(Calc.calc, Calc.calc_state, ('s, 'x :: {Bogus, Pord, Mergeableb, Okay}) Mem_Simple.state) lifting" where
"calc_lift = 
  no_control_lifting (schem_lift calc_schemi calc_schemo)"

term "(schem_lift calc_schemi calc_schemo)"

definition with_baseline :: 
  "(syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state) \<Rightarrow>
   (syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state)" where
"with_baseline f syn st =
  [^f syn st, baseline_f syn st^]"

(* TODO: priority stuff is all wrong here. *)
(* concretize our schem_lift at an appropriate type. *)
term "lift_map_s"
definition calc_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"calc_sem_l =
 lift_map_s calc_trans calc_lift
calc_sem"
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
  lift_map_s cond_trans
    cond_lift
  cond_sem
"

definition imp_sem_l :: "syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state" where
"imp_sem_l = imp_sem_l_gen imp_trans"

definition seq_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"seq_sem_l = seq_sem_l_gen seq_trans"

definition mem_lift where
"mem_lift = no_control_lifting mem_lift1"

definition mem_sem_l :: "syn \<Rightarrow> ('s, _) state \<Rightarrow> ('s, _) state" where
"mem_sem_l = lift_map_s mem_trans mem_lift mem0_sem"

definition sem_final :: "syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state" where
"sem_final =
  pcomps [with_baseline calc_sem_l, with_baseline mem_sem_l, with_baseline cond_sem_l, with_baseline imp_sem_l, with_baseline seq_sem_l]"

definition sems ::
  "(syn \<Rightarrow> ('s, (_ :: Pordc_all)) state \<Rightarrow> ('s, (_ :: Pordc_all)) state) set" where
"sems = {calc_sem_l, mem_sem_l, cond_sem_l, imp_sem_l, seq_sem_l}"

(* Domination facts needed for proof. *)
(* TODO: need to include syntax translation in dominant2 *)
(* Hmm... does calc dominate mem here actually? *)
(* Merge vs merge. *)
(* maybe we can just compute these...
 * will be annoying, but should work.
 * might be easier than dealing with the details of
 * using automation to construct proofs out of the locale instances.
 *)
(* YOU ARE HERE
 * i think the problem is with the skip case of calc. we would need to know that it isn't that case
 * that still doesn't answer why mem would be greater though...? *)
(*
lemma calc_dom_mem :
  "dominant2 calc_lift calc_trans mem_lift mem_trans { x . case x of (Sc _) \<Rightarrow> True | _ \<Rightarrow> False}"
proof(rule dominant2.intro)
  fix a1 a2 x
  fix b :: "(_, (_ :: {Okay, Mergeableb, Bogus})) state"
  term "b"
  term "LUpd mem_lift"
  assume X: "x \<in> {x. case x of Calc_Mem_Imp.syn.Sc x \<Rightarrow> True
                | _ \<Rightarrow> False}"
  assume B_ok : "b \<in> ok_S"
  then show
    "LUpd mem_lift (Calc_Mem_Imp.mem_trans x) a2 b <[
       LUpd calc_lift (Calc_Mem_Imp.calc_trans x) a1 b" using X
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs
  apply(auto simp add: schem_lift_defs lifter_instances
  prod_ok_S prio_ok_S option_ok_S triv_ok_S
prod_pleq leq_refl
 split: prod.splits md_prio.splits syn.splits option.splits)
*)

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


(*
proof(rule dominant2.intro)
  fix a1 a2 x
  fix b :: "(_, (_ :: {Okay, Mergeableb, Bogus})) state"
  term "b"
  term "LUpd mem_lift"
  assume X: "x \<in> {x. case x of Calc_Mem_Imp.syn.Sc x \<Rightarrow> True
                | _ \<Rightarrow> False}"
  assume B_ok : "b \<in> ok_S"
  then show
    "LUpd mem_lift (Calc_Mem_Imp.mem_trans x) a2 b <[
       LUpd calc_lift (Calc_Mem_Imp.calc_trans x) a1 b" using X
  unfolding calc_lift_def calc_schemi_def calc_schemo_def
            mem_lift_def mem_lift1_def no_control_lifting_def schem_lift_defs
  apply(auto simp add: schem_lift_defs lifter_instances
  prod_ok_S prio_ok_S option_ok_S triv_ok_S
prod_pleq leq_refl
*)

(*
  apply(simp)
  apply(rule dominant2_snd.ax)
  apply(rule dominant2_snd.intro)
  apply(rule dominant2_snd.ax)
  apply(rule dominant2_snd.intro)
  apply(rule dominant2_merge_left.ax)
  apply(rule dominant2_merge_left.intro)
*)
proof
  fix 

lemma calc_sem_dom_calc :
  "calc_sem_l \<downharpoonleft> sems { x . case x of (Sc _) \<Rightarrow> True | _ \<Rightarrow> False}"

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