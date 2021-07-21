theory Calc_Mem_Hoare
  imports Calc Calc_Mem "../../Hoare/Hoare_Direct" "../../Hoare/Hoare_Lift" "../../Lifter/Auto_Lifter_Proofs"

begin

(* Hoare rule for Calc_Mem (integrated, for now - should be possible to explore
 * separate Calc and Mem rules and composing them - TODO)
 *)

lemma HCalc_calc :
  assumes Hc : "c \<noteq> Cskip"
  shows "Calc.calc_sem % {{P1}} c
                         {{(\<lambda> st . case st of
                              (x1, x2, x3) \<Rightarrow> 
                              (\<exists> x3' . P1 (x1, x2, x3')) \<and>
                              (\<forall> x3' . calc_sem c (x1, x2, x3') = st))}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "case calc_sem c a of (x1, x2, x3) \<Rightarrow> (\<exists>x3'. P1 (x1, x2, x3')) \<and> (\<forall>x3'. calc_sem c (x1, x2, x3') = calc_sem c a)"
    using Hc H
    by(cases c; cases a; auto simp add: split: prod.splits)
qed

lemma HCalc_skip :
  shows "Calc.calc_sem % {{P1}} Cskip
                         {{P1}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "P1 (calc_sem Cskip a)"
    using H
    by(cases a; auto simp add: split: prod.splits)
qed


lemma HMem0_lit :
  shows "mem0_sem % {{P1}} Slit s i
                    {{(\<lambda> st . case st of (x1, x2) \<Rightarrow> (\<exists> x2' . P1 (x1, x2')) \<and> x2 = i)}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"
  show "case mem0_sem (Slit s i) a of (x1, x2) \<Rightarrow> (\<exists>x2'. P1 (x1, x2')) \<and> x2 = i" using H
    by(cases a; auto)
qed

lemma HMem0_copy :
  shows "mem0_sem % {{P1}} Scopy s1 s2
                    {{(\<lambda> st . case st of (x1, x2) \<Rightarrow> (\<exists> x2' . P1 (x1, x2')) \<and> x2 = x1)}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"
  show "case mem0_sem (Scopy s1 s2) a of (x1, x2) \<Rightarrow> (\<exists>x2'. P1 (x1, x2')) \<and> x2 = x1" using H
    by(cases a; auto)
qed

lemma HMem0_skip :
  shows "mem0_sem % {{P1}} Mem.Sskip
                    {{P1}}"
proof(rule HTSI)
  fix a
  assume H : "P1 a"

  show "P1 (mem0_sem Sskip a)"
    using H
    by(cases a; auto simp add: split: prod.splits)
qed

term "(schem_lift (SP NA NB)
                (SM (SL mem_key_src (SPRI (SO NA)))
                    (SL mem_key_dest (SPRIN 2 (SO NB)))))"  

lemma Mem_lift_valid :
  shows "lifting_valid (schem_lift (SP NA NB)
                (SM (SL mem_key_src (SPRI (SO NA)))
                    (SL mem_key_dest (SPRIN 2 (SO NB)))) :: (Mem.syn, Mem.state0, Mem.state) lifting) 
(\<lambda> syn . 
  (case syn of
    Slit s i \<Rightarrow> UNIV
    | Scopy s1 s2 \<Rightarrow> {st . (\<exists> s1v s1p . get st s1  = Some (mdp s1p (Some (mdt s1v))))}
    | _ \<Rightarrow> UNIV))"
proof(rule lifting_validI)
  fix s :: "Mem.syn" 
  fix a :: "(int * int)"
  fix b :: "Mem.state"
  show "LOut (schem_lift (SP NA NB) (SM (SL mem_key_src (SPRI (SO NA))) (SL mem_key_dest (SPRC (\<lambda>_. 2) (SO NB))))) s
        (LUpd (schem_lift (SP NA NB) (SM (SL mem_key_src (SPRI (SO NA))) (SL mem_key_dest (SPRC (\<lambda>_. 2) (SO NB))))) s a b) =
       a"
    apply(cases a; auto simp add: schem_lift_defs merge_l_def oalist_l_def prio_l_def option_l_def triv_l_def)
    apply(cases "mem_key_src s"; auto)
    apply(cases s; auto simp add: schem_lift_defs merge_l_def oalist_l_def prio_l_def option_l_def triv_l_def)



lemma HMem_lit : 
  shows "Mem.mem_sem % {{P1}} (Slit s i)
                       {{(\<lambda> st . 
                          \<exists> st0 . P1 st0 \<and> st = update s i st0)}}"

lemma HMem_copy : 
  shows "Mem.mem_sem % {{P1}} c
                       {{(\<lambda> st . True)}}"

lemma HMem_skip : 
  shows "Mem.mem_sem % {{P1}} c
                       {{(\<lambda> st . True)}}"



(* separate calc + mem rules, then merge (?). *)

(* issue - need to deal with the fact that we might get default values back
 * when things are not initialized. *)
lemma HCalc_Mem_Calc :
  shows "Calc_Mem.sem_final % {{P1}} (Sc calci s1 s2 s3) 
                              {{(\<lambda> st . \<forall> v1 v2 v3 p1 p2 p3 . 
                                (get st s1 = Some (mdp p1 (Some (mdt v1))) \<longrightarrow>
                                (get st s2 = Some (mdp p2 (Some (mdt v2)))) \<longrightarrow>
                                (get st s3 = Some (mdp p3 (Some (mdt v3)))) \<longrightarrow>
                                ((\<forall> orig' . calc_sem calci (v1, v2, orig') = (v1, v2, v3))) \<and>
                                 (\<exists> orig . P1 (update s3 orig st) \<or> P1 (delete s3 st)))) }}"
proof(rule HTSI)
  fix st
  assume H: "P1 st"

  show "\<forall>v1 v2 v3 p1 p2 p3.
            get (sem_final (Sc calci s1 s2 s3) st) s1 = Some (mdp p1 (Some (mdt v1))) \<longrightarrow>
            get (sem_final (Sc calci s1 s2 s3) st) s2 = Some (mdp p2 (Some (mdt v2))) \<longrightarrow>
            get (sem_final (Sc calci s1 s2 s3) st) s3 = Some (mdp p3 (Some (mdt v3))) \<longrightarrow>
            (\<forall>orig'. calc_sem calci (v1, v2, orig') = (v1, v2, v3)) \<and>
            (\<exists>orig. P1 (update s3 orig (sem_final (Sc calci s1 s2 s3) st)) \<or> P1 (delete s3 (sem_final (Sc calci s1 s2 s3) st)))"
  proof(step+)
    fix v1 v2 v3 p1 p2 p3 orig'

    assume Get1 : "get (sem_final (Sc calci s1 s2 s3) st) s1 = Some (mdp p1 (Some (mdt v1)))"
    assume Get2 : "get (sem_final (Sc calci s1 s2 s3) st) s2 = Some (mdp p2 (Some (mdt v2)))"
    assume Get3 : "get (sem_final (Sc calci s1 s2 s3) st) s3 = Some (mdp p3 (Some (mdt v3)))"

    obtain r1 where Get1' : "get st s1 = Some r1" sorry
    obtain r2 where Get2' : "get st s2 = Some r2" sorry
    obtain r3 where Get3' : "get st s3 = Some r3" sorry

    show "calc_sem calci (v1, v2, orig') = (v1, v2, v3)" using Get1 Get2 Get3
      
      apply(auto simp add: sem_final_def calc_sem_l_def mem_sem_l_def
schem_lift_defs calc_key_lift_def merge_l_def oalist_l_def prio_l_def
prod_bsup option_bsup bsup_oalist
split: prod.splits
)
      apply(auto simp add: Get1' Get2' Get3' get_update)
    

  show "\<exists>v1 v2 v3 p1 p2 p3.
            (get (sem_final (Sc calci s1 s2 s3) a) s1 = Some (mdp p1 (Some (mdt v1))) \<and>
             get (sem_final (Sc calci s1 s2 s3) a) s2 = Some (mdp p2 (Some (mdt v2))) \<and>
             get (sem_final (Sc calci s1 s2 s3) a) s3 = Some (mdp p3 (Some (mdt v3))) \<and> 
             (\<forall>orig'. calc_sem calci (v1, v2, orig') = (v1, v2, v3))) \<and>
            (\<exists>orig. P1 (update s3 orig (sem_final (Sc calci s1 s2 s3) a)) \<or>
                    P1 (delete s3 (sem_final (Sc calci s1 s2 s3) a)))"


    apply(auto simp add: calc_sem_l_def schem_lift_defs calc_key_lift_def merge_l_def oalist_l_def
        )

end
