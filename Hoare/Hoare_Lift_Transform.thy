theory Hoare_Lift_Transform
imports Hoare_Lift
begin

(* Alternative approach to Hoare lifting:
transforming predicate transformers. *)
(* TODO: this probably is no longer needed *)
(*
  assume
  {P} c {Q(P, c)}

  want to derive
  {Pbig} lift(c) {Qbig(P, c)} where
  
idea:
  Pbig \<rightarrow> (\ st . exists rest . Pbig (st + rest))
*)

definition liftt_conc ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: {Pord, Okay}) lifting \<Rightarrow>
   'b1 \<Rightarrow>
   (('a2 \<Rightarrow> bool) \<Rightarrow> ('a2 \<Rightarrow> bool)) \<Rightarrow>
   (('b2 \<Rightarrow> bool) \<Rightarrow> ('b2 \<Rightarrow> bool))" where
"liftt_conc sl l syn Q1 P2 st_big =
  (\<exists> old st_small . st_big = LUpd l (sl syn) st_small old \<and>
   P2 old \<and>
   Q1 (\<lambda> st . \<exists> full . LOut l (sl syn) full = st \<and> P2 full) st_small)"

lemma liftt_conc_spec :
  assumes Valid : "lifting_valid l S"
  assumes V : "\<And> P . (sem) % {{P}} x {{(Q P)}}"
  assumes Syn : "l' x' = x"
  shows "\<And> P' . (lift_map_s l' l sem) % {{P'}} x' {{liftt_conc l' l x' Q P'}}"
  using V Syn
  unfolding HTS_def HT_def liftt_conc_def lift_map_s_def 
  apply(auto)
  apply(rule_tac x = a in exI)
  apply(rule_tac x = "(sem (l' x') (LOut l (l' x') a))" in exI)
  apply(auto)
  apply(atomize)
  apply(drule_tac x = "(\<lambda>st. \<exists>full. LOut l (l' x') full = st \<and> P' full)" in spec)
  apply(auto)
  done
term "LOut"

  (* new idea: a more streamlined version. *)
(* TODO: give this a better name *)
(* TODO: do we need Hok? *)
lemma new_lift :
  fixes P' :: "_ \<Rightarrow> bool"
  assumes HP : "\<And> st . P st \<Longrightarrow> P' (LOut l x st)"
  assumes HOk : "\<And> st . P st \<Longrightarrow> st \<in> ok_S"
  assumes HV : "lifting_valid_ok_ext l S"
  assumes Hsyn : "l' x' = x"
  assumes HT : "sem % {{P'}} x {{Q'}}"
  shows "(lift_map_s l' l sem) % 
    {{P}} x' 
    {{(\<lambda> st . \<exists> old_big small_new . P old_big \<and> Q' small_new \<and> st = LUpd l x small_new old_big \<and> st \<in> ok_S)}}"
proof(rule HTSI)
  fix a
  assume H : "P a"

  then have H' : "P' (LOut l x a)"
    using HP
    by blast

  have Q' : "Q' (sem x (LOut l x a))"
    using HTSE[OF HT H']
    by auto

  interpret V : lifting_valid_ok_ext l S
    using HV.

  have Ok' : "LUpd l x (sem x (LOut l x a)) a \<in> ok_S"
    using V.ok_S_put[OF HOk[OF H]]
    by auto

  show " \<exists>old_big small_new.
            P old_big \<and>
            Q' small_new \<and>
            lift_map_s l' l sem x' a = LUpd l x small_new old_big \<and>
            lift_map_s l' l sem x' a \<in> ok_S"
    unfolding lift_map_s_def Hsyn LMap_def
    using H Q' Ok'
    by blast
qed


(*
definition liftt_pred_validx_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: {Pord, Okay}, 'z) lifting_scheme \<Rightarrow>
   ('a1 \<Rightarrow> 'b2 set) \<Rightarrow>
   'b1 \<Rightarrow>
   ('a2 \<Rightarrow> bool) \<Rightarrow>
   ('b2 \<Rightarrow> bool)"
*)

end