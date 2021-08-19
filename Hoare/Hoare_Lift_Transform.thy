theory Hoare_Lift_Transform
imports Hoare_Lift
begin

(* Alternative approach to Hoare lifting:
transforming predicate transformers. *)

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
   ('a1, 'a2, 'b2 :: {Pord, Okay}, 'z) lifting_scheme \<Rightarrow>
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