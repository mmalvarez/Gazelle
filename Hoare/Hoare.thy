theory Hoare imports "../Lifting/LiftUtils" "../Lifting/LangCompSimple"
begin

(*
datatype 'a triple =
  T "('a \<Rightarrow> bool)" "('a \<Rightarrow> 'a \<Rightarrow> bool)" "('a \<Rightarrow> bool)"
    ("{[_]} _ {[_]}" [0,0,0] 61)

(*
type_synonym 'a triple =
  "('a \<Rightarrow> bool) * ('a \<Rightarrow> 'a \<Rightarrow> bool) * ('a \<Rightarrow> bool)"
*)
definition VT :: "'a triple \<Rightarrow> bool" ("![ _ ]!" 58)
 where
"VT t =
  (case t of
    T pre x post \<Rightarrow>
      (\<forall> a b . pre a \<longrightarrow> x a b \<longrightarrow> post b))"
*)

abbreviation C where
"C x \<equiv> (\<lambda> _ . x)"

definition predimp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ *-> _" 63)
  where
"predimp P1 P2 =
  (\<forall> x . P1 x \<longrightarrow> P2 x)"

definition VT :: 
  "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" 
  ("{{_}} _ {{_}}" [0,0,0] 61) where
"VT pre x post =
  (\<forall> a b . pre a \<longrightarrow> x a b \<longrightarrow> post b)"

lemma VTI :
  assumes H1 : 
    "\<And> a b . pre a \<Longrightarrow> x a b \<Longrightarrow> post b"
  shows "VT pre x post" using assms
  unfolding VT_def by auto

lemma VTE :
  assumes H : "VT pre x post"
  assumes Ha : "pre a"
  assumes Hb : "x a b"
  shows "post b" using assms
  unfolding VT_def by auto

lemma Vtop :
  shows "{{P}} X {{C True}}"
  by(simp add:VT_def)

lemma Vbot :
  shows "{{C False}} X {{P}}"
  by(simp add:VT_def)

lemma Vconseq_pre :
  assumes H1 : "{{P}} X {{Q}}"
  assumes H2 : "P' *-> P"
  shows "{{P'}} X {{Q}}" using assms
  by(auto simp add: VT_def predimp_def)

lemma Vconseq_post :
  assumes H1 : "{{P}} X {{Q}}"
  assumes H2 : "Q *-> Q'"
  shows "{{P}} X {{Q'}}" using assms
  by(auto simp add: VT_def predimp_def)

lemma VandI :
  assumes H1 : "{{P1}} X {{Q1}}"
  assumes H2 : "{{P2}} X {{Q2}}"
  shows "{{(\<lambda> x . (P1 x \<and> P2 x))}} X {{(\<lambda> x . (Q1 x \<and> Q2 x))}}"
    using assms
    by(auto simp add: VT_def)

type_synonym ('x, 'a) syn_triple =
  "('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool)"

(* we could use ad-hoc polymorphism here, in leiu of an actual typeclass,
for syn_triple (keyed on syntax). but maybe this wouldn't be a good idea.
*)

(* "valid triple, syntax." *)
(*
definition VTS ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_: {{_}} _ {{_}}" [0,0,0,0] 62)
  where
"VTS sem pre x post =
  VT pre (sem x) post"
*)

(* hmm. how to deal with syntax transformation when lifting predicates? *)
(*
definition VTS :: 
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_: {{_}} _ {{_}}" [0,0,0,0] 62)
  where
"VTS sem pre x post =
  VT (pre x) (sem x) (post x)"
*)

abbreviation VTS :: 
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ % {{_}} _ {{_}}" [0,0,0,0] 63)
  where
"VTS sem pre x post \<equiv>
  VT (pre) (sem x) (post)"

(* executable VTS. probably less useful than relational one. *)
definition VTS' ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"VTS' sem pre x post =
  VT pre (\<lambda> a b . sem x a = b) post"

definition lift_pred_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   'b1 \<Rightarrow>
   ('a2 \<Rightarrow> bool) \<Rightarrow>
   ('b2 \<Rightarrow> bool)" where
"lift_pred_s l' l syn P st =
 P (LOut l (l' syn) st)"

(* TODO: figure out why there is this ambiguity *)
definition semprop2 ::
  "('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a3 \<Rightarrow> bool)"
  ("! _" [3] 61)
  where
"semprop2 f a1 a2 a3 \<equiv>
  (f a1 a2 = a3)"

(* need to consider liftings. *)
lemma Vlift :
  assumes Valid : "lifting_valid l v" 
  assumes V: "(!sem) % {{P}} x {{Q}}"
  assumes Syn : "l' x' = x"
  shows "(! lift_map_s l' l sem) % {{lift_pred_s l' l x' P}} x' {{lift_pred_s l' l x' Q}}"
 using V Syn
  unfolding VT_def lift_pred_s_def lift_map_s_def semprop2_def
  by(auto simp add: lifting_validDO[OF Valid])

(* need to fix up LangComp.thy.
   ok, i think we can actually avoid talking about lifting here. just merging (?) *)
(* maybe we actually do want to integrate these... *)


(* do we need explicit P0 ... Pn ?*)
lemma Vmerge :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "f \<in> set l"
  assumes V : "(!f) % {{P}} x {{Q}}"
  shows "(! pcomps' l) % 
         {{P}}
         x
         {{(\<lambda> st . \<exists> st_sub . Q st_sub \<and> st_sub <[ st)}}"
proof(rule VTI)
  fix a b
  assume HP : "P a"
  assume HS : "(! pcomps' l) x a b"

  have Conc_f : "Q (f x a)"
    using VTE[OF V HP]
    unfolding semprop2_def by auto

  have Elem : "f x a \<in> (\<lambda>f. f x a) ` set l"
    using Sem by auto

  have Nemp : "l \<noteq> []" using Sem by (cases l; auto)

  have Conc' : "f x a <[ pcomps' l x a"
    using is_sup_unfold1[OF sups_pres_pcomps_sup[OF Pres Nemp] Elem]
    by auto

  have Pc_l_b : "pcomps' l x a = b" using HS unfolding semprop2_def
    by auto

  show "\<exists>st_sub. Q st_sub \<and> st_sub <[ b"
    using Conc_f Conc' unfolding Pc_l_b
    by auto
qed
    

lemma Vmerge_mono :
  assumes Pres : "sups_pres (set l)"
  assumes Sem : "f \<in> set l"
  assumes Mono : "Pord.is_monop1 Q"
  assumes V : "(!f) % {{P}} x {{Q}}"
  shows "(! pcomps l) % 
         {{P}}
         x
         {{Q}}"
proof(-)
  have PC : "(! pcomps l) % {{P}} x {{\<lambda>st. \<exists>st_sub. Q st_sub \<and> st_sub <[ st}}"
    using Vmerge[OF Pres Sem V]
    by auto

  show "(! pcomps l) % {{P}} x {{Q}}"
  proof(rule Vconseq_post[OF PC])
    show "(\<lambda>st. \<exists>st_sub. Q st_sub \<and> st_sub <[ st) *-> Q"
      unfolding predimp_def
    proof(clarify)
      fix x st_sub
      assume Hi1 : "Q st_sub"
      assume Hi2 : "st_sub <[ x"
      show "Q x" using Hi1 Hi2 Mono unfolding is_monop1_def
        by(auto)
    qed
  qed
qed

  proof(rule 
  
  sorry

(* ok, should have a way of proving sups_pres holds on some lifted stuff *)
(*
lemma Vmerge :
  assumes Valid1 : "lifting_valid l1 v1" 
  assumes Valid2 : "lifting_valid l2 v2"
  assumes V1 : "(!sem1) % {{P1}} x1 {{Q1}}"
  assumes V2 : "(!sem2) % {{P2}} x2 {{Q2}}"

  assumes Syn1 : "l1' x1' = x1"
  assumes Syn2 : "l2' x2' = x2"

  

shows "(! (pcomp sem1 sem2)) % {{(\<lambda> st . P1 st \<and> P2 st)}}
        (
       {{ (\<lambda> st .
           \<exists> st1 st2 .
             Q1 st1 \<and> Q2 st2 \<and>
             st1 <[ st \<and> st2 <[ st )}}"
            
  apply(auto simp add: lift_pred_s_def semprop2_def)

*)
(* goal1: lifting (assuming liftability side conditions: *)
(* {{P}} X {{Q}} \<Longrightarrow> {{lift l P}} lift_map l X {{lift l Q}} *)

(* goal2: merging (assuming liftability side conditions: *)
(* {{P1}} X1 {{Q1}} \<Longrightarrow> {{P2}} X2 {{Q2}} \<Longrightarrow>
   {{lift P1 \<and> lift P2}} X s.t. pi1 x = x1, pi2 x = x2
   {{ (\<lambda> st' . \<exists> st x1' x2' .
          P1 (LOut l1 st) \<and> P2 (LOut l2 st) \<and>
          X1 (LOut l1 st) x1' \<and> X2 (LOut l2 st) x2' \<and>
          Q1 x1' \<and> Q2 x2' \<and>
          LUpd l1 x1' st <[ st' \<and>
          LUpd l2 x2' st <[ st') }}
*)
   

end