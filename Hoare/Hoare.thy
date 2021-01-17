theory Hoare imports "../Lifting/LiftUtils" "../Lifting/LangComp"
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

definition VTS :: 
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_ % {{_}} _ {{_}}" [0,0,0,0] 63)
  where
"VTS sem pre x post =
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
"semprop2 f a1 a2 a3 =
  (f a1 a2 = a3)"

(* need to consider liftings. *)
(* why is l' getting applied twice. *)
lemma Vlift :
  assumes Valid : "lifting_valid l v" 
  assumes V: "(!sem) % {{P}} x {{Q}}"
  assumes Syn : "l' x' = x"
  shows "(! lift_map_s l' l sem) % {{lift_pred_s l' l x' P}} x' {{lift_pred_s l' l x' Q}}"
 using V Syn
  unfolding VTS_def VT_def semprop2_def lift_pred_s_def lift_map_s_def
  by(auto simp add: lifting_validDO[OF Valid])

(* need to fix up LangComp.thy. *)
lemma Vmerge :
  assumes Valid1 : "lifting_valid l1 v1" 
  assumes Valid2 : "lifting_valid l2 v2"
  assumes V1 : "(!sem) % {{P}} x {{Q}}"
  assumes Syn1 : "l1' x1' = x1"
  assumes Syn2 : "l2' x2' = x2"
  shows "
    (! ()
            
  apply(auto simp add: lift_pred_s_def semprop2_def)
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