theory Hoare imports "../Lifting/LiftUtils"
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
definition VTS ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  ("_: {{_}} _ {{_}}" [0,0,0,0] 62)
  where
"VTS sem pre x post =
  VT pre (sem x) post"

(* executable VTS. probably less useful than relational one. *)
definition VTS' ::
  "('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
   ('a \<Rightarrow> bool) \<Rightarrow> 'x \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool"
  where
"VTS' sem pre x post =
  VT pre (\<lambda> a b . sem x a = b) post"

(* need to consider liftings. *)

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