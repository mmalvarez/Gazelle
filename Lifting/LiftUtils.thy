theory LiftUtils
 imports  "../MergeableTc/MergeableInstances" "../MergeableTc/MergeableAList"
begin

(* lifting' is used for syntax *)
type_synonym ('a, 'b) lifting' = "('b \<Rightarrow> 'a)"

(* key abstraction used to lift semantics into larger types *)
(* "pre-lifting" - definition of the idempotent part *)
record ('syn, 'a, 'b) plifting =
  LUpd :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b)"
  LOut :: "('syn \<Rightarrow> 'b \<Rightarrow> 'a)"
  LBase :: "'syn \<Rightarrow> 'b"

record ('syn, 'a, 'b) lifting =
  "('syn, 'a, 'b) plifting" +
  LPost :: "('syn \<Rightarrow> 'b \<Rightarrow> 'b)"

definition LNew :: "('syn, 'a, 'b, 'z) plifting_scheme \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

(* idea: OutS captures set of things we can project
   reset resets inner data back to base but does not change anything else *)
record ('syn, 'a, 'b) pliftingv = 
  LOutS :: "'syn \<Rightarrow> 'b set"

(*
record ('syn, 'a, 'b) liftingvm = "('syn, 'a, 'b) liftingv" +
  LMgS :: "'syn \<Rightarrow> 'b \<Rightarrow> 'b set"
*)

(* idea: capture how we need to weaken a predicate after a merge *)
record ('syn, 'a, 'b) liftingv = "('syn, 'a, 'b) pliftingv" +
  LMgS :: "'syn \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow>
           ('b \<Rightarrow> bool) \<Rightarrow> ('b \<Rightarrow> bool)"

(* let's see if this is more ergonomic *)
declare lifting.cases [simp]
declare liftingv.cases [simp]

(*
definition l_adapt  ::
  "('syn1 \<Rightarrow> 'syn2) \<Rightarrow>
   ('syn2, 'a, 'b) lifting \<Rightarrow>
   ('syn1, 'a, 'b) lifting" where
"l_adapt f t =
  \<lparr> LIn = (\<lambda> s a b . LIn t (f s) a b)
  , LOut = (\<lambda> s b . LOut t (f s) b)
  , LNew = (\<lambda> s a . LNew t (f s) a) \<rparr>"

declare l_adapt_def [simp]
*)


definition pl_map ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
    ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"pl_map l sem syn st =
  (LUpd l syn (sem syn (LOut l syn st)) st)"

declare pl_map_def [simp]

definition l_map ::
  "('x, 'a, 'b, 'z) lifting_scheme \<Rightarrow>
    ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"l_map l sem syn st =
  (LPost l syn (pl_map l sem syn st))"

declare l_map_def [simp]

(* trailing s = "with syntax" *)
definition pl_map_s ::
    "('a1, 'b1) lifting' \<Rightarrow>
     ('a1, 'a2, 'b2, 'z) plifting_scheme \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"pl_map_s l' l sem syn st =
  (LUpd l (l' syn) (sem (l' syn) (LOut l (l' syn) st)) st)"

declare pl_map_s_def [simp]

definition l_map_s ::
    "('a1, 'b1) lifting' \<Rightarrow>
     ('a1, 'a2, 'b2, 'z) lifting_scheme \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"l_map_s l' l sem syn st =
  (LPost l (l' syn) (pl_map_s l' l sem syn st))"


(* lowering functions? *)

(*
definition l_unmap ::
  "('x, 'a, 'b) lifting \<Rightarrow>
   ('x \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> 'a)" where
"l_unmap l sem syn st =
  (LOut l syn (sem syn (LNew l syn st)))"
*)

(*
declare l_unmap_def [simp]
*)

(* maybe unmaps needs to be propositional? 
perhaps we can get away with using the SOME operator
but it feels like we need a universal
*)
definition l_unmap_s ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2, 'z) plifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2)" where
"l_unmap_s l' l sem syn st =
  (let syn' = (SOME x . l' x = syn) :: 'b1 in
  (LOut l syn (sem syn' (LNew l syn st))))"

declare l_unmap_s_def [simp]

definition l_pred :: "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred t P =
  (\<lambda> s b . P s (LOut t s b))"

declare l_pred_def [simp]

definition l_unpred :: "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool)" where
"l_unpred t P =
  (\<lambda> s a . P s (LNew t s a))"

declare l_unpred_def [simp]

definition l_pred_step ::
  "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool)" where
"l_pred_step l P s st1 st2 =
        (P s (LOut l s st1) (LOut l s st2))"

(* idea: when contained data is the same,
   result's contained data is the same. *)
definition can_unmap ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2, 'z) plifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   bool" where
"can_unmap l' l f =
  (\<forall> b1_1 b2_1 b1_2 b2_2 . 
     l' b1_1 = l' b1_2 \<longrightarrow>
     LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2 \<longrightarrow>
     LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2))"

lemma can_unmap_intro :
  assumes H : "\<And> b1_1 b2_1 b1_2 b2_2 .
                  l' b1_1 = l' b1_2 \<Longrightarrow>
                  LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2 \<Longrightarrow>
                  LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2)"
  shows "can_unmap l' l f" using H unfolding can_unmap_def
  by(blast)

lemma can_unmap_unfold :
  assumes H1 : "can_unmap l' l f"
  assumes H2 : "l' b1_1 = l' b1_2"
  assumes H3 : "LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2"
  shows "LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2)"
  using H1 H2 H3 unfolding can_unmap_def
  by blast

(* ok, there is a duality here.
   - map & unpred both need l and pl versions (?)
   - unmap and pred don't *)

definition l_pred_step_s ::
  "('s1, 's2) lifting' \<Rightarrow>
   ('s1, 'b1, 'b2, 'z) plifting_scheme \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool) \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"l_pred_step_s l1 l2 P syn st1 st2 =
   (P (l1 syn) (LOut l2 (l1 syn) st1) (LOut l2 (l1 syn) st2))"

(* next: define
   - pl_unpred
   - l_unpred
   - pl_unpred_step
   - l_unpred_step
*)

definition pl_unpred_step_s ::
  "('s1, 's2) lifting' \<Rightarrow>
   ('s1, 'b1, 'b2, 'z) plifting_scheme \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool)" where
"pl_unpred_step_s l1 l2 P syn st1 st2 =
   (\<forall> syn' . l1 syn' = syn \<longrightarrow>
     (P syn' (LNew l2 syn st1) (LUpd l2 syn st2 (LNew l2 syn st1))))"

lemma pl_unpred_step_s_intro :
  assumes H : "\<And> syn' . l1 syn' = syn \<Longrightarrow>
          (P syn' (LNew l2 syn st1) (LUpd l2 syn st2 (LNew l2 syn st1)))"
  shows "pl_unpred_step_s l1 l2 P syn st1 st2"
  using H
  unfolding pl_unpred_step_s_def 
  by auto

lemma pl_unpred_step_s_unfold :
  assumes H : "pl_unpred_step_s l1 l2 P syn st1 st2"
  assumes H1 : "l1 syn' = syn"
  shows "(P syn' (LNew l2 syn st1) (LUpd l2 syn st2 (LNew l2 syn st1)))"
  using H H1
  unfolding pl_unpred_step_s_def
  by auto

definition l_unpred_step_s ::
  "('s1, 's2) lifting' \<Rightarrow>
   ('s1, 'b1, 'b2, 'z) lifting_scheme \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool)" where
"l_unpred_step_s l1 l2 P syn st1 st2 =
   (\<forall> syn' . l1 syn' = syn \<longrightarrow>
     (P syn' (LNew l2 syn st1) (LPost l2 syn (LUpd l2 syn st2 (LNew l2 syn st1)))))"

lemma l_unpred_step_s_intro :
  assumes H: "\<And> syn' . l1 syn' = syn \<Longrightarrow>
                (P syn' (LNew l2 syn st1) (LPost l2 syn (LUpd l2 syn st2 (LNew l2 syn st1))))"
  shows "l_unpred_step_s l1 l2 P syn st1 st2"
  using H
  unfolding l_unpred_step_s_def
  by auto

lemma l_unpred_step_s_unfold :
  assumes H: "l_unpred_step_s l1 l2 P syn st1 st2"
  assumes H1 : "l1 syn' = syn"
  shows "(P syn' (LNew l2 syn st1) (LPost l2 syn (LUpd l2 syn st2 (LNew l2 syn st1))))"
  using H H1
  unfolding l_unpred_step_s_def
  by auto

(* if we have a pord, do we want to allow out to return more information?
   i think maybe not - the goal of liftings is to inject exactly what we want... (?)
 *)
(* another question. will LIn be in the "OutS" set even if given b isn't?
   i think the answer is yes - this lifting is specific to the 'a-data *)
definition plifting_valid :: "('x, 'a, 'b, 'z) plifting_scheme \<Rightarrow> bool" where
"plifting_valid l =
  ((\<forall> s a b . LOut l s (LUpd l s a b) = a)\<and>
   (\<forall> s a a' b . 
      LUpd l s a (LUpd l s a' b) = LUpd l s a b))"

lemma plifting_valid_intro :
  assumes H1 : "\<And> s a b . LOut l s (LUpd l s a b) = a"
  assumes H2 : "\<And> s a a' b . LUpd l s a (LUpd l s a' b) = LUpd l s a b"
  shows "plifting_valid l"
  using H1 H2
  by(auto simp add:plifting_valid_def)

lemma plifting_valid_unfold1 :
  assumes H : "plifting_valid l"
  shows "LOut l s (LUpd l s a b) = a"
  using H by (auto simp add:plifting_valid_def)

lemma plifting_valid_unfold2 :
  assumes H : "plifting_valid l"
  shows "LUpd l s a (LUpd l s a' b) = LUpd l s a b"
  using H by (auto simp add:plifting_valid_def)

definition plifting_pv_valid :: "('x, 'a, 'b, 'z1) plifting_scheme \<Rightarrow>
                                 ('x, 'a, 'b, 'z2) pliftingv_scheme \<Rightarrow> bool" where
"plifting_pv_valid l v =
  ((plifting_valid l) \<and>
   (\<forall> s a b . LUpd l s a b \<in> LOutS v s) \<and>
   (\<forall> s b .
      b \<in> LOutS v s \<longrightarrow>
      b = LUpd l s (LOut l s b) b))"

lemma plifting_pv_valid_intro :
  assumes H : "plifting_valid l"
  assumes H1 : "\<And> s a b . LUpd l s a b \<in> LOutS v s"
  assumes H2 : "\<And> s b .
      b \<in> LOutS v s \<Longrightarrow>
      b = LUpd l s (LOut l s b) b"
  shows "plifting_pv_valid l v"
  using H H1 H2
  by (auto simp add:plifting_pv_valid_def)

lemma plifting_pv_valid_unfold1 :
  assumes H : "plifting_pv_valid l v"
  shows "plifting_valid l" using H by (auto simp add: plifting_pv_valid_def)

lemma plifting_pv_valid_unfold2 :
  assumes H : "plifting_pv_valid l v"
  shows "LUpd l s a b \<in> LOutS v s" using H by (auto simp add: plifting_pv_valid_def)

lemma plifting_pv_valid_unfold3 :
  assumes H : "plifting_pv_valid l v"
  assumes H1 : "b \<in> LOutS v s"
  shows "b = LUpd l s (LOut l s b) b"
  using H H1 by (auto simp add: plifting_pv_valid_def)

(* avoiding free type variables error in codegen *)
definition plifting_extend :: "('x, 'a, 'b) plifting \<Rightarrow> ('x\<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> ('x, 'a, 'b) lifting"
  where
"plifting_extend p post =
  \<lparr> LUpd = LUpd p
  , LOut = LOut p
  , LBase = LBase p
  , LPost = post \<rparr>"


lemma plifting_valid_cast :
  assumes H : "plifting_valid pv"
  shows "plifting_valid (plifting.extend pv x)"
proof(rule plifting_valid_intro)
  fix s a b
  show "LOut (plifting.extend pv x) s (LUpd (plifting.extend pv x) s a b) = a"
    using plifting_valid_unfold1[OF H] by(auto simp add:plifting.defs)
next
  fix s a a' b
  show "LUpd (plifting.extend pv x) s a (LUpd (plifting.extend pv x) s a' b) =
       LUpd (plifting.extend pv x) s a b"
    using plifting_valid_unfold2[OF H] by(auto simp add:plifting.defs)
qed

lemma plifting_pv_valid_cast :
  assumes H : "plifting_pv_valid pv v"
  shows "plifting_pv_valid (plifting.extend pv x) v"
proof(rule plifting_pv_valid_intro)
  show "plifting_valid (plifting.extend pv x)"
    using plifting_valid_cast[OF plifting_pv_valid_unfold1[OF H], of x] by (auto simp add: plifting.defs)
next
  fix s a b
  show "LUpd (plifting.extend pv x) s a b \<in> LOutS v s"
    using plifting_pv_valid_unfold2[OF H] by(auto simp add:plifting.defs)
next
  fix s b
  show "b \<in> LOutS v s \<Longrightarrow>
           b = LUpd (plifting.extend pv x) s (LOut (plifting.extend pv x) s b) b"
    using plifting_pv_valid_unfold3[OF H] by(auto simp add:plifting.defs)
qed

definition lifting_pv_valid :: "('x, 'a, 'b, 'z1) lifting_scheme \<Rightarrow>
                                ('x, 'a, 'b, 'z2) pliftingv_scheme \<Rightarrow> bool" where
"lifting_pv_valid l v =
  (plifting_pv_valid l v \<and>
   (\<forall> s b . b \<in> LOutS v s \<longrightarrow> LPost l s b \<in> LOutS v s) \<and>
   (\<forall> s b . b \<in> LOutS v s \<longrightarrow> LOut l s (LPost l s b) = LOut l s b))"

lemma lifting_pv_valid_intro :
  assumes H1 : "plifting_pv_valid l v"
  assumes H2 : "\<And> s a b . b \<in> LOutS v s \<Longrightarrow> LPost l s b \<in> LOutS v s"
  assumes H3 : "\<And> s a b . b \<in> LOutS v s \<Longrightarrow> LOut l s (LPost l s b) = LOut l s b"

shows "lifting_pv_valid l v" using H1 H2 H3 by (auto simp add:lifting_pv_valid_def)

lemma lifting_pv_valid_unfold1 :
  assumes H : "lifting_pv_valid l v"
  shows "plifting_pv_valid l v" using H by (auto simp add:lifting_pv_valid_def)

lemma lifting_pv_valid_unfold2 :
  assumes H : "lifting_pv_valid l v"
  assumes H1 : "b \<in> LOutS v s"
  shows "LPost l s b \<in> LOutS v s"
  using H H1 by (auto simp add:lifting_pv_valid_def)

lemma lifting_pv_valid_unfold3 :
  assumes H : "lifting_pv_valid l v"
  assumes H1 : "b \<in> LOutS v s"
  shows "LOut l s (LPost l s b) = LOut l s b"
  using H H1 by (auto simp add:lifting_pv_valid_def)


 (*  

lemma liftingv_valid_intro :
  assumes H1 : "lifting_valid l"
  assumes H2 : "\<And> s a b . LIn l s a b \<in> LOutS l s"
  assumes H3 : "\<And> s a . LNew l s a \<in> LOutS l s"
  assumes H4 : "\<And> s a b . LNew l s a <[ LIn l s a b"
  assumes H5 : "\<And> s b b' . b' <[ b \<Longrightarrow> 
                           b \<in> LOutS l s \<Longrightarrow>
                           b' <[ LIn l s (LOut l s b) b'"
  assumes H6 : "\<And> s a a' a'' b . LIn l s a (LIn l s a' b) =
                                 LIn l s a (LIn l s a'' b)"
  shows "liftingv_valid l"
  using H1 H2 H3 H4 H5 H6 by(auto simp add:liftingv_valid_def)

lemma liftingv_valid_unfold1 :
  assumes H : "liftingv_valid l"
  shows "lifting_valid l" using H by (auto simp add: liftingv_valid_def)

lemma liftingv_valid_unfold2 :
  assumes Hv : "liftingv_valid l"
  shows "LIn l s a b \<in> LOutS l s"
  using Hv by (auto simp add:liftingv_valid_def)

lemma liftingv_valid_unfold3 :
  assumes Hv : "liftingv_valid l"
  shows "LNew l s a \<in> LOutS l s"
  using Hv by (auto simp add: liftingv_valid_def)

lemma liftingv_valid_unfold4 :
  assumes Hv : "liftingv_valid l"
  shows "LNew l s a <[ LIn l s a b"
  using Hv by (auto simp add:liftingv_valid_def)

lemma liftingv_valid_unfold5 :
  assumes Hv : "liftingv_valid l"
  assumes Hleq : "b' <[ b"
  assumes Hout : "b \<in> LOutS l s"
  shows "b' <[ LIn l s (LOut l s b) b'"
  using Hv Hleq Hout by(auto simp add:liftingv_valid_def)

lemma liftingv_valid_unfold6 :
  assumes Hv : "liftingv_valid l"
  shows "LIn l s a (LIn l s a' b) =
         LIn l s a (LIn l s a'' b)"
    using Hv by (auto simp add:liftingv_valid_def)
*)

(*
definition liftingvm_valid :: "('x, 'a :: Mergeable, 'b :: Mergeable, 'z) liftingvm_scheme \<Rightarrow> bool" 
where
"liftingvm_valid l =
  ((liftingv_valid l) \<and>
   (\<forall> s a a' b b' . 
      b' \<in> LMgS l s b \<longrightarrow>
      a = LOut l s b \<longrightarrow>
      a' = LOut l s b' \<longrightarrow>
      LOut l s [^ b, b' ^] = [^ a, a' ^]))"
  *)

(*
lemma l_adapt_valid :
  fixes f :: "('x1 \<Rightarrow> 'x2)"  
  fixes t :: "('x2, 'a, 'b) lifting"
  assumes H : "lifting_valid t"
  shows "lifting_valid (l_adapt f t)" using H
  by(auto simp add:lifting_valid_def)
declare[[show_types]]
*)
lemma l_pred_step_s_pl_map_s :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) plifting_scheme"
  assumes Hv : "plifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step_s l1 l2 P (x1') (x2') (pl_map_s l1 l2 f (x1') (x2'))"
  using Hsyn Hsem HP plifting_valid_unfold1[OF Hv] 
  by(cases l2; auto simp add:l_pred_step_s_def)

lemma l_pred_step_s_pl_map_s_contra :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) plifting_scheme"
  assumes Hv : "plifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes HP : "l_pred_step_s l1 l2 P (x1') (x2') (pl_map_s l1 l2 f (x1') (x2'))"
  shows "P x1 x2 (f x1 x2)"
  using Hsyn Hsem HP plifting_valid_unfold1[OF Hv] 
  by(auto simp add:l_pred_step_s_def)

lemma l_pred_step_s_lmap_s :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) lifting_scheme"
  assumes Hv : "lifting_pv_valid l2 v"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "l_pred_step_s l1 l2 P (x1') (x2') (l_map_s l1 l2 f (x1') (x2'))"
proof-
  have Hv' : "plifting_pv_valid l2 v" using lifting_pv_valid_unfold1[OF Hv] by auto
  hence Hv'' : "plifting_valid l2" using plifting_pv_valid_unfold1[OF Hv'] by auto

  have HS :
    "(LUpd l2 (l1 x1') (f (l1 x1') (LOut l2 (l1 x1') x2')) x2') \<in> LOutS v (l1 x1')"
    using plifting_pv_valid_unfold2[OF Hv'] by auto

  have Eq1: "LOut l2 (l1 x1') (LPost l2 (l1 x1') (LUpd l2 (l1 x1') (f (l1 x1') (LOut l2 (l1 x1') x2')) x2')) =
        LOut l2 (l1 x1') (LUpd l2 (l1 x1') (f (l1 x1') (LOut l2 (l1 x1') x2')) x2')"
    by(rule lifting_pv_valid_unfold3[OF Hv plifting_pv_valid_unfold2[OF Hv']])

  have Eq2 : "LOut l2 (l1 x1') (LUpd l2 (l1 x1') (f (l1 x1') (LOut l2 (l1 x1') x2')) x2') =
              (f (l1 x1') (LOut l2 (l1 x1') x2'))"
    by(rule plifting_valid_unfold1[OF Hv''])

  show "l_pred_step_s l1 l2 P (x1') (x2') (l_map_s l1 l2 f (x1') (x2'))"
    using Hsyn Hsem HP
          lifting_pv_valid_unfold2[OF Hv HS]
    by(auto simp add:l_pred_step_s_def l_map_s_def Eq1 Eq2)
qed

lemma l_pred_step_s_lmap_s_contra :
  fixes l1 :: "('a1, 'b1) lifting'"
  fixes l2 :: "('a1, 'a2, 'b2, 'z) lifting_scheme"
  assumes Hv : "lifting_pv_valid l2 v"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes HP : "l_pred_step_s l1 l2 P (x1') (x2') (l_map_s l1 l2 f (x1') (x2'))"
  shows "P x1 x2 (f x1 x2)"
proof-

  have 1 : " (LUpd l2 x1 (f x1 x2) x2') \<in> LOutS v x1"
      using plifting_pv_valid_unfold2[OF lifting_pv_valid_unfold1[OF Hv]] by auto

  show " P x1 x2 (f x1 x2)" using HP
    unfolding l_pred_step_s_def pl_map_s_def l_map_s_def Hsyn Hsem
    using 
    lifting_pv_valid_unfold3[OF Hv 1]
    plifting_valid_unfold1[OF plifting_pv_valid_unfold1[OF lifting_pv_valid_unfold1[OF Hv]]]
    by(auto)
qed

definition can_unpred ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) plifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   bool" where
"can_unpred l' l P =
  (\<forall> syn syn' st1 st2 st'1 st'2.
    l' syn = l' syn' \<longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<longrightarrow>
    LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<longrightarrow>
    P syn st1 st2 = P syn' st'1 st'2)"
(* should roles of st'2 and st2 be reversed? *)

lemma can_unpred_intro :
  assumes H : 
    "\<And> syn syn' st1 st2 st'1 st'2 .
      l' syn = l' syn' \<Longrightarrow>
      LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<Longrightarrow>
      LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<Longrightarrow>
      P syn st1 st2 = P syn' st'1 st'2"
  shows "can_unpred l' l P"
  using H
  unfolding can_unpred_def
  by(blast)

lemma can_unpred_intro' :
  assumes H : 
    "\<And> syn syn' st1 st2 st'1 st'2 .
      l' syn = l' syn' \<Longrightarrow>
      LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<Longrightarrow>
      LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<Longrightarrow>
      P syn st1 st2 \<Longrightarrow> P syn' st'1 st'2"
  shows "can_unpred l' l P" unfolding can_unpred_def 
proof(rule allI; rule allI; rule allI; rule allI; rule allI; rule allI;
      rule impI; rule impI; rule impI)
  fix syn syn' st1 st2 st'1 st'2
  assume Hi1 : "l' syn = l' syn'"
  assume Hi2 : "LOut l (l' syn) st1 = LOut l (l' syn') st'1"
  assume Hi3 : "LOut l (l' syn) st2 = LOut l (l' syn') st'2"
  show "P syn st1 st2 = P syn' st'1 st'2"
    using H[OF Hi1 Hi2 Hi3] H[OF sym[OF Hi1] sym[OF Hi2] sym[OF Hi3]]
    by auto
qed

lemma can_unpred_unfold :
  assumes H : "can_unpred l' l P"
  assumes H1 : "l' syn = l' syn'"
  assumes H2 : "LOut l (l' syn) st1 = LOut l (l' syn') st'1"
  assumes H3 : "LOut l (l' syn) st2 = LOut l (l' syn') st'2 "
  assumes Hl : "P syn st1 st2"
  shows "P syn' st'1 st'2"
  using H H1 H2 H3 Hl
  unfolding can_unpred_def
  by blast

(* idea: this one needs to basically say
   if input states match w/r/t out
   and output states match or 
   output state exceeds given threshold
   *)
(* is this what we want? the problem is that we are
   requiring states above threshold to equal
   states below in terms of valuation under P
   *)
definition can_unpred_strong ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2 :: Pord, 'z) plifting_scheme \<Rightarrow>
   'b2 \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   bool" where
"can_unpred_strong l' l thresh P =
  ((can_unpred l' l P) \<and>
   (\<forall> syn syn' st1 st2 st'1 st'2.
     l' syn = l' syn' \<longrightarrow>
     P syn st1 st2 \<longrightarrow>
     LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<longrightarrow>
    (thresh <[ st'2 \<longrightarrow> P syn' st'1 st'2)))"
(* should roles of st'2 and st2 be reversed? *)

lemma can_unpred_strong_intro :
  assumes H1 : 
    "can_unpred l' l P"
  assumes H2 :
    "\<And> syn syn' st1 st2 st'1 st'2 .
      l' syn = l' syn' \<Longrightarrow>
      LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<Longrightarrow>
      thresh <[ st'2 \<Longrightarrow>
      P syn st1 st2 \<Longrightarrow>
      P syn' st'1 st'2"
  shows "can_unpred_strong l' l thresh P"
  using H1 H2
  unfolding can_unpred_strong_def
  by(blast)

lemma can_unpred_strong_unfold1 :
  assumes H : "can_unpred_strong l' l thresh P"
  shows "can_unpred l' l P"
  using H
  unfolding can_unpred_strong_def by auto

lemma can_unpred_strong_unfold2 :
  assumes H : "can_unpred_strong l' l thresh P"
  assumes H1 : "l' syn = l' syn'"
  assumes H2 : "LOut l (l' syn) st1 = LOut l (l' syn') st'1"
  assumes H3 : "thresh <[ st'2"
  assumes H4 : "P syn st1 st2"
  shows "P syn' st'1 st'2"
  using H H1 H2 H3 H4
  unfolding can_unpred_strong_def
  by blast

definition pres_LOutS ::
  "('a1, 'b1) lifting' \<Rightarrow>
   ('a1, 'a2, 'b2, 'z) liftingv_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   bool" where
"pres_LOutS l' l f =
  (\<forall> s b .
       b \<in> LOutS l (l' s) \<longrightarrow>
       f s b \<in> LOutS l (l' s))"

lemma pres_LOutS_intro :
  assumes H : "\<And> s b . b \<in> LOutS l (l' s) \<Longrightarrow>
                        f s b \<in> LOutS l (l' s)"
  shows "pres_LOutS l' l f"
  using H unfolding pres_LOutS_def by(blast)

lemma pres_LOutS_unfold :
  assumes H : "pres_LOutS l' l f"
  assumes H1 : "b \<in> LOutS l (l' s)"
  shows "f s b \<in> LOutS l (l' s)"
  using H H1 unfolding pres_LOutS_def by blast

(* first (?) prove
   pl_unpred_step_s_unmap_s *)

lemma pl_unpred_step_s_unmap_s  :
  assumes Hv : "plifting_valid l2"
  assumes Hunmap : "can_unmap l1 l2 f'"
  assumes Hunpred : "can_unpred l1 l2 P'"
  assumes H: "\<And> x1'' . l1 x1'' = x1 \<Longrightarrow> P' x1'' x2' (f' x1'' x2')"
  shows "pl_unpred_step_s l1 l2 P' x1 (LOut l2 x1 x2') (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2'))"
  unfolding pl_unpred_step_s_def l_unmap_s_def Let_def
proof(rule allI; rule impI)
  fix syn'
  assume Hsyn' : "l1 syn' = x1"

  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn')

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 syn'" using Hsyn' Syn by simp


  have Eq1 : "LOut l2 (l1 syn') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 syn') x2'"
    using Hsyn' plifting_valid_unfold1[OF Hv] unfolding LNew_def by auto

  have Eq2 :
"LOut l2 (l1 syn') (LUpd l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))) (LNew l2 x1 (LOut l2 x1 x2'))) =
  (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))"
    using plifting_valid_unfold1[OF Hv, of "l1 syn'"] Hsyn'
    by(auto)

  have Eq3 :
"LOut l2 (l1 (SOME x. l1 x = x1)) (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))) = LOut l2 (l1 syn') (f' syn' x2')"
  proof(rule can_unmap_unfold[OF Hunmap Syn_eq])
    show "LOut l2 (l1 (SOME x. l1 x = x1)) (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 syn') x2'"
      using Syn Hsyn' plifting_valid_unfold1[OF Hv, of "l1 (SOME x. l1 x = x1)"]
      unfolding LNew_def
      by(simp)
  qed

  have Eq3' :
"LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))) = LOut l2 (l1 syn') (f' syn' x2')"
    using Eq3 Syn by simp

  have Eq4 : " LOut l2 (l1 syn') (f' syn' x2') =
    LOut l2 (l1 syn') (LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2')))"
    using plifting_valid_unfold1[OF Hv, of "l1 syn'"] unfolding Hsyn' by(auto)

  show "P' syn' (LNew l2 x1 (LOut l2 x1 x2')) 
             (LUpd l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))
                (LNew l2 x1 (LOut l2 x1 x2')))" 
    unfolding  Eq3' 
  proof(rule can_unpred_unfold[OF Hunpred refl sym[OF Eq1] Eq4])
    show "P' syn' x2' (f' syn' x2')" using H[OF Hsyn'] by auto
  qed
qed

lemma pl_unpred_step_s_unmap_s_contra  :
  assumes Hv : "plifting_valid l2"
  assumes Hunmap : "can_unmap l1 l2 f'"
  assumes Hunpred : "can_unpred l1 l2 P'"
  assumes H: "pl_unpred_step_s l1 l2 P' x1 (LOut l2 x1 x2') (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2'))"
  assumes Hsyn :  "l1 x1'' = x1"
  shows "P' x1'' x2' (f' x1'' x2')"
proof-

  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn)

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 x1''" using Hsyn Syn by simp

  show "P' x1'' x2' (f' x1'' x2')"
  proof(rule can_unpred_unfold[OF Hunpred refl _ _ pl_unpred_step_s_unfold[OF H Hsyn]])
    show "LOut l2 (l1 x1'') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 x1'') x2'"
      using plifting_valid_unfold1[OF Hv] unfolding LNew_def Hsyn by auto
  next
    have 1 : "LOut l2 (l1 x1'') (LUpd l2 x1 (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2')) (LNew l2 x1 (LOut l2 x1 x2'))) =
              (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2'))"
      using plifting_valid_unfold1[OF Hv] unfolding Hsyn by auto

    have 2 : "LOut l2 (l1 (SOME x. l1 x = x1)) (LUpd l2 x1 (LOut l2 x1 x2') (LBase l2 x1)) = LOut l2 (l1 x1'') x2'"
      unfolding Syn Hsyn
      using plifting_valid_unfold1[OF Hv] by auto

    have 3 : "l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2') = LOut l2 (l1 x1'') (f' x1'' x2')"
      unfolding l_unmap_s_def Let_def 
      using can_unmap_unfold[OF Hunmap Syn_eq 2]
            plifting_valid_unfold1[OF Hv] 
      unfolding LNew_def Syn by auto

    show " LOut l2 (l1 x1'') (LUpd l2 x1 (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2')) (LNew l2 x1 (LOut l2 x1 x2'))) =
    LOut l2 (l1 x1'') (f' x1'' x2')"
      using 1 3 by auto
  qed
qed

declare [[show_types = false]]
lemma l_unpred_step_s_unmap_s  :
  assumes Hv : "lifting_pv_valid l2 v"
(*  assumes Hx2' : "x2' \<in> LOutS v x1"
  assumes Hpres : "pres_LOutS l1 v f'" *)
  assumes Hunmap : "can_unmap l1 l2 f'"
  assumes Hunpred : "can_unpred l1 l2 P'"
  assumes H: "\<And> x1'' . l1 x1'' = x1 \<Longrightarrow> P' x1'' x2' (f' x1'' x2')"
  shows "l_unpred_step_s l1 l2 P' x1 (LOut l2 x1 x2') (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2'))"
  unfolding l_unpred_step_s_def l_unmap_s_def Let_def
proof(rule allI; rule impI)
  fix syn'
  assume Hsyn' : "l1 syn' = x1"

  have Hv' : "plifting_pv_valid l2 v" using lifting_pv_valid_unfold1[OF Hv] by auto
  hence Hv'' : "plifting_valid l2" using plifting_pv_valid_unfold1[OF Hv'] by auto


  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn')

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 syn'" using Hsyn' Syn by simp

  have Eq1 : "LOut l2 (l1 syn') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 syn') x2'"
    using Hsyn' plifting_valid_unfold1[OF Hv''] unfolding LNew_def by auto

  have Eq2 :
"LOut l2 (l1 syn') (LUpd l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))) (LNew l2 x1 (LOut l2 x1 x2'))) =
  (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))"
    using plifting_valid_unfold1[OF Hv'', of "l1 syn'"] Hsyn'
    by(auto)

  have Eq3 :
"LOut l2 (l1 (SOME x. l1 x = x1)) (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))) = LOut l2 (l1 syn') (f' syn' x2')"
  proof(rule can_unmap_unfold[OF Hunmap Syn_eq])
    show "LOut l2 (l1 (SOME x. l1 x = x1)) (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 syn') x2'"
      using Syn Hsyn' plifting_valid_unfold1[OF Hv'', of "l1 (SOME x. l1 x = x1)"]
      unfolding LNew_def
      by(simp)
  qed

  have Eq3' :
"LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))) = LOut l2 (l1 syn') (f' syn' x2')"
    using Eq3 Syn by simp

  have Out1 : "LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2')) \<in> LOutS v x1"
    using plifting_pv_valid_unfold2[OF Hv'] by auto

  hence Eq4 : "LOut l2 (l1 syn') (LPost l2 x1 (LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2')))) =
               LOut l2 (l1 syn') (LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2')))"
    using lifting_pv_valid_unfold3[OF Hv Out1] unfolding Hsyn' by auto

  have Eq5 :  "LOut l2 (l1 syn') (LPost l2 x1 (LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2')))) =
               (LOut l2 (l1 syn') (f' syn' x2'))" using plifting_valid_unfold1[OF Hv''] unfolding Eq4
    unfolding Hsyn'
    by auto

  show " P' syn' (LNew l2 x1 (LOut l2 x1 x2'))
        (LPost l2 x1 (LUpd l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))) (LNew l2 x1 (LOut l2 x1 x2'))))" 
    unfolding  Eq3' 
  proof(rule can_unpred_unfold[OF Hunpred refl sym[OF Eq1] _ _, of "f' syn' x2'" ])
    show "LOut l2 (l1 syn') (f' syn' x2') =
    LOut l2 (l1 syn') (LPost l2 x1 (LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2'))))"
      using Eq5
      unfolding Hsyn' by(auto)
  next
    show "P' syn' x2' (f' syn' x2')" using H[OF Hsyn'] by auto
  qed
qed

lemma l_unpred_step_s_unmap_s_contra  :
  assumes Hv : "lifting_pv_valid l2 v"
(*  assumes Hx2' : "x2' \<in> LOutS v x1"
  assumes Hpres : "pres_LOutS l1 v f'" *)
  assumes Hunmap : "can_unmap l1 l2 f'"
  assumes Hunpred : "can_unpred l1 l2 P'"
  assumes H : "l_unpred_step_s l1 l2 P' x1 (LOut l2 x1 x2') (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2'))"
  assumes Hsyn: "l1 x1'' = x1"
  shows "P' x1'' x2' (f' x1'' x2')"
proof-

  have Hv' : "plifting_pv_valid l2 v" using lifting_pv_valid_unfold1[OF Hv] by auto
  hence Hv'' : "plifting_valid l2" using plifting_pv_valid_unfold1[OF Hv'] by auto

  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn)

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 x1''" using Hsyn Syn by simp

  show "P' x1'' x2' (f' x1'' x2')"
  proof(rule can_unpred_unfold[OF Hunpred refl _ _ l_unpred_step_s_unfold[OF H Hsyn]])
    show "LOut l2 (l1 x1'') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 x1'') x2'"
      unfolding LNew_def
      using plifting_valid_unfold1[OF Hv'']
      unfolding Hsyn 
      by(auto)
  next
    have Out1 : "LUpd l2 x1 (LOut l2 (l1 x1'') (f' x1'' x2')) (LNew l2 x1 (LOut l2 x1 x2')) \<in> LOutS v x1"
      using plifting_pv_valid_unfold2[OF Hv'] by auto
  
    hence Eq4 : "LOut l2 (l1 x1'') (LPost l2 x1 (LUpd l2 x1 (LOut l2 (l1 x1'') (f' x1'' x2')) (LNew l2 x1 (LOut l2 x1 x2')))) =
                 LOut l2 (l1 x1'') (LUpd l2 x1 (LOut l2 (l1 x1'') (f' x1'' x2')) (LNew l2 x1 (LOut l2 x1 x2')))"
      using lifting_pv_valid_unfold3[OF Hv Out1] unfolding Hsyn by auto
  
    have Eq5 :  "LOut l2 (l1 x1'') (LPost l2 x1 (LUpd l2 x1 (LOut l2 (l1 x1'') (f' x1'' x2')) (LNew l2 x1 (LOut l2 x1 x2')))) =
                 (LOut l2 (l1 x1'') (f' x1'' x2'))" using plifting_valid_unfold1[OF Hv''] unfolding Eq4
      unfolding Hsyn
      by auto
  
  (*
    have Eq6 : "(LUpd l2 x1 (LOut l2 x1 (f' (SOME x. l1 x = x1) 
                  (LNew l2 x1 (LOut l2 x1 x2')))) (LNew l2 x1 (LOut l2 x1 x2'))) =
                (LUpd l2 x1 (LOut l2 (l1 x1'') (f' x1'' x2')) (LNew l2 x1 (LOut l2 x1 x2')))"
      using can_unmap_unfold[OF Hunmap Syn_eq]
  *)
  
    have Eq6 : "LOut l2 x1 (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 x1 x2'"
      unfolding LNew_def
      using plifting_valid_unfold1[OF Hv''] by auto
  
    have Eq7 : "(LOut l2 x1 (f' (SOME x. l1 x = x1) 
                  (LNew l2 x1 (LOut l2 x1 x2')))) =
                (LOut l2 (l1 x1'') (f' x1'' x2')) "
      using can_unmap_unfold[OF Hunmap Syn_eq] Eq6 unfolding Syn Hsyn by(auto)

    show "LOut l2 (l1 x1'') (LPost l2 x1 (LUpd l2 x1 (l_unmap_s l1 l2 f' x1 (LOut l2 x1 x2')) (LNew l2 x1 (LOut l2 x1 x2')))) =
    LOut l2 (l1 x1'') (f' x1'' x2')" unfolding l_unmap_s_def Let_def Syn 
      using Eq5 can_unmap_unfold[OF Hunmap Syn_eq] Eq7 unfolding Syn Hsyn
      by(auto)
  qed
qed

(* Composition of sub-languages *)

end