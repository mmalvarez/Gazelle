theory Lifting
  imports "../Mergeable/Mergeable_Instances"
begin

(* (yet another) LiftUtils implementation
   this one makes use of the orderings on data to get a version of the
   "proj, then inj" law that is a compromise between the too-strict one
   for the idempotent part of LiftUtils
*)

(* 
  Lifting type definitions
*)

type_synonym ('a, 'b) syn_lifting = "('b \<Rightarrow> 'a)"

record ('syn, 'a, 'b) lifting =
  LUpd :: "('syn \<Rightarrow> 'a \<Rightarrow> 'b :: Pord \<Rightarrow> 'b)"
  LOut :: "('syn \<Rightarrow> 'b \<Rightarrow> 'a)"
  LBase :: "'syn \<Rightarrow> 'b"

declare lifting.defs[simp]

record ('syn, 'a, 'b) liftingv = "('syn, 'a, 'b :: Pord) lifting" +
  LOutS :: "'syn \<Rightarrow> 'b set"
  LInS :: "'syn \<Rightarrow> 'a set"

definition LNew :: "('syn, 'a, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> 'syn \<Rightarrow> 'a \<Rightarrow> 'b"  where
"LNew l s a = LUpd l s a (LBase l s)"

declare lifting.cases [simp]

(* Validity of lifting *)

(* i think we need to take ordering into account here.
   idea is that when we project, _data_ ordering needs to be preserved *)
(* TODO: can these laws be reduced? *)

(* if we get rid of H3 we no longer need the POrd constraint on a.
*)
definition lifting_valid :: "('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> bool" where
"lifting_valid l =
  ((\<forall> s a b . LUpd l s a b \<in> LOutS l s) \<and>
   (\<forall> s b . LOut l s b \<in> LInS l s) \<and>
   (\<forall> s a b . a \<in> LInS l s \<longrightarrow> a = LOut l s (LUpd l s a b)) \<and>
   (\<forall> s b . b \<in> LOutS l s \<longrightarrow> b <[ LUpd l s (LOut l s b) b))"

lemma lifting_validI :
  assumes HSO : "\<And> s a b . LUpd l s a b \<in> LOutS l s"
  assumes HSI : "\<And> s b . LOut l s b \<in> LInS l s"
  assumes HI : "\<And> s a b . a \<in> LInS l s \<Longrightarrow>  a = LOut l s (LUpd l s a b)"
  assumes HO : "\<And> s b . b \<in> LOutS l s \<Longrightarrow> b <[ LUpd l s (LOut l s b) b"
  shows "lifting_valid l" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDO :
  assumes H : "lifting_valid l"
  assumes HI : "a \<in> LInS l s"
  shows "a = LOut l s (LUpd l s a b)" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDO' :
  assumes H : "lifting_valid l"
  assumes HI : "a \<in> LInS l s"
  shows "a = LOut l s (LNew l s a)" using assms
  by(auto simp add: lifting_valid_def LNew_def)

lemma lifting_validDI :
  assumes H : "lifting_valid l"
  assumes HO : "b \<in> LOutS l s"
  shows "b <[ LUpd l s (LOut l s b) b" using assms
  by(auto simp add:lifting_valid_def)

lemma lifting_validDSO :
  assumes H : "lifting_valid l"
  shows "LUpd l s a b \<in> LOutS l s" using assms
  by(auto simp add: lifting_valid_def)

lemma lifting_validDSI :
  assumes H : "lifting_valid l"
  shows "LOut l s b \<in> LInS l s" using assms
  by(auto simp add: lifting_valid_def)

(* do we need another law relating data in case where we have upd (out )?
   also, what about put-put law? we didn't have that before so we shouldn't need it. *)

(*
  Mapping semantics through a lifting
*)

definition lift_map ::
  "('x, 'a , 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
    ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow>
    ('x \<Rightarrow> 'b \<Rightarrow> 'b)" where
"lift_map l sem syn st =
  (LUpd l syn (sem syn (LOut l syn st)) st)"

declare lift_map_def [simp]


(* trailing s = "with syntax" *)
definition lift_map_s ::
    "('a1, 'b1) syn_lifting \<Rightarrow>
     ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
     ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2) \<Rightarrow>
     ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2)" where
"lift_map_s l' l sem syn st =
  (LUpd l (l' syn) (sem (l' syn) (LOut l (l' syn) st)) st)"

declare lift_map_s_def [simp]

definition lower_map_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'a2)" where
"lower_map_s l' l sem syn st =
  (let syn' = (SOME x . l' x = syn) :: 'b1 in
  (LOut l syn (sem syn' (LNew l syn st))))"


(*
  "Mapping" predicates through a lifting
*)
declare lower_map_s_def [simp]

definition lift_pred :: "('x, 'a :: Pord, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool)" where
"lift_pred t P =
  (\<lambda> s b . P s (LOut t s b))"

declare lift_pred_def [simp]

definition lower_pred :: "('x, 'a :: Pord, 'b :: Pord, 'z) lifting_scheme \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> bool)" where
"lower_pred t P =
  (\<lambda> s a . P s (LNew t s a))"

declare lower_pred_def [simp]

definition lift_pred_step ::
  "('x, 'a :: Pord, 'b :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('x \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
   ('x \<Rightarrow> 'b \<Rightarrow> 'b \<Rightarrow> bool)" where
"lift_pred_step l P s st1 st2 =
        (P s (LOut l s st1) (LOut l s st2))"

definition lift_pred_step_s ::
  "('s1, 's2) syn_lifting \<Rightarrow>
   ('s1, 'b1 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool) \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool)" where
"lift_pred_step_s l1 l2 P syn st1 st2 =
   (P (l1 syn) (LOut l2 (l1 syn) st1) (LOut l2 (l1 syn) st2))"

definition lower_pred_step_s  ::
  "('s1, 's2) syn_lifting \<Rightarrow>
   ('s1, 'b1 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('s2 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   ('s1 \<Rightarrow> 'b1 \<Rightarrow> 'b1 \<Rightarrow> bool)" where
"lower_pred_step_s l1 l2 P syn st1 st2 =
   (\<forall> syn' . l1 syn' = syn \<longrightarrow>
     (P syn' (LNew l2 syn st1) (LUpd l2 syn st2 (LNew l2 syn st1))))"

lemma lower_pred_step_sI :
  assumes H : "\<And> syn' . l1 syn' = syn \<Longrightarrow>
                (P syn' (LNew l2 syn st1) (LUpd l2 syn st2 (LNew l2 syn st1)))"
  shows "lower_pred_step_s l1 l2 P syn st1 st2"
  using H
  unfolding lower_pred_step_s_def 
  by auto

lemma lower_pred_step_sD :
  assumes H : "lower_pred_step_s l1 l2 P syn st1 st2"
  assumes H1 : "l1 syn' = syn"
  shows "(P syn' (LNew l2 syn st1) (LUpd l2 syn st2 (LNew l2 syn st1)))"
  using H H1
  unfolding lower_pred_step_s_def
  by auto


(* Increasing-monotonicity (in second argument) for predicates *)
definition pred_mono2 ::
  "('s \<Rightarrow> 'a :: Pord \<Rightarrow> 'a :: Pord \<Rightarrow> bool) \<Rightarrow> bool" where
"pred_mono2 P =
  (\<forall> s x y y' .
    y <[ y' \<longrightarrow>
    P s x y \<longrightarrow>
    P s x y')"

lemma pred_mono2I :
  assumes H : "\<And> s x y y' .
                y <[ y' \<Longrightarrow>
                P s x y \<Longrightarrow>
                P s x y'"
  shows "pred_mono2 P" using assms
  by(auto simp add: pred_mono2_def)

lemma pred_mono2D :
  assumes H : "pred_mono2 P"
  assumes H1 : "y <[ y'"
  assumes H2 : "P s x y"
  shows "P s x y'" using assms
  by(auto simp add: pred_mono2_def)

(* Decreasing-monotonicity (in second argument) for predicates *)
definition pred_dmono2 ::
  "('s \<Rightarrow> 'a :: Pord \<Rightarrow> 'a :: Pord \<Rightarrow> bool) \<Rightarrow> bool" where
"pred_dmono2 P =
  (\<forall> s x y y' .
    y' <[ y \<longrightarrow>
    P s x y \<longrightarrow>
    P s x y')"

lemma pred_dmono2I :
  assumes H : "\<And> s x y y' .
                y' <[ y \<Longrightarrow>
                P s x y \<Longrightarrow>
                P s x y'"
  shows "pred_dmono2 P" using assms
  by(auto simp add: pred_dmono2_def)

lemma pred_dmono2D :
  assumes H : "pred_dmono2 P"
  assumes H1 : "y' <[ y"
  assumes H2 : "P s x y"
  shows "P s x y'" using assms
  by(auto simp add: pred_dmono2_def)

definition respects_InS ::
"('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> ('x \<Rightarrow> 'a \<Rightarrow> 'a) \<Rightarrow> bool" where
"respects_InS l f =
  (\<forall> x a . a \<in> LInS l x \<longrightarrow> f x a \<in> LInS l x)"

lemma respects_InSI :
  assumes H : "\<And> x a . a \<in> LInS l x \<Longrightarrow> f x a \<in> LInS l x"
  shows "respects_InS l f" using assms
  by(auto simp add: respects_InS_def)

lemma respects_InSD :
  assumes H0 : "respects_InS l f"
  assumes H : "a \<in> LInS l x"
  shows " f x a \<in> LInS l x" using assms
  by(auto simp add: respects_InS_def)

definition respects_OutS ::
"('x, 'a, 'b :: Pord, 'z) liftingv_scheme \<Rightarrow> ('x \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> bool" where
"respects_OutS l f =
  (\<forall> x b . b \<in> LOutS l x \<longrightarrow> f x b \<in> LOutS l x)"

lemma respects_OutSI :
  assumes H : "\<And> x b . b \<in> LOutS l x \<Longrightarrow> f x b \<in> LOutS l x"
  shows "respects_OutS l f" using assms
  by(auto simp add: respects_OutS_def)

lemma respects_OutSD :
  assumes H0 : "respects_OutS l f"
  assumes H : "b \<in> LOutS l x"
  shows "f x b \<in> LOutS l x" using assms
  by(auto simp add: respects_OutS_def)

(* do f and p both need to be monotone?
   just P i think? *)

declare [[show_types = false]]

lemma lift_pred_step_lift_map_s :
  fixes l1 :: "('a1, 'b1) syn_lifting"
  fixes l2 :: "('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) liftingv_scheme"
  assumes Hv : "lifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes Hres : "respects_InS l2 f"
  assumes HP : "P x1 x2 (f x1 x2)"
  shows "lift_pred_step_s l1 l2 P x1' x2' (lift_map_s l1 l2 f x1' x2')"
  using Hv Hsyn Hsem HP
proof-
  have In: "x2 \<in> LInS l2 x1" using lifting_validDSI[OF Hv, of x1 x2'] Hsem 
    by(auto)

  have In': "f x1 x2 \<in> LInS l2 x1" using respects_InSD[OF Hres] In by auto

  have Up1 : "(f x1 x2) =
              (LOut l2 x1 (LUpd l2 x1 (f x1 x2) x2'))"
    using lifting_validDO[OF Hv In'] by(auto simp add: Hsyn Hsem)

  hence Conc' : "P x1 x2 (LOut l2 x1 (LUpd l2 x1 (f x1 x2) x2'))" using HP by auto

  thus ?thesis
    by(auto simp add: lift_pred_step_s_def pred_mono2_def Hsyn Hsem)
qed

lemma lift_pred_step_lift_map_s_contra :
  fixes l1 :: "('a1, 'b1) syn_lifting"
  fixes l2 :: "('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) liftingv_scheme"
  assumes Hv : "lifting_valid l2"
  assumes Hsyn : "l1 x1' = x1"
  assumes Hsem : "LOut l2 x1 x2' = x2"
  assumes Hres : "respects_InS l2 f"
  assumes HP : "lift_pred_step_s l1 l2 P (x1') (x2') (lift_map_s l1 l2 f (x1') (x2'))"
  shows "P x1 x2 (f x1 x2)"
proof-
  have In: "x2 \<in> LInS l2 x1" using lifting_validDSI[OF Hv, of x1 x2'] Hsem 
    by(auto)

  have In': "f x1 x2 \<in> LInS l2 x1" using respects_InSD[OF Hres] In by auto

  have Up1 : "(f x1 x2) =
              (LOut l2 x1 (LUpd l2 x1 (f x1 x2) x2'))"
    using lifting_validDO[OF Hv In'] by(auto simp add: Hsyn Hsem)

  hence Conc' : "P x1 x2 (LOut l2 x1 (LUpd l2 x1 (f x1 x2) x2'))"
    using HP
    by(auto simp add: lift_pred_step_s_def pred_dmono2_def Hsyn Hsem)

  thus ?thesis using Up1
    by(auto simp add: lift_pred_step_s_def pred_dmono2_def Hsyn Hsem)
qed

(*
  We can always lift, but not always lower
  Here we specify when we can lower
*)
definition can_lower_map_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2) \<Rightarrow>
   bool" where
"can_lower_map_s l' l f =
  (\<forall> b1_1 b2_1 b1_2 b2_2 . 
     l' b1_1 = l' b1_2 \<longrightarrow>
     LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2 \<longrightarrow>
     LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2))"

lemma can_lower_map_sI :
  assumes H : 
  "\<And> b1_1 b2_1 b1_2 b2_2 .
     l' b1_1 = l' b1_2 \<Longrightarrow>
     LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2 \<Longrightarrow>
     LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2)"
shows "can_lower_map_s l' l f"
  unfolding can_lower_map_s_def
proof(clarify)
  fix b1_1 b1_2
  fix b2_1 b2_2
  assume H1 : "l' b1_1 = l' b1_2"
  assume H2 : "LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2"
  show "LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2)"
    using H[OF H1 H2] by auto
qed

lemma can_lower_map_sD :
  assumes H : "can_lower_map_s l' l f"
  assumes H1 : "l' b1_1 = l' b1_2"
  assumes H2 : "LOut l (l' b1_1) b2_1 = LOut l (l' b1_2) b2_2"
  shows "LOut l (l' b1_1) (f b1_1 b2_1) = LOut l (l' b1_2) (f b1_2 b2_2)"
  using assms unfolding can_lower_map_s_def by blast

(* are we going to run into trouble with being too strict on first component? *)
(* also, we may need to tight this by conditioning the predicate on st1 and st'1 being
   in LOutS *)
definition can_lower_pred_step_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   bool" where
"can_lower_pred_step_s l' l P =
  (\<forall> syn syn' st1 st2 st'1 st'2.
    l' syn = l' syn' \<longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<longrightarrow>
    LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<longrightarrow>
    P syn st1 st2 \<longrightarrow> P syn' st'1 st'2)"

(* does this need to actually be bi-directional? for now let's just have two definitions
*)
lemma can_lower_pred_step_sI :
  assumes H : 
  "\<And> syn syn' st1 st2 st'1 st'2 .
    l' syn = l' syn' \<Longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<Longrightarrow>
    LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<Longrightarrow>
    P syn st1 st2 \<Longrightarrow>
    P syn' st'1 st'2"
  shows "can_lower_pred_step_s l' l P"
  using assms unfolding can_lower_pred_step_s_def by blast

lemma can_lower_pred_step_sD :
  assumes H : "can_lower_pred_step_s l' l P"
  assumes H1 : "l' syn = l' syn'"
  assumes H2 : "LOut l (l' syn) st1 = LOut l (l' syn') st'1"
  assumes H3 : "LOut l (l' syn) st2 = LOut l (l' syn') st'2"
  assumes HP : "P syn st1 st2"
  shows "P syn' st'1 st'2"
  using assms unfolding can_lower_pred_step_s_def by blast

(*
definition can_dlower_pred_step_s ::
  "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   bool" where
"can_dlower_pred_step_s l' l P =
  (\<forall> syn syn' st1 st2 st'1 st'2.
    l' syn = l' syn' \<longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<longrightarrow>
    LOut l (l' syn) st'2 <[ LOut l (l' syn') st2 \<longrightarrow>
    P syn st1 st2 \<longrightarrow> P syn' st'1 st'2)"

(* does this need to actually be bi-directional? for now let's just have two definitions
*)
lemma can_dlower_pred_step_sI :
  assumes H : 
  "\<And> syn syn' st1 st2 st'1 st'2 .
    l' syn = l' syn' \<Longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<Longrightarrow>
    LOut l (l' syn) st'2 <[ LOut l (l' syn') st2 \<Longrightarrow>
    P syn st1 st2 \<Longrightarrow>
    P syn' st'1 st'2"
  shows "can_dlower_pred_step_s l' l P"
  using assms unfolding can_dlower_pred_step_s_def by blast

lemma can_dlower_pred_step_sD :
  assumes H : "can_dlower_pred_step_s l' l P"
  assumes H1 : "l' syn = l' syn'"
  assumes H2 : "LOut l (l' syn) st1 = LOut l (l' syn') st'1"
  assumes H3 : "LOut l (l' syn) st'2 <[ LOut l (l' syn') st2"
  assumes HP : "P syn st1 st2"
  shows "P syn' st'1 st'2"
  using assms unfolding can_dlower_pred_step_s_def by blast
*)

lemma lower_pred_step_s_lower_map_s  :
  assumes Hv : "lifting_valid l2"
  assumes Hunmap : "can_lower_map_s l1 l2 f'"
  assumes Hunpred : "can_lower_pred_step_s l1 l2 P'"
  assumes H: "\<And> x1'' . l1 x1'' = x1 \<Longrightarrow> P' x1'' x2' (f' x1'' x2')"
  shows "lower_pred_step_s l1 l2 P' x1 (LOut l2 x1 x2') (lower_map_s l1 l2 f' x1 (LOut l2 x1 x2'))"
proof(rule lower_pred_step_sI)
  fix syn'
  assume Hsyn : "l1 syn' = x1"

  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn)

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 syn'" using Hsyn Syn by simp

  have Eq1 : "LOut l2 (l1 syn') x2' = LOut l2 (l1 syn') (LNew l2 x1 (LOut l2 x1 x2'))"
    using Hsyn lifting_validDO[OF Hv]
               lifting_validDSI[OF Hv]
    unfolding LNew_def by auto

  have Eq2 :
    "(LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))) = 
      LOut l2 (l1 syn')
        (LUpd l2 x1 
          (LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2'))))
          (LNew l2 x1 (LOut l2 x1 x2')))"
    using lifting_validDO[OF Hv] lifting_validDSI[OF Hv] Hsyn
    by(auto)

  have Eq3 :
    "LOut l2 (l1 syn') (f' syn' x2') = 
     LOut l2 (l1 (SOME x. l1 x = x1)) (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))"
  proof(rule can_lower_map_sD[OF Hunmap])
    show "l1 syn' = l1 (SOME x. l1 x = x1)" using Syn_eq by auto
  next
    show "LOut l2 (l1 syn') x2' =
          LOut l2 (l1 (SOME x. l1 x = x1))
           (LNew l2 x1 (LOut l2 x1 x2'))"
      using Syn Hsyn lifting_validDO[OF Hv] lifting_validDSI[OF Hv]
      unfolding LNew_def 
      by(simp)
  qed

  have Eq3' :
    "LOut l2 (l1 syn') (f' syn' x2') =
     LOut l2 x1 (f' (SOME x. l1 x = x1) (LNew l2 x1 (LOut l2 x1 x2')))"
    using Eq3 Syn by simp

  have Eq4 : " LOut l2 (l1 syn') (f' syn' x2') =
    LOut l2 (l1 syn') (LUpd l2 x1 (LOut l2 (l1 syn') (f' syn' x2')) (LNew l2 x1 (LOut l2 x1 x2')))"
    using lifting_validDO[OF Hv] lifting_validDSI[OF Hv] leq_refl unfolding Hsyn by(auto)

  show "P' syn' (LNew l2 x1 (LOut l2 x1 x2'))
        (LUpd l2 x1 (lower_map_s l1 l2 f' x1 (LOut l2 x1 x2'))
          (LNew l2 x1 (LOut l2 x1 x2')))" unfolding lower_map_s_def Let_def 
(*    using Eq1 Eq2 Eq3' Eq4 *)

    using
    can_lower_pred_step_sD[OF Hunpred refl Eq1 Eq4 H[OF Hsyn]]
    unfolding LNew_def Syn Syn_eq Eq3
    by(auto)
qed

lemma lower_pred_step_s_lower_map_s_contra :
  assumes Hv : "lifting_valid l2"
  assumes Hunmap : "can_lower_map_s l1 l2 f'"
  assumes Hunpred : "can_lower_pred_step_s l1 l2 P'"
  assumes H: "lower_pred_step_s l1 l2 P' x1 (LOut l2 x1 x2')
              (lower_map_s l1 l2 f' x1 (LOut l2 x1 x2'))"
  assumes Hsyn :  "l1 x1'' = x1"
  shows "P' x1'' x2' (f' x1'' x2')"
proof-

  have Syn : "l1 (SOME x. l1 x = x1) = x1"
    by(rule Hilbert_Choice.someI; rule Hsyn)

  have Syn_eq : "l1 (SOME x. l1 x = x1) = l1 x1''" using Hsyn Syn by simp

  show "P' x1'' x2' (f' x1'' x2')"
  proof(rule can_lower_pred_step_sD[OF Hunpred refl _ _ lower_pred_step_sD[OF H Hsyn]])
    show "LOut l2 (l1 x1'') (LNew l2 x1 (LOut l2 x1 x2')) = LOut l2 (l1 x1'') x2'"
      using lifting_validDO[OF Hv] lifting_validDSI[OF Hv] unfolding LNew_def Hsyn by auto
  next
    have 1 : "lower_map_s l1 l2 f' x1 (LOut l2 x1 x2') =
              LOut l2 (l1 x1'') (LUpd l2 x1 (lower_map_s l1 l2 f' x1 (LOut l2 x1 x2')) 
                                            (LNew l2 x1 (LOut l2 x1 x2')))"
      using lifting_validDO[OF Hv] lifting_validDSI[OF Hv] unfolding Hsyn by auto

    have 2 : "LOut l2 (l1 x1'') x2' = 
              LOut l2 (l1 (SOME x. l1 x = x1)) (LUpd l2 x1 (LOut l2 x1 x2') (LBase l2 x1))"
      unfolding Syn Hsyn
      using lifting_validDO[OF Hv] lifting_validDSI[OF Hv] by auto

    have 3 : "LOut l2 (l1 x1'') (f' x1'' x2') = lower_map_s l1 l2 f' x1 (LOut l2 x1 x2')"
      unfolding lower_map_s_def Let_def 
      using can_lower_map_sD[OF Hunmap sym[OF Syn_eq]
                            , of x2' "(LUpd l2 x1 (LOut l2 x1 x2') (LBase l2 x1))"] 2
      unfolding LNew_def Syn Hsyn Syn_eq
      by(auto)

    show "LOut l2 (l1 x1'') (LUpd l2 x1 (lower_map_s l1 l2 f' x1 (LOut l2 x1 x2')) 
                                        (LNew l2 x1 (LOut l2 x1 x2'))) = LOut l2 (l1 x1'') (f' x1'' x2')"
      using leq_trans[of "LOut l2 (l1 x1'') (f' x1'' x2')"] 1 3 leq_refl by auto 
  qed
qed

lemma can_lower_lift_map_s :
  assumes Hv : "lifting_valid l2"
  assumes Hres : "respects_InS l2 f"
  shows "can_lower_map_s l1 l2 (lift_map_s l1 l2 f)"
proof(rule can_lower_map_sI)
  fix b1_1 b2_1 b1_2 b2_2
  assume Hsyn : "l1 b1_1 = l1 b1_2"
  assume Hsem : "LOut l2 (l1 b1_1) b2_1 = LOut l2 (l1 b1_2) b2_2"

  have InS1 : "f (l1 b1_1) (LOut l2 (l1 b1_1) b2_1) \<in> LInS l2 (l1 b1_1)"
    using respects_InSD[OF Hres] lifting_validDSI[OF Hv] by(auto)

  have InS2 : "f (l1 b1_2) (LOut l2 (l1 b1_2) b2_2) \<in> LInS l2 (l1 b1_2)"
    using respects_InSD[OF Hres] lifting_validDSI[OF Hv] by(auto)

  show "LOut l2 (l1 b1_1) (lift_map_s l1 l2 f b1_1 b2_1) =
        LOut l2 (l1 b1_2) (lift_map_s l1 l2 f b1_2 b2_2)"
    unfolding lift_map_s_def 
    using Hsem lifting_validDO[OF Hv] lifting_validDSI[OF Hv] InS1 InS2
    by(simp add: Hsyn Hsem)
qed

lemma can_lower_lift_pred_step_s :
  assumes Hv : "lifting_valid l2"
  shows "can_lower_pred_step_s l1 l2 (lift_pred_step_s l1 l2 P)"
proof(rule can_lower_pred_step_sI)
  fix syn syn' st1 st2 st'1 st'2
  assume Hsyn : "l1 syn = l1 syn'"
  assume Hsem1 : "LOut l2 (l1 syn) st1 = LOut l2 (l1 syn') st'1"
  assume Hsem2 : "LOut l2 (l1 syn) st2 = LOut l2 (l1 syn') st'2"
  assume H : "lift_pred_step_s l1 l2 P syn st1 st2"
  show "lift_pred_step_s l1 l2 P syn' st'1 st'2"
    using H Hsyn Hsem1 Hsem2 unfolding lift_pred_step_s_def
    by(auto)
qed

(* "Orthogonality" for a pair of lifted values 
idea: exists a LUB for the pair (values/liftings) s.t.
  - both projections are equal to the given values
  - this LUB is the true LUB

we can then generalize this to liftings
  - idea: liftings need to be orthogonal for all values
  - the test of this will be our lifting for LambdaInt - 
    if it is orthogonal it will be for nontrivial reasons
    (non-overlap of keys?)
    
*)
definition l_ortho' ::
  "('x, 'a1, 'b :: Pord) lifting \<Rightarrow>
   ('x, 'a2, 'b) lifting \<Rightarrow>
   'x \<Rightarrow> 'a1 \<Rightarrow> 'a2 \<Rightarrow> 'b \<Rightarrow> bool" where
"l_ortho' l1 l2 x a1 a2 b =
  (LOut l1 x b = a1 \<and>
   LOut l2 x b = a2)"

(* Idea: regardless of the state of the "database" (b)
   and how we "query" it (syntax x)
   we can always find compatible a1 and a2 *)
definition l_ortho_strong :: 
"('x, 'a1, 'b :: Pord) lifting \<Rightarrow>
 ('x, 'a2, 'b) lifting \<Rightarrow>
 bool" where
"l_ortho_strong l1 l2 =
  (\<forall> b x . 
    (\<exists> a1 a2 . l_ortho' l1 l2 x a1 a2 b))"


(*
(* 
  how we are going to use these:
  - the idea is that we are considering the general case where we have a predicate on
    a larger state, and some lifting that gets us there
  - the larger state predicate will not be (trivially) lowerable because it will depend
    on some data we don't have in the other state
  - however (I think) with appropriate monotonicity conditions, we can still get something
    this will be a more general (more useful) result corresponding to the situation
    where we are merging (which is basically all the time)
*)

definition can_lower_pred_step_s_weak ::
   "('a1, 'b1) syn_lifting \<Rightarrow>
   ('a1, 'a2 :: Pord, 'b2 :: Pord, 'z) lifting_scheme \<Rightarrow>
   ('b1 \<Rightarrow> 'b2 \<Rightarrow> 'b2 \<Rightarrow> bool) \<Rightarrow>
   bool" where
"can_lower_pred_step_s l' l P =
  (\<forall> syn syn' st1 st2 st'1 st'2.
    l' syn = l' syn' \<longrightarrow>
    LOut l (l' syn) st1 = LOut l (l' syn') st'1 \<longrightarrow>
    LOut l (l' syn) st2 = LOut l (l' syn') st'2 \<longrightarrow>
    P syn st1 st2 \<longrightarrow> P syn' st'1 st'2)"
*)
(* brainstorming examples for reasoning about combined semantics
  - compiler optimizations: arithmetic + something?
  - "constant elimination" in e.g. addition with zero
    - we need another language that has an overlap
    - where it will sometimes just always reset to 0 (with higher priority)
  - then we can think about merging predicates
    - use this to do some kind of interesting proof about merged semantics
    - "modes" for interpreting commands?
    - 
  - concurrency-like example (shared memory?)
*)

(*
  what useful operations can we think of as (sometimes) being always 0?
  
*)

(* other issues: orthogonality in merge lifting *)

end